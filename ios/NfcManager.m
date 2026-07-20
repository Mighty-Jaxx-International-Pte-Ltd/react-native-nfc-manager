#import "NfcManager.h"
#import "React/RCTBridge.h"
#import "React/RCTConvert.h"
#import "React/RCTEventDispatcher.h"
#import "React/RCTLog.h"
#import "GMEllipticCurveCrypto+hash.h"
#import "GMEllipticCurveCrypto.h"
#import "NSData+Hex.h"
#import "NSString+Hex.h"

NSData *derEncodeSignature(NSData* signature);
NSData *derDecodeSignature(NSData *der, int keySize);

NSString* getHexString(NSData *data) {
    NSUInteger capacity = data.length * 2;
    NSMutableString *sbuf = [NSMutableString stringWithCapacity:capacity];
    const unsigned char *buf = data.bytes;
    NSInteger i;
    for (i=0; i<data.length; ++i) {
        [sbuf appendFormat:@"%02lX", (unsigned long)buf[i]];
    }
    return sbuf;
}

static const NSUInteger NTAG215_USER_DATA_LENGTH_BYTES = 2;
static const NSUInteger NTAG215_USER_DATA_PAYLOAD_OFFSET = 8;
static const NSUInteger NTAG215_MAX_PAYLOAD_BYTES = 502;

static NSData *trimTrailingNullBytes(NSData *data) {
    const uint8_t *bytes = data.bytes;
    NSUInteger length = data.length;
    while (length > 0 && bytes[length - 1] == 0x00) {
        length -= 1;
    }
    if (length == data.length) {
        return data;
    }
    return [data subdataWithRange:NSMakeRange(0, length)];
}

static NSData *trimLeadingNullBytes(NSData *data) {
    const uint8_t *bytes = data.bytes;
    NSUInteger start = 0;
    while (start < data.length && bytes[start] == 0x00) {
        start += 1;
    }
    if (start == 0) {
        return data;
    }
    return [data subdataWithRange:NSMakeRange(start, data.length - start)];
}

static NSData *trimNullPadding(NSData *data) {
    return trimTrailingNullBytes(trimLeadingNullBytes(data));
}

static NSString *decodeNtag215UserData(NSData *rawFromPage04) {
    if (rawFromPage04.length < NTAG215_USER_DATA_LENGTH_BYTES) {
        return @"";
    }

    const uint8_t *bytes = rawFromPage04.bytes;
    NSUInteger payloadLength = ((NSUInteger)bytes[0] << 8) | bytes[1];

    if (payloadLength > 0 && payloadLength <= NTAG215_MAX_PAYLOAD_BYTES) {
        const NSUInteger payloadOffsets[] = {
            NTAG215_USER_DATA_LENGTH_BYTES,
            NTAG215_USER_DATA_PAYLOAD_OFFSET,
        };

        for (NSUInteger i = 0; i < sizeof(payloadOffsets) / sizeof(payloadOffsets[0]); i++) {
            NSUInteger payloadOffset = payloadOffsets[i];
            if (rawFromPage04.length >= payloadOffset + payloadLength) {
                NSData *payload = trimNullPadding([rawFromPage04 subdataWithRange:NSMakeRange(
                    payloadOffset,
                    payloadLength
                )]);
                return [[NSString alloc] initWithData:payload encoding:NSASCIIStringEncoding] ?: @"";
            }
        }
    }

    if (rawFromPage04.length > 0) {
        NSData *legacy = trimNullPadding(rawFromPage04);
        return [[NSString alloc] initWithData:legacy encoding:NSASCIIStringEncoding] ?: @"";
    }

    return @"";
}

NSString* getErrorMessage(NSError *error) {
     NSDictionary *userInfo = [error userInfo];
     NSError *underlyingError = [userInfo objectForKey:NSUnderlyingErrorKey];
    if (underlyingError != nil) {
        return [NSString stringWithFormat:@"%@:%ld,%@:%ld",
                [error domain], (long)[error code],
                [underlyingError domain], (long)[underlyingError code]];
    }
    return [NSString stringWithFormat:@"%@:%ld",
            [error domain], (long)[error code]];
}

static NSString * const NFCInvalidSignatureMessage = @"Invalid tag signature. This NFC tag could not be verified.";

NSString* getExceptionMessage(NSException *exception) {
    NSString *name = exception.name ?: @"";
    NSString *reason = exception.reason ?: @"";

    if ([name isEqualToString:@"Invalid signature"] ||
        [reason rangeOfString:@"signature" options:NSCaseInsensitiveSearch].location != NSNotFound) {
        return NFCInvalidSignatureMessage;
    }

    return [NSString stringWithFormat:@"%@: %@", name, reason];
}

static void nfcSafeExecute(RCTResponseSenderBlock callback, void (^block)(void)) {
    @try {
        block();
    } @catch (NSException *exception) {
        if (callback) {
            callback(@[getExceptionMessage(exception), [NSNull null]]);
        }
    }
}

static const uint8_t NTAG215_FAST_READ_START_PAGE = 0x04;
static const uint8_t NTAG215_FAST_READ_END_PAGE = 0x31;
static const uint8_t NTAG215_FAST_READ_CHUNK_PAGES = 0x0C; // 12 pages = 48 bytes
static const NSInteger NTAG215_FAST_READ_MAX_RETRIES = 2;

static BOOL isNfcTagConnectionLostError(NSError *error) {
    if (error == nil) {
        return NO;
    }
    // NFCReaderTransceiveErrorTagConnectionLost == 100
    if (error.code == 100) {
        return YES;
    }
    NSError *underlying = error.userInfo[NSUnderlyingErrorKey];
    return underlying != nil && underlying.code == 100;
}

static uint8_t ntag215EndPageForPayloadLength(NSUInteger payloadLength) {
    if (payloadLength == 0 || payloadLength > NTAG215_MAX_PAYLOAD_BYTES) {
        return NTAG215_FAST_READ_END_PAGE;
    }
    NSUInteger bytesNeeded = MAX(
        NTAG215_USER_DATA_LENGTH_BYTES + payloadLength,
        NTAG215_USER_DATA_PAYLOAD_OFFSET + payloadLength
    );
    NSUInteger pagesNeeded = (bytesNeeded + 3) / 4;
    NSUInteger endPage = NTAG215_FAST_READ_START_PAGE + pagesNeeded - 1;
    if (endPage > NTAG215_FAST_READ_END_PAGE) {
        return NTAG215_FAST_READ_END_PAGE;
    }
    return (uint8_t)endPage;
}

@implementation NfcManager {
    NSDictionary *nfcTechTypes;
    NSArray *techRequestTypes;
    NSString *detectPasswordInRequestTech;
    NSString *verifySignatureInRequestTech;
    RCTResponseSenderBlock techRequestCallback;
    id<NFCNDEFTag> connectedNdefTag;
}

RCT_EXPORT_MODULE()

@synthesize session;
@synthesize sessionEx;
@synthesize bridge = _bridge;

- (instancetype)init
{
    if (self = [super init]) {
        NSLog(@"NfcManager created");
    }
    
    if (@available(iOS 13.0, *)) {
        nfcTechTypes = @{
            [NSNumber numberWithInt: NFCTagTypeMiFare]: @"mifare",
            [NSNumber numberWithInt: NFCTagTypeFeliCa]: @"felica",
            [NSNumber numberWithInt: NFCTagTypeISO15693]: @"iso15693",
            // compatible with Android
            [NSNumber numberWithInt: NFCTagTypeISO7816Compatible]: @"IsoDep",
        };
    } else {
        nfcTechTypes = nil;
    }
    
    return self;
}

- (void)reset
{
    session = nil;
    sessionEx = nil;
    techRequestTypes = nil;
    techRequestCallback = nil;
    connectedNdefTag = nil;
    detectPasswordInRequestTech = nil;
    verifySignatureInRequestTech = nil;
}

- (NSArray<NSString *> *)supportedEvents
{
    return @[
             @"NfcManagerDiscoverTag",
             @"NfcManagerSessionClosed",
             @"NfcOriginalChecked",
             @"NfcOriginalCheckError",
             ];
}

- (NSData *)arrayToData: (NSArray *) array
{
  Byte bytes[[array count]];
  for (int i = 0; i < [array count]; i++) {
    bytes[i] = [[array objectAtIndex:i] integerValue];
  }
  NSData *payload = [[NSData alloc] initWithBytes:bytes length:[array count]];
  return payload;
}

- (NSArray *)dataToArray:(NSData *)data
{
    const unsigned char *dataBuffer = data ? (const unsigned char *)[data bytes] : NULL;
    
    if (!dataBuffer)
        return @[];
    
    NSUInteger          dataLength  = [data length];
    NSMutableArray     *array  = [NSMutableArray arrayWithCapacity:dataLength];
    
    for (int i = 0; i < dataLength; ++i)
        [array addObject:[NSNumber numberWithInteger:dataBuffer[i]]];
    
    return array;
}

- (NSDictionary*)convertNdefRecord:(NFCNDEFPayload *) record
{
    return @{
             @"id": [self dataToArray:[record identifier]],
             @"payload": [self dataToArray: [record payload]],
             @"type": [self dataToArray:[record type]],
             @"tnf": [NSNumber numberWithInt:[record typeNameFormat]]
             };
}

- (NSArray*)convertNdefMessage:(NFCNDEFMessage *)message
{
    NSArray * records = [message records];
    NSMutableArray *resultArray = [NSMutableArray arrayWithCapacity: [records count]];
    for (int i = 0; i < [records count]; i++) {
        [resultArray addObject:[self convertNdefRecord: records[i]]];
    }
    return resultArray;
}

- (NSString*)getRNTechName:(id<NFCTag>)tag {
    NSString * tech = [nfcTechTypes objectForKey:[NSNumber numberWithInt:(int)tag.type]];
    if (tech == nil) {
        tech = @"unknown";
    }
    return tech;
}

- (NSDictionary*)getRNTag:(id<NFCTag>)tag {
    NSMutableDictionary *tagInfo = @{}.mutableCopy;
    NSString* tech = [self getRNTechName:tag];
    [tagInfo setObject:tech forKey:@"tech"];
                   
    if (@available(iOS 13.0, *)) {
        if (tag.type == NFCTagTypeMiFare) {
            id<NFCMiFareTag> mifareTag = [tag asNFCMiFareTag];
            [tagInfo setObject:getHexString(mifareTag.identifier) forKey:@"id"];
        } else if (tag.type == NFCTagTypeISO7816Compatible) {
            id<NFCISO7816Tag> iso7816Tag = [tag asNFCISO7816Tag];
            [tagInfo setObject:getHexString(iso7816Tag.identifier) forKey:@"id"];
            [tagInfo setObject:iso7816Tag.initialSelectedAID forKey:@"initialSelectedAID"];
            [tagInfo setObject:[self dataToArray:iso7816Tag.historicalBytes] forKey:@"historicalBytes"];
            [tagInfo setObject:[self dataToArray:iso7816Tag.applicationData] forKey:@"applicationData"];
        } else if (tag.type == NFCTagTypeISO15693) {
            id<NFCISO15693Tag> iso15693Tag = [tag asNFCISO15693Tag];
            [tagInfo setObject:getHexString(iso15693Tag.identifier) forKey:@"id"];
            [tagInfo setObject:[NSNumber numberWithUnsignedInteger:iso15693Tag.icManufacturerCode] forKey:@"icManufacturerCode"];
            [tagInfo setObject:[self dataToArray:iso15693Tag.icSerialNumber] forKey:@"icSerialNumber"];
        } else if (tag.type == NFCTagTypeFeliCa) {
            // TODO
        }
    }

    return tagInfo;
}

- (id<NFCNDEFTag>)getNDEFTagHandle:(id<NFCTag>)tag {
    // all following types inherite from NFCNDEFTag
    if (@available(iOS 13.0, *)) {
        if (tag.type == NFCTagTypeMiFare) {
            return [tag asNFCMiFareTag];
        } else if (tag.type == NFCTagTypeISO7816Compatible) {
            return [tag asNFCISO7816Tag];
        } else if (tag.type == NFCTagTypeISO15693) {
            return [tag asNFCISO15693Tag];
        } else if (tag.type == NFCTagTypeFeliCa) {
            return [tag asNFCFeliCaTag];
        }
    }

    return nil;
}

- (void)readerSession:(NFCNDEFReaderSession *)session didDetectNDEFs:(NSArray<NFCNDEFMessage *> *)messages
{
    NSLog(@"readerSession:didDetectNDEFs");
    if ([messages count] > 0) {
        // parse the first message for now
        [self sendEventWithName:@"NfcManagerDiscoverTag"
                           body:@{@"ndefMessage": [self convertNdefMessage:messages[0]]}];
    } else {
        [self sendEventWithName:@"NfcManagerDiscoverTag"
                           body:@{@"ndefMessage": @[]}];
    }
}

- (void)readerSession:(NFCNDEFReaderSession *)session didInvalidateWithError:(NSError *)error
{
    NSLog(@"readerSession:didInvalidateWithError: (%@)", [error localizedDescription]);
    if (techRequestCallback) {
        techRequestCallback(@[getErrorMessage(error)]);
        techRequestCallback = nil;
    }
    
    [self reset];
    [self sendEventWithName:@"NfcManagerSessionClosed"
                       body:@{}];
}

- (void)tagReaderSession:(NFCTagReaderSession *)session didDetectTags:(NSArray<__kindof id<NFCTag>> *)tags
{
    NSLog(@"NFCTag didDetectTags");
    if (@available(iOS 13.0, *)) {
        if (techRequestCallback != nil) {
            BOOL found = false;
            RCTResponseSenderBlock pendingCallback = techRequestCallback;
            
            // by setting callback to nil, we know the promise is resolved
            techRequestCallback = nil;

            for (NSString* requestType in techRequestTypes) {
                for (id<NFCTag> tag in tags) {
                    NSString * tagType = [self getRNTechName:tag];
                    // here we treat Ndef is a special case, because all specific tech types
                    // inherites from NFCNDEFTag, so we simply allow it to connect
                    if ([tagType isEqualToString:requestType] || [requestType isEqualToString:@"Ndef"]) {
                        [sessionEx connectToTag:tag
                              completionHandler:^(NSError *error) {
                            if (error != nil) {
                                pendingCallback(@[getErrorMessage(error)]);
                                return;
                            }
                          id<NFCMiFareTag> mifareTag = [sessionEx.connectedTag asNFCMiFareTag];
                          if ([@"NO" caseInsensitiveCompare:verifySignatureInRequestTech ?: @"YES"] == NSOrderedSame) {
                              NSMutableDictionary *tagInfo = @{}.mutableCopy;
                              [tagInfo setObject:getHexString(mifareTag.identifier) forKey:@"id"];
                              [tagInfo setValue:requestType forKey:@"requestType"];
                              [tagInfo setValue:@"NO" forKey:@"passwordProtection"];
                              pendingCallback(@[[NSNull null], tagInfo]);
                              return;
                          }
                          NSData *data = [NSData dataWithHexString:@"3C00"];
                          NSLog(@"input bytes: %@", getHexString(data));
                          [mifareTag sendMiFareCommand:data
                                     completionHandler:^(NSData *response, NSError *error) {
                              nfcSafeExecute(pendingCallback, ^{
                                  if (error) {
                                     pendingCallback(@[getErrorMessage(error)]);
                                     return;
                                  }
                                  if(response.length == 1){
                                      pendingCallback(@[getErrorMessage(error)]);
                                      return;
                                  }
                                  GMEllipticCurve curve = GMEllipticCurveSecp128r1;
                                  GMEllipticCurveCrypto *crypto = [GMEllipticCurveCrypto cryptoForCurve:curve];
                                  crypto = [GMEllipticCurveCrypto cryptoForKeyBase64:@"BElOGjhtPTz+PcEOXeaKSZscIC21sTI5PontGf5b6Lxh"];
                                  NSData *udidData = [NSData dataWithHexString: [NSString stringWithFormat:@"000000000000000000%@",getHexString(mifareTag.identifier)]];
                                  NSData *encodedCorrectSignature = derEncodeSignature(response);
                                  BOOL valid = [crypto verifyEncodedSignature:encodedCorrectSignature forHash:udidData];
                                  if(valid){
                                    NSMutableDictionary *tagInfo = @{}.mutableCopy;
                                    [tagInfo setObject:getHexString(mifareTag.identifier) forKey:@"id"];
                                    [tagInfo setValue:requestType forKey:@"requestType"];
                                    [tagInfo setValue:@"NO" forKey:@"passwordProtection"];
                                    pendingCallback(@[[NSNull null], tagInfo]);
                                  }else{
                                      pendingCallback(@[NFCInvalidSignatureMessage, [NSNull null]]);
                                  }
                              });
                            }];
                        }];
                        found = true;
                        break;
                    }
                }
            }
            
            if (!found) {
                pendingCallback(@[@"No tech matches", [NSNull null]]);
            }
        }
    }
}

- (void)tagReaderSession:(NFCTagReaderSession *)session didInvalidateWithError:(NSError *)error
{
    NSLog(@"NFCTag didInvalidateWithError");
    if (techRequestCallback) {
        techRequestCallback(@[getErrorMessage(error)]);
        techRequestCallback = nil;
    }

    [self reset];
    [self sendEventWithName:@"NfcManagerSessionClosed"
                       body:@{}];
}

- (void)tagReaderSessionDidBecomeActive:(NFCTagReaderSession *)session
{
    NSLog(@"NFCTag didBecomeActive");
}

+ (BOOL)requiresMainQueueSetup
{
    return YES;
}

RCT_EXPORT_METHOD(isSupported: (NSString *)tech callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if ([tech isEqualToString:@""] || [tech isEqualToString:@"Ndef"]) {
        if (@available(iOS 11.0, *)) {
            callback(@[[NSNull null], NFCNDEFReaderSession.readingAvailable ? @YES : @NO]);
            return;
        }
    } else if ([tech isEqualToString:@"mifare"] || [tech isEqualToString:@"felica"] || [tech isEqualToString:@"iso15693"] || [tech isEqualToString:@"IsoDep"]) {
        if (@available(iOS 13.0, *)) {
            callback(@[[NSNull null], NFCTagReaderSession.readingAvailable ? @YES : @NO]);
            return;
        }
    }

    callback(@[[NSNull null], @NO]);
    });
}

RCT_EXPORT_METHOD(start: (nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 11.0, *)) {
        if (NFCNDEFReaderSession.readingAvailable) {
            NSLog(@"NfcManager initialized");
            [self reset];
            callback(@[]);
            return;
        }
    }

    callback(@[@"Not support in this device", [NSNull null]]);
    });
}

RCT_EXPORT_METHOD(requestTechnology: (NSArray *)techs :(NSString *)detectPassword :(NSString *)verifySignature callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (sessionEx == nil) {
        callback(@[@"you need to call registerTagEventEx first", [NSNull null]]);
        return;
    }
    if (techRequestCallback == nil) {
        techRequestTypes = techs;
        detectPasswordInRequestTech = detectPassword;
        verifySignatureInRequestTech = verifySignature ?: @"YES";
        techRequestCallback = callback;
    } else {
        callback(@[@"duplicate tech request, please call cancelTechnologyRequest to cancel previous one", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(cancelTechnologyRequest:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    techRequestTypes = nil;
    techRequestCallback = nil;
    [sessionEx invalidateSession];
    callback(@[]);
    });
}

RCT_EXPORT_METHOD(registerTagEvent:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 11.0, *)) {
        if (session == nil) {
            session = [[NFCNDEFReaderSession alloc]
                       initWithDelegate:self queue:dispatch_get_main_queue() invalidateAfterFirstRead:[[options objectForKey:@"invalidateAfterFirstRead"] boolValue]];
            session.alertMessage = [options objectForKey:@"alertMessage"];
            [session beginSession];
            callback(@[]);
        } else {
            callback(@[@"Duplicated registration", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(unregisterTagEvent:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 11.0, *)) {
        if (session != nil) {
            [session invalidateSession];
            callback(@[]);
        } else {
            callback(@[@"Not even registered", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(registerTagEventEx:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (sessionEx == nil) {
            sessionEx = [[NFCTagReaderSession alloc]
                         initWithPollingOption:(NFCPollingISO14443 | NFCPollingISO15693 | NFCPollingISO15693) delegate:self queue:dispatch_get_main_queue()];
            sessionEx.alertMessage = [options objectForKey:@"alertMessage"];
            [sessionEx beginSession];
            callback(@[]);
        } else {
//            [sessionEx beginSession];/\\\
            callback(@[@"Duplicated registration", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(unregisterTagEventEx:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (sessionEx != nil) {
            [sessionEx invalidateSession];
            callback(@[]);
        } else {
            callback(@[@"Not even registered", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(invalidateSession:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (session != nil) {
            [session invalidateSession];
            callback(@[]);
        } else if (sessionEx != nil) {
            [sessionEx invalidateSession];
            callback(@[]);
        } else {
            callback(@[@"No active session", [NSNull null]]);
        }
    }
    });
}

RCT_EXPORT_METHOD(invalidateSessionWithError:(NSString *)errorMessage callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (session != nil) {
            [session invalidateSessionWithErrorMessage: errorMessage];
            callback(@[]);
        } else if (sessionEx != nil) {
            [sessionEx invalidateSessionWithErrorMessage: errorMessage];
            callback(@[]);
        } else {
            callback(@[@"No active session", [NSNull null]]);
        }
    }
    });
}

RCT_EXPORT_METHOD(getTag: (nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        NSMutableDictionary* rnTag = @{}.mutableCopy;
        id<NFCNDEFTag> ndefTag = nil;
        
        if (session != nil) {
            if (self->connectedNdefTag) {
                ndefTag = self->connectedNdefTag;
            }
        } else if (sessionEx != nil) {
            if (sessionEx.connectedTag) {
                rnTag = [self getRNTag:sessionEx.connectedTag].mutableCopy;
                ndefTag = [self getNDEFTagHandle:sessionEx.connectedTag];
            }
        } else {
            callback(@[@"No session available", [NSNull null]]);
        }
        
        if (ndefTag) {
            [ndefTag readNDEFWithCompletionHandler:^(NFCNDEFMessage *ndefMessage, NSError *error) {
                if (!error) {
                    [rnTag setObject:[self convertNdefMessage:ndefMessage] forKey:@"ndefMessage"];
                }
                callback(@[[NSNull null], rnTag]);
            }];
            return;
        }
        
        callback(@[[NSNull null], rnTag]);
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(getNdefMessage: (nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        id<NFCNDEFTag> ndefTag = nil;
        
        if (session != nil) {
            if (self->connectedNdefTag) {
                ndefTag = self->connectedNdefTag;
            }
        } else if (sessionEx != nil) {
            if (sessionEx.connectedTag) {
                ndefTag = [self getNDEFTagHandle:sessionEx.connectedTag];
            }
        }
        
        if (ndefTag) {
            [ndefTag readNDEFWithCompletionHandler:^(NFCNDEFMessage *ndefMessage, NSError *error) {
                if (error) {
                    callback(@[getErrorMessage(error), [NSNull null]]);
                } else {
                    callback(@[[NSNull null], @{@"ndefMessage": [self convertNdefMessage:ndefMessage]}]);
                }
            }];
            return;
        }
        
        callback(@[@"No ndef available", [NSNull null]]);
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(writeNdefMessage:(NSArray*)bytes callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        id<NFCNDEFTag> ndefTag = nil;
        
        if (session != nil) {
            if (self->connectedNdefTag) {
                ndefTag = self->connectedNdefTag;
            }
        } else if (sessionEx != nil) {
            if (sessionEx.connectedTag) {
                ndefTag = [self getNDEFTagHandle:sessionEx.connectedTag];
            }
        }
        
        if (ndefTag) {
            NSData *data = [self arrayToData:bytes];
            NFCNDEFMessage *ndefMsg = [NFCNDEFMessage ndefMessageWithData:data];
            if (!ndefMsg) {
                callback(@[@"invalid ndef msg"]);
                return;
            }

            [ndefTag writeNDEF:ndefMsg completionHandler:^(NSError *error) {
                if (error) {
                    callback(@[getErrorMessage(error), [NSNull null]]);
                } else {
                    callback(@[[NSNull null]]);
                }
            }];
            return;
        }
        
        callback(@[@"No ndef available", [NSNull null]]);
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(sendMifareCommand:(NSArray *)bytes callback: (nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (sessionEx != nil) {
            if (sessionEx.connectedTag) {
                id<NFCMiFareTag> mifareTag = [sessionEx.connectedTag asNFCMiFareTag];
                NSData *data = [self arrayToData:bytes];
                NSLog(@"input bytes: %@", getHexString(data));
                if (mifareTag) {
                    [mifareTag sendMiFareCommand:data
                               completionHandler:^(NSData *response, NSError *error) {
                        if (error) {
                            callback(@[getErrorMessage(error), [NSNull null]]);
                        } else {
                            callback(@[[NSNull null], [self dataToArray:response]]);
                        }
                    }];
                    return;
                } else {
                    callback(@[@"not a mifare tag", [NSNull null]]);
                }
            }
            callback(@[@"Not connected", [NSNull null]]);
        } else {
            callback(@[@"Not even registered", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}


- (void)sendMiFareCommandWithRetry:(NSData *)command
                             toTag:(id<NFCMiFareTag>)tag
                           retries:(NSInteger)retriesLeft
                        completion:(void (^)(NSData *response, NSError *error))completion API_AVAILABLE(ios(13.0))
{
    __weak NfcManager *weakSelf = self;
    [tag sendMiFareCommand:command
         completionHandler:^(NSData *response, NSError *error) {
        if (error && isNfcTagConnectionLostError(error) && retriesLeft > 0) {
            NSLog(@"NFC FAST_READ/command lost connection, retrying (%ld left)", (long)retriesLeft);
            [weakSelf sendMiFareCommandWithRetry:command
                                           toTag:tag
                                         retries:retriesLeft - 1
                                      completion:completion];
            return;
        }
        if (completion) {
            completion(response, error);
        }
    }];
}

- (void)fastReadNtag215PagesFrom:(uint8_t)startPage
                              to:(uint8_t)endPage
                           onTag:(id<NFCMiFareTag>)tag
                     accumulated:(NSMutableData *)accumulated
                      completion:(void (^)(NSData *data, NSError *error))completion API_AVAILABLE(ios(13.0))
{
    if (startPage > endPage) {
        if (completion) {
            completion(accumulated, nil);
        }
        return;
    }

    uint8_t chunkEnd = (uint8_t)MIN((int)startPage + NTAG215_FAST_READ_CHUNK_PAGES - 1, (int)endPage);
    uint8_t cmdBytes[3] = { 0x3A, startPage, chunkEnd };
    NSData *command = [NSData dataWithBytes:cmdBytes length:3];
    __weak NfcManager *weakSelf = self;

    [self sendMiFareCommandWithRetry:command
                               toTag:tag
                             retries:NTAG215_FAST_READ_MAX_RETRIES
                          completion:^(NSData *response, NSError *error) {
        if (error) {
            if (completion) {
                completion(nil, error);
            }
            return;
        }
        if (response.length > 0) {
            [accumulated appendData:response];
        }
        [weakSelf fastReadNtag215PagesFrom:(uint8_t)(chunkEnd + 1)
                                        to:endPage
                                     onTag:tag
                               accumulated:accumulated
                                completion:completion];
    }];
}

- (void)fastReadNtag215UserMemoryOnTag:(id<NFCMiFareTag>)tag
                            completion:(void (^)(NSData *data, NSError *error))completion API_AVAILABLE(ios(13.0))
{
    NSMutableData *headerAcc = [NSMutableData data];
    __weak NfcManager *weakSelf = self;
    // Header first (pages 4-7) so we only pull as many pages as the payload needs.
    [self fastReadNtag215PagesFrom:NTAG215_FAST_READ_START_PAGE
                                to:0x07
                             onTag:tag
                       accumulated:headerAcc
                        completion:^(NSData *header, NSError *error) {
        if (error || header.length < NTAG215_USER_DATA_LENGTH_BYTES) {
            if (completion) {
                completion(nil, error);
            }
            return;
        }

        const uint8_t *bytes = header.bytes;
        NSUInteger payloadLength = ((NSUInteger)bytes[0] << 8) | bytes[1];
        uint8_t endPage = ntag215EndPageForPayloadLength(payloadLength);

        if (endPage <= 0x07) {
            if (completion) {
                completion(header, nil);
            }
            return;
        }

        NSMutableData *acc = [NSMutableData dataWithData:header];
        [weakSelf fastReadNtag215PagesFrom:0x08
                                        to:endPage
                                     onTag:tag
                               accumulated:acc
                                completion:completion];
    }];
}

RCT_EXPORT_METHOD(verifyOriginalCheckNtag215:(NSString *)publicKey :(NSString *)password :(NSString *)packString :(NSString *)udid :(NSString *) nfcPasswordProtection callback: (nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        NSMutableDictionary *resultChecking = @{}.mutableCopy;
        if (sessionEx != nil) {
            if (sessionEx.connectedTag) {
                id<NFCMiFareTag> mifareTag = [sessionEx.connectedTag asNFCMiFareTag];
                NSString *udidTag  = [mifareTag.identifier hexString];
                if(![[udid uppercaseString] isEqualToString:[udidTag uppercaseString]]){
                    callback(@[[NSNull null], @"ERROR  595"]);
                    [sessionEx invalidateSession];
                    return;
                }
                if (mifareTag) {
                    void (^finishWithUserData)(NSData *userData, NSError *error, NSString *errorCode) = ^(NSData *userData, NSError *error, NSString *errorCode) {
                        if (error) {
                            callback(@[getErrorMessage(error), errorCode ?: [NSNull null]]);
                            [sessionEx invalidateSession];
                            return;
                        }
                        NSString *encryptedString = decodeNtag215UserData(userData);
                        [resultChecking setValue:encryptedString forKey:@"encryptedString"];
                        callback(@[[NSNull null],  resultChecking]);
                        [sessionEx invalidateSession];
                    };

                    if(password.length > 0){
                        // Unlock with password, then chunked FAST_READ (avoids NFCError 100 on large single reads).
                        NSData *readSetting = [NSData dataWithHexString:[NSString stringWithFormat:@"1B%@",password]];
                        NSLog(@"input bytes: %@", [readSetting hexString]);
                        [self sendMiFareCommandWithRetry:readSetting
                                                   toTag:mifareTag
                                                 retries:NTAG215_FAST_READ_MAX_RETRIES
                                              completion:^(NSData *responseSetting, NSError *error) {
                            if (error) {
                                callback(@[getErrorMessage(error), @"ERROR  595"]);
                                [sessionEx invalidateSession];
                                return;
                            }
                            if(responseSetting.length == 1){
                                callback(@[getErrorMessage(error), @"ERROR  595"]);
                                [sessionEx invalidateSession];
                                return;
                            }
                            [self fastReadNtag215UserMemoryOnTag:mifareTag
                                                      completion:^(NSData *userData, NSError *readError) {
                                finishWithUserData(userData, readError, @"ERROR  632");
                            }];
                        }];
                    }else{
                        // Optional originality read, then chunked FAST_READ.
                        NSData *data = [NSData dataWithHexString:@"3C00"];
                        NSLog(@"input bytes: %@", getHexString(data));
                        [self sendMiFareCommandWithRetry:data
                                                   toTag:mifareTag
                                                 retries:NTAG215_FAST_READ_MAX_RETRIES
                                              completion:^(NSData *response, NSError *error) {
                            if (error) {
                                callback(@[getErrorMessage(error), [NSNull null]]);
                                [sessionEx invalidateSession];
                                return;
                            }
                            [self fastReadNtag215UserMemoryOnTag:mifareTag
                                                      completion:^(NSData *userData, NSError *readError) {
                                finishWithUserData(userData, readError, @"3A0431 ERROR AT 586");
                            }];
                        }];
                    }
                    return;
                } else {
                    callback(@[@"not a mifare tag", [NSNull null]]);
                }
            }
            callback(@[@"Not connected", [NSNull null]]);
        } else {
            callback(@[@"Not even registered", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(sendCommandAPDUBytes:(NSArray *)bytes callback: (nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (sessionEx != nil) {
            if (sessionEx.connectedTag) {
                id<NFCISO7816Tag> iso7816Tag = [sessionEx.connectedTag asNFCISO7816Tag];
                NSData *data = [self arrayToData:bytes];
                NFCISO7816APDU *apdu = [[NFCISO7816APDU alloc] initWithData:data];
                if (iso7816Tag) {
                    [iso7816Tag sendCommandAPDU:apdu completionHandler:^(NSData* response, uint8_t sw1, uint8_t sw2, NSError* error) {
                        if (error) {
                            callback(@[getErrorMessage(error), [NSNull null]]);
                        } else {
                            callback(@[[NSNull null], [self dataToArray:response], [NSNumber numberWithInt:sw1], [NSNumber numberWithInt:sw2]]);
                        }
                    }];
                    return;
                } else {
                    callback(@[@"not an iso7816 tag", [NSNull null]]);
                }
            }
            callback(@[@"Not connected", [NSNull null]]);
        } else {
            callback(@[@"Not even registered", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(sendCommandAPDU:(NSDictionary *)apduData callback: (nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (sessionEx != nil) {
            if (sessionEx.connectedTag) {
                id<NFCISO7816Tag> iso7816Tag = [sessionEx.connectedTag asNFCISO7816Tag];
                NSNumber *cla = [apduData objectForKey:@"cla"];
                NSNumber *ins = [apduData objectForKey:@"ins"];
                NSNumber *p1 = [apduData objectForKey:@"p1"];
                NSNumber *p2 = [apduData objectForKey:@"p2"];
                NSArray *dataArray = [apduData objectForKey:@"data"];
                NSData *data = [self arrayToData:dataArray];
                NSNumber *le = [apduData objectForKey:@"le"];
                
                /*
                NFCISO7816APDU *apdu = [[NFCISO7816APDU alloc] initWithInstructionClass:0 instructionCode:0x84 p1Parameter:0 p2Parameter:0 data:[[NSData alloc] init] expectedResponseLength:8]
                 */
                
                NFCISO7816APDU *apdu = [[NFCISO7816APDU alloc] initWithInstructionClass:[cla unsignedCharValue] instructionCode:[ins unsignedCharValue] p1Parameter:[p1 unsignedCharValue] p2Parameter:[p2 unsignedCharValue] data:data expectedResponseLength:[le integerValue]];
                if (iso7816Tag) {
                    [iso7816Tag sendCommandAPDU:apdu completionHandler:^(NSData* response, uint8_t sw1, uint8_t sw2, NSError* error) {
                        if (error) {
                            callback(@[getErrorMessage(error), [NSNull null]]);
                        } else {
                            callback(@[[NSNull null], [self dataToArray:response], [NSNumber numberWithInt:sw1], [NSNumber numberWithInt:sw2]]);
                        }
                    }];
                    return;
                } else {
                    callback(@[@"not an iso7816 tag", [NSNull null]]);
                }
            }
            callback(@[@"Not connected", [NSNull null]]);
        } else {
            callback(@[@"Not even registered", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(setAlertMessage: (NSString *)alertMessage callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 11.0, *)) {
        if (session != nil) {
            session.alertMessage = alertMessage;
            callback(@[]);
        } else if (sessionEx != nil) {
            sessionEx.alertMessage = alertMessage;
            callback(@[]);
        } else {
            callback(@[@"Not even registered", [NSNull null]]);
        }
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(isSessionAvailable:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 11.0, *)) {
        callback(@[[NSNull null], session != nil ? @YES : @NO]);
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(isSessionExAvailable:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 11.0, *)) {
        callback(@[[NSNull null], sessionEx != nil ? @YES : @NO]);
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

// ---------------------------
// iso15693
// ---------------------------
RCT_EXPORT_METHOD(iso15693_getSystemInfo:(nonnull NSNumber *)flags callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag rFlag = [flags unsignedIntValue];
        
        [tag getSystemInfoWithRequestFlag:rFlag completionHandler:
         ^(NSInteger dsfid, NSInteger afi, NSInteger blockSize, NSInteger blockCount, NSInteger icReference, NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[[NSNull null], @{
                           @"dsfid": @(dsfid),
                           @"afi": @(afi),
                           @"blockSize": @(blockSize),
                           @"blockCount": @(blockCount),
                           @"icReference": @(icReference)
            }]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_readSingleBlock:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t blockNumber = [[options objectForKey:@"blockNumber"] unsignedIntValue];
        
        [tag readSingleBlockWithRequestFlags:flags
                                 blockNumber:blockNumber
                           completionHandler:^(NSData *resp, NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[[NSNull null], [self dataToArray:resp]]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_writeSingleBlock:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t blockNumber = [[options objectForKey:@"blockNumber"] unsignedIntValue];
        NSData *dataBlock = [self arrayToData:[options mutableArrayValueForKey:@"dataBlock"]];
        
        [tag writeSingleBlockWithRequestFlags:flags
                                  blockNumber:blockNumber
                                    dataBlock:dataBlock
                           completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_lockBlock:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t blockNumber = [[options objectForKey:@"blockNumber"] unsignedIntValue];
        
        [tag lockBlockWithRequestFlags:flags
                                  blockNumber:blockNumber
                           completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_writeAFI:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t afi = [[options objectForKey:@"afi"] unsignedIntValue];
        
        [tag writeAFIWithRequestFlag:flags
                                 afi:afi
                   completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_lockAFI:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        
        [tag lockAFIWithRequestFlag:flags
                  completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_writeDSFID:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t dsfid = [[options objectForKey:@"dsfid"] unsignedIntValue];
        
        [tag writeDSFIDWithRequestFlag:flags
                                 dsfid:dsfid
                   completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_lockDSFID:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        
        // notice thie method name, DSFID -> DFSID, seems to be a typo in Core NFC
        [tag lockDFSIDWithRequestFlag:flags
                  completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_resetToReady:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        
        [tag resetToReadyWithRequestFlags:flags
                  completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_select:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        
        [tag selectWithRequestFlags:flags
                  completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_stayQuiet:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        [tag stayQuietWithCompletionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_customCommand:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        NSInteger customCommandCode = [[options objectForKey:@"customCommandCode"] integerValue];
        NSData *customRequestParameters = [self arrayToData:[options mutableArrayValueForKey:@"customRequestParameters"]];
        
        [tag customCommandWithRequestFlag:flags
                        customCommandCode: customCommandCode
                  customRequestParameters: customRequestParameters
                   completionHandler:^(NSData *resp, NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[[NSNull null], [self dataToArray:resp]]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_extendedReadSingleBlock:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t blockNumber = [[options objectForKey:@"blockNumber"] unsignedIntValue];
        
        [tag extendedReadSingleBlockWithRequestFlags:flags
                                         blockNumber:blockNumber
                                   completionHandler:^(NSData *resp, NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[[NSNull null], [self dataToArray:resp]]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_extendedWriteSingleBlock:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t blockNumber = [[options objectForKey:@"blockNumber"] unsignedIntValue];
        NSData *dataBlock = [self arrayToData:[options mutableArrayValueForKey:@"dataBlock"]];
        
        [tag extendedWriteSingleBlockWithRequestFlags:flags
                                  blockNumber:blockNumber
                                    dataBlock: dataBlock
                           completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

RCT_EXPORT_METHOD(iso15693_extendedLockBlock:(NSDictionary *)options callback:(nonnull RCTResponseSenderBlock)callback)
{
    nfcSafeExecute(callback, ^{
    if (@available(iOS 13.0, *)) {
        if (!sessionEx || !sessionEx.connectedTag) {
            callback(@[@"Not connected", [NSNull null]]);
            return;
        }
        
        id<NFCISO15693Tag> tag = [sessionEx.connectedTag asNFCISO15693Tag];
        if (!tag) {
            callback(@[@"incorrect tag type", [NSNull null]]);
            return;
        }

        RequestFlag flags = [[options objectForKey:@"flags"] unsignedIntValue];
        uint8_t blockNumber = [[options objectForKey:@"blockNumber"] unsignedIntValue];
        
        [tag extendedLockBlockWithRequestFlags:flags
                                  blockNumber:blockNumber
                           completionHandler:^(NSError *error) {
            if (error) {
                callback(@[getErrorMessage(error), [NSNull null]]);
                return;
            }
            
            callback(@[]);
        }];
    } else {
        callback(@[@"Not support in this device", [NSNull null]]);
    }
    });
}

@end
  
