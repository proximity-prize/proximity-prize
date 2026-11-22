import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptBase
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup5 -- serialize candidate build

namespace Low51EdgeRankReceipt
set_option maxRecDepth 16000

private inductive PrefixTree where
  | leaf (width value : Nat)
  | branch (zero one : PrefixTree)

private def PrefixTree.read : PrefixTree → Nat → Nat × Nat × Nat
  | .leaf width value, bits => (width, value, bits)
  | .branch zero one, bits =>
    if bits % 2 = 0 then zero.read (bits / 2) else one.read (bits / 2)

def receiptTree : PrefixTree :=
  .branch
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch (.leaf 8 49) (.leaf 8 131))
            (.branch
              (.branch
                (.branch
                  (.leaf 16 5910)
                  (.branch (.leaf 16 21827) (.leaf 88 27970066837786437574052025)))
                (.branch (.leaf 11 1127) (.leaf 11 1592)))
              (.branch
                (.leaf 14 4864)
                (.branch
                  (.leaf 16 9747)
                  (.branch
                    (.leaf 14 8960)
                    (.branch
                      (.leaf 11 1169)
                      (.branch
                        (.branch
                          (.branch (.branch (.leaf 41 980738019650) (.leaf 14 6147)) (.leaf 48 0))
                          (.leaf 27 12099731))
                        (.leaf 11 375))))))))
          (.branch
            (.branch (.leaf 8 64) (.leaf 8 101))
            (.branch
              (.leaf 11 823)
              (.branch
                (.branch (.branch (.leaf 11 268) (.leaf 19 218902)) (.leaf 11 146))
                (.branch (.leaf 19 34071) (.branch (.leaf 11 1283) (.leaf 16 29456)))))))
        (.branch
          (.branch
            (.branch
              (.leaf 8 134)
              (.branch
                (.branch
                  (.branch (.leaf 19 222998) (.branch (.leaf 11 343) (.leaf 22 571671)))
                  (.leaf 3 6))
                (.branch (.branch (.leaf 11 395) (.leaf 19 33591)) (.leaf 14 7424))))
            (.branch
              (.branch
                (.branch (.leaf 16 9266) (.branch (.leaf 24 1319441) (.leaf 11 914)))
                (.leaf 11 131))
              (.leaf 11 807)))
          (.branch
            (.branch
              (.branch
                (.branch (.branch (.leaf 27 8656678) (.leaf 16 5685)) (.leaf 11 514))
                (.branch (.leaf 16 13635) (.leaf 11 260)))
              (.branch
                (.branch
                  (.branch
                    (.leaf 11 1044)
                    (.branch (.leaf 22 659762) (.branch (.leaf 11 697) (.leaf 12 0))))
                  (.leaf 16 22051))
                (.leaf 8 112)))
            (.branch
              (.branch
                (.leaf 16 5170)
                (.branch (.branch (.leaf 19 206403) (.leaf 19 272406)) (.leaf 11 658)))
              (.leaf 8 20)))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.branch (.leaf 16 30486) (.leaf 16 9781)) (.leaf 19 34087))
                (.leaf 11 583))
              (.leaf 11 1320))
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf 19 41235) (.leaf 19 202323))
                  (.branch (.leaf 11 1028) (.leaf 16 9765)))
                (.leaf 8 146))
              (.branch
                (.branch
                  (.leaf 16 25360)
                  (.branch (.leaf 22 1083793) (.branch (.leaf 17 34819) (.leaf 11 529))))
                (.branch
                  (.branch (.leaf 19 210726) (.leaf 69 226353346175006164104))
                  (.leaf 14 6912)))))
          (.branch
            (.branch
              (.branch
                (.leaf 8 87)
                (.branch (.leaf 16 14102) (.branch (.leaf 14 8448) (.leaf 8 210))))
              (.leaf 8 85))
            (.branch
              (.branch (.leaf 3 5) (.leaf 8 114))
              (.branch (.leaf 16 9763) (.leaf 11 1080)))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.branch (.leaf 19 268342) (.leaf 19 214806)) (.leaf 16 8721))
                (.branch
                  (.branch
                    (.branch (.leaf 22 1128594) (.branch (.leaf 14 10240) (.leaf 11 290)))
                    (.leaf 19 206662))
                  (.leaf 11 155)))
              (.branch (.leaf 11 1111) (.leaf 8 39)))
            (.branch
              (.branch
                (.branch (.leaf 16 17939) (.leaf 11 771))
                (.branch
                  (.leaf 16 9508)
                  (.branch (.branch (.leaf 44 1589914224825) (.leaf 11 185)) (.leaf 11 667))))
              (.branch (.leaf 8 80) (.branch (.leaf 8 55) (.leaf 11 630)))))
          (.branch
            (.branch
              (.branch
                (.branch (.leaf 16 9250) (.leaf 16 17699))
                (.branch
                  (.branch (.leaf 11 397) (.leaf 14 4355))
                  (.branch (.leaf 16 5218) (.leaf 16 13845))))
              (.branch
                (.branch (.leaf 11 566) (.leaf 47 36366062994568))
                (.branch
                  (.branch (.branch (.leaf 27 28383767) (.leaf 39 73301886088)) (.leaf 16 17700))
                  (.leaf 16 13619))))
            (.branch
              (.branch
                (.branch (.leaf 16 5667) (.branch (.leaf 16 17684) (.leaf 11 522)))
                (.branch
                  (.branch (.leaf 19 137030) (.leaf 19 276262))
                  (.branch
                    (.branch (.leaf 19 299394) (.leaf 11 178))
                    (.branch
                      (.leaf 11 913)
                      (.branch
                        (.branch
                          (.leaf 14 11008)
                          (.branch
                            (.branch
                              (.leaf 14 12800)
                              (.branch (.leaf 14 12544) (.branch (.leaf 8 213) (.leaf 8 215))))
                            (.leaf 19 168258)))
                        (.leaf 11 441))))))
              (.branch (.leaf 11 154) (.branch (.leaf 14 6400) (.leaf 16 5942))))))))
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch (.branch (.leaf 14 5120) (.leaf 8 48)) (.leaf 8 33))
            (.branch
              (.branch
                (.branch
                  (.branch (.branch (.leaf 16 26147) (.leaf 19 138039)) (.leaf 19 34119))
                  (.leaf 11 1096))
                (.leaf 11 1047))
              (.leaf 8 17)))
          (.branch
            (.branch
              (.branch
                (.leaf 8 133)
                (.branch
                  (.branch (.leaf 14 7936) (.branch (.leaf 8 56) (.leaf 44 4890060507705)))
                  (.branch (.leaf 8 194) (.leaf 19 141091))))
              (.leaf 8 115))
            (.branch (.leaf 11 1304) (.leaf 8 22))))
        (.branch
          (.branch
            (.branch
              (.branch (.leaf 11 792) (.leaf 16 5411))
              (.branch
                (.branch (.branch (.leaf 19 210742) (.leaf 16 25424)) (.leaf 8 227))
                (.branch
                  (.branch (.leaf 33 4368141073) (.branch (.leaf 8 72) (.leaf 11 275)))
                  (.leaf 16 4880))))
            (.branch
              (.branch
                (.branch
                  (.leaf 16 22035)
                  (.branch
                    (.branch (.leaf 11 569) (.branch (.leaf 22 1690425) (.leaf 3 0)))
                    (.leaf 11 532)))
                (.branch (.leaf 16 9555) (.branch (.leaf 16 25891) (.leaf 27 8656662))))
              (.branch
                (.branch
                  (.branch (.branch (.leaf 11 1667) (.leaf 14 1288)) (.leaf 19 136739))
                  (.branch (.branch (.leaf 19 72503) (.leaf 11 278)) (.leaf 11 269)))
                (.leaf 8 130))))
          (.branch
            (.branch
              (.branch
                (.branch (.branch (.leaf 11 1282) (.leaf 16 25105)) (.leaf 16 17683))
                (.leaf 14 4608))
              (.branch
                (.branch (.branch (.leaf 16 13651) (.leaf 16 17747)) (.leaf 16 5651))
                (.branch
                  (.branch (.branch (.leaf 19 66326) (.leaf 14 4867)) (.leaf 11 267))
                  (.branch
                    (.leaf 11 279)
                    (.branch (.leaf 22 1165881) (.leaf 88 86026854220002610700732985))))))
            (.branch
              (.branch
                (.branch
                  (.leaf 16 21264)
                  (.branch (.leaf 11 1078) (.branch (.leaf 11 1540) (.leaf 16 25376))))
                (.leaf 8 144))
              (.branch
                (.branch
                  (.branch (.leaf 16 9749) (.leaf 16 21360))
                  (.branch
                    (.branch
                      (.leaf 8 214)
                      (.branch
                        (.leaf 22 637239)
                        (.branch
                          (.leaf 8 197)
                          (.branch (.leaf 30 277451042) (.branch (.leaf 14 12288) (.leaf 30 411734338))))))
                    (.leaf 16 5475)))
                (.leaf 8 166))))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf 11 550) (.branch (.leaf 16 21811) (.leaf 19 33815)))
                (.leaf 16 5395))
              (.leaf 11 791))
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf 22 1161370) (.branch (.leaf 11 1794) (.leaf 19 197912)))
                  (.branch (.leaf 24 1315345) (.branch (.leaf 44 7845904157201) (.leaf 16 21312))))
                (.leaf 8 36))
              (.branch
                (.leaf 14 4096)
                (.branch
                  (.branch (.leaf 19 34103) (.leaf 88 47322329298525161949612345))
                  (.leaf 8 149)))))
          (.branch
            (.branch
              (.leaf 8 102)
              (.branch
                (.leaf 8 98)
                (.branch
                  (.leaf 16 17955)
                  (.branch (.leaf 19 268326) (.branch (.leaf 11 785) (.leaf 11 1425))))))
            (.branch
              (.leaf 8 38)
              (.branch
                (.leaf 8 135)
                (.branch
                  (.branch (.branch (.leaf 14 9728) (.leaf 11 1209)) (.leaf 11 162))
                  (.branch (.leaf 11 530) (.leaf 19 140819)))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.branch (.leaf 11 1411) (.leaf 11 1795)) (.leaf 19 206387))
                  (.branch
                    (.branch
                      (.branch
                        (.branch (.leaf 28 19006600) (.leaf 72 816649156533711815816))
                        (.leaf 44 3790011746745))
                      (.leaf 11 851))
                    (.leaf 11 786)))
                (.leaf 8 176))
              (.branch
                (.leaf 11 1095)
                (.branch (.branch (.leaf 19 202291) (.leaf 19 71187)) (.leaf 8 162))))
            (.branch
              (.leaf 8 54)
              (.branch
                (.branch
                  (.leaf 16 9539)
                  (.branch (.leaf 11 772) (.branch (.leaf 8 104) (.leaf 11 1156))))
                (.branch (.leaf 11 282) (.leaf 16 5459)))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf 11 266)
                  (.branch (.branch (.leaf 27 9995319) (.leaf 11 651)) (.leaf 19 202307)))
                (.leaf 16 5138))
              (.leaf 3 4))
            (.branch
              (.branch (.leaf 8 50) (.leaf 11 870))
              (.branch
                (.branch
                  (.branch (.branch (.leaf 11 1155) (.leaf 19 66390)) (.leaf 11 644))
                  (.branch (.leaf 11 902) (.leaf 8 165)))
                (.leaf 16 5154))))))))
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.leaf 14 4352)
                (.branch
                  (.branch
                    (.leaf 16 25875)
                    (.branch (.leaf 88 66674591759263886325172665) (.leaf 11 650)))
                  (.leaf 11 1352)))
              (.leaf 8 83))
            (.branch
              (.branch
                (.leaf 8 81)
                (.branch
                  (.branch (.branch (.leaf 11 1094) (.leaf 19 66342)) (.leaf 16 16913))
                  (.leaf 16 13843)))
              (.leaf 8 19)))
          (.branch
            (.branch (.leaf 8 118) (.branch (.leaf 8 240) (.leaf 11 1079)))
            (.branch (.leaf 8 70) (.leaf 11 1048))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf 16 5139)
                  (.branch
                    (.branch (.leaf 16 5155) (.leaf 27 11606839))
                    (.branch (.leaf 55 11562611989055633) (.leaf 11 327))))
                (.leaf 11 854))
              (.branch (.branch (.leaf 14 6656) (.leaf 16 4625)) (.leaf 16 5186)))
            (.branch
              (.branch
                (.branch
                  (.leaf 11 515)
                  (.branch (.leaf 19 33831) (.branch (.leaf 16 29201) (.leaf 19 157219))))
                (.leaf 8 34))
              (.leaf 8 69)))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf 16 13072)
                  (.branch
                    (.leaf 36 9198388360)
                    (.branch
                      (.branch (.leaf 22 1346065) (.branch (.leaf 8 199) (.leaf 14 2961)))
                      (.leaf 19 132376))))
                (.branch
                  (.branch (.branch (.leaf 19 280342) (.leaf 11 1923)) (.leaf 19 141075))
                  (.branch
                    (.branch (.leaf 14 9216) (.leaf 27 8664854))
                    (.branch (.leaf 88 42181884582391438287354135) (.leaf 19 202566)))))
              (.leaf 3 2))
            (.branch
              (.branch (.leaf 8 117) (.leaf 8 66))
              (.branch (.branch (.leaf 16 10004) (.leaf 16 5412)) (.leaf 8 119))))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf 16 33552) (.leaf 80 539166428203673266177160))
                  (.branch
                    (.branch (.leaf 19 272438) (.leaf 22 1608337))
                    (.branch (.branch (.leaf 22 903609) (.leaf 11 825)) (.leaf 8 183))))
                (.branch
                  (.branch
                    (.branch (.leaf 11 1538) (.leaf 19 34135))
                    (.branch (.leaf 19 41362) (.leaf 24 1381395)))
                  (.leaf 16 9523)))
              (.branch
                (.branch
                  (.branch (.branch (.leaf 27 10172182) (.leaf 36 17954014344)) (.leaf 19 206646))
                  (.leaf 16 17168))
                (.branch
                  (.branch
                    (.branch (.leaf 19 276294) (.leaf 27 10523415))
                    (.branch
                      (.leaf 96 0)
                      (.branch
                        (.branch (.leaf 14 5635) (.branch (.leaf 19 102690) (.leaf 11 953)))
                        (.leaf 11 657))))
                  (.leaf 16 5443))))
            (.branch
              (.branch
                (.leaf 8 208)
                (.branch (.leaf 14 6144) (.branch (.leaf 14 8192) (.leaf 19 33559))))
              (.branch
                (.branch
                  (.branch
                    (.branch (.leaf 11 1297) (.leaf 16 21796))
                    (.branch (.leaf 19 210774) (.leaf 19 333845)))
                  (.branch (.branch (.leaf 22 2657425) (.leaf 36 4936975496)) (.leaf 11 539)))
                (.leaf 11 567))))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf 11 1026) (.leaf 11 808))
                  (.branch
                    (.branch (.leaf 11 147) (.leaf 16 45840))
                    (.branch (.leaf 19 136998) (.leaf 19 223014))))
                (.leaf 8 163))
              (.branch
                (.branch
                  (.branch
                    (.branch (.leaf 27 18383895) (.leaf 38 37331015446))
                    (.branch (.leaf 11 646) (.leaf 16 21408)))
                  (.leaf 16 9234))
                (.branch (.leaf 16 13603) (.leaf 8 211))))
            (.branch
              (.branch (.leaf 8 18) (.leaf 11 822))
              (.branch
                (.branch
                  (.branch (.leaf 14 4099) (.branch (.leaf 11 1042) (.leaf 19 105255)))
                  (.branch
                    (.branch (.leaf 19 137751) (.leaf 19 230680))
                    (.branch (.leaf 22 821521) (.leaf 27 10098486))))
                (.leaf 8 82)))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.leaf 8 224)
                (.branch
                  (.branch (.branch (.leaf 11 819) (.leaf 11 835)) (.leaf 11 598))
                  (.leaf 36 13459801224)))
              (.branch
                (.branch
                  (.leaf 19 39447)
                  (.branch
                    (.branch
                      (.leaf 19 149011)
                      (.branch
                        (.branch (.leaf 27 18487062) (.leaf 61 380731272064156808))
                        (.leaf 16 8608)))
                    (.branch (.leaf 11 1284) (.leaf 16 33648))))
                (.branch
                  (.branch
                    (.branch (.leaf 16 37712) (.leaf 19 206694))
                    (.branch (.leaf 19 214579) (.leaf 20 74240)))
                  (.branch (.leaf 8 198) (.leaf 19 268310)))))
            (.branch
              (.leaf 8 67)
              (.branch
                (.branch
                  (.branch (.branch (.leaf 27 35071507) (.leaf 8 113)) (.leaf 11 1335))
                  (.leaf 16 8976))
                (.branch
                  (.branch (.leaf 16 13604) (.leaf 16 17731))
                  (.branch
                    (.branch (.leaf 11 396) (.leaf 11 1143))
                    (.branch
                      (.branch
                        (.branch (.branch (.leaf 19 69906) (.leaf 19 135474)) (.leaf 44 2904749084962))
                        (.leaf 11 407))
                      (.leaf 14 8704)))))))
          (.branch
            (.branch
              (.branch (.leaf 8 160) (.branch (.leaf 14 5632) (.leaf 8 151)))
              (.branch
                (.branch
                  (.leaf 16 5427)
                  (.branch
                    (.branch (.leaf 19 214838) (.leaf 11 1041))
                    (.branch (.leaf 19 214595) (.leaf 19 268374))))
                (.branch
                  (.branch (.branch (.leaf 27 9995287) (.leaf 44 5645806635281)) (.leaf 14 7680))
                  (.leaf 16 5908))))
            (.branch
              (.branch
                (.leaf 11 551)
                (.branch
                  (.branch (.leaf 19 136982) (.branch (.leaf 16 9571) (.leaf 16 25907)))
                  (.branch
                    (.branch
                      (.leaf 22 2919697)
                      (.branch
                        (.branch
                          (.branch (.leaf 24 0) (.leaf 14 5891))
                          (.branch (.leaf 14 12032) (.leaf 33 1351192866)))
                        (.leaf 14 10496)))
                    (.leaf 16 5202))))
              (.branch (.leaf 11 838) (.branch (.leaf 11 259) (.leaf 16 13587))))))))
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf 8 86)
              (.branch
                (.branch
                  (.branch
                    (.branch (.leaf 11 311) (.leaf 14 4611))
                    (.branch (.leaf 16 29536) (.leaf 16 29987)))
                  (.branch
                    (.branch (.leaf 25 4473992) (.leaf 27 10168086))
                    (.branch (.leaf 33 673481864) (.leaf 44 5990109268665))))
                (.leaf 11 1336)))
            (.branch (.leaf 8 99) (.leaf 8 53)))
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf 11 615) (.branch (.leaf 16 34323) (.leaf 19 284438)))
                  (.branch
                    (.branch (.leaf 11 805) (.leaf 11 1553))
                    (.branch (.leaf 19 210483) (.leaf 16 21843))))
                (.leaf 8 192))
              (.leaf 8 37))
            (.branch
              (.branch
                (.branch
                  (.leaf 8 182)
                  (.branch (.leaf 11 402) (.branch (.leaf 11 291) (.leaf 24 1323537))))
                (.branch
                  (.branch
                    (.leaf 58 92500895912445064)
                    (.branch (.leaf 16 5137) (.leaf 27 10098470)))
                  (.branch
                    (.leaf 11 1560)
                    (.branch
                      (.leaf 19 41363)
                      (.branch
                        (.leaf 19 104580)
                        (.branch
                          (.branch
                            (.branch
                              (.branch
                                (.branch (.leaf 14 13056) (.branch (.leaf 14 6659) (.leaf 14 13568)))
                                (.leaf 14 6403))
                              (.leaf 14 11776))
                            (.leaf 11 354))
                          (.leaf 11 401)))))))
              (.branch
                (.leaf 11 1063)
                (.branch
                  (.leaf 11 133)
                  (.branch (.leaf 11 614) (.branch (.leaf 16 17957) (.leaf 19 218918))))))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.leaf 11 790)
                (.branch
                  (.branch (.leaf 8 88) (.branch (.leaf 44 2672774723895) (.leaf 22 1095834)))
                  (.branch
                    (.leaf 14 7168)
                    (.branch
                      (.branch (.leaf 19 72231) (.branch (.leaf 11 1081) (.leaf 14 11264)))
                      (.leaf 11 523)))))
              (.branch
                (.branch (.leaf 8 71) (.leaf 16 5653))
                (.branch
                  (.branch (.leaf 16 21795) (.branch (.leaf 44 2689962985785) (.leaf 19 66358)))
                  (.branch
                    (.branch (.leaf 19 165144) (.branch (.leaf 14 5123) (.leaf 19 39719)))
                    (.leaf 16 13588)))))
            (.branch
              (.branch (.leaf 8 32) (.leaf 8 65))
              (.branch
                (.branch (.branch (.leaf 11 411) (.leaf 16 17715)) (.leaf 16 10006))
                (.branch
                  (.branch
                    (.branch
                      (.leaf 16 13861)
                      (.branch (.leaf 11 273) (.branch (.leaf 8 40) (.leaf 22 702807))))
                    (.branch (.leaf 22 1952697) (.leaf 33 1221114010)))
                  (.leaf 16 9492)))))
          (.branch
            (.branch
              (.branch (.leaf 8 147) (.leaf 11 1064))
              (.branch
                (.branch
                  (.branch
                    (.branch
                      (.branch
                        (.branch
                          (.leaf 50 150122264806536)
                          (.branch (.branch (.leaf 19 233826) (.leaf 33 1485476162)) (.leaf 27 20488727)))
                        (.leaf 22 563475))
                      (.leaf 11 387))
                    (.branch (.leaf 27 8656694) (.leaf 19 272422)))
                  (.leaf 11 871))
                (.leaf 11 806)))
            (.branch
              (.branch
                (.branch (.leaf 19 72215) (.branch (.leaf 11 599) (.leaf 19 104983)))
                (.branch (.leaf 16 5396) (.leaf 16 13859)))
              (.leaf 8 51)))))
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.branch (.leaf 44 7090158029625) (.leaf 19 144915)) (.leaf 11 582))
                  (.leaf 8 195))
                (.branch
                  (.branch (.branch (.leaf 25 2655368) (.leaf 11 1539)) (.leaf 16 21009))
                  (.branch
                    (.branch (.branch (.leaf 39 82179277960) (.leaf 14 9984)) (.leaf 19 33895))
                    (.branch (.branch (.leaf 22 379065) (.leaf 22 596259)) (.leaf 11 313)))))
              (.branch
                (.leaf 11 855)
                (.branch
                  (.branch
                    (.branch (.leaf 16 5234) (.leaf 16 13232))
                    (.branch (.leaf 19 202355) (.leaf 19 214822)))
                  (.leaf 11 1576))))
            (.branch
              (.branch
                (.leaf 8 96)
                (.branch
                  (.branch
                    (.branch (.leaf 11 662) (.leaf 19 39799))
                    (.branch (.leaf 22 2214969) (.leaf 11 139)))
                  (.leaf 11 138)))
              (.branch
                (.branch
                  (.branch
                    (.leaf 11 1046)
                    (.branch
                      (.branch (.branch (.leaf 22 1428153) (.leaf 8 24)) (.leaf 14 1160))
                      (.leaf 6 8)))
                  (.branch (.leaf 11 770) (.branch (.leaf 19 202339) (.leaf 19 206710))))
                (.leaf 8 150))))
          (.branch
            (.branch
              (.branch
                (.branch (.branch (.leaf 11 516) (.leaf 19 206630)) (.leaf 11 283))
                (.branch
                  (.branch
                    (.branch (.leaf 36 12420942481) (.leaf 11 547))
                    (.branch (.leaf 16 29971) (.leaf 19 33911)))
                  (.leaf 14 5888)))
              (.branch
                (.leaf 11 132)
                (.branch
                  (.branch (.leaf 11 394) (.leaf 16 12817))
                  (.branch (.leaf 8 243) (.leaf 11 1062)))))
            (.branch
              (.leaf 3 3)
              (.branch
                (.branch
                  (.branch (.branch (.leaf 11 261) (.leaf 19 210499)) (.leaf 16 21779))
                  (.branch
                    (.branch
                      (.branch (.leaf 44 2947786914135) (.branch (.leaf 11 338) (.leaf 22 725330)))
                      (.leaf 16 5491))
                    (.branch (.leaf 19 206419) (.leaf 11 525))))
                (.leaf 3 1)))))
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch
                    (.leaf 8 178)
                    (.branch (.branch (.leaf 17 17544) (.leaf 25 6327185)) (.leaf 14 2070)))
                  (.leaf 16 9507))
                (.branch
                  (.branch
                    (.branch (.branch (.leaf 6 0) (.leaf 22 1870609)) (.leaf 11 900))
                    (.branch (.leaf 19 268358) (.leaf 22 641337)))
                  (.leaf 8 179)))
              (.branch
                (.leaf 8 35)
                (.branch
                  (.branch
                    (.leaf 11 1027)
                    (.branch
                      (.branch
                        (.branch (.branch (.leaf 11 295) (.leaf 19 37396)) (.leaf 11 322))
                        (.leaf 19 210515))
                      (.leaf 16 26131)))
                  (.leaf 8 97))))
            (.branch
              (.branch
                (.leaf 8 128)
                (.branch
                  (.branch (.leaf 8 167) (.leaf 11 274))
                  (.branch (.leaf 11 886) (.leaf 16 5926))))
              (.branch
                (.branch
                  (.branch
                    (.leaf 11 388)
                    (.branch
                      (.leaf 19 210758)
                      (.branch (.leaf 22 768375) (.branch (.leaf 14 10752) (.leaf 25 2393224)))))
                  (.leaf 14 5376))
                (.leaf 8 16))))
          (.branch
            (.branch (.branch (.leaf 11 839) (.leaf 11 535)) (.leaf 8 21))
            (.branch
              (.branch
                (.branch
                  (.branch
                    (.branch (.leaf 11 153) (.leaf 19 99608))
                    (.branch
                      (.branch
                        (.leaf 22 594194)
                        (.branch (.branch (.leaf 11 306) (.leaf 14 11520)) (.leaf 14 5379)))
                      (.leaf 16 5669)))
                  (.leaf 8 103))
                (.branch
                  (.branch
                    (.branch (.leaf 19 276278) (.branch (.leaf 14 9472) (.leaf 19 72263)))
                    (.branch (.leaf 11 140) (.leaf 11 141)))
                  (.branch (.branch (.leaf 11 1368) (.leaf 16 29488)) (.leaf 11 258))))
              (.branch
                (.branch (.leaf 8 23) (.leaf 16 9491))
                (.branch
                  (.branch
                    (.branch (.leaf 11 145) (.leaf 11 1608))
                    (.branch (.leaf 19 206678) (.leaf 22 1194138)))
                  (.branch
                    (.branch (.leaf 22 2395153) (.leaf 27 10098454))
                    (.branch (.branch (.leaf 44 2397762533655) (.leaf 8 181)) (.leaf 16 17296)))))))))))

private def restore : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, bits =>
    let (width, value, tail) := receiptTree.read bits
    value + (restore n tail <<< width)

/-- Restore the original witness bit stream. Its length occupies the first ten bits. -/
def packedSchedule (data : Nat) : Nat :=
  restore (data % 1024) (data / 1024)

end Low51EdgeRankReceipt
