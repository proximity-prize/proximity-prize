import ProximityPrize.SubmissionLower.E6970ReceiptBase

section Pack_E6970Receipt53

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt53_chunk0 := witnessA6966Final 53 60 0 990007 990076 32 3904
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk1 := witnessA6966Final 53 60 32 990077 990146 32 3776
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk2 := witnessA6966Final 53 60 64 990147 990215 32 3646
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk3 := witnessA6966Final 53 60 96 990216 990324 32 3718
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk4 := witnessA6966Final 53 60 128 990325 990397 32 3596
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk5 := witnessA6966Final 53 60 160 990398 990515 32 3408
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk6 := witnessA6966Final 53 60 192 990516 990592 32 3266
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk7 := witnessA6966Final 53 60 224 990640 990769 32 3184
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk8 := witnessA6966Final 53 60 256 990770 990905 32 2946
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk9 := witnessA6966Final 53 60 288 990960 991030 15 1299
  0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk10 := witnessRule 53 59 0 1000006 1000075 32 3726
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk11 := witnessRule 53 59 32 1000076 1000144 32 3576
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk12 := witnessRule 53 59 64 1000145 1000213 32 3476
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk13 := witnessRule 53 59 96 1000214 1000323 32 3446
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk14 := witnessRule 53 59 128 1000324 1000396 32 3366
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk15 := witnessRule 53 59 160 1000397 1000515 32 3174
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk16 := witnessRule 53 59 192 1000516 1000640 32 3044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk17 := witnessRule 53 59 224 1000641 1000771 32 2938
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk18 := witnessRule 53 59 256 1000772 1000963 32 2698
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk19 := witnessRule 53 59 288 1000964 1001029 10 788
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk20 := witnessRule 53 58 0 1010005 1010073 32 3532
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk21 := witnessRule 53 58 32 1010074 1010142 32 3414
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk22 := witnessRule 53 58 64 1010143 1010211 32 3256
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk23 := witnessRule 53 58 96 1010212 1010322 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk24 := witnessRule 53 58 128 1010323 1010396 32 3152
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk25 := witnessRule 53 58 160 1010397 1010516 32 2956
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk26 := witnessRule 53 58 192 1010517 1010642 32 2822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk27 := witnessRule 53 58 224 1010643 1010774 32 2676
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk28 := witnessRule 53 58 256 1010775 1011024 32 2458
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk29 := witnessRule 53 58 288 1011025 1011029 5 370
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk30 := witnessRule 53 57 0 1020004 1020072 32 3382
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk31 := witnessRule 53 57 32 1020073 1020140 32 3228
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk32 := witnessRule 53 57 64 1020141 1020210 32 3046
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk33 := witnessRule 53 57 96 1020211 1020322 32 2958
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk34 := witnessRule 53 57 128 1020323 1020396 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk35 := witnessRule 53 57 160 1020397 1020517 32 2740
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk36 := witnessRule 53 57 192 1020518 1020644 32 2599
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk37 := witnessRule 53 57 224 1020645 1020777 32 2430
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk38 := witnessRule 53 57 256 1020778 1021028 31 2242
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk39 := witnessRule 53 56 0 1030003 1030070 32 3216
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk40 := witnessRule 53 56 32 1030071 1030139 32 3032
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk41 := witnessRule 53 56 64 1030140 1030209 32 2822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk42 := witnessRule 53 56 96 1030210 1030322 32 2739
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk43 := witnessRule 53 56 128 1030323 1030397 32 2674
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk44 := witnessRule 53 56 160 1030398 1030519 32 2544
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk45 := witnessRule 53 56 192 1030520 1030647 32 2395
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk46 := witnessRule 53 56 224 1030648 1030834 32 2279
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk47 := witnessRule 53 56 256 1030835 1031028 25 1734
  0x1fffbff 0xb99a (by decide +kernel)
private def pack_E6970Receipt53_chunk48 := witnessRule 53 55 0 1040002 1040069 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk49 := witnessRule 53 55 32 1040070 1040138 32 2815
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk50 := witnessRule 53 55 64 1040139 1040209 32 2616
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk51 := witnessRule 53 55 96 1040210 1040323 32 2568
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk52 := witnessRule 53 55 128 1040324 1040398 32 2451
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk53 := witnessRule 53 55 160 1040399 1040521 32 2368
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk54 := witnessRule 53 55 192 1040522 1040650 32 2250
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk55 := witnessRule 53 55 224 1040651 1040839 32 2179
  0xdfffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt53_chunk56 := witnessRule 53 55 256 1040840 1041027 18 1209
  0x3ffef 0xba1a (by decide +kernel)
private def pack_E6970Receipt53_chunk57 := witnessRule 53 54 0 1050001 1050068 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk58 := witnessRule 53 54 32 1050069 1050138 32 2633
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk59 := witnessRule 53 54 64 1050139 1050209 32 2433
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk60 := witnessRule 53 54 96 1050210 1050324 32 2409
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk61 := witnessRule 53 54 128 1050325 1050400 32 2279
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk62 := witnessRule 53 54 160 1050401 1050524 32 2226
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk63 := witnessRule 53 54 192 1050525 1050705 32 2146
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk64 := witnessRule 53 54 224 1050706 1050900 32 2096
  0xdf3f6fff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt53_chunk65 := witnessRule 53 54 256 1050901 1051027 11 718
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk66 := witnessRule 53 53 0 1060000 1060068 32 2815
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk67 := witnessRule 53 53 32 1060069 1060138 32 2442
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk68 := witnessRule 53 53 64 1060139 1060210 32 2287
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk69 := witnessRule 53 53 96 1060211 1060326 32 2263
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk70 := witnessRule 53 53 128 1060327 1060448 32 2155
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk71 := witnessRule 53 53 160 1060449 1060576 32 2113
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk72 := witnessRule 53 53 192 1060577 1060710 32 2059
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt53_chunk73 := witnessRule 53 53 224 1060711 1060964 32 2023
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt53_chunk74 := witnessRule 53 53 256 1061024 1061026 3 192
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk75 := witnessRule 53 52 0 1070000 1070068 32 2637
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk76 := witnessRule 53 52 32 1070069 1070139 32 2286
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk77 := witnessRule 53 52 64 1070140 1070211 32 2161
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk78 := witnessRule 53 52 96 1070212 1070328 32 2141
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk79 := witnessRule 53 52 128 1070329 1070451 32 2064
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk80 := witnessRule 53 52 160 1070452 1070580 32 2014
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk81 := witnessRule 53 52 192 1070581 1070769 32 1975
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt53_chunk82 := witnessRule 53 52 224 1070770 1071026 27 1660
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt53_chunk83 := witnessRule 53 51 0 1080000 1080069 32 2486
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk84 := witnessRule 53 51 32 1080070 1080140 32 2154
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk85 := witnessRule 53 51 64 1080141 1080213 32 2053
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk86 := witnessRule 53 51 96 1080256 1080331 32 2044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk87 := witnessRule 53 51 128 1080332 1080455 32 1971
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk88 := witnessRule 53 51 160 1080456 1080585 32 1928
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt53_chunk89 := witnessRule 53 51 192 1080586 1080775 32 1902
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt53_chunk90 := witnessRule 53 51 224 1080832 1081025 18 1080
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt53_chunk91 := witnessRule 53 50 0 1090000 1090069 32 2334
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk92 := witnessRule 53 50 32 1090070 1090141 32 2046
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk93 := witnessRule 53 50 64 1090142 1090257 32 1969
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk94 := witnessRule 53 50 96 1090258 1090333 32 1933
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk95 := witnessRule 53 50 128 1090334 1090458 32 1886
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk96 := witnessRule 53 50 160 1090459 1090641 32 1855
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt53_chunk97 := witnessRule 53 50 192 1090642 1090837 32 1839
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt53_chunk98 := witnessRule 53 50 224 1090896 1091025 10 592
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk99 := witnessRule 53 49 0 1100000 1100070 32 2198
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk100 := witnessRule 53 49 32 1100071 1100142 32 1941
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk101 := witnessRule 53 49 64 1100143 1100259 32 1881
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk102 := witnessRule 53 49 96 1100260 1100336 32 1835
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk103 := witnessRule 53 49 128 1100337 1100462 32 1809
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt53_chunk104 := witnessRule 53 49 160 1100512 1100646 32 1790
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt53_chunk105 := witnessRule 53 49 192 1100647 1100962 32 1799
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt53_chunk106 := witnessRule 53 49 224 1101024 1101024 1 59
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk107 := witnessRule 53 48 0 1110000 1110070 32 2068
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk108 := witnessRule 53 48 32 1110071 1110143 32 1850
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk109 := witnessRule 53 48 64 1110144 1110261 32 1797
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk110 := witnessRule 53 48 96 1110262 1110385 32 1755
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt53_chunk111 := witnessRule 53 48 128 1110386 1110515 32 1741
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt53_chunk112 := witnessRule 53 48 160 1110516 1110705 32 1719
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt53_chunk113 := witnessRule 53 48 192 1110706 1111024 25 1376
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk114 := witnessRule 53 47 0 1120000 1120071 32 1956
  0xffffff3f 0x29ccd5b8a2 (by decide +kernel)
private def pack_E6970Receipt53_chunk115 := witnessRule 53 47 32 1120072 1120144 32 1758
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk116 := witnessRule 53 47 64 1120145 1120263 32 1718
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk117 := witnessRule 53 47 96 1120264 1120388 32 1686
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt53_chunk118 := witnessRule 53 47 128 1120389 1120519 32 1667
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt53_chunk119 := witnessRule 53 47 160 1120520 1120711 32 1664
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt53_chunk120 := witnessRule 53 47 192 1120768 1120961 16 867
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk121 := witnessRule 53 46 0 1130000 1130071 32 1850
  0xaffff57f 0x4b8b21bb714136ee8c66e1c990dcba9a (by decide +kernel)
private def pack_E6970Receipt53_chunk122 := witnessRule 53 46 32 1130072 1130145 32 1676
  0xfff5fffe 0x12e4c66e9d0d439b19b (by decide +kernel)
private def pack_E6970Receipt53_chunk123 := witnessRule 53 46 64 1130146 1130265 32 1647
  0xb6bfffd7 0x15d98cdbba319b97263374e86a9c58cde38a2 (by decide +kernel)
private def pack_E6970Receipt53_chunk124 := witnessRule 53 46 96 1130266 1130391 32 1617
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt53_chunk125 := witnessRule 53 46 128 1130392 1130523 32 1599
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt53_chunk126 := witnessRule 53 46 160 1130576 1130773 32 1628
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt53_chunk127 := witnessRule 53 46 192 1130832 1130960 8 429
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk128 := witnessRule 53 45 0 1140000 1140072 32 1759
  0x57ff551f 0x1dcd94dd3930a884b715131088f0c66d5d990db3a329b9736151094e2c2a262169c54cddb922 (by decide +kernel)
private def pack_E6970Receipt53_chunk129 := witnessRule 53 45 32 1140073 1140146 32 1594
  0xffaabff5 0xcecc66ddd190dc39329bb716151098e2495dd8cdb3ab21b (by decide +kernel)
private def pack_E6970Receipt53_chunk130 := witnessRule 53 45 64 1140147 1140267 32 1579
  0x920edb41 0xde190da3c319b5766436cecc66ddd190dc39b1988487265372e2c862125d8d0bdb19b3796336aeec66ddd58cdc39b21b9726331092e2ca6c629c584e0c5b883 (by decide +kernel)
private def pack_E6970Receipt53_chunk131 := witnessRule 53 45 96 1140268 1140394 32 1549
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt53_chunk132 := witnessRule 53 45 128 1140395 1140580 32 1546
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt53_chunk133 := witnessRule 53 45 160 1140581 1140960 32 1610
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk134 := witnessRule 53 44 0 1150000 1150072 32 1671
  0x1f5501f 0x21d18544c42c39b0a99c9726152310b2e2c2a872dc5895db8a8a09cb7141262f8c66c9e990d9bc329b677615108eeac2a26215dd1854ce439b0a918858726154394e4c4ae5c554ddb9289b (by decide +kernel)
private def pack_E6970Receipt53_chunk135 := witnessRule 53 44 32 1150073 1150147 32 1521
  0xed140f55 0x17c63366f4c66d1e190dabbb1988457665370eac2a2125cd8544c42cb930a99ca716152310b4e2a86c62dc55db8a09327b63366f2c86d1dd94dbbb30a884 (by decide +kernel)
private def pack_E6970Receipt53_chunk136 := witnessRule 53 44 64 1150192 1150269 32 1511
  0x80039200 0x5e994d93d321b3796331086f0ca6d1e190dabbb198845766536ceac862119d198dbb9b2988477267370e2cc62121e0d0bdb21b27b63366f2c86d1e58cdabbb21b676633108ceaca6ddd190c423b9b31b188736238312e4c26214625c58ce0c5391884 (by decide +kernel)
private def pack_E6970Receipt53_chunk137 := witnessRule 53 44 96 1150270 1150397 32 1487
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt53_chunk138 := witnessRule 53 44 128 1150448 1150584 32 1499
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt53_chunk139 := witnessRule 53 44 160 1150640 1150897 24 1186
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk140 := witnessRule 53 43 0 1160000 1160073 32 1589
  0x750007 0x6756154390eac4addcd8554e4b9b1289ca726251094e2c4a472dc944c42638a893b72258ca68ded8544223cb0a89885478615338aeec2a462155d98550e3bb312b6746155390e8c4a2725cd894424b931291ca716251310b4e4a66edc5491db912 (by decide +kernel)
private def pack_E6970Receipt53_chunk141 := witnessRule 53 43 32 1160074 1160193 32 1460
  0x38200628 0x188716538312e862105f190d93db1988427a65366f2c86210de198db3bb0a89885676615338eeac2a46215dd18550e439b0a99885872615538312e4c2a274629c5854428c538a91cc714127ac8685f18cc420bdb29b47a615108af0c2a262155dd854ce33b30a91885 (by decide +kernel)
private def pack_E6970Receipt53_chunk142 := witnessRule 53 43 64 1160194 1160271 32 1434
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4786431088eecc6d5d994c422bab39b18675633830ee8c4621461dcd90e0c439319885 (by decide +kernel)
private def pack_E6970Receipt53_chunk143 := witnessRule 53 43 96 1160320 1160451 32 1438
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt53_chunk144 := witnessRule 53 43 128 1160452 1160644 32 1459
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt53_chunk145 := witnessRule 53 43 160 1160645 1160896 16 779
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk146 := witnessRule 53 42 0 1170000 1170073 32 1507
  0x500003 0x776625108eeac4a4721d18944c42c39b1299c9726252310b2e2c4a870629c58965b928a09cc7225ec2a20c5f58544c428be30a99c27b6152310a4f4c2a8711e98959bc30aa9c578625138ceec4a2119d98948e3bab12898857746253390e6c4a462161c98950e53931ab97255376e6a26f1c89538a113 (by decide +kernel)
private def pack_E6970Receipt53_chunk147 := witnessRule 53 42 32 1170074 1170194 32 1398
  0x18000280 0x1877265310a30ee2ce70621d8c426b21883c66342f6ca62105e99cd9bd30a99c4796152310a8f0c2a8715dd854cc42abb30aa9c6756154310ace8c2ac7061dd18548e8c439b0a898861887261533a312e2c2a46218625c550e145388bd6153364f8c2a262149ed854ce1bd30a918853796154388f0c2a662151dd8554e33bb1289c (by decide +kernel)
private def pack_E6970Receipt53_chunk148 := witnessRule 53 42 64 1170195 1170321 32 1375
  0x3e003800 0x4716d36af8620c5e99cd93cb3188427868366eece6210dd9a4da3ab418844746a36ae6d262115c9acdb38b5188467c342f8c862105ed98d93d32988427967366f0cc6210ddda0d8c23bb21c1857663310a30aeaca70619d190c428c339b31c (by decide +kernel)
private def pack_E6970Receipt53_chunk149 := witnessRule 53 42 96 1170322 1170454 32 1377
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt53_chunk150 := witnessRule 53 42 128 1170455 1170706 32 1437
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk151 := witnessRule 53 42 160 1170707 1170896 9 434
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk152 := witnessRule 53 41 0 1180000 1180074 32 1430
  0x3 0x15dd894ce33b31291885675625438ee8c4a66215dcd8954e0c439b1289d1897262510a312e2c4a474629c944c428c5b8a894b714227cc4a26f5854cc42630aa9b27c6251386f6c4a210de98948e23cb1289885478625338aeec4a462155d98950e3bb31ab6746255390e8c6a2725cd8d4424b931a91ca716351310b4e6a66edc9491db8a113 (by decide +kernel)
private def pack_E6970Receipt53_chunk153 := witnessRule 53 41 32 1180075 1180196 32 1336
  0x6000100 0xc2ba33188518573683830ce4ce6214619c5a4e0c3bc1884c6155362f8c2a8709ed854cc4293d30aa9c3796154310a6f0c2ac711dd8554c42a3b30ab9c1857661533a30ceac2a46218619d18550e8c3b9b0a998861877261553a310e2c2a86218621c558e1c4391be61523109ac2a86c5f1854cc428bdb0aa9c27a6154310a4f2c2ac711e58948e2bc31289885 (by decide +kernel)
private def pack_E6970Receipt53_chunk154 := witnessRule 53 41 64 1180197 1180324 32 1316
  0x7e00e40 0x9d1b0c42139b71b3726d31086e2de6d1f8c418bc351b2776931084ecd66cdd5a8c421ba361b4736b31088e4da6d5c5b0c422bf1ac6631076d0685e5a4d8c13cb29c1837864310a306eecc70611d994c428c23ab39c (by decide +kernel)
private def pack_E6970Receipt53_chunk155 := witnessRule 53 41 96 1180325 1180458 32 1328
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt53_chunk156 := witnessRule 53 41 128 1180512 1180832 32 1428
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk157 := witnessRule 53 41 160 1180833 1180833 1 48
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk158 := witnessRule 53 40 0 1190000 1190074 32 1353
  0x3 0x11dd8954e2bb312a188557562563830ceac4a47461dd18944c430c3b9b1299d188726252310c310e2c4a874625c94cc42944b8a8a09dc714227cc4a40f98948d8beb128988517c6253384f6c4a462149e98950e1bcb1299885378625538af0c6a2719dd8d44233b31a91c7756351310aee8c6a6721cd8d48c42c3931aa1c1897263592e6aa6c629cd44e638a913 (by decide +kernel)
private def pack_E6970Receipt53_chunk159 := witnessRule 53 40 32 1190075 1190197 32 1274
  0x3000080 0xc1bab49c1847468310a308e6d470615c9a4c428c2b8b59c1867a3109ac2a8621318558d8bdb0aa988517a6157384f2c2ac62149e18560e0c1bc30aa1d184776153310c308ecc2aa74615d58550c430c2ba30ab1d186736155310c30ce4c2ae74e19c98ce1c3b8b118853877437ac4a66f18554c425b0ab9b27b6253386f4c4a46214de58950e23c31299885 (by decide +kernel)
private def pack_E6970Receipt53_chunk160 := witnessRule 53 40 64 1190198 1190326 32 1257
  0xe1fe03b0 0x1736400d9393798842716440d9ba00620c5d9b4d93ab618842746e366e6da6210dc9bcda38b7188447400d5b0ab9b181796738304f0cc6214609dda0e0c1bb339885 (by decide +kernel)
private def pack_E6970Receipt53_chunk161 := witnessRule 53 40 96 1190327 1190515 32 1296
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt53_chunk162 := witnessRule 53 40 128 1190516 1190832 26 1140
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk163 := witnessRule 53 39 0 1200000 1200075 32 1281
  0x1 0x6f0c4aa6214ddd895ce0c23bb1299d185766252310c30aeac4a874619d1894cc430c339b12a9d187726254310c30ee2c4ac74e1dc58548e9c438a8988528a712119cc4a264135894cc426312a9b17b6254310a2f4c4ac70de98d48e23cb1a89885478635338aeec6a462155d98d50e33ab1a9988567463553830ee8c6a274621cd8d4428c43931a91d189716351310c312e6a670629c949263992 (by decide +kernel)
private def pack_E6970Receipt53_chunk164 := witnessRule 53 39 32 1200076 1200199 32 1211
  0xc00040 0xc0bbb51c1827669310a304ead67060dd1a8c428c1b9b61c184726b310a308e2da70615f0c426312a9bb615731094c2b26c605e98554e8c13cb0aa18861827861563a306eec2aa621860dd9855ce8c23ab0ab18861847461583a708e8c870e15cd8cc429c2b9329c3867164310a70cec6f58948c826b12a1b17c6253310a2f6c4aa709e98950c4293cb12b1c (by decide +kernel)
private def pack_E6970Receipt53_chunk165 := witnessRule 53 39 64 1200200 1200329 32 1207
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt53_chunk166 := witnessRule 53 39 96 1200330 1200519 32 1272
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk167 := witnessRule 53 39 128 1200576 1200832 19 821
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk168 := witnessRule 53 38 0 1210000 1210075 32 1208
  0x1 0x304f2c4a87460de1894cc430c1bbb12a9d184766254310c308eac4ac74615d18954c430c2b9b12b9d3857361533a70ce4c2a46218e19c58550e9c3b8a998853887141311bcc4a80f58d48c42631aa1b17c6353384f6c6a462149e98d50e1bcb1a998853786355388eec6a862151d98d58e0c2bb31a91d186756351310c30ce8c6a67461dcd8d48c430c3b931aa1d188716353310c310e6aa70e21c944e0c5b8a914 (by decide +kernel)
private def pack_E6970Receipt53_chunk169 := witnessRule 53 38 32 1210076 1210200 32 1151
  0xe0604020 0xc0bab69c182746c310a304e6dc7060dc9b4c428c1b8b79c1847e31098c4a86412d8958c420c5b0aa988518a615738302f2c2ac6218605e18560e8c13b30ac9d382766538706eac86214e0dd198e1c239b2988538472673870ae2cc6214e15e0deb1299904c625531096c4ae6c5e98958c428bcb12c1c (by decide +kernel)
private def pack_E6970Receipt53_chunk170 := witnessRule 53 38 64 1210201 1210331 32 1167
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt53_chunk171 := witnessRule 53 38 96 1210384 1210579 32 1253
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk172 := witnessRule 53 38 128 1210580 1210769 12 509
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk173 := witnessRule 53 37 0 1220000 1220076 32 1138
  0x1 0x302f4c4a86218605e58958e8c13c312a98861827762573a306ecc4ac621860dd58960e9c1bab0aa1d384746153310c708e6c2aa74e15c98550c431c2b8b0ab1d3867155310a90ce2867358d44cc26b1a99884c6355362f6c6a862145e98d58e13cb1aa9885278635738306f0c6a674611dd8d48c430c23b31aa1d185756353310c30ae8c6aa74619cd8d50c430c33931ab1d3867262523a70ee2c4a26218e1dc94ce144b8a9208d (by decide +kernel)
private def pack_E6970Receipt53_chunk174 := witnessRule 53 37 32 1220077 1220202 32 1095
  0xfe1ab010 0x181736400e0c139379885182716440e0c1ba006212d8954cc20c530ab1905188615a38702ecce70e09d598c429c13a341c3837367310a706e4d270e11c5a0c429c23d1bd625234098c6a86212d8d58d8c5b12a9c (by decide +kernel)
private def pack_E6970Receipt53_chunk175 := witnessRule 53 37 64 1220203 1220386 32 1137
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt53_chunk176 := witnessRule 53 37 96 1220387 1220642 32 1237
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk177 := witnessRule 53 37 128 1220643 1220768 5 210
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk178 := witnessRule 53 36 0 1230000 1230076 32 1070
  0x0 0x18a6256310a312c4b070605e1895cc430c0bbb12c9d3817761553a704ecc2a86218e09d58558e9c1ba30aa98863837361573a708e4c2ac6218e11c58560eac238b21c585733109ac6aa0f58d48cc26322a1bb635631094c6b06c605e98d50e8c13cb1a998861827863553a306eec6a8621860dd98d58e8c23ab1aa98861847463573a708e8c4a674e15cd8948c431c2b9312a1d386716253310c70ce4aa7121dc544c4694539108c (by decide +kernel)
private def pack_E6970Receipt53_chunk179 := witnessRule 53 36 32 1230077 1230203 32 1050
  0xffdffe08 0x302e2c981c381746a38704e6d26214e09c9ace1c1b8b518853837c378c6a66612d8d54c820c5b12a1905 (by decide +kernel)
private def pack_E6970Receipt53_chunk180 := witnessRule 53 36 64 1230204 1230389 32 1109
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk181 := witnessRule 53 36 96 1230390 1230768 31 1185
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk182 := witnessRule 53 35 0 1240000 1240077 32 1006
  0x800000 0x316c4a668146298954cc28c4b12b99051886259310a710c2aa6214e1d855ce1c0bb30ab18863817561583a704e6c2b275609cd94e2c1b9321885583716638b08ea621358d44d42632299904b64553108316c6a862146298d58e0c0bcb1aa98861817863573a304eec6ac6218609d98d60e9c13b312a1d383756253310c706e8c4aa74e11cd8950c431c239312b1d385716255310c70ae4ae71615c54ce1c439210c (by decide +kernel)
private def pack_E6970Receipt53_chunk183 := witnessRule 53 35 32 1240078 1240205 32 1011
  0xffffffc4 0x1c0b9369c382716c310a704fc6f18d48d425b1aa1a04 (by decide +kernel)
private def pack_E6970Receipt53_chunk184 := witnessRule 53 35 64 1240256 1240392 32 1085
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk185 := witnessRule 53 35 96 1240448 1240705 24 897
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk186 := witnessRule 53 34 0 1250000 1250077 32 949
  0xaac00000 0x6298950d428c4312c19853876156320a70ac2b471605cd9ce2c139331885582716838b06ee621358d5c1e32291a04b64543308316c6a666146298d54c828c4b1ab9885188635938710c4aa70e05dd8950c431c0bb312b1d382756255310c704e8c4ae74e0dcd8958c431c1b9312c1d5837261543ab08e2c2a66219611c554e2c338990c (by decide +kernel)
private def pack_E6970Receipt53_chunk187 := witnessRule 53 34 32 1250078 1250257 32 977
  0xfffffffa 0x3817400ddb1a99b04 (by decide +kernel)
private def pack_E6970Receipt53_chunk188 := witnessRule 53 34 64 1250258 1250450 32 1061
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk189 := witnessRule 53 34 96 1250451 1250704 18 657
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk190 := witnessRule 53 33 0 1260000 1260078 32 900
  0xfffa0000 0x1605c5a8e632289b04b64533508316c6a46a146298d50d028c4b1ab19851886358320a710c4a86414e1d8958c429c3312c1c381756257310c702e8c4b275605d18554eac139b0aa18865827261563ab06e2c2aa621960dc55ce34239988c (by decide +kernel)
private def pack_E6970Receipt53_chunk191 := witnessRule 53 33 32 1260079 1260259 32 948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk192 := witnessRule 53 33 64 1260260 1260454 32 1039
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk193 := witnessRule 53 33 96 1260512 1260704 12 431
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk194 := witnessRule 53 32 0 1270000 1270078 32 856
  0xfffe0004 0xc6458076c8a46e1062d8d44dc28c531a99b051896355350a310c6ae6814e21894cd029c3b12a99853866257320a70ac4b262156158554c42ac230ab9c581736156310cb02e4c2b075609c564e3c13a9b (by decide +kernel)
private def pack_E6970Receipt53_chunk195 := witnessRule 53 32 32 1270128 1270261 32 920
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk196 := witnessRule 53 32 64 1270262 1270515 32 1019
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk197 := witnessRule 53 32 96 1270516 1270641 6 211
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk198 := witnessRule 53 31 0 1280000 1280128 32 819
  0xffff5556 0xb64513908314c6a470146218d58d829c3b12a1a853856258330ab08c2ac64156098568e3c0bb9b (by decide +kernel)
private def pack_E6970Receipt53_chunk199 := witnessRule 53 31 32 1280129 1280263 32 892
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk200 := witnessRule 53 31 64 1280264 1280640 32 1006
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk201 := witnessRule 53 30 0 1290000 1290129 32 786
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk202 := witnessRule 53 30 32 1290130 1290265 32 863
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk203 := witnessRule 53 30 64 1290320 1290640 27 825
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk204 := witnessRule 53 29 0 1300000 1300130 32 756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk205 := witnessRule 53 29 32 1300131 1300322 32 838
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk206 := witnessRule 53 29 64 1300323 1300577 21 621
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk207 := witnessRule 53 28 0 1310000 1310131 32 725
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk208 := witnessRule 53 28 32 1310132 1310324 32 811
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk209 := witnessRule 53 28 64 1310325 1310576 16 459
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk210 := witnessRule 53 27 0 1320000 1320132 32 695
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk211 := witnessRule 53 27 32 1320133 1320384 32 787
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk212 := witnessRule 53 27 64 1320385 1320576 11 308
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk213 := witnessRule 53 26 0 1330000 1330133 32 664
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk214 := witnessRule 53 26 32 1330134 1330387 32 763
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk215 := witnessRule 53 26 64 1330388 1330513 6 163
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk216 := witnessRule 53 25 0 1340000 1340134 32 634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk217 := witnessRule 53 25 32 1340135 1340450 32 744
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk218 := witnessRule 53 25 64 1340512 1340512 1 27
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk219 := witnessRule 53 24 0 1350000 1350135 32 603
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk220 := witnessRule 53 24 32 1350136 1350512 29 649
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk221 := witnessRule 53 23 0 1360000 1360136 32 573
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk222 := witnessRule 53 23 32 1360192 1360449 24 513
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk223 := witnessRule 53 22 0 1370000 1370192 32 543
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk224 := witnessRule 53 22 32 1370193 1370448 20 407
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk225 := witnessRule 53 21 0 1380000 1380194 32 515
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk226 := witnessRule 53 21 32 1380195 1380448 16 311
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk227 := witnessRule 53 20 0 1390000 1390195 32 485
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk228 := witnessRule 53 20 32 1390196 1390385 12 221
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk229 := witnessRule 53 19 0 1400000 1400197 32 457
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk230 := witnessRule 53 19 32 1400256 1400384 8 141
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk231 := witnessRule 53 18 0 1410000 1410257 32 429
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk232 := witnessRule 53 18 32 1410258 1410384 5 84
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk233 := witnessRule 53 17 0 1420000 1420320 32 404
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk234 := witnessRule 53 17 32 1420321 1420321 1 16
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk235 := witnessRule 53 16 0 1430000 1430320 30 348
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk236 := witnessRule 53 15 0 1440000 1440320 27 285
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk237 := witnessRule 53 14 0 1450000 1450257 24 225
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk238 := witnessRule 53 13 0 1460000 1460256 21 174
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk239 := witnessRule 53 12 0 1470000 1470256 19 137
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk240 := witnessRule 53 11 0 1480000 1480193 16 97
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk241 := witnessRule 53 10 0 1490000 1490192 14 69
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk242 := witnessRule 53 9 0 1500000 1500192 12 47
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk243 := witnessRule 53 8 0 1510000 1510129 10 27
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk244 := witnessRule 53 7 0 1520000 1520128 8 13
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk245 := witnessRule 53 6 0 1530000 1530128 7 4
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk246 := witnessRule 53 5 0 1540000 1540065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk247 := witnessRule 53 4 0 1550000 1550064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk248 := witnessRule 53 3 0 1560000 1560064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk249 := witnessRule 53 2 0 1570000 1570001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk250 := witnessRule 53 1 0 1580000 1580000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt53_chunk251 := witnessRule 53 0 0 1590000 1590000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt53_chunks : List (Chunk 53) := [pack_E6970Receipt53_chunk0, pack_E6970Receipt53_chunk1, pack_E6970Receipt53_chunk2, pack_E6970Receipt53_chunk3, pack_E6970Receipt53_chunk4, pack_E6970Receipt53_chunk5, pack_E6970Receipt53_chunk6, pack_E6970Receipt53_chunk7, pack_E6970Receipt53_chunk8, pack_E6970Receipt53_chunk9, pack_E6970Receipt53_chunk10, pack_E6970Receipt53_chunk11, pack_E6970Receipt53_chunk12, pack_E6970Receipt53_chunk13, pack_E6970Receipt53_chunk14, pack_E6970Receipt53_chunk15, pack_E6970Receipt53_chunk16, pack_E6970Receipt53_chunk17, pack_E6970Receipt53_chunk18, pack_E6970Receipt53_chunk19, pack_E6970Receipt53_chunk20, pack_E6970Receipt53_chunk21, pack_E6970Receipt53_chunk22, pack_E6970Receipt53_chunk23, pack_E6970Receipt53_chunk24, pack_E6970Receipt53_chunk25, pack_E6970Receipt53_chunk26, pack_E6970Receipt53_chunk27, pack_E6970Receipt53_chunk28, pack_E6970Receipt53_chunk29, pack_E6970Receipt53_chunk30, pack_E6970Receipt53_chunk31, pack_E6970Receipt53_chunk32, pack_E6970Receipt53_chunk33, pack_E6970Receipt53_chunk34, pack_E6970Receipt53_chunk35, pack_E6970Receipt53_chunk36, pack_E6970Receipt53_chunk37, pack_E6970Receipt53_chunk38, pack_E6970Receipt53_chunk39, pack_E6970Receipt53_chunk40, pack_E6970Receipt53_chunk41, pack_E6970Receipt53_chunk42, pack_E6970Receipt53_chunk43, pack_E6970Receipt53_chunk44, pack_E6970Receipt53_chunk45, pack_E6970Receipt53_chunk46, pack_E6970Receipt53_chunk47, pack_E6970Receipt53_chunk48, pack_E6970Receipt53_chunk49, pack_E6970Receipt53_chunk50, pack_E6970Receipt53_chunk51, pack_E6970Receipt53_chunk52, pack_E6970Receipt53_chunk53, pack_E6970Receipt53_chunk54, pack_E6970Receipt53_chunk55, pack_E6970Receipt53_chunk56, pack_E6970Receipt53_chunk57, pack_E6970Receipt53_chunk58, pack_E6970Receipt53_chunk59, pack_E6970Receipt53_chunk60, pack_E6970Receipt53_chunk61, pack_E6970Receipt53_chunk62, pack_E6970Receipt53_chunk63, pack_E6970Receipt53_chunk64, pack_E6970Receipt53_chunk65, pack_E6970Receipt53_chunk66, pack_E6970Receipt53_chunk67, pack_E6970Receipt53_chunk68, pack_E6970Receipt53_chunk69, pack_E6970Receipt53_chunk70, pack_E6970Receipt53_chunk71, pack_E6970Receipt53_chunk72, pack_E6970Receipt53_chunk73, pack_E6970Receipt53_chunk74, pack_E6970Receipt53_chunk75, pack_E6970Receipt53_chunk76, pack_E6970Receipt53_chunk77, pack_E6970Receipt53_chunk78, pack_E6970Receipt53_chunk79, pack_E6970Receipt53_chunk80, pack_E6970Receipt53_chunk81, pack_E6970Receipt53_chunk82, pack_E6970Receipt53_chunk83, pack_E6970Receipt53_chunk84, pack_E6970Receipt53_chunk85, pack_E6970Receipt53_chunk86, pack_E6970Receipt53_chunk87, pack_E6970Receipt53_chunk88, pack_E6970Receipt53_chunk89, pack_E6970Receipt53_chunk90, pack_E6970Receipt53_chunk91, pack_E6970Receipt53_chunk92, pack_E6970Receipt53_chunk93, pack_E6970Receipt53_chunk94, pack_E6970Receipt53_chunk95, pack_E6970Receipt53_chunk96, pack_E6970Receipt53_chunk97, pack_E6970Receipt53_chunk98, pack_E6970Receipt53_chunk99, pack_E6970Receipt53_chunk100, pack_E6970Receipt53_chunk101, pack_E6970Receipt53_chunk102, pack_E6970Receipt53_chunk103, pack_E6970Receipt53_chunk104, pack_E6970Receipt53_chunk105, pack_E6970Receipt53_chunk106, pack_E6970Receipt53_chunk107, pack_E6970Receipt53_chunk108, pack_E6970Receipt53_chunk109, pack_E6970Receipt53_chunk110, pack_E6970Receipt53_chunk111, pack_E6970Receipt53_chunk112, pack_E6970Receipt53_chunk113, pack_E6970Receipt53_chunk114, pack_E6970Receipt53_chunk115, pack_E6970Receipt53_chunk116, pack_E6970Receipt53_chunk117, pack_E6970Receipt53_chunk118, pack_E6970Receipt53_chunk119, pack_E6970Receipt53_chunk120, pack_E6970Receipt53_chunk121, pack_E6970Receipt53_chunk122, pack_E6970Receipt53_chunk123, pack_E6970Receipt53_chunk124, pack_E6970Receipt53_chunk125, pack_E6970Receipt53_chunk126, pack_E6970Receipt53_chunk127, pack_E6970Receipt53_chunk128, pack_E6970Receipt53_chunk129, pack_E6970Receipt53_chunk130, pack_E6970Receipt53_chunk131, pack_E6970Receipt53_chunk132, pack_E6970Receipt53_chunk133, pack_E6970Receipt53_chunk134, pack_E6970Receipt53_chunk135, pack_E6970Receipt53_chunk136, pack_E6970Receipt53_chunk137, pack_E6970Receipt53_chunk138, pack_E6970Receipt53_chunk139, pack_E6970Receipt53_chunk140, pack_E6970Receipt53_chunk141, pack_E6970Receipt53_chunk142, pack_E6970Receipt53_chunk143, pack_E6970Receipt53_chunk144, pack_E6970Receipt53_chunk145, pack_E6970Receipt53_chunk146, pack_E6970Receipt53_chunk147, pack_E6970Receipt53_chunk148, pack_E6970Receipt53_chunk149, pack_E6970Receipt53_chunk150, pack_E6970Receipt53_chunk151, pack_E6970Receipt53_chunk152, pack_E6970Receipt53_chunk153, pack_E6970Receipt53_chunk154, pack_E6970Receipt53_chunk155, pack_E6970Receipt53_chunk156, pack_E6970Receipt53_chunk157, pack_E6970Receipt53_chunk158, pack_E6970Receipt53_chunk159, pack_E6970Receipt53_chunk160, pack_E6970Receipt53_chunk161, pack_E6970Receipt53_chunk162, pack_E6970Receipt53_chunk163, pack_E6970Receipt53_chunk164, pack_E6970Receipt53_chunk165, pack_E6970Receipt53_chunk166, pack_E6970Receipt53_chunk167, pack_E6970Receipt53_chunk168, pack_E6970Receipt53_chunk169, pack_E6970Receipt53_chunk170, pack_E6970Receipt53_chunk171, pack_E6970Receipt53_chunk172, pack_E6970Receipt53_chunk173, pack_E6970Receipt53_chunk174, pack_E6970Receipt53_chunk175, pack_E6970Receipt53_chunk176, pack_E6970Receipt53_chunk177, pack_E6970Receipt53_chunk178, pack_E6970Receipt53_chunk179, pack_E6970Receipt53_chunk180, pack_E6970Receipt53_chunk181, pack_E6970Receipt53_chunk182, pack_E6970Receipt53_chunk183, pack_E6970Receipt53_chunk184, pack_E6970Receipt53_chunk185, pack_E6970Receipt53_chunk186, pack_E6970Receipt53_chunk187, pack_E6970Receipt53_chunk188, pack_E6970Receipt53_chunk189, pack_E6970Receipt53_chunk190, pack_E6970Receipt53_chunk191, pack_E6970Receipt53_chunk192, pack_E6970Receipt53_chunk193, pack_E6970Receipt53_chunk194, pack_E6970Receipt53_chunk195, pack_E6970Receipt53_chunk196, pack_E6970Receipt53_chunk197, pack_E6970Receipt53_chunk198, pack_E6970Receipt53_chunk199, pack_E6970Receipt53_chunk200, pack_E6970Receipt53_chunk201, pack_E6970Receipt53_chunk202, pack_E6970Receipt53_chunk203, pack_E6970Receipt53_chunk204, pack_E6970Receipt53_chunk205, pack_E6970Receipt53_chunk206, pack_E6970Receipt53_chunk207, pack_E6970Receipt53_chunk208, pack_E6970Receipt53_chunk209, pack_E6970Receipt53_chunk210, pack_E6970Receipt53_chunk211, pack_E6970Receipt53_chunk212, pack_E6970Receipt53_chunk213, pack_E6970Receipt53_chunk214, pack_E6970Receipt53_chunk215, pack_E6970Receipt53_chunk216, pack_E6970Receipt53_chunk217, pack_E6970Receipt53_chunk218, pack_E6970Receipt53_chunk219, pack_E6970Receipt53_chunk220, pack_E6970Receipt53_chunk221, pack_E6970Receipt53_chunk222, pack_E6970Receipt53_chunk223, pack_E6970Receipt53_chunk224, pack_E6970Receipt53_chunk225, pack_E6970Receipt53_chunk226, pack_E6970Receipt53_chunk227, pack_E6970Receipt53_chunk228, pack_E6970Receipt53_chunk229, pack_E6970Receipt53_chunk230, pack_E6970Receipt53_chunk231, pack_E6970Receipt53_chunk232, pack_E6970Receipt53_chunk233, pack_E6970Receipt53_chunk234, pack_E6970Receipt53_chunk235, pack_E6970Receipt53_chunk236, pack_E6970Receipt53_chunk237, pack_E6970Receipt53_chunk238, pack_E6970Receipt53_chunk239, pack_E6970Receipt53_chunk240, pack_E6970Receipt53_chunk241, pack_E6970Receipt53_chunk242, pack_E6970Receipt53_chunk243, pack_E6970Receipt53_chunk244, pack_E6970Receipt53_chunk245, pack_E6970Receipt53_chunk246, pack_E6970Receipt53_chunk247, pack_E6970Receipt53_chunk248, pack_E6970Receipt53_chunk249, pack_E6970Receipt53_chunk250, pack_E6970Receipt53_chunk251]
def rows53 := rowsFrom pack_E6970Receipt53_chunks
theorem good53 : ∀ r ∈ rows53, good 53 r = true := rowsFrom_good pack_E6970Receipt53_chunks
theorem sorted53 : rows53.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt53_chunks 0 (by decide +kernel)).1
theorem mass53 (i : Fin 61) :
    bandCount 53 (i.val : ℤ) 60 16 ≤ (rows53.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt53_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 53 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt53_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total53 : (rows53.map (price 53)).sum = 397572 :=
  (total_eq pack_E6970Receipt53_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt53

section Pack_E6970Receipt54

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt54_chunk0 := witnessA6966Final 54 60 0 1020006 1020074 32 3934
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk1 := witnessA6966Final 54 60 32 1020075 1020143 32 3836
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk2 := witnessA6966Final 54 60 64 1020144 1020211 32 3728
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk3 := witnessA6966Final 54 60 96 1020212 1020320 32 3598
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk4 := witnessA6966Final 54 60 128 1020321 1020393 32 3684
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk5 := witnessA6966Final 54 60 160 1020394 1020467 32 3360
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk6 := witnessA6966Final 54 60 192 1020512 1020588 32 3386
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk7 := witnessA6966Final 54 60 224 1020589 1020715 32 3160
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk8 := witnessA6966Final 54 60 256 1020716 1020901 32 2994
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk9 := witnessA6966Final 54 60 288 1020902 1021030 19 1635
  0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk10 := witnessRule 54 59 0 1030005 1030073 32 3756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk11 := witnessRule 54 59 32 1030074 1030141 32 3630
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk12 := witnessRule 54 59 64 1030142 1030210 32 3512
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk13 := witnessRule 54 59 96 1030211 1030320 32 3362
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk14 := witnessRule 54 59 128 1030321 1030393 32 3432
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk15 := witnessRule 54 59 160 1030394 1030512 32 3144
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk16 := witnessRule 54 59 192 1030513 1030590 32 3106
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk17 := witnessRule 54 59 224 1030591 1030768 32 2924
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk18 := witnessRule 54 59 256 1030769 1030960 32 2734
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk19 := witnessRule 54 59 288 1030961 1031029 13 1037
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk20 := witnessRule 54 58 0 1040004 1040071 32 3558
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk21 := witnessRule 54 58 32 1040072 1040139 32 3466
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk22 := witnessRule 54 58 64 1040140 1040208 32 3292
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk23 := witnessRule 54 58 96 1040209 1040279 32 3106
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk24 := witnessRule 54 58 128 1040320 1040393 32 3224
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk25 := witnessRule 54 58 160 1040394 1040513 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk26 := witnessRule 54 58 192 1040514 1040591 32 2834
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk27 := witnessRule 54 58 224 1040640 1040771 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk28 := witnessRule 54 58 256 1040772 1040964 32 2476
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk29 := witnessRule 54 58 288 1040965 1041029 8 592
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk30 := witnessRule 54 57 0 1050003 1050070 32 3408
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk31 := witnessRule 54 57 32 1050071 1050138 32 3234
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk32 := witnessRule 54 57 64 1050139 1050208 32 3072
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk33 := witnessRule 54 57 96 1050209 1050320 32 2910
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk34 := witnessRule 54 57 128 1050321 1050394 32 2956
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk35 := witnessRule 54 57 160 1050395 1050515 32 2728
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk36 := witnessRule 54 57 192 1050516 1050642 32 2610
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk37 := witnessRule 54 57 224 1050643 1050775 32 2447
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk38 := witnessRule 54 57 256 1050776 1051027 32 2292
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk39 := witnessRule 54 57 288 1051028 1051028 1 70
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk40 := witnessRule 54 56 0 1060002 1060068 32 3238
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk41 := witnessRule 54 56 32 1060069 1060137 32 3042
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk42 := witnessRule 54 56 64 1060138 1060207 32 2848
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk43 := witnessRule 54 56 96 1060208 1060320 32 2694
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk44 := witnessRule 54 56 128 1060321 1060395 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk45 := witnessRule 54 56 160 1060396 1060517 32 2527
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk46 := witnessRule 54 56 192 1060518 1060645 32 2394
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk47 := witnessRule 54 56 224 1060646 1060832 32 2254
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk48 := witnessRule 54 56 256 1060833 1061028 27 1850
  0x7ffefff 0xb99a (by decide +kernel)
private def pack_E6970Receipt54_chunk49 := witnessRule 54 55 0 1070001 1070068 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk50 := witnessRule 54 55 32 1070069 1070137 32 2807
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk51 := witnessRule 54 55 64 1070138 1070208 32 2620
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk52 := witnessRule 54 55 96 1070209 1070322 32 2536
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk53 := witnessRule 54 55 128 1070323 1070397 32 2457
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk54 := witnessRule 54 55 160 1070398 1070520 32 2350
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk55 := witnessRule 54 55 192 1070521 1070649 32 2226
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk56 := witnessRule 54 55 224 1070650 1070838 32 2149
  0xbfffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt54_chunk57 := witnessRule 54 55 256 1070839 1071027 19 1256
  0x7ffdf 0xba1a (by decide +kernel)
private def pack_E6970Receipt54_chunk58 := witnessRule 54 54 0 1080000 1080067 32 2904
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk59 := witnessRule 54 54 32 1080068 1080137 32 2621
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk60 := witnessRule 54 54 64 1080138 1080208 32 2420
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk61 := witnessRule 54 54 96 1080209 1080323 32 2382
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk62 := witnessRule 54 54 128 1080324 1080399 32 2269
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk63 := witnessRule 54 54 160 1080400 1080523 32 2201
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk64 := witnessRule 54 54 192 1080524 1080704 32 2112
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk65 := witnessRule 54 54 224 1080705 1080899 32 2068
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt54_chunk66 := witnessRule 54 54 256 1080900 1081027 12 770
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk67 := witnessRule 54 53 0 1090000 1090068 32 2730
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk68 := witnessRule 54 53 32 1090069 1090138 32 2409
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk69 := witnessRule 54 53 64 1090139 1090210 32 2257
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk70 := witnessRule 54 53 96 1090211 1090326 32 2241
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk71 := witnessRule 54 53 128 1090327 1090448 32 2125
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk72 := witnessRule 54 53 160 1090449 1090576 32 2081
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk73 := witnessRule 54 53 192 1090577 1090710 32 2027
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt54_chunk74 := witnessRule 54 53 224 1090711 1090964 32 1991
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt54_chunk75 := witnessRule 54 53 256 1091024 1091026 3 189
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk76 := witnessRule 54 52 0 1100000 1100068 32 2548
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk77 := witnessRule 54 52 32 1100069 1100139 32 2245
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk78 := witnessRule 54 52 64 1100140 1100211 32 2127
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk79 := witnessRule 54 52 96 1100212 1100328 32 2111
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk80 := witnessRule 54 52 128 1100329 1100451 32 2032
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk81 := witnessRule 54 52 160 1100452 1100580 32 1982
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk82 := witnessRule 54 52 192 1100581 1100769 32 1943
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt54_chunk83 := witnessRule 54 52 224 1100770 1101026 27 1633
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt54_chunk84 := witnessRule 54 51 0 1110000 1110069 32 2394
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk85 := witnessRule 54 51 32 1110070 1110140 32 2107
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk86 := witnessRule 54 51 64 1110141 1110213 32 2016
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk87 := witnessRule 54 51 96 1110256 1110331 32 2012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk88 := witnessRule 54 51 128 1110332 1110455 32 1939
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk89 := witnessRule 54 51 160 1110456 1110585 32 1896
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt54_chunk90 := witnessRule 54 51 192 1110586 1110775 32 1870
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt54_chunk91 := witnessRule 54 51 224 1110832 1111025 18 1062
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt54_chunk92 := witnessRule 54 50 0 1120000 1120069 32 2246
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk93 := witnessRule 54 50 32 1120070 1120141 32 2001
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk94 := witnessRule 54 50 64 1120142 1120257 32 1934
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk95 := witnessRule 54 50 96 1120258 1120333 32 1901
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk96 := witnessRule 54 50 128 1120334 1120458 32 1854
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk97 := witnessRule 54 50 160 1120459 1120641 32 1823
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt54_chunk98 := witnessRule 54 50 192 1120642 1120837 32 1807
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt54_chunk99 := witnessRule 54 50 224 1120896 1121025 10 582
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk100 := witnessRule 54 49 0 1130000 1130070 32 2114
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk101 := witnessRule 54 49 32 1130071 1130142 32 1898
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk102 := witnessRule 54 49 64 1130143 1130259 32 1846
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk103 := witnessRule 54 49 96 1130260 1130336 32 1803
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk104 := witnessRule 54 49 128 1130337 1130462 32 1777
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt54_chunk105 := witnessRule 54 49 160 1130512 1130646 32 1758
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt54_chunk106 := witnessRule 54 49 192 1130647 1130962 32 1767
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt54_chunk107 := witnessRule 54 49 224 1131024 1131024 1 58
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk108 := witnessRule 54 48 0 1140000 1140070 32 1988
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk109 := witnessRule 54 48 32 1140071 1140143 32 1809
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk110 := witnessRule 54 48 64 1140144 1140261 32 1762
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk111 := witnessRule 54 48 96 1140262 1140385 32 1723
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt54_chunk112 := witnessRule 54 48 128 1140386 1140515 32 1709
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt54_chunk113 := witnessRule 54 48 160 1140516 1140705 32 1687
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt54_chunk114 := witnessRule 54 48 192 1140706 1141024 25 1351
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk115 := witnessRule 54 47 0 1150000 1150071 32 1880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk116 := witnessRule 54 47 32 1150072 1150144 32 1717
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk117 := witnessRule 54 47 64 1150145 1150263 32 1683
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk118 := witnessRule 54 47 96 1150264 1150388 32 1654
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt54_chunk119 := witnessRule 54 47 128 1150389 1150519 32 1635
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt54_chunk120 := witnessRule 54 47 160 1150520 1150711 32 1632
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt54_chunk121 := witnessRule 54 47 192 1150768 1150961 16 851
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk122 := witnessRule 54 46 0 1160000 1160071 32 1780
  0xd7fffebf 0xa7163378e28a5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt54_chunk123 := witnessRule 54 46 32 1160072 1160145 32 1633
  0xfffe7fff 0x2dccd638a2 (by decide +kernel)
private def pack_E6970Receipt54_chunk124 := witnessRule 54 46 64 1160146 1160265 32 1613
  0xb6bfffff 0x5766336ee8c66e5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt54_chunk125 := witnessRule 54 46 96 1160266 1160391 32 1585
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt54_chunk126 := witnessRule 54 46 128 1160392 1160523 32 1567
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt54_chunk127 := witnessRule 54 46 160 1160576 1160773 32 1596
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt54_chunk128 := witnessRule 54 46 192 1160832 1160960 8 421
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk129 := witnessRule 54 45 0 1170000 1170072 32 1692
  0xa9ffeaaf 0x439b21b97165378e2a20f1c4933b319b77464370e4ca6edc58544263892 (by decide +kernel)
private def pack_E6970Receipt54_chunk130 := witnessRule 54 45 32 1170073 1170146 32 1551
  0xfff57ffe 0x87463372e4c86e9d4d3bab19b (by decide +kernel)
private def pack_E6970Receipt54_chunk131 := witnessRule 54 45 64 1170147 1170267 32 1545
  0x920edb69 0x37864368f0c66d5d990db3b319b77464370e6c662121c994dcb8b21884976342f6c66cde58cdabbb19b77563372e6c66e9c590ddb99883 (by decide +kernel)
private def pack_E6970Receipt54_chunk132 := witnessRule 54 45 96 1170268 1170394 32 1517
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt54_chunk133 := witnessRule 54 45 128 1170395 1170580 32 1514
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt54_chunk134 := witnessRule 54 45 160 1170581 1170960 32 1578
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk135 := witnessRule 54 44 0 1180000 1180072 32 1607
  0xa1feaa07 0x12e8c2a2129c98544c42d38b0a99cb715231098e2a28cde98cda3c321b57665370eac2a2125cd8544c42cb930a99ca716152310b4e2a86f1c955b8a093 (by decide +kernel)
private def pack_E6970Receipt54_chunk136 := witnessRule 54 44 32 1180073 1180147 32 1479
  0xeda28fea 0xbe319b37a6336af0c66d9d990dbbab1988477465374e6c2a212dc58544c42db8a99bc72448f2c66d5dd90db3ab29b (by decide +kernel)
private def pack_E6970Receipt54_chunk137 := witnessRule 54 44 64 1180192 1180269 32 1477
  0x80039240 0xbd329b27a64366f2c66210de194da3c321b577633108aecca6d9d590c4233a331b773653108ee4ce6e1c598c4243c1a17b64364f6c66cde590da3cb19b5776436ceec66ddd590dc3a31988487365372e4c862125c598dd3a9883 (by decide +kernel)
private def pack_E6970Receipt54_chunk138 := witnessRule 54 44 96 1180270 1180397 32 1455
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt54_chunk139 := witnessRule 54 44 128 1180448 1180584 32 1467
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt54_chunk140 := witnessRule 54 44 160 1180640 1180897 24 1162
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk141 := witnessRule 54 43 0 1190000 1190073 32 1530
  0x6aa007 0xeecc2a26215dd5854ce43a30a918858736154394e6c4ae5c58554e5b8b1289cc7251078e2824f98cd0be321b27a6536af2c2a2119dd8544c42b3b30a99c7756152310aee8c2a8725d1895c3930aa9ca726251396e2c4a212dc948de38a093 (by decide +kernel)
private def pack_E6970Receipt54_chunk142 := witnessRule 54 43 32 1190074 1190193 32 1418
  0x39040745 0x438b41b97731062f8c86c9f18cd9bd321b4796331088f0ca6d5dd90c422bb331b8756151310b0e8c2a6725cd8548c42cb930aa1ca716153310b4e2aa6ca29c4d8beb19b27b64366f4c66210de594db3c30a884 (by decide +kernel)
private def pack_E6970Receipt54_chunk143 := witnessRule 54 43 64 1190194 1190271 32 1400
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4796436af0c662115dd94db3b3218846756636ee8ca6211dcd9cdc39331884 (by decide +kernel)
private def pack_E6970Receipt54_chunk144 := witnessRule 54 43 96 1190320 1190451 32 1406
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt54_chunk145 := witnessRule 54 43 128 1190452 1190644 32 1427
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt54_chunk146 := witnessRule 54 43 160 1190645 1190896 16 763
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk147 := witnessRule 54 42 0 1200000 1200073 32 1450
  0x6a0003 0x19d9854cc42b3ab0aa9c8756251392e8c4a2125cd8948e53931289885a716253396e4a4621062dc5452730a91b27d6151086f6c2a26214de9854ce23cb0a91885478615438cf0c4ad5d98554e3bb31289c8756251090e8c4a4725cd8944c42cb931299ca716252310b4e4a86f1cd563912 (by decide +kernel)
private def pack_E6970Receipt54_chunk148 := witnessRule 54 42 32 1200074 1200194 32 1358
  0x1c000210 0xee4d06211dc5a8dc3c988317d6331082f8ca6c9ed90c4213d331b3796531086f0ce6d5e1854ce33bb0a91885676615438eeac2a66215dd18554e439b0aa1885872615638510e4c470a25c584c42944b99be633107aca685f190c420bdb31b47a6151310a8f2c2a6715e18548c42abbb0aa1c (by decide +kernel)
private def pack_E6970Receipt54_chunk149 := witnessRule 54 42 64 1200195 1200321 32 1341
  0x3e003c00 0x8e2da6d5f0c418bd339b2796631084f0d06cddd9cc421bb349b4756831088e8d46d5cda4c422b9359b6716a3108cf8685ed98d93db29b37a6431086f2cc6d1e194c4223bb39b576663108aead06d9d19cc42339b49b (by decide +kernel)
private def pack_E6970Receipt54_chunk150 := witnessRule 54 42 96 1200322 1200454 32 1345
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt54_chunk151 := witnessRule 54 42 128 1200455 1200706 32 1405
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk152 := witnessRule 54 42 160 1200707 1200896 9 425
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk153 := witnessRule 54 41 0 1210000 1210074 32 1376
  0x3 0x11dd8558e33bb1291c7766251310aeeac4a6721d18948c42c39b12a1c9726253310b2e2c4aa70a25c58544e94538a884c724127ec2a262139854cd8beb0a9188517c6154384f6c2a662149e98554e23d31289c579625108af0c4a4719dd8944c42b3b31299c7756252310aee8c4a8725d18d5c39312a9ca726351396e2c6a212dcd48de38a8a094 (by decide +kernel)
private def pack_E6970Receipt54_chunk154 := witnessRule 54 41 32 1210075 1210196 32 1298
  0x6000180 0x574693108ae6d66d9c9a8c42338b61b77b3107aca620f19cd0bdb3188417a68366f4c2a8711e5854cc42a3c30aa9c5776154310aaecc2ac719d58554c42b3a30ab9c28674633850ee6c46214a1dc990e14438b198852887537ac2a86c5f5854ce13e30a9188527b6154386f4c2a66214de58554e23c30aa1885 (by decide +kernel)
private def pack_E6970Receipt54_chunk155 := witnessRule 54 41 64 1210197 1210324 32 1282
  0x7e00f80 0x13a3618842736e366e4da6210dc5bcda3f18831786a364eed262109d9acd9bab518843746c368e6d662111c9b4dab8b6188457e342f6ce6c9e998c4213cb41b3786731086eed26d1d9a0c4223ab51b (by decide +kernel)
private def pack_E6970Receipt54_chunk156 := witnessRule 54 41 96 1210325 1210458 32 1296
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt54_chunk157 := witnessRule 54 41 128 1210512 1210832 32 1396
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk158 := witnessRule 54 41 160 1210833 1210833 1 47
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk159 := witnessRule 54 40 0 1220000 1220074 32 1303
  0x100001 0x15e18948c42abbb12a1c6766253310aceac4aa71dd18950c42bb9b12b1c2877361523a510e4c2a26218a21c5854ce944b8a9188528a714119cc4a46f58550c42630ab1b27c6252386f6c4a26214de9894ce23cb1291885478625438aeec4a662155d98954e3bb31a89c8756351090e8c6a4725cd8d44c42cb931a99ca716352310b4e6a86ca29c95e38a113 (by decide +kernel)
private def pack_E6970Receipt54_chunk160 := witnessRule 54 40 32 1220075 1220197 32 1236
  0x3800080 0x3756c368e8d662111cdb4dab93618845716e36cfa620f18558d8be30aa9c27b6154310a4f4c2ac70de58554c429bc30ab9c4776156310a8ecc2b070a11d990e142bab1988528574653850ce6c86214a19c998e143b8b298852877737cc2a6621358554d8be30aa188517b6156384f4c2aa62149e5855ce23cb1299c (by decide +kernel)
private def pack_E6970Receipt54_chunk161 := witnessRule 54 40 64 1220198 1220326 32 1225
  0xe1fe03f0 0x2e6c801b2726f31084e2c881b37400c418bb369b2756c31084e8dc6cdcdb4c421b9379b4716e31088e801a1796a364f0d262109ddacd9bb351884 (by decide +kernel)
private def pack_E6970Receipt54_chunk162 := witnessRule 54 40 96 1220327 1220515 32 1264
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt54_chunk163 := witnessRule 54 40 128 1220516 1220832 26 1114
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk164 := witnessRule 54 39 0 1230000 1230075 32 1232
  0x1 0x6f2c4aa711e18950c42a3bb12b1c5766255310aaeac4ae70a15d5854ce9433a30a918862867361543a50ee4c2a66218a1dc58554e94438aa1885388714239cc4a264139894cd8beb129188517c6254384f6c4a662149e98954e1bcb12a1885378625638af0c6a4719dd8d44c42b3b31a99c7756352310aee8c6a8721cd8d4cc42c3931aa9c2887262513a512e2c4a214a25c948e0c5b8a8a095 (by decide +kernel)
private def pack_E6970Receipt54_chunk165 := witnessRule 54 39 32 1230076 1230199 32 1175
  0xc20060 0xbbb69b2766c31084eadc6cdd1b4c421b9b79b4726e31088e2c801b57f3107ac2aa62131855cd8bdb0ab188517a6158384f0c2b270a09e194e141bbb21885283766638508eaca6214a11d19ce142b9b3188528572683850ce2ce6214a19e4deb12a1bc615631096c2b06c9ed8950e1bd31299885 (by decide +kernel)
private def pack_E6970Receipt54_chunk166 := witnessRule 54 39 64 1230200 1230329 32 1175
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt54_chunk167 := witnessRule 54 39 96 1230330 1230519 32 1240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk168 := witnessRule 54 39 128 1230576 1230832 19 802
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk169 := witnessRule 54 38 0 1240000 1240075 32 1163
  0x80000 0x4f2c4ae70de18958c429bbb12c1c2837761543a508ecc2a66218a11d58554e942ba30aa18862857361563a50ce4c2aa6218a19c5855cea4338b19c487723109cc4a4641358950c426312b1b17b6255310a2f4c4ae70de98d4ce23cb1a91885478635438aeec6a662155d98d54e33ab1aa188567463563850ce8c4a474a1dcd8944c43143b931299d288716252310c510e4a870e25c54466392113 (by decide +kernel)
private def pack_E6970Receipt54_chunk170 := witnessRule 54 38 32 1240076 1240200 32 1115
  0xe0758020 0x1756400d93a3798842736440d9b932006210dc5920368e881883c615632094c2b46ca05e19ce1413bb31885282766838506eace6214a0dd1a4e14239b41885284726a3850ae2d26214a15ecdeb1299904d6255362f8c4a862145ed8958e13d312a9885 (by decide +kernel)
private def pack_E6970Receipt54_chunk171 := witnessRule 54 38 64 1240201 1240331 32 1135
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt54_chunk172 := witnessRule 54 38 96 1240384 1240579 32 1221
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk173 := witnessRule 54 38 128 1240580 1240769 12 497
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk174 := witnessRule 54 37 0 1250000 1250076 32 1094
  0x0 0x17a6257310a2f2c4b270a05e58554e9413c30aa18862827761563a506ecc2aa6218a0dd5855ce9423a30ab18862847361583a908e6c871215c98cc42a42b8b29c486743109cc4a2681358d4cc42631aa9b17c6354384f6c6a662149e98d54e1bcb1aa18853786356388eec6aa62151d98d5ce1423b31299d285756252310c50ae8c4a874a19cd894cc4314339312a9d287716254310c50ee4ac7121dc548e14538a0908d (by decide +kernel)
private def pack_E6970Receipt54_chunk175 := witnessRule 54 37 32 1250077 1250202 32 1063
  0xfe1ff018 0x5cd930364e4c9018842716500d9ba60620ca05d9a8e1413ab49885282746b38506e6d46214a0dc9b0e14238b598852847d37ac4a8641318958c425b12c1b (by decide +kernel)
private def pack_E6970Receipt54_chunk176 := witnessRule 54 37 64 1250203 1250386 32 1105
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt54_chunk177 := witnessRule 54 37 96 1250387 1250642 32 1205
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk178 := witnessRule 54 37 128 1250643 1250768 5 205
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk179 := witnessRule 54 36 0 1260000 1260076 32 1028
  0x4040000 0x298964c4214530aa9885289615738502f0c2ac6218a05dd8560e9413ab0ac9d482756538906e8c8621520dcd98e2423932988548471673890aec621358d48cc26b1aa1884c6356362f6c6aa62145e98d5ce13cb1ab1885278635838504f0c4a874a0ddd894cc43141bb312a9d284756254310c508e8c4ac74a15cd8954c43142b9312b9d4857261533a90ce2c2a46219219c550e244390b (by decide +kernel)
private def pack_E6970Receipt54_chunk180 := witnessRule 54 36 32 1260077 1260203 32 1018
  0xffdffe08 0x2e2cb01b281746d38504e6d86214a09c9b8e141b8b698852837f37ac4a6681318954cc25b12b9904 (by decide +kernel)
private def pack_E6970Receipt54_chunk181 := witnessRule 54 36 64 1260204 1260389 32 1077
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk182 := witnessRule 54 36 96 1260390 1260768 31 1154
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk183 := witnessRule 54 35 0 1270000 1270077 32 966
  0xab000000 0x14c4b06610a258558c82943b0ad1c481756738904e8cc6215209cda0e241b9339885483716938908f0621358d44d426b1a99984c635532096c6ae621298d64d945312a9c281796254310c502f0c4ac74a09dd8954c431413b312b9d283756256310c506e8c4b07520dd18550ea4239b0a998864847261553a90ae2c2a86219215c558e2c339188c (by decide +kernel)
private def pack_E6970Receipt54_chunk184 := witnessRule 54 35 32 1270078 1270205 32 979
  0xffffffc6 0x281726400e14138b798852827440de312a1a84 (by decide +kernel)
private def pack_E6970Receipt54_chunk185 := witnessRule 54 35 64 1270256 1270392 32 1053
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk186 := witnessRule 54 35 96 1270448 1270705 24 873
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk187 := witnessRule 54 34 0 1280000 1280077 32 913
  0xffc20000 0x240b9b51c4827269310a904e2d67120de8c426b1a91a84c635434096c6ac661298d60c82145312a19052896256310a510c4b070a05dd895cc43140bb312c9d4817661553a904eac2a86219209d18558ea41b9b0aa98864837261573a908e2c2ac6219211c560e3423a1b (by decide +kernel)
private def pack_E6970Receipt54_chunk188 := witnessRule 54 34 32 1280078 1280257 32 945
  0xfffffffb 0x502e981b (by decide +kernel)
private def pack_E6970Receipt54_chunk189 := witnessRule 54 34 64 1280258 1280450 32 1029
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk190 := witnessRule 54 34 96 1280451 1280704 18 639
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk191 := witnessRule 54 33 0 1290000 1290078 32 865
  0xfffa0010 0x240b8b69cd635137098c6a66c12d8d54d42531ab9a0428a6253340a512c4aa6614a21895cc82943b12c98854876155310a90cc2ae71205d58558c43240ba30ac1d4827261593ad04e4ca71a0dc590c42b41bb1b (by decide +kernel)
private def pack_E6970Receipt54_chunk192 := witnessRule 54 33 32 1290079 1290259 32 916
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk193 := witnessRule 54 33 64 1290260 1290454 32 1007
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk194 := witnessRule 54 33 96 1290512 1290704 12 419
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk195 := witnessRule 54 32 0 1300000 1300078 32 822
  0xffff5558 0x631a91c04a63563608512c4a86a14a1d8960cc2a4330ab1905484615a38d02e4ce71a09c598c42b413c1b (by decide +kernel)
private def pack_E6970Receipt54_chunk196 := witnessRule 54 32 32 1300128 1300261 32 888
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk197 := witnessRule 54 32 64 1300262 1300515 32 987
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk198 := witnessRule 54 32 96 1300516 1300641 6 205
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk199 := witnessRule 54 31 0 1310000 1310128 32 787
  0xfffffffe 0x340bd1b (by decide +kernel)
private def pack_E6970Receipt54_chunk200 := witnessRule 54 31 32 1310129 1310263 32 860
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk201 := witnessRule 54 31 64 1310264 1310640 32 974
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk202 := witnessRule 54 30 0 1320000 1320129 32 754
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk203 := witnessRule 54 30 32 1320130 1320265 32 831
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk204 := witnessRule 54 30 64 1320320 1320640 27 798
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk205 := witnessRule 54 29 0 1330000 1330130 32 724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk206 := witnessRule 54 29 32 1330131 1330322 32 806
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk207 := witnessRule 54 29 64 1330323 1330577 21 600
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk208 := witnessRule 54 28 0 1340000 1340131 32 693
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk209 := witnessRule 54 28 32 1340132 1340324 32 779
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk210 := witnessRule 54 28 64 1340325 1340576 16 443
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk211 := witnessRule 54 27 0 1350000 1350132 32 663
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk212 := witnessRule 54 27 32 1350133 1350384 32 755
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk213 := witnessRule 54 27 64 1350385 1350576 11 297
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk214 := witnessRule 54 26 0 1360000 1360133 32 632
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk215 := witnessRule 54 26 32 1360134 1360387 32 731
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk216 := witnessRule 54 26 64 1360388 1360513 6 157
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk217 := witnessRule 54 25 0 1370000 1370134 32 602
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk218 := witnessRule 54 25 32 1370135 1370450 32 712
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk219 := witnessRule 54 25 64 1370512 1370512 1 26
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk220 := witnessRule 54 24 0 1380000 1380135 32 571
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk221 := witnessRule 54 24 32 1380136 1380512 29 620
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk222 := witnessRule 54 23 0 1390000 1390136 32 541
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk223 := witnessRule 54 23 32 1390192 1390449 24 489
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk224 := witnessRule 54 22 0 1400000 1400192 32 511
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk225 := witnessRule 54 22 32 1400193 1400448 20 387
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk226 := witnessRule 54 21 0 1410000 1410194 32 483
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk227 := witnessRule 54 21 32 1410195 1410448 16 295
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk228 := witnessRule 54 20 0 1420000 1420195 32 453
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk229 := witnessRule 54 20 32 1420196 1420385 12 209
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk230 := witnessRule 54 19 0 1430000 1430197 32 425
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk231 := witnessRule 54 19 32 1430256 1430384 8 133
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk232 := witnessRule 54 18 0 1440000 1440257 32 397
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk233 := witnessRule 54 18 32 1440258 1440384 5 79
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk234 := witnessRule 54 17 0 1450000 1450320 32 372
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk235 := witnessRule 54 17 32 1450321 1450321 1 15
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk236 := witnessRule 54 16 0 1460000 1460320 30 318
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk237 := witnessRule 54 15 0 1470000 1470320 27 258
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk238 := witnessRule 54 14 0 1480000 1480257 24 201
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk239 := witnessRule 54 13 0 1490000 1490256 21 153
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk240 := witnessRule 54 12 0 1500000 1500256 19 118
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk241 := witnessRule 54 11 0 1510000 1510193 16 81
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk242 := witnessRule 54 10 0 1520000 1520192 14 55
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk243 := witnessRule 54 9 0 1530000 1530192 12 35
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk244 := witnessRule 54 8 0 1540000 1540129 10 17
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk245 := witnessRule 54 7 0 1550000 1550128 8 5
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk246 := witnessRule 54 6 0 1560000 1560128 7 1
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk247 := witnessRule 54 5 0 1570000 1570065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk248 := witnessRule 54 4 0 1580000 1580064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk249 := witnessRule 54 3 0 1590000 1590064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk250 := witnessRule 54 2 0 1600000 1600001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk251 := witnessRule 54 1 0 1610000 1610000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt54_chunk252 := witnessRule 54 0 0 1620000 1620000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt54_chunks : List (Chunk 54) := [pack_E6970Receipt54_chunk0, pack_E6970Receipt54_chunk1, pack_E6970Receipt54_chunk2, pack_E6970Receipt54_chunk3, pack_E6970Receipt54_chunk4, pack_E6970Receipt54_chunk5, pack_E6970Receipt54_chunk6, pack_E6970Receipt54_chunk7, pack_E6970Receipt54_chunk8, pack_E6970Receipt54_chunk9, pack_E6970Receipt54_chunk10, pack_E6970Receipt54_chunk11, pack_E6970Receipt54_chunk12, pack_E6970Receipt54_chunk13, pack_E6970Receipt54_chunk14, pack_E6970Receipt54_chunk15, pack_E6970Receipt54_chunk16, pack_E6970Receipt54_chunk17, pack_E6970Receipt54_chunk18, pack_E6970Receipt54_chunk19, pack_E6970Receipt54_chunk20, pack_E6970Receipt54_chunk21, pack_E6970Receipt54_chunk22, pack_E6970Receipt54_chunk23, pack_E6970Receipt54_chunk24, pack_E6970Receipt54_chunk25, pack_E6970Receipt54_chunk26, pack_E6970Receipt54_chunk27, pack_E6970Receipt54_chunk28, pack_E6970Receipt54_chunk29, pack_E6970Receipt54_chunk30, pack_E6970Receipt54_chunk31, pack_E6970Receipt54_chunk32, pack_E6970Receipt54_chunk33, pack_E6970Receipt54_chunk34, pack_E6970Receipt54_chunk35, pack_E6970Receipt54_chunk36, pack_E6970Receipt54_chunk37, pack_E6970Receipt54_chunk38, pack_E6970Receipt54_chunk39, pack_E6970Receipt54_chunk40, pack_E6970Receipt54_chunk41, pack_E6970Receipt54_chunk42, pack_E6970Receipt54_chunk43, pack_E6970Receipt54_chunk44, pack_E6970Receipt54_chunk45, pack_E6970Receipt54_chunk46, pack_E6970Receipt54_chunk47, pack_E6970Receipt54_chunk48, pack_E6970Receipt54_chunk49, pack_E6970Receipt54_chunk50, pack_E6970Receipt54_chunk51, pack_E6970Receipt54_chunk52, pack_E6970Receipt54_chunk53, pack_E6970Receipt54_chunk54, pack_E6970Receipt54_chunk55, pack_E6970Receipt54_chunk56, pack_E6970Receipt54_chunk57, pack_E6970Receipt54_chunk58, pack_E6970Receipt54_chunk59, pack_E6970Receipt54_chunk60, pack_E6970Receipt54_chunk61, pack_E6970Receipt54_chunk62, pack_E6970Receipt54_chunk63, pack_E6970Receipt54_chunk64, pack_E6970Receipt54_chunk65, pack_E6970Receipt54_chunk66, pack_E6970Receipt54_chunk67, pack_E6970Receipt54_chunk68, pack_E6970Receipt54_chunk69, pack_E6970Receipt54_chunk70, pack_E6970Receipt54_chunk71, pack_E6970Receipt54_chunk72, pack_E6970Receipt54_chunk73, pack_E6970Receipt54_chunk74, pack_E6970Receipt54_chunk75, pack_E6970Receipt54_chunk76, pack_E6970Receipt54_chunk77, pack_E6970Receipt54_chunk78, pack_E6970Receipt54_chunk79, pack_E6970Receipt54_chunk80, pack_E6970Receipt54_chunk81, pack_E6970Receipt54_chunk82, pack_E6970Receipt54_chunk83, pack_E6970Receipt54_chunk84, pack_E6970Receipt54_chunk85, pack_E6970Receipt54_chunk86, pack_E6970Receipt54_chunk87, pack_E6970Receipt54_chunk88, pack_E6970Receipt54_chunk89, pack_E6970Receipt54_chunk90, pack_E6970Receipt54_chunk91, pack_E6970Receipt54_chunk92, pack_E6970Receipt54_chunk93, pack_E6970Receipt54_chunk94, pack_E6970Receipt54_chunk95, pack_E6970Receipt54_chunk96, pack_E6970Receipt54_chunk97, pack_E6970Receipt54_chunk98, pack_E6970Receipt54_chunk99, pack_E6970Receipt54_chunk100, pack_E6970Receipt54_chunk101, pack_E6970Receipt54_chunk102, pack_E6970Receipt54_chunk103, pack_E6970Receipt54_chunk104, pack_E6970Receipt54_chunk105, pack_E6970Receipt54_chunk106, pack_E6970Receipt54_chunk107, pack_E6970Receipt54_chunk108, pack_E6970Receipt54_chunk109, pack_E6970Receipt54_chunk110, pack_E6970Receipt54_chunk111, pack_E6970Receipt54_chunk112, pack_E6970Receipt54_chunk113, pack_E6970Receipt54_chunk114, pack_E6970Receipt54_chunk115, pack_E6970Receipt54_chunk116, pack_E6970Receipt54_chunk117, pack_E6970Receipt54_chunk118, pack_E6970Receipt54_chunk119, pack_E6970Receipt54_chunk120, pack_E6970Receipt54_chunk121, pack_E6970Receipt54_chunk122, pack_E6970Receipt54_chunk123, pack_E6970Receipt54_chunk124, pack_E6970Receipt54_chunk125, pack_E6970Receipt54_chunk126, pack_E6970Receipt54_chunk127, pack_E6970Receipt54_chunk128, pack_E6970Receipt54_chunk129, pack_E6970Receipt54_chunk130, pack_E6970Receipt54_chunk131, pack_E6970Receipt54_chunk132, pack_E6970Receipt54_chunk133, pack_E6970Receipt54_chunk134, pack_E6970Receipt54_chunk135, pack_E6970Receipt54_chunk136, pack_E6970Receipt54_chunk137, pack_E6970Receipt54_chunk138, pack_E6970Receipt54_chunk139, pack_E6970Receipt54_chunk140, pack_E6970Receipt54_chunk141, pack_E6970Receipt54_chunk142, pack_E6970Receipt54_chunk143, pack_E6970Receipt54_chunk144, pack_E6970Receipt54_chunk145, pack_E6970Receipt54_chunk146, pack_E6970Receipt54_chunk147, pack_E6970Receipt54_chunk148, pack_E6970Receipt54_chunk149, pack_E6970Receipt54_chunk150, pack_E6970Receipt54_chunk151, pack_E6970Receipt54_chunk152, pack_E6970Receipt54_chunk153, pack_E6970Receipt54_chunk154, pack_E6970Receipt54_chunk155, pack_E6970Receipt54_chunk156, pack_E6970Receipt54_chunk157, pack_E6970Receipt54_chunk158, pack_E6970Receipt54_chunk159, pack_E6970Receipt54_chunk160, pack_E6970Receipt54_chunk161, pack_E6970Receipt54_chunk162, pack_E6970Receipt54_chunk163, pack_E6970Receipt54_chunk164, pack_E6970Receipt54_chunk165, pack_E6970Receipt54_chunk166, pack_E6970Receipt54_chunk167, pack_E6970Receipt54_chunk168, pack_E6970Receipt54_chunk169, pack_E6970Receipt54_chunk170, pack_E6970Receipt54_chunk171, pack_E6970Receipt54_chunk172, pack_E6970Receipt54_chunk173, pack_E6970Receipt54_chunk174, pack_E6970Receipt54_chunk175, pack_E6970Receipt54_chunk176, pack_E6970Receipt54_chunk177, pack_E6970Receipt54_chunk178, pack_E6970Receipt54_chunk179, pack_E6970Receipt54_chunk180, pack_E6970Receipt54_chunk181, pack_E6970Receipt54_chunk182, pack_E6970Receipt54_chunk183, pack_E6970Receipt54_chunk184, pack_E6970Receipt54_chunk185, pack_E6970Receipt54_chunk186, pack_E6970Receipt54_chunk187, pack_E6970Receipt54_chunk188, pack_E6970Receipt54_chunk189, pack_E6970Receipt54_chunk190, pack_E6970Receipt54_chunk191, pack_E6970Receipt54_chunk192, pack_E6970Receipt54_chunk193, pack_E6970Receipt54_chunk194, pack_E6970Receipt54_chunk195, pack_E6970Receipt54_chunk196, pack_E6970Receipt54_chunk197, pack_E6970Receipt54_chunk198, pack_E6970Receipt54_chunk199, pack_E6970Receipt54_chunk200, pack_E6970Receipt54_chunk201, pack_E6970Receipt54_chunk202, pack_E6970Receipt54_chunk203, pack_E6970Receipt54_chunk204, pack_E6970Receipt54_chunk205, pack_E6970Receipt54_chunk206, pack_E6970Receipt54_chunk207, pack_E6970Receipt54_chunk208, pack_E6970Receipt54_chunk209, pack_E6970Receipt54_chunk210, pack_E6970Receipt54_chunk211, pack_E6970Receipt54_chunk212, pack_E6970Receipt54_chunk213, pack_E6970Receipt54_chunk214, pack_E6970Receipt54_chunk215, pack_E6970Receipt54_chunk216, pack_E6970Receipt54_chunk217, pack_E6970Receipt54_chunk218, pack_E6970Receipt54_chunk219, pack_E6970Receipt54_chunk220, pack_E6970Receipt54_chunk221, pack_E6970Receipt54_chunk222, pack_E6970Receipt54_chunk223, pack_E6970Receipt54_chunk224, pack_E6970Receipt54_chunk225, pack_E6970Receipt54_chunk226, pack_E6970Receipt54_chunk227, pack_E6970Receipt54_chunk228, pack_E6970Receipt54_chunk229, pack_E6970Receipt54_chunk230, pack_E6970Receipt54_chunk231, pack_E6970Receipt54_chunk232, pack_E6970Receipt54_chunk233, pack_E6970Receipt54_chunk234, pack_E6970Receipt54_chunk235, pack_E6970Receipt54_chunk236, pack_E6970Receipt54_chunk237, pack_E6970Receipt54_chunk238, pack_E6970Receipt54_chunk239, pack_E6970Receipt54_chunk240, pack_E6970Receipt54_chunk241, pack_E6970Receipt54_chunk242, pack_E6970Receipt54_chunk243, pack_E6970Receipt54_chunk244, pack_E6970Receipt54_chunk245, pack_E6970Receipt54_chunk246, pack_E6970Receipt54_chunk247, pack_E6970Receipt54_chunk248, pack_E6970Receipt54_chunk249, pack_E6970Receipt54_chunk250, pack_E6970Receipt54_chunk251, pack_E6970Receipt54_chunk252]
def rows54 := rowsFrom pack_E6970Receipt54_chunks
theorem good54 : ∀ r ∈ rows54, good 54 r = true := rowsFrom_good pack_E6970Receipt54_chunks
theorem sorted54 : rows54.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt54_chunks 0 (by decide +kernel)).1
theorem mass54 (i : Fin 61) :
    bandCount 54 (i.val : ℤ) 60 16 ≤ (rows54.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt54_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 54 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt54_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total54 : (rows54.map (price 54)).sum = 393295 :=
  (total_eq pack_E6970Receipt54_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt54

section Pack_E6970Receipt55

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt55_chunk0 := witnessA6966Final 55 60 0 1050005 1050072 32 3960
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk1 := witnessA6966Final 55 60 32 1050073 1050140 32 3888
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk2 := witnessA6966Final 55 60 64 1050141 1050208 32 3764
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk3 := witnessA6966Final 55 60 96 1050209 1050278 32 3600
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk4 := witnessA6966Final 55 60 128 1050279 1050390 32 3658
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk5 := witnessA6966Final 55 60 160 1050391 1050464 32 3432
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk6 := witnessA6966Final 55 60 192 1050465 1050585 32 3368
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk7 := witnessA6966Final 55 60 224 1050586 1050712 32 3178
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk8 := witnessA6966Final 55 60 256 1050713 1050898 32 2994
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk9 := witnessA6966Final 55 60 288 1050899 1051030 22 1908
  0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk10 := witnessRule 55 59 0 1060004 1060071 32 3782
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk11 := witnessRule 55 59 32 1060072 1060138 32 3676
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk12 := witnessRule 55 59 64 1060139 1060207 32 3554
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk13 := witnessRule 55 59 96 1060208 1060277 32 3364
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk14 := witnessRule 55 59 128 1060278 1060390 32 3412
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk15 := witnessRule 55 59 160 1060391 1060465 32 3182
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk16 := witnessRule 55 59 192 1060466 1060587 32 3134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk17 := witnessRule 55 59 224 1060588 1060715 32 2920
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk18 := witnessRule 55 59 256 1060716 1060902 32 2752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk19 := witnessRule 55 59 288 1060903 1061029 16 1278
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk20 := witnessRule 55 58 0 1070003 1070069 32 3580
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk21 := witnessRule 55 58 32 1070070 1070137 32 3478
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk22 := witnessRule 55 58 64 1070138 1070206 32 3320
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk23 := witnessRule 55 58 96 1070207 1070277 32 3134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk24 := witnessRule 55 58 128 1070278 1070391 32 3192
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk25 := witnessRule 55 58 160 1070392 1070466 32 2916
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk26 := witnessRule 55 58 192 1070512 1070589 32 2892
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk27 := witnessRule 55 58 224 1070590 1070769 32 2706
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk28 := witnessRule 55 58 256 1070770 1070962 32 2500
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk29 := witnessRule 55 58 288 1070963 1071029 10 740
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk30 := witnessRule 55 57 0 1080002 1080068 32 3430
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk31 := witnessRule 55 57 32 1080069 1080136 32 3246
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk32 := witnessRule 55 57 64 1080137 1080206 32 3104
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk33 := witnessRule 55 57 96 1080207 1080277 32 2898
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk34 := witnessRule 55 57 128 1080278 1080392 32 2968
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk35 := witnessRule 55 57 160 1080393 1080513 32 2716
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk36 := witnessRule 55 57 192 1080514 1080640 32 2622
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk37 := witnessRule 55 57 224 1080641 1080773 32 2480
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk38 := witnessRule 55 57 256 1080774 1081025 32 2281
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk39 := witnessRule 55 57 288 1081026 1081028 3 206
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk40 := witnessRule 55 56 0 1090001 1090067 32 3224
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk41 := witnessRule 55 56 32 1090068 1090136 32 3044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk42 := witnessRule 55 56 64 1090137 1090206 32 2864
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk43 := witnessRule 55 56 96 1090207 1090278 32 2672
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk44 := witnessRule 55 56 128 1090320 1090394 32 2750
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk45 := witnessRule 55 56 160 1090395 1090516 32 2520
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk46 := witnessRule 55 56 192 1090517 1090644 32 2393
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk47 := witnessRule 55 56 224 1090645 1090778 32 2232
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk48 := witnessRule 55 56 256 1090832 1091028 28 1898
  0xfffdfff 0xb99a (by decide +kernel)
private def pack_E6970Receipt55_chunk49 := witnessRule 55 55 0 1100000 1100067 32 3064
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk50 := witnessRule 55 55 32 1100068 1100136 32 2808
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk51 := witnessRule 55 55 64 1100137 1100207 32 2634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk52 := witnessRule 55 55 96 1100208 1100321 32 2509
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk53 := witnessRule 55 55 128 1100322 1100396 32 2469
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk54 := witnessRule 55 55 160 1100397 1100519 32 2335
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk55 := witnessRule 55 55 192 1100520 1100648 32 2204
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk56 := witnessRule 55 55 224 1100649 1100837 32 2119
  0x7fffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt55_chunk57 := witnessRule 55 55 256 1100838 1101027 20 1302
  0xfffbf 0xba1a (by decide +kernel)
private def pack_E6970Receipt55_chunk58 := witnessRule 55 54 0 1110000 1110067 32 2837
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk59 := witnessRule 55 54 32 1110068 1110137 32 2601
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk60 := witnessRule 55 54 64 1110138 1110208 32 2406
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk61 := witnessRule 55 54 96 1110209 1110323 32 2365
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk62 := witnessRule 55 54 128 1110324 1110399 32 2249
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk63 := witnessRule 55 54 160 1110400 1110523 32 2177
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk64 := witnessRule 55 54 192 1110524 1110704 32 2081
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk65 := witnessRule 55 54 224 1110705 1110899 32 2036
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt55_chunk66 := witnessRule 55 54 256 1110900 1111027 12 758
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk67 := witnessRule 55 53 0 1120000 1120068 32 2658
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk68 := witnessRule 55 53 32 1120069 1120138 32 2384
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk69 := witnessRule 55 53 64 1120139 1120210 32 2234
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk70 := witnessRule 55 53 96 1120211 1120326 32 2221
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk71 := witnessRule 55 53 128 1120327 1120448 32 2097
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk72 := witnessRule 55 53 160 1120449 1120576 32 2049
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk73 := witnessRule 55 53 192 1120577 1120710 32 1995
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt55_chunk74 := witnessRule 55 53 224 1120711 1120964 32 1959
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt55_chunk75 := witnessRule 55 53 256 1121024 1121026 3 186
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk76 := witnessRule 55 52 0 1130000 1130068 32 2472
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk77 := witnessRule 55 52 32 1130069 1130139 32 2212
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk78 := witnessRule 55 52 64 1130140 1130211 32 2100
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk79 := witnessRule 55 52 96 1130212 1130328 32 2083
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk80 := witnessRule 55 52 128 1130329 1130451 32 2000
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk81 := witnessRule 55 52 160 1130452 1130580 32 1950
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk82 := witnessRule 55 52 192 1130581 1130769 32 1911
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt55_chunk83 := witnessRule 55 52 224 1130770 1131026 27 1606
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt55_chunk84 := witnessRule 55 51 0 1140000 1140069 32 2314
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk85 := witnessRule 55 51 32 1140070 1140140 32 2066
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk86 := witnessRule 55 51 64 1140141 1140213 32 1985
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk87 := witnessRule 55 51 96 1140256 1140331 32 1980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk88 := witnessRule 55 51 128 1140332 1140455 32 1907
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk89 := witnessRule 55 51 160 1140456 1140585 32 1864
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt55_chunk90 := witnessRule 55 51 192 1140586 1140775 32 1838
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt55_chunk91 := witnessRule 55 51 224 1140832 1141025 18 1044
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt55_chunk92 := witnessRule 55 50 0 1150000 1150069 32 2168
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk93 := witnessRule 55 50 32 1150070 1150141 32 1961
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk94 := witnessRule 55 50 64 1150142 1150257 32 1902
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk95 := witnessRule 55 50 96 1150258 1150333 32 1869
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk96 := witnessRule 55 50 128 1150334 1150458 32 1822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk97 := witnessRule 55 50 160 1150459 1150641 32 1791
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt55_chunk98 := witnessRule 55 50 192 1150642 1150837 32 1775
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt55_chunk99 := witnessRule 55 50 224 1150896 1151025 10 572
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk100 := witnessRule 55 49 0 1160000 1160070 32 2040
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk101 := witnessRule 55 49 32 1160071 1160142 32 1860
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk102 := witnessRule 55 49 64 1160143 1160259 32 1814
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk103 := witnessRule 55 49 96 1160260 1160336 32 1771
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk104 := witnessRule 55 49 128 1160337 1160462 32 1745
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt55_chunk105 := witnessRule 55 49 160 1160512 1160646 32 1726
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt55_chunk106 := witnessRule 55 49 192 1160647 1160962 32 1735
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt55_chunk107 := witnessRule 55 49 224 1161024 1161024 1 57
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk108 := witnessRule 55 48 0 1170000 1170070 32 1918
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk109 := witnessRule 55 48 32 1170071 1170143 32 1771
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk110 := witnessRule 55 48 64 1170144 1170261 32 1730
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk111 := witnessRule 55 48 96 1170262 1170385 32 1691
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt55_chunk112 := witnessRule 55 48 128 1170386 1170515 32 1677
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt55_chunk113 := witnessRule 55 48 160 1170516 1170705 32 1655
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt55_chunk114 := witnessRule 55 48 192 1170706 1171024 25 1326
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk115 := witnessRule 55 47 0 1180000 1180071 32 1814
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk116 := witnessRule 55 47 32 1180072 1180144 32 1679
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk117 := witnessRule 55 47 64 1180145 1180263 32 1651
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk118 := witnessRule 55 47 96 1180264 1180388 32 1622
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt55_chunk119 := witnessRule 55 47 128 1180389 1180519 32 1603
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt55_chunk120 := witnessRule 55 47 160 1180520 1180711 32 1600
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt55_chunk121 := witnessRule 55 47 192 1180768 1180961 16 835
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk122 := witnessRule 55 46 0 1190000 1190071 32 1717
  0xffffffcf 0x2dccd638a2 (by decide +kernel)
private def pack_E6970Receipt55_chunk123 := witnessRule 55 46 32 1190072 1190145 32 1594
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk124 := witnessRule 55 46 64 1190146 1190265 32 1581
  0xb6bfffff 0x5766336ee8c66e5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt55_chunk125 := witnessRule 55 46 96 1190266 1190391 32 1553
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt55_chunk126 := witnessRule 55 46 128 1190392 1190523 32 1535
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt55_chunk127 := witnessRule 55 46 160 1190576 1190773 32 1564
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt55_chunk128 := witnessRule 55 46 192 1190832 1190960 8 413
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk129 := witnessRule 55 45 0 1200000 1200072 32 1632
  0xd5fffd5f 0x25cd8cdd38b21bc7141370e8c66e5c990dd3a9a (by decide +kernel)
private def pack_E6970Receipt55_chunk130 := witnessRule 55 45 32 1200073 1200146 32 1512
  0xfffe9fff 0x14e4c66edd0d0c63a (by decide +kernel)
private def pack_E6970Receipt55_chunk131 := witnessRule 55 45 64 1200147 1200267 32 1513
  0x920edb69 0x37864368f0c66d5d990db3b319b77464370e6c662121c994dcb8b21884976342f6c66cde58cdabbb19b77563372e6c66e9c590ddb99883 (by decide +kernel)
private def pack_E6970Receipt55_chunk132 := witnessRule 55 45 96 1200268 1200394 32 1485
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt55_chunk133 := witnessRule 55 45 128 1200395 1200580 32 1482
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt55_chunk134 := witnessRule 55 45 160 1200581 1200960 32 1546
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk135 := witnessRule 55 44 0 1210000 1210072 32 1548
  0x55ffd547 0xeeac86e1cd94ddb930a884c71513108af0c66d9d990dbba329ba736151096e2c2a26216dc54cde3922 (by decide +kernel)
private def pack_E6970Receipt55_chunk136 := witnessRule 55 44 32 1210073 1210147 32 1441
  0xedb40ffd 0x2f8c66cde98cdabc319b77663370e8c86e5cd8cc424b9329b18a726138316e2c21062dc8db3bb19b (by decide +kernel)
private def pack_E6970Receipt55_chunk137 := witnessRule 55 44 64 1210192 1210269 32 1445
  0x80039240 0xbd329b27a64366f2c66210de194da3c321b577633108aecca6d9d590c4233a331b773653108ee4ce6e1c598c4243c1a17b64364f6c66cde590da3cb19b5776436ceec66ddd590dc3a31988487365372e4c862125c598dd3a9883 (by decide +kernel)
private def pack_E6970Receipt55_chunk138 := witnessRule 55 44 96 1210270 1210397 32 1423
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt55_chunk139 := witnessRule 55 44 128 1210448 1210584 32 1435
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt55_chunk140 := witnessRule 55 44 160 1210640 1210897 24 1138
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk141 := witnessRule 55 43 0 1220000 1220073 32 1473
  0xa03d5407 0x10ecc2a2125d18544c42cb9b0a99ca726152310b4e2c2a87062dc5856638a8a09cc7141264f8c66cde990da3c329b7776151090eac2a262161d1854ce4b9b0a918859726154396e4c4ae9c554de39289b (by decide +kernel)
private def pack_E6970Receipt55_chunk142 := witnessRule 55 43 32 1220074 1220193 32 1380
  0x39200768 0x438b41b97731062f8c86c9f18cd9bd321b47a6336af0c86d9dd8cc4233b329b775643108ee8cc6c621d188e0c4b9b09885189726338314e2c46214629d0d8beb19b37b63368f2c86d5e18cc422bbb29b (by decide +kernel)
private def pack_E6970Receipt55_chunk143 := witnessRule 55 43 64 1220194 1220271 32 1368
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4796436af0c662115dd94db3b3218846756636ee8ca6211dcd9cdc39331884 (by decide +kernel)
private def pack_E6970Receipt55_chunk144 := witnessRule 55 43 96 1220320 1220451 32 1374
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt55_chunk145 := witnessRule 55 43 128 1220452 1220644 32 1395
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt55_chunk146 := witnessRule 55 43 160 1220645 1220896 16 747
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk147 := witnessRule 55 42 0 1230000 1230073 32 1398
  0x314001 0xceec2a671dd98548c42bbab0aa1c8746153310b0e6c2aa70625cd8544e8c53930a88518a7161523a316e2a26214631c49f321a17d6331082f8ca6d1ed854422bcb0a89885578615338ceec2a462159d98550e43b312b7746155392e8c4a2729cd8944253931291cb716251310b6e4a66f1c5491e3912 (by decide +kernel)
private def pack_E6970Receipt55_chunk148 := witnessRule 55 42 32 1230074 1230194 32 1319
  0x1e000382 0x772683108ee2d46e1e4c418be329b27c64366f6c66210de994da3cb218844786636aeeca62115d99cd8c33b319c1877562310a30ee8c870621cd8cc428c439329c1897164310a312ec6c5f590d93e31988427b65366f4c86210de598db3c30a89885 (by decide +kernel)
private def pack_E6970Receipt55_chunk149 := witnessRule 55 42 64 1230195 1230321 32 1309
  0x3e003c00 0x8e2da6d5f0c418bd339b2796631084f0d06cddd9cc421bb349b4756831088e8d46d5cda4c422b9359b6716a3108cf8685ed98d93db29b37a6431086f2cc6d1e194c4223bb39b576663108aead06d9d19cc42339b49b (by decide +kernel)
private def pack_E6970Receipt55_chunk150 := witnessRule 55 42 96 1230322 1230454 32 1313
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt55_chunk151 := witnessRule 55 42 128 1230455 1230706 32 1373
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk152 := witnessRule 55 42 160 1230707 1230896 9 416
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk153 := witnessRule 55 41 0 1240000 1240074 32 1327
  0x140000 0x15e1854cc42abbb0aa9c6766154310aceac2ac7061dd58548e8c43a30a898861887361533a312e4c2a46218625c58550e8c538a9988528a714139cc2a66c9f58544c4293e30a99c37b6152310a6f4c2a8711e5854cc42a3c30aa9c678625138eeec4a211dd98948e43ab12898858746253392e6c4a462165c98950e0c539312ca725536316e4a2735c895b8a113 (by decide +kernel)
private def pack_E6970Receipt55_chunk154 := witnessRule 55 41 32 1240075 1240196 32 1260
  0x7000180 0xae8d262115cdacdb393518846716c36ef6620c5f590c420be331b27b6531084f4ce6cde598c421bc341b18478643830aeec66214615d994e0c33ab2188518674663830ee6ca621461dc99ce0c438b318851887837cc8620f598d0be32988417b67366f6c2a6711e98548c42a3cb0aa1c (by decide +kernel)
private def pack_E6970Receipt55_chunk155 := witnessRule 55 41 64 1240197 1240324 32 1250
  0x7e00f80 0x13a3618842736e366e4da6210dc5bcda3f18831786a364eed262109d9acd9bab518843746c368e6d662111c9b4dab8b6188457e342f6ce6c9e998c4213cb41b3786731086eed26d1d9a0c4223ab51b (by decide +kernel)
private def pack_E6970Receipt55_chunk156 := witnessRule 55 41 96 1240325 1240458 32 1264
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt55_chunk157 := witnessRule 55 41 128 1240512 1240832 32 1364
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk158 := witnessRule 55 41 160 1240833 1240833 1 46
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk159 := witnessRule 55 40 0 1250000 1250074 32 1256
  0x100000 0x8f0c2aa62151dd855ce0c2bbb0a99d186766152310c30ceac2a87461dd1854cc430c3b9b0aa9d188726154310c310e2c2ac74e21c588e1c4b89884f61523109cc2a86c5f5854cc428be30aa9c27b6154310a4f4c2ac711e98948e2bcb1289885578625338ceec4a462159d98950e3bab1299885774625538310e8c4a274625cd894428c4b931291d18a716251310c314e4a67062dc5492638a113 (by decide +kernel)
private def pack_E6970Receipt55_chunk160 := witnessRule 55 40 32 1250075 1250197 32 1200
  0x39000c0 0xdd5b0da3a3598844736d36ae4d862115c5b8db3e9883d6631078d0685e9a4d8c13d329c1837964310a306f0cc70611dd94c428c23b339c1857566310a30ae8d070619cd9cc428c339349c1877168310a30ef46f58554d8beb0aa1c27c6153310a4f6c2aa70de98550c429bcb0ab1c (by decide +kernel)
private def pack_E6970Receipt55_chunk161 := witnessRule 55 40 64 1250198 1250326 32 1193
  0xe1fe03f0 0x2e6c801b2726f31084e2c881b37400c418bb369b2756c31084e8dc6cdcdb4c421b9379b4716e31088e801a1796a364f0d262109ddacd9bb351884 (by decide +kernel)
private def pack_E6970Receipt55_chunk162 := witnessRule 55 40 96 1250327 1250515 32 1232
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt55_chunk163 := witnessRule 55 40 128 1250516 1250832 26 1088
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk164 := witnessRule 55 39 0 1260000 1260075 32 1187
  0x80000 0x4f2c2b07060de58550e8c23c30a998861847761553a30aecc2a86218615d58558e8c33a30aa98861867361573a70ce6c670e1dc988c429c3b8b21c388733109cc4a66f58554c42630ab9b27c6253386f6c4a46214de98950e23cb1299885478625538aeec4a862155d98958e0c33b31291d187756251310c30ee8c4a674621cd8948c430c439312a1d189716253310c312e4aa70e25c544e0c63913 (by decide +kernel)
private def pack_E6970Receipt55_chunk165 := witnessRule 55 39 32 1260076 1260199 32 1140
  0xec0060 0x2eeda6c9d9b0c4213ab71b3746d31086e6de6d1c9b8c42238b2006d5fcc41e30ab9b1817a6738304f2cc6214609e1a0e0c1bbb39885183766938308ead06214611d1a8e0c2b9b49885185726b3830ce2d46214619f0df30aa1884d6156362f8c2aa62145ed855ce13d30ab1885 (by decide +kernel)
private def pack_E6970Receipt55_chunk166 := witnessRule 55 39 64 1260200 1260329 32 1143
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt55_chunk167 := witnessRule 55 39 96 1260330 1260519 32 1208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk168 := witnessRule 55 39 128 1260576 1260832 19 783
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk169 := witnessRule 55 38 0 1270000 1270075 32 1120
  0x80000 0x304f4c2a86218609e58558e8c1bc30aa98861837761573a308ecc2ac6218611d58560e9c23ab21c3857463310a70ae6ca70e19c990c429c338b31c387753109cc4a4641398950d8beb129988517c6255384f6c4a862149e98958e1bcb12a9885378625738308f0c4a674615dd8948c430c2bb312a1d186756253310c30ce8c4aa7461dcd8950c430c3b9312b1d3877261523a710e2c2a26218e21c54ce14539208c (by decide +kernel)
private def pack_E6970Receipt55_chunk170 := witnessRule 55 38 32 1270076 1270200 32 1082
  0xe07f8030 0xbab2006c9d1bcc42139b2206cdc990031086e2c901b47440c418c0bc351c1827769310a304ecd67060dd5a8c428c1ba361c184736b310a308e4da70615c5b0c428c2bf1bd6255378c2ae6212d8564d8c0bdb0aa9d (by decide +kernel)
private def pack_E6970Receipt55_chunk171 := witnessRule 55 38 64 1270201 1270331 32 1103
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt55_chunk172 := witnessRule 55 38 96 1270384 1270579 32 1189
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk173 := witnessRule 55 38 128 1270580 1270769 12 485
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk174 := witnessRule 55 37 0 1280000 1280076 32 1053
  0x10040000 0x62d855ce0c0bd30ab18861817961583a304eec2b274e09dd94e1c1bb321885383756638708e8ca6214e11cd9ce1c2b933188538571683870cee62139894cc826b12a9884c6257362f6c4ac62145e98960e0c13d312a1d183796253310c306f0c4aa74611dd8950c430c23b312b1d185756255310c30ae8c4ae74e15d1854ce9c339b0a918863867261543a70ee2c2a66218e1dc554e24438988c (by decide +kernel)
private def pack_E6970Receipt55_chunk175 := witnessRule 55 37 32 1280077 1280202 32 1031
  0xfe1ff018 0x17364c0d939324062109c5940366e981883181766d38304ead86214609d1b8e0c1b9b69885183726f38308e2dc6214611d0037ac4a8641318958c420c630aa9885 (by decide +kernel)
private def pack_E6970Receipt55_chunk176 := witnessRule 55 37 64 1280203 1280386 32 1073
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt55_chunk177 := witnessRule 55 37 96 1280387 1280642 32 1173
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk178 := witnessRule 55 37 128 1280643 1280768 5 200
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk179 := witnessRule 55 36 0 1290000 1290076 32 988
  0x58040000 0x18b6156320a312c2b470e05dd9ce1c13b331885382756838706e8ce6214e0dcda4e1c239341885384716a3870af2621398948d026b1aa1884c635636318c4aa70605ed8950c430c0bd312b1d182796255310c304f0c4ae7460ddd8958c430c1bb312c1d3837661543a708eac2a66218e11d18554e9c2b9b0aa18863857261563a70ce2c2aa6218e19c55ce2c3399b (by decide +kernel)
private def pack_E6970Receipt55_chunk180 := witnessRule 55 36 32 1290077 1290203 32 986
  0xffdffe0d 0xb8b2c06c605d190038304e6de6214609c991038306e2c8018851837480de312a9984 (by decide +kernel)
private def pack_E6970Receipt55_chunk181 := witnessRule 55 36 64 1290204 1290389 32 1045
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk182 := witnessRule 55 36 96 1290390 1290768 31 1123
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk183 := witnessRule 55 35 0 1300000 1300077 32 930
  0xff020000 0x702ead470e09d1a4c429c139b59c383726a310a706e2d870e11ecc426b1a99984c63553208318c4a8641462d8958c428c5312c1c181796257310c302f0c4b274e05e18554e9c13bb0aa18863827661563a706eac2aa6218e0dd1855ce9c239b0ab18863847261583ab08e4c871615c58cc42ac2ba9b (by decide +kernel)
private def pack_E6970Receipt55_chunk184 := witnessRule 55 35 32 1300078 1300205 32 947
  0xffffffc7 0xc0b9326070609c5920310a304ea01b (by decide +kernel)
private def pack_E6970Receipt55_chunk185 := witnessRule 55 35 64 1300256 1300392 32 1021
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk186 := witnessRule 55 35 96 1300448 1300705 24 849
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk187 := witnessRule 55 34 0 1310000 1310077 32 878
  0xffc20040 0x381736d38704e4d86214e09c5b8e1c1be9884d635235098c6a86810631894cd028c5b12a998518a6257320a312c4b26214e258554c429c430ab9c381776156310c702ecc2b074e09d18564eac13a329c5837364310ab06e4cc71611c594c42ac23b9b (by decide +kernel)
private def pack_E6970Receipt55_chunk188 := witnessRule 55 34 32 1310078 1310257 32 913
  0xfffffffb 0x302eb01b (by decide +kernel)
private def pack_E6970Receipt55_chunk189 := witnessRule 55 34 64 1310258 1310450 32 997
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk190 := witnessRule 55 34 96 1310451 1310704 18 621
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk191 := witnessRule 55 33 0 1320000 1320078 32 831
  0xfffb5560 0x1c0b8b2007318d4cd820c5b12a1a851896258330a710c2ac6414e198568e2c0ba339c5827366310ab04e4d07160dc59cc42ac1bc9b (by decide +kernel)
private def pack_E6970Receipt55_chunk192 := witnessRule 55 33 32 1320079 1320259 32 884
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk193 := witnessRule 55 33 64 1320260 1320454 32 975
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk194 := witnessRule 55 33 96 1320512 1320704 12 407
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk195 := witnessRule 55 32 0 1330000 1330078 32 790
  0xfffffff8 0xb02e4d471609c5a4c42ac13d9b (by decide +kernel)
private def pack_E6970Receipt55_chunk196 := witnessRule 55 32 32 1330128 1330261 32 856
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk197 := witnessRule 55 32 64 1330262 1330515 32 955
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk198 := witnessRule 55 32 96 1330516 1330641 6 199
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk199 := witnessRule 55 31 0 1340000 1340128 32 755
  0xfffffffe 0x2c0be9b (by decide +kernel)
private def pack_E6970Receipt55_chunk200 := witnessRule 55 31 32 1340129 1340263 32 828
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk201 := witnessRule 55 31 64 1340264 1340640 32 942
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk202 := witnessRule 55 30 0 1350000 1350129 32 722
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk203 := witnessRule 55 30 32 1350130 1350265 32 799
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk204 := witnessRule 55 30 64 1350320 1350640 27 771
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk205 := witnessRule 55 29 0 1360000 1360130 32 692
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk206 := witnessRule 55 29 32 1360131 1360322 32 774
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk207 := witnessRule 55 29 64 1360323 1360577 21 579
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk208 := witnessRule 55 28 0 1370000 1370131 32 661
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk209 := witnessRule 55 28 32 1370132 1370324 32 747
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk210 := witnessRule 55 28 64 1370325 1370576 16 427
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk211 := witnessRule 55 27 0 1380000 1380132 32 631
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk212 := witnessRule 55 27 32 1380133 1380384 32 723
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk213 := witnessRule 55 27 64 1380385 1380576 11 286
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk214 := witnessRule 55 26 0 1390000 1390133 32 600
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk215 := witnessRule 55 26 32 1390134 1390387 32 699
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk216 := witnessRule 55 26 64 1390388 1390513 6 151
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk217 := witnessRule 55 25 0 1400000 1400134 32 570
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk218 := witnessRule 55 25 32 1400135 1400450 32 680
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk219 := witnessRule 55 25 64 1400512 1400512 1 25
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk220 := witnessRule 55 24 0 1410000 1410135 32 539
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk221 := witnessRule 55 24 32 1410136 1410512 29 591
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk222 := witnessRule 55 23 0 1420000 1420136 32 509
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk223 := witnessRule 55 23 32 1420192 1420449 24 465
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk224 := witnessRule 55 22 0 1430000 1430192 32 479
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk225 := witnessRule 55 22 32 1430193 1430448 20 367
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk226 := witnessRule 55 21 0 1440000 1440194 32 451
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk227 := witnessRule 55 21 32 1440195 1440448 16 279
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk228 := witnessRule 55 20 0 1450000 1450195 32 421
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk229 := witnessRule 55 20 32 1450196 1450385 12 197
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk230 := witnessRule 55 19 0 1460000 1460197 32 393
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk231 := witnessRule 55 19 32 1460256 1460384 8 125
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk232 := witnessRule 55 18 0 1470000 1470257 32 365
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk233 := witnessRule 55 18 32 1470258 1470384 5 74
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk234 := witnessRule 55 17 0 1480000 1480320 32 340
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk235 := witnessRule 55 17 32 1480321 1480321 1 14
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk236 := witnessRule 55 16 0 1490000 1490320 30 288
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk237 := witnessRule 55 15 0 1500000 1500320 27 231
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk238 := witnessRule 55 14 0 1510000 1510257 24 177
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk239 := witnessRule 55 13 0 1520000 1520256 21 132
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk240 := witnessRule 55 12 0 1530000 1530256 19 99
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk241 := witnessRule 55 11 0 1540000 1540193 16 65
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk242 := witnessRule 55 10 0 1550000 1550192 14 41
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk243 := witnessRule 55 9 0 1560000 1560192 12 23
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk244 := witnessRule 55 8 0 1570000 1570129 10 7
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk245 := witnessRule 55 7 0 1580000 1580128 8 1
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk246 := witnessRule 55 6 0 1590000 1590128 7 0
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk247 := witnessRule 55 5 0 1600000 1600065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk248 := witnessRule 55 4 0 1610000 1610064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk249 := witnessRule 55 3 0 1620000 1620064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk250 := witnessRule 55 2 0 1630000 1630001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk251 := witnessRule 55 1 0 1640000 1640000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt55_chunk252 := witnessRule 55 0 0 1650000 1650000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt55_chunks : List (Chunk 55) := [pack_E6970Receipt55_chunk0, pack_E6970Receipt55_chunk1, pack_E6970Receipt55_chunk2, pack_E6970Receipt55_chunk3, pack_E6970Receipt55_chunk4, pack_E6970Receipt55_chunk5, pack_E6970Receipt55_chunk6, pack_E6970Receipt55_chunk7, pack_E6970Receipt55_chunk8, pack_E6970Receipt55_chunk9, pack_E6970Receipt55_chunk10, pack_E6970Receipt55_chunk11, pack_E6970Receipt55_chunk12, pack_E6970Receipt55_chunk13, pack_E6970Receipt55_chunk14, pack_E6970Receipt55_chunk15, pack_E6970Receipt55_chunk16, pack_E6970Receipt55_chunk17, pack_E6970Receipt55_chunk18, pack_E6970Receipt55_chunk19, pack_E6970Receipt55_chunk20, pack_E6970Receipt55_chunk21, pack_E6970Receipt55_chunk22, pack_E6970Receipt55_chunk23, pack_E6970Receipt55_chunk24, pack_E6970Receipt55_chunk25, pack_E6970Receipt55_chunk26, pack_E6970Receipt55_chunk27, pack_E6970Receipt55_chunk28, pack_E6970Receipt55_chunk29, pack_E6970Receipt55_chunk30, pack_E6970Receipt55_chunk31, pack_E6970Receipt55_chunk32, pack_E6970Receipt55_chunk33, pack_E6970Receipt55_chunk34, pack_E6970Receipt55_chunk35, pack_E6970Receipt55_chunk36, pack_E6970Receipt55_chunk37, pack_E6970Receipt55_chunk38, pack_E6970Receipt55_chunk39, pack_E6970Receipt55_chunk40, pack_E6970Receipt55_chunk41, pack_E6970Receipt55_chunk42, pack_E6970Receipt55_chunk43, pack_E6970Receipt55_chunk44, pack_E6970Receipt55_chunk45, pack_E6970Receipt55_chunk46, pack_E6970Receipt55_chunk47, pack_E6970Receipt55_chunk48, pack_E6970Receipt55_chunk49, pack_E6970Receipt55_chunk50, pack_E6970Receipt55_chunk51, pack_E6970Receipt55_chunk52, pack_E6970Receipt55_chunk53, pack_E6970Receipt55_chunk54, pack_E6970Receipt55_chunk55, pack_E6970Receipt55_chunk56, pack_E6970Receipt55_chunk57, pack_E6970Receipt55_chunk58, pack_E6970Receipt55_chunk59, pack_E6970Receipt55_chunk60, pack_E6970Receipt55_chunk61, pack_E6970Receipt55_chunk62, pack_E6970Receipt55_chunk63, pack_E6970Receipt55_chunk64, pack_E6970Receipt55_chunk65, pack_E6970Receipt55_chunk66, pack_E6970Receipt55_chunk67, pack_E6970Receipt55_chunk68, pack_E6970Receipt55_chunk69, pack_E6970Receipt55_chunk70, pack_E6970Receipt55_chunk71, pack_E6970Receipt55_chunk72, pack_E6970Receipt55_chunk73, pack_E6970Receipt55_chunk74, pack_E6970Receipt55_chunk75, pack_E6970Receipt55_chunk76, pack_E6970Receipt55_chunk77, pack_E6970Receipt55_chunk78, pack_E6970Receipt55_chunk79, pack_E6970Receipt55_chunk80, pack_E6970Receipt55_chunk81, pack_E6970Receipt55_chunk82, pack_E6970Receipt55_chunk83, pack_E6970Receipt55_chunk84, pack_E6970Receipt55_chunk85, pack_E6970Receipt55_chunk86, pack_E6970Receipt55_chunk87, pack_E6970Receipt55_chunk88, pack_E6970Receipt55_chunk89, pack_E6970Receipt55_chunk90, pack_E6970Receipt55_chunk91, pack_E6970Receipt55_chunk92, pack_E6970Receipt55_chunk93, pack_E6970Receipt55_chunk94, pack_E6970Receipt55_chunk95, pack_E6970Receipt55_chunk96, pack_E6970Receipt55_chunk97, pack_E6970Receipt55_chunk98, pack_E6970Receipt55_chunk99, pack_E6970Receipt55_chunk100, pack_E6970Receipt55_chunk101, pack_E6970Receipt55_chunk102, pack_E6970Receipt55_chunk103, pack_E6970Receipt55_chunk104, pack_E6970Receipt55_chunk105, pack_E6970Receipt55_chunk106, pack_E6970Receipt55_chunk107, pack_E6970Receipt55_chunk108, pack_E6970Receipt55_chunk109, pack_E6970Receipt55_chunk110, pack_E6970Receipt55_chunk111, pack_E6970Receipt55_chunk112, pack_E6970Receipt55_chunk113, pack_E6970Receipt55_chunk114, pack_E6970Receipt55_chunk115, pack_E6970Receipt55_chunk116, pack_E6970Receipt55_chunk117, pack_E6970Receipt55_chunk118, pack_E6970Receipt55_chunk119, pack_E6970Receipt55_chunk120, pack_E6970Receipt55_chunk121, pack_E6970Receipt55_chunk122, pack_E6970Receipt55_chunk123, pack_E6970Receipt55_chunk124, pack_E6970Receipt55_chunk125, pack_E6970Receipt55_chunk126, pack_E6970Receipt55_chunk127, pack_E6970Receipt55_chunk128, pack_E6970Receipt55_chunk129, pack_E6970Receipt55_chunk130, pack_E6970Receipt55_chunk131, pack_E6970Receipt55_chunk132, pack_E6970Receipt55_chunk133, pack_E6970Receipt55_chunk134, pack_E6970Receipt55_chunk135, pack_E6970Receipt55_chunk136, pack_E6970Receipt55_chunk137, pack_E6970Receipt55_chunk138, pack_E6970Receipt55_chunk139, pack_E6970Receipt55_chunk140, pack_E6970Receipt55_chunk141, pack_E6970Receipt55_chunk142, pack_E6970Receipt55_chunk143, pack_E6970Receipt55_chunk144, pack_E6970Receipt55_chunk145, pack_E6970Receipt55_chunk146, pack_E6970Receipt55_chunk147, pack_E6970Receipt55_chunk148, pack_E6970Receipt55_chunk149, pack_E6970Receipt55_chunk150, pack_E6970Receipt55_chunk151, pack_E6970Receipt55_chunk152, pack_E6970Receipt55_chunk153, pack_E6970Receipt55_chunk154, pack_E6970Receipt55_chunk155, pack_E6970Receipt55_chunk156, pack_E6970Receipt55_chunk157, pack_E6970Receipt55_chunk158, pack_E6970Receipt55_chunk159, pack_E6970Receipt55_chunk160, pack_E6970Receipt55_chunk161, pack_E6970Receipt55_chunk162, pack_E6970Receipt55_chunk163, pack_E6970Receipt55_chunk164, pack_E6970Receipt55_chunk165, pack_E6970Receipt55_chunk166, pack_E6970Receipt55_chunk167, pack_E6970Receipt55_chunk168, pack_E6970Receipt55_chunk169, pack_E6970Receipt55_chunk170, pack_E6970Receipt55_chunk171, pack_E6970Receipt55_chunk172, pack_E6970Receipt55_chunk173, pack_E6970Receipt55_chunk174, pack_E6970Receipt55_chunk175, pack_E6970Receipt55_chunk176, pack_E6970Receipt55_chunk177, pack_E6970Receipt55_chunk178, pack_E6970Receipt55_chunk179, pack_E6970Receipt55_chunk180, pack_E6970Receipt55_chunk181, pack_E6970Receipt55_chunk182, pack_E6970Receipt55_chunk183, pack_E6970Receipt55_chunk184, pack_E6970Receipt55_chunk185, pack_E6970Receipt55_chunk186, pack_E6970Receipt55_chunk187, pack_E6970Receipt55_chunk188, pack_E6970Receipt55_chunk189, pack_E6970Receipt55_chunk190, pack_E6970Receipt55_chunk191, pack_E6970Receipt55_chunk192, pack_E6970Receipt55_chunk193, pack_E6970Receipt55_chunk194, pack_E6970Receipt55_chunk195, pack_E6970Receipt55_chunk196, pack_E6970Receipt55_chunk197, pack_E6970Receipt55_chunk198, pack_E6970Receipt55_chunk199, pack_E6970Receipt55_chunk200, pack_E6970Receipt55_chunk201, pack_E6970Receipt55_chunk202, pack_E6970Receipt55_chunk203, pack_E6970Receipt55_chunk204, pack_E6970Receipt55_chunk205, pack_E6970Receipt55_chunk206, pack_E6970Receipt55_chunk207, pack_E6970Receipt55_chunk208, pack_E6970Receipt55_chunk209, pack_E6970Receipt55_chunk210, pack_E6970Receipt55_chunk211, pack_E6970Receipt55_chunk212, pack_E6970Receipt55_chunk213, pack_E6970Receipt55_chunk214, pack_E6970Receipt55_chunk215, pack_E6970Receipt55_chunk216, pack_E6970Receipt55_chunk217, pack_E6970Receipt55_chunk218, pack_E6970Receipt55_chunk219, pack_E6970Receipt55_chunk220, pack_E6970Receipt55_chunk221, pack_E6970Receipt55_chunk222, pack_E6970Receipt55_chunk223, pack_E6970Receipt55_chunk224, pack_E6970Receipt55_chunk225, pack_E6970Receipt55_chunk226, pack_E6970Receipt55_chunk227, pack_E6970Receipt55_chunk228, pack_E6970Receipt55_chunk229, pack_E6970Receipt55_chunk230, pack_E6970Receipt55_chunk231, pack_E6970Receipt55_chunk232, pack_E6970Receipt55_chunk233, pack_E6970Receipt55_chunk234, pack_E6970Receipt55_chunk235, pack_E6970Receipt55_chunk236, pack_E6970Receipt55_chunk237, pack_E6970Receipt55_chunk238, pack_E6970Receipt55_chunk239, pack_E6970Receipt55_chunk240, pack_E6970Receipt55_chunk241, pack_E6970Receipt55_chunk242, pack_E6970Receipt55_chunk243, pack_E6970Receipt55_chunk244, pack_E6970Receipt55_chunk245, pack_E6970Receipt55_chunk246, pack_E6970Receipt55_chunk247, pack_E6970Receipt55_chunk248, pack_E6970Receipt55_chunk249, pack_E6970Receipt55_chunk250, pack_E6970Receipt55_chunk251, pack_E6970Receipt55_chunk252]
def rows55 := rowsFrom pack_E6970Receipt55_chunks
theorem good55 : ∀ r ∈ rows55, good 55 r = true := rowsFrom_good pack_E6970Receipt55_chunks
theorem sorted55 : rows55.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt55_chunks 0 (by decide +kernel)).1
theorem mass55 (i : Fin 61) :
    bandCount 55 (i.val : ℤ) 60 16 ≤ (rows55.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt55_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 55 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt55_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total55 : (rows55.map (price 55)).sum = 388861 :=
  (total_eq pack_E6970Receipt55_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt55

section Pack_E6970Receipt56

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt56_chunk0 := witnessA6966Final 56 60 0 1080004 1080070 32 3982
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk1 := witnessA6966Final 56 60 32 1080071 1080137 32 3932
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk2 := witnessA6966Final 56 60 64 1080138 1080205 32 3800
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk3 := witnessA6966Final 56 60 96 1080206 1080275 32 3648
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk4 := witnessA6966Final 56 60 128 1080276 1080387 32 3586
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk5 := witnessA6966Final 56 60 160 1080388 1080461 32 3504
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk6 := witnessA6966Final 56 60 192 1080462 1080582 32 3350
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk7 := witnessA6966Final 56 60 224 1080583 1080709 32 3196
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk8 := witnessA6966Final 56 60 256 1080710 1080842 32 2994
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk9 := witnessA6966Final 56 60 288 1080896 1081030 25 2199
  0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk10 := witnessRule 56 59 0 1090003 1090069 32 3804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk11 := witnessRule 56 59 32 1090070 1090136 32 3690
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk12 := witnessRule 56 59 64 1090137 1090205 32 3582
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk13 := witnessRule 56 59 96 1090206 1090275 32 3396
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk14 := witnessRule 56 59 128 1090276 1090388 32 3368
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk15 := witnessRule 56 59 160 1090389 1090463 32 3234
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk16 := witnessRule 56 59 192 1090464 1090585 32 3126
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk17 := witnessRule 56 59 224 1090586 1090713 32 2936
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk18 := witnessRule 56 59 256 1090714 1090900 32 2756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk19 := witnessRule 56 59 288 1090901 1091029 18 1438
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk20 := witnessRule 56 58 0 1100002 1100067 32 3598
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk21 := witnessRule 56 58 32 1100068 1100135 32 3496
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk22 := witnessRule 56 58 64 1100136 1100204 32 3348
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk23 := witnessRule 56 58 96 1100205 1100275 32 3168
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk24 := witnessRule 56 58 128 1100276 1100389 32 3154
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk25 := witnessRule 56 58 160 1100390 1100464 32 2962
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk26 := witnessRule 56 58 192 1100465 1100587 32 2892
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk27 := witnessRule 56 58 224 1100588 1100716 32 2684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk28 := witnessRule 56 58 256 1100768 1100960 32 2524
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk29 := witnessRule 56 58 288 1100961 1101029 12 896
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk30 := witnessRule 56 57 0 1110001 1110067 32 3422
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk31 := witnessRule 56 57 32 1110068 1110135 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk32 := witnessRule 56 57 64 1110136 1110205 32 3120
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk33 := witnessRule 56 57 96 1110206 1110276 32 2912
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk34 := witnessRule 56 57 128 1110277 1110391 32 2954
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk35 := witnessRule 56 57 160 1110392 1110512 32 2710
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk36 := witnessRule 56 57 192 1110513 1110591 32 2628
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk37 := witnessRule 56 57 224 1110640 1110772 32 2498
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk38 := witnessRule 56 57 256 1110773 1111024 32 2280
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk39 := witnessRule 56 57 288 1111025 1111028 4 276
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk40 := witnessRule 56 56 0 1120000 1120066 32 3216
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk41 := witnessRule 56 56 32 1120067 1120135 32 3052
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk42 := witnessRule 56 56 64 1120136 1120205 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk43 := witnessRule 56 56 96 1120206 1120277 32 2684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk44 := witnessRule 56 56 128 1120278 1120393 32 2742
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk45 := witnessRule 56 56 160 1120394 1120515 32 2516
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk46 := witnessRule 56 56 192 1120516 1120643 32 2398
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk47 := witnessRule 56 56 224 1120644 1120777 32 2226
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk48 := witnessRule 56 56 256 1120778 1121028 29 1941
  0x1fffbfff 0xb99a (by decide +kernel)
private def pack_E6970Receipt56_chunk49 := witnessRule 56 55 0 1130000 1130067 32 3016
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk50 := witnessRule 56 55 32 1130068 1130136 32 2802
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk51 := witnessRule 56 55 64 1130137 1130207 32 2634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk52 := witnessRule 56 55 96 1130208 1130321 32 2506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk53 := witnessRule 56 55 128 1130322 1130396 32 2465
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk54 := witnessRule 56 55 160 1130397 1130519 32 2323
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk55 := witnessRule 56 55 192 1130520 1130648 32 2182
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk56 := witnessRule 56 55 224 1130649 1130837 32 2090
  0x7fffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt56_chunk57 := witnessRule 56 55 256 1130838 1131027 20 1282
  0xfffbf 0xba1a (by decide +kernel)
private def pack_E6970Receipt56_chunk58 := witnessRule 56 54 0 1140000 1140067 32 2785
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk59 := witnessRule 56 54 32 1140068 1140137 32 2590
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk60 := witnessRule 56 54 64 1140138 1140208 32 2397
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk61 := witnessRule 56 54 96 1140209 1140323 32 2349
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk62 := witnessRule 56 54 128 1140324 1140399 32 2231
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk63 := witnessRule 56 54 160 1140400 1140523 32 2155
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk64 := witnessRule 56 54 192 1140524 1140704 32 2051
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk65 := witnessRule 56 54 224 1140705 1140899 32 2004
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt56_chunk66 := witnessRule 56 54 256 1140900 1141027 12 746
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk67 := witnessRule 56 53 0 1150000 1150068 32 2599
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk68 := witnessRule 56 53 32 1150069 1150138 32 2366
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk69 := witnessRule 56 53 64 1150139 1150210 32 2213
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk70 := witnessRule 56 53 96 1150211 1150326 32 2203
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk71 := witnessRule 56 53 128 1150327 1150448 32 2070
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk72 := witnessRule 56 53 160 1150449 1150576 32 2018
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk73 := witnessRule 56 53 192 1150577 1150710 32 1963
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt56_chunk74 := witnessRule 56 53 224 1150711 1150964 32 1927
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt56_chunk75 := witnessRule 56 53 256 1151024 1151026 3 183
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk76 := witnessRule 56 52 0 1160000 1160068 32 2409
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk77 := witnessRule 56 52 32 1160069 1160139 32 2187
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk78 := witnessRule 56 52 64 1160140 1160211 32 2074
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk79 := witnessRule 56 52 96 1160212 1160328 32 2057
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk80 := witnessRule 56 52 128 1160329 1160451 32 1968
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk81 := witnessRule 56 52 160 1160452 1160580 32 1918
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk82 := witnessRule 56 52 192 1160581 1160769 32 1879
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt56_chunk83 := witnessRule 56 52 224 1160770 1161026 27 1579
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt56_chunk84 := witnessRule 56 51 0 1170000 1170069 32 2248
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk85 := witnessRule 56 51 32 1170070 1170140 32 2032
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk86 := witnessRule 56 51 64 1170141 1170213 32 1955
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk87 := witnessRule 56 51 96 1170256 1170331 32 1948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk88 := witnessRule 56 51 128 1170332 1170455 32 1875
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk89 := witnessRule 56 51 160 1170456 1170585 32 1832
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt56_chunk90 := witnessRule 56 51 192 1170586 1170775 32 1806
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt56_chunk91 := witnessRule 56 51 224 1170832 1171025 18 1026
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt56_chunk92 := witnessRule 56 50 0 1180000 1180069 32 2096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk93 := witnessRule 56 50 32 1180070 1180141 32 1924
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk94 := witnessRule 56 50 64 1180142 1180257 32 1870
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk95 := witnessRule 56 50 96 1180258 1180333 32 1837
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk96 := witnessRule 56 50 128 1180334 1180458 32 1790
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk97 := witnessRule 56 50 160 1180459 1180641 32 1759
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt56_chunk98 := witnessRule 56 50 192 1180642 1180837 32 1743
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt56_chunk99 := witnessRule 56 50 224 1180896 1181025 10 562
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk100 := witnessRule 56 49 0 1190000 1190070 32 1972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk101 := witnessRule 56 49 32 1190071 1190142 32 1825
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk102 := witnessRule 56 49 64 1190143 1190259 32 1782
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk103 := witnessRule 56 49 96 1190260 1190336 32 1739
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk104 := witnessRule 56 49 128 1190337 1190462 32 1713
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt56_chunk105 := witnessRule 56 49 160 1190512 1190646 32 1694
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt56_chunk106 := witnessRule 56 49 192 1190647 1190962 32 1703
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt56_chunk107 := witnessRule 56 49 224 1191024 1191024 1 56
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk108 := witnessRule 56 48 0 1200000 1200070 32 1854
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk109 := witnessRule 56 48 32 1200071 1200143 32 1736
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk110 := witnessRule 56 48 64 1200144 1200261 32 1698
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk111 := witnessRule 56 48 96 1200262 1200385 32 1659
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt56_chunk112 := witnessRule 56 48 128 1200386 1200515 32 1645
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt56_chunk113 := witnessRule 56 48 160 1200516 1200705 32 1623
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt56_chunk114 := witnessRule 56 48 192 1200706 1201024 25 1301
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk115 := witnessRule 56 47 0 1210000 1210071 32 1754
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk116 := witnessRule 56 47 32 1210072 1210144 32 1644
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk117 := witnessRule 56 47 64 1210145 1210263 32 1619
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk118 := witnessRule 56 47 96 1210264 1210388 32 1590
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt56_chunk119 := witnessRule 56 47 128 1210389 1210519 32 1571
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt56_chunk120 := witnessRule 56 47 160 1210520 1210711 32 1568
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt56_chunk121 := witnessRule 56 47 192 1210768 1210961 16 819
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk122 := witnessRule 56 46 0 1220000 1220071 32 1659
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk123 := witnessRule 56 46 32 1220072 1220145 32 1559
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk124 := witnessRule 56 46 64 1220146 1220265 32 1549
  0xb6bfffff 0x5766336ee8c66e5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt56_chunk125 := witnessRule 56 46 96 1220266 1220391 32 1521
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt56_chunk126 := witnessRule 56 46 128 1220392 1220523 32 1503
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt56_chunk127 := witnessRule 56 46 160 1220576 1220773 32 1532
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt56_chunk128 := witnessRule 56 46 192 1220832 1220960 8 405
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk129 := witnessRule 56 45 0 1230000 1230072 32 1577
  0xfaffffaf 0xb716337ae28a9c98cddba1a (by decide +kernel)
private def pack_E6970Receipt56_chunk130 := witnessRule 56 45 32 1230073 1230146 32 1477
  0xffffdfff 0x6399a (by decide +kernel)
private def pack_E6970Receipt56_chunk131 := witnessRule 56 45 64 1230147 1230267 32 1481
  0x920edb69 0x37864368f0c66d5d990db3b319b77464370e6c662121c994dcb8b21884976342f6c66cde58cdabbb19b77563372e6c66e9c590ddb99883 (by decide +kernel)
private def pack_E6970Receipt56_chunk132 := witnessRule 56 45 96 1230268 1230394 32 1453
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt56_chunk133 := witnessRule 56 45 128 1230395 1230580 32 1450
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt56_chunk134 := witnessRule 56 45 160 1230581 1230960 32 1514
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk135 := witnessRule 56 44 0 1240000 1240072 32 1495
  0xaa7ffaab 0x21d58cdcb9b21ba716537ae2a20f5c493bb319b87464372e4ca6f1c5854426b892 (by decide +kernel)
private def pack_E6970Receipt56_chunk136 := witnessRule 56 44 32 1240073 1240147 32 1405
  0xedb68fff 0x17c63366f4c66d5e18cdbbb319b97463374e4c86edc58cc425ba9a (by decide +kernel)
private def pack_E6970Receipt56_chunk137 := witnessRule 56 44 64 1240192 1240269 32 1413
  0x80039240 0xbd329b27a64366f2c66210de194da3c321b577633108aecca6d9d590c4233a331b773653108ee4ce6e1c598c4243c1a17b64364f6c66cde590da3cb19b5776436ceec66ddd590dc3a31988487365372e4c862125c598dd3a9883 (by decide +kernel)
private def pack_E6970Receipt56_chunk138 := witnessRule 56 44 96 1240270 1240397 32 1391
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt56_chunk139 := witnessRule 56 44 128 1240448 1240584 32 1403
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt56_chunk140 := witnessRule 56 44 160 1240640 1240897 24 1114
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk141 := witnessRule 56 43 0 1250000 1250073 32 1422
  0x143faa81 0x19dd90dbbb31988477565374e8c2a212dc98544c42db8b0a99cc71523108318e28d1e98cdabc321b67665372eac2a2129cd8544c42d3930a99cb716152310b6e2a86f5c95638a093 (by decide +kernel)
private def pack_E6970Receipt56_chunk142 := witnessRule 56 43 32 1250074 1250193 32 1344
  0x3924076d 0x21c5a0dcbb988317c64364f8c66cde990da3d319b5786436cf0c66ddd990dc3ab1988487465372e6c862125c998dd38b29884a77342fac66cded8cdabcb19b (by decide +kernel)
private def pack_E6970Receipt56_chunk143 := witnessRule 56 43 64 1250194 1250271 32 1336
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4796436af0c662115dd94db3b3218846756636ee8ca6211dcd9cdc39331884 (by decide +kernel)
private def pack_E6970Receipt56_chunk144 := witnessRule 56 43 96 1250320 1250451 32 1342
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt56_chunk145 := witnessRule 56 43 128 1250452 1250644 32 1363
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt56_chunk146 := witnessRule 56 43 160 1250645 1250896 16 731
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk147 := witnessRule 56 42 0 1260000 1260073 32 1349
  0x403a2801 0x57766370ecc2a262161d5854ce4ba30a918859736154394e4c2a662169c58554e14538b09c28b71062fcc66c9f190d9bdb1988437a6536cf2c2a211ddd8544c42bbb30a99c8756152310b0e8c2a8729d1895cb930aa9cb726251398e2c4a2131c948deb8a093 (by decide +kernel)
private def pack_E6970Receipt56_chunk148 := witnessRule 56 42 32 1260074 1260194 32 1283
  0x1e000390 0x772683108ee2d46e1e4c418be329b27c64366f6c66210de994da3d321b579633108af0ca6d9dd90c4233b331b775653108ee8ce6e1cd98c42439341b9716731092f2685f590d93eb19b37b64368f4c662111e594dabc321884 (by decide +kernel)
private def pack_E6970Receipt56_chunk149 := witnessRule 56 42 64 1260195 1260321 32 1277
  0x3e003c00 0x8e2da6d5f0c418bd339b2796631084f0d06cddd9cc421bb349b4756831088e8d46d5cda4c422b9359b6716a3108cf8685ed98d93db29b37a6431086f2cc6d1e194c4223bb39b576663108aead06d9d19cc42339b49b (by decide +kernel)
private def pack_E6970Receipt56_chunk150 := witnessRule 56 42 96 1260322 1260454 32 1281
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt56_chunk151 := witnessRule 56 42 128 1260455 1260706 32 1341
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk152 := witnessRule 56 42 160 1260707 1260896 9 407
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk153 := witnessRule 56 41 0 1270000 1270074 32 1281
  0x108000 0x15e5854ce33c30a91885677615438eecc2a66215dd58554e43a30aa1885873615638510e6c470a25c984c42944b8b19c28a723109ec6620f994d0beb2188417c66368f6c2a262151e9854ce2bcb0a91885578615438ceec2a662159d98554e43b31289c9756251092e8c4a4729cd8944c42d3931299cb716252310b6e4a86ca2dc55eb912 (by decide +kernel)
private def pack_E6970Receipt56_chunk154 := witnessRule 56 41 32 1270075 1270196 32 1224
  0x78001c0 0x2ba3498845736b36ce4d462119c5b0dbbd988317c66364f8ca6cded90c421bd331b4796531088f0ce6d5dd98c422bb341b675673108ce8d26ddcda0c423b9351b8716931090f6685f98cc420beb29b27c6431084f6cc6cde994c421bcb39b (by decide +kernel)
private def pack_E6970Receipt56_chunk155 := witnessRule 56 41 64 1270197 1270324 32 1218
  0x7e00f80 0x13a3618842736e366e4da6210dc5bcda3f18831786a364eed262109d9acd9bab518843746c368e6d662111c9b4dab8b6188457e342f6ce6c9e998c4213cb41b3786731086eed26d1d9a0c4223ab51b (by decide +kernel)
private def pack_E6970Receipt56_chunk156 := witnessRule 56 41 96 1270325 1270458 32 1232
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt56_chunk157 := witnessRule 56 41 128 1270512 1270832 32 1332
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk158 := witnessRule 56 41 160 1270833 1270833 1 45
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk159 := witnessRule 56 40 0 1280000 1280074 32 1212
  0x180000 0x11e58554e2bc30aa1885577615638cecc2aa62159d5855ce1433ab19c2877462310a50ee6c870a21c98cc4294438b29c289743109cc2a86c5f9854ce13eb0a9188527c6154386f6c2a66214de98554e23cb0aa1885478615638cf0c4a471ddd8944c42bbb31299c8756252310b0e8c4a8725cd894cc42cb9312a9c2897261513a514e2c2a214a29c548e0c638a094 (by decide +kernel)
private def pack_E6970Receipt56_chunk160 := witnessRule 56 40 32 1280075 1280197 32 1165
  0x3e000c0 0x1bab61b4746b31088e6da6d5c9b0c422b8b71b67d31062f8ce6c9ed98c4213d341b3796731086f0d26d1dda0c4223b351b575693108ae8d66d9cda8c42339361b7716b3108efa6b994c41eb39a17c6631082f6d06cded8550e23d30a99885 (by decide +kernel)
private def pack_E6970Receipt56_chunk161 := witnessRule 56 40 64 1280198 1280326 32 1161
  0xe1fe03f0 0x2e6c801b2726f31084e2c881b37400c418bb369b2756c31084e8dc6cdcdb4c421b9379b4716e31088e801a1796a364f0d262109ddacd9bb351884 (by decide +kernel)
private def pack_E6970Receipt56_chunk162 := witnessRule 56 40 96 1280327 1280515 32 1200
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt56_chunk163 := witnessRule 56 40 128 1280516 1280832 26 1062
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk164 := witnessRule 56 39 0 1290000 1290075 32 1146
  0x80000 0x6f4c2aa6214de5855ce23c30ab1885477615838508eec870a15d98cc42942bab29c2867464310a50ce6cc70a1dc994c42943b8b39c288763109ec2a6621398554d8beb0aa188517c6156384f6c2aa62149e9855ce23d31299c5796252310aaf0c4a8719dd894cc42b3b312a9c7756254310aee8c4ac70a1dd18548e94439b0a898862887261533a512e2c2a46218a25c550e1c5388b (by decide +kernel)
private def pack_E6970Receipt56_chunk165 := witnessRule 56 39 32 1290076 1290199 32 1106
  0xfc0070 0xbbb69b2766c31084eadc6cdd1b4c421b9b79b4726e31088e2c801b57f31062f4d46c9e5a4c4213c359b3776a31086ecd86d1d5acc4223a369b5736c3108ae4dc6d9c5b4c4233f9ad6156362fac2aa709f18550c4293db0ab1c (by decide +kernel)
private def pack_E6970Receipt56_chunk166 := witnessRule 56 39 64 1290200 1290329 32 1111
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt56_chunk167 := witnessRule 56 39 96 1290330 1290519 32 1176
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk168 := witnessRule 56 39 128 1290576 1290832 19 764
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk169 := witnessRule 56 38 0 1300000 1300075 32 1080
  0x800c0000 0x13cb0ac9c282796538506f0c86214a0ddd98e1423b32988528475673850ae8cc6214a15cda0e1433933988528671693850ef0621398950deb0ab1884c6158364f8c4a870ded894cc429bd312a9c4796254310a8f0c4ac715dd8954c42abb312b9c2857661533a50ceac2a46218a19d18550e943b9b0a998862877261553a510e2c2a86218a21c558e244391b (by decide +kernel)
private def pack_E6970Receipt56_chunk170 := witnessRule 56 38 32 1300076 1300200 32 1049
  0xe07f8030 0xbab2006c9d1bcc42139b2206cdc990031086e2c901b47440c418bc369b2776c31084ecdc6cdd5b4c421ba379b4736e31088e4c801b5716f3108ae881ae61553109ac2ae6c5f18558c428bdb0ac1c (by decide +kernel)
private def pack_E6970Receipt56_chunk171 := witnessRule 56 38 64 1300201 1300331 32 1071
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt56_chunk172 := witnessRule 56 38 96 1300384 1300579 32 1157
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk173 := witnessRule 56 38 128 1300580 1300769 12 473
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk174 := witnessRule 56 37 0 1310000 1310076 32 1013
  0x60040000 0x5b0ad1b281796738504f0cc6214a09dda0e141bb339885283756938508e8d06214a11cda8e142b9349885285716b3850cf462139894cc827312a9b17d6254310a2f8c4ac709ed8954c4293d312b9c3796256310a6f0c4b070a0de18550e9423bb0a998862847661553a50aeac2a86218a15d18558e94339b0aa98862867261573a90ce4c67121dc588c42a43ba1b (by decide +kernel)
private def pack_E6970Receipt56_chunk175 := witnessRule 56 37 32 1310077 1310202 32 999
  0xfe1ff01d 0x17364c0d939324062109c5940366e9818831766400d93ab798842746440d9b9b2006210dc9920368e2c881884474c0d6b0ab1904 (by decide +kernel)
private def pack_E6970Receipt56_chunk176 := witnessRule 56 37 64 1310203 1310386 32 1041
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt56_chunk177 := witnessRule 56 37 96 1310387 1310642 32 1141
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk178 := witnessRule 56 37 128 1310643 1310768 5 195
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk179 := witnessRule 56 36 0 1320000 1320076 32 952
  0xf8060000 0x140bbb51c2827669310a504ead670a0dd1a8c42941b9b61c284726b310a508e2da70a15f0c427312a1904d625631098c4b06c5ed895cc428bd312c9c2817a61553a504f2c2a86218a09e18558e941bbb0aa98862837661573a508eac2ac6218a11d18560ea423a321c4857363310a90ae4ca71219c590c42a433b1b (by decide +kernel)
private def pack_E6970Receipt56_chunk180 := witnessRule 56 36 32 1320077 1320203 32 954
  0xffdffe0f 0x5c5960362e8c981b2736480c4213932806cdc593031086ea81a (by decide +kernel)
private def pack_E6970Receipt56_chunk181 := witnessRule 56 36 64 1320204 1320389 32 1013
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk182 := witnessRule 56 36 96 1320390 1320768 31 1092
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk183 := witnessRule 56 35 0 1330000 1330077 32 895
  0xff020100 0xa05d5b4e1413a361885282736e38506e4da6214a0dc5bce1423f1884e62533409ac4aa66131895cc825b12c988428b6155310a514c2ae70a05e58558c43140bc30ac1d2827661593a904ecca7120dd590c42a41ba331c4847365310a908e4ce71215c598c42a42bc1b (by decide +kernel)
private def pack_E6970Receipt56_chunk184 := witnessRule 56 35 32 1330078 1330205 32 915
  0xffffffc7 0xb932c06c9c595031084eb81a (by decide +kernel)
private def pack_E6970Receipt56_chunk185 := witnessRule 56 35 64 1330256 1330392 32 989
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk186 := witnessRule 56 35 96 1330448 1330705 24 825
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk187 := witnessRule 56 34 0 1340000 1340077 32 844
  0xffc35580 0x140b9b20070a09c9bcc4294138b22070a0dd003109ac4a86a12d8960cc214530ab1905288615a38902ecce71209d598c42a413a341c4837367310a906e4d271211c5a0c42a423d1b (by decide +kernel)
private def pack_E6970Receipt56_chunk188 := witnessRule 56 34 32 1340078 1340257 32 881
  0xfffffffb 0x2ec81a (by decide +kernel)
private def pack_E6970Receipt56_chunk189 := witnessRule 56 34 64 1340258 1340450 32 965
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk190 := witnessRule 56 34 96 1340451 1340704 18 603
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk191 := witnessRule 56 33 0 1350000 1350078 32 799
  0xfffbffe0 0x2817164c0e240ba351c4827369310a904e4d67120dc5a8c42a41be1b (by decide +kernel)
private def pack_E6970Receipt56_chunk192 := witnessRule 56 33 32 1350079 1350259 32 852
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk193 := witnessRule 56 33 64 1350260 1350454 32 943
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk194 := witnessRule 56 33 96 1350512 1350704 12 395
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk195 := witnessRule 56 32 0 1360000 1360078 32 758
  0xfffffff8 0x902e4da71209c5b0c42a413f1b (by decide +kernel)
private def pack_E6970Receipt56_chunk196 := witnessRule 56 32 32 1360128 1360261 32 824
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk197 := witnessRule 56 32 64 1360262 1360515 32 923
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk198 := witnessRule 56 32 96 1360516 1360641 6 193
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk199 := witnessRule 56 31 0 1370000 1370128 32 723
  0xfffffffe 0x902e801b (by decide +kernel)
private def pack_E6970Receipt56_chunk200 := witnessRule 56 31 32 1370129 1370263 32 796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk201 := witnessRule 56 31 64 1370264 1370640 32 910
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk202 := witnessRule 56 30 0 1380000 1380129 32 690
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk203 := witnessRule 56 30 32 1380130 1380265 32 767
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk204 := witnessRule 56 30 64 1380320 1380640 27 744
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk205 := witnessRule 56 29 0 1390000 1390130 32 660
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk206 := witnessRule 56 29 32 1390131 1390322 32 742
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk207 := witnessRule 56 29 64 1390323 1390577 21 558
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk208 := witnessRule 56 28 0 1400000 1400131 32 629
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk209 := witnessRule 56 28 32 1400132 1400324 32 715
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk210 := witnessRule 56 28 64 1400325 1400576 16 411
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk211 := witnessRule 56 27 0 1410000 1410132 32 599
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk212 := witnessRule 56 27 32 1410133 1410384 32 691
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk213 := witnessRule 56 27 64 1410385 1410576 11 275
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk214 := witnessRule 56 26 0 1420000 1420133 32 568
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk215 := witnessRule 56 26 32 1420134 1420387 32 667
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk216 := witnessRule 56 26 64 1420388 1420513 6 145
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk217 := witnessRule 56 25 0 1430000 1430134 32 538
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk218 := witnessRule 56 25 32 1430135 1430450 32 648
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk219 := witnessRule 56 25 64 1430512 1430512 1 24
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk220 := witnessRule 56 24 0 1440000 1440135 32 507
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk221 := witnessRule 56 24 32 1440136 1440512 29 562
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk222 := witnessRule 56 23 0 1450000 1450136 32 477
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk223 := witnessRule 56 23 32 1450192 1450449 24 441
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk224 := witnessRule 56 22 0 1460000 1460192 32 447
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk225 := witnessRule 56 22 32 1460193 1460448 20 347
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk226 := witnessRule 56 21 0 1470000 1470194 32 419
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk227 := witnessRule 56 21 32 1470195 1470448 16 263
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk228 := witnessRule 56 20 0 1480000 1480195 32 389
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk229 := witnessRule 56 20 32 1480196 1480385 12 185
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk230 := witnessRule 56 19 0 1490000 1490197 32 361
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk231 := witnessRule 56 19 32 1490256 1490384 8 117
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk232 := witnessRule 56 18 0 1500000 1500257 32 333
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk233 := witnessRule 56 18 32 1500258 1500384 5 69
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk234 := witnessRule 56 17 0 1510000 1510320 32 308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk235 := witnessRule 56 17 32 1510321 1510321 1 13
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk236 := witnessRule 56 16 0 1520000 1520320 30 258
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk237 := witnessRule 56 15 0 1530000 1530320 27 204
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk238 := witnessRule 56 14 0 1540000 1540257 24 153
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk239 := witnessRule 56 13 0 1550000 1550256 21 111
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk240 := witnessRule 56 12 0 1560000 1560256 19 80
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk241 := witnessRule 56 11 0 1570000 1570193 16 49
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk242 := witnessRule 56 10 0 1580000 1580192 14 27
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk243 := witnessRule 56 9 0 1590000 1590192 12 11
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk244 := witnessRule 56 8 0 1600000 1600129 10 2
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk245 := witnessRule 56 7 0 1610000 1610128 8 0
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk246 := witnessRule 56 6 0 1620000 1620128 7 0
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk247 := witnessRule 56 5 0 1630000 1630065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk248 := witnessRule 56 4 0 1640000 1640064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk249 := witnessRule 56 3 0 1650000 1650064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk250 := witnessRule 56 2 0 1660000 1660001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk251 := witnessRule 56 1 0 1670000 1670000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt56_chunk252 := witnessRule 56 0 0 1680000 1680000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt56_chunks : List (Chunk 56) := [pack_E6970Receipt56_chunk0, pack_E6970Receipt56_chunk1, pack_E6970Receipt56_chunk2, pack_E6970Receipt56_chunk3, pack_E6970Receipt56_chunk4, pack_E6970Receipt56_chunk5, pack_E6970Receipt56_chunk6, pack_E6970Receipt56_chunk7, pack_E6970Receipt56_chunk8, pack_E6970Receipt56_chunk9, pack_E6970Receipt56_chunk10, pack_E6970Receipt56_chunk11, pack_E6970Receipt56_chunk12, pack_E6970Receipt56_chunk13, pack_E6970Receipt56_chunk14, pack_E6970Receipt56_chunk15, pack_E6970Receipt56_chunk16, pack_E6970Receipt56_chunk17, pack_E6970Receipt56_chunk18, pack_E6970Receipt56_chunk19, pack_E6970Receipt56_chunk20, pack_E6970Receipt56_chunk21, pack_E6970Receipt56_chunk22, pack_E6970Receipt56_chunk23, pack_E6970Receipt56_chunk24, pack_E6970Receipt56_chunk25, pack_E6970Receipt56_chunk26, pack_E6970Receipt56_chunk27, pack_E6970Receipt56_chunk28, pack_E6970Receipt56_chunk29, pack_E6970Receipt56_chunk30, pack_E6970Receipt56_chunk31, pack_E6970Receipt56_chunk32, pack_E6970Receipt56_chunk33, pack_E6970Receipt56_chunk34, pack_E6970Receipt56_chunk35, pack_E6970Receipt56_chunk36, pack_E6970Receipt56_chunk37, pack_E6970Receipt56_chunk38, pack_E6970Receipt56_chunk39, pack_E6970Receipt56_chunk40, pack_E6970Receipt56_chunk41, pack_E6970Receipt56_chunk42, pack_E6970Receipt56_chunk43, pack_E6970Receipt56_chunk44, pack_E6970Receipt56_chunk45, pack_E6970Receipt56_chunk46, pack_E6970Receipt56_chunk47, pack_E6970Receipt56_chunk48, pack_E6970Receipt56_chunk49, pack_E6970Receipt56_chunk50, pack_E6970Receipt56_chunk51, pack_E6970Receipt56_chunk52, pack_E6970Receipt56_chunk53, pack_E6970Receipt56_chunk54, pack_E6970Receipt56_chunk55, pack_E6970Receipt56_chunk56, pack_E6970Receipt56_chunk57, pack_E6970Receipt56_chunk58, pack_E6970Receipt56_chunk59, pack_E6970Receipt56_chunk60, pack_E6970Receipt56_chunk61, pack_E6970Receipt56_chunk62, pack_E6970Receipt56_chunk63, pack_E6970Receipt56_chunk64, pack_E6970Receipt56_chunk65, pack_E6970Receipt56_chunk66, pack_E6970Receipt56_chunk67, pack_E6970Receipt56_chunk68, pack_E6970Receipt56_chunk69, pack_E6970Receipt56_chunk70, pack_E6970Receipt56_chunk71, pack_E6970Receipt56_chunk72, pack_E6970Receipt56_chunk73, pack_E6970Receipt56_chunk74, pack_E6970Receipt56_chunk75, pack_E6970Receipt56_chunk76, pack_E6970Receipt56_chunk77, pack_E6970Receipt56_chunk78, pack_E6970Receipt56_chunk79, pack_E6970Receipt56_chunk80, pack_E6970Receipt56_chunk81, pack_E6970Receipt56_chunk82, pack_E6970Receipt56_chunk83, pack_E6970Receipt56_chunk84, pack_E6970Receipt56_chunk85, pack_E6970Receipt56_chunk86, pack_E6970Receipt56_chunk87, pack_E6970Receipt56_chunk88, pack_E6970Receipt56_chunk89, pack_E6970Receipt56_chunk90, pack_E6970Receipt56_chunk91, pack_E6970Receipt56_chunk92, pack_E6970Receipt56_chunk93, pack_E6970Receipt56_chunk94, pack_E6970Receipt56_chunk95, pack_E6970Receipt56_chunk96, pack_E6970Receipt56_chunk97, pack_E6970Receipt56_chunk98, pack_E6970Receipt56_chunk99, pack_E6970Receipt56_chunk100, pack_E6970Receipt56_chunk101, pack_E6970Receipt56_chunk102, pack_E6970Receipt56_chunk103, pack_E6970Receipt56_chunk104, pack_E6970Receipt56_chunk105, pack_E6970Receipt56_chunk106, pack_E6970Receipt56_chunk107, pack_E6970Receipt56_chunk108, pack_E6970Receipt56_chunk109, pack_E6970Receipt56_chunk110, pack_E6970Receipt56_chunk111, pack_E6970Receipt56_chunk112, pack_E6970Receipt56_chunk113, pack_E6970Receipt56_chunk114, pack_E6970Receipt56_chunk115, pack_E6970Receipt56_chunk116, pack_E6970Receipt56_chunk117, pack_E6970Receipt56_chunk118, pack_E6970Receipt56_chunk119, pack_E6970Receipt56_chunk120, pack_E6970Receipt56_chunk121, pack_E6970Receipt56_chunk122, pack_E6970Receipt56_chunk123, pack_E6970Receipt56_chunk124, pack_E6970Receipt56_chunk125, pack_E6970Receipt56_chunk126, pack_E6970Receipt56_chunk127, pack_E6970Receipt56_chunk128, pack_E6970Receipt56_chunk129, pack_E6970Receipt56_chunk130, pack_E6970Receipt56_chunk131, pack_E6970Receipt56_chunk132, pack_E6970Receipt56_chunk133, pack_E6970Receipt56_chunk134, pack_E6970Receipt56_chunk135, pack_E6970Receipt56_chunk136, pack_E6970Receipt56_chunk137, pack_E6970Receipt56_chunk138, pack_E6970Receipt56_chunk139, pack_E6970Receipt56_chunk140, pack_E6970Receipt56_chunk141, pack_E6970Receipt56_chunk142, pack_E6970Receipt56_chunk143, pack_E6970Receipt56_chunk144, pack_E6970Receipt56_chunk145, pack_E6970Receipt56_chunk146, pack_E6970Receipt56_chunk147, pack_E6970Receipt56_chunk148, pack_E6970Receipt56_chunk149, pack_E6970Receipt56_chunk150, pack_E6970Receipt56_chunk151, pack_E6970Receipt56_chunk152, pack_E6970Receipt56_chunk153, pack_E6970Receipt56_chunk154, pack_E6970Receipt56_chunk155, pack_E6970Receipt56_chunk156, pack_E6970Receipt56_chunk157, pack_E6970Receipt56_chunk158, pack_E6970Receipt56_chunk159, pack_E6970Receipt56_chunk160, pack_E6970Receipt56_chunk161, pack_E6970Receipt56_chunk162, pack_E6970Receipt56_chunk163, pack_E6970Receipt56_chunk164, pack_E6970Receipt56_chunk165, pack_E6970Receipt56_chunk166, pack_E6970Receipt56_chunk167, pack_E6970Receipt56_chunk168, pack_E6970Receipt56_chunk169, pack_E6970Receipt56_chunk170, pack_E6970Receipt56_chunk171, pack_E6970Receipt56_chunk172, pack_E6970Receipt56_chunk173, pack_E6970Receipt56_chunk174, pack_E6970Receipt56_chunk175, pack_E6970Receipt56_chunk176, pack_E6970Receipt56_chunk177, pack_E6970Receipt56_chunk178, pack_E6970Receipt56_chunk179, pack_E6970Receipt56_chunk180, pack_E6970Receipt56_chunk181, pack_E6970Receipt56_chunk182, pack_E6970Receipt56_chunk183, pack_E6970Receipt56_chunk184, pack_E6970Receipt56_chunk185, pack_E6970Receipt56_chunk186, pack_E6970Receipt56_chunk187, pack_E6970Receipt56_chunk188, pack_E6970Receipt56_chunk189, pack_E6970Receipt56_chunk190, pack_E6970Receipt56_chunk191, pack_E6970Receipt56_chunk192, pack_E6970Receipt56_chunk193, pack_E6970Receipt56_chunk194, pack_E6970Receipt56_chunk195, pack_E6970Receipt56_chunk196, pack_E6970Receipt56_chunk197, pack_E6970Receipt56_chunk198, pack_E6970Receipt56_chunk199, pack_E6970Receipt56_chunk200, pack_E6970Receipt56_chunk201, pack_E6970Receipt56_chunk202, pack_E6970Receipt56_chunk203, pack_E6970Receipt56_chunk204, pack_E6970Receipt56_chunk205, pack_E6970Receipt56_chunk206, pack_E6970Receipt56_chunk207, pack_E6970Receipt56_chunk208, pack_E6970Receipt56_chunk209, pack_E6970Receipt56_chunk210, pack_E6970Receipt56_chunk211, pack_E6970Receipt56_chunk212, pack_E6970Receipt56_chunk213, pack_E6970Receipt56_chunk214, pack_E6970Receipt56_chunk215, pack_E6970Receipt56_chunk216, pack_E6970Receipt56_chunk217, pack_E6970Receipt56_chunk218, pack_E6970Receipt56_chunk219, pack_E6970Receipt56_chunk220, pack_E6970Receipt56_chunk221, pack_E6970Receipt56_chunk222, pack_E6970Receipt56_chunk223, pack_E6970Receipt56_chunk224, pack_E6970Receipt56_chunk225, pack_E6970Receipt56_chunk226, pack_E6970Receipt56_chunk227, pack_E6970Receipt56_chunk228, pack_E6970Receipt56_chunk229, pack_E6970Receipt56_chunk230, pack_E6970Receipt56_chunk231, pack_E6970Receipt56_chunk232, pack_E6970Receipt56_chunk233, pack_E6970Receipt56_chunk234, pack_E6970Receipt56_chunk235, pack_E6970Receipt56_chunk236, pack_E6970Receipt56_chunk237, pack_E6970Receipt56_chunk238, pack_E6970Receipt56_chunk239, pack_E6970Receipt56_chunk240, pack_E6970Receipt56_chunk241, pack_E6970Receipt56_chunk242, pack_E6970Receipt56_chunk243, pack_E6970Receipt56_chunk244, pack_E6970Receipt56_chunk245, pack_E6970Receipt56_chunk246, pack_E6970Receipt56_chunk247, pack_E6970Receipt56_chunk248, pack_E6970Receipt56_chunk249, pack_E6970Receipt56_chunk250, pack_E6970Receipt56_chunk251, pack_E6970Receipt56_chunk252]
def rows56 := rowsFrom pack_E6970Receipt56_chunks
theorem good56 : ∀ r ∈ rows56, good 56 r = true := rowsFrom_good pack_E6970Receipt56_chunks
theorem sorted56 : rows56.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt56_chunks 0 (by decide +kernel)).1
theorem mass56 (i : Fin 61) :
    bandCount 56 (i.val : ℤ) 60 16 ≤ (rows56.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt56_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 56 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt56_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total56 : (rows56.map (price 56)).sum = 384318 :=
  (total_eq pack_E6970Receipt56_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt56

section Pack_E6970Receipt57

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt57_chunk0 := witnessA6966Final 57 60 0 1110003 1110068 32 4000
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk1 := witnessA6966Final 57 60 32 1110069 1110135 32 3952
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk2 := witnessA6966Final 57 60 64 1110136 1110203 32 3824
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk3 := witnessA6966Final 57 60 96 1110204 1110273 32 3680
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk4 := witnessA6966Final 57 60 128 1110274 1110385 32 3538
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk5 := witnessA6966Final 57 60 160 1110386 1110459 32 3552
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk6 := witnessA6966Final 57 60 192 1110460 1110580 32 3338
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk7 := witnessA6966Final 57 60 224 1110581 1110707 32 3208
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk8 := witnessA6966Final 57 60 256 1110708 1110840 32 3030
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk9 := witnessA6966Final 57 60 288 1110841 1111030 27 2367
  0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk10 := witnessRule 57 59 0 1120002 1120067 32 3822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk11 := witnessRule 57 59 32 1120068 1120134 32 3710
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk12 := witnessRule 57 59 64 1120135 1120203 32 3610
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk13 := witnessRule 57 59 96 1120204 1120273 32 3428
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk14 := witnessRule 57 59 128 1120274 1120386 32 3324
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk15 := witnessRule 57 59 160 1120387 1120461 32 3286
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk16 := witnessRule 57 59 192 1120462 1120583 32 3118
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk17 := witnessRule 57 59 224 1120584 1120711 32 2952
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk18 := witnessRule 57 59 256 1120712 1120898 32 2760
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk19 := witnessRule 57 59 288 1120899 1121029 20 1606
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk20 := witnessRule 57 58 0 1130001 1130066 32 3594
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk21 := witnessRule 57 58 32 1130067 1130134 32 3508
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk22 := witnessRule 57 58 64 1130135 1130203 32 3362
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk23 := witnessRule 57 58 96 1130204 1130274 32 3186
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk24 := witnessRule 57 58 128 1130275 1130388 32 3134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk25 := witnessRule 57 58 160 1130389 1130463 32 2986
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk26 := witnessRule 57 58 192 1130464 1130586 32 2892
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk27 := witnessRule 57 58 224 1130587 1130715 32 2690
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk28 := witnessRule 57 58 256 1130716 1130904 32 2518
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk29 := witnessRule 57 58 288 1130960 1131029 13 977
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk30 := witnessRule 57 57 0 1140000 1140066 32 3420
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk31 := witnessRule 57 57 32 1140067 1140134 32 3264
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk32 := witnessRule 57 57 64 1140135 1140204 32 3136
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk33 := witnessRule 57 57 96 1140205 1140275 32 2926
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk34 := witnessRule 57 57 128 1140276 1140390 32 2940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk35 := witnessRule 57 57 160 1140391 1140466 32 2704
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk36 := witnessRule 57 57 192 1140512 1140590 32 2656
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk37 := witnessRule 57 57 224 1140591 1140771 32 2494
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk38 := witnessRule 57 57 256 1140772 1140966 32 2282
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk39 := witnessRule 57 57 288 1141024 1141028 5 349
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk40 := witnessRule 57 56 0 1150000 1150066 32 3180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk41 := witnessRule 57 56 32 1150067 1150135 32 3052
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk42 := witnessRule 57 56 64 1150136 1150205 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk43 := witnessRule 57 56 96 1150206 1150277 32 2684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk44 := witnessRule 57 56 128 1150278 1150393 32 2742
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk45 := witnessRule 57 56 160 1150394 1150515 32 2516
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk46 := witnessRule 57 56 192 1150516 1150643 32 2398
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk47 := witnessRule 57 56 224 1150644 1150777 32 2220
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk48 := witnessRule 57 56 256 1150778 1151028 29 1924
  0x1fffbfff 0xb99a (by decide +kernel)
private def pack_E6970Receipt57_chunk49 := witnessRule 57 55 0 1160000 1160067 32 2980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk50 := witnessRule 57 55 32 1160068 1160136 32 2802
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk51 := witnessRule 57 55 64 1160137 1160207 32 2634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk52 := witnessRule 57 55 96 1160208 1160321 32 2506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk53 := witnessRule 57 55 128 1160322 1160396 32 2464
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk54 := witnessRule 57 55 160 1160397 1160519 32 2317
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk55 := witnessRule 57 55 192 1160520 1160648 32 2166
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk56 := witnessRule 57 55 224 1160649 1160837 32 2064
  0x7fffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt57_chunk57 := witnessRule 57 55 256 1160838 1161027 20 1262
  0xfffbf 0xba1a (by decide +kernel)
private def pack_E6970Receipt57_chunk58 := witnessRule 57 54 0 1170000 1170067 32 2748
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk59 := witnessRule 57 54 32 1170068 1170137 32 2588
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk60 := witnessRule 57 54 64 1170138 1170208 32 2393
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk61 := witnessRule 57 54 96 1170209 1170323 32 2337
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk62 := witnessRule 57 54 128 1170324 1170399 32 2216
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk63 := witnessRule 57 54 160 1170400 1170523 32 2135
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk64 := witnessRule 57 54 192 1170524 1170704 32 2023
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk65 := witnessRule 57 54 224 1170705 1170899 32 1972
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt57_chunk66 := witnessRule 57 54 256 1170900 1171027 12 734
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk67 := witnessRule 57 53 0 1180000 1180068 32 2555
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk68 := witnessRule 57 53 32 1180069 1180138 32 2356
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk69 := witnessRule 57 53 64 1180139 1180210 32 2194
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk70 := witnessRule 57 53 96 1180211 1180326 32 2187
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk71 := witnessRule 57 53 128 1180327 1180448 32 2044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk72 := witnessRule 57 53 160 1180449 1180576 32 1989
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk73 := witnessRule 57 53 192 1180577 1180710 32 1931
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt57_chunk74 := witnessRule 57 53 224 1180711 1180964 32 1895
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt57_chunk75 := witnessRule 57 53 256 1181024 1181026 3 180
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk76 := witnessRule 57 52 0 1190000 1190068 32 2359
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk77 := witnessRule 57 52 32 1190069 1190139 32 2170
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk78 := witnessRule 57 52 64 1190140 1190211 32 2049
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk79 := witnessRule 57 52 96 1190212 1190328 32 2033
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk80 := witnessRule 57 52 128 1190329 1190451 32 1937
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk81 := witnessRule 57 52 160 1190452 1190580 32 1886
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk82 := witnessRule 57 52 192 1190581 1190769 32 1847
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt57_chunk83 := witnessRule 57 52 224 1190770 1191026 27 1552
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt57_chunk84 := witnessRule 57 51 0 1200000 1200069 32 2195
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk85 := witnessRule 57 51 32 1200070 1200140 32 2006
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk86 := witnessRule 57 51 64 1200141 1200213 32 1926
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk87 := witnessRule 57 51 96 1200256 1200331 32 1917
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk88 := witnessRule 57 51 128 1200332 1200455 32 1843
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk89 := witnessRule 57 51 160 1200456 1200585 32 1800
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt57_chunk90 := witnessRule 57 51 192 1200586 1200775 32 1774
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt57_chunk91 := witnessRule 57 51 224 1200832 1201025 18 1008
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt57_chunk92 := witnessRule 57 50 0 1210000 1210069 32 2036
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk93 := witnessRule 57 50 32 1210070 1210141 32 1893
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk94 := witnessRule 57 50 64 1210142 1210257 32 1838
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk95 := witnessRule 57 50 96 1210258 1210333 32 1805
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk96 := witnessRule 57 50 128 1210334 1210458 32 1758
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk97 := witnessRule 57 50 160 1210459 1210641 32 1727
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt57_chunk98 := witnessRule 57 50 192 1210642 1210837 32 1711
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt57_chunk99 := witnessRule 57 50 224 1210896 1211025 10 552
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk100 := witnessRule 57 49 0 1220000 1220070 32 1914
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk101 := witnessRule 57 49 32 1220071 1220142 32 1793
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk102 := witnessRule 57 49 64 1220143 1220259 32 1750
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk103 := witnessRule 57 49 96 1220260 1220336 32 1707
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk104 := witnessRule 57 49 128 1220337 1220462 32 1681
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt57_chunk105 := witnessRule 57 49 160 1220512 1220646 32 1662
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt57_chunk106 := witnessRule 57 49 192 1220647 1220962 32 1671
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt57_chunk107 := witnessRule 57 49 224 1221024 1221024 1 55
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk108 := witnessRule 57 48 0 1230000 1230070 32 1800
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk109 := witnessRule 57 48 32 1230071 1230143 32 1704
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk110 := witnessRule 57 48 64 1230144 1230261 32 1666
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk111 := witnessRule 57 48 96 1230262 1230385 32 1627
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt57_chunk112 := witnessRule 57 48 128 1230386 1230515 32 1613
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt57_chunk113 := witnessRule 57 48 160 1230516 1230705 32 1591
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt57_chunk114 := witnessRule 57 48 192 1230706 1231024 25 1276
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk115 := witnessRule 57 47 0 1240000 1240071 32 1702
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk116 := witnessRule 57 47 32 1240072 1240144 32 1612
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk117 := witnessRule 57 47 64 1240145 1240263 32 1587
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk118 := witnessRule 57 47 96 1240264 1240388 32 1558
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt57_chunk119 := witnessRule 57 47 128 1240389 1240519 32 1539
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt57_chunk120 := witnessRule 57 47 160 1240520 1240711 32 1536
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt57_chunk121 := witnessRule 57 47 192 1240768 1240961 16 803
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk122 := witnessRule 57 46 0 1250000 1250071 32 1609
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk123 := witnessRule 57 46 32 1250072 1250145 32 1527
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk124 := witnessRule 57 46 64 1250146 1250265 32 1517
  0xb6bfffff 0x5766336ee8c66e5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt57_chunk125 := witnessRule 57 46 96 1250266 1250391 32 1489
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt57_chunk126 := witnessRule 57 46 128 1250392 1250523 32 1471
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt57_chunk127 := witnessRule 57 46 160 1250576 1250773 32 1500
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt57_chunk128 := witnessRule 57 46 192 1250832 1250960 8 397
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk129 := witnessRule 57 45 0 1260000 1260072 32 1527
  0xfffffff3 0x31ccd6b8a2 (by decide +kernel)
private def pack_E6970Receipt57_chunk130 := witnessRule 57 45 32 1260073 1260146 32 1445
  0xffffdfff 0x6399a (by decide +kernel)
private def pack_E6970Receipt57_chunk131 := witnessRule 57 45 64 1260147 1260267 32 1449
  0x920edb69 0x37864368f0c66d5d990db3b319b77464370e6c662121c994dcb8b21884976342f6c66cde58cdabbb19b77563372e6c66e9c590ddb99883 (by decide +kernel)
private def pack_E6970Receipt57_chunk132 := witnessRule 57 45 96 1260268 1260394 32 1421
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt57_chunk133 := witnessRule 57 45 128 1260395 1260580 32 1418
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt57_chunk134 := witnessRule 57 45 160 1260581 1260960 32 1482
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk135 := witnessRule 57 44 0 1270000 1270072 32 1446
  0xf47fff57 0x14e6c66edc590d8c638b3d7141372e8c66e9c990ddba9a (by decide +kernel)
private def pack_E6970Receipt57_chunk136 := witnessRule 57 44 32 1270073 1270147 32 1373
  0xedb68fff 0x17c63366f4c66d5e18cdbbb319b97463374e4c86edc58cc425ba9a (by decide +kernel)
private def pack_E6970Receipt57_chunk137 := witnessRule 57 44 64 1270192 1270269 32 1381
  0x80039240 0xbd329b27a64366f2c66210de194da3c321b577633108aecca6d9d590c4233a331b773653108ee4ce6e1c598c4243c1a17b64364f6c66cde590da3cb19b5776436ceec66ddd590dc3a31988487365372e4c862125c598dd3a9883 (by decide +kernel)
private def pack_E6970Receipt57_chunk138 := witnessRule 57 44 96 1270270 1270397 32 1359
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt57_chunk139 := witnessRule 57 44 128 1270448 1270584 32 1371
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt57_chunk140 := witnessRule 57 44 160 1270640 1270897 24 1090
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk141 := witnessRule 57 43 0 1280000 1280073 32 1376
  0xa03ff551 0xeeec66e1d590dcba3198849736536314e6c27062dc98420c5b8b11c18c713108cf0c66ddd990dc3a329bb736151098e2c2a262171c54cdeb922 (by decide +kernel)
private def pack_E6970Receipt57_chunk142 := witnessRule 57 43 32 1280074 1280193 32 1311
  0x3924076d 0x21c5a0dcbb988317c64364f8c66cde990da3d319b5786436cf0c66ddd990dc3ab1988487465372e6c862125c998dd38b29884a77342fac66cded8cdabcb19b (by decide +kernel)
private def pack_E6970Receipt57_chunk143 := witnessRule 57 43 64 1280194 1280271 32 1304
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4796436af0c662115dd94db3b3218846756636ee8ca6211dcd9cdc39331884 (by decide +kernel)
private def pack_E6970Receipt57_chunk144 := witnessRule 57 43 96 1280320 1280451 32 1310
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt57_chunk145 := witnessRule 57 43 128 1280452 1280644 32 1331
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt57_chunk146 := witnessRule 57 43 160 1280645 1280896 16 715
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk147 := witnessRule 57 42 0 1290000 1290073 32 1305
  0x3b4501 0xcf0c662119dd94dbbb3218847756636310eac470625d184c428c4b9b19c18a7262310a314e2c87062dccc420bf319b37c63368f4c86d5e58cc422bc329b8776151092eac2a262165d1854ce539b0a91885a72615438316e4c2b2dc554d8c638a89c (by decide +kernel)
private def pack_E6970Receipt57_chunk148 := witnessRule 57 42 32 1290074 1290194 32 1249
  0x1e000392 0xee4d06211dc5a8dc3c988317c65364f8c86cded8cc421bd329b47a6436af2c662115e194db3bb218846766636eeaca6211dd19cdc39b3188487268372e2ce62125e4d0beb21b27d63366f6c86d1ed8cdabcb21b (by decide +kernel)
private def pack_E6970Receipt57_chunk149 := witnessRule 57 42 64 1290195 1290321 32 1245
  0x3e003c00 0x8e2da6d5f0c418bd339b2796631084f0d06cddd9cc421bb349b4756831088e8d46d5cda4c422b9359b6716a3108cf8685ed98d93db29b37a6431086f2cc6d1e194c4223bb39b576663108aead06d9d19cc42339b49b (by decide +kernel)
private def pack_E6970Receipt57_chunk150 := witnessRule 57 42 96 1290322 1290454 32 1249
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt57_chunk151 := witnessRule 57 42 128 1290455 1290706 32 1309
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk152 := witnessRule 57 42 160 1290707 1290896 9 398
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk153 := witnessRule 57 41 0 1300000 1300074 32 1238
  0x1c1000 0x4796636af0ca62115dd9cd8c33bb19c1877662310a30eeac870621d18cc428c439b29c1897264310a312e2cc70629d4c420bf321b27d6331084f8ca6cded90c421bd331b6796151310acf0c2a671ddd8548c42bbb30aa1c8756153310b0e8c2aa70625d18544e8c539b0a88518a7261523a316e2c2a2621862dc54ce0c63923 (by decide +kernel)
private def pack_E6970Receipt57_chunk154 := witnessRule 57 41 32 1300075 1300196 32 1190
  0x78001e0 0x574693108ae6d66d9c9a8c42338b61b77b31062f8cc6c9f194d9bdb2188437a66368f2ca62111e19cdabbb318845766836ceace62119d1a4dbb9b418847726a370e2d262121ecd0beb29b27d64366f8c66210ded94da3d321884 (by decide +kernel)
private def pack_E6970Receipt57_chunk155 := witnessRule 57 41 64 1300197 1300324 32 1186
  0x7e00f80 0x13a3618842736e366e4da6210dc5bcda3f18831786a364eed262109d9acd9bab518843746c368e6d662111c9b4dab8b6188457e342f6ce6c9e998c4213cb41b3786731086eed26d1d9a0c4223ab51b (by decide +kernel)
private def pack_E6970Receipt57_chunk156 := witnessRule 57 41 96 1300325 1300458 32 1200
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt57_chunk157 := witnessRule 57 41 128 1300512 1300832 32 1300
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk158 := witnessRule 57 41 160 1300833 1300833 1 44
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk159 := witnessRule 57 40 0 1310000 1310074 32 1172
  0x180000 0xde5a0d8c23cb21c1857863310a30aeeca70619d990c428c33ab31c1877465310a30ee6ce70621c998c428c438b41c189773109ec8620f998d0beb2988417c67366f8c2a6711ed8548c42a3d30aa1c5796153310aaf0c2aa719dd8550c42b3b30ab1c1877661523a310eac2a26218621d1854ce8c4b9b0a918861897261543a314e2c2a66218629c554e1c5389b (by decide +kernel)
private def pack_E6970Receipt57_chunk160 := witnessRule 57 40 32 1310075 1310197 32 1131
  0x3e000e0 0x3756c368e8d662111cdb4dab93618845716e36cfa620c5f19cd93db3188427a68366f2ce6210de1a4da3bb418844766a36aead262115d1acdb39b518846726c36ee2d66211df4d0bf32188417d66364f8ca62109ed9cd9bd331884 (by decide +kernel)
private def pack_E6970Receipt57_chunk161 := witnessRule 57 40 64 1310198 1310326 32 1129
  0xe1fe03f0 0x2e6c801b2726f31084e2c881b37400c418bb369b2756c31084e8dc6cdcdb4c421b9379b4716e31088e801a1796a364f0d262109ddacd9bb351884 (by decide +kernel)
private def pack_E6970Receipt57_chunk162 := witnessRule 57 40 96 1310327 1310515 32 1168
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt57_chunk163 := witnessRule 57 40 128 1310516 1310832 26 1036
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk164 := witnessRule 57 39 0 1320000 1320075 32 1106
  0xc0000 0x609ed94e0c1bd321885183796638308f0ca6214611dd9ce0c2bb33188518575683830ce8ce6214619cda4e0c3b9341885187716a38310f2621398554d8bf30aa1c27d6153310a4f8c2aa70ded8550c429bd30ab1c4796155310a8f0c2ae70615e1854ce8c33bb0a918861867661543a30eeac2a6621861dd18554e8c439b0aa18861887261563a710e4c470e25c584c429c4b99b (by decide +kernel)
private def pack_E6970Receipt57_chunk165 := witnessRule 57 39 32 1320076 1320199 32 1074
  0xfc0072 0x1776d364ecd862109d5b8d9ba3698843736f368e4dc62111c590036afe620c5e9a8d93cb498842786b366eed46210dd9b0da3ab598844746d36ae6d862115c9b8db38b6988467f35ccc620f5a0d0bdb49b (by decide +kernel)
private def pack_E6970Receipt57_chunk166 := witnessRule 57 39 64 1320200 1320329 32 1079
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt57_chunk167 := witnessRule 57 39 96 1320330 1320519 32 1144
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk168 := witnessRule 57 39 128 1320576 1320832 19 745
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk169 := witnessRule 57 38 0 1330000 1330075 32 1042
  0xc0000 0x605ed9ce0c13d331885182796838306f0ce621460ddda4e0c23b341885184756a3830ae8d26214615cdace0c339351885186716c3830ef66213d8550c42730ab1b17d6155310a2f8c2ae709ed8558c4293d30ac1c1837a61543a308f2c2a66218611e18554e8c2bbb0aa18861857661563a30ceac2aa6218619d1855ce9c33a319c3877362310a70ee4c870e21c58cc429c43a9b (by decide +kernel)
private def pack_E6970Receipt57_chunk170 := witnessRule 57 38 32 1330076 1330200 32 1016
  0xe07f803b 0x5d5900364e8de62109cd910366e4c8018843716480da3a20620c5e1b4d93bb618842766e366eada6210dd1bcda39b718844726400dab8b7988457440d6b0ab9b (by decide +kernel)
private def pack_E6970Receipt57_chunk171 := witnessRule 57 38 64 1330201 1330331 32 1039
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt57_chunk172 := witnessRule 57 38 96 1330384 1330579 32 1125
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk173 := witnessRule 57 38 128 1330580 1330769 12 461
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk174 := witnessRule 57 37 0 1340000 1340076 32 977
  0xe0060000 0x302f2d470609e1a4c428c13bb59c183766a310a306ead870611d1acc428c239b69c185726c310a30ae2dc70619f4c427312a9bd615731098c2b26c605f18554e8c13db0aa18861827a61563a306f2c2aa621860de1855ce8c23bb0ab18861847661583a708ecc870e15d58cc429c2ba329c3867364310a70ce4cc70e1dc594c429c3bb9b (by decide +kernel)
private def pack_E6970Receipt57_chunk175 := witnessRule 57 37 32 1340077 1340202 32 967
  0xfe1ff01f 0x2e6c981b2726480c42138b2806cdd3031062ecc801b2756f31084e8c881b3736400c421b932406d1c591031088e981a (by decide +kernel)
private def pack_E6970Receipt57_chunk176 := witnessRule 57 37 64 1340203 1340386 32 1009
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt57_chunk177 := witnessRule 57 37 96 1340387 1340642 32 1109
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk178 := witnessRule 57 37 128 1340643 1340768 5 190
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk179 := witnessRule 57 36 0 1350000 1350076 32 917
  0xf8060400 0x605ddb4e0c13b361885182756e38306e8da621460dcdbce0c239371885184716400e0c2bf9884e62543209ac4ac62106358554c428c630ab9c1817b6156310c302f4c2b074609e18564e9c13c329c3837764310a706eccc70e11d594c429c23a339c3857366310a70ae4d070e19c59cc429c33c9b (by decide +kernel)
private def pack_E6970Receipt57_chunk180 := witnessRule 57 36 32 1350077 1350203 32 922
  0xffdffe0f 0x5c5960362e8c981b2736480c4213932806cdc593031086ea81a (by decide +kernel)
private def pack_E6970Receipt57_chunk181 := witnessRule 57 36 64 1350204 1350389 32 981
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk182 := witnessRule 57 36 96 1350390 1350768 31 1061
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk183 := witnessRule 57 35 0 1360000 1360077 32 861
  0xff035600 0x181756400e0c13a379885182736440e0c1b93200621460dc592038308e881884d62553308318c2ac64146298568e1c0bc339c3827766310a704ecd070e0dd59cc429c1ba349c3847368310a708e4d470e15c5a4c429c2bd9b (by decide +kernel)
private def pack_E6970Receipt57_chunk184 := witnessRule 57 35 32 1360078 1360205 32 883
  0xffffffc7 0xb932c06c9c595031084eb81a (by decide +kernel)
private def pack_E6970Receipt57_chunk185 := witnessRule 57 35 64 1360256 1360392 32 957
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk186 := witnessRule 57 35 96 1360448 1360705 24 801
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk187 := witnessRule 57 34 0 1370000 1370077 32 812
  0xffc3ff80 0x302e6c981c182726480c428c138b2807060dd303108702ecd470e09d5a4c429c13a359c383736a310a706e4d870e11c5acc429c23e9b (by decide +kernel)
private def pack_E6970Receipt57_chunk188 := witnessRule 57 34 32 1370078 1370257 32 849
  0xfffffffb 0x2ec81a (by decide +kernel)
private def pack_E6970Receipt57_chunk189 := witnessRule 57 34 64 1370258 1370450 32 933
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk190 := witnessRule 57 34 96 1370451 1370704 18 585
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk191 := witnessRule 57 33 0 1380000 1380078 32 767
  0xfffbffe0 0x181716580e1c0ba369c382736c310a704e4dc70e0dc5b4c429c1bf9b (by decide +kernel)
private def pack_E6970Receipt57_chunk192 := witnessRule 57 33 32 1380079 1380259 32 820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk193 := witnessRule 57 33 64 1380260 1380454 32 911
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk194 := witnessRule 57 33 96 1380512 1380704 12 383
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk195 := witnessRule 57 32 0 1390000 1390078 32 726
  0xfffffff8 0x702e4c801c382716f310a704e881b (by decide +kernel)
private def pack_E6970Receipt57_chunk196 := witnessRule 57 32 32 1390128 1390261 32 792
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk197 := witnessRule 57 32 64 1390262 1390515 32 891
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk198 := witnessRule 57 32 96 1390516 1390641 6 187
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk199 := witnessRule 57 31 0 1400000 1400128 32 691
  0xfffffffe 0x702e981b (by decide +kernel)
private def pack_E6970Receipt57_chunk200 := witnessRule 57 31 32 1400129 1400263 32 764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk201 := witnessRule 57 31 64 1400264 1400640 32 878
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk202 := witnessRule 57 30 0 1410000 1410129 32 658
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk203 := witnessRule 57 30 32 1410130 1410265 32 735
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk204 := witnessRule 57 30 64 1410320 1410640 27 717
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk205 := witnessRule 57 29 0 1420000 1420130 32 628
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk206 := witnessRule 57 29 32 1420131 1420322 32 710
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk207 := witnessRule 57 29 64 1420323 1420577 21 537
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk208 := witnessRule 57 28 0 1430000 1430131 32 597
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk209 := witnessRule 57 28 32 1430132 1430324 32 683
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk210 := witnessRule 57 28 64 1430325 1430576 16 395
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk211 := witnessRule 57 27 0 1440000 1440132 32 567
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk212 := witnessRule 57 27 32 1440133 1440384 32 659
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk213 := witnessRule 57 27 64 1440385 1440576 11 264
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk214 := witnessRule 57 26 0 1450000 1450133 32 536
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk215 := witnessRule 57 26 32 1450134 1450387 32 635
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk216 := witnessRule 57 26 64 1450388 1450513 6 139
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk217 := witnessRule 57 25 0 1460000 1460134 32 506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk218 := witnessRule 57 25 32 1460135 1460450 32 616
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk219 := witnessRule 57 25 64 1460512 1460512 1 23
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk220 := witnessRule 57 24 0 1470000 1470135 32 475
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk221 := witnessRule 57 24 32 1470136 1470512 29 533
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk222 := witnessRule 57 23 0 1480000 1480136 32 445
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk223 := witnessRule 57 23 32 1480192 1480449 24 417
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk224 := witnessRule 57 22 0 1490000 1490192 32 415
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk225 := witnessRule 57 22 32 1490193 1490448 20 327
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk226 := witnessRule 57 21 0 1500000 1500194 32 387
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk227 := witnessRule 57 21 32 1500195 1500448 16 247
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk228 := witnessRule 57 20 0 1510000 1510195 32 357
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk229 := witnessRule 57 20 32 1510196 1510385 12 173
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk230 := witnessRule 57 19 0 1520000 1520197 32 329
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk231 := witnessRule 57 19 32 1520256 1520384 8 109
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk232 := witnessRule 57 18 0 1530000 1530257 32 301
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk233 := witnessRule 57 18 32 1530258 1530384 5 64
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk234 := witnessRule 57 17 0 1540000 1540320 32 276
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk235 := witnessRule 57 17 32 1540321 1540321 1 12
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk236 := witnessRule 57 16 0 1550000 1550320 30 228
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk237 := witnessRule 57 15 0 1560000 1560320 27 177
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk238 := witnessRule 57 14 0 1570000 1570257 24 129
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk239 := witnessRule 57 13 0 1580000 1580256 21 90
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk240 := witnessRule 57 12 0 1590000 1590256 19 61
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk241 := witnessRule 57 11 0 1600000 1600193 16 33
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk242 := witnessRule 57 10 0 1610000 1610192 14 13
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk243 := witnessRule 57 9 0 1620000 1620192 12 4
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk244 := witnessRule 57 8 0 1630000 1630129 10 0
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk245 := witnessRule 57 7 0 1640000 1640128 8 0
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk246 := witnessRule 57 6 0 1650000 1650128 7 0
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk247 := witnessRule 57 5 0 1660000 1660065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk248 := witnessRule 57 4 0 1670000 1670064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk249 := witnessRule 57 3 0 1680000 1680064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk250 := witnessRule 57 2 0 1690000 1690001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk251 := witnessRule 57 1 0 1700000 1700000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt57_chunk252 := witnessRule 57 0 0 1710000 1710000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt57_chunks : List (Chunk 57) := [pack_E6970Receipt57_chunk0, pack_E6970Receipt57_chunk1, pack_E6970Receipt57_chunk2, pack_E6970Receipt57_chunk3, pack_E6970Receipt57_chunk4, pack_E6970Receipt57_chunk5, pack_E6970Receipt57_chunk6, pack_E6970Receipt57_chunk7, pack_E6970Receipt57_chunk8, pack_E6970Receipt57_chunk9, pack_E6970Receipt57_chunk10, pack_E6970Receipt57_chunk11, pack_E6970Receipt57_chunk12, pack_E6970Receipt57_chunk13, pack_E6970Receipt57_chunk14, pack_E6970Receipt57_chunk15, pack_E6970Receipt57_chunk16, pack_E6970Receipt57_chunk17, pack_E6970Receipt57_chunk18, pack_E6970Receipt57_chunk19, pack_E6970Receipt57_chunk20, pack_E6970Receipt57_chunk21, pack_E6970Receipt57_chunk22, pack_E6970Receipt57_chunk23, pack_E6970Receipt57_chunk24, pack_E6970Receipt57_chunk25, pack_E6970Receipt57_chunk26, pack_E6970Receipt57_chunk27, pack_E6970Receipt57_chunk28, pack_E6970Receipt57_chunk29, pack_E6970Receipt57_chunk30, pack_E6970Receipt57_chunk31, pack_E6970Receipt57_chunk32, pack_E6970Receipt57_chunk33, pack_E6970Receipt57_chunk34, pack_E6970Receipt57_chunk35, pack_E6970Receipt57_chunk36, pack_E6970Receipt57_chunk37, pack_E6970Receipt57_chunk38, pack_E6970Receipt57_chunk39, pack_E6970Receipt57_chunk40, pack_E6970Receipt57_chunk41, pack_E6970Receipt57_chunk42, pack_E6970Receipt57_chunk43, pack_E6970Receipt57_chunk44, pack_E6970Receipt57_chunk45, pack_E6970Receipt57_chunk46, pack_E6970Receipt57_chunk47, pack_E6970Receipt57_chunk48, pack_E6970Receipt57_chunk49, pack_E6970Receipt57_chunk50, pack_E6970Receipt57_chunk51, pack_E6970Receipt57_chunk52, pack_E6970Receipt57_chunk53, pack_E6970Receipt57_chunk54, pack_E6970Receipt57_chunk55, pack_E6970Receipt57_chunk56, pack_E6970Receipt57_chunk57, pack_E6970Receipt57_chunk58, pack_E6970Receipt57_chunk59, pack_E6970Receipt57_chunk60, pack_E6970Receipt57_chunk61, pack_E6970Receipt57_chunk62, pack_E6970Receipt57_chunk63, pack_E6970Receipt57_chunk64, pack_E6970Receipt57_chunk65, pack_E6970Receipt57_chunk66, pack_E6970Receipt57_chunk67, pack_E6970Receipt57_chunk68, pack_E6970Receipt57_chunk69, pack_E6970Receipt57_chunk70, pack_E6970Receipt57_chunk71, pack_E6970Receipt57_chunk72, pack_E6970Receipt57_chunk73, pack_E6970Receipt57_chunk74, pack_E6970Receipt57_chunk75, pack_E6970Receipt57_chunk76, pack_E6970Receipt57_chunk77, pack_E6970Receipt57_chunk78, pack_E6970Receipt57_chunk79, pack_E6970Receipt57_chunk80, pack_E6970Receipt57_chunk81, pack_E6970Receipt57_chunk82, pack_E6970Receipt57_chunk83, pack_E6970Receipt57_chunk84, pack_E6970Receipt57_chunk85, pack_E6970Receipt57_chunk86, pack_E6970Receipt57_chunk87, pack_E6970Receipt57_chunk88, pack_E6970Receipt57_chunk89, pack_E6970Receipt57_chunk90, pack_E6970Receipt57_chunk91, pack_E6970Receipt57_chunk92, pack_E6970Receipt57_chunk93, pack_E6970Receipt57_chunk94, pack_E6970Receipt57_chunk95, pack_E6970Receipt57_chunk96, pack_E6970Receipt57_chunk97, pack_E6970Receipt57_chunk98, pack_E6970Receipt57_chunk99, pack_E6970Receipt57_chunk100, pack_E6970Receipt57_chunk101, pack_E6970Receipt57_chunk102, pack_E6970Receipt57_chunk103, pack_E6970Receipt57_chunk104, pack_E6970Receipt57_chunk105, pack_E6970Receipt57_chunk106, pack_E6970Receipt57_chunk107, pack_E6970Receipt57_chunk108, pack_E6970Receipt57_chunk109, pack_E6970Receipt57_chunk110, pack_E6970Receipt57_chunk111, pack_E6970Receipt57_chunk112, pack_E6970Receipt57_chunk113, pack_E6970Receipt57_chunk114, pack_E6970Receipt57_chunk115, pack_E6970Receipt57_chunk116, pack_E6970Receipt57_chunk117, pack_E6970Receipt57_chunk118, pack_E6970Receipt57_chunk119, pack_E6970Receipt57_chunk120, pack_E6970Receipt57_chunk121, pack_E6970Receipt57_chunk122, pack_E6970Receipt57_chunk123, pack_E6970Receipt57_chunk124, pack_E6970Receipt57_chunk125, pack_E6970Receipt57_chunk126, pack_E6970Receipt57_chunk127, pack_E6970Receipt57_chunk128, pack_E6970Receipt57_chunk129, pack_E6970Receipt57_chunk130, pack_E6970Receipt57_chunk131, pack_E6970Receipt57_chunk132, pack_E6970Receipt57_chunk133, pack_E6970Receipt57_chunk134, pack_E6970Receipt57_chunk135, pack_E6970Receipt57_chunk136, pack_E6970Receipt57_chunk137, pack_E6970Receipt57_chunk138, pack_E6970Receipt57_chunk139, pack_E6970Receipt57_chunk140, pack_E6970Receipt57_chunk141, pack_E6970Receipt57_chunk142, pack_E6970Receipt57_chunk143, pack_E6970Receipt57_chunk144, pack_E6970Receipt57_chunk145, pack_E6970Receipt57_chunk146, pack_E6970Receipt57_chunk147, pack_E6970Receipt57_chunk148, pack_E6970Receipt57_chunk149, pack_E6970Receipt57_chunk150, pack_E6970Receipt57_chunk151, pack_E6970Receipt57_chunk152, pack_E6970Receipt57_chunk153, pack_E6970Receipt57_chunk154, pack_E6970Receipt57_chunk155, pack_E6970Receipt57_chunk156, pack_E6970Receipt57_chunk157, pack_E6970Receipt57_chunk158, pack_E6970Receipt57_chunk159, pack_E6970Receipt57_chunk160, pack_E6970Receipt57_chunk161, pack_E6970Receipt57_chunk162, pack_E6970Receipt57_chunk163, pack_E6970Receipt57_chunk164, pack_E6970Receipt57_chunk165, pack_E6970Receipt57_chunk166, pack_E6970Receipt57_chunk167, pack_E6970Receipt57_chunk168, pack_E6970Receipt57_chunk169, pack_E6970Receipt57_chunk170, pack_E6970Receipt57_chunk171, pack_E6970Receipt57_chunk172, pack_E6970Receipt57_chunk173, pack_E6970Receipt57_chunk174, pack_E6970Receipt57_chunk175, pack_E6970Receipt57_chunk176, pack_E6970Receipt57_chunk177, pack_E6970Receipt57_chunk178, pack_E6970Receipt57_chunk179, pack_E6970Receipt57_chunk180, pack_E6970Receipt57_chunk181, pack_E6970Receipt57_chunk182, pack_E6970Receipt57_chunk183, pack_E6970Receipt57_chunk184, pack_E6970Receipt57_chunk185, pack_E6970Receipt57_chunk186, pack_E6970Receipt57_chunk187, pack_E6970Receipt57_chunk188, pack_E6970Receipt57_chunk189, pack_E6970Receipt57_chunk190, pack_E6970Receipt57_chunk191, pack_E6970Receipt57_chunk192, pack_E6970Receipt57_chunk193, pack_E6970Receipt57_chunk194, pack_E6970Receipt57_chunk195, pack_E6970Receipt57_chunk196, pack_E6970Receipt57_chunk197, pack_E6970Receipt57_chunk198, pack_E6970Receipt57_chunk199, pack_E6970Receipt57_chunk200, pack_E6970Receipt57_chunk201, pack_E6970Receipt57_chunk202, pack_E6970Receipt57_chunk203, pack_E6970Receipt57_chunk204, pack_E6970Receipt57_chunk205, pack_E6970Receipt57_chunk206, pack_E6970Receipt57_chunk207, pack_E6970Receipt57_chunk208, pack_E6970Receipt57_chunk209, pack_E6970Receipt57_chunk210, pack_E6970Receipt57_chunk211, pack_E6970Receipt57_chunk212, pack_E6970Receipt57_chunk213, pack_E6970Receipt57_chunk214, pack_E6970Receipt57_chunk215, pack_E6970Receipt57_chunk216, pack_E6970Receipt57_chunk217, pack_E6970Receipt57_chunk218, pack_E6970Receipt57_chunk219, pack_E6970Receipt57_chunk220, pack_E6970Receipt57_chunk221, pack_E6970Receipt57_chunk222, pack_E6970Receipt57_chunk223, pack_E6970Receipt57_chunk224, pack_E6970Receipt57_chunk225, pack_E6970Receipt57_chunk226, pack_E6970Receipt57_chunk227, pack_E6970Receipt57_chunk228, pack_E6970Receipt57_chunk229, pack_E6970Receipt57_chunk230, pack_E6970Receipt57_chunk231, pack_E6970Receipt57_chunk232, pack_E6970Receipt57_chunk233, pack_E6970Receipt57_chunk234, pack_E6970Receipt57_chunk235, pack_E6970Receipt57_chunk236, pack_E6970Receipt57_chunk237, pack_E6970Receipt57_chunk238, pack_E6970Receipt57_chunk239, pack_E6970Receipt57_chunk240, pack_E6970Receipt57_chunk241, pack_E6970Receipt57_chunk242, pack_E6970Receipt57_chunk243, pack_E6970Receipt57_chunk244, pack_E6970Receipt57_chunk245, pack_E6970Receipt57_chunk246, pack_E6970Receipt57_chunk247, pack_E6970Receipt57_chunk248, pack_E6970Receipt57_chunk249, pack_E6970Receipt57_chunk250, pack_E6970Receipt57_chunk251, pack_E6970Receipt57_chunk252]
def rows57 := rowsFrom pack_E6970Receipt57_chunks
theorem good57 : ∀ r ∈ rows57, good 57 r = true := rowsFrom_good pack_E6970Receipt57_chunks
theorem sorted57 : rows57.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt57_chunks 0 (by decide +kernel)).1
theorem mass57 (i : Fin 61) :
    bandCount 57 (i.val : ℤ) 60 16 ≤ (rows57.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt57_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 57 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt57_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total57 : (rows57.map (price 57)).sum = 379690 :=
  (total_eq pack_E6970Receipt57_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt57

section Pack_E6970Receipt58

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt58_chunk0 := witnessA6966Final 58 60 0 1140002 1140066 32 4014
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk1 := witnessA6966Final 58 60 32 1140067 1140133 32 3972
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk2 := witnessA6966Final 58 60 64 1140134 1140201 32 3848
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk3 := witnessA6966Final 58 60 96 1140202 1140271 32 3712
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk4 := witnessA6966Final 58 60 128 1140272 1140342 32 3490
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk5 := witnessA6966Final 58 60 160 1140384 1140457 32 3600
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk6 := witnessA6966Final 58 60 192 1140458 1140578 32 3326
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk7 := witnessA6966Final 58 60 224 1140579 1140705 32 3220
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk8 := witnessA6966Final 58 60 256 1140706 1140838 32 3066
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk9 := witnessA6966Final 58 60 288 1140839 1141030 29 2543
  0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk10 := witnessRule 58 59 0 1150001 1150066 32 3824
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk11 := witnessRule 58 59 32 1150067 1150133 32 3720
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk12 := witnessRule 58 59 64 1150134 1150202 32 3624
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk13 := witnessRule 58 59 96 1150203 1150272 32 3444
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk14 := witnessRule 58 59 128 1150273 1150385 32 3302
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk15 := witnessRule 58 59 160 1150386 1150460 32 3312
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk16 := witnessRule 58 59 192 1150461 1150582 32 3114
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk17 := witnessRule 58 59 224 1150583 1150710 32 2960
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk18 := witnessRule 58 59 256 1150711 1150897 32 2762
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk19 := witnessRule 58 59 288 1150898 1151029 21 1693
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk20 := witnessRule 58 58 0 1160000 1160065 32 3596
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk21 := witnessRule 58 58 32 1160066 1160133 32 3520
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk22 := witnessRule 58 58 64 1160134 1160202 32 3376
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk23 := witnessRule 58 58 96 1160203 1160273 32 3204
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk24 := witnessRule 58 58 128 1160274 1160387 32 3114
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk25 := witnessRule 58 58 160 1160388 1160462 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk26 := witnessRule 58 58 192 1160463 1160585 32 2890
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk27 := witnessRule 58 58 224 1160586 1160714 32 2698
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk28 := witnessRule 58 58 256 1160715 1160903 32 2522
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk29 := witnessRule 58 58 288 1160904 1161029 14 1048
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk30 := witnessRule 58 57 0 1170000 1170066 32 3396
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk31 := witnessRule 58 57 32 1170067 1170134 32 3264
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk32 := witnessRule 58 57 64 1170135 1170204 32 3136
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk33 := witnessRule 58 57 96 1170205 1170275 32 2926
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk34 := witnessRule 58 57 128 1170276 1170390 32 2940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk35 := witnessRule 58 57 160 1170391 1170466 32 2704
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk36 := witnessRule 58 57 192 1170512 1170590 32 2656
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk37 := witnessRule 58 57 224 1170591 1170771 32 2494
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk38 := witnessRule 58 57 256 1170772 1170966 32 2282
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk39 := witnessRule 58 57 288 1171024 1171028 5 349
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk40 := witnessRule 58 56 0 1180000 1180066 32 3156
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk41 := witnessRule 58 56 32 1180067 1180135 32 3052
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk42 := witnessRule 58 56 64 1180136 1180205 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk43 := witnessRule 58 56 96 1180206 1180277 32 2684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk44 := witnessRule 58 56 128 1180278 1180393 32 2742
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk45 := witnessRule 58 56 160 1180394 1180515 32 2516
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk46 := witnessRule 58 56 192 1180516 1180643 32 2398
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk47 := witnessRule 58 56 224 1180644 1180777 32 2220
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk48 := witnessRule 58 56 256 1180778 1181028 29 1919
  0x1fffbfff 0xb99a (by decide +kernel)
private def pack_E6970Receipt58_chunk49 := witnessRule 58 55 0 1190000 1190067 32 2956
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk50 := witnessRule 58 55 32 1190068 1190136 32 2802
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk51 := witnessRule 58 55 64 1190137 1190207 32 2634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk52 := witnessRule 58 55 96 1190208 1190321 32 2506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk53 := witnessRule 58 55 128 1190322 1190396 32 2464
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk54 := witnessRule 58 55 160 1190397 1190519 32 2316
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk55 := witnessRule 58 55 192 1190520 1190648 32 2159
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk56 := witnessRule 58 55 224 1190649 1190837 32 2042
  0x7fffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt58_chunk57 := witnessRule 58 55 256 1190838 1191027 20 1243
  0xfffbf 0xba1a (by decide +kernel)
private def pack_E6970Receipt58_chunk58 := witnessRule 58 54 0 1200000 1200067 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk59 := witnessRule 58 54 32 1200068 1200137 32 2588
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk60 := witnessRule 58 54 64 1200138 1200208 32 2392
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk61 := witnessRule 58 54 96 1200209 1200323 32 2331
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk62 := witnessRule 58 54 128 1200324 1200399 32 2207
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk63 := witnessRule 58 54 160 1200400 1200523 32 2118
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk64 := witnessRule 58 54 192 1200524 1200704 32 1998
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk65 := witnessRule 58 54 224 1200705 1200899 32 1940
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt58_chunk66 := witnessRule 58 54 256 1200900 1201027 12 722
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk67 := witnessRule 58 53 0 1210000 1210068 32 2526
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk68 := witnessRule 58 53 32 1210069 1210138 32 2349
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk69 := witnessRule 58 53 64 1210139 1210210 32 2180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk70 := witnessRule 58 53 96 1210211 1210326 32 2172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk71 := witnessRule 58 53 128 1210327 1210448 32 2020
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk72 := witnessRule 58 53 160 1210449 1210576 32 1962
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk73 := witnessRule 58 53 192 1210577 1210710 32 1899
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt58_chunk74 := witnessRule 58 53 224 1210711 1210964 32 1863
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt58_chunk75 := witnessRule 58 53 256 1211024 1211026 3 177
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk76 := witnessRule 58 52 0 1220000 1220068 32 2322
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk77 := witnessRule 58 52 32 1220069 1220139 32 2155
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk78 := witnessRule 58 52 64 1220140 1220211 32 2025
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk79 := witnessRule 58 52 96 1220212 1220328 32 2011
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk80 := witnessRule 58 52 128 1220329 1220451 32 1907
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk81 := witnessRule 58 52 160 1220452 1220580 32 1854
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk82 := witnessRule 58 52 192 1220581 1220769 32 1815
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt58_chunk83 := witnessRule 58 52 224 1220770 1221026 27 1525
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt58_chunk84 := witnessRule 58 51 0 1230000 1230069 32 2155
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk85 := witnessRule 58 51 32 1230070 1230140 32 1982
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk86 := witnessRule 58 51 64 1230141 1230213 32 1898
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk87 := witnessRule 58 51 96 1230256 1230331 32 1887
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk88 := witnessRule 58 51 128 1230332 1230455 32 1811
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk89 := witnessRule 58 51 160 1230456 1230585 32 1768
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt58_chunk90 := witnessRule 58 51 192 1230586 1230775 32 1742
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt58_chunk91 := witnessRule 58 51 224 1230832 1231025 18 990
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt58_chunk92 := witnessRule 58 50 0 1240000 1240069 32 1990
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk93 := witnessRule 58 50 32 1240070 1240141 32 1863
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk94 := witnessRule 58 50 64 1240142 1240257 32 1806
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk95 := witnessRule 58 50 96 1240258 1240333 32 1773
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk96 := witnessRule 58 50 128 1240334 1240458 32 1726
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk97 := witnessRule 58 50 160 1240459 1240641 32 1695
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt58_chunk98 := witnessRule 58 50 192 1240642 1240837 32 1679
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt58_chunk99 := witnessRule 58 50 224 1240896 1241025 10 542
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk100 := witnessRule 58 49 0 1250000 1250070 32 1862
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk101 := witnessRule 58 49 32 1250071 1250142 32 1761
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk102 := witnessRule 58 49 64 1250143 1250259 32 1718
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk103 := witnessRule 58 49 96 1250260 1250336 32 1675
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk104 := witnessRule 58 49 128 1250337 1250462 32 1649
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt58_chunk105 := witnessRule 58 49 160 1250512 1250646 32 1630
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt58_chunk106 := witnessRule 58 49 192 1250647 1250962 32 1639
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt58_chunk107 := witnessRule 58 49 224 1251024 1251024 1 54
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk108 := witnessRule 58 48 0 1260000 1260070 32 1752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk109 := witnessRule 58 48 32 1260071 1260143 32 1672
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk110 := witnessRule 58 48 64 1260144 1260261 32 1634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk111 := witnessRule 58 48 96 1260262 1260385 32 1595
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt58_chunk112 := witnessRule 58 48 128 1260386 1260515 32 1581
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt58_chunk113 := witnessRule 58 48 160 1260516 1260705 32 1559
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt58_chunk114 := witnessRule 58 48 192 1260706 1261024 25 1251
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk115 := witnessRule 58 47 0 1270000 1270071 32 1656
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk116 := witnessRule 58 47 32 1270072 1270144 32 1580
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk117 := witnessRule 58 47 64 1270145 1270263 32 1555
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk118 := witnessRule 58 47 96 1270264 1270388 32 1526
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt58_chunk119 := witnessRule 58 47 128 1270389 1270519 32 1507
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt58_chunk120 := witnessRule 58 47 160 1270520 1270711 32 1504
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt58_chunk121 := witnessRule 58 47 192 1270768 1270961 16 787
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk122 := witnessRule 58 46 0 1280000 1280071 32 1565
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk123 := witnessRule 58 46 32 1280072 1280145 32 1495
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk124 := witnessRule 58 46 64 1280146 1280265 32 1485
  0xb6bfffff 0x5766336ee8c66e5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt58_chunk125 := witnessRule 58 46 96 1280266 1280391 32 1457
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt58_chunk126 := witnessRule 58 46 128 1280392 1280523 32 1439
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt58_chunk127 := witnessRule 58 46 160 1280576 1280773 32 1468
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt58_chunk128 := witnessRule 58 46 192 1280832 1280960 8 389
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk129 := witnessRule 58 45 0 1290000 1290072 32 1483
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk130 := witnessRule 58 45 32 1290073 1290146 32 1413
  0xffffdfff 0x6399a (by decide +kernel)
private def pack_E6970Receipt58_chunk131 := witnessRule 58 45 64 1290147 1290267 32 1417
  0x920edb69 0x37864368f0c66d5d990db3b319b77464370e6c662121c994dcb8b21884976342f6c66cde58cdabbb19b77563372e6c66e9c590ddb99883 (by decide +kernel)
private def pack_E6970Receipt58_chunk132 := witnessRule 58 45 96 1290268 1290394 32 1389
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt58_chunk133 := witnessRule 58 45 128 1290395 1290580 32 1386
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt58_chunk134 := witnessRule 58 45 160 1290581 1290960 32 1450
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk135 := witnessRule 58 44 0 1300000 1300072 32 1403
  0xfeffffeb 0x18e2c66edc98cde3a1a (by decide +kernel)
private def pack_E6970Receipt58_chunk136 := witnessRule 58 44 32 1300073 1300147 32 1341
  0xedb68fff 0x17c63366f4c66d5e18cdbbb319b97463374e4c86edc58cc425ba9a (by decide +kernel)
private def pack_E6970Receipt58_chunk137 := witnessRule 58 44 64 1300192 1300269 32 1349
  0x80039240 0xbd329b27a64366f2c66210de194da3c321b577633108aecca6d9d590c4233a331b773653108ee4ce6e1c598c4243c1a17b64364f6c66cde590da3cb19b5776436ceec66ddd590dc3a31988487365372e4c862125c598dd3a9883 (by decide +kernel)
private def pack_E6970Receipt58_chunk138 := witnessRule 58 44 96 1300270 1300397 32 1327
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt58_chunk139 := witnessRule 58 44 128 1300448 1300584 32 1339
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt58_chunk140 := witnessRule 58 44 160 1300640 1300897 24 1066
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk141 := witnessRule 58 43 0 1310000 1310073 32 1334
  0xb43ffeaa 0xeeec66e5d58cdd39b21bb726331096e2ca6f1d0c41c3b319b97464374e4ca6f5c58544273892 (by decide +kernel)
private def pack_E6970Receipt58_chunk142 := witnessRule 58 43 32 1310074 1310193 32 1279
  0x3924076d 0x21c5a0dcbb988317c64364f8c66cde990da3d319b5786436cf0c66ddd990dc3ab1988487465372e6c862125c998dd38b29884a77342fac66cded8cdabcb19b (by decide +kernel)
private def pack_E6970Receipt58_chunk143 := witnessRule 58 43 64 1310194 1310271 32 1272
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4796436af0c662115dd94db3b3218846756636ee8ca6211dcd9cdc39331884 (by decide +kernel)
private def pack_E6970Receipt58_chunk144 := witnessRule 58 43 96 1310320 1310451 32 1278
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt58_chunk145 := witnessRule 58 43 128 1310452 1310644 32 1299
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt58_chunk146 := witnessRule 58 43 160 1310645 1310896 16 699
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk147 := witnessRule 58 42 0 1320000 1320073 32 1264
  0x403b68a0 0x33cb19b77764370ecc662121d594dcba32188497366374e4ca62129c59cddbb188317e63366f8c66d5e98cdb3c321b777633108eecca6e9d5854425b9b0a89885b726153398e2c2a462171c550d9463a (by decide +kernel)
private def pack_E6970Receipt58_chunk148 := witnessRule 58 42 32 1320074 1320194 32 1217
  0x1e000392 0xee4d06211dc5a8dc3c988317c65364f8c86cded8cc421bd329b47a6436af2c662115e194db3bb218846766636eeaca6211dd19cdc39b3188487268372e2ce62125e4d0beb21b27d63366f6c86d1ed8cdabcb21b (by decide +kernel)
private def pack_E6970Receipt58_chunk149 := witnessRule 58 42 64 1320195 1320321 32 1213
  0x3e003c00 0x8e2da6d5f0c418bd339b2796631084f0d06cddd9cc421bb349b4756831088e8d46d5cda4c422b9359b6716a3108cf8685ed98d93db29b37a6431086f2cc6d1e194c4223bb39b576663108aead06d9d19cc42339b49b (by decide +kernel)
private def pack_E6970Receipt58_chunk150 := witnessRule 58 42 96 1320322 1320454 32 1217
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt58_chunk151 := witnessRule 58 42 128 1320455 1320706 32 1277
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk152 := witnessRule 58 42 160 1320707 1320896 9 389
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk153 := witnessRule 58 41 0 1330000 1330074 32 1199
  0x1c8200 0xaf4c662115e594db3c3218846776636eecca6211dd59cdc3a33188487368372e4ce62125c5a4dd3c188317e64364fcc66cdf190da3db1988447a6536af2c862115e198dc3bb0a898858766153392eac2a462165d18550e539b0a99885a72615538514e4c270a2dc5842145b91b (by decide +kernel)
private def pack_E6970Receipt58_chunk154 := witnessRule 58 41 32 1330075 1330196 32 1157
  0x78001e0 0x574693108ae6d66d9c9a8c42338b61b77b31062f8cc6c9f194d9bdb2188437a66368f2ca62111e19cdabbb318845766836ceace62119d1a4dbb9b418847726a370e2d262121ecd0beb29b27d64366f8c66210ded94da3db21b (by decide +kernel)
private def pack_E6970Receipt58_chunk155 := witnessRule 58 41 64 1330197 1330324 32 1154
  0x7e00f80 0x13a3618842736e366e4da6210dc5bcda3f18831786a364eed262109d9acd9bab518843746c368e6d662111c9b4dab8b6188457e342f6ce6c9e998c4213cb41b3786731086eed26d1d9a0c4223ab51b (by decide +kernel)
private def pack_E6970Receipt58_chunk156 := witnessRule 58 41 96 1330325 1330458 32 1168
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt58_chunk157 := witnessRule 58 41 128 1330512 1330832 32 1268
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk158 := witnessRule 58 41 160 1330833 1330833 1 43
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk159 := witnessRule 58 40 0 1340000 1340074 32 1134
  0x1c0000 0x23d3298844796736af0cc62115dda0db3b3398846756936ee8d06211dcda8dc393498848716b372f4620c5fd8cc420bf329b27d6431084f8cc6cded94c421bd339b57a615338cf2c2a462159e18550e3bbb0a998857766155390eac2a862161d18558e1443a311c2897361310a512e4c670a29c588c429453a1b (by decide +kernel)
private def pack_E6970Receipt58_chunk160 := witnessRule 58 40 32 1340075 1340197 32 1097
  0x3e000f0 0x6ead86d1d1acc42239b69b5726c3108ae2dc6d9f4c418be339b27b6631084f4d06cde59cc421bc349b4776831088ecd46d5d5a4c422ba359b6736a3108ce4d86ddc5acc423be9a17d66364faca6cdf190c421bdb31b (by decide +kernel)
private def pack_E6970Receipt58_chunk161 := witnessRule 58 40 64 1340198 1340326 32 1097
  0xe1fe03f0 0x2e6c801b2726f31084e2c881b37400c418bb369b2756c31084e8dc6cdcdb4c421b9379b4716e31088e801a1796a364f0d262109ddacd9bb351884 (by decide +kernel)
private def pack_E6970Receipt58_chunk162 := witnessRule 58 40 96 1340327 1340515 32 1136
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt58_chunk163 := witnessRule 58 40 128 1340516 1340832 26 1010
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk164 := witnessRule 58 39 0 1350000 1350075 32 1070
  0xc0000 0x9eda0d9bd33988437969368f0d062111dda8dabb3498845756b36ce8d462119cdb0dbb93598847716d370f8620fd94c41f339a17d6631082f8d06cdf18550e23db0a9988547a615538af2c2a862155e18558e33bb0aa988567661573850cecc670a1dd588c42943ba321c2887363310a510e4ca70a25c590c42944bb1b (by decide +kernel)
private def pack_E6970Receipt58_chunk165 := witnessRule 58 39 32 1350076 1350199 32 1040
  0xfc007c 0x2eeda6c9d9b0c4213ab71b3746d31086e6de6d1c9b8c42238b2006d5fcc418bd351b2796931084f0d66cddda8c421bb361b4756b31088e8da6d5cdb0c422b9371b6716d3108cfe685f59cd93e331884 (by decide +kernel)
private def pack_E6970Receipt58_chunk166 := witnessRule 58 39 64 1350200 1350329 32 1047
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt58_chunk167 := witnessRule 58 39 96 1350330 1350519 32 1112
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk168 := witnessRule 58 39 128 1350576 1350832 19 726
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk169 := witnessRule 58 38 0 1360000 1360075 32 1006
  0xe0000 0xbdb51b27a6931084f2d66cde1a8c421bbb61b4766b31088eada6d5d1b0c422b9b71b6726d3108ce2de6ddf8c41f30ab1b17e6155384fac2a862149f18558e1bdb0aa988537a6157388f2c2ac62151e18560e1423c321c2857763310a50aecca70a19d590c429433a331c2877365310a50ee4ce70a21c598c429443c1b (by decide +kernel)
private def pack_E6970Receipt58_chunk170 := witnessRule 58 38 32 1360076 1360200 32 984
  0xe07f803f 0xbab2006c9d1bcc42139b2206cdc990031086e2c901b47440c418bc369b2776c31084ecdc6cdd5b4c421ba379b4736e31088e4c801b5716f3108ae881a (by decide +kernel)
private def pack_E6970Receipt58_chunk171 := witnessRule 58 38 64 1360201 1360331 32 1007
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt58_chunk172 := witnessRule 58 38 96 1360384 1360579 32 1093
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk173 := witnessRule 58 38 128 1360580 1360769 12 449
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk174 := witnessRule 58 37 0 1370000 1370076 32 942
  0xe0061000 0x1796d364f0d862109ddb8d9bb3698843756f368e8dc62111cd90036ae4de62115c591036ce801883f61553109cc2ae6c5f58558c428be30ac1c27a615938504f4ca70a0de590c42941bc331c2847765310a508ecce70a15d598c42942ba341c2867367310a50ce4d270a1dc5a0c42943bd1b (by decide +kernel)
private def pack_E6970Receipt58_chunk175 := witnessRule 58 37 32 1370077 1370202 32 935
  0xfe1ff01f 0x2e6c981b2726480c42138b2806cdd3031062ecc801b2756f31084e8c881b3736400c421b932406d1c591031088e981a (by decide +kernel)
private def pack_E6970Receipt58_chunk176 := witnessRule 58 37 64 1370203 1370386 32 977
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt58_chunk177 := witnessRule 58 37 96 1370387 1370642 32 1077
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk178 := witnessRule 58 37 128 1370643 1370768 5 185
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk179 := witnessRule 58 36 0 1380000 1380076 32 883
  0xf8075800 0x2eec801b2766f31084eac881b3746400c421b9b2406d1c991031088e2c981b57480c41f30ab1904c615a36502f4ce70a09e598c429413c341c2837767310a506ecd270a11d5a0c429423a351c2857369310a50ae4d670a19c5a8c429433e1b (by decide +kernel)
private def pack_E6970Receipt58_chunk180 := witnessRule 58 36 32 1380077 1380203 32 890
  0xffdffe0f 0x5c5960362e8c981b2736480c4213932806cdc593031086ea81a (by decide +kernel)
private def pack_E6970Receipt58_chunk181 := witnessRule 58 36 64 1380204 1380389 32 949
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk182 := witnessRule 58 36 96 1380390 1380768 31 1030
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk183 := witnessRule 58 35 0 1390000 1390077 32 829
  0xff03fe00 0x2eac981b2746480c42139b2806cdc993031086e2ca81b47500c41940bc351c2827769310a504ecd670a0dd5a8c42941ba361c284736b310a508e4da70a15c5b0c42942bf1b (by decide +kernel)
private def pack_E6970Receipt58_chunk184 := witnessRule 58 35 32 1390078 1390205 32 851
  0xffffffc7 0xb932c06c9c595031084eb81a (by decide +kernel)
private def pack_E6970Receipt58_chunk185 := witnessRule 58 35 64 1390256 1390392 32 925
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk186 := witnessRule 58 35 96 1390448 1390705 24 777
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk187 := witnessRule 58 34 0 1400000 1400077 32 780
  0xffc3ff80 0xb9b2c06c9c995031084e2cb81b37580c41940bb369c282756c310a504e8dc70a0dcdb4c42941b9379c284716e310a508e801b (by decide +kernel)
private def pack_E6970Receipt58_chunk188 := witnessRule 58 34 32 1400078 1400257 32 817
  0xfffffffb 0x2ec81a (by decide +kernel)
private def pack_E6970Receipt58_chunk189 := witnessRule 58 34 64 1400258 1400450 32 901
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk190 := witnessRule 58 34 96 1400451 1400704 18 567
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk191 := witnessRule 58 33 0 1410000 1410078 32 735
  0xfffbffe0 0x1716640d940ba320070a09cdbcc4294139322070a0dc5900310a506e901b (by decide +kernel)
private def pack_E6970Receipt58_chunk192 := witnessRule 58 33 32 1410079 1410259 32 788
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk193 := witnessRule 58 33 64 1410260 1410454 32 879
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk194 := witnessRule 58 33 96 1410512 1410704 12 371
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk195 := witnessRule 58 32 0 1420000 1420078 32 694
  0xfffffff8 0x140b9326070a09c5920310a504ea01b (by decide +kernel)
private def pack_E6970Receipt58_chunk196 := witnessRule 58 32 32 1420128 1420261 32 760
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk197 := witnessRule 58 32 64 1420262 1420515 32 859
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk198 := witnessRule 58 32 96 1420516 1420641 6 181
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk199 := witnessRule 58 31 0 1430000 1430128 32 659
  0xfffffffe 0x502eb01b (by decide +kernel)
private def pack_E6970Receipt58_chunk200 := witnessRule 58 31 32 1430129 1430263 32 732
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk201 := witnessRule 58 31 64 1430264 1430640 32 846
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk202 := witnessRule 58 30 0 1440000 1440129 32 626
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk203 := witnessRule 58 30 32 1440130 1440265 32 703
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk204 := witnessRule 58 30 64 1440320 1440640 27 690
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk205 := witnessRule 58 29 0 1450000 1450130 32 596
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk206 := witnessRule 58 29 32 1450131 1450322 32 678
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk207 := witnessRule 58 29 64 1450323 1450577 21 516
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk208 := witnessRule 58 28 0 1460000 1460131 32 565
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk209 := witnessRule 58 28 32 1460132 1460324 32 651
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk210 := witnessRule 58 28 64 1460325 1460576 16 379
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk211 := witnessRule 58 27 0 1470000 1470132 32 535
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk212 := witnessRule 58 27 32 1470133 1470384 32 627
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk213 := witnessRule 58 27 64 1470385 1470576 11 253
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk214 := witnessRule 58 26 0 1480000 1480133 32 504
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk215 := witnessRule 58 26 32 1480134 1480387 32 603
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk216 := witnessRule 58 26 64 1480388 1480513 6 133
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk217 := witnessRule 58 25 0 1490000 1490134 32 474
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk218 := witnessRule 58 25 32 1490135 1490450 32 584
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk219 := witnessRule 58 25 64 1490512 1490512 1 22
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk220 := witnessRule 58 24 0 1500000 1500135 32 443
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk221 := witnessRule 58 24 32 1500136 1500512 29 504
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk222 := witnessRule 58 23 0 1510000 1510136 32 413
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk223 := witnessRule 58 23 32 1510192 1510449 24 393
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk224 := witnessRule 58 22 0 1520000 1520192 32 383
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk225 := witnessRule 58 22 32 1520193 1520448 20 307
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk226 := witnessRule 58 21 0 1530000 1530194 32 355
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk227 := witnessRule 58 21 32 1530195 1530448 16 231
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk228 := witnessRule 58 20 0 1540000 1540195 32 325
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk229 := witnessRule 58 20 32 1540196 1540385 12 161
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk230 := witnessRule 58 19 0 1550000 1550197 32 297
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk231 := witnessRule 58 19 32 1550256 1550384 8 101
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk232 := witnessRule 58 18 0 1560000 1560257 32 269
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk233 := witnessRule 58 18 32 1560258 1560384 5 59
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk234 := witnessRule 58 17 0 1570000 1570320 32 244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk235 := witnessRule 58 17 32 1570321 1570321 1 11
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk236 := witnessRule 58 16 0 1580000 1580320 30 198
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk237 := witnessRule 58 15 0 1590000 1590320 27 150
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk238 := witnessRule 58 14 0 1600000 1600257 24 105
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk239 := witnessRule 58 13 0 1610000 1610256 21 69
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk240 := witnessRule 58 12 0 1620000 1620256 19 42
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk241 := witnessRule 58 11 0 1630000 1630193 16 17
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk242 := witnessRule 58 10 0 1640000 1640192 14 5
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk243 := witnessRule 58 9 0 1650000 1650192 12 1
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk244 := witnessRule 58 8 0 1660000 1660129 10 0
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk245 := witnessRule 58 7 0 1670000 1670128 8 0
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk246 := witnessRule 58 6 0 1680000 1680128 7 0
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk247 := witnessRule 58 5 0 1690000 1690065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk248 := witnessRule 58 4 0 1700000 1700064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk249 := witnessRule 58 3 0 1710000 1710064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk250 := witnessRule 58 2 0 1720000 1720001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk251 := witnessRule 58 1 0 1730000 1730000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt58_chunk252 := witnessRule 58 0 0 1740000 1740000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt58_chunks : List (Chunk 58) := [pack_E6970Receipt58_chunk0, pack_E6970Receipt58_chunk1, pack_E6970Receipt58_chunk2, pack_E6970Receipt58_chunk3, pack_E6970Receipt58_chunk4, pack_E6970Receipt58_chunk5, pack_E6970Receipt58_chunk6, pack_E6970Receipt58_chunk7, pack_E6970Receipt58_chunk8, pack_E6970Receipt58_chunk9, pack_E6970Receipt58_chunk10, pack_E6970Receipt58_chunk11, pack_E6970Receipt58_chunk12, pack_E6970Receipt58_chunk13, pack_E6970Receipt58_chunk14, pack_E6970Receipt58_chunk15, pack_E6970Receipt58_chunk16, pack_E6970Receipt58_chunk17, pack_E6970Receipt58_chunk18, pack_E6970Receipt58_chunk19, pack_E6970Receipt58_chunk20, pack_E6970Receipt58_chunk21, pack_E6970Receipt58_chunk22, pack_E6970Receipt58_chunk23, pack_E6970Receipt58_chunk24, pack_E6970Receipt58_chunk25, pack_E6970Receipt58_chunk26, pack_E6970Receipt58_chunk27, pack_E6970Receipt58_chunk28, pack_E6970Receipt58_chunk29, pack_E6970Receipt58_chunk30, pack_E6970Receipt58_chunk31, pack_E6970Receipt58_chunk32, pack_E6970Receipt58_chunk33, pack_E6970Receipt58_chunk34, pack_E6970Receipt58_chunk35, pack_E6970Receipt58_chunk36, pack_E6970Receipt58_chunk37, pack_E6970Receipt58_chunk38, pack_E6970Receipt58_chunk39, pack_E6970Receipt58_chunk40, pack_E6970Receipt58_chunk41, pack_E6970Receipt58_chunk42, pack_E6970Receipt58_chunk43, pack_E6970Receipt58_chunk44, pack_E6970Receipt58_chunk45, pack_E6970Receipt58_chunk46, pack_E6970Receipt58_chunk47, pack_E6970Receipt58_chunk48, pack_E6970Receipt58_chunk49, pack_E6970Receipt58_chunk50, pack_E6970Receipt58_chunk51, pack_E6970Receipt58_chunk52, pack_E6970Receipt58_chunk53, pack_E6970Receipt58_chunk54, pack_E6970Receipt58_chunk55, pack_E6970Receipt58_chunk56, pack_E6970Receipt58_chunk57, pack_E6970Receipt58_chunk58, pack_E6970Receipt58_chunk59, pack_E6970Receipt58_chunk60, pack_E6970Receipt58_chunk61, pack_E6970Receipt58_chunk62, pack_E6970Receipt58_chunk63, pack_E6970Receipt58_chunk64, pack_E6970Receipt58_chunk65, pack_E6970Receipt58_chunk66, pack_E6970Receipt58_chunk67, pack_E6970Receipt58_chunk68, pack_E6970Receipt58_chunk69, pack_E6970Receipt58_chunk70, pack_E6970Receipt58_chunk71, pack_E6970Receipt58_chunk72, pack_E6970Receipt58_chunk73, pack_E6970Receipt58_chunk74, pack_E6970Receipt58_chunk75, pack_E6970Receipt58_chunk76, pack_E6970Receipt58_chunk77, pack_E6970Receipt58_chunk78, pack_E6970Receipt58_chunk79, pack_E6970Receipt58_chunk80, pack_E6970Receipt58_chunk81, pack_E6970Receipt58_chunk82, pack_E6970Receipt58_chunk83, pack_E6970Receipt58_chunk84, pack_E6970Receipt58_chunk85, pack_E6970Receipt58_chunk86, pack_E6970Receipt58_chunk87, pack_E6970Receipt58_chunk88, pack_E6970Receipt58_chunk89, pack_E6970Receipt58_chunk90, pack_E6970Receipt58_chunk91, pack_E6970Receipt58_chunk92, pack_E6970Receipt58_chunk93, pack_E6970Receipt58_chunk94, pack_E6970Receipt58_chunk95, pack_E6970Receipt58_chunk96, pack_E6970Receipt58_chunk97, pack_E6970Receipt58_chunk98, pack_E6970Receipt58_chunk99, pack_E6970Receipt58_chunk100, pack_E6970Receipt58_chunk101, pack_E6970Receipt58_chunk102, pack_E6970Receipt58_chunk103, pack_E6970Receipt58_chunk104, pack_E6970Receipt58_chunk105, pack_E6970Receipt58_chunk106, pack_E6970Receipt58_chunk107, pack_E6970Receipt58_chunk108, pack_E6970Receipt58_chunk109, pack_E6970Receipt58_chunk110, pack_E6970Receipt58_chunk111, pack_E6970Receipt58_chunk112, pack_E6970Receipt58_chunk113, pack_E6970Receipt58_chunk114, pack_E6970Receipt58_chunk115, pack_E6970Receipt58_chunk116, pack_E6970Receipt58_chunk117, pack_E6970Receipt58_chunk118, pack_E6970Receipt58_chunk119, pack_E6970Receipt58_chunk120, pack_E6970Receipt58_chunk121, pack_E6970Receipt58_chunk122, pack_E6970Receipt58_chunk123, pack_E6970Receipt58_chunk124, pack_E6970Receipt58_chunk125, pack_E6970Receipt58_chunk126, pack_E6970Receipt58_chunk127, pack_E6970Receipt58_chunk128, pack_E6970Receipt58_chunk129, pack_E6970Receipt58_chunk130, pack_E6970Receipt58_chunk131, pack_E6970Receipt58_chunk132, pack_E6970Receipt58_chunk133, pack_E6970Receipt58_chunk134, pack_E6970Receipt58_chunk135, pack_E6970Receipt58_chunk136, pack_E6970Receipt58_chunk137, pack_E6970Receipt58_chunk138, pack_E6970Receipt58_chunk139, pack_E6970Receipt58_chunk140, pack_E6970Receipt58_chunk141, pack_E6970Receipt58_chunk142, pack_E6970Receipt58_chunk143, pack_E6970Receipt58_chunk144, pack_E6970Receipt58_chunk145, pack_E6970Receipt58_chunk146, pack_E6970Receipt58_chunk147, pack_E6970Receipt58_chunk148, pack_E6970Receipt58_chunk149, pack_E6970Receipt58_chunk150, pack_E6970Receipt58_chunk151, pack_E6970Receipt58_chunk152, pack_E6970Receipt58_chunk153, pack_E6970Receipt58_chunk154, pack_E6970Receipt58_chunk155, pack_E6970Receipt58_chunk156, pack_E6970Receipt58_chunk157, pack_E6970Receipt58_chunk158, pack_E6970Receipt58_chunk159, pack_E6970Receipt58_chunk160, pack_E6970Receipt58_chunk161, pack_E6970Receipt58_chunk162, pack_E6970Receipt58_chunk163, pack_E6970Receipt58_chunk164, pack_E6970Receipt58_chunk165, pack_E6970Receipt58_chunk166, pack_E6970Receipt58_chunk167, pack_E6970Receipt58_chunk168, pack_E6970Receipt58_chunk169, pack_E6970Receipt58_chunk170, pack_E6970Receipt58_chunk171, pack_E6970Receipt58_chunk172, pack_E6970Receipt58_chunk173, pack_E6970Receipt58_chunk174, pack_E6970Receipt58_chunk175, pack_E6970Receipt58_chunk176, pack_E6970Receipt58_chunk177, pack_E6970Receipt58_chunk178, pack_E6970Receipt58_chunk179, pack_E6970Receipt58_chunk180, pack_E6970Receipt58_chunk181, pack_E6970Receipt58_chunk182, pack_E6970Receipt58_chunk183, pack_E6970Receipt58_chunk184, pack_E6970Receipt58_chunk185, pack_E6970Receipt58_chunk186, pack_E6970Receipt58_chunk187, pack_E6970Receipt58_chunk188, pack_E6970Receipt58_chunk189, pack_E6970Receipt58_chunk190, pack_E6970Receipt58_chunk191, pack_E6970Receipt58_chunk192, pack_E6970Receipt58_chunk193, pack_E6970Receipt58_chunk194, pack_E6970Receipt58_chunk195, pack_E6970Receipt58_chunk196, pack_E6970Receipt58_chunk197, pack_E6970Receipt58_chunk198, pack_E6970Receipt58_chunk199, pack_E6970Receipt58_chunk200, pack_E6970Receipt58_chunk201, pack_E6970Receipt58_chunk202, pack_E6970Receipt58_chunk203, pack_E6970Receipt58_chunk204, pack_E6970Receipt58_chunk205, pack_E6970Receipt58_chunk206, pack_E6970Receipt58_chunk207, pack_E6970Receipt58_chunk208, pack_E6970Receipt58_chunk209, pack_E6970Receipt58_chunk210, pack_E6970Receipt58_chunk211, pack_E6970Receipt58_chunk212, pack_E6970Receipt58_chunk213, pack_E6970Receipt58_chunk214, pack_E6970Receipt58_chunk215, pack_E6970Receipt58_chunk216, pack_E6970Receipt58_chunk217, pack_E6970Receipt58_chunk218, pack_E6970Receipt58_chunk219, pack_E6970Receipt58_chunk220, pack_E6970Receipt58_chunk221, pack_E6970Receipt58_chunk222, pack_E6970Receipt58_chunk223, pack_E6970Receipt58_chunk224, pack_E6970Receipt58_chunk225, pack_E6970Receipt58_chunk226, pack_E6970Receipt58_chunk227, pack_E6970Receipt58_chunk228, pack_E6970Receipt58_chunk229, pack_E6970Receipt58_chunk230, pack_E6970Receipt58_chunk231, pack_E6970Receipt58_chunk232, pack_E6970Receipt58_chunk233, pack_E6970Receipt58_chunk234, pack_E6970Receipt58_chunk235, pack_E6970Receipt58_chunk236, pack_E6970Receipt58_chunk237, pack_E6970Receipt58_chunk238, pack_E6970Receipt58_chunk239, pack_E6970Receipt58_chunk240, pack_E6970Receipt58_chunk241, pack_E6970Receipt58_chunk242, pack_E6970Receipt58_chunk243, pack_E6970Receipt58_chunk244, pack_E6970Receipt58_chunk245, pack_E6970Receipt58_chunk246, pack_E6970Receipt58_chunk247, pack_E6970Receipt58_chunk248, pack_E6970Receipt58_chunk249, pack_E6970Receipt58_chunk250, pack_E6970Receipt58_chunk251, pack_E6970Receipt58_chunk252]
def rows58 := rowsFrom pack_E6970Receipt58_chunks
theorem good58 : ∀ r ∈ rows58, good 58 r = true := rowsFrom_good pack_E6970Receipt58_chunks
theorem sorted58 : rows58.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt58_chunks 0 (by decide +kernel)).1
theorem mass58 (i : Fin 61) :
    bandCount 58 (i.val : ℤ) 60 16 ≤ (rows58.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt58_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 58 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt58_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total58 : (rows58.map (price 58)).sum = 375035 :=
  (total_eq pack_E6970Receipt58_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt58

section Pack_E6970Receipt59

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt59_chunk0 := witnessA6966Final 59 60 0 1170001 1170065 32 4020
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk1 := witnessA6966Final 59 60 32 1170066 1170132 32 3982
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk2 := witnessA6966Final 59 60 64 1170133 1170200 32 3860
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk3 := witnessA6966Final 59 60 96 1170201 1170270 32 3728
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk4 := witnessA6966Final 59 60 128 1170271 1170341 32 3508
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk5 := witnessA6966Final 59 60 160 1170342 1170456 32 3582
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk6 := witnessA6966Final 59 60 192 1170457 1170577 32 3320
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk7 := witnessA6966Final 59 60 224 1170578 1170704 32 3226
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk8 := witnessA6966Final 59 60 256 1170705 1170837 32 3084
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk9 := witnessA6966Final 59 60 288 1170838 1171030 30 2634
  0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk10 := witnessRule 59 59 0 1180000 1180065 32 3832
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk11 := witnessRule 59 59 32 1180066 1180132 32 3730
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk12 := witnessRule 59 59 64 1180133 1180201 32 3638
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk13 := witnessRule 59 59 96 1180202 1180271 32 3460
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk14 := witnessRule 59 59 128 1180272 1180384 32 3280
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk15 := witnessRule 59 59 160 1180385 1180459 32 3338
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk16 := witnessRule 59 59 192 1180460 1180581 32 3110
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk17 := witnessRule 59 59 224 1180582 1180709 32 2968
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk18 := witnessRule 59 59 256 1180710 1180896 32 2764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk19 := witnessRule 59 59 288 1180897 1181029 22 1782
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk20 := witnessRule 59 58 0 1190000 1190065 32 3584
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk21 := witnessRule 59 58 32 1190066 1190133 32 3520
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk22 := witnessRule 59 58 64 1190134 1190202 32 3376
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk23 := witnessRule 59 58 96 1190203 1190273 32 3204
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk24 := witnessRule 59 58 128 1190274 1190387 32 3114
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk25 := witnessRule 59 58 160 1190388 1190462 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk26 := witnessRule 59 58 192 1190463 1190585 32 2890
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk27 := witnessRule 59 58 224 1190586 1190714 32 2698
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk28 := witnessRule 59 58 256 1190715 1190903 32 2522
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk29 := witnessRule 59 58 288 1190904 1191029 14 1048
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk30 := witnessRule 59 57 0 1200000 1200066 32 3384
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk31 := witnessRule 59 57 32 1200067 1200134 32 3264
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk32 := witnessRule 59 57 64 1200135 1200204 32 3136
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk33 := witnessRule 59 57 96 1200205 1200275 32 2926
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk34 := witnessRule 59 57 128 1200276 1200390 32 2940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk35 := witnessRule 59 57 160 1200391 1200466 32 2704
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk36 := witnessRule 59 57 192 1200512 1200590 32 2656
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk37 := witnessRule 59 57 224 1200591 1200771 32 2494
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk38 := witnessRule 59 57 256 1200772 1200966 32 2282
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk39 := witnessRule 59 57 288 1201024 1201028 5 349
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk40 := witnessRule 59 56 0 1210000 1210066 32 3144
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk41 := witnessRule 59 56 32 1210067 1210135 32 3052
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk42 := witnessRule 59 56 64 1210136 1210205 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk43 := witnessRule 59 56 96 1210206 1210277 32 2684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk44 := witnessRule 59 56 128 1210278 1210393 32 2742
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk45 := witnessRule 59 56 160 1210394 1210515 32 2516
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk46 := witnessRule 59 56 192 1210516 1210643 32 2398
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk47 := witnessRule 59 56 224 1210644 1210777 32 2220
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk48 := witnessRule 59 56 256 1210778 1211028 29 1919
  0x1fffbfff 0xb99a (by decide +kernel)
private def pack_E6970Receipt59_chunk49 := witnessRule 59 55 0 1220000 1220067 32 2944
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk50 := witnessRule 59 55 32 1220068 1220136 32 2802
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk51 := witnessRule 59 55 64 1220137 1220207 32 2634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk52 := witnessRule 59 55 96 1220208 1220321 32 2506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk53 := witnessRule 59 55 128 1220322 1220396 32 2464
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk54 := witnessRule 59 55 160 1220397 1220519 32 2316
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk55 := witnessRule 59 55 192 1220520 1220648 32 2158
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk56 := witnessRule 59 55 224 1220649 1220837 32 2030
  0x7fffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt59_chunk57 := witnessRule 59 55 256 1220838 1221027 20 1228
  0xfffbf 0xba1a (by decide +kernel)
private def pack_E6970Receipt59_chunk58 := witnessRule 59 54 0 1230000 1230067 32 2712
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk59 := witnessRule 59 54 32 1230068 1230137 32 2588
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk60 := witnessRule 59 54 64 1230138 1230208 32 2392
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk61 := witnessRule 59 54 96 1230209 1230323 32 2330
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk62 := witnessRule 59 54 128 1230324 1230399 32 2204
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk63 := witnessRule 59 54 160 1230400 1230523 32 2107
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk64 := witnessRule 59 54 192 1230524 1230704 32 1976
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk65 := witnessRule 59 54 224 1230705 1230899 32 1910
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt59_chunk66 := witnessRule 59 54 256 1230900 1231027 12 710
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk67 := witnessRule 59 53 0 1240000 1240068 32 2512
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk68 := witnessRule 59 53 32 1240069 1240138 32 2345
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk69 := witnessRule 59 53 64 1240139 1240210 32 2172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk70 := witnessRule 59 53 96 1240211 1240326 32 2160
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk71 := witnessRule 59 53 128 1240327 1240448 32 1999
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk72 := witnessRule 59 53 160 1240449 1240576 32 1938
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk73 := witnessRule 59 53 192 1240577 1240710 32 1867
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt59_chunk74 := witnessRule 59 53 224 1240711 1240964 32 1831
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt59_chunk75 := witnessRule 59 53 256 1241024 1241026 3 174
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk76 := witnessRule 59 52 0 1250000 1250068 32 2300
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk77 := witnessRule 59 52 32 1250069 1250139 32 2143
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk78 := witnessRule 59 52 64 1250140 1250211 32 2002
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk79 := witnessRule 59 52 96 1250212 1250328 32 1991
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk80 := witnessRule 59 52 128 1250329 1250451 32 1879
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk81 := witnessRule 59 52 160 1250452 1250580 32 1822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk82 := witnessRule 59 52 192 1250581 1250769 32 1783
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt59_chunk83 := witnessRule 59 52 224 1250770 1251026 27 1498
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt59_chunk84 := witnessRule 59 51 0 1260000 1260069 32 2128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk85 := witnessRule 59 51 32 1260070 1260140 32 1960
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk86 := witnessRule 59 51 64 1260141 1260213 32 1871
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk87 := witnessRule 59 51 96 1260256 1260331 32 1859
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk88 := witnessRule 59 51 128 1260332 1260455 32 1779
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk89 := witnessRule 59 51 160 1260456 1260585 32 1736
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt59_chunk90 := witnessRule 59 51 192 1260586 1260775 32 1710
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt59_chunk91 := witnessRule 59 51 224 1260832 1261025 18 972
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt59_chunk92 := witnessRule 59 50 0 1270000 1270069 32 1958
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk93 := witnessRule 59 50 32 1270070 1270141 32 1834
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk94 := witnessRule 59 50 64 1270142 1270257 32 1775
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk95 := witnessRule 59 50 96 1270258 1270333 32 1741
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk96 := witnessRule 59 50 128 1270334 1270458 32 1694
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk97 := witnessRule 59 50 160 1270459 1270641 32 1663
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt59_chunk98 := witnessRule 59 50 192 1270642 1270837 32 1647
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt59_chunk99 := witnessRule 59 50 224 1270896 1271025 10 532
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk100 := witnessRule 59 49 0 1280000 1280070 32 1822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk101 := witnessRule 59 49 32 1280071 1280142 32 1729
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk102 := witnessRule 59 49 64 1280143 1280259 32 1686
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk103 := witnessRule 59 49 96 1280260 1280336 32 1643
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk104 := witnessRule 59 49 128 1280337 1280462 32 1617
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt59_chunk105 := witnessRule 59 49 160 1280512 1280646 32 1598
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt59_chunk106 := witnessRule 59 49 192 1280647 1280962 32 1607
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt59_chunk107 := witnessRule 59 49 224 1281024 1281024 1 53
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk108 := witnessRule 59 48 0 1290000 1290070 32 1712
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk109 := witnessRule 59 48 32 1290071 1290143 32 1640
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk110 := witnessRule 59 48 64 1290144 1290261 32 1602
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk111 := witnessRule 59 48 96 1290262 1290385 32 1563
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt59_chunk112 := witnessRule 59 48 128 1290386 1290515 32 1549
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt59_chunk113 := witnessRule 59 48 160 1290516 1290705 32 1527
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt59_chunk114 := witnessRule 59 48 192 1290706 1291024 25 1226
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk115 := witnessRule 59 47 0 1300000 1300071 32 1618
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk116 := witnessRule 59 47 32 1300072 1300144 32 1548
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk117 := witnessRule 59 47 64 1300145 1300263 32 1523
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk118 := witnessRule 59 47 96 1300264 1300388 32 1494
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt59_chunk119 := witnessRule 59 47 128 1300389 1300519 32 1475
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt59_chunk120 := witnessRule 59 47 160 1300520 1300711 32 1472
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt59_chunk121 := witnessRule 59 47 192 1300768 1300961 16 771
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk122 := witnessRule 59 46 0 1310000 1310071 32 1527
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk123 := witnessRule 59 46 32 1310072 1310145 32 1463
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk124 := witnessRule 59 46 64 1310146 1310265 32 1453
  0xb6bfffff 0x5766336ee8c66e5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt59_chunk125 := witnessRule 59 46 96 1310266 1310391 32 1425
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt59_chunk126 := witnessRule 59 46 128 1310392 1310523 32 1407
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt59_chunk127 := witnessRule 59 46 160 1310576 1310773 32 1436
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt59_chunk128 := witnessRule 59 46 192 1310832 1310960 8 381
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk129 := witnessRule 59 45 0 1320000 1320072 32 1445
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk130 := witnessRule 59 45 32 1320073 1320146 32 1381
  0xffffdfff 0x6399a (by decide +kernel)
private def pack_E6970Receipt59_chunk131 := witnessRule 59 45 64 1320147 1320267 32 1385
  0x920edb69 0x37864368f0c66d5d990db3b319b77464370e6c662121c994dcb8b21884976342f6c66cde58cdabbb19b77563372e6c66e9c590ddb99883 (by decide +kernel)
private def pack_E6970Receipt59_chunk132 := witnessRule 59 45 96 1320268 1320394 32 1357
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt59_chunk133 := witnessRule 59 45 128 1320395 1320580 32 1354
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt59_chunk134 := witnessRule 59 45 160 1320581 1320960 32 1418
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk135 := witnessRule 59 44 0 1330000 1330072 32 1365
  0xfefffffc 0x18e2c66f5ccd738a2 (by decide +kernel)
private def pack_E6970Receipt59_chunk136 := witnessRule 59 44 32 1330073 1330147 32 1309
  0xedb68fff 0x17c63366f4c66d5e18cdbbb319b97463374e4c86edc58cc425ba9a (by decide +kernel)
private def pack_E6970Receipt59_chunk137 := witnessRule 59 44 64 1330192 1330269 32 1317
  0x80039240 0xbd329b27a64366f2c66210de194da3c321b577633108aecca6d9d590c4233a331b773653108ee4ce6e1c598c4243c1a17b64364f6c66cde590da3cb19b5776436ceec66ddd590dc3a31988487365372e4c862125c598dd3a9883 (by decide +kernel)
private def pack_E6970Receipt59_chunk138 := witnessRule 59 44 96 1330270 1330397 32 1295
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt59_chunk139 := witnessRule 59 44 128 1330448 1330584 32 1307
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt59_chunk140 := witnessRule 59 44 160 1330640 1330897 24 1042
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk141 := witnessRule 59 43 0 1340000 1340073 32 1297
  0xb43fffd0 0xeeec66e5d58cdd39b21bb726331096e2ca6f1d0c41d3a319bb726436318e4cf1d4d0c6b89b (by decide +kernel)
private def pack_E6970Receipt59_chunk142 := witnessRule 59 43 32 1340074 1340193 32 1247
  0x3924076d 0x21c5a0dcbb988317c64364f8c66cde990da3d319b5786436cf0c66ddd990dc3ab1988487465372e6c862125c998dd38b29884a77342fac66cded8cdabcb19b (by decide +kernel)
private def pack_E6970Receipt59_chunk143 := witnessRule 59 43 64 1340194 1340271 32 1240
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4796436af0c662115dd94db3b3218846756636ee8ca6211dcd9cdc39331884 (by decide +kernel)
private def pack_E6970Receipt59_chunk144 := witnessRule 59 43 96 1340320 1340451 32 1246
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt59_chunk145 := witnessRule 59 43 128 1340452 1340644 32 1267
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt59_chunk146 := witnessRule 59 43 160 1340645 1340896 16 683
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk147 := witnessRule 59 42 0 1350000 1350073 32 1228
  0x403b6d00 0x33cb19b77764370ecc662121d594dcba32188497366374e4ca62129c59cddbb188317e63366f8c66d5e98cdbbc319b87664372eac662125d194d8c53a309c18b736108316e4c470631c584c428c6399b (by decide +kernel)
private def pack_E6970Receipt59_chunk148 := witnessRule 59 42 32 1350074 1350194 32 1185
  0x1e000392 0xee4d06211dc5a8dc3c988317c65364f8c86cded8cc421bd329b47a6436af2c662115e194db3bb218846766636eeaca6211dd19cdc39b3188487268372e2ce62125e4d0beb21b27d63366f6c86d1ed8cdabcb21b (by decide +kernel)
private def pack_E6970Receipt59_chunk149 := witnessRule 59 42 64 1350195 1350321 32 1181
  0x3e003c00 0x8e2da6d5f0c418bd339b2796631084f0d06cddd9cc421bb349b4756831088e8d46d5cda4c422b9359b6716a3108cf8685ed98d93db29b37a6431086f2cc6d1e194c4223bb39b576663108aead06d9d19cc42339b49b (by decide +kernel)
private def pack_E6970Receipt59_chunk150 := witnessRule 59 42 96 1350322 1350454 32 1185
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt59_chunk151 := witnessRule 59 42 128 1350455 1350706 32 1245
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk152 := witnessRule 59 42 160 1350707 1350896 9 380
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk153 := witnessRule 59 41 0 1360000 1360074 32 1163
  0x1c9000 0xaf4c662115e594db3c3218846776636eecca6211dd59cdc3a33188487368372e4ce62125c5a4dd3c188317e64364fcc66cdf190da3e319b57a6436cf2c662119e194dbbbb218847766636310ecc470625d584c428c4ba319c18a7362310a314e4c87062dc58cc428c5ba9b (by decide +kernel)
private def pack_E6970Receipt59_chunk154 := witnessRule 59 41 32 1360075 1360196 32 1125
  0x78001e0 0x574693108ae6d66d9c9a8c42338b61b77b31062f8cc6c9f194d9bdb2188437a66368f2ca62111e19cdabbb318845766836ceace62119d1a4dbb9b418847726a370e2d262121ecd0beb29b27d64366f8c66210ded94da3db21b (by decide +kernel)
private def pack_E6970Receipt59_chunk155 := witnessRule 59 41 64 1360197 1360324 32 1122
  0x7e00f80 0x13a3618842736e366e4da6210dc5bcda3f18831786a364eed262109d9acd9bab518843746c368e6d662111c9b4dab8b6188457e342f6ce6c9e998c4213cb41b3786731086eed26d1d9a0c4223ab51b (by decide +kernel)
private def pack_E6970Receipt59_chunk156 := witnessRule 59 41 96 1360325 1360458 32 1136
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt59_chunk157 := witnessRule 59 41 128 1360512 1360832 32 1236
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk158 := witnessRule 59 41 160 1360833 1360833 1 42
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk159 := witnessRule 59 40 0 1370000 1370074 32 1098
  0x1e0000 0x47a6531088f2ce6d5e198c422bbb41b676673108cead26ddd1a0c423b9b51b8726931090e2d66e5e8c418bf329b27e64366fac66210df194da3db2188447a6636af2ca62115e19cd8c33c319c1877762310a30eecc870621d58cc428c43a329c1897364310a312e4cc70629c594c428c53b9b (by decide +kernel)
private def pack_E6970Receipt59_chunk160 := witnessRule 59 40 32 1370075 1370197 32 1065
  0x3e000f0 0x6ead86d1d1acc42239b69b5726c3108ae2dc6d9f4c418be339b27b6631084f4d06cde59cc421bc349b4776831088ecd46d5d5a4c422ba359b6736a3108ce4d86ddc5acc423be9a17d66364faca6cdf190c421bdb31b (by decide +kernel)
private def pack_E6970Receipt59_chunk161 := witnessRule 59 40 64 1370198 1370326 32 1065
  0xe1fe03f0 0x2e6c801b2726f31084e2c881b37400c418bb369b2756c31084e8dc6cdcdb4c421b9379b4716e31088e801a1796a364f0d262109ddacd9bb351884 (by decide +kernel)
private def pack_E6970Receipt59_chunk162 := witnessRule 59 40 96 1370327 1370515 32 1104
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt59_chunk163 := witnessRule 59 40 128 1370516 1370832 26 984
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk164 := witnessRule 59 39 0 1380000 1380075 32 1034
  0xe0000 0x13db41b37a6731086f2d26d1e1a0c4223bb51b576693108aead66d9d1a8c42339b61b7726b3108ee2da6e1f0c418bfb2188417e66364faca62109f19cd9bdb3188437a6836308f4c870615e58cc428c2bc329c1867764310a30ceccc7061dd594c428c3ba339c1887366310a310e4d070625c59cc428c4bc9b (by decide +kernel)
private def pack_E6970Receipt59_chunk165 := witnessRule 59 39 32 1380076 1380199 32 1008
  0xfc007c 0x2eeda6c9d9b0c4213ab71b3746d31086e6de6d1c9b8c42238b2006d5fcc418bd351b2796931084f0d66cddda8c421bb361b4756b31088e8da6d5cdb0c422b9371b6716d3108cfe685f59cd93e331884 (by decide +kernel)
private def pack_E6970Receipt59_chunk166 := witnessRule 59 39 64 1380200 1380329 32 1015
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt59_chunk167 := witnessRule 59 39 96 1380330 1380519 32 1080
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk168 := witnessRule 59 39 128 1380576 1380832 19 707
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk169 := witnessRule 59 38 0 1390000 1390075 32 972
  0xe4000 0x17b6a364f4d262109e5acd9bc3518843776c368ecd662111d5b4daba3618845736e36ce4da62119c5bcdbbf1883f663107cd0685f1a4d8c13e329c1837b64310a306f4cc70611e594c428c23c339c1857766310a30aecd070619d59cc428c33a349c1877368310a30ee4d470621c5a4c428c43d9b (by decide +kernel)
private def pack_E6970Receipt59_chunk170 := witnessRule 59 38 32 1390076 1390200 32 952
  0xe07f803f 0xbab2006c9d1bcc42139b2206cdc990031086e2c901b47440c418bc369b2776c31084ecdc6cdd5b4c421ba379b4736e31088e4c801b5716f3108ae881a (by decide +kernel)
private def pack_E6970Receipt59_chunk171 := witnessRule 59 38 64 1390201 1390331 32 975
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt59_chunk172 := witnessRule 59 38 96 1390384 1390579 32 1061
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk173 := witnessRule 59 38 128 1390580 1390769 12 437
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk174 := witnessRule 59 37 0 1400000 1400076 32 908
  0xe0076000 0x5e5b4d93c3618842776e366ecda6210dd5bcda3a3718844736400dab93798845716440db3a00620f9855cd8c0be339c1827b66310a304f4d07060de59cc428c1bc349c1847768310a308ecd470615d5a4c428c2ba359c186736a310a30ce4d87061dc5acc428c3be9b (by decide +kernel)
private def pack_E6970Receipt59_chunk175 := witnessRule 59 37 32 1400077 1400202 32 903
  0xfe1ff01f 0x2e6c981b2726480c42138b2806cdd3031062ecc801b2756f31084e8c881b3736400c421b932406d1c591031088e981a (by decide +kernel)
private def pack_E6970Receipt59_chunk176 := witnessRule 59 37 64 1400203 1400386 32 945
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt59_chunk177 := witnessRule 59 37 96 1400387 1400642 32 1045
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk178 := witnessRule 59 37 128 1400643 1400768 5 180
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk179 := witnessRule 59 36 0 1410000 1410076 32 851
  0xf807f800 0xbbb2006c9d9bcc4213ab2206cdd190031086e6c901b4726440c42238b2606d5d203106302f4d470609e5a4c428c13c359c183776a310a306ecd870611d5acc428c23a369c185736c310a30ae4dc70619c5b4c428c33f9b (by decide +kernel)
private def pack_E6970Receipt59_chunk180 := witnessRule 59 36 32 1410077 1410203 32 858
  0xffdffe0f 0x5c5960362e8c981b2736480c4213932806cdc593031086ea81a (by decide +kernel)
private def pack_E6970Receipt59_chunk181 := witnessRule 59 36 64 1410204 1410389 32 917
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk182 := witnessRule 59 36 96 1410390 1410768 31 999
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk183 := witnessRule 59 35 0 1420000 1420077 32 797
  0xff03fe00 0x2eac981b2746480c42139b2806cdc993031086e2ca81b47500c418c0bc369c182776c310a304ecdc7060dd5b4c428c1ba379c184736e310a308e4c801c185716f310a30ae881b (by decide +kernel)
private def pack_E6970Receipt59_chunk184 := witnessRule 59 35 32 1420078 1420205 32 819
  0xffffffc7 0xb932c06c9c595031084eb81a (by decide +kernel)
private def pack_E6970Receipt59_chunk185 := witnessRule 59 35 64 1420256 1420392 32 893
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk186 := witnessRule 59 35 96 1420448 1420705 24 753
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk187 := witnessRule 59 34 0 1430000 1430077 32 748
  0xffc3ff80 0x2e6cb01b2726540c42138b2e06cdd603106302ecc801c182756f310a304e8c881c183736400c428c1b9324070611c5910310a308e981b (by decide +kernel)
private def pack_E6970Receipt59_chunk188 := witnessRule 59 34 32 1430078 1430257 32 785
  0xfffffffb 0x2ec81a (by decide +kernel)
private def pack_E6970Receipt59_chunk189 := witnessRule 59 34 64 1430258 1430450 32 869
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk190 := witnessRule 59 34 96 1430451 1430704 18 549
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk191 := witnessRule 59 33 0 1440000 1440078 32 703
  0xfffbffe0 0x5c599036302e8c981c182736480c428c13932807060dc5930310a306ea81b (by decide +kernel)
private def pack_E6970Receipt59_chunk192 := witnessRule 59 33 32 1440079 1440259 32 756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk193 := witnessRule 59 33 64 1440260 1440454 32 847
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk194 := witnessRule 59 33 96 1440512 1440704 12 359
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk195 := witnessRule 59 32 0 1450000 1450078 32 662
  0xfffffff8 0xc0b932c070609c5950310a304eb81b (by decide +kernel)
private def pack_E6970Receipt59_chunk196 := witnessRule 59 32 32 1450128 1450261 32 728
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk197 := witnessRule 59 32 64 1450262 1450515 32 827
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk198 := witnessRule 59 32 96 1450516 1450641 6 175
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk199 := witnessRule 59 31 0 1460000 1460128 32 627
  0xfffffffe 0x302ec81b (by decide +kernel)
private def pack_E6970Receipt59_chunk200 := witnessRule 59 31 32 1460129 1460263 32 700
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk201 := witnessRule 59 31 64 1460264 1460640 32 814
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk202 := witnessRule 59 30 0 1470000 1470129 32 594
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk203 := witnessRule 59 30 32 1470130 1470265 32 671
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk204 := witnessRule 59 30 64 1470320 1470640 27 663
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk205 := witnessRule 59 29 0 1480000 1480130 32 564
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk206 := witnessRule 59 29 32 1480131 1480322 32 646
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk207 := witnessRule 59 29 64 1480323 1480577 21 495
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk208 := witnessRule 59 28 0 1490000 1490131 32 533
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk209 := witnessRule 59 28 32 1490132 1490324 32 619
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk210 := witnessRule 59 28 64 1490325 1490576 16 363
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk211 := witnessRule 59 27 0 1500000 1500132 32 503
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk212 := witnessRule 59 27 32 1500133 1500384 32 595
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk213 := witnessRule 59 27 64 1500385 1500576 11 242
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk214 := witnessRule 59 26 0 1510000 1510133 32 472
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk215 := witnessRule 59 26 32 1510134 1510387 32 571
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk216 := witnessRule 59 26 64 1510388 1510513 6 127
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk217 := witnessRule 59 25 0 1520000 1520134 32 442
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk218 := witnessRule 59 25 32 1520135 1520450 32 552
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk219 := witnessRule 59 25 64 1520512 1520512 1 21
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk220 := witnessRule 59 24 0 1530000 1530135 32 411
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk221 := witnessRule 59 24 32 1530136 1530512 29 475
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk222 := witnessRule 59 23 0 1540000 1540136 32 381
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk223 := witnessRule 59 23 32 1540192 1540449 24 369
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk224 := witnessRule 59 22 0 1550000 1550192 32 351
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk225 := witnessRule 59 22 32 1550193 1550448 20 287
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk226 := witnessRule 59 21 0 1560000 1560194 32 323
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk227 := witnessRule 59 21 32 1560195 1560448 16 215
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk228 := witnessRule 59 20 0 1570000 1570195 32 293
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk229 := witnessRule 59 20 32 1570196 1570385 12 149
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk230 := witnessRule 59 19 0 1580000 1580197 32 265
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk231 := witnessRule 59 19 32 1580256 1580384 8 93
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk232 := witnessRule 59 18 0 1590000 1590257 32 237
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk233 := witnessRule 59 18 32 1590258 1590384 5 54
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk234 := witnessRule 59 17 0 1600000 1600320 32 212
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk235 := witnessRule 59 17 32 1600321 1600321 1 10
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk236 := witnessRule 59 16 0 1610000 1610320 30 168
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk237 := witnessRule 59 15 0 1620000 1620320 27 123
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk238 := witnessRule 59 14 0 1630000 1630257 24 81
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk239 := witnessRule 59 13 0 1640000 1640256 21 48
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk240 := witnessRule 59 12 0 1650000 1650256 19 23
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk241 := witnessRule 59 11 0 1660000 1660193 16 7
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk242 := witnessRule 59 10 0 1670000 1670192 14 1
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk243 := witnessRule 59 9 0 1680000 1680192 12 0
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk244 := witnessRule 59 8 0 1690000 1690129 10 0
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk245 := witnessRule 59 7 0 1700000 1700128 8 0
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk246 := witnessRule 59 6 0 1710000 1710128 7 0
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk247 := witnessRule 59 5 0 1720000 1720065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk248 := witnessRule 59 4 0 1730000 1730064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk249 := witnessRule 59 3 0 1740000 1740064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk250 := witnessRule 59 2 0 1750000 1750001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk251 := witnessRule 59 1 0 1760000 1760000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt59_chunk252 := witnessRule 59 0 0 1770000 1770000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt59_chunks : List (Chunk 59) := [pack_E6970Receipt59_chunk0, pack_E6970Receipt59_chunk1, pack_E6970Receipt59_chunk2, pack_E6970Receipt59_chunk3, pack_E6970Receipt59_chunk4, pack_E6970Receipt59_chunk5, pack_E6970Receipt59_chunk6, pack_E6970Receipt59_chunk7, pack_E6970Receipt59_chunk8, pack_E6970Receipt59_chunk9, pack_E6970Receipt59_chunk10, pack_E6970Receipt59_chunk11, pack_E6970Receipt59_chunk12, pack_E6970Receipt59_chunk13, pack_E6970Receipt59_chunk14, pack_E6970Receipt59_chunk15, pack_E6970Receipt59_chunk16, pack_E6970Receipt59_chunk17, pack_E6970Receipt59_chunk18, pack_E6970Receipt59_chunk19, pack_E6970Receipt59_chunk20, pack_E6970Receipt59_chunk21, pack_E6970Receipt59_chunk22, pack_E6970Receipt59_chunk23, pack_E6970Receipt59_chunk24, pack_E6970Receipt59_chunk25, pack_E6970Receipt59_chunk26, pack_E6970Receipt59_chunk27, pack_E6970Receipt59_chunk28, pack_E6970Receipt59_chunk29, pack_E6970Receipt59_chunk30, pack_E6970Receipt59_chunk31, pack_E6970Receipt59_chunk32, pack_E6970Receipt59_chunk33, pack_E6970Receipt59_chunk34, pack_E6970Receipt59_chunk35, pack_E6970Receipt59_chunk36, pack_E6970Receipt59_chunk37, pack_E6970Receipt59_chunk38, pack_E6970Receipt59_chunk39, pack_E6970Receipt59_chunk40, pack_E6970Receipt59_chunk41, pack_E6970Receipt59_chunk42, pack_E6970Receipt59_chunk43, pack_E6970Receipt59_chunk44, pack_E6970Receipt59_chunk45, pack_E6970Receipt59_chunk46, pack_E6970Receipt59_chunk47, pack_E6970Receipt59_chunk48, pack_E6970Receipt59_chunk49, pack_E6970Receipt59_chunk50, pack_E6970Receipt59_chunk51, pack_E6970Receipt59_chunk52, pack_E6970Receipt59_chunk53, pack_E6970Receipt59_chunk54, pack_E6970Receipt59_chunk55, pack_E6970Receipt59_chunk56, pack_E6970Receipt59_chunk57, pack_E6970Receipt59_chunk58, pack_E6970Receipt59_chunk59, pack_E6970Receipt59_chunk60, pack_E6970Receipt59_chunk61, pack_E6970Receipt59_chunk62, pack_E6970Receipt59_chunk63, pack_E6970Receipt59_chunk64, pack_E6970Receipt59_chunk65, pack_E6970Receipt59_chunk66, pack_E6970Receipt59_chunk67, pack_E6970Receipt59_chunk68, pack_E6970Receipt59_chunk69, pack_E6970Receipt59_chunk70, pack_E6970Receipt59_chunk71, pack_E6970Receipt59_chunk72, pack_E6970Receipt59_chunk73, pack_E6970Receipt59_chunk74, pack_E6970Receipt59_chunk75, pack_E6970Receipt59_chunk76, pack_E6970Receipt59_chunk77, pack_E6970Receipt59_chunk78, pack_E6970Receipt59_chunk79, pack_E6970Receipt59_chunk80, pack_E6970Receipt59_chunk81, pack_E6970Receipt59_chunk82, pack_E6970Receipt59_chunk83, pack_E6970Receipt59_chunk84, pack_E6970Receipt59_chunk85, pack_E6970Receipt59_chunk86, pack_E6970Receipt59_chunk87, pack_E6970Receipt59_chunk88, pack_E6970Receipt59_chunk89, pack_E6970Receipt59_chunk90, pack_E6970Receipt59_chunk91, pack_E6970Receipt59_chunk92, pack_E6970Receipt59_chunk93, pack_E6970Receipt59_chunk94, pack_E6970Receipt59_chunk95, pack_E6970Receipt59_chunk96, pack_E6970Receipt59_chunk97, pack_E6970Receipt59_chunk98, pack_E6970Receipt59_chunk99, pack_E6970Receipt59_chunk100, pack_E6970Receipt59_chunk101, pack_E6970Receipt59_chunk102, pack_E6970Receipt59_chunk103, pack_E6970Receipt59_chunk104, pack_E6970Receipt59_chunk105, pack_E6970Receipt59_chunk106, pack_E6970Receipt59_chunk107, pack_E6970Receipt59_chunk108, pack_E6970Receipt59_chunk109, pack_E6970Receipt59_chunk110, pack_E6970Receipt59_chunk111, pack_E6970Receipt59_chunk112, pack_E6970Receipt59_chunk113, pack_E6970Receipt59_chunk114, pack_E6970Receipt59_chunk115, pack_E6970Receipt59_chunk116, pack_E6970Receipt59_chunk117, pack_E6970Receipt59_chunk118, pack_E6970Receipt59_chunk119, pack_E6970Receipt59_chunk120, pack_E6970Receipt59_chunk121, pack_E6970Receipt59_chunk122, pack_E6970Receipt59_chunk123, pack_E6970Receipt59_chunk124, pack_E6970Receipt59_chunk125, pack_E6970Receipt59_chunk126, pack_E6970Receipt59_chunk127, pack_E6970Receipt59_chunk128, pack_E6970Receipt59_chunk129, pack_E6970Receipt59_chunk130, pack_E6970Receipt59_chunk131, pack_E6970Receipt59_chunk132, pack_E6970Receipt59_chunk133, pack_E6970Receipt59_chunk134, pack_E6970Receipt59_chunk135, pack_E6970Receipt59_chunk136, pack_E6970Receipt59_chunk137, pack_E6970Receipt59_chunk138, pack_E6970Receipt59_chunk139, pack_E6970Receipt59_chunk140, pack_E6970Receipt59_chunk141, pack_E6970Receipt59_chunk142, pack_E6970Receipt59_chunk143, pack_E6970Receipt59_chunk144, pack_E6970Receipt59_chunk145, pack_E6970Receipt59_chunk146, pack_E6970Receipt59_chunk147, pack_E6970Receipt59_chunk148, pack_E6970Receipt59_chunk149, pack_E6970Receipt59_chunk150, pack_E6970Receipt59_chunk151, pack_E6970Receipt59_chunk152, pack_E6970Receipt59_chunk153, pack_E6970Receipt59_chunk154, pack_E6970Receipt59_chunk155, pack_E6970Receipt59_chunk156, pack_E6970Receipt59_chunk157, pack_E6970Receipt59_chunk158, pack_E6970Receipt59_chunk159, pack_E6970Receipt59_chunk160, pack_E6970Receipt59_chunk161, pack_E6970Receipt59_chunk162, pack_E6970Receipt59_chunk163, pack_E6970Receipt59_chunk164, pack_E6970Receipt59_chunk165, pack_E6970Receipt59_chunk166, pack_E6970Receipt59_chunk167, pack_E6970Receipt59_chunk168, pack_E6970Receipt59_chunk169, pack_E6970Receipt59_chunk170, pack_E6970Receipt59_chunk171, pack_E6970Receipt59_chunk172, pack_E6970Receipt59_chunk173, pack_E6970Receipt59_chunk174, pack_E6970Receipt59_chunk175, pack_E6970Receipt59_chunk176, pack_E6970Receipt59_chunk177, pack_E6970Receipt59_chunk178, pack_E6970Receipt59_chunk179, pack_E6970Receipt59_chunk180, pack_E6970Receipt59_chunk181, pack_E6970Receipt59_chunk182, pack_E6970Receipt59_chunk183, pack_E6970Receipt59_chunk184, pack_E6970Receipt59_chunk185, pack_E6970Receipt59_chunk186, pack_E6970Receipt59_chunk187, pack_E6970Receipt59_chunk188, pack_E6970Receipt59_chunk189, pack_E6970Receipt59_chunk190, pack_E6970Receipt59_chunk191, pack_E6970Receipt59_chunk192, pack_E6970Receipt59_chunk193, pack_E6970Receipt59_chunk194, pack_E6970Receipt59_chunk195, pack_E6970Receipt59_chunk196, pack_E6970Receipt59_chunk197, pack_E6970Receipt59_chunk198, pack_E6970Receipt59_chunk199, pack_E6970Receipt59_chunk200, pack_E6970Receipt59_chunk201, pack_E6970Receipt59_chunk202, pack_E6970Receipt59_chunk203, pack_E6970Receipt59_chunk204, pack_E6970Receipt59_chunk205, pack_E6970Receipt59_chunk206, pack_E6970Receipt59_chunk207, pack_E6970Receipt59_chunk208, pack_E6970Receipt59_chunk209, pack_E6970Receipt59_chunk210, pack_E6970Receipt59_chunk211, pack_E6970Receipt59_chunk212, pack_E6970Receipt59_chunk213, pack_E6970Receipt59_chunk214, pack_E6970Receipt59_chunk215, pack_E6970Receipt59_chunk216, pack_E6970Receipt59_chunk217, pack_E6970Receipt59_chunk218, pack_E6970Receipt59_chunk219, pack_E6970Receipt59_chunk220, pack_E6970Receipt59_chunk221, pack_E6970Receipt59_chunk222, pack_E6970Receipt59_chunk223, pack_E6970Receipt59_chunk224, pack_E6970Receipt59_chunk225, pack_E6970Receipt59_chunk226, pack_E6970Receipt59_chunk227, pack_E6970Receipt59_chunk228, pack_E6970Receipt59_chunk229, pack_E6970Receipt59_chunk230, pack_E6970Receipt59_chunk231, pack_E6970Receipt59_chunk232, pack_E6970Receipt59_chunk233, pack_E6970Receipt59_chunk234, pack_E6970Receipt59_chunk235, pack_E6970Receipt59_chunk236, pack_E6970Receipt59_chunk237, pack_E6970Receipt59_chunk238, pack_E6970Receipt59_chunk239, pack_E6970Receipt59_chunk240, pack_E6970Receipt59_chunk241, pack_E6970Receipt59_chunk242, pack_E6970Receipt59_chunk243, pack_E6970Receipt59_chunk244, pack_E6970Receipt59_chunk245, pack_E6970Receipt59_chunk246, pack_E6970Receipt59_chunk247, pack_E6970Receipt59_chunk248, pack_E6970Receipt59_chunk249, pack_E6970Receipt59_chunk250, pack_E6970Receipt59_chunk251, pack_E6970Receipt59_chunk252]
def rows59 := rowsFrom pack_E6970Receipt59_chunks
theorem good59 : ∀ r ∈ rows59, good 59 r = true := rowsFrom_good pack_E6970Receipt59_chunks
theorem sorted59 : rows59.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt59_chunks 0 (by decide +kernel)).1
theorem mass59 (i : Fin 61) :
    bandCount 59 (i.val : ℤ) 60 16 ≤ (rows59.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt59_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 59 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt59_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total59 : (rows59.map (price 59)).sum = 370363 :=
  (total_eq pack_E6970Receipt59_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt59

section Pack_E6970Receipt60

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt60_chunk0 := witnessA6966Final 60 60 0 1200000 1200064 32 120780
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk1 := witnessA6966Final 60 60 32 1200065 1200131 32 119760
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk2 := witnessA6966Final 60 60 64 1200132 1200199 32 116160
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk3 := witnessA6966Final 60 60 96 1200200 1200269 32 112320
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk4 := witnessA6966Final 60 60 128 1200270 1200340 32 105780
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk5 := witnessA6966Final 60 60 160 1200341 1200455 32 106920
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk6 := witnessA6966Final 60 60 192 1200456 1200576 32 99420
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk7 := witnessA6966Final 60 60 224 1200577 1200655 32 96960
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk8 := witnessA6966Final 60 60 256 1200704 1200836 32 93060
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk9 := witnessA6966Final 60 60 288 1200837 1201030 31 81810
  0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk10 := witnessRule 60 59 0 1210000 1210065 32 114780
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk11 := witnessRule 60 59 32 1210066 1210132 32 111900
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk12 := witnessRule 60 59 64 1210133 1210201 32 109140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk13 := witnessRule 60 59 96 1210202 1210271 32 103800
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk14 := witnessRule 60 59 128 1210272 1210384 32 98400
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk15 := witnessRule 60 59 160 1210385 1210459 32 100140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk16 := witnessRule 60 59 192 1210460 1210581 32 93300
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk17 := witnessRule 60 59 224 1210582 1210709 32 89040
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk18 := witnessRule 60 59 256 1210710 1210896 32 82920
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk19 := witnessRule 60 59 288 1210897 1211029 22 53460
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk20 := witnessRule 60 58 0 1220000 1220065 32 107340
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk21 := witnessRule 60 58 32 1220066 1220133 32 105600
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk22 := witnessRule 60 58 64 1220134 1220202 32 101280
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk23 := witnessRule 60 58 96 1220203 1220273 32 96120
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk24 := witnessRule 60 58 128 1220274 1220387 32 93420
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk25 := witnessRule 60 58 160 1220388 1220462 32 90360
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk26 := witnessRule 60 58 192 1220463 1220585 32 86700
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk27 := witnessRule 60 58 224 1220586 1220714 32 80940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk28 := witnessRule 60 58 256 1220715 1220903 32 75660
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk29 := witnessRule 60 58 288 1220904 1221029 14 31440
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk30 := witnessRule 60 57 0 1230000 1230066 32 101340
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk31 := witnessRule 60 57 32 1230067 1230134 32 97920
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk32 := witnessRule 60 57 64 1230135 1230204 32 94080
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk33 := witnessRule 60 57 96 1230205 1230275 32 87780
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk34 := witnessRule 60 57 128 1230276 1230390 32 88200
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk35 := witnessRule 60 57 160 1230391 1230466 32 81120
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk36 := witnessRule 60 57 192 1230512 1230590 32 79680
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk37 := witnessRule 60 57 224 1230591 1230771 32 74820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk38 := witnessRule 60 57 256 1230772 1230966 32 68460
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk39 := witnessRule 60 57 288 1231024 1231028 5 10470
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk40 := witnessRule 60 56 0 1240000 1240066 32 94140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk41 := witnessRule 60 56 32 1240067 1240135 32 91560
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk42 := witnessRule 60 56 64 1240136 1240205 32 86400
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk43 := witnessRule 60 56 96 1240206 1240277 32 80520
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk44 := witnessRule 60 56 128 1240278 1240393 32 82260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk45 := witnessRule 60 56 160 1240394 1240515 32 75480
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk46 := witnessRule 60 56 192 1240516 1240643 32 71940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk47 := witnessRule 60 56 224 1240644 1240777 32 66600
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk48 := witnessRule 60 56 256 1240778 1241028 29 57570
  0x1fffbfff 0xb99a (by decide +kernel)
private def pack_E6970Receipt60_chunk49 := witnessRule 60 55 0 1250000 1250067 32 88140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk50 := witnessRule 60 55 32 1250068 1250136 32 84060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk51 := witnessRule 60 55 64 1250137 1250207 32 79020
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk52 := witnessRule 60 55 96 1250208 1250321 32 75180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk53 := witnessRule 60 55 128 1250322 1250396 32 73920
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk54 := witnessRule 60 55 160 1250397 1250519 32 69480
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk55 := witnessRule 60 55 192 1250520 1250648 32 64740
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk56 := witnessRule 60 55 224 1250649 1250837 32 60840
  0x7fffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt60_chunk57 := witnessRule 60 55 256 1250838 1251027 20 36720
  0xfffbf 0xba1a (by decide +kernel)
private def pack_E6970Receipt60_chunk58 := witnessRule 60 54 0 1260000 1260067 32 81180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk59 := witnessRule 60 54 32 1260068 1260137 32 77640
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk60 := witnessRule 60 54 64 1260138 1260208 32 71760
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk61 := witnessRule 60 54 96 1260209 1260323 32 69900
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk62 := witnessRule 60 54 128 1260324 1260399 32 66120
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk63 := witnessRule 60 54 160 1260400 1260523 32 63120
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk64 := witnessRule 60 54 192 1260524 1260704 32 58569
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk65 := witnessRule 60 54 224 1260705 1260899 32 55943
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt60_chunk66 := witnessRule 60 54 256 1260900 1261027 12 20654
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk67 := witnessRule 60 53 0 1270000 1270068 32 75180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk68 := witnessRule 60 53 32 1270069 1270138 32 70320
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk69 := witnessRule 60 53 64 1270139 1270210 32 65100
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk70 := witnessRule 60 53 96 1270211 1270326 32 64443
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk71 := witnessRule 60 53 128 1270327 1270448 32 59175
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk72 := witnessRule 60 53 160 1270449 1270576 32 56742
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk73 := witnessRule 60 53 192 1270577 1270710 32 53557
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt60_chunk74 := witnessRule 60 53 224 1270711 1270964 32 51478
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt60_chunk75 := witnessRule 60 53 256 1271024 1271026 3 4960
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk76 := witnessRule 60 52 0 1280000 1280068 32 68466
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk77 := witnessRule 60 52 32 1280069 1280139 32 63849
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk78 := witnessRule 60 52 64 1280140 1280211 32 58890
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk79 := witnessRule 60 52 96 1280212 1280328 32 58373
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk80 := witnessRule 60 52 128 1280329 1280451 32 53885
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk81 := witnessRule 60 52 160 1280452 1280580 32 50991
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk82 := witnessRule 60 52 192 1280581 1280769 32 48797
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt60_chunk83 := witnessRule 60 52 224 1280770 1281026 27 40819
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt60_chunk84 := witnessRule 60 51 0 1290000 1290069 32 62510
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk85 := witnessRule 60 51 32 1290070 1290140 32 57081
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk86 := witnessRule 60 51 64 1290141 1290213 32 53009
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk87 := witnessRule 60 51 96 1290256 1290331 32 52760
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk88 := witnessRule 60 51 128 1290332 1290455 32 48607
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk89 := witnessRule 60 51 160 1290456 1290585 32 46246
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt60_chunk90 := witnessRule 60 51 192 1290586 1290775 32 44846
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt60_chunk91 := witnessRule 60 51 224 1290832 1291025 18 25769
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt60_chunk92 := witnessRule 60 50 0 1300000 1300069 32 56174
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk93 := witnessRule 60 50 32 1300070 1300141 32 51406
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk94 := witnessRule 60 50 64 1300142 1300257 32 48404
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk95 := witnessRule 60 50 96 1300258 1300333 32 46541
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk96 := witnessRule 60 50 128 1300334 1300458 32 44027
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk97 := witnessRule 60 50 160 1300459 1300641 32 42404
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt60_chunk98 := witnessRule 60 50 192 1300642 1300837 32 41571
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt60_chunk99 := witnessRule 60 50 224 1300896 1301025 10 13890
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk100 := witnessRule 60 49 0 1310000 1310070 32 50430
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk101 := witnessRule 60 49 32 1310071 1310142 32 45928
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk102 := witnessRule 60 49 64 1310143 1310259 32 43654
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk103 := witnessRule 60 49 96 1310260 1310336 32 41397
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk104 := witnessRule 60 49 128 1310337 1310462 32 40084
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt60_chunk105 := witnessRule 60 49 160 1310512 1310646 32 39120
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt60_chunk106 := witnessRule 60 49 192 1310647 1310962 32 39570
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt60_chunk107 := witnessRule 60 49 224 1311024 1311024 1 1378
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk108 := witnessRule 60 48 0 1320000 1320070 32 44830
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk109 := witnessRule 60 48 32 1320071 1320143 32 41262
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk110 := witnessRule 60 48 64 1320144 1320261 32 39359
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk111 := witnessRule 60 48 96 1320262 1320385 32 37431
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt60_chunk112 := witnessRule 60 48 128 1320386 1320515 32 36744
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt60_chunk113 := witnessRule 60 48 160 1320516 1320705 32 35685
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt60_chunk114 := witnessRule 60 48 192 1320706 1321024 25 29471
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk115 := witnessRule 60 47 0 1330000 1330071 32 40048
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk116 := witnessRule 60 47 32 1330072 1330144 32 36716
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk117 := witnessRule 60 47 64 1330145 1330263 32 35538
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk118 := witnessRule 60 47 96 1330264 1330388 32 34168
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt60_chunk119 := witnessRule 60 47 128 1330389 1330519 32 33281
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt60_chunk120 := witnessRule 60 47 160 1330520 1330711 32 33136
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt60_chunk121 := witnessRule 60 47 192 1330768 1330961 16 18199
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk122 := witnessRule 60 46 0 1340000 1340071 32 35609
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk123 := witnessRule 60 46 32 1340072 1340145 32 32757
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk124 := witnessRule 60 46 64 1340146 1340265 32 32318
  0xb6bfffff 0x5766336ee8c66e5c98cdd3a1a (by decide +kernel)
private def pack_E6970Receipt60_chunk125 := witnessRule 60 46 96 1340266 1340391 32 31056
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt60_chunk126 := witnessRule 60 46 128 1340392 1340523 32 30255
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt60_chunk127 := witnessRule 60 46 160 1340576 1340773 32 31518
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt60_chunk128 := witnessRule 60 46 192 1340832 1340960 8 8884
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk129 := witnessRule 60 45 0 1350000 1350072 32 31837
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk130 := witnessRule 60 45 32 1350073 1350146 32 29162
  0xffffdfff 0x6399a (by decide +kernel)
private def pack_E6970Receipt60_chunk131 := witnessRule 60 45 64 1350147 1350267 32 29335
  0x920edb69 0x37864368f0c66d5d990db3b319b77464370e6c662121c994dcb8b21884976342f6c66cde58cdabbb19b77563372e6c66e9c590ddb99883 (by decide +kernel)
private def pack_E6970Receipt60_chunk132 := witnessRule 60 45 96 1350268 1350394 32 28137
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt60_chunk133 := witnessRule 60 45 128 1350395 1350580 32 27993
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt60_chunk134 := witnessRule 60 45 160 1350581 1350960 32 30745
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk135 := witnessRule 60 44 0 1360000 1360072 32 28383
  0xfeffffff 0x638b19b (by decide +kernel)
private def pack_E6970Receipt60_chunk136 := witnessRule 60 44 32 1360073 1360147 32 26176
  0xedb68fff 0x17c63366f4c66d5e18cdbbb319b97463374e4c86edc58cc425ba9a (by decide +kernel)
private def pack_E6970Receipt60_chunk137 := witnessRule 60 44 64 1360192 1360269 32 26500
  0x80039240 0xbd329b27a64366f2c66210de194da3c321b577633108aecca6d9d590c4233a331b773653108ee4ce6e1c598c4243c1a17b64364f6c66cde590da3cb19b5776436ceec66ddd590dc3a31988487365372e4c862125c598dd3a9883 (by decide +kernel)
private def pack_E6970Receipt60_chunk138 := witnessRule 60 44 96 1360270 1360397 32 25599
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt60_chunk139 := witnessRule 60 44 128 1360448 1360584 32 26053
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt60_chunk140 := witnessRule 60 44 160 1360640 1360897 24 22118
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk141 := witnessRule 60 43 0 1370000 1370073 32 25634
  0xb43ffffa 0x77763372eac66e9cd90ddb9319884b7165378e8620f1c98cdeba1a (by decide +kernel)
private def pack_E6970Receipt60_chunk142 := witnessRule 60 43 32 1370074 1370193 32 23744
  0x3924076d 0x21c5a0dcbb988317c64364f8c66cde990da3d319b5786436cf0c66ddd990dc3ab1988487465372e6c862125c998dd38b29884a77342fac66cded8cdabcb19b (by decide +kernel)
private def pack_E6970Receipt60_chunk143 := witnessRule 60 43 64 1370194 1370271 32 23456
  0xf000f000 0x17a66364f4ca6cde590c421bc331b4776531088ecce6d5d598c422ba341b673673108ce4d26ddc5a0c423bd1a17b65364f6c86cde98cc421bcb29b4796436af0c662115dd94db3b3218846756636ee8ca6211dcd9cdc39331884 (by decide +kernel)
private def pack_E6970Receipt60_chunk144 := witnessRule 60 43 96 1370320 1370451 32 23672
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt60_chunk145 := witnessRule 60 43 128 1370452 1370644 32 24464
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt60_chunk146 := witnessRule 60 43 160 1370645 1370896 16 14246
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk147 := witnessRule 60 42 0 1380000 1380073 32 22957
  0x403b6da0 0xcf2c66dddd90dc3b31988487565372e8c862125cd98dd39329884a7167376ec620c5f98cd9be319b57a6336ef0c66e5d98cdd3a321bb736331096e4ca6f1c590c4263b1a (by decide +kernel)
private def pack_E6970Receipt60_chunk148 := witnessRule 60 42 32 1380074 1380194 32 21424
  0x1e000392 0xee4d06211dc5a8dc3c988317c65364f8c86cded8cc421bd329b47a6436af2c662115e194db3bb218846766636eeaca6211dd19cdc39b3188487268372e2ce62125e4d0beb21b27d63366f6c86d1ed8cdabcb21b (by decide +kernel)
private def pack_E6970Receipt60_chunk149 := witnessRule 60 42 64 1380195 1380321 32 21254
  0x3e003c00 0x8e2da6d5f0c418bd339b2796631084f0d06cddd9cc421bb349b4756831088e8d46d5cda4c422b9359b6716a3108cf8685ed98d93db29b37a6431086f2cc6d1e194c4223bb39b576663108aead06d9d19cc42339b49b (by decide +kernel)
private def pack_E6970Receipt60_chunk150 := witnessRule 60 42 96 1380322 1380454 32 21370
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt60_chunk151 := witnessRule 60 42 128 1380455 1380706 32 23617
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk152 := witnessRule 60 42 160 1380707 1380896 9 7836
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk153 := witnessRule 60 41 0 1390000 1390074 32 20566
  0x1c9200 0x15e98cc422bcb29b678643108ceecc6ddd994c423bab39b8746631090e6d06e5c99cc424b8b49ba7831062fcc86c9f98cd9be321b47c6336af4c86d9e98cdbbc321b8776331090ecca6e5d590c424ba331ba736531094e4ce6edc598c425bc1a (by decide +kernel)
private def pack_E6970Receipt60_chunk154 := witnessRule 60 41 32 1390075 1390196 32 19292
  0x78001e0 0x574693108ae6d66d9c9a8c42338b61b77b31062f8cc6c9f194d9bdb2188437a66368f2ca62111e19cdabbb318845766836ceace62119d1a4dbb9b418847726a370e2d262121ecd0beb29b27d64366f8c66210ded94da3db21b (by decide +kernel)
private def pack_E6970Receipt60_chunk155 := witnessRule 60 41 64 1390197 1390324 32 19153
  0x7e00f80 0x13a3618842736e366e4da6210dc5bcda3f18831786a364eed262109d9acd9bab518843746c368e6d662111c9b4dab8b6188457e342f6ce6c9e998c4213cb41b3786731086eed26d1d9a0c4223ab51b (by decide +kernel)
private def pack_E6970Receipt60_chunk156 := witnessRule 60 41 96 1390325 1390458 32 19609
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt60_chunk157 := witnessRule 60 41 128 1390512 1390832 32 23285
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk158 := witnessRule 60 41 160 1390833 1390833 1 861
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk159 := witnessRule 60 40 0 1400000 1400074 32 18308
  0x1e0000 0x47a6531088f2ce6d5e198c422bbb41b676673108cead26ddd1a0c423b9b51b8726931090e2d66e5e8c418bf329b27e64366fac66210df194da3e321b57b633108af4ca6d9e590c4233c331b777653108eecce6e1d598c4243a341b9736731092e4d26e9c5a0c4253d1a (by decide +kernel)
private def pack_E6970Receipt60_chunk160 := witnessRule 60 40 32 1400075 1400197 32 17266
  0x3e000f0 0x6ead86d1d1acc42239b69b5726c3108ae2dc6d9f4c418be339b27b6631084f4d06cde59cc421bc349b4776831088ecd46d5d5a4c422ba359b6736a3108ce4d86ddc5acc423be9a17d66364faca6cdf190c421bdb31b (by decide +kernel)
private def pack_E6970Receipt60_chunk161 := witnessRule 60 40 64 1400198 1400326 32 17223
  0xe1fe03f0 0x2e6c801b2726f31084e2c881b37400c418bb369b2756c31084e8dc6cdcdb4c421b9379b4716e31088e801a1796a364f0d262109ddacd9bb351884 (by decide +kernel)
private def pack_E6970Receipt60_chunk162 := witnessRule 60 40 96 1400327 1400515 32 18505
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt60_chunk163 := witnessRule 60 40 128 1400516 1400832 26 18154
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk164 := witnessRule 60 39 0 1410000 1410075 32 16212
  0xf0000 0x27b68366f4ce6210de5a4da3c3418844776a36aecd262115d5acdb3a3518846736c36ee4d66211dc5b4dc3e188317e66364fcca6cdf590c421be331b47b6531088f4ce6d5e598c422bc341b677673108cecd26ddd5a0c423ba351b8736931090e4d66e5c5a8c424be1a (by decide +kernel)
private def pack_E6970Receipt60_chunk165 := witnessRule 60 39 32 1410076 1410199 32 15439
  0xfc007c 0x2eeda6c9d9b0c4213ab71b3746d31086e6de6d1c9b8c42238b2006d5fcc418bd351b2796931084f0d66cddda8c421bb361b4756b31088e8da6d5cdb0c422b9371b6716d3108cfe685f59cd93e331884 (by decide +kernel)
private def pack_E6970Receipt60_chunk166 := witnessRule 60 39 64 1410200 1410329 32 15611
  0xff7fe0ff 0x17164c0d8ba32006c9cdbcc4213932206cdc590031086e901a (by decide +kernel)
private def pack_E6970Receipt60_chunk167 := witnessRule 60 39 96 1410330 1410519 32 17698
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk168 := witnessRule 60 39 128 1410576 1410832 19 12814
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk169 := witnessRule 60 38 0 1420000 1420075 32 14299
  0xf8000 0x2f6d46c9e9a4c4213cb59b3786a31086eed86d1d9acc4223ab69b5746c3108ae6dc6d9c9b4c42338b79b77e31062fcce6c9f598c4213e341b37b6731086f4d26d1e5a0c4223c351b577693108aecd66d9d5a8c4233a361b7736b3108ee4da6e1c5b0c4243f1a (by decide +kernel)
private def pack_E6970Receipt60_chunk170 := witnessRule 60 38 32 1420076 1420200 32 13738
  0xe07f803f 0xbab2006c9d1bcc42139b2206cdc990031086e2c901b47440c418bc369b2776c31084ecdc6cdd5b4c421ba379b4736e31088e4c801b5716f3108ae881a (by decide +kernel)
private def pack_E6970Receipt60_chunk171 := witnessRule 60 38 64 1420201 1420331 32 14378
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt60_chunk172 := witnessRule 60 38 96 1420384 1420579 32 17076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk173 := witnessRule 60 38 128 1420580 1420769 12 7744
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk174 := witnessRule 60 37 0 1430000 1430076 32 12504
  0xe007e000 0x2f2da6c9e1b0c4213bb71b3766d31086eade6d1d1b8c42239b2006d5c9bcc422b8b2206d9d0031062f8d46c9eda4c4213d359b3796a31086f0d86d1ddacc4223b369b5756c3108ae8dc6d9cdb4c42339379b7716e3108ee801a (by decide +kernel)
private def pack_E6970Receipt60_chunk175 := witnessRule 60 37 32 1430077 1430202 32 12322
  0xfe1ff01f 0x2e6c981b2726480c42138b2806cdd3031062ecc801b2756f31084e8c881b3736400c421b932406d1c591031088e981a (by decide +kernel)
private def pack_E6970Receipt60_chunk176 := witnessRule 60 37 64 1430203 1430386 32 13491
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt60_chunk177 := witnessRule 60 37 96 1430387 1430642 32 16566
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk178 := witnessRule 60 37 128 1430643 1430768 5 3151
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk179 := witnessRule 60 36 0 1440000 1440076 32 10950
  0xf807f800 0xbbb2006c9d9bcc4213ab2206cdd190031086e6c901b4726440c42238b2606d5d2031062f4da6c9e5b0c4213c371b3776d31086ecde6d1d5b8c4223a32006d5cdbcc422b932206d9c59003108ce901a (by decide +kernel)
private def pack_E6970Receipt60_chunk180 := witnessRule 60 36 32 1440077 1440203 32 11092
  0xffdffe0f 0x5c5960362e8c981b2736480c4213932806cdc593031086ea81a (by decide +kernel)
private def pack_E6970Receipt60_chunk181 := witnessRule 60 36 64 1440204 1440389 32 12692
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk182 := witnessRule 60 36 96 1440390 1440768 31 15636
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk183 := witnessRule 60 35 0 1450000 1450077 32 9569
  0xff03fe00 0x2eac981b2746480c42139b2806cdc993031086e2ca81b47500c418bc32006c9ddbcc4213b32206cdd590031086e8c901b4736440c4223932606d5c59203108aea01a (by decide +kernel)
private def pack_E6970Receipt60_chunk184 := witnessRule 60 35 32 1450078 1450205 32 10080
  0xffffffc7 0xb932c06c9c595031084eb81a (by decide +kernel)
private def pack_E6970Receipt60_chunk185 := witnessRule 60 35 64 1450256 1450392 32 12024
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk186 := witnessRule 60 35 96 1450448 1450705 24 11456
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk187 := witnessRule 60 34 0 1460000 1460077 32 8394
  0xffc3ff80 0xb9b2c06c9c995031084e2cb81b37580c418bb32606c9d592031084e8ca01b37364c0c421b932a06d1c594031088eb01a (by decide +kernel)
private def pack_E6970Receipt60_chunk188 := witnessRule 60 34 32 1460078 1460257 32 9244
  0xfffffffb 0x2ec81a (by decide +kernel)
private def pack_E6970Receipt60_chunk189 := witnessRule 60 34 64 1460258 1460450 32 11380
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk190 := witnessRule 60 34 96 1460451 1460704 18 8110
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk191 := witnessRule 60 33 0 1470000 1470078 32 7384
  0xfffbffe0 0x5c5990362e8cb01b2736540c4213932e06cdc596031086ec01a (by decide +kernel)
private def pack_E6970Receipt60_chunk192 := witnessRule 60 33 32 1470079 1470259 32 8561
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk193 := witnessRule 60 33 64 1470260 1470454 32 10804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk194 := witnessRule 60 33 96 1470512 1470704 12 5196
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk195 := witnessRule 60 32 0 1480000 1480078 32 6523
  0xfffffff8 0xb933206c9c598031084ed01a (by decide +kernel)
private def pack_E6970Receipt60_chunk196 := witnessRule 60 32 32 1480128 1480261 32 7926
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk197 := witnessRule 60 32 64 1480262 1480515 32 10298
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk198 := witnessRule 60 32 96 1480516 1480641 6 2466
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk199 := witnessRule 60 31 0 1490000 1490128 32 5834
  0xfffffffe 0x2ee01a (by decide +kernel)
private def pack_E6970Receipt60_chunk200 := witnessRule 60 31 32 1490129 1490263 32 7316
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk201 := witnessRule 60 31 64 1490264 1490640 32 9984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk202 := witnessRule 60 30 0 1500000 1500129 32 5222
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk203 := witnessRule 60 30 32 1500130 1500265 32 6710
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk204 := witnessRule 60 30 64 1500320 1500640 27 7836
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk205 := witnessRule 60 29 0 1510000 1510130 32 4695
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk206 := witnessRule 60 29 32 1510131 1510322 32 6212
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk207 := witnessRule 60 29 64 1510323 1510577 21 5603
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk208 := witnessRule 60 28 0 1520000 1520131 32 4180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk209 := witnessRule 60 28 32 1520132 1520324 32 5694
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk210 := witnessRule 60 28 64 1520325 1520576 16 3946
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk211 := witnessRule 60 27 0 1530000 1530132 32 3710
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk212 := witnessRule 60 27 32 1530133 1530384 32 5254
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk213 := witnessRule 60 27 64 1530385 1530576 11 2546
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk214 := witnessRule 60 26 0 1540000 1540133 32 3254
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk215 := witnessRule 60 26 32 1540134 1540387 32 4834
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk216 := witnessRule 60 26 64 1540388 1540513 6 1282
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk217 := witnessRule 60 25 0 1550000 1550134 32 2841
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk218 := witnessRule 60 25 32 1550135 1550450 32 4519
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk219 := witnessRule 60 25 64 1550512 1550512 1 210
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk220 := witnessRule 60 24 0 1560000 1560135 32 2444
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk221 := witnessRule 60 24 32 1560136 1560512 29 3686
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk222 := witnessRule 60 23 0 1570000 1570136 32 2088
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk223 := witnessRule 60 23 32 1570192 1570449 24 2672
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk224 := witnessRule 60 22 0 1580000 1580192 32 1762
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk225 := witnessRule 60 22 32 1580193 1580448 20 1930
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk226 := witnessRule 60 21 0 1590000 1590194 32 1484
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk227 := witnessRule 60 21 32 1590195 1590448 16 1348
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk228 := witnessRule 60 20 0 1600000 1600195 32 1212
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk229 := witnessRule 60 20 32 1600196 1600385 12 856
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk230 := witnessRule 60 19 0 1610000 1610197 32 984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk231 := witnessRule 60 19 32 1610256 1610384 8 496
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk232 := witnessRule 60 18 0 1620000 1620257 32 784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk233 := witnessRule 60 18 32 1620258 1620384 5 266
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk234 := witnessRule 60 17 0 1630000 1630320 32 629
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk235 := witnessRule 60 17 32 1630321 1630321 1 45
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk236 := witnessRule 60 16 0 1640000 1640320 30 418
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk237 := witnessRule 60 15 0 1650000 1650320 27 246
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk238 := witnessRule 60 14 0 1660000 1660257 24 116
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk239 := witnessRule 60 13 0 1670000 1670256 21 46
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk240 := witnessRule 60 12 0 1680000 1680256 19 16
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk241 := witnessRule 60 11 0 1690000 1690193 16 2
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk242 := witnessRule 60 10 0 1700000 1700192 14 0
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk243 := witnessRule 60 9 0 1710000 1710192 12 0
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk244 := witnessRule 60 8 0 1720000 1720129 10 0
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk245 := witnessRule 60 7 0 1730000 1730128 8 0
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk246 := witnessRule 60 6 0 1740000 1740128 7 0
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk247 := witnessRule 60 5 0 1750000 1750065 5 0
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk248 := witnessRule 60 4 0 1760000 1760064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk249 := witnessRule 60 3 0 1770000 1770064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk250 := witnessRule 60 2 0 1780000 1780001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk251 := witnessRule 60 1 0 1790000 1790000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt60_chunk252 := witnessRule 60 0 0 1800000 1800000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt60_chunks : List (Chunk 60) := [pack_E6970Receipt60_chunk0, pack_E6970Receipt60_chunk1, pack_E6970Receipt60_chunk2, pack_E6970Receipt60_chunk3, pack_E6970Receipt60_chunk4, pack_E6970Receipt60_chunk5, pack_E6970Receipt60_chunk6, pack_E6970Receipt60_chunk7, pack_E6970Receipt60_chunk8, pack_E6970Receipt60_chunk9, pack_E6970Receipt60_chunk10, pack_E6970Receipt60_chunk11, pack_E6970Receipt60_chunk12, pack_E6970Receipt60_chunk13, pack_E6970Receipt60_chunk14, pack_E6970Receipt60_chunk15, pack_E6970Receipt60_chunk16, pack_E6970Receipt60_chunk17, pack_E6970Receipt60_chunk18, pack_E6970Receipt60_chunk19, pack_E6970Receipt60_chunk20, pack_E6970Receipt60_chunk21, pack_E6970Receipt60_chunk22, pack_E6970Receipt60_chunk23, pack_E6970Receipt60_chunk24, pack_E6970Receipt60_chunk25, pack_E6970Receipt60_chunk26, pack_E6970Receipt60_chunk27, pack_E6970Receipt60_chunk28, pack_E6970Receipt60_chunk29, pack_E6970Receipt60_chunk30, pack_E6970Receipt60_chunk31, pack_E6970Receipt60_chunk32, pack_E6970Receipt60_chunk33, pack_E6970Receipt60_chunk34, pack_E6970Receipt60_chunk35, pack_E6970Receipt60_chunk36, pack_E6970Receipt60_chunk37, pack_E6970Receipt60_chunk38, pack_E6970Receipt60_chunk39, pack_E6970Receipt60_chunk40, pack_E6970Receipt60_chunk41, pack_E6970Receipt60_chunk42, pack_E6970Receipt60_chunk43, pack_E6970Receipt60_chunk44, pack_E6970Receipt60_chunk45, pack_E6970Receipt60_chunk46, pack_E6970Receipt60_chunk47, pack_E6970Receipt60_chunk48, pack_E6970Receipt60_chunk49, pack_E6970Receipt60_chunk50, pack_E6970Receipt60_chunk51, pack_E6970Receipt60_chunk52, pack_E6970Receipt60_chunk53, pack_E6970Receipt60_chunk54, pack_E6970Receipt60_chunk55, pack_E6970Receipt60_chunk56, pack_E6970Receipt60_chunk57, pack_E6970Receipt60_chunk58, pack_E6970Receipt60_chunk59, pack_E6970Receipt60_chunk60, pack_E6970Receipt60_chunk61, pack_E6970Receipt60_chunk62, pack_E6970Receipt60_chunk63, pack_E6970Receipt60_chunk64, pack_E6970Receipt60_chunk65, pack_E6970Receipt60_chunk66, pack_E6970Receipt60_chunk67, pack_E6970Receipt60_chunk68, pack_E6970Receipt60_chunk69, pack_E6970Receipt60_chunk70, pack_E6970Receipt60_chunk71, pack_E6970Receipt60_chunk72, pack_E6970Receipt60_chunk73, pack_E6970Receipt60_chunk74, pack_E6970Receipt60_chunk75, pack_E6970Receipt60_chunk76, pack_E6970Receipt60_chunk77, pack_E6970Receipt60_chunk78, pack_E6970Receipt60_chunk79, pack_E6970Receipt60_chunk80, pack_E6970Receipt60_chunk81, pack_E6970Receipt60_chunk82, pack_E6970Receipt60_chunk83, pack_E6970Receipt60_chunk84, pack_E6970Receipt60_chunk85, pack_E6970Receipt60_chunk86, pack_E6970Receipt60_chunk87, pack_E6970Receipt60_chunk88, pack_E6970Receipt60_chunk89, pack_E6970Receipt60_chunk90, pack_E6970Receipt60_chunk91, pack_E6970Receipt60_chunk92, pack_E6970Receipt60_chunk93, pack_E6970Receipt60_chunk94, pack_E6970Receipt60_chunk95, pack_E6970Receipt60_chunk96, pack_E6970Receipt60_chunk97, pack_E6970Receipt60_chunk98, pack_E6970Receipt60_chunk99, pack_E6970Receipt60_chunk100, pack_E6970Receipt60_chunk101, pack_E6970Receipt60_chunk102, pack_E6970Receipt60_chunk103, pack_E6970Receipt60_chunk104, pack_E6970Receipt60_chunk105, pack_E6970Receipt60_chunk106, pack_E6970Receipt60_chunk107, pack_E6970Receipt60_chunk108, pack_E6970Receipt60_chunk109, pack_E6970Receipt60_chunk110, pack_E6970Receipt60_chunk111, pack_E6970Receipt60_chunk112, pack_E6970Receipt60_chunk113, pack_E6970Receipt60_chunk114, pack_E6970Receipt60_chunk115, pack_E6970Receipt60_chunk116, pack_E6970Receipt60_chunk117, pack_E6970Receipt60_chunk118, pack_E6970Receipt60_chunk119, pack_E6970Receipt60_chunk120, pack_E6970Receipt60_chunk121, pack_E6970Receipt60_chunk122, pack_E6970Receipt60_chunk123, pack_E6970Receipt60_chunk124, pack_E6970Receipt60_chunk125, pack_E6970Receipt60_chunk126, pack_E6970Receipt60_chunk127, pack_E6970Receipt60_chunk128, pack_E6970Receipt60_chunk129, pack_E6970Receipt60_chunk130, pack_E6970Receipt60_chunk131, pack_E6970Receipt60_chunk132, pack_E6970Receipt60_chunk133, pack_E6970Receipt60_chunk134, pack_E6970Receipt60_chunk135, pack_E6970Receipt60_chunk136, pack_E6970Receipt60_chunk137, pack_E6970Receipt60_chunk138, pack_E6970Receipt60_chunk139, pack_E6970Receipt60_chunk140, pack_E6970Receipt60_chunk141, pack_E6970Receipt60_chunk142, pack_E6970Receipt60_chunk143, pack_E6970Receipt60_chunk144, pack_E6970Receipt60_chunk145, pack_E6970Receipt60_chunk146, pack_E6970Receipt60_chunk147, pack_E6970Receipt60_chunk148, pack_E6970Receipt60_chunk149, pack_E6970Receipt60_chunk150, pack_E6970Receipt60_chunk151, pack_E6970Receipt60_chunk152, pack_E6970Receipt60_chunk153, pack_E6970Receipt60_chunk154, pack_E6970Receipt60_chunk155, pack_E6970Receipt60_chunk156, pack_E6970Receipt60_chunk157, pack_E6970Receipt60_chunk158, pack_E6970Receipt60_chunk159, pack_E6970Receipt60_chunk160, pack_E6970Receipt60_chunk161, pack_E6970Receipt60_chunk162, pack_E6970Receipt60_chunk163, pack_E6970Receipt60_chunk164, pack_E6970Receipt60_chunk165, pack_E6970Receipt60_chunk166, pack_E6970Receipt60_chunk167, pack_E6970Receipt60_chunk168, pack_E6970Receipt60_chunk169, pack_E6970Receipt60_chunk170, pack_E6970Receipt60_chunk171, pack_E6970Receipt60_chunk172, pack_E6970Receipt60_chunk173, pack_E6970Receipt60_chunk174, pack_E6970Receipt60_chunk175, pack_E6970Receipt60_chunk176, pack_E6970Receipt60_chunk177, pack_E6970Receipt60_chunk178, pack_E6970Receipt60_chunk179, pack_E6970Receipt60_chunk180, pack_E6970Receipt60_chunk181, pack_E6970Receipt60_chunk182, pack_E6970Receipt60_chunk183, pack_E6970Receipt60_chunk184, pack_E6970Receipt60_chunk185, pack_E6970Receipt60_chunk186, pack_E6970Receipt60_chunk187, pack_E6970Receipt60_chunk188, pack_E6970Receipt60_chunk189, pack_E6970Receipt60_chunk190, pack_E6970Receipt60_chunk191, pack_E6970Receipt60_chunk192, pack_E6970Receipt60_chunk193, pack_E6970Receipt60_chunk194, pack_E6970Receipt60_chunk195, pack_E6970Receipt60_chunk196, pack_E6970Receipt60_chunk197, pack_E6970Receipt60_chunk198, pack_E6970Receipt60_chunk199, pack_E6970Receipt60_chunk200, pack_E6970Receipt60_chunk201, pack_E6970Receipt60_chunk202, pack_E6970Receipt60_chunk203, pack_E6970Receipt60_chunk204, pack_E6970Receipt60_chunk205, pack_E6970Receipt60_chunk206, pack_E6970Receipt60_chunk207, pack_E6970Receipt60_chunk208, pack_E6970Receipt60_chunk209, pack_E6970Receipt60_chunk210, pack_E6970Receipt60_chunk211, pack_E6970Receipt60_chunk212, pack_E6970Receipt60_chunk213, pack_E6970Receipt60_chunk214, pack_E6970Receipt60_chunk215, pack_E6970Receipt60_chunk216, pack_E6970Receipt60_chunk217, pack_E6970Receipt60_chunk218, pack_E6970Receipt60_chunk219, pack_E6970Receipt60_chunk220, pack_E6970Receipt60_chunk221, pack_E6970Receipt60_chunk222, pack_E6970Receipt60_chunk223, pack_E6970Receipt60_chunk224, pack_E6970Receipt60_chunk225, pack_E6970Receipt60_chunk226, pack_E6970Receipt60_chunk227, pack_E6970Receipt60_chunk228, pack_E6970Receipt60_chunk229, pack_E6970Receipt60_chunk230, pack_E6970Receipt60_chunk231, pack_E6970Receipt60_chunk232, pack_E6970Receipt60_chunk233, pack_E6970Receipt60_chunk234, pack_E6970Receipt60_chunk235, pack_E6970Receipt60_chunk236, pack_E6970Receipt60_chunk237, pack_E6970Receipt60_chunk238, pack_E6970Receipt60_chunk239, pack_E6970Receipt60_chunk240, pack_E6970Receipt60_chunk241, pack_E6970Receipt60_chunk242, pack_E6970Receipt60_chunk243, pack_E6970Receipt60_chunk244, pack_E6970Receipt60_chunk245, pack_E6970Receipt60_chunk246, pack_E6970Receipt60_chunk247, pack_E6970Receipt60_chunk248, pack_E6970Receipt60_chunk249, pack_E6970Receipt60_chunk250, pack_E6970Receipt60_chunk251, pack_E6970Receipt60_chunk252]
def rows60 := rowsFrom pack_E6970Receipt60_chunks
theorem good60 : ∀ r ∈ rows60, good 60 r = true := rowsFrom_good pack_E6970Receipt60_chunks
theorem sorted60 : rows60.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt60_chunks 0 (by decide +kernel)).1
theorem mass60 (i : Fin 61) :
    bandCount 60 (i.val : ℤ) 60 16 ≤ (rows60.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt60_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 60 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt60_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total60 : (rows60.map (price 60)).sum = 9542106 :=
  (total_eq pack_E6970Receipt60_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt60
