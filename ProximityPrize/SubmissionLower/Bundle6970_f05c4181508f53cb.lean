import ProximityPrize.SubmissionLower.E6970ReceiptBase

section Pack_E6970Receipt40

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt40_chunk0 := witnessA6966Final 40 60 0 600020 600153 32 3377
  0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk1 := witnessA6966Final 40 60 32 600154 600334 32 3351
  0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk2 := witnessA6966Final 40 60 64 600335 600463 32 3298
  0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk3 := witnessA6966Final 40 60 96 600464 600590 32 3267
  0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk4 := witnessA6966Final 40 60 128 600591 600717 32 3215
  0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk5 := witnessA6966Final 40 60 160 600768 600903 32 3094
  0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk6 := witnessA6966Final 40 60 192 600904 601030 17 1573
  0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk7 := witnessRule 40 59 0 610019 610151 32 3237
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk8 := witnessRule 40 59 32 610152 610331 32 3203
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk9 := witnessRule 40 59 64 610332 610459 32 3176
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk10 := witnessRule 40 59 96 610460 610585 32 3148
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk11 := witnessRule 40 59 128 610586 610713 32 3065
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk12 := witnessRule 40 59 160 610714 610900 32 2962
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk13 := witnessRule 40 59 192 610901 611029 18 1610
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk14 := witnessRule 40 58 0 620018 620149 32 3144
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk15 := witnessRule 40 58 32 620150 620279 32 3069
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk16 := witnessRule 40 58 64 620328 620454 32 3105
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk17 := witnessRule 40 58 96 620455 620579 32 3055
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk18 := witnessRule 40 58 128 620580 620708 32 2962
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk19 := witnessRule 40 58 160 620709 620897 32 2861
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk20 := witnessRule 40 58 192 620898 621029 20 1739
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk21 := witnessRule 40 57 0 630017 630147 32 3079
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk22 := witnessRule 40 57 32 630148 630276 32 3003
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk23 := witnessRule 40 57 64 630277 630403 32 2984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk24 := witnessRule 40 57 96 630451 630528 32 2974
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk25 := witnessRule 40 57 128 630576 630705 32 2887
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk26 := witnessRule 40 57 160 630706 630841 32 2765
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk27 := witnessRule 40 57 192 630896 631028 20 1696
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk28 := witnessRule 40 56 0 640016 640145 32 3025
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk29 := witnessRule 40 56 32 640146 640273 32 2943
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk30 := witnessRule 40 56 64 640274 640399 32 2925
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk31 := witnessRule 40 56 96 640400 640523 32 2912
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk32 := witnessRule 40 56 128 640524 640651 32 2767
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk33 := witnessRule 40 56 160 640652 640838 32 2684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk34 := witnessRule 40 56 192 640839 641028 21 1729
  0x1fffbf 0xb99a (by decide +kernel)
private def pack_E6970Receipt40_chunk35 := witnessRule 40 55 0 650015 650143 32 2981
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk36 := witnessRule 40 55 32 650144 650270 32 2889
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk37 := witnessRule 40 55 64 650271 650395 32 2870
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk38 := witnessRule 40 55 96 650396 650519 32 2824
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk39 := witnessRule 40 55 128 650520 650648 32 2672
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk40 := witnessRule 40 55 160 650649 650837 32 2598
  0x7fffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt40_chunk41 := witnessRule 40 55 192 650838 651027 20 1602
  0xfffbf 0xba1a (by decide +kernel)
private def pack_E6970Receipt40_chunk42 := witnessRule 40 54 0 660014 660141 32 2939
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk43 := witnessRule 40 54 32 660142 660267 32 2851
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk44 := witnessRule 40 54 64 660268 660391 32 2821
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk45 := witnessRule 40 54 96 660392 660515 32 2745
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk46 := witnessRule 40 54 128 660516 660645 32 2587
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk47 := witnessRule 40 54 160 660646 660835 32 2522
  0x7edfffff 0x4e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt40_chunk48 := witnessRule 40 54 192 660836 661027 20 1562
  0xfffbe 0x5d4d0b8b21b (by decide +kernel)
private def pack_E6970Receipt40_chunk49 := witnessRule 40 53 0 670013 670139 32 2895
  0xffaffd7f 0x3716336ae2889c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt40_chunk50 := witnessRule 40 53 32 670140 670264 32 2812
  0xffffffe7 0x11ccd2b8a2 (by decide +kernel)
private def pack_E6970Receipt40_chunk51 := witnessRule 40 53 64 670265 670387 32 2763
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk52 := witnessRule 40 53 96 670388 670512 32 2656
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk53 := witnessRule 40 53 128 670513 670643 32 2526
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk54 := witnessRule 40 53 160 670644 670835 32 2451
  0x3e5f6fff 0x2e2ca6c9c590d8b9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt40_chunk55 := witnessRule 40 53 192 670836 671026 18 1373
  0x3ffdf 0xbb1a (by decide +kernel)
private def pack_E6970Receipt40_chunk56 := witnessRule 40 52 0 680012 680137 32 2847
  0xeabfabff 0xac6685cd90d938b29b5715106cc2a9190d0b9329b (by decide +kernel)
private def pack_E6970Receipt40_chunk57 := witnessRule 40 52 32 680138 680261 32 2764
  0xfd5ffabf 0x9cd8cd9b8b21b57141362e8c66c9c990d9ba9a (by decide +kernel)
private def pack_E6970Receipt40_chunk58 := witnessRule 40 52 64 680262 680338 32 2676
  0xfebffebf 0x4716336ce288dc98cda3a1a (by decide +kernel)
private def pack_E6970Receipt40_chunk59 := witnessRule 40 52 96 680384 680461 32 2660
  0xfffffe7f 0x15ccd338a2 (by decide +kernel)
private def pack_E6970Receipt40_chunk60 := witnessRule 40 52 128 680462 680641 32 2454
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk61 := witnessRule 40 52 160 680642 680834 32 2384
  0x3e1e4fb6 0xb8b31b27165362e4ca6c9c990d9b8b19884375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt40_chunk62 := witnessRule 40 52 192 680835 681026 17 1269
  0x1ffef 0xbb9a (by decide +kernel)
private def pack_E6970Receipt40_chunk63 := witnessRule 40 51 0 690011 690135 32 2787
  0xd43fd07f 0x56152364e8c2a210dc98544c429b8b0a99c471523108ae2a28c5d585442139b0a898852726153386e2c2a46214dc550dab92a (by decide +kernel)
private def pack_E6970Receipt40_chunk64 := witnessRule 40 51 32 690136 690213 32 2692
  0x557fea3f 0x1d8552b21a17365368e4c2a2115c544c422329a3736151088e2c2a262151c54cdab922 (by decide +kernel)
private def pack_E6970Receipt40_chunk65 := witnessRule 40 51 64 690259 690335 32 2719
  0x54ff557f 0x5d58cd939b21b3716536ce2a20d9c493319a17464364e4ca6d5c58544233892 (by decide +kernel)
private def pack_E6970Receipt40_chunk66 := witnessRule 40 51 96 690336 690459 32 2561
  0xd5ff57ff 0xdcd8cda38b21b67141364e8c66cdc990da3a9a (by decide +kernel)
private def pack_E6970Receipt40_chunk67 := witnessRule 40 51 128 690460 690640 32 2373
  0xf6dffaff 0xbab19b3736336ae2c66d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt40_chunk68 := witnessRule 40 51 160 690641 690835 32 2317
  0xdf0f0792 0x2e2ce6c5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt40_chunk69 := witnessRule 40 51 192 690836 691025 14 1026
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk70 := witnessRule 40 50 0 700010 700087 32 2719
  0xff02ff 0xcc2a262115854cd8ba30a918851736154386e6c4ac9c58554e238b1289c5725106cc4a958548c42230aa1b27462562e4c2aa70dc98944e239291b (by decide +kernel)
private def pack_E6970Receipt40_chunk71 := witnessRule 40 50 32 700134 700210 32 2705
  0x81fe80ff 0x9d18544c42939b0a99c3726152310a6e2c2a8715c5895ab8a8a09c76151062eac2a262145d1854ce139b0a918852726154388e4c4acdc554dab9289b (by decide +kernel)
private def pack_E6970Receipt40_chunk72 := witnessRule 40 50 64 700211 700331 32 2689
  0xffa83fe 0x4726151310a8e2c2a6715c548c42338a8a366152364eac2a210dcd8544c429b930a99c4716152310a8e2a86d9c950bb30a884 (by decide +kernel)
private def pack_E6970Receipt40_chunk73 := witnessRule 40 50 96 700332 700456 32 2469
  0xafaa8ff5 0xae4c2a2119c544c42430aa664342e8ca6d1cd854422b8b0a898855715336ce489594d1ba30a884 (by decide +kernel)
private def pack_E6970Receipt40_chunk74 := witnessRule 40 50 128 700457 700587 32 2302
  0xe41e8aea 0x17564364eac66cdcd90da393198844716536ae8620d9c508d8bb319b27464366e6c66210dc994db38b0a88477124ec6685d590d939b29b (by decide +kernel)
private def pack_E6970Receipt40_chunk75 := witnessRule 40 50 160 700640 700835 32 2256
  0xff8f0780 0x2e4ce6c9c598c4213c1a17366364e6ca6cdc990c421b8b31b47531062e8ca6c9d190d9b9b1988437265368e4c86d5c58cc422ba9a (by decide +kernel)
private def pack_E6970Receipt40_chunk76 := witnessRule 40 50 192 700836 701025 12 865
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk77 := witnessRule 40 49 0 710009 710086 32 2691
  0x7ff03ff 0xac4a46c5d58944e13a3128842736252386e4c4a2621598944d8bab128841746252384e6c4a262149c9894ce1b8b1291885 (by decide +kernel)
private def pack_E6970Receipt40_chunk78 := witnessRule 40 49 32 710087 710208 32 2677
  0x2ffc0ffe 0x5cd8554e1b9b1289c471625238cc4a26c5d9895a30aa9b2746251386e6c4a210dc98948e3b12a (by decide +kernel)
private def pack_E6970Receipt40_chunk79 := witnessRule 40 49 64 710209 710329 32 2618
  0x3fc05ff0 0x15c58944e3392883761513108cc2a66c5d58548c428ba30aa1c37462564e4c2aa711c98944e2b9291b76254cc2a4621158550d93ab12b (by decide +kernel)
private def pack_E6970Receipt40_chunk80 := witnessRule 40 49 96 710330 710455 32 2385
  0xfa03f40 0x8e4c2a462151c58550e338b12b6715141382eec2a2109d58544c4293a30a99c3736152310a6e4c2a8715c9895a38aa9b67251370c2a20c5d98544c428bab0a99c2746152310a4e6c2a8711cd8959b8b0aa9c (by decide +kernel)
private def pack_E6970Receipt40_chunk81 := witnessRule 40 49 128 710456 710587 32 2233
  0xe00841d4 0x5d98cc420bab29b2746431084e6cc6cdc994c421b8b39b571615338ce2a46211dc853b19883665342eac862105d198da39b0a89885472615338ae2c2a462155c550dbb8a88b76152364ecc2a210dd18544c429b9b0a99c (by decide +kernel)
private def pack_E6970Receipt40_chunk82 := witnessRule 40 49 160 710640 710837 32 2202
  0xfff7c3c0 0x2f4685cd9cd93933188427168366ee620c5d198d93a329b3736431086e4cc6d1c594c4223b9a (by decide +kernel)
private def pack_E6970Receipt40_chunk83 := witnessRule 40 49 192 710896 711024 8 567
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk84 := witnessRule 40 48 0 720008 720084 32 2665
  0x3fe05ff 0xba312918851736254386e6c6ac9c58954e238b1a89c5735106cc6a958948c422312a1b27463562e4c4aa70dc98d44e239a91b (by decide +kernel)
private def pack_E6970Receipt40_chunk85 := witnessRule 40 48 32 720085 720205 32 2651
  0x1ff007fc 0xdc58950e2b8b1ab572514138ec4a20d98948d8bab12898851746253384e6c4a462149c98950e23931ab3725536ae6a26d98944c422b1299b (by decide +kernel)
private def pack_E6970Receipt40_chunk86 := witnessRule 40 48 64 720206 720326 32 2551
  0xfe007fc0 0x86254cc4a46c5d98944e13ab128842746252386e6c4a26214dc9894ce238b12918854725436ce6a9d8944d8bb3128841756252384e8c4a262149cd894ce1b931291885 (by decide +kernel)
private def pack_E6970Receipt40_chunk87 := witnessRule 40 48 96 720327 720453 32 2304
  0x1c007c00 0x571625238ce4a26211dc5449c312a761523108cc2a86c9d98958ba30aa9c3746251388e6c4a2111c98948e2b8b12898855725336ce2a48dd8944d8bbb12b56155364eac4a270dd1894421b9b1291c4726251310a8e2c4a6715c948c4233928a3 (by decide +kernel)
private def pack_E6970Receipt40_chunk88 := witnessRule 40 48 128 720454 720586 32 2169
  0xc0180300 0x1994c41ab39a1746631082e6d06cdcd8550e23930a99885471615538ae2a862119c508c46330aa1b1766153384eac2a462149d18550e1b9b0a998853726155388e2c2a862151c558db39291b861513108ec2a66c5d98548c428bab0aa1c2746153310a4e6c2aa711cd8944e2b9312884 (by decide +kernel)
private def pack_E6970Receipt40_chunk89 := witnessRule 40 48 160 720640 720897 32 2154
  0xfffff7e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a (by decide +kernel)
private def pack_E6970Receipt40_chunk90 := witnessRule 40 48 192 720898 721024 5 350
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk91 := witnessRule 40 47 0 730007 730083 32 2641
  0x1ffe07ff 0x13a31a8842736352386e4c6a2621598d44d8bab1a8841746352384e6c6a262149c98d4ce1b8b1a91885 (by decide +kernel)
private def pack_E6970Receipt40_chunk92 := witnessRule 40 47 32 730084 730203 32 2625
  0xffe07ff8 0x331a89b17663568c4aa6c9d18d44e1b9b1a884372635238ec6a958d48d8bab1a89c (by decide +kernel)
private def pack_E6970Receipt40_chunk93 := witnessRule 40 47 64 730204 730325 32 2445
  0xfc05ff02 0xec4a262119894cd8bab12918851746254386e8c6ac9c98954e23931a89c5735236ec6a998948c422b12a1b27563562e6c4aa70dcd8d44e238b1a91c (by decide +kernel)
private def pack_E6970Receipt40_chunk94 := witnessRule 40 47 96 730326 730453 32 2225
  0x1c00f801 0x8e2c4a8715c94cc4233928a09c86251362eec4a2105d98948e13ab12898852746253386e6c4a46214dc98950e2b931ab4725536ce6a26e189441bb1291b1766251310a2eac4a6709d18948c42939b12a1c47363566e2c4aa715c58d44e339a883 (by decide +kernel)
private def pack_E6970Receipt40_chunk95 := witnessRule 40 47 128 730454 730640 32 2104
  0x70080180 0x9ecd2b0ab1b1756155384e8c2a862149cd8558e1b930aa98853716157388e2ac6210611c510e3b0a9988466155362eac2a862145d18558e139b0aa98852726157388e4c4a6715c58948c42ab92a1b7715216ec4a46d98550c422b0ab1b2756252386e8c4a26214dcd894ce23931291885 (by decide +kernel)
private def pack_E6970Receipt40_chunk96 := witnessRule 40 47 160 730641 730961 32 2118
  0xfffffffc 0x5c9a8d938b49884 (by decide +kernel)
private def pack_E6970Receipt40_chunk97 := witnessRule 40 46 0 740006 740081 32 2617
  0x1ffc0bff 0xdcd915938b1aa9c471645138cc8a958d48c42231aa1b27464562e4c6aa70dc99144e23a291b (by decide +kernel)
private def pack_E6970Receipt40_chunk98 := witnessRule 40 46 32 740082 740200 32 2598
  0xff807ff0 0x7635106cc6a46c5d58d44c428ba31a99c2736352310a4e4c6a8711c99159b9aa9b663513108ac6a66c5d18d48c428b9b1aa1c (by decide +kernel)
private def pack_E6970Receipt40_chunk99 := witnessRule 40 46 64 740201 740323 32 2340
  0xf00ffc07 0x10c6a998d48d8bb31a89c2756351084e8c6a470dcd8d44c429b931a99c4716352310aec6a26c5d98d4420bab1a91c2746351310a4e6c6a670dc98d48c429b8b1aa1c (by decide +kernel)
private def pack_E6970Receipt40_chunk100 := witnessRule 40 46 96 740324 740452 32 2159
  0x3807f01f 0x2b8b1a91c6735131090c4a40dd8948c423312a1b1756253310a2e8c4aa70dd18d44e239b1a884472635238ec6a26c5dd8d5ab12a9b2756351386e8c6a210dcd8d48e23931a89885 (by decide +kernel)
private def pack_E6970Receipt40_chunk101 := witnessRule 40 46 128 740453 740641 32 2042
  0xb08c0100 0xbe9a661553108ac2ae6c5d18558c428b9b0ac1c271615938504e2ca70a0dd0c423312a1b5615631088c2b06c9d18950e1b9b12998853726255388e2c4a862151c958d8c2b8a9188d762513208ec4a66c5d98948c428bab12a1c2746253310a4e6c4aa70dc98950c429b8b12b1c (by decide +kernel)
private def pack_E6970Receipt40_chunk102 := witnessRule 40 46 160 740642 740960 28 1817
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk103 := witnessRule 40 45 0 750005 750080 32 2597
  0x7ffc0fff 0x6e4c8a2621599144d8bab228841746452384e6c8a262149c9914ce1b8b2291885 (by decide +kernel)
private def pack_E6970Receipt40_chunk104 := witnessRule 40 45 32 750081 750199 32 2522
  0xff03ffe0 0xcc8a26c5d9915a31aa9b2746451386e6c8a210dc99148e3b22a56452362eac8a2709d191442139b2291c (by decide +kernel)
private def pack_E6970Receipt40_chunk105 := witnessRule 40 45 64 750200 750323 32 2256
  0xf017f817 0xec6a2621198d4cd8bab1a918851746354386e8c8ac9c98d54e23932289c5745236ec8a998d48c422b1aa1b27564562e6c6aa70dcd9144e238b2291c (by decide +kernel)
private def pack_E6970Receipt40_chunk106 := witnessRule 40 45 96 750324 750453 32 2077
  0x3c04f003 0x23931a91885471635438ec6a2621198d4cd8bb31a91c2756351310a4e8c6a670dcd8d48c429b931aa1c4735536ce8a26e18d441bb1a91b1766351310a2eac6a6709d18d48c42939b1aa1c47364566e2c6aa715c59144e33a2883 (by decide +kernel)
private def pack_E6970Receipt40_chunk107 := witnessRule 40 45 128 750454 750643 32 1980
  0xfeb604c0 0x2b0ab19043615a36502e2ce719894cc823312a9b1756254310a2e8c4ac709cd8954c42939312b9c3725836506e2a871d8948c823312a188456256362e8c4aa62145cd895ce1b9b1a99c (by decide +kernel)
private def pack_E6970Receipt40_chunk108 := witnessRule 40 45 160 750644 750960 23 1470
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk109 := witnessRule 40 44 0 760004 760078 32 2576
  0x7ff817ff 0x471655138ccaa959148c422322a1b27465562e4c8aa70dc99544e23aa91b (by decide +kernel)
private def pack_E6970Receipt40_chunk110 := witnessRule 40 44 32 760079 760197 32 2443
  0xfc03ffc0 0x1d91441b32291b1756451310a2e8c8a6709cd9148c42939322a1c47265566e8aa6d99144c422b2299b1746452310a2e6c8a870dcd955938b22a9c (by decide +kernel)
private def pack_E6970Receipt40_chunk111 := witnessRule 40 44 64 760198 760322 32 2176
  0xe01ff01f 0x10c8a999148d8bb32289c2756451084e8c8a470dcd9144c429b932299c4716452310aec8a26c5d9914420bab2291c2746451310a4e6c8a670dc99148c429b8b22a1c (by decide +kernel)
private def pack_E6970Receipt40_chunk112 := witnessRule 40 44 96 760323 760453 32 2010
  0x3c02f01f 0xdc98d50c429b8b1ab1c7635306ec6a4621198d50d8bab1a998851746355384e6c6a862149c98d58e23932291c5745336ec8a26d98d4cc422b1aa9b2756451386e8c8a210dcd9148e23932289885 (by decide +kernel)
private def pack_E6970Receipt40_chunk113 := witnessRule 40 44 128 760454 760645 32 1928
  0xffff8140 0x3312a19045625631088c4b06c5cd895cc428b9312c9c2817261553a504e2ac71d8944d02331a9988456355362eac6a8709d18d4cc42939b1aa9c (by decide +kernel)
private def pack_E6970Receipt40_chunk114 := witnessRule 40 44 160 760646 760897 18 1132
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk115 := witnessRule 40 43 0 770003 770077 32 2559
  0xfff81fff 0x199544d8bab2a8841746552384e6caa262149c9954ce1b8b2a91885 (by decide +kernel)
private def pack_E6970Receipt40_chunk116 := witnessRule 40 43 32 770078 770197 32 2336
  0xfc0fff81 0x66551362eccaad19154d93a32a89c3736551086e4caa471d9552b2a91b1756551384e8caa2109cd9548e1b932a89885 (by decide +kernel)
private def pack_E6970Receipt40_chunk117 := witnessRule 40 43 64 770198 770323 32 2092
  0xf017f02f 0xec8a262119914cd8bab22918851746454386e8caac9c99154e23932a89c5755236ecaa999148c422b22a1b27565562e6c8aa70dcd9544e238b2a91c (by decide +kernel)
private def pack_E6970Receipt40_chunk118 := witnessRule 40 43 96 770324 770455 32 1923
  0x700f813 0xba31aa98851736357384e4c6ac62149c58d60e14138b12a1d763513308cc8a66d58d54c42231ab9b2746453386e6c8a46214dc99150e238b22998857645206ec8a46c5d99144c428bab2299c2746452310a4e6c8a870dc59154e2b8b2a89c (by decide +kernel)
private def pack_E6970Receipt40_chunk119 := witnessRule 40 43 128 770456 770705 32 1890
  0xffffe038 0x19894cd022b12a99844625732086c4b26210a0d8554c4294130ab9c281716156310ccc6a4661198d50c422b1ab1b (by decide +kernel)
private def pack_E6970Receipt40_chunk120 := witnessRule 40 43 160 770706 770896 12 745
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk121 := witnessRule 40 42 0 780002 780075 32 2541
  0xfff02fff 0xccca959548c42232aa1b27466562e4caaa70dc99944e23b291b (by decide +kernel)
private def pack_E6970Receipt40_chunk122 := witnessRule 40 42 32 780076 780196 32 2226
  0xf807ff01 0xecaa20d99548d8bab2a898851746553384e6caa462149c99550e239332b3755536ccaa262115954cd8ba32a918851736554386e6ccac9c59554e238b3289c (by decide +kernel)
private def pack_E6970Receipt40_chunk123 := witnessRule 40 42 64 780197 780323 32 2013
  0xf00ff01f 0xecaa20d99548d8bb32a89c2756551084e8caa470dcd9544c429b932a99c4716552310aecaa26c5d9954420bab2a91c2746551310a4e6caa670dc99548c429b8b2aa1c (by decide +kernel)
private def pack_E6970Receipt40_chunk124 := witnessRule 40 42 96 780324 780456 32 1851
  0x180bc03 0xac6aa641118d5cc421b1ac9b283625538502e4c4a86218a05c58958e941392a98857635506cc8a4641199150d8bab22998851746455384e6c8a862149c99158e1ba2b9b764513208cc8a6621159154d8ba322a18851736456386e6caa4711c99544c42a38b2a99c (by decide +kernel)
private def pack_E6970Receipt40_chunk125 := witnessRule 40 42 128 780457 780708 32 1861
  0xfffffd54 0x158950d421b12c19842826156320a502b46d98d44d42331a99984 (by decide +kernel)
private def pack_E6970Receipt40_chunk126 := witnessRule 40 42 160 780768 780896 7 431
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk127 := witnessRule 40 41 0 790001 790075 32 2471
  0xfff03fff 0x199944d8bab328841746652384e6cca262149c9994ce1b8b3291885 (by decide +kernel)
private def pack_E6970Receipt40_chunk128 := witnessRule 40 41 32 790076 790197 32 2140
  0xfc0fff03 0x66651362ecccad19554d93a33289c3736651086e4cca471d9952b3291b1756651384e8cca2109cd9948e1b933289885 (by decide +kernel)
private def pack_E6970Receipt40_chunk129 := witnessRule 40 41 64 790198 790325 32 1914
  0xbc05f817 0x1847451423aecaa262119954cd8bab2a918851746554384e6caa662149c99554e23933289c5765236ecca999548c422b2aa1b27566562e6caaa70dcd9944e238b3291c (by decide +kernel)
private def pack_E6970Receipt40_chunk130 := witnessRule 40 41 96 790326 790512 32 1784
  0xc0100700 0x198d48d422b1aa1a044635633086c6b06410a0d8950c82941312b1885281625838502e4ae6214e05c54514eb32289a04664533208ac8aa62111915cd8b9b22b1885172645838502e4c6a874a09c58d4cc4314139aa9c7645406ccaa4621159550d8bab2a99c2746552310a4e6caa870dc9954cc429b8b2aa9c (by decide +kernel)
private def pack_E6970Receipt40_chunk131 := witnessRule 40 41 128 790513 790833 32 1849
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk132 := witnessRule 40 40 0 800000 800074 32 2405
  0xffe05fff 0xccea959948c422332a1b27467562e4ccaa70dc99d44e23ba91b (by decide +kernel)
private def pack_E6970Receipt40_chunk133 := witnessRule 40 40 32 800075 800197 32 2046
  0xfc03ff01 0xecca20d99948d8bab32898851746653384e6cca462149c99950e23933ab3765536ccca262115994cd8ba332918851736654386e6ceac9c59954e238b3a89c (by decide +kernel)
private def pack_E6970Receipt40_chunk134 := witnessRule 40 40 64 800198 800326 32 1829
  0x3e01fc07 0x138b2ab9c2827164533aecaa60d99948dab2aa188446556364e8cca470dcd9944c429b933299c4716652310aecca26c5d9994420bab3291c2746651310a4e6cca670dc99948c429b8b32a1c (by decide +kernel)
private def pack_E6970Receipt40_chunk135 := witnessRule 40 40 96 800327 800515 32 1733
  0xfa0601c0 0x2b1a99b04363573408506c4a66814a098954cc2940b12b9905282593108902aa621199148d022b22a19844645632086c8b06210a0d8d50c4294131ab1c281716355310c502e6ae7199544cc2332a9988456555362e8caa862145cd9558e13932aa9885 (by decide +kernel)
private def pack_E6970Receipt40_chunk136 := witnessRule 40 40 128 800516 800832 26 1478
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk137 := witnessRule 40 39 0 810000 810075 32 2287
  0xfff03fff 0x199d44d8bab3a8841746752384e6cea262149c99d4ce1b8b3a91885 (by decide +kernel)
private def pack_E6970Receipt40_chunk138 := witnessRule 40 39 32 810076 810199 32 1951
  0xff03ff81 0x66751362eccead19954d93a33a89c3736751086e4cea471d9d52b3a91b1756751384e8cea2109cd9d48e1b933a89885 (by decide +kernel)
private def pack_E6970Receipt40_chunk139 := witnessRule 40 39 64 810200 810329 32 1741
  0x1c0bf02 0x232ab18843655836506c8a870a05c9914cc43140b8b22a9d2827454310a506e6a284623999944c82333299b1756652310a2e8cca8709cd994cc42939332a9c3765636ecca40d99948c422b32a1b1746653310a2e6ccaa70dcd9d44e238b3a91c (by decide +kernel)
private def pack_E6970Receipt40_chunk140 := witnessRule 40 39 96 810330 810519 32 1697
  0xffeaa81c 0x1b1ab1b042826254350a504b0661120514c462b2299a84364573308506c6a66614a098d54c82940b1ab98852835936904aa6d99548cc22b2aa1904 (by decide +kernel)
private def pack_E6970Receipt40_chunk141 := witnessRule 40 39 128 810576 810832 19 1068
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk142 := witnessRule 40 38 0 820000 820075 32 2172
  0x7ff02fff 0x471685138cd0a959d48c42233aa1b27468562e4ceaa70dc9a144e23c291b (by decide +kernel)
private def pack_E6970Receipt40_chunk143 := witnessRule 40 38 32 820076 820200 32 1857
  0x7f807fc0 0x6e2cea871d9d441b33a91b1756751310a2e8cea6709cd9d48c4293933aa1c47268566eeaa6d99d44c422b3a99b1746752310a2e6cea870dcda15938b3aa9c (by decide +kernel)
private def pack_E6970Receipt40_chunk144 := witnessRule 40 38 64 820201 820331 32 1668
  0x7017c0 0xccaa26a115954cd02232aa9984365573208506c8a66414a099154c42940b22b9c2817456310a702e6a28875999501b332919045665431088ccac6c5cd9954c428b9332b9c2817265533a504eaa87199d44c422b3a99b1756752384e8cea262149cd9d4ce1b933a91885 (by decide +kernel)
private def pack_E6970Receipt40_chunk145 := witnessRule 40 38 96 820384 820579 32 1674
  0xfffffd43 0x159148dc21b22b1a842826354340a502c6ac6614a0d60c822412a1904 (by decide +kernel)
private def pack_E6970Receipt40_chunk146 := witnessRule 40 38 128 820580 820769 12 665
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk147 := witnessRule 40 37 0 830000 830076 32 2065
  0x7ff81fff 0x6e4d0a262159a144d8bab428841746852384e6d0a262149c9a14ce1b8b4291885 (by decide +kernel)
private def pack_E6970Receipt40_chunk148 := witnessRule 40 37 32 830077 830202 32 1762
  0xfe07fe0 0x2e6ceaa709c99d50c42938b3ab1c2827166523acd0a26d59d4cc42233aa9b2746851386e6d0a210dc9a148e3b42a56852362ead0a2709d1a1442139b4291c (by decide +kernel)
private def pack_E6970Receipt40_chunk149 := witnessRule 40 37 64 830203 830386 32 1612
  0x350601f0 0x241299a04481514431110cacaa46c10d9558d02141322a19852816456320a508b0621120d50c421c13928a1190e666513408acca6661119954c821b32b98842836553310a504caaa70a05c59550c43140baab1c6675306ccea4621159d50d8ba33a99885 (by decide +kernel)
private def pack_E6970Receipt40_chunk150 := witnessRule 40 37 96 830387 830642 32 1653
  0xfffffffa 0xa098d4cd82941ab9a04 (by decide +kernel)
private def pack_E6970Receipt40_chunk151 := witnessRule 40 37 128 830643 830768 5 275
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk152 := witnessRule 40 36 0 840000 840076 32 1957
  0x1ff817ff 0xdcda55938b42a9c471695138cd2a95a148c422342a1b27469562e4d0aa70dc9a544e23ca91b (by decide +kernel)
private def pack_E6970Receipt40_chunk153 := witnessRule 40 36 32 840077 840203 32 1673
  0x3f02ff0 0x233aa98843675736506cca670a05c99948c43140b8b32a1d2827653310acd0a40d9a148d8bab42898851746853384e6d0a462149c9a150e1bc2a9b668513108ad0a66c5d1a148c428b9b42a1c (by decide +kernel)
private def pack_E6970Receipt40_chunk154 := witnessRule 40 36 64 840204 840389 32 1564
  0xd7d1f43c 0x141ab1b04481514331130c504c8a66a14a115ccc2241a999844825144311a6ccac6610a099550c82940b2ab18852855836908a86d99d44cc22b3a99904 (by decide +kernel)
private def pack_E6970Receipt40_chunk155 := witnessRule 40 36 96 840390 840768 31 1588
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk156 := witnessRule 40 35 0 850000 850077 32 1853
  0x1ffc0fff 0x13a34a8842736952386e4d2a262159a544d8bab4a8841746952384e6d2a262149c9a54ce1b8b4a91885 (by decide +kernel)
private def pack_E6970Receipt40_chunk157 := witnessRule 40 35 32 850078 850205 32 1590
  0x817c0bf8 0x2b3a91a044675433086ceac6410a0d9948c82941332a1885281665638702eaa286759a144c822b429988446855362e6d0a862145c9a158e140b933a91d282775338cd2a20d5a548d8bab4a89c (by decide +kernel)
private def pack_E6970Receipt40_chunk158 := witnessRule 40 35 64 850256 850392 32 1528
  0xffde954f 0x232a91c84284563508904a286622419205c54508cc72b3289b84366553508504caa66814a155cc82242299904 (by decide +kernel)
private def pack_E6970Receipt40_chunk159 := witnessRule 40 35 96 850448 850705 24 1209
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk160 := witnessRule 40 34 0 860000 860077 32 1750
  0x27fc0bff 0x2e8d2a462145cda550e138b4aa9c2827168513acd4a95a548c42234aa1b2746a562e4d2aa70dc9a944e23d291b (by decide +kernel)
private def pack_E6970Receipt40_chunk161 := witnessRule 40 34 32 860078 860257 32 1534
  0xf53e03fc 0x1b3aa9a042826653330a50cae62112154cc423342a035685233088d0a86410da158c42141b3a91885282675438502e2cea662199a544c422b4a99b (by decide +kernel)
private def pack_E6970Receipt40_chunk162 := witnessRule 40 34 64 860258 860450 32 1481
  0xffffeef5 0x482514231140c8cca47010a1558d02241a8a1988886 (by decide +kernel)
private def pack_E6970Receipt40_chunk163 := witnessRule 40 34 96 860451 860704 18 891
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk164 := witnessRule 40 33 0 870000 870078 32 1650
  0x3fe07ff 0x5695232088d2a86210da558d941b4291c281726851310c502e2d0a6759a944d8bab528841746a52384e6d4a262149c9a94ce1b8b5291885 (by decide +kernel)
private def pack_E6970Receipt40_chunk165 := witnessRule 40 33 32 870079 870259 32 1472
  0x7fd7fa7e 0x906a284622618a1958cc224228a1988d2826753320a50eae6d2194cdb34a983 (by decide +kernel)
private def pack_E6970Receipt40_chunk166 := witnessRule 40 33 64 870260 870454 32 1455
  0xffffff7f 0x2c0a11a0c (by decide +kernel)
private def pack_E6970Receipt40_chunk167 := witnessRule 40 33 96 870512 870704 12 587
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk168 := witnessRule 40 32 0 880000 880078 32 1558
  0x42fe05ff 0x2b4a89a04369553208506d0a26414a09a14cc42940b42a9c3817751423acd4a40d5a948c422352a1b1736a53310a2e4d4aa70a05c9a544e9413ca91c (by decide +kernel)
private def pack_E6970Receipt40_chunk169 := witnessRule 40 32 32 880128 880261 32 1417
  0xfd7be57f 0x8cea2721099d54dc224228a11889064685236086d0a86a10a099d48d02943ab1904 (by decide +kernel)
private def pack_E6970Receipt40_chunk170 := witnessRule 40 32 64 880262 880515 32 1435
  0xfffffff7 0x1b3291d84 (by decide +kernel)
private def pack_E6970Receipt40_chunk171 := witnessRule 40 32 96 880516 880641 6 289
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk172 := witnessRule 40 31 0 890000 890128 32 1491
  0xdaff03ff 0x234a91a842826852330a510ac62115a944cc223529990436a553108506d2a26214a09a54ce140b8b4a91886 (by decide +kernel)
private def pack_E6970Receipt40_chunk173 := witnessRule 40 31 32 890129 890263 32 1351
  0xffbffdef 0x6cea474109a154d82242a8a1188886 (by decide +kernel)
private def pack_E6970Receipt40_chunk174 := witnessRule 40 31 64 890264 890640 32 1422
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk175 := witnessRule 40 30 0 900000 900129 32 1421
  0xffbffdff 0x12194508c46944ab1b (by decide +kernel)
private def pack_E6970Receipt40_chunk176 := witnessRule 40 30 32 900130 900265 32 1297
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk177 := witnessRule 40 30 64 900320 900640 27 1176
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk178 := witnessRule 40 29 0 910000 910130 32 1354
  0xf2ffa5ff 0x6d2a470109a550dc2140b4291b0546a5136084d4aa6810a09a544d02944aa9904 (by decide +kernel)
private def pack_E6970Receipt40_chunk179 := witnessRule 40 29 32 910131 910322 32 1260
  0xfffbfebf 0x4cea47a10da144ec20b42a9c84 (by decide +kernel)
private def pack_E6970Receipt40_chunk180 := witnessRule 40 29 64 910323 910577 21 894
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk181 := witnessRule 40 28 0 920000 920131 32 1284
  0xfdffdbff 0x2d2aa7010da948dc2140b4a91a85 (by decide +kernel)
private def pack_E6970Receipt40_chunk182 := witnessRule 40 28 32 920132 920324 32 1229
  0xffffffbf 0x134291e04 (by decide +kernel)
private def pack_E6970Receipt40_chunk183 := witnessRule 40 28 64 920325 920576 16 667
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk184 := witnessRule 40 27 0 930000 930132 32 1219
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk185 := witnessRule 40 27 32 930133 930384 32 1203
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk186 := witnessRule 40 27 64 930385 930576 11 451
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk187 := witnessRule 40 26 0 940000 940133 32 1161
  0xfd7fe5ff 0x134a89e849553b064d4a474105a950e42144a91c04 (by decide +kernel)
private def pack_E6970Receipt40_chunk188 := witnessRule 40 26 32 940134 940387 32 1179
  0xfffffff7 0xb4291f84 (by decide +kernel)
private def pack_E6970Receipt40_chunk189 := witnessRule 40 26 64 940388 940513 6 241
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk190 := witnessRule 40 25 0 950000 950134 32 1108
  0xff7ffbff 0x5a548f8252a9d03 (by decide +kernel)
private def pack_E6970Receipt40_chunk191 := witnessRule 40 25 32 950135 950450 32 1160
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk192 := witnessRule 40 25 64 950512 950512 1 40
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk193 := witnessRule 40 24 0 960000 960135 32 1058
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk194 := witnessRule 40 24 32 960136 960512 29 1026
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk195 := witnessRule 40 23 0 970000 970136 32 1016
  0xffdff5ff 0x4a91a200c5a944fc20c4a8a09e85 (by decide +kernel)
private def pack_E6970Receipt40_chunk196 := witnessRule 40 23 32 970192 970449 24 825
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk197 := witnessRule 40 22 0 980000 980192 32 976
  0xfffffbff 0x14a468003 (by decide +kernel)
private def pack_E6970Receipt40_chunk198 := witnessRule 40 22 32 980193 980448 20 667
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk199 := witnessRule 40 21 0 990000 990194 32 940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk200 := witnessRule 40 21 32 990195 990448 16 519
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk201 := witnessRule 40 20 0 1000000 1000195 32 906
  0xfffffdff 0x12a489003 (by decide +kernel)
private def pack_E6970Receipt40_chunk202 := witnessRule 40 20 32 1000196 1000385 12 377
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk203 := witnessRule 40 19 0 1010000 1010197 32 875
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk204 := witnessRule 40 19 32 1010256 1010384 8 245
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk205 := witnessRule 40 18 0 1020000 1020257 32 845
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk206 := witnessRule 40 18 32 1020258 1020384 5 149
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk207 := witnessRule 40 17 0 1030000 1030320 32 820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk208 := witnessRule 40 17 32 1030321 1030321 1 29
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk209 := witnessRule 40 16 0 1040000 1040320 30 738
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk210 := witnessRule 40 15 0 1050000 1050320 27 636
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk211 := witnessRule 40 14 0 1060000 1060257 24 537
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk212 := witnessRule 40 13 0 1070000 1070256 21 447
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk213 := witnessRule 40 12 0 1080000 1080256 19 384
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk214 := witnessRule 40 11 0 1090000 1090193 16 305
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk215 := witnessRule 40 10 0 1100000 1100192 14 251
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk216 := witnessRule 40 9 0 1110000 1110192 12 203
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk217 := witnessRule 40 8 0 1120000 1120129 10 157
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk218 := witnessRule 40 7 0 1130000 1130128 8 117
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk219 := witnessRule 40 6 0 1140000 1140128 7 95
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk220 := witnessRule 40 5 0 1150000 1150065 5 62
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk221 := witnessRule 40 4 0 1160000 1160064 4 45
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk222 := witnessRule 40 3 0 1170000 1170064 3 31
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk223 := witnessRule 40 2 0 1180000 1180001 2 18
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk224 := witnessRule 40 1 0 1190000 1190000 1 8
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt40_chunk225 := witnessRule 40 0 0 1200000 1200000 1 7
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt40_chunks : List (Chunk 40) := [pack_E6970Receipt40_chunk0, pack_E6970Receipt40_chunk1, pack_E6970Receipt40_chunk2, pack_E6970Receipt40_chunk3, pack_E6970Receipt40_chunk4, pack_E6970Receipt40_chunk5, pack_E6970Receipt40_chunk6, pack_E6970Receipt40_chunk7, pack_E6970Receipt40_chunk8, pack_E6970Receipt40_chunk9, pack_E6970Receipt40_chunk10, pack_E6970Receipt40_chunk11, pack_E6970Receipt40_chunk12, pack_E6970Receipt40_chunk13, pack_E6970Receipt40_chunk14, pack_E6970Receipt40_chunk15, pack_E6970Receipt40_chunk16, pack_E6970Receipt40_chunk17, pack_E6970Receipt40_chunk18, pack_E6970Receipt40_chunk19, pack_E6970Receipt40_chunk20, pack_E6970Receipt40_chunk21, pack_E6970Receipt40_chunk22, pack_E6970Receipt40_chunk23, pack_E6970Receipt40_chunk24, pack_E6970Receipt40_chunk25, pack_E6970Receipt40_chunk26, pack_E6970Receipt40_chunk27, pack_E6970Receipt40_chunk28, pack_E6970Receipt40_chunk29, pack_E6970Receipt40_chunk30, pack_E6970Receipt40_chunk31, pack_E6970Receipt40_chunk32, pack_E6970Receipt40_chunk33, pack_E6970Receipt40_chunk34, pack_E6970Receipt40_chunk35, pack_E6970Receipt40_chunk36, pack_E6970Receipt40_chunk37, pack_E6970Receipt40_chunk38, pack_E6970Receipt40_chunk39, pack_E6970Receipt40_chunk40, pack_E6970Receipt40_chunk41, pack_E6970Receipt40_chunk42, pack_E6970Receipt40_chunk43, pack_E6970Receipt40_chunk44, pack_E6970Receipt40_chunk45, pack_E6970Receipt40_chunk46, pack_E6970Receipt40_chunk47, pack_E6970Receipt40_chunk48, pack_E6970Receipt40_chunk49, pack_E6970Receipt40_chunk50, pack_E6970Receipt40_chunk51, pack_E6970Receipt40_chunk52, pack_E6970Receipt40_chunk53, pack_E6970Receipt40_chunk54, pack_E6970Receipt40_chunk55, pack_E6970Receipt40_chunk56, pack_E6970Receipt40_chunk57, pack_E6970Receipt40_chunk58, pack_E6970Receipt40_chunk59, pack_E6970Receipt40_chunk60, pack_E6970Receipt40_chunk61, pack_E6970Receipt40_chunk62, pack_E6970Receipt40_chunk63, pack_E6970Receipt40_chunk64, pack_E6970Receipt40_chunk65, pack_E6970Receipt40_chunk66, pack_E6970Receipt40_chunk67, pack_E6970Receipt40_chunk68, pack_E6970Receipt40_chunk69, pack_E6970Receipt40_chunk70, pack_E6970Receipt40_chunk71, pack_E6970Receipt40_chunk72, pack_E6970Receipt40_chunk73, pack_E6970Receipt40_chunk74, pack_E6970Receipt40_chunk75, pack_E6970Receipt40_chunk76, pack_E6970Receipt40_chunk77, pack_E6970Receipt40_chunk78, pack_E6970Receipt40_chunk79, pack_E6970Receipt40_chunk80, pack_E6970Receipt40_chunk81, pack_E6970Receipt40_chunk82, pack_E6970Receipt40_chunk83, pack_E6970Receipt40_chunk84, pack_E6970Receipt40_chunk85, pack_E6970Receipt40_chunk86, pack_E6970Receipt40_chunk87, pack_E6970Receipt40_chunk88, pack_E6970Receipt40_chunk89, pack_E6970Receipt40_chunk90, pack_E6970Receipt40_chunk91, pack_E6970Receipt40_chunk92, pack_E6970Receipt40_chunk93, pack_E6970Receipt40_chunk94, pack_E6970Receipt40_chunk95, pack_E6970Receipt40_chunk96, pack_E6970Receipt40_chunk97, pack_E6970Receipt40_chunk98, pack_E6970Receipt40_chunk99, pack_E6970Receipt40_chunk100, pack_E6970Receipt40_chunk101, pack_E6970Receipt40_chunk102, pack_E6970Receipt40_chunk103, pack_E6970Receipt40_chunk104, pack_E6970Receipt40_chunk105, pack_E6970Receipt40_chunk106, pack_E6970Receipt40_chunk107, pack_E6970Receipt40_chunk108, pack_E6970Receipt40_chunk109, pack_E6970Receipt40_chunk110, pack_E6970Receipt40_chunk111, pack_E6970Receipt40_chunk112, pack_E6970Receipt40_chunk113, pack_E6970Receipt40_chunk114, pack_E6970Receipt40_chunk115, pack_E6970Receipt40_chunk116, pack_E6970Receipt40_chunk117, pack_E6970Receipt40_chunk118, pack_E6970Receipt40_chunk119, pack_E6970Receipt40_chunk120, pack_E6970Receipt40_chunk121, pack_E6970Receipt40_chunk122, pack_E6970Receipt40_chunk123, pack_E6970Receipt40_chunk124, pack_E6970Receipt40_chunk125, pack_E6970Receipt40_chunk126, pack_E6970Receipt40_chunk127, pack_E6970Receipt40_chunk128, pack_E6970Receipt40_chunk129, pack_E6970Receipt40_chunk130, pack_E6970Receipt40_chunk131, pack_E6970Receipt40_chunk132, pack_E6970Receipt40_chunk133, pack_E6970Receipt40_chunk134, pack_E6970Receipt40_chunk135, pack_E6970Receipt40_chunk136, pack_E6970Receipt40_chunk137, pack_E6970Receipt40_chunk138, pack_E6970Receipt40_chunk139, pack_E6970Receipt40_chunk140, pack_E6970Receipt40_chunk141, pack_E6970Receipt40_chunk142, pack_E6970Receipt40_chunk143, pack_E6970Receipt40_chunk144, pack_E6970Receipt40_chunk145, pack_E6970Receipt40_chunk146, pack_E6970Receipt40_chunk147, pack_E6970Receipt40_chunk148, pack_E6970Receipt40_chunk149, pack_E6970Receipt40_chunk150, pack_E6970Receipt40_chunk151, pack_E6970Receipt40_chunk152, pack_E6970Receipt40_chunk153, pack_E6970Receipt40_chunk154, pack_E6970Receipt40_chunk155, pack_E6970Receipt40_chunk156, pack_E6970Receipt40_chunk157, pack_E6970Receipt40_chunk158, pack_E6970Receipt40_chunk159, pack_E6970Receipt40_chunk160, pack_E6970Receipt40_chunk161, pack_E6970Receipt40_chunk162, pack_E6970Receipt40_chunk163, pack_E6970Receipt40_chunk164, pack_E6970Receipt40_chunk165, pack_E6970Receipt40_chunk166, pack_E6970Receipt40_chunk167, pack_E6970Receipt40_chunk168, pack_E6970Receipt40_chunk169, pack_E6970Receipt40_chunk170, pack_E6970Receipt40_chunk171, pack_E6970Receipt40_chunk172, pack_E6970Receipt40_chunk173, pack_E6970Receipt40_chunk174, pack_E6970Receipt40_chunk175, pack_E6970Receipt40_chunk176, pack_E6970Receipt40_chunk177, pack_E6970Receipt40_chunk178, pack_E6970Receipt40_chunk179, pack_E6970Receipt40_chunk180, pack_E6970Receipt40_chunk181, pack_E6970Receipt40_chunk182, pack_E6970Receipt40_chunk183, pack_E6970Receipt40_chunk184, pack_E6970Receipt40_chunk185, pack_E6970Receipt40_chunk186, pack_E6970Receipt40_chunk187, pack_E6970Receipt40_chunk188, pack_E6970Receipt40_chunk189, pack_E6970Receipt40_chunk190, pack_E6970Receipt40_chunk191, pack_E6970Receipt40_chunk192, pack_E6970Receipt40_chunk193, pack_E6970Receipt40_chunk194, pack_E6970Receipt40_chunk195, pack_E6970Receipt40_chunk196, pack_E6970Receipt40_chunk197, pack_E6970Receipt40_chunk198, pack_E6970Receipt40_chunk199, pack_E6970Receipt40_chunk200, pack_E6970Receipt40_chunk201, pack_E6970Receipt40_chunk202, pack_E6970Receipt40_chunk203, pack_E6970Receipt40_chunk204, pack_E6970Receipt40_chunk205, pack_E6970Receipt40_chunk206, pack_E6970Receipt40_chunk207, pack_E6970Receipt40_chunk208, pack_E6970Receipt40_chunk209, pack_E6970Receipt40_chunk210, pack_E6970Receipt40_chunk211, pack_E6970Receipt40_chunk212, pack_E6970Receipt40_chunk213, pack_E6970Receipt40_chunk214, pack_E6970Receipt40_chunk215, pack_E6970Receipt40_chunk216, pack_E6970Receipt40_chunk217, pack_E6970Receipt40_chunk218, pack_E6970Receipt40_chunk219, pack_E6970Receipt40_chunk220, pack_E6970Receipt40_chunk221, pack_E6970Receipt40_chunk222, pack_E6970Receipt40_chunk223, pack_E6970Receipt40_chunk224, pack_E6970Receipt40_chunk225]
def rows40 := rowsFrom pack_E6970Receipt40_chunks
theorem good40 : ∀ r ∈ rows40, good 40 r = true := rowsFrom_good pack_E6970Receipt40_chunks
theorem sorted40 : rows40.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt40_chunks 0 (by decide +kernel)).1
theorem mass40 (i : Fin 61) :
    bandCount 40 (i.val : ℤ) 60 16 ≤ (rows40.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt40_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 40 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt40_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total40 : (rows40.map (price 40)).sum = 419139 :=
  (total_eq pack_E6970Receipt40_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt40

section Pack_E6970Receipt41

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt41_chunk0 := witnessA6966Final 41 60 0 630019 630150 32 3426
  0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk1 := witnessA6966Final 41 60 32 630151 630280 32 3318
  0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk2 := witnessA6966Final 41 60 64 630329 630455 32 3362
  0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk3 := witnessA6966Final 41 60 96 630456 630580 32 3313
  0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk4 := witnessA6966Final 41 60 128 630581 630707 32 3244
  0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk5 := witnessA6966Final 41 60 160 630708 630840 32 3094
  0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk6 := witnessA6966Final 41 60 192 630841 631030 27 2494
  0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk7 := witnessRule 41 59 0 640018 640148 32 3268
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk8 := witnessRule 41 59 32 640149 640277 32 3185
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk9 := witnessRule 41 59 64 640278 640404 32 3165
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk10 := witnessRule 41 59 96 640452 640529 32 3159
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk11 := witnessRule 41 59 128 640576 640654 32 3109
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk12 := witnessRule 41 59 160 640704 640837 32 2990
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk13 := witnessRule 41 59 192 640838 641029 28 2494
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk14 := witnessRule 41 58 0 650017 650146 32 3154
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk15 := witnessRule 41 58 32 650147 650274 32 3085
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk16 := witnessRule 41 58 64 650275 650400 32 3066
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk17 := witnessRule 41 58 96 650401 650524 32 3057
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk18 := witnessRule 41 58 128 650525 650650 32 2960
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk19 := witnessRule 41 58 160 650651 650834 32 2861
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk20 := witnessRule 41 58 192 650835 651029 29 2504
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk21 := witnessRule 41 57 0 660016 660144 32 3083
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk22 := witnessRule 41 57 32 660145 660271 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk23 := witnessRule 41 57 64 660272 660396 32 2993
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk24 := witnessRule 41 57 96 660397 660519 32 2978
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk25 := witnessRule 41 57 128 660520 660646 32 2850
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk26 := witnessRule 41 57 160 660647 660832 32 2755
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk27 := witnessRule 41 57 192 660833 661028 29 2433
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk28 := witnessRule 41 56 0 670015 670142 32 3026
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk29 := witnessRule 41 56 32 670143 670268 32 2947
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk30 := witnessRule 41 56 64 670269 670392 32 2926
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk31 := witnessRule 41 56 96 670393 670515 32 2877
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk32 := witnessRule 41 56 128 670516 670643 32 2754
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk33 := witnessRule 41 56 160 670644 670777 32 2662
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk34 := witnessRule 41 56 192 670778 671028 29 2366
  0x1fffbfff 0xb99a (by decide +kernel)
private def pack_E6970Receipt41_chunk35 := witnessRule 41 55 0 680014 680140 32 2970
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk36 := witnessRule 41 55 32 680141 680265 32 2893
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk37 := witnessRule 41 55 64 680266 680388 32 2856
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk38 := witnessRule 41 55 96 680389 680465 32 2775
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk39 := witnessRule 41 55 128 680512 680640 32 2689
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk40 := witnessRule 41 55 160 680641 680775 32 2585
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk41 := witnessRule 41 55 192 680776 681027 28 2220
  0xfffbf7f 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt41_chunk42 := witnessRule 41 54 0 690013 690138 32 2911
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk43 := witnessRule 41 54 32 690139 690262 32 2833
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk44 := witnessRule 41 54 64 690263 690339 32 2753
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk45 := witnessRule 41 54 96 690385 690461 32 2771
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk46 := witnessRule 41 54 128 690462 690588 32 2583
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk47 := witnessRule 41 54 160 690589 690774 32 2505
  0x6fffffff 0x5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt41_chunk48 := witnessRule 41 54 192 690775 691027 27 2084
  0x7ffdf3f 0x2ea685c590d938b19b (by decide +kernel)
private def pack_E6970Receipt41_chunk49 := witnessRule 41 53 0 700012 700136 32 2846
  0xffffff3f 0x11ccd2b8a2 (by decide +kernel)
private def pack_E6970Receipt41_chunk50 := witnessRule 41 53 32 700137 700214 32 2753
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk51 := witnessRule 41 53 64 700260 700336 32 2779
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk52 := witnessRule 41 53 96 700337 700458 32 2693
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk53 := witnessRule 41 53 128 700459 700586 32 2492
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk54 := witnessRule 41 53 160 700587 700773 32 2428
  0x2fb7ffff 0xb9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt41_chunk55 := witnessRule 41 53 192 700774 701026 25 1881
  0x1ffef9f 0x2ec685c594d938b21b (by decide +kernel)
private def pack_E6970Receipt41_chunk56 := witnessRule 41 52 0 710011 710088 32 2776
  0xf57feaff 0x9cd8cd9b8b21b57141362e8c66c9c990d9ba9a (by decide +kernel)
private def pack_E6970Receipt41_chunk57 := witnessRule 41 52 32 710135 710211 32 2760
  0xfafffaff 0x4716336ce288dc98cda3a1a (by decide +kernel)
private def pack_E6970Receipt41_chunk58 := witnessRule 41 52 64 710212 710332 32 2743
  0xfffff9ff 0x15ccd338a2 (by decide +kernel)
private def pack_E6970Receipt41_chunk59 := witnessRule 41 52 96 710333 710455 32 2584
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk60 := witnessRule 41 52 128 710456 710584 32 2410
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk61 := witnessRule 41 52 160 710585 710773 32 2355
  0x8793edbf 0x2e4ca6c9c990d9b8b19884375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt41_chunk62 := witnessRule 41 52 192 710774 711026 23 1691
  0x7ffbcf 0x2ee685c598d938b29b (by decide +kernel)
private def pack_E6970Receipt41_chunk63 := witnessRule 41 51 0 720010 720087 32 2745
  0xaaffd47f 0x2b21a17365368e4c2a2115c544c422329a3736151088e2c2a262151c54cdab922 (by decide +kernel)
private def pack_E6970Receipt41_chunk64 := witnessRule 41 51 32 720088 720209 32 2731
  0xa9feaafe 0x9cd90d9b8b29b6715106ce24998cd0ba321b2726536ae2c2a2119c493b0aa (by decide +kernel)
private def pack_E6970Receipt41_chunk65 := witnessRule 41 51 64 720210 720329 32 2712
  0xbffd5ffe 0x338a09b27463366e4c86d1d4d0bab19b (by decide +kernel)
private def pack_E6970Receipt41_chunk66 := witnessRule 41 51 96 720330 720453 32 2490
  0xbffafffa 0x3b8a24726336ae868dcd8cda38b21b (by decide +kernel)
private def pack_E6970Receipt41_chunk67 := witnessRule 41 51 128 720454 720583 32 2336
  0xb7ffcffe 0x1b9b19b5716336ce669dc512b8b19b (by decide +kernel)
private def pack_E6970Receipt41_chunk68 := witnessRule 41 51 160 720584 720773 32 2285
  0xc3c1e4bd 0x2e4cc6c9c994d9b8b21884376342e6ca6c9cd90d9b931988437165368e2c86c5d190d93a319b37264368e4c66d5d0d0bab19b (by decide +kernel)
private def pack_E6970Receipt41_chunk69 := witnessRule 41 51 192 720774 721025 20 1439
  0xffff7 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt41_chunk70 := witnessRule 41 50 0 730009 730085 32 2717
  0x81fe80ff 0x9d18544c42939b0a99c3726152310a6e2c2a8715c5895ab8a8a09c76151062eac2a262145d1854ce139b0a918852726154388e4c4acdc554dab9289b (by decide +kernel)
private def pack_E6970Receipt41_chunk71 := witnessRule 41 50 32 730086 730206 32 2701
  0xffa83fe 0x4726151310a8e2c2a6715c548c42338a8a366152364eac2a210dcd8544c429b930a99c4716152310a8e2a86d9c950bb30a884 (by decide +kernel)
private def pack_E6970Receipt41_chunk72 := witnessRule 41 50 64 730207 730326 32 2635
  0xfeaa3ff5 0x430aa664342e8ca6d1cd854422b8b0a898855715336ce489594d1ba30a884 (by decide +kernel)
private def pack_E6970Receipt41_chunk73 := witnessRule 41 50 96 730327 730451 32 2407
  0x7eaafd55 0xee2485d98cd93a321b3726536ce2c2a211dc493b19a17564364e6ca6d5c985442338a89884 (by decide +kernel)
private def pack_E6970Receipt41_chunk74 := witnessRule 41 50 128 730452 730582 32 2269
  0x93da3faa 0x1b9b21b4736336ae2c86d9ccc418bb319b37463368e4c86d5c58cc422ba9a27563366e6c86d1c594dbb8a883 (by decide +kernel)
private def pack_E6970Receipt41_chunk75 := witnessRule 41 50 160 730583 730774 32 2220
  0xf1e0f01c 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b571633108aea685d590d93ab19b (by decide +kernel)
private def pack_E6970Receipt41_chunk76 := witnessRule 41 50 192 730775 731025 17 1201
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk77 := witnessRule 41 49 0 740008 740084 32 2689
  0x17fe07ff 0x9d58958b9b0aa9c3736251388e2c4a47198944d8bb312b46155364e8c4a270dcd894421b931291c (by decide +kernel)
private def pack_E6970Receipt41_chunk78 := witnessRule 41 49 32 740085 740204 32 2674
  0x3fe02ff8 0x2b8b1289c6725106ec2a262119854cd8bab0a918851746154386e8c4ac9c98554e23931289c5725236ec4a998548c422b0aa1b (by decide +kernel)
private def pack_E6970Receipt41_chunk79 := witnessRule 41 49 64 740205 740324 32 2560
  0xfd01ff40 0x2eec2a2109d58544c4293a30a99c3736152310a6e4c2a8715c9895a38aa9b67251370c2a20c5d98544c428bab0a99c2746152310a4e6c2a8711cd8959b8b0aa9c (by decide +kernel)
private def pack_E6970Receipt41_chunk80 := witnessRule 41 49 96 740325 740450 32 2333
  0xfa83f503 0xcca68dd585442239b0a89885472615338ae2c2a462155c550dbb92a76152364ecc2a210dd18544c429b9b0a99c4726152310a8e2c2a8719c5895b38a8a09c (by decide +kernel)
private def pack_E6970Receipt41_chunk81 := witnessRule 41 49 128 740451 740582 32 2203
  0x1c11c50 0x4eac86cdd18cc421b9b29b4726431088e2cc6d5d4c41b38a19b17664364eac662109d194d9b9b218843726636ce2c2a262159c54cdbb8a08b764342ecc662105d594da3a30a8845726151310aae2c2a6719c548c423b8a8a3 (by decide +kernel)
private def pack_E6970Receipt41_chunk82 := witnessRule 41 49 160 740583 740832 32 2162
  0xfef8781e 0x17a342e6ce6c9c998c42138b41b37731062e8cc6c9d194d9b9b2188437266368e2ca62111dcd0bab29b (by decide +kernel)
private def pack_E6970Receipt41_chunk83 := witnessRule 41 49 192 740833 741024 13 902
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk84 := witnessRule 41 48 0 750007 750082 32 2664
  0x7fc01ff 0x9cd894ce1b931291885371625438ae2c6ad5c94504e3b1288366252362eac4a262145d1894ce139b12918852726254388e4c6acdc954dab9a89b (by decide +kernel)
private def pack_E6970Receipt41_chunk85 := witnessRule 41 48 32 750083 750201 32 2644
  0xff801ff0 0x21895331291b1766251384eac4a2109d18948e1b9b12898853726253388e2c4a462151c950db39aa76251362ecc4a2105d58948e13a31289885 (by decide +kernel)
private def pack_E6970Receipt41_chunk86 := witnessRule 41 48 64 750202 750322 32 2435
  0xe003fc00 0x4312a761523108cc2a86c9d98958ba30aa9c3746251388e6c4a2111c98948e2b8b12898855725336ce2a48dd8944d8bbb12b56155364eac4a270dd1894421b9b1291c4726251310a8e2c4a6715c948c4233928a3 (by decide +kernel)
private def pack_E6970Receipt41_chunk87 := witnessRule 41 48 96 750323 750449 32 2271
  0xd003c007 0x25854418bbb0a898851766153384eac2a462149d18550e23a312b372615538ae4c4a2719c589442339291b77141270c2a26211d854cd8bb30a918851756154386eac4ac9cd8554e239b1289c572625108ae2c4a4719c944c423b8a893 (by decide +kernel)
private def pack_E6970Receipt41_chunk88 := witnessRule 41 48 128 750450 750582 32 2141
  0x1800a00 0x17566364e8ca62109cd9cd9b93318843716836308e2c870615ccc423b21883666342eaca62105d19cd9ba30a99c4736152310a8e4c2a8715c5854cc42ab8aa9b771513118ee2422dd854cd93b30a898852756153386e8c2a46214dcd8550e23930a99885471615538ce2c4a271dc9441bb8a093 (by decide +kernel)
private def pack_E6970Receipt41_chunk89 := witnessRule 41 48 160 750583 750834 32 2111
  0xffff7e0e 0x2e2d46c5d19cd939b3188427268366e2ce6210de4d0bb321884 (by decide +kernel)
private def pack_E6970Receipt41_chunk90 := witnessRule 41 48 192 750835 751024 9 616
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk91 := witnessRule 41 47 0 760006 760081 32 2640
  0x5ffc0fff 0x3736351388e2c6a47198d44d8bb31ab46255364e8c6a270dcd8d4421b931a91c (by decide +kernel)
private def pack_E6970Receipt41_chunk92 := witnessRule 41 47 32 760082 760199 32 2612
  0xff017fe0 0x3b128988466253362eac4a462145d18950e1ba31ab2726255388e4c6a2715cd48dbb1aa662523108ac4a86c9d58d58b9b12a9c (by decide +kernel)
private def pack_E6970Receipt41_chunk93 := witnessRule 41 47 64 760200 760321 32 2337
  0xc00ff003 0x86251362eec4a2105d98948e13ab12898852746253386e6c4a46214dc98950e2b931ab4725536ce6a26e189441bb1291b1766251310a2eac4a6709d18948c42939b12a1c47363566e2c4aa715c58d44e339a883 (by decide +kernel)
private def pack_E6970Receipt41_chunk94 := witnessRule 41 47 96 760322 760449 32 2202
  0xc007800f 0x218944dbb0a9988466155364ecc4a270dd5894421ba31291c4736251310a8e4c4a6715c58948c42ab92a1b773552c4a9d8948d8bbb1289c2766251084eac4a470dd18944c429b9b1299c4726252310a8e2c4a8719c58d5b3928a09c (by decide +kernel)
private def pack_E6970Receipt41_chunk95 := witnessRule 41 47 128 760450 760583 32 2072
  0x20c01800 0xccc620d5a0d0b9b49b182736538306e4c8621460dc598e0c23a988466155362ecc2a8709d5854cc4293a30aa9c3736154310a6e4c2ac711c58554c42a38ab9b1857153390c2a46211d8550d8bb30a998851756155384e8c2a862149cd8558e239b1291c5726251310aae2c4a6719c948c423b8a8a08c (by decide +kernel)
private def pack_E6970Receipt41_chunk96 := witnessRule 41 47 160 760584 760896 32 2073
  0xffffffc7 0x2e4d46c9c5a4c4213d9a (by decide +kernel)
private def pack_E6970Receipt41_chunk97 := witnessRule 41 47 192 760897 760961 4 270
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk98 := witnessRule 41 46 0 770005 770079 32 2617
  0x7ff807ff 0x1b8b1aa1c7635106cc6a46c5d58d44c428ba31a99c2736352310a4e4c6a8711c99159b9aa9b (by decide +kernel)
private def pack_E6970Receipt41_chunk99 := witnessRule 41 46 32 770080 770197 32 2521
  0xfc03ffc0 0x218d5331a91b1766351384eac6a2109d18d48e1b9b1a898853726353388e2c6a46215d8d44d8bb31a8841756352384e8c6a262149cd8d4ce1b931a91885 (by decide +kernel)
private def pack_E6970Receipt41_chunk100 := witnessRule 41 46 64 770198 770320 32 2251
  0x807fe03f 0x10c6a9d8948c423312a1b27663562e8c4aa70dd18d44e239b1a884472635238ec6a26c5dd8d5ab12a9b2756351386e8c6a210dcd8d48e23931a89885 (by decide +kernel)
private def pack_E6970Receipt41_chunk101 := witnessRule 41 46 96 770321 770449 32 2138
  0xc01780bf 0x2189481c31291b1776251310a2ecc4a6709d58948c4293a312a1c3736253310a6e4c4aa715c98d44e339a91b862513108ec4a66c5d98948c428bab12a1c37563564e6c4aa711cd8d44e2b8b1a91c (by decide +kernel)
private def pack_E6970Receipt41_chunk102 := witnessRule 41 46 128 770450 770584 32 2006
  0xd8600400 0x2b0ab9b181736738304e4cc6214609c5a0e0c1bb9884761543108cc2ac6c5d58554c428ba30ab9c2736156310a4e4c2b07060dc98550e8c238b0a9988618471553830ce26431d894cdb30aa988456157364eac4a670dd18948c429b9b12a1c4726253310a8e2c4aa715c950c4233928a11c (by decide +kernel)
private def pack_E6970Receipt41_chunk103 := witnessRule 41 46 160 770585 770960 31 1978
  0x7ffffffd 0xbe9a (by decide +kernel)
private def pack_E6970Receipt41_chunk104 := witnessRule 41 45 0 780004 780078 32 2597
  0x7ff81fff 0x8e2c8a47199144d8bb322b46355364e8c8a270dcd914421b932291c (by decide +kernel)
private def pack_E6970Receipt41_chunk105 := witnessRule 41 45 32 780079 780196 32 2447
  0xf80bff81 0x1d8d44c42331a99b1756352310a2e8c6a870dd191593931aa9c472645138ae8a46dd915331a9188456354364eac8ac5cd8d54e1b9b2289c (by decide +kernel)
private def pack_E6970Receipt41_chunk106 := witnessRule 41 45 64 780197 780320 32 2179
  0x801fc00f 0x86351362eec6a2105d98d48e13ab1a898852746353386e6c6a46214dc98d50e2b9322b4735536ce8a26e18d441bb1a91b1766351310a2eac6a6709d18d48c42939b1aa1c47364566e2c6aa715c59144e33a2883 (by decide +kernel)
private def pack_E6970Receipt41_chunk107 := witnessRule 41 45 96 780321 780450 32 2057
  0x6003800f 0x30ae4a4621618944c823b129988466255362eac4a862145d18958e1ba31a91c4736351310a8e4c6a6715c58d48c42ab9aa1b77351170c6a20dd8d48d8bbb1a89c2766351084eac6a470dd18d44c429b9b1a99c4726352310a8e2c6a8719c5915b39a8a09c (by decide +kernel)
private def pack_E6970Receipt41_chunk108 := witnessRule 41 45 128 780451 780640 32 1945
  0xffb80200 0x302e2d47198954dab0ab98844615936302e8c2aa74609cd8550c430c13930ab1d183716155310c306e2ae70a11ccc463b129190476254362ecc4a662145d58954e13a312a18852736256386e4c4aa6214dc5895ce0c238b1299d (by decide +kernel)
private def pack_E6970Receipt41_chunk109 := witnessRule 41 45 160 780641 780960 26 1630
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk110 := witnessRule 41 44 0 790003 790076 32 2577
  0xfff00fff 0x7645106cc8a46c5d59144c428ba32299c2736452310a4e4c8a8711c99559ba2a9b (by decide +kernel)
private def pack_E6970Receipt41_chunk111 := witnessRule 41 44 32 790077 790195 32 2323
  0xf00fff01 0x10c8a999148d8bb32289c2756451084e8c8a470dcd9144c429b932299c4716452310aec8a26c5d9914420bab2291c2746451310a4e6c8a670dc99148c429b8b22a1c (by decide +kernel)
private def pack_E6970Receipt41_chunk112 := witnessRule 41 44 64 790196 790320 32 2107
  0x807fc07f 0x10c8a9d8d48c42331aa1b27664562e8c6aa70dd19144e239b22884472645238ec8a26c5dd915ab1aa9b2756451386e8c8a210dcd9148e23932289885 (by decide +kernel)
private def pack_E6970Receipt41_chunk113 := witnessRule 41 44 96 790321 790451 32 1978
  0x7009c05f 0x306e2c4aa76189501bb1a9188466354362ecc6a6709d58d48c4293a31aa1c3736353310a6e4c6aa711cd58d8c2b9a91c863513108ec6a66c5d98d48c428bab1aa1c2746353310a4e6c6aa711cd9144e2b8b2291c (by decide +kernel)
private def pack_E6970Receipt41_chunk114 := witnessRule 41 44 128 790452 790643 32 1892
  0xfffe0480 0xcc4a8641158958c420c2b0aa9885184615738302e6c2ac6218605c98560e8c138ac9c3827536ec4a6641198954c422b12b9b1746256310a2e6c4b070609cd8950e8c1b931299886 (by decide +kernel)
private def pack_E6970Receipt41_chunk115 := witnessRule 41 44 160 790644 790897 20 1234
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk116 := witnessRule 41 43 0 800002 800075 32 2560
  0xfff03fff 0x199544d8bb32ab46455364e8caa270dcd954421b932a91c (by decide +kernel)
private def pack_E6970Receipt41_chunk117 := witnessRule 41 43 32 800076 800195 32 2226
  0xf017fe05 0xec8a262119914cd8bab22918851746454386e8caac9c99154e23932a89c5755236ecaa999148c422b22a1b27565562e6c8aa70dcd9544e238b2a91c (by decide +kernel)
private def pack_E6970Receipt41_chunk118 := witnessRule 41 43 64 800196 800321 32 2031
  0xc01fc01f 0x219144d8bbb228841766452384eac8a262149d1914ce1b9b2291885372645438ae4caad1d154dc32288376452362ecc8a262145d5914ce13a322918852736454388e6caacdc59154e2b8b2a89c (by decide +kernel)
private def pack_E6970Receipt41_chunk119 := witnessRule 41 43 96 800322 800453 32 1888
  0x1c02e00f 0xc0b9b12b1d182726255310c304e2c4ae75d8d44cc23b1a9988466355362eac6a862145d18d58e139b1aa9885272635738306e4c6a674611cd50e431a9837645236cc6a8621158d58d93ab2291c3746451310a6e6c8a6711c99148c42a38b22a1c (by decide +kernel)
private def pack_E6970Receipt41_chunk120 := witnessRule 41 43 128 800454 800646 32 1849
  0xffffd5a0 0x2b12a99841846156320a304c2b470e05dcdbb1291a04663543108ac6ac6c6158954e0c0ba312a1886 (by decide +kernel)
private def pack_E6970Receipt41_chunk121 := witnessRule 41 43 160 800704 800896 14 853
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk122 := witnessRule 41 42 0 810001 810074 32 2486
  0xffe01fff 0x7655106ccaa46c5d59544c428ba32a99c2736552310a4e4caa8711c99959baaa9b (by decide +kernel)
private def pack_E6970Receipt41_chunk123 := witnessRule 41 42 32 810075 810195 32 2132
  0xf00ffe03 0x10caa999548d8bb32a89c2756551084e8caa470dcd9544c429b932a99c4716552310aecaa26c5d9954420bab2a91c2746551310a4e6caa670dc99548c429b8b2aa1c (by decide +kernel)
private def pack_E6970Receipt41_chunk124 := witnessRule 41 42 64 810196 810322 32 1949
  0xe01fe03f 0x10c8a40dd9148c423322a1b1756453310a2e8c8aa70dd19544e239b2a884472655238ecaa26c5dd955ab22a9b2756551386e8caa210dcd9548e23932a89885 (by decide +kernel)
private def pack_E6970Receipt41_chunk125 := witnessRule 41 42 96 810323 810455 32 1808
  0x3007803 0x1856254320a308c4ac621460d8960e0c0b9312b98861817162593a702e2c2aa75d8d541bb1a919846645436ac6ac621118d60d8c0ba31aa1d182736353310c304e4c6aa7460dc58d50c433b228990476453362ecc8a462145d59150e13a322998852736455386e4c8a86214dc59158e0c238b2291d (by decide +kernel)
private def pack_E6970Receipt41_chunk126 := witnessRule 41 42 128 810456 810707 32 1825
  0xfffffffc 0x198d4ccc22b1aa9904 (by decide +kernel)
private def pack_E6970Receipt41_chunk127 := witnessRule 41 42 160 810708 810896 8 483
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk128 := witnessRule 41 41 0 820000 820074 32 2420
  0xffe07fff 0x199944d8bb332b46555364e8cca270dcd994421b933291c (by decide +kernel)
private def pack_E6970Receipt41_chunk129 := witnessRule 41 41 32 820075 820196 32 2052
  0xf80bfe05 0xecaa262119954cd8bab2a918851746554386e8ccac9c99554e23933289c5765236ecca999548c422b2aa1b27566562e6caaa70dcd9944e238b3291c (by decide +kernel)
private def pack_E6970Receipt41_chunk130 := witnessRule 41 41 64 820197 820324 32 1853
  0x780bf007 0x611d14cc42bb2a8988466553362eccaa4709d59544c4293a32a99c3736552310a6e4caa8711d554dc32a88376552362eccaa262145d5954ce13a32a918852736554388e6ccacdc59554e2b8b3289c (by decide +kernel)
private def pack_E6970Receipt41_chunk131 := witnessRule 41 41 96 820325 820458 32 1741
  0x80200e00 0xcc6a46a1158d50d020c2b1299a051846255330a306c4ae64146098964c429c130aa9885381615738702e2ac6215d8d44d4233229990456455310830ac6a862146118d58e0c0b9b1aa98861817263573a304e2c6ac6218609cd60e3b22a03764523208cc8a8621159158d8ba322a9885173645738304e6c8a67460dc99148c430c1b8b22a1d (by decide +kernel)
private def pack_E6970Receipt41_chunk132 := witnessRule 41 41 128 820512 820832 32 1812
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk133 := witnessRule 41 41 160 820833 820833 1 60
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk134 := witnessRule 41 40 0 830000 830074 32 2297
  0xffe01fff 0x7665106ccca46c5d59944c428ba33299c2736652310a4e4cca8711c99d59bb2a9b (by decide +kernel)
private def pack_E6970Receipt41_chunk135 := witnessRule 41 40 32 830075 830197 32 1963
  0xfc03ff01 0x10cca999948d8bb33289c2756651084e8cca470dcd9944c429b933299c4716652310aecca26c5d9994420bab3291c2746651310a4e6cca670dc99948c429b8b32a1c (by decide +kernel)
private def pack_E6970Receipt41_chunk136 := witnessRule 41 40 64 830198 830326 32 1766
  0x2e017c07 0x304e4c8a86218609c59158e941b9a8a19d7655306ecaa4621199550d8bab2a998851746555384e6caa862149c99558e0c1b932a91d184755338ecca26d9954cc422b2aa9b2756651386e8cca210dcd9948e23933289885 (by decide +kernel)
private def pack_E6970Receipt41_chunk137 := witnessRule 41 40 96 830327 830515 32 1691
  0xfaaa00c0 0x563533608308c4a86a146098960cc29c0b0ab19054814636cc8a4681159150cc20c2b1a999851846355320a306c6ae62146098d64e1c1312a9c381716254310c702e4ac71d9144d02332a99884565553630ac8a870605d1914cc430c0b9b22a9d (by decide +kernel)
private def pack_E6970Receipt41_chunk138 := witnessRule 41 40 128 830516 830832 26 1452
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk139 := witnessRule 41 39 0 840000 840075 32 2183
  0x7ff03fff 0x8e2cea47199d44d8bb33ab46655364e8cea270dcd9d4421b933a91c (by decide +kernel)
private def pack_E6970Receipt41_chunk140 := witnessRule 41 39 32 840076 840199 32 1870
  0x7f017f81 0x308e2cca275d9944c42333299b1756652310a2e8cca870dd19d5939332a9c472675138aeea46dd9d533329188456654364eaceac5cd9954e1b9b3a89c (by decide +kernel)
private def pack_E6970Receipt41_chunk141 := witnessRule 41 39 64 840200 840329 32 1684
  0x1c03f02 0x615914cc828c2322a9885183645738302e4c8ac6218605c59160e9c0b8b1aa1d3827353310aecaa266119994cdab2aa98844655736302e8caa674609cd9548c430c13932aa1d183716553310cecca40dd9948d8bb332898851756653384e8cca462149cd9950e1b8b32a9c (by decide +kernel)
private def pack_E6970Receipt41_chunk142 := witnessRule 41 39 96 840330 840519 32 1661
  0xffffe81c 0x2b2299a841846354340a306c6ac66146098d60c829c1312a19053816256310a704b06d99548cc22b2aa1904 (by decide +kernel)
private def pack_E6970Receipt41_chunk143 := witnessRule 41 39 128 840576 840832 19 1049
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk144 := witnessRule 41 38 0 850000 850075 32 2073
  0x7ff00fff 0x1b8b3aa1c7675106ccea46c5d59d44c428ba33a99c2736752310a4e4cea8711c9a159bbaa9b (by decide +kernel)
private def pack_E6970Receipt41_chunk145 := witnessRule 41 38 32 850076 850200 32 1779
  0x3f807fc0 0x183726651310c306e2cca675d9d441b33a91b1766751384eacea2109d19d48e1b9b3a898853726753388e2cea46215d9d44d8bb33a8841756752384e8cea262149cd9d4ce1b933a91885 (by decide +kernel)
private def pack_E6970Receipt41_chunk146 := witnessRule 41 38 64 850201 850331 32 1615
  0x3013c0 0x332a89a8456553340830ac8a468146119150cc28c1b22b19051826458310a704c6a86214e058d58e1c0b9aa9885382725143311cecaaa0d99948c822b32a18841856553310a308caaa70605cd9550c430c0b932ab1d182755738704e8a671d9944c8233329988456655362e8cca862145cd9958e0c139b3291d (by decide +kernel)
private def pack_E6970Receipt41_chunk147 := witnessRule 41 38 96 850384 850579 32 1639
  0xfffffd41 0xac8a46e106118d4cd828c131ab9a053826253340a702c4aa6614e095cc82240a8a29885 (by decide +kernel)
private def pack_E6970Receipt41_chunk148 := witnessRule 41 38 128 850580 850769 12 653
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk149 := witnessRule 41 37 0 860000 860076 32 1968
  0x5ff81fff 0x3736851388e2d0a4719a144d8bb342b46755364e8d0a270dcda14421b934291c (by decide +kernel)
private def pack_E6970Receipt41_chunk150 := witnessRule 41 37 32 860077 860202 32 1688
  0xbe02fe0 0x605d19948c430c0b9b32a1d182726653310c304e2ccaa74a0dd54508ebb3a8988466753362eacea462145d19d50e139b3a99885272675538306e4cea274611dd48e3b42a667523108acea86c9d5a158b9b3aa9c (by decide +kernel)
private def pack_E6970Receipt41_chunk151 := witnessRule 41 37 64 860203 860386 32 1560
  0xb50600f0 0x240a8a21985565523608308c8a66a14609915ccc29c131a999853816355320a706ae62112094514e333289a0456653330830acaa466146119550c828c1b2ab1885182655838704c8a870e05c5914cc431c0ba2a9c7665406ccea4621159d50d8c2b3299c (by decide +kernel)
private def pack_E6970Receipt41_chunk152 := witnessRule 41 37 96 860387 860642 32 1621
  0xfffffffa 0x6098d58d829c0b12a1a85 (by decide +kernel)
private def pack_E6970Receipt41_chunk153 := witnessRule 41 37 128 860643 860768 5 270
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk154 := witnessRule 41 36 0 870000 870076 32 1864
  0x1ff807ff 0x4e6d0a670dc9a148c429b8b42a1c7685106cd0a46c5d5a144c428ba34299c2736852310a4e4d0a8711c9a559bc2a9b (by decide +kernel)
private def pack_E6970Receipt41_chunk155 := witnessRule 41 36 32 870077 870203 32 1602
  0x3f00ff0 0x6159948c828c2332a1885183665638302e4ccaa6218605c5995ce9c0b8b2a99d7675306cd0a46d59d50c42233ab1b1817467523a304e6cea26218609c99d4ce8c1b8b3a9188676851362ecd0a2105d5a148e13a34289885 (by decide +kernel)
private def pack_E6970Receipt41_chunk156 := witnessRule 41 36 64 870204 870389 32 1520
  0xffd0f41c 0xc1322b1a853816354340a706ac66112094510c82a40b8a8a1990e1846553340a304caae6414e09914cc829c0b22a98853845736902e6a6623599d44cc22b3a99904 (by decide +kernel)
private def pack_E6970Receipt41_chunk157 := witnessRule 41 36 96 870390 870768 31 1557
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk158 := witnessRule 41 35 0 880000 880077 32 1762
  0x17fc0fff 0x5d1a14cc428b9b42a9c1827368513a306e2d0a4759a544d8bb34ab46855364e8d2a270dcda54421b934a91c (by decide +kernel)
private def pack_E6970Receipt41_chunk159 := witnessRule 41 35 32 880078 880205 32 1525
  0x803c0bf8 0xacea468106159944d028c2332999851836655320a304ccae6214e09954cc429c0b2aa9c3817554310a704e8a28462399a144c822b42998841856752310a308cea870605cd9d4cc430c0b933aa9d182775638ed0a40d9a148c422b42a1b (by decide +kernel)
private def pack_E6970Receipt41_chunk160 := witnessRule 41 35 64 880256 880392 32 1486
  0xffde9547 0x119548e421c0b1a99b054825143340ab02a664221559944dc20c232a91b051826556340a702c8a86614e1158c82241a8a21885 (by decide +kernel)
private def pack_E6970Receipt41_chunk161 := witnessRule 41 35 96 880448 880705 24 1185
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk162 := witnessRule 41 34 0 890000 890077 32 1662
  0x7fc03ff 0xc2b4291c181746851310c302e6d0a674609c9a148c430c138b42a1d7695106cd2a46c5d5a544c428ba34a99c2736952310a4e4d2a87060dc9a561bcaa9b (by decide +kernel)
private def pack_E6970Receipt41_chunk163 := witnessRule 41 34 32 890078 890257 32 1469
  0xf51e02fc 0x308cca46a146099958cc29c0b2aa1905385563108908a288719a1501ab42919841856751330a308cea6641460d9d54c428c133ab9c382665338702eca8719a544c422b4a99b (by decide +kernel)
private def pack_E6970Receipt41_chunk164 := witnessRule 41 34 64 890258 890450 32 1445
  0xffffeaf4 0x12094508d82ac0a1998c466523808702c8a66a1520d450ccc2ac129990c (by decide +kernel)
private def pack_E6970Receipt41_chunk165 := witnessRule 41 34 96 890451 890704 18 873
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk166 := witnessRule 41 33 0 900000 900078 32 1567
  0x1fe07ff 0x2b4a919041856851320a308d0a6621460da154e0c0b9342a18861817168563a702e2cea4759a944dab4a998844695536302e8d2a274609cda54428c13934a91d (by decide +kernel)
private def pack_E6970Receipt41_chunk167 := witnessRule 41 33 32 900079 900259 32 1413
  0x7fd3fa7e 0x4835142350a702caa66815211450cc82a40b9a8a1190e1826756320a702cca86214e1958db34a983 (by decide +kernel)
private def pack_E6970Receipt41_chunk168 := witnessRule 41 33 64 900260 900454 32 1423
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk169 := witnessRule 41 33 96 900512 900704 12 575
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk170 := witnessRule 41 32 0 910000 910078 32 1479
  0x40fe05ff 0x15a544d020c2342919851836854320a304d0ac6214e099d48c429c0b3aa1c3817753310acd4a40d5a948c420c2b4a89885184695338302e6d2a46218605c9a550e8c13caa9c (by decide +kernel)
private def pack_E6970Receipt41_chunk171 := witnessRule 41 32 32 910128 910261 32 1362
  0xf57be55f 0x2c0a8a1198886467513908306cca470152114508d02a34291b041846751360a304ceaa6814e05994ccc2a42a8a19885 (by decide +kernel)
private def pack_E6970Receipt41_chunk172 := witnessRule 41 32 64 910262 910515 32 1403
  0xfffffff7 0x1b3291d84 (by decide +kernel)
private def pack_E6970Receipt41_chunk173 := witnessRule 41 32 96 910516 910641 6 283
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk174 := witnessRule 41 31 0 920000 920128 32 1413
  0xdabf02ff 0x8d2a46a10609a154cc29c0b3a99905486514338ad4a26610615a54c20c234a919051836954310a304d2ac70e09a148e1c0bc299c (by decide +kernel)
private def pack_E6970Receipt41_chunk175 := witnessRule 41 31 32 920129 920263 32 1303
  0xffbfbdef 0x367523a08b04a284663460d9d48dc2a42a8a11985 (by decide +kernel)
private def pack_E6970Receipt41_chunk176 := witnessRule 41 31 64 920264 920640 32 1390
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk177 := witnessRule 41 30 0 930000 930129 32 1348
  0xffbffdff 0x12194508c829c0b4299885 (by decide +kernel)
private def pack_E6970Receipt41_chunk178 := witnessRule 41 30 32 930130 930265 32 1257
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk179 := witnessRule 41 30 64 930320 930640 27 1149
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk180 := witnessRule 41 29 0 940000 940130 32 1283
  0xf2ffa57f 0x369523808306d0a27014605a154d82a35289b041836952350a304d2a86814e05a148cc2a43a8a11885 (by decide +kernel)
private def pack_E6970Receipt41_chunk181 := witnessRule 41 29 32 940131 940322 32 1224
  0xfffbfebf 0x4cea47a10da144ec20c133a91d05 (by decide +kernel)
private def pack_E6970Receipt41_chunk182 := witnessRule 41 29 64 940323 940577 21 873
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk183 := witnessRule 41 28 0 950000 950131 32 1217
  0xfdffdbff 0x304d0a47214da948dc20c0b4aa9a85 (by decide +kernel)
private def pack_E6970Receipt41_chunk184 := witnessRule 41 28 32 950132 950324 32 1195
  0xffffffbf 0x134291e04 (by decide +kernel)
private def pack_E6970Receipt41_chunk185 := witnessRule 41 28 64 950325 950576 16 651
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk186 := witnessRule 41 27 0 960000 960132 32 1160
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk187 := witnessRule 41 27 32 960133 960384 32 1171
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk188 := witnessRule 41 27 64 960385 960576 11 440
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk189 := witnessRule 41 26 0 970000 970133 32 1106
  0xfd7fe5ff 0x134a89e8418168523c0a4d4a47410609a544e828c4aa9c04 (by decide +kernel)
private def pack_E6970Receipt41_chunk190 := witnessRule 41 26 32 970134 970387 32 1147
  0xfffffff7 0xb4291f84 (by decide +kernel)
private def pack_E6970Receipt41_chunk191 := witnessRule 41 26 64 970388 970513 6 235
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk192 := witnessRule 41 25 0 980000 980134 32 1057
  0xff7ffbff 0x5a548f820c0b4a91d85 (by decide +kernel)
private def pack_E6970Receipt41_chunk193 := witnessRule 41 25 32 980135 980450 32 1128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk194 := witnessRule 41 25 64 980512 980512 1 39
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk195 := witnessRule 41 24 0 990000 990135 32 1014
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk196 := witnessRule 41 24 32 990136 990512 29 997
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk197 := witnessRule 41 23 0 1000000 1000136 32 974
  0xffdff5ff 0x4a91a200c5a944fc20c4a91f04 (by decide +kernel)
private def pack_E6970Receipt41_chunk198 := witnessRule 41 23 32 1000192 1000449 24 801
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk199 := witnessRule 41 22 0 1010000 1010192 32 936
  0xfffffbff 0x14a468003 (by decide +kernel)
private def pack_E6970Receipt41_chunk200 := witnessRule 41 22 32 1010193 1010448 20 647
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk201 := witnessRule 41 21 0 1020000 1020194 32 904
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk202 := witnessRule 41 21 32 1020195 1020448 16 503
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk203 := witnessRule 41 20 0 1030000 1030195 32 871
  0xfffffdff 0x12a28269804 (by decide +kernel)
private def pack_E6970Receipt41_chunk204 := witnessRule 41 20 32 1030196 1030385 12 365
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk205 := witnessRule 41 19 0 1040000 1040197 32 841
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk206 := witnessRule 41 19 32 1040256 1040384 8 237
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk207 := witnessRule 41 18 0 1050000 1050257 32 813
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk208 := witnessRule 41 18 32 1050258 1050384 5 144
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk209 := witnessRule 41 17 0 1060000 1060320 32 788
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk210 := witnessRule 41 17 32 1060321 1060321 1 28
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk211 := witnessRule 41 16 0 1070000 1070320 30 708
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk212 := witnessRule 41 15 0 1080000 1080320 27 609
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk213 := witnessRule 41 14 0 1090000 1090257 24 513
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk214 := witnessRule 41 13 0 1100000 1100256 21 426
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk215 := witnessRule 41 12 0 1110000 1110256 19 365
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk216 := witnessRule 41 11 0 1120000 1120193 16 289
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk217 := witnessRule 41 10 0 1130000 1130192 14 237
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk218 := witnessRule 41 9 0 1140000 1140192 12 191
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk219 := witnessRule 41 8 0 1150000 1150129 10 147
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk220 := witnessRule 41 7 0 1160000 1160128 8 109
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk221 := witnessRule 41 6 0 1170000 1170128 7 88
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk222 := witnessRule 41 5 0 1180000 1180065 5 57
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk223 := witnessRule 41 4 0 1190000 1190064 4 41
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk224 := witnessRule 41 3 0 1200000 1200064 3 28
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk225 := witnessRule 41 2 0 1210000 1210001 2 16
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk226 := witnessRule 41 1 0 1220000 1220000 1 7
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt41_chunk227 := witnessRule 41 0 0 1230000 1230000 1 6
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt41_chunks : List (Chunk 41) := [pack_E6970Receipt41_chunk0, pack_E6970Receipt41_chunk1, pack_E6970Receipt41_chunk2, pack_E6970Receipt41_chunk3, pack_E6970Receipt41_chunk4, pack_E6970Receipt41_chunk5, pack_E6970Receipt41_chunk6, pack_E6970Receipt41_chunk7, pack_E6970Receipt41_chunk8, pack_E6970Receipt41_chunk9, pack_E6970Receipt41_chunk10, pack_E6970Receipt41_chunk11, pack_E6970Receipt41_chunk12, pack_E6970Receipt41_chunk13, pack_E6970Receipt41_chunk14, pack_E6970Receipt41_chunk15, pack_E6970Receipt41_chunk16, pack_E6970Receipt41_chunk17, pack_E6970Receipt41_chunk18, pack_E6970Receipt41_chunk19, pack_E6970Receipt41_chunk20, pack_E6970Receipt41_chunk21, pack_E6970Receipt41_chunk22, pack_E6970Receipt41_chunk23, pack_E6970Receipt41_chunk24, pack_E6970Receipt41_chunk25, pack_E6970Receipt41_chunk26, pack_E6970Receipt41_chunk27, pack_E6970Receipt41_chunk28, pack_E6970Receipt41_chunk29, pack_E6970Receipt41_chunk30, pack_E6970Receipt41_chunk31, pack_E6970Receipt41_chunk32, pack_E6970Receipt41_chunk33, pack_E6970Receipt41_chunk34, pack_E6970Receipt41_chunk35, pack_E6970Receipt41_chunk36, pack_E6970Receipt41_chunk37, pack_E6970Receipt41_chunk38, pack_E6970Receipt41_chunk39, pack_E6970Receipt41_chunk40, pack_E6970Receipt41_chunk41, pack_E6970Receipt41_chunk42, pack_E6970Receipt41_chunk43, pack_E6970Receipt41_chunk44, pack_E6970Receipt41_chunk45, pack_E6970Receipt41_chunk46, pack_E6970Receipt41_chunk47, pack_E6970Receipt41_chunk48, pack_E6970Receipt41_chunk49, pack_E6970Receipt41_chunk50, pack_E6970Receipt41_chunk51, pack_E6970Receipt41_chunk52, pack_E6970Receipt41_chunk53, pack_E6970Receipt41_chunk54, pack_E6970Receipt41_chunk55, pack_E6970Receipt41_chunk56, pack_E6970Receipt41_chunk57, pack_E6970Receipt41_chunk58, pack_E6970Receipt41_chunk59, pack_E6970Receipt41_chunk60, pack_E6970Receipt41_chunk61, pack_E6970Receipt41_chunk62, pack_E6970Receipt41_chunk63, pack_E6970Receipt41_chunk64, pack_E6970Receipt41_chunk65, pack_E6970Receipt41_chunk66, pack_E6970Receipt41_chunk67, pack_E6970Receipt41_chunk68, pack_E6970Receipt41_chunk69, pack_E6970Receipt41_chunk70, pack_E6970Receipt41_chunk71, pack_E6970Receipt41_chunk72, pack_E6970Receipt41_chunk73, pack_E6970Receipt41_chunk74, pack_E6970Receipt41_chunk75, pack_E6970Receipt41_chunk76, pack_E6970Receipt41_chunk77, pack_E6970Receipt41_chunk78, pack_E6970Receipt41_chunk79, pack_E6970Receipt41_chunk80, pack_E6970Receipt41_chunk81, pack_E6970Receipt41_chunk82, pack_E6970Receipt41_chunk83, pack_E6970Receipt41_chunk84, pack_E6970Receipt41_chunk85, pack_E6970Receipt41_chunk86, pack_E6970Receipt41_chunk87, pack_E6970Receipt41_chunk88, pack_E6970Receipt41_chunk89, pack_E6970Receipt41_chunk90, pack_E6970Receipt41_chunk91, pack_E6970Receipt41_chunk92, pack_E6970Receipt41_chunk93, pack_E6970Receipt41_chunk94, pack_E6970Receipt41_chunk95, pack_E6970Receipt41_chunk96, pack_E6970Receipt41_chunk97, pack_E6970Receipt41_chunk98, pack_E6970Receipt41_chunk99, pack_E6970Receipt41_chunk100, pack_E6970Receipt41_chunk101, pack_E6970Receipt41_chunk102, pack_E6970Receipt41_chunk103, pack_E6970Receipt41_chunk104, pack_E6970Receipt41_chunk105, pack_E6970Receipt41_chunk106, pack_E6970Receipt41_chunk107, pack_E6970Receipt41_chunk108, pack_E6970Receipt41_chunk109, pack_E6970Receipt41_chunk110, pack_E6970Receipt41_chunk111, pack_E6970Receipt41_chunk112, pack_E6970Receipt41_chunk113, pack_E6970Receipt41_chunk114, pack_E6970Receipt41_chunk115, pack_E6970Receipt41_chunk116, pack_E6970Receipt41_chunk117, pack_E6970Receipt41_chunk118, pack_E6970Receipt41_chunk119, pack_E6970Receipt41_chunk120, pack_E6970Receipt41_chunk121, pack_E6970Receipt41_chunk122, pack_E6970Receipt41_chunk123, pack_E6970Receipt41_chunk124, pack_E6970Receipt41_chunk125, pack_E6970Receipt41_chunk126, pack_E6970Receipt41_chunk127, pack_E6970Receipt41_chunk128, pack_E6970Receipt41_chunk129, pack_E6970Receipt41_chunk130, pack_E6970Receipt41_chunk131, pack_E6970Receipt41_chunk132, pack_E6970Receipt41_chunk133, pack_E6970Receipt41_chunk134, pack_E6970Receipt41_chunk135, pack_E6970Receipt41_chunk136, pack_E6970Receipt41_chunk137, pack_E6970Receipt41_chunk138, pack_E6970Receipt41_chunk139, pack_E6970Receipt41_chunk140, pack_E6970Receipt41_chunk141, pack_E6970Receipt41_chunk142, pack_E6970Receipt41_chunk143, pack_E6970Receipt41_chunk144, pack_E6970Receipt41_chunk145, pack_E6970Receipt41_chunk146, pack_E6970Receipt41_chunk147, pack_E6970Receipt41_chunk148, pack_E6970Receipt41_chunk149, pack_E6970Receipt41_chunk150, pack_E6970Receipt41_chunk151, pack_E6970Receipt41_chunk152, pack_E6970Receipt41_chunk153, pack_E6970Receipt41_chunk154, pack_E6970Receipt41_chunk155, pack_E6970Receipt41_chunk156, pack_E6970Receipt41_chunk157, pack_E6970Receipt41_chunk158, pack_E6970Receipt41_chunk159, pack_E6970Receipt41_chunk160, pack_E6970Receipt41_chunk161, pack_E6970Receipt41_chunk162, pack_E6970Receipt41_chunk163, pack_E6970Receipt41_chunk164, pack_E6970Receipt41_chunk165, pack_E6970Receipt41_chunk166, pack_E6970Receipt41_chunk167, pack_E6970Receipt41_chunk168, pack_E6970Receipt41_chunk169, pack_E6970Receipt41_chunk170, pack_E6970Receipt41_chunk171, pack_E6970Receipt41_chunk172, pack_E6970Receipt41_chunk173, pack_E6970Receipt41_chunk174, pack_E6970Receipt41_chunk175, pack_E6970Receipt41_chunk176, pack_E6970Receipt41_chunk177, pack_E6970Receipt41_chunk178, pack_E6970Receipt41_chunk179, pack_E6970Receipt41_chunk180, pack_E6970Receipt41_chunk181, pack_E6970Receipt41_chunk182, pack_E6970Receipt41_chunk183, pack_E6970Receipt41_chunk184, pack_E6970Receipt41_chunk185, pack_E6970Receipt41_chunk186, pack_E6970Receipt41_chunk187, pack_E6970Receipt41_chunk188, pack_E6970Receipt41_chunk189, pack_E6970Receipt41_chunk190, pack_E6970Receipt41_chunk191, pack_E6970Receipt41_chunk192, pack_E6970Receipt41_chunk193, pack_E6970Receipt41_chunk194, pack_E6970Receipt41_chunk195, pack_E6970Receipt41_chunk196, pack_E6970Receipt41_chunk197, pack_E6970Receipt41_chunk198, pack_E6970Receipt41_chunk199, pack_E6970Receipt41_chunk200, pack_E6970Receipt41_chunk201, pack_E6970Receipt41_chunk202, pack_E6970Receipt41_chunk203, pack_E6970Receipt41_chunk204, pack_E6970Receipt41_chunk205, pack_E6970Receipt41_chunk206, pack_E6970Receipt41_chunk207, pack_E6970Receipt41_chunk208, pack_E6970Receipt41_chunk209, pack_E6970Receipt41_chunk210, pack_E6970Receipt41_chunk211, pack_E6970Receipt41_chunk212, pack_E6970Receipt41_chunk213, pack_E6970Receipt41_chunk214, pack_E6970Receipt41_chunk215, pack_E6970Receipt41_chunk216, pack_E6970Receipt41_chunk217, pack_E6970Receipt41_chunk218, pack_E6970Receipt41_chunk219, pack_E6970Receipt41_chunk220, pack_E6970Receipt41_chunk221, pack_E6970Receipt41_chunk222, pack_E6970Receipt41_chunk223, pack_E6970Receipt41_chunk224, pack_E6970Receipt41_chunk225, pack_E6970Receipt41_chunk226, pack_E6970Receipt41_chunk227]
def rows41 := rowsFrom pack_E6970Receipt41_chunks
theorem good41 : ∀ r ∈ rows41, good 41 r = true := rowsFrom_good pack_E6970Receipt41_chunks
theorem sorted41 : rows41.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt41_chunks 0 (by decide +kernel)).1
theorem mass41 (i : Fin 61) :
    bandCount 41 (i.val : ℤ) 60 16 ≤ (rows41.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt41_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 41 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt41_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total41 : (rows41.map (price 41)).sum = 421016 :=
  (total_eq pack_E6970Receipt41_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt41

section Pack_E6970Receipt42

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt42_chunk0 := witnessA6966Final 42 60 0 660018 660147 32 3466
  0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk1 := witnessA6966Final 42 60 32 660148 660275 32 3386
  0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk2 := witnessA6966Final 42 60 64 660276 660401 32 3352
  0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk3 := witnessA6966Final 42 60 96 660402 660525 32 3340
  0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk4 := witnessA6966Final 42 60 128 660526 660649 32 3286
  0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk5 := witnessA6966Final 42 60 160 660650 660779 32 3109
  0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk6 := witnessA6966Final 42 60 192 660780 661025 32 2978
  0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk7 := witnessRule 42 60 224 661026 661030 5 445
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk8 := witnessRule 42 59 0 670017 670145 32 3295
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk9 := witnessRule 42 59 32 670146 670272 32 3228
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk10 := witnessRule 42 59 64 670273 670397 32 3201
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk11 := witnessRule 42 59 96 670398 670520 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk12 := witnessRule 42 59 128 670521 670645 32 3095
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk13 := witnessRule 42 59 160 670646 670776 32 2967
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk14 := witnessRule 42 59 192 670777 671024 32 2848
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk15 := witnessRule 42 59 224 671025 671029 5 435
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk16 := witnessRule 42 58 0 680016 680143 32 3167
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk17 := witnessRule 42 58 32 680144 680269 32 3103
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk18 := witnessRule 42 58 64 680270 680393 32 3079
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk19 := witnessRule 42 58 96 680394 680515 32 3053
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk20 := witnessRule 42 58 128 680516 680641 32 2949
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk21 := witnessRule 42 58 160 680642 680773 32 2866
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk22 := witnessRule 42 58 192 680774 680966 32 2748
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk23 := witnessRule 42 58 224 681024 681029 6 509
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk24 := witnessRule 42 57 0 690015 690141 32 3081
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk25 := witnessRule 42 57 32 690142 690266 32 3010
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk26 := witnessRule 42 57 64 690267 690389 32 2985
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk27 := witnessRule 42 57 96 690390 690466 32 2910
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk28 := witnessRule 42 57 128 690512 690590 32 2869
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk29 := witnessRule 42 57 160 690591 690771 32 2767
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk30 := witnessRule 42 57 192 690772 690966 32 2661
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk31 := witnessRule 42 57 224 691024 691028 5 412
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk32 := witnessRule 42 56 0 700014 700139 32 3008
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk33 := witnessRule 42 56 32 700140 700263 32 2938
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk34 := witnessRule 42 56 64 700264 700340 32 2866
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk35 := witnessRule 42 56 96 700386 700461 32 2922
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk36 := witnessRule 42 56 128 700462 700586 32 2752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk37 := witnessRule 42 56 160 700587 700769 32 2658
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk38 := witnessRule 42 56 192 700770 700965 32 2584
  0xffbfffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt42_chunk39 := witnessRule 42 56 224 701024 701028 5 401
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk40 := witnessRule 42 55 0 710013 710137 32 2929
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk41 := witnessRule 42 55 32 710138 710215 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk42 := witnessRule 42 55 64 710261 710337 32 2872
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk43 := witnessRule 42 55 96 710338 710458 32 2824
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk44 := witnessRule 42 55 128 710459 710584 32 2645
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk45 := witnessRule 42 55 160 710585 710768 32 2559
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk46 := witnessRule 42 55 192 710769 711024 32 2512
  0xffdfbfff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt42_chunk47 := witnessRule 42 55 224 711025 711027 3 234
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk48 := witnessRule 42 54 0 720012 720089 32 2845
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk49 := witnessRule 42 54 32 720136 720212 32 2833
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk50 := witnessRule 42 54 64 720213 720333 32 2820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk51 := witnessRule 42 54 96 720334 720454 32 2735
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk52 := witnessRule 42 54 128 720455 720581 32 2551
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk53 := witnessRule 42 54 160 720582 720714 32 2474
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk54 := witnessRule 42 54 192 720768 721025 32 2442
  0xffef9fb7 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt42_chunk55 := witnessRule 42 54 224 721026 721027 2 155
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk56 := witnessRule 42 53 0 730011 730088 32 2805
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk57 := witnessRule 42 53 32 730089 730210 32 2791
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk58 := witnessRule 42 53 64 730211 730330 32 2775
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk59 := witnessRule 42 53 96 730331 730452 32 2617
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk60 := witnessRule 42 53 128 730453 730580 32 2460
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk61 := witnessRule 42 53 160 730581 730714 32 2398
  0xedffffff 0x5cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt42_chunk62 := witnessRule 42 53 192 730768 731026 31 2305
  0x7ffbe7cb 0x5d8d0b8b29b27164362e4c86c9c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt42_chunk63 := witnessRule 42 52 0 740010 740086 32 2772
  0xfafffaff 0x4716336ce288dc98cda3a1a (by decide +kernel)
private def pack_E6970Receipt42_chunk64 := witnessRule 42 52 32 740087 740207 32 2755
  0xfffff9ff 0x15ccd338a2 (by decide +kernel)
private def pack_E6970Receipt42_chunk65 := witnessRule 42 52 64 740208 740326 32 2732
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk66 := witnessRule 42 52 96 740327 740449 32 2507
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk67 := witnessRule 42 52 128 740450 740578 32 2389
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk68 := witnessRule 42 52 160 740579 740713 32 2329
  0xe4fb6fff 0x2e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt42_chunk69 := witnessRule 42 52 192 740768 741026 29 2103
  0x1ffef3e1 0x2ee685c598d938b29b17265364e4c86cdc58cc421ba9a (by decide +kernel)
private def pack_E6970Receipt42_chunk70 := witnessRule 42 51 0 750009 750085 32 2743
  0x54ff557f 0x5d58cd939b21b3716536ce2a20d9c493319a17464364e4ca6d5c58544233892 (by decide +kernel)
private def pack_E6970Receipt42_chunk71 := witnessRule 42 51 32 750086 750205 32 2725
  0x5ffeafff 0x238b21b67141364e8c66cdc990da3a9a (by decide +kernel)
private def pack_E6970Receipt42_chunk72 := witnessRule 42 51 64 750206 750324 32 2644
  0xfff5fffd 0x8e4c66d5d0d1b9b19b (by decide +kernel)
private def pack_E6970Receipt42_chunk73 := witnessRule 42 51 96 750325 750448 32 2421
  0xffe7ffeb 0x67334ee2895c58cdbb8a2 (by decide +kernel)
private def pack_E6970Receipt42_chunk74 := witnessRule 42 51 128 750449 750578 32 2319
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk75 := witnessRule 42 51 160 750579 750768 32 2260
  0x783c97b6 0xdd8d0b9b29b27364366e4c66210dc594da38b21b17464364e8c66cdc990da39319b574342eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt42_chunk76 := witnessRule 42 51 192 750769 751025 25 1769
  0x1fffef8 0x17167362e4cc6c9c994d9b8b21884 (by decide +kernel)
private def pack_E6970Receipt42_chunk77 := witnessRule 42 50 0 760008 760083 32 2714
  0x43fea0ff 0x3746151088e4c2a262151c5854ce2b8a918846715146cc2a46c9d5854421b9b0a898853726153388e2c2a462151c550db392a (by decide +kernel)
private def pack_E6970Receipt42_chunk78 := witnessRule 42 50 32 760084 760202 32 2693
  0xffaa8ffd 0x86154cc8685d194da39b0a8845716151310aae2a66d9c912b29a (by decide +kernel)
private def pack_E6970Receipt42_chunk79 := witnessRule 42 50 64 760203 760321 32 2539
  0xfaabfeaa 0x5d98cd93a321b3726536ce2c2a211dc493b19a17564364e6ca6d5c985442338a89884 (by decide +kernel)
private def pack_E6970Receipt42_chunk80 := witnessRule 42 50 96 760322 760399 32 2377
  0xfabff54f 0x37463368e4c86d5d4d13ab19b37364368e2ca6ddc5441bb892 (by decide +kernel)
private def pack_E6970Receipt42_chunk81 := witnessRule 42 50 128 760400 760577 32 2254
  0x7b69feaf 0x338b19b17663366e8c66d5c98cdb3a1a871148e6c66d5c590dbb8a09b (by decide +kernel)
private def pack_E6970Receipt42_chunk82 := witnessRule 42 50 160 760578 760769 32 2195
  0x3c1e0392 0x4e2cc62109e0d0b9b31b27365366e4c86210dc598da3a988317465364e8c86cdcd8cc421b9329b4726436ae2c662115d4d0bab21b27563366e6c86d1cd8cdab8b21b (by decide +kernel)
private def pack_E6970Receipt42_chunk83 := witnessRule 42 50 192 760770 761025 22 1524
  0x3ffffe 0xb9339b (by decide +kernel)
private def pack_E6970Receipt42_chunk84 := witnessRule 42 49 0 770007 770082 32 2688
  0x7fc05ff 0x139b0aa1c47362566e2c2aa715c58944e3392883761513108cc2a66c5d58548c428ba30aa1c37462564e4c2aa711c98944e2b9291b (by decide +kernel)
private def pack_E6970Receipt42_chunk85 := witnessRule 42 49 32 770083 770200 32 2663
  0xffa03fe8 0x1776151084eac2a262149d1854ce1b9b0a91885372615438ae4c4ad1c554db39289b86151062ecc2a262145d5854ce13a30a91885 (by decide +kernel)
private def pack_E6970Receipt42_chunk86 := witnessRule 42 49 64 770201 770320 32 2421
  0xea0ffa81 0xcca68dd585442239b0a89885472615338ae2c2a462155c550dbb92a76152364ecc2a210dd18544c429b9b0a99c4726152310a8e2c2a8719c5895b38a8a09c (by decide +kernel)
private def pack_E6970Receipt42_chunk87 := witnessRule 42 49 96 770321 770398 32 2314
  0x551eaa1f 0x10c6685d990d93a329b573615108ce2c2a262159c54cdbb92296154ec8685d594da3a30a8845726151310aae2c2a6719c548c423b8a8a3 (by decide +kernel)
private def pack_E6970Receipt42_chunk88 := witnessRule 42 49 128 770399 770578 32 2183
  0x1c83e8af 0x572633108ae2ca6d9d0c418bb321b27663366e8c86d1cd8cc42239329b571643108aec685dd8cd93ab21b3746331086e6ca6d9c9854423b8a89884 (by decide +kernel)
private def pack_E6970Receipt42_chunk89 := witnessRule 42 49 160 770579 770771 32 2129
  0xef8781e0 0x17a342e6ce6c9c998c42138b41b37731062e8cc6c9d194d9b9b2188437266368e2ca62111dcd0bab29b27564366e8c66210dcd94da39b21b (by decide +kernel)
private def pack_E6970Receipt42_chunk90 := witnessRule 42 49 192 770772 771024 17 1157
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk91 := witnessRule 42 48 0 780006 780080 32 2662
  0xff801ff 0x11c98944c42a38b1299c572523108ce4a28e1895331291b1766251384eac4a2109d18948e1b9b12898853726253388e2c4a462151c950db39aa (by decide +kernel)
private def pack_E6970Receipt42_chunk92 := witnessRule 42 48 32 780081 780197 32 2609
  0xfc007fc0 0x4312a761523108cc2a86c9d98958ba30aa9c3746251388e6c4a2111c98948e2b8b12898855725336ce2a48dd8944d8bbb12b56155364eac4a270dd1894421b9b1291c (by decide +kernel)
private def pack_E6970Receipt42_chunk93 := witnessRule 42 48 64 780198 780273 32 2341
  0x801fc007 0xbbb0a898851766153384eac2a462149d18550e23a312b372615538ae4c4a2719c589442339291b77141270c2a26211d854cd8bb30a918851756154386eac4ac9cd8554e239b1289c572625108ae2c4a4719c944c423b8a893 (by decide +kernel)
private def pack_E6970Receipt42_chunk94 := witnessRule 42 48 96 780274 780397 32 2254
  0xa03e803e 0x4eec2a210dd58544c429ba30a99c4736152310a8e4c2a8719c9895ab8aa9b77251362f0c2a2109d98544c4293ab0a99c3746152310a6e6c2a8715cd895a38b0aa9c671625138ee4a20ddc5049cb0a883 (by decide +kernel)
private def pack_E6970Receipt42_chunk95 := witnessRule 42 48 128 780398 780578 32 2113
  0x1c008406 0x2393298844716736aec620c5dd8cc420bb329b2756431084e8cc6cdcd94c421b9339b572615338ce2c2a462159c550dc390a8633106eca685d990c420bab31b4746151310a8e6c2a6715c98548c42ab8b0aa1c671533108ee2a28271dc5049c30a91b (by decide +kernel)
private def pack_E6970Receipt42_chunk96 := witnessRule 42 48 160 780579 780773 32 2072
  0xfff7e0f0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b (by decide +kernel)
private def pack_E6970Receipt42_chunk97 := witnessRule 42 48 192 780774 781024 13 872
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk98 := witnessRule 42 47 0 790005 790079 32 2640
  0x1ff80bff 0x6e2c4aa715c58d44e339a883762513108cc4a66c5d58948c428ba312a1c37463564e4c4aa711c98d44e2b9a91b (by decide +kernel)
private def pack_E6970Receipt42_chunk99 := witnessRule 42 47 32 790080 790196 32 2527
  0xf801ff80 0x431289b1776251082ecc4a4709d58944c4293a31299c3736252310a6e4c4a8715c98d5a392a9b67351370c4a20dd8948d8bb312898851756253384e8c4a462149cd8950e239b1ab (by decide +kernel)
private def pack_E6970Receipt42_chunk100 := witnessRule 42 47 64 790197 790272 32 2265
  0x3f800f 0xbc312b66155364ecc4a270dd5894421ba31291c4736251310a8e4c4a6715c58948c42ab92a1b773552c4a9d8948d8bbb1289c2766251084eac4a470dd18944c429b9b1299c4726252310a8e2c4a8719c58d5b3928a09c (by decide +kernel)
private def pack_E6970Receipt42_chunk101 := witnessRule 42 47 96 790273 790397 32 2167
  0x1c003e 0x86153362eec2a462145d98550e13ab0a998852746155388e8c4a2715cd894422b931291c6716251310ace4a66ddc5491cb12a861523108ec2a86c9dd8958bab0aa9c3756251388e8c4a2111cd8948e2b931289885571625338ce4a46211dc9451c31289b (by decide +kernel)
private def pack_E6970Receipt42_chunk102 := witnessRule 42 47 128 790398 790580 32 2046
  0x6006002 0x4e8cc62109cda0d9b933988437169368f0620dd94c41b339a1756631082e8d06cdd18550e239b0a99885472615538ae2c2a862155c558d8c339188c76154362eec2a6709d98548c4293ab0aa1c3746153310a6e6c2aa711c98550c42a38b0ab1c671625238ee4a262121c4845cb0a89884 (by decide +kernel)
private def pack_E6970Receipt42_chunk103 := witnessRule 42 47 160 790581 790834 32 2029
  0xfffffe3e 0x1726a364e2d262109ecd0bab39b (by decide +kernel)
private def pack_E6970Receipt42_chunk104 := witnessRule 42 47 192 790835 790961 7 463
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk105 := witnessRule 42 46 0 800004 800077 32 2616
  0xfff00fff 0x86354cc6a46c5d98d44e13ab1a8842746352386e6c6a26214dc98d4ce238b1a91885 (by decide +kernel)
private def pack_E6970Receipt42_chunk106 := witnessRule 42 46 32 800078 800194 32 2427
  0xe01fff01 0x10c6a9d8948c423312a1b27663562e8c4aa70dd18d44e239b1a884472635238ec6a26c5dd8d5ab12a9b2756351386e8c6a210dcd8d48e23931a89885 (by decide +kernel)
private def pack_E6970Receipt42_chunk107 := witnessRule 42 46 64 800195 800271 32 2223
  0x17f017f 0x1776251310a2ecc4a6709d58948c4293a312a1c47463566e4c4aa715c98d44e339a91b862513108ec4a66c5d98948c428bab12a1c37563564e6c4aa711cd8d44e2b8b1a91c (by decide +kernel)
private def pack_E6970Receipt42_chunk108 := witnessRule 42 46 96 800272 800397 32 2083
  0x9c007c 0x10c4a46dd8550c42330ab1b2766252386eac4a26214dd1894ce239b1291885472625438ae4aa6ddcd44dcb1289b1786251082eec4a4709d98944c4293ab1299c3746252310a6e6c4a8715cd8d5a38b12a9c671635138ee6a20e589441c31291b (by decide +kernel)
private def pack_E6970Receipt42_chunk109 := witnessRule 42 46 128 800398 800581 32 1980
  0xc3802003 0x1736a364e4d262109c5acd9bd188366156362ecc2aa709d58550c4293a30ab1c3736155310a6e4c2ae711c58558c42a38ac1b28474370c2a66211d8554d8bb30aa18851756156384e8c2aa62149cd855ce239b1299c5726252310aae2c4a8719c94cc423b8a8a0988d (by decide +kernel)
private def pack_E6970Receipt42_chunk110 := witnessRule 42 46 160 800582 800897 32 1997
  0xffffffef 0xbe9a (by decide +kernel)
private def pack_E6970Receipt42_chunk111 := witnessRule 42 46 192 800898 800960 2 131
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk112 := witnessRule 42 45 0 810003 810076 32 2598
  0x7ff017ff 0x33a2883763513108cc6a66c5d58d48c428ba31aa1c37464564e4c6aa711c99144e2ba291b (by decide +kernel)
private def pack_E6970Receipt42_chunk113 := witnessRule 42 45 32 810077 810194 32 2321
  0xe007fe00 0x10c6a26c5dd8d4420bb31a91c2756351310a4e8c6a670dcd8d48c429b931aa1c57264568e6aa6d9d144dc31a88376352362ecc6a262145d58d4ce13a31a918852736354388e6c8acdc58d54e2b8b2289c (by decide +kernel)
private def pack_E6970Receipt42_chunk114 := witnessRule 42 45 64 810195 810271 32 2129
  0x3f001f 0xbc31ab66255364ecc6a270dd58d4421ba31a91c4736351310a8e4c6a6715c58d48c42ab9aa1b774552c6a9d8d48d8bbb1a89c2766351084eac6a470dd18d44c429b9b1a99c4726352310a8e2c6a8719c5915b39a8a09c (by decide +kernel)
private def pack_E6970Receipt42_chunk115 := witnessRule 42 45 96 810272 810448 32 2009
  0x8006001e 0x43128990486253362eec4a462145d98950e13ab12998852746255386e6c4a86214dc98958e2b931a91c6716351310ace6a66ddc5490464b12903862523108ec4a86c5d9894cc428bab12a9c3756351388e8c6a2111cd8d48e2b931a89885571635338ce6a46211dcd451c31a89b (by decide +kernel)
private def pack_E6970Receipt42_chunk116 := witnessRule 42 45 128 810449 810584 32 1911
  0xfee10c00 0x2e2da6dd8554c42330ab9b1756156310a2e8c2b0709c98564e14139329c2837164310a506ec6dd8950db30ab188456158364eac4a870dd1894cc429b9b12a9c4726254310a8e2c4ac715c954c420c2b8a8a19d (by decide +kernel)
private def pack_E6970Receipt42_chunk117 := witnessRule 42 45 160 810585 810960 28 1725
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk118 := witnessRule 42 44 0 820002 820074 32 2576
  0xffe01fff 0x86454cc8a46c5d99144e13ab228842746452386e6c8a26214dc9914ce238b2291885 (by decide +kernel)
private def pack_E6970Receipt42_chunk119 := witnessRule 42 44 32 820075 820193 32 2203
  0xc03ffc07 0x10c8a9d8d48c42331aa1b27664562e8c6aa70dd19144e239b22884472645238ec8a26c5dd915ab1aa9b2756451386e8c8a210dcd9148e23932289885 (by decide +kernel)
private def pack_E6970Receipt42_chunk120 := witnessRule 42 44 64 820194 820271 32 2065
  0xbf017f 0x431a91b1776351310a2ecc6a6709d58d48c4293a31aa1c47464566e4c6aa715c99144e33a291b863513108ec6a66c5d98d48c428bab1aa1c37564564e6c6aa711cd9144e2b8b2291c (by decide +kernel)
private def pack_E6970Receipt42_chunk121 := witnessRule 42 44 96 820272 820449 32 1934
  0x6003011e 0x508e2a6621618948c823b12a188466256362eac4aa62145d1895ce1ba31a99c4736352310a8e4c6a8715c58d4cc42ab9aa9b1867251311b0c6a26211d8d4cd8bbb1a91c2766351310a4eac6a670dd18d48c429b9b1aa1c471635538ce2c8a271dd1441cb1a883 (by decide +kernel)
private def pack_E6970Receipt42_chunk122 := witnessRule 42 44 128 820450 820641 32 1856
  0xfffd6200 0x198558c82230ad1b281726738504e2cc6214a09e0dbb129990476255362ecc4a862145d58958e13a312a98852736257386e4c4ac6214dc58960e141b8b0aa1d (by decide +kernel)
private def pack_E6970Receipt42_chunk123 := witnessRule 42 44 160 820642 820897 22 1332
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk124 := witnessRule 42 43 0 830001 830074 32 2504
  0xffe02fff 0x764513108cc8a66c5d59148c428ba322a1c37465564e4c8aa711c99544e2baa91b (by decide +kernel)
private def pack_E6970Receipt42_chunk125 := witnessRule 42 43 32 830075 830194 32 2131
  0xe00ffc01 0x219144d8bbb228841766452384eac8a262149d1914ce1b9b2291885372645438ae4caad1d154dc32288376452362ecc8a262145d5914ce13a322918852736454388e6caacdc59154e2b8b2a89c (by decide +kernel)
private def pack_E6970Receipt42_chunk126 := witnessRule 42 43 64 830195 830320 32 1966
  0x803f803f 0x219144dbb1a9988466355364ecc8a270dd5914421ba32291c4736451310a8e4c8a6715c59148c42cb22a76452362eec8a2709d99144213ab2291c3746451310a6e6c8a6711c99148c42a38b22a1c (by decide +kernel)
private def pack_E6970Receipt42_chunk127 := witnessRule 42 43 96 830321 830452 32 1847
  0x1804c00f 0x502e6c2aa74a09c98550c4314138b0ab1d862513408ec6a6621198d54d8bb31aa1c2756353310a4e8c6aa70dcd8d50c429b931ab1c4735736508e4a67218d4c1c31a9188476354362ecc6a662145d58d54e13a31aa18852736356388e6c8a4715c99144c42ab8b2299c (by decide +kernel)
private def pack_E6970Receipt42_chunk128 := witnessRule 42 43 128 830453 830645 32 1815
  0xffffff60 0xa05e8dbb12a1904662563108ac4b06c5d1895cc428b9b12c9c (by decide +kernel)
private def pack_E6970Receipt42_chunk129 := witnessRule 42 43 160 830646 830896 15 897
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk130 := witnessRule 42 42 0 840000 840073 32 2432
  0xffc03fff 0x86554ccaa46c5d99544e13ab2a8842746552386e6caa26214dc9954ce238b2a91885 (by decide +kernel)
private def pack_E6970Receipt42_chunk131 := witnessRule 42 42 32 840074 840194 32 2043
  0xe01ffc07 0x10caa9d9148c423322a1b27665562e8c8aa70dd19544e239b2a884472655238ecaa26c5dd955ab22a9b2756551386e8caa210dcd9548e23932a89885 (by decide +kernel)
private def pack_E6970Receipt42_chunk132 := witnessRule 42 42 64 840195 840321 32 1889
  0xc017c05f 0x2191481c32291b1776451310a2ecc8a6709d59148c4293a322a1c3736453310a6e4c8aa715c99544e33aa91b864513108ec8a66c5d99148c428bab22a1c37565564e6c8aa711cd9544e2b8b2a91c (by decide +kernel)
private def pack_E6970Receipt42_chunk133 := witnessRule 42 42 96 840322 840454 32 1768
  0x700b007 0x8c4b26210a118554c42941b0ab9c281726156310c502e2c2b075d8d48cc23b1aa188466356362eac6aa62145d18d5ce139b1ab1885272635838504e4c4a874a0dc954e431a899847645336cc6aa621158d5cd93ab2299c3746452310a6e6c8a8711c9914cc42a38b22a9c (by decide +kernel)
private def pack_E6970Receipt42_chunk134 := witnessRule 42 42 128 840455 840706 32 1789
  0xfffffff8 0xec4a6681198954cc22b12b9904 (by decide +kernel)
private def pack_E6970Receipt42_chunk135 := witnessRule 42 42 160 840707 840896 9 533
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk136 := witnessRule 42 41 0 850000 850074 32 2310
  0xffe02fff 0x765513108ccaa66c5d59548c428ba32aa1c37466564e4caaa711c99944e2bb291b (by decide +kernel)
private def pack_E6970Receipt42_chunk137 := witnessRule 42 41 32 850075 850196 32 1973
  0xf803fe00 0x219544d8bbb2a8841766552384eacaa262149d1954ce1b9b2a91885372655438ae4ccad1d554dc32a88376552362eccaa262145d5954ce13a32a918852736554388e6ccacdc59554e2b8b3289c (by decide +kernel)
private def pack_E6970Receipt42_chunk138 := witnessRule 42 41 64 850197 850324 32 1788
  0x7803f007 0x506e2c6a67619144c823b229988466455362eac8a862145d19158e1ba32a91c4736551310a8e4caa6715c59548c42c32a88376552362eecaa2709d99544213ab2a91c3746551310a6e6caa6711c99548c42a38b2aa1c (by decide +kernel)
private def pack_E6970Receipt42_chunk139 := witnessRule 42 41 96 850325 850458 32 1699
  0xd5600e00 0x198950d422312c19842836156320a502c2b471d8d44d423b1a99984663553208ac6ae621118d64d942312a9c281736254310c502e4c4ac74a09c58954c43431aa83764523208ec8a86c5d9914cc428bab22a9c2746454310a4e6c8ac70dc99154c429b8b22b9c (by decide +kernel)
private def pack_E6970Receipt42_chunk140 := witnessRule 42 41 128 850512 850832 32 1780
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk141 := witnessRule 42 41 160 850833 850833 1 59
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk142 := witnessRule 42 40 0 860000 860074 32 2192
  0xffe01fff 0x86654ccca46c5d99944e13ab328842746652386e6cca26214dc9994ce238b3291885 (by decide +kernel)
private def pack_E6970Receipt42_chunk143 := witnessRule 42 40 32 860075 860197 32 1883
  0xfc03ff01 0x10cca9d9548c42332aa1b27666562e8caaa70dd19944e239b32884472665238ecca26c5dd995ab2aa9b2756651386e8cca210dcd9948e23933289885 (by decide +kernel)
private def pack_E6970Receipt42_chunk144 := witnessRule 42 40 64 860198 860326 32 1708
  0xe017c05 0x140b9b1aa1d282726353310c504e2c6aa74a0dcd50c42c322a03765523108ccaa86c5d9954ce13ab2a918852746554386e6caa66214dc99554e23aab1b865513108ecaa66c5d99548c428bab2aa1c2746553310a4e6caaa711cd9944e2b8b3291c (by decide +kernel)
private def pack_E6970Receipt42_chunk145 := witnessRule 42 40 96 860327 860515 32 1655
  0xfffe00c0 0xec6a46a1198d50d022b1ab1984463583208508c4a86414a0d8958c42941312c1c281716257310c502e4b271d9144d023b2299904664553108ac8ae6c5d19158c428b9b22c1c (by decide +kernel)
private def pack_E6970Receipt42_chunk146 := witnessRule 42 40 128 860516 860832 26 1426
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk147 := witnessRule 42 39 0 870000 870075 32 2084
  0x3ff017ff 0xdc59954e2b8b3a89c766513108ccca66c5d59948c428ba332a1c37467564e4ccaa711c99d44e2bba91b (by decide +kernel)
private def pack_E6970Receipt42_chunk148 := witnessRule 42 39 32 870076 870199 32 1793
  0x7f007f80 0x238b32a1c86651362eecca2105d99948e13ab32898852746653386e6cca46214dc99950e2b933ab47655370cca20dd9948d8bb332898851756653384e8cca462149cd9950e239b3ab (by decide +kernel)
private def pack_E6970Receipt42_chunk149 := witnessRule 42 39 64 870200 870329 32 1630
  0xc02f00 0x2b22b1904464583108508c6a86214a0d8d58e140b931aa98862817163573a504e6ac6214e09c94510ebb2a89984765533108ccaaa6c5d59550c428ba32ab1c2736555310a4e4caae70a09c9914ce941ba2a1c8655306ecca46d99550c422b2ab1b2756652386e8cca26214dcd994ce23933291885 (by decide +kernel)
private def pack_E6970Receipt42_chunk150 := witnessRule 42 39 96 870330 870519 32 1626
  0xffffe80c 0x198d4cd82231ab9a042846253340a506c4aa6614a09895cc82940b12c98854816155310a902ae6dd9148d023322a1984 (by decide +kernel)
private def pack_E6970Receipt42_chunk151 := witnessRule 42 39 128 870576 870832 19 1030
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk152 := witnessRule 42 38 0 880000 880075 32 1978
  0x7ff00fff 0x23933a8988586754ccea46c5d99d44e13ab3a8842746752386e6cea26214dc99d4ce238b3a91885 (by decide +kernel)
private def pack_E6970Receipt42_chunk153 := witnessRule 42 38 32 880076 880200 32 1705
  0x1f807fc0 0x1b9332a1885371665638506e2caa476199481bb329188466654362eacca662145d19954e1ba33a89c4736751088e4cea471d9d44d8bbb3ab56655364eacea270dd19d4421b9b3a91c (by decide +kernel)
private def pack_E6970Receipt42_chunk154 := witnessRule 42 38 64 880201 880331 32 1564
  0x3003c0 0x1d9144d82332299a845645534088c8ae6610a118d4ccc2941b1aa99052826357310a502c6b2712058954e240b92a18857655506ecaa4661199550c822b2ab18844655836508c8a870a05cd914cc43140b9322a9d282716454310c504e8ac71d9944c823b3299b1766652310a2eacca8709d1994cc42939b32a9c (by decide +kernel)
private def pack_E6970Receipt42_chunk155 := witnessRule 42 38 96 880384 880579 32 1605
  0xfffffd55 0x331a91c04463563608506c4a86a14a058960cc2a40ab1904 (by decide +kernel)
private def pack_E6970Receipt42_chunk156 := witnessRule 42 38 128 880580 880769 12 641
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk157 := witnessRule 42 37 0 890000 890076 32 1876
  0xff80bff 0x2736754388e6d0acdc59d54e2b8b4289c767513108ccea66c5d59d48c428ba33aa1c37468564e4ceaa711c9a144e2bc291b (by decide +kernel)
private def pack_E6970Receipt42_chunk158 := witnessRule 42 37 32 890077 890202 32 1618
  0x3e02fe0 0x2e8ccaa62145cd995ce140b9b2a99d282726552310c504e2caa874a0dd54cc42bb3a8988466753362eccea4709d59d44c4293a33a99c3736752310a6e4cea8711dd54dc33a88376752362eccea262145d59d4ce13a33a91885 (by decide +kernel)
private def pack_E6970Receipt42_chunk159 := witnessRule 42 37 64 890203 890386 32 1516
  0xf5020070 0x199148dc22322b1a842836354340a504c6ac6614a058d60c82a40b12a1905482563108902e2a2886239d9544d42332a99a045655533088caae6410a11914cc82941b22a9885282645738502e2c8ac6218a05d160e240b9aa1c7665406ecca4641199950c422b32b1b (by decide +kernel)
private def pack_E6970Receipt42_chunk160 := witnessRule 42 37 96 890387 890642 32 1589
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk161 := witnessRule 42 37 128 890643 890768 5 265
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk162 := witnessRule 42 36 0 900000 900076 32 1774
  0x1ff807ff 0x6e8d0a210dcda148e2393428988586854cd0a46c5d9a144e13ab428842746852386e6d0a26214dc9a14ce238b4291885 (by decide +kernel)
private def pack_E6970Receipt42_chunk163 := witnessRule 42 36 32 900077 900203 32 1536
  0x2f00bf0 0x5665532088ccae6210a11954cc42941b2aa9c281726554310c502e2caac74e09d1450cebb3a983767523108ccea86c5d59d4cc428ba33aa9c2736754310a4e4ceac70a09c99948e941bb299c7685136ccea6621159d54d93ab4289c (by decide +kernel)
private def pack_E6970Receipt42_chunk164 := witnessRule 42 36 64 900204 900389 32 1478
  0xffd0f41c 0x141b1a99b052816357340a902c4a6681520954cc22c0aa188885465563408506c8a86614a099158c82940b22c18854816354310a906ac6dd9944d02333299984 (by decide +kernel)
private def pack_E6970Receipt42_chunk165 := witnessRule 42 36 96 900390 900768 31 1526
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk166 := witnessRule 42 35 0 910000 910077 32 1676
  0x13fc05ff 0xbab4299c2746852310a4e6d0a870dc5a154e141b8b3a89d768513108cd0a66c5d5a148c428ba342a1c37469564e4d0aa711c9a544e2bca91b (by decide +kernel)
private def pack_E6970Receipt42_chunk167 := witnessRule 42 35 32 910078 910205 32 1463
  0x803c03f8 0x666523508acca8681119958cc214232a919852836554320a504caac6214a059560e240b22a1c4817453310aecea2661199d4cc822b3aa98844675736508cca670a05cd9948c43140b9332a1d282716653310ced0a40dda148d8bb34289885 (by decide +kernel)
private def pack_E6970Receipt42_chunk168 := witnessRule 42 35 64 910256 910392 32 1446
  0xffdea543 0xac8a47410a058d58d82a412a1a84581443218ccaa2701119554d82141b2299a852816457330a902c6a6661520d54c822c12a188c (by decide +kernel)
private def pack_E6970Receipt42_chunk169 := witnessRule 42 35 96 910448 910705 24 1161
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk170 := witnessRule 42 34 0 920000 920077 32 1579
  0x3fc03ff 0x15a154d8ba342a1885173685638502e6cea474a09c99d44c4314138b3a99d7695106cd2a46c5d9a544e13ab4a8842746952386e6d2a26214dc9a54ce238b4a91885 (by decide +kernel)
private def pack_E6970Receipt42_chunk171 := witnessRule 42 34 32 920078 920257 32 1410
  0xf50e027c 0x2332a9a842836553340a502caae6415205914cc82a422a9884481735143311ceceaa0d99d48d022b3aa1984467563208508cca46414a0d9950c42941332b1c281765738902eaa671da144c82334299884 (by decide +kernel)
private def pack_E6970Receipt42_chunk172 := witnessRule 42 34 64 920258 920450 32 1413
  0xfffffef4 0x565523908502c8ac6a1520d50d022c129988905 (by decide +kernel)
private def pack_E6970Receipt42_chunk173 := witnessRule 42 34 96 920451 920704 18 855
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk174 := witnessRule 42 33 0 930000 930078 32 1488
  0x17e02ff 0x668523308ad0a864111a158c4214233a91885283675438502e4cea66218a05c59d54e9c13b28a11d769513108cd2a66c5d5a548c428ba34aa1c2736953310a4e4d2aa70a09c9a144e941bc291c (by decide +kernel)
private def pack_E6970Receipt42_chunk175 := witnessRule 42 33 32 930079 930259 32 1358
  0x5fd3fa3e 0x120d4cd822c0a8a19908862816556340a908a8661160d4cc4442941b32999852816657310a902caa6621521554dbb42a03 (by decide +kernel)
private def pack_E6970Receipt42_chunk176 := witnessRule 42 33 64 930260 930454 32 1391
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk177 := witnessRule 42 33 96 930512 930704 12 563
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk178 := witnessRule 42 32 0 940000 940078 32 1404
  0x40fe01ff 0xcd0a26a111a154cc214233a899852836753320a504ceaa6214a059d5ce240b3299c7695306cd2a464115a550c42234ab1b284685238502e6d0a26218a05c9a14ce94138b4291886 (by decide +kernel)
private def pack_E6970Receipt42_chunk179 := witnessRule 42 32 32 940128 940261 32 1311
  0xf57ae54f 0xb02a28464261959944e821b32a9c04484533508b04a286643559d48dc2233aa1b042836652350a502ccac661521550c822c229988c (by decide +kernel)
private def pack_E6970Receipt42_chunk180 := witnessRule 42 32 64 940262 940515 32 1371
  0xfffffff7 0x232a91e04 (by decide +kernel)
private def pack_E6970Receipt42_chunk181 := witnessRule 42 32 96 940516 940641 6 277
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk182 := witnessRule 42 31 0 950000 950128 32 1342
  0xda9f02ff 0x568523608506cea46814a059d58c82a432a1884481755142311ccd2a268115a54ccc2234aa99042846851320a506d0a66214a09a154e140bc2b1c (by decide +kernel)
private def pack_E6970Receipt42_chunk183 := witnessRule 42 31 32 950129 950263 32 1261
  0xffbfbdef 0x466523b08b04a284642418d9d54dc2242a99a04 (by decide +kernel)
private def pack_E6970Receipt42_chunk184 := witnessRule 42 31 64 950264 950640 32 1358
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk185 := witnessRule 42 30 0 960000 960129 32 1279
  0xffbffd7f 0x90ca66610a05a158c42a43aa1b (by decide +kernel)
private def pack_E6970Receipt42_chunk186 := witnessRule 42 30 32 960130 960265 32 1219
  0xfffffffd 0x2c1a8a1190886 (by decide +kernel)
private def pack_E6970Receipt42_chunk187 := witnessRule 42 30 64 960320 960640 27 1122
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk188 := witnessRule 42 29 0 970000 970130 32 1216
  0xf2f7a57f 0x234291c84368543808504cea46e156114508c86ab4a89b84369553508506d0a26a14a05a154cc2a43a99904 (by decide +kernel)
private def pack_E6970Receipt42_chunk189 := witnessRule 42 29 32 970131 970322 32 1190
  0xfffbfebf 0x6cca47c1119d44f02133aa9d04 (by decide +kernel)
private def pack_E6970Receipt42_chunk190 := witnessRule 42 29 64 970323 970577 21 852
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk191 := witnessRule 42 28 0 980000 980131 32 1158
  0xfdffdbff 0x4d0aa72111a548e0214134291b05 (by decide +kernel)
private def pack_E6970Receipt42_chunk192 := witnessRule 42 28 32 980132 980324 32 1163
  0xffffffbf 0x1b3a91e84 (by decide +kernel)
private def pack_E6970Receipt42_chunk193 := witnessRule 42 28 64 980325 980576 16 635
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk194 := witnessRule 42 27 0 990000 990132 32 1105
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk195 := witnessRule 42 27 32 990133 990384 32 1139
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk196 := witnessRule 42 27 64 990385 990576 11 429
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk197 := witnessRule 42 26 0 1000000 1000133 32 1055
  0xfd7fe5ff 0x1b4289f04168553c086d2a476109a550e82140b4291c85 (by decide +kernel)
private def pack_E6970Receipt42_chunk198 := witnessRule 42 26 32 1000134 1000387 32 1115
  0xfffffff7 0x4cea468004 (by decide +kernel)
private def pack_E6970Receipt42_chunk199 := witnessRule 42 26 64 1000388 1000513 6 229
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk200 := witnessRule 42 25 0 1010000 1010134 32 1013
  0xff7ffbff 0x9a148fc20b4aa9d84 (by decide +kernel)
private def pack_E6970Receipt42_chunk201 := witnessRule 42 25 32 1010135 1010450 32 1096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk202 := witnessRule 42 25 64 1010512 1010512 1 38
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk203 := witnessRule 42 24 0 1020000 1020135 32 972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk204 := witnessRule 42 24 32 1020136 1020512 29 968
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk205 := witnessRule 42 23 0 1030000 1030136 32 934
  0xffdff5ff 0x2d0a46900426951340024aa9f03 (by decide +kernel)
private def pack_E6970Receipt42_chunk206 := witnessRule 42 23 32 1030192 1030449 24 777
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk207 := witnessRule 42 22 0 1040000 1040192 32 900
  0xfffffbff 0x2d2a468804 (by decide +kernel)
private def pack_E6970Receipt42_chunk208 := witnessRule 42 22 32 1040193 1040448 20 627
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk209 := witnessRule 42 21 0 1050000 1050194 32 869
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk210 := witnessRule 42 21 32 1050195 1050448 16 487
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk211 := witnessRule 42 20 0 1060000 1060195 32 837
  0xfffffdff 0x12a46a003 (by decide +kernel)
private def pack_E6970Receipt42_chunk212 := witnessRule 42 20 32 1060196 1060385 12 353
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk213 := witnessRule 42 19 0 1070000 1070197 32 809
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk214 := witnessRule 42 19 32 1070256 1070384 8 229
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk215 := witnessRule 42 18 0 1080000 1080257 32 781
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk216 := witnessRule 42 18 32 1080258 1080384 5 139
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk217 := witnessRule 42 17 0 1090000 1090320 32 756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk218 := witnessRule 42 17 32 1090321 1090321 1 27
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk219 := witnessRule 42 16 0 1100000 1100320 30 678
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk220 := witnessRule 42 15 0 1110000 1110320 27 582
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk221 := witnessRule 42 14 0 1120000 1120257 24 489
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk222 := witnessRule 42 13 0 1130000 1130256 21 405
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk223 := witnessRule 42 12 0 1140000 1140256 19 346
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk224 := witnessRule 42 11 0 1150000 1150193 16 273
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk225 := witnessRule 42 10 0 1160000 1160192 14 223
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk226 := witnessRule 42 9 0 1170000 1170192 12 179
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk227 := witnessRule 42 8 0 1180000 1180129 10 137
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk228 := witnessRule 42 7 0 1190000 1190128 8 101
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk229 := witnessRule 42 6 0 1200000 1200128 7 81
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk230 := witnessRule 42 5 0 1210000 1210065 5 52
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk231 := witnessRule 42 4 0 1220000 1220064 4 37
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk232 := witnessRule 42 3 0 1230000 1230064 3 25
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk233 := witnessRule 42 2 0 1240000 1240001 2 14
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk234 := witnessRule 42 1 0 1250000 1250000 1 6
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt42_chunk235 := witnessRule 42 0 0 1260000 1260000 1 5
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt42_chunks : List (Chunk 42) := [pack_E6970Receipt42_chunk0, pack_E6970Receipt42_chunk1, pack_E6970Receipt42_chunk2, pack_E6970Receipt42_chunk3, pack_E6970Receipt42_chunk4, pack_E6970Receipt42_chunk5, pack_E6970Receipt42_chunk6, pack_E6970Receipt42_chunk7, pack_E6970Receipt42_chunk8, pack_E6970Receipt42_chunk9, pack_E6970Receipt42_chunk10, pack_E6970Receipt42_chunk11, pack_E6970Receipt42_chunk12, pack_E6970Receipt42_chunk13, pack_E6970Receipt42_chunk14, pack_E6970Receipt42_chunk15, pack_E6970Receipt42_chunk16, pack_E6970Receipt42_chunk17, pack_E6970Receipt42_chunk18, pack_E6970Receipt42_chunk19, pack_E6970Receipt42_chunk20, pack_E6970Receipt42_chunk21, pack_E6970Receipt42_chunk22, pack_E6970Receipt42_chunk23, pack_E6970Receipt42_chunk24, pack_E6970Receipt42_chunk25, pack_E6970Receipt42_chunk26, pack_E6970Receipt42_chunk27, pack_E6970Receipt42_chunk28, pack_E6970Receipt42_chunk29, pack_E6970Receipt42_chunk30, pack_E6970Receipt42_chunk31, pack_E6970Receipt42_chunk32, pack_E6970Receipt42_chunk33, pack_E6970Receipt42_chunk34, pack_E6970Receipt42_chunk35, pack_E6970Receipt42_chunk36, pack_E6970Receipt42_chunk37, pack_E6970Receipt42_chunk38, pack_E6970Receipt42_chunk39, pack_E6970Receipt42_chunk40, pack_E6970Receipt42_chunk41, pack_E6970Receipt42_chunk42, pack_E6970Receipt42_chunk43, pack_E6970Receipt42_chunk44, pack_E6970Receipt42_chunk45, pack_E6970Receipt42_chunk46, pack_E6970Receipt42_chunk47, pack_E6970Receipt42_chunk48, pack_E6970Receipt42_chunk49, pack_E6970Receipt42_chunk50, pack_E6970Receipt42_chunk51, pack_E6970Receipt42_chunk52, pack_E6970Receipt42_chunk53, pack_E6970Receipt42_chunk54, pack_E6970Receipt42_chunk55, pack_E6970Receipt42_chunk56, pack_E6970Receipt42_chunk57, pack_E6970Receipt42_chunk58, pack_E6970Receipt42_chunk59, pack_E6970Receipt42_chunk60, pack_E6970Receipt42_chunk61, pack_E6970Receipt42_chunk62, pack_E6970Receipt42_chunk63, pack_E6970Receipt42_chunk64, pack_E6970Receipt42_chunk65, pack_E6970Receipt42_chunk66, pack_E6970Receipt42_chunk67, pack_E6970Receipt42_chunk68, pack_E6970Receipt42_chunk69, pack_E6970Receipt42_chunk70, pack_E6970Receipt42_chunk71, pack_E6970Receipt42_chunk72, pack_E6970Receipt42_chunk73, pack_E6970Receipt42_chunk74, pack_E6970Receipt42_chunk75, pack_E6970Receipt42_chunk76, pack_E6970Receipt42_chunk77, pack_E6970Receipt42_chunk78, pack_E6970Receipt42_chunk79, pack_E6970Receipt42_chunk80, pack_E6970Receipt42_chunk81, pack_E6970Receipt42_chunk82, pack_E6970Receipt42_chunk83, pack_E6970Receipt42_chunk84, pack_E6970Receipt42_chunk85, pack_E6970Receipt42_chunk86, pack_E6970Receipt42_chunk87, pack_E6970Receipt42_chunk88, pack_E6970Receipt42_chunk89, pack_E6970Receipt42_chunk90, pack_E6970Receipt42_chunk91, pack_E6970Receipt42_chunk92, pack_E6970Receipt42_chunk93, pack_E6970Receipt42_chunk94, pack_E6970Receipt42_chunk95, pack_E6970Receipt42_chunk96, pack_E6970Receipt42_chunk97, pack_E6970Receipt42_chunk98, pack_E6970Receipt42_chunk99, pack_E6970Receipt42_chunk100, pack_E6970Receipt42_chunk101, pack_E6970Receipt42_chunk102, pack_E6970Receipt42_chunk103, pack_E6970Receipt42_chunk104, pack_E6970Receipt42_chunk105, pack_E6970Receipt42_chunk106, pack_E6970Receipt42_chunk107, pack_E6970Receipt42_chunk108, pack_E6970Receipt42_chunk109, pack_E6970Receipt42_chunk110, pack_E6970Receipt42_chunk111, pack_E6970Receipt42_chunk112, pack_E6970Receipt42_chunk113, pack_E6970Receipt42_chunk114, pack_E6970Receipt42_chunk115, pack_E6970Receipt42_chunk116, pack_E6970Receipt42_chunk117, pack_E6970Receipt42_chunk118, pack_E6970Receipt42_chunk119, pack_E6970Receipt42_chunk120, pack_E6970Receipt42_chunk121, pack_E6970Receipt42_chunk122, pack_E6970Receipt42_chunk123, pack_E6970Receipt42_chunk124, pack_E6970Receipt42_chunk125, pack_E6970Receipt42_chunk126, pack_E6970Receipt42_chunk127, pack_E6970Receipt42_chunk128, pack_E6970Receipt42_chunk129, pack_E6970Receipt42_chunk130, pack_E6970Receipt42_chunk131, pack_E6970Receipt42_chunk132, pack_E6970Receipt42_chunk133, pack_E6970Receipt42_chunk134, pack_E6970Receipt42_chunk135, pack_E6970Receipt42_chunk136, pack_E6970Receipt42_chunk137, pack_E6970Receipt42_chunk138, pack_E6970Receipt42_chunk139, pack_E6970Receipt42_chunk140, pack_E6970Receipt42_chunk141, pack_E6970Receipt42_chunk142, pack_E6970Receipt42_chunk143, pack_E6970Receipt42_chunk144, pack_E6970Receipt42_chunk145, pack_E6970Receipt42_chunk146, pack_E6970Receipt42_chunk147, pack_E6970Receipt42_chunk148, pack_E6970Receipt42_chunk149, pack_E6970Receipt42_chunk150, pack_E6970Receipt42_chunk151, pack_E6970Receipt42_chunk152, pack_E6970Receipt42_chunk153, pack_E6970Receipt42_chunk154, pack_E6970Receipt42_chunk155, pack_E6970Receipt42_chunk156, pack_E6970Receipt42_chunk157, pack_E6970Receipt42_chunk158, pack_E6970Receipt42_chunk159, pack_E6970Receipt42_chunk160, pack_E6970Receipt42_chunk161, pack_E6970Receipt42_chunk162, pack_E6970Receipt42_chunk163, pack_E6970Receipt42_chunk164, pack_E6970Receipt42_chunk165, pack_E6970Receipt42_chunk166, pack_E6970Receipt42_chunk167, pack_E6970Receipt42_chunk168, pack_E6970Receipt42_chunk169, pack_E6970Receipt42_chunk170, pack_E6970Receipt42_chunk171, pack_E6970Receipt42_chunk172, pack_E6970Receipt42_chunk173, pack_E6970Receipt42_chunk174, pack_E6970Receipt42_chunk175, pack_E6970Receipt42_chunk176, pack_E6970Receipt42_chunk177, pack_E6970Receipt42_chunk178, pack_E6970Receipt42_chunk179, pack_E6970Receipt42_chunk180, pack_E6970Receipt42_chunk181, pack_E6970Receipt42_chunk182, pack_E6970Receipt42_chunk183, pack_E6970Receipt42_chunk184, pack_E6970Receipt42_chunk185, pack_E6970Receipt42_chunk186, pack_E6970Receipt42_chunk187, pack_E6970Receipt42_chunk188, pack_E6970Receipt42_chunk189, pack_E6970Receipt42_chunk190, pack_E6970Receipt42_chunk191, pack_E6970Receipt42_chunk192, pack_E6970Receipt42_chunk193, pack_E6970Receipt42_chunk194, pack_E6970Receipt42_chunk195, pack_E6970Receipt42_chunk196, pack_E6970Receipt42_chunk197, pack_E6970Receipt42_chunk198, pack_E6970Receipt42_chunk199, pack_E6970Receipt42_chunk200, pack_E6970Receipt42_chunk201, pack_E6970Receipt42_chunk202, pack_E6970Receipt42_chunk203, pack_E6970Receipt42_chunk204, pack_E6970Receipt42_chunk205, pack_E6970Receipt42_chunk206, pack_E6970Receipt42_chunk207, pack_E6970Receipt42_chunk208, pack_E6970Receipt42_chunk209, pack_E6970Receipt42_chunk210, pack_E6970Receipt42_chunk211, pack_E6970Receipt42_chunk212, pack_E6970Receipt42_chunk213, pack_E6970Receipt42_chunk214, pack_E6970Receipt42_chunk215, pack_E6970Receipt42_chunk216, pack_E6970Receipt42_chunk217, pack_E6970Receipt42_chunk218, pack_E6970Receipt42_chunk219, pack_E6970Receipt42_chunk220, pack_E6970Receipt42_chunk221, pack_E6970Receipt42_chunk222, pack_E6970Receipt42_chunk223, pack_E6970Receipt42_chunk224, pack_E6970Receipt42_chunk225, pack_E6970Receipt42_chunk226, pack_E6970Receipt42_chunk227, pack_E6970Receipt42_chunk228, pack_E6970Receipt42_chunk229, pack_E6970Receipt42_chunk230, pack_E6970Receipt42_chunk231, pack_E6970Receipt42_chunk232, pack_E6970Receipt42_chunk233, pack_E6970Receipt42_chunk234, pack_E6970Receipt42_chunk235]
def rows42 := rowsFrom pack_E6970Receipt42_chunks
theorem good42 : ∀ r ∈ rows42, good 42 r = true := rowsFrom_good pack_E6970Receipt42_chunks
theorem sorted42 : rows42.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt42_chunks 0 (by decide +kernel)).1
theorem mass42 (i : Fin 61) :
    bandCount 42 (i.val : ℤ) 60 16 ≤ (rows42.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt42_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 42 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt42_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total42 : (rows42.map (price 42)).sum = 422032 :=
  (total_eq pack_E6970Receipt42_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt42

section Pack_E6970Receipt43

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt43_chunk0 := witnessA6966Final 43 60 0 690017 690144 32 3496
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk1 := witnessA6966Final 43 60 32 690145 690270 32 3434
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk2 := witnessA6966Final 43 60 64 690271 690394 32 3394
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk3 := witnessA6966Final 43 60 96 690395 690516 32 3352
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk4 := witnessA6966Final 43 60 128 690517 690640 32 3278
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk5 := witnessA6966Final 43 60 160 690641 690770 32 3192
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk6 := witnessA6966Final 43 60 192 690771 690960 32 2989
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk7 := witnessA6966Final 43 60 224 690961 691030 14 1253
  0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk8 := witnessRule 43 59 0 700016 700142 32 3312
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk9 := witnessRule 43 59 32 700143 700267 32 3255
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk10 := witnessRule 43 59 64 700268 700390 32 3214
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk11 := witnessRule 43 59 96 700391 700467 32 3153
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk12 := witnessRule 43 59 128 700512 700589 32 3174
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk13 := witnessRule 43 59 160 700590 700717 32 2985
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk14 := witnessRule 43 59 192 700768 700904 32 2868
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk15 := witnessRule 43 59 224 700960 701029 14 1213
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk16 := witnessRule 43 58 0 710015 710140 32 3171
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk17 := witnessRule 43 58 32 710141 710264 32 3109
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk18 := witnessRule 43 58 64 710265 710341 32 3045
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk19 := witnessRule 43 58 96 710387 710462 32 3101
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk20 := witnessRule 43 58 128 710463 710585 32 2982
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk21 := witnessRule 43 58 160 710586 710714 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk22 := witnessRule 43 58 192 710715 710903 32 2749
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk23 := witnessRule 43 58 224 710904 711029 14 1175
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk24 := witnessRule 43 57 0 720014 720138 32 3054
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk25 := witnessRule 43 57 32 720139 720216 32 2977
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk26 := witnessRule 43 57 64 720262 720338 32 3007
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk27 := witnessRule 43 57 96 720339 720458 32 2998
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk28 := witnessRule 43 57 128 720459 720582 32 2832
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk29 := witnessRule 43 57 160 720583 720712 32 2737
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk30 := witnessRule 43 57 192 720713 720902 32 2650
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk31 := witnessRule 43 57 224 720903 721028 13 1059
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk32 := witnessRule 43 56 0 730013 730090 32 2954
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk33 := witnessRule 43 56 32 730137 730213 32 2946
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk34 := witnessRule 43 56 64 730214 730334 32 2937
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk35 := witnessRule 43 56 96 730335 730454 32 2882
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk36 := witnessRule 43 56 128 730455 730579 32 2719
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk37 := witnessRule 43 56 160 730580 730710 32 2644
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk38 := witnessRule 43 56 192 730711 730902 32 2562
  0xdfffffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt43_chunk39 := witnessRule 43 56 224 730903 731028 12 951
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk40 := witnessRule 43 55 0 740012 740089 32 2898
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk41 := witnessRule 43 55 32 740090 740211 32 2888
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk42 := witnessRule 43 55 64 740212 740331 32 2876
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk43 := witnessRule 43 55 96 740332 740451 32 2781
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk44 := witnessRule 43 55 128 740452 740577 32 2620
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk45 := witnessRule 43 55 160 740578 740709 32 2552
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk46 := witnessRule 43 55 192 740710 740902 32 2484
  0xefdfffff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt43_chunk47 := witnessRule 43 55 224 740960 741027 10 771
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk48 := witnessRule 43 54 0 750011 750087 32 2849
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk49 := witnessRule 43 54 32 750088 750208 32 2836
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk50 := witnessRule 43 54 64 750209 750327 32 2818
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk51 := witnessRule 43 54 96 750328 750448 32 2642
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk52 := witnessRule 43 54 128 750449 750527 32 2539
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk53 := witnessRule 43 54 160 750576 750708 32 2469
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk54 := witnessRule 43 54 192 750709 750960 32 2412
  0xfbe7edff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt43_chunk55 := witnessRule 43 54 224 750961 751027 8 602
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk56 := witnessRule 43 53 0 760010 760086 32 2807
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk57 := witnessRule 43 53 32 760087 760206 32 2792
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk58 := witnessRule 43 53 64 760207 760324 32 2758
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk59 := witnessRule 43 53 96 760325 760400 32 2541
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk60 := witnessRule 43 53 128 760401 760525 32 2459
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk61 := witnessRule 43 53 160 760526 760708 32 2383
  0x7fffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt43_chunk62 := witnessRule 43 53 192 760709 760962 32 2341
  0xfef9f2fb 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt43_chunk63 := witnessRule 43 53 224 760963 761026 5 371
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk64 := witnessRule 43 52 0 770009 770084 32 2772
  0xfffffe7f 0x15ccd338a2 (by decide +kernel)
private def pack_E6970Receipt43_chunk65 := witnessRule 43 52 32 770085 770203 32 2753
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk66 := witnessRule 43 52 64 770204 770321 32 2629
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk67 := witnessRule 43 52 96 770322 770398 32 2498
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk68 := witnessRule 43 52 128 770399 770524 32 2366
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk69 := witnessRule 43 52 160 770525 770708 32 2307
  0x9f6dffff 0x1b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt43_chunk70 := witnessRule 43 52 192 770709 771024 32 2281
  0xffde7c3c 0xbb9a17166364e2ca6c5c994d939321b3716331086ea685cd90d939b19b (by decide +kernel)
private def pack_E6970Receipt43_chunk71 := witnessRule 43 52 224 771025 771026 2 147
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk72 := witnessRule 43 51 0 780008 780083 32 2744
  0xabffd5ff 0xdcd8cda38b21b67141364e8c66cdc990da3a9a (by decide +kernel)
private def pack_E6970Receipt43_chunk73 := witnessRule 43 51 32 780084 780201 32 2718
  0xfffebfff 0x11c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt43_chunk74 := witnessRule 43 51 64 780202 780275 32 2513
  0xffcffffa 0x67334ee2895c58cdbb8a2 (by decide +kernel)
private def pack_E6970Receipt43_chunk75 := witnessRule 43 51 96 780320 780396 32 2461
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk76 := witnessRule 43 51 128 780397 780523 32 2282
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk77 := witnessRule 43 51 160 780524 780709 32 2234
  0x792f6df 0xb9b29b27364366e4c66210dc594da38b21b17464364e8c66cdc990da39319b574342eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt43_chunk78 := witnessRule 43 51 192 780710 781025 30 2090
  0x3fffdf0f 0xb8b39b17266364e4ca6cdc590c421bb1a (by decide +kernel)
private def pack_E6970Receipt43_chunk79 := witnessRule 43 50 0 790007 790081 32 2715
  0xaffaa8ff 0x2b930a8846715131090c2a9990d0ba329b473615108ae2c2a262155c54cdb3922 (by decide +kernel)
private def pack_E6970Receipt43_chunk80 := witnessRule 43 50 32 790082 790198 32 2671
  0xffaabfea 0x17663364e8c86cdc994db38b0a88477124ec6685d590d939b29b (by decide +kernel)
private def pack_E6970Receipt43_chunk81 := witnessRule 43 50 64 790199 790273 32 2446
  0xf57ffd53 0x37463368e4c86d5d4d13ab19b37364368e2ca6ddc5441bb892 (by decide +kernel)
private def pack_E6970Receipt43_chunk82 := witnessRule 43 50 96 790274 790395 32 2363
  0xf5ffeaff 0x2b9319b674348e6c66d5c590dbb8a09b (by decide +kernel)
private def pack_E6970Receipt43_chunk83 := witnessRule 43 50 128 790396 790523 32 2204
  0xb6dffd7f 0x5d98cd9ba319b5726336ee6699c58cdc38a2 (by decide +kernel)
private def pack_E6970Receipt43_chunk84 := witnessRule 43 50 160 790524 790710 32 2164
  0xc1e03927 0x5cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b (by decide +kernel)
private def pack_E6970Receipt43_chunk85 := witnessRule 43 50 192 790711 791025 26 1773
  0x3ffffe3 0x2e4ce6c9c598c4213c1a (by decide +kernel)
private def pack_E6970Receipt43_chunk86 := witnessRule 43 49 0 800006 800080 32 2690
  0xffd01ff 0x4726152310a8e2c2a8719c5895b38a8a09c1776151084eac2a262149d1854ce1b9b0a91885372615438ae4c4ad1c554db39289b (by decide +kernel)
private def pack_E6970Receipt43_chunk87 := witnessRule 43 49 32 800081 800196 32 2620
  0xfea0ffd4 0xcca68dd585442239b0a89885472615338ae2c2a462155c550dbb92a76152364ecc2a210dd18544c429b9b0a99c (by decide +kernel)
private def pack_E6970Receipt43_chunk88 := witnessRule 43 49 64 800197 800271 32 2383
  0x547f550f 0x5d990d93a329b573615108ce2c2a262159c54cdbb92296154ec8685d594da3a30a8845726151310aae2c2a6719c548c423b8a8a3 (by decide +kernel)
private def pack_E6970Receipt43_chunk89 := witnessRule 43 49 96 800272 800394 32 2275
  0xaafd55fd 0xdd190da39329b7716151090e2485dd8cd93ab21b3736536ce4c2a211dc544c424319a (by decide +kernel)
private def pack_E6970Receipt43_chunk90 := witnessRule 43 49 128 800395 800523 32 2131
  0xc90ed13e 0x17664364ecc66cdd190da3a319b5726436ce2c662119d4d438988b17763366eac66d1cd90dab931988457165370e2a20e1c4913b319b (by decide +kernel)
private def pack_E6970Receipt43_chunk91 := witnessRule 43 49 160 800524 800712 32 2102
  0xf8781e01 0x5cd9cd93933188427168366ee620c5d198d93a329b3736431086e4cc6d1c594c4223b9a17565364eac86cdd18cc421b9b29b4736436ae4c662115c594db3a1883 (by decide +kernel)
private def pack_E6970Receipt43_chunk92 := witnessRule 43 49 192 800768 801024 21 1402
  0x1ffffe 0xbd1a (by decide +kernel)
private def pack_E6970Receipt43_chunk93 := witnessRule 43 48 0 810005 810078 32 2664
  0x1ff001ff 0x15c58948e33928988477151270c4a9d8548c42330aa1b27662562e8c2aa70dd18944e239b12884472625238ae2c4a262155c94cdb38a923 (by decide +kernel)
private def pack_E6970Receipt43_chunk94 := witnessRule 43 48 32 810079 810194 32 2512
  0xe801ff00 0x12c2a20c5dd8544c428bb30a99c2756152310a4e8c2a8711d18959b930aa9c572625138ce2c4a2119c948dbb8a093861513108ec2a66c5d98548c428bab0aa1c37562564e6c2aa711cd8944e2b9312884 (by decide +kernel)
private def pack_E6970Receipt43_chunk95 := witnessRule 43 48 64 810195 810270 32 2335
  0x80ff401f 0x1bab0a898853746153388e6c2a462151c98550e339312b5715536ee4a26c5e18544213b30a898852756153386e8c2a46214dcd8550e2b9b12b471615538ce2c4a271dc9441bb8a093 (by decide +kernel)
private def pack_E6970Receipt43_chunk96 := witnessRule 43 48 96 810271 810394 32 2188
  0xa07a80fa 0x11d5854422b9b0a89885572615338ce2c2a462159c550dc392a7714126eca68dd98544223a30a89885473615338ae4c2a462155c58550e3b8b12b771514138ee2824e18548d93bb0a884 (by decide +kernel)
private def pack_E6970Receipt43_chunk97 := witnessRule 43 48 128 810395 810524 32 2063
  0xf0070478 0x17665364ecc86cdd58cc421ba329b4736431088e4cc6d5c594c422bb9a18673362eec86c9d98cc4213ab29b3746431086e6cc6d9c98544c42b38b0a99c7715231090c8685dd8cc420bb329b (by decide +kernel)
private def pack_E6970Receipt43_chunk98 := witnessRule 43 48 160 810576 810770 32 2043
  0xffbf0780 0xb8b51b17467364e6cc62109c9a0d9b8b39884379342eacc6c9d594d9ba32188437366368e4ca62111c59cdabb1883 (by decide +kernel)
private def pack_E6970Receipt43_chunk99 := witnessRule 43 48 192 810771 811024 16 1052
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk100 := witnessRule 43 47 0 820004 820077 32 2642
  0x3ff003ff 0x6716356ce4a2827218944d8bbb128841766252384eac4a262149d1894ce1b9b1291885372625438ae4c6ad1c954db39a89b (by decide +kernel)
private def pack_E6970Receipt43_chunk101 := witnessRule 43 47 32 820078 820193 32 2428
  0xc007fe00 0x86251362f0c4ad98554d93b31289c3756251086e8c4a4711cd8944c42a3931299c5716252310aae4a86ddcd54b12a76252362eec4a2709d98944213ab1291c3746251310a6e6c4a6711c98948c42a38b12a1c (by decide +kernel)
private def pack_E6970Receipt43_chunk102 := witnessRule 43 47 64 820194 820269 32 2267
  0xfc003f 0x37662564e8c2aa711d18944e2b9b12884572625238ce2c4a262159c94cdbb8a923962550c2a46211d8550d93bb12b1756155386eac4a2711d189442239b1291c5726251310aae2c4a6719c948c423b928a3 (by decide +kernel)
private def pack_E6970Receipt43_chunk103 := witnessRule 43 47 96 820270 820394 32 2107
  0x6800f0 0x13b30a99c3756152310a6e8c2a8711cd854cc42a3930aa9c672625138ee2c4a211dc948dc38a093a6151062f0c2a262145dd854ce13b30a918852756154388eac4acdcd8554e2b9b1289c672625108ce2c4a471dc944c42438a8939615131090c2a66c5dd8548c428bb30aa1c (by decide +kernel)
private def pack_E6970Receipt43_chunk104 := witnessRule 43 47 128 820395 820577 32 2001
  0x3803000a 0x1b8b49b47831062eec862105d998d93ab2988427467366e6cc6210dc9a0d8c239321c1857163310a30aea6e190c41bb31a1766531082eace6cdd5854ce23a30a91885473615438ae4c2a662155c58554e338aa18847715142390e2422e1854cd93bb0a89885 (by decide +kernel)
private def pack_E6970Receipt43_chunk105 := witnessRule 43 47 160 820578 820773 32 1992
  0xfffff1f0 0x2e4d46c9c5a4c4213d9a17567364e8cc62109cda0d9b9339884 (by decide +kernel)
private def pack_E6970Receipt43_chunk106 := witnessRule 43 47 192 820832 820961 10 648
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk107 := witnessRule 43 46 0 830003 830075 32 2619
  0xffe01fff 0x86354ec4a4621198950d93b31ab1746255386e8c6a2711cd8d44223931a91c (by decide +kernel)
private def pack_E6970Receipt43_chunk108 := witnessRule 43 46 32 830076 830192 32 2295
  0x802ffc05 0x2589441c31291b1776251310a2ecc4a6709d58948c4293a312a1c47463566e4c4aa715c98d44e339a91b862513108ec4a66c5d98948c428bab12a1c37563564e6c4aa711cd8d44e2b8b1a91c (by decide +kernel)
private def pack_E6970Receipt43_chunk109 := witnessRule 43 46 64 830193 830269 32 2205
  0xfc007f 0x4ecc4a470dd58944c429ba31299c4736252310a8e4c4a8719c98d5ab92a9b77351372c4a26c5e1894420bbb1291c2766251310a4eac4a670dd18948c429b9b12a1c57363568e2c4aa719c58d44e3b9a883 (by decide +kernel)
private def pack_E6970Receipt43_chunk110 := witnessRule 43 46 96 830270 830395 32 2025
  0x3000f0 0x5dd854cc428bb30aa9c2756154310a4e8c2ac711d18948e2b9b1289885572625338ce2c4a462159c950dc39288b96251370c2a66211d8554d93bb1289c3766251086eac4a4711d18944c42a39b1299c5726252310aae2c4a871dc58d5bb928a09ca62550c4a46c5e18944e13bb12884 (by decide +kernel)
private def pack_E6970Receipt43_chunk111 := witnessRule 43 46 128 830396 830579 32 1939
  0xe40c004 0xb9b51b2726931084e2d66cde8c41bb31883668342e8d26c609d194e0c1b9b21885183726638308e2ca6214611dcdbb0aa9b1776154384ecc2a662149d58554e1ba30aa18853736156388e4c2aa62151c5855ce0c2b8b0a99d1867152310b0e2842e58548c42430aa1b (by decide +kernel)
private def pack_E6970Receipt43_chunk112 := witnessRule 43 46 160 830580 830835 32 1956
  0xffffffbf 0xbe9a (by decide +kernel)
private def pack_E6970Receipt43_chunk113 := witnessRule 43 46 192 830896 830960 4 257
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk114 := witnessRule 43 45 0 840002 840074 32 2601
  0xffe007ff 0x218d44d8bbb1a8841766352384eac6a262149d18d4ce1b9b1a91885372635438ae4c8ad1cd54db3a289b (by decide +kernel)
private def pack_E6970Receipt43_chunk115 := witnessRule 43 45 32 840075 840192 32 2197
  0x800ff800 0x218d44d8bc31ab66255364ecc6a270dd58d4421ba31a91c4736351310a8e4c6a6715c58d48c42ab9aa1b774552c6a9d8d48d8bbb1a89c2766351084eac6a470dd18d44c429b9b1a99c4726352310a8e2c6a8719c5915b39a8a09c (by decide +kernel)
private def pack_E6970Receipt43_chunk116 := witnessRule 43 45 64 840193 840269 32 2111
  0x7c003f 0xbb312a1c37663564e8c4aa711d18d44e2b9b1a884572635238ce2c6a262159cd4cdbb92923963550c4a46211d8950d93bb1ab1756255386eac6a2711d18d442239b1a91c5726351310aae2c6a6719cd48c423b9a8a3 (by decide +kernel)
private def pack_E6970Receipt43_chunk117 := witnessRule 43 45 96 840270 840396 32 1947
  0x80038 0x8625336ec2aa62119855cd93b31299c3756252310a6e8c4a8711cd894cc42a39312a9c5716254310aae4ac6c619c948e438a0908c96252072c4a46c5e18944c428bbb1299c2766252310a4eac4a870dd1894cc429b9b12a9c573635138ce4c6a2119c58d48e3b9a8988487251272c4a262121894cd8bbb1291885 (by decide +kernel)
private def pack_E6970Receipt43_chunk118 := witnessRule 43 45 128 840397 840582 32 1877
  0xfbd83001 0x5c5b4db30ab9b181746738304e6cc6214609c9a0e0c1b8b3988518379370c2a86211d8558d8bb30aa98851756157384e8c2ac62149cd8560e0c1b9b0aa1d184726153310c308e2c2aa74615c550c428c338a1188d (by decide +kernel)
private def pack_E6970Receipt43_chunk119 := witnessRule 43 45 160 840583 840960 30 1814
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk120 := witnessRule 43 44 0 850001 850073 32 2521
  0xffc03fff 0x86454ec6a4621198d50d93b322b1746355386e8c8a2711cd9144223932291c (by decide +kernel)
private def pack_E6970Receipt43_chunk121 := witnessRule 43 44 32 850074 850192 32 2109
  0x802ff80b 0x258d441c31a91b1776351310a2ecc6a6709d58d48c4293a31aa1c47464566e4c6aa715c99144e33a291b863513108ec6a66c5d98d48c428bab1aa1c37564564e6c6aa711cd9144e2b8b2291c (by decide +kernel)
private def pack_E6970Receipt43_chunk122 := witnessRule 43 44 64 850193 850270 32 2020
  0x3e003f 0xbc31a89c2776351084ecc6a470dd58d44c429ba31a99c4736352310a8e4c6a8719c9915ab9aa9b77451372c6a26c5e18d4420bbb1a91c2766351310a4eac6a670dd18d48c429b9b1aa1c57364568e2c6aa719c59144e3ba2883 (by decide +kernel)
private def pack_E6970Receipt43_chunk123 := witnessRule 43 44 96 850271 850448 32 1876
  0x4002001c 0x508e2887218948c824312a1b1776253310a2ecc4aa709d58950c4293a312b1c3736255310a6e4c4ae70611c9894ce8c2b8b129188618572543830ee2a43258944c8243129988476255362ecc4a862145d58958e1bab1a91c4746351310a8e6c6a6715c98d48c42ab8b1aa1c673533108ee6a2827258d441c31a91b (by decide +kernel)
private def pack_E6970Receipt43_chunk124 := witnessRule 43 44 128 850449 850640 32 1823
  0xffffc600 0x181726a38304e2d26214609ecdbb12a9b661573108ac2b26c605d58554e8c13a30aa18861827361563a306e4c2aa621860dc5855ce8c238ab1885 (by decide +kernel)
private def pack_E6970Receipt43_chunk125 := witnessRule 43 44 160 850641 850897 23 1368
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk126 := witnessRule 43 43 0 860000 860073 32 2453
  0xffc01fff 0x432289b1776451082ecc8a4709d59144c4293a32299c3736452310a6e4c8a8715c9955a3a2a9b (by decide +kernel)
private def pack_E6970Receipt43_chunk127 := witnessRule 43 43 32 860074 860193 32 2041
  0xc01ff803 0x219144d8bc322b66355364ecc8a270dd5914421ba32291c4736451310a8e4c8a6715c59148c42cb22a76452362eec8a2709d99144213ab2291c3746451310a6e6c8a6711c99148c42a38b22a1c (by decide +kernel)
private def pack_E6970Receipt43_chunk128 := witnessRule 43 43 64 860194 860271 32 1906
  0x7f007f 0x258d44c42431a99b1776352310a2ecc6a8709d58d4cc4293a31aa9c474645138ae6c8a2115c99148e4b22a863523108ec6a86c9dd9158bab1aa9c3756451388e8c8a2111cd9148e2b932289885 (by decide +kernel)
private def pack_E6970Receipt43_chunk129 := witnessRule 43 43 96 860320 860451 32 1810
  0x88008007 0x609c58564e9c138b29c3837431090c4a66411d8954c423312b9b1756256310a2e8c4b070609d18950e8c1b9b12998861837262553a308e2c4a86218611c958e142b8a9188d96254070c6a46211d8d50d8bbb1a99c2766352310a4eac6a870dd18d4cc429b9b1aa9c4726354310a8e2c6ac70615c58d48e8c339a89885 (by decide +kernel)
private def pack_E6970Receipt43_chunk130 := witnessRule 43 43 128 860452 860644 32 1780
  0xfffffec0 0x302fa6dd8950c823312b18841866155310a30ac2ae70605d18558c430c0b9b0ac1d (by decide +kernel)
private def pack_E6970Receipt43_chunk131 := witnessRule 43 43 160 860645 860896 16 939
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk132 := witnessRule 43 42 0 870000 870073 32 2323
  0xffc03fff 0x86554ec8a4621199150d93b32ab1746455386e8caa2711cd9544223932a91c (by decide +kernel)
private def pack_E6970Receipt43_chunk133 := witnessRule 43 42 32 870074 870194 32 1971
  0xe00bfc05 0x2591441c32291b1776451310a2ecc8a6709d59148c4293a322a1c47465566e4c8aa715c99544e33aa91b864513108ec8a66c5d99148c428bab22a1c37565564e6c8aa711cd9544e2b8b2a91c (by decide +kernel)
private def pack_E6970Receipt43_chunk134 := witnessRule 43 42 64 870195 870321 32 1822
  0xc013c007 0x258d4c1c32291b763543108cc6ac6c9d99148e1bab22898853746453388e6c8a462151c99150e2ba2a9b1867451392c8a26c5e1914420bbb2291c2766451310a4eac8a670dd19148c429b9b22a1c57365568e2c8aa719c59544e3baa883 (by decide +kernel)
private def pack_E6970Receipt43_chunk135 := witnessRule 43 42 96 870322 870454 32 1723
  0x5b009003 0x30ac2ac641460d8568e1c0b8b39c862523408ec6a8621198d58d8c3312a9c181756254310c302e8c4ac74609cd8954c430c139312b9d183725838706e2a87218d44cc2431a9988476355362ecc6a862145d58d58e13a31aa9885273635738306e6c6a674611c98d48c430c238b1aa1d (by decide +kernel)
private def pack_E6970Receipt43_chunk136 := witnessRule 43 42 128 870455 870706 32 1757
  0xfffffffd 0x3312a9984 (by decide +kernel)
private def pack_E6970Receipt43_chunk137 := witnessRule 43 42 160 870707 870896 9 524
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk138 := witnessRule 43 41 0 880000 880074 32 2206
  0xffe00fff 0x432a89b1776551082eccaa4709d59544c4293a32a99c3736552310a6e4caa8715c9995a3aaa9b (by decide +kernel)
private def pack_E6970Receipt43_chunk139 := witnessRule 43 41 32 880075 880196 32 1896
  0xf803fe00 0x219544d8bc32ab66455364eccaa270dd5954421ba32a91c4736551310a8e4caa6715c59548c42cb2aa76552362eecaa2709d99544213ab2a91c3746551310a6e6caa6711c99548c42a38b2aa1c (by decide +kernel)
private def pack_E6970Receipt43_chunk140 := witnessRule 43 41 64 880197 880324 32 1730
  0x7802f007 0x1837163563b0c8a264121914cd8bbb22918851766454384eac8a662149d19154e1b9b22a1885372645638308e4c8a474615d14ce4b22903864523108ec8a86c5d9914cc428bab22a9c3756551388e8caa2111cd9548e2b932a89885 (by decide +kernel)
private def pack_E6970Receipt43_chunk141 := witnessRule 43 41 96 880325 880458 32 1661
  0xfff00a00 0x1d8d4ccc2331aa99041866254320a30ac4ac62146118960e0c0b9b12b98861817262593a702e4c2aa74e09c558e431aa83863523308ec8a86d98d58c422b1ac1b1817563543a304e8c6a66218609cd8d54e8c1b931aa1886 (by decide +kernel)
private def pack_E6970Receipt43_chunk142 := witnessRule 43 41 128 880512 880832 32 1748
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk143 := witnessRule 43 41 160 880833 880833 1 58
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk144 := witnessRule 43 40 0 890000 890074 32 2094
  0x7fe01fff 0x2b8b3291c86654ecaa4621199550d93b332b1746555386e8cca2711cd9944223933291c (by decide +kernel)
private def pack_E6970Receipt43_chunk145 := witnessRule 43 40 32 890075 890197 32 1808
  0xfc017f01 0x4b2a88386552362eecaa262145d9954ce13ab2a918852746554388e8ccacdc99554e2b933289c67652370caa26211d954cd8bb32a918851756554386eaccac9cd9554e239b3289c (by decide +kernel)
private def pack_E6970Receipt43_chunk146 := witnessRule 43 40 64 890198 890326 32 1655
  0xe007c04 0x302e6c6ae74609c98d58c430c138b1ac1d3827162543b0c8a80e19148c823b22a188466456362eac8aa62145d1915ce0c13a32299d183736452310c306e4c8a874611c5914cc43432a8988476553362eecaa4709d99544c4293ab2a99c3746552310a6e6caa8711c59554e0c2b8b2a89d (by decide +kernel)
private def pack_E6970Receipt43_chunk147 := witnessRule 43 40 96 890327 890515 32 1619
  0xfffe00c0 0xec6a46a1198d50d020c331299a051856255330a308c4ae641460d8964c429c1b0aa9885382615738702e2c2ac621a18d44d423b229990466455310830cc6a862146158d58e0c0ba31aa9886 (by decide +kernel)
private def pack_E6970Receipt43_chunk148 := witnessRule 43 40 128 890516 890832 26 1400
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk149 := witnessRule 43 39 0 900000 900075 32 1990
  0x3ff007ff 0x8e4cca462151c59950e433289b1776651082eccca4709d59944c4293a33299c3736652310a6e4cca8715c99d5a3b2a9b (by decide +kernel)
private def pack_E6970Receipt43_chunk150 := witnessRule 43 39 32 900076 900199 32 1720
  0x3f007f80 0x611c99544c430c238b2a99d8665136ecaa6621199554d93b33289c3756651086e8cca4711cd9944c42a3933299c5716652310b2cca9d9948d8bbb3289c2766651084eacca470dd19944c429b9b3299c (by decide +kernel)
private def pack_E6970Receipt43_chunk151 := witnessRule 43 39 64 900200 900329 32 1579
  0xc02f00 0xc331a999851856355320a308c6ae621460d8d64e1c1b12a9c381726254310c702e2c4ac74e09c954c42c32289a04765533108ccaaa6c6199150e0c0bab22998861817464553a304e6c8a86218609c99158e8c1ba2b9c86553070caa46211d9550d8bb32a998851756555384e8caa862149cd9558e0c1b9b2a91d (by decide +kernel)
private def pack_E6970Receipt43_chunk152 := witnessRule 43 39 96 900330 900519 32 1592
  0xffffeaac 0xcc6a66c106158950d428c1b12c19853826156320a702b46dd9148d023322a1984 (by decide +kernel)
private def pack_E6970Receipt43_chunk153 := witnessRule 43 39 128 900576 900832 19 1011
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk154 := witnessRule 43 38 0 910000 910075 32 1887
  0x5ff00fff 0x11cd9d44e2b8b3a91c86754ecca4621199950d93b33ab1746655386e8cea2711cd9d44223933a91c (by decide +kernel)
private def pack_E6970Receipt43_chunk155 := witnessRule 43 38 32 910076 910200 32 1636
  0x17802fc0 0x1827365543a306e4caa6621860dc59554e9423a28a11d86652070cca46c5dd9944c428bb33299c2756652310a4e8cca870dcd994cc429b9332a9c1847266513a30aeca47219944c423b3299b1766652310a2eacca870dd59d5939b32a9c (by decide +kernel)
private def pack_E6970Receipt43_chunk156 := witnessRule 43 38 64 910201 910331 32 1519
  0x1001c0 0x764513608cc8a66a106198d48d428c2b1aa1a051846356330a306c6b06414e0d8950c829c1312b1885381625838702e4ae6215205c54514ec322b03765523308ccaa86410619914cc828c2b22a9885184645738302e6c8ac6218605c99160e9c0b931aa1d382716353310c704e6aa7219544cc23b3299b665553108acaae6c605d5954ce8c13a32a91886 (by decide +kernel)
private def pack_E6970Receipt43_chunk157 := witnessRule 43 38 96 910384 910579 32 1573
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk158 := witnessRule 43 38 128 910580 910769 12 629
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk159 := witnessRule 43 37 0 920000 920076 32 1788
  0xff803ff 0x1ba33a898853736753388e4cea462151c59d50e433a89b1776751082eccea4709d59d44c4293a33a99c3736752310a6e4cea8715c9a15a3baa9b (by decide +kernel)
private def pack_E6970Receipt43_chunk160 := witnessRule 43 37 32 920077 920202 32 1552
  0x3e00fe0 0x185655538302e8caa86218605cd9558e8c13932aa98861827165573a704e2c8a67619944c823b329988466655362eacca862145d19958e0c13a33291d183736651310c306e4cca674611c59948c43433a88376752362eecea2709d99d44213ab3a91c (by decide +kernel)
private def pack_E6970Receipt43_chunk161 := witnessRule 43 37 64 920203 920386 32 1474
  0xf5020070 0x199148dc20c2b1a99b051836357340a706c4a66814e098954cc29c0b12b9905382593108b02aa6211d9544d42332a99a041866452340a30ac8a866146119158c828c1b22c18853836354310a704c6ac70e05c58d54c431c0b9ab9c8655506ecca4641199950c420c332a99885 (by decide +kernel)
private def pack_E6970Receipt43_chunk162 := witnessRule 43 37 96 920387 920642 32 1557
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk163 := witnessRule 43 37 128 920643 920768 5 260
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk164 := witnessRule 43 36 0 930000 930076 32 1689
  0x17f807ff 0x2746753310a4e6ceaa7060dcd9d44e8c238b3a91d86854ecea4621199d50d93b342b1746755386e8d0a2711cda144223934291c (by decide +kernel)
private def pack_E6970Receipt43_chunk165 := witnessRule 43 36 32 930077 930203 32 1474
  0x700bf0 0x6199548cc28c2b2aa19051846556310a306cab070e0d9150e1c0b9322998863817164553a704e8a86214e0dcd4508c474332a03767523108ccea86c619994ce0c0bab32918861817466543a304e6cca66218609c99954e8c1bb2b1c867513108ecea66c5d99d48c428bab3aa1c (by decide +kernel)
private def pack_E6970Receipt43_chunk166 := witnessRule 43 36 64 930204 930389 32 1438
  0xffd5740c 0xc1b1ab1b053826254350a704b0661160514c460c2b2299a851836457330a706c6a66614e098d54c829c0b1ab98853835936b04aa6dd9944d02333299984 (by decide +kernel)
private def pack_E6970Receipt43_chunk167 := witnessRule 43 36 96 930390 930768 31 1495
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk168 := witnessRule 43 35 0 940000 940077 32 1593
  0x3fc01ff 0xaceac6c605d59d48e8c13a33a898861827367533a306e4cea4621860dc59d50ec34289b1776851082ecd0a4709d5a144c4293a34299c3736852310a6e4d0a870611c9a1623c2a9b (by decide +kernel)
private def pack_E6970Receipt43_chunk169 := witnessRule 43 35 32 940078 940205 32 1408
  0x801c02f8 0x199948d420c332a89a851856553340a308caaa661460d955cc829c1b22999053826455310a702c8ae70e05d158c42a40b9a8a21d767513308ccea664106199948c828c2b32a1885184665638302e6ccaa6218605c9995ce9c0b932a99d3827554390cea60dda148db33aa1884 (by decide +kernel)
private def pack_E6970Receipt43_chunk170 := witnessRule 43 35 64 940256 940392 32 1410
  0xfffff543 0xccaa270106159148dc28c1b22b1a853826354340a702c6ac6614e0d60c822c12a1904 (by decide +kernel)
private def pack_E6970Receipt43_chunk171 := witnessRule 43 35 96 940448 940705 24 1137
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk172 := witnessRule 43 34 0 950000 950077 32 1501
  0x1fc03ff 0x30ccea462146159d50e0c0ba33a998861817367553a304e4cea86218609c59d58e9c138b3291d8685206ed0a462119a150d8bab4299885174685538304e8d0a27460dcda14428c1b934291d (by decide +kernel)
private def pack_E6970Receipt43_chunk173 := witnessRule 43 34 32 950078 950257 32 1355
  0x7506007c 0x581514431110c30acaa46c1460d9558d029c1322a19853816456320a708b0621160d50c422413928a1190e7675506ccea468106199944d028c2b32999851846655320a306ccae6214e0d954cc429c132aa9c381716554310c702eaac71da144c82334299884 (by decide +kernel)
private def pack_E6970Receipt43_chunk174 := witnessRule 43 34 64 950258 950450 32 1381
  0xfffffef4 0x565523908704c6a66c14e0d5cd022c1299a04 (by decide +kernel)
private def pack_E6970Receipt43_chunk175 := witnessRule 43 34 96 950451 950704 18 837
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk176 := witnessRule 43 33 0 960000 960078 32 1413
  0x7e02ff 0x3342919841866751330a30acea664146119d54c428c1b3ab9c383665338702e4cca46218e05c59950e9c13b299885769513108cd2a66c619a148e0c0bab42898861817468533a304e6d0a46218609c9a150e8c1bc2a9c (by decide +kernel)
private def pack_E6970Receipt43_chunk177 := witnessRule 43 33 32 960079 960259 32 1307
  0x5fd1fa1e 0x383563608b02a286622618e09914cd429c22b9984583533308b04a288623460d9958cc29c132aa19053816556310a70ab06d61150dbb42a03 (by decide +kernel)
private def pack_E6970Receipt43_chunk178 := witnessRule 43 33 64 960260 960454 32 1359
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk179 := witnessRule 43 33 96 960512 960704 12 551
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk180 := witnessRule 43 32 0 970000 970078 32 1335
  0x40be017f 0x334289a841856752340a308cea8661460d9d58c829c1b32919053826654310a702ccac71205d5450cebb4a98366952320830cd0a26414615a14cc428c2342a9c181736854310c302e4d0ac74e05c99d48e9c13ba99c (by decide +kernel)
private def pack_E6970Receipt43_chunk181 := witnessRule 43 32 32 970128 970261 32 1267
  0xfd7a654f 0xacca274106119548e429c22b1a84582514331120cb02e2a284663959d48dc20c2b3289b851836655350a704caa66814e155cc822c2299904 (by decide +kernel)
private def pack_E6970Receipt43_chunk182 := witnessRule 43 32 64 970262 970515 32 1339
  0xfffffff7 0x232a91e04 (by decide +kernel)
private def pack_E6970Receipt43_chunk183 := witnessRule 43 32 96 970516 970641 6 271
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk184 := witnessRule 43 31 0 980000 980128 32 1275
  0xda9f00ff 0x2b4291b041836755340a704cca66614e195cc422c2a9988466951340830cd0a810615a148cc28c2342a19051836856310a706cea46214e099d50e1c0b8b3a99886 (by decide +kernel)
private def pack_E6970Receipt43_chunk185 := witnessRule 43 31 32 980129 980263 32 1221
  0xffbfbdeb 0x233291d84582514231140c308cca47014e1558d022c1a8a1988886 (by decide +kernel)
private def pack_E6970Receipt43_chunk186 := witnessRule 43 31 64 980264 980640 32 1326
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk187 := witnessRule 43 30 0 990000 990129 32 1214
  0xffaffd3f 0x1c32b19845845143311a704cea66414e1d5cdac3299b (by decide +kernel)
private def pack_E6970Receipt43_chunk188 := witnessRule 43 30 32 990130 990265 32 1183
  0xfffff7fd 0x1a0508d062c1a8a1188986 (by decide +kernel)
private def pack_E6970Receipt43_chunk189 := witnessRule 43 30 64 990320 990640 27 1095
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk190 := witnessRule 43 29 0 1000000 1000130 32 1157
  0xf2f7a57f 0x234291c841846751390a304ceaa6e156114508c44832b4a89b841846852360a306d0a86a14e099d48d029c3ab1904 (by decide +kernel)
private def pack_E6970Receipt43_chunk191 := witnessRule 43 29 32 1000131 1000322 32 1158
  0xfffbfebf 0x6cca47c1119d44f020c1b3291d85 (by decide +kernel)
private def pack_E6970Receipt43_chunk192 := witnessRule 43 29 64 1000323 1000577 21 831
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk193 := witnessRule 43 28 0 1010000 1010131 32 1103
  0xfdffdbdf 0x18367523a0a8d2a47010609a154d82ac2a8a1188886 (by decide +kernel)
private def pack_E6970Receipt43_chunk194 := witnessRule 43 28 32 1010132 1010324 32 1131
  0xffffffbf 0x1b3a91e84 (by decide +kernel)
private def pack_E6970Receipt43_chunk195 := witnessRule 43 28 64 1010325 1010576 16 619
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk196 := witnessRule 43 27 0 1020000 1020132 32 1054
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk197 := witnessRule 43 27 32 1020133 1020384 32 1107
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk198 := witnessRule 43 27 64 1020385 1020576 11 418
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk199 := witnessRule 43 26 0 1030000 1030133 32 1011
  0xfd7fe5ff 0x1b4289f0418267523d0a6d2a4761060da144ec28c0b42a9c85 (by decide +kernel)
private def pack_E6970Receipt43_chunk200 := witnessRule 43 26 32 1030134 1030387 32 1083
  0xfffffff7 0x4cea468004 (by decide +kernel)
private def pack_E6970Receipt43_chunk201 := witnessRule 43 26 64 1030388 1030513 6 223
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk202 := witnessRule 43 25 0 1040000 1040134 32 971
  0xff7ffbff 0x9a148fc20c134291e05 (by decide +kernel)
private def pack_E6970Receipt43_chunk203 := witnessRule 43 25 32 1040135 1040450 32 1064
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk204 := witnessRule 43 25 64 1040512 1040512 1 37
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk205 := witnessRule 43 24 0 1050000 1050135 32 932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk206 := witnessRule 43 24 32 1050136 1050512 29 939
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk207 := witnessRule 43 23 0 1060000 1060136 32 898
  0xffdff5ff 0x2d0a46900426951340020c0b4291f85 (by decide +kernel)
private def pack_E6970Receipt43_chunk208 := witnessRule 43 23 32 1060192 1060449 24 753
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk209 := witnessRule 43 22 0 1070000 1070192 32 865
  0xfffffbff 0x2d2a468804 (by decide +kernel)
private def pack_E6970Receipt43_chunk210 := witnessRule 43 22 32 1070193 1070448 20 607
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk211 := witnessRule 43 21 0 1080000 1080194 32 835
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk212 := witnessRule 43 21 32 1080195 1080448 16 471
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk213 := witnessRule 43 20 0 1090000 1090195 32 805
  0xfffffdff 0x12a46a003 (by decide +kernel)
private def pack_E6970Receipt43_chunk214 := witnessRule 43 20 32 1090196 1090385 12 341
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk215 := witnessRule 43 19 0 1100000 1100197 32 777
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk216 := witnessRule 43 19 32 1100256 1100384 8 221
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk217 := witnessRule 43 18 0 1110000 1110257 32 749
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk218 := witnessRule 43 18 32 1110258 1110384 5 134
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk219 := witnessRule 43 17 0 1120000 1120320 32 724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk220 := witnessRule 43 17 32 1120321 1120321 1 26
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk221 := witnessRule 43 16 0 1130000 1130320 30 648
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk222 := witnessRule 43 15 0 1140000 1140320 27 555
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk223 := witnessRule 43 14 0 1150000 1150257 24 465
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk224 := witnessRule 43 13 0 1160000 1160256 21 384
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk225 := witnessRule 43 12 0 1170000 1170256 19 327
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk226 := witnessRule 43 11 0 1180000 1180193 16 257
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk227 := witnessRule 43 10 0 1190000 1190192 14 209
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk228 := witnessRule 43 9 0 1200000 1200192 12 167
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk229 := witnessRule 43 8 0 1210000 1210129 10 127
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk230 := witnessRule 43 7 0 1220000 1220128 8 93
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk231 := witnessRule 43 6 0 1230000 1230128 7 74
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk232 := witnessRule 43 5 0 1240000 1240065 5 47
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk233 := witnessRule 43 4 0 1250000 1250064 4 33
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk234 := witnessRule 43 3 0 1260000 1260064 3 22
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk235 := witnessRule 43 2 0 1270000 1270001 2 12
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk236 := witnessRule 43 1 0 1280000 1280000 1 5
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt43_chunk237 := witnessRule 43 0 0 1290000 1290000 1 4
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt43_chunks : List (Chunk 43) := [pack_E6970Receipt43_chunk0, pack_E6970Receipt43_chunk1, pack_E6970Receipt43_chunk2, pack_E6970Receipt43_chunk3, pack_E6970Receipt43_chunk4, pack_E6970Receipt43_chunk5, pack_E6970Receipt43_chunk6, pack_E6970Receipt43_chunk7, pack_E6970Receipt43_chunk8, pack_E6970Receipt43_chunk9, pack_E6970Receipt43_chunk10, pack_E6970Receipt43_chunk11, pack_E6970Receipt43_chunk12, pack_E6970Receipt43_chunk13, pack_E6970Receipt43_chunk14, pack_E6970Receipt43_chunk15, pack_E6970Receipt43_chunk16, pack_E6970Receipt43_chunk17, pack_E6970Receipt43_chunk18, pack_E6970Receipt43_chunk19, pack_E6970Receipt43_chunk20, pack_E6970Receipt43_chunk21, pack_E6970Receipt43_chunk22, pack_E6970Receipt43_chunk23, pack_E6970Receipt43_chunk24, pack_E6970Receipt43_chunk25, pack_E6970Receipt43_chunk26, pack_E6970Receipt43_chunk27, pack_E6970Receipt43_chunk28, pack_E6970Receipt43_chunk29, pack_E6970Receipt43_chunk30, pack_E6970Receipt43_chunk31, pack_E6970Receipt43_chunk32, pack_E6970Receipt43_chunk33, pack_E6970Receipt43_chunk34, pack_E6970Receipt43_chunk35, pack_E6970Receipt43_chunk36, pack_E6970Receipt43_chunk37, pack_E6970Receipt43_chunk38, pack_E6970Receipt43_chunk39, pack_E6970Receipt43_chunk40, pack_E6970Receipt43_chunk41, pack_E6970Receipt43_chunk42, pack_E6970Receipt43_chunk43, pack_E6970Receipt43_chunk44, pack_E6970Receipt43_chunk45, pack_E6970Receipt43_chunk46, pack_E6970Receipt43_chunk47, pack_E6970Receipt43_chunk48, pack_E6970Receipt43_chunk49, pack_E6970Receipt43_chunk50, pack_E6970Receipt43_chunk51, pack_E6970Receipt43_chunk52, pack_E6970Receipt43_chunk53, pack_E6970Receipt43_chunk54, pack_E6970Receipt43_chunk55, pack_E6970Receipt43_chunk56, pack_E6970Receipt43_chunk57, pack_E6970Receipt43_chunk58, pack_E6970Receipt43_chunk59, pack_E6970Receipt43_chunk60, pack_E6970Receipt43_chunk61, pack_E6970Receipt43_chunk62, pack_E6970Receipt43_chunk63, pack_E6970Receipt43_chunk64, pack_E6970Receipt43_chunk65, pack_E6970Receipt43_chunk66, pack_E6970Receipt43_chunk67, pack_E6970Receipt43_chunk68, pack_E6970Receipt43_chunk69, pack_E6970Receipt43_chunk70, pack_E6970Receipt43_chunk71, pack_E6970Receipt43_chunk72, pack_E6970Receipt43_chunk73, pack_E6970Receipt43_chunk74, pack_E6970Receipt43_chunk75, pack_E6970Receipt43_chunk76, pack_E6970Receipt43_chunk77, pack_E6970Receipt43_chunk78, pack_E6970Receipt43_chunk79, pack_E6970Receipt43_chunk80, pack_E6970Receipt43_chunk81, pack_E6970Receipt43_chunk82, pack_E6970Receipt43_chunk83, pack_E6970Receipt43_chunk84, pack_E6970Receipt43_chunk85, pack_E6970Receipt43_chunk86, pack_E6970Receipt43_chunk87, pack_E6970Receipt43_chunk88, pack_E6970Receipt43_chunk89, pack_E6970Receipt43_chunk90, pack_E6970Receipt43_chunk91, pack_E6970Receipt43_chunk92, pack_E6970Receipt43_chunk93, pack_E6970Receipt43_chunk94, pack_E6970Receipt43_chunk95, pack_E6970Receipt43_chunk96, pack_E6970Receipt43_chunk97, pack_E6970Receipt43_chunk98, pack_E6970Receipt43_chunk99, pack_E6970Receipt43_chunk100, pack_E6970Receipt43_chunk101, pack_E6970Receipt43_chunk102, pack_E6970Receipt43_chunk103, pack_E6970Receipt43_chunk104, pack_E6970Receipt43_chunk105, pack_E6970Receipt43_chunk106, pack_E6970Receipt43_chunk107, pack_E6970Receipt43_chunk108, pack_E6970Receipt43_chunk109, pack_E6970Receipt43_chunk110, pack_E6970Receipt43_chunk111, pack_E6970Receipt43_chunk112, pack_E6970Receipt43_chunk113, pack_E6970Receipt43_chunk114, pack_E6970Receipt43_chunk115, pack_E6970Receipt43_chunk116, pack_E6970Receipt43_chunk117, pack_E6970Receipt43_chunk118, pack_E6970Receipt43_chunk119, pack_E6970Receipt43_chunk120, pack_E6970Receipt43_chunk121, pack_E6970Receipt43_chunk122, pack_E6970Receipt43_chunk123, pack_E6970Receipt43_chunk124, pack_E6970Receipt43_chunk125, pack_E6970Receipt43_chunk126, pack_E6970Receipt43_chunk127, pack_E6970Receipt43_chunk128, pack_E6970Receipt43_chunk129, pack_E6970Receipt43_chunk130, pack_E6970Receipt43_chunk131, pack_E6970Receipt43_chunk132, pack_E6970Receipt43_chunk133, pack_E6970Receipt43_chunk134, pack_E6970Receipt43_chunk135, pack_E6970Receipt43_chunk136, pack_E6970Receipt43_chunk137, pack_E6970Receipt43_chunk138, pack_E6970Receipt43_chunk139, pack_E6970Receipt43_chunk140, pack_E6970Receipt43_chunk141, pack_E6970Receipt43_chunk142, pack_E6970Receipt43_chunk143, pack_E6970Receipt43_chunk144, pack_E6970Receipt43_chunk145, pack_E6970Receipt43_chunk146, pack_E6970Receipt43_chunk147, pack_E6970Receipt43_chunk148, pack_E6970Receipt43_chunk149, pack_E6970Receipt43_chunk150, pack_E6970Receipt43_chunk151, pack_E6970Receipt43_chunk152, pack_E6970Receipt43_chunk153, pack_E6970Receipt43_chunk154, pack_E6970Receipt43_chunk155, pack_E6970Receipt43_chunk156, pack_E6970Receipt43_chunk157, pack_E6970Receipt43_chunk158, pack_E6970Receipt43_chunk159, pack_E6970Receipt43_chunk160, pack_E6970Receipt43_chunk161, pack_E6970Receipt43_chunk162, pack_E6970Receipt43_chunk163, pack_E6970Receipt43_chunk164, pack_E6970Receipt43_chunk165, pack_E6970Receipt43_chunk166, pack_E6970Receipt43_chunk167, pack_E6970Receipt43_chunk168, pack_E6970Receipt43_chunk169, pack_E6970Receipt43_chunk170, pack_E6970Receipt43_chunk171, pack_E6970Receipt43_chunk172, pack_E6970Receipt43_chunk173, pack_E6970Receipt43_chunk174, pack_E6970Receipt43_chunk175, pack_E6970Receipt43_chunk176, pack_E6970Receipt43_chunk177, pack_E6970Receipt43_chunk178, pack_E6970Receipt43_chunk179, pack_E6970Receipt43_chunk180, pack_E6970Receipt43_chunk181, pack_E6970Receipt43_chunk182, pack_E6970Receipt43_chunk183, pack_E6970Receipt43_chunk184, pack_E6970Receipt43_chunk185, pack_E6970Receipt43_chunk186, pack_E6970Receipt43_chunk187, pack_E6970Receipt43_chunk188, pack_E6970Receipt43_chunk189, pack_E6970Receipt43_chunk190, pack_E6970Receipt43_chunk191, pack_E6970Receipt43_chunk192, pack_E6970Receipt43_chunk193, pack_E6970Receipt43_chunk194, pack_E6970Receipt43_chunk195, pack_E6970Receipt43_chunk196, pack_E6970Receipt43_chunk197, pack_E6970Receipt43_chunk198, pack_E6970Receipt43_chunk199, pack_E6970Receipt43_chunk200, pack_E6970Receipt43_chunk201, pack_E6970Receipt43_chunk202, pack_E6970Receipt43_chunk203, pack_E6970Receipt43_chunk204, pack_E6970Receipt43_chunk205, pack_E6970Receipt43_chunk206, pack_E6970Receipt43_chunk207, pack_E6970Receipt43_chunk208, pack_E6970Receipt43_chunk209, pack_E6970Receipt43_chunk210, pack_E6970Receipt43_chunk211, pack_E6970Receipt43_chunk212, pack_E6970Receipt43_chunk213, pack_E6970Receipt43_chunk214, pack_E6970Receipt43_chunk215, pack_E6970Receipt43_chunk216, pack_E6970Receipt43_chunk217, pack_E6970Receipt43_chunk218, pack_E6970Receipt43_chunk219, pack_E6970Receipt43_chunk220, pack_E6970Receipt43_chunk221, pack_E6970Receipt43_chunk222, pack_E6970Receipt43_chunk223, pack_E6970Receipt43_chunk224, pack_E6970Receipt43_chunk225, pack_E6970Receipt43_chunk226, pack_E6970Receipt43_chunk227, pack_E6970Receipt43_chunk228, pack_E6970Receipt43_chunk229, pack_E6970Receipt43_chunk230, pack_E6970Receipt43_chunk231, pack_E6970Receipt43_chunk232, pack_E6970Receipt43_chunk233, pack_E6970Receipt43_chunk234, pack_E6970Receipt43_chunk235, pack_E6970Receipt43_chunk236, pack_E6970Receipt43_chunk237]
def rows43 := rowsFrom pack_E6970Receipt43_chunks
theorem good43 : ∀ r ∈ rows43, good 43 r = true := rowsFrom_good pack_E6970Receipt43_chunks
theorem sorted43 : rows43.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt43_chunks 0 (by decide +kernel)).1
theorem mass43 (i : Fin 61) :
    bandCount 43 (i.val : ℤ) 60 16 ≤ (rows43.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt43_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 43 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt43_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total43 : (rows43.map (price 43)).sum = 422410 :=
  (total_eq pack_E6970Receipt43_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt43

section Pack_E6970Receipt44

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt44_chunk0 := witnessA6966Final 44 60 0 720016 720141 32 3514
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk1 := witnessA6966Final 44 60 32 720142 720265 32 3456
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk2 := witnessA6966Final 44 60 64 720266 720342 32 3394
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk3 := witnessA6966Final 44 60 96 720388 720463 32 3449
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk4 := witnessA6966Final 44 60 128 720464 720584 32 3366
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk5 := witnessA6966Final 44 60 160 720585 720711 32 3193
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk6 := witnessA6966Final 44 60 192 720712 720897 32 3020
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk7 := witnessA6966Final 44 60 224 720898 721030 23 2054
  0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk8 := witnessRule 44 59 0 730015 730139 32 3319
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk9 := witnessRule 44 59 32 730140 730217 32 3250
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk10 := witnessRule 44 59 64 730263 730339 32 3282
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk11 := witnessRule 44 59 96 730340 730459 32 3266
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk12 := witnessRule 44 59 128 730460 730581 32 3137
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk13 := witnessRule 44 59 160 730582 730709 32 3007
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk14 := witnessRule 44 59 192 730710 730896 32 2851
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk15 := witnessRule 44 59 224 730897 731029 22 1892
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk16 := witnessRule 44 58 0 740014 740091 32 3147
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk17 := witnessRule 44 58 32 740138 740214 32 3143
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk18 := witnessRule 44 58 64 740215 740335 32 3136
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk19 := witnessRule 44 58 96 740336 740454 32 3102
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk20 := witnessRule 44 58 128 740455 740577 32 2946
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk21 := witnessRule 44 58 160 740578 740706 32 2867
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk22 := witnessRule 44 58 192 740707 740841 32 2739
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk23 := witnessRule 44 58 224 740896 741029 22 1832
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk24 := witnessRule 44 57 0 750013 750090 32 3039
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk25 := witnessRule 44 57 32 750091 750212 32 3033
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk26 := witnessRule 44 57 64 750213 750332 32 3021
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk27 := witnessRule 44 57 96 750333 750451 32 2947
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk28 := witnessRule 44 57 128 750452 750528 32 2800
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk29 := witnessRule 44 57 160 750576 750705 32 2749
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk30 := witnessRule 44 57 192 750706 750841 32 2637
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk31 := witnessRule 44 57 224 750896 751028 20 1616
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk32 := witnessRule 44 56 0 760012 760088 32 2962
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk33 := witnessRule 44 56 32 760089 760209 32 2953
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk34 := witnessRule 44 56 64 760210 760328 32 2931
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk35 := witnessRule 44 56 96 760329 760403 32 2800
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk36 := witnessRule 44 56 128 760448 760525 32 2744
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk37 := witnessRule 44 56 160 760526 760653 32 2626
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk38 := witnessRule 44 56 192 760704 760840 32 2554
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk39 := witnessRule 44 56 224 760896 761028 19 1490
  0x7ffef 0xb99a (by decide +kernel)
private def pack_E6970Receipt44_chunk40 := witnessRule 44 55 0 770011 770087 32 2904
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk41 := witnessRule 44 55 32 770088 770207 32 2893
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk42 := witnessRule 44 55 64 770208 770325 32 2862
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk43 := witnessRule 44 55 96 770326 770400 32 2701
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk44 := witnessRule 44 55 128 770401 770523 32 2625
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk45 := witnessRule 44 55 160 770524 770652 32 2526
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk46 := witnessRule 44 55 192 770704 770896 32 2469
  0xf7ffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt44_chunk47 := witnessRule 44 55 224 770897 771027 16 1217
  0xfffb 0xba1a (by decide +kernel)
private def pack_E6970Receipt44_chunk48 := witnessRule 44 54 0 780010 780085 32 2853
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk49 := witnessRule 44 54 32 780086 780204 32 2838
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk50 := witnessRule 44 54 64 780205 780321 32 2749
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk51 := witnessRule 44 54 96 780322 780397 32 2662
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk52 := witnessRule 44 54 128 780398 780521 32 2518
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk53 := witnessRule 44 54 160 780522 780651 32 2433
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk54 := witnessRule 44 54 192 780652 780897 32 2391
  0xf9fb7fff 0x17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt44_chunk55 := witnessRule 44 54 224 780898 781027 14 1038
  0x3ffe 0xba9a (by decide +kernel)
private def pack_E6970Receipt44_chunk56 := witnessRule 44 53 0 790009 790084 32 2810
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk57 := witnessRule 44 53 32 790085 790202 32 2791
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk58 := witnessRule 44 53 64 790203 790276 32 2608
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk59 := witnessRule 44 53 96 790320 790395 32 2613
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk60 := witnessRule 44 53 128 790396 790520 32 2420
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk61 := witnessRule 44 53 160 790521 790651 32 2347
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk62 := witnessRule 44 53 192 790704 790899 32 2318
  0xdf3e5f6f 0x176342e2ca6c9c590d8b9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt44_chunk63 := witnessRule 44 53 224 790900 791026 10 726
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk64 := witnessRule 44 52 0 800008 800082 32 2773
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk65 := witnessRule 44 52 32 800083 800199 32 2739
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk66 := witnessRule 44 52 64 800200 800273 32 2570
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk67 := witnessRule 44 52 96 800274 800393 32 2493
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk68 := witnessRule 44 52 128 800394 800519 32 2329
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk69 := witnessRule 44 52 160 800520 800651 32 2271
  0xedbfffff 0x2e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt44_chunk70 := witnessRule 44 52 192 800704 800901 32 2252
  0xfbcf8793 0x2ee685c598d938b29b17265364e4c86cdc58cc421ba9a17364364e6c66cdc590da38b19b (by decide +kernel)
private def pack_E6970Receipt44_chunk71 := witnessRule 44 52 224 800960 801026 7 499
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk72 := witnessRule 44 51 0 810007 810081 32 2744
  0xd7fff5ff 0x5716336ee2891c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt44_chunk73 := witnessRule 44 51 32 810082 810197 32 2685
  0xfffe7fff 0x19ccd3b8a2 (by decide +kernel)
private def pack_E6970Receipt44_chunk74 := witnessRule 44 51 64 810198 810271 32 2489
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk75 := witnessRule 44 51 96 810272 810392 32 2388
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk76 := witnessRule 44 51 128 810393 810519 32 2244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk77 := witnessRule 44 51 160 810520 810705 32 2202
  0x792f6dff 0x238b21b17464364e8c66cdc990da39319b574342eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt44_chunk78 := witnessRule 44 51 192 810706 810963 32 2193
  0xfffdf0f0 0xb8b39b17266364e4ca6cdc590c421bb1a17365364e6c86cdc98cc421b8b29b (by decide +kernel)
private def pack_E6970Receipt44_chunk79 := witnessRule 44 51 224 811024 811025 2 141
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk80 := witnessRule 44 50 0 820006 820079 32 2716
  0x4ffeaaff 0x4716536ee2a20ddc490bb319b27464366e4ca6d9c5854423b892 (by decide +kernel)
private def pack_E6970Receipt44_chunk81 := witnessRule 44 50 32 820080 820194 32 2601
  0xffabfff5 0x1ba319b4726436aea689d58cd9b9b21b (by decide +kernel)
private def pack_E6970Receipt44_chunk82 := witnessRule 44 50 64 820195 820269 32 2459
  0xebfffabf 0x2b9319b674348e6c66d5c590dbb8a09b (by decide +kernel)
private def pack_E6970Receipt44_chunk83 := witnessRule 44 50 96 820270 820391 32 2293
  0xe7ffd7ff 0x773350e2899c58cdc38a2 (by decide +kernel)
private def pack_E6970Receipt44_chunk84 := witnessRule 44 50 128 820392 820519 32 2167
  0x6dffffff 0x6e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt44_chunk85 := witnessRule 44 50 160 820520 820706 32 2134
  0x1e03927b 0x1b932188437166368ea620c5d194d93a321b3736331086e4ca6d1c990dab8b19884575342eac86c9d58cd9b9b21b4736336ae2c86d9c58cd8bb319b (by decide +kernel)
private def pack_E6970Receipt44_chunk86 := witnessRule 44 50 192 820707 821025 30 2010
  0x3ffffe3c 0xb9339b2716631084f0685cd98d939b29b (by decide +kernel)
private def pack_E6970Receipt44_chunk87 := witnessRule 44 49 0 830005 830078 32 2691
  0x1ffd41ff 0x15c5854ce338a918847715146cca68dd585442239b0a89885472615338ae2c2a462155c550dbb92a (by decide +kernel)
private def pack_E6970Receipt44_chunk88 := witnessRule 44 49 32 830079 830193 32 2510
  0xeaa3feaa 0x863342ecc86c9d194dab9b0a8846716151310ace2a66ddc914b0aa764342eaca6d1d1854422b930a89885 (by decide +kernel)
private def pack_E6970Receipt44_chunk89 := witnessRule 44 49 64 830194 830268 32 2385
  0x55ff557f 0x1ba321b4726536ee2c2a2121c490bbb19b27564366e6ca6d9c9854423b8a89884 (by decide +kernel)
private def pack_E6970Receipt44_chunk90 := witnessRule 44 49 96 830269 830391 32 2209
  0xaffd53fd 0x5726436cea68dd58cda39b21b57165370e2a20e1c4913b319b (by decide +kernel)
private def pack_E6970Receipt44_chunk91 := witnessRule 44 49 128 830392 830520 32 2095
  0x4976d1fe 0x13b319b37464368e8c66d5c990db39319b774342eec66cdd58cdab9b19b6716436ee6620e1c504da3a319b (by decide +kernel)
private def pack_E6970Receipt44_chunk92 := witnessRule 44 49 160 830521 830709 32 2066
  0xc3c0f00e 0x2e6ce6c9c998c42138b41b37731062e8cc6c9d194d9b9b2188437266368e2ca62111dcd0bab29b27564366e8c66210dcd94da39b21b572633108ae2ca6d9d0c418bb321b (by decide +kernel)
private def pack_E6970Receipt44_chunk93 := witnessRule 44 49 192 830710 831024 24 1576
  0xfffff7 0xbd1a (by decide +kernel)
private def pack_E6970Receipt44_chunk94 := witnessRule 44 48 0 840004 840076 32 2666
  0x3fe801ff 0x3b9288377141272c2a20c5dd8544c428bb30a99c2756152310a4e8c2a8711d18959b930aa9c572625138ce2c4a2119c948dbb8a093 (by decide +kernel)
private def pack_E6970Receipt44_chunk95 := witnessRule 44 48 32 840077 840149 32 2383
  0xa80ffe80 0x430a91b2776151086eac2a26214dd1854ce239b0a91885472615438ce4c4ad5c554dbb9289b1786151084ecc2a262149d5854ce1ba30a91885373615438ae6c4ad1c58554e338b1289c (by decide +kernel)
private def pack_E6970Receipt44_chunk96 := witnessRule 44 48 64 840192 840267 32 2361
  0x81fd407f 0xae6c2a262155c9854ce338b0a9188567154370e4a9dc5049bb29a3766151088e8c2a262151cd854ce2b930a91885571615438ee2c4addc54504e3b8a093 (by decide +kernel)
private def pack_E6970Receipt44_chunk97 := witnessRule 44 48 96 840268 840391 32 2128
  0xa3aa87aa 0x673615108ee2c2a26215dc54cdc3922963342eec86c9d594daba30a8846726151310ace2c2a671dc548c42438a8a3a61550c8685d994da3ab0a884 (by decide +kernel)
private def pack_E6970Receipt44_chunk98 := witnessRule 44 48 128 840392 840521 32 2026
  0x803904e8 0x5d994d93b321b3756331086e8ca6d1d190dab9b198845726536ce2c862119d8d0bbb21b27763366eac86d1d18cc42239b29b572643108ae2cc6e1c544c42438a08b17863364ecc86cdd58cc421ba329b (by decide +kernel)
private def pack_E6970Receipt44_chunk99 := witnessRule 44 48 160 840522 840711 32 2008
  0xfdf83c07 0xb8b51b17467364e6cc62109c9a0d9b8b39884379342eacc6c9d594d9ba32188437366368e4ca62111c59cdabb1883 (by decide +kernel)
private def pack_E6970Receipt44_chunk100 := witnessRule 44 48 192 840768 841024 19 1225
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk101 := witnessRule 44 47 0 850003 850075 32 2644
  0x7fe003ff 0x77251470c4a26c5e1895b30aa9b2766251386eac4a210dd18948e239b1289885472625338ae2c4a462155c950dbb9aa (by decide +kernel)
private def pack_E6970Receipt44_chunk102 := witnessRule 44 47 32 850076 850148 32 2285
  0xff800 0x12c2a262121854cd8bbb0a918851766154386ecc4ac9d18554e23a31289c573625108ae4c4a4719c58944c42b39299b77152472c4aa18548c423b0aa1b27762562eac2aa70dd58944e23a312884473625238ae4c4a262155c5894ce339291884 (by decide +kernel)
private def pack_E6970Receipt44_chunk103 := witnessRule 44 47 64 850192 850267 32 2257
  0x1f4007f 0x6e8c2a8715d1895a3930aa9c672625138ee2c4a211dc948dc38a093a6151062f0c2a262145dd854ce13b30a918852756154388eac4acdcd8554e2b9b1289c672625108ce2c4a471dc944c42438a893 (by decide +kernel)
private def pack_E6970Receipt44_chunk104 := witnessRule 44 47 96 850268 850392 32 2049
  0x1d401e8 0x11d58544c42a3a30a99c5736152310aae4c2a8719c5854cc42b38aa9b87251372c2a46c9e1854421bb30a898853756153388e8c2a462151cd8550e339b12b571615538ee2c4a2721c9441c38a0931796151084eec2a262149d9854ce1bab0a91885 (by decide +kernel)
private def pack_E6970Receipt44_chunk105 := witnessRule 44 47 128 850393 850523 32 1958
  0xf00e0061 0x5d998d93b329b3756431086e8cc6d1cd94c42239339b571663108af0685e18cc420bbb29b2766431084eacc6cdd194c421b9b39b573615338ce4c2a462159c58550e3b8a9988496331070ca685dd90c420bb331b (by decide +kernel)
private def pack_E6970Receipt44_chunk106 := witnessRule 44 47 160 850576 850771 32 1960
  0xffffc7c0 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt44_chunk107 := witnessRule 44 47 192 850772 850961 12 763
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk108 := witnessRule 44 46 0 860002 860073 32 2620
  0xffc017ff 0x2589441c31291b1776251310a2ecc4a6709d58948c4293a312a1c47463566e4c4aa715c98d44e339a91b (by decide +kernel)
private def pack_E6970Receipt44_chunk109 := witnessRule 44 46 32 860074 860147 32 2197
  0x1ff001 0x218948d8bc31289c2776251084ecc4a470dd58944c429ba31299c4736252310a8e4c4a8719c98d5ab92a9b77351372c4a26c5e1894420bbb1291c2766251310a4eac4a670dd18948c429b9b12a1c57363568e2c4aa719c58d44e3b9a883 (by decide +kernel)
private def pack_E6970Receipt44_chunk110 := witnessRule 44 46 64 860148 860267 32 2159
  0x1f000fe 0x4756251088e8c4a4715cd8944c42ab931299c6716252310ace4a86e1cd54b1289b1796256ec2aa6c9dd8944e1bb3128843756252388e8c4a262151cd894ce2b931291885571625438ee2c6addc94504e5312a (by decide +kernel)
private def pack_E6970Receipt44_chunk111 := witnessRule 44 46 96 860268 860393 32 1971
  0x4001c0 0x2766154386eac2a66214dd18554e239b0aa1885472615638ce4c4a471dc58944c42bb9299b87241174c2a262125854cd8bc30a918851776154384ecc2a662149d58554e23ab1289c574625108ae6c4a4719c98944c42b38b1299c7725231090e4a28e98954b0a9188486154364f0c4ac5d98554e1bb31289c (by decide +kernel)
private def pack_E6970Receipt44_chunk112 := witnessRule 44 46 128 860394 860577 32 1899
  0x3e030018 0x4e2d66cde8c418bb339b2756631084e8d06cdcd9cc421b9349b4716831088f46a194c41bb39a1766631082ead06cdd58550e23a30a99885473615538ae4c2a862155c58558e338aa98841867143390c2a86c5e1854ce13bb0a91885 (by decide +kernel)
private def pack_E6970Receipt44_chunk113 := witnessRule 44 46 160 860578 860833 32 1919
  0xfffffefc 0x2fa685cda8d939349884 (by decide +kernel)
private def pack_E6970Receipt44_chunk114 := witnessRule 44 46 192 860834 860960 6 377
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk115 := witnessRule 44 45 0 870001 870073 32 2544
  0xffc007ff 0x10c6a26c5e18d5b312a9b2766351386eac6a210dd18d48e239b1a89885472635338ae2c6a462155cd50dbba2a (by decide +kernel)
private def pack_E6970Receipt44_chunk116 := witnessRule 44 45 32 870074 870147 32 2101
  0xff000 0x9625131090c4a66c5dd8948c428bb312a1c37663564e8c4aa711d18d44e2b9b1a884572635238ce2c6a262159cd4cdbb92923963550c4a46211d8950d93bb1ab1756255386eac6a2711d18d442239b1a91c5726351310aae2c6a6719cd48c423b9a8a3 (by decide +kernel)
private def pack_E6970Receipt44_chunk117 := witnessRule 44 45 64 870192 870268 32 2068
  0x78003f 0x9d9894ce1bab1291885374625438ae8c6ad1c98954e33931a89c771635108ee6a46e1c54504a531288396252362f0c4a262145dd894ce13b312918852756254388eac6acdcd8954e2b9b1a89c672635108ce2c6a471dcd44c424392893 (by decide +kernel)
private def pack_E6970Receipt44_chunk118 := witnessRule 44 45 96 870269 870395 32 1895
  0x80030 0x430aa9b1776154310a2ecc2ac709d58554c4293a30ab9c474625338ae6c4a462155c98950e338b1299885672553630ee2a262361c5048464b1291b861543108ec2ac6c9dd8948e1bb312898853756253388e8c4a462151cd8950e2b931299885571625538ee2c6a2721cd441c392093a6251362f2c4a2105e18948e13bb1289885 (by decide +kernel)
private def pack_E6970Receipt44_chunk119 := witnessRule 44 45 128 870396 870581 32 1840
  0xf7f07002 0xb8b69b1746a364e6d262109c9acd9b8b5188437c34ec2ac6c5dd8554e13b30aa18852756156386e8c2aa6214dcd855ce23930ab1885471615838508e2c870a15ccc424b0a99884 (by decide +kernel)
private def pack_E6970Receipt44_chunk120 := witnessRule 44 45 160 870582 870960 31 1841
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk121 := witnessRule 44 44 0 880000 880072 32 2468
  0xff802fff 0x258d441c31a91b1776351310a2ecc6a6709d58d48c4293a31aa1c47464566e4c6aa715c99144e33a291b (by decide +kernel)
private def pack_E6970Receipt44_chunk122 := witnessRule 44 44 32 880073 880147 32 2017
  0xff001 0x14c6aa18d48d8bc31a89c2776351084ecc6a470dd58d44c429ba31a99c4736352310a8e4c6a8719c9915ab9aa9b77451372c6a26c5e18d4420bbb1a91c2766351310a4eac6a670dd18d48c429b9b1aa1c57364568e2c6aa719c59144e3ba2883 (by decide +kernel)
private def pack_E6970Receipt44_chunk123 := witnessRule 44 44 64 880192 880269 32 1978
  0x3c003f 0x5dd894cc428bb312a9c3766351388eac6a2111d18d48e2b9b1a89885572635338ce2c6a462159cd50dc3a2a96351362f2c6add8954d93bb1a89c3766351086eac6a4711d18d44c42a39b1a99c5726352310aae2c6a871dc5915bb9a8a09c (by decide +kernel)
private def pack_E6970Receipt44_chunk124 := witnessRule 44 44 96 880270 880397 32 1823
  0xc0040018 0x10c4a86dd8558c42330ac1b2766254386eac4a66214dd18954e239b12a1885472625638ae2c4aa62155c95cd942b8a99c9625132092c4a66c5e18948c428bbb12a1c2766253310a4eac4aa70dd18950c429b9b12b1c573635238ce4c6a262159c58d4ce3b9a918848725141194c4a40e58948c424312a1b (by decide +kernel)
private def pack_E6970Receipt44_chunk125 := witnessRule 44 44 128 880448 880584 32 1789
  0xffff8c20 0x1726d364e2d862109f8d430aa988476157362ecc2ac62145d58560e139b0ac9c282736538506e4c86214a0dc598e1423a9884 (by decide +kernel)
private def pack_E6970Receipt44_chunk126 := witnessRule 44 44 160 880640 880897 24 1402
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk127 := witnessRule 44 43 0 890000 890073 32 2340
  0xffc01fff 0x432289b1786456cc6aa6c9d99144e1bab228843746452388e6c8a262151c9914ce2b8b2291885 (by decide +kernel)
private def pack_E6970Receipt44_chunk128 := witnessRule 44 43 32 890074 890193 32 1973
  0xc01ff803 0x258d44c42431a99b1776352310a2ecc6a870dd991593a31aa9c474645138ae6c8a2115c99148e4b22a863523108ec6a86c9dd9158bab1aa9c3756451388e8c8a2111cd9148e2b932289885 (by decide +kernel)
private def pack_E6970Receipt44_chunk129 := witnessRule 44 43 64 890194 890271 32 1842
  0x2f005f 0x4b1a8988486353362f0c6a4709dd8d44c4293b31a99c3756352310a6e8c6a8711cd8d4cc42a3931aa9c672645138ee8a46e98d441cb1a91b1786351310a2eec6a6709d98d48c4293ab1aa1c47564566e6c6aa715cd9144e338b2291c (by decide +kernel)
private def pack_E6970Receipt44_chunk130 := witnessRule 44 43 96 890320 890451 32 1762
  0x8004003 0x281736738504e4cc6214a09c5a0e141bb98848625332090c4aa6c5dd8950c428bb312b1c2756255310a4e8c4ae70dcd8958c429b9312c1c2837261543a508e2c2a66218a11c554e14338990c9625232090c4a86211d8958d8bb312a98851756257386eac6a6711d18d48c42a39b1aa1c5726353310aae2c6aa719cd50c420c33928a11d (by decide +kernel)
private def pack_E6970Receipt44_chunk131 := witnessRule 44 43 128 890452 890644 32 1747
  0xfffffeeb 0xba0069d8558c822b0ad1b (by decide +kernel)
private def pack_E6970Receipt44_chunk132 := witnessRule 44 43 160 890645 890896 16 923
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk133 := witnessRule 44 42 0 900000 900073 32 2218
  0x7fc017ff 0xeeaa20e591441c32291b1776451310a2ecc8a6709d59148c4293a322a1c47465566e4c8aa715c99544e33aa91b (by decide +kernel)
private def pack_E6970Receipt44_chunk134 := witnessRule 44 42 32 900074 900194 32 1899
  0xe001fc00 0x29915432291b1786451384eec8a2109d99148e1bab22898853746453388e6c8a462151c99150e33932ab5745536eeaa26e59144d8bc3228841776452384ecc8a262149d5914ce1ba32291885373645438ae6caad1c59154e338b2a89c (by decide +kernel)
private def pack_E6970Receipt44_chunk135 := witnessRule 44 42 64 900195 900321 32 1761
  0xc001c003 0x4b1a9839635231090c6a86c5dd8d4cc428bb31aa9c2756354310a4e8c6ac711d19148e2b9b2289885572645338ce2c8a462159d150d8c3b9a88c96451370c6a66211d8d54d93bb2289c3766451086eac8a4711d19144c42a39b2299c5726452310aae2c8a871dc5955bba28a09c (by decide +kernel)
private def pack_E6970Receipt44_chunk136 := witnessRule 44 42 96 900322 900454 32 1683
  0xfb800000 0x281716a390c4a86411d8958c423312c1b1756257310a2e8c4b270a05d18554e94139b0aa18862827261563a506e2c2aa6218a0dc55ce1c239988c9625134090c6a66211d8d54d8bbb1aa1c2766353310a4eac6aa70dd18d50c429b9b1ab1c4726355310a8e2c6ae70a11c5894ce942b9291885 (by decide +kernel)
private def pack_E6970Receipt44_chunk137 := witnessRule 44 42 128 900455 900706 32 1725
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk138 := witnessRule 44 42 160 900707 900896 9 515
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk139 := witnessRule 44 41 0 910000 910074 32 2107
  0xffe00fff 0x432a89b1786556cc8aa6c9d99544e1bab2a8843746552388e6caa262151c9954ce2b8b2a91885 (by decide +kernel)
private def pack_E6970Receipt44_chunk140 := witnessRule 44 41 32 910075 910196 32 1822
  0xf803fe00 0x259144c42432299b1776452310a2ecc8a870dd995593a322a9c474655138ae6caa2115c99548e4b2aa864523108ec8a86c9dd9558bab22a9c3756551388e8caa2111cd9548e2b932a89885 (by decide +kernel)
private def pack_E6970Receipt44_chunk141 := witnessRule 44 41 64 910197 910324 32 1677
  0x38027005 0x506e4c4a66218a0dc58954ecb1a899848645336ec6aa621198d5cd93b32299c3756452310a6e8c8a8711cd914cc42a39322a9c574563650ae6a472591481cb2291b1786451310a2eec8a6709d99148c4293ab22a1c3746453310a6e6c8aa715cd9544e338b2a91c (by decide +kernel)
private def pack_E6970Receipt44_chunk142 := witnessRule 44 41 96 910325 910458 32 1624
  0xfff00900 0x21894cd023b12a9984662573208ac4b26210a158554c4294230ab9c281736156310c502e4c2b074a09c564e2413a9b8635233090c6a86211d8d58d8bb31aa98851756357384e8c6ac62149cd8d60e14139b12a1d (by decide +kernel)
private def pack_E6970Receipt44_chunk143 := witnessRule 44 41 128 910512 910832 32 1716
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk144 := witnessRule 44 41 160 910833 910833 1 57
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk145 := witnessRule 44 40 0 920000 920074 32 2000
  0x3fe00bff 0x471655538ce2cca272595441c32a91b1776551310a2eccaa6709d59548c4293a32aa1c47466566e4caaa715c99944e33b291b (by decide +kernel)
private def pack_E6970Receipt44_chunk146 := witnessRule 44 40 32 920075 920197 32 1736
  0xfc007f00 0x12caa20e19548d8bc32a89c2776551084eccaa470dd59544c429ba32a99c4736552310a8e4caa8719c9995abaaa9b96551362f0caa2105dd9548e13b32a898852756553386e8caa46214dcd9550e2b9b32b (by decide +kernel)
private def pack_E6970Receipt44_chunk147 := witnessRule 44 40 64 920198 920326 32 1605
  0xe005c00 0x140ba312a18862817362563a504e4c4aa6218a09c5895cecb1aa838645232090c8a86c5dd914cc428bb322a9c2756454310a4e8c8ac70dcd9154c429b9322b9c2837263533a508e6a87259144c8243229988476455362ecc8a862145d59158e1bab2a91c4746551310a8e6caa6715c99548c42ab8b2aa1c (by decide +kernel)
private def pack_E6970Receipt44_chunk148 := witnessRule 44 40 96 920327 920515 32 1584
  0xffff5580 0xec4a86a1158960cc214230ab1905282615a38902ee6e18d44d42431a99984763553208cc6ae621158d64d942b12a9c (by decide +kernel)
private def pack_E6970Receipt44_chunk149 := witnessRule 44 40 128 920516 920832 26 1374
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk150 := witnessRule 44 39 0 930000 930075 32 1900
  0x3ff007ff 0x8e6cca4715c99944c42c33289b1786656ccaaa6c9d99944e1bab328843746652388e6cca262151c9994ce2b8b3291885 (by decide +kernel)
private def pack_E6970Receipt44_chunk151 := witnessRule 44 39 32 930076 930199 32 1652
  0x1f007f80 0x8e4caa862151c59558e14238b2291d9655131090caa66c5dd9548c428bb32aa1c2756553310a4e8caaa711d19944e2b9b328845726652392ccaa19548c423b2aa1b27766562eacaaa70dd59944e23a332884 (by decide +kernel)
private def pack_E6970Receipt44_chunk152 := witnessRule 44 39 64 930200 930329 32 1533
  0xc00f00 0x198d58cc22b1ac19042856254320a508c4ac6214a0d8960e140b9312b98862817162593a902e2c2aa7619144d02432299904764553108cc8ae6c5d59158c428ba322c1c2817463543a504e6c6a66218a09c98d54e941b8b1aa188696454070caa46211d9550d8bbb2a99c2766552310a4eacaa870dd1954cc429b9b2aa9c (by decide +kernel)
private def pack_E6970Receipt44_chunk153 := witnessRule 44 39 96 930330 930519 32 1560
  0xfffffffc 0x218d48d423b1aa1a04 (by decide +kernel)
private def pack_E6970Receipt44_chunk154 := witnessRule 44 39 128 930576 930832 19 992
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk155 := witnessRule 44 38 0 940000 940075 32 1800
  0xff005ff 0xdcd9950e2b9b3ab471665538ce2cea272599441c33291b1776651310a2eccca6709d59948c4293a332a1c47467566e4ccaa715c99d44e33ba91b (by decide +kernel)
private def pack_E6970Receipt44_chunk156 := witnessRule 44 38 32 940076 940200 32 1571
  0x7802fc0 0x139b2ab9c2827364533a506e4c8a46218a0dc59150e9423a29988596553070cca46dd9550c42332ab1b2766652386eacca26214dd1994ce239b3291885472665438aecaa6e59944d8bc3328841776652384eccca262149d5994ce1ba33291885 (by decide +kernel)
private def pack_E6970Receipt44_chunk157 := witnessRule 44 38 64 940201 940331 32 1476
  0x1001c0 0x863513708ec6a66c1198d54d422b1ab9a042856253340a508c4aa6614a0d895cc82941312c98854826155310a902c2ae71205c558c42c322b03864523408ec8a8661199158c822b22c18842856354310a508c6ac70a05cd8d54c43140b931ab9d282716356310c504e6b07219544cc2432a9988476555362eccaa862145d59558e13a32aa9885 (by decide +kernel)
private def pack_E6970Receipt44_chunk158 := witnessRule 44 38 96 940384 940579 32 1541
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk159 := witnessRule 44 38 128 940580 940769 12 617
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk160 := witnessRule 44 37 0 950000 950076 32 1703
  0xff803ff 0x1bab3a89c4746751088e6cea4715c99d44c42c33a89b1786756cccaa6c9d99d44e1bab3a8843746752388e6cea262151c99d4ce2b8b3a91885 (by decide +kernel)
private def pack_E6970Receipt44_chunk161 := witnessRule 44 37 32 950077 950202 32 1491
  0x2e00be0 0x159560d942b22a1c281746453310c502e6c8aa74a09c99150c4314138b22b1d3837351433b0cca264121994cd8bbb32918851766654384eacca662149d19954e1b9b32a1885372665638506e4caa474a11d54ce4b32903866523108ecca86c5d9994cc428bab32a9c (by decide +kernel)
private def pack_E6970Receipt44_chunk162 := witnessRule 44 37 64 950203 950386 32 1434
  0xf5540030 0x3b1a91c04563563608508c4a86a14a098960cc2a40b0ab190558146370c8a26c11d914cd423322a9a0456457330850ac6a66614a118d54c82941b1ab9885282635938904c4aa71205c58950c43240b92b1c86555070caa46611d9550c82332ab1884 (by decide +kernel)
private def pack_E6970Receipt44_chunk163 := witnessRule 44 37 96 950387 950642 32 1525
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk164 := witnessRule 44 37 128 950643 950768 5 255
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk165 := witnessRule 44 36 0 960000 960076 32 1608
  0x13f802ff 0x4eacea670dd19d48c429b9b3aa1c471675538508e2cca27659d441c33a91b1776751310a2eccea6709d59d48c4293a33aa1c47468566e4ceaa715c9a144e33c291b (by decide +kernel)
private def pack_E6970Receipt44_chunk166 := witnessRule 44 36 32 960077 960203 32 1418
  0x7003f0 0xccaaa66115955cc82142b22999052846455310a506c8ae70a05c99158c43140b8b22c1d4817163543a904e6a66216199501c33291904766543108cccac6c5d59954c428ba332b9c2817465533a504e6caa46218a09c99550e941b8b2a99886867513108ecea66c5dd9d48e13b33a89885 (by decide +kernel)
private def pack_E6970Receipt44_chunk167 := witnessRule 44 36 64 960204 960389 32 1402
  0xfffff40c 0x2b22b1a842846354340a506c6ac6614a098d60c82a41312a19054816256310a904b06e19544d423b2a99a04 (by decide +kernel)
private def pack_E6970Receipt44_chunk168 := witnessRule 44 36 96 960390 960768 31 1464
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk169 := witnessRule 44 35 0 970000 970077 32 1516
  0x1fc01ff 0x1766753310a2eaceaa709d19d50c42939b3ab1c2827366523a506e4cca26218a0dc5994cec34289b767533108cceaa6c9d9a144e1bab428843746852388e6d0a262151c9a14ce2b8b4291885 (by decide +kernel)
private def pack_E6970Receipt44_chunk170 := witnessRule 44 35 32 970078 970205 32 1355
  0x800c0278 0x765523608ccaa86a1159558d02142b2291a052846454330a506c8ac6414a099160c42a4131aa1885481635638902e6aa6215209c9450cc47433289a04766533308cccaa64115995cc42142b2a99885284655538502e6caa86218a05c99558e9413aab9c4827453390cea60e19d48c423b3aa1b (by decide +kernel)
private def pack_E6970Receipt44_chunk171 := witnessRule 44 35 64 970256 970392 32 1375
  0xfffff541 0x764513908ac8aa6e10a118d4cd8294131ab9a054826253340a902c4aa66152095cc822c0a8a29885 (by decide +kernel)
private def pack_E6970Receipt44_chunk172 := witnessRule 44 35 96 970448 970705 24 1113
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk173 := witnessRule 44 34 0 980000 980077 32 1426
  0x17c017f 0x199d54c422b3ab9b285665338502e8cca46218a05cd9950e94139332998862827166553a706eaa284761a1481c34291b1776851310a2ecd0a6709d5a148c4293a342a1c3736853310a6e4d0aa70a0dc99d44e9423ba91c (by decide +kernel)
private def pack_E6970Receipt44_chunk174 := witnessRule 44 34 32 980078 980257 32 1304
  0x7506003c 0x2c0a8a21985565553608508c8a66a14a09915ccc2a4131a999854816355320a906ae62116094514e4332b03766523508ccca8681159958cc2142b2a919852846554320a506caac6214a099560e241322a1c481716453310c902e8aa7219d44cc23b3a99904 (by decide +kernel)
private def pack_E6970Receipt44_chunk175 := witnessRule 44 34 64 980258 980450 32 1349
  0xfffffef5 0xcc8a47410a098d58d82a40b12a1a85 (by decide +kernel)
private def pack_E6970Receipt44_chunk176 := witnessRule 44 34 96 980451 980704 18 819
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk177 := witnessRule 44 33 0 990000 990078 32 1344
  0x7e00ff 0x1d9d48d02333aa198456756320850acca46414a119950c42941b32b1c281726655310c502e2ccae75205c5954cec34289904768533108cd0aa6c5d5a150c428ba342b1c2817467523a504e6cea26218a09c99d4ce941b8b3a91886 (by decide +kernel)
private def pack_E6970Receipt44_chunk178 := witnessRule 44 33 32 990079 990259 32 1263
  0xffd0fa0e 0x2826456350a902c6a8681520d58cc22c128a21905581715143321c508caa66814a09955cc82a41322999054816455310a908ae6d605cd4cc46c33aa83 (by decide +kernel)
private def pack_E6970Receipt44_chunk179 := witnessRule 44 33 64 990260 990454 32 1327
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk180 := witnessRule 44 33 96 990512 990704 12 539
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk181 := witnessRule 44 32 0 1000000 1000078 32 1270
  0x401e017f 0xecea26c1159d54d02142b3289a052846653330a506ccaa6414a09995cc42a4132a99885481655538902eaa86215209d14508c474342a03768523308cd0a864115a158c42142b3a91885284675438502e6cea66218a05c99d54e9413bab1c (by decide +kernel)
private def pack_E6970Receipt44_chunk182 := witnessRule 44 32 32 1000128 1000261 32 1225
  0xfd7a6547 0x665513b088caaa72112058d4cd82ac128a19a056815332110accca4701159950dc214232a91b052826556340a902c8a8661521158c822c1a8a21885 (by decide +kernel)
private def pack_E6970Receipt44_chunk183 := witnessRule 44 32 64 1000262 1000515 32 1307
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk184 := witnessRule 44 32 96 1000516 1000641 6 265
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk185 := witnessRule 44 31 0 1010000 1010128 32 1212
  0xda8f00bf 0xccea46e10a119948d42941332b19854816554320a90aac62116114510e3b4289a84668533408ad0aa6610a159d44cc294233a999052836755310a504ceae71209994ce240bb2a1c (by decide +kernel)
private def pack_E6970Receipt44_chunk186 := witnessRule 44 31 32 1010129 1010263 32 1183
  0xffbfade9 0xacaa478116094508d82b40a1998c466553808902c8a66a1560d450ccc2b4129990c (by decide +kernel)
private def pack_E6970Receipt44_chunk187 := witnessRule 44 31 64 1010264 1010640 32 1294
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk188 := witnessRule 44 30 0 1020000 1020129 32 1155
  0xffa7fd3f 0x1205954cd02ac228a19905581735142321c504ceac64152059950c42a432b1b (by decide +kernel)
private def pack_E6970Receipt44_chunk189 := witnessRule 44 30 32 1020130 1020265 32 1151
  0xfffffffd 0x2c1a8a11a85 (by decide +kernel)
private def pack_E6970Receipt44_chunk190 := witnessRule 44 30 64 1020320 1020640 27 1068
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk191 := witnessRule 44 29 0 1030000 1030130 32 1102
  0xb2f7a55f 0xd02a28466221959d48e82233aa1c842836652380ab08a28468159a144e022342a9b042846751360a504ceaa6815205994ccc2ac2a8a19885 (by decide +kernel)
private def pack_E6970Receipt44_chunk192 := witnessRule 44 29 32 1030131 1030322 32 1126
  0xfffffebf 0x159944f421b32a9d84 (by decide +kernel)
private def pack_E6970Receipt44_chunk193 := witnessRule 44 29 64 1030323 1030577 21 810
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk194 := witnessRule 44 28 0 1040000 1040131 32 1052
  0xfdfddbdf 0x1b3aa9d046825142331aad0a47210a0d9d48dc2ac2a8a11985 (by decide +kernel)
private def pack_E6970Receipt44_chunk195 := witnessRule 44 28 32 1040132 1040324 32 1099
  0xffffffbf 0x233291f04 (by decide +kernel)
private def pack_E6970Receipt44_chunk196 := witnessRule 44 28 64 1040325 1040576 16 603
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk197 := witnessRule 44 27 0 1050000 1050132 32 1010
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk198 := witnessRule 44 27 32 1050133 1050384 32 1075
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk199 := witnessRule 44 27 64 1050385 1050576 11 407
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk200 := witnessRule 44 26 0 1060000 1060133 32 969
  0xfd7fe5ff 0x233a89f84267553d088d0a47810da150ec214133a91d05 (by decide +kernel)
private def pack_E6970Receipt44_chunk201 := witnessRule 44 26 32 1060134 1060387 32 1051
  0xfffffff7 0x6cca468804 (by decide +kernel)
private def pack_E6970Receipt44_chunk202 := witnessRule 44 26 64 1060388 1060513 6 217
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk203 := witnessRule 44 25 0 1070000 1070134 32 931
  0xff7ffbff 0x36752340021342a9e04 (by decide +kernel)
private def pack_E6970Receipt44_chunk204 := witnessRule 44 25 32 1070135 1070450 32 1032
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk205 := witnessRule 44 25 64 1070512 1070512 1 36
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk206 := witnessRule 44 24 0 1080000 1080135 32 896
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk207 := witnessRule 44 24 32 1080136 1080512 29 910
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk208 := witnessRule 44 23 0 1090000 1090136 32 863
  0xffdff5ff 0x4cea46980436851344020b42a9f84 (by decide +kernel)
private def pack_E6970Receipt44_chunk209 := witnessRule 44 23 32 1090192 1090449 24 729
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk210 := witnessRule 44 22 0 1100000 1100192 32 831
  0xfffffbff 0x4d0a469004 (by decide +kernel)
private def pack_E6970Receipt44_chunk211 := witnessRule 44 22 32 1100193 1100448 20 587
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk212 := witnessRule 44 21 0 1110000 1110194 32 803
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk213 := witnessRule 44 21 32 1110195 1110448 16 455
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk214 := witnessRule 44 20 0 1120000 1120195 32 773
  0xfffffdff 0x2d0a46a804 (by decide +kernel)
private def pack_E6970Receipt44_chunk215 := witnessRule 44 20 32 1120196 1120385 12 329
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk216 := witnessRule 44 19 0 1130000 1130197 32 745
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk217 := witnessRule 44 19 32 1130256 1130384 8 213
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk218 := witnessRule 44 18 0 1140000 1140257 32 717
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk219 := witnessRule 44 18 32 1140258 1140384 5 129
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk220 := witnessRule 44 17 0 1150000 1150320 32 692
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk221 := witnessRule 44 17 32 1150321 1150321 1 25
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk222 := witnessRule 44 16 0 1160000 1160320 30 618
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk223 := witnessRule 44 15 0 1170000 1170320 27 528
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk224 := witnessRule 44 14 0 1180000 1180257 24 441
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk225 := witnessRule 44 13 0 1190000 1190256 21 363
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk226 := witnessRule 44 12 0 1200000 1200256 19 308
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk227 := witnessRule 44 11 0 1210000 1210193 16 241
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk228 := witnessRule 44 10 0 1220000 1220192 14 195
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk229 := witnessRule 44 9 0 1230000 1230192 12 155
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk230 := witnessRule 44 8 0 1240000 1240129 10 117
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk231 := witnessRule 44 7 0 1250000 1250128 8 85
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk232 := witnessRule 44 6 0 1260000 1260128 7 67
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk233 := witnessRule 44 5 0 1270000 1270065 5 42
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk234 := witnessRule 44 4 0 1280000 1280064 4 29
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk235 := witnessRule 44 3 0 1290000 1290064 3 19
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk236 := witnessRule 44 2 0 1300000 1300001 2 10
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk237 := witnessRule 44 1 0 1310000 1310000 1 4
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt44_chunk238 := witnessRule 44 0 0 1320000 1320000 1 3
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt44_chunks : List (Chunk 44) := [pack_E6970Receipt44_chunk0, pack_E6970Receipt44_chunk1, pack_E6970Receipt44_chunk2, pack_E6970Receipt44_chunk3, pack_E6970Receipt44_chunk4, pack_E6970Receipt44_chunk5, pack_E6970Receipt44_chunk6, pack_E6970Receipt44_chunk7, pack_E6970Receipt44_chunk8, pack_E6970Receipt44_chunk9, pack_E6970Receipt44_chunk10, pack_E6970Receipt44_chunk11, pack_E6970Receipt44_chunk12, pack_E6970Receipt44_chunk13, pack_E6970Receipt44_chunk14, pack_E6970Receipt44_chunk15, pack_E6970Receipt44_chunk16, pack_E6970Receipt44_chunk17, pack_E6970Receipt44_chunk18, pack_E6970Receipt44_chunk19, pack_E6970Receipt44_chunk20, pack_E6970Receipt44_chunk21, pack_E6970Receipt44_chunk22, pack_E6970Receipt44_chunk23, pack_E6970Receipt44_chunk24, pack_E6970Receipt44_chunk25, pack_E6970Receipt44_chunk26, pack_E6970Receipt44_chunk27, pack_E6970Receipt44_chunk28, pack_E6970Receipt44_chunk29, pack_E6970Receipt44_chunk30, pack_E6970Receipt44_chunk31, pack_E6970Receipt44_chunk32, pack_E6970Receipt44_chunk33, pack_E6970Receipt44_chunk34, pack_E6970Receipt44_chunk35, pack_E6970Receipt44_chunk36, pack_E6970Receipt44_chunk37, pack_E6970Receipt44_chunk38, pack_E6970Receipt44_chunk39, pack_E6970Receipt44_chunk40, pack_E6970Receipt44_chunk41, pack_E6970Receipt44_chunk42, pack_E6970Receipt44_chunk43, pack_E6970Receipt44_chunk44, pack_E6970Receipt44_chunk45, pack_E6970Receipt44_chunk46, pack_E6970Receipt44_chunk47, pack_E6970Receipt44_chunk48, pack_E6970Receipt44_chunk49, pack_E6970Receipt44_chunk50, pack_E6970Receipt44_chunk51, pack_E6970Receipt44_chunk52, pack_E6970Receipt44_chunk53, pack_E6970Receipt44_chunk54, pack_E6970Receipt44_chunk55, pack_E6970Receipt44_chunk56, pack_E6970Receipt44_chunk57, pack_E6970Receipt44_chunk58, pack_E6970Receipt44_chunk59, pack_E6970Receipt44_chunk60, pack_E6970Receipt44_chunk61, pack_E6970Receipt44_chunk62, pack_E6970Receipt44_chunk63, pack_E6970Receipt44_chunk64, pack_E6970Receipt44_chunk65, pack_E6970Receipt44_chunk66, pack_E6970Receipt44_chunk67, pack_E6970Receipt44_chunk68, pack_E6970Receipt44_chunk69, pack_E6970Receipt44_chunk70, pack_E6970Receipt44_chunk71, pack_E6970Receipt44_chunk72, pack_E6970Receipt44_chunk73, pack_E6970Receipt44_chunk74, pack_E6970Receipt44_chunk75, pack_E6970Receipt44_chunk76, pack_E6970Receipt44_chunk77, pack_E6970Receipt44_chunk78, pack_E6970Receipt44_chunk79, pack_E6970Receipt44_chunk80, pack_E6970Receipt44_chunk81, pack_E6970Receipt44_chunk82, pack_E6970Receipt44_chunk83, pack_E6970Receipt44_chunk84, pack_E6970Receipt44_chunk85, pack_E6970Receipt44_chunk86, pack_E6970Receipt44_chunk87, pack_E6970Receipt44_chunk88, pack_E6970Receipt44_chunk89, pack_E6970Receipt44_chunk90, pack_E6970Receipt44_chunk91, pack_E6970Receipt44_chunk92, pack_E6970Receipt44_chunk93, pack_E6970Receipt44_chunk94, pack_E6970Receipt44_chunk95, pack_E6970Receipt44_chunk96, pack_E6970Receipt44_chunk97, pack_E6970Receipt44_chunk98, pack_E6970Receipt44_chunk99, pack_E6970Receipt44_chunk100, pack_E6970Receipt44_chunk101, pack_E6970Receipt44_chunk102, pack_E6970Receipt44_chunk103, pack_E6970Receipt44_chunk104, pack_E6970Receipt44_chunk105, pack_E6970Receipt44_chunk106, pack_E6970Receipt44_chunk107, pack_E6970Receipt44_chunk108, pack_E6970Receipt44_chunk109, pack_E6970Receipt44_chunk110, pack_E6970Receipt44_chunk111, pack_E6970Receipt44_chunk112, pack_E6970Receipt44_chunk113, pack_E6970Receipt44_chunk114, pack_E6970Receipt44_chunk115, pack_E6970Receipt44_chunk116, pack_E6970Receipt44_chunk117, pack_E6970Receipt44_chunk118, pack_E6970Receipt44_chunk119, pack_E6970Receipt44_chunk120, pack_E6970Receipt44_chunk121, pack_E6970Receipt44_chunk122, pack_E6970Receipt44_chunk123, pack_E6970Receipt44_chunk124, pack_E6970Receipt44_chunk125, pack_E6970Receipt44_chunk126, pack_E6970Receipt44_chunk127, pack_E6970Receipt44_chunk128, pack_E6970Receipt44_chunk129, pack_E6970Receipt44_chunk130, pack_E6970Receipt44_chunk131, pack_E6970Receipt44_chunk132, pack_E6970Receipt44_chunk133, pack_E6970Receipt44_chunk134, pack_E6970Receipt44_chunk135, pack_E6970Receipt44_chunk136, pack_E6970Receipt44_chunk137, pack_E6970Receipt44_chunk138, pack_E6970Receipt44_chunk139, pack_E6970Receipt44_chunk140, pack_E6970Receipt44_chunk141, pack_E6970Receipt44_chunk142, pack_E6970Receipt44_chunk143, pack_E6970Receipt44_chunk144, pack_E6970Receipt44_chunk145, pack_E6970Receipt44_chunk146, pack_E6970Receipt44_chunk147, pack_E6970Receipt44_chunk148, pack_E6970Receipt44_chunk149, pack_E6970Receipt44_chunk150, pack_E6970Receipt44_chunk151, pack_E6970Receipt44_chunk152, pack_E6970Receipt44_chunk153, pack_E6970Receipt44_chunk154, pack_E6970Receipt44_chunk155, pack_E6970Receipt44_chunk156, pack_E6970Receipt44_chunk157, pack_E6970Receipt44_chunk158, pack_E6970Receipt44_chunk159, pack_E6970Receipt44_chunk160, pack_E6970Receipt44_chunk161, pack_E6970Receipt44_chunk162, pack_E6970Receipt44_chunk163, pack_E6970Receipt44_chunk164, pack_E6970Receipt44_chunk165, pack_E6970Receipt44_chunk166, pack_E6970Receipt44_chunk167, pack_E6970Receipt44_chunk168, pack_E6970Receipt44_chunk169, pack_E6970Receipt44_chunk170, pack_E6970Receipt44_chunk171, pack_E6970Receipt44_chunk172, pack_E6970Receipt44_chunk173, pack_E6970Receipt44_chunk174, pack_E6970Receipt44_chunk175, pack_E6970Receipt44_chunk176, pack_E6970Receipt44_chunk177, pack_E6970Receipt44_chunk178, pack_E6970Receipt44_chunk179, pack_E6970Receipt44_chunk180, pack_E6970Receipt44_chunk181, pack_E6970Receipt44_chunk182, pack_E6970Receipt44_chunk183, pack_E6970Receipt44_chunk184, pack_E6970Receipt44_chunk185, pack_E6970Receipt44_chunk186, pack_E6970Receipt44_chunk187, pack_E6970Receipt44_chunk188, pack_E6970Receipt44_chunk189, pack_E6970Receipt44_chunk190, pack_E6970Receipt44_chunk191, pack_E6970Receipt44_chunk192, pack_E6970Receipt44_chunk193, pack_E6970Receipt44_chunk194, pack_E6970Receipt44_chunk195, pack_E6970Receipt44_chunk196, pack_E6970Receipt44_chunk197, pack_E6970Receipt44_chunk198, pack_E6970Receipt44_chunk199, pack_E6970Receipt44_chunk200, pack_E6970Receipt44_chunk201, pack_E6970Receipt44_chunk202, pack_E6970Receipt44_chunk203, pack_E6970Receipt44_chunk204, pack_E6970Receipt44_chunk205, pack_E6970Receipt44_chunk206, pack_E6970Receipt44_chunk207, pack_E6970Receipt44_chunk208, pack_E6970Receipt44_chunk209, pack_E6970Receipt44_chunk210, pack_E6970Receipt44_chunk211, pack_E6970Receipt44_chunk212, pack_E6970Receipt44_chunk213, pack_E6970Receipt44_chunk214, pack_E6970Receipt44_chunk215, pack_E6970Receipt44_chunk216, pack_E6970Receipt44_chunk217, pack_E6970Receipt44_chunk218, pack_E6970Receipt44_chunk219, pack_E6970Receipt44_chunk220, pack_E6970Receipt44_chunk221, pack_E6970Receipt44_chunk222, pack_E6970Receipt44_chunk223, pack_E6970Receipt44_chunk224, pack_E6970Receipt44_chunk225, pack_E6970Receipt44_chunk226, pack_E6970Receipt44_chunk227, pack_E6970Receipt44_chunk228, pack_E6970Receipt44_chunk229, pack_E6970Receipt44_chunk230, pack_E6970Receipt44_chunk231, pack_E6970Receipt44_chunk232, pack_E6970Receipt44_chunk233, pack_E6970Receipt44_chunk234, pack_E6970Receipt44_chunk235, pack_E6970Receipt44_chunk236, pack_E6970Receipt44_chunk237, pack_E6970Receipt44_chunk238]
def rows44 := rowsFrom pack_E6970Receipt44_chunks
theorem good44 : ∀ r ∈ rows44, good 44 r = true := rowsFrom_good pack_E6970Receipt44_chunks
theorem sorted44 : rows44.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt44_chunks 0 (by decide +kernel)).1
theorem mass44 (i : Fin 61) :
    bandCount 44 (i.val : ℤ) 60 16 ≤ (rows44.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt44_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 44 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt44_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total44 : (rows44.map (price 44)).sum = 422055 :=
  (total_eq pack_E6970Receipt44_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt44

section Pack_E6970Receipt45

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt45_chunk0 := witnessA6966Final 45 60 0 750015 750092 32 3520
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk1 := witnessA6966Final 45 60 32 750139 750215 32 3518
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk2 := witnessA6966Final 45 60 64 750216 750336 32 3500
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk3 := witnessA6966Final 45 60 96 750337 750455 32 3442
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk4 := witnessA6966Final 45 60 128 750456 750576 32 3315
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk5 := witnessA6966Final 45 60 160 750577 750655 32 3236
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk6 := witnessA6966Final 45 60 192 750704 750836 32 3111
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk7 := witnessA6966Final 45 60 224 750837 751030 31 2768
  0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk8 := witnessRule 45 59 0 760014 760091 32 3344
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk9 := witnessRule 45 59 32 760092 760213 32 3338
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk10 := witnessRule 45 59 64 760214 760333 32 3309
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk11 := witnessRule 45 59 96 760334 760451 32 3229
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk12 := witnessRule 45 59 128 760452 760527 32 3151
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk13 := witnessRule 45 59 160 760528 760652 32 3045
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk14 := witnessRule 45 59 192 760653 760835 32 2899
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk15 := witnessRule 45 59 224 760836 761029 30 2558
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk16 := witnessRule 45 58 0 770013 770089 32 3189
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk17 := witnessRule 45 58 32 770090 770210 32 3182
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk18 := witnessRule 45 58 64 770211 770329 32 3139
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk19 := witnessRule 45 58 96 770330 770404 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk20 := witnessRule 45 58 128 770448 770524 32 3046
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk21 := witnessRule 45 58 160 770525 770650 32 2862
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk22 := witnessRule 45 58 192 770651 770834 32 2740
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk23 := witnessRule 45 58 224 770835 771029 29 2388
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk24 := witnessRule 45 57 0 780012 780088 32 3067
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk25 := witnessRule 45 57 32 780089 780208 32 3058
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk26 := witnessRule 45 57 64 780209 780326 32 3009
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk27 := witnessRule 45 57 96 780327 780400 32 2922
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk28 := witnessRule 45 57 128 780401 780521 32 2854
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk29 := witnessRule 45 57 160 780522 780648 32 2718
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk30 := witnessRule 45 57 192 780649 780834 32 2627
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk31 := witnessRule 45 57 224 780835 781028 27 2152
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk32 := witnessRule 45 56 0 790011 790086 32 2976
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk33 := witnessRule 45 56 32 790087 790205 32 2961
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk34 := witnessRule 45 56 64 790206 790322 32 2878
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk35 := witnessRule 45 56 96 790323 790397 32 2839
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk36 := witnessRule 45 56 128 790398 790519 32 2703
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk37 := witnessRule 45 56 160 790520 790647 32 2607
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk38 := witnessRule 45 56 192 790648 790834 32 2528
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk39 := witnessRule 45 56 224 790835 791028 25 1934
  0x1fffbff 0xb99a (by decide +kernel)
private def pack_E6970Receipt45_chunk40 := witnessRule 45 55 0 800010 800085 32 2915
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk41 := witnessRule 45 55 32 800086 800203 32 2896
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk42 := witnessRule 45 55 64 800204 800277 32 2732
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk43 := witnessRule 45 55 96 800320 800394 32 2812
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk44 := witnessRule 45 55 128 800395 800517 32 2586
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk45 := witnessRule 45 55 160 800518 800646 32 2509
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk46 := witnessRule 45 55 192 800647 800835 32 2441
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk47 := witnessRule 45 55 224 800836 801027 22 1652
  0x3ffefd 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt45_chunk48 := witnessRule 45 54 0 810009 810083 32 2862
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk49 := witnessRule 45 54 32 810084 810200 32 2835
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk50 := witnessRule 45 54 64 810201 810274 32 2679
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk51 := witnessRule 45 54 96 810275 810392 32 2668
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk52 := witnessRule 45 54 128 810393 810516 32 2483
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk53 := witnessRule 45 54 160 810517 810646 32 2414
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk54 := witnessRule 45 54 192 810647 810836 32 2361
  0x3f6fffff 0x17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt45_chunk55 := witnessRule 45 54 224 810837 811027 19 1389
  0x7ffdf 0xba9a (by decide +kernel)
private def pack_E6970Receipt45_chunk56 := witnessRule 45 53 0 820008 820082 32 2818
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk57 := witnessRule 45 53 32 820083 820198 32 2776
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk58 := witnessRule 45 53 64 820199 820271 32 2631
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk59 := witnessRule 45 53 96 820272 820390 32 2538
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk60 := witnessRule 45 53 128 820391 820515 32 2387
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk61 := witnessRule 45 53 160 820516 820646 32 2328
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk62 := witnessRule 45 53 192 820647 820838 32 2286
  0xe7cbedff 0x2e2ca6c9c590d8b9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt45_chunk63 := witnessRule 45 53 224 820839 821026 15 1071
  0x7ffb 0xbb1a (by decide +kernel)
private def pack_E6970Receipt45_chunk64 := witnessRule 45 52 0 830007 830080 32 2779
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk65 := witnessRule 45 52 32 830081 830195 32 2683
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk66 := witnessRule 45 52 64 830196 830269 32 2577
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk67 := witnessRule 45 52 96 830270 830389 32 2424
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk68 := witnessRule 45 52 128 830390 830515 32 2296
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk69 := witnessRule 45 52 160 830516 830647 32 2249
  0xdbffffff 0xdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt45_chunk70 := witnessRule 45 52 192 830648 830897 32 2217
  0xbcf8793e 0x177342e2cc6c9c594d8b9329b27264366e2c66210dd4d0b9b21b27363366e2c86d1c58cd8ba319b (by decide +kernel)
private def pack_E6970Receipt45_chunk71 := witnessRule 45 52 224 830898 831026 11 770
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk72 := witnessRule 45 51 0 840006 840079 32 2749
  0xfffffcff 0x19ccd3b8a2 (by decide +kernel)
private def pack_E6970Receipt45_chunk73 := witnessRule 45 51 32 840080 840193 32 2598
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk74 := witnessRule 45 51 64 840194 840267 32 2526
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk75 := witnessRule 45 51 96 840268 840388 32 2322
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk76 := witnessRule 45 51 128 840389 840515 32 2212
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk77 := witnessRule 45 51 160 840516 840648 32 2175
  0x92f6dfff 0x17464364e8c66cdc990da39319b574342eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt45_chunk78 := witnessRule 45 51 192 840649 840900 32 2156
  0xffdf0f07 0x5c59cd8b9331b27265366e2c86210dd8d0b9b29b27364366e4c66210dc594da38b21b (by decide +kernel)
private def pack_E6970Receipt45_chunk79 := witnessRule 45 51 224 840960 841025 6 414
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk80 := witnessRule 45 50 0 850005 850077 32 2719
  0xbfffabff 0x77141366e8c66d1c990daba9a (by decide +kernel)
private def pack_E6970Receipt45_chunk81 := witnessRule 45 50 32 850078 850150 32 2453
  0xffaffffa 0x5726336ce8691cd8cdab8b21b (by decide +kernel)
private def pack_E6970Receipt45_chunk82 := witnessRule 45 50 64 850192 850266 32 2500
  0xe7fffaff 0x773350e2899c58cdc38a2 (by decide +kernel)
private def pack_E6970Receipt45_chunk83 := witnessRule 45 50 96 850267 850388 32 2231
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk84 := witnessRule 45 50 128 850389 850516 32 2134
  0x6fffffff 0x15c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt45_chunk85 := witnessRule 45 50 160 850517 850650 32 2102
  0xf01c93db 0x2e8ca6c9d190d9b9b1988437265368e4c86d5c58cc422ba9a17564364eac66cdcd90da39b19b5716436ce2c66c5d98cd9ba319b (by decide +kernel)
private def pack_E6970Receipt45_chunk86 := witnessRule 45 50 192 850704 851024 32 2110
  0xfffff1e0 0x17267364e2cc62109e0d0b9b31b27365366e4c86210dc598da3a9883 (by decide +kernel)
private def pack_E6970Receipt45_chunk87 := witnessRule 45 50 224 851025 851025 1 69
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk88 := witnessRule 45 49 0 860004 860076 32 2697
  0x7ff551ff 0x7715131090c6685d990d93a329b573615108ce2c2a262159c54cdbb922 (by decide +kernel)
private def pack_E6970Receipt45_chunk89 := witnessRule 45 49 32 860077 860148 32 2414
  0xeaafff55 0x13b319b37464368e4ca6ddc5854424389217763364eac86cdcd94db3930a884 (by decide +kernel)
private def pack_E6970Receipt45_chunk90 := witnessRule 45 49 64 860149 860265 32 2379
  0x5fff54ff 0xae4c86d9d4d1bab19b4736436ae2ca6e1c5441c3892 (by decide +kernel)
private def pack_E6970Receipt45_chunk91 := witnessRule 45 49 96 860266 860388 32 2148
  0xbffd5ffd 0x3ba1a5736336ce2c86e1c504da3a319b (by decide +kernel)
private def pack_E6970Receipt45_chunk92 := witnessRule 45 49 128 860389 860517 32 2064
  0x4bb6dffe 0x23a319b5726436ce4c66ddd0d0bbb19b3756336ae6c66ddc58cdb39319b (by decide +kernel)
private def pack_E6970Receipt45_chunk93 := witnessRule 45 49 160 860518 860706 32 2037
  0x1e078072 0x2726631084e2d06cddcc418ba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b (by decide +kernel)
private def pack_E6970Receipt45_chunk94 := witnessRule 45 49 192 860707 861024 27 1740
  0x7ffffbe 0x5e8d0b9b39b (by decide +kernel)
private def pack_E6970Receipt45_chunk95 := witnessRule 45 48 0 870003 870074 32 2670
  0x7fea03ff 0x1dc5049c30a91b2776151086eac2a26214dd1854ce239b0a91885472615438ce4c4ad5c554dbb9289b (by decide +kernel)
private def pack_E6970Receipt45_chunk96 := witnessRule 45 48 32 870075 870147 32 2317
  0x540ffd40 0x4321a17665368eac2a2115cd8544c42ab930a99c6716152310ace2a86e1c953b8a093765346ecc2a2111d18544c42a39b0a99c5726152310aae2c2a871dc5895bb8a8a09c (by decide +kernel)
private def pack_E6970Receipt45_chunk97 := witnessRule 45 48 64 870148 870265 32 2275
  0x47eaa1fd 0x339b0a8847716151310aee2a66e1c914b19a17764364eaca6d5d18544233930a89885671615338ee2a462121c5451d30aa (by decide +kernel)
private def pack_E6970Receipt45_chunk98 := witnessRule 45 48 96 870266 870389 32 2070
  0x57d55fd5 0xae4ca6e1c5854424b89227763366eac86d1cd94dbb930a8848715131082f0c66c9d990d9ba329b (by decide +kernel)
private def pack_E6970Receipt45_chunk99 := witnessRule 45 48 128 870390 870519 32 1993
  0xe483b4 0x13b321b3756331086e8ca6d1d190dab9b198845726536ce2c862119d8d0bbb21b27763366eac86d1d58cdab9b21b672633108ce2ca6ddd0c41c38a11b17863366ecc66d1d190dab9b19884 (by decide +kernel)
private def pack_E6970Receipt45_chunk100 := witnessRule 45 48 160 870520 870709 32 1973
  0xf7e0f01e 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b (by decide +kernel)
private def pack_E6970Receipt45_chunk101 := witnessRule 45 48 192 870710 871024 21 1331
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk102 := witnessRule 45 47 0 880002 880073 32 2650
  0xffc003ff 0x9615131090c2a66c5dd8548c428bb30aa1c37662564e8c2aa711d18944e2b9b12884572625238ce2c4a262159c94cdbb8a923 (by decide +kernel)
private def pack_E6970Receipt45_chunk103 := witnessRule 45 47 32 880074 880146 32 2223
  0x801fe800 0x9dd8544c4293b30a99c3756152310a6e8c2a8715d1895a3930aa9c672625138ee2c4a211dc948dc38a093a6151062f0c2a262145dd854ce13b30a918852756154388eac4acdcd8554e2b9b1289c672625108ce2c4a471dc944c42438a893 (by decide +kernel)
private def pack_E6970Receipt45_chunk104 := witnessRule 45 47 64 880147 880265 32 2175
  0x7ea00fe 0x2b9b0a91885572615438ee4c4ad9c554dc39289b96152364f0c2a210dd98544c429bab0a99c4746152310a8e6c2a8719cd895ab8b0aa9c7716251390e4a20e1c50498bcb0a884 (by decide +kernel)
private def pack_E6970Receipt45_chunk105 := witnessRule 45 47 96 880266 880390 32 1995
  0x818a03d4 0x339b0a89885672615338ee2c2a46215dc550dcb8a88b87141272c8685e18cc420bbb29b476615108ae8c2a262155cd854ce33930a918856716154390e2c4ae1c54504e438a093865346eec2a2111d58544c42a3a30a99c (by decide +kernel)
private def pack_E6970Receipt45_chunk106 := witnessRule 45 47 128 880391 880521 32 1923
  0xc03c00e0 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368e8c862111cd98dab9329884571673630ce2c67061dc8c420bc321b2776331084ecca6cdd590c421ba331b (by decide +kernel)
private def pack_E6970Receipt45_chunk107 := witnessRule 45 47 160 880522 880769 32 1925
  0xffff1f03 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt45_chunk108 := witnessRule 45 47 192 880770 880961 14 873
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk109 := witnessRule 45 46 0 890001 890072 32 2564
  0xff8007ff 0xa62550c4a46c5e18944e13bb128842766252386eac4a26214dd1894ce239b1291885472625438ce4c6ad5c954dbb9a89b (by decide +kernel)
private def pack_E6970Receipt45_chunk110 := witnessRule 45 46 32 890073 890146 32 2133
  0x1fe001 0x10c2a86c9e18958bb30aa9c3766251388eac4a2111d18948e2b9b1289885572625338ce2c4a462159c950dc39aa96251362f2c4add8554d93bb1289c3766251086eac4a4711d18944c42a39b1299c5726252310aae2c4a871dc58d5bb928a09c (by decide +kernel)
private def pack_E6970Receipt45_chunk111 := witnessRule 45 46 64 890147 890266 32 2085
  0x1e000fc 0xdd18554e2ba31289c673625108ce4c4a471dc58944c42bb9299b87152474c2a262125854cd8bc30a918851776154386eec4ac9d58554e23ab1289c574625108ae6c4a4719c98944c42b38b1299c7725231090e4a28e98954b0a91884 (by decide +kernel)
private def pack_E6970Receipt45_chunk112 := witnessRule 45 46 96 890267 890392 32 1920
  0xd001a0 0xdd9854ce23ab0a91885474615438ae6c2a662155c98554e338b0aa1885671563630ee2a4725854cd93c30a898852776153386ecc2a46214dd58550e23a30a99885473615538ce6c4a271dc9894423b8b1291c8725131092e2a24ed854418bcb0a898851786153384eec2a462149d98550e23b312b (by decide +kernel)
private def pack_E6970Receipt45_chunk113 := witnessRule 45 46 128 890393 890576 32 1862
  0x7c070030 0xde8c418bb339b2756631084e8d06cdcd9cc421b9349b4716831088f4685e190c420bbb31b2766531084eace6cdd198c421b9b41b18473643830ae4c66214615c594e0c33a188496431070cc685dd94c420bb339b (by decide +kernel)
private def pack_E6970Receipt45_chunk114 := witnessRule 45 46 160 890577 890832 32 1885
  0xfffffdf8 0x17d342e6d46c9c9a4c42138b59b (by decide +kernel)
private def pack_E6970Receipt45_chunk115 := witnessRule 45 46 192 890833 890960 7 432
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk116 := witnessRule 45 45 0 900000 900072 32 2494
  0xff8007ff 0x9625131090c4a66c5dd8948c428bb312a1c37663564e8c4aa711d18d44e2b9b1a884572635238ce2c6a262159cd4cdbb92923 (by decide +kernel)
private def pack_E6970Receipt45_chunk117 := witnessRule 45 45 32 900073 900146 32 2041
  0xfe000 0xbcb128841786252384eec4a262149d9894ce1bab1291885374625438ae8c6ad1c98954e33931a89c771635108ee6a46e1c54504a531288396252362f0c4a262145dd894ce13b312918852756254388eac6acdcd8954e2b9b1a89c672635108ce2c6a471dcd44c424392893 (by decide +kernel)
private def pack_E6970Receipt45_chunk118 := witnessRule 45 45 64 900147 900267 32 1995
  0x70003e 0x3766252388eac4a262151d1894ce2b9b1291885572625438ee4c6ad9c954dc39a89b972256c4aa58948d8bcb1289c2786251084eec4a470dd98944c429bab1299c4746252310a8e6c4a8719cd8d5ab8b12a9c7716351390e6a20e1c9049d31289b (by decide +kernel)
private def pack_E6970Receipt45_chunk119 := witnessRule 45 45 96 900268 900394 32 1847
  0x100020 0x5e18550e13bb0a998852766155386eac2a86214dd18558e239b0aa988547261573830ae4c2a674619c58548c430c338aa1c18872174c2a4621258550d8bc30a998851776155384ecc2a862149d58558e23ab1291c5746251310aae6c4a6719c98948c42b38b12a1c7725331090e4a282725c89531289b9615331090c2aa6c9e18944e1bbb12884 (by decide +kernel)
private def pack_E6970Receipt45_chunk120 := witnessRule 45 45 128 900395 900580 32 1805
  0xefe0e406 0x1716d362e8d46c9cda4c42139359b3716a31086f86a198c41bb41a1756936304eaca7060dd190c428c1b9b31c1847265310a308e2ce70615d8c42430aa9b (by decide +kernel)
private def pack_E6970Receipt45_chunk121 := witnessRule 45 45 160 900581 900960 32 1866
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk122 := witnessRule 45 44 0 910000 910072 32 2358
  0xff8007ff 0xa63550c6a46c5e18d44e13bb1a8842766352386eac6a26214dd18d4ce239b1a91885472635438ce4c8ad5cd54dbba289b (by decide +kernel)
private def pack_E6970Receipt45_chunk123 := witnessRule 45 44 32 910073 910147 32 1952
  0x7f000 0x531aa9625231090c4a86c9e18d58bb312a9c3766351388eac6a2111d18d48e2b9b1a89885572635338ce2c6a462159cd50dc3a2a96351362f2c6add8954d93bb1a89c3766351086eac6a4711d18d44c42a39b1a99c5726352310aae2c6a871dc5915bb9a8a09c (by decide +kernel)
private def pack_E6970Receipt45_chunk124 := witnessRule 45 44 64 910192 910269 32 1910
  0x1c001f 0x1786253384eec4a462149d98950e1bab1299885374625538ae8c6a2719cd8d44233931a91c7716351310aee6a66e1c9491d3128988496253362f0c4a462145dd8950e1bbb1ab2756255388eac6a2715d18d4422b9b1a91c6726351310ace2c6a671dcd48c42439a8a3 (by decide +kernel)
private def pack_E6970Receipt45_chunk125 := witnessRule 45 44 96 910270 910397 32 1776
  0xc0020008 0x9615431090c2ac6c5dd8554c428bb30ab9c2756156310a4e8c2b07060dd18550e8c239b0a998861847261553a30ae2c2a86218615c558e14339188c96253370c2aa6211d855cd93bb1299c3766252310a6eac4a8711d1894cc42a39b12a9c5726254310aae2c4ac70619c58948e8c3b92898859715121194c4a40e98948d8bcb1289885 (by decide +kernel)
private def pack_E6970Receipt45_chunk126 := witnessRule 45 44 128 910448 910584 32 1755
  0xffff8ec0 0x5c9b4d938b6188427e34ec2ae6c605d59ce0c13a331885182736838306e4ce621460dc5a4e0c23c1884 (by decide +kernel)
private def pack_E6970Receipt45_chunk127 := witnessRule 45 44 160 910640 910897 24 1378
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk128 := witnessRule 45 43 0 920000 920073 32 2237
  0xffc01fff 0x4b1a8988486353362eec6a462145d98d50e1bb322b2746355388e8c8a2715cd914422b932291c (by decide +kernel)
private def pack_E6970Receipt45_chunk129 := witnessRule 45 43 32 920074 920193 32 1905
  0xc00bf802 0x531a89b1796351082f0c6a4709dd8d44c4293b31a99c3756352310a6e8c6a8715d1915a3931aa9c672645138ee8a46e98d441cb1a91b1786351310a2eec6a6709d98d48c4293ab1aa1c47564566e6c6aa715cd9144e338b2291c (by decide +kernel)
private def pack_E6970Receipt45_chunk130 := witnessRule 45 43 64 920194 920271 32 1783
  0x270007 0x5312899049625331090c4aa6c5dd8950c428bb312b1c3766352388eac6a262151d18d4ce2b9b1a91885572635438ce6aa6c61dcd44e531a88396352362f2c6a2709e18d44213bb1a91c3766351310a6eac6a6711d18d48c42a39b1aa1c6736456ae2c6aa71dc59144e43a2883 (by decide +kernel)
private def pack_E6970Receipt45_chunk131 := witnessRule 45 43 96 920320 920451 32 1718
  0xc004001 0x181736a38304e4d26214609c5ace0c1bd18848625536ec2ae621198564d8c0bb30aa9d182756154310c304e8c2ac7460dcd8554c430c1b930ab9d184716156310c308e2b070e11d0dcb129190496254362f0c4a662145dd8954e13b312a18852756256386e8c4aa6214dcd895ce0c239b1299d185726252310c30ae2c4a874619c94cc428c3b8a8a0988e (by decide +kernel)
private def pack_E6970Receipt45_chunk132 := witnessRule 45 43 128 920452 920644 32 1715
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt45_chunk133 := witnessRule 45 43 160 920645 920896 16 907
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk134 := witnessRule 45 42 0 930000 930073 32 2119
  0x3fc003ff 0x1dc5955bba28a09ca64550c8a46c5e19144e13bb228842766452386eac8a26214dd1914ce239b2291885472645438ce4caad5d154dbbaa89b (by decide +kernel)
private def pack_E6970Receipt45_chunk135 := witnessRule 45 42 32 930074 930194 32 1831
  0xe000fc00 0x14c8aa58d48c42431aa1b27864562ecc6aa70dd99144e23ab22884474645238ae6c8a262155c9914ce338b229188567454370eaaa59144d8bcb22b76355364eec8a270dd9914421bab2291c4746451310a8e6c8a6715c99148c42ab8b22a1c (by decide +kernel)
private def pack_E6970Receipt45_chunk136 := witnessRule 45 42 64 930195 930321 32 1704
  0x4000c001 0x2857151433b4c4a80e58d48c42431aa1b1786353384eec6a462149d98d50e1bab1a998853746355388e6c6a862151c98d58e0c2b931a91d186716351310c30ce6a6721c949046531a8988496353362f0c6a462145dd8d50e13b31a998852756355388eac8a2715d1914422b9b2291c6726451310ace2c8a671dd148c4243a28a3 (by decide +kernel)
private def pack_E6970Receipt45_chunk137 := witnessRule 45 42 96 930322 930454 32 1646
  0xfb810800 0x605c5b4e4312a190476256310830ec2aa6214619855ce0c0bab0ab18861817461583a304e4c2b274e09c994e1c1b8b2188538376372c4a6641218954c423b12b9b1766256310a2eac4b070609d58950e8c1ba312998861837362553a308e4c4a86218611c58958e8c2b92a9885 (by decide +kernel)
private def pack_E6970Receipt45_chunk138 := witnessRule 45 42 128 930455 930706 32 1693
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk139 := witnessRule 45 42 160 930707 930896 9 506
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk140 := witnessRule 45 41 0 940000 940074 32 2015
  0xbfe00fff 0x19c59548e4b228988486453362eec8a462145d99150e1bb32ab2746455388e8caa2715cd954422b932a91c (by decide +kernel)
private def pack_E6970Receipt45_chunk141 := witnessRule 45 41 32 940075 940196 32 1751
  0x78017e00 0xc3ba2884a6451362f2c8a2105e19148e13bb22898852766453386eac8a46214dd19150e2ba32ab472645538ce4caa271dd548dd32288396452362f0c8a262145dd914ce13b322918852756454388eacaacdcd9154e2b9b2a89c (by decide +kernel)
private def pack_E6970Receipt45_chunk142 := witnessRule 45 41 64 940197 940324 32 1628
  0x8003004 0x183726256310c306e2c4b074e0dc58550e9c238a998859635133092c6a6621218d54d8bbb1aa18851766356384eac6aa62149d18d5ce0c1ba31a99d184736352310c308e4c6a874615c58d4cc430c2b9aa9c2867251311b4c6a60e59148dc31aa188476356364eec8a470dd99144c429bab2299c4746452310a8e6c8a8715c59154e0c338b2289d (by decide +kernel)
private def pack_E6970Receipt45_chunk143 := witnessRule 45 41 96 940325 940458 32 1588
  0xfffab100 0x1d8954cc20c330ab1905184615a38702e4ce70e09c598c429c13c1b9625234090c6a86211d8d58d8c3b12a9c181766254310c302eac4ac74609d18954c430c139b12b9d (by decide +kernel)
private def pack_E6970Receipt45_chunk144 := witnessRule 45 41 128 940512 940832 32 1684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk145 := witnessRule 45 41 160 940833 940833 1 56
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk146 := witnessRule 45 40 0 950000 950074 32 1911
  0x3fe003ff 0x2b932a918855716554394caaa19548d8bc32a89c2776551084eccaa470dd59544c429ba32a99c4736552310a8e4caa8719c9995abaaa9b (by decide +kernel)
private def pack_E6970Receipt45_chunk147 := witnessRule 45 40 32 950075 950197 32 1669
  0x7c007f00 0x1857164533b4c8a40e59148c424322a1b1776453310a2ecc8aa70dd99544e23ab2a884474655238ae6caa262155c9954ce338b2a9188596551362f2caadd9154d93bb2a89c3766551086eacaa4711d19544c42a39b2a99c (by decide +kernel)
private def pack_E6970Receipt45_chunk148 := witnessRule 45 40 64 950198 950326 32 1558
  0x6004c00 0x302e8c4ae6218605cd8964e9c0b9b0aa9d382726154310c704e2c2ac7658d541cb1a919848645436ec6ac621198d60d8c0bb31aa1d182756353310c304e8c6aa7460dcd8d50c430c1b931ab1d184735738708e4a67259144c824b2299b1786452310a2eec8a8709d9914cc4293ab22a9c3746454310a6e6c8ac70611cd9148e8c2b932289886 (by decide +kernel)
private def pack_E6970Receipt45_chunk149 := witnessRule 45 40 96 950327 950515 32 1552
  0xffffffa0 0xe05e8dc31a9998476355320830ec4a864146198958c428c2b12c1c (by decide +kernel)
private def pack_E6970Receipt45_chunk150 := witnessRule 45 40 128 950516 950832 26 1348
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk151 := witnessRule 45 39 0 960000 960075 32 1815
  0x2ff007ff 0x373655538ae6cca2719c59948e4b2a8988486553362eecaa462145d99550e1bb332b2746555388e8cca2715cd994422b933291c (by decide +kernel)
private def pack_E6970Receipt45_chunk152 := witnessRule 45 39 32 960076 960199 32 1588
  0x1f002f80 0xc1b9b22a1d184726453310c308e2c8aa7659544c42432a99b1786552384eecaa262149d9954ce1bab2a918853746554388e6caa662151c99554e0c2b932a89d1867552394caa20e59548d8bc32a898851776553384eccaa462149d59550e23ab32b (by decide +kernel)
private def pack_E6970Receipt45_chunk153 := witnessRule 45 39 64 960200 960329 32 1490
  0xc00b00 0x30ec4a668146198954cc28c2b12b99051846259310a708c2aa6214e0d855ce1c0b930ab18863817161583b2c6a26a121914cc823b22a98841876354310a30cc6ac70605d58d54c430c0ba31ab9d182736356310c304e4c6b074e09c98950e9c1b92a9c96454072c8a4641219150c423b22b1b1766455310a2eac8ae70609d5914ce8c1ba32291886 (by decide +kernel)
private def pack_E6970Receipt45_chunk154 := witnessRule 45 39 96 960330 960519 32 1528
  0xfffffffc 0x218d48d423b1aa1a04 (by decide +kernel)
private def pack_E6970Receipt45_chunk155 := witnessRule 45 39 128 960576 960832 19 973
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk156 := witnessRule 45 38 0 970000 970075 32 1717
  0xff001ff 0x8e8cca262151cd994ce2b9332918855716654394ccaa19948d8bc33289c2776651084eccca470dd59944c429ba33299c4736652310a8e4cca8719c99d5abb2a9b (by decide +kernel)
private def pack_E6970Receipt45_chunk157 := witnessRule 45 38 32 970076 970200 32 1511
  0x7800fc0 0x609d19150c430c139b22b1d183726455310c306e2c8ae74e0dc58d4cecb2a9839655231090caa86c5dd954cc428bb32aa9c2756554310a4e8caac7060dd19548e8c239b2a898861847265533a30ae2caa4621a59944dc32a9988476555364eecca270dd9994421bab3291c (by decide +kernel)
private def pack_E6970Receipt45_chunk158 := witnessRule 45 38 64 970201 970331 32 1434
  0xaab001c0 0x1d8d4cd820c3312a1a851846258330a706c2ac6414e058568e4b1ab83864523408ec8a8661061d8d4ccc28c331aa99051856357310a308c6b270e118954e1c0b9b12a18863817262563a704e2c4aa621a59144d02432a99884765553630ec8a870605d9914cc430c0bab22a9d (by decide +kernel)
private def pack_E6970Receipt45_chunk159 := witnessRule 45 38 96 970384 970579 32 1509
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk160 := witnessRule 45 38 128 970580 970769 12 605
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk161 := witnessRule 45 37 0 980000 980076 32 1624
  0xbf803ff 0x9d59950e1ba33299885373665538308e6cca274615c59948ecb328988486653362eecca462145d99950e1bb33ab2746655388e8cea2715cd9d4422b933a91c (by decide +kernel)
private def pack_E6970Receipt45_chunk162 := witnessRule 45 37 32 980077 980202 32 1434
  0xe00be0 0x30cc8aa6214615915ce0c0ba322b18861817364583a702e6c6a874e09c98d4cc431c138b1aa9d3837354310b2caa266121994cdbb2aa98846655736302eccaa674609d59548c430c13a32aa1d183736553310c306e4caaa74611d558e4b3290396652362f0cca262145dd994ce13b33291885 (by decide +kernel)
private def pack_E6970Receipt45_chunk163 := witnessRule 45 37 64 980203 980386 32 1398
  0xfffe0030 0x10c8a26c11d914cd420c3b1a91a851866354340a30ac6ac66146118d60c829c2312a19053836256310a704c4b070e05c5895cc431c0b92c9c96456070caa46611d9550c820c3b2299905 (by decide +kernel)
private def pack_E6970Receipt45_chunk164 := witnessRule 45 37 96 980387 980642 32 1493
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk165 := witnessRule 45 37 128 980643 980768 5 250
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk166 := witnessRule 45 36 0 990000 990076 32 1531
  0x3f800ff 0xbab32b1c1827566523a306e8cca2621860dcd994ce8c239332918861847166543b2cea20e19d48d8bc33a89c2776751084eccea470dd59d44c429ba33a99c4736752310a8e4cea870615c99d62bbaa9b (by decide +kernel)
private def pack_E6970Receipt45_chunk167 := witnessRule 45 36 32 990077 990203 32 1366
  0x3002f0 0xc3b2291a051866454330a30ac8ac64146119160c429c231aa1885383635638702e4c6aa6218e05c58d5ce9c139ab18854827251443b2caaa0e19948c823b32a18841876553310a30ccaaa70605d59550c430c0ba32ab1d182736555310c304e4caae74e09c9914ce9c1ba2a1c9665132090cca66211d9954d8bb332a1885 (by decide +kernel)
private def pack_E6970Receipt45_chunk168 := witnessRule 45 36 64 990204 990389 32 1367
  0xfffff404 0x6198d4cd828c231ab9a053846253340a706c4aa6614e09895cc829c0b12c98855816155310ab02ae6e19544d423b2a99a04 (by decide +kernel)
private def pack_E6970Receipt45_chunk169 := witnessRule 45 36 96 990390 990768 31 1433
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk170 := witnessRule 45 35 0 1000000 1000077 32 1442
  0xfc01ff 0xc3b3299c181766652310c302eacca874609d1994cc430c139b32a9d183726654310c306e2ccac74e0dc59548ecb3a8988486753362eecea462145d99d50e13ab3a99885274675538306e8cea274611cd9d4428c23933a91d (by decide +kernel)
private def pack_E6970Receipt45_chunk171 := witnessRule 45 35 32 1000078 1000205 32 1306
  0x800c0078 0x3b2a91b041876451360a30cc8a66a146159154d028c2322b99853846353330a706c6aa6414e098d5cc429c0b1ac9c581625538b02e4a8621619944d023b32999841876552330a30ccaa864146159558c428c232ac1c384645438702e6c8a66218e05c99154e9c138b22a18863827456392cca80e19d48c423b3aa1b (by decide +kernel)
private def pack_E6970Receipt45_chunk172 := witnessRule 45 35 64 1000256 1000392 32 1341
  0xfffff555 0x1d9144e420c331a91c051846356360a706c4a86a14e058960cc2ac0ab1904 (by decide +kernel)
private def pack_E6970Receipt45_chunk173 := witnessRule 45 35 96 1000448 1000705 24 1089
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk174 := witnessRule 45 34 0 1010000 1010077 32 1357
  0x7c017f 0x30ecca464146199950c428c2b32b1c181746655310c302e6ccae74e05cd954ce9c13932a918863827165543a706eaa6621659d4c1c34291b767543108cceac6c605d99d48e8c13ab3a898861827467533a306e6cea4621860dc99d50e8c23baa9c (by decide +kernel)
private def pack_E6970Receipt45_chunk175 := witnessRule 45 34 32 1010078 1010257 32 1260
  0xf502001c 0x6199148dc28c2322b1a853836354340a704c6ac6614e058d60c82ac0b12a1905582563108b02e2a288623a199581bb3291a841876551350a30ccaa668146159554cc28c232ab99053846453320a706c8aa6214e09915ce1c0b8b22b1886381745838b02e6a87219d44cc23b3a99904 (by decide +kernel)
private def pack_E6970Receipt45_chunk176 := witnessRule 45 34 64 1010258 1010450 32 1317
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk177 := witnessRule 45 34 96 1010451 1010704 18 801
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk178 := witnessRule 45 33 0 1020000 1020078 32 1279
  0x5e00bf 0x76752340830ecca26814619994ccc28c2b32a99051846657310a708caa66214e0d9554e1c0b932aa18863817165563a904e8a286761a144c823b42998841876752310a30ccea870605d59d4cc430c0ba33aa9d182736754310c304e4ceac74e09c99948e9c1bb299c (by decide +kernel)
private def pack_E6970Receipt45_chunk179 := witnessRule 45 33 32 1020079 1020259 32 1221
  0xffd0fa0e 0x3836353360a702c6ae6815605894cd02ac12a99846815431110a308caac6814e0d9150cc29c1322b19053816458310ab02c6a8621560d58dc33aa83 (by decide +kernel)
private def pack_E6970Receipt45_chunk180 := witnessRule 45 33 64 1020260 1020454 32 1295
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk181 := witnessRule 45 33 96 1020512 1020704 12 527
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk182 := witnessRule 45 32 0 1030000 1030078 32 1209
  0x401e007f 0x76751360830ccca46a146159950d028c2332b19853846552330a706caa86414e099558c429c0b2ac1c581645438b02e8a662161a1501bb42919841876751330a30ccea664146159d54c428c233ab9c384665338702e6cca46218e05c99950e9c138b3299886 (by decide +kernel)
private def pack_E6970Receipt45_chunk183 := witnessRule 45 32 32 1030128 1030261 32 1185
  0xfd7aa543 0x332a89d8418564523a0a702c6ac6c1560950d42340a2190c66652380830ccaa270146119554d829c1b2299a853816457330ab02c6a6661560d54c823412a188c (by decide +kernel)
private def pack_E6970Receipt45_chunk184 := witnessRule 45 32 64 1030262 1030515 32 1275
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk185 := witnessRule 45 32 96 1030516 1030641 6 259
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk186 := witnessRule 45 31 0 1040000 1040128 32 1155
  0xda87009f 0x333a91b841846655350a706caa66814e05955cc82ac0b2299905584553108b02e6a2866239da144d420c3b3aa841866752340a30acea866146119d58c829c2332919053836654310a704ccac70e05d95ce2c0baa99c (by decide +kernel)
private def pack_E6970Receipt45_chunk187 := witnessRule 45 31 32 1040129 1040263 32 1149
  0xffbffde9 0x2b2a91e041856552390a702c8ac6a1560d50d0234129988905 (by decide +kernel)
private def pack_E6970Receipt45_chunk188 := witnessRule 45 31 64 1040264 1040640 32 1262
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk189 := witnessRule 45 30 0 1050000 1050129 32 1100
  0x7fa7fd1f 0x681514332110c702caac681561150cc2341a99888853836653330a702ccae6215605954cc42ac2aa9b (by decide +kernel)
private def pack_E6970Receipt45_chunk190 := witnessRule 45 30 32 1050130 1050265 32 1119
  0xfffffffd 0x2c1a99b04 (by decide +kernel)
private def pack_E6970Receipt45_chunk191 := witnessRule 45 30 64 1050320 1050640 27 1041
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk192 := witnessRule 45 29 0 1060000 1060130 32 1051
  0xb2f5a54f 0x340a8a1190986567523a0830acca2741460d9954e02ac2299a846825143321acd0a270106159d48dc28c233aa1b053836652350a702ccac661561550c8234229988c (by decide +kernel)
private def pack_E6970Receipt45_chunk193 := witnessRule 45 29 32 1060131 1060322 32 1094
  0xfffffebf 0x159944f420c232a91e05 (by decide +kernel)
private def pack_E6970Receipt45_chunk194 := witnessRule 45 29 64 1060323 1060577 21 789
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk195 := witnessRule 45 28 0 1070000 1070131 32 1008
  0xfdfddbdf 0xc233291d85682514232120cad0a4721060d9d54dc2ac2a99a04 (by decide +kernel)
private def pack_E6970Receipt45_chunk196 := witnessRule 45 28 32 1070132 1070324 32 1067
  0xffffffbf 0x233291f04 (by decide +kernel)
private def pack_E6970Receipt45_chunk197 := witnessRule 45 28 64 1070325 1070576 16 587
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk198 := witnessRule 45 27 0 1080000 1080132 32 968
  0xfffffff7 0x341a8a1190886 (by decide +kernel)
private def pack_E6970Receipt45_chunk199 := witnessRule 45 27 32 1080133 1080384 32 1043
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk200 := witnessRule 45 27 64 1080385 1080576 11 396
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk201 := witnessRule 45 26 0 1090000 1090133 32 929
  0xfd7fe5ff 0x233a89f8418366523e0a8d0a478106119d44f028c133aa9d05 (by decide +kernel)
private def pack_E6970Receipt45_chunk202 := witnessRule 45 26 32 1090134 1090387 32 1019
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk203 := witnessRule 45 26 64 1090388 1090513 6 211
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk204 := witnessRule 45 25 0 1100000 1100134 32 895
  0xff7ffbff 0x36752340020c1b3a91e85 (by decide +kernel)
private def pack_E6970Receipt45_chunk205 := witnessRule 45 25 32 1100135 1100450 32 1000
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk206 := witnessRule 45 25 64 1100512 1100512 1 35
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk207 := witnessRule 45 24 0 1110000 1110135 32 861
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk208 := witnessRule 45 24 32 1110136 1110512 29 881
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk209 := witnessRule 45 23 0 1120000 1120136 32 829
  0xfffff5ff 0xda144d1008304cea468005 (by decide +kernel)
private def pack_E6970Receipt45_chunk210 := witnessRule 45 23 32 1120192 1120449 24 705
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk211 := witnessRule 45 22 0 1130000 1130192 32 799
  0xfffffbff 0x4d0a469004 (by decide +kernel)
private def pack_E6970Receipt45_chunk212 := witnessRule 45 22 32 1130193 1130448 20 567
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk213 := witnessRule 45 21 0 1140000 1140194 32 771
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk214 := witnessRule 45 21 32 1140195 1140448 16 439
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk215 := witnessRule 45 20 0 1150000 1150195 32 741
  0xfffffdff 0x2d0a46a804 (by decide +kernel)
private def pack_E6970Receipt45_chunk216 := witnessRule 45 20 32 1150196 1150385 12 317
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk217 := witnessRule 45 19 0 1160000 1160197 32 713
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk218 := witnessRule 45 19 32 1160256 1160384 8 205
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk219 := witnessRule 45 18 0 1170000 1170257 32 685
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk220 := witnessRule 45 18 32 1170258 1170384 5 124
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk221 := witnessRule 45 17 0 1180000 1180320 32 660
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk222 := witnessRule 45 17 32 1180321 1180321 1 24
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk223 := witnessRule 45 16 0 1190000 1190320 30 588
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk224 := witnessRule 45 15 0 1200000 1200320 27 501
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk225 := witnessRule 45 14 0 1210000 1210257 24 417
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk226 := witnessRule 45 13 0 1220000 1220256 21 342
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk227 := witnessRule 45 12 0 1230000 1230256 19 289
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk228 := witnessRule 45 11 0 1240000 1240193 16 225
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk229 := witnessRule 45 10 0 1250000 1250192 14 181
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk230 := witnessRule 45 9 0 1260000 1260192 12 143
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk231 := witnessRule 45 8 0 1270000 1270129 10 107
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk232 := witnessRule 45 7 0 1280000 1280128 8 77
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk233 := witnessRule 45 6 0 1290000 1290128 7 60
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk234 := witnessRule 45 5 0 1300000 1300065 5 37
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk235 := witnessRule 45 4 0 1310000 1310064 4 25
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk236 := witnessRule 45 3 0 1320000 1320064 3 16
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk237 := witnessRule 45 2 0 1330000 1330001 2 8
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk238 := witnessRule 45 1 0 1340000 1340000 1 3
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt45_chunk239 := witnessRule 45 0 0 1350000 1350000 1 2
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt45_chunks : List (Chunk 45) := [pack_E6970Receipt45_chunk0, pack_E6970Receipt45_chunk1, pack_E6970Receipt45_chunk2, pack_E6970Receipt45_chunk3, pack_E6970Receipt45_chunk4, pack_E6970Receipt45_chunk5, pack_E6970Receipt45_chunk6, pack_E6970Receipt45_chunk7, pack_E6970Receipt45_chunk8, pack_E6970Receipt45_chunk9, pack_E6970Receipt45_chunk10, pack_E6970Receipt45_chunk11, pack_E6970Receipt45_chunk12, pack_E6970Receipt45_chunk13, pack_E6970Receipt45_chunk14, pack_E6970Receipt45_chunk15, pack_E6970Receipt45_chunk16, pack_E6970Receipt45_chunk17, pack_E6970Receipt45_chunk18, pack_E6970Receipt45_chunk19, pack_E6970Receipt45_chunk20, pack_E6970Receipt45_chunk21, pack_E6970Receipt45_chunk22, pack_E6970Receipt45_chunk23, pack_E6970Receipt45_chunk24, pack_E6970Receipt45_chunk25, pack_E6970Receipt45_chunk26, pack_E6970Receipt45_chunk27, pack_E6970Receipt45_chunk28, pack_E6970Receipt45_chunk29, pack_E6970Receipt45_chunk30, pack_E6970Receipt45_chunk31, pack_E6970Receipt45_chunk32, pack_E6970Receipt45_chunk33, pack_E6970Receipt45_chunk34, pack_E6970Receipt45_chunk35, pack_E6970Receipt45_chunk36, pack_E6970Receipt45_chunk37, pack_E6970Receipt45_chunk38, pack_E6970Receipt45_chunk39, pack_E6970Receipt45_chunk40, pack_E6970Receipt45_chunk41, pack_E6970Receipt45_chunk42, pack_E6970Receipt45_chunk43, pack_E6970Receipt45_chunk44, pack_E6970Receipt45_chunk45, pack_E6970Receipt45_chunk46, pack_E6970Receipt45_chunk47, pack_E6970Receipt45_chunk48, pack_E6970Receipt45_chunk49, pack_E6970Receipt45_chunk50, pack_E6970Receipt45_chunk51, pack_E6970Receipt45_chunk52, pack_E6970Receipt45_chunk53, pack_E6970Receipt45_chunk54, pack_E6970Receipt45_chunk55, pack_E6970Receipt45_chunk56, pack_E6970Receipt45_chunk57, pack_E6970Receipt45_chunk58, pack_E6970Receipt45_chunk59, pack_E6970Receipt45_chunk60, pack_E6970Receipt45_chunk61, pack_E6970Receipt45_chunk62, pack_E6970Receipt45_chunk63, pack_E6970Receipt45_chunk64, pack_E6970Receipt45_chunk65, pack_E6970Receipt45_chunk66, pack_E6970Receipt45_chunk67, pack_E6970Receipt45_chunk68, pack_E6970Receipt45_chunk69, pack_E6970Receipt45_chunk70, pack_E6970Receipt45_chunk71, pack_E6970Receipt45_chunk72, pack_E6970Receipt45_chunk73, pack_E6970Receipt45_chunk74, pack_E6970Receipt45_chunk75, pack_E6970Receipt45_chunk76, pack_E6970Receipt45_chunk77, pack_E6970Receipt45_chunk78, pack_E6970Receipt45_chunk79, pack_E6970Receipt45_chunk80, pack_E6970Receipt45_chunk81, pack_E6970Receipt45_chunk82, pack_E6970Receipt45_chunk83, pack_E6970Receipt45_chunk84, pack_E6970Receipt45_chunk85, pack_E6970Receipt45_chunk86, pack_E6970Receipt45_chunk87, pack_E6970Receipt45_chunk88, pack_E6970Receipt45_chunk89, pack_E6970Receipt45_chunk90, pack_E6970Receipt45_chunk91, pack_E6970Receipt45_chunk92, pack_E6970Receipt45_chunk93, pack_E6970Receipt45_chunk94, pack_E6970Receipt45_chunk95, pack_E6970Receipt45_chunk96, pack_E6970Receipt45_chunk97, pack_E6970Receipt45_chunk98, pack_E6970Receipt45_chunk99, pack_E6970Receipt45_chunk100, pack_E6970Receipt45_chunk101, pack_E6970Receipt45_chunk102, pack_E6970Receipt45_chunk103, pack_E6970Receipt45_chunk104, pack_E6970Receipt45_chunk105, pack_E6970Receipt45_chunk106, pack_E6970Receipt45_chunk107, pack_E6970Receipt45_chunk108, pack_E6970Receipt45_chunk109, pack_E6970Receipt45_chunk110, pack_E6970Receipt45_chunk111, pack_E6970Receipt45_chunk112, pack_E6970Receipt45_chunk113, pack_E6970Receipt45_chunk114, pack_E6970Receipt45_chunk115, pack_E6970Receipt45_chunk116, pack_E6970Receipt45_chunk117, pack_E6970Receipt45_chunk118, pack_E6970Receipt45_chunk119, pack_E6970Receipt45_chunk120, pack_E6970Receipt45_chunk121, pack_E6970Receipt45_chunk122, pack_E6970Receipt45_chunk123, pack_E6970Receipt45_chunk124, pack_E6970Receipt45_chunk125, pack_E6970Receipt45_chunk126, pack_E6970Receipt45_chunk127, pack_E6970Receipt45_chunk128, pack_E6970Receipt45_chunk129, pack_E6970Receipt45_chunk130, pack_E6970Receipt45_chunk131, pack_E6970Receipt45_chunk132, pack_E6970Receipt45_chunk133, pack_E6970Receipt45_chunk134, pack_E6970Receipt45_chunk135, pack_E6970Receipt45_chunk136, pack_E6970Receipt45_chunk137, pack_E6970Receipt45_chunk138, pack_E6970Receipt45_chunk139, pack_E6970Receipt45_chunk140, pack_E6970Receipt45_chunk141, pack_E6970Receipt45_chunk142, pack_E6970Receipt45_chunk143, pack_E6970Receipt45_chunk144, pack_E6970Receipt45_chunk145, pack_E6970Receipt45_chunk146, pack_E6970Receipt45_chunk147, pack_E6970Receipt45_chunk148, pack_E6970Receipt45_chunk149, pack_E6970Receipt45_chunk150, pack_E6970Receipt45_chunk151, pack_E6970Receipt45_chunk152, pack_E6970Receipt45_chunk153, pack_E6970Receipt45_chunk154, pack_E6970Receipt45_chunk155, pack_E6970Receipt45_chunk156, pack_E6970Receipt45_chunk157, pack_E6970Receipt45_chunk158, pack_E6970Receipt45_chunk159, pack_E6970Receipt45_chunk160, pack_E6970Receipt45_chunk161, pack_E6970Receipt45_chunk162, pack_E6970Receipt45_chunk163, pack_E6970Receipt45_chunk164, pack_E6970Receipt45_chunk165, pack_E6970Receipt45_chunk166, pack_E6970Receipt45_chunk167, pack_E6970Receipt45_chunk168, pack_E6970Receipt45_chunk169, pack_E6970Receipt45_chunk170, pack_E6970Receipt45_chunk171, pack_E6970Receipt45_chunk172, pack_E6970Receipt45_chunk173, pack_E6970Receipt45_chunk174, pack_E6970Receipt45_chunk175, pack_E6970Receipt45_chunk176, pack_E6970Receipt45_chunk177, pack_E6970Receipt45_chunk178, pack_E6970Receipt45_chunk179, pack_E6970Receipt45_chunk180, pack_E6970Receipt45_chunk181, pack_E6970Receipt45_chunk182, pack_E6970Receipt45_chunk183, pack_E6970Receipt45_chunk184, pack_E6970Receipt45_chunk185, pack_E6970Receipt45_chunk186, pack_E6970Receipt45_chunk187, pack_E6970Receipt45_chunk188, pack_E6970Receipt45_chunk189, pack_E6970Receipt45_chunk190, pack_E6970Receipt45_chunk191, pack_E6970Receipt45_chunk192, pack_E6970Receipt45_chunk193, pack_E6970Receipt45_chunk194, pack_E6970Receipt45_chunk195, pack_E6970Receipt45_chunk196, pack_E6970Receipt45_chunk197, pack_E6970Receipt45_chunk198, pack_E6970Receipt45_chunk199, pack_E6970Receipt45_chunk200, pack_E6970Receipt45_chunk201, pack_E6970Receipt45_chunk202, pack_E6970Receipt45_chunk203, pack_E6970Receipt45_chunk204, pack_E6970Receipt45_chunk205, pack_E6970Receipt45_chunk206, pack_E6970Receipt45_chunk207, pack_E6970Receipt45_chunk208, pack_E6970Receipt45_chunk209, pack_E6970Receipt45_chunk210, pack_E6970Receipt45_chunk211, pack_E6970Receipt45_chunk212, pack_E6970Receipt45_chunk213, pack_E6970Receipt45_chunk214, pack_E6970Receipt45_chunk215, pack_E6970Receipt45_chunk216, pack_E6970Receipt45_chunk217, pack_E6970Receipt45_chunk218, pack_E6970Receipt45_chunk219, pack_E6970Receipt45_chunk220, pack_E6970Receipt45_chunk221, pack_E6970Receipt45_chunk222, pack_E6970Receipt45_chunk223, pack_E6970Receipt45_chunk224, pack_E6970Receipt45_chunk225, pack_E6970Receipt45_chunk226, pack_E6970Receipt45_chunk227, pack_E6970Receipt45_chunk228, pack_E6970Receipt45_chunk229, pack_E6970Receipt45_chunk230, pack_E6970Receipt45_chunk231, pack_E6970Receipt45_chunk232, pack_E6970Receipt45_chunk233, pack_E6970Receipt45_chunk234, pack_E6970Receipt45_chunk235, pack_E6970Receipt45_chunk236, pack_E6970Receipt45_chunk237, pack_E6970Receipt45_chunk238, pack_E6970Receipt45_chunk239]
def rows45 := rowsFrom pack_E6970Receipt45_chunks
theorem good45 : ∀ r ∈ rows45, good 45 r = true := rowsFrom_good pack_E6970Receipt45_chunks
theorem sorted45 : rows45.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt45_chunks 0 (by decide +kernel)).1
theorem mass45 (i : Fin 61) :
    bandCount 45 (i.val : ℤ) 60 16 ≤ (rows45.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt45_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 45 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt45_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total45 : (rows45.map (price 45)).sum = 421151 :=
  (total_eq pack_E6970Receipt45_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt45

section Pack_E6970Receipt46

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt46_chunk0 := witnessA6966Final 46 60 0 780014 780090 32 3582
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk1 := witnessA6966Final 46 60 32 780091 780211 32 3564
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk2 := witnessA6966Final 46 60 64 780212 780330 32 3506
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk3 := witnessA6966Final 46 60 96 780331 780405 32 3384
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk4 := witnessA6966Final 46 60 128 780448 780523 32 3504
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk5 := witnessA6966Final 46 60 160 780524 780647 32 3266
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk6 := witnessA6966Final 46 60 192 780648 780777 32 3090
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk7 := witnessA6966Final 46 60 224 780778 780967 32 2900
  0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk8 := witnessRule 46 60 256 781024 781030 7 605
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk9 := witnessRule 46 59 0 790013 790089 32 3404
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk10 := witnessRule 46 59 32 790090 790209 32 3378
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk11 := witnessRule 46 59 64 790210 790327 32 3296
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk12 := witnessRule 46 59 96 790328 790401 32 3251
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk13 := witnessRule 46 59 128 790402 790520 32 3230
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk14 := witnessRule 46 59 160 790521 790645 32 3047
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk15 := witnessRule 46 59 192 790646 790776 32 2893
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk16 := witnessRule 46 59 224 790777 791024 32 2733
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk17 := witnessRule 46 59 256 791025 791029 5 415
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk18 := witnessRule 46 58 0 800012 800087 32 3239
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk19 := witnessRule 46 58 32 800088 800206 32 3203
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk20 := witnessRule 46 58 64 800207 800323 32 3098
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk21 := witnessRule 46 58 96 800324 800397 32 3157
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk22 := witnessRule 46 58 128 800398 800517 32 2997
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk23 := witnessRule 46 58 160 800518 800643 32 2865
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk24 := witnessRule 46 58 192 800644 800775 32 2738
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk25 := witnessRule 46 58 224 800776 801025 32 2620
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk26 := witnessRule 46 58 256 801026 801029 4 320
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk27 := witnessRule 46 57 0 810011 810086 32 3104
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk28 := witnessRule 46 57 32 810087 810204 32 3073
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk29 := witnessRule 46 57 64 810205 810278 32 2910
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk30 := witnessRule 46 57 96 810321 810394 32 3045
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk31 := witnessRule 46 57 128 810395 810515 32 2810
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk32 := witnessRule 46 57 160 810516 810642 32 2713
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk33 := witnessRule 46 57 192 810643 810775 32 2615
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk34 := witnessRule 46 57 224 810776 811027 32 2528
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk35 := witnessRule 46 57 256 811028 811028 1 78
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk36 := witnessRule 46 56 0 820010 820084 32 2999
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk37 := witnessRule 46 56 32 820085 820201 32 2961
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk38 := witnessRule 46 56 64 820202 820275 32 2830
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk39 := witnessRule 46 56 96 820276 820391 32 2889
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk40 := witnessRule 46 56 128 820392 820513 32 2659
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk41 := witnessRule 46 56 160 820514 820641 32 2599
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk42 := witnessRule 46 56 192 820642 820775 32 2515
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk43 := witnessRule 46 56 224 820776 821028 31 2373
  0x7ffeffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt46_chunk44 := witnessRule 46 55 0 830009 830083 32 2927
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk45 := witnessRule 46 55 32 830084 830199 32 2886
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk46 := witnessRule 46 55 64 830200 830272 32 2756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk47 := witnessRule 46 55 96 830273 830389 32 2723
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk48 := witnessRule 46 55 128 830390 830512 32 2544
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk49 := witnessRule 46 55 160 830513 830641 32 2501
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk50 := witnessRule 46 55 192 830642 830776 32 2419
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk51 := witnessRule 46 55 224 830777 831027 27 2006
  0x7ffdfbf 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt46_chunk52 := witnessRule 46 54 0 840008 840081 32 2872
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk53 := witnessRule 46 54 32 840082 840196 32 2789
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk54 := witnessRule 46 54 64 840197 840269 32 2734
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk55 := witnessRule 46 54 96 840270 840387 32 2585
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk56 := witnessRule 46 54 128 840388 840464 32 2448
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk57 := witnessRule 46 54 160 840512 840641 32 2407
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk58 := witnessRule 46 54 192 840642 840777 32 2335
  0xedffffff 0x5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt46_chunk59 := witnessRule 46 54 224 840832 841027 24 1734
  0xfffbe7 0x2ea685c590d938b19b (by decide +kernel)
private def pack_E6970Receipt46_chunk60 := witnessRule 46 53 0 850007 850080 32 2826
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk61 := witnessRule 46 53 32 850081 850194 32 2698
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk62 := witnessRule 46 53 64 850195 850267 32 2661
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk63 := witnessRule 46 53 96 850268 850386 32 2465
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk64 := witnessRule 46 53 128 850387 850464 32 2356
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk65 := witnessRule 46 53 160 850512 850642 32 2312
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk66 := witnessRule 46 53 192 850643 850834 32 2261
  0x7cbedfff 0x9c590d8b9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt46_chunk67 := witnessRule 46 53 224 850835 851026 19 1335
  0x7ffbe 0x5d8d0b8b29b (by decide +kernel)
private def pack_E6970Receipt46_chunk68 := witnessRule 46 52 0 860006 860078 32 2785
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk69 := witnessRule 46 52 32 860079 860151 32 2544
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk70 := witnessRule 46 52 64 860192 860265 32 2668
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk71 := witnessRule 46 52 96 860266 860385 32 2359
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk72 := witnessRule 46 52 128 860386 860463 32 2268
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk73 := witnessRule 46 52 160 860512 860643 32 2229
  0xbfffffff 0x2b99a (by decide +kernel)
private def pack_E6970Receipt46_chunk74 := witnessRule 46 52 192 860644 860836 32 2187
  0xcf8793ed 0x17166364e2ca6c5c994d939321b3716331086ea685cd90d939b19b37164368e2c66c5d18cd9b9319b (by decide +kernel)
private def pack_E6970Receipt46_chunk75 := witnessRule 46 52 224 860837 861026 15 1032
  0x7ffb 0xbb9a (by decide +kernel)
private def pack_E6970Receipt46_chunk76 := witnessRule 46 51 0 870005 870077 32 2754
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk77 := witnessRule 46 51 32 870078 870149 32 2491
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk78 := witnessRule 46 51 64 870150 870264 32 2528
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk79 := witnessRule 46 51 96 870265 870385 32 2263
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk80 := witnessRule 46 51 128 870386 870512 32 2181
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk81 := witnessRule 46 51 160 870513 870645 32 2152
  0x97b6ffff 0xdc990da39319b574342eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt46_chunk82 := witnessRule 46 51 192 870646 870897 32 2121
  0xfef8783c 0x17167362e4cc6c9c994d9b8b21884376342e6ca6c9cd90d9b931988437165368e2c86c5d190d93a319b (by decide +kernel)
private def pack_E6970Receipt46_chunk83 := witnessRule 46 51 224 870898 871025 9 609
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk84 := witnessRule 46 50 0 880004 880075 32 2723
  0x7fffebff 0x10e2895c98cdb3a1a (by decide +kernel)
private def pack_E6970Receipt46_chunk85 := witnessRule 46 50 32 880076 880147 32 2449
  0xff9ffffd 0xee66a1c51338b19b (by decide +kernel)
private def pack_E6970Receipt46_chunk86 := witnessRule 46 50 64 880148 880263 32 2402
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk87 := witnessRule 46 50 96 880264 880385 32 2175
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk88 := witnessRule 46 50 128 880386 880513 32 2104
  0x7fffffff 0x3b99a (by decide +kernel)
private def pack_E6970Receipt46_chunk89 := witnessRule 46 50 160 880514 880647 32 2077
  0x80e49edb 0x17465364e8c86cdcd8cc421b9329b4726436ae2c662115d4d0bab21b27563366e6c86d1cd8cdab8b21b67163362ecc66cdd18cdab9319b (by decide +kernel)
private def pack_E6970Receipt46_chunk90 := witnessRule 46 50 192 880648 880960 32 2070
  0xffff8f07 0x17267364e2cc62109e0d0b9b31b27365366e4c86210dc598da3a9883 (by decide +kernel)
private def pack_E6970Receipt46_chunk91 := witnessRule 46 50 224 880961 881025 4 268
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk92 := witnessRule 46 49 0 890003 890074 32 2701
  0x7ffd55ff 0x21c4913b319b37464368e4ca6ddc58544243892 (by decide +kernel)
private def pack_E6970Receipt46_chunk93 := witnessRule 46 49 32 890075 890146 32 2345
  0xf57fffaa 0x8e8c66d5c990db3a9a37563368e6c86d5c594dc38a883 (by decide +kernel)
private def pack_E6970Receipt46_chunk94 := witnessRule 46 49 64 890147 890263 32 2289
  0xbfffabff 0x77434ae6c66d9c590dc38a09b (by decide +kernel)
private def pack_E6970Receipt46_chunk95 := witnessRule 46 49 96 890264 890386 32 2092
  0x3ffebffe 0x4399a97144ee2c66e5c51339319b (by decide +kernel)
private def pack_E6970Receipt46_chunk96 := witnessRule 46 49 128 890387 890515 32 2033
  0x2edb7fff 0xae4c86d9c98cdbba1a17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt46_chunk97 := witnessRule 46 49 160 890516 890704 32 2006
  0x781e01c9 0x6ee620c5d198d93a329b3736431086e4cc6d1c594c4223b9a17565364eac86cdd18cc421b9b29b4736436ae4c662115c594db3a188317664364ecc66cdd190da3a319b (by decide +kernel)
private def pack_E6970Receipt46_chunk98 := witnessRule 46 49 192 890705 891024 29 1839
  0x1ffffef8 0x17a342e6ce6c9c998c42138b41b (by decide +kernel)
private def pack_E6970Receipt46_chunk99 := witnessRule 46 48 0 900002 900072 32 2671
  0xffaa81ff 0x298554321a17665368eac2a2115cd8544c42ab930a99c6716152310ace2a86e1c953b8a093 (by decide +kernel)
private def pack_E6970Receipt46_chunk100 := witnessRule 46 48 32 900073 900145 32 2258
  0xaa3feaa1 0x9d990d9ba329b673615108ee2c2a26215dc54cdc3922963342eec86c9d594daba30a8846726151310ace2c2a671dc548c42438a8a3 (by decide +kernel)
private def pack_E6970Receipt46_chunk101 := witnessRule 46 48 64 900146 900263 32 2191
  0xaff557fe 0x8716151092e2489dd8cd9bab21b4736536ee4c2a2121c544c420bc319b (by decide +kernel)
private def pack_E6970Receipt46_chunk102 := witnessRule 46 48 96 900264 900387 32 2017
  0x3fea9fea 0x1dc58cc423ba9a4756336ae6c86d9c594dcb8a883971246ecc66d1d190dab9329b (by decide +kernel)
private def pack_E6970Receipt46_chunk103 := witnessRule 46 48 128 900388 900517 32 1962
  0x3924eda 0xdd194da3a321b573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdb39321b (by decide +kernel)
private def pack_E6970Receipt46_chunk104 := witnessRule 46 48 160 900518 900707 32 1942
  0xdf83c078 0x1716a362e8ce6c9cd98c42139341b3716731086f2685d598d93ab29b3746431086e6cc6d1c994c42238b39b57631062ecca6c9d990d9bab19884 (by decide +kernel)
private def pack_E6970Receipt46_chunk105 := witnessRule 46 48 192 900708 901024 23 1430
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk106 := witnessRule 46 47 0 910001 910072 32 2593
  0xffd003ff 0x2f2c2a2109dd8544c4293b30a99c3756152310a6e8c2a8715d1895a3930aa9c672625138ee2c4a211dc948dc38a093 (by decide +kernel)
private def pack_E6970Receipt46_chunk107 := witnessRule 46 47 32 910073 910145 32 2157
  0xa03fea00 0x6eec2a2111d58544c42a3a30a99c5736152310aae4c2a871dc9895b38aa9b87251372c2a46c9e1854421bb30a898853756153388e8c2a462151cd8550e339b12b571615538ee2c4a2721c9441c38a093 (by decide +kernel)
private def pack_E6970Receipt46_chunk108 := witnessRule 46 47 64 910146 910264 32 2099
  0x3aa80fe 0x19cd8544c42b3930a99c7716152310aee2a86e5c95438a093b61552c8685dd94da3b30a8845746151310aae6c2a6719c98548c42b38b0aa1c87162570e2a282721c5049c329a (by decide +kernel)
private def pack_E6970Receipt46_chunk109 := witnessRule 46 47 96 910265 910389 32 1945
  0x23a28755 0x15cd90c422b9331b8716151310b0e2a66e5c50458bcb19b27764366ecc66210dd594db3a30a8847726151310aee2c2a6721c548c424b8a8a3a63342f0c86c9d994dabab0a884 (by decide +kernel)
private def pack_E6970Receipt46_chunk110 := witnessRule 46 47 128 910390 910520 32 1890
  0x807801c8 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d58cc4223a329b (by decide +kernel)
private def pack_E6970Receipt46_chunk111 := witnessRule 46 47 160 910521 910768 32 1890
  0xfffe3e07 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt46_chunk112 := witnessRule 46 47 192 910769 910961 15 919
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk113 := witnessRule 46 46 0 920000 920071 32 2511
  0xff0007ff 0x5312a9615231090c2a86c9e18958bb30aa9c3766251388eac4a2111d18948e2b9b1289885572625338ce2c4a462159c950dc39aa (by decide +kernel)
private def pack_E6970Receipt46_chunk114 := witnessRule 46 46 32 920072 920145 32 2073
  0x1fc001 0x1786153384eec2a462149d98550e23b312b374615538ae8c4a2719cd8944233931291c7716251310aee4a66e1c5491d30a8988496153362f0c2a462145dd8550e1bbb12b2756155388eac4a2715d1894422b9b1291c6726251310ace2c4a671dc948c4243928a3 (by decide +kernel)
private def pack_E6970Receipt46_chunk115 := witnessRule 46 46 64 920146 920265 32 2013
  0x1e800fa 0x23a30aa1c6746256ae4c2aa71dc98944e438b1288487252372e2824c5e98544213c30a898852776153386ecc2a46214dd58550e2bab12b473615538ce6c4a271dc9894423b8b1291c8725131092e2a24ed854418bcb0a89885 (by decide +kernel)
private def pack_E6970Receipt46_chunk116 := witnessRule 46 46 96 920266 920391 32 1874
  0x8401a8 0xdd594c421ba339b574615338ce6c2a462159c98550e3b8b0a998857715536310e2623298cc41cb29a1786431082eecc6d1d98544c42a3ab0a99c5746152310aae6c2a8719c9854cc42b38b0aa9c8716251392e4a20e5c5049d30a91b2796151086eec2a26214dd9854ce23ab0a91885 (by decide +kernel)
private def pack_E6970Receipt46_chunk117 := witnessRule 46 46 128 920392 920523 32 1824
  0xf80f0070 0x17667364eacc62109d1a0d9b9b3988437269368e2d062111e8d0bbb31b27765366ecc86210dd598da3a3298844736736ae4cc62115c5a0db3b98831796331082f0ca6c9dd90c4213b331b (by decide +kernel)
private def pack_E6970Receipt46_chunk118 := witnessRule 46 46 160 920576 920773 32 1852
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt46_chunk119 := witnessRule 46 46 192 920832 920960 8 485
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk120 := witnessRule 46 45 0 930000 930072 32 2381
  0x7f8003ff 0x21c9049d31289b1796251082f0c4a4709dd8944c4293b31299c3756252310a6e8c4a8715d18d5a39312a9c672635138ee2c6a211dcd48dc38a8a094 (by decide +kernel)
private def pack_E6970Receipt46_chunk121 := witnessRule 46 45 32 930073 930146 32 1974
  0x7e000 0x5e9895c30aa9b2786251386eec4a210dd98948e23ab1289885474625338ae6c4a462155c98950e3b931ab67255370e6a26e5c895b12a96252362f2c4a2709e18944213bb1291c3766251310a6eac4a6711d18948c42a39b12a1c6736356ae2c4aa71dc58d44e439a883 (by decide +kernel)
private def pack_E6970Receipt46_chunk122 := witnessRule 46 45 64 930147 930267 32 1928
  0x30001e 0x9d98554e23b31289c575625108ae8c4a4719cd8944c42b3931299c7716252310aee4a86e5cd54b912b62554c2a4621258550d93cb12b1776155386eec4a2711d98944223ab1291c5746251310aae6c4a6719c98948c42b38b12a1c87163570e4a282725c89531289b (by decide +kernel)
private def pack_E6970Receipt46_chunk123 := witnessRule 46 45 96 930268 930394 32 1801
  0x180020 0x4339a1776631082ecd06cdd98550e23ab0a99885474615538ae6c2a862155c98558e338b0aa9885671573650ce66e58550d8bcb0a99c2786152310a4eec2a870dd9854cc429bab0aa9c4746154310a8e6c2ac719cd8948e3b9312898857716253390e4a462125c5450465b0a89884a6153362f2c2a462145e18550e13bb0a99885 (by decide +kernel)
private def pack_E6970Receipt46_chunk124 := witnessRule 46 45 128 930395 930580 32 1771
  0xefe0f806 0x2e2da6c5d1a8d939b498842726b366e2d46210df0d0bbb39b2766631084ead06cdd19cc421b9b49b4726831088e2d46d5e4c41cb29883 (by decide +kernel)
private def pack_E6970Receipt46_chunk125 := witnessRule 46 45 160 930581 930960 32 1834
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk126 := witnessRule 46 44 0 940000 940072 32 2251
  0x7f8003ff 0x21cd451d31aa9625231090c4a86c9e18d58bb312a9c3766351388eac6a2111d18d48e2b9b1a89885572635338ce2c6a462159cd50dc3a2a (by decide +kernel)
private def pack_E6970Receipt46_chunk127 := witnessRule 46 44 32 940073 940147 32 1892
  0x3f000 0x2d89441d31291b1796251310a2f0c4a6709dd8948c4293b312a1c47663566e8c4aa715d18d44e339b1a884672635238ee2c6a26215dcd4cdc392923a625131092c4a66c5e18948c428bbb12a1c37763564eac4aa711d58d44e2ba31a884573635238ce4c6a262159c58d4ce3b9a91884 (by decide +kernel)
private def pack_E6970Receipt46_chunk128 := witnessRule 46 44 64 940192 940269 32 1845
  0xc000f 0x218558d93c31291c3776251310a6ecc4a6711d58948c42a3a312a1c5736253310aae4c4aa71dc98d44e438b1a88487352372e2a28252d8944d8bd3128841796252384f0c4a262149dd894ce1bb31291885375625438aeac6ad1cd8954e339b1a89c772635108ee2c6a4721cd44c424b92893 (by decide +kernel)
private def pack_E6970Receipt46_chunk129 := witnessRule 46 44 96 940270 940397 32 1733
  0xe0020004 0x10c2ac6c5e18554e13bb0aa18852766156386eac2aa6214dd1855ce239b0ab1885472615838508e4c870a15c58cc42942ba9ba615331092c2aa6c5e18550c428bbb0ab1c2766155310a4eac2ae711d5894ce2ba31291885573625438ce4c4a662159c58954e3b92a18841877151423b2e282423298948dcb0aa1884 (by decide +kernel)
private def pack_E6970Receipt46_chunk130 := witnessRule 46 44 128 940448 940584 32 1723
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt46_chunk131 := witnessRule 46 44 160 940640 940897 24 1354
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk132 := witnessRule 46 43 0 950000 950073 32 2136
  0x3fc00bff 0x3b8b2289c87451074c6a26c5e58d4420bc31a91c2776351310a4ecc6a670dd58d48c429ba31aa1c57464568e4c6aa719c99144e3ba291b (by decide +kernel)
private def pack_E6970Receipt46_chunk133 := witnessRule 46 43 32 950074 950193 32 1839
  0xc001f800 0xa6351362f4c6ae18954d93c31a89c3776351086ecc6a4711d58d44c42a3a31a99c5736352310aae4c6a871dc9915b39aa9b87451376c6aa58d48d8bcb1a89c2786351084eec6a470dd98d44c429bab1a99c4746352310a8e6c6a8719cd915ab8b1aa9c (by decide +kernel)
private def pack_E6970Receipt46_chunk134 := witnessRule 46 43 64 950194 950271 32 1728
  0x30003 0xa625132094c4a66c5e58948c428bc312a1c2776253310a4ecc4aa70dd58950c429ba312b1c574635238ce6c6a262159c98d4ce3b8b1a918857735436310e4a232d89481d3129188496254362f0c4a662145dd8954e1bbb1a89c4766351088eac6a4715d18d44c42ab9b1a99c6726352310ace2c6a8721c5915c39a8a09c (by decide +kernel)
private def pack_E6970Receipt46_chunk135 := witnessRule 46 43 96 950320 950451 32 1677
  0xc206000 0x2e6da6c9c9b0c42138b71b37d31072c2aa62121855cd8bbb0ab18851766158384e8c2b270a09d194e141b9b21885283726638508e2ca6214a11dcdcb12a1b861563108ec2b06c9dd8950e1bb312998853756255388e8c4a862151cd8958e2b9312a988557162573850ae2c2a674a19c548c428c438a10c (by decide +kernel)
private def pack_E6970Receipt46_chunk136 := witnessRule 46 43 128 950452 950644 32 1683
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt46_chunk137 := witnessRule 46 43 160 950645 950896 16 891
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk138 := witnessRule 46 42 0 960000 960073 32 2026
  0x1fc001ff 0x671645338ee8a462121d1451d322a9635231090c6a86c9e19158bb31aa9c3766451388eac8a2111d19148e2b9b2289885572645338ce2c8a462159d150dc3aaa (by decide +kernel)
private def pack_E6970Receipt46_chunk139 := witnessRule 46 42 32 960074 960194 32 1765
  0xe0007c00 0xb6351074c6a46c5e58d44c428bc31a99c2776352310a4ecc6a8711d99159ba31aa9c574645138ce6c8a2119c99148e3b8b228988577453370e6a48e98d44c424b1a99b1786352310a2eec6a870ddd91593ab1aa9c475645138ae8c8a2115cd9148e33932289885 (by decide +kernel)
private def pack_E6970Receipt46_chunk140 := witnessRule 46 42 64 960195 960321 32 1654
  0x20004000 0xa15c550c4294338a1188da625232092c4a8621218958d8bbb12a98851766257386ecc6a6711d58d48c42a3a31aa1c5736353310aae4c6aa719c58d50c42b39ab1b2867252392e2a282423698d44c424b1a99b1796352384f0c6a262149dd8d4ce1bb31a918853756354388e8c6a662151cd8d54e339b2289c772645108ee2c8a4721d144c424b9a893 (by decide +kernel)
private def pack_E6970Receipt46_chunk141 := witnessRule 46 42 96 960322 960454 32 1608
  0xfbd60800 0xb8b2006e18558c82330ad1b281746738504e6cc6214a09c9a0e141b8b3988528379372c4a6641258954d8bc312a18851776256384ecc4aa62149d5895ce1ba312b1885373625838506e6c2a874a11c9854cc4314238b0aa9d (by decide +kernel)
private def pack_E6970Receipt46_chunk142 := witnessRule 46 42 128 960455 960706 32 1661
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk143 := witnessRule 46 42 160 960707 960896 9 497
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk144 := witnessRule 46 41 0 970000 970074 32 1925
  0xfe005ff 0xce6caad5c59154e3b8b2a89c87551074c8a26c5e5914420bc32291c2776451310a4ecc8a670dd59148c429ba322a1c57465568e4c8aa719c99544e3baa91b (by decide +kernel)
private def pack_E6970Receipt46_chunk145 := witnessRule 46 41 32 970075 970196 32 1685
  0x38003e00 0x77453310830ee6a2827699144dcb1a9988486355364f0c8a270ddd914421bb32291c4756451310a8e8c8a6715cd9148c42ab9322a1c7726556ce8aa6e1d544ddb22a96452362f2c8a2709e19144213bb2291c3766451310a6eac8a6711d19148c42a39b22a1c (by decide +kernel)
private def pack_E6970Receipt46_chunk146 := witnessRule 46 41 64 970197 970324 32 1582
  0x1000 0x504e6c2ac74a0dc98554c43141b8b0ab9d2847156310a708e2887298944d024b1a9988486355362f0c6a8709dd8d4cc4293b31aa9c3756354310a6e8c6ac711cd8d54c42a3931ab9c2847262533a50ae2c4a46218a15c950e143b8a90ca6353074c6a4621258d50d8bc31a998851776355384ecc6a862149d58d58e23ab2291c5746451310aae6c8a6719c99148c42b38b22a1c (by decide +kernel)
private def pack_E6970Receipt46_chunk147 := witnessRule 46 41 96 970325 970458 32 1555
  0xfffff180 0xa05c9a8e14138b498852827b372c4a8641218958c423b12c1b1766257310a2eac4b270a05d58554e9413a30aa1886 (by decide +kernel)
private def pack_E6970Receipt46_chunk148 := witnessRule 46 41 128 970512 970832 32 1652
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk149 := witnessRule 46 41 160 970833 970833 1 55
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk150 := witnessRule 46 40 0 980000 980074 32 1827
  0x3fe003ff 0x2b9b2a91c6726551310b4caaa59148c424322a1b27865562ecc8aa70dd99544e23ab2a884474655238ae6caa262155c9954ce338b2a91885 (by decide +kernel)
private def pack_E6970Receipt46_chunk151 := witnessRule 46 40 32 980075 980197 32 1606
  0x1c007f00 0x15c59158e142b8b1a91d2867351310b4c8a40e99148d8bcb22898851786453384eec8a462149d99150e1bab2299885374645538ae8caa2719cd9544233932a91ca645131092c8a66c5e19148c428bbb22a1c37765564eac8aa711d59544e2ba32a884 (by decide +kernel)
private def pack_E6970Receipt46_chunk152 := witnessRule 46 40 64 980198 980326 32 1514
  0x11000400 0x142b0ab9c281746156310c502e6c2b074a09c58564ea4138b29c4837431092c6a4661258d50c42431ab1b1776355310a2ecc6ae709d58d58c4293a31ac1c2827462543a506e6c4a66218a0dc98954e94238b12a188628472563870ae2a4623698d44cc24b2299b863553108ec6ae6c9dd914ce1bb322918853756454388e8c8a662151cd9154e2b9322a1885 (by decide +kernel)
private def pack_E6970Receipt46_chunk153 := witnessRule 46 40 96 980327 980515 32 1520
  0xffffffa0 0xa05f4dcb1299a04862553308ec4ae641198964c4214330aa9885 (by decide +kernel)
private def pack_E6970Receipt46_chunk154 := witnessRule 46 40 128 980516 980832 26 1322
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk155 := witnessRule 46 39 0 990000 990075 32 1733
  0x3f002ff 0x23a32a91885473655438ce6ccad5c59554e3b8b3289c87651074caa26c5e5954420bc32a91c2776551310a4eccaa670dd59548c429ba32aa1c57466568e4caaa719c99944e3bb291b (by decide +kernel)
private def pack_E6970Receipt46_chunk156 := witnessRule 46 39 32 990076 990199 32 1529
  0xf002780 0x6e6c8ae70a0dcd8d4ce9423931a918862847163543b4c8a264125914cc424322a9b1776454310a2ecc8ac70dd99548e23ab2a89885474655338ae6caa462155c99550e33aaa9b2867451394caa20e59548d8bcb2a89c2786551084eecaa470dd99544c429bab2a99c (by decide +kernel)
private def pack_E6970Receipt46_chunk157 := witnessRule 46 39 64 990200 990329 32 1448
  0xab400900 0x66258330850ac2ac6414a0d8568e240b8b39c9635135092c6a6661218d54c823b1ab9884663593650cc4aa70a05d58950c43140ba312b1d282736255310c504e4c4ae74a0dc960e241b8aa1ca6355072c8a4641259150d8bc322998851776455384ecc8a862149d59158e1ba322a9885 (by decide +kernel)
private def pack_E6970Receipt46_chunk158 := witnessRule 46 39 96 990330 990519 32 1496
  0xfffffffe 0x4312a1a84 (by decide +kernel)
private def pack_E6970Receipt46_chunk159 := witnessRule 46 39 128 990576 990832 19 954
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk160 := witnessRule 46 38 0 1000000 1000075 32 1638
  0xff001ff 0x8eacca2715d1994422b9b3291c6726651310b4ccaa59548c42432aa1b27866562eccaaa70dd99944e23ab32884474665238ae6cca262155c9994ce338b3291885 (by decide +kernel)
private def pack_E6970Receipt46_chunk161 := witnessRule 46 38 32 1000076 1000200 32 1455
  0x7800bc0 0x502eac6a874a09d18d4cc4314139b1aa9d283726354310c506e2c6ac76991501cb2a9188486554362f0caa6709dd9548c4293b32aa1c3756553310a6e8caaa711cd9550c42a3932ab1c2847264523a50ae8a67299544c424b2a99b1786552310a2eecaa8709d9954cc4293ab2aa9c (by decide +kernel)
private def pack_E6970Receipt46_chunk162 := witnessRule 46 38 64 1000201 1000331 32 1398
  0xfff80140 0x4b1a91a84863543408ec6ac661198d60c82143312a19052856256310a508c4b070a05cd895cc43140b9312c9d4817261553a904e2ac7259144d024b2299904864553108ec8ae6c5d99158c428bab22c1c (by decide +kernel)
private def pack_E6970Receipt46_chunk163 := witnessRule 46 38 96 1000384 1000579 32 1477
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk164 := witnessRule 46 38 128 1000580 1000769 12 593
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk165 := witnessRule 46 37 0 1010000 1010076 32 1548
  0x9f8017f 0x1bb332898853756653388e8cca462151cd9950e2b8b32a9c2857165513b4cca26c5e5994420bc33291c2776651310a4eccca670dd59948c429ba332a1c57467568e4ccaa719c99d44e3bba91b (by decide +kernel)
private def pack_E6970Receipt46_chunk166 := witnessRule 46 37 32 1010077 1010202 32 1381
  0xe003e0 0x66458310850cc6a86214a158d58e140ba31aa98862817363573a504e4c6ac6218a09c58d60ea4138b12a1d9655133092caa6621219554d8bbb2aa18851766556384eacaaa62149d1955ce1413a32299d283736452310c506e4c8a874a11c5914cc43532a98396652370caa86211d9558d93bb3291c (by decide +kernel)
private def pack_E6970Receipt46_chunk167 := witnessRule 46 37 64 1010203 1010386 32 1363
  0xfffe0030 0x12c6a26e1218d4cd823b1aa9a8466357340850cc4a66814a158954cc2942312b99052836259310a906c2aa6215209855ce240b8b0ab188696456072c8a4681219150cc23b22b1904 (by decide +kernel)
private def pack_E6970Receipt46_chunk168 := witnessRule 46 37 96 1010387 1010642 32 1461
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk169 := witnessRule 46 37 128 1010643 1010768 5 245
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk170 := witnessRule 46 36 0 1020000 1020076 32 1460
  0x1f800ff 0x9d9994cc4293ab32a9c3746654310a6e6ccac70a0dcd9548e9423932a898862847165533b4cca40e59948c424332a1b1776653310a2ecccaa70dd99d44e23ab3a884474675238ae6cea262155c99d4ce338b3a91885 (by decide +kernel)
private def pack_E6970Receipt46_chunk171 := witnessRule 46 36 32 1020077 1020203 32 1315
  0x3002f0 0x3b22a9a0466457330850cc6a66614a158d54c8294231ab9885283635938906c4aa71205c98950c43240b8b12b1d4827255310b2caaa0e59548cc2432aa1904765563108ccab06ca199150e140bab22998862817464553a504e6c8a86218a09c99158e941ba2b9c9665132092cca66c5e19948c428bbb32a1c (by decide +kernel)
private def pack_E6970Receipt46_chunk172 := witnessRule 46 36 64 1020204 1020389 32 1333
  0xfffff554 0xcc6ac6c10a158950d42941b12c19854826156320a902b46e59144d82432299a84 (by decide +kernel)
private def pack_E6970Receipt46_chunk173 := witnessRule 46 36 96 1020390 1020768 31 1402
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk174 := witnessRule 46 35 0 1030000 1030077 32 1373
  0xbc00bf 0x76656362ecccaa62145d5995ce140bab2a99d282746552310c504e6caa874a0dc9954cc43141b8b2aa9d3847451423b2cea2621219d4cd8bc33a91c2776751310a4eccea670dd59d48c429ba33aa1c4736753310a8e4ceaa70a11c99944e942bb291c (by decide +kernel)
private def pack_E6970Receipt46_chunk175 := witnessRule 46 35 32 1030078 1030205 32 1262
  0x80040038 0x10c8a46e11d9150d823322b1a842866352350a50ac6a86814a118d58cc2941b1ac19054836254320a904c4ac62152058960e240b92b98855817151453b2caa26a121954cd023b2aa998466557320850cc8a66414a159154c42942322b9c281736456310c502e4c8b075205c98d50ea4138b1a998864827355392cca80e59948c824332a1884 (by decide +kernel)
private def pack_E6970Receipt46_chunk176 := witnessRule 46 35 64 1030256 1030392 32 1309
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk177 := witnessRule 46 35 96 1030448 1030705 24 1065
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk178 := witnessRule 46 34 0 1040000 1040077 32 1292
  0x7c007f 0x766553208cccae6210a19954cc42942b2aa9c281746554310c502e6caac74a09c99554c4314138b2ab9d4827164533b2cea60e59d48c42433aa1b1776753310a2ecceaa709d59d50c4293a33ab1c2827466523a506e6cca26218a0dc9994ce94238b3291886 (by decide +kernel)
private def pack_E6970Receipt46_chunk179 := witnessRule 46 34 32 1040078 1040257 32 1218
  0xf502001c 0x199154dc2142b1a99b052836357340a906c4a668152098954cc2a40b12b9905482593108d02aa62125955c1c32a91b04765543508ccaac6810a199148d02942b22a19852846456320a506c8b0621520d8d50c42a4131ab1c481716355310c902e6ae7259944d02433299984 (by decide +kernel)
private def pack_E6970Receipt46_chunk180 := witnessRule 46 34 64 1040258 1040450 32 1285
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk181 := witnessRule 46 34 96 1040451 1040704 18 783
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk182 := witnessRule 46 33 0 1050000 1050078 32 1218
  0xe00bf 0x219948d423b32a1a0466656330850ccaa46614a159550c8294232ab1885283655838906c8a871205c9914cc43240b8b22a9d4827454310a906e6a284623a59d44cc2433a99904767553108cceae6ca19994ce140bab32918862817466543a504e6cca66218a09c99954e941bb2b1c (by decide +kernel)
private def pack_E6970Receipt46_chunk183 := witnessRule 46 33 32 1050079 1050259 32 1181
  0xffd57a06 0x2836356360a904c4a86a1520960cc2340a2988c2856453350a506c8ae661520d8d4ccc2a4131aa99054816357310a906b26da0954dcb32b03 (by decide +kernel)
private def pack_E6970Receipt46_chunk184 := witnessRule 46 33 64 1050260 1050454 32 1263
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk185 := witnessRule 46 33 96 1050512 1050704 12 515
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk186 := witnessRule 46 32 0 1060000 1060078 32 1154
  0x400e005f 0x219944dc23332a9a842866551350a50acaa66814a119554cc2941b2ab99054836453320a904c8aa6215205915ce240ba2b18855817351443b2ceaa0e19d48d023b3aa198466756320850ccca46414a159950c42942332b1c281736655310c502e4ccae75205c9954cea413aaa1c (by decide +kernel)
private def pack_E6970Receipt46_chunk187 := witnessRule 46 32 32 1060128 1060261 32 1149
  0xffffe543 0x765523908ccaa87010a159148dc2941b22b1a854826354340a902c6ac661520d60c823412a1904 (by decide +kernel)
private def pack_E6970Receipt46_chunk188 := witnessRule 46 32 64 1060262 1060515 32 1243
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk189 := witnessRule 46 32 96 1060516 1060641 6 253
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk190 := witnessRule 46 31 0 1070000 1070128 32 1101
  0xda83001f 0xecca47010a159548d82941b2ab1a054826454330a902c8ac641521160c42341aa1884582725142321d0cea26c11d9d4cd42333aa9a042866651340a50acca66614a119954c82941b32b98854836553310a904caaa71205c59550c43240baab1c (by decide +kernel)
private def pack_E6970Receipt46_chunk191 := witnessRule 46 31 32 1070129 1070263 32 1116
  0xfffffde8 0x2b2aa9c844826353360a906ae6811a094cd02340a8a2188886 (by decide +kernel)
private def pack_E6970Receipt46_chunk192 := witnessRule 46 31 64 1070264 1070640 32 1230
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk193 := witnessRule 46 30 0 1080000 1080129 32 1049
  0x7fa3fd0f 0x1a05450cc44c324132299a85484573308d06a66611a094510c46941b32b19854826554320a902caac621521560db422a1b (by decide +kernel)
private def pack_E6970Receipt46_chunk194 := witnessRule 46 30 32 1080130 1080265 32 1087
  0xfffffffd 0x241ab1b04 (by decide +kernel)
private def pack_E6970Receipt46_chunk195 := witnessRule 46 30 64 1080320 1080640 27 1014
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk196 := witnessRule 46 29 0 1090000 1090130 32 1007
  0xf2f4a54f 0x333291d84566543a08508caa4721521158d4234128a1988906681715142331cecea2721159d54dc2142b3289b852836655350a904caa668152155cc82342299904 (by decide +kernel)
private def pack_E6970Receipt46_chunk197 := witnessRule 46 29 32 1090131 1090322 32 1062
  0xfffffebf 0x199544f82232aa9e04 (by decide +kernel)
private def pack_E6970Receipt46_chunk198 := witnessRule 46 29 64 1090323 1090577 21 768
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk199 := witnessRule 46 28 0 1100000 1100131 32 966
  0xfdfddbd7 0x119954ec234128a1188a06667523a08508cca4701521558d02341a8a1988886 (by decide +kernel)
private def pack_E6970Receipt46_chunk200 := witnessRule 46 28 32 1100132 1100324 32 1035
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk201 := witnessRule 46 28 64 1100325 1100576 16 571
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk202 := witnessRule 46 27 0 1110000 1110132 32 928
  0xffffbff7 0x1e0508d06341a8a1188986 (by decide +kernel)
private def pack_E6970Receipt46_chunk203 := witnessRule 46 27 32 1110133 1110384 32 1011
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk204 := witnessRule 46 27 64 1110385 1110576 11 385
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk205 := witnessRule 46 26 0 1120000 1120133 32 893
  0xfd7fe5ff 0xacca268004366553e08acea47a1119d50f02141b3291d85 (by decide +kernel)
private def pack_E6970Receipt46_chunk206 := witnessRule 46 26 32 1120134 1120387 32 987
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk207 := witnessRule 46 26 64 1120388 1120513 6 205
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk208 := witnessRule 46 25 0 1130000 1130134 32 860
  0xff7ffbff 0x46652344021b3aa9e84 (by decide +kernel)
private def pack_E6970Receipt46_chunk209 := witnessRule 46 25 32 1130135 1130450 32 968
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk210 := witnessRule 46 25 64 1130512 1130512 1 34
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk211 := witnessRule 46 24 0 1140000 1140135 32 827
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk212 := witnessRule 46 24 32 1140136 1140512 29 852
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk213 := witnessRule 46 23 0 1150000 1150136 32 797
  0xfffff5ff 0x119d44d20084ceaa68004 (by decide +kernel)
private def pack_E6970Receipt46_chunk214 := witnessRule 46 23 32 1150192 1150449 24 681
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk215 := witnessRule 46 22 0 1160000 1160192 32 767
  0xfffffbff 0x6cea469804 (by decide +kernel)
private def pack_E6970Receipt46_chunk216 := witnessRule 46 22 32 1160193 1160448 20 547
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk217 := witnessRule 46 21 0 1170000 1170194 32 739
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk218 := witnessRule 46 21 32 1170195 1170448 16 423
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk219 := witnessRule 46 20 0 1180000 1180195 32 709
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk220 := witnessRule 46 20 32 1180196 1180385 12 305
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk221 := witnessRule 46 19 0 1190000 1190197 32 681
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk222 := witnessRule 46 19 32 1190256 1190384 8 197
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk223 := witnessRule 46 18 0 1200000 1200257 32 653
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk224 := witnessRule 46 18 32 1200258 1200384 5 119
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk225 := witnessRule 46 17 0 1210000 1210320 32 628
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk226 := witnessRule 46 17 32 1210321 1210321 1 23
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk227 := witnessRule 46 16 0 1220000 1220320 30 558
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk228 := witnessRule 46 15 0 1230000 1230320 27 474
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk229 := witnessRule 46 14 0 1240000 1240257 24 393
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk230 := witnessRule 46 13 0 1250000 1250256 21 321
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk231 := witnessRule 46 12 0 1260000 1260256 19 270
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk232 := witnessRule 46 11 0 1270000 1270193 16 209
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk233 := witnessRule 46 10 0 1280000 1280192 14 167
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk234 := witnessRule 46 9 0 1290000 1290192 12 131
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk235 := witnessRule 46 8 0 1300000 1300129 10 97
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk236 := witnessRule 46 7 0 1310000 1310128 8 69
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk237 := witnessRule 46 6 0 1320000 1320128 7 53
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk238 := witnessRule 46 5 0 1330000 1330065 5 32
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk239 := witnessRule 46 4 0 1340000 1340064 4 21
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk240 := witnessRule 46 3 0 1350000 1350064 3 13
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk241 := witnessRule 46 2 0 1360000 1360001 2 6
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk242 := witnessRule 46 1 0 1370000 1370000 1 2
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt46_chunk243 := witnessRule 46 0 0 1380000 1380000 1 1
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt46_chunks : List (Chunk 46) := [pack_E6970Receipt46_chunk0, pack_E6970Receipt46_chunk1, pack_E6970Receipt46_chunk2, pack_E6970Receipt46_chunk3, pack_E6970Receipt46_chunk4, pack_E6970Receipt46_chunk5, pack_E6970Receipt46_chunk6, pack_E6970Receipt46_chunk7, pack_E6970Receipt46_chunk8, pack_E6970Receipt46_chunk9, pack_E6970Receipt46_chunk10, pack_E6970Receipt46_chunk11, pack_E6970Receipt46_chunk12, pack_E6970Receipt46_chunk13, pack_E6970Receipt46_chunk14, pack_E6970Receipt46_chunk15, pack_E6970Receipt46_chunk16, pack_E6970Receipt46_chunk17, pack_E6970Receipt46_chunk18, pack_E6970Receipt46_chunk19, pack_E6970Receipt46_chunk20, pack_E6970Receipt46_chunk21, pack_E6970Receipt46_chunk22, pack_E6970Receipt46_chunk23, pack_E6970Receipt46_chunk24, pack_E6970Receipt46_chunk25, pack_E6970Receipt46_chunk26, pack_E6970Receipt46_chunk27, pack_E6970Receipt46_chunk28, pack_E6970Receipt46_chunk29, pack_E6970Receipt46_chunk30, pack_E6970Receipt46_chunk31, pack_E6970Receipt46_chunk32, pack_E6970Receipt46_chunk33, pack_E6970Receipt46_chunk34, pack_E6970Receipt46_chunk35, pack_E6970Receipt46_chunk36, pack_E6970Receipt46_chunk37, pack_E6970Receipt46_chunk38, pack_E6970Receipt46_chunk39, pack_E6970Receipt46_chunk40, pack_E6970Receipt46_chunk41, pack_E6970Receipt46_chunk42, pack_E6970Receipt46_chunk43, pack_E6970Receipt46_chunk44, pack_E6970Receipt46_chunk45, pack_E6970Receipt46_chunk46, pack_E6970Receipt46_chunk47, pack_E6970Receipt46_chunk48, pack_E6970Receipt46_chunk49, pack_E6970Receipt46_chunk50, pack_E6970Receipt46_chunk51, pack_E6970Receipt46_chunk52, pack_E6970Receipt46_chunk53, pack_E6970Receipt46_chunk54, pack_E6970Receipt46_chunk55, pack_E6970Receipt46_chunk56, pack_E6970Receipt46_chunk57, pack_E6970Receipt46_chunk58, pack_E6970Receipt46_chunk59, pack_E6970Receipt46_chunk60, pack_E6970Receipt46_chunk61, pack_E6970Receipt46_chunk62, pack_E6970Receipt46_chunk63, pack_E6970Receipt46_chunk64, pack_E6970Receipt46_chunk65, pack_E6970Receipt46_chunk66, pack_E6970Receipt46_chunk67, pack_E6970Receipt46_chunk68, pack_E6970Receipt46_chunk69, pack_E6970Receipt46_chunk70, pack_E6970Receipt46_chunk71, pack_E6970Receipt46_chunk72, pack_E6970Receipt46_chunk73, pack_E6970Receipt46_chunk74, pack_E6970Receipt46_chunk75, pack_E6970Receipt46_chunk76, pack_E6970Receipt46_chunk77, pack_E6970Receipt46_chunk78, pack_E6970Receipt46_chunk79, pack_E6970Receipt46_chunk80, pack_E6970Receipt46_chunk81, pack_E6970Receipt46_chunk82, pack_E6970Receipt46_chunk83, pack_E6970Receipt46_chunk84, pack_E6970Receipt46_chunk85, pack_E6970Receipt46_chunk86, pack_E6970Receipt46_chunk87, pack_E6970Receipt46_chunk88, pack_E6970Receipt46_chunk89, pack_E6970Receipt46_chunk90, pack_E6970Receipt46_chunk91, pack_E6970Receipt46_chunk92, pack_E6970Receipt46_chunk93, pack_E6970Receipt46_chunk94, pack_E6970Receipt46_chunk95, pack_E6970Receipt46_chunk96, pack_E6970Receipt46_chunk97, pack_E6970Receipt46_chunk98, pack_E6970Receipt46_chunk99, pack_E6970Receipt46_chunk100, pack_E6970Receipt46_chunk101, pack_E6970Receipt46_chunk102, pack_E6970Receipt46_chunk103, pack_E6970Receipt46_chunk104, pack_E6970Receipt46_chunk105, pack_E6970Receipt46_chunk106, pack_E6970Receipt46_chunk107, pack_E6970Receipt46_chunk108, pack_E6970Receipt46_chunk109, pack_E6970Receipt46_chunk110, pack_E6970Receipt46_chunk111, pack_E6970Receipt46_chunk112, pack_E6970Receipt46_chunk113, pack_E6970Receipt46_chunk114, pack_E6970Receipt46_chunk115, pack_E6970Receipt46_chunk116, pack_E6970Receipt46_chunk117, pack_E6970Receipt46_chunk118, pack_E6970Receipt46_chunk119, pack_E6970Receipt46_chunk120, pack_E6970Receipt46_chunk121, pack_E6970Receipt46_chunk122, pack_E6970Receipt46_chunk123, pack_E6970Receipt46_chunk124, pack_E6970Receipt46_chunk125, pack_E6970Receipt46_chunk126, pack_E6970Receipt46_chunk127, pack_E6970Receipt46_chunk128, pack_E6970Receipt46_chunk129, pack_E6970Receipt46_chunk130, pack_E6970Receipt46_chunk131, pack_E6970Receipt46_chunk132, pack_E6970Receipt46_chunk133, pack_E6970Receipt46_chunk134, pack_E6970Receipt46_chunk135, pack_E6970Receipt46_chunk136, pack_E6970Receipt46_chunk137, pack_E6970Receipt46_chunk138, pack_E6970Receipt46_chunk139, pack_E6970Receipt46_chunk140, pack_E6970Receipt46_chunk141, pack_E6970Receipt46_chunk142, pack_E6970Receipt46_chunk143, pack_E6970Receipt46_chunk144, pack_E6970Receipt46_chunk145, pack_E6970Receipt46_chunk146, pack_E6970Receipt46_chunk147, pack_E6970Receipt46_chunk148, pack_E6970Receipt46_chunk149, pack_E6970Receipt46_chunk150, pack_E6970Receipt46_chunk151, pack_E6970Receipt46_chunk152, pack_E6970Receipt46_chunk153, pack_E6970Receipt46_chunk154, pack_E6970Receipt46_chunk155, pack_E6970Receipt46_chunk156, pack_E6970Receipt46_chunk157, pack_E6970Receipt46_chunk158, pack_E6970Receipt46_chunk159, pack_E6970Receipt46_chunk160, pack_E6970Receipt46_chunk161, pack_E6970Receipt46_chunk162, pack_E6970Receipt46_chunk163, pack_E6970Receipt46_chunk164, pack_E6970Receipt46_chunk165, pack_E6970Receipt46_chunk166, pack_E6970Receipt46_chunk167, pack_E6970Receipt46_chunk168, pack_E6970Receipt46_chunk169, pack_E6970Receipt46_chunk170, pack_E6970Receipt46_chunk171, pack_E6970Receipt46_chunk172, pack_E6970Receipt46_chunk173, pack_E6970Receipt46_chunk174, pack_E6970Receipt46_chunk175, pack_E6970Receipt46_chunk176, pack_E6970Receipt46_chunk177, pack_E6970Receipt46_chunk178, pack_E6970Receipt46_chunk179, pack_E6970Receipt46_chunk180, pack_E6970Receipt46_chunk181, pack_E6970Receipt46_chunk182, pack_E6970Receipt46_chunk183, pack_E6970Receipt46_chunk184, pack_E6970Receipt46_chunk185, pack_E6970Receipt46_chunk186, pack_E6970Receipt46_chunk187, pack_E6970Receipt46_chunk188, pack_E6970Receipt46_chunk189, pack_E6970Receipt46_chunk190, pack_E6970Receipt46_chunk191, pack_E6970Receipt46_chunk192, pack_E6970Receipt46_chunk193, pack_E6970Receipt46_chunk194, pack_E6970Receipt46_chunk195, pack_E6970Receipt46_chunk196, pack_E6970Receipt46_chunk197, pack_E6970Receipt46_chunk198, pack_E6970Receipt46_chunk199, pack_E6970Receipt46_chunk200, pack_E6970Receipt46_chunk201, pack_E6970Receipt46_chunk202, pack_E6970Receipt46_chunk203, pack_E6970Receipt46_chunk204, pack_E6970Receipt46_chunk205, pack_E6970Receipt46_chunk206, pack_E6970Receipt46_chunk207, pack_E6970Receipt46_chunk208, pack_E6970Receipt46_chunk209, pack_E6970Receipt46_chunk210, pack_E6970Receipt46_chunk211, pack_E6970Receipt46_chunk212, pack_E6970Receipt46_chunk213, pack_E6970Receipt46_chunk214, pack_E6970Receipt46_chunk215, pack_E6970Receipt46_chunk216, pack_E6970Receipt46_chunk217, pack_E6970Receipt46_chunk218, pack_E6970Receipt46_chunk219, pack_E6970Receipt46_chunk220, pack_E6970Receipt46_chunk221, pack_E6970Receipt46_chunk222, pack_E6970Receipt46_chunk223, pack_E6970Receipt46_chunk224, pack_E6970Receipt46_chunk225, pack_E6970Receipt46_chunk226, pack_E6970Receipt46_chunk227, pack_E6970Receipt46_chunk228, pack_E6970Receipt46_chunk229, pack_E6970Receipt46_chunk230, pack_E6970Receipt46_chunk231, pack_E6970Receipt46_chunk232, pack_E6970Receipt46_chunk233, pack_E6970Receipt46_chunk234, pack_E6970Receipt46_chunk235, pack_E6970Receipt46_chunk236, pack_E6970Receipt46_chunk237, pack_E6970Receipt46_chunk238, pack_E6970Receipt46_chunk239, pack_E6970Receipt46_chunk240, pack_E6970Receipt46_chunk241, pack_E6970Receipt46_chunk242, pack_E6970Receipt46_chunk243]
def rows46 := rowsFrom pack_E6970Receipt46_chunks
theorem good46 : ∀ r ∈ rows46, good 46 r = true := rowsFrom_good pack_E6970Receipt46_chunks
theorem sorted46 : rows46.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt46_chunks 0 (by decide +kernel)).1
theorem mass46 (i : Fin 61) :
    bandCount 46 (i.val : ℤ) 60 16 ≤ (rows46.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt46_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 46 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt46_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total46 : (rows46.map (price 46)).sum = 419635 :=
  (total_eq pack_E6970Receipt46_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt46

section Pack_E6970Receipt47

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt47_chunk0 := witnessA6966Final 47 60 0 810013 810088 32 3640
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk1 := witnessA6966Final 47 60 32 810089 810207 32 3590
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk2 := witnessA6966Final 47 60 64 810208 810324 32 3476
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk3 := witnessA6966Final 47 60 96 810325 810398 32 3568
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk4 := witnessA6966Final 47 60 128 810399 810516 32 3420
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk5 := witnessA6966Final 47 60 160 810517 810640 32 3266
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk6 := witnessA6966Final 47 60 192 810641 810770 32 3172
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk7 := witnessA6966Final 47 60 224 810771 810960 32 2943
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk8 := witnessA6966Final 47 60 256 810961 811030 14 1213
  0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk9 := witnessRule 47 59 0 820012 820087 32 3462
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk10 := witnessRule 47 59 32 820088 820205 32 3396
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk11 := witnessRule 47 59 64 820206 820279 32 3244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk12 := witnessRule 47 59 96 820322 820394 32 3422
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk13 := witnessRule 47 59 128 820395 820513 32 3155
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk14 := witnessRule 47 59 160 820514 820591 32 3080
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk15 := witnessRule 47 59 192 820592 820769 32 2953
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk16 := witnessRule 47 59 224 820770 820961 32 2758
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk17 := witnessRule 47 59 256 820962 821029 12 986
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk18 := witnessRule 47 58 0 830011 830085 32 3292
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk19 := witnessRule 47 58 32 830086 830202 32 3203
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk20 := witnessRule 47 58 64 830203 830276 32 3117
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk21 := witnessRule 47 58 96 830277 830391 32 3190
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk22 := witnessRule 47 58 128 830392 830466 32 2937
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk23 := witnessRule 47 58 160 830512 830589 32 2917
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk24 := witnessRule 47 58 192 830590 830769 32 2761
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk25 := witnessRule 47 58 224 830770 830962 32 2612
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk26 := witnessRule 47 58 256 830963 831029 10 795
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk27 := witnessRule 47 57 0 840010 840084 32 3149
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk28 := witnessRule 47 57 32 840085 840200 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk29 := witnessRule 47 57 64 840201 840273 32 2989
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk30 := witnessRule 47 57 96 840274 840388 32 2991
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk31 := witnessRule 47 57 128 840389 840464 32 2800
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk32 := witnessRule 47 57 160 840465 840588 32 2732
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk33 := witnessRule 47 57 192 840589 840769 32 2609
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk34 := witnessRule 47 57 224 840770 840964 32 2511
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk35 := witnessRule 47 57 256 840965 841028 7 540
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk36 := witnessRule 47 56 0 850009 850082 32 3030
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk37 := witnessRule 47 56 32 850083 850197 32 2929
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk38 := witnessRule 47 56 64 850198 850270 32 2905
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk39 := witnessRule 47 56 96 850271 850386 32 2792
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk40 := witnessRule 47 56 128 850387 850462 32 2667
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk41 := witnessRule 47 56 160 850463 850587 32 2585
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk42 := witnessRule 47 56 192 850588 850770 32 2499
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk43 := witnessRule 47 56 224 850771 851024 32 2422
  0xffdfffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt47_chunk44 := witnessRule 47 56 256 851025 851028 4 300
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk45 := witnessRule 47 55 0 860008 860081 32 2945
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk46 := witnessRule 47 55 32 860082 860195 32 2819
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk47 := witnessRule 47 55 64 860196 860267 32 2841
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk48 := witnessRule 47 55 96 860268 860384 32 2628
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk49 := witnessRule 47 55 128 860385 860461 32 2558
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk50 := witnessRule 47 55 160 860462 860587 32 2472
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk51 := witnessRule 47 55 192 860588 860771 32 2400
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk52 := witnessRule 47 55 224 860772 861027 32 2346
  0xfffbf7ff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt47_chunk53 := witnessRule 47 54 0 870007 870079 32 2886
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk54 := witnessRule 47 54 32 870080 870152 32 2660
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk55 := witnessRule 47 54 64 870193 870265 32 2822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk56 := witnessRule 47 54 96 870266 870339 32 2499
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk57 := witnessRule 47 54 128 870384 870460 32 2461
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk58 := witnessRule 47 54 160 870461 870587 32 2372
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk59 := witnessRule 47 54 192 870588 870773 32 2313
  0xdfffffff 0x1b99a (by decide +kernel)
private def pack_E6970Receipt47_chunk60 := witnessRule 47 54 224 870774 871027 28 1993
  0xfffbe7e 0x175342e2c86c9c58cd8b9319b (by decide +kernel)
private def pack_E6970Receipt47_chunk61 := witnessRule 47 53 0 880006 880078 32 2839
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk62 := witnessRule 47 53 32 880079 880150 32 2599
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk63 := witnessRule 47 53 64 880151 880263 32 2718
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk64 := witnessRule 47 53 96 880264 880338 32 2400
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk65 := witnessRule 47 53 128 880339 880460 32 2355
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk66 := witnessRule 47 53 160 880461 880588 32 2275
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk67 := witnessRule 47 53 192 880589 880775 32 2235
  0xcbedffff 0xb9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt47_chunk68 := witnessRule 47 53 224 880776 881026 23 1594
  0x7ffbe7 0x2ec685c594d938b21b (by decide +kernel)
private def pack_E6970Receipt47_chunk69 := witnessRule 47 52 0 890005 890076 32 2796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk70 := witnessRule 47 52 32 890077 890148 32 2545
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk71 := witnessRule 47 52 64 890149 890262 32 2570
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk72 := witnessRule 47 52 96 890263 890337 32 2302
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk73 := witnessRule 47 52 128 890338 890460 32 2256
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk74 := witnessRule 47 52 160 890461 890640 32 2192
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk75 := witnessRule 47 52 192 890641 890833 32 2162
  0x7c3c9f6d 0x27165362e4ca6c9c990d9b8b19884375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt47_chunk76 := witnessRule 47 52 224 890834 891026 18 1217
  0x3ffde 0x5dcd0b8b31b (by decide +kernel)
private def pack_E6970Receipt47_chunk77 := witnessRule 47 51 0 900004 900075 32 2764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk78 := witnessRule 47 51 32 900076 900146 32 2490
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk79 := witnessRule 47 51 64 900147 900261 32 2435
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk80 := witnessRule 47 51 96 900262 900337 32 2212
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk81 := witnessRule 47 51 128 900338 900461 32 2162
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk82 := witnessRule 47 51 160 900462 900642 32 2120
  0xbdb7ffff 0x574342eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt47_chunk83 := witnessRule 47 51 192 900643 900837 32 2090
  0xf7c3c1e4 0x5c59cd8b9331b27265366e2c86210dd8d0b9b29b27364366e4c66210dc594da38b21b17464364e8c66cdc990da39319b (by decide +kernel)
private def pack_E6970Receipt47_chunk84 := witnessRule 47 51 224 900838 901025 12 797
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk85 := witnessRule 47 50 0 910003 910073 32 2731
  0xfffff9ff 0x1dccd438a2 (by decide +kernel)
private def pack_E6970Receipt47_chunk86 := witnessRule 47 50 32 910074 910145 32 2384
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk87 := witnessRule 47 50 64 910146 910261 32 2316
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk88 := witnessRule 47 50 96 910262 910337 32 2122
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk89 := witnessRule 47 50 128 910384 910462 32 2078
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk90 := witnessRule 47 50 160 910512 910645 32 2051
  0x3927b6d 0x27464366e6c66210dc994da39321b571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt47_chunk91 := witnessRule 47 50 192 910646 910899 32 2033
  0xfffe3c1e 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b (by decide +kernel)
private def pack_E6970Receipt47_chunk92 := witnessRule 47 50 224 910900 911025 6 395
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk93 := witnessRule 47 49 0 920002 920072 32 2706
  0xffff57ff 0x8e8c66d5c990db3a9a (by decide +kernel)
private def pack_E6970Receipt47_chunk94 := witnessRule 47 49 32 920073 920144 32 2284
  0xfaffffd5 0x339319b77434ae6c66d9c590dc38a09b (by decide +kernel)
private def pack_E6970Receipt47_chunk95 := witnessRule 47 49 64 920145 920261 32 2208
  0x3fffd7ff 0x873352e289dc58cdcb8a2 (by decide +kernel)
private def pack_E6970Receipt47_chunk96 := witnessRule 47 49 96 920262 920384 32 2043
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk97 := witnessRule 47 49 128 920385 920513 32 2004
  0xbb6dffff 0x3ba1a17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt47_chunk98 := witnessRule 47 49 160 920514 920648 32 1975
  0xe0780724 0x17466364e8ca6cdcd90c421b9331b4716531088ee685d594d93ab21b3746331086e6ca6d1cd90dab93198845716536ce8620c5d990d93b319b37464368e8c66d5c990db39319b (by decide +kernel)
private def pack_E6970Receipt47_chunk99 := witnessRule 47 49 192 920649 921024 31 1935
  0x7ffffbe1 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt47_chunk100 := witnessRule 47 48 0 930001 930071 32 2616
  0xffeaa3ff 0x2f0c66c9d990d9ba329b673615108ee2c2a26215dc54cdc3922 (by decide +kernel)
private def pack_E6970Receipt47_chunk101 := witnessRule 47 48 32 930072 930144 32 2194
  0xaabffaab 0xdd98cda3a321b57265370e2c2a2125c4913bb19b37564368e6ca6ddc985442438a89884 (by decide +kernel)
private def pack_E6970Receipt47_chunk102 := witnessRule 47 48 64 930145 930262 32 2114
  0xbffd53ff 0x1dd4d23ab19b5736436ce2ca6e5c5441cb892 (by decide +kernel)
private def pack_E6970Receipt47_chunk103 := witnessRule 47 48 96 930263 930386 32 1969
  0x9ffabffa 0x10e86a9c45339b19b77164372e2826d5d18cdb39321b (by decide +kernel)
private def pack_E6970Receipt47_chunk104 := witnessRule 47 48 128 930387 930516 32 1931
  0x7249db6 0x23a321b573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt47_chunk105 := witnessRule 47 48 160 930517 930706 32 1911
  0xbf0780f0 0xb8b51b17467364e6cc62109c9a0d9b8b39884379342eacc6c9d594d9ba32188437366368e4ca62111c59cdabb188317665364ecc86cdd58cc421ba329b (by decide +kernel)
private def pack_E6970Receipt47_chunk106 := witnessRule 47 48 192 930707 931024 24 1466
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk107 := witnessRule 47 47 0 940000 940071 32 2542
  0xffd407ff 0x4329a3776151088eac2a262151d1854ce2b9b0a91885572615438ee4c4ad9c554dc39289b (by decide +kernel)
private def pack_E6970Receipt47_chunk108 := witnessRule 47 47 32 940072 940144 32 2096
  0xa81faa80 0x4ecca6d5d585442339b0a89885672615338ee2c2a46215dc550dcb92a87141276c2aa590d0bbb29b476615108ae8c2a262155cd854ce33930a918856716154390e2c4ae1c54504e438a093 (by decide +kernel)
private def pack_E6970Receipt47_chunk109 := witnessRule 47 47 64 940145 940263 32 2030
  0x47eaa1fa 0x1dcd85442438b0a8988587153372e4885e58cd93bb21b3756536ce8c2a211dc98544c42bb8b0a99c8715231092e2a28e98cd0bc321b (by decide +kernel)
private def pack_E6970Receipt47_chunk110 := witnessRule 47 47 96 940264 940388 32 1898
  0x768afd5 0xce6c662119c994dbb8b2188477634310e46c5e58cd9bbb19b4756436ae8c662115cd94dc3930a8849715131084f0c66cdd990da3a329b (by decide +kernel)
private def pack_E6970Receipt47_chunk111 := witnessRule 47 47 128 940389 940519 32 1859
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt47_chunk112 := witnessRule 47 47 160 940520 940711 32 1856
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt47_chunk113 := witnessRule 47 47 192 940768 940961 16 963
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk114 := witnessRule 47 46 0 950000 950071 32 2402
  0xff4003ff 0x5b0a8831796151310a2f0c2a6709dd8548c4293b30aa1c47662566e8c2aa715d18944e339b12884672625238ee2c4a26215dc94cdc38a923 (by decide +kernel)
private def pack_E6970Receipt47_chunk115 := witnessRule 47 46 32 950072 950145 32 2006
  0x400fe800 0x4f2c2a210ddd8544c429bb30a99c4756152310a8e8c2a8719d1895ab930aa9c7726251390e2c4a2121c948dcb8a09317a6151084f0c2a262149dd854ce1bb30a91885375615438aeac4ad1cd8554e339b1289c772625108ee2c4a4721c944c424b8a893 (by decide +kernel)
private def pack_E6970Receipt47_chunk116 := witnessRule 47 46 64 950146 950265 32 1946
  0x1f5007d 0xaeac2a262155d1854ce339b0a918856726154390e4c4addc554dcb9289b965346f0c2a2111d98544c42a3ab0a99c5746152310aae6c2a871dcd895b38b0aa9c8716251392e4a20e5c5049d30a91b (by decide +kernel)
private def pack_E6970Receipt47_chunk117 := witnessRule 47 46 96 950266 950391 32 1828
  0xe080c5 0x37665368eac862111d198dab9b29884572673630ce4c67061dc588c428c3ba1b17964364f0c662109dd94d9bb3218843756636ce8c2a262159cd854ce3b930a918857716154390e2a662125c54504e4b8a093a64342f2c662105e194da3bb0a884 (by decide +kernel)
private def pack_E6970Receipt47_chunk118 := witnessRule 47 46 128 950392 950523 32 1791
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt47_chunk119 := witnessRule 47 46 160 950576 950773 32 1820
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt47_chunk120 := witnessRule 47 46 192 950832 950960 8 477
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk121 := witnessRule 47 45 0 960000 960072 32 2275
  0x3f8001ff 0x8725141392e44a98944d8bd312b86155364f0c4a270ddd894421bb31291c4756251310a8e8c4a6715cd8948c42ab9312a1c7726356ce4aa6e1cd44dcb912 (by decide +kernel)
private def pack_E6970Receipt47_chunk122 := witnessRule 47 45 32 960073 960146 32 1914
  0x3e000 0x14c2a66c5e58548c428bc30aa1c37862564ecc2aa711d98944e2bab12884574625238ce6c4a262159c9894ce3b8b129188577254372e6aa5c895b12aa615231092c2a86c9e58958bbb0aa9c3776251388ecc4a2111d58948e2ba31289885573625338ce4c4a462159c58950e438b1ab (by decide +kernel)
private def pack_E6970Receipt47_chunk123 := witnessRule 47 45 64 960147 960267 32 1866
  0x14001e 0xddd8548c429bb30aa1c4756153310a8e8c2aa719d18944e3b9b128847726252390e2c4a262161c94cdcb8a923972258c2a20c5e98544c428bcb0a99c2786152310a4eec2a8711dd8959bab0aa9c575625138ce8c4a2119cd8948e3b9312898857716253390e4a462125c9451db0a89884 (by decide +kernel)
private def pack_E6970Receipt47_chunk124 := witnessRule 47 45 96 960268 960394 32 1758
  0x180014 0x1796431082f0cc6c9dd94c4213b339b3756631086e8d06c611d190e0c2b9b1988518572653830ce2c86214619d8dd321883966342f0ca62105dd9cd9bbb0a99c4766152310a8eac2a8715d1854cc42ab9b0aa9c6726154310ace2c2ac7061dc58548e8c438a89885a7121174c2a66c9e58544c4293c30a99c (by decide +kernel)
private def pack_E6970Receipt47_chunk125 := witnessRule 47 45 128 960395 960580 32 1738
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt47_chunk126 := witnessRule 47 45 160 960581 960960 32 1802
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk127 := witnessRule 47 44 0 970000 970072 32 2153
  0x3f8001ff 0x8735131092e4a24ed89441d31291b1796251310a2f0c4a6709dd8948c4293b312a1c47663566e8c4aa715d18d44e339b1a884672635238ee2c6a26215dcd4cdc392923 (by decide +kernel)
private def pack_E6970Receipt47_chunk128 := witnessRule 47 44 32 970073 970147 32 1831
  0x1f000 0x18c4aa98948d8bd31289c2796251084f0c4a470ddd8944c429bb31299c4756252310a8e8c4a8719d18d5ab9312a9c7726351390e2c6a2121cd48dcb8a8a094b6251362f4c4a2105e58948e13c312898852776253386ecc4a46214dd58950e2bab1ab473625538ce6c6a271dc98d4423b8b1a91c (by decide +kernel)
private def pack_E6970Receipt47_chunk129 := witnessRule 47 44 64 970192 970269 32 1786
  0x40007 0x1796153310a2f0c2aa709dd8550c4293b30ab1c476625238aeac4a262155d1894ce339b1291885672625438ee2c4a66215dc954d8c439289ca72256c4a26e9854cc424b0aa9b2796251386f0c4a210ddd8948e23b31289885475625338ae8c4a462155cd8950e3b9b1ab6716255390e2c6a2725cd441cb92093 (by decide +kernel)
private def pack_E6970Receipt47_chunk130 := witnessRule 47 44 96 970270 970397 32 1692
  0xe4030004 0x4b31883868342ecd26c609d994e0c1bab21885183746638308e6ca6214611c99ce0c2b8b3188518578372c2aa6c5e58550e13c30a998852776155386ecc2a86214dd58558e23a30aa988547361573830ae6c2a674619c98548c430c338b0aa1d1877153310a310e2826236d8548c42530aa1b (by decide +kernel)
private def pack_E6970Receipt47_chunk131 := witnessRule 47 44 128 970448 970584 32 1691
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt47_chunk132 := witnessRule 47 44 160 970640 970897 24 1330
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk133 := witnessRule 47 43 0 980000 980073 32 2043
  0x1fc001ff 0x6716354390e2c8ae1cd4504e531a89b17a63570c4aa6c9e18d44e1bbb1a8843766352388eac6a262151d18d4ce2b9b1a91885572635438ee4c8ad9cd54dc3a289b (by decide +kernel)
private def pack_E6970Receipt47_chunk134 := witnessRule 47 43 32 980074 980193 32 1777
  0xc000f800 0x5b1289884a6253362f2c4a462145e18950e1bc31ab2766255388ecc6a2715d58d4422ba31a91c6736351310ace4c6a671dc58d48c42bb9aa1b974556c6aa98948c424b12a1b27963562eec4aa70ddd8d44e23b31a884475635238ae8c6a262155cd8d4ce33931a91885 (by decide +kernel)
private def pack_E6970Receipt47_chunk135 := witnessRule 47 43 64 980194 980271 32 1677
  0x80010001 0x531299b9615531090c2ae6c9e1894ce1bbb12918853766254388eac4a662151d18954e2b9b12a188557262563830ce4c4a47461dc58944c430c3b9299c9715241196c4a40ed8948d8bd312898851796253384f0c4a462149dd8950e1bb31299885375625538aeac6a2719d18d442339b1a91c7726351310aee2c6a6721cd48c424b9a8a3 (by decide +kernel)
private def pack_E6970Receipt47_chunk136 := witnessRule 47 43 96 980320 980451 32 1638
  0xec06000 0xb9b69b2726c31084e2dc6cdf4c41c30ab9b181766738304eacc6214609d1a0e0c1b9b39885183726938308e2d06214611e8dd30aa188496156362f0c2aa62145dd855ce13b30ab1885275615838306eac2a874611d1854cc430c239b0aa9d185726154310c30ae2c2ac74619c554c4294338a19c (by decide +kernel)
private def pack_E6970Receipt47_chunk137 := witnessRule 47 43 128 980452 980644 32 1651
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt47_chunk138 := witnessRule 47 43 160 980645 980896 16 875
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk139 := witnessRule 47 42 0 990000 990073 32 1939
  0xfc000ff 0x1dc9914423b8b2291c8745131092e6a24ed8d441d31a91b1796351310a2f0c6a6709dd8d48c4293b31aa1c47664566e8c6aa715d19144e339b22884672645238ee2c8a26215dd14cdc39a923 (by decide +kernel)
private def pack_E6970Receipt47_chunk140 := witnessRule 47 42 32 990074 990194 32 1700
  0x60003c00 0x25c54904a5b1a883a6352362f4c6a2709e58d44213c31a91c3776351310a6ecc6a6711d58d48c42a3a31aa1c6746456ae4c6aa71dc99144e438b2288487452372e4a28252d8d44d8bd31a8841796352384f0c6a262149dd8d4ce1bb31a91885375635438aeac8ad1cd8d54e339b2289c (by decide +kernel)
private def pack_E6970Receipt47_chunk141 := witnessRule 47 42 64 990195 990321 32 1608
  0x20000000 0x708e2c870e15ccc42531291904a6254362f2c4a662145e18954e13bb12a18852766256386eac4aa6214dd1895ce0c23a31299d185736252310c30ae4c4a874619c5894cc430c3392a9c2877151311b4e4422ed8944c8253129988496255362f0c4a862145dd8958e1bbb1a91c4766351310a8eac6a6715d18d48c42ab9b1aa1c6726353310ace2c6aa7061dc58d44e8c439a884 (by decide +kernel)
private def pack_E6970Receipt47_chunk142 := witnessRule 47 42 96 990322 990454 32 1574
  0xfbfe0c00 0x5c590036302e8d470609cda4c428c139359c183716a310a306f86e58954dc30ab98847615936302eec2aa74609d98550c430c13ab0ab1d183746155310c306e6c2ae74611c98558c430c238b0ac1d (by decide +kernel)
private def pack_E6970Receipt47_chunk143 := witnessRule 47 42 128 990455 990706 32 1629
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk144 := witnessRule 47 42 160 990707 990896 9 488
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk145 := witnessRule 47 41 0 1000000 1000074 32 1842
  0x7e000ff 0x15cd914ce339322918856716454390e2caae1d14504e532289b17a64570c6aa6c9e19144e1bbb228843766452388eac8a262151d1914ce2b9b2291885572645438ee4caad9d154dc3aa89b (by decide +kernel)
private def pack_E6970Receipt47_chunk146 := witnessRule 47 41 32 1000075 1000196 32 1623
  0x18001e00 0x619c58d4ce8c3b9a918851887251411b6c6a2621298d4cd8bcb1a918851786354384eec6a662149d98d54e23b32289c575645108ae8c8a4719cd9144c42b3932299c7716452310aee8a86c621d15db22aa635231092c6a86c9e59158bbb1aa9c3776451388ecc8a2111d59148e2ba32289885 (by decide +kernel)
private def pack_E6970Receipt47_chunk147 := witnessRule 47 41 64 1000197 1000324 32 1539
  0x4000000 0x304e6c2b274e09cd94e1c1b9321885383716638708ea62129894cc824b12a988486257362eec4ac62145d98960e0c13b312a1d183756253310c306e8c4aa74611cd8950c430c239312b1d185716255310c30ae4ae70e15c54ce0c439210cb6254074c6a4621258d50d8bcb1a99c2786352310a4eec6a870dd98d4cc429bab1aa9c4746354310a8e6c6ac70615cd8d48e8c33931a89886 (by decide +kernel)
private def pack_E6970Receipt47_chunk148 := witnessRule 47 41 96 1000325 1000458 32 1522
  0xfffff181 0xc0b9369c182716c310a304fc6e58950c824312b18841886155310a30ec2ae70605d98558c430c0bab0ac1d (by decide +kernel)
private def pack_E6970Receipt47_chunk149 := witnessRule 47 41 128 1000512 1000832 32 1620
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk150 := witnessRule 47 41 160 1000833 1000833 1 54
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk151 := witnessRule 47 40 0 1010000 1010074 32 1747
  0x2fe003ff 0x11cd9154e339b2a89c7716552396c8a20e99148d8bcb22898851786453384eec8a462149d99150e23b32ab374645538ae8caa2719cd9544233932a91c (by decide +kernel)
private def pack_E6970Receipt47_chunk152 := witnessRule 47 40 32 1010075 1010197 32 1548
  0xc002f00 0xc2b931a998861857163553a30ce6a86214a19c94508edb1a983a6452372c6a8621218d58d93c32291c3776451310a6ecc8a6711d59148c42a3a322a1c5736453310aae4c8aa70619c99144e8c3ba291cb6451362f4c8a2105e59148e13c322898852776453386ecc8a46214dd59150e2bab2ab (by decide +kernel)
private def pack_E6970Receipt47_chunk153 := witnessRule 47 40 64 1010198 1010326 32 1471
  0x61000000 0xc2b0ad1c381736738704e4cc6214e09c5a0e1c1bb9884a625234092c6a8621218d58d8c4312a9c181776254310c302ecc4ac74609d58954c430c13a312b9d183736256310c306e4c4b074e0dc98550e9c238b0a9988638471553870ce2643298d44cc2531a9988496355362f0c6a862145dd8d58e13b31aa9885275635738306eac6a674611d18d48c430c239b1aa1d (by decide +kernel)
private def pack_E6970Receipt47_chunk154 := witnessRule 47 40 96 1010327 1010515 32 1488
  0xffffffb5 0xc0ba006e18954cc20c3b0ab1905 (by decide +kernel)
private def pack_E6970Receipt47_chunk155 := witnessRule 47 40 128 1010516 1010832 26 1296
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk156 := witnessRule 47 39 0 1020000 1020075 32 1655
  0x1f0007f 0x475655238ae8caa262155cd954ce33932a9188567165543830ee2cab21d54504e532a89b17a65570c8aa6c9e19544e1bbb2a8843766552388eacaa262151d1954ce2b9b2a91885572655438ee4ccad9d554dc3b289b (by decide +kernel)
private def pack_E6970Receipt47_chunk157 := witnessRule 47 39 32 1020076 1020199 32 1475
  0x3000380 0x306e8c6a8621860dcd8d58e8c23931aa98861847163573a708e2c4a674e15c948c42d32289904a6453362f2c8a462145e19150e13bb22998852766455386eac8a86214dd19158e0c23a32291d185736451310c30ae4c8a674619c59148c430c33a2a1c2877351196c8a40e99148c424b22a1b1786453310a2eec8aa70ddd9544e23b32a884 (by decide +kernel)
private def pack_E6970Receipt47_chunk158 := witnessRule 47 39 64 1020200 1020329 32 1410
  0xff600000 0xe05c5a8e4b1a99984863553208310c4a8641461d8958c428c3312c1c181756257310c302e8c4b274e05d18554e9c139b0aa18863827261563a706e2c2aa6218e0dc55ce24239988ca6355074c6a4661259150dc31ab18847635836302eec6a874609d98d4cc430c13ab1aa9d (by decide +kernel)
private def pack_E6970Receipt47_chunk159 := witnessRule 47 39 96 1020330 1020519 32 1464
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk160 := witnessRule 47 39 128 1020576 1020832 19 935
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk161 := witnessRule 47 38 0 1030000 1030075 32 1564
  0xbf001ff 0x3756554388e8caa662151cd9554e0c2b9b2a89d1867165523b6caa20e99548d8bcb2a898851786553384eecaa462149d99550e23b332b374655538ae8cca2719cd9944233933291c (by decide +kernel)
private def pack_E6970Receipt47_chunk162 := witnessRule 47 38 32 1030076 1030200 32 1403
  0x38009c0 0xc0bab1ab9d182746356310c304e6c6b074e09cd8950e9c1b9312998863837162553b4c8a80e99148c824b22a188486456362eec8aa62145d9915ce0c13b32299d183756452310c306e8c8a874611cd914cc430c239322a9d18574563870ae6a47299544c424b2a99b1796552384f0caa262149dd954ce1bb32a91885 (by decide +kernel)
private def pack_E6970Receipt47_chunk163 := witnessRule 47 38 64 1030201 1030331 32 1362
  0xfff80100 0x258d48d42431aa1a041886253340a30ec4aa6614619895cc828c2b12c98853856155310a708c2ae70e05cd8558c431c0b930ac1d382715938b04ea6e98d44d424b2299904864553108310c6a8621461d8d58e0c0bb31aa9886 (by decide +kernel)
private def pack_E6970Receipt47_chunk164 := witnessRule 47 38 96 1030384 1030579 32 1445
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk165 := witnessRule 47 38 128 1030580 1030769 12 581
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk166 := witnessRule 47 37 0 1040000 1040076 32 1477
  0x1f8007f 0x4eccaa862149d59558e0c1bab2a91d184746551310c308e6caa674615c99548c430c2b8b2aa1da6651372caa6621219554d93c33289c3776651086eccca4711d59944c42a3a33299c5736652310aae4cca870619c999633b2a9b (by decide +kernel)
private def pack_E6970Receipt47_chunk167 := witnessRule 47 37 32 1040077 1040202 32 1331
  0xe002e0 0xc3b1aa99051866357310a30ac6b270e158954e1c0ba312a18863817362563a704e4c4aa6218e09c5895ced32289a049655331090caaa6c6219150e0c0bbb22998861817664553a304eac8a86218609d19158e8c1b9b22a98861837264573a706e4c6a674e11cd50e532a983a655231092caa86c5e1954cc428bbb2aa9c (by decide +kernel)
private def pack_E6970Receipt47_chunk168 := witnessRule 47 37 64 1040203 1040386 32 1329
  0xffff5560 0x218d4cd820c3b12a1a851856258330a708c2ac6414e098568e2c0bb9ba6357072c8a4681219150cc20c431a99985 (by decide +kernel)
private def pack_E6970Receipt47_chunk169 := witnessRule 47 37 96 1040387 1040642 32 1429
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk170 := witnessRule 47 37 128 1040643 1040768 5 240
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk171 := witnessRule 47 36 0 1050000 1050076 32 1391
  0xf800ff 0x302eecaa674609d99548c430c13ab2aa1d183746553310c306e6caaa74611c99550c430c238b2ab1d3847164523b4cca40e99948d8bcb32898851786653384eecca462149d99950e1bab3299885374665538308e8cca274615cd994428c2b933291d (by decide +kernel)
private def pack_E6970Receipt47_chunk172 := witnessRule 47 36 32 1050077 1050203 32 1271
  0x3000f0 0x6218d48d428c3b1aa1a051866356330a30ac6b06414e158950c829c2312b1885383625838702e4c4ae6218e05c58964eac0b8b0aa9da6456072caa4661219550c820c4322999051876455310a30cc8ae70605d59158c430c0ba322c1d3817463543a704e6c6a66218e09c98d54e9c1b8b1aa1886a655133092cca66e19554c423b2ab9b (by decide +kernel)
private def pack_E6970Receipt47_chunk173 := witnessRule 47 36 64 1050204 1050389 32 1301
  0xfffffffc 0x259144d82432299a84 (by decide +kernel)
private def pack_E6970Receipt47_chunk174 := witnessRule 47 36 96 1050390 1050768 31 1371
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk175 := witnessRule 47 35 0 1060000 1060077 32 1309
  0x3c00bf 0xc432a99885187655538302eccaa86218605d59558e8c13a32aa98861827365573a704e6c8a674e0dc99148c431c1b8b22a1d3847453310b4cca264125994cc424332a9b1776654310a2ecccac70609d99948e8c1bab32898861837466533a308e6cca46218611c99950e8c2bb2a9c (by decide +kernel)
private def pack_E6970Receipt47_chunk176 := witnessRule 47 35 32 1060078 1060205 32 1220
  0x80040038 0x10c8a46e106218d44dc28c3b1a99b051866355350a30ac6ae6814e15894cd029c2312a99853836257320a704c4b262156098554c42ac0b0ab9c5817156310b2caa26a121954cd020c432291a051876454330a30cc8ac64146159160c429c2b1aa1885384635638702e6c6aa6218e05c98d5ce9c138b1ab18863827358394caaa0e59948c824332a1884 (by decide +kernel)
private def pack_E6970Receipt47_chunk177 := witnessRule 47 35 64 1060256 1060392 32 1277
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk178 := witnessRule 47 35 96 1060448 1060705 24 1041
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk179 := witnessRule 47 34 0 1070000 1070077 32 1231
  0x5c005f 0x6219548cc28c3b2aa19051866556310a30acab070e159150e1c0ba322998863817364553a704e4c8a86218e09c59158ea41b9a8a19da6654072cea4621219d50d8c433299c181776652310c302eccca874609d5994cc430c13a332a9d183736654310c306e4ccac74e0dc99548e9c23aa99c (by decide +kernel)
private def pack_E6970Receipt47_chunk180 := witnessRule 47 34 32 1070078 1070257 32 1178
  0xf554000c 0xc3b1a91c051856356360a708c4a86a14e098960cc2ac0b0ab190568146372caae0e19548d820c432289b051876453350a30cc8aa6814615915ccc29c2b1a999853846355320a706c6ae6214e098d64e2c1312a9c581716254310cb02e4ac7259944d02433299984 (by decide +kernel)
private def pack_E6970Receipt47_chunk181 := witnessRule 47 34 64 1070258 1070450 32 1253
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk182 := witnessRule 47 34 96 1070451 1070704 18 765
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk183 := witnessRule 47 33 0 1080000 1080078 32 1163
  0xe003f 0x10cca46a106219544d428c3b2a99a051866555330a30acaae6414e15914cc829c2322a9885383645738702e4c8ac6218e05c59160eac0b8b1aa1d5827353310b2cea2661219d4cc820c4332919051876654310a30cccac70605d59954c430c0ba332b9d3817465533a704e6caa46218e09c99550e9c1b8b2a99886 (by decide +kernel)
private def pack_E6970Receipt47_chunk184 := witnessRule 47 33 32 1080079 1080259 32 1145
  0xfffffa06 0x1856456350a708c6a86814e0d8d58cc29c131ac19055826254320ab02c4ac621560960dcb32b03 (by decide +kernel)
private def pack_E6970Receipt47_chunk185 := witnessRule 47 33 64 1080260 1080454 32 1231
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk186 := witnessRule 47 33 96 1080512 1080704 12 503
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk187 := witnessRule 47 32 0 1090000 1090078 32 1102
  0x4006004f 0x86651370830ecaa46c146199550d428c2b2ab1a053856452340a708c8a86614e0d9158c829c1322c18855826354310ab02c6ac71605cd54c42ac13928a1988e96755070cea468106219944d028c3b32999851866655320a30accae6214e15954cc429c232aa9c381736554310c702e4caac74e09d55ce2c13a299c (by decide +kernel)
private def pack_E6970Receipt47_chunk188 := witnessRule 47 32 32 1090128 1090261 32 1114
  0xffffe541 0x3b2a91c841876451390a30ac8aa6e14e118d4cd829c131ab9a055826253340ab02c4aa66156095cc82340a8a29885 (by decide +kernel)
private def pack_E6970Receipt47_chunk189 := witnessRule 47 32 64 1090262 1090515 32 1211
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk190 := witnessRule 47 32 96 1090516 1090641 6 247
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk191 := witnessRule 47 31 0 1100000 1100128 32 1050
  0xda83000f 0x76652380830acaaa6c14e11914cd429c1322b99855826353330ab02c6aa641560d5cc4234128a29c867513608310ccac1061d9948d428c3332a1a051856656330a70acaa46614e119550c829c1b2ab1885382655838b04c8a871605c5914cc432c0ba2a9c (by decide +kernel)
private def pack_E6970Receipt47_chunk192 := witnessRule 47 31 32 1100129 1100263 32 1084
  0xfffffdea 0x18664523a0a704c6ac6c156058950d42b40a8a21985 (by decide +kernel)
private def pack_E6970Receipt47_chunk193 := witnessRule 47 31 64 1100264 1100640 32 1198
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk194 := witnessRule 47 30 0 1110000 1110129 32 1005
  0xffa1fd07 0x704c8ac6a156058d50d02ac1ab19846825144320ad02e2a2866438e11954cd029c132ab99055826453320ab02c8aa62156115cdb40b9a9988d (by decide +kernel)
private def pack_E6970Receipt47_chunk195 := witnessRule 47 30 32 1110130 1110265 32 1055
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk196 := witnessRule 47 30 64 1110320 1110640 27 987
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk197 := witnessRule 47 29 0 1120000 1120130 32 965
  0xf2f4a547 0x199948ec20c332a89d851846555390ab02c6a66c15a09450cd02bc0a999088576751390830ccca470146159950dc29c232a91b053826556340ab02c8a8661561158c82341a8a21885 (by decide +kernel)
private def pack_E6970Receipt47_chunk198 := witnessRule 47 29 32 1120131 1120322 32 1030
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk199 := witnessRule 47 29 64 1120323 1120577 21 747
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk200 := witnessRule 47 28 0 1130000 1130131 32 926
  0xfdfd5bd3 0x18565523c0ad04a2846c15e050ccc6333a91d041846655380ab02c8a66a15a0d450ccc2bc129990c (by decide +kernel)
private def pack_E6970Receipt47_chunk201 := witnessRule 47 28 32 1130132 1130324 32 1003
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk202 := witnessRule 47 28 64 1130325 1130576 16 555
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk203 := witnessRule 47 27 0 1140000 1140132 32 892
  0xfffffff7 0x341a8a11a85 (by decide +kernel)
private def pack_E6970Receipt47_chunk204 := witnessRule 47 27 32 1140133 1140384 32 979
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk205 := witnessRule 47 27 64 1140385 1140576 11 374
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk206 := witnessRule 47 26 0 1150000 1150133 32 858
  0xffffe5fd 0x567523d0830acca27a1460d9954ec2bc0a8a1198886 (by decide +kernel)
private def pack_E6970Receipt47_chunk207 := witnessRule 47 26 32 1150134 1150387 32 955
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk208 := witnessRule 47 26 64 1150388 1150513 6 199
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk209 := witnessRule 47 25 0 1160000 1160134 32 826
  0xfffffbff 0xc233291f05 (by decide +kernel)
private def pack_E6970Receipt47_chunk210 := witnessRule 47 25 32 1160135 1160450 32 936
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk211 := witnessRule 47 25 64 1160512 1160512 1 33
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk212 := witnessRule 47 24 0 1170000 1170135 32 795
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk213 := witnessRule 47 24 32 1170136 1170512 29 823
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk214 := witnessRule 47 23 0 1180000 1180136 32 765
  0xfffff5ff 0x119d44d2008306cca468805 (by decide +kernel)
private def pack_E6970Receipt47_chunk215 := witnessRule 47 23 32 1180192 1180449 24 657
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk216 := witnessRule 47 22 0 1190000 1190192 32 735
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk217 := witnessRule 47 22 32 1190193 1190448 20 527
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk218 := witnessRule 47 21 0 1200000 1200194 32 707
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk219 := witnessRule 47 21 32 1200195 1200448 16 407
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk220 := witnessRule 47 20 0 1210000 1210195 32 677
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk221 := witnessRule 47 20 32 1210196 1210385 12 293
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk222 := witnessRule 47 19 0 1220000 1220197 32 649
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk223 := witnessRule 47 19 32 1220256 1220384 8 189
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk224 := witnessRule 47 18 0 1230000 1230257 32 621
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk225 := witnessRule 47 18 32 1230258 1230384 5 114
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk226 := witnessRule 47 17 0 1240000 1240320 32 596
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk227 := witnessRule 47 17 32 1240321 1240321 1 22
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk228 := witnessRule 47 16 0 1250000 1250320 30 528
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk229 := witnessRule 47 15 0 1260000 1260320 27 447
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk230 := witnessRule 47 14 0 1270000 1270257 24 369
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk231 := witnessRule 47 13 0 1280000 1280256 21 300
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk232 := witnessRule 47 12 0 1290000 1290256 19 251
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk233 := witnessRule 47 11 0 1300000 1300193 16 193
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk234 := witnessRule 47 10 0 1310000 1310192 14 153
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk235 := witnessRule 47 9 0 1320000 1320192 12 119
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk236 := witnessRule 47 8 0 1330000 1330129 10 87
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk237 := witnessRule 47 7 0 1340000 1340128 8 61
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk238 := witnessRule 47 6 0 1350000 1350128 7 46
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk239 := witnessRule 47 5 0 1360000 1360065 5 27
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk240 := witnessRule 47 4 0 1370000 1370064 4 17
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk241 := witnessRule 47 3 0 1380000 1380064 3 10
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk242 := witnessRule 47 2 0 1390000 1390001 2 4
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk243 := witnessRule 47 1 0 1400000 1400000 1 1
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt47_chunk244 := witnessRule 47 0 0 1410000 1410000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt47_chunks : List (Chunk 47) := [pack_E6970Receipt47_chunk0, pack_E6970Receipt47_chunk1, pack_E6970Receipt47_chunk2, pack_E6970Receipt47_chunk3, pack_E6970Receipt47_chunk4, pack_E6970Receipt47_chunk5, pack_E6970Receipt47_chunk6, pack_E6970Receipt47_chunk7, pack_E6970Receipt47_chunk8, pack_E6970Receipt47_chunk9, pack_E6970Receipt47_chunk10, pack_E6970Receipt47_chunk11, pack_E6970Receipt47_chunk12, pack_E6970Receipt47_chunk13, pack_E6970Receipt47_chunk14, pack_E6970Receipt47_chunk15, pack_E6970Receipt47_chunk16, pack_E6970Receipt47_chunk17, pack_E6970Receipt47_chunk18, pack_E6970Receipt47_chunk19, pack_E6970Receipt47_chunk20, pack_E6970Receipt47_chunk21, pack_E6970Receipt47_chunk22, pack_E6970Receipt47_chunk23, pack_E6970Receipt47_chunk24, pack_E6970Receipt47_chunk25, pack_E6970Receipt47_chunk26, pack_E6970Receipt47_chunk27, pack_E6970Receipt47_chunk28, pack_E6970Receipt47_chunk29, pack_E6970Receipt47_chunk30, pack_E6970Receipt47_chunk31, pack_E6970Receipt47_chunk32, pack_E6970Receipt47_chunk33, pack_E6970Receipt47_chunk34, pack_E6970Receipt47_chunk35, pack_E6970Receipt47_chunk36, pack_E6970Receipt47_chunk37, pack_E6970Receipt47_chunk38, pack_E6970Receipt47_chunk39, pack_E6970Receipt47_chunk40, pack_E6970Receipt47_chunk41, pack_E6970Receipt47_chunk42, pack_E6970Receipt47_chunk43, pack_E6970Receipt47_chunk44, pack_E6970Receipt47_chunk45, pack_E6970Receipt47_chunk46, pack_E6970Receipt47_chunk47, pack_E6970Receipt47_chunk48, pack_E6970Receipt47_chunk49, pack_E6970Receipt47_chunk50, pack_E6970Receipt47_chunk51, pack_E6970Receipt47_chunk52, pack_E6970Receipt47_chunk53, pack_E6970Receipt47_chunk54, pack_E6970Receipt47_chunk55, pack_E6970Receipt47_chunk56, pack_E6970Receipt47_chunk57, pack_E6970Receipt47_chunk58, pack_E6970Receipt47_chunk59, pack_E6970Receipt47_chunk60, pack_E6970Receipt47_chunk61, pack_E6970Receipt47_chunk62, pack_E6970Receipt47_chunk63, pack_E6970Receipt47_chunk64, pack_E6970Receipt47_chunk65, pack_E6970Receipt47_chunk66, pack_E6970Receipt47_chunk67, pack_E6970Receipt47_chunk68, pack_E6970Receipt47_chunk69, pack_E6970Receipt47_chunk70, pack_E6970Receipt47_chunk71, pack_E6970Receipt47_chunk72, pack_E6970Receipt47_chunk73, pack_E6970Receipt47_chunk74, pack_E6970Receipt47_chunk75, pack_E6970Receipt47_chunk76, pack_E6970Receipt47_chunk77, pack_E6970Receipt47_chunk78, pack_E6970Receipt47_chunk79, pack_E6970Receipt47_chunk80, pack_E6970Receipt47_chunk81, pack_E6970Receipt47_chunk82, pack_E6970Receipt47_chunk83, pack_E6970Receipt47_chunk84, pack_E6970Receipt47_chunk85, pack_E6970Receipt47_chunk86, pack_E6970Receipt47_chunk87, pack_E6970Receipt47_chunk88, pack_E6970Receipt47_chunk89, pack_E6970Receipt47_chunk90, pack_E6970Receipt47_chunk91, pack_E6970Receipt47_chunk92, pack_E6970Receipt47_chunk93, pack_E6970Receipt47_chunk94, pack_E6970Receipt47_chunk95, pack_E6970Receipt47_chunk96, pack_E6970Receipt47_chunk97, pack_E6970Receipt47_chunk98, pack_E6970Receipt47_chunk99, pack_E6970Receipt47_chunk100, pack_E6970Receipt47_chunk101, pack_E6970Receipt47_chunk102, pack_E6970Receipt47_chunk103, pack_E6970Receipt47_chunk104, pack_E6970Receipt47_chunk105, pack_E6970Receipt47_chunk106, pack_E6970Receipt47_chunk107, pack_E6970Receipt47_chunk108, pack_E6970Receipt47_chunk109, pack_E6970Receipt47_chunk110, pack_E6970Receipt47_chunk111, pack_E6970Receipt47_chunk112, pack_E6970Receipt47_chunk113, pack_E6970Receipt47_chunk114, pack_E6970Receipt47_chunk115, pack_E6970Receipt47_chunk116, pack_E6970Receipt47_chunk117, pack_E6970Receipt47_chunk118, pack_E6970Receipt47_chunk119, pack_E6970Receipt47_chunk120, pack_E6970Receipt47_chunk121, pack_E6970Receipt47_chunk122, pack_E6970Receipt47_chunk123, pack_E6970Receipt47_chunk124, pack_E6970Receipt47_chunk125, pack_E6970Receipt47_chunk126, pack_E6970Receipt47_chunk127, pack_E6970Receipt47_chunk128, pack_E6970Receipt47_chunk129, pack_E6970Receipt47_chunk130, pack_E6970Receipt47_chunk131, pack_E6970Receipt47_chunk132, pack_E6970Receipt47_chunk133, pack_E6970Receipt47_chunk134, pack_E6970Receipt47_chunk135, pack_E6970Receipt47_chunk136, pack_E6970Receipt47_chunk137, pack_E6970Receipt47_chunk138, pack_E6970Receipt47_chunk139, pack_E6970Receipt47_chunk140, pack_E6970Receipt47_chunk141, pack_E6970Receipt47_chunk142, pack_E6970Receipt47_chunk143, pack_E6970Receipt47_chunk144, pack_E6970Receipt47_chunk145, pack_E6970Receipt47_chunk146, pack_E6970Receipt47_chunk147, pack_E6970Receipt47_chunk148, pack_E6970Receipt47_chunk149, pack_E6970Receipt47_chunk150, pack_E6970Receipt47_chunk151, pack_E6970Receipt47_chunk152, pack_E6970Receipt47_chunk153, pack_E6970Receipt47_chunk154, pack_E6970Receipt47_chunk155, pack_E6970Receipt47_chunk156, pack_E6970Receipt47_chunk157, pack_E6970Receipt47_chunk158, pack_E6970Receipt47_chunk159, pack_E6970Receipt47_chunk160, pack_E6970Receipt47_chunk161, pack_E6970Receipt47_chunk162, pack_E6970Receipt47_chunk163, pack_E6970Receipt47_chunk164, pack_E6970Receipt47_chunk165, pack_E6970Receipt47_chunk166, pack_E6970Receipt47_chunk167, pack_E6970Receipt47_chunk168, pack_E6970Receipt47_chunk169, pack_E6970Receipt47_chunk170, pack_E6970Receipt47_chunk171, pack_E6970Receipt47_chunk172, pack_E6970Receipt47_chunk173, pack_E6970Receipt47_chunk174, pack_E6970Receipt47_chunk175, pack_E6970Receipt47_chunk176, pack_E6970Receipt47_chunk177, pack_E6970Receipt47_chunk178, pack_E6970Receipt47_chunk179, pack_E6970Receipt47_chunk180, pack_E6970Receipt47_chunk181, pack_E6970Receipt47_chunk182, pack_E6970Receipt47_chunk183, pack_E6970Receipt47_chunk184, pack_E6970Receipt47_chunk185, pack_E6970Receipt47_chunk186, pack_E6970Receipt47_chunk187, pack_E6970Receipt47_chunk188, pack_E6970Receipt47_chunk189, pack_E6970Receipt47_chunk190, pack_E6970Receipt47_chunk191, pack_E6970Receipt47_chunk192, pack_E6970Receipt47_chunk193, pack_E6970Receipt47_chunk194, pack_E6970Receipt47_chunk195, pack_E6970Receipt47_chunk196, pack_E6970Receipt47_chunk197, pack_E6970Receipt47_chunk198, pack_E6970Receipt47_chunk199, pack_E6970Receipt47_chunk200, pack_E6970Receipt47_chunk201, pack_E6970Receipt47_chunk202, pack_E6970Receipt47_chunk203, pack_E6970Receipt47_chunk204, pack_E6970Receipt47_chunk205, pack_E6970Receipt47_chunk206, pack_E6970Receipt47_chunk207, pack_E6970Receipt47_chunk208, pack_E6970Receipt47_chunk209, pack_E6970Receipt47_chunk210, pack_E6970Receipt47_chunk211, pack_E6970Receipt47_chunk212, pack_E6970Receipt47_chunk213, pack_E6970Receipt47_chunk214, pack_E6970Receipt47_chunk215, pack_E6970Receipt47_chunk216, pack_E6970Receipt47_chunk217, pack_E6970Receipt47_chunk218, pack_E6970Receipt47_chunk219, pack_E6970Receipt47_chunk220, pack_E6970Receipt47_chunk221, pack_E6970Receipt47_chunk222, pack_E6970Receipt47_chunk223, pack_E6970Receipt47_chunk224, pack_E6970Receipt47_chunk225, pack_E6970Receipt47_chunk226, pack_E6970Receipt47_chunk227, pack_E6970Receipt47_chunk228, pack_E6970Receipt47_chunk229, pack_E6970Receipt47_chunk230, pack_E6970Receipt47_chunk231, pack_E6970Receipt47_chunk232, pack_E6970Receipt47_chunk233, pack_E6970Receipt47_chunk234, pack_E6970Receipt47_chunk235, pack_E6970Receipt47_chunk236, pack_E6970Receipt47_chunk237, pack_E6970Receipt47_chunk238, pack_E6970Receipt47_chunk239, pack_E6970Receipt47_chunk240, pack_E6970Receipt47_chunk241, pack_E6970Receipt47_chunk242, pack_E6970Receipt47_chunk243, pack_E6970Receipt47_chunk244]
def rows47 := rowsFrom pack_E6970Receipt47_chunks
theorem good47 : ∀ r ∈ rows47, good 47 r = true := rowsFrom_good pack_E6970Receipt47_chunks
theorem sorted47 : rows47.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt47_chunks 0 (by decide +kernel)).1
theorem mass47 (i : Fin 61) :
    bandCount 47 (i.val : ℤ) 60 16 ≤ (rows47.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt47_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 47 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt47_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total47 : (rows47.map (price 47)).sum = 417654 :=
  (total_eq pack_E6970Receipt47_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt47

section Pack_E6970Receipt48

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt48_chunk0 := witnessA6966Final 48 60 0 840012 840086 32 3694
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk1 := witnessA6966Final 48 60 32 840087 840203 32 3596
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk2 := witnessA6966Final 48 60 64 840204 840277 32 3536
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk3 := witnessA6966Final 48 60 96 840278 840391 32 3602
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk4 := witnessA6966Final 48 60 128 840392 840465 32 3408
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk5 := witnessA6966Final 48 60 160 840466 840586 32 3374
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk6 := witnessA6966Final 48 60 192 840587 840713 32 3172
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk7 := witnessA6966Final 48 60 224 840714 840899 32 2994
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk8 := witnessA6966Final 48 60 256 840900 841030 21 1820
  0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk9 := witnessRule 48 59 0 850011 850085 32 3516
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk10 := witnessRule 48 59 32 850086 850201 32 3394
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk11 := witnessRule 48 59 64 850202 850274 32 3370
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk12 := witnessRule 48 59 96 850275 850388 32 3340
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk13 := witnessRule 48 59 128 850389 850463 32 3234
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk14 := witnessRule 48 59 160 850464 850585 32 3126
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk15 := witnessRule 48 59 192 850586 850713 32 2939
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk16 := witnessRule 48 59 224 850714 850900 32 2773
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk17 := witnessRule 48 59 256 850901 851029 18 1470
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk18 := witnessRule 48 58 0 860010 860083 32 3342
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk19 := witnessRule 48 58 32 860084 860198 32 3188
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk20 := witnessRule 48 58 64 860199 860271 32 3238
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk21 := witnessRule 48 58 96 860272 860385 32 3095
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk22 := witnessRule 48 58 128 860386 860460 32 3069
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk23 := witnessRule 48 58 160 860461 860583 32 2902
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk24 := witnessRule 48 58 192 860584 860712 32 2746
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk25 := witnessRule 48 58 224 860713 860901 32 2606
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk26 := witnessRule 48 58 256 860902 861029 16 1261
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk27 := witnessRule 48 57 0 870009 870082 32 3194
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk28 := witnessRule 48 57 32 870083 870196 32 3020
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk29 := witnessRule 48 57 64 870197 870268 32 3097
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk30 := witnessRule 48 57 96 870269 870341 32 2865
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk31 := witnessRule 48 57 128 870384 870459 32 2901
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk32 := witnessRule 48 57 160 870460 870583 32 2716
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk33 := witnessRule 48 57 192 870584 870713 32 2585
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk34 := witnessRule 48 57 224 870714 870903 32 2488
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk35 := witnessRule 48 57 256 870960 871028 12 919
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk36 := witnessRule 48 56 0 880008 880080 32 3066
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk37 := witnessRule 48 56 32 880081 880153 32 2823
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk38 := witnessRule 48 56 64 880194 880265 32 3051
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk39 := witnessRule 48 56 96 880266 880338 32 2722
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk40 := witnessRule 48 56 128 880339 880457 32 2702
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk41 := witnessRule 48 56 160 880458 880582 32 2564
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk42 := witnessRule 48 56 192 880583 880713 32 2469
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk43 := witnessRule 48 56 224 880714 880961 32 2402
  0xfbffffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt48_chunk44 := witnessRule 48 56 256 880962 881028 9 666
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk45 := witnessRule 48 55 0 890007 890079 32 2970
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk46 := witnessRule 48 55 32 890080 890151 32 2733
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk47 := witnessRule 48 55 64 890152 890263 32 2894
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk48 := witnessRule 48 55 96 890264 890337 32 2590
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk49 := witnessRule 48 55 128 890338 890457 32 2545
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk50 := witnessRule 48 55 160 890458 890583 32 2446
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk51 := witnessRule 48 55 192 890584 890715 32 2365
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk52 := witnessRule 48 55 224 890768 890965 32 2324
  0xffbf7fff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt48_chunk53 := witnessRule 48 55 256 891024 891027 4 288
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk54 := witnessRule 48 54 0 900006 900077 32 2899
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk55 := witnessRule 48 54 32 900078 900149 32 2665
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk56 := witnessRule 48 54 64 900150 900261 32 2769
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk57 := witnessRule 48 54 96 900262 900335 32 2480
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk58 := witnessRule 48 54 128 900336 900456 32 2423
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk59 := witnessRule 48 54 160 900457 900583 32 2346
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk60 := witnessRule 48 54 192 900584 900769 32 2283
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk61 := witnessRule 48 54 224 900770 901027 32 2248
  0xfffbe7ed 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt48_chunk62 := witnessRule 48 53 0 910005 910076 32 2852
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk63 := witnessRule 48 53 32 910077 910147 32 2601
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk64 := witnessRule 48 53 64 910148 910260 32 2614
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk65 := witnessRule 48 53 96 910261 910335 32 2376
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk66 := witnessRule 48 53 128 910336 910457 32 2320
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk67 := witnessRule 48 53 160 910458 910585 32 2249
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk68 := witnessRule 48 53 192 910586 910772 32 2204
  0x5f6fffff 0x27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt48_chunk69 := witnessRule 48 53 224 910773 911026 26 1774
  0x3ffdf3e 0x176342e2ca6c9c590d8b9321b (by decide +kernel)
private def pack_E6970Receipt48_chunk70 := witnessRule 48 52 0 920004 920074 32 2807
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk71 := witnessRule 48 52 32 920075 920145 32 2546
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk72 := witnessRule 48 52 64 920146 920259 32 2473
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk73 := witnessRule 48 52 96 920260 920334 32 2278
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk74 := witnessRule 48 52 128 920335 920457 32 2222
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk75 := witnessRule 48 52 160 920458 920586 32 2162
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk76 := witnessRule 48 52 192 920587 920775 32 2130
  0xe1e4fb6f 0x2e4ca6c9c990d9b8b19884375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt48_chunk77 := witnessRule 48 52 224 920776 921026 21 1399
  0x1ffef3 0x2ee685c598d938b29b (by decide +kernel)
private def pack_E6970Receipt48_chunk78 := witnessRule 48 51 0 930003 930073 32 2774
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk79 := witnessRule 48 51 32 930074 930144 32 2426
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk80 := witnessRule 48 51 64 930145 930259 32 2349
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk81 := witnessRule 48 51 96 930260 930335 32 2182
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk82 := witnessRule 48 51 128 930336 930459 32 2129
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk83 := witnessRule 48 51 160 930460 930640 32 2084
  0xf6dfffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt48_chunk84 := witnessRule 48 51 192 930641 930835 32 2061
  0xdf0f0792 0x2e2ce6c5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt48_chunk85 := witnessRule 48 51 224 930836 931025 14 914
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk86 := witnessRule 48 50 0 940002 940071 32 2734
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk87 := witnessRule 48 50 32 940072 940143 32 2328
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk88 := witnessRule 48 50 64 940144 940259 32 2236
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk89 := witnessRule 48 50 96 940260 940335 32 2091
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk90 := witnessRule 48 50 128 940336 940460 32 2044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk91 := witnessRule 48 50 160 940461 940643 32 2017
  0xe49edb7 0xdc994da39321b571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt48_chunk92 := witnessRule 48 50 192 940644 940897 32 1999
  0xfff8f078 0x2e4ce6c9c598c4213c1a17366364e6ca6cdc990c421b8b31b47531062e8ca6c9d190d9b9b19884 (by decide +kernel)
private def pack_E6970Receipt48_chunk93 := witnessRule 48 50 224 940898 941025 8 516
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk94 := witnessRule 48 49 0 950001 950071 32 2650
  0xffffd7ff 0x19c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt48_chunk95 := witnessRule 48 49 32 950072 950143 32 2219
  0xfe7ffff5 0x873352e289dc58cdcb8a2 (by decide +kernel)
private def pack_E6970Receipt48_chunk96 := witnessRule 48 49 64 950144 950260 32 2136
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk97 := witnessRule 48 49 96 950261 950337 32 1999
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk98 := witnessRule 48 49 128 950384 950512 32 1973
  0x76dbffff 0x3ba1a17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt48_chunk99 := witnessRule 48 49 160 950513 950647 32 1946
  0xc0f00e49 0x17466364e8ca6cdcd90c421b9331b4716531088ee685d594d93ab21b3746331086e6ca6d1cd90dab93198845716536ce8620c5d990d93b319b37464368e8c66d5c990db39319b (by decide +kernel)
private def pack_E6970Receipt48_chunk100 := witnessRule 48 49 192 950648 951024 32 1964
  0xfffff7c3 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt48_chunk101 := witnessRule 48 48 0 960000 960070 32 2562
  0xfffaabff 0x1bb319b4746436ae4ca6e1c5854424b892 (by decide +kernel)
private def pack_E6970Receipt48_chunk102 := witnessRule 48 48 32 960071 960143 32 2132
  0xeafffea9 0x5746336ce4c86ddd4d23ab19b5736436ce2ca6e5c5441cb892 (by decide +kernel)
private def pack_E6970Receipt48_chunk103 := witnessRule 48 48 64 960144 960261 32 2044
  0xbfff57ff 0x87434ce6c66ddc590dcb8a09b (by decide +kernel)
private def pack_E6970Receipt48_chunk104 := witnessRule 48 48 96 960262 960385 32 1925
  0xbffebffe 0x973350e2c66e9c513b9319b (by decide +kernel)
private def pack_E6970Receipt48_chunk105 := witnessRule 48 48 128 960386 960515 32 1901
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt48_chunk106 := witnessRule 48 48 160 960516 960705 32 1879
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt48_chunk107 := witnessRule 48 48 192 960706 961024 25 1501
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk108 := witnessRule 48 47 0 970000 970071 32 2430
  0xffaa81ff 0x298cd0bc321b2766536aeac2a2119cd8544c42b3930a99c7716152310aee2a86e5c95438a093 (by decide +kernel)
private def pack_E6970Receipt48_chunk109 := witnessRule 48 47 32 970072 970144 32 2029
  0x551ff550 0x4f0c66cdd990da3a329b7736151090e2c2a262161c54cdcb92217963364eec86cdd594db3a30a8847726151310aee2c2a6721c548c424b8a8a3 (by decide +kernel)
private def pack_E6970Receipt48_chunk110 := witnessRule 48 47 64 970145 970263 32 1963
  0xabfd55ff 0x67265372e2c2a2129c491bbb19b4756436ae6ca6e1c9854424b8a89884 (by decide +kernel)
private def pack_E6970Receipt48_chunk111 := witnessRule 48 47 96 970264 970388 32 1855
  0x476d13fa 0x19d18cdbb9321b8716331090ea685e58cd9bbb19b5756336ce6c86ddc98cc423b8b29ba7151074e2491d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt48_chunk112 := witnessRule 48 47 128 970389 970519 32 1827
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt48_chunk113 := witnessRule 48 47 160 970520 970711 32 1824
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt48_chunk114 := witnessRule 48 47 192 970768 970961 16 947
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk115 := witnessRule 48 46 0 980000 980071 32 2294
  0x7fa801ff 0x4b8a093a6152364f2c2a210ddd8544c429bb30a99c4756152310a8e8c2a8719d1895ab930aa9c7726251390e2c4a2121c948dcb8a093 (by decide +kernel)
private def pack_E6970Receipt48_chunk116 := witnessRule 48 46 32 980072 980145 32 1942
  0xa80ff500 0x2f0ca6d1dd854422bab0a89885574615338ce6c2a462159c98550e439312b77155372e4a26e594d1bc30a8844766151310a8eac2a6715d18548c42ab9b0aa1c7736256ce2c2aa721c58944e4b92883 (by decide +kernel)
private def pack_E6970Receipt48_chunk117 := witnessRule 48 46 64 980146 980265 32 1885
  0xa06aa03a 0x675615108ee6c2a26215dc9854ce438b0a9188587154374e4aa5c5049db19a17964364eeca6d5d98544233a30a89885673615338ee4c2a46215dc58550e4b8b12b9715141392e2824f18555321a (by decide +kernel)
private def pack_E6970Receipt48_chunk118 := witnessRule 48 46 96 980266 980391 32 1786
  0xe411e8 0xdd994da3b321b575633108ae8ca6d9cd90c42339331b771653108eee685e590d93cb19b37764368ecc662111d594daba32188457366370e4c2a262161c5854ce4b8a9188417a63364f0c86cddd8cc421bb329b (by decide +kernel)
private def pack_E6970Receipt48_chunk119 := witnessRule 48 46 128 980392 980523 32 1759
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt48_chunk120 := witnessRule 48 46 160 980576 980773 32 1788
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt48_chunk121 := witnessRule 48 46 192 980832 980960 8 469
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk122 := witnessRule 48 45 0 990000 990072 32 2174
  0x3f8000ff 0x43929188497251476c2a262129854cd8bcb0a918851786154386f0c4ac9d98554e23b31289c575625108ae8c4a4719cd8944c42b3931299c7716252310aee4a86e5cd54b912 (by decide +kernel)
private def pack_E6970Receipt48_chunk123 := witnessRule 48 45 32 990073 990146 32 1856
  0x4001e800 0x5ed8544213cb0a898852786153386eec2a46214dd98550e2bb312b474615538ce8c4a271dcd894423b931291c8716251310b0e4a66e5c5491cb912c6151062f4c2a262145e5854ce13c30a918852776154388eec4acdd58554e2bab1289c674625108ce6c4a471dc98944c42bb8b1299c (by decide +kernel)
private def pack_E6970Receipt48_chunk124 := witnessRule 48 45 64 990147 990267 32 1806
  0x801a8007 0x4776151310a8ecc2a6715d58548c42aba30aa1c6736153310ace4c2aa721c98944e4b8b1288497252374e2824ed8548d93d30a8843786151310a6eec2a6711d98548c42a3ab0aa1c6756256ae6c2aa71dcd8944e4393128848716252392e4a262129c5449cb912 (by decide +kernel)
private def pack_E6970Receipt48_chunk125 := witnessRule 48 45 96 990268 990394 32 1718
  0x801c0010 0x2f0cc6c9e194d9bbb2188437666368eaca62111d19cdab9b318845726836ce2ce62119e4d0bd31988417965364f0c862109dd98d9bb3298843756736aeac2a6719d18548c42b39b0aa1c7726153310aee2c2aa721c550c420c438a11cb6331074ca685e590c420bc331b (by decide +kernel)
private def pack_E6970Receipt48_chunk126 := witnessRule 48 45 128 990395 990580 32 1706
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt48_chunk127 := witnessRule 48 45 160 990581 990960 32 1770
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk128 := witnessRule 48 44 0 1000000 1000072 32 2057
  0x1f8000ff 0x21c58d44e4b9a88397241278c4aa98948d8bd31289c2796251084f0c4a470ddd8944c429bb31299c4756252310a8e8c4a8719d18d5ab9312a9c7726351390e2c6a2121cd48dcb8a8a094 (by decide +kernel)
private def pack_E6970Receipt48_chunk129 := witnessRule 48 44 32 1000073 1000147 32 1774
  0xf000 0xc62556c2a4621298550d93d312b1786155386f0c4a2711dd8944223b31291c5756251310aae8c4a6719cd8948c42b39312a1c8726356ee4aa6e5cd44dd3912b6251362f6c4ae58554d93cb1289c3786251086eec4a4711d98944c42a3ab1299c5746252310aae6c4a871dcd8d5b38b12a9c (by decide +kernel)
private def pack_E6970Receipt48_chunk130 := witnessRule 48 44 64 1000192 1000269 32 1730
  0x3 0x5e9854ce13cb0a918852786154386eec2a66214dd98554e23ab0aa1885474615638ce8c4a471dcd8944c42bb931299c8716252310b0e4a86c625c544653912c615131096c2a66c5e98548c428bcb0aa1c2786153310a4eec2aa711dd8944e2bb312884575625238ce8c4a262159cd894ce3b9312918857716254392e2c6ae5c94504e53912 (by decide +kernel)
private def pack_E6970Receipt48_chunk131 := witnessRule 48 44 96 1000270 1000397 32 1654
  0xf8030006 0x2f0ce6c9dd98c4213b341b3756731086e8d26d1cda0c42239351b571693108af66a994c41cb39a1786631082eed06cddd8550e23b30a99885475615538ae8c2a862155cd8558e33930aa988567161573850ce2c670a1dc8c42530aa1b (by decide +kernel)
private def pack_E6970Receipt48_chunk132 := witnessRule 48 44 128 1000448 1000584 32 1659
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt48_chunk133 := witnessRule 48 44 160 1000640 1000897 24 1306
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk134 := witnessRule 48 43 0 1010000 1010073 32 1956
  0xfc000ff 0x1dc98d44c42bb8b1a99c8735231092e6a28ed8944c42531299b1796252310a2f0c4a870de18d593b312a9c476635138aeac6a2115d18d48e339b1a89885672635338ee2c6a46215dcd50dcba2a (by decide +kernel)
private def pack_E6970Receipt48_chunk135 := witnessRule 48 43 32 1010074 1010193 32 1715
  0xc0007800 0x318944d8bdb1288417a6252384f2c4a262149e1894ce1bbb1291885376625438aecc6ad1d18954e33a31a89c773635108ee4c6a4721c58d44c42c39a99b97252478c4a20ed8948d8bd312898851796253384f0c4a462149dd8950e23bb1ab375625538aeac6a2719d18d442339b1a91c (by decide +kernel)
private def pack_E6970Receipt48_chunk136 := witnessRule 48 43 64 1010194 1010271 32 1631
  0x80018000 0x5b0a99884a6155362f2c2a862145e18558e13bb0aa98852766157388ecc4a6715d58948c42aba312a1c6736253310ace4c4aa71dc58950c42bb92b1b2877152396c4a46e98550c424b0ab1b2796252386f0c4a26214ddd894ce23b31291885475625438ae8c4a662155cd8954e3b9b1a89c8726351090e2c6a4725cd44c425392893 (by decide +kernel)
private def pack_E6970Receipt48_chunk137 := witnessRule 48 43 96 1010320 1010451 32 1602
  0xfc07000 0x2e6da6c9c9b0c42138b71b37d31062ecd46c9d5a4c4213a359b3736a31086e4d86d1c5acc4223e9a96156362f2c2aa709e18550c4293bb0ab1c3766155310a6eac2ae711d18558c42a39b0ac1c28473643850ae4c66214a15c594e1433a1884 (by decide +kernel)
private def pack_E6970Receipt48_chunk138 := witnessRule 48 43 128 1010452 1010644 32 1619
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt48_chunk139 := witnessRule 48 43 160 1010645 1010896 16 859
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk140 := witnessRule 48 42 0 1020000 1020073 32 1854
  0x7c0007f 0x7736456ce2c6aa721c59144e4ba28839715241298c6aa98d48d8bd31a89c2796351084f0c6a470ddd8d44c429bb31a99c4756352310a8e8c6a8719d1915ab931aa9c7726451390e2c8a2121d148dcb928a094 (by decide +kernel)
private def pack_E6970Receipt48_chunk141 := witnessRule 48 42 32 1020074 1020194 32 1640
  0x20001c00 0x1887251413b4e2844f189481db1291884a6254362f2c4a662145e18954e1bc31a89c4776351088ecc6a4715d58d44c42aba31a99c6736352310ace4c6a8721c9915bb9aa9b97451374e2a44ed8d44d8bdb1ab96255364f2c6a270de18d4421bbb1a91c4766351310a8eac6a6715d18d48c42ab9b1aa1c (by decide +kernel)
private def pack_E6970Receipt48_chunk142 := witnessRule 48 42 64 1020195 1020321 32 1566
  0x30000000 0xa11c59ce142bb1884a6254372c2ac621218560d93c312a1c3776253310a6ecc4aa711d58950c42a3a312b1c5736255310aae4c4ae70a15c9854ce94338b0a91886286715438510e42ed8944c825b1299b17a6252310a2f2c4a8709e1894cc4293bb12a9c3766254310a6eac4ac715d58d48e33a31a89885673635338ee4c6a46215dc58d50e439a99884 (by decide +kernel)
private def pack_E6970Receipt48_chunk143 := witnessRule 48 42 96 1020322 1020454 32 1539
  0xfbfe0c20 0xb8b2006c5d1b4d939b618842726e366e2da6210dfcd530aa988496157362f0c2ac62145dd8560e13ab0ac9c282756538506e8c86214a0dcd98e14239329885 (by decide +kernel)
private def pack_E6970Receipt48_chunk144 := witnessRule 48 42 128 1020455 1020706 32 1597
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk145 := witnessRule 48 42 160 1020707 1020896 9 479
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk146 := witnessRule 48 41 0 1030000 1030074 32 1764
  0x3e0007f 0x674645108ce6c8a471dc99144c42bb8b2299c8745231092e8a28ed8d44c42531a99b1796352310a2f0c6a870de191593b31aa9c476645138aeac8a2115d19148e339b2289885672645338ee2c8a46215dd150dcbaaa (by decide +kernel)
private def pack_E6970Receipt48_chunk147 := witnessRule 48 41 32 1030075 1030196 32 1565
  0x8000e00 0x67163563850ce2c4a474a1dc944c428c4b8a8908db635131094c6a66c5e98d48e13cb1a898852786353386eec6a46214dd98d50e23ab1a99885474635538ce8c8a271dcd914423b932291c8716451310b0e8a66e5cd491e31a883b6352362f4c6a262145e58d4ce13c31a918852776354388eec8acdd58d54e2bab2289c (by decide +kernel)
private def pack_E6970Receipt48_chunk148 := witnessRule 48 41 64 1030197 1030324 32 1499
  0x4000800 0xa09d198c4294139b41c2837267310a506e2d270a11e0c42531299904a6255362f2c4a862145e18958e13bb12a98852766257386eac4ac6214dd18960e141ba30aa1d284736153310c508e4c2aa74a15c58550c43142b8ab1c3867231196c4a4641298950c424b12b1b1786255310a2eec4ae70ddd8d4ce23b31a91885475635438ae8c6a662155cd8d54e33931aa1885 (by decide +kernel)
private def pack_E6970Receipt48_chunk149 := witnessRule 48 41 96 1030325 1030458 32 1488
  0xfffff1d6 0x5c9900364e2de62109d10352c2ac6411d8568d940bab39c (by decide +kernel)
private def pack_E6970Receipt48_chunk150 := witnessRule 48 41 128 1030512 1030832 32 1588
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk151 := witnessRule 48 41 160 1030833 1030833 1 53
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk152 := witnessRule 48 40 0 1040000 1040074 32 1670
  0x3e0017f 0xae8c8a462155cd9150e3b9b2ab6716455390e2caa2725d5441e322aa6452362f4c8a2709e59144213c32291c3776451310a6ecc8a6711d59148c42a3a322a1c6746556ae4c8aa71dc99544e43aa91b (by decide +kernel)
private def pack_E6970Receipt48_chunk153 := witnessRule 48 40 32 1040075 1040197 32 1494
  0x4002700 0x508e6c4a674a15c98948c43142b8b12a1d2867253310a50ee2a282623ad8d4c1db1a91884a6354362f2c6a662145e18d54e13bb1aa18852766356388ecc8a4715d59144c42aba32299c6736452310ace4c8a871dd154d943b9a89cb6451374c6a6621258d54d93cb2289c3786451086eec8a4711d99144c42a3ab2299c (by decide +kernel)
private def pack_E6970Receipt48_chunk154 := witnessRule 48 40 64 1040198 1040326 32 1433
  0xe1800000 0x502e6d470a09c9a4c4294138b59c2837a31094c4a8641258958c424312c1b1776257310a2ecc4b270a05d98554e9413ab0aa18862827461563a506e6c2aa6218a0dc9855ce94238b0ab1886284715838908e86ed8944d02531a9988496355362f2c6a8709e18d4cc4293bb1aa9c3766354310a6eac6ac711d18d54c42a39b1ab9c (by decide +kernel)
private def pack_E6970Receipt48_chunk155 := witnessRule 48 40 96 1040327 1040515 32 1456
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt48_chunk156 := witnessRule 48 40 128 1040516 1040832 26 1270
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk157 := witnessRule 48 39 0 1050000 1050075 32 1582
  0xf0003f 0xdd59154e2bab2a89c674655108ce6caa471dc99544c42bb8b2a99c875523108310e8a292d9144c42532299b1796452310a2f0c8a870de195593b322a9c476655138aeacaa2115d19548e339b2a89885672655338ee2caa46215dd550dcbb2a (by decide +kernel)
private def pack_E6970Receipt48_chunk158 := witnessRule 48 39 32 1050076 1050199 32 1423
  0x1000180 0x1413ab12a1d283746253310c506e6c4aa74a11c98950c4314238b12b1d2857255310a70ae2a28676d8d44cc2532299b9635531090c6ae6c9e1914ce1bbb22918853766454388eac8a662151d19154e2b9b22a188557264563850ae4c6a474a19c58d44c4314339a99c1887252411b6c8a40ed9148d8bd322898851796453384f0c8a462149dd9150e1bb32299885 (by decide +kernel)
private def pack_E6970Receipt48_chunk159 := witnessRule 48 39 64 1050200 1050329 32 1374
  0xff601080 0x281716d394c4a6681258954cc24312b990476259310850ec2aa6214a19855ce140bab0ab18862817461583a504e4c2b275209c994e241b8b2188548376374c6a4661298d50c424b1ab1b1786355310a2eec6ae709d98d58c4293ab1ac1c (by decide +kernel)
private def pack_E6970Receipt48_chunk160 := witnessRule 48 39 96 1050330 1050519 32 1432
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk161 := witnessRule 48 39 128 1050576 1050832 19 916
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk162 := witnessRule 48 38 0 1060000 1060075 32 1494
  0x8f000bf 0x4766551310a8eacaa6715d19548c42ab9b2aa1c67165553850ce2c8a274a1dd14425b2a883a6552362f4caa2709e59544213c32a91c3776551310a6eccaa6711d59548c42a3a32aa1c6746656ae4caaa71dc99944e43b291b (by decide +kernel)
private def pack_E6970Receipt48_chunk163 := witnessRule 48 38 32 1060076 1060200 32 1354
  0x8000c0 0x140bb312a18862817562563a504e8c4aa6218a09cd895ce941b9312b18862837162583a906e2c2a875211c54cc42db1aa83a645232094c8a86c5e5914cc428bc322a9c2776454310a4ecc8ac70dd59154c429ba322b9c2837463533a508e6c6a46218a11c98d50e942b8b1a9988628573553870ce4a26236d9144c8253229988496455362f0c8a862145dd9158e1bbb2a91c (by decide +kernel)
private def pack_E6970Receipt48_chunk164 := witnessRule 48 38 64 1060201 1060331 32 1327
  0xfffd5600 0x4b12a1a8476258330850cc2ac6414a118568e240b9339c4827166310a904f06e98d44d42531a999849635532090c6ae6211d8d64d943b12a9c (by decide +kernel)
private def pack_E6970Receipt48_chunk165 := witnessRule 48 38 96 1060384 1060579 32 1413
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk166 := witnessRule 48 38 128 1060580 1060769 12 569
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk167 := witnessRule 48 37 0 1070000 1070076 32 1410
  0xf8007f 0x2776554386eccaa66214dd59554e23a32aa1885473655638508e6c8a474a15c99144c43142b8b2299db655131094caa66c5e59548c428bc32aa1c2776553310a4eccaaa711d99944e2bab32884574665238ce6cca262159c9994ce3b8b3291885 (by decide +kernel)
private def pack_E6970Receipt48_chunk168 := witnessRule 48 37 32 1070077 1070202 32 1286
  0x600260 0xec6b06410a1d8950c82943312b1885285625838502e8c4ae6218a05cd8964ea40b9b0aa9d482726154310c904e2c2ac7699144d025322999049645531090c8ae6c5dd9158c428bb322c1c2817663543a504eac6a66218a09d18d54e941b9b1aa18862837263563a508e6ae71211c94ce5b22a03a655231092caa86c5e5954ce13c32a91885 (by decide +kernel)
private def pack_E6970Receipt48_chunk169 := witnessRule 48 37 64 1070203 1070386 32 1297
  0xffffffe8 0x4817a374c6a46a1258d50d02431ab1984 (by decide +kernel)
private def pack_E6970Receipt48_chunk170 := witnessRule 48 37 96 1070387 1070642 32 1397
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk171 := witnessRule 48 37 128 1070643 1070768 5 235
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk172 := witnessRule 48 36 0 1080000 1080076 32 1328
  0xf8005f 0xbbb2ab1c2766555310a4eacaae70a09d5914ce941ba322918862837364543a508e4c8a66218a11c59154edb2a983a6652372caa8621219558d93c33291c3776651310a6eccca6711d59948c42a3a332a1c5736653310aae4ccaa70a15c99544e9433aa91c (by decide +kernel)
private def pack_E6970Receipt48_chunk173 := witnessRule 48 36 32 1080077 1080203 32 1228
  0x3000b0 0x10c6aa6a11d8d5cd02143b1299a052866255330a50ac4ae6414a118964c42a4230aa9885483615738902e4c2ac6219205c58560ed322b03a645234092c8a8661219158c823b22c18842876354310a50cc6ac70a05d58d54c43140ba31ab9d282736356310c504e4c6b075209c98950ea41b92a9ca655133094caa6621259554d8bc32aa1885 (by decide +kernel)
private def pack_E6970Receipt48_chunk174 := witnessRule 48 36 64 1080204 1080389 32 1269
  0xfffffffc 0x298d44dc24b1a99b04 (by decide +kernel)
private def pack_E6970Receipt48_chunk175 := witnessRule 48 36 96 1080390 1080768 31 1340
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk176 := witnessRule 48 35 0 1090000 1090077 32 1248
  0x3c003f 0x219558c423b2ac1b287645438502ecc8a66218a05d59154e9413a322a18862827364563a506e4c8aa6218a0dc5915cea41b8b1a99da665132094cca66c5e59948c428bc332a1c2776653310a4ecccaa70dd59950c429ba332b1c2837465523a508e6caa26218a11c9954ce942b8b2a91886 (by decide +kernel)
private def pack_E6970Receipt48_chunk177 := witnessRule 48 35 32 1090078 1090205 32 1180
  0xaaac0038 0x4b1a91c0476356360850cc4a86a14a118960cc2a41b0ab1905481615a394c8a26c125914cd424322a9a0476457330850ec6a66614a198d54c82942b1ab9885284635938908c4aa71205cd8950c43240b9312b1d482716255310d4caaa0e99548cc24b2aa1904 (by decide +kernel)
private def pack_E6970Receipt48_chunk178 := witnessRule 48 35 64 1090256 1090392 32 1245
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk179 := witnessRule 48 35 96 1090448 1090705 24 1017
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk180 := witnessRule 48 34 0 1100000 1100077 32 1176
  0x1c005f 0x10caaa6611d955cc82143b22999052866455310a50ac8ae70a05d19158c43140b9b22c1d4817363543a904e4c6a66219209c58d54ea41b9aa1885a6654074cca4641259950c424332b1b1776655310a2ecccae70a05d9954ce9413ab2a918862827465543a506e6caa66218a0dc99554e9423aab1c (by decide +kernel)
private def pack_E6970Receipt48_chunk181 := witnessRule 48 34 32 1100078 1100257 32 1142
  0xfffe000c 0x14c8b00e59148dc24322a1b0476456350850ec6a46a14a198d50d02942b1ab19852846358320a908c4a8641520d8958c42a41312c1c481716257310c902e4b27299544d424b2a99a04 (by decide +kernel)
private def pack_E6970Receipt48_chunk182 := witnessRule 48 34 64 1100258 1100450 32 1221
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk183 := witnessRule 48 34 96 1100451 1100704 18 747
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk184 := witnessRule 48 33 0 1110000 1110078 32 1111
  0x6002f 0x4b2a91b04865543508ecaac6810a1d9148d02943322a19852856456320a508c8b062152118d50c42a41b1ab1c481726355310c902e2c6ae75209cd58c42ac13928a21da665134092cca6661219954c823b32b98842876553310a50ccaaa70a05d59550c43140ba32ab1d282736555310c504e4caae75209c9914cea41ba2a1c (by decide +kernel)
private def pack_E6970Receipt48_chunk185 := witnessRule 48 33 32 1110079 1110259 32 1110
  0xfffffa02 0x14331a99b052846357340a908c4a6681520d8954cc2a41312b99054816259310ad02c2aa6215a055cdd32ab83 (by decide +kernel)
private def pack_E6970Receipt48_chunk186 := witnessRule 48 33 64 1110260 1110454 32 1199
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk187 := witnessRule 48 33 96 1110512 1110704 12 491
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk188 := witnessRule 48 32 0 1120000 1120078 32 1053
  0x4006000f 0x4b2a89c0476555360850ec8a26c14a19914cd42942b22a9a052846457330a908c6a6661520d8d54c82a4131ab9885481635938d02c4aa71a05c950c42d332b039665235090cca86811d9958cc2143b2a919852866554320a50acaac6214a119560e242322a1c481736453310c902e4c8aa75209c59150c432413a2b1c (by decide +kernel)
private def pack_E6970Receipt48_chunk189 := witnessRule 48 32 32 1120128 1120261 32 1080
  0xffffe555 0x10c8a47411d9150e4214331a91c052846356360a906c4a86a152058960cc2b40ab1904 (by decide +kernel)
private def pack_E6970Receipt48_chunk190 := witnessRule 48 32 64 1120262 1120515 32 1179
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk191 := witnessRule 48 32 96 1120516 1120641 6 241
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk192 := witnessRule 48 31 0 1130000 1130128 32 1006
  0xda810007 0x219548e4214332291b852846456350a906c6a868152098d58cc2a40b1ac19056816254320ad04ac6211a05c54510c474b3289b84866533608eccaa6a10a1d9544d4294332a99a052856555330a508caae6415211914cc82a41b22a9885482645738902e2c8ac6219205d160e340b9aa1c (by decide +kernel)
private def pack_E6970Receipt48_chunk193 := witnessRule 48 31 32 1130129 1130263 32 1052
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk194 := witnessRule 48 31 64 1130264 1130640 32 1166
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk195 := witnessRule 48 30 0 1140000 1140129 32 963
  0xffa1fd07 0x906c6a66c152058d5cd02b40b1299a05682553308f02a8622214a119558d02a41b22a19854826456320a902c8b06215a058d50c42b41ab1b (by decide +kernel)
private def pack_E6970Receipt48_chunk196 := witnessRule 48 30 32 1140130 1140265 32 1023
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk197 := witnessRule 48 30 64 1140320 1140640 27 960
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk198 := witnessRule 48 29 0 1150000 1150130 32 925
  0xf2f52543 0xecaa4781199550ec2142b2291d054816356360ad04a86a11e0510c86433289d0466655380850ccaa27014a119554d82a41b2299a854816457330ad02c6a66615a0d54c823c12a188c (by decide +kernel)
private def pack_E6970Receipt48_chunk199 := witnessRule 48 29 32 1150131 1150322 32 998
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk200 := witnessRule 48 29 64 1150323 1150577 21 726
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk201 := witnessRule 48 28 0 1160000 1160131 32 890
  0xfdffdbd3 0x159554f023b3291d842856552390a902c8ac6a15a0d50d023c129988905 (by decide +kernel)
private def pack_E6970Receipt48_chunk202 := witnessRule 48 28 32 1160132 1160324 32 971
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk203 := witnessRule 48 28 64 1160325 1160576 16 539
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk204 := witnessRule 48 27 0 1170000 1170132 32 857
  0xfffffff5 0x1a0d4cd823c0a8a1990886 (by decide +kernel)
private def pack_E6970Receipt48_chunk205 := witnessRule 48 27 32 1170133 1170384 32 947
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk206 := witnessRule 48 27 64 1170385 1170576 11 363
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk207 := witnessRule 48 26 0 1180000 1180133 32 824
  0xffffe5fd 0x666523e08acca87a10a119548f02bc0a8a1190986 (by decide +kernel)
private def pack_E6970Receipt48_chunk208 := witnessRule 48 26 32 1180134 1180387 32 923
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk209 := witnessRule 48 26 64 1180388 1180513 6 193
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk210 := witnessRule 48 25 0 1190000 1190134 32 794
  0xfffffbff 0x2332a9f04 (by decide +kernel)
private def pack_E6970Receipt48_chunk211 := witnessRule 48 25 32 1190135 1190450 32 904
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk212 := witnessRule 48 25 64 1190512 1190512 1 32
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk213 := witnessRule 48 24 0 1200000 1200135 32 763
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk214 := witnessRule 48 24 32 1200136 1200512 29 794
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk215 := witnessRule 48 23 0 1210000 1210136 32 733
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk216 := witnessRule 48 23 32 1210192 1210449 24 633
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk217 := witnessRule 48 22 0 1220000 1220192 32 703
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk218 := witnessRule 48 22 32 1220193 1220448 20 507
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk219 := witnessRule 48 21 0 1230000 1230194 32 675
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk220 := witnessRule 48 21 32 1230195 1230448 16 391
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk221 := witnessRule 48 20 0 1240000 1240195 32 645
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk222 := witnessRule 48 20 32 1240196 1240385 12 281
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk223 := witnessRule 48 19 0 1250000 1250197 32 617
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk224 := witnessRule 48 19 32 1250256 1250384 8 181
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk225 := witnessRule 48 18 0 1260000 1260257 32 589
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk226 := witnessRule 48 18 32 1260258 1260384 5 109
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk227 := witnessRule 48 17 0 1270000 1270320 32 564
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk228 := witnessRule 48 17 32 1270321 1270321 1 21
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk229 := witnessRule 48 16 0 1280000 1280320 30 498
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk230 := witnessRule 48 15 0 1290000 1290320 27 420
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk231 := witnessRule 48 14 0 1300000 1300257 24 345
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk232 := witnessRule 48 13 0 1310000 1310256 21 279
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk233 := witnessRule 48 12 0 1320000 1320256 19 232
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk234 := witnessRule 48 11 0 1330000 1330193 16 177
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk235 := witnessRule 48 10 0 1340000 1340192 14 139
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk236 := witnessRule 48 9 0 1350000 1350192 12 107
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk237 := witnessRule 48 8 0 1360000 1360129 10 77
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk238 := witnessRule 48 7 0 1370000 1370128 8 53
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk239 := witnessRule 48 6 0 1380000 1380128 7 39
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk240 := witnessRule 48 5 0 1390000 1390065 5 22
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk241 := witnessRule 48 4 0 1400000 1400064 4 13
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk242 := witnessRule 48 3 0 1410000 1410064 3 7
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk243 := witnessRule 48 2 0 1420000 1420001 2 2
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk244 := witnessRule 48 1 0 1430000 1430000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt48_chunk245 := witnessRule 48 0 0 1440000 1440000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt48_chunks : List (Chunk 48) := [pack_E6970Receipt48_chunk0, pack_E6970Receipt48_chunk1, pack_E6970Receipt48_chunk2, pack_E6970Receipt48_chunk3, pack_E6970Receipt48_chunk4, pack_E6970Receipt48_chunk5, pack_E6970Receipt48_chunk6, pack_E6970Receipt48_chunk7, pack_E6970Receipt48_chunk8, pack_E6970Receipt48_chunk9, pack_E6970Receipt48_chunk10, pack_E6970Receipt48_chunk11, pack_E6970Receipt48_chunk12, pack_E6970Receipt48_chunk13, pack_E6970Receipt48_chunk14, pack_E6970Receipt48_chunk15, pack_E6970Receipt48_chunk16, pack_E6970Receipt48_chunk17, pack_E6970Receipt48_chunk18, pack_E6970Receipt48_chunk19, pack_E6970Receipt48_chunk20, pack_E6970Receipt48_chunk21, pack_E6970Receipt48_chunk22, pack_E6970Receipt48_chunk23, pack_E6970Receipt48_chunk24, pack_E6970Receipt48_chunk25, pack_E6970Receipt48_chunk26, pack_E6970Receipt48_chunk27, pack_E6970Receipt48_chunk28, pack_E6970Receipt48_chunk29, pack_E6970Receipt48_chunk30, pack_E6970Receipt48_chunk31, pack_E6970Receipt48_chunk32, pack_E6970Receipt48_chunk33, pack_E6970Receipt48_chunk34, pack_E6970Receipt48_chunk35, pack_E6970Receipt48_chunk36, pack_E6970Receipt48_chunk37, pack_E6970Receipt48_chunk38, pack_E6970Receipt48_chunk39, pack_E6970Receipt48_chunk40, pack_E6970Receipt48_chunk41, pack_E6970Receipt48_chunk42, pack_E6970Receipt48_chunk43, pack_E6970Receipt48_chunk44, pack_E6970Receipt48_chunk45, pack_E6970Receipt48_chunk46, pack_E6970Receipt48_chunk47, pack_E6970Receipt48_chunk48, pack_E6970Receipt48_chunk49, pack_E6970Receipt48_chunk50, pack_E6970Receipt48_chunk51, pack_E6970Receipt48_chunk52, pack_E6970Receipt48_chunk53, pack_E6970Receipt48_chunk54, pack_E6970Receipt48_chunk55, pack_E6970Receipt48_chunk56, pack_E6970Receipt48_chunk57, pack_E6970Receipt48_chunk58, pack_E6970Receipt48_chunk59, pack_E6970Receipt48_chunk60, pack_E6970Receipt48_chunk61, pack_E6970Receipt48_chunk62, pack_E6970Receipt48_chunk63, pack_E6970Receipt48_chunk64, pack_E6970Receipt48_chunk65, pack_E6970Receipt48_chunk66, pack_E6970Receipt48_chunk67, pack_E6970Receipt48_chunk68, pack_E6970Receipt48_chunk69, pack_E6970Receipt48_chunk70, pack_E6970Receipt48_chunk71, pack_E6970Receipt48_chunk72, pack_E6970Receipt48_chunk73, pack_E6970Receipt48_chunk74, pack_E6970Receipt48_chunk75, pack_E6970Receipt48_chunk76, pack_E6970Receipt48_chunk77, pack_E6970Receipt48_chunk78, pack_E6970Receipt48_chunk79, pack_E6970Receipt48_chunk80, pack_E6970Receipt48_chunk81, pack_E6970Receipt48_chunk82, pack_E6970Receipt48_chunk83, pack_E6970Receipt48_chunk84, pack_E6970Receipt48_chunk85, pack_E6970Receipt48_chunk86, pack_E6970Receipt48_chunk87, pack_E6970Receipt48_chunk88, pack_E6970Receipt48_chunk89, pack_E6970Receipt48_chunk90, pack_E6970Receipt48_chunk91, pack_E6970Receipt48_chunk92, pack_E6970Receipt48_chunk93, pack_E6970Receipt48_chunk94, pack_E6970Receipt48_chunk95, pack_E6970Receipt48_chunk96, pack_E6970Receipt48_chunk97, pack_E6970Receipt48_chunk98, pack_E6970Receipt48_chunk99, pack_E6970Receipt48_chunk100, pack_E6970Receipt48_chunk101, pack_E6970Receipt48_chunk102, pack_E6970Receipt48_chunk103, pack_E6970Receipt48_chunk104, pack_E6970Receipt48_chunk105, pack_E6970Receipt48_chunk106, pack_E6970Receipt48_chunk107, pack_E6970Receipt48_chunk108, pack_E6970Receipt48_chunk109, pack_E6970Receipt48_chunk110, pack_E6970Receipt48_chunk111, pack_E6970Receipt48_chunk112, pack_E6970Receipt48_chunk113, pack_E6970Receipt48_chunk114, pack_E6970Receipt48_chunk115, pack_E6970Receipt48_chunk116, pack_E6970Receipt48_chunk117, pack_E6970Receipt48_chunk118, pack_E6970Receipt48_chunk119, pack_E6970Receipt48_chunk120, pack_E6970Receipt48_chunk121, pack_E6970Receipt48_chunk122, pack_E6970Receipt48_chunk123, pack_E6970Receipt48_chunk124, pack_E6970Receipt48_chunk125, pack_E6970Receipt48_chunk126, pack_E6970Receipt48_chunk127, pack_E6970Receipt48_chunk128, pack_E6970Receipt48_chunk129, pack_E6970Receipt48_chunk130, pack_E6970Receipt48_chunk131, pack_E6970Receipt48_chunk132, pack_E6970Receipt48_chunk133, pack_E6970Receipt48_chunk134, pack_E6970Receipt48_chunk135, pack_E6970Receipt48_chunk136, pack_E6970Receipt48_chunk137, pack_E6970Receipt48_chunk138, pack_E6970Receipt48_chunk139, pack_E6970Receipt48_chunk140, pack_E6970Receipt48_chunk141, pack_E6970Receipt48_chunk142, pack_E6970Receipt48_chunk143, pack_E6970Receipt48_chunk144, pack_E6970Receipt48_chunk145, pack_E6970Receipt48_chunk146, pack_E6970Receipt48_chunk147, pack_E6970Receipt48_chunk148, pack_E6970Receipt48_chunk149, pack_E6970Receipt48_chunk150, pack_E6970Receipt48_chunk151, pack_E6970Receipt48_chunk152, pack_E6970Receipt48_chunk153, pack_E6970Receipt48_chunk154, pack_E6970Receipt48_chunk155, pack_E6970Receipt48_chunk156, pack_E6970Receipt48_chunk157, pack_E6970Receipt48_chunk158, pack_E6970Receipt48_chunk159, pack_E6970Receipt48_chunk160, pack_E6970Receipt48_chunk161, pack_E6970Receipt48_chunk162, pack_E6970Receipt48_chunk163, pack_E6970Receipt48_chunk164, pack_E6970Receipt48_chunk165, pack_E6970Receipt48_chunk166, pack_E6970Receipt48_chunk167, pack_E6970Receipt48_chunk168, pack_E6970Receipt48_chunk169, pack_E6970Receipt48_chunk170, pack_E6970Receipt48_chunk171, pack_E6970Receipt48_chunk172, pack_E6970Receipt48_chunk173, pack_E6970Receipt48_chunk174, pack_E6970Receipt48_chunk175, pack_E6970Receipt48_chunk176, pack_E6970Receipt48_chunk177, pack_E6970Receipt48_chunk178, pack_E6970Receipt48_chunk179, pack_E6970Receipt48_chunk180, pack_E6970Receipt48_chunk181, pack_E6970Receipt48_chunk182, pack_E6970Receipt48_chunk183, pack_E6970Receipt48_chunk184, pack_E6970Receipt48_chunk185, pack_E6970Receipt48_chunk186, pack_E6970Receipt48_chunk187, pack_E6970Receipt48_chunk188, pack_E6970Receipt48_chunk189, pack_E6970Receipt48_chunk190, pack_E6970Receipt48_chunk191, pack_E6970Receipt48_chunk192, pack_E6970Receipt48_chunk193, pack_E6970Receipt48_chunk194, pack_E6970Receipt48_chunk195, pack_E6970Receipt48_chunk196, pack_E6970Receipt48_chunk197, pack_E6970Receipt48_chunk198, pack_E6970Receipt48_chunk199, pack_E6970Receipt48_chunk200, pack_E6970Receipt48_chunk201, pack_E6970Receipt48_chunk202, pack_E6970Receipt48_chunk203, pack_E6970Receipt48_chunk204, pack_E6970Receipt48_chunk205, pack_E6970Receipt48_chunk206, pack_E6970Receipt48_chunk207, pack_E6970Receipt48_chunk208, pack_E6970Receipt48_chunk209, pack_E6970Receipt48_chunk210, pack_E6970Receipt48_chunk211, pack_E6970Receipt48_chunk212, pack_E6970Receipt48_chunk213, pack_E6970Receipt48_chunk214, pack_E6970Receipt48_chunk215, pack_E6970Receipt48_chunk216, pack_E6970Receipt48_chunk217, pack_E6970Receipt48_chunk218, pack_E6970Receipt48_chunk219, pack_E6970Receipt48_chunk220, pack_E6970Receipt48_chunk221, pack_E6970Receipt48_chunk222, pack_E6970Receipt48_chunk223, pack_E6970Receipt48_chunk224, pack_E6970Receipt48_chunk225, pack_E6970Receipt48_chunk226, pack_E6970Receipt48_chunk227, pack_E6970Receipt48_chunk228, pack_E6970Receipt48_chunk229, pack_E6970Receipt48_chunk230, pack_E6970Receipt48_chunk231, pack_E6970Receipt48_chunk232, pack_E6970Receipt48_chunk233, pack_E6970Receipt48_chunk234, pack_E6970Receipt48_chunk235, pack_E6970Receipt48_chunk236, pack_E6970Receipt48_chunk237, pack_E6970Receipt48_chunk238, pack_E6970Receipt48_chunk239, pack_E6970Receipt48_chunk240, pack_E6970Receipt48_chunk241, pack_E6970Receipt48_chunk242, pack_E6970Receipt48_chunk243, pack_E6970Receipt48_chunk244, pack_E6970Receipt48_chunk245]
def rows48 := rowsFrom pack_E6970Receipt48_chunks
theorem good48 : ∀ r ∈ rows48, good 48 r = true := rowsFrom_good pack_E6970Receipt48_chunks
theorem sorted48 : rows48.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt48_chunks 0 (by decide +kernel)).1
theorem mass48 (i : Fin 61) :
    bandCount 48 (i.val : ℤ) 60 16 ≤ (rows48.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt48_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 48 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt48_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total48 : (rows48.map (price 48)).sum = 415176 :=
  (total_eq pack_E6970Receipt48_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt48

section Pack_E6970Receipt49

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt49_chunk0 := witnessA6966Final 49 60 0 870011 870084 32 3744
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk1 := witnessA6966Final 49 60 32 870085 870199 32 3582
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk2 := witnessA6966Final 49 60 64 870200 870272 32 3660
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk3 := witnessA6966Final 49 60 96 870273 870385 32 3508
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk4 := witnessA6966Final 49 60 128 870386 870459 32 3552
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk5 := witnessA6966Final 49 60 160 870460 870580 32 3338
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk6 := witnessA6966Final 49 60 192 870581 870707 32 3208
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk7 := witnessA6966Final 49 60 224 870708 870840 32 3030
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk8 := witnessA6966Final 49 60 256 870841 871030 27 2368
  0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk9 := witnessRule 49 59 0 880010 880083 32 3566
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk10 := witnessRule 49 59 32 880084 880197 32 3372
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk11 := witnessRule 49 59 64 880198 880269 32 3482
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk12 := witnessRule 49 59 96 880270 880341 32 3282
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk13 := witnessRule 49 59 128 880342 880457 32 3350
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk14 := witnessRule 49 59 160 880458 880579 32 3102
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk15 := witnessRule 49 59 192 880580 880707 32 2984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk16 := witnessRule 49 59 224 880708 880841 32 2789
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk17 := witnessRule 49 59 256 880842 881029 24 1971
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk18 := witnessRule 49 58 0 890009 890081 32 3388
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk19 := witnessRule 49 58 32 890082 890154 32 3136
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk20 := witnessRule 49 58 64 890195 890266 32 3364
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk21 := witnessRule 49 58 96 890267 890338 32 3092
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk22 := witnessRule 49 58 128 890339 890455 32 3083
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk23 := witnessRule 49 58 160 890456 890578 32 2883
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk24 := witnessRule 49 58 192 890579 890707 32 2782
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk25 := witnessRule 49 58 224 890708 890896 32 2604
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk26 := witnessRule 49 58 256 890897 891029 21 1640
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk27 := witnessRule 49 57 0 900008 900080 32 3238
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk28 := witnessRule 49 57 32 900081 900152 32 2976
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk29 := witnessRule 49 57 64 900153 900263 32 3180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk30 := witnessRule 49 57 96 900264 900336 32 2920
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk31 := witnessRule 49 57 128 900337 900454 32 2863
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk32 := witnessRule 49 57 160 900455 900578 32 2700
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk33 := witnessRule 49 57 192 900579 900708 32 2599
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk34 := witnessRule 49 57 224 900709 900898 32 2469
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk35 := witnessRule 49 57 256 900899 901028 17 1282
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk36 := witnessRule 49 56 0 910007 910078 32 3100
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk37 := witnessRule 49 56 32 910079 910150 32 2858
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk38 := witnessRule 49 56 64 910151 910261 32 2992
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk39 := witnessRule 49 56 96 910262 910334 32 2751
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk40 := witnessRule 49 56 128 910335 910453 32 2672
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk41 := witnessRule 49 56 160 910454 910578 32 2545
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk42 := witnessRule 49 56 192 910579 910709 32 2459
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk43 := witnessRule 49 56 224 910710 910901 32 2373
  0xbfffffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt49_chunk44 := witnessRule 49 56 256 910902 911028 13 951
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk45 := witnessRule 49 55 0 920006 920077 32 3000
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk46 := witnessRule 49 55 32 920078 920148 32 2751
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk47 := witnessRule 49 55 64 920149 920259 32 2834
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk48 := witnessRule 49 55 96 920260 920333 32 2607
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk49 := witnessRule 49 55 128 920334 920453 32 2514
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk50 := witnessRule 49 55 160 920454 920579 32 2422
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk51 := witnessRule 49 55 192 920580 920711 32 2349
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk52 := witnessRule 49 55 224 920712 920961 32 2291
  0xfbf7ffff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt49_chunk53 := witnessRule 49 55 256 920962 921027 8 568
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk54 := witnessRule 49 54 0 930005 930075 32 2916
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk55 := witnessRule 49 54 32 930076 930146 32 2675
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk56 := witnessRule 49 54 64 930147 930258 32 2661
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk57 := witnessRule 49 54 96 930259 930332 32 2470
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk58 := witnessRule 49 54 128 930333 930453 32 2390
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk59 := witnessRule 49 54 160 930454 930580 32 2320
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk60 := witnessRule 49 54 192 930581 930713 32 2254
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk61 := witnessRule 49 54 224 930714 931024 32 2217
  0xffdf3f6f 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt49_chunk62 := witnessRule 49 54 256 931025 931027 3 210
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk63 := witnessRule 49 53 0 940004 940074 32 2867
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk64 := witnessRule 49 53 32 940075 940144 32 2607
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk65 := witnessRule 49 53 64 940145 940257 32 2509
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk66 := witnessRule 49 53 96 940258 940332 32 2368
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk67 := witnessRule 49 53 128 940333 940454 32 2288
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk68 := witnessRule 49 53 160 940455 940582 32 2223
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk69 := witnessRule 49 53 192 940583 940769 32 2173
  0xfb7fffff 0x5cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt49_chunk70 := witnessRule 49 53 224 940770 941026 29 1951
  0x1ffef9f2 0x5d8d0b8b29b27164362e4c86c9c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt49_chunk71 := witnessRule 49 52 0 950003 950072 32 2820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk72 := witnessRule 49 52 32 950073 950143 32 2488
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk73 := witnessRule 49 52 64 950144 950257 32 2384
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk74 := witnessRule 49 52 96 950258 950332 32 2259
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk75 := witnessRule 49 52 128 950333 950455 32 2191
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk76 := witnessRule 49 52 160 950456 950584 32 2134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk77 := witnessRule 49 52 192 950585 950773 32 2099
  0x8793edbf 0x2e4ca6c9c990d9b8b19884375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt49_chunk78 := witnessRule 49 52 224 950774 951026 23 1507
  0x7ffbcf 0x2ee685c598d938b29b (by decide +kernel)
private def pack_E6970Receipt49_chunk79 := witnessRule 49 51 0 960002 960071 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk80 := witnessRule 49 51 32 960072 960142 32 2372
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk81 := witnessRule 49 51 64 960143 960257 32 2267
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk82 := witnessRule 49 51 96 960258 960333 32 2161
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk83 := witnessRule 49 51 128 960334 960457 32 2098
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk84 := witnessRule 49 51 160 960458 960587 32 2052
  0xdb7fffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt49_chunk85 := witnessRule 49 51 192 960588 960833 32 2032
  0x7c3c1e4b 0x2e2ce6c5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt49_chunk86 := witnessRule 49 51 224 960834 961025 16 1025
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk87 := witnessRule 49 50 0 970001 970070 32 2682
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk88 := witnessRule 49 50 32 970071 970142 32 2268
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk89 := witnessRule 49 50 64 970143 970258 32 2168
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk90 := witnessRule 49 50 96 970259 970334 32 2058
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk91 := witnessRule 49 50 128 970335 970459 32 2013
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk92 := witnessRule 49 50 160 970460 970642 32 1984
  0x1c93db6f 0x239321b571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt49_chunk93 := witnessRule 49 50 192 970643 970896 32 1967
  0xfff1e0f0 0x17267364e2cc62109e0d0b9b31b27365366e4c86210dc598da3a988317465364e8c86cdcd8cc421b9329b (by decide +kernel)
private def pack_E6970Receipt49_chunk94 := witnessRule 49 50 224 970897 971025 9 570
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk95 := witnessRule 49 49 0 980000 980070 32 2601
  0xfffff3ff 0x21ccd4b8a2 (by decide +kernel)
private def pack_E6970Receipt49_chunk96 := witnessRule 49 49 32 980071 980142 32 2160
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk97 := witnessRule 49 49 64 980143 980259 32 2071
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk98 := witnessRule 49 49 96 980260 980336 32 1966
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk99 := witnessRule 49 49 128 980337 980462 32 1937
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt49_chunk100 := witnessRule 49 49 160 980512 980646 32 1918
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt49_chunk101 := witnessRule 49 49 192 980647 980962 32 1927
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt49_chunk102 := witnessRule 49 49 224 981024 981024 1 63
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk103 := witnessRule 49 48 0 990000 990070 32 2453
  0xffff57ff 0xae8c66d9c990dbba9a (by decide +kernel)
private def pack_E6970Receipt49_chunk104 := witnessRule 49 48 32 990071 990143 32 2063
  0xfd7fffd5 0x3b9319b87434ce6c66ddc590dcb8a09b (by decide +kernel)
private def pack_E6970Receipt49_chunk105 := witnessRule 49 48 64 990144 990261 32 1984
  0xcfffebff 0x973354e28a1c58cdd38a2 (by decide +kernel)
private def pack_E6970Receipt49_chunk106 := witnessRule 49 48 96 990262 990385 32 1886
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt49_chunk107 := witnessRule 49 48 128 990386 990515 32 1869
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt49_chunk108 := witnessRule 49 48 160 990516 990705 32 1847
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt49_chunk109 := witnessRule 49 48 192 990706 991024 25 1476
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk110 := witnessRule 49 47 0 1000000 1000071 32 2323
  0xfff551ff 0x4f0c66cdd990da3a329b7736151090e2c2a262161c54cdcb922 (by decide +kernel)
private def pack_E6970Receipt49_chunk111 := witnessRule 49 47 32 1000072 1000144 32 1967
  0xeaaffeaa 0x11d98cdaba321b67265372e2c2a2129c491bbb19b4756436ae6ca6e1c9854424b8a89884 (by decide +kernel)
private def pack_E6970Receipt49_chunk112 := witnessRule 49 47 64 1000145 1000263 32 1902
  0x57ffaa7f 0x6746336ee4c86e1d4d2bab19b6736436ee2ca6e9c5441d3892 (by decide +kernel)
private def pack_E6970Receipt49_chunk113 := witnessRule 49 47 96 1000264 1000388 32 1817
  0x476da3ff 0xce8c66ddc990dc38b19884875342f2c66cddd8cdabab19b77363370e2c86e5ccc41d38a09b (by decide +kernel)
private def pack_E6970Receipt49_chunk114 := witnessRule 49 47 128 1000389 1000519 32 1795
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt49_chunk115 := witnessRule 49 47 160 1000520 1000711 32 1792
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt49_chunk116 := witnessRule 49 47 192 1000768 1000961 16 931
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk117 := witnessRule 49 46 0 1010000 1010071 32 2194
  0x3f5501ff 0x4b8a8a09c97141278c2aa990d0bc329b477615108aeac2a262155d1854ce339b0a918856726154390e4c4addc554dcb9289b (by decide +kernel)
private def pack_E6970Receipt49_chunk118 := witnessRule 49 46 32 1010072 1010145 32 1885
  0x5503eaa0 0x2f4c66c9e190d9bb329b675615108ee6c2a26215dc9854ce438b0a9188587154374e4aa5c5049db19a17964364eeca6d5d98544233a30a89885673615338ee4c2a46215dc58550e4b8b12b (by decide +kernel)
private def pack_E6970Receipt49_chunk119 := witnessRule 49 46 64 1010146 1010265 32 1827
  0x147d543f 0x8ecc86d5d58cc422ba329b8736151092e2c2a262165c54cdd392227963366eec86d1d594dbba30a8848726151310b0e2c2a6725c548c42538a8a3 (by decide +kernel)
private def pack_E6970Receipt49_chunk120 := witnessRule 49 46 96 1010266 1010391 32 1748
  0xe480ed 0x1bb329b4766436aeac662115d194db39b218846726636ee2ca6211ddcd0bcb21b27963366eec86d1dd8cdabab21b674633108ce6ca6ddc990c423b8b31b188716238312e262105e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt49_chunk121 := witnessRule 49 46 128 1010392 1010523 32 1727
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt49_chunk122 := witnessRule 49 46 160 1010576 1010773 32 1756
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt49_chunk123 := witnessRule 49 46 192 1010832 1010960 8 461
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk124 := witnessRule 49 45 0 1020000 1020072 32 2080
  0xfd0007f 0x21c58948e4b9289884a7151272e4485ed8544213cb0a898852786153386eec2a46214dd98550e2bb312b474615538ce8c4a271dcd894423b931291c8716251310b0e4a66e5c5491cb912 (by decide +kernel)
private def pack_E6970Receipt49_chunk125 := witnessRule 49 45 32 1020073 1020146 32 1798
  0xa801f500 0x2994d1bcb0a8844776151310a8ecc2a6715d58548c42aba30aa1c7746256ce4c2aa721c98944e4b8b1288497252374e2824ed8548d93d30a8843786151310a6eec2a6711d98548c42a3ab0aa1c6756256ae6c2aa71dcd8944e439312884 (by decide +kernel)
private def pack_E6970Receipt49_chunk126 := witnessRule 49 45 64 1020147 1020267 32 1753
  0x101c5007 0x4f0ca6cddd90c421bb331b6756151310ace8c2a671dcd8548c42bb930aa1c8716153310b0e2aa6c625c544e5b21a17a6331082f2ca6d1e1854422bb30a89885575615338ce8c2a462159cd8550e439b12b7716155392e2c4a2729c9441d38a093 (by decide +kernel)
private def pack_E6970Receipt49_chunk127 := witnessRule 49 45 96 1020268 1020394 32 1680
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1d990c4223ab31b574653108ae6ce6c619cd8ce0c3b9311885187716438310e662105e990d93cb19884 (by decide +kernel)
private def pack_E6970Receipt49_chunk128 := witnessRule 49 45 128 1020395 1020580 32 1674
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt49_chunk129 := witnessRule 49 45 160 1020581 1020960 32 1738
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk130 := witnessRule 49 44 0 1030000 1030072 32 1970
  0xf80007f 0x7716254392e2c6ae5c94504e53912c62556c2a4621298550d93d312b1786155386f0c4a2711dd8944223b31291c5756251310aae8c4a6719cd8948c42b39312a1c8726356ee4aa6e5cd44dd3912 (by decide +kernel)
private def pack_E6970Receipt49_chunk131 := witnessRule 49 44 32 1030073 1030147 32 1720
  0x40007000 0xd6151062f6c2a262145e9854ce13cb0a918852786154388f0c4acdd98554e2bb31289c675625108ce8c4a471dcd8944c42bb931299c8716252310b0e4a86e9cd553912c615131096c2a66c5e98548c428bcb0aa1c37962564eec2aa711dd8944e2bb312884575625238ce8c4a262159cd894ce3b931291885 (by decide +kernel)
private def pack_E6970Receipt49_chunk132 := witnessRule 49 44 64 1030192 1030269 32 1679
  0x28003 0xa66342f2ca62105e19cd9bc30a99c4776152310a8ecc2a8715d5854cc42aba30aa9c6736154310ace4c2ac7061dc98548e8c438b0a898861887153394e4822ed854cd93d30a898852796153386f0c2a46214ddd8550e23b30a99885475615538ceac4a271dd1894423b9b1291c8726251310b0e2c4a6725c948c4253928a3 (by decide +kernel)
private def pack_E6970Receipt49_chunk133 := witnessRule 49 44 96 1030270 1030397 32 1618
  0xf8038006 0x5e19cd93bb3188427668366eace6210dd1a4da39b418844726a36ae2d262115ecd0bd32188417966364f0ca62109dd9cd9bb3318843756836308eac870615d18cc428c2b9b29c1867264310a30ce2cc7061dd4c425b21883 (by decide +kernel)
private def pack_E6970Receipt49_chunk134 := witnessRule 49 44 128 1030448 1030584 32 1627
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt49_chunk135 := witnessRule 49 44 160 1030640 1030897 24 1282
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk136 := witnessRule 49 43 0 1040000 1040073 32 1873
  0x7c0007f 0x7736351390e4c6a2121c58d48e4b9a89884a7251278c4a26c5ed894420bd31291c2796251310a4f0c4a670ddd8948c429bb312a1c57663568e8c4aa719d18d44e3b9b1a8847726352390e2c6a262161cd4cdcb92923 (by decide +kernel)
private def pack_E6970Receipt49_chunk137 := witnessRule 49 43 32 1040074 1040193 32 1656
  0x40003800 0xa7241278c4a26ed854cc42530aa9b27a6251386f2c4a210de18948e23bb1289885476625338aeac4a462155d18950e3ba31ab6726255390e4c6a2725c58d4424b9a91ba71514129ac4aad8948d8bdb1289c27a6251084f2c4a470de18944c429bbb1299c4766252310a8eac4a8719d58d5ab9b12a9c (by decide +kernel)
private def pack_E6970Receipt49_chunk138 := witnessRule 49 43 64 1040194 1040271 32 1588
  0xc0008000 0x530aa9b17a6154384f2c2a662149e18554e1bbb0aa18853766156388eac2aa62151d1855ce0c2ba30a99d186736152310c30ce4c2a87461dc5854cc430c3b8aa9c2887131198c2a46212d8550d8bd30a998851796155384f0c2a862149dd8558e23bb1291c5766251310aaeac4a6719d18948c42b39b12a1c7726253310aee2c4aa70621c58944e8c4b92884 (by decide +kernel)
private def pack_E6970Receipt49_chunk139 := witnessRule 49 43 96 1040320 1040451 32 1568
  0xfc07200 0x5cdb4d9393618842716e366fa620c5d9a8d93ab498842746b366e6d46210dc9b0da38b5988447d354cc620e5a0d0bbb49b182776538306ecc8621460dd598e0c23a32988518473673830ae4cc6214615c5a0e0c33b9884 (by decide +kernel)
private def pack_E6970Receipt49_chunk140 := witnessRule 49 43 128 1040452 1040644 32 1587
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt49_chunk141 := witnessRule 49 43 160 1040645 1040896 16 843
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk142 := witnessRule 49 42 0 1050000 1050073 32 1777
  0x3c0003f 0x19cd8d4ce3b931a918857716354392e2c8ae5cd4504e538a113c63556c4a4621298950d93d31ab1786255386f0c6a2711dd8d44223b31a91c5756351310aae8c6a6719cd8d48c42b3931aa1c8726456ee6aa6e5d144dd38a913 (by decide +kernel)
private def pack_E6970Receipt49_chunk143 := witnessRule 49 42 32 1050074 1050194 32 1584
  0x20000c00 0xc4392918851897151411b8c4a40f18948d8bdb128988517a6253384f2c4a462149e18950e1bbb1299885376625538aecc6a2719d58d44233a31a91c7736351310aee4c6a6721c58d48c42c39aa1b18973574e2844f18944c425b1299b17a6252310a2f2c4a870de58d593bb12a9c477635138aecc6a2115d58d48e33a31a89885 (by decide +kernel)
private def pack_E6970Receipt49_chunk144 := witnessRule 49 42 64 1050195 1050321 32 1525
  0x30002000 0xc238b51c1857931096c2a8621298558d8bcb0aa98851786157384eec2ac62149d98560e0c1bb30aa1d184756153310c308e8c2aa74615cd8550c430c2b930ab1d186716155310c30ce2ae70e19ccddb1299ba615531092c2ae6c9e5894ce1bc312918853776254388ecc4a662151d58954e2ba312a188557362563830ce6c4a47461dc98944c430c3b8b1299d (by decide +kernel)
private def pack_E6970Receipt49_chunk145 := witnessRule 49 42 96 1050322 1050454 32 1505
  0xfbfe0ec0 0x2e2c801b1746d364e6d862109c9b8d9b8b6988437f352c2ae6c605dd9ce0c13b331885182756838306e8ce621460dcda4e0c239341885 (by decide +kernel)
private def pack_E6970Receipt49_chunk146 := witnessRule 49 42 128 1050455 1050706 32 1565
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk147 := witnessRule 49 42 160 1050707 1050896 9 470
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk148 := witnessRule 49 41 0 1060000 1060074 32 1688
  0x1e0003f 0x19d5915ab9b1aa9c7736451390e4c8a2121c59148e4ba289884a7351278c6a26c5ed8d4420bd31a91c2796351310a4f0c6a670ddd8d48c429bb31aa1c57664568e8c6aa719d19144e3b9b228847726452390e2c8a262161d14cdcb9a923 (by decide +kernel)
private def pack_E6970Receipt49_chunk149 := witnessRule 49 41 32 1060075 1060196 32 1514
  0x600 0x619c9894cc430c338b12a9d1877254310a50ee2a284769c904846631289904b625331094c4aa6c5e58950c428bc312b1c3786352388eec6a262151d98d4ce2bab1a91885574635438ce6c6a662159c98d54e0c3b931a89d1887163510a310e6a4729c94504a631a883b6352362f6c6a2709e98d44213cb1a91c3786351310a6eec6a6711d98d48c42a3ab1aa1c (by decide +kernel)
private def pack_E6970Receipt49_chunk150 := witnessRule 49 41 64 1060197 1060324 32 1459
  0x6000800 0xc13a349885182736b38306e4d4621460dc5b0e0c23d9884a6255372c2ae621218564d8c0bc30aa9d182776154310c304ecc2ac7460dd58554c430c1ba30ab9d184736156310c308e4c2b074e11c990e1c2b8b1988538575376c4a46412d8950d8bd312998851796255384f0c4a862149dd8958e1bb312a9885375625738308eac4a674615d18948c430c2b9b12a1d (by decide +kernel)
private def pack_E6970Receipt49_chunk151 := witnessRule 49 41 96 1060325 1060458 32 1456
  0xfffff1fe 0x1726400d938b7988427440d0c0bab51c (by decide +kernel)
private def pack_E6970Receipt49_chunk152 := witnessRule 49 41 128 1060512 1060832 32 1556
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk153 := witnessRule 49 41 160 1060833 1060833 1 52
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk154 := witnessRule 49 40 0 1070000 1070074 32 1598
  0x1e0003f 0x15d59148e33a32289885673645338ee4c8a46215dc59150e0c438b22c9745141398c8aad8d48c42531aa1b27a64562f0c6aa70de19144e23bb22884476645238aeac8a262155d1914ce339b22918856726454390e4caaddd154dcbaa89b (by decide +kernel)
private def pack_E6970Receipt49_chunk155 := witnessRule 49 40 32 1070075 1070197 32 1444
  0x300 0x611cd8958e8c2b9312a98861857162573a70ae2c2a674e19c548c4294438a10cc6254076c6a4621298d50d8bd31a99c2796352310a4f0c6a870ddd8d4cc429bb31aa9c4756354310a8e8c6ac70615d18d48e8c339b1a898861867263533a30ee2c6a4621861dcd50e14439288cc635131096c6a66c5e98d48c428bcb1aa1c2786353310a4eec6aa711dd9144e2bb322884 (by decide +kernel)
private def pack_E6970Receipt49_chunk156 := witnessRule 49 40 64 1070198 1070326 32 1396
  0xe1810200 0xc0b9b69c182726c310a304e2dc7060df4c425312a1904962563108312c2aa6214621855ce0c0bbb0ab18861817661583a304e8c2b274e09d194e1c1b9b21885383726638708e2ca6214e11dcddb1299904a625531092c4ae6c5e18958c428bbb12c1c1827762543a306ecc4a6621860dd58954e8c23a312a1886 (by decide +kernel)
private def pack_E6970Receipt49_chunk157 := witnessRule 49 40 96 1070327 1070515 32 1424
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt49_chunk158 := witnessRule 49 40 128 1070516 1070832 26 1244
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk159 := witnessRule 49 39 0 1080000 1080075 32 1513
  0x70001f 0x4766452310a8eac8a8715d1914cc42ab9b22a9c1867364513a30ee4c8a21461dc59148e8c43a2898851897351298c8a26c5ed914420bd32291c2796451310a4f0c8a670ddd9148c429bb322a1c57665568e8c8aa719d19544e3b9b2a8847726552390e2caa262161d54cdcba2923 (by decide +kernel)
private def pack_E6970Receipt49_chunk160 := witnessRule 49 39 32 1080076 1080199 32 1375
  0x80 0x304eac4ae7460dd18958c430c1b9b12c1d3837361543a708e4c2a66218e11c58554e9c2b8aa18853867142311b6c6a26612d8d4cc42531aa9b1796354310a2f0c6ac709dd8d54c4293b31ab9c1837663533a308eac6a46218611d18d50e8c2b9b1a998861857263553a30ce2c6a86218619cd58e1c339291c189715141211d8c6a60ed9148dd31aa188496356364f2c8a470de19144c429bbb2299c (by decide +kernel)
private def pack_E6970Receipt49_chunk161 := witnessRule 49 39 64 1080200 1080329 32 1338
  0xff756080 0x605c5900392c4aa66106218558c828c330ad1c381746738704e6cc6214e09c9a0e1c1b8b3988538379376c4a4681298d50c424b1ab1b189625538302f0c4a86218605dd8958e8c13b312a9886 (by decide +kernel)
private def pack_E6970Receipt49_chunk162 := witnessRule 49 39 96 1080330 1080519 32 1400
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk163 := witnessRule 49 39 128 1080576 1080832 19 897
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk164 := witnessRule 49 38 0 1090000 1090075 32 1429
  0x70001f 0x3766454310a6eac8ac70611d59148e8c2ba322898861857364533a30ce4c8a46218619c59150e8c3ba2998852877351413b8c8a40ed9148c425322a1b1796453310a2f0c8aa70de19544e23bb2a884476655238aeacaa262155d1954ce339b2a9188567265543830ee4cab1dd554d8c43aa89c (by decide +kernel)
private def pack_E6970Receipt49_chunk165 := witnessRule 49 38 32 1090076 1090200 32 1308
  0x40 0x302ecc4ae6218605d58964e9c0bab0aa9d382746154310c704e6c2ac74e0dc98554c431c1b8b0ab9d3847156310a908e28872d8d541db1a91984a6454372c6ac621218d60d8c0bc31aa1d182776353310c304ecc6aa7460dd58d50c430c1ba31ab1d184736355310c308e4c6ae74e11c9894ce9c2b8b129188638572543870ee2a432d9144c825b2299b17a6452310a2f2c8a8709e1914cc4293bb22a9c (by decide +kernel)
private def pack_E6970Receipt49_chunk166 := witnessRule 49 38 64 1090201 1090331 32 1295
  0xfffffe20 0x381726a38704e2d26214e09ecdd31a99984963553208312c4a864146218958c428c3b12c1c (by decide +kernel)
private def pack_E6970Receipt49_chunk167 := witnessRule 49 38 96 1090384 1090579 32 1381
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk168 := witnessRule 49 38 128 1090580 1090769 12 557
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk169 := witnessRule 49 37 0 1100000 1100076 32 1347
  0x38007f 0x5dd915ce0c13bb2299d183766452310c306eac8a874611d1914cc430c239b22a9d185726454310c30ae2c8ac74e15c58d48e9c339a89885b655131094caa66c5e99548e13cb2a898852786553386eecaa46214dd99550e23ab2a9988547465553830ae8caa274619cd954428c33932a91d (by decide +kernel)
private def pack_E6970Receipt49_chunk170 := witnessRule 49 37 32 1100077 1100202 32 1244
  0x1000020 0x6218954cc28c3b12b99051866259310a70cc2aa6214e15855ce1c0ba30ab18863817361583a704e2c2b275609c594e2c1ba1884b635135094c8a6641259154c420c4b1aa1885188635638302eec6aa6218605d98d5ce8c13ab1ab18861827463583a704e8c4a874e0dcd894cc431c1b9312a9d384716254310c708e4ac71215c548c46db22a03b645232094c8a8621259158d8bc322a9885 (by decide +kernel)
private def pack_E6970Receipt49_chunk171 := witnessRule 49 37 64 1100203 1100386 32 1265
  0xffffffe8 0x3817d374c6a46a1258d50d020c4b1299a05 (by decide +kernel)
private def pack_E6970Receipt49_chunk172 := witnessRule 49 37 96 1100387 1100642 32 1365
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk173 := witnessRule 49 37 128 1100643 1100768 5 230
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk174 := witnessRule 49 36 0 1110000 1110076 32 1269
  0x78004f 0x302f0c8a66218605dd9154e8c13b322a18861827564563a306e8c8aa621860dcd915ce9c1b9b1a99d384726352310c708e2c6a876d954c1db2a91884a6554362f2caa662145e19554e13bb2aa1885276655638306eccaa474611d59544c430c23a32a99d185736552310c30ae4caa874619d554e1c33a289c (by decide +kernel)
private def pack_E6970Receipt49_chunk175 := witnessRule 49 36 32 1110077 1110203 32 1187
  0xaad00090 0x310c4a86a146198960cc29c2b0ab1905383615a38b02e2ce72d8d5c1d32291a04964543308312c6a666146218d54c828c3b1ab988518663593870cc4aa70e05d58950c431c0ba312b1d382736255310c704e4c4ae74e0dc960e2c1b8aa1cb645134094caa6621259554d8c4b22a1c (by decide +kernel)
private def pack_E6970Receipt49_chunk176 := witnessRule 49 36 64 1110204 1110389 32 1237
  0xfffffffe 0x4b1a99b04 (by decide +kernel)
private def pack_E6970Receipt49_chunk177 := witnessRule 49 36 96 1110390 1110768 31 1309
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk178 := witnessRule 49 35 0 1120000 1120077 32 1193
  0x3c002f 0x312c8a664146219154c428c3b22b9c181766456310c302eac8b074e05d58d50e9c13a31a998863827363553a706e4c6a86218e0dc58d58edb2a89984a6653372caaa62121955cd8c0bc32a99d182776552310c304eccaa87460dd5954cc430c1ba32aa9d184736554310c308e4caac74e11c99148e9c2ba299c (by decide +kernel)
private def pack_E6970Receipt49_chunk179 := witnessRule 49 35 32 1120078 1120205 32 1144
  0xfffc0028 0xa645136092c8a66a106258d48d428c431aa1a051876356330a30cc6b06414e198950c829c2b12b1885384625838702e6c4ae6218e05c98964eac0b930aa9d5827156396c8ac0e99548cc24b2aa1904 (by decide +kernel)
private def pack_E6970Receipt49_chunk180 := witnessRule 49 35 64 1120256 1120392 32 1213
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk181 := witnessRule 49 35 96 1120448 1120705 24 993
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk182 := witnessRule 49 34 0 1130000 1130077 32 1124
  0x1c001f 0x1896452340a310c8a8661461d9158c828c3322c18853866354310a70ac6ac70e05d18d54c431c0b9b1ab9d382726356310c704e2c6b075609c58950edb2aa83a665232092cca86210625954cc428c432aa9c181776554310c302eccaac74609d59554c430c13a32ab9d3827464533a706e6c8a46218e0dc99150e9c238b2299886 (by decide +kernel)
private def pack_E6970Receipt49_chunk183 := witnessRule 49 34 32 1130078 1130257 32 1107
  0xfffe000c 0x14c8b00e59148dc20c4b1a89b851886353360a30ec6aa6a146198d5cd029c331299a053856255330a708c4ae6414e0d8964c42ac1b0aa9885582615738b02e2c2ac621a99544d424b2a99a04 (by decide +kernel)
private def pack_E6970Receipt49_chunk184 := witnessRule 49 34 64 1130258 1130450 32 1189
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk185 := witnessRule 49 34 96 1130451 1130704 18 729
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk186 := witnessRule 49 33 0 1140000 1140078 32 1062
  0x6002f 0x4b2a91b041896451360a310c8a66a1461d9154d028c3322b99853866353330a70ac6aa6414e118d5cc429c1b1ac9c583625538b02e4c4a86219605c58958eac1392a9885a665134092cca666106259548cc28c432aa19051876556310a30ccab070e199150e1c0bab22998863817464553a704e6c8a86218e09c99158e9c1ba2b9c (by decide +kernel)
private def pack_E6970Receipt49_chunk187 := witnessRule 49 33 32 1140079 1140259 32 1076
  0xfffffaaa 0x6198d58d829c2b12a1a853836258330ab04c2ac641560568dd32ab83 (by decide +kernel)
private def pack_E6970Receipt49_chunk188 := witnessRule 49 33 64 1140260 1140454 32 1167
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk189 := witnessRule 49 33 96 1140512 1140704 12 479
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk190 := witnessRule 49 32 0 1150000 1150078 32 1009
  0x40020007 0x12caa270106219148dc28c3b22a1b051866456350a70cc6a46a14e158d50d029c231ab19853836358320ab06c4a864156098958c42ac0b12c1c5817257310ad02e2a28a76999581cb3291a841896551350a310caa6681461d9554cc28c332ab99053866453320a70ac8aa6214e11915ce1c0b9b22b18863817264583ab02e4c6a875609c58d4cc432c139aa9c (by decide +kernel)
private def pack_E6970Receipt49_chunk191 := witnessRule 49 32 32 1150128 1150261 32 1048
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk192 := witnessRule 49 32 64 1150262 1150515 32 1147
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk193 := witnessRule 49 32 96 1150516 1150641 6 235
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk194 := witnessRule 49 31 0 1160000 1160128 32 964
  0xda810007 0x219548e420c3322a9b853856353360a706c6ae681560d894cd02ac1312a99855816257320ab04b26211e0554c424b3289b84189655708310caa46c1461d9550d428c332ab1a053866452340a70ac8a86614e119158c829c1b22c18855836354310ab04c6ac71605c58d54c432c0b9ab9c (by decide +kernel)
private def pack_E6970Receipt49_chunk195 := witnessRule 49 31 32 1160129 1160263 32 1020
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk196 := witnessRule 49 31 64 1160264 1160640 32 1134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk197 := witnessRule 49 30 0 1170000 1170129 32 923
  0xffaafd03 0x706c6ac6c156098950d42ac12c198478145311870ac8a66a14e0d915ccc2ac1b1a999855826355320ab02c6ae621560d64dbc12a9b (by decide +kernel)
private def pack_E6970Receipt49_chunk198 := witnessRule 49 30 32 1170130 1170265 32 991
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk199 := witnessRule 49 30 64 1170320 1170640 27 933
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk200 := witnessRule 49 29 0 1180000 1180130 32 889
  0xf7ffa543 0x1d9548f02433289d041876552390a30ccaa87014e159148dc29c1b22b1a855826354340ab02c6ac661560d60c823c12a1904 (by decide +kernel)
private def pack_E6970Receipt49_chunk201 := witnessRule 49 29 32 1180131 1180322 32 966
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk202 := witnessRule 49 29 64 1180323 1180577 21 705
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk203 := witnessRule 49 28 0 1190000 1190131 32 855
  0xffffdbd1 0x1d9948ec20c2b2aa9c855826353360ab06ae6811e094cd023c0a8a2188886 (by decide +kernel)
private def pack_E6970Receipt49_chunk204 := witnessRule 49 28 32 1190132 1190324 32 939
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk205 := witnessRule 49 28 64 1190325 1190576 16 523
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk206 := witnessRule 49 27 0 1200000 1200132 32 823
  0xfffffff5 0x160d58d823c0a8a1988986 (by decide +kernel)
private def pack_E6970Receipt49_chunk207 := witnessRule 49 27 32 1200133 1200384 32 915
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk208 := witnessRule 49 27 64 1200385 1200576 11 352
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk209 := witnessRule 49 26 0 1210000 1210133 32 792
  0xffffe5ff 0xccca47c106199544f828c232aa9e05 (by decide +kernel)
private def pack_E6970Receipt49_chunk210 := witnessRule 49 26 32 1210134 1210387 32 891
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk211 := witnessRule 49 26 64 1210388 1210513 6 187
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk212 := witnessRule 49 25 0 1220000 1220134 32 762
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk213 := witnessRule 49 25 32 1220135 1220450 32 872
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk214 := witnessRule 49 25 64 1220512 1220512 1 31
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk215 := witnessRule 49 24 0 1230000 1230135 32 731
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk216 := witnessRule 49 24 32 1230136 1230512 29 765
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk217 := witnessRule 49 23 0 1240000 1240136 32 701
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk218 := witnessRule 49 23 32 1240192 1240449 24 609
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk219 := witnessRule 49 22 0 1250000 1250192 32 671
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk220 := witnessRule 49 22 32 1250193 1250448 20 487
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk221 := witnessRule 49 21 0 1260000 1260194 32 643
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk222 := witnessRule 49 21 32 1260195 1260448 16 375
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk223 := witnessRule 49 20 0 1270000 1270195 32 613
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk224 := witnessRule 49 20 32 1270196 1270385 12 269
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk225 := witnessRule 49 19 0 1280000 1280197 32 585
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk226 := witnessRule 49 19 32 1280256 1280384 8 173
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk227 := witnessRule 49 18 0 1290000 1290257 32 557
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk228 := witnessRule 49 18 32 1290258 1290384 5 104
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk229 := witnessRule 49 17 0 1300000 1300320 32 532
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk230 := witnessRule 49 17 32 1300321 1300321 1 20
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk231 := witnessRule 49 16 0 1310000 1310320 30 468
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk232 := witnessRule 49 15 0 1320000 1320320 27 393
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk233 := witnessRule 49 14 0 1330000 1330257 24 321
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk234 := witnessRule 49 13 0 1340000 1340256 21 258
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk235 := witnessRule 49 12 0 1350000 1350256 19 213
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk236 := witnessRule 49 11 0 1360000 1360193 16 161
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk237 := witnessRule 49 10 0 1370000 1370192 14 125
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk238 := witnessRule 49 9 0 1380000 1380192 12 95
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk239 := witnessRule 49 8 0 1390000 1390129 10 67
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk240 := witnessRule 49 7 0 1400000 1400128 8 45
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk241 := witnessRule 49 6 0 1410000 1410128 7 32
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk242 := witnessRule 49 5 0 1420000 1420065 5 17
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk243 := witnessRule 49 4 0 1430000 1430064 4 9
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk244 := witnessRule 49 3 0 1440000 1440064 3 4
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk245 := witnessRule 49 2 0 1450000 1450001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk246 := witnessRule 49 1 0 1460000 1460000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt49_chunk247 := witnessRule 49 0 0 1470000 1470000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt49_chunks : List (Chunk 49) := [pack_E6970Receipt49_chunk0, pack_E6970Receipt49_chunk1, pack_E6970Receipt49_chunk2, pack_E6970Receipt49_chunk3, pack_E6970Receipt49_chunk4, pack_E6970Receipt49_chunk5, pack_E6970Receipt49_chunk6, pack_E6970Receipt49_chunk7, pack_E6970Receipt49_chunk8, pack_E6970Receipt49_chunk9, pack_E6970Receipt49_chunk10, pack_E6970Receipt49_chunk11, pack_E6970Receipt49_chunk12, pack_E6970Receipt49_chunk13, pack_E6970Receipt49_chunk14, pack_E6970Receipt49_chunk15, pack_E6970Receipt49_chunk16, pack_E6970Receipt49_chunk17, pack_E6970Receipt49_chunk18, pack_E6970Receipt49_chunk19, pack_E6970Receipt49_chunk20, pack_E6970Receipt49_chunk21, pack_E6970Receipt49_chunk22, pack_E6970Receipt49_chunk23, pack_E6970Receipt49_chunk24, pack_E6970Receipt49_chunk25, pack_E6970Receipt49_chunk26, pack_E6970Receipt49_chunk27, pack_E6970Receipt49_chunk28, pack_E6970Receipt49_chunk29, pack_E6970Receipt49_chunk30, pack_E6970Receipt49_chunk31, pack_E6970Receipt49_chunk32, pack_E6970Receipt49_chunk33, pack_E6970Receipt49_chunk34, pack_E6970Receipt49_chunk35, pack_E6970Receipt49_chunk36, pack_E6970Receipt49_chunk37, pack_E6970Receipt49_chunk38, pack_E6970Receipt49_chunk39, pack_E6970Receipt49_chunk40, pack_E6970Receipt49_chunk41, pack_E6970Receipt49_chunk42, pack_E6970Receipt49_chunk43, pack_E6970Receipt49_chunk44, pack_E6970Receipt49_chunk45, pack_E6970Receipt49_chunk46, pack_E6970Receipt49_chunk47, pack_E6970Receipt49_chunk48, pack_E6970Receipt49_chunk49, pack_E6970Receipt49_chunk50, pack_E6970Receipt49_chunk51, pack_E6970Receipt49_chunk52, pack_E6970Receipt49_chunk53, pack_E6970Receipt49_chunk54, pack_E6970Receipt49_chunk55, pack_E6970Receipt49_chunk56, pack_E6970Receipt49_chunk57, pack_E6970Receipt49_chunk58, pack_E6970Receipt49_chunk59, pack_E6970Receipt49_chunk60, pack_E6970Receipt49_chunk61, pack_E6970Receipt49_chunk62, pack_E6970Receipt49_chunk63, pack_E6970Receipt49_chunk64, pack_E6970Receipt49_chunk65, pack_E6970Receipt49_chunk66, pack_E6970Receipt49_chunk67, pack_E6970Receipt49_chunk68, pack_E6970Receipt49_chunk69, pack_E6970Receipt49_chunk70, pack_E6970Receipt49_chunk71, pack_E6970Receipt49_chunk72, pack_E6970Receipt49_chunk73, pack_E6970Receipt49_chunk74, pack_E6970Receipt49_chunk75, pack_E6970Receipt49_chunk76, pack_E6970Receipt49_chunk77, pack_E6970Receipt49_chunk78, pack_E6970Receipt49_chunk79, pack_E6970Receipt49_chunk80, pack_E6970Receipt49_chunk81, pack_E6970Receipt49_chunk82, pack_E6970Receipt49_chunk83, pack_E6970Receipt49_chunk84, pack_E6970Receipt49_chunk85, pack_E6970Receipt49_chunk86, pack_E6970Receipt49_chunk87, pack_E6970Receipt49_chunk88, pack_E6970Receipt49_chunk89, pack_E6970Receipt49_chunk90, pack_E6970Receipt49_chunk91, pack_E6970Receipt49_chunk92, pack_E6970Receipt49_chunk93, pack_E6970Receipt49_chunk94, pack_E6970Receipt49_chunk95, pack_E6970Receipt49_chunk96, pack_E6970Receipt49_chunk97, pack_E6970Receipt49_chunk98, pack_E6970Receipt49_chunk99, pack_E6970Receipt49_chunk100, pack_E6970Receipt49_chunk101, pack_E6970Receipt49_chunk102, pack_E6970Receipt49_chunk103, pack_E6970Receipt49_chunk104, pack_E6970Receipt49_chunk105, pack_E6970Receipt49_chunk106, pack_E6970Receipt49_chunk107, pack_E6970Receipt49_chunk108, pack_E6970Receipt49_chunk109, pack_E6970Receipt49_chunk110, pack_E6970Receipt49_chunk111, pack_E6970Receipt49_chunk112, pack_E6970Receipt49_chunk113, pack_E6970Receipt49_chunk114, pack_E6970Receipt49_chunk115, pack_E6970Receipt49_chunk116, pack_E6970Receipt49_chunk117, pack_E6970Receipt49_chunk118, pack_E6970Receipt49_chunk119, pack_E6970Receipt49_chunk120, pack_E6970Receipt49_chunk121, pack_E6970Receipt49_chunk122, pack_E6970Receipt49_chunk123, pack_E6970Receipt49_chunk124, pack_E6970Receipt49_chunk125, pack_E6970Receipt49_chunk126, pack_E6970Receipt49_chunk127, pack_E6970Receipt49_chunk128, pack_E6970Receipt49_chunk129, pack_E6970Receipt49_chunk130, pack_E6970Receipt49_chunk131, pack_E6970Receipt49_chunk132, pack_E6970Receipt49_chunk133, pack_E6970Receipt49_chunk134, pack_E6970Receipt49_chunk135, pack_E6970Receipt49_chunk136, pack_E6970Receipt49_chunk137, pack_E6970Receipt49_chunk138, pack_E6970Receipt49_chunk139, pack_E6970Receipt49_chunk140, pack_E6970Receipt49_chunk141, pack_E6970Receipt49_chunk142, pack_E6970Receipt49_chunk143, pack_E6970Receipt49_chunk144, pack_E6970Receipt49_chunk145, pack_E6970Receipt49_chunk146, pack_E6970Receipt49_chunk147, pack_E6970Receipt49_chunk148, pack_E6970Receipt49_chunk149, pack_E6970Receipt49_chunk150, pack_E6970Receipt49_chunk151, pack_E6970Receipt49_chunk152, pack_E6970Receipt49_chunk153, pack_E6970Receipt49_chunk154, pack_E6970Receipt49_chunk155, pack_E6970Receipt49_chunk156, pack_E6970Receipt49_chunk157, pack_E6970Receipt49_chunk158, pack_E6970Receipt49_chunk159, pack_E6970Receipt49_chunk160, pack_E6970Receipt49_chunk161, pack_E6970Receipt49_chunk162, pack_E6970Receipt49_chunk163, pack_E6970Receipt49_chunk164, pack_E6970Receipt49_chunk165, pack_E6970Receipt49_chunk166, pack_E6970Receipt49_chunk167, pack_E6970Receipt49_chunk168, pack_E6970Receipt49_chunk169, pack_E6970Receipt49_chunk170, pack_E6970Receipt49_chunk171, pack_E6970Receipt49_chunk172, pack_E6970Receipt49_chunk173, pack_E6970Receipt49_chunk174, pack_E6970Receipt49_chunk175, pack_E6970Receipt49_chunk176, pack_E6970Receipt49_chunk177, pack_E6970Receipt49_chunk178, pack_E6970Receipt49_chunk179, pack_E6970Receipt49_chunk180, pack_E6970Receipt49_chunk181, pack_E6970Receipt49_chunk182, pack_E6970Receipt49_chunk183, pack_E6970Receipt49_chunk184, pack_E6970Receipt49_chunk185, pack_E6970Receipt49_chunk186, pack_E6970Receipt49_chunk187, pack_E6970Receipt49_chunk188, pack_E6970Receipt49_chunk189, pack_E6970Receipt49_chunk190, pack_E6970Receipt49_chunk191, pack_E6970Receipt49_chunk192, pack_E6970Receipt49_chunk193, pack_E6970Receipt49_chunk194, pack_E6970Receipt49_chunk195, pack_E6970Receipt49_chunk196, pack_E6970Receipt49_chunk197, pack_E6970Receipt49_chunk198, pack_E6970Receipt49_chunk199, pack_E6970Receipt49_chunk200, pack_E6970Receipt49_chunk201, pack_E6970Receipt49_chunk202, pack_E6970Receipt49_chunk203, pack_E6970Receipt49_chunk204, pack_E6970Receipt49_chunk205, pack_E6970Receipt49_chunk206, pack_E6970Receipt49_chunk207, pack_E6970Receipt49_chunk208, pack_E6970Receipt49_chunk209, pack_E6970Receipt49_chunk210, pack_E6970Receipt49_chunk211, pack_E6970Receipt49_chunk212, pack_E6970Receipt49_chunk213, pack_E6970Receipt49_chunk214, pack_E6970Receipt49_chunk215, pack_E6970Receipt49_chunk216, pack_E6970Receipt49_chunk217, pack_E6970Receipt49_chunk218, pack_E6970Receipt49_chunk219, pack_E6970Receipt49_chunk220, pack_E6970Receipt49_chunk221, pack_E6970Receipt49_chunk222, pack_E6970Receipt49_chunk223, pack_E6970Receipt49_chunk224, pack_E6970Receipt49_chunk225, pack_E6970Receipt49_chunk226, pack_E6970Receipt49_chunk227, pack_E6970Receipt49_chunk228, pack_E6970Receipt49_chunk229, pack_E6970Receipt49_chunk230, pack_E6970Receipt49_chunk231, pack_E6970Receipt49_chunk232, pack_E6970Receipt49_chunk233, pack_E6970Receipt49_chunk234, pack_E6970Receipt49_chunk235, pack_E6970Receipt49_chunk236, pack_E6970Receipt49_chunk237, pack_E6970Receipt49_chunk238, pack_E6970Receipt49_chunk239, pack_E6970Receipt49_chunk240, pack_E6970Receipt49_chunk241, pack_E6970Receipt49_chunk242, pack_E6970Receipt49_chunk243, pack_E6970Receipt49_chunk244, pack_E6970Receipt49_chunk245, pack_E6970Receipt49_chunk246, pack_E6970Receipt49_chunk247]
def rows49 := rowsFrom pack_E6970Receipt49_chunks
theorem good49 : ∀ r ∈ rows49, good 49 r = true := rowsFrom_good pack_E6970Receipt49_chunks
theorem sorted49 : rows49.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt49_chunks 0 (by decide +kernel)).1
theorem mass49 (i : Fin 61) :
    bandCount 49 (i.val : ℤ) 60 16 ≤ (rows49.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt49_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 49 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt49_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total49 : (rows49.map (price 49)).sum = 412314 :=
  (total_eq pack_E6970Receipt49_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt49

section Pack_E6970Receipt50

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt50_chunk0 := witnessA6966Final 50 60 0 900010 900082 32 3790
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk1 := witnessA6966Final 50 60 32 900083 900155 32 3548
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk2 := witnessA6966Final 50 60 64 900196 900267 32 3768
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk3 := witnessA6966Final 50 60 96 900268 900338 32 3562
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk4 := witnessA6966Final 50 60 128 900339 900453 32 3528
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk5 := witnessA6966Final 50 60 160 900454 900529 32 3336
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk6 := witnessA6966Final 50 60 192 900530 900653 32 3266
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk7 := witnessA6966Final 50 60 224 900654 900834 32 3082
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk8 := witnessA6966Final 50 60 256 900835 901029 32 2840
  0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk9 := witnessRule 50 60 288 901030 901030 1 79
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk10 := witnessRule 50 59 0 910009 910081 32 3612
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk11 := witnessRule 50 59 32 910082 910153 32 3366
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk12 := witnessRule 50 59 64 910154 910264 32 3542
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk13 := witnessRule 50 59 96 910265 910336 32 3374
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk14 := witnessRule 50 59 128 910337 910452 32 3272
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk15 := witnessRule 50 59 160 910453 910528 32 3112
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk16 := witnessRule 50 59 192 910529 910653 32 3018
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk17 := witnessRule 50 59 224 910654 910836 32 2858
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk18 := witnessRule 50 59 256 910837 911029 29 2367
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk19 := witnessRule 50 58 0 920008 920079 32 3430
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk20 := witnessRule 50 58 32 920080 920151 32 3210
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk21 := witnessRule 50 58 64 920152 920261 32 3328
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk22 := witnessRule 50 58 96 920262 920333 32 3186
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk23 := witnessRule 50 58 128 920334 920450 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk24 := witnessRule 50 58 160 920451 920527 32 2922
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk25 := witnessRule 50 58 192 920528 920653 32 2788
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk26 := witnessRule 50 58 224 920654 920837 32 2643
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk27 := witnessRule 50 58 256 920838 921029 26 2010
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk28 := witnessRule 50 57 0 930007 930078 32 3280
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk29 := witnessRule 50 57 32 930079 930149 32 3042
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk30 := witnessRule 50 57 64 930150 930259 32 3099
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk31 := witnessRule 50 57 96 930260 930332 32 2996
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk32 := witnessRule 50 57 128 930333 930450 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk33 := witnessRule 50 57 160 930451 930527 32 2707
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk34 := witnessRule 50 57 192 930528 930704 32 2609
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk35 := witnessRule 50 57 224 930705 930840 32 2463
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk36 := witnessRule 50 57 256 930841 931028 21 1569
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk37 := witnessRule 50 56 0 940006 940076 32 3131
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk38 := witnessRule 50 56 32 940077 940147 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk39 := witnessRule 50 56 64 940148 940257 32 2907
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk40 := witnessRule 50 56 96 940258 940330 32 2818
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk41 := witnessRule 50 56 128 940331 940449 32 2619
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk42 := witnessRule 50 56 160 940450 940527 32 2548
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk43 := witnessRule 50 56 192 940528 940705 32 2456
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk44 := witnessRule 50 56 224 940706 940897 32 2354
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk45 := witnessRule 50 56 256 940898 941028 17 1227
  0x1fffb 0xb99a (by decide +kernel)
private def pack_E6970Receipt50_chunk46 := witnessRule 50 55 0 950005 950075 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk47 := witnessRule 50 55 32 950076 950145 32 2783
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk48 := witnessRule 50 55 64 950146 950256 32 2706
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk49 := witnessRule 50 55 96 950257 950330 32 2648
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk50 := witnessRule 50 55 128 950331 950450 32 2480
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk51 := witnessRule 50 55 160 950451 950576 32 2399
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk52 := witnessRule 50 55 192 950577 950708 32 2335
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk53 := witnessRule 50 55 224 950709 950901 32 2261
  0xdfbfffff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt50_chunk54 := witnessRule 50 55 256 950902 951027 11 771
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk55 := witnessRule 50 54 0 960004 960073 32 2936
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk56 := witnessRule 50 54 32 960074 960143 32 2694
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk57 := witnessRule 50 54 64 960144 960214 32 2528
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk58 := witnessRule 50 54 96 960256 960329 32 2506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk59 := witnessRule 50 54 128 960330 960450 32 2353
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk60 := witnessRule 50 54 160 960451 960577 32 2297
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk61 := witnessRule 50 54 192 960578 960710 32 2234
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk62 := witnessRule 50 54 224 960711 960962 32 2185
  0xfef9fb7f 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt50_chunk63 := witnessRule 50 54 256 960963 961027 6 411
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk64 := witnessRule 50 53 0 970003 970072 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk65 := witnessRule 50 53 32 970073 970142 32 2552
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk66 := witnessRule 50 53 64 970143 970214 32 2403
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk67 := witnessRule 50 53 96 970256 970330 32 2368
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk68 := witnessRule 50 53 128 970331 970452 32 2256
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk69 := witnessRule 50 53 160 970453 970580 32 2195
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk70 := witnessRule 50 53 192 970581 970714 32 2142
  0xedffffff 0x5cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt50_chunk71 := witnessRule 50 53 224 970768 971026 31 2057
  0x7ffbe7cb 0x5d8d0b8b29b27164362e4c86c9c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt50_chunk72 := witnessRule 50 52 0 980002 980070 32 2828
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk73 := witnessRule 50 52 32 980071 980141 32 2439
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk74 := witnessRule 50 52 64 980142 980213 32 2291
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk75 := witnessRule 50 52 96 980256 980330 32 2253
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk76 := witnessRule 50 52 128 980331 980453 32 2159
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk77 := witnessRule 50 52 160 980454 980582 32 2106
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk78 := witnessRule 50 52 192 980583 980771 32 2069
  0x1e4fb6ff 0x9c990d9b8b19884375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt50_chunk79 := witnessRule 50 52 224 980772 981026 25 1612
  0x1ffef3e 0x177342e2cc6c9c594d8b9329b (by decide +kernel)
private def pack_E6970Receipt50_chunk80 := witnessRule 50 51 0 990001 990070 32 2733
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk81 := witnessRule 50 51 32 990071 990141 32 2314
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk82 := witnessRule 50 51 64 990142 990256 32 2198
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk83 := witnessRule 50 51 96 990257 990332 32 2134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk84 := witnessRule 50 51 128 990333 990456 32 2067
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk85 := witnessRule 50 51 160 990457 990586 32 2022
  0xb6ffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt50_chunk86 := witnessRule 50 51 192 990587 990832 32 1999
  0xf8783c97 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt50_chunk87 := witnessRule 50 51 224 990833 991025 17 1071
  0x1fffe 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt50_chunk88 := witnessRule 50 50 0 1000000 1000069 32 2633
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk89 := witnessRule 50 50 32 1000070 1000141 32 2212
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk90 := witnessRule 50 50 64 1000142 1000257 32 2105
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk91 := witnessRule 50 50 96 1000258 1000333 32 2029
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk92 := witnessRule 50 50 128 1000334 1000458 32 1982
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk93 := witnessRule 50 50 160 1000459 1000641 32 1951
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt50_chunk94 := witnessRule 50 50 192 1000642 1000837 32 1935
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt50_chunk95 := witnessRule 50 50 224 1000896 1001025 10 622
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk96 := witnessRule 50 49 0 1010000 1010070 32 2491
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk97 := witnessRule 50 49 32 1010071 1010142 32 2095
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk98 := witnessRule 50 49 64 1010143 1010259 32 2013
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk99 := witnessRule 50 49 96 1010260 1010336 32 1931
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk100 := witnessRule 50 49 128 1010337 1010462 32 1905
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt50_chunk101 := witnessRule 50 49 160 1010512 1010646 32 1886
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt50_chunk102 := witnessRule 50 49 192 1010647 1010962 32 1895
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt50_chunk103 := witnessRule 50 49 224 1011024 1011024 1 62
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk104 := witnessRule 50 48 0 1020000 1020070 32 2347
  0xffffebff 0x1dc98cdc3a1a (by decide +kernel)
private def pack_E6970Receipt50_chunk105 := witnessRule 50 48 32 1020071 1020143 32 2000
  0xff9ffffa 0x973354e28a1c58cdd38a2 (by decide +kernel)
private def pack_E6970Receipt50_chunk106 := witnessRule 50 48 64 1020144 1020261 32 1929
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk107 := witnessRule 50 48 96 1020262 1020385 32 1851
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt50_chunk108 := witnessRule 50 48 128 1020386 1020515 32 1837
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt50_chunk109 := witnessRule 50 48 160 1020516 1020705 32 1815
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt50_chunk110 := witnessRule 50 48 192 1020706 1021024 25 1451
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk111 := witnessRule 50 47 0 1030000 1030071 32 2220
  0x3ffeaaff 0x14e2a20e9c4923b319b5746436ce4ca6e5c58544253892 (by decide +kernel)
private def pack_E6970Receipt50_chunk112 := witnessRule 50 47 32 1030072 1030144 32 1907
  0xfd5fffd5 0x19d18cdbb9321b87534aeac66d9cd90dbb8b29b (by decide +kernel)
private def pack_E6970Receipt50_chunk113 := witnessRule 50 47 64 1030145 1030263 32 1848
  0xebfff57f 0x439319b97434ee6c66e1c590dd38a09b (by decide +kernel)
private def pack_E6970Receipt50_chunk114 := witnessRule 50 47 96 1030264 1030388 32 1782
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt50_chunk115 := witnessRule 50 47 128 1030389 1030519 32 1763
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt50_chunk116 := witnessRule 50 47 160 1030520 1030711 32 1760
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt50_chunk117 := witnessRule 50 47 192 1030768 1030961 16 915
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk118 := witnessRule 50 46 0 1040000 1040071 32 2098
  0x3feaa07f 0x9715231094e2a28c5e98cd93c321b3766536ceac2a211dcd8544c42bb930a99c8716152310b0e2a86e9c954b8a093 (by decide +kernel)
private def pack_E6970Receipt50_chunk119 := witnessRule 50 46 32 1040072 1040145 32 1829
  0xeaa3fd54 0x1bc319b4766436ae8ca6e1cd854424b8b0a8988597153374e4889e58cd9bbb21b4756536ee8c2a2121c98544c42c38b0a99c (by decide +kernel)
private def pack_E6970Receipt50_chunk120 := witnessRule 50 46 64 1040146 1040265 32 1773
  0xa2bfaabf 0xaecc66d9d190dbb9b1988477265374e2c2a212dc4923bb19b5756436ce6ca6e5c985442538a89884 (by decide +kernel)
private def pack_E6970Receipt50_chunk121 := witnessRule 50 46 96 1040266 1040391 32 1713
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt50_chunk122 := witnessRule 50 46 128 1040392 1040523 32 1695
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt50_chunk123 := witnessRule 50 46 160 1040576 1040773 32 1724
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt50_chunk124 := witnessRule 50 46 192 1040832 1040960 8 453
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk125 := witnessRule 50 45 0 1050000 1050072 32 1990
  0xfea007f 0x7716155392e2c4a2729c9441d38a093a65346f2c2a2111dd8544c42a3b30a99c5756152310aae8c2a871dd1895b3930aa9c8726251392e2c4a2125c948dd38a093 (by decide +kernel)
private def pack_E6970Receipt50_chunk126 := witnessRule 50 45 32 1050073 1050146 32 1744
  0x5501eaa0 0xc63342f4c86c9e194dabbb0a8846756151310ace8c2a671dcd8548c42bb930aa1c97262570e2aa6e9c944deb0aab64342f2ca6d1e1854422bb30a89885575615338ce8c2a462159cd8550e439b12b (by decide +kernel)
private def pack_E6970Receipt50_chunk127 := witnessRule 50 45 64 1050147 1050267 32 1703
  0x820e8a03 0xde190da3bb198844766536aeac862115d198dc39b0a898858726153392e2c2a462165c550d8c5388b17b63364f2c86cde18cc421bbb29b676615108ee8c2a26215dcd854ce43930a918858716154394e2c4ae9c54504e538a093 (by decide +kernel)
private def pack_E6970Receipt50_chunk128 := witnessRule 50 45 96 1050268 1050394 32 1645
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt50_chunk129 := witnessRule 50 45 128 1050395 1050580 32 1642
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt50_chunk130 := witnessRule 50 45 160 1050581 1050960 32 1706
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk131 := witnessRule 50 44 0 1060000 1060072 32 1888
  0xfa0003f 0x8726251310b0e2c4a6725c948c4253928a3d6151062f6c2a262145e9854ce13cb0a918852786154388f0c4acdd98554e2bb31289c675625108ce8c4a471dcd8944c42bb931299c8716252310b0e4a86e9cd553912 (by decide +kernel)
private def pack_E6970Receipt50_chunk132 := witnessRule 50 44 32 1060073 1060147 32 1666
  0xa8003a00 0x630a91b27b6151086f2c2a26214de1854ce23bb0a91885476615438cecc4ad5d18554e3ba31289c8736251090e4c4a4725c58944c42cb9299ba7152474e4485f18544213d30a898852796153386f0c2a46214ddd8550e2bbb12b475615538ceac4a271dd1894423b9b1291c (by decide +kernel)
private def pack_E6970Receipt50_chunk133 := witnessRule 50 44 64 1060192 1060269 32 1632
  0x21000 0x5ed8cc420bd329b2796431084f0cc6cddd94c421bb339b576615338ceac2a462159d18550e3b9b0a998857726155390e2c2a862161c558d944391bc6331076ca685e990c420bcb31b4786151310a8eec2a6715d98548c42abab0aa1c6746153310ace6c2aa721cd8944e4b93128849716252394e4a26212dc5449d3912 (by decide +kernel)
private def pack_E6970Receipt50_chunk134 := witnessRule 50 44 96 1060270 1060397 32 1583
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt50_chunk135 := witnessRule 50 44 128 1060448 1060584 32 1595
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt50_chunk136 := witnessRule 50 44 160 1060640 1060897 24 1258
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk137 := witnessRule 50 43 0 1070000 1070073 32 1794
  0x3c0003f 0x19cd8950e439b1ab7716255392e2c6a2729cd441d392093c6251362f8c4ae98554d93d31289c3796251086f0c4a4711dd8944c42a3b31299c5756252310aae8c4a871dd18d5b39312a9c8726351392e2c6a2125cd48dd38a8a094 (by decide +kernel)
private def pack_E6970Receipt50_chunk138 := witnessRule 50 43 32 1070074 1070193 32 1601
  0x1800 0x625c54504edb912d615131098c2a66c5ed8548c428bd30aa1c2796153310a4f0c2aa711e18944e2bbb12884576625238ceac4a262159d1894ce3b9b12918857726254392e4c6ae1c954dd39a89bb7225ac4ab18548c425b0aa1b27b62562f2c2aa70de58944e23c312884477625238aecc4a262155d5894ce33a31291885 (by decide +kernel)
private def pack_E6970Receipt50_chunk139 := witnessRule 50 43 64 1070194 1070271 32 1548
  0xc000c000 0xb6531074ce685e598c420bc341b3786154388eec2a662151d98554e2bab0aa1885574615638ce6c2aa62159c9855ce14339319c2877162310a50ee86ed8550d8bdb0a99c27a6152310a4f2c2a870de1854cc429bbb0aa9c4766154310a8eac2ac719d58948e3ba312898857736253390e4c4a462161c58950e4b9299884 (by decide +kernel)
private def pack_E6970Receipt50_chunk140 := witnessRule 50 43 96 1070320 1070451 32 1534
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt50_chunk141 := witnessRule 50 43 128 1070452 1070644 32 1555
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt50_chunk142 := witnessRule 50 43 160 1070645 1070896 16 827
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk143 := witnessRule 50 42 0 1080000 1080073 32 1704
  0x1c0001f 0x774635108ee6c6a4721c98d44c42c38b1a99c9735231094e6a28e9c5089eb12883c6252362f6c4a262145e9894ce13cb12918852786254388f0c6acdd98954e2bb31a89c675635108ce8c6a471dcd8d44c42bb931a99c8716352310b0e6a86e9d15538a113 (by decide +kernel)
private def pack_E6970Receipt50_chunk144 := witnessRule 50 42 32 1080074 1080194 32 1531
  0x10000400 0xa1dc58548e94438a8988518a7121198c4a46ed8550c42530ab1b27a6252386f2c4a26214de1894ce23bb1291885476625438aeac4a662155d18954e3ba31a89c8736351090e4c6a4725c58d44c42cb9a99ba7252474e2844f58944d8be31288417b6252384f4c4a262149e5894ce1bc31291885377625438aeec6ad1d58954e33ab1a89c (by decide +kernel)
private def pack_E6970Receipt50_chunk145 := witnessRule 50 42 64 1080195 1080321 32 1486
  0x38002000 0x4716d36af8620e98558d8bd30aa9c2796154310a4f0c2ac70ddd8554c429bb30ab9c4756156310a8e8c2b070a11d190e142b9b1988528572653850ce2c86214a19d8de30a99884b6155362f4c2a862145e58558e13c30aa98852776157388eec4a6715d98948c42abab12a1c6746253310ace6c4aa71dc98950c42bb8b12b1c (by decide +kernel)
private def pack_E6970Receipt50_chunk146 := witnessRule 50 42 96 1080322 1080454 32 1473
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt50_chunk147 := witnessRule 50 42 128 1080455 1080706 32 1533
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk148 := witnessRule 50 42 160 1080707 1080896 9 461
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk149 := witnessRule 50 41 0 1090000 1090074 32 1617
  0xe0001f 0x575635338ce8c6a462159cd8d50e439b22b7716355392e2c8a2729d1441d38a92094c6351362f8c6ae98954d93d31a89c3796351086f0c6a4711dd8d44c42a3b31a99c5756352310aae8c6a871dd1915b3931aa9c8726451392e2c8a2125d148dd3928a094 (by decide +kernel)
private def pack_E6970Receipt50_chunk150 := witnessRule 50 41 32 1090075 1090196 32 1464
  0x200 0x50ae6c2a674a19c98548c4314338b0aa1d2877153310a510e282623718944c82631299b17b6252310a2f4c4a8709e5894cc4293c312a9c3776254310a6ecc4ac715d98d48e33ab1a89885674635338ee6c6a46215dc98d50e438b1a998858735536510e4a272dc5489eb12903c625231096c4a86c5e9894cc428bcb12a9c3796351388f0c6a2111dd8d48e2bb31a89885 (by decide +kernel)
private def pack_E6970Receipt50_chunk151 := witnessRule 50 41 64 1090197 1090324 32 1422
  0x6100c00 0x4e8d862109cdb8d9b93698843716f368fc620ed8554c42530ab9b1796156310a2f0c2b0709d98564e1413b329c2837564310a506e8cc70a11cd94c4294239339c2857166310a50af06ed8950dd30ab188496158364f2c4a870de1894cc429bbb12a9c4766254310a8eac4ac715d18954c42ab9b12b9c (by decide +kernel)
private def pack_E6970Receipt50_chunk152 := witnessRule 50 41 96 1090325 1090458 32 1424
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt50_chunk153 := witnessRule 50 41 128 1090512 1090832 32 1524
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk154 := witnessRule 50 41 160 1090833 1090833 1 51
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk155 := witnessRule 50 40 0 1100000 1100074 32 1530
  0xe0001f 0x475635538ceac8a271dd1914423b9b2291c8726451310b0e2c8a6725d148c420c4b9a8a4d6351078c6a46c5ed8d44c428bd31a99c2796352310a4f0c6a8711e19159bb31aa9c576645138ceac8a2119d19148e3b9b22898857726453390e2c8a462161d150dd3aaa (by decide +kernel)
private def pack_E6970Receipt50_chunk156 := witnessRule 50 40 32 1100075 1100197 32 1398
  0x2000100 0xa11d1854cc4314239b0aa9d285726154310c50ae2c2ac74a19c554c429c338a19cc625232096c4a8621298958d8bcb12a98851786257386f0c6a6711dd8d48c42a3b31aa1c5756353310aae8c6aa719cd8d50c42b3931ab1c2867262523a50ee2c4a26218a1dc94ce0c4b8a9208dc635131096c6a66c5ed8d48e13d31a898852796353386f0c6a46214ddd8d50e23b31a99885 (by decide +kernel)
private def pack_E6970Receipt50_chunk157 := witnessRule 50 40 64 1100198 1100326 32 1359
  0xe1d60200 0x1736400d9393798842716440d9ba00620e98558c82430ad1b281766738504eacc6214a09d1a0e141b9b39885283726938508e2d06214a11e8ddb1299904b6255362f4c4a862145e58958e13c312a98852776257386ecc4ac6214dd58960e141bab0aa1d (by decide +kernel)
private def pack_E6970Receipt50_chunk158 := witnessRule 50 40 96 1100327 1100515 32 1392
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt50_chunk159 := witnessRule 50 40 128 1100516 1100832 26 1218
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk160 := witnessRule 50 39 0 1110000 1110075 32 1448
  0x30000f 0x11dd9148e2bb32289885575645338ce8c8a462159cd9150e3b93229988577164553850ee2c6a274a21cd442539292094c6451376c6a6621298d54d93d32289c3796451086f0c8a4711dd9144c42a3b32299c5756452310aae8c8a871dd1955b39322a9c8726551392e2caa2125d548dd39a8a094 (by decide +kernel)
private def pack_E6970Receipt50_chunk161 := witnessRule 50 39 32 1110076 1110199 32 1331
  0x0 0x282766154310c504eac2ac74a0dd18554c43141b9b0ab9d284726156310c508e2c2b075211c590e242b99884c625134096c6a6621298d54d8bd31aa1c2796353310a4f0c6aa70ddd8d50c429bb31ab1c4756355310a8e8c6ae70a11d1894ce942b9b12918862857262543a50ce2c4a66218a19c954e1c3b8a8988d18a7221198c6a60f18d48c425b1aa1b17a6353310a2f2c6aa709e18d50c4293bb1ab1c (by decide +kernel)
private def pack_E6970Receipt50_chunk162 := witnessRule 50 39 64 1110200 1110329 32 1305
  0xff7fe0c0 0x5c593036502e8d470a09cda4c4294139359c283716a310a506f86ed8950c825312b188496258362f0c4ae62145dd8964e140bbb0aa9d (by decide +kernel)
private def pack_E6970Receipt50_chunk163 := witnessRule 50 39 96 1110330 1110519 32 1368
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk164 := witnessRule 50 39 128 1110576 1110832 19 878
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk165 := witnessRule 50 38 0 1120000 1120075 32 1367
  0x30000f 0xddd9150e23b32299885475645538ae8c8a862155cd9158e142b9b1a91d286726351310c50ce2c6a674a1dcd48c429443928a08dc6452078c8a46c5ed9144c428bd32299c2796452310a4f0c8a870ddd914cc429bb322a9c576655138ceacaa2119d19548e3b9b2a898857726553390e2caa462161d550d9443a2b (by decide +kernel)
private def pack_E6970Receipt50_chunk166 := witnessRule 50 38 32 1120076 1120200 32 1265
  0x10400000 0xa1d855ce140bb30ab18862817561583a504e6c2b275209cd94e241b9321885483716638908ea6212d8d48cc25b1aa1884a6356362f2c6aa62145e18d5ce13bb1ab1885276635838504ecc4a874a0dd5894cc43141ba312a9d284736254310c508e4c4ac74a15c58954c43142b92b9c485715338510e4843318d44cc25b2299ba635531092c6ae6c9e5914ce1bc32291885 (by decide +kernel)
private def pack_E6970Receipt50_chunk167 := witnessRule 50 38 64 1120201 1120331 32 1263
  0xfffffe20 0x281726d38504e2d86214a09f8ddb1299a04a625533092c4ae641218964c4214430aa9885 (by decide +kernel)
private def pack_E6970Receipt50_chunk168 := witnessRule 50 38 96 1120384 1120579 32 1349
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk169 := witnessRule 50 38 128 1120580 1120769 12 545
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk170 := witnessRule 50 37 0 1130000 1130076 32 1290
  0x18002f 0x13c322a18852776456386ecc8aa6214dd5915ce141bab1a99d284746352310c508e6c6a874a15c98d4cc43142b8b1aa9d2867354310a70ce4a2847719144c825b2299884a6455362f2c8a862145e19158e1bc32a91c4776551310a8eccaa6715d59548c42aba32aa1c6736553310ace4caaa70a19c99144e943ba291c (by decide +kernel)
private def pack_E6970Receipt50_chunk171 := witnessRule 50 37 32 1130077 1130202 32 1202
  0x56000000 0x86258330850ec2ac6414a158568e240b9b39c4827266310a904e2d07120ddcc425b1a89a84b635333094c6aa641258d5cc42431ac9b288625538502eec4a86218a05d98958e9413ab12a98862827462573a506e6c4ac6218a0dc98960ea41b930aa1d484716153310c908e2aa71219c4c86631aa83b645232096c8a86c5e9914cc428bcb22a9c (by decide +kernel)
private def pack_E6970Receipt50_chunk172 := witnessRule 50 37 64 1130203 1130386 32 1233
  0xffffffed 0x2817400dd312a1a84 (by decide +kernel)
private def pack_E6970Receipt50_chunk173 := witnessRule 50 37 96 1130387 1130642 32 1333
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk174 := witnessRule 50 37 128 1130643 1130768 5 225
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk175 := witnessRule 50 36 0 1140000 1140076 32 1214
  0x180007 0x2f0c8ac62145dd9160e140bbb1aa1d282766353310c504eac6aa74a0dd18d50c43141b9b1ab1d284726355310c508e2c6ae75211c5894cea42b9291885c6454076caa4621299550d8bd32a99c2796552310a4f0caa870ddd954cc429bb32aa9c4756554310a8e8caac70a11d19148e942b9b22898862857264533a50ce2c8a46218a19d150e1c3b9a88c (by decide +kernel)
private def pack_E6970Receipt50_chunk176 := witnessRule 50 36 32 1140077 1140203 32 1151
  0xffd80000 0x481716a396c6a46a1298d50d024b1ab1984863583208510c4a86414a1d8958c42943312c1c281756257310c502e8c4b275205d18554ea4139b0aa18864827261563a906e2c2aa621920dc55ce2c239988cb645134096c8a6641299154c424b22b9b (by decide +kernel)
private def pack_E6970Receipt50_chunk177 := witnessRule 50 36 64 1140204 1140389 32 1205
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk178 := witnessRule 50 36 96 1140390 1140768 31 1278
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk179 := witnessRule 50 35 0 1150000 1150077 32 1141
  0x1c0027 0x4b22b1904864583108510c6a86214a1d8d58e140bb31aa98862817563573a504e8c6ac6218a09cd8d60ea4139b12a1d483726253310c906e2c4aa76d9544cc25b2a99884a6555362f2caa862145e19558e13bb2aa9885276655738504ecc8a674a0dd59148c43141ba322a1d284736453310c508e4c8aa74a15d158e242b9a91c (by decide +kernel)
private def pack_E6970Receipt50_chunk180 := witnessRule 50 35 32 1150078 1150205 32 1109
  0xfffc0020 0x5b1a89b84a635336092c6aa6a1218d5cd0214431299a052876255330a50cc4ae6414a158964c42a42b0aa9885484615738902e6c2ac6219205c98560ea4138ac9c68275376c8ac0ed9148d025322a1984 (by decide +kernel)
private def pack_E6970Receipt50_chunk181 := witnessRule 50 35 64 1150256 1150392 32 1181
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk182 := witnessRule 50 35 96 1150448 1150705 24 969
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk183 := witnessRule 50 34 0 1160000 1160077 32 1075
  0x1c0017 0x4b22a9a04864573308510c6a66614a1d8d54c8294331ab988528563593890ac4aa71205d18950c43240b9b12b1d482726255310c904e2c4ae76d95541db2a91984a655432092caac621219560d944322a1c281776453310c502ecc8aa74a09d59150c431413a322b1d283736455310c506e4c8ae7520dc98d4cea4239aa1c (by decide +kernel)
private def pack_E6970Receipt50_chunk184 := witnessRule 50 34 32 1160078 1160257 32 1073
  0xffff5558 0x531a91c0486356360850ec4a86a14a158960cc2a4230ab1905482615a38d02ee6ed9144d82532299a84 (by decide +kernel)
private def pack_E6970Receipt50_chunk185 := witnessRule 50 34 64 1160258 1160450 32 1157
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk186 := witnessRule 50 34 96 1160451 1160704 18 711
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk187 := witnessRule 50 33 0 1170000 1170078 32 1018
  0x6000f 0x299148dc24b22a1b04864563508510c6a46a14a1d8d50d0294331ab19852856358320a90ac4a864152118958c42a41b12c1c481726257310c902e2c4b275a05c58554edb2a89a84a655334092caaa66121955cc82144322999052876455310a50cc8ae70a05d59158c43140ba322c1d4817463543a904e6c6a66219209c98d54ea41b8b1aa1886 (by decide +kernel)
private def pack_E6970Receipt50_chunk188 := witnessRule 50 33 32 1170079 1170259 32 1044
  0xfffffffe 0x5b22c03 (by decide +kernel)
private def pack_E6970Receipt50_chunk189 := witnessRule 50 33 64 1170260 1170454 32 1135
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk190 := witnessRule 50 33 96 1170512 1170704 12 467
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk191 := witnessRule 50 32 0 1180000 1180078 32 967
  0x40020007 0x14c8a2721219154dc214431a89b852876353360a50cc6aa6a14a158d5cd02a42b1299a054846255330a906c4ae64152098964c42b4130aa9885681615738d02e2ac6216d955c1d32a91b049655435090caac6810a219148d02943b22a19852866456320a50ac8b062152158d50c42a4231ab1c481736355310c902e4c6ae75209c58d58c4324139ac1c (by decide +kernel)
private def pack_E6970Receipt50_chunk192 := witnessRule 50 32 32 1180128 1180261 32 1016
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk193 := witnessRule 50 32 64 1180262 1180515 32 1115
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk194 := witnessRule 50 32 96 1180516 1180641 6 229
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk195 := witnessRule 50 31 0 1190000 1190128 32 924
  0xdaaa0003 0x4b2291d042876352380a50ac6ac6c152118950d42a41312c19856816156320af028c6e99544e024b2a99b84865553608510c8a26c14a1d914cd42943322a9a052856457330a90ac6a666152118d54c82a41b1ab9885482635938d04c4aa71a05c58950c43340b92b1c (by decide +kernel)
private def pack_E6970Receipt50_chunk196 := witnessRule 50 31 32 1190129 1190263 32 988
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk197 := witnessRule 50 31 64 1190264 1190640 32 1102
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk198 := witnessRule 50 30 0 1200000 1200129 32 887
  0xfffffd03 0x50ac8ac6a152118d50d02a41b1ab19854826358320ad04c4a86415a058958c42b412c1b (by decide +kernel)
private def pack_E6970Receipt50_chunk199 := witnessRule 50 30 32 1200130 1200265 32 959
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk200 := witnessRule 50 30 64 1200320 1200640 27 906
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk201 := witnessRule 50 29 0 1210000 1210130 32 854
  0xffffa541 0x259544ec23b2aa9c842876451390a50ac8aa6e152118d4cd82a4131ab9a056826253340ad02c4aa6615a095cc823c0a8a29885 (by decide +kernel)
private def pack_E6970Receipt50_chunk202 := witnessRule 50 29 32 1210131 1210322 32 934
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk203 := witnessRule 50 29 64 1210323 1210577 21 684
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk204 := witnessRule 50 28 0 1220000 1220131 32 821
  0xffffdbd5 0x432a91e0428664523a0a904c6ac6c15a058950d42bc0a8a21985 (by decide +kernel)
private def pack_E6970Receipt50_chunk205 := witnessRule 50 28 32 1220132 1220324 32 907
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk206 := witnessRule 50 28 64 1220325 1220576 16 507
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk207 := witnessRule 50 27 0 1230000 1230132 32 791
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk208 := witnessRule 50 27 32 1230133 1230384 32 883
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk209 := witnessRule 50 27 64 1230385 1230576 11 341
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk210 := witnessRule 50 26 0 1240000 1240133 32 760
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk211 := witnessRule 50 26 32 1240134 1240387 32 859
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk212 := witnessRule 50 26 64 1240388 1240513 6 181
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk213 := witnessRule 50 25 0 1250000 1250134 32 730
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk214 := witnessRule 50 25 32 1250135 1250450 32 840
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk215 := witnessRule 50 25 64 1250512 1250512 1 30
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk216 := witnessRule 50 24 0 1260000 1260135 32 699
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk217 := witnessRule 50 24 32 1260136 1260512 29 736
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk218 := witnessRule 50 23 0 1270000 1270136 32 669
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk219 := witnessRule 50 23 32 1270192 1270449 24 585
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk220 := witnessRule 50 22 0 1280000 1280192 32 639
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk221 := witnessRule 50 22 32 1280193 1280448 20 467
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk222 := witnessRule 50 21 0 1290000 1290194 32 611
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk223 := witnessRule 50 21 32 1290195 1290448 16 359
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk224 := witnessRule 50 20 0 1300000 1300195 32 581
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk225 := witnessRule 50 20 32 1300196 1300385 12 257
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk226 := witnessRule 50 19 0 1310000 1310197 32 553
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk227 := witnessRule 50 19 32 1310256 1310384 8 165
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk228 := witnessRule 50 18 0 1320000 1320257 32 525
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk229 := witnessRule 50 18 32 1320258 1320384 5 99
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk230 := witnessRule 50 17 0 1330000 1330320 32 500
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk231 := witnessRule 50 17 32 1330321 1330321 1 19
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk232 := witnessRule 50 16 0 1340000 1340320 30 438
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk233 := witnessRule 50 15 0 1350000 1350320 27 366
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk234 := witnessRule 50 14 0 1360000 1360257 24 297
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk235 := witnessRule 50 13 0 1370000 1370256 21 237
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk236 := witnessRule 50 12 0 1380000 1380256 19 194
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk237 := witnessRule 50 11 0 1390000 1390193 16 145
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk238 := witnessRule 50 10 0 1400000 1400192 14 111
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk239 := witnessRule 50 9 0 1410000 1410192 12 83
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk240 := witnessRule 50 8 0 1420000 1420129 10 57
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk241 := witnessRule 50 7 0 1430000 1430128 8 37
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk242 := witnessRule 50 6 0 1440000 1440128 7 25
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk243 := witnessRule 50 5 0 1450000 1450065 5 12
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk244 := witnessRule 50 4 0 1460000 1460064 4 5
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk245 := witnessRule 50 3 0 1470000 1470064 3 1
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk246 := witnessRule 50 2 0 1480000 1480001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk247 := witnessRule 50 1 0 1490000 1490000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt50_chunk248 := witnessRule 50 0 0 1500000 1500000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt50_chunks : List (Chunk 50) := [pack_E6970Receipt50_chunk0, pack_E6970Receipt50_chunk1, pack_E6970Receipt50_chunk2, pack_E6970Receipt50_chunk3, pack_E6970Receipt50_chunk4, pack_E6970Receipt50_chunk5, pack_E6970Receipt50_chunk6, pack_E6970Receipt50_chunk7, pack_E6970Receipt50_chunk8, pack_E6970Receipt50_chunk9, pack_E6970Receipt50_chunk10, pack_E6970Receipt50_chunk11, pack_E6970Receipt50_chunk12, pack_E6970Receipt50_chunk13, pack_E6970Receipt50_chunk14, pack_E6970Receipt50_chunk15, pack_E6970Receipt50_chunk16, pack_E6970Receipt50_chunk17, pack_E6970Receipt50_chunk18, pack_E6970Receipt50_chunk19, pack_E6970Receipt50_chunk20, pack_E6970Receipt50_chunk21, pack_E6970Receipt50_chunk22, pack_E6970Receipt50_chunk23, pack_E6970Receipt50_chunk24, pack_E6970Receipt50_chunk25, pack_E6970Receipt50_chunk26, pack_E6970Receipt50_chunk27, pack_E6970Receipt50_chunk28, pack_E6970Receipt50_chunk29, pack_E6970Receipt50_chunk30, pack_E6970Receipt50_chunk31, pack_E6970Receipt50_chunk32, pack_E6970Receipt50_chunk33, pack_E6970Receipt50_chunk34, pack_E6970Receipt50_chunk35, pack_E6970Receipt50_chunk36, pack_E6970Receipt50_chunk37, pack_E6970Receipt50_chunk38, pack_E6970Receipt50_chunk39, pack_E6970Receipt50_chunk40, pack_E6970Receipt50_chunk41, pack_E6970Receipt50_chunk42, pack_E6970Receipt50_chunk43, pack_E6970Receipt50_chunk44, pack_E6970Receipt50_chunk45, pack_E6970Receipt50_chunk46, pack_E6970Receipt50_chunk47, pack_E6970Receipt50_chunk48, pack_E6970Receipt50_chunk49, pack_E6970Receipt50_chunk50, pack_E6970Receipt50_chunk51, pack_E6970Receipt50_chunk52, pack_E6970Receipt50_chunk53, pack_E6970Receipt50_chunk54, pack_E6970Receipt50_chunk55, pack_E6970Receipt50_chunk56, pack_E6970Receipt50_chunk57, pack_E6970Receipt50_chunk58, pack_E6970Receipt50_chunk59, pack_E6970Receipt50_chunk60, pack_E6970Receipt50_chunk61, pack_E6970Receipt50_chunk62, pack_E6970Receipt50_chunk63, pack_E6970Receipt50_chunk64, pack_E6970Receipt50_chunk65, pack_E6970Receipt50_chunk66, pack_E6970Receipt50_chunk67, pack_E6970Receipt50_chunk68, pack_E6970Receipt50_chunk69, pack_E6970Receipt50_chunk70, pack_E6970Receipt50_chunk71, pack_E6970Receipt50_chunk72, pack_E6970Receipt50_chunk73, pack_E6970Receipt50_chunk74, pack_E6970Receipt50_chunk75, pack_E6970Receipt50_chunk76, pack_E6970Receipt50_chunk77, pack_E6970Receipt50_chunk78, pack_E6970Receipt50_chunk79, pack_E6970Receipt50_chunk80, pack_E6970Receipt50_chunk81, pack_E6970Receipt50_chunk82, pack_E6970Receipt50_chunk83, pack_E6970Receipt50_chunk84, pack_E6970Receipt50_chunk85, pack_E6970Receipt50_chunk86, pack_E6970Receipt50_chunk87, pack_E6970Receipt50_chunk88, pack_E6970Receipt50_chunk89, pack_E6970Receipt50_chunk90, pack_E6970Receipt50_chunk91, pack_E6970Receipt50_chunk92, pack_E6970Receipt50_chunk93, pack_E6970Receipt50_chunk94, pack_E6970Receipt50_chunk95, pack_E6970Receipt50_chunk96, pack_E6970Receipt50_chunk97, pack_E6970Receipt50_chunk98, pack_E6970Receipt50_chunk99, pack_E6970Receipt50_chunk100, pack_E6970Receipt50_chunk101, pack_E6970Receipt50_chunk102, pack_E6970Receipt50_chunk103, pack_E6970Receipt50_chunk104, pack_E6970Receipt50_chunk105, pack_E6970Receipt50_chunk106, pack_E6970Receipt50_chunk107, pack_E6970Receipt50_chunk108, pack_E6970Receipt50_chunk109, pack_E6970Receipt50_chunk110, pack_E6970Receipt50_chunk111, pack_E6970Receipt50_chunk112, pack_E6970Receipt50_chunk113, pack_E6970Receipt50_chunk114, pack_E6970Receipt50_chunk115, pack_E6970Receipt50_chunk116, pack_E6970Receipt50_chunk117, pack_E6970Receipt50_chunk118, pack_E6970Receipt50_chunk119, pack_E6970Receipt50_chunk120, pack_E6970Receipt50_chunk121, pack_E6970Receipt50_chunk122, pack_E6970Receipt50_chunk123, pack_E6970Receipt50_chunk124, pack_E6970Receipt50_chunk125, pack_E6970Receipt50_chunk126, pack_E6970Receipt50_chunk127, pack_E6970Receipt50_chunk128, pack_E6970Receipt50_chunk129, pack_E6970Receipt50_chunk130, pack_E6970Receipt50_chunk131, pack_E6970Receipt50_chunk132, pack_E6970Receipt50_chunk133, pack_E6970Receipt50_chunk134, pack_E6970Receipt50_chunk135, pack_E6970Receipt50_chunk136, pack_E6970Receipt50_chunk137, pack_E6970Receipt50_chunk138, pack_E6970Receipt50_chunk139, pack_E6970Receipt50_chunk140, pack_E6970Receipt50_chunk141, pack_E6970Receipt50_chunk142, pack_E6970Receipt50_chunk143, pack_E6970Receipt50_chunk144, pack_E6970Receipt50_chunk145, pack_E6970Receipt50_chunk146, pack_E6970Receipt50_chunk147, pack_E6970Receipt50_chunk148, pack_E6970Receipt50_chunk149, pack_E6970Receipt50_chunk150, pack_E6970Receipt50_chunk151, pack_E6970Receipt50_chunk152, pack_E6970Receipt50_chunk153, pack_E6970Receipt50_chunk154, pack_E6970Receipt50_chunk155, pack_E6970Receipt50_chunk156, pack_E6970Receipt50_chunk157, pack_E6970Receipt50_chunk158, pack_E6970Receipt50_chunk159, pack_E6970Receipt50_chunk160, pack_E6970Receipt50_chunk161, pack_E6970Receipt50_chunk162, pack_E6970Receipt50_chunk163, pack_E6970Receipt50_chunk164, pack_E6970Receipt50_chunk165, pack_E6970Receipt50_chunk166, pack_E6970Receipt50_chunk167, pack_E6970Receipt50_chunk168, pack_E6970Receipt50_chunk169, pack_E6970Receipt50_chunk170, pack_E6970Receipt50_chunk171, pack_E6970Receipt50_chunk172, pack_E6970Receipt50_chunk173, pack_E6970Receipt50_chunk174, pack_E6970Receipt50_chunk175, pack_E6970Receipt50_chunk176, pack_E6970Receipt50_chunk177, pack_E6970Receipt50_chunk178, pack_E6970Receipt50_chunk179, pack_E6970Receipt50_chunk180, pack_E6970Receipt50_chunk181, pack_E6970Receipt50_chunk182, pack_E6970Receipt50_chunk183, pack_E6970Receipt50_chunk184, pack_E6970Receipt50_chunk185, pack_E6970Receipt50_chunk186, pack_E6970Receipt50_chunk187, pack_E6970Receipt50_chunk188, pack_E6970Receipt50_chunk189, pack_E6970Receipt50_chunk190, pack_E6970Receipt50_chunk191, pack_E6970Receipt50_chunk192, pack_E6970Receipt50_chunk193, pack_E6970Receipt50_chunk194, pack_E6970Receipt50_chunk195, pack_E6970Receipt50_chunk196, pack_E6970Receipt50_chunk197, pack_E6970Receipt50_chunk198, pack_E6970Receipt50_chunk199, pack_E6970Receipt50_chunk200, pack_E6970Receipt50_chunk201, pack_E6970Receipt50_chunk202, pack_E6970Receipt50_chunk203, pack_E6970Receipt50_chunk204, pack_E6970Receipt50_chunk205, pack_E6970Receipt50_chunk206, pack_E6970Receipt50_chunk207, pack_E6970Receipt50_chunk208, pack_E6970Receipt50_chunk209, pack_E6970Receipt50_chunk210, pack_E6970Receipt50_chunk211, pack_E6970Receipt50_chunk212, pack_E6970Receipt50_chunk213, pack_E6970Receipt50_chunk214, pack_E6970Receipt50_chunk215, pack_E6970Receipt50_chunk216, pack_E6970Receipt50_chunk217, pack_E6970Receipt50_chunk218, pack_E6970Receipt50_chunk219, pack_E6970Receipt50_chunk220, pack_E6970Receipt50_chunk221, pack_E6970Receipt50_chunk222, pack_E6970Receipt50_chunk223, pack_E6970Receipt50_chunk224, pack_E6970Receipt50_chunk225, pack_E6970Receipt50_chunk226, pack_E6970Receipt50_chunk227, pack_E6970Receipt50_chunk228, pack_E6970Receipt50_chunk229, pack_E6970Receipt50_chunk230, pack_E6970Receipt50_chunk231, pack_E6970Receipt50_chunk232, pack_E6970Receipt50_chunk233, pack_E6970Receipt50_chunk234, pack_E6970Receipt50_chunk235, pack_E6970Receipt50_chunk236, pack_E6970Receipt50_chunk237, pack_E6970Receipt50_chunk238, pack_E6970Receipt50_chunk239, pack_E6970Receipt50_chunk240, pack_E6970Receipt50_chunk241, pack_E6970Receipt50_chunk242, pack_E6970Receipt50_chunk243, pack_E6970Receipt50_chunk244, pack_E6970Receipt50_chunk245, pack_E6970Receipt50_chunk246, pack_E6970Receipt50_chunk247, pack_E6970Receipt50_chunk248]
def rows50 := rowsFrom pack_E6970Receipt50_chunks
theorem good50 : ∀ r ∈ rows50, good 50 r = true := rowsFrom_good pack_E6970Receipt50_chunks
theorem sorted50 : rows50.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt50_chunks 0 (by decide +kernel)).1
theorem mass50 (i : Fin 61) :
    bandCount 50 (i.val : ℤ) 60 16 ≤ (rows50.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt50_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 50 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt50_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total50 : (rows50.map (price 50)).sum = 409061 :=
  (total_eq pack_E6970Receipt50_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt50

section Pack_E6970Receipt51

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt51_chunk0 := witnessA6966Final 51 60 0 930009 930080 32 3832
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk1 := witnessA6966Final 51 60 32 930081 930152 32 3632
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk2 := witnessA6966Final 51 60 64 930153 930262 32 3722
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk3 := witnessA6966Final 51 60 96 930263 930333 32 3652
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk4 := witnessA6966Final 51 60 128 930334 930448 32 3438
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk5 := witnessA6966Final 51 60 160 930449 930524 32 3476
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk6 := witnessA6966Final 51 60 192 930525 930648 32 3266
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk7 := witnessA6966Final 51 60 224 930649 930778 32 3076
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk8 := witnessA6966Final 51 60 256 930779 931024 32 2886
  0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk9 := witnessRule 51 60 288 931025 931030 6 504
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk10 := witnessRule 51 59 0 940008 940079 32 3654
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk11 := witnessRule 51 59 32 940080 940150 32 3444
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk12 := witnessRule 51 59 64 940151 940259 32 3482
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk13 := witnessRule 51 59 96 940260 940331 32 3474
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk14 := witnessRule 51 59 128 940332 940404 32 3192
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk15 := witnessRule 51 59 160 940448 940523 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk16 := witnessRule 51 59 192 940524 940648 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk17 := witnessRule 51 59 224 940649 940779 32 2828
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk18 := witnessRule 51 59 256 940832 941027 32 2661
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk19 := witnessRule 51 59 288 941028 941029 2 153
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk20 := witnessRule 51 58 0 950007 950077 32 3468
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk21 := witnessRule 51 58 32 950078 950148 32 3286
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk22 := witnessRule 51 58 64 950149 950257 32 3238
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk23 := witnessRule 51 58 96 950258 950329 32 3266
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk24 := witnessRule 51 58 128 950330 950403 32 2990
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk25 := witnessRule 51 58 160 950404 950523 32 3006
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk26 := witnessRule 51 58 192 950524 950649 32 2794
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk27 := witnessRule 51 58 224 950650 950833 32 2622
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk28 := witnessRule 51 58 256 950834 951029 30 2310
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk29 := witnessRule 51 57 0 960006 960076 32 3318
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk30 := witnessRule 51 57 32 960077 960146 32 3112
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk31 := witnessRule 51 57 64 960147 960216 32 3000
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk32 := witnessRule 51 57 96 960256 960328 32 3088
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk33 := witnessRule 51 57 128 960329 960402 32 2776
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk34 := witnessRule 51 57 160 960403 960523 32 2772
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk35 := witnessRule 51 57 192 960524 960650 32 2587
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk36 := witnessRule 51 57 224 960651 960836 32 2456
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk37 := witnessRule 51 57 256 960837 961028 25 1841
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk38 := witnessRule 51 56 0 970005 970074 32 3161
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk39 := witnessRule 51 56 32 970075 970144 32 2970
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk40 := witnessRule 51 56 64 970145 970214 32 2802
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk41 := witnessRule 51 56 96 970215 970327 32 2848
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk42 := witnessRule 51 56 128 970328 970402 32 2596
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk43 := witnessRule 51 56 160 970403 970524 32 2572
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk44 := witnessRule 51 56 192 970525 970652 32 2425
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk45 := witnessRule 51 56 224 970653 970839 32 2332
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk46 := witnessRule 51 56 256 970840 971028 20 1427
  0xfffdf 0xb99a (by decide +kernel)
private def pack_E6970Receipt51_chunk47 := witnessRule 51 55 0 980004 980073 32 3053
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk48 := witnessRule 51 55 32 980074 980142 32 2829
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk49 := witnessRule 51 55 64 980143 980213 32 2636
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk50 := witnessRule 51 55 96 980214 980327 32 2647
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk51 := witnessRule 51 55 128 980328 980402 32 2435
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk52 := witnessRule 51 55 160 980448 980525 32 2409
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk53 := witnessRule 51 55 192 980526 980705 32 2308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk54 := witnessRule 51 55 224 980706 980898 32 2237
  0xfdffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt51_chunk55 := witnessRule 51 55 256 980899 981027 14 966
  0x3ffe 0xba1a (by decide +kernel)
private def pack_E6970Receipt51_chunk56 := witnessRule 51 54 0 990003 990071 32 2953
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk57 := witnessRule 51 54 32 990072 990141 32 2665
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk58 := witnessRule 51 54 64 990142 990212 32 2488
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk59 := witnessRule 51 54 96 990213 990327 32 2467
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk60 := witnessRule 51 54 128 990328 990448 32 2319
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk61 := witnessRule 51 54 160 990449 990527 32 2271
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk62 := witnessRule 51 54 192 990576 990708 32 2213
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk63 := witnessRule 51 54 224 990709 990960 32 2156
  0xfbe7edff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt51_chunk64 := witnessRule 51 54 256 990961 991027 8 538
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk65 := witnessRule 51 53 0 1000002 1000070 32 2894
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk66 := witnessRule 51 53 32 1000071 1000140 32 2509
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk67 := witnessRule 51 53 64 1000141 1000212 32 2359
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk68 := witnessRule 51 53 96 1000213 1000328 32 2324
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk69 := witnessRule 51 53 128 1000329 1000450 32 2222
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk70 := witnessRule 51 53 160 1000451 1000578 32 2169
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk71 := witnessRule 51 53 192 1000579 1000712 32 2116
  0xb7ffffff 0x5cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt51_chunk72 := witnessRule 51 53 224 1000713 1001025 32 2088
  0xffef9f2f 0x5d8d0b8b29b27164362e4c86c9c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt51_chunk73 := witnessRule 51 53 256 1001026 1001026 1 67
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk74 := witnessRule 51 52 0 1010001 1010069 32 2779
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk75 := witnessRule 51 52 32 1010070 1010140 32 2388
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk76 := witnessRule 51 52 64 1010141 1010212 32 2245
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk77 := witnessRule 51 52 96 1010213 1010329 32 2211
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk78 := witnessRule 51 52 128 1010330 1010452 32 2128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk79 := witnessRule 51 52 160 1010453 1010581 32 2076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk80 := witnessRule 51 52 192 1010582 1010770 32 2038
  0x3c9f6dff 0x1b8b19884375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt51_chunk81 := witnessRule 51 52 224 1010771 1011026 26 1650
  0x3ffde7c 0xbb9a17166364e2ca6c5c994d939321b (by decide +kernel)
private def pack_E6970Receipt51_chunk82 := witnessRule 51 51 0 1020000 1020069 32 2689
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk83 := witnessRule 51 51 32 1020070 1020140 32 2262
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk84 := witnessRule 51 51 64 1020141 1020213 32 2138
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk85 := witnessRule 51 51 96 1020256 1020331 32 2111
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk86 := witnessRule 51 51 128 1020332 1020455 32 2035
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk87 := witnessRule 51 51 160 1020456 1020585 32 1992
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt51_chunk88 := witnessRule 51 51 192 1020586 1020775 32 1966
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt51_chunk89 := witnessRule 51 51 224 1020832 1021025 18 1116
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt51_chunk90 := witnessRule 51 50 0 1030000 1030069 32 2529
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk91 := witnessRule 51 50 32 1030070 1030141 32 2150
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk92 := witnessRule 51 50 64 1030142 1030257 32 2053
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk93 := witnessRule 51 50 96 1030258 1030333 32 1997
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk94 := witnessRule 51 50 128 1030334 1030458 32 1950
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk95 := witnessRule 51 50 160 1030459 1030641 32 1919
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt51_chunk96 := witnessRule 51 50 192 1030642 1030837 32 1903
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt51_chunk97 := witnessRule 51 50 224 1030896 1031025 10 612
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk98 := witnessRule 51 49 0 1040000 1040070 32 2388
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk99 := witnessRule 51 49 32 1040071 1040142 32 2038
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk100 := witnessRule 51 49 64 1040143 1040259 32 1963
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk101 := witnessRule 51 49 96 1040260 1040336 32 1899
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk102 := witnessRule 51 49 128 1040337 1040462 32 1873
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt51_chunk103 := witnessRule 51 49 160 1040512 1040646 32 1854
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt51_chunk104 := witnessRule 51 49 192 1040647 1040962 32 1863
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt51_chunk105 := witnessRule 51 49 224 1041024 1041024 1 61
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk106 := witnessRule 51 48 0 1050000 1050070 32 2248
  0xfffffcff 0x25ccd538a2 (by decide +kernel)
private def pack_E6970Receipt51_chunk107 := witnessRule 51 48 32 1050071 1050143 32 1945
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk108 := witnessRule 51 48 64 1050144 1050261 32 1879
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk109 := witnessRule 51 48 96 1050262 1050385 32 1819
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt51_chunk110 := witnessRule 51 48 128 1050386 1050515 32 1805
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt51_chunk111 := witnessRule 51 48 160 1050516 1050705 32 1783
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt51_chunk112 := witnessRule 51 48 192 1050706 1051024 25 1426
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk113 := witnessRule 51 47 0 1060000 1060071 32 2125
  0xbfffd5ff 0xa714136ce8c66ddc990dc3a9a (by decide +kernel)
private def pack_E6970Receipt51_chunk114 := witnessRule 51 47 32 1060072 1060144 32 1854
  0xffaffffa 0x87263372e869dcd8cdc38b21b (by decide +kernel)
private def pack_E6970Receipt51_chunk115 := witnessRule 51 47 64 1060145 1060263 32 1799
  0xfcfffebf 0xa73356e28a5c58cddb8a2 (by decide +kernel)
private def pack_E6970Receipt51_chunk116 := witnessRule 51 47 96 1060264 1060388 32 1750
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt51_chunk117 := witnessRule 51 47 128 1060389 1060519 32 1731
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt51_chunk118 := witnessRule 51 47 160 1060520 1060711 32 1728
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt51_chunk119 := witnessRule 51 47 192 1060768 1060961 16 899
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk120 := witnessRule 51 46 0 1070000 1070071 32 2009
  0xbffd547f 0xa715131086f0c66d1d990daba329b8736151092e2c2a262165c54cdd3922 (by decide +kernel)
private def pack_E6970Receipt51_chunk121 := witnessRule 51 46 32 1070072 1070145 32 1774
  0xfd55ffaa 0x2bb319b6746436ee4ca6e9c5854425b8924776336aeac86d9cd94dcb930a884 (by decide +kernel)
private def pack_E6970Receipt51_chunk122 := witnessRule 51 46 64 1070146 1070265 32 1726
  0xb43ff54f 0xaecc66ddd18cdc39321b9716331092ea68629c4db3ab19b77364370e2ca6edc5441db892 (by decide +kernel)
private def pack_E6970Receipt51_chunk123 := witnessRule 51 46 96 1070266 1070391 32 1681
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt51_chunk124 := witnessRule 51 46 128 1070392 1070523 32 1663
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt51_chunk125 := witnessRule 51 46 160 1070576 1070773 32 1692
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt51_chunk126 := witnessRule 51 46 192 1070832 1070960 8 445
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk127 := witnessRule 51 45 0 1080000 1080072 32 1909
  0x7d5407f 0x8726152310b0e2c2a8729c5895d38a8a09ca7141278c6685e990d93c329b577615108ceac2a262159d1854ce3b9b0a918857726154392e4c4ae1c554dd39289b (by decide +kernel)
private def pack_E6970Receipt51_chunk128 := witnessRule 51 45 32 1080073 1080146 32 1692
  0xeaa07d54 0x27a63366f0c86d1d994dbbab0a8848736151310b0e4c2a6725c58548c42cb8aa1bb72554e2824c5ed8cd93cb21b3776536cecc2a211dd18544c42bb9b0a99c (by decide +kernel)
private def pack_E6970Receipt51_chunk129 := witnessRule 51 45 64 1080147 1080267 32 1656
  0x900ed143 0x37864368f0c66d5d990db3ab198846746536ee6c86211dc998d8c439311c1897161310a312e66c5ed8cd9bcb19b4776436aecc662115d594dc3a30a8849726151310b2e2c2a6729c548c425b8a8a3 (by decide +kernel)
private def pack_E6970Receipt51_chunk130 := witnessRule 51 45 96 1080268 1080394 32 1613
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt51_chunk131 := witnessRule 51 45 128 1080395 1080580 32 1610
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt51_chunk132 := witnessRule 51 45 160 1080581 1080960 32 1674
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk133 := witnessRule 51 44 0 1090000 1090072 32 1810
  0x3d4001f 0x439b1289c9726251092e2c4a4729c944c425b8a893a72258c2a46c9ed854421bcb0a898853786153388eec2a462151d98550e33b312b574615538ee8c4a2721cd8944243931291c9716251310b2e4a66e9c5491d3912 (by decide +kernel)
private def pack_E6970Receipt51_chunk134 := witnessRule 51 44 32 1090073 1090147 32 1616
  0xc5003d40 0x3190d0bdb1988417a65368f2c2a2115dd8544c42abb30a99c6756152310ace8c2a8721d1895bb930aa9c9726251394e2c4a2129c948ddb8a093b65346f4c2a2111e18544c42a3bb0a99c5766152310aaeac2a871dd5895b39b0aa9c (by decide +kernel)
private def pack_E6970Receipt51_chunk135 := witnessRule 51 44 64 1090192 1090269 32 1587
  0x80038200 0x2f4ca6c9e990d9bcb1988437865368eec862111d998dabab29884574673630ce8c67061dcd88c428c3b9321c1887163310a310ea6c5ed90d93d31988427965366f0c86210ddd98db3b30a89885675615338ee8c2a46215dcd8550e43930a99885871615538312e2c2a274629c54425b8a093 (by decide +kernel)
private def pack_E6970Receipt51_chunk136 := witnessRule 51 44 96 1090270 1090397 32 1551
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt51_chunk137 := witnessRule 51 44 128 1090448 1090584 32 1563
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt51_chunk138 := witnessRule 51 44 160 1090640 1090897 24 1234
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk139 := witnessRule 51 43 0 1100000 1100073 32 1723
  0x1c0001f 0x7746251310aee6c4a6721c98948c42c38b12a1ca7163574e4a28272dc896b0a89884c6153362f6c2a462145e98550e1bd312b2786155388f0c4a2715dd894422bb31291c6756251310ace8c4a671dcd8948c42bb9312a1c97263570e4aa6e9cd44ddb912 (by decide +kernel)
private def pack_E6970Receipt51_chunk140 := witnessRule 51 43 32 1100074 1100193 32 1550
  0x28000a00 0x1897152310a314e282331854cd93db0a8988527a6153386f2c2a46214de18550e23bb0a99885476615538cecc4a271dd5894423ba31291c8736251310b0e4c4a6725c58948c42cb92a1b18a72576e44b9854418be30a8988517b6153384f4c2a462149e58550e23cb12b377615538aeec4a2719d98944233ab1291c (by decide +kernel)
private def pack_E6970Receipt51_chunk141 := witnessRule 51 43 64 1100194 1100271 32 1508
  0xe000c000 0x2f6c862105e998d93cb2988427867366eecc6210dd9a0d8c23b321c1857563310a30ae8ca70619cd90c428c339331c1877165310a30eee6f190c41db31a17a6531082f2ce6cde5854ce23c30a91885477615438aecc2a662155d58554e33a30aa188567361563830ee6c2a474621c98544c430c438b0a99d (by decide +kernel)
private def pack_E6970Receipt51_chunk142 := witnessRule 51 43 96 1100320 1100451 32 1502
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt51_chunk143 := witnessRule 51 43 128 1100452 1100644 32 1523
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt51_chunk144 := witnessRule 51 43 160 1100645 1100896 16 811
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk145 := witnessRule 51 42 0 1110000 1110073 32 1633
  0xc0000f 0x1dd58d5b39b12a9c8736351392e4c6a2125c58d48e539a89884b7251274e2844f9895631291b17c6251384f6c4a2109e98948e1bcb12898853786253388eec4a462151d98950e33b31ab574625538ee8c6a2721cd8d44243931a91c9716351310b2e6a66e9c9491d38a113 (by decide +kernel)
private def pack_E6970Receipt51_chunk146 := witnessRule 51 42 32 1110074 1110194 32 1484
  0x10000400 0x61dc58554e8c438aa1885288714239ac2a4621318550d8bdb0a9988517a6155384f2c2a862149e18558e23c31291c5776251310aaecc4a6719d58948c42b3a312a1c7736253310aee4c4aa70621c98944e8c4b8b128851897252396e2a2825358944de30a99884b6155364f6c4a270de9894421bcb1291c4786251310a8eec4a6715d98948c42abab12a1c (by decide +kernel)
private def pack_E6970Receipt51_chunk147 := witnessRule 51 42 64 1110195 1110321 32 1448
  0x39003000 0x11c5b4dabe1883b6631074d0685e1a4d8c13c329c1837764310a306eccc70611d594c428c23a339c1857366310a30ae4d070619c59cc428c33c9bb6155362f6c2a8709e9854cc4293cb0aa9c3786154310a6eec2ac711d98554c42a3ab0ab9c1857561533a30ce8c2a46218619cd8550e8c3b930a99886 (by decide +kernel)
private def pack_E6970Receipt51_chunk148 := witnessRule 51 42 96 1110322 1110454 32 1441
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt51_chunk149 := witnessRule 51 42 128 1110455 1110706 32 1501
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk150 := witnessRule 51 42 160 1110707 1110896 9 452
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk151 := witnessRule 51 41 0 1120000 1120074 32 1551
  0x60000f 0x19d98d44233ab1a91c7746351310aee6c6a6721c98d48c42c38b1aa1c1897163594e6a28272dc5089eb1289884c6253362f6c4a462145e98950e1bd31ab2786255388f0c6a2715dd8d4422bb31a91c6756351310ace8c6a671dcd8d48c42bb931aa1c97264570e6aa6e9d144ddb8a913 (by decide +kernel)
private def pack_E6970Receipt51_chunk152 := witnessRule 51 41 32 1120075 1120196 32 1418
  0x4000000 0x30ae6c2ac74619c98554c430c338b0ab9d38671633870ee462131894cddb0aa9884a6157364f4c4a670de58948c429bc312a1c4776253310a8ecc4aa715d58950c42aba312b1c1867462523a30ee6c4a2621861dc9894ce8c438b1291886188725438512e2a232dc5089eb12903d6252362f8c4a262145ed894ce13d312918852796254386f0c4a66214ddd8954e2bbb1a89c (by decide +kernel)
private def pack_E6970Receipt51_chunk153 := witnessRule 51 41 64 1120197 1120324 32 1385
  0x7600c00 0x13a3618842736e366e4da6210dc5bcda3f1883a615736302f0ce70609dd98c428c13b341c1837567310a306e8d270611cda0c428c239351c1857169310a30af66f18550c425b0ab1b17a6155310a2f2c2ae709e18558c4293bb0ac1c1837761543a308ecc2a66218611d58554e8c2ba30aa1886 (by decide +kernel)
private def pack_E6970Receipt51_chunk154 := witnessRule 51 41 96 1120325 1120458 32 1392
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt51_chunk155 := witnessRule 51 41 128 1120512 1120832 32 1492
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk156 := witnessRule 51 41 160 1120833 1120833 1 50
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk157 := witnessRule 51 40 0 1130000 1130074 32 1467
  0x60000f 0x15d98d48c42abab1aa1c6746353310ace6c6aa7061dcd8d44e8c43931a8851887163523a312e6a26214629c944a6b1a883c6352362f8c6a2709ed8d44213d31a91c3796351310a6f0c6a6711dd8d48c42a3b31aa1c6766456ae8c6aa71dd19144e439b228848726452392e2c8a262165d14cdd39a923 (by decide +kernel)
private def pack_E6970Receipt51_chunk158 := witnessRule 51 40 32 1130075 1130197 32 1354
  0x2000000 0x308e8c2ac6218611cd8560e9c239b21c3857263310a70ae2ca70e19d0c42631291904c6254362f6c4a662145e98954e13cb12a18852786256386eec4aa6214dd9895ce0c23b31299d185756252310c30ae8c4a874619cd894cc430c339312a9d187716254310c30ee4ac70e1dc548e0c538a0908dd625132098c4a66212d8954d8bd312a18851796256386f2c6a4711e18d44c42a3bb1a99c (by decide +kernel)
private def pack_E6970Receipt51_chunk159 := witnessRule 51 40 64 1130198 1130326 32 1325
  0xe1fe0300 0xb9b2006c9c9bcc42138b2206cdd003106302ecd470609d5a4c428c13a359c183736a310a306e4d870611c5acc428c23e9bb6255374c2ae621258564d8c0bcb0aa9d182786154310c304eec2ac7460dd98554c430c1bab0ab9d (by decide +kernel)
private def pack_E6970Receipt51_chunk160 := witnessRule 51 40 96 1130327 1130515 32 1360
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt51_chunk161 := witnessRule 51 40 128 1130516 1130832 26 1192
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk162 := witnessRule 51 39 0 1140000 1140075 32 1388
  0x100007 0x3776355388ecc6a862151d58d58e0c2bab1a91d186746351310c30ce6c6a67461dc98d48c430c3b8b1aa1d1887353310a510e4a28276dc54508a6b1a89884c6353362f6c6a462145e98d50e13cb1a998852786355388f0c8a2715dd914422bb32291c6756451310ace8c8a671dcd9148c42bb9322a1c1887264590e8aa6c625d144e5b92913 (by decide +kernel)
private def pack_E6970Receipt51_chunk163 := witnessRule 51 39 32 1140076 1140199 32 1289
  0x80800000 0x609d58564e9c13ab29c3837464310a706e6cc70e11c994c429c238b39c3857631098c4a66412d8954c425312b9b1796256310a2f0c4b070609e18950e8c1bbb12998861837662553a308eac4a86218611d18958e8c2b9b12a98861857262573a70ae4c2a674e19c58548c431c338aa1c3887217ac4a80f18d48c425b1aa1b17b6353384f4c6a462149e58d50e1bc31a99885 (by decide +kernel)
private def pack_E6970Receipt51_chunk164 := witnessRule 51 39 64 1140200 1140329 32 1272
  0xff7fe0c0 0x5c593036302e8da70609cdb0c428c139371c183716d310a306fe6ed8950c825312b188418a6155310a312c2ae70605e18558c430c0bbb0ac1d (by decide +kernel)
private def pack_E6970Receipt51_chunk165 := witnessRule 51 39 96 1140330 1140519 32 1336
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk166 := witnessRule 51 39 128 1140576 1140832 19 859
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk167 := witnessRule 51 38 0 1150000 1150075 32 1310
  0x100007 0x277635738306eec6a674611d98d48c430c23ab1aa1d185746353310c30ae6c6aa74619c98d50c430c338b1ab1d3867162523a70ee4a26214a25c544846eb1a983c6452376c6a8621298d58d93d32291c3796451310a6f0c8a6711dd9148c42a3b322a1c5756453310aae8c8aa70619d19144e8c3b9b228851877264523a310e2c8a26218621d14ce0c4b9a924 (by decide +kernel)
private def pack_E6970Receipt51_chunk168 := witnessRule 51 38 32 1150076 1150200 32 1224
  0x60400000 0xc3b0ad1c381756738704e8cc6214e09cda0e1c1b9339885383716938708f0621318948d025b1aa1884a635636314c4aa70605e58950c430c0bc312b1d182776255310c304ecc4ae7460dd58958c430c1ba312c1d3837461543a708e6c2a66218e11c98554e9c2b8b0aa188638571563890ce4623318d44cc2631a99884b6355362f4c6a862145e58d58e13c31aa9885 (by decide +kernel)
private def pack_E6970Receipt51_chunk169 := witnessRule 51 38 64 1150201 1150331 32 1231
  0xfffffe35 0xc0b9320070609c5bcc428c13a206e98954cc20c4b0ab1905 (by decide +kernel)
private def pack_E6970Receipt51_chunk170 := witnessRule 51 38 96 1150384 1150579 32 1317
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk171 := witnessRule 51 38 128 1150580 1150769 12 533
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk172 := witnessRule 51 37 0 1160000 1160076 32 1235
  0x80027 0x302f2c6a874609e18d4cc430c13bb1aa9d183766354310c306eac6ac74611d18d54c430c239b1ab9d3847362533a70ae4c4a46218e15c58950e9c339299885387715141311d8c8a264131914cd8bdb229188517a6454384f2c8a662149e19154e1bbb22a1885376645638308ecc8a474615d59144c430c2ba32299d186736452310c30ce4c8a87461dd154e1c3b9a89c (by decide +kernel)
private def pack_E6970Receipt51_chunk173 := witnessRule 51 37 32 1160077 1160202 32 1166
  0xfe100000 0x381736a38704e4d26214e09c5ace1c1bd1884b635333094c6aa64106298950c828c4b12b1885188625838302eec4ae6218605d98964e9c0bb30aa9d382756154310c704e8c2ac74e0dcd8554c431c1b930ab9d384716156310c708e2b071611d0de31aa83c635233096c8a86e98d58c424b1ac1b (by decide +kernel)
private def pack_E6970Receipt51_chunk174 := witnessRule 51 37 64 1160203 1160386 32 1201
  0xffffffef 0x302e981b (by decide +kernel)
private def pack_E6970Receipt51_chunk175 := witnessRule 51 37 96 1160387 1160642 32 1301
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk176 := witnessRule 51 37 128 1160643 1160768 5 220
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk177 := witnessRule 51 36 0 1170000 1170076 32 1163
  0x80003 0xc4b1ab1c181786355310c302eec6ae74609d98d58c430c13ab1ac1d3827562543a706e8c4a66218e0dcd8954e9c239312a18863847162563a70ae4aa6215215c5450cee322a03c645232096c8a8621299158d8bcb22a9885178645738304f0c8a67460ddd9148c430c1bb322a1d184756453310c308e8c8aa74615cd9150c430c2b9322b1d3857263523a70ce2c6a26218e19cd4ce1443929208d (by decide +kernel)
private def pack_E6970Receipt51_chunk178 := witnessRule 51 36 32 1170077 1170203 32 1116
  0xffd80100 0x702e2da72d8d48d42531aa1a0418a6253340a312c4aa6614621895cc828c3b12c98853876155310a70cc2ae70e05d58558c431c0ba30ac1d3827261593ab04e4ca7160dc590c42ac1bb1bc635135096c8a6641299154c420c531aa1885 (by decide +kernel)
private def pack_E6970Receipt51_chunk179 := witnessRule 51 36 64 1170204 1170389 32 1173
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk180 := witnessRule 51 36 96 1170390 1170768 31 1247
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk181 := witnessRule 51 35 0 1180000 1180077 32 1092
  0x40003 0xc531a999851896355320a310c6ae621461d8d64e1c3b12a9c381766254310c702eac4ac74e09d18954c431c139b12b9d383726256310c706e2c4b07560dc58550eac238a99885c645134096caa6621299554d8c5322a1c181796453310c302f0c8aa74609dd9150c430c13b322b1d183756455310c306e8c8ae74e0dd18d4ce9c239b1a918863847263543a70ae2c6a66218e15cd54e2433928988d (by decide +kernel)
private def pack_E6970Receipt51_chunk182 := witnessRule 51 35 32 1180078 1180205 32 1075
  0xfffeaac0 0x14c6a66c106258950d428c3b12c19853866156320a708c2b471605c99ce2c138b3188558278378c6ae0ed9148d025322a1984 (by decide +kernel)
private def pack_E6970Receipt51_chunk183 := witnessRule 51 35 64 1180256 1180392 32 1149
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk184 := witnessRule 51 35 96 1180448 1180705 24 945
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk185 := witnessRule 51 34 0 1190000 1190077 32 1031
  0xc0013 0x314c6a46a146258d50d028c431ab19851876358320a70ec4a86414e198958c429c2b12c1c381746257310c702e6c4b275605cd8554eac13930aa18865827161563b8c8ac0ed9548cc2532aa190418a6453320a312c8aa6214621915ce0c0bbb22b18861817664583a702ecc6a874e09d58d4cc431c13a31aa9d383736354310c706e4c6ac74e11cd5ce2c239299c (by decide +kernel)
private def pack_E6970Receipt51_chunk186 := witnessRule 51 34 32 1190078 1190257 32 1041
  0xfffffff8 0xb02f46ed9144d82532299a84 (by decide +kernel)
private def pack_E6970Receipt51_chunk187 := witnessRule 51 34 64 1190258 1190450 32 1125
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk188 := witnessRule 51 34 96 1190451 1190704 18 693
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk189 := witnessRule 51 33 0 1200000 1200078 32 976
  0x6000b 0x14c8a46e106298d44dc28c4b1a99b051886355350a30ec6ae6814e1d894cd029c3312a99853856257320a708c4b262156118554c42ac1b0ab9c581726156310cb02e2c2b076d9544d42532a99a0418a6452340a312c8a866146219158c828c3b22c18853876354310a70cc6ac70e05d58d54c431c0ba31ab9d382736356310c704e4c6b075609c98950eac1b92a9c (by decide +kernel)
private def pack_E6970Receipt51_chunk190 := witnessRule 51 33 32 1200079 1200259 32 1012
  0xfffffffe 0x5b22c03 (by decide +kernel)
private def pack_E6970Receipt51_chunk191 := witnessRule 51 33 64 1200260 1200454 32 1103
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk192 := witnessRule 51 33 96 1200512 1200704 12 455
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk193 := witnessRule 51 32 0 1210000 1210078 32 927
  0x55560007 0x532289c841896352380a30ec6ac6c14e198950d429c2312c19855836156320ab02c2b472d955c1d32a91b0418a6451360a312c8a66a146219154d028c3b22b99853876353330a70cc6aa6414e158d5cc429c231ac9c584625538b02e6c4a86219605c98958eac138b12a9886 (by decide +kernel)
private def pack_E6970Receipt51_chunk194 := witnessRule 51 32 32 1210128 1210261 32 984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk195 := witnessRule 51 32 64 1210262 1210515 32 1083
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk196 := witnessRule 51 32 96 1210516 1210641 6 223
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk197 := witnessRule 51 31 0 1220000 1220128 32 888
  0xffff0003 0x299544e020c5322c041896452370a310c8a86c1461d9158d429c3b1a91a853866354340a70ac6ac6614e118d60c82ac2312a19055836256310ab04c4b071605c5895cc432c0b92c9c (by decide +kernel)
private def pack_E6970Receipt51_chunk198 := witnessRule 51 31 32 1220129 1220263 32 956
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk199 := witnessRule 51 31 64 1220264 1220640 32 1070
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk200 := witnessRule 51 30 0 1230000 1230129 32 852
  0xfffffd01 0x3866353360a708c6ae6815611894cd02ac1b12a99855826257320ab02c4b26215e058554c42bc0ab9b (by decide +kernel)
private def pack_E6970Receipt51_chunk201 := witnessRule 51 30 32 1230130 1230265 32 927
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk202 := witnessRule 51 30 64 1230320 1230640 27 879
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk203 := witnessRule 51 29 0 1240000 1240130 32 820
  0xffffa555 0x965513b08310c8a4741461d9150e429c331a91c053846356360ab06c4a86a156058960cc2bc0ab1904 (by decide +kernel)
private def pack_E6970Receipt51_chunk204 := witnessRule 51 29 32 1240131 1240322 32 902
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk205 := witnessRule 51 29 64 1240323 1240577 21 663
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk206 := witnessRule 51 28 0 1250000 1250131 32 789
  0xffffdfff 0x432a91e04 (by decide +kernel)
private def pack_E6970Receipt51_chunk207 := witnessRule 51 28 32 1250132 1250324 32 875
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk208 := witnessRule 51 28 64 1250325 1250576 16 491
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk209 := witnessRule 51 27 0 1260000 1260132 32 759
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk210 := witnessRule 51 27 32 1260133 1260384 32 851
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk211 := witnessRule 51 27 64 1260385 1260576 11 330
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk212 := witnessRule 51 26 0 1270000 1270133 32 728
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk213 := witnessRule 51 26 32 1270134 1270387 32 827
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk214 := witnessRule 51 26 64 1270388 1270513 6 175
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk215 := witnessRule 51 25 0 1280000 1280134 32 698
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk216 := witnessRule 51 25 32 1280135 1280450 32 808
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk217 := witnessRule 51 25 64 1280512 1280512 1 29
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk218 := witnessRule 51 24 0 1290000 1290135 32 667
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk219 := witnessRule 51 24 32 1290136 1290512 29 707
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk220 := witnessRule 51 23 0 1300000 1300136 32 637
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk221 := witnessRule 51 23 32 1300192 1300449 24 561
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk222 := witnessRule 51 22 0 1310000 1310192 32 607
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk223 := witnessRule 51 22 32 1310193 1310448 20 447
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk224 := witnessRule 51 21 0 1320000 1320194 32 579
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk225 := witnessRule 51 21 32 1320195 1320448 16 343
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk226 := witnessRule 51 20 0 1330000 1330195 32 549
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk227 := witnessRule 51 20 32 1330196 1330385 12 245
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk228 := witnessRule 51 19 0 1340000 1340197 32 521
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk229 := witnessRule 51 19 32 1340256 1340384 8 157
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk230 := witnessRule 51 18 0 1350000 1350257 32 493
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk231 := witnessRule 51 18 32 1350258 1350384 5 94
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk232 := witnessRule 51 17 0 1360000 1360320 32 468
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk233 := witnessRule 51 17 32 1360321 1360321 1 18
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk234 := witnessRule 51 16 0 1370000 1370320 30 408
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk235 := witnessRule 51 15 0 1380000 1380320 27 339
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk236 := witnessRule 51 14 0 1390000 1390257 24 273
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk237 := witnessRule 51 13 0 1400000 1400256 21 216
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk238 := witnessRule 51 12 0 1410000 1410256 19 175
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk239 := witnessRule 51 11 0 1420000 1420193 16 129
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk240 := witnessRule 51 10 0 1430000 1430192 14 97
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk241 := witnessRule 51 9 0 1440000 1440192 12 71
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk242 := witnessRule 51 8 0 1450000 1450129 10 47
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk243 := witnessRule 51 7 0 1460000 1460128 8 29
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk244 := witnessRule 51 6 0 1470000 1470128 7 18
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk245 := witnessRule 51 5 0 1480000 1480065 5 7
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk246 := witnessRule 51 4 0 1490000 1490064 4 1
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk247 := witnessRule 51 3 0 1500000 1500064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk248 := witnessRule 51 2 0 1510000 1510001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk249 := witnessRule 51 1 0 1520000 1520000 1 0
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt51_chunk250 := witnessRule 51 0 0 1530000 1530000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt51_chunks : List (Chunk 51) := [pack_E6970Receipt51_chunk0, pack_E6970Receipt51_chunk1, pack_E6970Receipt51_chunk2, pack_E6970Receipt51_chunk3, pack_E6970Receipt51_chunk4, pack_E6970Receipt51_chunk5, pack_E6970Receipt51_chunk6, pack_E6970Receipt51_chunk7, pack_E6970Receipt51_chunk8, pack_E6970Receipt51_chunk9, pack_E6970Receipt51_chunk10, pack_E6970Receipt51_chunk11, pack_E6970Receipt51_chunk12, pack_E6970Receipt51_chunk13, pack_E6970Receipt51_chunk14, pack_E6970Receipt51_chunk15, pack_E6970Receipt51_chunk16, pack_E6970Receipt51_chunk17, pack_E6970Receipt51_chunk18, pack_E6970Receipt51_chunk19, pack_E6970Receipt51_chunk20, pack_E6970Receipt51_chunk21, pack_E6970Receipt51_chunk22, pack_E6970Receipt51_chunk23, pack_E6970Receipt51_chunk24, pack_E6970Receipt51_chunk25, pack_E6970Receipt51_chunk26, pack_E6970Receipt51_chunk27, pack_E6970Receipt51_chunk28, pack_E6970Receipt51_chunk29, pack_E6970Receipt51_chunk30, pack_E6970Receipt51_chunk31, pack_E6970Receipt51_chunk32, pack_E6970Receipt51_chunk33, pack_E6970Receipt51_chunk34, pack_E6970Receipt51_chunk35, pack_E6970Receipt51_chunk36, pack_E6970Receipt51_chunk37, pack_E6970Receipt51_chunk38, pack_E6970Receipt51_chunk39, pack_E6970Receipt51_chunk40, pack_E6970Receipt51_chunk41, pack_E6970Receipt51_chunk42, pack_E6970Receipt51_chunk43, pack_E6970Receipt51_chunk44, pack_E6970Receipt51_chunk45, pack_E6970Receipt51_chunk46, pack_E6970Receipt51_chunk47, pack_E6970Receipt51_chunk48, pack_E6970Receipt51_chunk49, pack_E6970Receipt51_chunk50, pack_E6970Receipt51_chunk51, pack_E6970Receipt51_chunk52, pack_E6970Receipt51_chunk53, pack_E6970Receipt51_chunk54, pack_E6970Receipt51_chunk55, pack_E6970Receipt51_chunk56, pack_E6970Receipt51_chunk57, pack_E6970Receipt51_chunk58, pack_E6970Receipt51_chunk59, pack_E6970Receipt51_chunk60, pack_E6970Receipt51_chunk61, pack_E6970Receipt51_chunk62, pack_E6970Receipt51_chunk63, pack_E6970Receipt51_chunk64, pack_E6970Receipt51_chunk65, pack_E6970Receipt51_chunk66, pack_E6970Receipt51_chunk67, pack_E6970Receipt51_chunk68, pack_E6970Receipt51_chunk69, pack_E6970Receipt51_chunk70, pack_E6970Receipt51_chunk71, pack_E6970Receipt51_chunk72, pack_E6970Receipt51_chunk73, pack_E6970Receipt51_chunk74, pack_E6970Receipt51_chunk75, pack_E6970Receipt51_chunk76, pack_E6970Receipt51_chunk77, pack_E6970Receipt51_chunk78, pack_E6970Receipt51_chunk79, pack_E6970Receipt51_chunk80, pack_E6970Receipt51_chunk81, pack_E6970Receipt51_chunk82, pack_E6970Receipt51_chunk83, pack_E6970Receipt51_chunk84, pack_E6970Receipt51_chunk85, pack_E6970Receipt51_chunk86, pack_E6970Receipt51_chunk87, pack_E6970Receipt51_chunk88, pack_E6970Receipt51_chunk89, pack_E6970Receipt51_chunk90, pack_E6970Receipt51_chunk91, pack_E6970Receipt51_chunk92, pack_E6970Receipt51_chunk93, pack_E6970Receipt51_chunk94, pack_E6970Receipt51_chunk95, pack_E6970Receipt51_chunk96, pack_E6970Receipt51_chunk97, pack_E6970Receipt51_chunk98, pack_E6970Receipt51_chunk99, pack_E6970Receipt51_chunk100, pack_E6970Receipt51_chunk101, pack_E6970Receipt51_chunk102, pack_E6970Receipt51_chunk103, pack_E6970Receipt51_chunk104, pack_E6970Receipt51_chunk105, pack_E6970Receipt51_chunk106, pack_E6970Receipt51_chunk107, pack_E6970Receipt51_chunk108, pack_E6970Receipt51_chunk109, pack_E6970Receipt51_chunk110, pack_E6970Receipt51_chunk111, pack_E6970Receipt51_chunk112, pack_E6970Receipt51_chunk113, pack_E6970Receipt51_chunk114, pack_E6970Receipt51_chunk115, pack_E6970Receipt51_chunk116, pack_E6970Receipt51_chunk117, pack_E6970Receipt51_chunk118, pack_E6970Receipt51_chunk119, pack_E6970Receipt51_chunk120, pack_E6970Receipt51_chunk121, pack_E6970Receipt51_chunk122, pack_E6970Receipt51_chunk123, pack_E6970Receipt51_chunk124, pack_E6970Receipt51_chunk125, pack_E6970Receipt51_chunk126, pack_E6970Receipt51_chunk127, pack_E6970Receipt51_chunk128, pack_E6970Receipt51_chunk129, pack_E6970Receipt51_chunk130, pack_E6970Receipt51_chunk131, pack_E6970Receipt51_chunk132, pack_E6970Receipt51_chunk133, pack_E6970Receipt51_chunk134, pack_E6970Receipt51_chunk135, pack_E6970Receipt51_chunk136, pack_E6970Receipt51_chunk137, pack_E6970Receipt51_chunk138, pack_E6970Receipt51_chunk139, pack_E6970Receipt51_chunk140, pack_E6970Receipt51_chunk141, pack_E6970Receipt51_chunk142, pack_E6970Receipt51_chunk143, pack_E6970Receipt51_chunk144, pack_E6970Receipt51_chunk145, pack_E6970Receipt51_chunk146, pack_E6970Receipt51_chunk147, pack_E6970Receipt51_chunk148, pack_E6970Receipt51_chunk149, pack_E6970Receipt51_chunk150, pack_E6970Receipt51_chunk151, pack_E6970Receipt51_chunk152, pack_E6970Receipt51_chunk153, pack_E6970Receipt51_chunk154, pack_E6970Receipt51_chunk155, pack_E6970Receipt51_chunk156, pack_E6970Receipt51_chunk157, pack_E6970Receipt51_chunk158, pack_E6970Receipt51_chunk159, pack_E6970Receipt51_chunk160, pack_E6970Receipt51_chunk161, pack_E6970Receipt51_chunk162, pack_E6970Receipt51_chunk163, pack_E6970Receipt51_chunk164, pack_E6970Receipt51_chunk165, pack_E6970Receipt51_chunk166, pack_E6970Receipt51_chunk167, pack_E6970Receipt51_chunk168, pack_E6970Receipt51_chunk169, pack_E6970Receipt51_chunk170, pack_E6970Receipt51_chunk171, pack_E6970Receipt51_chunk172, pack_E6970Receipt51_chunk173, pack_E6970Receipt51_chunk174, pack_E6970Receipt51_chunk175, pack_E6970Receipt51_chunk176, pack_E6970Receipt51_chunk177, pack_E6970Receipt51_chunk178, pack_E6970Receipt51_chunk179, pack_E6970Receipt51_chunk180, pack_E6970Receipt51_chunk181, pack_E6970Receipt51_chunk182, pack_E6970Receipt51_chunk183, pack_E6970Receipt51_chunk184, pack_E6970Receipt51_chunk185, pack_E6970Receipt51_chunk186, pack_E6970Receipt51_chunk187, pack_E6970Receipt51_chunk188, pack_E6970Receipt51_chunk189, pack_E6970Receipt51_chunk190, pack_E6970Receipt51_chunk191, pack_E6970Receipt51_chunk192, pack_E6970Receipt51_chunk193, pack_E6970Receipt51_chunk194, pack_E6970Receipt51_chunk195, pack_E6970Receipt51_chunk196, pack_E6970Receipt51_chunk197, pack_E6970Receipt51_chunk198, pack_E6970Receipt51_chunk199, pack_E6970Receipt51_chunk200, pack_E6970Receipt51_chunk201, pack_E6970Receipt51_chunk202, pack_E6970Receipt51_chunk203, pack_E6970Receipt51_chunk204, pack_E6970Receipt51_chunk205, pack_E6970Receipt51_chunk206, pack_E6970Receipt51_chunk207, pack_E6970Receipt51_chunk208, pack_E6970Receipt51_chunk209, pack_E6970Receipt51_chunk210, pack_E6970Receipt51_chunk211, pack_E6970Receipt51_chunk212, pack_E6970Receipt51_chunk213, pack_E6970Receipt51_chunk214, pack_E6970Receipt51_chunk215, pack_E6970Receipt51_chunk216, pack_E6970Receipt51_chunk217, pack_E6970Receipt51_chunk218, pack_E6970Receipt51_chunk219, pack_E6970Receipt51_chunk220, pack_E6970Receipt51_chunk221, pack_E6970Receipt51_chunk222, pack_E6970Receipt51_chunk223, pack_E6970Receipt51_chunk224, pack_E6970Receipt51_chunk225, pack_E6970Receipt51_chunk226, pack_E6970Receipt51_chunk227, pack_E6970Receipt51_chunk228, pack_E6970Receipt51_chunk229, pack_E6970Receipt51_chunk230, pack_E6970Receipt51_chunk231, pack_E6970Receipt51_chunk232, pack_E6970Receipt51_chunk233, pack_E6970Receipt51_chunk234, pack_E6970Receipt51_chunk235, pack_E6970Receipt51_chunk236, pack_E6970Receipt51_chunk237, pack_E6970Receipt51_chunk238, pack_E6970Receipt51_chunk239, pack_E6970Receipt51_chunk240, pack_E6970Receipt51_chunk241, pack_E6970Receipt51_chunk242, pack_E6970Receipt51_chunk243, pack_E6970Receipt51_chunk244, pack_E6970Receipt51_chunk245, pack_E6970Receipt51_chunk246, pack_E6970Receipt51_chunk247, pack_E6970Receipt51_chunk248, pack_E6970Receipt51_chunk249, pack_E6970Receipt51_chunk250]
def rows51 := rowsFrom pack_E6970Receipt51_chunks
theorem good51 : ∀ r ∈ rows51, good 51 r = true := rowsFrom_good pack_E6970Receipt51_chunks
theorem sorted51 : rows51.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt51_chunks 0 (by decide +kernel)).1
theorem mass51 (i : Fin 61) :
    bandCount 51 (i.val : ℤ) 60 16 ≤ (rows51.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt51_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 51 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt51_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total51 : (rows51.map (price 51)).sum = 405502 :=
  (total_eq pack_E6970Receipt51_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt51

section Pack_E6970Receipt52

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt52_chunk0 := witnessA6966Final 52 60 0 960008 960078 32 3870
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk1 := witnessA6966Final 52 60 32 960079 960149 32 3708
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk2 := witnessA6966Final 52 60 64 960150 960257 32 3648
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk3 := witnessA6966Final 52 60 96 960258 960328 32 3742
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk4 := witnessA6966Final 52 60 128 960329 960401 32 3508
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk5 := witnessA6966Final 52 60 160 960402 960519 32 3456
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk6 := witnessA6966Final 52 60 192 960520 960643 32 3266
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk7 := witnessA6966Final 52 60 224 960644 960773 32 3136
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk8 := witnessA6966Final 52 60 256 960774 960963 32 2914
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk9 := witnessA6966Final 52 60 288 960964 961030 11 931
  0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk10 := witnessRule 52 59 0 970007 970077 32 3692
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk11 := witnessRule 52 59 32 970078 970147 32 3514
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk12 := witnessRule 52 59 64 970148 970217 32 3388
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk13 := witnessRule 52 59 96 970256 970327 32 3554
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk14 := witnessRule 52 59 128 970328 970400 32 3278
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk15 := witnessRule 52 59 160 970401 970519 32 3214
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk16 := witnessRule 52 59 192 970520 970644 32 3036
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk17 := witnessRule 52 59 224 970645 970775 32 2882
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk18 := witnessRule 52 59 256 970776 970967 32 2654
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk19 := witnessRule 52 59 288 971024 971029 6 480
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk20 := witnessRule 52 58 0 980006 980075 32 3502
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk21 := witnessRule 52 58 32 980076 980145 32 3354
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk22 := witnessRule 52 58 64 980146 980214 32 3228
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk23 := witnessRule 52 58 96 980215 980325 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk24 := witnessRule 52 58 128 980326 980399 32 3080
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk25 := witnessRule 52 58 160 980400 980519 32 2980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk26 := witnessRule 52 58 192 980520 980645 32 2810
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk27 := witnessRule 52 58 224 980646 980777 32 2630
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk28 := witnessRule 52 58 256 980778 981027 32 2467
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk29 := witnessRule 52 58 288 981028 981029 2 147
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk30 := witnessRule 52 57 0 990005 990074 32 3352
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk31 := witnessRule 52 57 32 990075 990143 32 3174
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk32 := witnessRule 52 57 64 990144 990213 32 3014
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk33 := witnessRule 52 57 96 990214 990325 32 3026
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk34 := witnessRule 52 57 128 990326 990399 32 2836
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk35 := witnessRule 52 57 160 990400 990520 32 2759
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk36 := witnessRule 52 57 192 990521 990647 32 2587
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk37 := witnessRule 52 57 224 990648 990833 32 2437
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk38 := witnessRule 52 57 256 990834 991028 28 2039
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk39 := witnessRule 52 56 0 1000004 1000072 32 3190
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk40 := witnessRule 52 56 32 1000073 1000141 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk41 := witnessRule 52 56 64 1000142 1000211 32 2807
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk42 := witnessRule 52 56 96 1000212 1000324 32 2785
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk43 := witnessRule 52 56 128 1000325 1000399 32 2636
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk44 := witnessRule 52 56 160 1000400 1000521 32 2558
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk45 := witnessRule 52 56 192 1000522 1000649 32 2409
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk46 := witnessRule 52 56 224 1000650 1000836 32 2305
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk47 := witnessRule 52 56 256 1000837 1001028 23 1617
  0x7ffeff 0xb99a (by decide +kernel)
private def pack_E6970Receipt52_chunk48 := witnessRule 52 55 0 1010003 1010071 32 3075
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk49 := witnessRule 52 55 32 1010072 1010140 32 2818
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk50 := witnessRule 52 55 64 1010141 1010211 32 2617
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk51 := witnessRule 52 55 96 1010212 1010325 32 2609
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk52 := witnessRule 52 55 128 1010326 1010400 32 2437
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk53 := witnessRule 52 55 160 1010401 1010523 32 2387
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk54 := witnessRule 52 55 192 1010524 1010652 32 2273
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk55 := witnessRule 52 55 224 1010704 1010896 32 2213
  0xf7ffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt52_chunk56 := witnessRule 52 55 256 1010897 1011027 16 1089
  0xfffb 0xba1a (by decide +kernel)
private def pack_E6970Receipt52_chunk57 := witnessRule 52 54 0 1020002 1020069 32 2967
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk58 := witnessRule 52 54 32 1020070 1020139 32 2652
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk59 := witnessRule 52 54 64 1020140 1020210 32 2457
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk60 := witnessRule 52 54 96 1020211 1020325 32 2434
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk61 := witnessRule 52 54 128 1020326 1020401 32 2295
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk62 := witnessRule 52 54 160 1020402 1020525 32 2253
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk63 := witnessRule 52 54 192 1020526 1020706 32 2179
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk64 := witnessRule 52 54 224 1020707 1020901 32 2126
  0xef9fb7ff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt52_chunk65 := witnessRule 52 54 256 1020902 1021027 10 663
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk66 := witnessRule 52 53 0 1030001 1030069 32 2851
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk67 := witnessRule 52 53 32 1030070 1030139 32 2470
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk68 := witnessRule 52 53 64 1030140 1030211 32 2319
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk69 := witnessRule 52 53 96 1030212 1030327 32 2290
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk70 := witnessRule 52 53 128 1030328 1030449 32 2188
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk71 := witnessRule 52 53 160 1030450 1030577 32 2141
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk72 := witnessRule 52 53 192 1030578 1030711 32 2087
  0x6fffffff 0x5cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt52_chunk73 := witnessRule 52 53 224 1030712 1031024 32 2055
  0xffdf3e5f 0x5d8d0b8b29b27164362e4c86c9c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt52_chunk74 := witnessRule 52 53 256 1031025 1031026 2 131
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk75 := witnessRule 52 52 0 1040000 1040068 32 2733
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk76 := witnessRule 52 52 32 1040069 1040139 32 2341
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk77 := witnessRule 52 52 64 1040140 1040211 32 2202
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk78 := witnessRule 52 52 96 1040212 1040328 32 2172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk79 := witnessRule 52 52 128 1040329 1040451 32 2096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk80 := witnessRule 52 52 160 1040452 1040580 32 2046
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk81 := witnessRule 52 52 192 1040581 1040769 32 2007
  0x793edbff 0x375342e6c86c9cd8cd9b8b21b47163362e8c66cdc98cdab99a (by decide +kernel)
private def pack_E6970Receipt52_chunk82 := witnessRule 52 52 224 1040770 1041026 27 1687
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt52_chunk83 := witnessRule 52 51 0 1050000 1050069 32 2584
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk84 := witnessRule 52 51 32 1050070 1050140 32 2204
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk85 := witnessRule 52 51 64 1050141 1050213 32 2093
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk86 := witnessRule 52 51 96 1050256 1050331 32 2076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk87 := witnessRule 52 51 128 1050332 1050455 32 2003
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk88 := witnessRule 52 51 160 1050456 1050585 32 1960
  0x6dffffff 0x2eac66cdcd8cdab8b19b (by decide +kernel)
private def pack_E6970Receipt52_chunk89 := witnessRule 52 51 192 1050586 1050775 32 1934
  0xf0f0792f 0x5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b27463366e4c86d1c98cdaba1a (by decide +kernel)
private def pack_E6970Receipt52_chunk90 := witnessRule 52 51 224 1050832 1051025 18 1098
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt52_chunk91 := witnessRule 52 50 0 1060000 1060069 32 2428
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk92 := witnessRule 52 50 32 1060070 1060141 32 2094
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk93 := witnessRule 52 50 64 1060142 1060257 32 2007
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk94 := witnessRule 52 50 96 1060258 1060333 32 1965
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk95 := witnessRule 52 50 128 1060334 1060458 32 1918
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk96 := witnessRule 52 50 160 1060459 1060641 32 1887
  0x3927b6df 0x571633108aea685d590d93ab19b37364368e6c66d5c590db38b19b17663366e8c66d5c98cdbb99a (by decide +kernel)
private def pack_E6970Receipt52_chunk97 := witnessRule 52 50 192 1060642 1060837 32 1871
  0xffe3c1e0 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b27464366e6c66210dc994da39321b (by decide +kernel)
private def pack_E6970Receipt52_chunk98 := witnessRule 52 50 224 1060896 1061025 10 602
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk99 := witnessRule 52 49 0 1070000 1070070 32 2288
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk100 := witnessRule 52 49 32 1070071 1070142 32 1987
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk101 := witnessRule 52 49 64 1070143 1070259 32 1919
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk102 := witnessRule 52 49 96 1070260 1070336 32 1867
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk103 := witnessRule 52 49 128 1070337 1070462 32 1841
  0xedb7ffff 0x17763366eac66d5cd8cdbb8b19b (by decide +kernel)
private def pack_E6970Receipt52_chunk104 := witnessRule 52 49 160 1070512 1070646 32 1822
  0x81e01c92 0xba331b27465366e6c86210dc998da38b29884477342eaca6c9d590d9ba31988437365368e6c86d5c98cc422b8b29b67431062ecc86c9d98cd9ba321b4746336ae4c86d9c98cdbba1a (by decide +kernel)
private def pack_E6970Receipt52_chunk105 := witnessRule 52 49 192 1070647 1070962 32 1831
  0xffffef87 0xbd1a17367364e4cc62109c5a0d9bb9883 (by decide +kernel)
private def pack_E6970Receipt52_chunk106 := witnessRule 52 49 224 1071024 1071024 1 60
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk107 := witnessRule 52 48 0 1080000 1080070 32 2154
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk108 := witnessRule 52 48 32 1080071 1080143 32 1894
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk109 := witnessRule 52 48 64 1080144 1080261 32 1835
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk110 := witnessRule 52 48 96 1080262 1080385 32 1787
  0xbfffffff 0x4b99a (by decide +kernel)
private def pack_E6970Receipt52_chunk111 := witnessRule 52 48 128 1080386 1080515 32 1773
  0xe493b6d 0x573633108ae4ca6d9c590c4233b1a17764364eec66cdd590da3ab19b5736436ce6c66ddc590dc39988317863366ecc66d5d18cdbb9319b (by decide +kernel)
private def pack_E6970Receipt52_chunk112 := witnessRule 52 48 160 1080516 1080705 32 1751
  0x7e0f01e0 0x5c5a8d8ba339b2736631084e4d06cdc59cc421bc9a17566364eaca6cdd190c421b9b31b4726531088e2ce6d5d8c418bb329b27664366eac66210dd194da3a321b (by decide +kernel)
private def pack_E6970Receipt52_chunk113 := witnessRule 52 48 192 1080706 1081024 25 1401
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk114 := witnessRule 52 47 0 1090000 1090071 32 2036
  0x5ffffaff 0x97163376e28a1c98cdcba1a (by decide +kernel)
private def pack_E6970Receipt52_chunk115 := witnessRule 52 47 32 1090072 1090144 32 1804
  0xfff3ffff 0x29ccd5b8a2 (by decide +kernel)
private def pack_E6970Receipt52_chunk116 := witnessRule 52 47 64 1090145 1090263 32 1756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk117 := witnessRule 52 47 96 1090264 1090388 32 1718
  0x476db7ff 0x33a319b77264370e2c662121d4d0bcb19b3776336aeac66ddcd8cdcb8b19b (by decide +kernel)
private def pack_E6970Receipt52_chunk118 := witnessRule 52 47 128 1090389 1090519 32 1699
  0xf00392 0x2eccc6c9d994d9bab2188437466368e6ca62111c99cdab8b31884578342eeca6c9dd90d9bb31988437565368eac86d5d18cc422b9b29b672643108ce2cc6ddd4c418bc321b27863366ecc86d1d98cdaba321b (by decide +kernel)
private def pack_E6970Receipt52_chunk119 := witnessRule 52 47 160 1090520 1090711 32 1696
  0xfffc7c0f 0xb9351b2716931084f6685d59cd93a33188427368366e4ce6210dc5a4da3c1883 (by decide +kernel)
private def pack_E6970Receipt52_chunk120 := witnessRule 52 47 192 1090768 1090961 16 883
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk121 := witnessRule 52 46 0 1100000 1100071 32 1925
  0x4fffaabf 0x87165376e2a20edc492bb319b6746436ee4ca6e9c5854425b892 (by decide +kernel)
private def pack_E6970Receipt52_chunk122 := witnessRule 52 46 32 1100072 1100145 32 1723
  0xffabfff5 0x3ba319b87264372ea699d58cdbb9b21b (by decide +kernel)
private def pack_E6970Receipt52_chunk123 := witnessRule 52 46 64 1100146 1100265 32 1684
  0xb6bffeaf 0xaecc66ddd18cdcb9319ba74350e6c66e5c590ddb8a09b (by decide +kernel)
private def pack_E6970Receipt52_chunk124 := witnessRule 52 46 96 1100266 1100391 32 1649
  0xe490ed 0x37665368ecc86d5d58cc422ba329b673643108ce4cc6ddc594c423bb9a17964364f2c66cddd90da3bb19b5756436ceac66ddcd90dc3931988487165372e8620c5e98cd9bc319b (by decide +kernel)
private def pack_E6970Receipt52_chunk125 := witnessRule 52 46 128 1100392 1100523 32 1631
  0xf80f0078 0x2ecce6c9d598c4213a341b3736731086e4d26d1c5a0c4223d1a17766364eeca6cdd990c421bab31b4746531088e6ce6d5c998c422b8b41b67731062f0ca6c9e190d9bbb19884 (by decide +kernel)
private def pack_E6970Receipt52_chunk126 := witnessRule 52 46 160 1100576 1100773 32 1660
  0xfffffbf0 0xbe9a1736a364e4d262109c5acd9bd1883 (by decide +kernel)
private def pack_E6970Receipt52_chunk127 := witnessRule 52 46 192 1100832 1100960 8 437
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk128 := witnessRule 52 45 0 1110000 1110072 32 1831
  0x87faa81f 0x25c98544c42cb8b0a99ca715231096e2a28c9e98cd9bc321b4766536eeac2a2121cd8544c42c3930a99c9716152310b2e2a86edc95538a093 (by decide +kernel)
private def pack_E6970Receipt52_chunk129 := witnessRule 52 45 32 1110073 1110146 32 1641
  0xfd547faa 0x8f0c66d5d990db3a329b9736151094e2c2a262169c54cddb92237963368eec86d5d594dc3a30a884 (by decide +kernel)
private def pack_E6970Receipt52_chunk130 := witnessRule 52 45 64 1110147 1110267 32 1615
  0x920eda2b 0x1bc321b4786336aecc86d9d98cdbba321b8736331090e4ca6e5c590c424bb1a17b63366f2c66d5dd8cdb3ab21b774633108ee6ca6e9c9854425b8a89884 (by decide +kernel)
private def pack_E6970Receipt52_chunk131 := witnessRule 52 45 96 1110268 1110394 32 1581
  0x801e001c 0x17866364f0ca6cddd90c421bb331b4756531088e8ce6d5cd98c422b9341b671673108cf2685e594d93cb21b3786331086eeca6d1dd90dabb3198845756536ce8c862119cd98dbb932988477167370ec620c5e990d93d319b (by decide +kernel)
private def pack_E6970Receipt52_chunk132 := witnessRule 52 45 128 1110395 1110580 32 1578
  0xefe0f807 0x5c5b4d8ba351b2736931084e4d66cdc5a8c421be1a17767364eccc62109d5a0d9ba33988437369368e4d062111c5a8dabc9883 (by decide +kernel)
private def pack_E6970Receipt52_chunk133 := witnessRule 52 45 160 1110581 1110960 32 1642
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk134 := witnessRule 52 44 0 1120000 1120072 32 1737
  0x3aa801f 0x7736154392e6c4ae1c58554e538b1289cb7251076e2824f98556321a17a65368f2c2a2115dd8544c42abb30a99c6756152310ace8c2a8721d1895bb930aa9c9726251394e2c4a2129c948ddb8a093 (by decide +kernel)
private def pack_E6970Receipt52_chunk135 := witnessRule 52 44 32 1120073 1120147 32 1568
  0xe8a03aa8 0x2f8c66c9e990d9bcb198843786536ceec2a211dd58544c42bba30a99c8736152310b0e4c2a8729c9895cb8aa9bb725137ac6685ed90d93cb29b578615108cecc2a262159d5854ce3ba30a91885 (by decide +kernel)
private def pack_E6970Receipt52_chunk136 := witnessRule 52 44 64 1120192 1120269 32 1547
  0x80039040 0x5e994d93d321b3796331086f0ca6d1e190dabbb198845766536ceac862119d198dbb9b2988477267370e2cc62121e0d0bdb21b27b63366f2c86d1e18cc4223bb29b576643108aeacc6e1d18544c42c39b0a99c9726152310b2e2c2a8729c54cc420c538a09c (by decide +kernel)
private def pack_E6970Receipt52_chunk137 := witnessRule 52 44 96 1120270 1120397 32 1519
  0xf803c007 0x17867364eecc62109d9a0d9bab3988437469368e6d062111c9a8dab8b4988457b342f2cc6c9e594d9bc32188437766368ecca62111d59cdaba3318845736836ce4ce62119c5a4dbbc1883 (by decide +kernel)
private def pack_E6970Receipt52_chunk138 := witnessRule 52 44 128 1120448 1120584 32 1531
  0xffff8fc0 0xb9369b2716c31084fc685d5a8d93a3498842736b366e4d46210dc5b0da3d9883 (by decide +kernel)
private def pack_E6970Receipt52_chunk139 := witnessRule 52 44 160 1120640 1120897 24 1210
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk140 := witnessRule 52 43 0 1130000 1130073 32 1654
  0x1e8000f 0xeeac4a2721d189442439b1291c9726251310b2e2c4a6729c948c425b928a317d6151084f6c2a262149e9854ce1bcb0a91885378615438af0c4ad1d98554e33b31289c775625108ee8c4a4721cd8944c42c3931299c9716252310b2e4a86edcd55b912 (by decide +kernel)
private def pack_E6970Receipt52_chunk141 := witnessRule 52 43 32 1130074 1130193 32 1503
  0x21000540 0x510e2c470a25c4c426b19883c65342f6c862105e998da3cb0a89885478615338aeec2a462155d98550e33ab0a998856746155390e8c4a2725cd894424b931291ca716251310b4e4a66edc5491db912d6152364f8c2a210de98544c429bcb0a99c4786152310a8eec2a8719dd895abab0aa9c (by decide +kernel)
private def pack_E6970Receipt52_chunk142 := witnessRule 52 43 64 1130194 1130271 32 1470
  0xf000e000 0xbd331b27a65366f2c86210de198da3bb298844766736aeacc62115d1a0db39b398846726936ee2d06211de8d0be31988417b65364f4c862109e598d9bc3298843776736aeec2a6719d98548c42b3ab0aa1c7746153310aee6c2aa721c98550c42c38b0ab1c (by decide +kernel)
private def pack_E6970Receipt52_chunk143 := witnessRule 52 43 96 1130320 1130451 32 1470
  0xfc07c00 0xb9b69b2726c31084e2dc6cdf4c418bb351b2756931084e8d66cdcda8c421b9361b4716b31088fa685e59cd93c33188427768366ecce6210dd5a4da3a3418844736a36ae4d262115c5acdb3d1883 (by decide +kernel)
private def pack_E6970Receipt52_chunk144 := witnessRule 52 43 128 1130452 1130644 32 1491
  0xfffffeff 0x2e801a (by decide +kernel)
private def pack_E6970Receipt52_chunk145 := witnessRule 52 43 160 1130645 1130896 16 795
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk146 := witnessRule 52 42 0 1140000 1140073 32 1568
  0x40000f 0xceac4a671dd18948c42bb9b12a1c97363570e2c4aa729c58d44e5b9a883b7241274e2844f98956b0a91884c6154364f8c4ac5e98554e1bd31289c4796251088f0c4a4715dd8944c42abb31299c6756252310ace8c4a8721d18d5bb9312a9c9726351394e2c6a2129cd48ddb8a8a094 (by decide +kernel)
private def pack_E6970Receipt52_chunk147 := witnessRule 52 42 32 1140074 1140194 32 1439
  0x18000400 0x143b9311885287716438510e6621318550d8be30a99c27b6152310a4f4c2a870de5854cc429bc30aa9c4776154310a8ecc2ac719d98948e3bab12898857746253390e6c4a462161c98950e4b8b12998859725536512e2a27398544c426b0a99b17c6152310a2f6c2a8709e9854cc4293cb0aa9c479625138af0c4a2115dd8948e33b31289885 (by decide +kernel)
private def pack_E6970Receipt52_chunk148 := witnessRule 52 42 64 1140195 1140321 32 1411
  0x3e003000 0x238b69b57c31062f4ce6c9e598c4213c341b3776731086ecd26d1d5a0c4223a351b573693108ae4d66d9c5a8c4233e1ac6531076ce685e998c420bcb41b3796154388f0c2a662151dd8554e2bb30aa1885575615638ce8c2aa62159cd855ce14339b19c (by decide +kernel)
private def pack_E6970Receipt52_chunk149 := witnessRule 52 42 96 1140322 1140454 32 1409
  0xfbfe0fc0 0x5c5900362e8da6c9cdb0c42139371b3716d31086fe685dda8d93b3498842756b366e8d46210dcdb0da39359884 (by decide +kernel)
private def pack_E6970Receipt52_chunk150 := witnessRule 52 42 128 1140455 1140706 32 1469
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk151 := witnessRule 52 42 160 1140707 1140896 9 443
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk152 := witnessRule 52 41 0 1150000 1150074 32 1488
  0x200007 0x5766253310aaeac4aa71dd58d44e43a31a8848736352392e4c6a262165c58d4ce539a9188418a7251496e2844f98944d8beb1288417c6252384f6c4a262149e9894ce1bcb1291885378625438af0c6ad1d98954e33b31a89c775635108ee8c6a4721cd8d44c42c3931a99c9716352310b2e6a86edd155b8a113 (by decide +kernel)
private def pack_E6970Receipt52_chunk153 := witnessRule 52 41 32 1150075 1150196 32 1376
  0x4000100 0xa15d18cc42942b9b29c2867264310a50ce2cc70a1dd4c426b0a99884c6155362f6c2a862145e98558e13cb0aa98852786157388f0c4a6715dd8948c42abb312a1c6756253310ace8c4aa71dcd8950c42bb9312b1c2877261523a510e2c2a26218a21c54ce0c539208cd6252378c2a86212d8558d93db1291c37a6251310a6f2c4a6711e18948c42a3bb12a1c (by decide +kernel)
private def pack_E6970Receipt52_chunk154 := witnessRule 52 41 64 1150197 1150324 32 1350
  0x7e00e00 0x4e8d862109cdb8d9b93698843716f368fc620c5e1a8d93bb498842766b366ead46210dd1b0da39b598844726d36ae2d862115f8d5b0ab1b17b6155384f4c2a862149e58558e1bc30aa98853776157388ecc2ac62151d58560e1423ab21c (by decide +kernel)
private def pack_E6970Receipt52_chunk155 := witnessRule 52 41 96 1150325 1150458 32 1360
  0xfffff1fe 0x1726400d938b7988427440d0bab69b (by decide +kernel)
private def pack_E6970Receipt52_chunk156 := witnessRule 52 41 128 1150512 1150832 32 1460
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk157 := witnessRule 52 41 160 1150833 1150833 1 49
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk158 := witnessRule 52 40 0 1160000 1160074 32 1408
  0x200007 0x577635238cecc6a262159d58d4ce3ba31a918857736354390e4c6a662161c58d54e14438b1289d2897251096e2a48253989481eb1291884c6254362f6c4a662145e98954e1bd31a89c4796351088f0c6a4715dd8d44c42abb31a99c6756352310ace8c6a8721d1915bb931aa9c9726451394e2c8a2129d148ddb928a094 (by decide +kernel)
private def pack_E6970Receipt52_chunk159 := witnessRule 52 40 32 1160075 1160197 32 1313
  0x3000000 0xa0dd598e1423a32988528473673850ae4cc6214a15c5a0e1433b9884c6254376c2ac621298560d93d312a1c3796253310a6f0c4aa711dd8950c42a3b312b1c5756255310aae8c4ae70a15d1854ce94339b0a918862867261543a50ee2c2a66218a1dc554e1c438988cd62513209ac4a66c5f18948c428bdb12a1c27a6253310a4f2c4aa70de18950c429bbb12b1c (by decide +kernel)
private def pack_E6970Receipt52_chunk160 := witnessRule 52 40 64 1160198 1160326 32 1291
  0xe1fe0308 0x5cd900364e4de62109c5910366e8018831766d364ead862109d1b8d9b9b698843726f368e2dc62111d00358c2aa6212d855cd8bd30ab18851796158384eec2b270a09dd94e141bb321885 (by decide +kernel)
private def pack_E6970Receipt52_chunk161 := witnessRule 52 40 96 1160327 1160515 32 1328
  0xffffffbf 0x2e981a (by decide +kernel)
private def pack_E6970Receipt52_chunk162 := witnessRule 52 40 128 1160516 1160832 26 1166
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk163 := witnessRule 52 39 0 1170000 1170075 32 1332
  0x100003 0x23c31a91885477635438aecc6a662155d58d54e33a31aa188567363563850ce6c4a474a1dc98944c43143b8b1299d2887252310a512e2a2823758d44c42631a99b17c6352384f6c6a262149e98d4ce1bcb1a918853786354388eec6a662151d98d54e33b32289c775645108ee8c8a4721cd9144c42c3932299c9716452310b2e8a86ca25cd5db92113 (by decide +kernel)
private def pack_E6970Receipt52_chunk164 := witnessRule 52 39 32 1170076 1170199 32 1249
  0x800040 0xa05dd9ce1413b331885282756838506e8ce6214a0dcda4e14239341885284716a3850af262131894cc826312a9b17b6254310a2f4c4ac709e58954c4293c312b9c3776256310a6ecc4b070a0dd98550e9423ab0a998862847461553a50ae6c2a86218a15c98558e94338b0aa988628671573890ce66f58948c826312a1884b6256362f4c4aa62145e5895ce1bcb1a99c (by decide +kernel)
private def pack_E6970Receipt52_chunk165 := witnessRule 52 39 64 1170200 1170329 32 1239
  0xff7fe0eb 0x5c5930362e8c801b2736f31084e4c881b3716400c421ba406ad8558c824b0ad1b (by decide +kernel)
private def pack_E6970Receipt52_chunk166 := witnessRule 52 39 96 1170330 1170519 32 1304
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk167 := witnessRule 52 39 128 1170576 1170832 19 840
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk168 := witnessRule 52 38 0 1180000 1180075 32 1258
  0x3 0xde18d50c429bbb1ab1c4766355310a8eac6ae70a11d5894ce942ba312918862857362543a50ce4c4a66218a19c58954e943b92a18853877151423a314e482423758d4c1eb1a91884c6354362f6c6a662145e98d54e13cb1aa18852786356388f0c8a4715dd9144c42abb32299c6756452310ace8c8a871dcd914cc42bb9322a9c2877263513a510e2c6a214a21cd48e0c53928a095 (by decide +kernel)
private def pack_E6970Receipt52_chunk169 := witnessRule 52 38 32 1180076 1180200 32 1186
  0xe0600000 0x502ead470a09d1a4c4294139b59c283726a310a506e2d870a11ecc426312a1904b625631094c4b06c5e5895cc428bc312c9c2817861553a504eec2a86218a09d98558e941bab0aa98862837461573a508e6c2ac6218a11c98560ea4239321c4857163310a90aea6f58944d02631a99884b6355362f6c6a8709e98d4cc4293cb1aa9c (by decide +kernel)
private def pack_E6970Receipt52_chunk170 := witnessRule 52 38 64 1180201 1180331 32 1199
  0xfffffe3f 0xb932606c9c592031084ea01a (by decide +kernel)
private def pack_E6970Receipt52_chunk171 := witnessRule 52 38 96 1180384 1180579 32 1285
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk172 := witnessRule 52 38 128 1180580 1180769 12 521
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk173 := witnessRule 52 37 0 1190000 1190076 32 1185
  0x3 0x5e58d5ce13c31ab1885277635838504eec4a874a0dd9894cc43141bab12a9d284746254310c508e6c4ac74a15c98954c43142b8b12b9d4857161533a90ce2a46214e21c50866b1a89984c6453376c6aa621298d5cd93d32299c3796452310a6f0c8a8711dd914cc42a3b322a9c5756454310aae8c8ac70a15d18d48e94339b1a898862867263533a50ee2c6a46218a1dcd50e1c439288c (by decide +kernel)
private def pack_E6970Receipt52_chunk174 := witnessRule 52 37 32 1190077 1190202 32 1130
  0xfe100810 0xa05cdb4e14139361885282716e38506fa62131894cd025b12a9984a625732092c4b26210a258554c4294430ab9c281776156310c502ecc2b074a09d18564ea413a329c4837364310a906e4cc71211c594c42a423b9bc635233098c6a86212d8d58d8bd31aa9885 (by decide +kernel)
private def pack_E6970Receipt52_chunk175 := witnessRule 52 37 64 1190203 1190386 32 1169
  0xffffffef 0x2eb01a (by decide +kernel)
private def pack_E6970Receipt52_chunk176 := witnessRule 52 37 96 1190387 1190642 32 1269
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk177 := witnessRule 52 37 128 1190643 1190768 5 215
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk178 := witnessRule 52 36 0 1200000 1200076 32 1114
  0x1 0x12c6b26ca258954e140bc312a18862817762563a504ecc4aa6218a09d5895ce941ba312b18862837362583a906e6c2a875211c9854cc4324238b0aa9d4857154310a90ce284623758d541e32291904c6454362f6c8a662145e99154e13cb22a18852786456386eec8aa6214dd9915ce141bb31a99d284756352310c508e8c6a874a15cd8d4cc43142b931aa9d286716354310c50ce6ac71219c948e144b8a8a0908e (by decide +kernel)
private def pack_E6970Receipt52_chunk179 := witnessRule 52 36 32 1200077 1200203 32 1082
  0xffdd5600 0x281716400e5b12a1a84962583308510c2ac6414a198568e240ba339c4827366310a904e4d07120dc59cc42a41bc9bc635135098c6a66612d8d54c82531ab9884 (by decide +kernel)
private def pack_E6970Receipt52_chunk180 := witnessRule 52 36 64 1200204 1200389 32 1141
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk181 := witnessRule 52 36 96 1200390 1200768 31 1216
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk182 := witnessRule 52 35 0 1210000 1210077 32 1048
  0x1 0x14c6ac661258d60c82144b12a19052886256310a50ec4b070a05d9895cc43140bab12c9d4817561553a904e8c2a86219209cd8558ea41b930aa98864837161573a908e2ac6215611c510e632289a04c645332096c8aa62129915cd8bcb22b1885178645838502f0c6a874a09dd8d4cc431413b31aa9d283756354310c506e8c6ac74a11cd8d54c431423931ab9d4847262533a90ae2c4a46219215c950e243b8a90c (by decide +kernel)
private def pack_E6970Receipt52_chunk183 := witnessRule 52 35 32 1210078 1210205 32 1043
  0xffffffc4 0x240b9351c4827169310a904f66f18d48d425b1aa1a04 (by decide +kernel)
private def pack_E6970Receipt52_chunk184 := witnessRule 52 35 64 1210256 1210392 32 1117
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk185 := witnessRule 52 35 96 1210448 1210705 24 921
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk186 := witnessRule 52 34 0 1220000 1220077 32 989
  0x200001 0x298d54d424b1ab9a042896253340a510c4aa6614a1d895cc82943312c98854866155310a90ac2ae71205d18558c43240b9b0ac1d4827161593ad04e2ca71a0dd0c426322b03c645234096c8a8661299158c824b22c18842896354310a510c6ac70a05dd8d54c43140bb31ab9d282756356310c504e8c6b075209d18950ea41b9b12998864837262553a908e2c4a86219211c958e2c2b8a9188d (by decide +kernel)
private def pack_E6970Receipt52_chunk187 := witnessRule 52 34 32 1220078 1220257 32 1009
  0xfffffff8 0x902fa6f18d44dc25b1a99b04 (by decide +kernel)
private def pack_E6970Receipt52_chunk188 := witnessRule 52 34 64 1220258 1220450 32 1093
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk189 := witnessRule 52 34 96 1220451 1220704 18 675
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk190 := witnessRule 52 33 0 1230000 1230078 32 936
  0x555a0009 0x2d8d48e024b1ab1b042886254350a50cc4b066152158558c82a41b0ad1c6817167398c8a26c12d914cd425322a9a04964573308512c6a66614a218d54c82943b1ab988528663593890cc4aa71205d58950c43240ba312b1d482736255310c904e4c4ae7520dc960e341b8aa1c (by decide +kernel)
private def pack_E6970Receipt52_chunk191 := witnessRule 52 33 32 1230079 1230259 32 980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk192 := witnessRule 52 33 64 1230260 1230454 32 1071
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk193 := witnessRule 52 33 96 1230512 1230704 12 443
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk194 := witnessRule 52 32 0 1240000 1240078 32 891
  0xfffe0005 0x18c8b00ed9148dc25322a1b04964563508512c6a46a14a218d50d02943b1ab19852866358320a90cc4a864152158958c42a42312c1c481736257310c902e4c4b275a05c98554eb4138ab1c (by decide +kernel)
private def pack_E6970Receipt52_chunk195 := witnessRule 52 32 32 1240128 1240261 32 952
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk196 := witnessRule 52 32 64 1240262 1240515 32 1051
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk197 := witnessRule 52 32 96 1240516 1240641 6 217
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk198 := witnessRule 52 31 0 1250000 1250128 32 853
  0xffff0003 0x2d9144e42532299c04964553708512c6a26e14a218d4cd82943b1aa9a852866357340a90cc4a668152158954cc2a42312b99054836259310ad06c2aa6215a09855ce340b8b0ab1886 (by decide +kernel)
private def pack_E6970Receipt52_chunk199 := witnessRule 52 31 32 1250129 1250263 32 924
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk200 := witnessRule 52 31 64 1250264 1250640 32 1038
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk201 := witnessRule 52 30 0 1260000 1260129 32 818
  0xfffffd55 0x14331ab1b054856254350a906c4b06615a098558c82b40ad1b (by decide +kernel)
private def pack_E6970Receipt52_chunk202 := witnessRule 52 30 32 1260130 1260265 32 895
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk203 := witnessRule 52 30 64 1260320 1260640 27 852
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk204 := witnessRule 52 29 0 1270000 1270130 32 788
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk205 := witnessRule 52 29 32 1270131 1270322 32 870
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk206 := witnessRule 52 29 64 1270323 1270577 21 642
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk207 := witnessRule 52 28 0 1280000 1280131 32 757
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk208 := witnessRule 52 28 32 1280132 1280324 32 843
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk209 := witnessRule 52 28 64 1280325 1280576 16 475
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk210 := witnessRule 52 27 0 1290000 1290132 32 727
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk211 := witnessRule 52 27 32 1290133 1290384 32 819
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk212 := witnessRule 52 27 64 1290385 1290576 11 319
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk213 := witnessRule 52 26 0 1300000 1300133 32 696
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk214 := witnessRule 52 26 32 1300134 1300387 32 795
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk215 := witnessRule 52 26 64 1300388 1300513 6 169
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk216 := witnessRule 52 25 0 1310000 1310134 32 666
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk217 := witnessRule 52 25 32 1310135 1310450 32 776
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk218 := witnessRule 52 25 64 1310512 1310512 1 28
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk219 := witnessRule 52 24 0 1320000 1320135 32 635
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk220 := witnessRule 52 24 32 1320136 1320512 29 678
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk221 := witnessRule 52 23 0 1330000 1330136 32 605
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk222 := witnessRule 52 23 32 1330192 1330449 24 537
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk223 := witnessRule 52 22 0 1340000 1340192 32 575
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk224 := witnessRule 52 22 32 1340193 1340448 20 427
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk225 := witnessRule 52 21 0 1350000 1350194 32 547
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk226 := witnessRule 52 21 32 1350195 1350448 16 327
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk227 := witnessRule 52 20 0 1360000 1360195 32 517
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk228 := witnessRule 52 20 32 1360196 1360385 12 233
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk229 := witnessRule 52 19 0 1370000 1370197 32 489
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk230 := witnessRule 52 19 32 1370256 1370384 8 149
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk231 := witnessRule 52 18 0 1380000 1380257 32 461
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk232 := witnessRule 52 18 32 1380258 1380384 5 89
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk233 := witnessRule 52 17 0 1390000 1390320 32 436
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk234 := witnessRule 52 17 32 1390321 1390321 1 17
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk235 := witnessRule 52 16 0 1400000 1400320 30 378
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk236 := witnessRule 52 15 0 1410000 1410320 27 312
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk237 := witnessRule 52 14 0 1420000 1420257 24 249
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk238 := witnessRule 52 13 0 1430000 1430256 21 195
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk239 := witnessRule 52 12 0 1440000 1440256 19 156
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk240 := witnessRule 52 11 0 1450000 1450193 16 113
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk241 := witnessRule 52 10 0 1460000 1460192 14 83
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk242 := witnessRule 52 9 0 1470000 1470192 12 59
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk243 := witnessRule 52 8 0 1480000 1480129 10 37
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk244 := witnessRule 52 7 0 1490000 1490128 8 21
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk245 := witnessRule 52 6 0 1500000 1500128 7 11
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk246 := witnessRule 52 5 0 1510000 1510065 5 2
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk247 := witnessRule 52 4 0 1520000 1520064 4 0
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk248 := witnessRule 52 3 0 1530000 1530064 3 0
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk249 := witnessRule 52 2 0 1540000 1540001 2 0
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt52_chunk250 := witnessRule 52 1 0 1550000 1550000 1 0
  0x1 0x0 (by decide +kernel)
private def chunk251 := witnessRule 52 0 0 1560000 1560000 1 0
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt52_chunks : List (Chunk 52) := [pack_E6970Receipt52_chunk0, pack_E6970Receipt52_chunk1, pack_E6970Receipt52_chunk2, pack_E6970Receipt52_chunk3, pack_E6970Receipt52_chunk4, pack_E6970Receipt52_chunk5, pack_E6970Receipt52_chunk6, pack_E6970Receipt52_chunk7, pack_E6970Receipt52_chunk8, pack_E6970Receipt52_chunk9, pack_E6970Receipt52_chunk10, pack_E6970Receipt52_chunk11, pack_E6970Receipt52_chunk12, pack_E6970Receipt52_chunk13, pack_E6970Receipt52_chunk14, pack_E6970Receipt52_chunk15, pack_E6970Receipt52_chunk16, pack_E6970Receipt52_chunk17, pack_E6970Receipt52_chunk18, pack_E6970Receipt52_chunk19, pack_E6970Receipt52_chunk20, pack_E6970Receipt52_chunk21, pack_E6970Receipt52_chunk22, pack_E6970Receipt52_chunk23, pack_E6970Receipt52_chunk24, pack_E6970Receipt52_chunk25, pack_E6970Receipt52_chunk26, pack_E6970Receipt52_chunk27, pack_E6970Receipt52_chunk28, pack_E6970Receipt52_chunk29, pack_E6970Receipt52_chunk30, pack_E6970Receipt52_chunk31, pack_E6970Receipt52_chunk32, pack_E6970Receipt52_chunk33, pack_E6970Receipt52_chunk34, pack_E6970Receipt52_chunk35, pack_E6970Receipt52_chunk36, pack_E6970Receipt52_chunk37, pack_E6970Receipt52_chunk38, pack_E6970Receipt52_chunk39, pack_E6970Receipt52_chunk40, pack_E6970Receipt52_chunk41, pack_E6970Receipt52_chunk42, pack_E6970Receipt52_chunk43, pack_E6970Receipt52_chunk44, pack_E6970Receipt52_chunk45, pack_E6970Receipt52_chunk46, pack_E6970Receipt52_chunk47, pack_E6970Receipt52_chunk48, pack_E6970Receipt52_chunk49, pack_E6970Receipt52_chunk50, pack_E6970Receipt52_chunk51, pack_E6970Receipt52_chunk52, pack_E6970Receipt52_chunk53, pack_E6970Receipt52_chunk54, pack_E6970Receipt52_chunk55, pack_E6970Receipt52_chunk56, pack_E6970Receipt52_chunk57, pack_E6970Receipt52_chunk58, pack_E6970Receipt52_chunk59, pack_E6970Receipt52_chunk60, pack_E6970Receipt52_chunk61, pack_E6970Receipt52_chunk62, pack_E6970Receipt52_chunk63, pack_E6970Receipt52_chunk64, pack_E6970Receipt52_chunk65, pack_E6970Receipt52_chunk66, pack_E6970Receipt52_chunk67, pack_E6970Receipt52_chunk68, pack_E6970Receipt52_chunk69, pack_E6970Receipt52_chunk70, pack_E6970Receipt52_chunk71, pack_E6970Receipt52_chunk72, pack_E6970Receipt52_chunk73, pack_E6970Receipt52_chunk74, pack_E6970Receipt52_chunk75, pack_E6970Receipt52_chunk76, pack_E6970Receipt52_chunk77, pack_E6970Receipt52_chunk78, pack_E6970Receipt52_chunk79, pack_E6970Receipt52_chunk80, pack_E6970Receipt52_chunk81, pack_E6970Receipt52_chunk82, pack_E6970Receipt52_chunk83, pack_E6970Receipt52_chunk84, pack_E6970Receipt52_chunk85, pack_E6970Receipt52_chunk86, pack_E6970Receipt52_chunk87, pack_E6970Receipt52_chunk88, pack_E6970Receipt52_chunk89, pack_E6970Receipt52_chunk90, pack_E6970Receipt52_chunk91, pack_E6970Receipt52_chunk92, pack_E6970Receipt52_chunk93, pack_E6970Receipt52_chunk94, pack_E6970Receipt52_chunk95, pack_E6970Receipt52_chunk96, pack_E6970Receipt52_chunk97, pack_E6970Receipt52_chunk98, pack_E6970Receipt52_chunk99, pack_E6970Receipt52_chunk100, pack_E6970Receipt52_chunk101, pack_E6970Receipt52_chunk102, pack_E6970Receipt52_chunk103, pack_E6970Receipt52_chunk104, pack_E6970Receipt52_chunk105, pack_E6970Receipt52_chunk106, pack_E6970Receipt52_chunk107, pack_E6970Receipt52_chunk108, pack_E6970Receipt52_chunk109, pack_E6970Receipt52_chunk110, pack_E6970Receipt52_chunk111, pack_E6970Receipt52_chunk112, pack_E6970Receipt52_chunk113, pack_E6970Receipt52_chunk114, pack_E6970Receipt52_chunk115, pack_E6970Receipt52_chunk116, pack_E6970Receipt52_chunk117, pack_E6970Receipt52_chunk118, pack_E6970Receipt52_chunk119, pack_E6970Receipt52_chunk120, pack_E6970Receipt52_chunk121, pack_E6970Receipt52_chunk122, pack_E6970Receipt52_chunk123, pack_E6970Receipt52_chunk124, pack_E6970Receipt52_chunk125, pack_E6970Receipt52_chunk126, pack_E6970Receipt52_chunk127, pack_E6970Receipt52_chunk128, pack_E6970Receipt52_chunk129, pack_E6970Receipt52_chunk130, pack_E6970Receipt52_chunk131, pack_E6970Receipt52_chunk132, pack_E6970Receipt52_chunk133, pack_E6970Receipt52_chunk134, pack_E6970Receipt52_chunk135, pack_E6970Receipt52_chunk136, pack_E6970Receipt52_chunk137, pack_E6970Receipt52_chunk138, pack_E6970Receipt52_chunk139, pack_E6970Receipt52_chunk140, pack_E6970Receipt52_chunk141, pack_E6970Receipt52_chunk142, pack_E6970Receipt52_chunk143, pack_E6970Receipt52_chunk144, pack_E6970Receipt52_chunk145, pack_E6970Receipt52_chunk146, pack_E6970Receipt52_chunk147, pack_E6970Receipt52_chunk148, pack_E6970Receipt52_chunk149, pack_E6970Receipt52_chunk150, pack_E6970Receipt52_chunk151, pack_E6970Receipt52_chunk152, pack_E6970Receipt52_chunk153, pack_E6970Receipt52_chunk154, pack_E6970Receipt52_chunk155, pack_E6970Receipt52_chunk156, pack_E6970Receipt52_chunk157, pack_E6970Receipt52_chunk158, pack_E6970Receipt52_chunk159, pack_E6970Receipt52_chunk160, pack_E6970Receipt52_chunk161, pack_E6970Receipt52_chunk162, pack_E6970Receipt52_chunk163, pack_E6970Receipt52_chunk164, pack_E6970Receipt52_chunk165, pack_E6970Receipt52_chunk166, pack_E6970Receipt52_chunk167, pack_E6970Receipt52_chunk168, pack_E6970Receipt52_chunk169, pack_E6970Receipt52_chunk170, pack_E6970Receipt52_chunk171, pack_E6970Receipt52_chunk172, pack_E6970Receipt52_chunk173, pack_E6970Receipt52_chunk174, pack_E6970Receipt52_chunk175, pack_E6970Receipt52_chunk176, pack_E6970Receipt52_chunk177, pack_E6970Receipt52_chunk178, pack_E6970Receipt52_chunk179, pack_E6970Receipt52_chunk180, pack_E6970Receipt52_chunk181, pack_E6970Receipt52_chunk182, pack_E6970Receipt52_chunk183, pack_E6970Receipt52_chunk184, pack_E6970Receipt52_chunk185, pack_E6970Receipt52_chunk186, pack_E6970Receipt52_chunk187, pack_E6970Receipt52_chunk188, pack_E6970Receipt52_chunk189, pack_E6970Receipt52_chunk190, pack_E6970Receipt52_chunk191, pack_E6970Receipt52_chunk192, pack_E6970Receipt52_chunk193, pack_E6970Receipt52_chunk194, pack_E6970Receipt52_chunk195, pack_E6970Receipt52_chunk196, pack_E6970Receipt52_chunk197, pack_E6970Receipt52_chunk198, pack_E6970Receipt52_chunk199, pack_E6970Receipt52_chunk200, pack_E6970Receipt52_chunk201, pack_E6970Receipt52_chunk202, pack_E6970Receipt52_chunk203, pack_E6970Receipt52_chunk204, pack_E6970Receipt52_chunk205, pack_E6970Receipt52_chunk206, pack_E6970Receipt52_chunk207, pack_E6970Receipt52_chunk208, pack_E6970Receipt52_chunk209, pack_E6970Receipt52_chunk210, pack_E6970Receipt52_chunk211, pack_E6970Receipt52_chunk212, pack_E6970Receipt52_chunk213, pack_E6970Receipt52_chunk214, pack_E6970Receipt52_chunk215, pack_E6970Receipt52_chunk216, pack_E6970Receipt52_chunk217, pack_E6970Receipt52_chunk218, pack_E6970Receipt52_chunk219, pack_E6970Receipt52_chunk220, pack_E6970Receipt52_chunk221, pack_E6970Receipt52_chunk222, pack_E6970Receipt52_chunk223, pack_E6970Receipt52_chunk224, pack_E6970Receipt52_chunk225, pack_E6970Receipt52_chunk226, pack_E6970Receipt52_chunk227, pack_E6970Receipt52_chunk228, pack_E6970Receipt52_chunk229, pack_E6970Receipt52_chunk230, pack_E6970Receipt52_chunk231, pack_E6970Receipt52_chunk232, pack_E6970Receipt52_chunk233, pack_E6970Receipt52_chunk234, pack_E6970Receipt52_chunk235, pack_E6970Receipt52_chunk236, pack_E6970Receipt52_chunk237, pack_E6970Receipt52_chunk238, pack_E6970Receipt52_chunk239, pack_E6970Receipt52_chunk240, pack_E6970Receipt52_chunk241, pack_E6970Receipt52_chunk242, pack_E6970Receipt52_chunk243, pack_E6970Receipt52_chunk244, pack_E6970Receipt52_chunk245, pack_E6970Receipt52_chunk246, pack_E6970Receipt52_chunk247, pack_E6970Receipt52_chunk248, pack_E6970Receipt52_chunk249, pack_E6970Receipt52_chunk250, chunk251]
def rows52 := rowsFrom pack_E6970Receipt52_chunks
theorem good52 : ∀ r ∈ rows52, good 52 r = true := rowsFrom_good pack_E6970Receipt52_chunks
theorem sorted52 : rows52.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt52_chunks 0 (by decide +kernel)).1
theorem mass52 (i : Fin 61) :
    bandCount 52 (i.val : ℤ) 60 16 ≤ (rows52.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt52_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 52 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt52_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total52 : (rows52.map (price 52)).sum = 401652 :=
  (total_eq pack_E6970Receipt52_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt52

section Pack_E6970Receipt9

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt9_chunk0 := witnessRule 9 27 0 576 576 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk1 := witnessRule 9 26 0 10513 10513 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk2 := witnessRule 9 25 0 20450 20512 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk3 := witnessRule 9 24 0 30387 30512 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk4 := witnessRule 9 23 0 40324 40449 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk5 := witnessRule 9 22 0 50261 50448 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk6 := witnessRule 9 21 0 60198 60448 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk7 := witnessRule 9 20 0 70135 70385 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk8 := witnessRule 9 19 0 80072 80384 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk9 := witnessRule 9 18 0 90009 90384 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk10 := witnessRule 9 17 0 100008 100321 13 1339
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk11 := witnessRule 9 16 0 110007 110320 14 1430
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk12 := witnessRule 9 15 0 120006 120320 15 1517
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk13 := witnessRule 9 14 0 130005 130257 15 1505
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk14 := witnessRule 9 13 0 140004 140256 15 1493
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk15 := witnessRule 9 12 0 150003 150256 15 1469
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk16 := witnessRule 9 11 0 160002 160193 14 1362
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk17 := witnessRule 9 10 0 170001 170192 13 1243
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk18 := witnessRule 9 9 0 180000 180192 12 1128
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk19 := witnessRule 9 8 0 190000 190129 10 918
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk20 := witnessRule 9 7 0 200000 200128 8 716
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk21 := witnessRule 9 6 0 210000 210128 7 605
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk22 := witnessRule 9 5 0 220000 220065 5 423
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk23 := witnessRule 9 4 0 230000 230064 4 328
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk24 := witnessRule 9 3 0 240000 240064 3 237
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk25 := witnessRule 9 2 0 250000 250001 2 154
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk26 := witnessRule 9 1 0 260000 260000 1 75
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt9_chunk27 := witnessRule 9 0 0 270000 270000 1 71
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt9_chunks : List (Chunk 9) := [pack_E6970Receipt9_chunk0, pack_E6970Receipt9_chunk1, pack_E6970Receipt9_chunk2, pack_E6970Receipt9_chunk3, pack_E6970Receipt9_chunk4, pack_E6970Receipt9_chunk5, pack_E6970Receipt9_chunk6, pack_E6970Receipt9_chunk7, pack_E6970Receipt9_chunk8, pack_E6970Receipt9_chunk9, pack_E6970Receipt9_chunk10, pack_E6970Receipt9_chunk11, pack_E6970Receipt9_chunk12, pack_E6970Receipt9_chunk13, pack_E6970Receipt9_chunk14, pack_E6970Receipt9_chunk15, pack_E6970Receipt9_chunk16, pack_E6970Receipt9_chunk17, pack_E6970Receipt9_chunk18, pack_E6970Receipt9_chunk19, pack_E6970Receipt9_chunk20, pack_E6970Receipt9_chunk21, pack_E6970Receipt9_chunk22, pack_E6970Receipt9_chunk23, pack_E6970Receipt9_chunk24, pack_E6970Receipt9_chunk25, pack_E6970Receipt9_chunk26, pack_E6970Receipt9_chunk27]
def rows9 := rowsFrom pack_E6970Receipt9_chunks
theorem good9 : ∀ r ∈ rows9, good 9 r = true := rowsFrom_good pack_E6970Receipt9_chunks
theorem sorted9 : rows9.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt9_chunks 0 (by decide +kernel)).1
theorem mass9 (i : Fin 61) :
    bandCount 9 (i.val : ℤ) 60 16 ≤ (rows9.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt9_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 9 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt9_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total9 : (rows9.map (price 9)).sum = 21560 :=
  (total_eq pack_E6970Receipt9_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt9
