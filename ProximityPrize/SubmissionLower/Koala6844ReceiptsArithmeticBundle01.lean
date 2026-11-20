import ProximityPrize.SubmissionLower.Koala6844ReceiptsColumnsClosed
import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetFast
import ProximityPrize.SubmissionLower.Koala6844ReceiptsArithmeticFast
import ProximityPrize.SubmissionLower.Koala6844ReceiptsSchedule
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles


namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def contributionWindow (f : Nat → Int) (start length : Nat) : Int :=
  ((List.range' start length).map f).sum

private theorem joinWindows (f : Nat → Int) (start left right : Nat) (x y : Int)
    (hx : contributionWindow f start left = x)
    (hy : contributionWindow f (start+left) right = y) :
    contributionWindow f start (left+right) = x+y := by
  unfold contributionWindow at *
  rw [← List.range'_append_1 (s := start) (m := left) (n := right),
    List.map_append, List.sum_append, hx, hy]

private theorem contributionSum (shape : FirstJetShape) (room count : Nat)
    (expected : Int) (count_eq : shape.q = count)
    (window : contributionWindow (firstJetAuxContribution shape room) 0 count = expected) :
    ((List.range shape.q).map (firstJetAuxContribution shape room)).sum = expected := by
  rw [count_eq, List.range_eq_range']
  exact window



private theorem primaryWindow0 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 512 = 3666865884626844 :=
  firstJetWindow_of_closed primaryShape 0 0 512 (3666865884626844) (by decide +kernel) (by decide +kernel)

private theorem primaryWindow512 : contributionWindow (firstJetAuxContribution primaryShape 0) 512 233 = 408958872767868 :=
  firstJetWindow_of_closed primaryShape 0 512 233 (408958872767868) (by decide +kernel) (by decide +kernel)

private theorem primaryJoin0_745 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 745 = 4075824757394712 :=
  joinWindows (firstJetAuxContribution primaryShape 0) 0 512 233 (3666865884626844) (408958872767868) primaryWindow0 primaryWindow512

theorem primary_firstJetGap_eq : firstJetGap primaryShape 0 = 146477001 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum primaryShape 0 745 (4075824757394712) rfl primaryJoin0_745]
  decide +kernel
private theorem firstRoomWindow0 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 = 82262095097539632 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 0 512 (82262095097539632) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow512 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 512 512 = 170587900132684944 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 512 512 (170587900132684944) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 = 154733148961266732 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1024 512 (154733148961266732) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1536 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1536 512 = 76319502656930676 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1536 512 (76319502656930676) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 2048 352 = 8334917467924536 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 2048 352 (8334917467924536) (by decide +kernel) (by decide +kernel)

private theorem firstRoomJoin0_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 = 252849995230224576 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 512 (82262095097539632) (170587900132684944) firstRoomWindow0 firstRoomWindow512

private theorem firstRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 1024 = 231052651618197408 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 512 (154733148961266732) (76319502656930676) firstRoomWindow1024 firstRoomWindow1536

private theorem firstRoomJoin0_2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 = 483902646848421984 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 1024 (252849995230224576) (231052651618197408) firstRoomJoin0_1024 firstRoomJoin1024_1024

private theorem firstRoomJoin0_2400 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2400 = 492237564316346520 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 352 (483902646848421984) (8334917467924536) firstRoomJoin0_2048 firstRoomWindow2048

theorem firstRoom_firstJetGap_eq : firstJetGap firstRoomShape firstRoomCut = 1098778930116326 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstRoomShape firstRoomCut 2400 (492237564316346520) rfl firstRoomJoin0_2400]
  decide +kernel
private theorem secondRoomWindow0 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 = 82478187747488016 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 0 512 (82478187747488016) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow512 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 512 512 = 170750926844298888 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 512 512 (170750926844298888) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 = 154843109645817000 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1024 512 (154843109645817000) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1536 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1536 512 = 76376397335815272 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1536 512 (76376397335815272) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 2048 447 = 8524476761228784 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 2048 447 (8524476761228784) (by decide +kernel) (by decide +kernel)

private theorem secondRoomJoin0_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 = 253229114591786904 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 512 (82478187747488016) (170750926844298888) secondRoomWindow0 secondRoomWindow512

private theorem secondRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 1024 = 231219506981632272 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 512 (154843109645817000) (76376397335815272) secondRoomWindow1024 secondRoomWindow1536

private theorem secondRoomJoin0_2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 = 484448621573419176 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 1024 (253229114591786904) (231219506981632272) secondRoomJoin0_1024 secondRoomJoin1024_1024

private theorem secondRoomJoin0_2495 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2495 = 492973098334647960 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 447 (484448621573419176) (8524476761228784) secondRoomJoin0_2048 secondRoomWindow2048

theorem secondRoom_firstJetGap_eq : firstJetGap secondRoomShape secondRoomCut = 2086336310 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondRoomShape secondRoomCut 2495 (492973098334647960) rfl secondRoomJoin0_2495]
  decide +kernel
private theorem firstAdaptiveWindow0 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 512 = 83450852837832036 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 0 512 (83450852837832036) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow512 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 512 512 = 171484795276865628 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 512 512 (171484795276865628) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 = 155338181443547832 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1024 512 (155338181443547832) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1536 512 = 76632672580530336 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1536 512 (76632672580530336) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 2048 352 = 8394191544983712 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 2048 352 (8394191544983712) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 = 254935648114697664 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 512 512 (83450852837832036) (171484795276865628) firstAdaptiveWindow0 firstAdaptiveWindow512

private theorem firstAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 1024 = 231970854024078168 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 512 (155338181443547832) (76632672580530336) firstAdaptiveWindow1024 firstAdaptiveWindow1536

private theorem firstAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 = 486906502138775832 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 1024 (254935648114697664) (231970854024078168) firstAdaptiveJoin0_1024 firstAdaptiveJoin1024_1024

private theorem firstAdaptiveJoin0_2400 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2400 = 495300693683759544 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 352 (486906502138775832) (8394191544983712) firstAdaptiveJoin0_2048 firstAdaptiveWindow2048

theorem firstAdaptive_firstJetGap_eq : firstJetGap firstAdaptiveShape 0 = firstAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstAdaptiveShape 0 2400 (495300693683759544) rfl firstAdaptiveJoin0_2400]
  decide +kernel
private theorem secondAdaptiveWindow0 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 512 = 144954042776773174980 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 0 512 (144954042776773174980) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 512 512 = 325668879743272417740 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 512 512 (325668879743272417740) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 = 502889848754044314108 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1024 512 (502889848754044314108) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1536 512 = 676616949808103969880 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1536 512 (676616949808103969880) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 = 846850182904386702252 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2048 512 (846850182904386702252) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2560 512 = 1013589548042878765512 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2560 512 (1013589548042878765512) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 = 1176835045223553173112 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3072 512 (1176835045223553173112) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3584 512 = 1336586674446448780152 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3584 512 (1336586674446448780152) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 = 1492844435711534754300 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4096 512 (1492844435711534754300) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4608 512 = 1645608329018815109664 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4608 512 (1645608329018815109664) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 = 1794878354368313535888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5120 512 (1794878354368313535888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5632 512 = 1940654511759993409368 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5632 512 (1940654511759993409368) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 = 2082936801193887224796 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6144 512 (2082936801193887224796) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6656 512 = 2221725222670402707504 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6656 512 (2221725222670402707504) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 = 2357019776191114843680 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7168 512 (2357019776191114843680) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7680 512 = 2488820461755378304632 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7680 512 (2488820461755378304632) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 = 2617127279361939743700 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8192 512 (2617127279361939743700) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8704 512 = 2741940229010684298672 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8704 512 (2741940229010684298672) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 = 2863259310701635909476 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9216 512 (2863259310701635909476) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9728 512 = 2981084524434792938964 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9728 512 (2981084524434792938964) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 = 3095415870210133707888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10240 512 (3095415870210133707888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10752 512 = 3206253348027697105224 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10752 512 (3206253348027697105224) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 = 3313596957887448081792 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11264 512 (3313596957887448081792) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11776 512 = 3417446699789397405516 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11776 512 (3417446699789397405516) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 = 3517802573733560961708 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12288 512 (3517802573733560961708) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12800 512 = 3614664579720160481628 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12800 512 (3614664579720160481628) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 = 3708032717750777173932 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13312 512 (3708032717750777173932) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13824 512 = 3797906987825231999076 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13824 512 (3797906987825231999076) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 = 3884287389942047575992 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14336 512 (3884287389942047575992) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14848 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14848 512 = 3967173924101054963268 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14848 512 (3967173924101054963268) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15360 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 = 4046566590302282487444 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15360 512 (4046566590302282487444) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15872 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15872 512 = 4122465388545692006748 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15872 512 (4122465388545692006748) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 = 4194870318831312544272 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16384 512 (4194870318831312544272) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16896 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16896 512 = 4263781381159134530916 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16896 512 (4263781381159134530916) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17408 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 = 4329198575529142168632 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17408 512 (4329198575529142168632) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17920 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17920 512 = 4391121901941372963132 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17920 512 (4391121901941372963132) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18432 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 = 4449551360395789011756 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18432 512 (4449551360395789011756) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18944 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18944 512 = 4504486950892544210184 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18944 512 (4504486950892544210184) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19456 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 = 4555928673433052939988 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19456 512 (4555928673433052939988) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19968 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19968 512 = 4603876528017642717900 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19968 512 (4603876528017642717900) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20480 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 = 4648330514644712032524 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20480 512 (4648330514644712032524) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20992 512 = 4689290633314003031844 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20992 512 (4689290633314003031844) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow21504 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 = 4726756884025483586616 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 21504 512 (4726756884025483586616) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22016 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22016 512 = 4760729266779159531300 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22016 512 (4760729266779159531300) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22528 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 = 4791207781575052657968 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22528 512 (4791207781575052657968) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23040 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23040 512 = 4818194706669939363828 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23040 512 (4818194706669939363828) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23552 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 = 4841717169214733747196 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23552 512 (4841717169214733747196) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24064 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24064 512 = 4861826986924692841224 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24064 512 (4861826986924692841224) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24576 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 = 4878578202995335484520 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24576 512 (4878578202995335484520) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25088 512 = 4892024860622280088500 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25088 512 (4892024860622280088500) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25600 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 = 4902221003002247629728 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25600 512 (4902221003002247629728) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26112 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26112 512 = 4909220673331525001964 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26112 512 (4909220673331525001964) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26624 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 = 4913077914804106262424 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26624 512 (4913077914804106262424) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27136 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27136 512 = 4913846770615029712788 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27136 512 (4913846770615029712788) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27648 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 = 4911581283959803466448 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27648 512 (4911581283959803466448) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28160 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28160 512 = 4906335498033994746072 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28160 512 (4906335498033994746072) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28672 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 = 4898163456033096067092 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28672 512 (4898163456033096067092) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29184 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29184 512 = 4887119201152648238412 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29184 512 (4887119201152648238412) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29696 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 = 4873256776588193580108 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29696 512 (4873256776588193580108) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30208 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30208 512 = 4856630225535228916116 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30208 512 (4856630225535228916116) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30720 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 = 4837293591189319754928 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30720 512 (4837293591189319754928) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31232 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31232 512 = 4815300916745979876672 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31232 512 (4815300916745979876672) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31744 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 = 4790706245401745980140 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31744 512 (4790706245401745980140) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32256 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32256 512 = 4763563620353214163788 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32256 512 (4763563620353214163788) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 = 4733927084794600911240 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32768 512 (4733927084794600911240) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33280 512 = 4701850681920648569412 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33280 512 (4701850681920648569412) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33792 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 = 4667388454926915722928 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33792 512 (4667388454926915722928) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34304 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34304 512 = 4630594447008919379424 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34304 512 (4630594447008919379424) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 = 4591522701362173688592 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34816 512 (4591522701362173688592) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35328 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35328 512 = 4550227261182243965472 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35328 512 (4550227261182243965472) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35840 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 = 4506762169664620275252 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35840 512 (4506762169664620275252) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36352 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36352 512 = 4461181470004849528152 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36352 512 (4461181470004849528152) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36864 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 = 4413539205398466348504 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36864 512 (4413539205398466348504) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37376 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37376 512 = 4363889419040972171592 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37376 512 (4363889419040972171592) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37888 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 = 4312286154128658226284 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37888 512 (4312286154128658226284) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38400 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38400 512 = 4258783453858386306588 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38400 512 (4258783453858386306588) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38912 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 = 4203435361424639809560 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38912 512 (4203435361424639809560) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39424 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39424 512 = 4146295920021922818888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39424 512 (4146295920021922818888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39936 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 = 4087419172845770923944 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39936 512 (4087419172845770923944) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40448 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40448 512 = 4026859163091677707056 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40448 512 (4026859163091677707056) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40960 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 = 3964669933955206233348 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40960 512 (3964669933955206233348) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41472 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41472 512 = 3900905528631865636056 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41472 512 (3900905528631865636056) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41984 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 = 3835619990317176392916 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41984 512 (3835619990317176392916) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow42496 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 42496 512 = 3768867362206700407056 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 42496 512 (3768867362206700407056) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43008 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 = 3700701687495927112992 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43008 512 (3700701687495927112992) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43520 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43520 512 = 3631177009380408871200 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43520 512 (3631177009380408871200) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44032 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 = 3560347371056140561248 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44032 512 (3560347371056140561248) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44544 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44544 512 = 3488266815720197995176 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44544 512 (3488266815720197995176) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45056 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 = 3414989386567381665000 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45056 512 (3414989386567381665000) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45568 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45568 512 = 3340569126792011154576 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45568 512 (3340569126792011154576) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46080 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 = 3265060079589517251912 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46080 512 (3265060079589517251912) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46592 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46592 512 = 3188516288155442322948 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46592 512 (3188516288155442322948) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47104 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 = 3110991795685326720576 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47104 512 (3110991795685326720576) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47616 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47616 512 = 3032540645374668468228 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47616 512 (3032540645374668468228) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48128 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 = 2953216880419033580988 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48128 512 (2953216880419033580988) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48640 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48640 512 = 2873074544013923999112 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48640 512 (2873074544013923999112) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49152 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 = 2792167679354867132460 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49152 512 (2792167679354867132460) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49664 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49664 512 = 2710550329637419781088 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49664 512 (2710550329637419781088) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50176 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 = 2628276538057356621588 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50176 512 (2628276538057356621588) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50688 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50688 512 = 2545400347811803640724 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50688 512 (2545400347811803640724) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51200 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 = 2461975802096002760964 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51200 512 (2461975802096002760964) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51712 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51712 512 = 2378056944104049977172 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51712 512 (2378056944104049977172) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52224 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 = 2293697817031315601460 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52224 512 (2293697817031315601460) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52736 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52736 512 = 2208952464073364207484 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52736 512 (2208952464073364207484) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53248 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 = 2123874928425685519080 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53248 512 (2123874928425685519080) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53760 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53760 512 = 2038519253283827963292 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53760 512 (2038519253283827963292) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54272 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 = 1952939481843324108984 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54272 512 (1952939481843324108984) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54784 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54784 512 = 1867189657299676735728 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54784 512 (1867189657299676735728) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55296 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 = 1781323822848453310896 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55296 512 (1781323822848453310896) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55808 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55808 512 = 1695396021685150173720 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55808 512 (1695396021685150173720) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56320 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 = 1609460297005460489772 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56320 512 (1609460297005460489772) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56832 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56832 512 = 1523570692006373139360 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56832 512 (1523570692006373139360) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57344 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 = 1437781249883637652488 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57344 512 (1437781249883637652488) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57856 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57856 512 = 1352146013831193943272 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57856 512 (1352146013831193943272) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58368 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 = 1266719027044340129964 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58368 512 (1266719027044340129964) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58880 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58880 512 = 1181554332718583348328 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58880 512 (1181554332718583348328) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow59392 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 512 = 1096705974049445776176 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 59392 512 (1096705974049445776176) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow59904 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59904 512 = 1012574533033832295444 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 59904 512 (1012574533033832295444) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow60416 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60416 512 = 931669153342680810600 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 60416 512 (931669153342680810600) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow60928 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60928 512 = 855068329899249744168 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 60928 512 (855068329899249744168) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow61440 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 512 = 782757071041174500096 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 61440 512 (782757071041174500096) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow61952 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61952 512 = 714641725744876774620 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 61952 512 (714641725744876774620) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow62464 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62464 512 = 650597528502243261924 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 62464 512 (650597528502243261924) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow62976 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62976 512 = 590499018794505230268 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 62976 512 (590499018794505230268) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow63488 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 512 = 534220736101969026636 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 63488 512 (534220736101969026636) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow64000 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64000 512 = 481637219902829583168 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 64000 512 (481637219902829583168) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow64512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64512 512 = 432623009676847239912 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 64512 512 (432623009676847239912) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow65024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65024 512 = 387052644903982264740 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 65024 512 (387052644903982264740) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow65536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 512 = 344800665064209805740 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 65536 512 (344800665064209805740) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow66048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66048 512 = 305741609637521793780 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 66048 512 (305741609637521793780) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow66560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66560 512 = 269750018103888090384 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 66560 512 (269750018103888090384) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow67072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67072 512 = 236700429943299914400 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 67072 512 (236700429943299914400) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow67584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 512 = 206467384635718097640 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 67584 512 (206467384635718097640) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow68096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68096 512 = 178925421661138356684 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 68096 512 (178925421661138356684) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow68608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68608 512 = 153949080499563352056 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 68608 512 (153949080499563352056) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow69120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69120 512 = 131412900631955148612 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 69120 512 (131412900631955148612) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow69632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 512 = 111191421538097851464 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 69632 512 (111191421538097851464) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow70144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70144 512 = 93159182696837154636 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 70144 512 (93159182696837154636) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow70656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70656 512 = 77190723588126412140 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 70656 512 (77190723588126412140) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow71168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71168 512 = 63160583691916670832 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 71168 512 (63160583691916670832) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow71680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 512 = 50943302488221124572 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 71680 512 (50943302488221124572) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow72192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72192 512 = 40413419457002837748 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 72192 512 (40413419457002837748) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow72704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72704 512 = 31445474078245789608 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 72704 512 (31445474078245789608) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow73216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73216 512 = 23914005831927483552 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 73216 512 (23914005831927483552) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow73728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 512 = 17693554198022601888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 73728 512 (17693554198022601888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow74240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74240 512 = 12658658656532977128 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 74240 512 (12658658656532977128) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow74752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74752 512 = 8683858687403347824 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 74752 512 (8683858687403347824) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow75264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75264 512 = 5643693771080326860 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 75264 512 (5643693771080326860) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow75776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 512 = 3412703387086078656 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 75776 512 (3412703387086078656) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow76288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76288 512 = 1865427015074794068 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 76288 512 (1865427015074794068) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow76800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76800 512 = 876404134980950028 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 76800 512 (876404134980950028) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow77312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77312 512 = 320174226822683052 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 77312 512 (320174226822683052) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow77824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77824 512 = 71276770572598368 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 77824 512 (71276770572598368) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow78336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 78336 480 = 4251279654768564 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 78336 480 (4251279654768564) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 = 470622922520045592720 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 512 512 (144954042776773174980) (325668879743272417740) secondAdaptiveWindow0 secondAdaptiveWindow512

private theorem secondAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 1024 = 1179506798562148283988 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 512 (502889848754044314108) (676616949808103969880) secondAdaptiveWindow1024 secondAdaptiveWindow1536

private theorem secondAdaptiveJoin2048_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 = 1860439730947265467764 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 512 (846850182904386702252) (1013589548042878765512) secondAdaptiveWindow2048 secondAdaptiveWindow2560

private theorem secondAdaptiveJoin3072_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 1024 = 2513421719670001953264 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 512 (1176835045223553173112) (1336586674446448780152) secondAdaptiveWindow3072 secondAdaptiveWindow3584

private theorem secondAdaptiveJoin4096_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 = 3138452764730349863964 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 512 (1492844435711534754300) (1645608329018815109664) secondAdaptiveWindow4096 secondAdaptiveWindow4608

private theorem secondAdaptiveJoin5120_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 1024 = 3735532866128306945256 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 512 (1794878354368313535888) (1940654511759993409368) secondAdaptiveWindow5120 secondAdaptiveWindow5632

private theorem secondAdaptiveJoin6144_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 = 4304662023864289932300 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 512 (2082936801193887224796) (2221725222670402707504) secondAdaptiveWindow6144 secondAdaptiveWindow6656

private theorem secondAdaptiveJoin7168_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 1024 = 4845840237946493148312 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 512 (2357019776191114843680) (2488820461755378304632) secondAdaptiveWindow7168 secondAdaptiveWindow7680

private theorem secondAdaptiveJoin8192_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 = 5359067508372624042372 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 512 (2617127279361939743700) (2741940229010684298672) secondAdaptiveWindow8192 secondAdaptiveWindow8704

private theorem secondAdaptiveJoin9216_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 1024 = 5844343835136428848440 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 512 (2863259310701635909476) (2981084524434792938964) secondAdaptiveWindow9216 secondAdaptiveWindow9728

private theorem secondAdaptiveJoin10240_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 = 6301669218237830813112 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 512 (3095415870210133707888) (3206253348027697105224) secondAdaptiveWindow10240 secondAdaptiveWindow10752

private theorem secondAdaptiveJoin11264_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 1024 = 6731043657676845487308 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 512 (3313596957887448081792) (3417446699789397405516) secondAdaptiveWindow11264 secondAdaptiveWindow11776

private theorem secondAdaptiveJoin12288_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 = 7132467153453721443336 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 512 (3517802573733560961708) (3614664579720160481628) secondAdaptiveWindow12288 secondAdaptiveWindow12800

private theorem secondAdaptiveJoin13312_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 1024 = 7505939705576009173008 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 512 (3708032717750777173932) (3797906987825231999076) secondAdaptiveWindow13312 secondAdaptiveWindow13824

private theorem secondAdaptiveJoin14336_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 = 7851461314043102539260 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 512 (3884287389942047575992) (3967173924101054963268) secondAdaptiveWindow14336 secondAdaptiveWindow14848

private theorem secondAdaptiveJoin15360_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 1024 = 8169031978847974494192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 512 (4046566590302282487444) (4122465388545692006748) secondAdaptiveWindow15360 secondAdaptiveWindow15872

private theorem secondAdaptiveJoin16384_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 = 8458651699990447075188 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 512 (4194870318831312544272) (4263781381159134530916) secondAdaptiveWindow16384 secondAdaptiveWindow16896

private theorem secondAdaptiveJoin17408_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 1024 = 8720320477470515131764 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 512 (4329198575529142168632) (4391121901941372963132) secondAdaptiveWindow17408 secondAdaptiveWindow17920

private theorem secondAdaptiveJoin18432_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 = 8954038311288333221940 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 512 (4449551360395789011756) (4504486950892544210184) secondAdaptiveWindow18432 secondAdaptiveWindow18944

private theorem secondAdaptiveJoin19456_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 1024 = 9159805201450695657888 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 512 (4555928673433052939988) (4603876528017642717900) secondAdaptiveWindow19456 secondAdaptiveWindow19968

private theorem secondAdaptiveJoin20480_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 = 9337621147958715064368 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 512 (4648330514644712032524) (4689290633314003031844) secondAdaptiveWindow20480 secondAdaptiveWindow20992

private theorem secondAdaptiveJoin21504_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 1024 = 9487486150804643117916 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 512 (4726756884025483586616) (4760729266779159531300) secondAdaptiveWindow21504 secondAdaptiveWindow22016

private theorem secondAdaptiveJoin22528_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 = 9609402488244992021796 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 512 (4791207781575052657968) (4818194706669939363828) secondAdaptiveWindow22528 secondAdaptiveWindow23040

private theorem secondAdaptiveJoin23552_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 1024 = 9703544156139426588420 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 512 (4841717169214733747196) (4861826986924692841224) secondAdaptiveWindow23552 secondAdaptiveWindow24064

private theorem secondAdaptiveJoin24576_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 = 9770603063617615573020 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 512 (4878578202995335484520) (4892024860622280088500) secondAdaptiveWindow24576 secondAdaptiveWindow25088

private theorem secondAdaptiveJoin25600_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 1024 = 9811441676333772631692 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 512 (4902221003002247629728) (4909220673331525001964) secondAdaptiveWindow25600 secondAdaptiveWindow26112

private theorem secondAdaptiveJoin26624_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 = 9826924685419135975212 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 512 (4913077914804106262424) (4913846770615029712788) secondAdaptiveWindow26624 secondAdaptiveWindow27136

private theorem secondAdaptiveJoin27648_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 1024 = 9817916781993798212520 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 512 (4911581283959803466448) (4906335498033994746072) secondAdaptiveWindow27648 secondAdaptiveWindow28160

private theorem secondAdaptiveJoin28672_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 = 9785282657185744305504 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 512 (4898163456033096067092) (4887119201152648238412) secondAdaptiveWindow28672 secondAdaptiveWindow29184

private theorem secondAdaptiveJoin29696_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 1024 = 9729887002123422496224 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 512 (4873256776588193580108) (4856630225535228916116) secondAdaptiveWindow29696 secondAdaptiveWindow30208

private theorem secondAdaptiveJoin30720_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 = 9652594507935299631600 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 512 (4837293591189319754928) (4815300916745979876672) secondAdaptiveWindow30720 secondAdaptiveWindow31232

private theorem secondAdaptiveJoin31744_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 1024 = 9554269865754960143928 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 512 (4790706245401745980140) (4763563620353214163788) secondAdaptiveWindow31744 secondAdaptiveWindow32256

private theorem secondAdaptiveJoin32768_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 = 9435777766715249480652 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 512 (4733927084794600911240) (4701850681920648569412) secondAdaptiveWindow32768 secondAdaptiveWindow33280

private theorem secondAdaptiveJoin33792_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 1024 = 9297982901935835102352 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 512 (4667388454926915722928) (4630594447008919379424) secondAdaptiveWindow33792 secondAdaptiveWindow34304

private theorem secondAdaptiveJoin34816_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 = 9141749962544417654064 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 512 (4591522701362173688592) (4550227261182243965472) secondAdaptiveWindow34816 secondAdaptiveWindow35328

private theorem secondAdaptiveJoin35840_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 1024 = 8967943639669469803404 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 512 (4506762169664620275252) (4461181470004849528152) secondAdaptiveWindow35840 secondAdaptiveWindow36352

private theorem secondAdaptiveJoin36864_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 = 8777428624439438520096 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 512 (4413539205398466348504) (4363889419040972171592) secondAdaptiveWindow36864 secondAdaptiveWindow37376

private theorem secondAdaptiveJoin37888_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 1024 = 8571069607987044532872 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 512 (4312286154128658226284) (4258783453858386306588) secondAdaptiveWindow37888 secondAdaptiveWindow38400

private theorem secondAdaptiveJoin38912_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 = 8349731281446562628448 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 512 (4203435361424639809560) (4146295920021922818888) secondAdaptiveWindow38912 secondAdaptiveWindow39424

private theorem secondAdaptiveJoin39936_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 1024 = 8114278335937448631000 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 512 (4087419172845770923944) (4026859163091677707056) secondAdaptiveWindow39936 secondAdaptiveWindow40448

private theorem secondAdaptiveJoin40960_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 = 7865575462587071869404 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 512 (3964669933955206233348) (3900905528631865636056) secondAdaptiveWindow40960 secondAdaptiveWindow41472

private theorem secondAdaptiveJoin41984_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 1024 = 7604487352523876799972 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 512 (3835619990317176392916) (3768867362206700407056) secondAdaptiveWindow41984 secondAdaptiveWindow42496

private theorem secondAdaptiveJoin43008_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 = 7331878696876335984192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 512 (3700701687495927112992) (3631177009380408871200) secondAdaptiveWindow43008 secondAdaptiveWindow43520

private theorem secondAdaptiveJoin44032_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 1024 = 7048614186776338556424 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 512 (3560347371056140561248) (3488266815720197995176) secondAdaptiveWindow44032 secondAdaptiveWindow44544

private theorem secondAdaptiveJoin45056_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 = 6755558513359392819576 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 512 (3414989386567381665000) (3340569126792011154576) secondAdaptiveWindow45056 secondAdaptiveWindow45568

private theorem secondAdaptiveJoin46080_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 1024 = 6453576367744959574860 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 512 (3265060079589517251912) (3188516288155442322948) secondAdaptiveWindow46080 secondAdaptiveWindow46592

private theorem secondAdaptiveJoin47104_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 = 6143532441059995188804 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 512 (3110991795685326720576) (3032540645374668468228) secondAdaptiveWindow47104 secondAdaptiveWindow47616

private theorem secondAdaptiveJoin48128_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 1024 = 5826291424432957580100 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 512 (2953216880419033580988) (2873074544013923999112) secondAdaptiveWindow48128 secondAdaptiveWindow48640

private theorem secondAdaptiveJoin49152_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 = 5502718008992286913548 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 512 (2792167679354867132460) (2710550329637419781088) secondAdaptiveWindow49152 secondAdaptiveWindow49664

private theorem secondAdaptiveJoin50176_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 1024 = 5173676885869160262312 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 512 (2628276538057356621588) (2545400347811803640724) secondAdaptiveWindow50176 secondAdaptiveWindow50688

private theorem secondAdaptiveJoin51200_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 = 4840032746200052738136 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 512 (2461975802096002760964) (2378056944104049977172) secondAdaptiveWindow51200 secondAdaptiveWindow51712

private theorem secondAdaptiveJoin52224_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 1024 = 4502650281104679808944 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 512 (2293697817031315601460) (2208952464073364207484) secondAdaptiveWindow52224 secondAdaptiveWindow52736

private theorem secondAdaptiveJoin53248_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 = 4162394181709513482372 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 512 (2123874928425685519080) (2038519253283827963292) secondAdaptiveWindow53248 secondAdaptiveWindow53760

private theorem secondAdaptiveJoin54272_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 1024 = 3820129139143000844712 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 512 (1952939481843324108984) (1867189657299676735728) secondAdaptiveWindow54272 secondAdaptiveWindow54784

private theorem secondAdaptiveJoin55296_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 = 3476719844533603484616 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 512 (1781323822848453310896) (1695396021685150173720) secondAdaptiveWindow55296 secondAdaptiveWindow55808

private theorem secondAdaptiveJoin56320_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 1024 = 3133030989011833629132 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 512 (1609460297005460489772) (1523570692006373139360) secondAdaptiveWindow56320 secondAdaptiveWindow56832

private theorem secondAdaptiveJoin57344_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 = 2789927263714831595760 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 512 (1437781249883637652488) (1352146013831193943272) secondAdaptiveWindow57344 secondAdaptiveWindow57856

private theorem secondAdaptiveJoin58368_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 1024 = 2448273359762923478292 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 512 (1266719027044340129964) (1181554332718583348328) secondAdaptiveWindow58368 secondAdaptiveWindow58880

private theorem secondAdaptiveJoin59392_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 1024 = 2109280507083278071620 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 59392 512 512 (1096705974049445776176) (1012574533033832295444) secondAdaptiveWindow59392 secondAdaptiveWindow59904

private theorem secondAdaptiveJoin60416_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60416 1024 = 1786737483241930554768 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 60416 512 512 (931669153342680810600) (855068329899249744168) secondAdaptiveWindow60416 secondAdaptiveWindow60928

private theorem secondAdaptiveJoin61440_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 1024 = 1497398796786051274716 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 512 512 (782757071041174500096) (714641725744876774620) secondAdaptiveWindow61440 secondAdaptiveWindow61952

private theorem secondAdaptiveJoin62464_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62464 1024 = 1241096547296748492192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 62464 512 512 (650597528502243261924) (590499018794505230268) secondAdaptiveWindow62464 secondAdaptiveWindow62976

private theorem secondAdaptiveJoin63488_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 1024 = 1015857956004798609804 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 63488 512 512 (534220736101969026636) (481637219902829583168) secondAdaptiveWindow63488 secondAdaptiveWindow64000

private theorem secondAdaptiveJoin64512_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64512 1024 = 819675654580829504652 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 64512 512 512 (432623009676847239912) (387052644903982264740) secondAdaptiveWindow64512 secondAdaptiveWindow65024

private theorem secondAdaptiveJoin65536_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 1024 = 650542274701731599520 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 512 512 (344800665064209805740) (305741609637521793780) secondAdaptiveWindow65536 secondAdaptiveWindow66048

private theorem secondAdaptiveJoin66560_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66560 1024 = 506450448047188004784 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 66560 512 512 (269750018103888090384) (236700429943299914400) secondAdaptiveWindow66560 secondAdaptiveWindow67072

private theorem secondAdaptiveJoin67584_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 1024 = 385392806296856454324 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 67584 512 512 (206467384635718097640) (178925421661138356684) secondAdaptiveWindow67584 secondAdaptiveWindow68096

private theorem secondAdaptiveJoin68608_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68608 1024 = 285361981131518500668 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 68608 512 512 (153949080499563352056) (131412900631955148612) secondAdaptiveWindow68608 secondAdaptiveWindow69120

private theorem secondAdaptiveJoin69632_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 1024 = 204350604234935006100 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 512 512 (111191421538097851464) (93159182696837154636) secondAdaptiveWindow69632 secondAdaptiveWindow70144

private theorem secondAdaptiveJoin70656_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70656 1024 = 140351307280043082972 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 70656 512 512 (77190723588126412140) (63160583691916670832) secondAdaptiveWindow70656 secondAdaptiveWindow71168

private theorem secondAdaptiveJoin71680_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 1024 = 91356721945223962320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 71680 512 512 (50943302488221124572) (40413419457002837748) secondAdaptiveWindow71680 secondAdaptiveWindow72192

private theorem secondAdaptiveJoin72704_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72704 1024 = 55359479910173273160 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 72704 512 512 (31445474078245789608) (23914005831927483552) secondAdaptiveWindow72704 secondAdaptiveWindow73216

private theorem secondAdaptiveJoin73728_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 1024 = 30352212854555579016 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 512 512 (17693554198022601888) (12658658656532977128) secondAdaptiveWindow73728 secondAdaptiveWindow74240

private theorem secondAdaptiveJoin74752_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74752 1024 = 14327552458483674684 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 74752 512 512 (8683858687403347824) (5643693771080326860) secondAdaptiveWindow74752 secondAdaptiveWindow75264

private theorem secondAdaptiveJoin75776_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 1024 = 5278130402160872724 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 75776 512 512 (3412703387086078656) (1865427015074794068) secondAdaptiveWindow75776 secondAdaptiveWindow76288

private theorem secondAdaptiveJoin76800_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76800 1024 = 1196578361803633080 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 76800 512 512 (876404134980950028) (320174226822683052) secondAdaptiveWindow76800 secondAdaptiveWindow77312

private theorem secondAdaptiveJoin77824_992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77824 992 = 75528050227366932 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 77824 512 480 (71276770572598368) (4251279654768564) secondAdaptiveWindow77824 secondAdaptiveWindow78336

private theorem secondAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 = 1650129721082193876708 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 1024 (470622922520045592720) (1179506798562148283988) secondAdaptiveJoin0_1024 secondAdaptiveJoin1024_1024

private theorem secondAdaptiveJoin2048_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 2048 = 4373861450617267421028 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 1024 (1860439730947265467764) (2513421719670001953264) secondAdaptiveJoin2048_1024 secondAdaptiveJoin3072_1024

private theorem secondAdaptiveJoin4096_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 = 6873985630858656809220 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 1024 (3138452764730349863964) (3735532866128306945256) secondAdaptiveJoin4096_1024 secondAdaptiveJoin5120_1024

private theorem secondAdaptiveJoin6144_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 2048 = 9150502261810783080612 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 1024 (4304662023864289932300) (4845840237946493148312) secondAdaptiveJoin6144_1024 secondAdaptiveJoin7168_1024

private theorem secondAdaptiveJoin8192_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 = 11203411343509052890812 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 1024 (5359067508372624042372) (5844343835136428848440) secondAdaptiveJoin8192_1024 secondAdaptiveJoin9216_1024

private theorem secondAdaptiveJoin10240_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 2048 = 13032712875914676300420 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 1024 (6301669218237830813112) (6731043657676845487308) secondAdaptiveJoin10240_1024 secondAdaptiveJoin11264_1024

private theorem secondAdaptiveJoin12288_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 = 14638406859029730616344 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 1024 (7132467153453721443336) (7505939705576009173008) secondAdaptiveJoin12288_1024 secondAdaptiveJoin13312_1024

private theorem secondAdaptiveJoin14336_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 2048 = 16020493292891077033452 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 1024 (7851461314043102539260) (8169031978847974494192) secondAdaptiveJoin14336_1024 secondAdaptiveJoin15360_1024

private theorem secondAdaptiveJoin16384_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 = 17178972177460962206952 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 1024 (8458651699990447075188) (8720320477470515131764) secondAdaptiveJoin16384_1024 secondAdaptiveJoin17408_1024

private theorem secondAdaptiveJoin18432_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 2048 = 18113843512739028879828 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 1024 (8954038311288333221940) (9159805201450695657888) secondAdaptiveJoin18432_1024 secondAdaptiveJoin19456_1024

private theorem secondAdaptiveJoin20480_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 = 18825107298763358182284 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 1024 (9337621147958715064368) (9487486150804643117916) secondAdaptiveJoin20480_1024 secondAdaptiveJoin21504_1024

private theorem secondAdaptiveJoin22528_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 2048 = 19312946644384418610216 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 1024 (9609402488244992021796) (9703544156139426588420) secondAdaptiveJoin22528_1024 secondAdaptiveJoin23552_1024

private theorem secondAdaptiveJoin24576_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 = 19582044739951388204712 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 1024 (9770603063617615573020) (9811441676333772631692) secondAdaptiveJoin24576_1024 secondAdaptiveJoin25600_1024

private theorem secondAdaptiveJoin26624_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 2048 = 19644841467412934187732 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 1024 (9826924685419135975212) (9817916781993798212520) secondAdaptiveJoin26624_1024 secondAdaptiveJoin27648_1024

private theorem secondAdaptiveJoin28672_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 = 19515169659309166801728 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 1024 (9785282657185744305504) (9729887002123422496224) secondAdaptiveJoin28672_1024 secondAdaptiveJoin29696_1024

private theorem secondAdaptiveJoin30720_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 2048 = 19206864373690259775528 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 1024 (9652594507935299631600) (9554269865754960143928) secondAdaptiveJoin30720_1024 secondAdaptiveJoin31744_1024

private theorem secondAdaptiveJoin32768_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 = 18733760668651084583004 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 1024 (9435777766715249480652) (9297982901935835102352) secondAdaptiveJoin32768_1024 secondAdaptiveJoin33792_1024

private theorem secondAdaptiveJoin34816_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 2048 = 18109693602213887457468 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 1024 (9141749962544417654064) (8967943639669469803404) secondAdaptiveJoin34816_1024 secondAdaptiveJoin35840_1024

private theorem secondAdaptiveJoin36864_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 = 17348498232426483052968 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 1024 (8777428624439438520096) (8571069607987044532872) secondAdaptiveJoin36864_1024 secondAdaptiveJoin37888_1024

private theorem secondAdaptiveJoin38912_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 2048 = 16464009617384011259448 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 1024 (8349731281446562628448) (8114278335937448631000) secondAdaptiveJoin38912_1024 secondAdaptiveJoin39936_1024

private theorem secondAdaptiveJoin40960_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 = 15470062815110948669376 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 1024 (7865575462587071869404) (7604487352523876799972) secondAdaptiveJoin40960_1024 secondAdaptiveJoin41984_1024

private theorem secondAdaptiveJoin43008_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 2048 = 14380492883652674540616 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 1024 (7331878696876335984192) (7048614186776338556424) secondAdaptiveJoin43008_1024 secondAdaptiveJoin44032_1024

private theorem secondAdaptiveJoin45056_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 = 13209134881104352394436 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 1024 (6755558513359392819576) (6453576367744959574860) secondAdaptiveJoin45056_1024 secondAdaptiveJoin46080_1024

private theorem secondAdaptiveJoin47104_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 2048 = 11969823865492952768904 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 1024 (6143532441059995188804) (5826291424432957580100) secondAdaptiveJoin47104_1024 secondAdaptiveJoin48128_1024

private theorem secondAdaptiveJoin49152_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 = 10676394894861447175860 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 1024 (5502718008992286913548) (5173676885869160262312) secondAdaptiveJoin49152_1024 secondAdaptiveJoin50176_1024

private theorem secondAdaptiveJoin51200_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 2048 = 9342683027304732547080 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 1024 (4840032746200052738136) (4502650281104679808944) secondAdaptiveJoin51200_1024 secondAdaptiveJoin52224_1024

private theorem secondAdaptiveJoin53248_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 = 7982523320852514327084 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 1024 (4162394181709513482372) (3820129139143000844712) secondAdaptiveJoin53248_1024 secondAdaptiveJoin54272_1024

private theorem secondAdaptiveJoin55296_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 2048 = 6609750833545437113748 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 1024 (3476719844533603484616) (3133030989011833629132) secondAdaptiveJoin55296_1024 secondAdaptiveJoin56320_1024

private theorem secondAdaptiveJoin57344_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 2048 = 5238200623477755074052 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 1024 (2789927263714831595760) (2448273359762923478292) secondAdaptiveJoin57344_1024 secondAdaptiveJoin58368_1024

private theorem secondAdaptiveJoin59392_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 2048 = 3896017990325208626388 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 59392 1024 1024 (2109280507083278071620) (1786737483241930554768) secondAdaptiveJoin59392_1024 secondAdaptiveJoin60416_1024

private theorem secondAdaptiveJoin61440_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 2048 = 2738495344082799766908 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 1024 1024 (1497398796786051274716) (1241096547296748492192) secondAdaptiveJoin61440_1024 secondAdaptiveJoin62464_1024

private theorem secondAdaptiveJoin63488_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 2048 = 1835533610585628114456 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 63488 1024 1024 (1015857956004798609804) (819675654580829504652) secondAdaptiveJoin63488_1024 secondAdaptiveJoin64512_1024

private theorem secondAdaptiveJoin65536_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 2048 = 1156992722748919604304 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 1024 1024 (650542274701731599520) (506450448047188004784) secondAdaptiveJoin65536_1024 secondAdaptiveJoin66560_1024

private theorem secondAdaptiveJoin67584_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 2048 = 670754787428374954992 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 67584 1024 1024 (385392806296856454324) (285361981131518500668) secondAdaptiveJoin67584_1024 secondAdaptiveJoin68608_1024

private theorem secondAdaptiveJoin69632_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 2048 = 344701911514978089072 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 1024 1024 (204350604234935006100) (140351307280043082972) secondAdaptiveJoin69632_1024 secondAdaptiveJoin70656_1024

private theorem secondAdaptiveJoin71680_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 2048 = 146716201855397235480 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 71680 1024 1024 (91356721945223962320) (55359479910173273160) secondAdaptiveJoin71680_1024 secondAdaptiveJoin72704_1024

private theorem secondAdaptiveJoin73728_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 2048 = 44679765313039253700 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 1024 1024 (30352212854555579016) (14327552458483674684) secondAdaptiveJoin73728_1024 secondAdaptiveJoin74752_1024

private theorem secondAdaptiveJoin75776_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 2048 = 6474708763964505804 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 75776 1024 1024 (5278130402160872724) (1196578361803633080) secondAdaptiveJoin75776_1024 secondAdaptiveJoin76800_1024

private theorem secondAdaptiveJoin0_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 = 6023991171699461297736 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 2048 (1650129721082193876708) (4373861450617267421028) secondAdaptiveJoin0_2048 secondAdaptiveJoin2048_2048

private theorem secondAdaptiveJoin4096_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 4096 = 16024487892669439889832 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 2048 (6873985630858656809220) (9150502261810783080612) secondAdaptiveJoin4096_2048 secondAdaptiveJoin6144_2048

private theorem secondAdaptiveJoin8192_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 = 24236124219423729191232 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 2048 (11203411343509052890812) (13032712875914676300420) secondAdaptiveJoin8192_2048 secondAdaptiveJoin10240_2048

private theorem secondAdaptiveJoin12288_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 4096 = 30658900151920807649796 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 2048 (14638406859029730616344) (16020493292891077033452) secondAdaptiveJoin12288_2048 secondAdaptiveJoin14336_2048

private theorem secondAdaptiveJoin16384_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 = 35292815690199991086780 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 2048 (17178972177460962206952) (18113843512739028879828) secondAdaptiveJoin16384_2048 secondAdaptiveJoin18432_2048

private theorem secondAdaptiveJoin20480_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 4096 = 38138053943147776792500 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 2048 (18825107298763358182284) (19312946644384418610216) secondAdaptiveJoin20480_2048 secondAdaptiveJoin22528_2048

private theorem secondAdaptiveJoin24576_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 = 39226886207364322392444 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 2048 (19582044739951388204712) (19644841467412934187732) secondAdaptiveJoin24576_2048 secondAdaptiveJoin26624_2048

private theorem secondAdaptiveJoin28672_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 4096 = 38722034032999426577256 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 2048 (19515169659309166801728) (19206864373690259775528) secondAdaptiveJoin28672_2048 secondAdaptiveJoin30720_2048

private theorem secondAdaptiveJoin32768_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 = 36843454270864972040472 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 2048 (18733760668651084583004) (18109693602213887457468) secondAdaptiveJoin32768_2048 secondAdaptiveJoin34816_2048

private theorem secondAdaptiveJoin36864_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 4096 = 33812507849810494312416 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 2048 (17348498232426483052968) (16464009617384011259448) secondAdaptiveJoin36864_2048 secondAdaptiveJoin38912_2048

private theorem secondAdaptiveJoin40960_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 = 29850555698763623209992 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 2048 (15470062815110948669376) (14380492883652674540616) secondAdaptiveJoin40960_2048 secondAdaptiveJoin43008_2048

private theorem secondAdaptiveJoin45056_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 4096 = 25178958746597305163340 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 2048 (13209134881104352394436) (11969823865492952768904) secondAdaptiveJoin45056_2048 secondAdaptiveJoin47104_2048

private theorem secondAdaptiveJoin49152_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 = 20019077922166179722940 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 2048 (10676394894861447175860) (9342683027304732547080) secondAdaptiveJoin49152_2048 secondAdaptiveJoin51200_2048

private theorem secondAdaptiveJoin53248_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 4096 = 14592274154397951440832 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 2048 (7982523320852514327084) (6609750833545437113748) secondAdaptiveJoin53248_2048 secondAdaptiveJoin55296_2048

private theorem secondAdaptiveJoin57344_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 4096 = 9134218613802963700440 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 2048 2048 (5238200623477755074052) (3896017990325208626388) secondAdaptiveJoin57344_2048 secondAdaptiveJoin59392_2048

private theorem secondAdaptiveJoin61440_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 4096 = 4574028954668427881364 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 2048 2048 (2738495344082799766908) (1835533610585628114456) secondAdaptiveJoin61440_2048 secondAdaptiveJoin63488_2048

private theorem secondAdaptiveJoin65536_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 4096 = 1827747510177294559296 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 2048 2048 (1156992722748919604304) (670754787428374954992) secondAdaptiveJoin65536_2048 secondAdaptiveJoin67584_2048

private theorem secondAdaptiveJoin69632_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 4096 = 491418113370375324552 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 2048 2048 (344701911514978089072) (146716201855397235480) secondAdaptiveJoin69632_2048 secondAdaptiveJoin71680_2048

private theorem secondAdaptiveJoin73728_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 4096 = 51154474077003759504 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 2048 2048 (44679765313039253700) (6474708763964505804) secondAdaptiveJoin73728_2048 secondAdaptiveJoin75776_2048

private theorem secondAdaptiveJoin0_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 = 22048479064368901187568 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 4096 (6023991171699461297736) (16024487892669439889832) secondAdaptiveJoin0_4096 secondAdaptiveJoin4096_4096

private theorem secondAdaptiveJoin8192_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 8192 = 54895024371344536841028 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 4096 (24236124219423729191232) (30658900151920807649796) secondAdaptiveJoin8192_4096 secondAdaptiveJoin12288_4096

private theorem secondAdaptiveJoin16384_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 = 73430869633347767879280 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 4096 (35292815690199991086780) (38138053943147776792500) secondAdaptiveJoin16384_4096 secondAdaptiveJoin20480_4096

private theorem secondAdaptiveJoin24576_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 8192 = 77948920240363748969700 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 4096 (39226886207364322392444) (38722034032999426577256) secondAdaptiveJoin24576_4096 secondAdaptiveJoin28672_4096

private theorem secondAdaptiveJoin32768_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 = 70655962120675466352888 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 4096 (36843454270864972040472) (33812507849810494312416) secondAdaptiveJoin32768_4096 secondAdaptiveJoin36864_4096

private theorem secondAdaptiveJoin40960_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 8192 = 55029514445360928373332 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 4096 (29850555698763623209992) (25178958746597305163340) secondAdaptiveJoin40960_4096 secondAdaptiveJoin45056_4096

private theorem secondAdaptiveJoin49152_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 = 34611352076564131163772 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 4096 (20019077922166179722940) (14592274154397951440832) secondAdaptiveJoin49152_4096 secondAdaptiveJoin53248_4096

private theorem secondAdaptiveJoin57344_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 8192 = 13708247568471391581804 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 4096 4096 (9134218613802963700440) (4574028954668427881364) secondAdaptiveJoin57344_4096 secondAdaptiveJoin61440_4096

private theorem secondAdaptiveJoin65536_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 8192 = 2319165623547669883848 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 4096 4096 (1827747510177294559296) (491418113370375324552) secondAdaptiveJoin65536_4096 secondAdaptiveJoin69632_4096

private theorem secondAdaptiveJoin73728_5088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 5088 = 51230002127231126436 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 4096 992 (51154474077003759504) (75528050227366932) secondAdaptiveJoin73728_4096 secondAdaptiveJoin77824_992

private theorem secondAdaptiveJoin0_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 = 76943503435713438028596 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 8192 (22048479064368901187568) (54895024371344536841028) secondAdaptiveJoin0_8192 secondAdaptiveJoin8192_8192

private theorem secondAdaptiveJoin16384_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 16384 = 151379789873711516848980 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 8192 (73430869633347767879280) (77948920240363748969700) secondAdaptiveJoin16384_8192 secondAdaptiveJoin24576_8192

private theorem secondAdaptiveJoin32768_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 = 125685476566036394726220 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 8192 (70655962120675466352888) (55029514445360928373332) secondAdaptiveJoin32768_8192 secondAdaptiveJoin40960_8192

private theorem secondAdaptiveJoin49152_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 16384 = 48319599645035522745576 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 8192 (34611352076564131163772) (13708247568471391581804) secondAdaptiveJoin49152_8192 secondAdaptiveJoin57344_8192

private theorem secondAdaptiveJoin65536_13280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 13280 = 2370395625674901010284 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 8192 5088 (2319165623547669883848) (51230002127231126436) secondAdaptiveJoin65536_8192 secondAdaptiveJoin73728_5088

private theorem secondAdaptiveJoin0_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 = 228323293309424954877576 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 16384 (76943503435713438028596) (151379789873711516848980) secondAdaptiveJoin0_16384 secondAdaptiveJoin16384_16384

private theorem secondAdaptiveJoin32768_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 32768 = 174005076211071917471796 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 16384 (125685476566036394726220) (48319599645035522745576) secondAdaptiveJoin32768_16384 secondAdaptiveJoin49152_16384

private theorem secondAdaptiveJoin0_65536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 65536 = 402328369520496872349372 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 32768 (228323293309424954877576) (174005076211071917471796) secondAdaptiveJoin0_32768 secondAdaptiveJoin32768_32768

private theorem secondAdaptiveJoin0_78816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 78816 = 404698765146171773359656 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 65536 13280 (402328369520496872349372) (2370395625674901010284) secondAdaptiveJoin0_65536 secondAdaptiveJoin65536_13280

theorem secondAdaptive_firstJetGap_eq : firstJetGap secondAdaptiveShape 0 = secondAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondAdaptiveShape 0 78816 (404698765146171773359656) rfl secondAdaptiveJoin0_78816]
  decide +kernel

private def sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : sliceWindow f a b = x) (hy : sliceWindow f (a+b) c = y) :
    sliceWindow f a (b+c) = x+y := by
  simp only [sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [sliceWindow,Nat.zero_add]

private theorem margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← sliceWindow_zero (auxiliaryRankSlice src),
    ← sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem contact00OrdinaryColumns : ordinaryColumnCount contact00 = 2480989475391485 := by decide +kernel
private theorem contact00ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact00) 0 4 = 6881888892148 :=
  contactColumnsWindow_fast contact00 0 4 6881888892148 (by decide +kernel)
private theorem contact00ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact00) 4 4 = 6543948677524 :=
  contactColumnsWindow_fast contact00 4 4 6543948677524 (by decide +kernel)
private theorem contact00ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact00) 8 4 = 6214549875956 :=
  contactColumnsWindow_fast contact00 8 4 6214549875956 (by decide +kernel)
private theorem contact00ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact00) 12 4 = 5893695316644 :=
  contactColumnsWindow_fast contact00 12 4 5893695316644 (by decide +kernel)
private theorem contact00ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact00) 16 4 = 5581383070897 :=
  contactColumnsWindow_fast contact00 16 4 5581383070897 (by decide +kernel)
private theorem contact00ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact00) 20 4 = 5277615096692 :=
  contactColumnsWindow_fast contact00 20 4 5277615096692 (by decide +kernel)
private theorem contact00ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact00) 24 4 = 4982405648732 :=
  contactColumnsWindow_fast contact00 24 4 4982405648732 (by decide +kernel)
private theorem contact00ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact00) 28 4 = 4695773248238 :=
  contactColumnsWindow_fast contact00 28 4 4695773248238 (by decide +kernel)
private theorem contact00ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact00) 32 4 = 4417688295524 :=
  contactColumnsWindow_fast contact00 32 4 4417688295524 (by decide +kernel)
private theorem contact00ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact00) 36 4 = 4148148774307 :=
  contactColumnsWindow_fast contact00 36 4 4148148774307 (by decide +kernel)
private theorem contact00ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact00) 40 4 = 3887156488828 :=
  contactColumnsWindow_fast contact00 40 4 3887156488828 (by decide +kernel)
private theorem contact00ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact00) 44 4 = 3634729200541 :=
  contactColumnsWindow_fast contact00 44 4 3634729200541 (by decide +kernel)
private theorem contact00ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact00) 48 4 = 3390879897850 :=
  contactColumnsWindow_fast contact00 48 4 3390879897850 (by decide +kernel)
private theorem contact00ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact00) 52 4 = 3155579575024 :=
  contactColumnsWindow_fast contact00 52 4 3155579575024 (by decide +kernel)
private theorem contact00ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact00) 56 4 = 2928828858219 :=
  contactColumnsWindow_fast contact00 56 4 2928828858219 (by decide +kernel)
private theorem contact00ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact00) 60 4 = 2710627515832 :=
  contactColumnsWindow_fast contact00 60 4 2710627515832 (by decide +kernel)
private theorem contact00ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact00) 64 4 = 2501000359747 :=
  contactColumnsWindow_fast contact00 64 4 2501000359747 (by decide +kernel)
private theorem contact00ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact00) 68 4 = 2299948803265 :=
  contactColumnsWindow_fast contact00 68 4 2299948803265 (by decide +kernel)
private theorem contact00ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact00) 72 4 = 2107451126556 :=
  contactColumnsWindow_fast contact00 72 4 2107451126556 (by decide +kernel)
private theorem contact00ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact00) 76 4 = 1923503605678 :=
  contactColumnsWindow_fast contact00 76 4 1923503605678 (by decide +kernel)
private theorem contact00ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact00) 80 4 = 1748105246140 :=
  contactColumnsWindow_fast contact00 80 4 1748105246140 (by decide +kernel)
private theorem contact00ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact00) 84 4 = 1581285807736 :=
  contactColumnsWindow_fast contact00 84 4 1581285807736 (by decide +kernel)
private theorem contact00ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact00) 88 4 = 1423037830571 :=
  contactColumnsWindow_fast contact00 88 4 1423037830571 (by decide +kernel)
private theorem contact00ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact00) 92 4 = 1273343341812 :=
  contactColumnsWindow_fast contact00 92 4 1273343341812 (by decide +kernel)
private theorem contact00ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact00) 96 4 = 1132198976914 :=
  contactColumnsWindow_fast contact00 96 4 1132198976914 (by decide +kernel)
private theorem contact00ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact00) 100 4 = 999604370819 :=
  contactColumnsWindow_fast contact00 100 4 999604370819 (by decide +kernel)
private theorem contact00ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact00) 104 4 = 875591974636 :=
  contactColumnsWindow_fast contact00 104 4 875591974636 (by decide +kernel)
private theorem contact00ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact00) 108 4 = 760147563305 :=
  contactColumnsWindow_fast contact00 108 4 760147563305 (by decide +kernel)
private theorem contact00ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact00) 112 4 = 653256185399 :=
  contactColumnsWindow_fast contact00 112 4 653256185399 (by decide +kernel)
private theorem contact00ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact00) 116 4 = 554915053588 :=
  contactColumnsWindow_fast contact00 116 4 554915053588 (by decide +kernel)
private theorem contact00ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact00) 120 4 = 465124707233 :=
  contactColumnsWindow_fast contact00 120 4 465124707233 (by decide +kernel)
private theorem contact00ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact00) 124 4 = 383918750800 :=
  contactColumnsWindow_fast contact00 124 4 383918750800 (by decide +kernel)
private theorem contact00ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact00) 128 4 = 311277952948 :=
  contactColumnsWindow_fast contact00 128 4 311277952948 (by decide +kernel)
private theorem contact00ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact00) 132 4 = 247189857441 :=
  contactColumnsWindow_fast contact00 132 4 247189857441 (by decide +kernel)
private theorem contact00ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact00) 136 4 = 191644811661 :=
  contactColumnsWindow_fast contact00 136 4 191644811661 (by decide +kernel)
private theorem contact00ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact00) 140 4 = 144541352607 :=
  contactColumnsWindow_fast contact00 140 4 144541352607 (by decide +kernel)
private theorem contact00ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact00) 144 4 = 105610314320 :=
  contactColumnsWindow_fast contact00 144 4 105610314320 (by decide +kernel)
private theorem contact00ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact00) 148 4 = 74354135462 :=
  contactColumnsWindow_fast contact00 148 4 74354135462 (by decide +kernel)
private theorem contact00ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact00) 152 4 = 50129273415 :=
  contactColumnsWindow_fast contact00 152 4 50129273415 (by decide +kernel)
private theorem contact00ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact00) 156 4 = 32139406481 :=
  contactColumnsWindow_fast contact00 156 4 32139406481 (by decide +kernel)
private theorem contact00ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact00) 160 2 = 11014851594 :=
  contactColumnsWindow_fast contact00 160 2 11014851594 (by decide +kernel)
private theorem contact00ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact00) 0 8 = 13425837569672 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 4 4 6881888892148 6543948677524 contact00ColumnsSlice0 contact00ColumnsSlice4
private theorem contact00ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact00) 8 8 = 12108245192600 :=
  combineSlices (auxiliaryColumnSlice contact00) 8 4 4 6214549875956 5893695316644 contact00ColumnsSlice8 contact00ColumnsSlice12
private theorem contact00ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact00) 16 8 = 10858998167589 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 4 4 5581383070897 5277615096692 contact00ColumnsSlice16 contact00ColumnsSlice20
private theorem contact00ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact00) 24 8 = 9678178896970 :=
  combineSlices (auxiliaryColumnSlice contact00) 24 4 4 4982405648732 4695773248238 contact00ColumnsSlice24 contact00ColumnsSlice28
private theorem contact00ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact00) 32 8 = 8565837069831 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 4 4 4417688295524 4148148774307 contact00ColumnsSlice32 contact00ColumnsSlice36
private theorem contact00ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact00) 40 8 = 7521885689369 :=
  combineSlices (auxiliaryColumnSlice contact00) 40 4 4 3887156488828 3634729200541 contact00ColumnsSlice40 contact00ColumnsSlice44
private theorem contact00ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact00) 48 8 = 6546459472874 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 4 4 3390879897850 3155579575024 contact00ColumnsSlice48 contact00ColumnsSlice52
private theorem contact00ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact00) 56 8 = 5639456374051 :=
  combineSlices (auxiliaryColumnSlice contact00) 56 4 4 2928828858219 2710627515832 contact00ColumnsSlice56 contact00ColumnsSlice60
private theorem contact00ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact00) 64 8 = 4800949163012 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 4 4 2501000359747 2299948803265 contact00ColumnsSlice64 contact00ColumnsSlice68
private theorem contact00ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact00) 72 8 = 4030954732234 :=
  combineSlices (auxiliaryColumnSlice contact00) 72 4 4 2107451126556 1923503605678 contact00ColumnsSlice72 contact00ColumnsSlice76
private theorem contact00ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact00) 80 8 = 3329391053876 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 4 4 1748105246140 1581285807736 contact00ColumnsSlice80 contact00ColumnsSlice84
private theorem contact00ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact00) 88 8 = 2696381172383 :=
  combineSlices (auxiliaryColumnSlice contact00) 88 4 4 1423037830571 1273343341812 contact00ColumnsSlice88 contact00ColumnsSlice92
private theorem contact00ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact00) 96 8 = 2131803347733 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 4 4 1132198976914 999604370819 contact00ColumnsSlice96 contact00ColumnsSlice100
private theorem contact00ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact00) 104 8 = 1635739537941 :=
  combineSlices (auxiliaryColumnSlice contact00) 104 4 4 875591974636 760147563305 contact00ColumnsSlice104 contact00ColumnsSlice108
private theorem contact00ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact00) 112 8 = 1208171238987 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 4 4 653256185399 554915053588 contact00ColumnsSlice112 contact00ColumnsSlice116
private theorem contact00ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact00) 120 8 = 849043458033 :=
  combineSlices (auxiliaryColumnSlice contact00) 120 4 4 465124707233 383918750800 contact00ColumnsSlice120 contact00ColumnsSlice124
private theorem contact00ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact00) 128 8 = 558467810389 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 4 4 311277952948 247189857441 contact00ColumnsSlice128 contact00ColumnsSlice132
private theorem contact00ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact00) 136 8 = 336186164268 :=
  combineSlices (auxiliaryColumnSlice contact00) 136 4 4 191644811661 144541352607 contact00ColumnsSlice136 contact00ColumnsSlice140
private theorem contact00ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact00) 144 8 = 179964449782 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 4 4 105610314320 74354135462 contact00ColumnsSlice144 contact00ColumnsSlice148
private theorem contact00ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact00) 152 8 = 82268679896 :=
  combineSlices (auxiliaryColumnSlice contact00) 152 4 4 50129273415 32139406481 contact00ColumnsSlice152 contact00ColumnsSlice156
private theorem contact00ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact00) 0 16 = 25534082762272 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 8 8 13425837569672 12108245192600 contact00ColumnsJoin0_8 contact00ColumnsJoin8_8
private theorem contact00ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact00) 16 16 = 20537177064559 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 8 8 10858998167589 9678178896970 contact00ColumnsJoin16_8 contact00ColumnsJoin24_8
private theorem contact00ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact00) 32 16 = 16087722759200 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 8 8 8565837069831 7521885689369 contact00ColumnsJoin32_8 contact00ColumnsJoin40_8
private theorem contact00ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact00) 48 16 = 12185915846925 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 8 8 6546459472874 5639456374051 contact00ColumnsJoin48_8 contact00ColumnsJoin56_8
private theorem contact00ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact00) 64 16 = 8831903895246 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 8 8 4800949163012 4030954732234 contact00ColumnsJoin64_8 contact00ColumnsJoin72_8
private theorem contact00ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact00) 80 16 = 6025772226259 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 8 8 3329391053876 2696381172383 contact00ColumnsJoin80_8 contact00ColumnsJoin88_8
private theorem contact00ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact00) 96 16 = 3767542885674 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 8 8 2131803347733 1635739537941 contact00ColumnsJoin96_8 contact00ColumnsJoin104_8
private theorem contact00ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact00) 112 16 = 2057214697020 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 8 8 1208171238987 849043458033 contact00ColumnsJoin112_8 contact00ColumnsJoin120_8
private theorem contact00ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact00) 128 16 = 894653974657 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 8 8 558467810389 336186164268 contact00ColumnsJoin128_8 contact00ColumnsJoin136_8
private theorem contact00ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact00) 144 16 = 262233129678 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 8 8 179964449782 82268679896 contact00ColumnsJoin144_8 contact00ColumnsJoin152_8
private theorem contact00ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact00) 0 32 = 46071259826831 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 16 16 25534082762272 20537177064559 contact00ColumnsJoin0_16 contact00ColumnsJoin16_16
private theorem contact00ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact00) 32 32 = 28273638606125 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 16 16 16087722759200 12185915846925 contact00ColumnsJoin32_16 contact00ColumnsJoin48_16
private theorem contact00ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact00) 64 32 = 14857676121505 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 16 16 8831903895246 6025772226259 contact00ColumnsJoin64_16 contact00ColumnsJoin80_16
private theorem contact00ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact00) 96 32 = 5824757582694 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 16 16 3767542885674 2057214697020 contact00ColumnsJoin96_16 contact00ColumnsJoin112_16
private theorem contact00ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact00) 128 32 = 1156887104335 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 16 16 894653974657 262233129678 contact00ColumnsJoin128_16 contact00ColumnsJoin144_16
private theorem contact00ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact00) 0 64 = 74344898432956 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 32 32 46071259826831 28273638606125 contact00ColumnsJoin0_32 contact00ColumnsJoin32_32
private theorem contact00ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact00) 64 64 = 20682433704199 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 32 32 14857676121505 5824757582694 contact00ColumnsJoin64_32 contact00ColumnsJoin96_32
private theorem contact00ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact00) 128 34 = 1167901955929 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 32 2 1156887104335 11014851594 contact00ColumnsJoin128_32 contact00ColumnsSlice160
private theorem contact00ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact00) 0 128 = 95027332137155 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 64 64 74344898432956 20682433704199 contact00ColumnsJoin0_64 contact00ColumnsJoin64_64
private theorem contact00ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact00) 0 162 = 96195234093084 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 128 34 95027332137155 1167901955929 contact00ColumnsJoin0_128 contact00ColumnsJoin128_34
private theorem contact00OrdinaryRanks : ordinaryRankBound contact00 = 9539884217 := by decide +kernel
private theorem contact00RanksSlice0 : sliceWindow (auxiliaryRankSlice contact00) 0 4 = 25947700 :=
  contactRankWindow_of_rec contact00 0 4 25947700 (by decide +kernel)
private theorem contact00RanksSlice4 : sliceWindow (auxiliaryRankSlice contact00) 4 4 = 24284500 :=
  contactRankWindow_of_rec contact00 4 4 24284500 (by decide +kernel)
private theorem contact00RanksSlice8 : sliceWindow (auxiliaryRankSlice contact00) 8 4 = 22680436 :=
  contactRankWindow_of_rec contact00 8 4 22680436 (by decide +kernel)
private theorem contact00RanksSlice12 : sliceWindow (auxiliaryRankSlice contact00) 12 4 = 21135508 :=
  contactRankWindow_of_rec contact00 12 4 21135508 (by decide +kernel)
private theorem contact00RanksSlice16 : sliceWindow (auxiliaryRankSlice contact00) 16 4 = 19649716 :=
  contactRankWindow_of_rec contact00 16 4 19649716 (by decide +kernel)
private theorem contact00RanksSlice20 : sliceWindow (auxiliaryRankSlice contact00) 20 4 = 18223060 :=
  contactRankWindow_of_rec contact00 20 4 18223060 (by decide +kernel)
private theorem contact00RanksSlice24 : sliceWindow (auxiliaryRankSlice contact00) 24 4 = 16855540 :=
  contactRankWindow_of_rec contact00 24 4 16855540 (by decide +kernel)
private theorem contact00RanksSlice28 : sliceWindow (auxiliaryRankSlice contact00) 28 4 = 15547156 :=
  contactRankWindow_of_rec contact00 28 4 15547156 (by decide +kernel)
private theorem contact00RanksSlice32 : sliceWindow (auxiliaryRankSlice contact00) 32 4 = 14297908 :=
  contactRankWindow_of_rec contact00 32 4 14297908 (by decide +kernel)
private theorem contact00RanksSlice36 : sliceWindow (auxiliaryRankSlice contact00) 36 4 = 13107796 :=
  contactRankWindow_of_rec contact00 36 4 13107796 (by decide +kernel)
private theorem contact00RanksSlice40 : sliceWindow (auxiliaryRankSlice contact00) 40 4 = 11976820 :=
  contactRankWindow_of_rec contact00 40 4 11976820 (by decide +kernel)
private theorem contact00RanksSlice44 : sliceWindow (auxiliaryRankSlice contact00) 44 4 = 10904980 :=
  contactRankWindow_of_rec contact00 44 4 10904980 (by decide +kernel)
private theorem contact00RanksSlice48 : sliceWindow (auxiliaryRankSlice contact00) 48 4 = 9892276 :=
  contactRankWindow_of_rec contact00 48 4 9892276 (by decide +kernel)
private theorem contact00RanksSlice52 : sliceWindow (auxiliaryRankSlice contact00) 52 4 = 8938708 :=
  contactRankWindow_of_rec contact00 52 4 8938708 (by decide +kernel)
private theorem contact00RanksSlice56 : sliceWindow (auxiliaryRankSlice contact00) 56 4 = 8043882 :=
  contactRankWindow_of_rec contact00 56 4 8043882 (by decide +kernel)
private theorem contact00RanksSlice60 : sliceWindow (auxiliaryRankSlice contact00) 60 4 = 7206684 :=
  contactRankWindow_of_rec contact00 60 4 7206684 (by decide +kernel)
private theorem contact00RanksSlice64 : sliceWindow (auxiliaryRankSlice contact00) 64 4 = 6425827 :=
  contactRankWindow_of_rec contact00 64 4 6425827 (by decide +kernel)
private theorem contact00RanksSlice68 : sliceWindow (auxiliaryRankSlice contact00) 68 4 = 5699744 :=
  contactRankWindow_of_rec contact00 68 4 5699744 (by decide +kernel)
private theorem contact00RanksSlice72 : sliceWindow (auxiliaryRankSlice contact00) 72 4 = 5026688 :=
  contactRankWindow_of_rec contact00 72 4 5026688 (by decide +kernel)
private theorem contact00RanksSlice76 : sliceWindow (auxiliaryRankSlice contact00) 76 4 = 4404859 :=
  contactRankWindow_of_rec contact00 76 4 4404859 (by decide +kernel)
private theorem contact00RanksSlice80 : sliceWindow (auxiliaryRankSlice contact00) 80 4 = 3832688 :=
  contactRankWindow_of_rec contact00 80 4 3832688 (by decide +kernel)
private theorem contact00RanksSlice84 : sliceWindow (auxiliaryRankSlice contact00) 84 4 = 3308292 :=
  contactRankWindow_of_rec contact00 84 4 3308292 (by decide +kernel)
private theorem contact00RanksSlice88 : sliceWindow (auxiliaryRankSlice contact00) 88 4 = 2829875 :=
  contactRankWindow_of_rec contact00 88 4 2829875 (by decide +kernel)
private theorem contact00RanksSlice92 : sliceWindow (auxiliaryRankSlice contact00) 92 4 = 2396000 :=
  contactRankWindow_of_rec contact00 92 4 2396000 (by decide +kernel)
private theorem contact00RanksSlice96 : sliceWindow (auxiliaryRankSlice contact00) 96 4 = 2004648 :=
  contactRankWindow_of_rec contact00 96 4 2004648 (by decide +kernel)
private theorem contact00RanksSlice100 : sliceWindow (auxiliaryRankSlice contact00) 100 4 = 1654027 :=
  contactRankWindow_of_rec contact00 100 4 1654027 (by decide +kernel)
private theorem contact00RanksSlice104 : sliceWindow (auxiliaryRankSlice contact00) 104 4 = 1342832 :=
  contactRankWindow_of_rec contact00 104 4 1342832 (by decide +kernel)
private theorem contact00RanksSlice108 : sliceWindow (auxiliaryRankSlice contact00) 108 4 = 1068908 :=
  contactRankWindow_of_rec contact00 108 4 1068908 (by decide +kernel)
private theorem contact00RanksSlice112 : sliceWindow (auxiliaryRankSlice contact00) 112 4 = 830467 :=
  contactRankWindow_of_rec contact00 112 4 830467 (by decide +kernel)
private theorem contact00RanksSlice116 : sliceWindow (auxiliaryRankSlice contact00) 116 4 = 626336 :=
  contactRankWindow_of_rec contact00 116 4 626336 (by decide +kernel)
private theorem contact00RanksSlice120 : sliceWindow (auxiliaryRankSlice contact00) 120 4 = 454224 :=
  contactRankWindow_of_rec contact00 120 4 454224 (by decide +kernel)
private theorem contact00RanksSlice124 : sliceWindow (auxiliaryRankSlice contact00) 124 4 = 312347 :=
  contactRankWindow_of_rec contact00 124 4 312347 (by decide +kernel)
private theorem contact00RanksSlice128 : sliceWindow (auxiliaryRankSlice contact00) 128 4 = 199664 :=
  contactRankWindow_of_rec contact00 128 4 199664 (by decide +kernel)
private theorem contact00RanksSlice132 : sliceWindow (auxiliaryRankSlice contact00) 132 4 = 113748 :=
  contactRankWindow_of_rec contact00 132 4 113748 (by decide +kernel)
private theorem contact00RanksSlice136 : sliceWindow (auxiliaryRankSlice contact00) 136 4 = 52819 :=
  contactRankWindow_of_rec contact00 136 4 52819 (by decide +kernel)
private theorem contact00RanksSlice140 : sliceWindow (auxiliaryRankSlice contact00) 140 4 = 16030 :=
  contactRankWindow_of_rec contact00 140 4 16030 (by decide +kernel)
private theorem contact00RanksSlice144 : sliceWindow (auxiliaryRankSlice contact00) 144 4 = 903 :=
  contactRankWindow_of_rec contact00 144 4 903 (by decide +kernel)
private theorem contact00RanksSlice148 : sliceWindow (auxiliaryRankSlice contact00) 148 14 = 0 :=
  contactRankWindow_of_rec contact00 148 14 0 (by decide +kernel)
private theorem contact00RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact00) 0 8 = 50232200 :=
  combineSlices (auxiliaryRankSlice contact00) 0 4 4 25947700 24284500 contact00RanksSlice0 contact00RanksSlice4
private theorem contact00RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact00) 8 8 = 43815944 :=
  combineSlices (auxiliaryRankSlice contact00) 8 4 4 22680436 21135508 contact00RanksSlice8 contact00RanksSlice12
private theorem contact00RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact00) 16 8 = 37872776 :=
  combineSlices (auxiliaryRankSlice contact00) 16 4 4 19649716 18223060 contact00RanksSlice16 contact00RanksSlice20
private theorem contact00RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact00) 24 8 = 32402696 :=
  combineSlices (auxiliaryRankSlice contact00) 24 4 4 16855540 15547156 contact00RanksSlice24 contact00RanksSlice28
private theorem contact00RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact00) 32 8 = 27405704 :=
  combineSlices (auxiliaryRankSlice contact00) 32 4 4 14297908 13107796 contact00RanksSlice32 contact00RanksSlice36
private theorem contact00RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact00) 40 8 = 22881800 :=
  combineSlices (auxiliaryRankSlice contact00) 40 4 4 11976820 10904980 contact00RanksSlice40 contact00RanksSlice44
private theorem contact00RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact00) 48 8 = 18830984 :=
  combineSlices (auxiliaryRankSlice contact00) 48 4 4 9892276 8938708 contact00RanksSlice48 contact00RanksSlice52
private theorem contact00RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact00) 56 8 = 15250566 :=
  combineSlices (auxiliaryRankSlice contact00) 56 4 4 8043882 7206684 contact00RanksSlice56 contact00RanksSlice60
private theorem contact00RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact00) 64 8 = 12125571 :=
  combineSlices (auxiliaryRankSlice contact00) 64 4 4 6425827 5699744 contact00RanksSlice64 contact00RanksSlice68
private theorem contact00RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact00) 72 8 = 9431547 :=
  combineSlices (auxiliaryRankSlice contact00) 72 4 4 5026688 4404859 contact00RanksSlice72 contact00RanksSlice76
private theorem contact00RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact00) 80 8 = 7140980 :=
  combineSlices (auxiliaryRankSlice contact00) 80 4 4 3832688 3308292 contact00RanksSlice80 contact00RanksSlice84
private theorem contact00RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact00) 88 8 = 5225875 :=
  combineSlices (auxiliaryRankSlice contact00) 88 4 4 2829875 2396000 contact00RanksSlice88 contact00RanksSlice92
private theorem contact00RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact00) 96 8 = 3658675 :=
  combineSlices (auxiliaryRankSlice contact00) 96 4 4 2004648 1654027 contact00RanksSlice96 contact00RanksSlice100
private theorem contact00RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact00) 104 8 = 2411740 :=
  combineSlices (auxiliaryRankSlice contact00) 104 4 4 1342832 1068908 contact00RanksSlice104 contact00RanksSlice108
private theorem contact00RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact00) 112 8 = 1456803 :=
  combineSlices (auxiliaryRankSlice contact00) 112 4 4 830467 626336 contact00RanksSlice112 contact00RanksSlice116
private theorem contact00RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact00) 120 8 = 766571 :=
  combineSlices (auxiliaryRankSlice contact00) 120 4 4 454224 312347 contact00RanksSlice120 contact00RanksSlice124
private theorem contact00RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact00) 128 8 = 313412 :=
  combineSlices (auxiliaryRankSlice contact00) 128 4 4 199664 113748 contact00RanksSlice128 contact00RanksSlice132
private theorem contact00RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact00) 136 8 = 68849 :=
  combineSlices (auxiliaryRankSlice contact00) 136 4 4 52819 16030 contact00RanksSlice136 contact00RanksSlice140
private theorem contact00RanksJoin144_18 : sliceWindow (auxiliaryRankSlice contact00) 144 18 = 903 :=
  combineSlices (auxiliaryRankSlice contact00) 144 4 14 903 0 contact00RanksSlice144 contact00RanksSlice148
private theorem contact00RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact00) 0 16 = 94048144 :=
  combineSlices (auxiliaryRankSlice contact00) 0 8 8 50232200 43815944 contact00RanksJoin0_8 contact00RanksJoin8_8
private theorem contact00RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact00) 16 16 = 70275472 :=
  combineSlices (auxiliaryRankSlice contact00) 16 8 8 37872776 32402696 contact00RanksJoin16_8 contact00RanksJoin24_8
private theorem contact00RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact00) 32 16 = 50287504 :=
  combineSlices (auxiliaryRankSlice contact00) 32 8 8 27405704 22881800 contact00RanksJoin32_8 contact00RanksJoin40_8
private theorem contact00RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact00) 48 16 = 34081550 :=
  combineSlices (auxiliaryRankSlice contact00) 48 8 8 18830984 15250566 contact00RanksJoin48_8 contact00RanksJoin56_8
private theorem contact00RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact00) 64 16 = 21557118 :=
  combineSlices (auxiliaryRankSlice contact00) 64 8 8 12125571 9431547 contact00RanksJoin64_8 contact00RanksJoin72_8
private theorem contact00RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact00) 80 16 = 12366855 :=
  combineSlices (auxiliaryRankSlice contact00) 80 8 8 7140980 5225875 contact00RanksJoin80_8 contact00RanksJoin88_8
private theorem contact00RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact00) 96 16 = 6070415 :=
  combineSlices (auxiliaryRankSlice contact00) 96 8 8 3658675 2411740 contact00RanksJoin96_8 contact00RanksJoin104_8
private theorem contact00RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact00) 112 16 = 2223374 :=
  combineSlices (auxiliaryRankSlice contact00) 112 8 8 1456803 766571 contact00RanksJoin112_8 contact00RanksJoin120_8
private theorem contact00RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact00) 128 16 = 382261 :=
  combineSlices (auxiliaryRankSlice contact00) 128 8 8 313412 68849 contact00RanksJoin128_8 contact00RanksJoin136_8
private theorem contact00RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact00) 0 32 = 164323616 :=
  combineSlices (auxiliaryRankSlice contact00) 0 16 16 94048144 70275472 contact00RanksJoin0_16 contact00RanksJoin16_16
private theorem contact00RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact00) 32 32 = 84369054 :=
  combineSlices (auxiliaryRankSlice contact00) 32 16 16 50287504 34081550 contact00RanksJoin32_16 contact00RanksJoin48_16
private theorem contact00RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact00) 64 32 = 33923973 :=
  combineSlices (auxiliaryRankSlice contact00) 64 16 16 21557118 12366855 contact00RanksJoin64_16 contact00RanksJoin80_16
private theorem contact00RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact00) 96 32 = 8293789 :=
  combineSlices (auxiliaryRankSlice contact00) 96 16 16 6070415 2223374 contact00RanksJoin96_16 contact00RanksJoin112_16
private theorem contact00RanksJoin128_34 : sliceWindow (auxiliaryRankSlice contact00) 128 34 = 383164 :=
  combineSlices (auxiliaryRankSlice contact00) 128 16 18 382261 903 contact00RanksJoin128_16 contact00RanksJoin144_18
private theorem contact00RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact00) 0 64 = 248692670 :=
  combineSlices (auxiliaryRankSlice contact00) 0 32 32 164323616 84369054 contact00RanksJoin0_32 contact00RanksJoin32_32
private theorem contact00RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact00) 64 64 = 42217762 :=
  combineSlices (auxiliaryRankSlice contact00) 64 32 32 33923973 8293789 contact00RanksJoin64_32 contact00RanksJoin96_32
private theorem contact00RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact00) 0 128 = 290910432 :=
  combineSlices (auxiliaryRankSlice contact00) 0 64 64 248692670 42217762 contact00RanksJoin0_64 contact00RanksJoin64_64
private theorem contact00RanksJoin0_162 : sliceWindow (auxiliaryRankSlice contact00) 0 162 = 291293596 :=
  combineSlices (auxiliaryRankSlice contact00) 0 128 34 290910432 383164 contact00RanksJoin0_128 contact00RanksJoin128_34
theorem contact00_margin : sourceMargin contact00 :=
  margin_of_checked_counts contact00 162 2480989475391485 96195234093084 9539884217 291293596 rfl contact00OrdinaryColumns contact00ColumnsJoin0_162 contact00OrdinaryRanks contact00RanksJoin0_162 (by decide +kernel)

private theorem contact02OrdinaryColumns : ordinaryColumnCount contact02 = 3614914112780516 := by decide +kernel
private theorem contact02ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact02) 0 4 = 11545774969080 :=
  contactColumnsWindow_fast contact02 0 4 11545774969080 (by decide +kernel)
private theorem contact02ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact02) 4 4 = 11029006318664 :=
  contactColumnsWindow_fast contact02 4 4 11029006318664 (by decide +kernel)
private theorem contact02ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact02) 8 4 = 10524133666648 :=
  contactColumnsWindow_fast contact02 8 4 10524133666648 (by decide +kernel)
private theorem contact02ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact02) 12 4 = 10031157013032 :=
  contactColumnsWindow_fast contact02 12 4 10031157013032 (by decide +kernel)
private theorem contact02ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact02) 16 4 = 9550076357816 :=
  contactColumnsWindow_fast contact02 16 4 9550076357816 (by decide +kernel)
private theorem contact02ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact02) 20 4 = 9080891701000 :=
  contactColumnsWindow_fast contact02 20 4 9080891701000 (by decide +kernel)
private theorem contact02ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact02) 24 4 = 8623603042584 :=
  contactColumnsWindow_fast contact02 24 4 8623603042584 (by decide +kernel)
private theorem contact02ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact02) 28 4 = 8178210382568 :=
  contactColumnsWindow_fast contact02 28 4 8178210382568 (by decide +kernel)
private theorem contact02ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact02) 32 4 = 7744713720952 :=
  contactColumnsWindow_fast contact02 32 4 7744713720952 (by decide +kernel)
private theorem contact02ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact02) 36 4 = 7323113057736 :=
  contactColumnsWindow_fast contact02 36 4 7323113057736 (by decide +kernel)
private theorem contact02ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact02) 40 4 = 6913408392920 :=
  contactColumnsWindow_fast contact02 40 4 6913408392920 (by decide +kernel)
private theorem contact02ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact02) 44 4 = 6515599726504 :=
  contactColumnsWindow_fast contact02 44 4 6515599726504 (by decide +kernel)
private theorem contact02ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact02) 48 4 = 6129687058488 :=
  contactColumnsWindow_fast contact02 48 4 6129687058488 (by decide +kernel)
private theorem contact02ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact02) 52 4 = 5755670388872 :=
  contactColumnsWindow_fast contact02 52 4 5755670388872 (by decide +kernel)
private theorem contact02ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact02) 56 4 = 5393557339634 :=
  contactColumnsWindow_fast contact02 56 4 5393557339634 (by decide +kernel)
private theorem contact02ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact02) 60 4 = 5043406951964 :=
  contactColumnsWindow_fast contact02 60 4 5043406951964 (by decide +kernel)
private theorem contact02ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact02) 64 4 = 4705168119519 :=
  contactColumnsWindow_fast contact02 64 4 4705168119519 (by decide +kernel)
private theorem contact02ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact02) 68 4 = 4378830012790 :=
  contactColumnsWindow_fast contact02 68 4 4378830012790 (by decide +kernel)
private theorem contact02ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact02) 72 4 = 4064390042301 :=
  contactColumnsWindow_fast contact02 72 4 4064390042301 (by decide +kernel)
private theorem contact02ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact02) 76 4 = 3761862489554 :=
  contactColumnsWindow_fast contact02 76 4 3761862489554 (by decide +kernel)
private theorem contact02ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact02) 80 4 = 3471300142612 :=
  contactColumnsWindow_fast contact02 80 4 3471300142612 (by decide +kernel)
private theorem contact02ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact02) 84 4 = 3192649965733 :=
  contactColumnsWindow_fast contact02 84 4 3192649965733 (by decide +kernel)
private theorem contact02ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact02) 88 4 = 2925903668526 :=
  contactColumnsWindow_fast contact02 88 4 2925903668526 (by decide +kernel)
private theorem contact02ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact02) 92 4 = 2671059520424 :=
  contactColumnsWindow_fast contact02 92 4 2671059520424 (by decide +kernel)
private theorem contact02ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact02) 96 4 = 2428135763992 :=
  contactColumnsWindow_fast contact02 96 4 2428135763992 (by decide +kernel)
private theorem contact02ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact02) 100 4 = 2197180744430 :=
  contactColumnsWindow_fast contact02 100 4 2197180744430 (by decide +kernel)
private theorem contact02ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact02) 104 4 = 1978138728958 :=
  contactColumnsWindow_fast contact02 104 4 1978138728958 (by decide +kernel)
private theorem contact02ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact02) 108 4 = 1771003538613 :=
  contactColumnsWindow_fast contact02 108 4 1771003538613 (by decide +kernel)
private theorem contact02ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact02) 112 4 = 1575775830045 :=
  contactColumnsWindow_fast contact02 112 4 1575775830045 (by decide +kernel)
private theorem contact02ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact02) 116 4 = 1392476031123 :=
  contactColumnsWindow_fast contact02 116 4 1392476031123 (by decide +kernel)
private theorem contact02ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact02) 120 4 = 1221141756593 :=
  contactColumnsWindow_fast contact02 120 4 1221141756593 (by decide +kernel)
private theorem contact02ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact02) 124 4 = 1061718191291 :=
  contactColumnsWindow_fast contact02 124 4 1061718191291 (by decide +kernel)
private theorem contact02ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact02) 128 4 = 914201552121 :=
  contactColumnsWindow_fast contact02 128 4 914201552121 (by decide +kernel)
private theorem contact02ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact02) 132 4 = 778592494551 :=
  contactColumnsWindow_fast contact02 132 4 778592494551 (by decide +kernel)
private theorem contact02ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact02) 136 4 = 654916846077 :=
  contactColumnsWindow_fast contact02 136 4 654916846077 (by decide +kernel)
private theorem contact02ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact02) 140 4 = 543202947455 :=
  contactColumnsWindow_fast contact02 140 4 543202947455 (by decide +kernel)
private theorem contact02ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact02) 144 4 = 443397858682 :=
  contactColumnsWindow_fast contact02 144 4 443397858682 (by decide +kernel)
private theorem contact02ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact02) 148 4 = 355475017572 :=
  contactColumnsWindow_fast contact02 148 4 355475017572 (by decide +kernel)
private theorem contact02ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact02) 152 4 = 279262322494 :=
  contactColumnsWindow_fast contact02 152 4 279262322494 (by decide +kernel)
private theorem contact02ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact02) 156 4 = 214415817122 :=
  contactColumnsWindow_fast contact02 156 4 214415817122 (by decide +kernel)
private theorem contact02ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact02) 160 4 = 160407308423 :=
  contactColumnsWindow_fast contact02 160 4 160407308423 (by decide +kernel)
private theorem contact02ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact02) 164 4 = 116479796165 :=
  contactColumnsWindow_fast contact02 164 4 116479796165 (by decide +kernel)
private theorem contact02ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact02) 168 4 = 81764162314 :=
  contactColumnsWindow_fast contact02 168 4 81764162314 (by decide +kernel)
private theorem contact02ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact02) 172 4 = 55231384110 :=
  contactColumnsWindow_fast contact02 172 4 55231384110 (by decide +kernel)
private theorem contact02ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact02) 0 8 = 22574781287744 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 4 4 11545774969080 11029006318664 contact02ColumnsSlice0 contact02ColumnsSlice4
private theorem contact02ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact02) 8 8 = 20555290679680 :=
  combineSlices (auxiliaryColumnSlice contact02) 8 4 4 10524133666648 10031157013032 contact02ColumnsSlice8 contact02ColumnsSlice12
private theorem contact02ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact02) 16 8 = 18630968058816 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 4 4 9550076357816 9080891701000 contact02ColumnsSlice16 contact02ColumnsSlice20
private theorem contact02ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact02) 24 8 = 16801813425152 :=
  combineSlices (auxiliaryColumnSlice contact02) 24 4 4 8623603042584 8178210382568 contact02ColumnsSlice24 contact02ColumnsSlice28
private theorem contact02ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact02) 32 8 = 15067826778688 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 4 4 7744713720952 7323113057736 contact02ColumnsSlice32 contact02ColumnsSlice36
private theorem contact02ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact02) 40 8 = 13429008119424 :=
  combineSlices (auxiliaryColumnSlice contact02) 40 4 4 6913408392920 6515599726504 contact02ColumnsSlice40 contact02ColumnsSlice44
private theorem contact02ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact02) 48 8 = 11885357447360 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 4 4 6129687058488 5755670388872 contact02ColumnsSlice48 contact02ColumnsSlice52
private theorem contact02ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact02) 56 8 = 10436964291598 :=
  combineSlices (auxiliaryColumnSlice contact02) 56 4 4 5393557339634 5043406951964 contact02ColumnsSlice56 contact02ColumnsSlice60
private theorem contact02ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact02) 64 8 = 9083998132309 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 4 4 4705168119519 4378830012790 contact02ColumnsSlice64 contact02ColumnsSlice68
private theorem contact02ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact02) 72 8 = 7826252531855 :=
  combineSlices (auxiliaryColumnSlice contact02) 72 4 4 4064390042301 3761862489554 contact02ColumnsSlice72 contact02ColumnsSlice76
private theorem contact02ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact02) 80 8 = 6663950108345 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 4 4 3471300142612 3192649965733 contact02ColumnsSlice80 contact02ColumnsSlice84
private theorem contact02ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact02) 88 8 = 5596963188950 :=
  combineSlices (auxiliaryColumnSlice contact02) 88 4 4 2925903668526 2671059520424 contact02ColumnsSlice88 contact02ColumnsSlice92
private theorem contact02ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact02) 96 8 = 4625316508422 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 4 4 2428135763992 2197180744430 contact02ColumnsSlice96 contact02ColumnsSlice100
private theorem contact02ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact02) 104 8 = 3749142267571 :=
  combineSlices (auxiliaryColumnSlice contact02) 104 4 4 1978138728958 1771003538613 contact02ColumnsSlice104 contact02ColumnsSlice108
private theorem contact02ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact02) 112 8 = 2968251861168 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 4 4 1575775830045 1392476031123 contact02ColumnsSlice112 contact02ColumnsSlice116
private theorem contact02ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact02) 120 8 = 2282859947884 :=
  combineSlices (auxiliaryColumnSlice contact02) 120 4 4 1221141756593 1061718191291 contact02ColumnsSlice120 contact02ColumnsSlice124
private theorem contact02ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact02) 128 8 = 1692794046672 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 4 4 914201552121 778592494551 contact02ColumnsSlice128 contact02ColumnsSlice132
private theorem contact02ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact02) 136 8 = 1198119793532 :=
  combineSlices (auxiliaryColumnSlice contact02) 136 4 4 654916846077 543202947455 contact02ColumnsSlice136 contact02ColumnsSlice140
private theorem contact02ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact02) 144 8 = 798872876254 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 4 4 443397858682 355475017572 contact02ColumnsSlice144 contact02ColumnsSlice148
private theorem contact02ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact02) 152 8 = 493678139616 :=
  combineSlices (auxiliaryColumnSlice contact02) 152 4 4 279262322494 214415817122 contact02ColumnsSlice152 contact02ColumnsSlice156
private theorem contact02ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact02) 160 8 = 276887104588 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 4 4 160407308423 116479796165 contact02ColumnsSlice160 contact02ColumnsSlice164
private theorem contact02ColumnsJoin168_8 : sliceWindow (auxiliaryColumnSlice contact02) 168 8 = 136995546424 :=
  combineSlices (auxiliaryColumnSlice contact02) 168 4 4 81764162314 55231384110 contact02ColumnsSlice168 contact02ColumnsSlice172
private theorem contact02ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact02) 0 16 = 43130071967424 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 8 8 22574781287744 20555290679680 contact02ColumnsJoin0_8 contact02ColumnsJoin8_8
private theorem contact02ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact02) 16 16 = 35432781483968 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 8 8 18630968058816 16801813425152 contact02ColumnsJoin16_8 contact02ColumnsJoin24_8
private theorem contact02ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact02) 32 16 = 28496834898112 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 8 8 15067826778688 13429008119424 contact02ColumnsJoin32_8 contact02ColumnsJoin40_8
private theorem contact02ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact02) 48 16 = 22322321738958 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 8 8 11885357447360 10436964291598 contact02ColumnsJoin48_8 contact02ColumnsJoin56_8
private theorem contact02ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact02) 64 16 = 16910250664164 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 8 8 9083998132309 7826252531855 contact02ColumnsJoin64_8 contact02ColumnsJoin72_8
private theorem contact02ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact02) 80 16 = 12260913297295 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 8 8 6663950108345 5596963188950 contact02ColumnsJoin80_8 contact02ColumnsJoin88_8
private theorem contact02ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact02) 96 16 = 8374458775993 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 8 8 4625316508422 3749142267571 contact02ColumnsJoin96_8 contact02ColumnsJoin104_8
private theorem contact02ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact02) 112 16 = 5251111809052 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 8 8 2968251861168 2282859947884 contact02ColumnsJoin112_8 contact02ColumnsJoin120_8
private theorem contact02ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact02) 128 16 = 2890913840204 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 8 8 1692794046672 1198119793532 contact02ColumnsJoin128_8 contact02ColumnsJoin136_8
private theorem contact02ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact02) 144 16 = 1292551015870 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 8 8 798872876254 493678139616 contact02ColumnsJoin144_8 contact02ColumnsJoin152_8
private theorem contact02ColumnsJoin160_16 : sliceWindow (auxiliaryColumnSlice contact02) 160 16 = 413882651012 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 8 8 276887104588 136995546424 contact02ColumnsJoin160_8 contact02ColumnsJoin168_8
private theorem contact02ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact02) 0 32 = 78562853451392 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 16 16 43130071967424 35432781483968 contact02ColumnsJoin0_16 contact02ColumnsJoin16_16
private theorem contact02ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact02) 32 32 = 50819156637070 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 16 16 28496834898112 22322321738958 contact02ColumnsJoin32_16 contact02ColumnsJoin48_16
private theorem contact02ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact02) 64 32 = 29171163961459 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 16 16 16910250664164 12260913297295 contact02ColumnsJoin64_16 contact02ColumnsJoin80_16
private theorem contact02ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact02) 96 32 = 13625570585045 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 16 16 8374458775993 5251111809052 contact02ColumnsJoin96_16 contact02ColumnsJoin112_16
private theorem contact02ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact02) 128 32 = 4183464856074 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 16 16 2890913840204 1292551015870 contact02ColumnsJoin128_16 contact02ColumnsJoin144_16
private theorem contact02ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact02) 0 64 = 129382010088462 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 32 32 78562853451392 50819156637070 contact02ColumnsJoin0_32 contact02ColumnsJoin32_32
private theorem contact02ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact02) 64 64 = 42796734546504 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 32 32 29171163961459 13625570585045 contact02ColumnsJoin64_32 contact02ColumnsJoin96_32
private theorem contact02ColumnsJoin128_48 : sliceWindow (auxiliaryColumnSlice contact02) 128 48 = 4597347507086 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 32 16 4183464856074 413882651012 contact02ColumnsJoin128_32 contact02ColumnsJoin160_16
private theorem contact02ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact02) 0 128 = 172178744634966 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 64 64 129382010088462 42796734546504 contact02ColumnsJoin0_64 contact02ColumnsJoin64_64
private theorem contact02ColumnsJoin0_176 : sliceWindow (auxiliaryColumnSlice contact02) 0 176 = 176776092142052 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 128 48 172178744634966 4597347507086 contact02ColumnsJoin0_128 contact02ColumnsJoin128_48
private theorem contact02OrdinaryRanks : ordinaryRankBound contact02 = 13924111557 := by decide +kernel
private theorem contact02RanksSlice0 : sliceWindow (auxiliaryRankSlice contact02) 0 4 = 43553844 :=
  contactRankWindow_of_rec contact02 0 4 43553844 (by decide +kernel)
private theorem contact02RanksSlice4 : sliceWindow (auxiliaryRankSlice contact02) 4 4 = 41021028 :=
  contactRankWindow_of_rec contact02 4 4 41021028 (by decide +kernel)
private theorem contact02RanksSlice8 : sliceWindow (auxiliaryRankSlice contact02) 8 4 = 38570580 :=
  contactRankWindow_of_rec contact02 8 4 38570580 (by decide +kernel)
private theorem contact02RanksSlice12 : sliceWindow (auxiliaryRankSlice contact02) 12 4 = 36202500 :=
  contactRankWindow_of_rec contact02 12 4 36202500 (by decide +kernel)
private theorem contact02RanksSlice16 : sliceWindow (auxiliaryRankSlice contact02) 16 4 = 33916788 :=
  contactRankWindow_of_rec contact02 16 4 33916788 (by decide +kernel)
private theorem contact02RanksSlice20 : sliceWindow (auxiliaryRankSlice contact02) 20 4 = 31713444 :=
  contactRankWindow_of_rec contact02 20 4 31713444 (by decide +kernel)
private theorem contact02RanksSlice24 : sliceWindow (auxiliaryRankSlice contact02) 24 4 = 29592468 :=
  contactRankWindow_of_rec contact02 24 4 29592468 (by decide +kernel)
private theorem contact02RanksSlice28 : sliceWindow (auxiliaryRankSlice contact02) 28 4 = 27553860 :=
  contactRankWindow_of_rec contact02 28 4 27553860 (by decide +kernel)
private theorem contact02RanksSlice32 : sliceWindow (auxiliaryRankSlice contact02) 32 4 = 25597620 :=
  contactRankWindow_of_rec contact02 32 4 25597620 (by decide +kernel)
private theorem contact02RanksSlice36 : sliceWindow (auxiliaryRankSlice contact02) 36 4 = 23723748 :=
  contactRankWindow_of_rec contact02 36 4 23723748 (by decide +kernel)
private theorem contact02RanksSlice40 : sliceWindow (auxiliaryRankSlice contact02) 40 4 = 21932244 :=
  contactRankWindow_of_rec contact02 40 4 21932244 (by decide +kernel)
private theorem contact02RanksSlice44 : sliceWindow (auxiliaryRankSlice contact02) 44 4 = 20223108 :=
  contactRankWindow_of_rec contact02 44 4 20223108 (by decide +kernel)
private theorem contact02RanksSlice48 : sliceWindow (auxiliaryRankSlice contact02) 48 4 = 18596340 :=
  contactRankWindow_of_rec contact02 48 4 18596340 (by decide +kernel)
private theorem contact02RanksSlice52 : sliceWindow (auxiliaryRankSlice contact02) 52 4 = 17051907 :=
  contactRankWindow_of_rec contact02 52 4 17051907 (by decide +kernel)
private theorem contact02RanksSlice56 : sliceWindow (auxiliaryRankSlice contact02) 56 4 = 15589111 :=
  contactRankWindow_of_rec contact02 56 4 15589111 (by decide +kernel)
private theorem contact02RanksSlice60 : sliceWindow (auxiliaryRankSlice contact02) 60 4 = 14206537 :=
  contactRankWindow_of_rec contact02 60 4 14206537 (by decide +kernel)
private theorem contact02RanksSlice64 : sliceWindow (auxiliaryRankSlice contact02) 64 4 = 12902711 :=
  contactRankWindow_of_rec contact02 64 4 12902711 (by decide +kernel)
private theorem contact02RanksSlice68 : sliceWindow (auxiliaryRankSlice contact02) 68 4 = 11675852 :=
  contactRankWindow_of_rec contact02 68 4 11675852 (by decide +kernel)
private theorem contact02RanksSlice72 : sliceWindow (auxiliaryRankSlice contact02) 72 4 = 10523989 :=
  contactRankWindow_of_rec contact02 72 4 10523989 (by decide +kernel)
private theorem contact02RanksSlice76 : sliceWindow (auxiliaryRankSlice contact02) 76 4 = 9444995 :=
  contactRankWindow_of_rec contact02 76 4 9444995 (by decide +kernel)
private theorem contact02RanksSlice80 : sliceWindow (auxiliaryRankSlice contact02) 80 4 = 8436772 :=
  contactRankWindow_of_rec contact02 80 4 8436772 (by decide +kernel)
private theorem contact02RanksSlice84 : sliceWindow (auxiliaryRankSlice contact02) 84 4 = 7497505 :=
  contactRankWindow_of_rec contact02 84 4 7497505 (by decide +kernel)
private theorem contact02RanksSlice88 : sliceWindow (auxiliaryRankSlice contact02) 88 4 = 6624911 :=
  contactRankWindow_of_rec contact02 88 4 6624911 (by decide +kernel)
private theorem contact02RanksSlice92 : sliceWindow (auxiliaryRankSlice contact02) 92 4 = 5816892 :=
  contactRankWindow_of_rec contact02 92 4 5816892 (by decide +kernel)
private theorem contact02RanksSlice96 : sliceWindow (auxiliaryRankSlice contact02) 96 4 = 5071789 :=
  contactRankWindow_of_rec contact02 96 4 5071789 (by decide +kernel)
private theorem contact02RanksSlice100 : sliceWindow (auxiliaryRankSlice contact02) 100 4 = 4387163 :=
  contactRankWindow_of_rec contact02 100 4 4387163 (by decide +kernel)
private theorem contact02RanksSlice104 : sliceWindow (auxiliaryRankSlice contact02) 104 4 = 3760916 :=
  contactRankWindow_of_rec contact02 104 4 3760916 (by decide +kernel)
private theorem contact02RanksSlice108 : sliceWindow (auxiliaryRankSlice contact02) 108 4 = 3191545 :=
  contactRankWindow_of_rec contact02 108 4 3191545 (by decide +kernel)
private theorem contact02RanksSlice112 : sliceWindow (auxiliaryRankSlice contact02) 112 4 = 2676455 :=
  contactRankWindow_of_rec contact02 112 4 2676455 (by decide +kernel)
private theorem contact02RanksSlice116 : sliceWindow (auxiliaryRankSlice contact02) 116 4 = 2213548 :=
  contactRankWindow_of_rec contact02 116 4 2213548 (by decide +kernel)
private theorem contact02RanksSlice120 : sliceWindow (auxiliaryRankSlice contact02) 120 4 = 1801477 :=
  contactRankWindow_of_rec contact02 120 4 1801477 (by decide +kernel)
private theorem contact02RanksSlice124 : sliceWindow (auxiliaryRankSlice contact02) 124 4 = 1437491 :=
  contactRankWindow_of_rec contact02 124 4 1437491 (by decide +kernel)
private theorem contact02RanksSlice128 : sliceWindow (auxiliaryRankSlice contact02) 128 4 = 1119492 :=
  contactRankWindow_of_rec contact02 128 4 1119492 (by decide +kernel)
private theorem contact02RanksSlice132 : sliceWindow (auxiliaryRankSlice contact02) 132 4 = 846289 :=
  contactRankWindow_of_rec contact02 132 4 846289 (by decide +kernel)
private theorem contact02RanksSlice136 : sliceWindow (auxiliaryRankSlice contact02) 136 4 = 614975 :=
  contactRankWindow_of_rec contact02 136 4 614975 (by decide +kernel)
private theorem contact02RanksSlice140 : sliceWindow (auxiliaryRankSlice contact02) 140 4 = 423452 :=
  contactRankWindow_of_rec contact02 140 4 423452 (by decide +kernel)
private theorem contact02RanksSlice144 : sliceWindow (auxiliaryRankSlice contact02) 144 4 = 270685 :=
  contactRankWindow_of_rec contact02 144 4 270685 (by decide +kernel)
private theorem contact02RanksSlice148 : sliceWindow (auxiliaryRankSlice contact02) 148 4 = 153674 :=
  contactRankWindow_of_rec contact02 148 4 153674 (by decide +kernel)
private theorem contact02RanksSlice152 : sliceWindow (auxiliaryRankSlice contact02) 152 4 = 70801 :=
  contactRankWindow_of_rec contact02 152 4 70801 (by decide +kernel)
private theorem contact02RanksSlice156 : sliceWindow (auxiliaryRankSlice contact02) 156 4 = 21315 :=
  contactRankWindow_of_rec contact02 156 4 21315 (by decide +kernel)
private theorem contact02RanksSlice160 : sliceWindow (auxiliaryRankSlice contact02) 160 4 = 1196 :=
  contactRankWindow_of_rec contact02 160 4 1196 (by decide +kernel)
private theorem contact02RanksSlice164 : sliceWindow (auxiliaryRankSlice contact02) 164 12 = 0 :=
  contactRankWindow_of_rec contact02 164 12 0 (by decide +kernel)
private theorem contact02RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact02) 0 8 = 84574872 :=
  combineSlices (auxiliaryRankSlice contact02) 0 4 4 43553844 41021028 contact02RanksSlice0 contact02RanksSlice4
private theorem contact02RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact02) 8 8 = 74773080 :=
  combineSlices (auxiliaryRankSlice contact02) 8 4 4 38570580 36202500 contact02RanksSlice8 contact02RanksSlice12
private theorem contact02RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact02) 16 8 = 65630232 :=
  combineSlices (auxiliaryRankSlice contact02) 16 4 4 33916788 31713444 contact02RanksSlice16 contact02RanksSlice20
private theorem contact02RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact02) 24 8 = 57146328 :=
  combineSlices (auxiliaryRankSlice contact02) 24 4 4 29592468 27553860 contact02RanksSlice24 contact02RanksSlice28
private theorem contact02RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact02) 32 8 = 49321368 :=
  combineSlices (auxiliaryRankSlice contact02) 32 4 4 25597620 23723748 contact02RanksSlice32 contact02RanksSlice36
private theorem contact02RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact02) 40 8 = 42155352 :=
  combineSlices (auxiliaryRankSlice contact02) 40 4 4 21932244 20223108 contact02RanksSlice40 contact02RanksSlice44
private theorem contact02RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact02) 48 8 = 35648247 :=
  combineSlices (auxiliaryRankSlice contact02) 48 4 4 18596340 17051907 contact02RanksSlice48 contact02RanksSlice52
private theorem contact02RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact02) 56 8 = 29795648 :=
  combineSlices (auxiliaryRankSlice contact02) 56 4 4 15589111 14206537 contact02RanksSlice56 contact02RanksSlice60
private theorem contact02RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact02) 64 8 = 24578563 :=
  combineSlices (auxiliaryRankSlice contact02) 64 4 4 12902711 11675852 contact02RanksSlice64 contact02RanksSlice68
private theorem contact02RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact02) 72 8 = 19968984 :=
  combineSlices (auxiliaryRankSlice contact02) 72 4 4 10523989 9444995 contact02RanksSlice72 contact02RanksSlice76
private theorem contact02RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact02) 80 8 = 15934277 :=
  combineSlices (auxiliaryRankSlice contact02) 80 4 4 8436772 7497505 contact02RanksSlice80 contact02RanksSlice84
private theorem contact02RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact02) 88 8 = 12441803 :=
  combineSlices (auxiliaryRankSlice contact02) 88 4 4 6624911 5816892 contact02RanksSlice88 contact02RanksSlice92
private theorem contact02RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact02) 96 8 = 9458952 :=
  combineSlices (auxiliaryRankSlice contact02) 96 4 4 5071789 4387163 contact02RanksSlice96 contact02RanksSlice100
private theorem contact02RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact02) 104 8 = 6952461 :=
  combineSlices (auxiliaryRankSlice contact02) 104 4 4 3760916 3191545 contact02RanksSlice104 contact02RanksSlice108
private theorem contact02RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact02) 112 8 = 4890003 :=
  combineSlices (auxiliaryRankSlice contact02) 112 4 4 2676455 2213548 contact02RanksSlice112 contact02RanksSlice116
private theorem contact02RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact02) 120 8 = 3238968 :=
  combineSlices (auxiliaryRankSlice contact02) 120 4 4 1801477 1437491 contact02RanksSlice120 contact02RanksSlice124
private theorem contact02RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact02) 128 8 = 1965781 :=
  combineSlices (auxiliaryRankSlice contact02) 128 4 4 1119492 846289 contact02RanksSlice128 contact02RanksSlice132
private theorem contact02RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact02) 136 8 = 1038427 :=
  combineSlices (auxiliaryRankSlice contact02) 136 4 4 614975 423452 contact02RanksSlice136 contact02RanksSlice140
private theorem contact02RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact02) 144 8 = 424359 :=
  combineSlices (auxiliaryRankSlice contact02) 144 4 4 270685 153674 contact02RanksSlice144 contact02RanksSlice148
private theorem contact02RanksJoin152_8 : sliceWindow (auxiliaryRankSlice contact02) 152 8 = 92116 :=
  combineSlices (auxiliaryRankSlice contact02) 152 4 4 70801 21315 contact02RanksSlice152 contact02RanksSlice156
private theorem contact02RanksJoin160_16 : sliceWindow (auxiliaryRankSlice contact02) 160 16 = 1196 :=
  combineSlices (auxiliaryRankSlice contact02) 160 4 12 1196 0 contact02RanksSlice160 contact02RanksSlice164
private theorem contact02RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact02) 0 16 = 159347952 :=
  combineSlices (auxiliaryRankSlice contact02) 0 8 8 84574872 74773080 contact02RanksJoin0_8 contact02RanksJoin8_8
private theorem contact02RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact02) 16 16 = 122776560 :=
  combineSlices (auxiliaryRankSlice contact02) 16 8 8 65630232 57146328 contact02RanksJoin16_8 contact02RanksJoin24_8
private theorem contact02RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact02) 32 16 = 91476720 :=
  combineSlices (auxiliaryRankSlice contact02) 32 8 8 49321368 42155352 contact02RanksJoin32_8 contact02RanksJoin40_8
private theorem contact02RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact02) 48 16 = 65443895 :=
  combineSlices (auxiliaryRankSlice contact02) 48 8 8 35648247 29795648 contact02RanksJoin48_8 contact02RanksJoin56_8
private theorem contact02RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact02) 64 16 = 44547547 :=
  combineSlices (auxiliaryRankSlice contact02) 64 8 8 24578563 19968984 contact02RanksJoin64_8 contact02RanksJoin72_8
private theorem contact02RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact02) 80 16 = 28376080 :=
  combineSlices (auxiliaryRankSlice contact02) 80 8 8 15934277 12441803 contact02RanksJoin80_8 contact02RanksJoin88_8
private theorem contact02RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact02) 96 16 = 16411413 :=
  combineSlices (auxiliaryRankSlice contact02) 96 8 8 9458952 6952461 contact02RanksJoin96_8 contact02RanksJoin104_8
private theorem contact02RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact02) 112 16 = 8128971 :=
  combineSlices (auxiliaryRankSlice contact02) 112 8 8 4890003 3238968 contact02RanksJoin112_8 contact02RanksJoin120_8
private theorem contact02RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact02) 128 16 = 3004208 :=
  combineSlices (auxiliaryRankSlice contact02) 128 8 8 1965781 1038427 contact02RanksJoin128_8 contact02RanksJoin136_8
private theorem contact02RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact02) 144 16 = 516475 :=
  combineSlices (auxiliaryRankSlice contact02) 144 8 8 424359 92116 contact02RanksJoin144_8 contact02RanksJoin152_8
private theorem contact02RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact02) 0 32 = 282124512 :=
  combineSlices (auxiliaryRankSlice contact02) 0 16 16 159347952 122776560 contact02RanksJoin0_16 contact02RanksJoin16_16
private theorem contact02RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact02) 32 32 = 156920615 :=
  combineSlices (auxiliaryRankSlice contact02) 32 16 16 91476720 65443895 contact02RanksJoin32_16 contact02RanksJoin48_16
private theorem contact02RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact02) 64 32 = 72923627 :=
  combineSlices (auxiliaryRankSlice contact02) 64 16 16 44547547 28376080 contact02RanksJoin64_16 contact02RanksJoin80_16
private theorem contact02RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact02) 96 32 = 24540384 :=
  combineSlices (auxiliaryRankSlice contact02) 96 16 16 16411413 8128971 contact02RanksJoin96_16 contact02RanksJoin112_16
private theorem contact02RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact02) 128 32 = 3520683 :=
  combineSlices (auxiliaryRankSlice contact02) 128 16 16 3004208 516475 contact02RanksJoin128_16 contact02RanksJoin144_16
private theorem contact02RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact02) 0 64 = 439045127 :=
  combineSlices (auxiliaryRankSlice contact02) 0 32 32 282124512 156920615 contact02RanksJoin0_32 contact02RanksJoin32_32
private theorem contact02RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact02) 64 64 = 97464011 :=
  combineSlices (auxiliaryRankSlice contact02) 64 32 32 72923627 24540384 contact02RanksJoin64_32 contact02RanksJoin96_32
private theorem contact02RanksJoin128_48 : sliceWindow (auxiliaryRankSlice contact02) 128 48 = 3521879 :=
  combineSlices (auxiliaryRankSlice contact02) 128 32 16 3520683 1196 contact02RanksJoin128_32 contact02RanksJoin160_16
private theorem contact02RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact02) 0 128 = 536509138 :=
  combineSlices (auxiliaryRankSlice contact02) 0 64 64 439045127 97464011 contact02RanksJoin0_64 contact02RanksJoin64_64
private theorem contact02RanksJoin0_176 : sliceWindow (auxiliaryRankSlice contact02) 0 176 = 540031017 :=
  combineSlices (auxiliaryRankSlice contact02) 0 128 48 536509138 3521879 contact02RanksJoin0_128 contact02RanksJoin128_48
theorem contact02_margin : sourceMargin contact02 :=
  margin_of_checked_counts contact02 176 3614914112780516 176776092142052 13924111557 540031017 rfl contact02OrdinaryColumns contact02ColumnsJoin0_176 contact02OrdinaryRanks contact02RanksJoin0_176 (by decide +kernel)

private theorem contact04OrdinaryColumns : ordinaryColumnCount contact04 = 1826030831205307 := by decide +kernel
private theorem contact04ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact04) 0 4 = 8026701569250 :=
  contactColumnsWindow_fast contact04 0 4 8026701569250 (by decide +kernel)
private theorem contact04ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact04) 4 4 = 7637611868210 :=
  contactColumnsWindow_fast contact04 4 4 7637611868210 (by decide +kernel)
private theorem contact04ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact04) 8 4 = 7258263507426 :=
  contactColumnsWindow_fast contact04 8 4 7258263507426 (by decide +kernel)
private theorem contact04ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact04) 12 4 = 6888653581303 :=
  contactColumnsWindow_fast contact04 12 4 6888653581303 (by decide +kernel)
private theorem contact04ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact04) 16 4 = 6528752703650 :=
  contactColumnsWindow_fast contact04 16 4 6528752703650 (by decide +kernel)
private theorem contact04ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact04) 20 4 = 6178562040502 :=
  contactColumnsWindow_fast contact04 20 4 6178562040502 (by decide +kernel)
private theorem contact04ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact04) 24 4 = 5838083724058 :=
  contactColumnsWindow_fast contact04 24 4 5838083724058 (by decide +kernel)
private theorem contact04ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact04) 28 4 = 5507355169790 :=
  contactColumnsWindow_fast contact04 28 4 5507355169790 (by decide +kernel)
private theorem contact04ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact04) 32 4 = 5186363450805 :=
  contactColumnsWindow_fast contact04 32 4 5186363450805 (by decide +kernel)
private theorem contact04ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact04) 36 4 = 4875083037178 :=
  contactColumnsWindow_fast contact04 36 4 4875083037178 (by decide +kernel)
private theorem contact04ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact04) 40 4 = 4573517882426 :=
  contactColumnsWindow_fast contact04 40 4 4573517882426 (by decide +kernel)
private theorem contact04ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact04) 44 4 = 4281668415276 :=
  contactColumnsWindow_fast contact04 44 4 4281668415276 (by decide +kernel)
private theorem contact04ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact04) 48 4 = 3999576942362 :=
  contactColumnsWindow_fast contact04 48 4 3999576942362 (by decide +kernel)
private theorem contact04ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact04) 52 4 = 3727220030755 :=
  contactColumnsWindow_fast contact04 52 4 3727220030755 (by decide +kernel)
private theorem contact04ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact04) 56 4 = 3464579266597 :=
  contactColumnsWindow_fast contact04 56 4 3464579266597 (by decide +kernel)
private theorem contact04ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact04) 60 4 = 3211654068218 :=
  contactColumnsWindow_fast contact04 60 4 3211654068218 (by decide +kernel)
private theorem contact04ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact04) 64 4 = 2968445905404 :=
  contactColumnsWindow_fast contact04 64 4 2968445905404 (by decide +kernel)
private theorem contact04ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact04) 68 4 = 2734998630494 :=
  contactColumnsWindow_fast contact04 68 4 2734998630494 (by decide +kernel)
private theorem contact04ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact04) 72 4 = 2511281720922 :=
  contactColumnsWindow_fast contact04 72 4 2511281720922 (by decide +kernel)
private theorem contact04ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact04) 76 4 = 2297280921571 :=
  contactColumnsWindow_fast contact04 76 4 2297280921571 (by decide +kernel)
private theorem contact04ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact04) 80 4 = 2092995491810 :=
  contactColumnsWindow_fast contact04 80 4 2092995491810 (by decide +kernel)
private theorem contact04ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact04) 84 4 = 1898428911595 :=
  contactColumnsWindow_fast contact04 84 4 1898428911595 (by decide +kernel)
private theorem contact04ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact04) 88 4 = 1713625665147 :=
  contactColumnsWindow_fast contact04 88 4 1713625665147 (by decide +kernel)
private theorem contact04ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact04) 92 4 = 1538548805574 :=
  contactColumnsWindow_fast contact04 92 4 1538548805574 (by decide +kernel)
private theorem contact04ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact04) 96 4 = 1373187814345 :=
  contactColumnsWindow_fast contact04 96 4 1373187814345 (by decide +kernel)
private theorem contact04ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact04) 100 4 = 1217542198926 :=
  contactColumnsWindow_fast contact04 100 4 1217542198926 (by decide +kernel)
private theorem contact04ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact04) 104 4 = 1071618611890 :=
  contactColumnsWindow_fast contact04 104 4 1071618611890 (by decide +kernel)
private theorem contact04ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact04) 108 4 = 935457972081 :=
  contactColumnsWindow_fast contact04 108 4 935457972081 (by decide +kernel)
private theorem contact04ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact04) 112 4 = 809021128026 :=
  contactColumnsWindow_fast contact04 112 4 809021128026 (by decide +kernel)
private theorem contact04ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact04) 116 4 = 692300109054 :=
  contactColumnsWindow_fast contact04 116 4 692300109054 (by decide +kernel)
private theorem contact04ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact04) 120 4 = 585294236382 :=
  contactColumnsWindow_fast contact04 120 4 585294236382 (by decide +kernel)
private theorem contact04ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact04) 124 4 = 488013563470 :=
  contactColumnsWindow_fast contact04 124 4 488013563470 (by decide +kernel)
private theorem contact04ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact04) 128 4 = 400495625186 :=
  contactColumnsWindow_fast contact04 128 4 400495625186 (by decide +kernel)
private theorem contact04ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact04) 132 4 = 322698808563 :=
  contactColumnsWindow_fast contact04 132 4 322698808563 (by decide +kernel)
private theorem contact04ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact04) 136 4 = 254611670635 :=
  contactColumnsWindow_fast contact04 136 4 254611670635 (by decide +kernel)
private theorem contact04ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact04) 140 4 = 196136586070 :=
  contactColumnsWindow_fast contact04 140 4 196136586070 (by decide +kernel)
private theorem contact04ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact04) 144 4 = 146995348182 :=
  contactColumnsWindow_fast contact04 144 4 146995348182 (by decide +kernel)
private theorem contact04ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact04) 148 4 = 106753384992 :=
  contactColumnsWindow_fast contact04 148 4 106753384992 (by decide +kernel)
private theorem contact04ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact04) 152 4 = 74739934835 :=
  contactColumnsWindow_fast contact04 152 4 74739934835 (by decide +kernel)
private theorem contact04ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact04) 156 4 = 50162253356 :=
  contactColumnsWindow_fast contact04 156 4 50162253356 (by decide +kernel)
private theorem contact04ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact04) 0 8 = 15664313437460 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 4 4 8026701569250 7637611868210 contact04ColumnsSlice0 contact04ColumnsSlice4
private theorem contact04ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact04) 8 8 = 14146917088729 :=
  combineSlices (auxiliaryColumnSlice contact04) 8 4 4 7258263507426 6888653581303 contact04ColumnsSlice8 contact04ColumnsSlice12
private theorem contact04ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact04) 16 8 = 12707314744152 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 4 4 6528752703650 6178562040502 contact04ColumnsSlice16 contact04ColumnsSlice20
private theorem contact04ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact04) 24 8 = 11345438893848 :=
  combineSlices (auxiliaryColumnSlice contact04) 24 4 4 5838083724058 5507355169790 contact04ColumnsSlice24 contact04ColumnsSlice28
private theorem contact04ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact04) 32 8 = 10061446487983 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 4 4 5186363450805 4875083037178 contact04ColumnsSlice32 contact04ColumnsSlice36
private theorem contact04ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact04) 40 8 = 8855186297702 :=
  combineSlices (auxiliaryColumnSlice contact04) 40 4 4 4573517882426 4281668415276 contact04ColumnsSlice40 contact04ColumnsSlice44
private theorem contact04ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact04) 48 8 = 7726796973117 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 4 4 3999576942362 3727220030755 contact04ColumnsSlice48 contact04ColumnsSlice52
private theorem contact04ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact04) 56 8 = 6676233334815 :=
  combineSlices (auxiliaryColumnSlice contact04) 56 4 4 3464579266597 3211654068218 contact04ColumnsSlice56 contact04ColumnsSlice60
private theorem contact04ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact04) 64 8 = 5703444535898 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 4 4 2968445905404 2734998630494 contact04ColumnsSlice64 contact04ColumnsSlice68
private theorem contact04ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact04) 72 8 = 4808562642493 :=
  combineSlices (auxiliaryColumnSlice contact04) 72 4 4 2511281720922 2297280921571 contact04ColumnsSlice72 contact04ColumnsSlice76
private theorem contact04ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact04) 80 8 = 3991424403405 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 4 4 2092995491810 1898428911595 contact04ColumnsSlice80 contact04ColumnsSlice84
private theorem contact04ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact04) 88 8 = 3252174470721 :=
  combineSlices (auxiliaryColumnSlice contact04) 88 4 4 1713625665147 1538548805574 contact04ColumnsSlice88 contact04ColumnsSlice92
private theorem contact04ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact04) 96 8 = 2590730013271 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 4 4 1373187814345 1217542198926 contact04ColumnsSlice96 contact04ColumnsSlice100
private theorem contact04ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact04) 104 8 = 2007076583971 :=
  combineSlices (auxiliaryColumnSlice contact04) 104 4 4 1071618611890 935457972081 contact04ColumnsSlice104 contact04ColumnsSlice108
private theorem contact04ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact04) 112 8 = 1501321237080 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 4 4 809021128026 692300109054 contact04ColumnsSlice112 contact04ColumnsSlice116
private theorem contact04ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact04) 120 8 = 1073307799852 :=
  combineSlices (auxiliaryColumnSlice contact04) 120 4 4 585294236382 488013563470 contact04ColumnsSlice120 contact04ColumnsSlice124
private theorem contact04ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact04) 128 8 = 723194433749 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 4 4 400495625186 322698808563 contact04ColumnsSlice128 contact04ColumnsSlice132
private theorem contact04ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact04) 136 8 = 450748256705 :=
  combineSlices (auxiliaryColumnSlice contact04) 136 4 4 254611670635 196136586070 contact04ColumnsSlice136 contact04ColumnsSlice140
private theorem contact04ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact04) 144 8 = 253748733174 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 4 4 146995348182 106753384992 contact04ColumnsSlice144 contact04ColumnsSlice148
private theorem contact04ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact04) 152 8 = 124902188191 :=
  combineSlices (auxiliaryColumnSlice contact04) 152 4 4 74739934835 50162253356 contact04ColumnsSlice152 contact04ColumnsSlice156
private theorem contact04ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact04) 0 16 = 29811230526189 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 8 8 15664313437460 14146917088729 contact04ColumnsJoin0_8 contact04ColumnsJoin8_8
private theorem contact04ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact04) 16 16 = 24052753638000 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 8 8 12707314744152 11345438893848 contact04ColumnsJoin16_8 contact04ColumnsJoin24_8
private theorem contact04ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact04) 32 16 = 18916632785685 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 8 8 10061446487983 8855186297702 contact04ColumnsJoin32_8 contact04ColumnsJoin40_8
private theorem contact04ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact04) 48 16 = 14403030307932 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 8 8 7726796973117 6676233334815 contact04ColumnsJoin48_8 contact04ColumnsJoin56_8
private theorem contact04ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact04) 64 16 = 10512007178391 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 8 8 5703444535898 4808562642493 contact04ColumnsJoin64_8 contact04ColumnsJoin72_8
private theorem contact04ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact04) 80 16 = 7243598874126 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 8 8 3991424403405 3252174470721 contact04ColumnsJoin80_8 contact04ColumnsJoin88_8
private theorem contact04ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact04) 96 16 = 4597806597242 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 8 8 2590730013271 2007076583971 contact04ColumnsJoin96_8 contact04ColumnsJoin104_8
private theorem contact04ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact04) 112 16 = 2574629036932 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 8 8 1501321237080 1073307799852 contact04ColumnsJoin112_8 contact04ColumnsJoin120_8
private theorem contact04ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact04) 128 16 = 1173942690454 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 8 8 723194433749 450748256705 contact04ColumnsJoin128_8 contact04ColumnsJoin136_8
private theorem contact04ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact04) 144 16 = 378650921365 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 8 8 253748733174 124902188191 contact04ColumnsJoin144_8 contact04ColumnsJoin152_8
private theorem contact04ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact04) 0 32 = 53863984164189 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 16 16 29811230526189 24052753638000 contact04ColumnsJoin0_16 contact04ColumnsJoin16_16
private theorem contact04ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact04) 32 32 = 33319663093617 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 16 16 18916632785685 14403030307932 contact04ColumnsJoin32_16 contact04ColumnsJoin48_16
private theorem contact04ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact04) 64 32 = 17755606052517 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 16 16 10512007178391 7243598874126 contact04ColumnsJoin64_16 contact04ColumnsJoin80_16
private theorem contact04ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact04) 96 32 = 7172435634174 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 16 16 4597806597242 2574629036932 contact04ColumnsJoin96_16 contact04ColumnsJoin112_16
private theorem contact04ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact04) 128 32 = 1552593611819 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 16 16 1173942690454 378650921365 contact04ColumnsJoin128_16 contact04ColumnsJoin144_16
private theorem contact04ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact04) 0 64 = 87183647257806 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 32 32 53863984164189 33319663093617 contact04ColumnsJoin0_32 contact04ColumnsJoin32_32
private theorem contact04ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact04) 64 64 = 24928041686691 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 32 32 17755606052517 7172435634174 contact04ColumnsJoin64_32 contact04ColumnsJoin96_32
private theorem contact04ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact04) 0 128 = 112111688944497 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 64 64 87183647257806 24928041686691 contact04ColumnsJoin0_64 contact04ColumnsJoin64_64
private theorem contact04ColumnsJoin0_160 : sliceWindow (auxiliaryColumnSlice contact04) 0 160 = 113664282556316 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 128 32 112111688944497 1552593611819 contact04ColumnsJoin0_128 contact04ColumnsJoin128_32
private theorem contact04OrdinaryRanks : ordinaryRankBound contact04 = 7053419077 := by decide +kernel
private theorem contact04RanksSlice0 : sliceWindow (auxiliaryRankSlice contact04) 0 4 = 30233214 :=
  contactRankWindow_of_rec contact04 0 4 30233214 (by decide +kernel)
private theorem contact04RanksSlice4 : sliceWindow (auxiliaryRankSlice contact04) 4 4 = 28326414 :=
  contactRankWindow_of_rec contact04 4 4 28326414 (by decide +kernel)
private theorem contact04RanksSlice8 : sliceWindow (auxiliaryRankSlice contact04) 8 4 = 26486814 :=
  contactRankWindow_of_rec contact04 8 4 26486814 (by decide +kernel)
private theorem contact04RanksSlice12 : sliceWindow (auxiliaryRankSlice contact04) 12 4 = 24714414 :=
  contactRankWindow_of_rec contact04 12 4 24714414 (by decide +kernel)
private theorem contact04RanksSlice16 : sliceWindow (auxiliaryRankSlice contact04) 16 4 = 23009214 :=
  contactRankWindow_of_rec contact04 16 4 23009214 (by decide +kernel)
private theorem contact04RanksSlice20 : sliceWindow (auxiliaryRankSlice contact04) 20 4 = 21371214 :=
  contactRankWindow_of_rec contact04 20 4 21371214 (by decide +kernel)
private theorem contact04RanksSlice24 : sliceWindow (auxiliaryRankSlice contact04) 24 4 = 19800414 :=
  contactRankWindow_of_rec contact04 24 4 19800414 (by decide +kernel)
private theorem contact04RanksSlice28 : sliceWindow (auxiliaryRankSlice contact04) 28 4 = 18296814 :=
  contactRankWindow_of_rec contact04 28 4 18296814 (by decide +kernel)
private theorem contact04RanksSlice32 : sliceWindow (auxiliaryRankSlice contact04) 32 4 = 16860414 :=
  contactRankWindow_of_rec contact04 32 4 16860414 (by decide +kernel)
private theorem contact04RanksSlice36 : sliceWindow (auxiliaryRankSlice contact04) 36 4 = 15491214 :=
  contactRankWindow_of_rec contact04 36 4 15491214 (by decide +kernel)
private theorem contact04RanksSlice40 : sliceWindow (auxiliaryRankSlice contact04) 40 4 = 14189214 :=
  contactRankWindow_of_rec contact04 40 4 14189214 (by decide +kernel)
private theorem contact04RanksSlice44 : sliceWindow (auxiliaryRankSlice contact04) 44 4 = 12954414 :=
  contactRankWindow_of_rec contact04 44 4 12954414 (by decide +kernel)
private theorem contact04RanksSlice48 : sliceWindow (auxiliaryRankSlice contact04) 48 4 = 11786814 :=
  contactRankWindow_of_rec contact04 48 4 11786814 (by decide +kernel)
private theorem contact04RanksSlice52 : sliceWindow (auxiliaryRankSlice contact04) 52 4 = 10686203 :=
  contactRankWindow_of_rec contact04 52 4 10686203 (by decide +kernel)
private theorem contact04RanksSlice56 : sliceWindow (auxiliaryRankSlice contact04) 56 4 = 9651487 :=
  contactRankWindow_of_rec contact04 56 4 9651487 (by decide +kernel)
private theorem contact04RanksSlice60 : sliceWindow (auxiliaryRankSlice contact04) 60 4 = 8681362 :=
  contactRankWindow_of_rec contact04 60 4 8681362 (by decide +kernel)
private theorem contact04RanksSlice64 : sliceWindow (auxiliaryRankSlice contact04) 64 4 = 7774192 :=
  contactRankWindow_of_rec contact04 64 4 7774192 (by decide +kernel)
private theorem contact04RanksSlice68 : sliceWindow (auxiliaryRankSlice contact04) 68 4 = 6928199 :=
  contactRankWindow_of_rec contact04 68 4 6928199 (by decide +kernel)
private theorem contact04RanksSlice72 : sliceWindow (auxiliaryRankSlice contact04) 72 4 = 6141486 :=
  contactRankWindow_of_rec contact04 72 4 6141486 (by decide +kernel)
private theorem contact04RanksSlice76 : sliceWindow (auxiliaryRankSlice contact04) 76 4 = 5412136 :=
  contactRankWindow_of_rec contact04 76 4 5412136 (by decide +kernel)
private theorem contact04RanksSlice80 : sliceWindow (auxiliaryRankSlice contact04) 80 4 = 4738511 :=
  contactRankWindow_of_rec contact04 80 4 4738511 (by decide +kernel)
private theorem contact04RanksSlice84 : sliceWindow (auxiliaryRankSlice contact04) 84 4 = 4118570 :=
  contactRankWindow_of_rec contact04 84 4 4118570 (by decide +kernel)
private theorem contact04RanksSlice88 : sliceWindow (auxiliaryRankSlice contact04) 88 4 = 3550400 :=
  contactRankWindow_of_rec contact04 88 4 3550400 (by decide +kernel)
private theorem contact04RanksSlice92 : sliceWindow (auxiliaryRankSlice contact04) 92 4 = 3032503 :=
  contactRankWindow_of_rec contact04 92 4 3032503 (by decide +kernel)
private theorem contact04RanksSlice96 : sliceWindow (auxiliaryRankSlice contact04) 96 4 = 2562694 :=
  contactRankWindow_of_rec contact04 96 4 2562694 (by decide +kernel)
private theorem contact04RanksSlice100 : sliceWindow (auxiliaryRankSlice contact04) 100 4 = 2139064 :=
  contactRankWindow_of_rec contact04 100 4 2139064 (by decide +kernel)
private theorem contact04RanksSlice104 : sliceWindow (auxiliaryRankSlice contact04) 104 4 = 1760255 :=
  contactRankWindow_of_rec contact04 104 4 1760255 (by decide +kernel)
private theorem contact04RanksSlice108 : sliceWindow (auxiliaryRankSlice contact04) 108 4 = 1423938 :=
  contactRankWindow_of_rec contact04 108 4 1423938 (by decide +kernel)
private theorem contact04RanksSlice112 : sliceWindow (auxiliaryRankSlice contact04) 112 4 = 1128208 :=
  contactRankWindow_of_rec contact04 112 4 1128208 (by decide +kernel)
private theorem contact04RanksSlice116 : sliceWindow (auxiliaryRankSlice contact04) 116 4 = 871847 :=
  contactRankWindow_of_rec contact04 116 4 871847 (by decide +kernel)
private theorem contact04RanksSlice120 : sliceWindow (auxiliaryRankSlice contact04) 120 4 = 652382 :=
  contactRankWindow_of_rec contact04 120 4 652382 (by decide +kernel)
private theorem contact04RanksSlice124 : sliceWindow (auxiliaryRankSlice contact04) 124 4 = 467912 :=
  contactRankWindow_of_rec contact04 124 4 467912 (by decide +kernel)
private theorem contact04RanksSlice128 : sliceWindow (auxiliaryRankSlice contact04) 128 4 = 317359 :=
  contactRankWindow_of_rec contact04 128 4 317359 (by decide +kernel)
private theorem contact04RanksSlice132 : sliceWindow (auxiliaryRankSlice contact04) 132 4 = 198106 :=
  contactRankWindow_of_rec contact04 132 4 198106 (by decide +kernel)
private theorem contact04RanksSlice136 : sliceWindow (auxiliaryRankSlice contact04) 136 4 = 108256 :=
  contactRankWindow_of_rec contact04 136 4 108256 (by decide +kernel)
private theorem contact04RanksSlice140 : sliceWindow (auxiliaryRankSlice contact04) 140 4 = 46910 :=
  contactRankWindow_of_rec contact04 140 4 46910 (by decide +kernel)
private theorem contact04RanksSlice144 : sliceWindow (auxiliaryRankSlice contact04) 144 4 = 11531 :=
  contactRankWindow_of_rec contact04 144 4 11531 (by decide +kernel)
private theorem contact04RanksSlice148 : sliceWindow (auxiliaryRankSlice contact04) 148 12 = 0 :=
  contactRankWindow_of_rec contact04 148 12 0 (by decide +kernel)
private theorem contact04RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact04) 0 8 = 58559628 :=
  combineSlices (auxiliaryRankSlice contact04) 0 4 4 30233214 28326414 contact04RanksSlice0 contact04RanksSlice4
private theorem contact04RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact04) 8 8 = 51201228 :=
  combineSlices (auxiliaryRankSlice contact04) 8 4 4 26486814 24714414 contact04RanksSlice8 contact04RanksSlice12
private theorem contact04RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact04) 16 8 = 44380428 :=
  combineSlices (auxiliaryRankSlice contact04) 16 4 4 23009214 21371214 contact04RanksSlice16 contact04RanksSlice20
private theorem contact04RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact04) 24 8 = 38097228 :=
  combineSlices (auxiliaryRankSlice contact04) 24 4 4 19800414 18296814 contact04RanksSlice24 contact04RanksSlice28
private theorem contact04RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact04) 32 8 = 32351628 :=
  combineSlices (auxiliaryRankSlice contact04) 32 4 4 16860414 15491214 contact04RanksSlice32 contact04RanksSlice36
private theorem contact04RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact04) 40 8 = 27143628 :=
  combineSlices (auxiliaryRankSlice contact04) 40 4 4 14189214 12954414 contact04RanksSlice40 contact04RanksSlice44
private theorem contact04RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact04) 48 8 = 22473017 :=
  combineSlices (auxiliaryRankSlice contact04) 48 4 4 11786814 10686203 contact04RanksSlice48 contact04RanksSlice52
private theorem contact04RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact04) 56 8 = 18332849 :=
  combineSlices (auxiliaryRankSlice contact04) 56 4 4 9651487 8681362 contact04RanksSlice56 contact04RanksSlice60
private theorem contact04RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact04) 64 8 = 14702391 :=
  combineSlices (auxiliaryRankSlice contact04) 64 4 4 7774192 6928199 contact04RanksSlice64 contact04RanksSlice68
private theorem contact04RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact04) 72 8 = 11553622 :=
  combineSlices (auxiliaryRankSlice contact04) 72 4 4 6141486 5412136 contact04RanksSlice72 contact04RanksSlice76
private theorem contact04RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact04) 80 8 = 8857081 :=
  combineSlices (auxiliaryRankSlice contact04) 80 4 4 4738511 4118570 contact04RanksSlice80 contact04RanksSlice84
private theorem contact04RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact04) 88 8 = 6582903 :=
  combineSlices (auxiliaryRankSlice contact04) 88 4 4 3550400 3032503 contact04RanksSlice88 contact04RanksSlice92
private theorem contact04RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact04) 96 8 = 4701758 :=
  combineSlices (auxiliaryRankSlice contact04) 96 4 4 2562694 2139064 contact04RanksSlice96 contact04RanksSlice100
private theorem contact04RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact04) 104 8 = 3184193 :=
  combineSlices (auxiliaryRankSlice contact04) 104 4 4 1760255 1423938 contact04RanksSlice104 contact04RanksSlice108
private theorem contact04RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact04) 112 8 = 2000055 :=
  combineSlices (auxiliaryRankSlice contact04) 112 4 4 1128208 871847 contact04RanksSlice112 contact04RanksSlice116
private theorem contact04RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact04) 120 8 = 1120294 :=
  combineSlices (auxiliaryRankSlice contact04) 120 4 4 652382 467912 contact04RanksSlice120 contact04RanksSlice124
private theorem contact04RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact04) 128 8 = 515465 :=
  combineSlices (auxiliaryRankSlice contact04) 128 4 4 317359 198106 contact04RanksSlice128 contact04RanksSlice132
private theorem contact04RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact04) 136 8 = 155166 :=
  combineSlices (auxiliaryRankSlice contact04) 136 4 4 108256 46910 contact04RanksSlice136 contact04RanksSlice140
private theorem contact04RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact04) 144 16 = 11531 :=
  combineSlices (auxiliaryRankSlice contact04) 144 4 12 11531 0 contact04RanksSlice144 contact04RanksSlice148
private theorem contact04RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact04) 0 16 = 109760856 :=
  combineSlices (auxiliaryRankSlice contact04) 0 8 8 58559628 51201228 contact04RanksJoin0_8 contact04RanksJoin8_8
private theorem contact04RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact04) 16 16 = 82477656 :=
  combineSlices (auxiliaryRankSlice contact04) 16 8 8 44380428 38097228 contact04RanksJoin16_8 contact04RanksJoin24_8
private theorem contact04RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact04) 32 16 = 59495256 :=
  combineSlices (auxiliaryRankSlice contact04) 32 8 8 32351628 27143628 contact04RanksJoin32_8 contact04RanksJoin40_8
private theorem contact04RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact04) 48 16 = 40805866 :=
  combineSlices (auxiliaryRankSlice contact04) 48 8 8 22473017 18332849 contact04RanksJoin48_8 contact04RanksJoin56_8
private theorem contact04RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact04) 64 16 = 26256013 :=
  combineSlices (auxiliaryRankSlice contact04) 64 8 8 14702391 11553622 contact04RanksJoin64_8 contact04RanksJoin72_8
private theorem contact04RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact04) 80 16 = 15439984 :=
  combineSlices (auxiliaryRankSlice contact04) 80 8 8 8857081 6582903 contact04RanksJoin80_8 contact04RanksJoin88_8
private theorem contact04RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact04) 96 16 = 7885951 :=
  combineSlices (auxiliaryRankSlice contact04) 96 8 8 4701758 3184193 contact04RanksJoin96_8 contact04RanksJoin104_8
private theorem contact04RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact04) 112 16 = 3120349 :=
  combineSlices (auxiliaryRankSlice contact04) 112 8 8 2000055 1120294 contact04RanksJoin112_8 contact04RanksJoin120_8
private theorem contact04RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact04) 128 16 = 670631 :=
  combineSlices (auxiliaryRankSlice contact04) 128 8 8 515465 155166 contact04RanksJoin128_8 contact04RanksJoin136_8
private theorem contact04RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact04) 0 32 = 192238512 :=
  combineSlices (auxiliaryRankSlice contact04) 0 16 16 109760856 82477656 contact04RanksJoin0_16 contact04RanksJoin16_16
private theorem contact04RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact04) 32 32 = 100301122 :=
  combineSlices (auxiliaryRankSlice contact04) 32 16 16 59495256 40805866 contact04RanksJoin32_16 contact04RanksJoin48_16
private theorem contact04RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact04) 64 32 = 41695997 :=
  combineSlices (auxiliaryRankSlice contact04) 64 16 16 26256013 15439984 contact04RanksJoin64_16 contact04RanksJoin80_16
private theorem contact04RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact04) 96 32 = 11006300 :=
  combineSlices (auxiliaryRankSlice contact04) 96 16 16 7885951 3120349 contact04RanksJoin96_16 contact04RanksJoin112_16
private theorem contact04RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact04) 128 32 = 682162 :=
  combineSlices (auxiliaryRankSlice contact04) 128 16 16 670631 11531 contact04RanksJoin128_16 contact04RanksJoin144_16
private theorem contact04RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact04) 0 64 = 292539634 :=
  combineSlices (auxiliaryRankSlice contact04) 0 32 32 192238512 100301122 contact04RanksJoin0_32 contact04RanksJoin32_32
private theorem contact04RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact04) 64 64 = 52702297 :=
  combineSlices (auxiliaryRankSlice contact04) 64 32 32 41695997 11006300 contact04RanksJoin64_32 contact04RanksJoin96_32
private theorem contact04RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact04) 0 128 = 345241931 :=
  combineSlices (auxiliaryRankSlice contact04) 0 64 64 292539634 52702297 contact04RanksJoin0_64 contact04RanksJoin64_64
private theorem contact04RanksJoin0_160 : sliceWindow (auxiliaryRankSlice contact04) 0 160 = 345924093 :=
  combineSlices (auxiliaryRankSlice contact04) 0 128 32 345241931 682162 contact04RanksJoin0_128 contact04RanksJoin128_32
theorem contact04_margin : sourceMargin contact04 :=
  margin_of_checked_counts contact04 160 1826030831205307 113664282556316 7053419077 345924093 rfl contact04OrdinaryColumns contact04ColumnsJoin0_160 contact04OrdinaryRanks contact04RanksJoin0_160 (by decide +kernel)

private theorem contact06OrdinaryColumns : ordinaryColumnCount contact06 = 2069854592899692 := by decide +kernel
private theorem contact06ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact06) 0 4 = 7926559413890 :=
  contactColumnsWindow_fast contact06 0 4 7926559413890 (by decide +kernel)
private theorem contact06ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact06) 4 4 = 7546331947554 :=
  contactColumnsWindow_fast contact06 4 4 7546331947554 (by decide +kernel)
private theorem contact06ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact06) 8 4 = 7175489060380 :=
  contactColumnsWindow_fast contact06 8 4 7175489060380 (by decide +kernel)
private theorem contact06ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact06) 12 4 = 6814030958741 :=
  contactColumnsWindow_fast contact06 12 4 6814030958741 (by decide +kernel)
private theorem contact06ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact06) 16 4 = 6461993698630 :=
  contactColumnsWindow_fast contact06 16 4 6461993698630 (by decide +kernel)
private theorem contact06ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact06) 20 4 = 6119362508604 :=
  contactColumnsWindow_fast contact06 20 4 6119362508604 (by decide +kernel)
private theorem contact06ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact06) 24 4 = 5786119761086 :=
  contactColumnsWindow_fast contact06 24 4 5786119761086 (by decide +kernel)
private theorem contact06ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact06) 28 4 = 5462264010171 :=
  contactColumnsWindow_fast contact06 28 4 5462264010171 (by decide +kernel)
private theorem contact06ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact06) 32 4 = 5147798377486 :=
  contactColumnsWindow_fast contact06 32 4 5147798377486 (by decide +kernel)
private theorem contact06ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact06) 36 4 = 4842758294883 :=
  contactColumnsWindow_fast contact06 36 4 4842758294883 (by decide +kernel)
private theorem contact06ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact06) 40 4 = 4547125219729 :=
  contactColumnsWindow_fast contact06 40 4 4547125219729 (by decide +kernel)
private theorem contact06ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact06) 44 4 = 4260882542562 :=
  contactColumnsWindow_fast contact06 44 4 4260882542562 (by decide +kernel)
private theorem contact06ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact06) 48 4 = 3984031563567 :=
  contactColumnsWindow_fast contact06 48 4 3984031563567 (by decide +kernel)
private theorem contact06ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact06) 52 4 = 3716574185624 :=
  contactColumnsWindow_fast contact06 52 4 3716574185624 (by decide +kernel)
private theorem contact06ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact06) 56 4 = 3458549537940 :=
  contactColumnsWindow_fast contact06 56 4 3458549537940 (by decide +kernel)
private theorem contact06ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact06) 60 4 = 3209931337669 :=
  contactColumnsWindow_fast contact06 60 4 3209931337669 (by decide +kernel)
private theorem contact06ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact06) 64 4 = 2970707154690 :=
  contactColumnsWindow_fast contact06 64 4 2970707154690 (by decide +kernel)
private theorem contact06ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact06) 68 4 = 2740874630379 :=
  contactColumnsWindow_fast contact06 68 4 2740874630379 (by decide +kernel)
private theorem contact06ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact06) 72 4 = 2520437962253 :=
  contactColumnsWindow_fast contact06 72 4 2520437962253 (by decide +kernel)
private theorem contact06ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact06) 76 4 = 2309435005176 :=
  contactColumnsWindow_fast contact06 76 4 2309435005176 (by decide +kernel)
private theorem contact06ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact06) 80 4 = 2107835852149 :=
  contactColumnsWindow_fast contact06 80 4 2107835852149 (by decide +kernel)
private theorem contact06ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact06) 84 4 = 1915630184967 :=
  contactColumnsWindow_fast contact06 84 4 1915630184967 (by decide +kernel)
private theorem contact06ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact06) 88 4 = 1732816196911 :=
  contactColumnsWindow_fast contact06 88 4 1732816196911 (by decide +kernel)
private theorem contact06ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact06) 92 4 = 1559400793709 :=
  contactColumnsWindow_fast contact06 92 4 1559400793709 (by decide +kernel)
private theorem contact06ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact06) 96 4 = 1395418879095 :=
  contactColumnsWindow_fast contact06 96 4 1395418879095 (by decide +kernel)
private theorem contact06ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact06) 100 4 = 1240838806523 :=
  contactColumnsWindow_fast contact06 100 4 1240838806523 (by decide +kernel)
private theorem contact06ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact06) 104 4 = 1095651844083 :=
  contactColumnsWindow_fast contact06 104 4 1095651844083 (by decide +kernel)
private theorem contact06ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact06) 108 4 = 959856192598 :=
  contactColumnsWindow_fast contact06 108 4 959856192598 (by decide +kernel)
private theorem contact06ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact06) 112 4 = 833462021705 :=
  contactColumnsWindow_fast contact06 112 4 833462021705 (by decide +kernel)
private theorem contact06ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact06) 116 4 = 716501450117 :=
  contactColumnsWindow_fast contact06 116 4 716501450117 (by decide +kernel)
private theorem contact06ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact06) 120 4 = 608940244940 :=
  contactColumnsWindow_fast contact06 120 4 608940244940 (by decide +kernel)
private theorem contact06ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact06) 124 4 = 510771912483 :=
  contactColumnsWindow_fast contact06 124 4 510771912483 (by decide +kernel)
private theorem contact06ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact06) 128 4 = 421994688252 :=
  contactColumnsWindow_fast contact06 128 4 421994688252 (by decide +kernel)
private theorem contact06ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact06) 132 4 = 342622913830 :=
  contactColumnsWindow_fast contact06 132 4 342622913830 (by decide +kernel)
private theorem contact06ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact06) 136 4 = 272682318062 :=
  contactColumnsWindow_fast contact06 136 4 272682318062 (by decide +kernel)
private theorem contact06ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact06) 140 4 = 212112243424 :=
  contactColumnsWindow_fast contact06 140 4 212112243424 (by decide +kernel)
private theorem contact06ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact06) 144 4 = 160725794034 :=
  contactColumnsWindow_fast contact06 144 4 160725794034 (by decide +kernel)
private theorem contact06ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact06) 148 4 = 118146825325 :=
  contactColumnsWindow_fast contact06 148 4 118146825325 (by decide +kernel)
private theorem contact06ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact06) 152 4 = 83857715818 :=
  contactColumnsWindow_fast contact06 152 4 83857715818 (by decide +kernel)
private theorem contact06ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact06) 156 4 = 57174649147 :=
  contactColumnsWindow_fast contact06 156 4 57174649147 (by decide +kernel)
private theorem contact06ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact06) 160 3 = 29445231542 :=
  contactColumnsWindow_fast contact06 160 3 29445231542 (by decide +kernel)
private theorem contact06ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact06) 0 8 = 15472891361444 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 4 4 7926559413890 7546331947554 contact06ColumnsSlice0 contact06ColumnsSlice4
private theorem contact06ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact06) 8 8 = 13989520019121 :=
  combineSlices (auxiliaryColumnSlice contact06) 8 4 4 7175489060380 6814030958741 contact06ColumnsSlice8 contact06ColumnsSlice12
private theorem contact06ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact06) 16 8 = 12581356207234 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 4 4 6461993698630 6119362508604 contact06ColumnsSlice16 contact06ColumnsSlice20
private theorem contact06ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact06) 24 8 = 11248383771257 :=
  combineSlices (auxiliaryColumnSlice contact06) 24 4 4 5786119761086 5462264010171 contact06ColumnsSlice24 contact06ColumnsSlice28
private theorem contact06ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact06) 32 8 = 9990556672369 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 4 4 5147798377486 4842758294883 contact06ColumnsSlice32 contact06ColumnsSlice36
private theorem contact06ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact06) 40 8 = 8808007762291 :=
  combineSlices (auxiliaryColumnSlice contact06) 40 4 4 4547125219729 4260882542562 contact06ColumnsSlice40 contact06ColumnsSlice44
private theorem contact06ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact06) 48 8 = 7700605749191 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 4 4 3984031563567 3716574185624 contact06ColumnsSlice48 contact06ColumnsSlice52
private theorem contact06ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact06) 56 8 = 6668480875609 :=
  combineSlices (auxiliaryColumnSlice contact06) 56 4 4 3458549537940 3209931337669 contact06ColumnsSlice56 contact06ColumnsSlice60
private theorem contact06ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact06) 64 8 = 5711581785069 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 4 4 2970707154690 2740874630379 contact06ColumnsSlice64 contact06ColumnsSlice68
private theorem contact06ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact06) 72 8 = 4829872967429 :=
  combineSlices (auxiliaryColumnSlice contact06) 72 4 4 2520437962253 2309435005176 contact06ColumnsSlice72 contact06ColumnsSlice76
private theorem contact06ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact06) 80 8 = 4023466037116 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 4 4 2107835852149 1915630184967 contact06ColumnsSlice80 contact06ColumnsSlice84
private theorem contact06ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact06) 88 8 = 3292216990620 :=
  combineSlices (auxiliaryColumnSlice contact06) 88 4 4 1732816196911 1559400793709 contact06ColumnsSlice88 contact06ColumnsSlice92
private theorem contact06ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact06) 96 8 = 2636257685618 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 4 4 1395418879095 1240838806523 contact06ColumnsSlice96 contact06ColumnsSlice100
private theorem contact06ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact06) 104 8 = 2055508036681 :=
  combineSlices (auxiliaryColumnSlice contact06) 104 4 4 1095651844083 959856192598 contact06ColumnsSlice104 contact06ColumnsSlice108
private theorem contact06ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact06) 112 8 = 1549963471822 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 4 4 833462021705 716501450117 contact06ColumnsSlice112 contact06ColumnsSlice116
private theorem contact06ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact06) 120 8 = 1119712157423 :=
  combineSlices (auxiliaryColumnSlice contact06) 120 4 4 608940244940 510771912483 contact06ColumnsSlice120 contact06ColumnsSlice124
private theorem contact06ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact06) 128 8 = 764617602082 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 4 4 421994688252 342622913830 contact06ColumnsSlice128 contact06ColumnsSlice132
private theorem contact06ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact06) 136 8 = 484794561486 :=
  combineSlices (auxiliaryColumnSlice contact06) 136 4 4 272682318062 212112243424 contact06ColumnsSlice136 contact06ColumnsSlice140
private theorem contact06ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact06) 144 8 = 278872619359 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 4 4 160725794034 118146825325 contact06ColumnsSlice144 contact06ColumnsSlice148
private theorem contact06ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact06) 152 8 = 141032364965 :=
  combineSlices (auxiliaryColumnSlice contact06) 152 4 4 83857715818 57174649147 contact06ColumnsSlice152 contact06ColumnsSlice156
private theorem contact06ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact06) 0 16 = 29462411380565 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 8 8 15472891361444 13989520019121 contact06ColumnsJoin0_8 contact06ColumnsJoin8_8
private theorem contact06ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact06) 16 16 = 23829739978491 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 8 8 12581356207234 11248383771257 contact06ColumnsJoin16_8 contact06ColumnsJoin24_8
private theorem contact06ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact06) 32 16 = 18798564434660 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 8 8 9990556672369 8808007762291 contact06ColumnsJoin32_8 contact06ColumnsJoin40_8
private theorem contact06ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact06) 48 16 = 14369086624800 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 8 8 7700605749191 6668480875609 contact06ColumnsJoin48_8 contact06ColumnsJoin56_8
private theorem contact06ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact06) 64 16 = 10541454752498 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 8 8 5711581785069 4829872967429 contact06ColumnsJoin64_8 contact06ColumnsJoin72_8
private theorem contact06ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact06) 80 16 = 7315683027736 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 8 8 4023466037116 3292216990620 contact06ColumnsJoin80_8 contact06ColumnsJoin88_8
private theorem contact06ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact06) 96 16 = 4691765722299 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 8 8 2636257685618 2055508036681 contact06ColumnsJoin96_8 contact06ColumnsJoin104_8
private theorem contact06ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact06) 112 16 = 2669675629245 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 8 8 1549963471822 1119712157423 contact06ColumnsJoin112_8 contact06ColumnsJoin120_8
private theorem contact06ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact06) 128 16 = 1249412163568 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 8 8 764617602082 484794561486 contact06ColumnsJoin128_8 contact06ColumnsJoin136_8
private theorem contact06ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact06) 144 16 = 419904984324 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 8 8 278872619359 141032364965 contact06ColumnsJoin144_8 contact06ColumnsJoin152_8
private theorem contact06ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact06) 0 32 = 53292151359056 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 16 16 29462411380565 23829739978491 contact06ColumnsJoin0_16 contact06ColumnsJoin16_16
private theorem contact06ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact06) 32 32 = 33167651059460 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 16 16 18798564434660 14369086624800 contact06ColumnsJoin32_16 contact06ColumnsJoin48_16
private theorem contact06ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact06) 64 32 = 17857137780234 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 16 16 10541454752498 7315683027736 contact06ColumnsJoin64_16 contact06ColumnsJoin80_16
private theorem contact06ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact06) 96 32 = 7361441351544 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 16 16 4691765722299 2669675629245 contact06ColumnsJoin96_16 contact06ColumnsJoin112_16
private theorem contact06ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact06) 128 32 = 1669317147892 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 16 16 1249412163568 419904984324 contact06ColumnsJoin128_16 contact06ColumnsJoin144_16
private theorem contact06ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact06) 0 64 = 86459802418516 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 32 32 53292151359056 33167651059460 contact06ColumnsJoin0_32 contact06ColumnsJoin32_32
private theorem contact06ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact06) 64 64 = 25218579131778 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 32 32 17857137780234 7361441351544 contact06ColumnsJoin64_32 contact06ColumnsJoin96_32
private theorem contact06ColumnsJoin128_35 : sliceWindow (auxiliaryColumnSlice contact06) 128 35 = 1698762379434 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 32 3 1669317147892 29445231542 contact06ColumnsJoin128_32 contact06ColumnsSlice160
private theorem contact06ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact06) 0 128 = 111678381550294 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 64 64 86459802418516 25218579131778 contact06ColumnsJoin0_64 contact06ColumnsJoin64_64
private theorem contact06ColumnsJoin0_163 : sliceWindow (auxiliaryColumnSlice contact06) 0 163 = 113377143929728 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 128 35 111678381550294 1698762379434 contact06ColumnsJoin0_128 contact06ColumnsJoin128_35
private theorem contact06OrdinaryRanks : ordinaryRankBound contact06 = 7984328451 := by decide +kernel
private theorem contact06RanksSlice0 : sliceWindow (auxiliaryRankSlice contact06) 0 4 = 29869000 :=
  contactRankWindow_of_rec contact06 0 4 29869000 (by decide +kernel)
private theorem contact06RanksSlice4 : sliceWindow (auxiliaryRankSlice contact06) 4 4 = 28001400 :=
  contactRankWindow_of_rec contact06 4 4 28001400 (by decide +kernel)
private theorem contact06RanksSlice8 : sliceWindow (auxiliaryRankSlice contact06) 8 4 = 26198760 :=
  contactRankWindow_of_rec contact06 8 4 26198760 (by decide +kernel)
private theorem contact06RanksSlice12 : sliceWindow (auxiliaryRankSlice contact06) 12 4 = 24461080 :=
  contactRankWindow_of_rec contact06 12 4 24461080 (by decide +kernel)
private theorem contact06RanksSlice16 : sliceWindow (auxiliaryRankSlice contact06) 16 4 = 22788360 :=
  contactRankWindow_of_rec contact06 16 4 22788360 (by decide +kernel)
private theorem contact06RanksSlice20 : sliceWindow (auxiliaryRankSlice contact06) 20 4 = 21180600 :=
  contactRankWindow_of_rec contact06 20 4 21180600 (by decide +kernel)
private theorem contact06RanksSlice24 : sliceWindow (auxiliaryRankSlice contact06) 24 4 = 19637800 :=
  contactRankWindow_of_rec contact06 24 4 19637800 (by decide +kernel)
private theorem contact06RanksSlice28 : sliceWindow (auxiliaryRankSlice contact06) 28 4 = 18159960 :=
  contactRankWindow_of_rec contact06 28 4 18159960 (by decide +kernel)
private theorem contact06RanksSlice32 : sliceWindow (auxiliaryRankSlice contact06) 32 4 = 16747080 :=
  contactRankWindow_of_rec contact06 32 4 16747080 (by decide +kernel)
private theorem contact06RanksSlice36 : sliceWindow (auxiliaryRankSlice contact06) 36 4 = 15399160 :=
  contactRankWindow_of_rec contact06 36 4 15399160 (by decide +kernel)
private theorem contact06RanksSlice40 : sliceWindow (auxiliaryRankSlice contact06) 40 4 = 14116200 :=
  contactRankWindow_of_rec contact06 40 4 14116200 (by decide +kernel)
private theorem contact06RanksSlice44 : sliceWindow (auxiliaryRankSlice contact06) 44 4 = 12898200 :=
  contactRankWindow_of_rec contact06 44 4 12898200 (by decide +kernel)
private theorem contact06RanksSlice48 : sliceWindow (auxiliaryRankSlice contact06) 48 4 = 11745160 :=
  contactRankWindow_of_rec contact06 48 4 11745160 (by decide +kernel)
private theorem contact06RanksSlice52 : sliceWindow (auxiliaryRankSlice contact06) 52 4 = 10657051 :=
  contactRankWindow_of_rec contact06 52 4 10657051 (by decide +kernel)
private theorem contact06RanksSlice56 : sliceWindow (auxiliaryRankSlice contact06) 56 4 = 9633259 :=
  contactRankWindow_of_rec contact06 56 4 9633259 (by decide +kernel)
private theorem contact06RanksSlice60 : sliceWindow (auxiliaryRankSlice contact06) 60 4 = 8672537 :=
  contactRankWindow_of_rec contact06 60 4 8672537 (by decide +kernel)
private theorem contact06RanksSlice64 : sliceWindow (auxiliaryRankSlice contact06) 64 4 = 7773583 :=
  contactRankWindow_of_rec contact06 64 4 7773583 (by decide +kernel)
private theorem contact06RanksSlice68 : sliceWindow (auxiliaryRankSlice contact06) 68 4 = 6934816 :=
  contactRankWindow_of_rec contact06 68 4 6934816 (by decide +kernel)
private theorem contact06RanksSlice72 : sliceWindow (auxiliaryRankSlice contact06) 72 4 = 6154485 :=
  contactRankWindow_of_rec contact06 72 4 6154485 (by decide +kernel)
private theorem contact06RanksSlice76 : sliceWindow (auxiliaryRankSlice contact06) 76 4 = 5430699 :=
  contactRankWindow_of_rec contact06 76 4 5430699 (by decide +kernel)
private theorem contact06RanksSlice80 : sliceWindow (auxiliaryRankSlice contact06) 80 4 = 4761592 :=
  contactRankWindow_of_rec contact06 80 4 4761592 (by decide +kernel)
private theorem contact06RanksSlice84 : sliceWindow (auxiliaryRankSlice contact06) 84 4 = 4145553 :=
  contactRankWindow_of_rec contact06 84 4 4145553 (by decide +kernel)
private theorem contact06RanksSlice88 : sliceWindow (auxiliaryRankSlice contact06) 88 4 = 3580551 :=
  contactRankWindow_of_rec contact06 88 4 3580551 (by decide +kernel)
private theorem contact06RanksSlice92 : sliceWindow (auxiliaryRankSlice contact06) 92 4 = 3064720 :=
  contactRankWindow_of_rec contact06 92 4 3064720 (by decide +kernel)
private theorem contact06RanksSlice96 : sliceWindow (auxiliaryRankSlice contact06) 96 4 = 2596589 :=
  contactRankWindow_of_rec contact06 96 4 2596589 (by decide +kernel)
private theorem contact06RanksSlice100 : sliceWindow (auxiliaryRankSlice contact06) 100 4 = 2173987 :=
  contactRankWindow_of_rec contact06 100 4 2173987 (by decide +kernel)
private theorem contact06RanksSlice104 : sliceWindow (auxiliaryRankSlice contact06) 104 4 = 1795048 :=
  contactRankWindow_of_rec contact06 104 4 1795048 (by decide +kernel)
private theorem contact06RanksSlice108 : sliceWindow (auxiliaryRankSlice contact06) 108 4 = 1458441 :=
  contactRankWindow_of_rec contact06 108 4 1458441 (by decide +kernel)
private theorem contact06RanksSlice112 : sliceWindow (auxiliaryRankSlice contact06) 112 4 = 1161855 :=
  contactRankWindow_of_rec contact06 112 4 1161855 (by decide +kernel)
private theorem contact06RanksSlice116 : sliceWindow (auxiliaryRankSlice contact06) 116 4 = 903424 :=
  contactRankWindow_of_rec contact06 116 4 903424 (by decide +kernel)
private theorem contact06RanksSlice120 : sliceWindow (auxiliaryRankSlice contact06) 120 4 = 681957 :=
  contactRankWindow_of_rec contact06 120 4 681957 (by decide +kernel)
private theorem contact06RanksSlice124 : sliceWindow (auxiliaryRankSlice contact06) 124 4 = 495003 :=
  contactRankWindow_of_rec contact06 124 4 495003 (by decide +kernel)
private theorem contact06RanksSlice128 : sliceWindow (auxiliaryRankSlice contact06) 128 4 = 340696 :=
  contactRankWindow_of_rec contact06 128 4 340696 (by decide +kernel)
private theorem contact06RanksSlice132 : sliceWindow (auxiliaryRankSlice contact06) 132 4 = 217985 :=
  contactRankWindow_of_rec contact06 132 4 217985 (by decide +kernel)
private theorem contact06RanksSlice136 : sliceWindow (auxiliaryRankSlice contact06) 136 4 = 124279 :=
  contactRankWindow_of_rec contact06 136 4 124279 (by decide +kernel)
private theorem contact06RanksSlice140 : sliceWindow (auxiliaryRankSlice contact06) 140 4 = 57715 :=
  contactRankWindow_of_rec contact06 140 4 57715 (by decide +kernel)
private theorem contact06RanksSlice144 : sliceWindow (auxiliaryRankSlice contact06) 144 4 = 17510 :=
  contactRankWindow_of_rec contact06 144 4 17510 (by decide +kernel)
private theorem contact06RanksSlice148 : sliceWindow (auxiliaryRankSlice contact06) 148 4 = 987 :=
  contactRankWindow_of_rec contact06 148 4 987 (by decide +kernel)
private theorem contact06RanksSlice152 : sliceWindow (auxiliaryRankSlice contact06) 152 11 = 0 :=
  contactRankWindow_of_rec contact06 152 11 0 (by decide +kernel)
private theorem contact06RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact06) 0 8 = 57870400 :=
  combineSlices (auxiliaryRankSlice contact06) 0 4 4 29869000 28001400 contact06RanksSlice0 contact06RanksSlice4
private theorem contact06RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact06) 8 8 = 50659840 :=
  combineSlices (auxiliaryRankSlice contact06) 8 4 4 26198760 24461080 contact06RanksSlice8 contact06RanksSlice12
private theorem contact06RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact06) 16 8 = 43968960 :=
  combineSlices (auxiliaryRankSlice contact06) 16 4 4 22788360 21180600 contact06RanksSlice16 contact06RanksSlice20
private theorem contact06RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact06) 24 8 = 37797760 :=
  combineSlices (auxiliaryRankSlice contact06) 24 4 4 19637800 18159960 contact06RanksSlice24 contact06RanksSlice28
private theorem contact06RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact06) 32 8 = 32146240 :=
  combineSlices (auxiliaryRankSlice contact06) 32 4 4 16747080 15399160 contact06RanksSlice32 contact06RanksSlice36
private theorem contact06RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact06) 40 8 = 27014400 :=
  combineSlices (auxiliaryRankSlice contact06) 40 4 4 14116200 12898200 contact06RanksSlice40 contact06RanksSlice44
private theorem contact06RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact06) 48 8 = 22402211 :=
  combineSlices (auxiliaryRankSlice contact06) 48 4 4 11745160 10657051 contact06RanksSlice48 contact06RanksSlice52
private theorem contact06RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact06) 56 8 = 18305796 :=
  combineSlices (auxiliaryRankSlice contact06) 56 4 4 9633259 8672537 contact06RanksSlice56 contact06RanksSlice60
private theorem contact06RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact06) 64 8 = 14708399 :=
  combineSlices (auxiliaryRankSlice contact06) 64 4 4 7773583 6934816 contact06RanksSlice64 contact06RanksSlice68
private theorem contact06RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact06) 72 8 = 11585184 :=
  combineSlices (auxiliaryRankSlice contact06) 72 4 4 6154485 5430699 contact06RanksSlice72 contact06RanksSlice76
private theorem contact06RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact06) 80 8 = 8907145 :=
  combineSlices (auxiliaryRankSlice contact06) 80 4 4 4761592 4145553 contact06RanksSlice80 contact06RanksSlice84
private theorem contact06RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact06) 88 8 = 6645271 :=
  combineSlices (auxiliaryRankSlice contact06) 88 4 4 3580551 3064720 contact06RanksSlice88 contact06RanksSlice92
private theorem contact06RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact06) 96 8 = 4770576 :=
  combineSlices (auxiliaryRankSlice contact06) 96 4 4 2596589 2173987 contact06RanksSlice96 contact06RanksSlice100
private theorem contact06RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact06) 104 8 = 3253489 :=
  combineSlices (auxiliaryRankSlice contact06) 104 4 4 1795048 1458441 contact06RanksSlice104 contact06RanksSlice108
private theorem contact06RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact06) 112 8 = 2065279 :=
  combineSlices (auxiliaryRankSlice contact06) 112 4 4 1161855 903424 contact06RanksSlice112 contact06RanksSlice116
private theorem contact06RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact06) 120 8 = 1176960 :=
  combineSlices (auxiliaryRankSlice contact06) 120 4 4 681957 495003 contact06RanksSlice120 contact06RanksSlice124
private theorem contact06RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact06) 128 8 = 558681 :=
  combineSlices (auxiliaryRankSlice contact06) 128 4 4 340696 217985 contact06RanksSlice128 contact06RanksSlice132
private theorem contact06RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact06) 136 8 = 181994 :=
  combineSlices (auxiliaryRankSlice contact06) 136 4 4 124279 57715 contact06RanksSlice136 contact06RanksSlice140
private theorem contact06RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact06) 144 8 = 18497 :=
  combineSlices (auxiliaryRankSlice contact06) 144 4 4 17510 987 contact06RanksSlice144 contact06RanksSlice148
private theorem contact06RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact06) 0 16 = 108530240 :=
  combineSlices (auxiliaryRankSlice contact06) 0 8 8 57870400 50659840 contact06RanksJoin0_8 contact06RanksJoin8_8
private theorem contact06RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact06) 16 16 = 81766720 :=
  combineSlices (auxiliaryRankSlice contact06) 16 8 8 43968960 37797760 contact06RanksJoin16_8 contact06RanksJoin24_8
private theorem contact06RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact06) 32 16 = 59160640 :=
  combineSlices (auxiliaryRankSlice contact06) 32 8 8 32146240 27014400 contact06RanksJoin32_8 contact06RanksJoin40_8
private theorem contact06RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact06) 48 16 = 40708007 :=
  combineSlices (auxiliaryRankSlice contact06) 48 8 8 22402211 18305796 contact06RanksJoin48_8 contact06RanksJoin56_8
private theorem contact06RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact06) 64 16 = 26293583 :=
  combineSlices (auxiliaryRankSlice contact06) 64 8 8 14708399 11585184 contact06RanksJoin64_8 contact06RanksJoin72_8
private theorem contact06RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact06) 80 16 = 15552416 :=
  combineSlices (auxiliaryRankSlice contact06) 80 8 8 8907145 6645271 contact06RanksJoin80_8 contact06RanksJoin88_8
private theorem contact06RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact06) 96 16 = 8024065 :=
  combineSlices (auxiliaryRankSlice contact06) 96 8 8 4770576 3253489 contact06RanksJoin96_8 contact06RanksJoin104_8
private theorem contact06RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact06) 112 16 = 3242239 :=
  combineSlices (auxiliaryRankSlice contact06) 112 8 8 2065279 1176960 contact06RanksJoin112_8 contact06RanksJoin120_8
private theorem contact06RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact06) 128 16 = 740675 :=
  combineSlices (auxiliaryRankSlice contact06) 128 8 8 558681 181994 contact06RanksJoin128_8 contact06RanksJoin136_8
private theorem contact06RanksJoin144_19 : sliceWindow (auxiliaryRankSlice contact06) 144 19 = 18497 :=
  combineSlices (auxiliaryRankSlice contact06) 144 8 11 18497 0 contact06RanksJoin144_8 contact06RanksSlice152
private theorem contact06RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact06) 0 32 = 190296960 :=
  combineSlices (auxiliaryRankSlice contact06) 0 16 16 108530240 81766720 contact06RanksJoin0_16 contact06RanksJoin16_16
private theorem contact06RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact06) 32 32 = 99868647 :=
  combineSlices (auxiliaryRankSlice contact06) 32 16 16 59160640 40708007 contact06RanksJoin32_16 contact06RanksJoin48_16
private theorem contact06RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact06) 64 32 = 41845999 :=
  combineSlices (auxiliaryRankSlice contact06) 64 16 16 26293583 15552416 contact06RanksJoin64_16 contact06RanksJoin80_16
private theorem contact06RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact06) 96 32 = 11266304 :=
  combineSlices (auxiliaryRankSlice contact06) 96 16 16 8024065 3242239 contact06RanksJoin96_16 contact06RanksJoin112_16
private theorem contact06RanksJoin128_35 : sliceWindow (auxiliaryRankSlice contact06) 128 35 = 759172 :=
  combineSlices (auxiliaryRankSlice contact06) 128 16 19 740675 18497 contact06RanksJoin128_16 contact06RanksJoin144_19
private theorem contact06RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact06) 0 64 = 290165607 :=
  combineSlices (auxiliaryRankSlice contact06) 0 32 32 190296960 99868647 contact06RanksJoin0_32 contact06RanksJoin32_32
private theorem contact06RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact06) 64 64 = 53112303 :=
  combineSlices (auxiliaryRankSlice contact06) 64 32 32 41845999 11266304 contact06RanksJoin64_32 contact06RanksJoin96_32
private theorem contact06RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact06) 0 128 = 343277910 :=
  combineSlices (auxiliaryRankSlice contact06) 0 64 64 290165607 53112303 contact06RanksJoin0_64 contact06RanksJoin64_64
private theorem contact06RanksJoin0_163 : sliceWindow (auxiliaryRankSlice contact06) 0 163 = 344037082 :=
  combineSlices (auxiliaryRankSlice contact06) 0 128 35 343277910 759172 contact06RanksJoin0_128 contact06RanksJoin128_35
theorem contact06_margin : sourceMargin contact06 :=
  margin_of_checked_counts contact06 163 2069854592899692 113377143929728 7984328451 344037082 rfl contact06OrdinaryColumns contact06ColumnsJoin0_163 contact06OrdinaryRanks contact06RanksJoin0_163 (by decide +kernel)

private theorem contact08OrdinaryColumns : ordinaryColumnCount contact08 = 2034833017704222 := by decide +kernel
private theorem contact08ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact08) 0 4 = 8338882376604 :=
  contactColumnsWindow_fast contact08 0 4 8338882376604 (by decide +kernel)
private theorem contact08ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact08) 4 4 = 7936713527772 :=
  contactColumnsWindow_fast contact08 4 4 7936713527772 (by decide +kernel)
private theorem contact08ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact08) 8 4 = 7544530177374 :=
  contactColumnsWindow_fast contact08 8 4 7544530177374 (by decide +kernel)
private theorem contact08ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact08) 12 4 = 7162332559303 :=
  contactColumnsWindow_fast contact08 12 4 7162332559303 (by decide +kernel)
private theorem contact08ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact08) 16 4 = 6790159935290 :=
  contactColumnsWindow_fast contact08 16 4 6790159935290 (by decide +kernel)
private theorem contact08ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact08) 20 4 = 6427996154553 :=
  contactColumnsWindow_fast contact08 20 4 6427996154553 (by decide +kernel)
private theorem contact08ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact08) 24 4 = 6075821885786 :=
  contactColumnsWindow_fast contact08 24 4 6075821885786 (by decide +kernel)
private theorem contact08ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact08) 28 4 = 5733635624983 :=
  contactColumnsWindow_fast contact08 28 4 5733635624983 (by decide +kernel)
private theorem contact08ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact08) 32 4 = 5401440690679 :=
  contactColumnsWindow_fast contact08 32 4 5401440690679 (by decide +kernel)
private theorem contact08ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact08) 36 4 = 5079275768469 :=
  contactColumnsWindow_fast contact08 36 4 5079275768469 (by decide +kernel)
private theorem contact08ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact08) 40 4 = 4767120449015 :=
  contactColumnsWindow_fast contact08 40 4 4767120449015 (by decide +kernel)
private theorem contact08ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact08) 44 4 = 4464956661706 :=
  contactColumnsWindow_fast contact08 44 4 4464956661706 (by decide +kernel)
private theorem contact08ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact08) 48 4 = 4172785744525 :=
  contactColumnsWindow_fast contact08 48 4 4172785744525 (by decide +kernel)
private theorem contact08ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact08) 52 4 = 3890609822745 :=
  contactColumnsWindow_fast contact08 52 4 3890609822745 (by decide +kernel)
private theorem contact08ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact08) 56 4 = 3618471478438 :=
  contactColumnsWindow_fast contact08 56 4 3618471478438 (by decide +kernel)
private theorem contact08ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact08) 60 4 = 3356341935785 :=
  contactColumnsWindow_fast contact08 60 4 3356341935785 (by decide +kernel)
private theorem contact08ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact08) 64 4 = 3104207656372 :=
  contactColumnsWindow_fast contact08 64 4 3104207656372 (by decide +kernel)
private theorem contact08ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact08) 68 4 = 2862066207583 :=
  contactColumnsWindow_fast contact08 68 4 2862066207583 (by decide +kernel)
private theorem contact08ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact08) 72 4 = 2629922199162 :=
  contactColumnsWindow_fast contact08 72 4 2629922199162 (by decide +kernel)
private theorem contact08ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact08) 76 4 = 2407816843384 :=
  contactColumnsWindow_fast contact08 76 4 2407816843384 (by decide +kernel)
private theorem contact08ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact08) 80 4 = 2195717381435 :=
  contactColumnsWindow_fast contact08 80 4 2195717381435 (by decide +kernel)
private theorem contact08ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact08) 84 4 = 1993612632358 :=
  contactColumnsWindow_fast contact08 84 4 1993612632358 (by decide +kernel)
private theorem contact08ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact08) 88 4 = 1801500736396 :=
  contactColumnsWindow_fast contact08 88 4 1801500736396 (by decide +kernel)
private theorem contact08ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact08) 92 4 = 1619389244874 :=
  contactColumnsWindow_fast contact08 92 4 1619389244874 (by decide +kernel)
private theorem contact08ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact08) 96 4 = 1447316177610 :=
  contactColumnsWindow_fast contact08 96 4 1447316177610 (by decide +kernel)
private theorem contact08ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact08) 100 4 = 1285246830900 :=
  contactColumnsWindow_fast contact08 100 4 1285246830900 (by decide +kernel)
private theorem contact08ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact08) 104 4 = 1133171808075 :=
  contactColumnsWindow_fast contact08 104 4 1133171808075 (by decide +kernel)
private theorem contact08ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact08) 108 4 = 991089257947 :=
  contactColumnsWindow_fast contact08 108 4 991089257947 (by decide +kernel)
private theorem contact08ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact08) 112 4 = 859010249466 :=
  contactColumnsWindow_fast contact08 112 4 859010249466 (by decide +kernel)
private theorem contact08ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact08) 116 4 = 736969781946 :=
  contactColumnsWindow_fast contact08 116 4 736969781946 (by decide +kernel)
private theorem contact08ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact08) 120 4 = 624930330105 :=
  contactColumnsWindow_fast contact08 120 4 624930330105 (by decide +kernel)
private theorem contact08ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact08) 124 4 = 522884955909 :=
  contactColumnsWindow_fast contact08 124 4 522884955909 (by decide +kernel)
private theorem contact08ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact08) 128 4 = 430831845103 :=
  contactColumnsWindow_fast contact08 128 4 430831845103 (by decide +kernel)
private theorem contact08ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact08) 132 4 = 348786588467 :=
  contactColumnsWindow_fast contact08 132 4 348786588467 (by decide +kernel)
private theorem contact08ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact08) 136 4 = 276773439130 :=
  contactColumnsWindow_fast contact08 136 4 276773439130 (by decide +kernel)
private theorem contact08ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact08) 140 4 = 214672700697 :=
  contactColumnsWindow_fast contact08 140 4 214672700697 (by decide +kernel)
private theorem contact08ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact08) 144 4 = 162198810624 :=
  contactColumnsWindow_fast contact08 144 4 162198810624 (by decide +kernel)
private theorem contact08ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact08) 148 4 = 118899163275 :=
  contactColumnsWindow_fast contact08 148 4 118899163275 (by decide +kernel)
private theorem contact08ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact08) 152 4 = 84179884675 :=
  contactColumnsWindow_fast contact08 152 4 84179884675 (by decide +kernel)
private theorem contact08ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact08) 156 4 = 57279643575 :=
  contactColumnsWindow_fast contact08 156 4 57279643575 (by decide +kernel)
private theorem contact08ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact08) 160 4 = 37225174602 :=
  contactColumnsWindow_fast contact08 160 4 37225174602 (by decide +kernel)
private theorem contact08ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact08) 0 8 = 16275595904376 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 4 4 8338882376604 7936713527772 contact08ColumnsSlice0 contact08ColumnsSlice4
private theorem contact08ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact08) 8 8 = 14706862736677 :=
  combineSlices (auxiliaryColumnSlice contact08) 8 4 4 7544530177374 7162332559303 contact08ColumnsSlice8 contact08ColumnsSlice12
private theorem contact08ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact08) 16 8 = 13218156089843 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 4 4 6790159935290 6427996154553 contact08ColumnsSlice16 contact08ColumnsSlice20
private theorem contact08ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact08) 24 8 = 11809457510769 :=
  combineSlices (auxiliaryColumnSlice contact08) 24 4 4 6075821885786 5733635624983 contact08ColumnsSlice24 contact08ColumnsSlice28
private theorem contact08ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact08) 32 8 = 10480716459148 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 4 4 5401440690679 5079275768469 contact08ColumnsSlice32 contact08ColumnsSlice36
private theorem contact08ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact08) 40 8 = 9232077110721 :=
  combineSlices (auxiliaryColumnSlice contact08) 40 4 4 4767120449015 4464956661706 contact08ColumnsSlice40 contact08ColumnsSlice44
private theorem contact08ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact08) 48 8 = 8063395567270 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 4 4 4172785744525 3890609822745 contact08ColumnsSlice48 contact08ColumnsSlice52
private theorem contact08ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact08) 56 8 = 6974813414223 :=
  combineSlices (auxiliaryColumnSlice contact08) 56 4 4 3618471478438 3356341935785 contact08ColumnsSlice56 contact08ColumnsSlice60
private theorem contact08ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact08) 64 8 = 5966273863955 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 4 4 3104207656372 2862066207583 contact08ColumnsSlice64 contact08ColumnsSlice68
private theorem contact08ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact08) 72 8 = 5037739042546 :=
  combineSlices (auxiliaryColumnSlice contact08) 72 4 4 2629922199162 2407816843384 contact08ColumnsSlice72 contact08ColumnsSlice76
private theorem contact08ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact08) 80 8 = 4189330013793 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 4 4 2195717381435 1993612632358 contact08ColumnsSlice80 contact08ColumnsSlice84
private theorem contact08ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact08) 88 8 = 3420889981270 :=
  combineSlices (auxiliaryColumnSlice contact08) 88 4 4 1801500736396 1619389244874 contact08ColumnsSlice88 contact08ColumnsSlice92
private theorem contact08ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact08) 96 8 = 2732563008510 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 4 4 1447316177610 1285246830900 contact08ColumnsSlice96 contact08ColumnsSlice100
private theorem contact08ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact08) 104 8 = 2124261066022 :=
  combineSlices (auxiliaryColumnSlice contact08) 104 4 4 1133171808075 991089257947 contact08ColumnsSlice104 contact08ColumnsSlice108
private theorem contact08ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact08) 112 8 = 1595980031412 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 4 4 859010249466 736969781946 contact08ColumnsSlice112 contact08ColumnsSlice116
private theorem contact08ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact08) 120 8 = 1147815286014 :=
  combineSlices (auxiliaryColumnSlice contact08) 120 4 4 624930330105 522884955909 contact08ColumnsSlice120 contact08ColumnsSlice124
private theorem contact08ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact08) 128 8 = 779618433570 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 4 4 430831845103 348786588467 contact08ColumnsSlice128 contact08ColumnsSlice132
private theorem contact08ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact08) 136 8 = 491446139827 :=
  combineSlices (auxiliaryColumnSlice contact08) 136 4 4 276773439130 214672700697 contact08ColumnsSlice136 contact08ColumnsSlice140
private theorem contact08ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact08) 144 8 = 281097973899 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 4 4 162198810624 118899163275 contact08ColumnsSlice144 contact08ColumnsSlice148
private theorem contact08ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact08) 152 8 = 141459528250 :=
  combineSlices (auxiliaryColumnSlice contact08) 152 4 4 84179884675 57279643575 contact08ColumnsSlice152 contact08ColumnsSlice156
private theorem contact08ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact08) 0 16 = 30982458641053 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 8 8 16275595904376 14706862736677 contact08ColumnsJoin0_8 contact08ColumnsJoin8_8
private theorem contact08ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact08) 16 16 = 25027613600612 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 8 8 13218156089843 11809457510769 contact08ColumnsJoin16_8 contact08ColumnsJoin24_8
private theorem contact08ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact08) 32 16 = 19712793569869 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 8 8 10480716459148 9232077110721 contact08ColumnsJoin32_8 contact08ColumnsJoin40_8
private theorem contact08ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact08) 48 16 = 15038208981493 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 8 8 8063395567270 6974813414223 contact08ColumnsJoin48_8 contact08ColumnsJoin56_8
private theorem contact08ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact08) 64 16 = 11004012906501 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 8 8 5966273863955 5037739042546 contact08ColumnsJoin64_8 contact08ColumnsJoin72_8
private theorem contact08ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact08) 80 16 = 7610219995063 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 8 8 4189330013793 3420889981270 contact08ColumnsJoin80_8 contact08ColumnsJoin88_8
private theorem contact08ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact08) 96 16 = 4856824074532 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 8 8 2732563008510 2124261066022 contact08ColumnsJoin96_8 contact08ColumnsJoin104_8
private theorem contact08ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact08) 112 16 = 2743795317426 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 8 8 1595980031412 1147815286014 contact08ColumnsJoin112_8 contact08ColumnsJoin120_8
private theorem contact08ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact08) 128 16 = 1271064573397 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 8 8 779618433570 491446139827 contact08ColumnsJoin128_8 contact08ColumnsJoin136_8
private theorem contact08ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact08) 144 16 = 422557502149 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 8 8 281097973899 141459528250 contact08ColumnsJoin144_8 contact08ColumnsJoin152_8
private theorem contact08ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact08) 0 32 = 56010072241665 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 16 16 30982458641053 25027613600612 contact08ColumnsJoin0_16 contact08ColumnsJoin16_16
private theorem contact08ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact08) 32 32 = 34751002551362 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 16 16 19712793569869 15038208981493 contact08ColumnsJoin32_16 contact08ColumnsJoin48_16
private theorem contact08ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact08) 64 32 = 18614232901564 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 16 16 11004012906501 7610219995063 contact08ColumnsJoin64_16 contact08ColumnsJoin80_16
private theorem contact08ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact08) 96 32 = 7600619391958 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 16 16 4856824074532 2743795317426 contact08ColumnsJoin96_16 contact08ColumnsJoin112_16
private theorem contact08ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact08) 128 32 = 1693622075546 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 16 16 1271064573397 422557502149 contact08ColumnsJoin128_16 contact08ColumnsJoin144_16
private theorem contact08ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact08) 0 64 = 90761074793027 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 32 32 56010072241665 34751002551362 contact08ColumnsJoin0_32 contact08ColumnsJoin32_32
private theorem contact08ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact08) 64 64 = 26214852293522 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 32 32 18614232901564 7600619391958 contact08ColumnsJoin64_32 contact08ColumnsJoin96_32
private theorem contact08ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact08) 128 36 = 1730847250148 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 32 4 1693622075546 37225174602 contact08ColumnsJoin128_32 contact08ColumnsSlice160
private theorem contact08ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact08) 0 128 = 116975927086549 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 64 64 90761074793027 26214852293522 contact08ColumnsJoin0_64 contact08ColumnsJoin64_64
private theorem contact08ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact08) 0 164 = 118706774336697 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 128 36 116975927086549 1730847250148 contact08ColumnsJoin0_128 contact08ColumnsJoin128_36
private theorem contact08OrdinaryRanks : ordinaryRankBound contact08 = 7853331030 := by decide +kernel
private theorem contact08RanksSlice0 : sliceWindow (auxiliaryRankSlice contact08) 0 4 = 31418376 :=
  contactRankWindow_of_rec contact08 0 4 31418376 (by decide +kernel)
private theorem contact08RanksSlice4 : sliceWindow (auxiliaryRankSlice contact08) 4 4 = 29448456 :=
  contactRankWindow_of_rec contact08 4 4 29448456 (by decide +kernel)
private theorem contact08RanksSlice8 : sliceWindow (auxiliaryRankSlice contact08) 8 4 = 27547656 :=
  contactRankWindow_of_rec contact08 8 4 27547656 (by decide +kernel)
private theorem contact08RanksSlice12 : sliceWindow (auxiliaryRankSlice contact08) 12 4 = 25715976 :=
  contactRankWindow_of_rec contact08 12 4 25715976 (by decide +kernel)
private theorem contact08RanksSlice16 : sliceWindow (auxiliaryRankSlice contact08) 16 4 = 23953416 :=
  contactRankWindow_of_rec contact08 16 4 23953416 (by decide +kernel)
private theorem contact08RanksSlice20 : sliceWindow (auxiliaryRankSlice contact08) 20 4 = 22259976 :=
  contactRankWindow_of_rec contact08 20 4 22259976 (by decide +kernel)
private theorem contact08RanksSlice24 : sliceWindow (auxiliaryRankSlice contact08) 24 4 = 20635656 :=
  contactRankWindow_of_rec contact08 24 4 20635656 (by decide +kernel)
private theorem contact08RanksSlice28 : sliceWindow (auxiliaryRankSlice contact08) 28 4 = 19080456 :=
  contactRankWindow_of_rec contact08 28 4 19080456 (by decide +kernel)
private theorem contact08RanksSlice32 : sliceWindow (auxiliaryRankSlice contact08) 32 4 = 17594376 :=
  contactRankWindow_of_rec contact08 32 4 17594376 (by decide +kernel)
private theorem contact08RanksSlice36 : sliceWindow (auxiliaryRankSlice contact08) 36 4 = 16177416 :=
  contactRankWindow_of_rec contact08 36 4 16177416 (by decide +kernel)
private theorem contact08RanksSlice40 : sliceWindow (auxiliaryRankSlice contact08) 40 4 = 14829576 :=
  contactRankWindow_of_rec contact08 40 4 14829576 (by decide +kernel)
private theorem contact08RanksSlice44 : sliceWindow (auxiliaryRankSlice contact08) 44 4 = 13550856 :=
  contactRankWindow_of_rec contact08 44 4 13550856 (by decide +kernel)
private theorem contact08RanksSlice48 : sliceWindow (auxiliaryRankSlice contact08) 48 4 = 12341256 :=
  contactRankWindow_of_rec contact08 48 4 12341256 (by decide +kernel)
private theorem contact08RanksSlice52 : sliceWindow (auxiliaryRankSlice contact08) 52 4 = 11200354 :=
  contactRankWindow_of_rec contact08 52 4 11200354 (by decide +kernel)
private theorem contact08RanksSlice56 : sliceWindow (auxiliaryRankSlice contact08) 56 4 = 10126958 :=
  contactRankWindow_of_rec contact08 56 4 10126958 (by decide +kernel)
private theorem contact08RanksSlice60 : sliceWindow (auxiliaryRankSlice contact08) 60 4 = 9119728 :=
  contactRankWindow_of_rec contact08 60 4 9119728 (by decide +kernel)
private theorem contact08RanksSlice64 : sliceWindow (auxiliaryRankSlice contact08) 64 4 = 8177156 :=
  contactRankWindow_of_rec contact08 64 4 8177156 (by decide +kernel)
private theorem contact08RanksSlice68 : sliceWindow (auxiliaryRankSlice contact08) 68 4 = 7297354 :=
  contactRankWindow_of_rec contact08 68 4 7297354 (by decide +kernel)
private theorem contact08RanksSlice72 : sliceWindow (auxiliaryRankSlice contact08) 72 4 = 6478552 :=
  contactRankWindow_of_rec contact08 72 4 6478552 (by decide +kernel)
private theorem contact08RanksSlice76 : sliceWindow (auxiliaryRankSlice contact08) 76 4 = 5718764 :=
  contactRankWindow_of_rec contact08 76 4 5718764 (by decide +kernel)
private theorem contact08RanksSlice80 : sliceWindow (auxiliaryRankSlice contact08) 80 4 = 5016066 :=
  contactRankWindow_of_rec contact08 80 4 5016066 (by decide +kernel)
private theorem contact08RanksSlice84 : sliceWindow (auxiliaryRankSlice contact08) 84 4 = 4368832 :=
  contactRankWindow_of_rec contact08 84 4 4368832 (by decide +kernel)
private theorem contact08RanksSlice88 : sliceWindow (auxiliaryRankSlice contact08) 88 4 = 3774932 :=
  contactRankWindow_of_rec contact08 88 4 3774932 (by decide +kernel)
private theorem contact08RanksSlice92 : sliceWindow (auxiliaryRankSlice contact08) 92 4 = 3232442 :=
  contactRankWindow_of_rec contact08 92 4 3232442 (by decide +kernel)
private theorem contact08RanksSlice96 : sliceWindow (auxiliaryRankSlice contact08) 96 4 = 2739880 :=
  contactRankWindow_of_rec contact08 96 4 2739880 (by decide +kernel)
private theorem contact08RanksSlice100 : sliceWindow (auxiliaryRankSlice contact08) 100 4 = 2294972 :=
  contactRankWindow_of_rec contact08 100 4 2294972 (by decide +kernel)
private theorem contact08RanksSlice104 : sliceWindow (auxiliaryRankSlice contact08) 104 4 = 1895794 :=
  contactRankWindow_of_rec contact08 104 4 1895794 (by decide +kernel)
private theorem contact08RanksSlice108 : sliceWindow (auxiliaryRankSlice contact08) 108 4 = 1541008 :=
  contactRankWindow_of_rec contact08 108 4 1541008 (by decide +kernel)
private theorem contact08RanksSlice112 : sliceWindow (auxiliaryRankSlice contact08) 112 4 = 1228196 :=
  contactRankWindow_of_rec contact08 112 4 1228196 (by decide +kernel)
private theorem contact08RanksSlice116 : sliceWindow (auxiliaryRankSlice contact08) 116 4 = 955434 :=
  contactRankWindow_of_rec contact08 116 4 955434 (by decide +kernel)
private theorem contact08RanksSlice120 : sliceWindow (auxiliaryRankSlice contact08) 120 4 = 721528 :=
  contactRankWindow_of_rec contact08 120 4 721528 (by decide +kernel)
private theorem contact08RanksSlice124 : sliceWindow (auxiliaryRankSlice contact08) 124 4 = 523916 :=
  contactRankWindow_of_rec contact08 124 4 523916 (by decide +kernel)
private theorem contact08RanksSlice128 : sliceWindow (auxiliaryRankSlice contact08) 128 4 = 360674 :=
  contactRankWindow_of_rec contact08 128 4 360674 (by decide +kernel)
private theorem contact08RanksSlice132 : sliceWindow (auxiliaryRankSlice contact08) 132 4 = 230752 :=
  contactRankWindow_of_rec contact08 132 4 230752 (by decide +kernel)
private theorem contact08RanksSlice136 : sliceWindow (auxiliaryRankSlice contact08) 136 4 = 131444 :=
  contactRankWindow_of_rec contact08 136 4 131444 (by decide +kernel)
private theorem contact08RanksSlice140 : sliceWindow (auxiliaryRankSlice contact08) 140 4 = 60871 :=
  contactRankWindow_of_rec contact08 140 4 60871 (by decide +kernel)
private theorem contact08RanksSlice144 : sliceWindow (auxiliaryRankSlice contact08) 144 4 = 18404 :=
  contactRankWindow_of_rec contact08 144 4 18404 (by decide +kernel)
private theorem contact08RanksSlice148 : sliceWindow (auxiliaryRankSlice contact08) 148 4 = 1035 :=
  contactRankWindow_of_rec contact08 148 4 1035 (by decide +kernel)
private theorem contact08RanksSlice152 : sliceWindow (auxiliaryRankSlice contact08) 152 12 = 0 :=
  contactRankWindow_of_rec contact08 152 12 0 (by decide +kernel)
private theorem contact08RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact08) 0 8 = 60866832 :=
  combineSlices (auxiliaryRankSlice contact08) 0 4 4 31418376 29448456 contact08RanksSlice0 contact08RanksSlice4
private theorem contact08RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact08) 8 8 = 53263632 :=
  combineSlices (auxiliaryRankSlice contact08) 8 4 4 27547656 25715976 contact08RanksSlice8 contact08RanksSlice12
private theorem contact08RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact08) 16 8 = 46213392 :=
  combineSlices (auxiliaryRankSlice contact08) 16 4 4 23953416 22259976 contact08RanksSlice16 contact08RanksSlice20
private theorem contact08RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact08) 24 8 = 39716112 :=
  combineSlices (auxiliaryRankSlice contact08) 24 4 4 20635656 19080456 contact08RanksSlice24 contact08RanksSlice28
private theorem contact08RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact08) 32 8 = 33771792 :=
  combineSlices (auxiliaryRankSlice contact08) 32 4 4 17594376 16177416 contact08RanksSlice32 contact08RanksSlice36
private theorem contact08RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact08) 40 8 = 28380432 :=
  combineSlices (auxiliaryRankSlice contact08) 40 4 4 14829576 13550856 contact08RanksSlice40 contact08RanksSlice44
private theorem contact08RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact08) 48 8 = 23541610 :=
  combineSlices (auxiliaryRankSlice contact08) 48 4 4 12341256 11200354 contact08RanksSlice48 contact08RanksSlice52
private theorem contact08RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact08) 56 8 = 19246686 :=
  combineSlices (auxiliaryRankSlice contact08) 56 4 4 10126958 9119728 contact08RanksSlice56 contact08RanksSlice60
private theorem contact08RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact08) 64 8 = 15474510 :=
  combineSlices (auxiliaryRankSlice contact08) 64 4 4 8177156 7297354 contact08RanksSlice64 contact08RanksSlice68
private theorem contact08RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact08) 72 8 = 12197316 :=
  combineSlices (auxiliaryRankSlice contact08) 72 4 4 6478552 5718764 contact08RanksSlice72 contact08RanksSlice76
private theorem contact08RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact08) 80 8 = 9384898 :=
  combineSlices (auxiliaryRankSlice contact08) 80 4 4 5016066 4368832 contact08RanksSlice80 contact08RanksSlice84
private theorem contact08RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact08) 88 8 = 7007374 :=
  combineSlices (auxiliaryRankSlice contact08) 88 4 4 3774932 3232442 contact08RanksSlice88 contact08RanksSlice92
private theorem contact08RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact08) 96 8 = 5034852 :=
  combineSlices (auxiliaryRankSlice contact08) 96 4 4 2739880 2294972 contact08RanksSlice96 contact08RanksSlice100
private theorem contact08RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact08) 104 8 = 3436802 :=
  combineSlices (auxiliaryRankSlice contact08) 104 4 4 1895794 1541008 contact08RanksSlice104 contact08RanksSlice108
private theorem contact08RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact08) 112 8 = 2183630 :=
  combineSlices (auxiliaryRankSlice contact08) 112 4 4 1228196 955434 contact08RanksSlice112 contact08RanksSlice116
private theorem contact08RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact08) 120 8 = 1245444 :=
  combineSlices (auxiliaryRankSlice contact08) 120 4 4 721528 523916 contact08RanksSlice120 contact08RanksSlice124
private theorem contact08RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact08) 128 8 = 591426 :=
  combineSlices (auxiliaryRankSlice contact08) 128 4 4 360674 230752 contact08RanksSlice128 contact08RanksSlice132
private theorem contact08RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact08) 136 8 = 192315 :=
  combineSlices (auxiliaryRankSlice contact08) 136 4 4 131444 60871 contact08RanksSlice136 contact08RanksSlice140
private theorem contact08RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact08) 144 8 = 19439 :=
  combineSlices (auxiliaryRankSlice contact08) 144 4 4 18404 1035 contact08RanksSlice144 contact08RanksSlice148
private theorem contact08RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact08) 0 16 = 114130464 :=
  combineSlices (auxiliaryRankSlice contact08) 0 8 8 60866832 53263632 contact08RanksJoin0_8 contact08RanksJoin8_8
private theorem contact08RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact08) 16 16 = 85929504 :=
  combineSlices (auxiliaryRankSlice contact08) 16 8 8 46213392 39716112 contact08RanksJoin16_8 contact08RanksJoin24_8
private theorem contact08RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact08) 32 16 = 62152224 :=
  combineSlices (auxiliaryRankSlice contact08) 32 8 8 33771792 28380432 contact08RanksJoin32_8 contact08RanksJoin40_8
private theorem contact08RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact08) 48 16 = 42788296 :=
  combineSlices (auxiliaryRankSlice contact08) 48 8 8 23541610 19246686 contact08RanksJoin48_8 contact08RanksJoin56_8
private theorem contact08RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact08) 64 16 = 27671826 :=
  combineSlices (auxiliaryRankSlice contact08) 64 8 8 15474510 12197316 contact08RanksJoin64_8 contact08RanksJoin72_8
private theorem contact08RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact08) 80 16 = 16392272 :=
  combineSlices (auxiliaryRankSlice contact08) 80 8 8 9384898 7007374 contact08RanksJoin80_8 contact08RanksJoin88_8
private theorem contact08RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact08) 96 16 = 8471654 :=
  combineSlices (auxiliaryRankSlice contact08) 96 8 8 5034852 3436802 contact08RanksJoin96_8 contact08RanksJoin104_8
private theorem contact08RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact08) 112 16 = 3429074 :=
  combineSlices (auxiliaryRankSlice contact08) 112 8 8 2183630 1245444 contact08RanksJoin112_8 contact08RanksJoin120_8
private theorem contact08RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact08) 128 16 = 783741 :=
  combineSlices (auxiliaryRankSlice contact08) 128 8 8 591426 192315 contact08RanksJoin128_8 contact08RanksJoin136_8
private theorem contact08RanksJoin144_20 : sliceWindow (auxiliaryRankSlice contact08) 144 20 = 19439 :=
  combineSlices (auxiliaryRankSlice contact08) 144 8 12 19439 0 contact08RanksJoin144_8 contact08RanksSlice152
private theorem contact08RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact08) 0 32 = 200059968 :=
  combineSlices (auxiliaryRankSlice contact08) 0 16 16 114130464 85929504 contact08RanksJoin0_16 contact08RanksJoin16_16
private theorem contact08RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact08) 32 32 = 104940520 :=
  combineSlices (auxiliaryRankSlice contact08) 32 16 16 62152224 42788296 contact08RanksJoin32_16 contact08RanksJoin48_16
private theorem contact08RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact08) 64 32 = 44064098 :=
  combineSlices (auxiliaryRankSlice contact08) 64 16 16 27671826 16392272 contact08RanksJoin64_16 contact08RanksJoin80_16
private theorem contact08RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact08) 96 32 = 11900728 :=
  combineSlices (auxiliaryRankSlice contact08) 96 16 16 8471654 3429074 contact08RanksJoin96_16 contact08RanksJoin112_16
private theorem contact08RanksJoin128_36 : sliceWindow (auxiliaryRankSlice contact08) 128 36 = 803180 :=
  combineSlices (auxiliaryRankSlice contact08) 128 16 20 783741 19439 contact08RanksJoin128_16 contact08RanksJoin144_20
private theorem contact08RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact08) 0 64 = 305000488 :=
  combineSlices (auxiliaryRankSlice contact08) 0 32 32 200059968 104940520 contact08RanksJoin0_32 contact08RanksJoin32_32
private theorem contact08RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact08) 64 64 = 55964826 :=
  combineSlices (auxiliaryRankSlice contact08) 64 32 32 44064098 11900728 contact08RanksJoin64_32 contact08RanksJoin96_32
private theorem contact08RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact08) 0 128 = 360965314 :=
  combineSlices (auxiliaryRankSlice contact08) 0 64 64 305000488 55964826 contact08RanksJoin0_64 contact08RanksJoin64_64
private theorem contact08RanksJoin0_164 : sliceWindow (auxiliaryRankSlice contact08) 0 164 = 361768494 :=
  combineSlices (auxiliaryRankSlice contact08) 0 128 36 360965314 803180 contact08RanksJoin0_128 contact08RanksJoin128_36
theorem contact08_margin : sourceMargin contact08 :=
  margin_of_checked_counts contact08 164 2034833017704222 118706774336697 7853331030 361768494 rfl contact08OrdinaryColumns contact08ColumnsJoin0_164 contact08OrdinaryRanks contact08RanksJoin0_164 (by decide +kernel)

private theorem contact10OrdinaryColumns : ordinaryColumnCount contact10 = 3786153658631204 := by decide +kernel
private theorem contact10ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact10) 0 4 = 10383633996560 :=
  contactColumnsWindow_fast contact10 0 4 10383633996560 (by decide +kernel)
private theorem contact10ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact10) 4 4 = 9907258624656 :=
  contactColumnsWindow_fast contact10 4 4 9907258624656 (by decide +kernel)
private theorem contact10ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact10) 8 4 = 9442122983952 :=
  contactColumnsWindow_fast contact10 8 4 9442122983952 (by decide +kernel)
private theorem contact10ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact10) 12 4 = 8988227074448 :=
  contactColumnsWindow_fast contact10 12 4 8988227074448 (by decide +kernel)
private theorem contact10ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact10) 16 4 = 8545570896144 :=
  contactColumnsWindow_fast contact10 16 4 8545570896144 (by decide +kernel)
private theorem contact10ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact10) 20 4 = 8114154449040 :=
  contactColumnsWindow_fast contact10 20 4 8114154449040 (by decide +kernel)
private theorem contact10ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact10) 24 4 = 7693977733136 :=
  contactColumnsWindow_fast contact10 24 4 7693977733136 (by decide +kernel)
private theorem contact10ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact10) 28 4 = 7285073301082 :=
  contactColumnsWindow_fast contact10 28 4 7285073301082 (by decide +kernel)
private theorem contact10ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact10) 32 4 = 6887458842378 :=
  contactColumnsWindow_fast contact10 32 4 6887458842378 (by decide +kernel)
private theorem contact10ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact10) 36 4 = 6501087315196 :=
  contactColumnsWindow_fast contact10 36 4 6501087315196 (by decide +kernel)
private theorem contact10ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact10) 40 4 = 6125958459705 :=
  contactColumnsWindow_fast contact10 40 4 6125958459705 (by decide +kernel)
private theorem contact10ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact10) 44 4 = 5762073377622 :=
  contactColumnsWindow_fast contact10 44 4 5762073377622 (by decide +kernel)
private theorem contact10ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact10) 48 4 = 5409470711058 :=
  contactColumnsWindow_fast contact10 48 4 5409470711058 (by decide +kernel)
private theorem contact10ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact10) 52 4 = 5068154973470 :=
  contactColumnsWindow_fast contact10 52 4 5068154973470 (by decide +kernel)
private theorem contact10ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact10) 56 4 = 4738084947183 :=
  contactColumnsWindow_fast contact10 56 4 4738084947183 (by decide +kernel)
private theorem contact10ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact10) 60 4 = 4419262223138 :=
  contactColumnsWindow_fast contact10 60 4 4419262223138 (by decide +kernel)
private theorem contact10ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact10) 64 4 = 4111685723303 :=
  contactColumnsWindow_fast contact10 64 4 4111685723303 (by decide +kernel)
private theorem contact10ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact10) 68 4 = 3815404226133 :=
  contactColumnsWindow_fast contact10 68 4 3815404226133 (by decide +kernel)
private theorem contact10ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact10) 72 4 = 3530404762118 :=
  contactColumnsWindow_fast contact10 72 4 3530404762118 (by decide +kernel)
private theorem contact10ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact10) 76 4 = 3256656333603 :=
  contactColumnsWindow_fast contact10 76 4 3256656333603 (by decide +kernel)
private theorem contact10ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact10) 80 4 = 2994157707230 :=
  contactColumnsWindow_fast contact10 80 4 2994157707230 (by decide +kernel)
private theorem contact10ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact10) 84 4 = 2742911402620 :=
  contactColumnsWindow_fast contact10 84 4 2742911402620 (by decide +kernel)
private theorem contact10ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact10) 88 4 = 2502965766495 :=
  contactColumnsWindow_fast contact10 88 4 2502965766495 (by decide +kernel)
private theorem contact10ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact10) 92 4 = 2274295804412 :=
  contactColumnsWindow_fast contact10 92 4 2274295804412 (by decide +kernel)
private theorem contact10ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact10) 96 4 = 2056876838325 :=
  contactColumnsWindow_fast contact10 96 4 2056876838325 (by decide +kernel)
private theorem contact10ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact10) 100 4 = 1850707903107 :=
  contactColumnsWindow_fast contact10 100 4 1850707903107 (by decide +kernel)
private theorem contact10ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact10) 104 4 = 1655793004918 :=
  contactColumnsWindow_fast contact10 104 4 1655793004918 (by decide +kernel)
private theorem contact10ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact10) 108 4 = 1472182134633 :=
  contactColumnsWindow_fast contact10 108 4 1472182134633 (by decide +kernel)
private theorem contact10ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact10) 112 4 = 1299841705433 :=
  contactColumnsWindow_fast contact10 112 4 1299841705433 (by decide +kernel)
private theorem contact10ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact10) 116 4 = 1138752295437 :=
  contactColumnsWindow_fast contact10 116 4 1138752295437 (by decide +kernel)
private theorem contact10ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact10) 120 4 = 988913083197 :=
  contactColumnsWindow_fast contact10 120 4 988913083197 (by decide +kernel)
private theorem contact10ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact10) 124 4 = 850329434992 :=
  contactColumnsWindow_fast contact10 124 4 850329434992 (by decide +kernel)
private theorem contact10ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact10) 128 4 = 723053386667 :=
  contactColumnsWindow_fast contact10 128 4 723053386667 (by decide +kernel)
private theorem contact10ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact10) 132 4 = 607042701797 :=
  contactColumnsWindow_fast contact10 132 4 607042701797 (by decide +kernel)
private theorem contact10ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact10) 136 4 = 502282611258 :=
  contactColumnsWindow_fast contact10 136 4 502282611258 (by decide +kernel)
private theorem contact10ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact10) 140 4 = 408773065184 :=
  contactColumnsWindow_fast contact10 140 4 408773065184 (by decide +kernel)
private theorem contact10ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact10) 144 4 = 326507584098 :=
  contactColumnsWindow_fast contact10 144 4 326507584098 (by decide +kernel)
private theorem contact10ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact10) 148 4 = 255395264013 :=
  contactColumnsWindow_fast contact10 148 4 255395264013 (by decide +kernel)
private theorem contact10ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact10) 152 4 = 195043619802 :=
  contactColumnsWindow_fast contact10 152 4 195043619802 (by decide +kernel)
private theorem contact10ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact10) 156 4 = 144924029780 :=
  contactColumnsWindow_fast contact10 156 4 144924029780 (by decide +kernel)
private theorem contact10ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact10) 160 4 = 104357762773 :=
  contactColumnsWindow_fast contact10 160 4 104357762773 (by decide +kernel)
private theorem contact10ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact10) 164 4 = 72512061708 :=
  contactColumnsWindow_fast contact10 164 4 72512061708 (by decide +kernel)
private theorem contact10ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact10) 168 4 = 48408260385 :=
  contactColumnsWindow_fast contact10 168 4 48408260385 (by decide +kernel)
private theorem contact10ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact10) 172 1 = 9129627962 :=
  contactColumnsWindow_fast contact10 172 1 9129627962 (by decide +kernel)
private theorem contact10ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact10) 0 8 = 20290892621216 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 4 4 10383633996560 9907258624656 contact10ColumnsSlice0 contact10ColumnsSlice4
private theorem contact10ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact10) 8 8 = 18430350058400 :=
  combineSlices (auxiliaryColumnSlice contact10) 8 4 4 9442122983952 8988227074448 contact10ColumnsSlice8 contact10ColumnsSlice12
private theorem contact10ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact10) 16 8 = 16659725345184 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 4 4 8545570896144 8114154449040 contact10ColumnsSlice16 contact10ColumnsSlice20
private theorem contact10ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact10) 24 8 = 14979051034218 :=
  combineSlices (auxiliaryColumnSlice contact10) 24 4 4 7693977733136 7285073301082 contact10ColumnsSlice24 contact10ColumnsSlice28
private theorem contact10ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact10) 32 8 = 13388546157574 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 4 4 6887458842378 6501087315196 contact10ColumnsSlice32 contact10ColumnsSlice36
private theorem contact10ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact10) 40 8 = 11888031837327 :=
  combineSlices (auxiliaryColumnSlice contact10) 40 4 4 6125958459705 5762073377622 contact10ColumnsSlice40 contact10ColumnsSlice44
private theorem contact10ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact10) 48 8 = 10477625684528 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 4 4 5409470711058 5068154973470 contact10ColumnsSlice48 contact10ColumnsSlice52
private theorem contact10ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact10) 56 8 = 9157347170321 :=
  combineSlices (auxiliaryColumnSlice contact10) 56 4 4 4738084947183 4419262223138 contact10ColumnsSlice56 contact10ColumnsSlice60
private theorem contact10ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact10) 64 8 = 7927089949436 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 4 4 4111685723303 3815404226133 contact10ColumnsSlice64 contact10ColumnsSlice68
private theorem contact10ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact10) 72 8 = 6787061095721 :=
  combineSlices (auxiliaryColumnSlice contact10) 72 4 4 3530404762118 3256656333603 contact10ColumnsSlice72 contact10ColumnsSlice76
private theorem contact10ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact10) 80 8 = 5737069109850 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 4 4 2994157707230 2742911402620 contact10ColumnsSlice80 contact10ColumnsSlice84
private theorem contact10ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact10) 88 8 = 4777261570907 :=
  combineSlices (auxiliaryColumnSlice contact10) 88 4 4 2502965766495 2274295804412 contact10ColumnsSlice88 contact10ColumnsSlice92
private theorem contact10ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact10) 96 8 = 3907584741432 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 4 4 2056876838325 1850707903107 contact10ColumnsSlice96 contact10ColumnsSlice100
private theorem contact10ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact10) 104 8 = 3127975139551 :=
  combineSlices (auxiliaryColumnSlice contact10) 104 4 4 1655793004918 1472182134633 contact10ColumnsSlice104 contact10ColumnsSlice108
private theorem contact10ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact10) 112 8 = 2438594000870 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 4 4 1299841705433 1138752295437 contact10ColumnsSlice112 contact10ColumnsSlice116
private theorem contact10ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact10) 120 8 = 1839242518189 :=
  combineSlices (auxiliaryColumnSlice contact10) 120 4 4 988913083197 850329434992 contact10ColumnsSlice120 contact10ColumnsSlice124
private theorem contact10ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact10) 128 8 = 1330096088464 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 4 4 723053386667 607042701797 contact10ColumnsSlice128 contact10ColumnsSlice132
private theorem contact10ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact10) 136 8 = 911055676442 :=
  combineSlices (auxiliaryColumnSlice contact10) 136 4 4 502282611258 408773065184 contact10ColumnsSlice136 contact10ColumnsSlice140
private theorem contact10ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact10) 144 8 = 581902848111 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 4 4 326507584098 255395264013 contact10ColumnsSlice144 contact10ColumnsSlice148
private theorem contact10ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact10) 152 8 = 339967649582 :=
  combineSlices (auxiliaryColumnSlice contact10) 152 4 4 195043619802 144924029780 contact10ColumnsSlice152 contact10ColumnsSlice156
private theorem contact10ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact10) 160 8 = 176869824481 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 4 4 104357762773 72512061708 contact10ColumnsSlice160 contact10ColumnsSlice164
private theorem contact10ColumnsJoin168_5 : sliceWindow (auxiliaryColumnSlice contact10) 168 5 = 57537888347 :=
  combineSlices (auxiliaryColumnSlice contact10) 168 4 1 48408260385 9129627962 contact10ColumnsSlice168 contact10ColumnsSlice172
private theorem contact10ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact10) 0 16 = 38721242679616 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 8 8 20290892621216 18430350058400 contact10ColumnsJoin0_8 contact10ColumnsJoin8_8
private theorem contact10ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact10) 16 16 = 31638776379402 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 8 8 16659725345184 14979051034218 contact10ColumnsJoin16_8 contact10ColumnsJoin24_8
private theorem contact10ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact10) 32 16 = 25276577994901 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 8 8 13388546157574 11888031837327 contact10ColumnsJoin32_8 contact10ColumnsJoin40_8
private theorem contact10ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact10) 48 16 = 19634972854849 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 8 8 10477625684528 9157347170321 contact10ColumnsJoin48_8 contact10ColumnsJoin56_8
private theorem contact10ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact10) 64 16 = 14714151045157 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 8 8 7927089949436 6787061095721 contact10ColumnsJoin64_8 contact10ColumnsJoin72_8
private theorem contact10ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact10) 80 16 = 10514330680757 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 8 8 5737069109850 4777261570907 contact10ColumnsJoin80_8 contact10ColumnsJoin88_8
private theorem contact10ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact10) 96 16 = 7035559880983 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 8 8 3907584741432 3127975139551 contact10ColumnsJoin96_8 contact10ColumnsJoin104_8
private theorem contact10ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact10) 112 16 = 4277836519059 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 8 8 2438594000870 1839242518189 contact10ColumnsJoin112_8 contact10ColumnsJoin120_8
private theorem contact10ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact10) 128 16 = 2241151764906 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 8 8 1330096088464 911055676442 contact10ColumnsJoin128_8 contact10ColumnsJoin136_8
private theorem contact10ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact10) 144 16 = 921870497693 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 8 8 581902848111 339967649582 contact10ColumnsJoin144_8 contact10ColumnsJoin152_8
private theorem contact10ColumnsJoin160_13 : sliceWindow (auxiliaryColumnSlice contact10) 160 13 = 234407712828 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 8 5 176869824481 57537888347 contact10ColumnsJoin160_8 contact10ColumnsJoin168_5
private theorem contact10ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact10) 0 32 = 70360019059018 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 16 16 38721242679616 31638776379402 contact10ColumnsJoin0_16 contact10ColumnsJoin16_16
private theorem contact10ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact10) 32 32 = 44911550849750 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 16 16 25276577994901 19634972854849 contact10ColumnsJoin32_16 contact10ColumnsJoin48_16
private theorem contact10ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact10) 64 32 = 25228481725914 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 16 16 14714151045157 10514330680757 contact10ColumnsJoin64_16 contact10ColumnsJoin80_16
private theorem contact10ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact10) 96 32 = 11313396400042 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 16 16 7035559880983 4277836519059 contact10ColumnsJoin96_16 contact10ColumnsJoin112_16
private theorem contact10ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact10) 128 32 = 3163022262599 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 16 16 2241151764906 921870497693 contact10ColumnsJoin128_16 contact10ColumnsJoin144_16
private theorem contact10ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact10) 0 64 = 115271569908768 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 32 32 70360019059018 44911550849750 contact10ColumnsJoin0_32 contact10ColumnsJoin32_32
private theorem contact10ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact10) 64 64 = 36541878125956 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 32 32 25228481725914 11313396400042 contact10ColumnsJoin64_32 contact10ColumnsJoin96_32
private theorem contact10ColumnsJoin128_45 : sliceWindow (auxiliaryColumnSlice contact10) 128 45 = 3397429975427 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 32 13 3163022262599 234407712828 contact10ColumnsJoin128_32 contact10ColumnsJoin160_13
private theorem contact10ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact10) 0 128 = 151813448034724 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 64 64 115271569908768 36541878125956 contact10ColumnsJoin0_64 contact10ColumnsJoin64_64
private theorem contact10ColumnsJoin0_173 : sliceWindow (auxiliaryColumnSlice contact10) 0 173 = 155210878010151 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 128 45 151813448034724 3397429975427 contact10ColumnsJoin0_128 contact10ColumnsJoin128_45
private theorem contact10OrdinaryRanks : ordinaryRankBound contact10 = 14560880446 := by decide +kernel
private theorem contact10RanksSlice0 : sliceWindow (auxiliaryRankSlice contact10) 0 4 = 39177548 :=
  contactRankWindow_of_rec contact10 0 4 39177548 (by decide +kernel)
private theorem contact10RanksSlice4 : sliceWindow (auxiliaryRankSlice contact10) 4 4 = 36842828 :=
  contactRankWindow_of_rec contact10 4 4 36842828 (by decide +kernel)
private theorem contact10RanksSlice8 : sliceWindow (auxiliaryRankSlice contact10) 8 4 = 34585932 :=
  contactRankWindow_of_rec contact10 8 4 34585932 (by decide +kernel)
private theorem contact10RanksSlice12 : sliceWindow (auxiliaryRankSlice contact10) 12 4 = 32406860 :=
  contactRankWindow_of_rec contact10 12 4 32406860 (by decide +kernel)
private theorem contact10RanksSlice16 : sliceWindow (auxiliaryRankSlice contact10) 16 4 = 30305612 :=
  contactRankWindow_of_rec contact10 16 4 30305612 (by decide +kernel)
private theorem contact10RanksSlice20 : sliceWindow (auxiliaryRankSlice contact10) 20 4 = 28282188 :=
  contactRankWindow_of_rec contact10 20 4 28282188 (by decide +kernel)
private theorem contact10RanksSlice24 : sliceWindow (auxiliaryRankSlice contact10) 24 4 = 26336588 :=
  contactRankWindow_of_rec contact10 24 4 26336588 (by decide +kernel)
private theorem contact10RanksSlice28 : sliceWindow (auxiliaryRankSlice contact10) 28 4 = 24468812 :=
  contactRankWindow_of_rec contact10 28 4 24468812 (by decide +kernel)
private theorem contact10RanksSlice32 : sliceWindow (auxiliaryRankSlice contact10) 32 4 = 22678860 :=
  contactRankWindow_of_rec contact10 32 4 22678860 (by decide +kernel)
private theorem contact10RanksSlice36 : sliceWindow (auxiliaryRankSlice contact10) 36 4 = 20966732 :=
  contactRankWindow_of_rec contact10 36 4 20966732 (by decide +kernel)
private theorem contact10RanksSlice40 : sliceWindow (auxiliaryRankSlice contact10) 40 4 = 19332428 :=
  contactRankWindow_of_rec contact10 40 4 19332428 (by decide +kernel)
private theorem contact10RanksSlice44 : sliceWindow (auxiliaryRankSlice contact10) 44 4 = 17775948 :=
  contactRankWindow_of_rec contact10 44 4 17775948 (by decide +kernel)
private theorem contact10RanksSlice48 : sliceWindow (auxiliaryRankSlice contact10) 48 4 = 16297292 :=
  contactRankWindow_of_rec contact10 48 4 16297292 (by decide +kernel)
private theorem contact10RanksSlice52 : sliceWindow (auxiliaryRankSlice contact10) 52 4 = 14896364 :=
  contactRankWindow_of_rec contact10 52 4 14896364 (by decide +kernel)
private theorem contact10RanksSlice56 : sliceWindow (auxiliaryRankSlice contact10) 56 4 = 13572226 :=
  contactRankWindow_of_rec contact10 56 4 13572226 (by decide +kernel)
private theorem contact10RanksSlice60 : sliceWindow (auxiliaryRankSlice contact10) 60 4 = 12323468 :=
  contactRankWindow_of_rec contact10 60 4 12323468 (by decide +kernel)
private theorem contact10RanksSlice64 : sliceWindow (auxiliaryRankSlice contact10) 64 4 = 11148642 :=
  contactRankWindow_of_rec contact10 64 4 11148642 (by decide +kernel)
private theorem contact10RanksSlice68 : sliceWindow (auxiliaryRankSlice contact10) 68 4 = 10045948 :=
  contactRankWindow_of_rec contact10 68 4 10045948 (by decide +kernel)
private theorem contact10RanksSlice72 : sliceWindow (auxiliaryRankSlice contact10) 72 4 = 9013356 :=
  contactRankWindow_of_rec contact10 72 4 9013356 (by decide +kernel)
private theorem contact10RanksSlice76 : sliceWindow (auxiliaryRankSlice contact10) 76 4 = 8048826 :=
  contactRankWindow_of_rec contact10 76 4 8048826 (by decide +kernel)
private theorem contact10RanksSlice80 : sliceWindow (auxiliaryRankSlice contact10) 80 4 = 7150556 :=
  contactRankWindow_of_rec contact10 80 4 7150556 (by decide +kernel)
private theorem contact10RanksSlice84 : sliceWindow (auxiliaryRankSlice contact10) 84 4 = 6316364 :=
  contactRankWindow_of_rec contact10 84 4 6316364 (by decide +kernel)
private theorem contact10RanksSlice88 : sliceWindow (auxiliaryRankSlice contact10) 88 4 = 5544210 :=
  contactRankWindow_of_rec contact10 88 4 5544210 (by decide +kernel)
private theorem contact10RanksSlice92 : sliceWindow (auxiliaryRankSlice contact10) 92 4 = 4832444 :=
  contactRankWindow_of_rec contact10 92 4 4832444 (by decide +kernel)
private theorem contact10RanksSlice96 : sliceWindow (auxiliaryRankSlice contact10) 96 4 = 4178732 :=
  contactRankWindow_of_rec contact10 96 4 4178732 (by decide +kernel)
private theorem contact10RanksSlice100 : sliceWindow (auxiliaryRankSlice contact10) 100 4 = 3581034 :=
  contactRankWindow_of_rec contact10 100 4 3581034 (by decide +kernel)
private theorem contact10RanksSlice104 : sliceWindow (auxiliaryRankSlice contact10) 104 4 = 3037852 :=
  contactRankWindow_of_rec contact10 104 4 3037852 (by decide +kernel)
private theorem contact10RanksSlice108 : sliceWindow (auxiliaryRankSlice contact10) 108 4 = 2546700 :=
  contactRankWindow_of_rec contact10 108 4 2546700 (by decide +kernel)
private theorem contact10RanksSlice112 : sliceWindow (auxiliaryRankSlice contact10) 112 4 = 2105538 :=
  contactRankWindow_of_rec contact10 112 4 2105538 (by decide +kernel)
private theorem contact10RanksSlice116 : sliceWindow (auxiliaryRankSlice contact10) 116 4 = 1713020 :=
  contactRankWindow_of_rec contact10 116 4 1713020 (by decide +kernel)
private theorem contact10RanksSlice120 : sliceWindow (auxiliaryRankSlice contact10) 120 4 = 1366508 :=
  contactRankWindow_of_rec contact10 120 4 1366508 (by decide +kernel)
private theorem contact10RanksSlice124 : sliceWindow (auxiliaryRankSlice contact10) 124 4 = 1063962 :=
  contactRankWindow_of_rec contact10 124 4 1063962 (by decide +kernel)
private theorem contact10RanksSlice128 : sliceWindow (auxiliaryRankSlice contact10) 128 4 = 804188 :=
  contactRankWindow_of_rec contact10 128 4 804188 (by decide +kernel)
private theorem contact10RanksSlice132 : sliceWindow (auxiliaryRankSlice contact10) 132 4 = 584396 :=
  contactRankWindow_of_rec contact10 132 4 584396 (by decide +kernel)
private theorem contact10RanksSlice136 : sliceWindow (auxiliaryRankSlice contact10) 136 4 = 402546 :=
  contactRankWindow_of_rec contact10 136 4 402546 (by decide +kernel)
private theorem contact10RanksSlice140 : sliceWindow (auxiliaryRankSlice contact10) 140 4 = 257596 :=
  contactRankWindow_of_rec contact10 140 4 257596 (by decide +kernel)
private theorem contact10RanksSlice144 : sliceWindow (auxiliaryRankSlice contact10) 144 4 = 146608 :=
  contactRankWindow_of_rec contact10 144 4 146608 (by decide +kernel)
private theorem contact10RanksSlice148 : sliceWindow (auxiliaryRankSlice contact10) 148 4 = 67753 :=
  contactRankWindow_of_rec contact10 148 4 67753 (by decide +kernel)
private theorem contact10RanksSlice152 : sliceWindow (auxiliaryRankSlice contact10) 152 4 = 20455 :=
  contactRankWindow_of_rec contact10 152 4 20455 (by decide +kernel)
private theorem contact10RanksSlice156 : sliceWindow (auxiliaryRankSlice contact10) 156 4 = 1150 :=
  contactRankWindow_of_rec contact10 156 4 1150 (by decide +kernel)
private theorem contact10RanksSlice160 : sliceWindow (auxiliaryRankSlice contact10) 160 13 = 0 :=
  contactRankWindow_of_rec contact10 160 13 0 (by decide +kernel)
private theorem contact10RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact10) 0 8 = 76020376 :=
  combineSlices (auxiliaryRankSlice contact10) 0 4 4 39177548 36842828 contact10RanksSlice0 contact10RanksSlice4
private theorem contact10RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact10) 8 8 = 66992792 :=
  combineSlices (auxiliaryRankSlice contact10) 8 4 4 34585932 32406860 contact10RanksSlice8 contact10RanksSlice12
private theorem contact10RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact10) 16 8 = 58587800 :=
  combineSlices (auxiliaryRankSlice contact10) 16 4 4 30305612 28282188 contact10RanksSlice16 contact10RanksSlice20
private theorem contact10RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact10) 24 8 = 50805400 :=
  combineSlices (auxiliaryRankSlice contact10) 24 4 4 26336588 24468812 contact10RanksSlice24 contact10RanksSlice28
private theorem contact10RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact10) 32 8 = 43645592 :=
  combineSlices (auxiliaryRankSlice contact10) 32 4 4 22678860 20966732 contact10RanksSlice32 contact10RanksSlice36
private theorem contact10RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact10) 40 8 = 37108376 :=
  combineSlices (auxiliaryRankSlice contact10) 40 4 4 19332428 17775948 contact10RanksSlice40 contact10RanksSlice44
private theorem contact10RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact10) 48 8 = 31193656 :=
  combineSlices (auxiliaryRankSlice contact10) 48 4 4 16297292 14896364 contact10RanksSlice48 contact10RanksSlice52
private theorem contact10RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact10) 56 8 = 25895694 :=
  combineSlices (auxiliaryRankSlice contact10) 56 4 4 13572226 12323468 contact10RanksSlice56 contact10RanksSlice60
private theorem contact10RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact10) 64 8 = 21194590 :=
  combineSlices (auxiliaryRankSlice contact10) 64 4 4 11148642 10045948 contact10RanksSlice64 contact10RanksSlice68
private theorem contact10RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact10) 72 8 = 17062182 :=
  combineSlices (auxiliaryRankSlice contact10) 72 4 4 9013356 8048826 contact10RanksSlice72 contact10RanksSlice76
private theorem contact10RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact10) 80 8 = 13466920 :=
  combineSlices (auxiliaryRankSlice contact10) 80 4 4 7150556 6316364 contact10RanksSlice80 contact10RanksSlice84
private theorem contact10RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact10) 88 8 = 10376654 :=
  combineSlices (auxiliaryRankSlice contact10) 88 4 4 5544210 4832444 contact10RanksSlice88 contact10RanksSlice92
private theorem contact10RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact10) 96 8 = 7759766 :=
  combineSlices (auxiliaryRankSlice contact10) 96 4 4 4178732 3581034 contact10RanksSlice96 contact10RanksSlice100
private theorem contact10RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact10) 104 8 = 5584552 :=
  combineSlices (auxiliaryRankSlice contact10) 104 4 4 3037852 2546700 contact10RanksSlice104 contact10RanksSlice108
private theorem contact10RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact10) 112 8 = 3818558 :=
  combineSlices (auxiliaryRankSlice contact10) 112 4 4 2105538 1713020 contact10RanksSlice112 contact10RanksSlice116
private theorem contact10RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact10) 120 8 = 2430470 :=
  combineSlices (auxiliaryRankSlice contact10) 120 4 4 1366508 1063962 contact10RanksSlice120 contact10RanksSlice124
private theorem contact10RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact10) 128 8 = 1388584 :=
  combineSlices (auxiliaryRankSlice contact10) 128 4 4 804188 584396 contact10RanksSlice128 contact10RanksSlice132
private theorem contact10RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact10) 136 8 = 660142 :=
  combineSlices (auxiliaryRankSlice contact10) 136 4 4 402546 257596 contact10RanksSlice136 contact10RanksSlice140
private theorem contact10RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact10) 144 8 = 214361 :=
  combineSlices (auxiliaryRankSlice contact10) 144 4 4 146608 67753 contact10RanksSlice144 contact10RanksSlice148
private theorem contact10RanksJoin152_8 : sliceWindow (auxiliaryRankSlice contact10) 152 8 = 21605 :=
  combineSlices (auxiliaryRankSlice contact10) 152 4 4 20455 1150 contact10RanksSlice152 contact10RanksSlice156
private theorem contact10RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact10) 0 16 = 143013168 :=
  combineSlices (auxiliaryRankSlice contact10) 0 8 8 76020376 66992792 contact10RanksJoin0_8 contact10RanksJoin8_8
private theorem contact10RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact10) 16 16 = 109393200 :=
  combineSlices (auxiliaryRankSlice contact10) 16 8 8 58587800 50805400 contact10RanksJoin16_8 contact10RanksJoin24_8
private theorem contact10RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact10) 32 16 = 80753968 :=
  combineSlices (auxiliaryRankSlice contact10) 32 8 8 43645592 37108376 contact10RanksJoin32_8 contact10RanksJoin40_8
private theorem contact10RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact10) 48 16 = 57089350 :=
  combineSlices (auxiliaryRankSlice contact10) 48 8 8 31193656 25895694 contact10RanksJoin48_8 contact10RanksJoin56_8
private theorem contact10RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact10) 64 16 = 38256772 :=
  combineSlices (auxiliaryRankSlice contact10) 64 8 8 21194590 17062182 contact10RanksJoin64_8 contact10RanksJoin72_8
private theorem contact10RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact10) 80 16 = 23843574 :=
  combineSlices (auxiliaryRankSlice contact10) 80 8 8 13466920 10376654 contact10RanksJoin80_8 contact10RanksJoin88_8
private theorem contact10RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact10) 96 16 = 13344318 :=
  combineSlices (auxiliaryRankSlice contact10) 96 8 8 7759766 5584552 contact10RanksJoin96_8 contact10RanksJoin104_8
private theorem contact10RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact10) 112 16 = 6249028 :=
  combineSlices (auxiliaryRankSlice contact10) 112 8 8 3818558 2430470 contact10RanksJoin112_8 contact10RanksJoin120_8
private theorem contact10RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact10) 128 16 = 2048726 :=
  combineSlices (auxiliaryRankSlice contact10) 128 8 8 1388584 660142 contact10RanksJoin128_8 contact10RanksJoin136_8
private theorem contact10RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact10) 144 16 = 235966 :=
  combineSlices (auxiliaryRankSlice contact10) 144 8 8 214361 21605 contact10RanksJoin144_8 contact10RanksJoin152_8
private theorem contact10RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact10) 0 32 = 252406368 :=
  combineSlices (auxiliaryRankSlice contact10) 0 16 16 143013168 109393200 contact10RanksJoin0_16 contact10RanksJoin16_16
private theorem contact10RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact10) 32 32 = 137843318 :=
  combineSlices (auxiliaryRankSlice contact10) 32 16 16 80753968 57089350 contact10RanksJoin32_16 contact10RanksJoin48_16
private theorem contact10RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact10) 64 32 = 62100346 :=
  combineSlices (auxiliaryRankSlice contact10) 64 16 16 38256772 23843574 contact10RanksJoin64_16 contact10RanksJoin80_16
private theorem contact10RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact10) 96 32 = 19593346 :=
  combineSlices (auxiliaryRankSlice contact10) 96 16 16 13344318 6249028 contact10RanksJoin96_16 contact10RanksJoin112_16
private theorem contact10RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact10) 128 32 = 2284692 :=
  combineSlices (auxiliaryRankSlice contact10) 128 16 16 2048726 235966 contact10RanksJoin128_16 contact10RanksJoin144_16
private theorem contact10RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact10) 0 64 = 390249686 :=
  combineSlices (auxiliaryRankSlice contact10) 0 32 32 252406368 137843318 contact10RanksJoin0_32 contact10RanksJoin32_32
private theorem contact10RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact10) 64 64 = 81693692 :=
  combineSlices (auxiliaryRankSlice contact10) 64 32 32 62100346 19593346 contact10RanksJoin64_32 contact10RanksJoin96_32
private theorem contact10RanksJoin128_45 : sliceWindow (auxiliaryRankSlice contact10) 128 45 = 2284692 :=
  combineSlices (auxiliaryRankSlice contact10) 128 32 13 2284692 0 contact10RanksJoin128_32 contact10RanksSlice160
private theorem contact10RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact10) 0 128 = 471943378 :=
  combineSlices (auxiliaryRankSlice contact10) 0 64 64 390249686 81693692 contact10RanksJoin0_64 contact10RanksJoin64_64
private theorem contact10RanksJoin0_173 : sliceWindow (auxiliaryRankSlice contact10) 0 173 = 474228070 :=
  combineSlices (auxiliaryRankSlice contact10) 0 128 45 471943378 2284692 contact10RanksJoin0_128 contact10RanksJoin128_45
theorem contact10_margin : sourceMargin contact10 :=
  margin_of_checked_counts contact10 173 3786153658631204 155210878010151 14560880446 474228070 rfl contact10OrdinaryColumns contact10ColumnsJoin0_173 contact10OrdinaryRanks contact10RanksJoin0_173 (by decide +kernel)

private theorem contact12OrdinaryColumns : ordinaryColumnCount contact12 = 177977180559548 := by decide +kernel
private theorem contact12ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact12) 0 4 = 1141121198170 :=
  contactColumnsWindow_fast contact12 0 4 1141121198170 (by decide +kernel)
private theorem contact12ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact12) 4 4 = 1049379012138 :=
  contactColumnsWindow_fast contact12 4 4 1049379012138 (by decide +kernel)
private theorem contact12ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact12) 8 4 = 961504406496 :=
  contactColumnsWindow_fast contact12 8 4 961504406496 (by decide +kernel)
private theorem contact12ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact12) 12 4 = 877496202410 :=
  contactColumnsWindow_fast contact12 12 4 877496202410 (by decide +kernel)
private theorem contact12ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact12) 16 4 = 797353211769 :=
  contactColumnsWindow_fast contact12 16 4 797353211769 (by decide +kernel)
private theorem contact12ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact12) 20 4 = 721083406570 :=
  contactColumnsWindow_fast contact12 20 4 721083406570 (by decide +kernel)
private theorem contact12ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact12) 24 4 = 648703097202 :=
  contactColumnsWindow_fast contact12 24 4 648703097202 (by decide +kernel)
private theorem contact12ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact12) 28 4 = 580191701988 :=
  contactColumnsWindow_fast contact12 28 4 580191701988 (by decide +kernel)
private theorem contact12ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact12) 32 4 = 515546530562 :=
  contactColumnsWindow_fast contact12 32 4 515546530562 (by decide +kernel)
private theorem contact12ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact12) 36 4 = 454766813442 :=
  contactColumnsWindow_fast contact12 36 4 454766813442 (by decide +kernel)
private theorem contact12ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact12) 40 4 = 397862249290 :=
  contactColumnsWindow_fast contact12 40 4 397862249290 (by decide +kernel)
private theorem contact12ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact12) 44 4 = 344846029314 :=
  contactColumnsWindow_fast contact12 44 4 344846029314 (by decide +kernel)
private theorem contact12ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact12) 48 4 = 295697852178 :=
  contactColumnsWindow_fast contact12 48 4 295697852178 (by decide +kernel)
private theorem contact12ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact12) 52 4 = 250415705762 :=
  contactColumnsWindow_fast contact12 52 4 250415705762 (by decide +kernel)
private theorem contact12ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact12) 56 4 = 208999307706 :=
  contactColumnsWindow_fast contact12 56 4 208999307706 (by decide +kernel)
private theorem contact12ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact12) 60 4 = 171459962638 :=
  contactColumnsWindow_fast contact12 60 4 171459962638 (by decide +kernel)
private theorem contact12ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact12) 64 4 = 137807808474 :=
  contactColumnsWindow_fast contact12 64 4 137807808474 (by decide +kernel)
private theorem contact12ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact12) 68 4 = 108022930650 :=
  contactColumnsWindow_fast contact12 68 4 108022930650 (by decide +kernel)
private theorem contact12ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact12) 72 4 = 82103728010 :=
  contactColumnsWindow_fast contact12 72 4 82103728010 (by decide +kernel)
private theorem contact12ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact12) 76 4 = 60050649018 :=
  contactColumnsWindow_fast contact12 76 4 60050649018 (by decide +kernel)
private theorem contact12ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact12) 80 4 = 41875959635 :=
  contactColumnsWindow_fast contact12 80 4 41875959635 (by decide +kernel)
private theorem contact12ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact12) 84 4 = 27538970165 :=
  contactColumnsWindow_fast contact12 84 4 27538970165 (by decide +kernel)
private theorem contact12ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact12) 88 4 = 16824323381 :=
  contactColumnsWindow_fast contact12 88 4 16824323381 (by decide +kernel)
private theorem contact12ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact12) 92 4 = 9365956705 :=
  contactColumnsWindow_fast contact12 92 4 9365956705 (by decide +kernel)
private theorem contact12ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact12) 96 2 = 2764397982 :=
  contactColumnsWindow_fast contact12 96 2 2764397982 (by decide +kernel)
private theorem contact12ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact12) 0 8 = 2190500210308 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 4 4 1141121198170 1049379012138 contact12ColumnsSlice0 contact12ColumnsSlice4
private theorem contact12ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact12) 8 8 = 1839000608906 :=
  combineSlices (auxiliaryColumnSlice contact12) 8 4 4 961504406496 877496202410 contact12ColumnsSlice8 contact12ColumnsSlice12
private theorem contact12ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact12) 16 8 = 1518436618339 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 4 4 797353211769 721083406570 contact12ColumnsSlice16 contact12ColumnsSlice20
private theorem contact12ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact12) 24 8 = 1228894799190 :=
  combineSlices (auxiliaryColumnSlice contact12) 24 4 4 648703097202 580191701988 contact12ColumnsSlice24 contact12ColumnsSlice28
private theorem contact12ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact12) 32 8 = 970313344004 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 4 4 515546530562 454766813442 contact12ColumnsSlice32 contact12ColumnsSlice36
private theorem contact12ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact12) 40 8 = 742708278604 :=
  combineSlices (auxiliaryColumnSlice contact12) 40 4 4 397862249290 344846029314 contact12ColumnsSlice40 contact12ColumnsSlice44
private theorem contact12ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact12) 48 8 = 546113557940 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 4 4 295697852178 250415705762 contact12ColumnsSlice48 contact12ColumnsSlice52
private theorem contact12ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact12) 56 8 = 380459270344 :=
  combineSlices (auxiliaryColumnSlice contact12) 56 4 4 208999307706 171459962638 contact12ColumnsSlice56 contact12ColumnsSlice60
private theorem contact12ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact12) 64 8 = 245830739124 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 4 4 137807808474 108022930650 contact12ColumnsSlice64 contact12ColumnsSlice68
private theorem contact12ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact12) 72 8 = 142154377028 :=
  combineSlices (auxiliaryColumnSlice contact12) 72 4 4 82103728010 60050649018 contact12ColumnsSlice72 contact12ColumnsSlice76
private theorem contact12ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact12) 80 8 = 69414929800 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 4 4 41875959635 27538970165 contact12ColumnsSlice80 contact12ColumnsSlice84
private theorem contact12ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact12) 88 8 = 26190280086 :=
  combineSlices (auxiliaryColumnSlice contact12) 88 4 4 16824323381 9365956705 contact12ColumnsSlice88 contact12ColumnsSlice92
private theorem contact12ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact12) 0 16 = 4029500819214 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 8 8 2190500210308 1839000608906 contact12ColumnsJoin0_8 contact12ColumnsJoin8_8
private theorem contact12ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact12) 16 16 = 2747331417529 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 8 8 1518436618339 1228894799190 contact12ColumnsJoin16_8 contact12ColumnsJoin24_8
private theorem contact12ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact12) 32 16 = 1713021622608 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 8 8 970313344004 742708278604 contact12ColumnsJoin32_8 contact12ColumnsJoin40_8
private theorem contact12ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact12) 48 16 = 926572828284 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 8 8 546113557940 380459270344 contact12ColumnsJoin48_8 contact12ColumnsJoin56_8
private theorem contact12ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact12) 64 16 = 387985116152 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 8 8 245830739124 142154377028 contact12ColumnsJoin64_8 contact12ColumnsJoin72_8
private theorem contact12ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact12) 80 16 = 95605209886 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 8 8 69414929800 26190280086 contact12ColumnsJoin80_8 contact12ColumnsJoin88_8
private theorem contact12ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact12) 0 32 = 6776832236743 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 16 16 4029500819214 2747331417529 contact12ColumnsJoin0_16 contact12ColumnsJoin16_16
private theorem contact12ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact12) 32 32 = 2639594450892 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 16 16 1713021622608 926572828284 contact12ColumnsJoin32_16 contact12ColumnsJoin48_16
private theorem contact12ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact12) 64 32 = 483590326038 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 16 16 387985116152 95605209886 contact12ColumnsJoin64_16 contact12ColumnsJoin80_16
private theorem contact12ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact12) 0 64 = 9416426687635 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 32 32 6776832236743 2639594450892 contact12ColumnsJoin0_32 contact12ColumnsJoin32_32
private theorem contact12ColumnsJoin64_34 : sliceWindow (auxiliaryColumnSlice contact12) 64 34 = 486354724020 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 32 2 483590326038 2764397982 contact12ColumnsJoin64_32 contact12ColumnsSlice96
private theorem contact12ColumnsJoin0_98 : sliceWindow (auxiliaryColumnSlice contact12) 0 98 = 9902781411655 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 64 34 9416426687635 486354724020 contact12ColumnsJoin0_64 contact12ColumnsJoin64_34
private theorem contact12OrdinaryRanks : ordinaryRankBound contact12 = 686425985 := by decide +kernel
private theorem contact12RanksSlice0 : sliceWindow (auxiliaryRankSlice contact12) 0 4 = 4274046 :=
  contactRankWindow_of_rec contact12 0 4 4274046 (by decide +kernel)
private theorem contact12RanksSlice4 : sliceWindow (auxiliaryRankSlice contact12) 4 4 = 3829294 :=
  contactRankWindow_of_rec contact12 4 4 3829294 (by decide +kernel)
private theorem contact12RanksSlice8 : sliceWindow (auxiliaryRankSlice contact12) 8 4 = 3411294 :=
  contactRankWindow_of_rec contact12 8 4 3411294 (by decide +kernel)
private theorem contact12RanksSlice12 : sliceWindow (auxiliaryRankSlice contact12) 12 4 = 3020046 :=
  contactRankWindow_of_rec contact12 12 4 3020046 (by decide +kernel)
private theorem contact12RanksSlice16 : sliceWindow (auxiliaryRankSlice contact12) 16 4 = 2655550 :=
  contactRankWindow_of_rec contact12 16 4 2655550 (by decide +kernel)
private theorem contact12RanksSlice20 : sliceWindow (auxiliaryRankSlice contact12) 20 4 = 2317806 :=
  contactRankWindow_of_rec contact12 20 4 2317806 (by decide +kernel)
private theorem contact12RanksSlice24 : sliceWindow (auxiliaryRankSlice contact12) 24 4 = 2006814 :=
  contactRankWindow_of_rec contact12 24 4 2006814 (by decide +kernel)
private theorem contact12RanksSlice28 : sliceWindow (auxiliaryRankSlice contact12) 28 4 = 1722555 :=
  contactRankWindow_of_rec contact12 28 4 1722555 (by decide +kernel)
private theorem contact12RanksSlice32 : sliceWindow (auxiliaryRankSlice contact12) 32 4 = 1464625 :=
  contactRankWindow_of_rec contact12 32 4 1464625 (by decide +kernel)
private theorem contact12RanksSlice36 : sliceWindow (auxiliaryRankSlice contact12) 36 4 = 1232154 :=
  contactRankWindow_of_rec contact12 36 4 1232154 (by decide +kernel)
private theorem contact12RanksSlice40 : sliceWindow (auxiliaryRankSlice contact12) 40 4 = 1024020 :=
  contactRankWindow_of_rec contact12 40 4 1024020 (by decide +kernel)
private theorem contact12RanksSlice44 : sliceWindow (auxiliaryRankSlice contact12) 44 4 = 839029 :=
  contactRankWindow_of_rec contact12 44 4 839029 (by decide +kernel)
private theorem contact12RanksSlice48 : sliceWindow (auxiliaryRankSlice contact12) 48 4 = 676102 :=
  contactRankWindow_of_rec contact12 48 4 676102 (by decide +kernel)
private theorem contact12RanksSlice52 : sliceWindow (auxiliaryRankSlice contact12) 52 4 = 533984 :=
  contactRankWindow_of_rec contact12 52 4 533984 (by decide +kernel)
private theorem contact12RanksSlice56 : sliceWindow (auxiliaryRankSlice contact12) 56 4 = 411481 :=
  contactRankWindow_of_rec contact12 56 4 411481 (by decide +kernel)
private theorem contact12RanksSlice60 : sliceWindow (auxiliaryRankSlice contact12) 60 4 = 307602 :=
  contactRankWindow_of_rec contact12 60 4 307602 (by decide +kernel)
private theorem contact12RanksSlice64 : sliceWindow (auxiliaryRankSlice contact12) 64 4 = 221004 :=
  contactRankWindow_of_rec contact12 64 4 221004 (by decide +kernel)
private theorem contact12RanksSlice68 : sliceWindow (auxiliaryRankSlice contact12) 68 4 = 150493 :=
  contactRankWindow_of_rec contact12 68 4 150493 (by decide +kernel)
private theorem contact12RanksSlice72 : sliceWindow (auxiliaryRankSlice contact12) 72 4 = 95166 :=
  contactRankWindow_of_rec contact12 72 4 95166 (by decide +kernel)
private theorem contact12RanksSlice76 : sliceWindow (auxiliaryRankSlice contact12) 76 4 = 53592 :=
  contactRankWindow_of_rec contact12 76 4 53592 (by decide +kernel)
private theorem contact12RanksSlice80 : sliceWindow (auxiliaryRankSlice contact12) 80 4 = 24577 :=
  contactRankWindow_of_rec contact12 80 4 24577 (by decide +kernel)
private theorem contact12RanksSlice84 : sliceWindow (auxiliaryRankSlice contact12) 84 4 = 7330 :=
  contactRankWindow_of_rec contact12 84 4 7330 (by decide +kernel)
private theorem contact12RanksSlice88 : sliceWindow (auxiliaryRankSlice contact12) 88 4 = 403 :=
  contactRankWindow_of_rec contact12 88 4 403 (by decide +kernel)
private theorem contact12RanksSlice92 : sliceWindow (auxiliaryRankSlice contact12) 92 6 = 0 :=
  contactRankWindow_of_rec contact12 92 6 0 (by decide +kernel)
private theorem contact12RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact12) 0 8 = 8103340 :=
  combineSlices (auxiliaryRankSlice contact12) 0 4 4 4274046 3829294 contact12RanksSlice0 contact12RanksSlice4
private theorem contact12RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact12) 8 8 = 6431340 :=
  combineSlices (auxiliaryRankSlice contact12) 8 4 4 3411294 3020046 contact12RanksSlice8 contact12RanksSlice12
private theorem contact12RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact12) 16 8 = 4973356 :=
  combineSlices (auxiliaryRankSlice contact12) 16 4 4 2655550 2317806 contact12RanksSlice16 contact12RanksSlice20
private theorem contact12RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact12) 24 8 = 3729369 :=
  combineSlices (auxiliaryRankSlice contact12) 24 4 4 2006814 1722555 contact12RanksSlice24 contact12RanksSlice28
private theorem contact12RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact12) 32 8 = 2696779 :=
  combineSlices (auxiliaryRankSlice contact12) 32 4 4 1464625 1232154 contact12RanksSlice32 contact12RanksSlice36
private theorem contact12RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact12) 40 8 = 1863049 :=
  combineSlices (auxiliaryRankSlice contact12) 40 4 4 1024020 839029 contact12RanksSlice40 contact12RanksSlice44
private theorem contact12RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact12) 48 8 = 1210086 :=
  combineSlices (auxiliaryRankSlice contact12) 48 4 4 676102 533984 contact12RanksSlice48 contact12RanksSlice52
private theorem contact12RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact12) 56 8 = 719083 :=
  combineSlices (auxiliaryRankSlice contact12) 56 4 4 411481 307602 contact12RanksSlice56 contact12RanksSlice60
private theorem contact12RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact12) 64 8 = 371497 :=
  combineSlices (auxiliaryRankSlice contact12) 64 4 4 221004 150493 contact12RanksSlice64 contact12RanksSlice68
private theorem contact12RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact12) 72 8 = 148758 :=
  combineSlices (auxiliaryRankSlice contact12) 72 4 4 95166 53592 contact12RanksSlice72 contact12RanksSlice76
private theorem contact12RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact12) 80 8 = 31907 :=
  combineSlices (auxiliaryRankSlice contact12) 80 4 4 24577 7330 contact12RanksSlice80 contact12RanksSlice84
private theorem contact12RanksJoin88_10 : sliceWindow (auxiliaryRankSlice contact12) 88 10 = 403 :=
  combineSlices (auxiliaryRankSlice contact12) 88 4 6 403 0 contact12RanksSlice88 contact12RanksSlice92
private theorem contact12RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact12) 0 16 = 14534680 :=
  combineSlices (auxiliaryRankSlice contact12) 0 8 8 8103340 6431340 contact12RanksJoin0_8 contact12RanksJoin8_8
private theorem contact12RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact12) 16 16 = 8702725 :=
  combineSlices (auxiliaryRankSlice contact12) 16 8 8 4973356 3729369 contact12RanksJoin16_8 contact12RanksJoin24_8
private theorem contact12RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact12) 32 16 = 4559828 :=
  combineSlices (auxiliaryRankSlice contact12) 32 8 8 2696779 1863049 contact12RanksJoin32_8 contact12RanksJoin40_8
private theorem contact12RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact12) 48 16 = 1929169 :=
  combineSlices (auxiliaryRankSlice contact12) 48 8 8 1210086 719083 contact12RanksJoin48_8 contact12RanksJoin56_8
private theorem contact12RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact12) 64 16 = 520255 :=
  combineSlices (auxiliaryRankSlice contact12) 64 8 8 371497 148758 contact12RanksJoin64_8 contact12RanksJoin72_8
private theorem contact12RanksJoin80_18 : sliceWindow (auxiliaryRankSlice contact12) 80 18 = 32310 :=
  combineSlices (auxiliaryRankSlice contact12) 80 8 10 31907 403 contact12RanksJoin80_8 contact12RanksJoin88_10
private theorem contact12RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact12) 0 32 = 23237405 :=
  combineSlices (auxiliaryRankSlice contact12) 0 16 16 14534680 8702725 contact12RanksJoin0_16 contact12RanksJoin16_16
private theorem contact12RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact12) 32 32 = 6488997 :=
  combineSlices (auxiliaryRankSlice contact12) 32 16 16 4559828 1929169 contact12RanksJoin32_16 contact12RanksJoin48_16
private theorem contact12RanksJoin64_34 : sliceWindow (auxiliaryRankSlice contact12) 64 34 = 552565 :=
  combineSlices (auxiliaryRankSlice contact12) 64 16 18 520255 32310 contact12RanksJoin64_16 contact12RanksJoin80_18
private theorem contact12RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact12) 0 64 = 29726402 :=
  combineSlices (auxiliaryRankSlice contact12) 0 32 32 23237405 6488997 contact12RanksJoin0_32 contact12RanksJoin32_32
private theorem contact12RanksJoin0_98 : sliceWindow (auxiliaryRankSlice contact12) 0 98 = 30278967 :=
  combineSlices (auxiliaryRankSlice contact12) 0 64 34 29726402 552565 contact12RanksJoin0_64 contact12RanksJoin64_34
theorem contact12_margin : sourceMargin contact12 :=
  margin_of_checked_counts contact12 98 177977180559548 9902781411655 686425985 30278967 rfl contact12OrdinaryColumns contact12ColumnsJoin0_98 contact12OrdinaryRanks contact12RanksJoin0_98 (by decide +kernel)

private theorem contact14OrdinaryColumns : ordinaryColumnCount contact14 = 192494464819153 := by decide +kernel
private theorem contact14ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact14) 0 4 = 950160194578 :=
  contactColumnsWindow_fast contact14 0 4 950160194578 (by decide +kernel)
private theorem contact14ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact14) 4 4 = 872771801888 :=
  contactColumnsWindow_fast contact14 4 4 872771801888 (by decide +kernel)
private theorem contact14ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact14) 8 4 = 798703422846 :=
  contactColumnsWindow_fast contact14 8 4 798703422846 (by decide +kernel)
private theorem contact14ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact14) 12 4 = 727940143497 :=
  contactColumnsWindow_fast contact14 12 4 727940143497 (by decide +kernel)
private theorem contact14ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact14) 16 4 = 660479330640 :=
  contactColumnsWindow_fast contact14 16 4 660479330640 (by decide +kernel)
private theorem contact14ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact14) 20 4 = 596319529218 :=
  contactColumnsWindow_fast contact14 20 4 596319529218 (by decide +kernel)
private theorem contact14ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact14) 24 4 = 535465476704 :=
  contactColumnsWindow_fast contact14 24 4 535465476704 (by decide +kernel)
private theorem contact14ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact14) 28 4 = 477932872045 :=
  contactColumnsWindow_fast contact14 28 4 477932872045 (by decide +kernel)
private theorem contact14ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact14) 32 4 = 423706923165 :=
  contactColumnsWindow_fast contact14 32 4 423706923165 (by decide +kernel)
private theorem contact14ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact14) 36 4 = 372783524286 :=
  contactColumnsWindow_fast contact14 36 4 372783524286 (by decide +kernel)
private theorem contact14ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact14) 40 4 = 325161233133 :=
  contactColumnsWindow_fast contact14 40 4 325161233133 (by decide +kernel)
private theorem contact14ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact14) 44 4 = 280845762434 :=
  contactColumnsWindow_fast contact14 44 4 280845762434 (by decide +kernel)
private theorem contact14ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact14) 48 4 = 239851935078 :=
  contactColumnsWindow_fast contact14 48 4 239851935078 (by decide +kernel)
private theorem contact14ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact14) 52 4 = 202163559717 :=
  contactColumnsWindow_fast contact14 52 4 202163559717 (by decide +kernel)
private theorem contact14ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact14) 56 4 = 167777498784 :=
  contactColumnsWindow_fast contact14 56 4 167777498784 (by decide +kernel)
private theorem contact14ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact14) 60 4 = 136692717900 :=
  contactColumnsWindow_fast contact14 60 4 136692717900 (by decide +kernel)
private theorem contact14ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact14) 64 4 = 108916141825 :=
  contactColumnsWindow_fast contact14 64 4 108916141825 (by decide +kernel)
private theorem contact14ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact14) 68 4 = 84460862472 :=
  contactColumnsWindow_fast contact14 68 4 84460862472 (by decide +kernel)
private theorem contact14ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact14) 72 4 = 63309982566 :=
  contactColumnsWindow_fast contact14 72 4 63309982566 (by decide +kernel)
private theorem contact14ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact14) 76 4 = 45461254134 :=
  contactColumnsWindow_fast contact14 76 4 45461254134 (by decide +kernel)
private theorem contact14ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact14) 80 4 = 30913222187 :=
  contactColumnsWindow_fast contact14 80 4 30913222187 (by decide +kernel)
private theorem contact14ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact14) 84 4 = 19634082974 :=
  contactColumnsWindow_fast contact14 84 4 19634082974 (by decide +kernel)
private theorem contact14ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact14) 88 4 = 11446406425 :=
  contactColumnsWindow_fast contact14 88 4 11446406425 (by decide +kernel)
private theorem contact14ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact14) 92 4 = 5976587635 :=
  contactColumnsWindow_fast contact14 92 4 5976587635 (by decide +kernel)
private theorem contact14ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact14) 0 8 = 1822931996466 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 4 4 950160194578 872771801888 contact14ColumnsSlice0 contact14ColumnsSlice4
private theorem contact14ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact14) 8 8 = 1526643566343 :=
  combineSlices (auxiliaryColumnSlice contact14) 8 4 4 798703422846 727940143497 contact14ColumnsSlice8 contact14ColumnsSlice12
private theorem contact14ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact14) 16 8 = 1256798859858 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 4 4 660479330640 596319529218 contact14ColumnsSlice16 contact14ColumnsSlice20
private theorem contact14ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact14) 24 8 = 1013398348749 :=
  combineSlices (auxiliaryColumnSlice contact14) 24 4 4 535465476704 477932872045 contact14ColumnsSlice24 contact14ColumnsSlice28
private theorem contact14ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact14) 32 8 = 796490447451 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 4 4 423706923165 372783524286 contact14ColumnsSlice32 contact14ColumnsSlice36
private theorem contact14ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact14) 40 8 = 606006995567 :=
  combineSlices (auxiliaryColumnSlice contact14) 40 4 4 325161233133 280845762434 contact14ColumnsSlice40 contact14ColumnsSlice44
private theorem contact14ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact14) 48 8 = 442015494795 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 4 4 239851935078 202163559717 contact14ColumnsSlice48 contact14ColumnsSlice52
private theorem contact14ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact14) 56 8 = 304470216684 :=
  combineSlices (auxiliaryColumnSlice contact14) 56 4 4 167777498784 136692717900 contact14ColumnsSlice56 contact14ColumnsSlice60
private theorem contact14ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact14) 64 8 = 193377004297 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 4 4 108916141825 84460862472 contact14ColumnsSlice64 contact14ColumnsSlice68
private theorem contact14ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact14) 72 8 = 108771236700 :=
  combineSlices (auxiliaryColumnSlice contact14) 72 4 4 63309982566 45461254134 contact14ColumnsSlice72 contact14ColumnsSlice76
private theorem contact14ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact14) 80 8 = 50547305161 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 4 4 30913222187 19634082974 contact14ColumnsSlice80 contact14ColumnsSlice84
private theorem contact14ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact14) 88 8 = 17422994060 :=
  combineSlices (auxiliaryColumnSlice contact14) 88 4 4 11446406425 5976587635 contact14ColumnsSlice88 contact14ColumnsSlice92
private theorem contact14ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact14) 0 16 = 3349575562809 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 8 8 1822931996466 1526643566343 contact14ColumnsJoin0_8 contact14ColumnsJoin8_8
private theorem contact14ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact14) 16 16 = 2270197208607 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 8 8 1256798859858 1013398348749 contact14ColumnsJoin16_8 contact14ColumnsJoin24_8
private theorem contact14ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact14) 32 16 = 1402497443018 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 8 8 796490447451 606006995567 contact14ColumnsJoin32_8 contact14ColumnsJoin40_8
private theorem contact14ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact14) 48 16 = 746485711479 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 8 8 442015494795 304470216684 contact14ColumnsJoin48_8 contact14ColumnsJoin56_8
private theorem contact14ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact14) 64 16 = 302148240997 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 8 8 193377004297 108771236700 contact14ColumnsJoin64_8 contact14ColumnsJoin72_8
private theorem contact14ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact14) 80 16 = 67970299221 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 8 8 50547305161 17422994060 contact14ColumnsJoin80_8 contact14ColumnsJoin88_8
private theorem contact14ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact14) 0 32 = 5619772771416 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 16 16 3349575562809 2270197208607 contact14ColumnsJoin0_16 contact14ColumnsJoin16_16
private theorem contact14ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact14) 32 32 = 2148983154497 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 16 16 1402497443018 746485711479 contact14ColumnsJoin32_16 contact14ColumnsJoin48_16
private theorem contact14ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact14) 64 32 = 370118540218 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 16 16 302148240997 67970299221 contact14ColumnsJoin64_16 contact14ColumnsJoin80_16
private theorem contact14ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact14) 0 64 = 7768755925913 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 32 32 5619772771416 2148983154497 contact14ColumnsJoin0_32 contact14ColumnsJoin32_32
private theorem contact14ColumnsJoin0_96 : sliceWindow (auxiliaryColumnSlice contact14) 0 96 = 8138874466131 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 64 32 7768755925913 370118540218 contact14ColumnsJoin0_64 contact14ColumnsJoin64_32
private theorem contact14OrdinaryRanks : ordinaryRankBound contact14 = 740657879 := by decide +kernel
private theorem contact14RanksSlice0 : sliceWindow (auxiliaryRankSlice contact14) 0 4 = 3559590 :=
  contactRankWindow_of_rec contact14 0 4 3559590 (by decide +kernel)
private theorem contact14RanksSlice4 : sliceWindow (auxiliaryRankSlice contact14) 4 4 = 3182598 :=
  contactRankWindow_of_rec contact14 4 4 3182598 (by decide +kernel)
private theorem contact14RanksSlice8 : sliceWindow (auxiliaryRankSlice contact14) 8 4 = 2828454 :=
  contactRankWindow_of_rec contact14 8 4 2828454 (by decide +kernel)
private theorem contact14RanksSlice12 : sliceWindow (auxiliaryRankSlice contact14) 12 4 = 2497158 :=
  contactRankWindow_of_rec contact14 12 4 2497158 (by decide +kernel)
private theorem contact14RanksSlice16 : sliceWindow (auxiliaryRankSlice contact14) 16 4 = 2188710 :=
  contactRankWindow_of_rec contact14 16 4 2188710 (by decide +kernel)
private theorem contact14RanksSlice20 : sliceWindow (auxiliaryRankSlice contact14) 20 4 = 1903110 :=
  contactRankWindow_of_rec contact14 20 4 1903110 (by decide +kernel)
private theorem contact14RanksSlice24 : sliceWindow (auxiliaryRankSlice contact14) 24 4 = 1640358 :=
  contactRankWindow_of_rec contact14 24 4 1640358 (by decide +kernel)
private theorem contact14RanksSlice28 : sliceWindow (auxiliaryRankSlice contact14) 28 4 = 1400454 :=
  contactRankWindow_of_rec contact14 28 4 1400454 (by decide +kernel)
private theorem contact14RanksSlice32 : sliceWindow (auxiliaryRankSlice contact14) 32 4 = 1183278 :=
  contactRankWindow_of_rec contact14 32 4 1183278 (by decide +kernel)
private theorem contact14RanksSlice36 : sliceWindow (auxiliaryRankSlice contact14) 36 4 = 988204 :=
  contactRankWindow_of_rec contact14 36 4 988204 (by decide +kernel)
private theorem contact14RanksSlice40 : sliceWindow (auxiliaryRankSlice contact14) 40 4 = 814433 :=
  contactRankWindow_of_rec contact14 40 4 814433 (by decide +kernel)
private theorem contact14RanksSlice44 : sliceWindow (auxiliaryRankSlice contact14) 44 4 = 660925 :=
  contactRankWindow_of_rec contact14 44 4 660925 (by decide +kernel)
private theorem contact14RanksSlice48 : sliceWindow (auxiliaryRankSlice contact14) 48 4 = 526560 :=
  contactRankWindow_of_rec contact14 48 4 526560 (by decide +kernel)
private theorem contact14RanksSlice52 : sliceWindow (auxiliaryRankSlice contact14) 52 4 = 410353 :=
  contactRankWindow_of_rec contact14 52 4 410353 (by decide +kernel)
private theorem contact14RanksSlice56 : sliceWindow (auxiliaryRankSlice contact14) 56 4 = 311137 :=
  contactRankWindow_of_rec contact14 56 4 311137 (by decide +kernel)
private theorem contact14RanksSlice60 : sliceWindow (auxiliaryRankSlice contact14) 60 4 = 227796 :=
  contactRankWindow_of_rec contact14 60 4 227796 (by decide +kernel)
private theorem contact14RanksSlice64 : sliceWindow (auxiliaryRankSlice contact14) 64 4 = 159425 :=
  contactRankWindow_of_rec contact14 64 4 159425 (by decide +kernel)
private theorem contact14RanksSlice68 : sliceWindow (auxiliaryRankSlice contact14) 68 4 = 104773 :=
  contactRankWindow_of_rec contact14 68 4 104773 (by decide +kernel)
private theorem contact14RanksSlice72 : sliceWindow (auxiliaryRankSlice contact14) 72 4 = 62728 :=
  contactRankWindow_of_rec contact14 72 4 62728 (by decide +kernel)
private theorem contact14RanksSlice76 : sliceWindow (auxiliaryRankSlice contact14) 76 4 = 32465 :=
  contactRankWindow_of_rec contact14 76 4 32465 (by decide +kernel)
private theorem contact14RanksSlice80 : sliceWindow (auxiliaryRankSlice contact14) 80 4 = 12649 :=
  contactRankWindow_of_rec contact14 80 4 12649 (by decide +kernel)
private theorem contact14RanksSlice84 : sliceWindow (auxiliaryRankSlice contact14) 84 4 = 2189 :=
  contactRankWindow_of_rec contact14 84 4 2189 (by decide +kernel)
private theorem contact14RanksSlice88 : sliceWindow (auxiliaryRankSlice contact14) 88 8 = 0 :=
  contactRankWindow_of_rec contact14 88 8 0 (by decide +kernel)
private theorem contact14RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact14) 0 8 = 6742188 :=
  combineSlices (auxiliaryRankSlice contact14) 0 4 4 3559590 3182598 contact14RanksSlice0 contact14RanksSlice4
private theorem contact14RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact14) 8 8 = 5325612 :=
  combineSlices (auxiliaryRankSlice contact14) 8 4 4 2828454 2497158 contact14RanksSlice8 contact14RanksSlice12
private theorem contact14RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact14) 16 8 = 4091820 :=
  combineSlices (auxiliaryRankSlice contact14) 16 4 4 2188710 1903110 contact14RanksSlice16 contact14RanksSlice20
private theorem contact14RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact14) 24 8 = 3040812 :=
  combineSlices (auxiliaryRankSlice contact14) 24 4 4 1640358 1400454 contact14RanksSlice24 contact14RanksSlice28
private theorem contact14RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact14) 32 8 = 2171482 :=
  combineSlices (auxiliaryRankSlice contact14) 32 4 4 1183278 988204 contact14RanksSlice32 contact14RanksSlice36
private theorem contact14RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact14) 40 8 = 1475358 :=
  combineSlices (auxiliaryRankSlice contact14) 40 4 4 814433 660925 contact14RanksSlice40 contact14RanksSlice44
private theorem contact14RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact14) 48 8 = 936913 :=
  combineSlices (auxiliaryRankSlice contact14) 48 4 4 526560 410353 contact14RanksSlice48 contact14RanksSlice52
private theorem contact14RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact14) 56 8 = 538933 :=
  combineSlices (auxiliaryRankSlice contact14) 56 4 4 311137 227796 contact14RanksSlice56 contact14RanksSlice60
private theorem contact14RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact14) 64 8 = 264198 :=
  combineSlices (auxiliaryRankSlice contact14) 64 4 4 159425 104773 contact14RanksSlice64 contact14RanksSlice68
private theorem contact14RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact14) 72 8 = 95193 :=
  combineSlices (auxiliaryRankSlice contact14) 72 4 4 62728 32465 contact14RanksSlice72 contact14RanksSlice76
private theorem contact14RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact14) 80 8 = 14838 :=
  combineSlices (auxiliaryRankSlice contact14) 80 4 4 12649 2189 contact14RanksSlice80 contact14RanksSlice84
private theorem contact14RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact14) 0 16 = 12067800 :=
  combineSlices (auxiliaryRankSlice contact14) 0 8 8 6742188 5325612 contact14RanksJoin0_8 contact14RanksJoin8_8
private theorem contact14RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact14) 16 16 = 7132632 :=
  combineSlices (auxiliaryRankSlice contact14) 16 8 8 4091820 3040812 contact14RanksJoin16_8 contact14RanksJoin24_8
private theorem contact14RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact14) 32 16 = 3646840 :=
  combineSlices (auxiliaryRankSlice contact14) 32 8 8 2171482 1475358 contact14RanksJoin32_8 contact14RanksJoin40_8
private theorem contact14RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact14) 48 16 = 1475846 :=
  combineSlices (auxiliaryRankSlice contact14) 48 8 8 936913 538933 contact14RanksJoin48_8 contact14RanksJoin56_8
private theorem contact14RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact14) 64 16 = 359391 :=
  combineSlices (auxiliaryRankSlice contact14) 64 8 8 264198 95193 contact14RanksJoin64_8 contact14RanksJoin72_8
private theorem contact14RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact14) 80 16 = 14838 :=
  combineSlices (auxiliaryRankSlice contact14) 80 8 8 14838 0 contact14RanksJoin80_8 contact14RanksSlice88
private theorem contact14RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact14) 0 32 = 19200432 :=
  combineSlices (auxiliaryRankSlice contact14) 0 16 16 12067800 7132632 contact14RanksJoin0_16 contact14RanksJoin16_16
private theorem contact14RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact14) 32 32 = 5122686 :=
  combineSlices (auxiliaryRankSlice contact14) 32 16 16 3646840 1475846 contact14RanksJoin32_16 contact14RanksJoin48_16
private theorem contact14RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact14) 64 32 = 374229 :=
  combineSlices (auxiliaryRankSlice contact14) 64 16 16 359391 14838 contact14RanksJoin64_16 contact14RanksJoin80_16
private theorem contact14RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact14) 0 64 = 24323118 :=
  combineSlices (auxiliaryRankSlice contact14) 0 32 32 19200432 5122686 contact14RanksJoin0_32 contact14RanksJoin32_32
private theorem contact14RanksJoin0_96 : sliceWindow (auxiliaryRankSlice contact14) 0 96 = 24697347 :=
  combineSlices (auxiliaryRankSlice contact14) 0 64 32 24323118 374229 contact14RanksJoin0_64 contact14RanksJoin64_32
theorem contact14_margin : sourceMargin contact14 :=
  margin_of_checked_counts contact14 96 192494464819153 8138874466131 740657879 24697347 rfl contact14OrdinaryColumns contact14ColumnsJoin0_96 contact14OrdinaryRanks contact14RanksJoin0_96 (by decide +kernel)

private theorem contact16OrdinaryColumns : ordinaryColumnCount contact16 = 172282802965419 := by decide +kernel
private theorem contact16ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact16) 0 4 = 1091452010389 :=
  contactColumnsWindow_fast contact16 0 4 1091452010389 (by decide +kernel)
private theorem contact16ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact16) 4 4 = 1004096731304 :=
  contactColumnsWindow_fast contact16 4 4 1004096731304 (by decide +kernel)
private theorem contact16ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact16) 8 4 = 920405469029 :=
  contactColumnsWindow_fast contact16 8 4 920405469029 (by decide +kernel)
private theorem contact16ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact16) 12 4 = 840377181654 :=
  contactColumnsWindow_fast contact16 12 4 840377181654 (by decide +kernel)
private theorem contact16ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact16) 16 4 = 764010716170 :=
  contactColumnsWindow_fast contact16 16 4 764010716170 (by decide +kernel)
private theorem contact16ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact16) 20 4 = 691313585928 :=
  contactColumnsWindow_fast contact16 20 4 691313585928 (by decide +kernel)
private theorem contact16ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact16) 24 4 = 622301061584 :=
  contactColumnsWindow_fast contact16 24 4 622301061584 (by decide +kernel)
private theorem contact16ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact16) 28 4 = 556953900026 :=
  contactColumnsWindow_fast contact16 28 4 556953900026 (by decide +kernel)
private theorem contact16ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact16) 32 4 = 495269540538 :=
  contactColumnsWindow_fast contact16 32 4 495269540538 (by decide +kernel)
private theorem contact16ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact16) 36 4 = 437247237612 :=
  contactColumnsWindow_fast contact16 36 4 437247237612 (by decide +kernel)
private theorem contact16ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact16) 40 4 = 382896104163 :=
  contactColumnsWindow_fast contact16 40 4 382896104163 (by decide +kernel)
private theorem contact16ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact16) 44 4 = 332228510120 :=
  contactColumnsWindow_fast contact16 44 4 332228510120 (by decide +kernel)
private theorem contact16ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact16) 48 4 = 285225456734 :=
  contactColumnsWindow_fast contact16 48 4 285225456734 (by decide +kernel)
private theorem contact16ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact16) 52 4 = 241885017678 :=
  contactColumnsWindow_fast contact16 52 4 241885017678 (by decide +kernel)
private theorem contact16ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact16) 56 4 = 202206921636 :=
  contactColumnsWindow_fast contact16 56 4 202206921636 (by decide +kernel)
private theorem contact16ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact16) 60 4 = 166201763664 :=
  contactColumnsWindow_fast contact16 60 4 166201763664 (by decide +kernel)
private theorem contact16ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact16) 64 4 = 133879076912 :=
  contactColumnsWindow_fast contact16 64 4 133879076912 (by decide +kernel)
private theorem contact16ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact16) 68 4 = 105220210658 :=
  contactColumnsWindow_fast contact16 68 4 105220210658 (by decide +kernel)
private theorem contact16ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact16) 72 4 = 80223613074 :=
  contactColumnsWindow_fast contact16 72 4 80223613074 (by decide +kernel)
private theorem contact16ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact16) 76 4 = 58889723916 :=
  contactColumnsWindow_fast contact16 76 4 58889723916 (by decide +kernel)
private theorem contact16ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact16) 80 4 = 41230882985 :=
  contactColumnsWindow_fast contact16 80 4 41230882985 (by decide +kernel)
private theorem contact16ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact16) 84 4 = 27226675827 :=
  contactColumnsWindow_fast contact16 84 4 27226675827 (by decide +kernel)
private theorem contact16ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact16) 88 4 = 16704167291 :=
  contactColumnsWindow_fast contact16 88 4 16704167291 (by decide +kernel)
private theorem contact16ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact16) 92 4 = 9336231855 :=
  contactColumnsWindow_fast contact16 92 4 9336231855 (by decide +kernel)
private theorem contact16ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact16) 96 2 = 2762240972 :=
  contactColumnsWindow_fast contact16 96 2 2762240972 (by decide +kernel)
private theorem contact16ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact16) 0 8 = 2095548741693 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 4 4 1091452010389 1004096731304 contact16ColumnsSlice0 contact16ColumnsSlice4
private theorem contact16ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact16) 8 8 = 1760782650683 :=
  combineSlices (auxiliaryColumnSlice contact16) 8 4 4 920405469029 840377181654 contact16ColumnsSlice8 contact16ColumnsSlice12
private theorem contact16ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact16) 16 8 = 1455324302098 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 4 4 764010716170 691313585928 contact16ColumnsSlice16 contact16ColumnsSlice20
private theorem contact16ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact16) 24 8 = 1179254961610 :=
  combineSlices (auxiliaryColumnSlice contact16) 24 4 4 622301061584 556953900026 contact16ColumnsSlice24 contact16ColumnsSlice28
private theorem contact16ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact16) 32 8 = 932516778150 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 4 4 495269540538 437247237612 contact16ColumnsSlice32 contact16ColumnsSlice36
private theorem contact16ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact16) 40 8 = 715124614283 :=
  combineSlices (auxiliaryColumnSlice contact16) 40 4 4 382896104163 332228510120 contact16ColumnsSlice40 contact16ColumnsSlice44
private theorem contact16ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact16) 48 8 = 527110474412 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 4 4 285225456734 241885017678 contact16ColumnsSlice48 contact16ColumnsSlice52
private theorem contact16ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact16) 56 8 = 368408685300 :=
  combineSlices (auxiliaryColumnSlice contact16) 56 4 4 202206921636 166201763664 contact16ColumnsSlice56 contact16ColumnsSlice60
private theorem contact16ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact16) 64 8 = 239099287570 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 4 4 133879076912 105220210658 contact16ColumnsSlice64 contact16ColumnsSlice68
private theorem contact16ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact16) 72 8 = 139113336990 :=
  combineSlices (auxiliaryColumnSlice contact16) 72 4 4 80223613074 58889723916 contact16ColumnsSlice72 contact16ColumnsSlice76
private theorem contact16ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact16) 80 8 = 68457558812 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 4 4 41230882985 27226675827 contact16ColumnsSlice80 contact16ColumnsSlice84
private theorem contact16ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact16) 88 8 = 26040399146 :=
  combineSlices (auxiliaryColumnSlice contact16) 88 4 4 16704167291 9336231855 contact16ColumnsSlice88 contact16ColumnsSlice92
private theorem contact16ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact16) 0 16 = 3856331392376 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 8 8 2095548741693 1760782650683 contact16ColumnsJoin0_8 contact16ColumnsJoin8_8
private theorem contact16ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact16) 16 16 = 2634579263708 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 8 8 1455324302098 1179254961610 contact16ColumnsJoin16_8 contact16ColumnsJoin24_8
private theorem contact16ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact16) 32 16 = 1647641392433 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 8 8 932516778150 715124614283 contact16ColumnsJoin32_8 contact16ColumnsJoin40_8
private theorem contact16ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact16) 48 16 = 895519159712 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 8 8 527110474412 368408685300 contact16ColumnsJoin48_8 contact16ColumnsJoin56_8
private theorem contact16ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact16) 64 16 = 378212624560 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 8 8 239099287570 139113336990 contact16ColumnsJoin64_8 contact16ColumnsJoin72_8
private theorem contact16ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact16) 80 16 = 94497957958 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 8 8 68457558812 26040399146 contact16ColumnsJoin80_8 contact16ColumnsJoin88_8
private theorem contact16ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact16) 0 32 = 6490910656084 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 16 16 3856331392376 2634579263708 contact16ColumnsJoin0_16 contact16ColumnsJoin16_16
private theorem contact16ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact16) 32 32 = 2543160552145 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 16 16 1647641392433 895519159712 contact16ColumnsJoin32_16 contact16ColumnsJoin48_16
private theorem contact16ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact16) 64 32 = 472710582518 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 16 16 378212624560 94497957958 contact16ColumnsJoin64_16 contact16ColumnsJoin80_16
private theorem contact16ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact16) 0 64 = 9034071208229 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 32 32 6490910656084 2543160552145 contact16ColumnsJoin0_32 contact16ColumnsJoin32_32
private theorem contact16ColumnsJoin64_34 : sliceWindow (auxiliaryColumnSlice contact16) 64 34 = 475472823490 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 32 2 472710582518 2762240972 contact16ColumnsJoin64_32 contact16ColumnsSlice96
private theorem contact16ColumnsJoin0_98 : sliceWindow (auxiliaryColumnSlice contact16) 0 98 = 9509544031719 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 64 34 9034071208229 475472823490 contact16ColumnsJoin0_64 contact16ColumnsJoin64_34
private theorem contact16OrdinaryRanks : ordinaryRankBound contact16 = 664521603 := by decide +kernel
private theorem contact16RanksSlice0 : sliceWindow (auxiliaryRankSlice contact16) 0 4 = 4087788 :=
  contactRankWindow_of_rec contact16 0 4 4087788 (by decide +kernel)
private theorem contact16RanksSlice4 : sliceWindow (auxiliaryRankSlice contact16) 4 4 = 3663276 :=
  contactRankWindow_of_rec contact16 4 4 3663276 (by decide +kernel)
private theorem contact16RanksSlice8 : sliceWindow (auxiliaryRankSlice contact16) 8 4 = 3264108 :=
  contactRankWindow_of_rec contact16 8 4 3264108 (by decide +kernel)
private theorem contact16RanksSlice12 : sliceWindow (auxiliaryRankSlice contact16) 12 4 = 2890284 :=
  contactRankWindow_of_rec contact16 12 4 2890284 (by decide +kernel)
private theorem contact16RanksSlice16 : sliceWindow (auxiliaryRankSlice contact16) 16 4 = 2541804 :=
  contactRankWindow_of_rec contact16 16 4 2541804 (by decide +kernel)
private theorem contact16RanksSlice20 : sliceWindow (auxiliaryRankSlice contact16) 20 4 = 2218668 :=
  contactRankWindow_of_rec contact16 20 4 2218668 (by decide +kernel)
private theorem contact16RanksSlice24 : sliceWindow (auxiliaryRankSlice contact16) 24 4 = 1920876 :=
  contactRankWindow_of_rec contact16 24 4 1920876 (by decide +kernel)
private theorem contact16RanksSlice28 : sliceWindow (auxiliaryRankSlice contact16) 28 4 = 1648428 :=
  contactRankWindow_of_rec contact16 28 4 1648428 (by decide +kernel)
private theorem contact16RanksSlice32 : sliceWindow (auxiliaryRankSlice contact16) 32 4 = 1401070 :=
  contactRankWindow_of_rec contact16 32 4 1401070 (by decide +kernel)
private theorem contact16RanksSlice36 : sliceWindow (auxiliaryRankSlice contact16) 36 4 = 1178078 :=
  contactRankWindow_of_rec contact16 36 4 1178078 (by decide +kernel)
private theorem contact16RanksSlice40 : sliceWindow (auxiliaryRankSlice contact16) 40 4 = 978542 :=
  contactRankWindow_of_rec contact16 40 4 978542 (by decide +kernel)
private theorem contact16RanksSlice44 : sliceWindow (auxiliaryRankSlice contact16) 44 4 = 801304 :=
  contactRankWindow_of_rec contact16 44 4 801304 (by decide +kernel)
private theorem contact16RanksSlice48 : sliceWindow (auxiliaryRankSlice contact16) 48 4 = 645306 :=
  contactRankWindow_of_rec contact16 48 4 645306 (by decide +kernel)
private theorem contact16RanksSlice52 : sliceWindow (auxiliaryRankSlice contact16) 52 4 = 509342 :=
  contactRankWindow_of_rec contact16 52 4 509342 (by decide +kernel)
private theorem contact16RanksSlice56 : sliceWindow (auxiliaryRankSlice contact16) 56 4 = 392236 :=
  contactRankWindow_of_rec contact16 56 4 392236 (by decide +kernel)
private theorem contact16RanksSlice60 : sliceWindow (auxiliaryRankSlice contact16) 60 4 = 293014 :=
  contactRankWindow_of_rec contact16 60 4 293014 (by decide +kernel)
private theorem contact16RanksSlice64 : sliceWindow (auxiliaryRankSlice contact16) 64 4 = 210382 :=
  contactRankWindow_of_rec contact16 64 4 210382 (by decide +kernel)
private theorem contact16RanksSlice68 : sliceWindow (auxiliaryRankSlice contact16) 68 4 = 143168 :=
  contactRankWindow_of_rec contact16 68 4 143168 (by decide +kernel)
private theorem contact16RanksSlice72 : sliceWindow (auxiliaryRankSlice contact16) 72 4 = 90482 :=
  contactRankWindow_of_rec contact16 72 4 90482 (by decide +kernel)
private theorem contact16RanksSlice76 : sliceWindow (auxiliaryRankSlice contact16) 76 4 = 50942 :=
  contactRankWindow_of_rec contact16 76 4 50942 (by decide +kernel)
private theorem contact16RanksSlice80 : sliceWindow (auxiliaryRankSlice contact16) 80 4 = 23380 :=
  contactRankWindow_of_rec contact16 80 4 23380 (by decide +kernel)
private theorem contact16RanksSlice84 : sliceWindow (auxiliaryRankSlice contact16) 84 4 = 6997 :=
  contactRankWindow_of_rec contact16 84 4 6997 (by decide +kernel)
private theorem contact16RanksSlice88 : sliceWindow (auxiliaryRankSlice contact16) 88 4 = 386 :=
  contactRankWindow_of_rec contact16 88 4 386 (by decide +kernel)
private theorem contact16RanksSlice92 : sliceWindow (auxiliaryRankSlice contact16) 92 6 = 0 :=
  contactRankWindow_of_rec contact16 92 6 0 (by decide +kernel)
private theorem contact16RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact16) 0 8 = 7751064 :=
  combineSlices (auxiliaryRankSlice contact16) 0 4 4 4087788 3663276 contact16RanksSlice0 contact16RanksSlice4
private theorem contact16RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact16) 8 8 = 6154392 :=
  combineSlices (auxiliaryRankSlice contact16) 8 4 4 3264108 2890284 contact16RanksSlice8 contact16RanksSlice12
private theorem contact16RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact16) 16 8 = 4760472 :=
  combineSlices (auxiliaryRankSlice contact16) 16 4 4 2541804 2218668 contact16RanksSlice16 contact16RanksSlice20
private theorem contact16RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact16) 24 8 = 3569304 :=
  combineSlices (auxiliaryRankSlice contact16) 24 4 4 1920876 1648428 contact16RanksSlice24 contact16RanksSlice28
private theorem contact16RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact16) 32 8 = 2579148 :=
  combineSlices (auxiliaryRankSlice contact16) 32 4 4 1401070 1178078 contact16RanksSlice32 contact16RanksSlice36
private theorem contact16RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact16) 40 8 = 1779846 :=
  combineSlices (auxiliaryRankSlice contact16) 40 4 4 978542 801304 contact16RanksSlice40 contact16RanksSlice44
private theorem contact16RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact16) 48 8 = 1154648 :=
  combineSlices (auxiliaryRankSlice contact16) 48 4 4 645306 509342 contact16RanksSlice48 contact16RanksSlice52
private theorem contact16RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact16) 56 8 = 685250 :=
  combineSlices (auxiliaryRankSlice contact16) 56 4 4 392236 293014 contact16RanksSlice56 contact16RanksSlice60
private theorem contact16RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact16) 64 8 = 353550 :=
  combineSlices (auxiliaryRankSlice contact16) 64 4 4 210382 143168 contact16RanksSlice64 contact16RanksSlice68
private theorem contact16RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact16) 72 8 = 141424 :=
  combineSlices (auxiliaryRankSlice contact16) 72 4 4 90482 50942 contact16RanksSlice72 contact16RanksSlice76
private theorem contact16RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact16) 80 8 = 30377 :=
  combineSlices (auxiliaryRankSlice contact16) 80 4 4 23380 6997 contact16RanksSlice80 contact16RanksSlice84
private theorem contact16RanksJoin88_10 : sliceWindow (auxiliaryRankSlice contact16) 88 10 = 386 :=
  combineSlices (auxiliaryRankSlice contact16) 88 4 6 386 0 contact16RanksSlice88 contact16RanksSlice92
private theorem contact16RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact16) 0 16 = 13905456 :=
  combineSlices (auxiliaryRankSlice contact16) 0 8 8 7751064 6154392 contact16RanksJoin0_8 contact16RanksJoin8_8
private theorem contact16RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact16) 16 16 = 8329776 :=
  combineSlices (auxiliaryRankSlice contact16) 16 8 8 4760472 3569304 contact16RanksJoin16_8 contact16RanksJoin24_8
private theorem contact16RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact16) 32 16 = 4358994 :=
  combineSlices (auxiliaryRankSlice contact16) 32 8 8 2579148 1779846 contact16RanksJoin32_8 contact16RanksJoin40_8
private theorem contact16RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact16) 48 16 = 1839898 :=
  combineSlices (auxiliaryRankSlice contact16) 48 8 8 1154648 685250 contact16RanksJoin48_8 contact16RanksJoin56_8
private theorem contact16RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact16) 64 16 = 494974 :=
  combineSlices (auxiliaryRankSlice contact16) 64 8 8 353550 141424 contact16RanksJoin64_8 contact16RanksJoin72_8
private theorem contact16RanksJoin80_18 : sliceWindow (auxiliaryRankSlice contact16) 80 18 = 30763 :=
  combineSlices (auxiliaryRankSlice contact16) 80 8 10 30377 386 contact16RanksJoin80_8 contact16RanksJoin88_10
private theorem contact16RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact16) 0 32 = 22235232 :=
  combineSlices (auxiliaryRankSlice contact16) 0 16 16 13905456 8329776 contact16RanksJoin0_16 contact16RanksJoin16_16
private theorem contact16RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact16) 32 32 = 6198892 :=
  combineSlices (auxiliaryRankSlice contact16) 32 16 16 4358994 1839898 contact16RanksJoin32_16 contact16RanksJoin48_16
private theorem contact16RanksJoin64_34 : sliceWindow (auxiliaryRankSlice contact16) 64 34 = 525737 :=
  combineSlices (auxiliaryRankSlice contact16) 64 16 18 494974 30763 contact16RanksJoin64_16 contact16RanksJoin80_18
private theorem contact16RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact16) 0 64 = 28434124 :=
  combineSlices (auxiliaryRankSlice contact16) 0 32 32 22235232 6198892 contact16RanksJoin0_32 contact16RanksJoin32_32
private theorem contact16RanksJoin0_98 : sliceWindow (auxiliaryRankSlice contact16) 0 98 = 28959861 :=
  combineSlices (auxiliaryRankSlice contact16) 0 64 34 28434124 525737 contact16RanksJoin0_64 contact16RanksJoin64_34
theorem contact16_margin : sourceMargin contact16 :=
  margin_of_checked_counts contact16 98 172282802965419 9509544031719 664521603 28959861 rfl contact16OrdinaryColumns contact16ColumnsJoin0_98 contact16OrdinaryRanks contact16RanksJoin0_98 (by decide +kernel)

private theorem contact18OrdinaryColumns : ordinaryColumnCount contact18 = 2346616614913759 := by decide +kernel
private theorem contact18ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact18) 0 4 = 7049472435372 :=
  contactColumnsWindow_fast contact18 0 4 7049472435372 (by decide +kernel)
private theorem contact18ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact18) 4 4 = 6702351862924 :=
  contactColumnsWindow_fast contact18 4 4 6702351862924 (by decide +kernel)
private theorem contact18ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact18) 8 4 = 6364031528911 :=
  contactColumnsWindow_fast contact18 8 4 6364031528911 (by decide +kernel)
private theorem contact18ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact18) 12 4 = 6034514326878 :=
  contactColumnsWindow_fast contact18 12 4 6034514326878 (by decide +kernel)
private theorem contact18ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact18) 16 4 = 5713798283170 :=
  contactColumnsWindow_fast contact18 16 4 5713798283170 (by decide +kernel)
private theorem contact18ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact18) 20 4 = 5401885397928 :=
  contactColumnsWindow_fast contact18 20 4 5401885397928 (by decide +kernel)
private theorem contact18ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact18) 24 4 = 5098790549988 :=
  contactColumnsWindow_fast contact18 24 4 5098790549988 (by decide +kernel)
private theorem contact18ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact18) 28 4 = 4804532985614 :=
  contactColumnsWindow_fast contact18 28 4 4804532985614 (by decide +kernel)
private theorem contact18ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact18) 32 4 = 4519081840240 :=
  contactColumnsWindow_fast contact18 32 4 4519081840240 (by decide +kernel)
private theorem contact18ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact18) 36 4 = 4242435033605 :=
  contactColumnsWindow_fast contact18 36 4 4242435033605 (by decide +kernel)
private theorem contact18ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact18) 40 4 = 3974594405960 :=
  contactColumnsWindow_fast contact18 40 4 3974594405960 (by decide +kernel)
private theorem contact18ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact18) 44 4 = 3715578494311 :=
  contactColumnsWindow_fast contact18 44 4 3715578494311 (by decide +kernel)
private theorem contact18ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact18) 48 4 = 3465400755355 :=
  contactColumnsWindow_fast contact18 48 4 3465400755355 (by decide +kernel)
private theorem contact18ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact18) 52 4 = 3224030976690 :=
  contactColumnsWindow_fast contact18 52 4 3224030976690 (by decide +kernel)
private theorem contact18ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact18) 56 4 = 2991469785565 :=
  contactColumnsWindow_fast contact18 56 4 2991469785565 (by decide +kernel)
private theorem contact18ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact18) 60 4 = 2767716949623 :=
  contactColumnsWindow_fast contact18 60 4 2767716949623 (by decide +kernel)
private theorem contact18ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact18) 64 4 = 2552798287648 :=
  contactColumnsWindow_fast contact18 64 4 2552798287648 (by decide +kernel)
private theorem contact18ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact18) 68 4 = 2346715260994 :=
  contactColumnsWindow_fast contact18 68 4 2346715260994 (by decide +kernel)
private theorem contact18ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact18) 72 4 = 2149445176059 :=
  contactColumnsWindow_fast contact18 72 4 2149445176059 (by decide +kernel)
private theorem contact18ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact18) 76 4 = 1960984238102 :=
  contactColumnsWindow_fast contact18 76 4 1960984238102 (by decide +kernel)
private theorem contact18ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact18) 80 4 = 1781331436989 :=
  contactColumnsWindow_fast contact18 80 4 1781331436989 (by decide +kernel)
private theorem contact18ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact18) 84 4 = 1610517737329 :=
  contactColumnsWindow_fast contact18 84 4 1610517737329 (by decide +kernel)
private theorem contact18ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact18) 88 4 = 1448535354014 :=
  contactColumnsWindow_fast contact18 88 4 1448535354014 (by decide +kernel)
private theorem contact18ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact18) 92 4 = 1295365513161 :=
  contactColumnsWindow_fast contact18 92 4 1295365513161 (by decide +kernel)
private theorem contact18ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact18) 96 4 = 1151004787763 :=
  contactColumnsWindow_fast contact18 96 4 1151004787763 (by decide +kernel)
private theorem contact18ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact18) 100 4 = 1015452821480 :=
  contactColumnsWindow_fast contact18 100 4 1015452821480 (by decide +kernel)
private theorem contact18ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact18) 104 4 = 888743380987 :=
  contactColumnsWindow_fast contact18 104 4 888743380987 (by decide +kernel)
private theorem contact18ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact18) 108 4 = 770861627492 :=
  contactColumnsWindow_fast contact18 108 4 770861627492 (by decide +kernel)
private theorem contact18ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact18) 112 4 = 661791951993 :=
  contactColumnsWindow_fast contact18 112 4 661791951993 (by decide +kernel)
private theorem contact18ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact18) 116 4 = 561531517693 :=
  contactColumnsWindow_fast contact18 116 4 561531517693 (by decide +kernel)
private theorem contact18ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact18) 120 4 = 470080912817 :=
  contactColumnsWindow_fast contact18 120 4 470080912817 (by decide +kernel)
private theorem contact18ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact18) 124 4 = 387475106917 :=
  contactColumnsWindow_fast contact18 124 4 387475106917 (by decide +kernel)
private theorem contact18ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact18) 128 4 = 313694031757 :=
  contactColumnsWindow_fast contact18 128 4 313694031757 (by decide +kernel)
private theorem contact18ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact18) 132 4 = 248724649721 :=
  contactColumnsWindow_fast contact18 132 4 248724649721 (by decide +kernel)
private theorem contact18ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact18) 136 4 = 192547649945 :=
  contactColumnsWindow_fast contact18 136 4 192547649945 (by decide +kernel)
private theorem contact18ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact18) 140 4 = 145016925843 :=
  contactColumnsWindow_fast contact18 140 4 145016925843 (by decide +kernel)
private theorem contact18ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact18) 144 4 = 105821134850 :=
  contactColumnsWindow_fast contact18 144 4 105821134850 (by decide +kernel)
private theorem contact18ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact18) 148 4 = 74423471760 :=
  contactColumnsWindow_fast contact18 148 4 74423471760 (by decide +kernel)
private theorem contact18ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact18) 152 4 = 50141322217 :=
  contactColumnsWindow_fast contact18 152 4 50141322217 (by decide +kernel)
private theorem contact18ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact18) 156 4 = 32139682411 :=
  contactColumnsWindow_fast contact18 156 4 32139682411 (by decide +kernel)
private theorem contact18ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact18) 160 2 = 11014851594 :=
  contactColumnsWindow_fast contact18 160 2 11014851594 (by decide +kernel)
private theorem contact18ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact18) 0 8 = 13751824298296 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 4 4 7049472435372 6702351862924 contact18ColumnsSlice0 contact18ColumnsSlice4
private theorem contact18ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact18) 8 8 = 12398545855789 :=
  combineSlices (auxiliaryColumnSlice contact18) 8 4 4 6364031528911 6034514326878 contact18ColumnsSlice8 contact18ColumnsSlice12
private theorem contact18ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact18) 16 8 = 11115683681098 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 4 4 5713798283170 5401885397928 contact18ColumnsSlice16 contact18ColumnsSlice20
private theorem contact18ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact18) 24 8 = 9903323535602 :=
  combineSlices (auxiliaryColumnSlice contact18) 24 4 4 5098790549988 4804532985614 contact18ColumnsSlice24 contact18ColumnsSlice28
private theorem contact18ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact18) 32 8 = 8761516873845 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 4 4 4519081840240 4242435033605 contact18ColumnsSlice32 contact18ColumnsSlice36
private theorem contact18ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact18) 40 8 = 7690172900271 :=
  combineSlices (auxiliaryColumnSlice contact18) 40 4 4 3974594405960 3715578494311 contact18ColumnsSlice40 contact18ColumnsSlice44
private theorem contact18ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact18) 48 8 = 6689431732045 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 4 4 3465400755355 3224030976690 contact18ColumnsSlice48 contact18ColumnsSlice52
private theorem contact18ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact18) 56 8 = 5759186735188 :=
  combineSlices (auxiliaryColumnSlice contact18) 56 4 4 2991469785565 2767716949623 contact18ColumnsSlice56 contact18ColumnsSlice60
private theorem contact18ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact18) 64 8 = 4899513548642 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 4 4 2552798287648 2346715260994 contact18ColumnsSlice64 contact18ColumnsSlice68
private theorem contact18ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact18) 72 8 = 4110429414161 :=
  combineSlices (auxiliaryColumnSlice contact18) 72 4 4 2149445176059 1960984238102 contact18ColumnsSlice72 contact18ColumnsSlice76
private theorem contact18ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact18) 80 8 = 3391849174318 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 4 4 1781331436989 1610517737329 contact18ColumnsSlice80 contact18ColumnsSlice84
private theorem contact18ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact18) 88 8 = 2743900867175 :=
  combineSlices (auxiliaryColumnSlice contact18) 88 4 4 1448535354014 1295365513161 contact18ColumnsSlice88 contact18ColumnsSlice92
private theorem contact18ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact18) 96 8 = 2166457609243 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 4 4 1151004787763 1015452821480 contact18ColumnsSlice96 contact18ColumnsSlice100
private theorem contact18ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact18) 104 8 = 1659605008479 :=
  combineSlices (auxiliaryColumnSlice contact18) 104 4 4 888743380987 770861627492 contact18ColumnsSlice104 contact18ColumnsSlice108
private theorem contact18ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact18) 112 8 = 1223323469686 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 4 4 661791951993 561531517693 contact18ColumnsSlice112 contact18ColumnsSlice116
private theorem contact18ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact18) 120 8 = 857556019734 :=
  combineSlices (auxiliaryColumnSlice contact18) 120 4 4 470080912817 387475106917 contact18ColumnsSlice120 contact18ColumnsSlice124
private theorem contact18ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact18) 128 8 = 562418681478 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 4 4 313694031757 248724649721 contact18ColumnsSlice128 contact18ColumnsSlice132
private theorem contact18ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact18) 136 8 = 337564575788 :=
  combineSlices (auxiliaryColumnSlice contact18) 136 4 4 192547649945 145016925843 contact18ColumnsSlice136 contact18ColumnsSlice140
private theorem contact18ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact18) 144 8 = 180244606610 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 4 4 105821134850 74423471760 contact18ColumnsSlice144 contact18ColumnsSlice148
private theorem contact18ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact18) 152 8 = 82281004628 :=
  combineSlices (auxiliaryColumnSlice contact18) 152 4 4 50141322217 32139682411 contact18ColumnsSlice152 contact18ColumnsSlice156
private theorem contact18ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact18) 0 16 = 26150370154085 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 8 8 13751824298296 12398545855789 contact18ColumnsJoin0_8 contact18ColumnsJoin8_8
private theorem contact18ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact18) 16 16 = 21019007216700 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 8 8 11115683681098 9903323535602 contact18ColumnsJoin16_8 contact18ColumnsJoin24_8
private theorem contact18ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact18) 32 16 = 16451689774116 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 8 8 8761516873845 7690172900271 contact18ColumnsJoin32_8 contact18ColumnsJoin40_8
private theorem contact18ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact18) 48 16 = 12448618467233 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 8 8 6689431732045 5759186735188 contact18ColumnsJoin48_8 contact18ColumnsJoin56_8
private theorem contact18ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact18) 64 16 = 9009942962803 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 8 8 4899513548642 4110429414161 contact18ColumnsJoin64_8 contact18ColumnsJoin72_8
private theorem contact18ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact18) 80 16 = 6135750041493 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 8 8 3391849174318 2743900867175 contact18ColumnsJoin80_8 contact18ColumnsJoin88_8
private theorem contact18ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact18) 96 16 = 3826062617722 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 8 8 2166457609243 1659605008479 contact18ColumnsJoin96_8 contact18ColumnsJoin104_8
private theorem contact18ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact18) 112 16 = 2080879489420 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 8 8 1223323469686 857556019734 contact18ColumnsJoin112_8 contact18ColumnsJoin120_8
private theorem contact18ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact18) 128 16 = 899983257266 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 8 8 562418681478 337564575788 contact18ColumnsJoin128_8 contact18ColumnsJoin136_8
private theorem contact18ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact18) 144 16 = 262525611238 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 8 8 180244606610 82281004628 contact18ColumnsJoin144_8 contact18ColumnsJoin152_8
private theorem contact18ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact18) 0 32 = 47169377370785 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 16 16 26150370154085 21019007216700 contact18ColumnsJoin0_16 contact18ColumnsJoin16_16
private theorem contact18ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact18) 32 32 = 28900308241349 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 16 16 16451689774116 12448618467233 contact18ColumnsJoin32_16 contact18ColumnsJoin48_16
private theorem contact18ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact18) 64 32 = 15145693004296 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 16 16 9009942962803 6135750041493 contact18ColumnsJoin64_16 contact18ColumnsJoin80_16
private theorem contact18ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact18) 96 32 = 5906942107142 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 16 16 3826062617722 2080879489420 contact18ColumnsJoin96_16 contact18ColumnsJoin112_16
private theorem contact18ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact18) 128 32 = 1162508868504 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 16 16 899983257266 262525611238 contact18ColumnsJoin128_16 contact18ColumnsJoin144_16
private theorem contact18ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact18) 0 64 = 76069685612134 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 32 32 47169377370785 28900308241349 contact18ColumnsJoin0_32 contact18ColumnsJoin32_32
private theorem contact18ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact18) 64 64 = 21052635111438 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 32 32 15145693004296 5906942107142 contact18ColumnsJoin64_32 contact18ColumnsJoin96_32
private theorem contact18ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact18) 128 34 = 1173523720098 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 32 2 1162508868504 11014851594 contact18ColumnsJoin128_32 contact18ColumnsSlice160
private theorem contact18ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact18) 0 128 = 97122320723572 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 64 64 76069685612134 21052635111438 contact18ColumnsJoin0_64 contact18ColumnsJoin64_64
private theorem contact18ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact18) 0 162 = 98295844443670 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 128 34 97122320723572 1173523720098 contact18ColumnsJoin0_128 contact18ColumnsJoin128_34
private theorem contact18OrdinaryRanks : ordinaryRankBound contact18 = 9028334050 := by decide +kernel
private theorem contact18RanksSlice0 : sliceWindow (auxiliaryRankSlice contact18) 0 4 = 26575668 :=
  contactRankWindow_of_rec contact18 0 4 26575668 (by decide +kernel)
private theorem contact18RanksSlice4 : sliceWindow (auxiliaryRankSlice contact18) 4 4 = 24869684 :=
  contactRankWindow_of_rec contact18 4 4 24869684 (by decide +kernel)
private theorem contact18RanksSlice8 : sliceWindow (auxiliaryRankSlice contact18) 8 4 = 23224628 :=
  contactRankWindow_of_rec contact18 8 4 23224628 (by decide +kernel)
private theorem contact18RanksSlice12 : sliceWindow (auxiliaryRankSlice contact18) 12 4 = 21640500 :=
  contactRankWindow_of_rec contact18 12 4 21640500 (by decide +kernel)
private theorem contact18RanksSlice16 : sliceWindow (auxiliaryRankSlice contact18) 16 4 = 20117300 :=
  contactRankWindow_of_rec contact18 16 4 20117300 (by decide +kernel)
private theorem contact18RanksSlice20 : sliceWindow (auxiliaryRankSlice contact18) 20 4 = 18655028 :=
  contactRankWindow_of_rec contact18 20 4 18655028 (by decide +kernel)
private theorem contact18RanksSlice24 : sliceWindow (auxiliaryRankSlice contact18) 24 4 = 17253684 :=
  contactRankWindow_of_rec contact18 24 4 17253684 (by decide +kernel)
private theorem contact18RanksSlice28 : sliceWindow (auxiliaryRankSlice contact18) 28 4 = 15913268 :=
  contactRankWindow_of_rec contact18 28 4 15913268 (by decide +kernel)
private theorem contact18RanksSlice32 : sliceWindow (auxiliaryRankSlice contact18) 32 4 = 14633780 :=
  contactRankWindow_of_rec contact18 32 4 14633780 (by decide +kernel)
private theorem contact18RanksSlice36 : sliceWindow (auxiliaryRankSlice contact18) 36 4 = 13415220 :=
  contactRankWindow_of_rec contact18 36 4 13415220 (by decide +kernel)
private theorem contact18RanksSlice40 : sliceWindow (auxiliaryRankSlice contact18) 40 4 = 12257588 :=
  contactRankWindow_of_rec contact18 40 4 12257588 (by decide +kernel)
private theorem contact18RanksSlice44 : sliceWindow (auxiliaryRankSlice contact18) 44 4 = 11160884 :=
  contactRankWindow_of_rec contact18 44 4 11160884 (by decide +kernel)
private theorem contact18RanksSlice48 : sliceWindow (auxiliaryRankSlice contact18) 48 4 = 10125108 :=
  contactRankWindow_of_rec contact18 48 4 10125108 (by decide +kernel)
private theorem contact18RanksSlice52 : sliceWindow (auxiliaryRankSlice contact18) 52 4 = 9150176 :=
  contactRankWindow_of_rec contact18 52 4 9150176 (by decide +kernel)
private theorem contact18RanksSlice56 : sliceWindow (auxiliaryRankSlice contact18) 56 4 = 8235266 :=
  contactRankWindow_of_rec contact18 56 4 8235266 (by decide +kernel)
private theorem contact18RanksSlice60 : sliceWindow (auxiliaryRankSlice contact18) 60 4 = 7379140 :=
  contactRankWindow_of_rec contact18 60 4 7379140 (by decide +kernel)
private theorem contact18RanksSlice64 : sliceWindow (auxiliaryRankSlice contact18) 64 4 = 6580522 :=
  contactRankWindow_of_rec contact18 64 4 6580522 (by decide +kernel)
private theorem contact18RanksSlice68 : sliceWindow (auxiliaryRankSlice contact18) 68 4 = 5837820 :=
  contactRankWindow_of_rec contact18 68 4 5837820 (by decide +kernel)
private theorem contact18RanksSlice72 : sliceWindow (auxiliaryRankSlice contact18) 72 4 = 5149236 :=
  contactRankWindow_of_rec contact18 72 4 5149236 (by decide +kernel)
private theorem contact18RanksSlice76 : sliceWindow (auxiliaryRankSlice contact18) 76 4 = 4512962 :=
  contactRankWindow_of_rec contact18 76 4 4512962 (by decide +kernel)
private theorem contact18RanksSlice80 : sliceWindow (auxiliaryRankSlice contact18) 80 4 = 3927404 :=
  contactRankWindow_of_rec contact18 80 4 3927404 (by decide +kernel)
private theorem contact18RanksSlice84 : sliceWindow (auxiliaryRankSlice contact18) 84 4 = 3390628 :=
  contactRankWindow_of_rec contact18 84 4 3390628 (by decide +kernel)
private theorem contact18RanksSlice88 : sliceWindow (auxiliaryRankSlice contact18) 88 4 = 2900826 :=
  contactRankWindow_of_rec contact18 88 4 2900826 (by decide +kernel)
private theorem contact18RanksSlice92 : sliceWindow (auxiliaryRankSlice contact18) 92 4 = 2456540 :=
  contactRankWindow_of_rec contact18 92 4 2456540 (by decide +kernel)
private theorem contact18RanksSlice96 : sliceWindow (auxiliaryRankSlice contact18) 96 4 = 2055700 :=
  contactRankWindow_of_rec contact18 96 4 2055700 (by decide +kernel)
private theorem contact18RanksSlice100 : sliceWindow (auxiliaryRankSlice contact18) 100 4 = 1696498 :=
  contactRankWindow_of_rec contact18 100 4 1696498 (by decide +kernel)
private theorem contact18RanksSlice104 : sliceWindow (auxiliaryRankSlice contact18) 104 4 = 1377612 :=
  contactRankWindow_of_rec contact18 104 4 1377612 (by decide +kernel)
private theorem contact18RanksSlice108 : sliceWindow (auxiliaryRankSlice contact18) 108 4 = 1096836 :=
  contactRankWindow_of_rec contact18 108 4 1096836 (by decide +kernel)
private theorem contact18RanksSlice112 : sliceWindow (auxiliaryRankSlice contact18) 112 4 = 852362 :=
  contactRankWindow_of_rec contact18 112 4 852362 (by decide +kernel)
private theorem contact18RanksSlice116 : sliceWindow (auxiliaryRankSlice contact18) 116 4 = 643004 :=
  contactRankWindow_of_rec contact18 116 4 643004 (by decide +kernel)
private theorem contact18RanksSlice120 : sliceWindow (auxiliaryRankSlice contact18) 120 4 = 466420 :=
  contactRankWindow_of_rec contact18 120 4 466420 (by decide +kernel)
private theorem contact18RanksSlice124 : sliceWindow (auxiliaryRankSlice contact18) 124 4 = 320802 :=
  contactRankWindow_of_rec contact18 124 4 320802 (by decide +kernel)
private theorem contact18RanksSlice128 : sliceWindow (auxiliaryRankSlice contact18) 128 4 = 205100 :=
  contactRankWindow_of_rec contact18 128 4 205100 (by decide +kernel)
private theorem contact18RanksSlice132 : sliceWindow (auxiliaryRankSlice contact18) 132 4 = 116836 :=
  contactRankWindow_of_rec contact18 132 4 116836 (by decide +kernel)
private theorem contact18RanksSlice136 : sliceWindow (auxiliaryRankSlice contact18) 136 4 = 54205 :=
  contactRankWindow_of_rec contact18 136 4 54205 (by decide +kernel)
private theorem contact18RanksSlice140 : sliceWindow (auxiliaryRankSlice contact18) 140 4 = 16421 :=
  contactRankWindow_of_rec contact18 140 4 16421 (by decide +kernel)
private theorem contact18RanksSlice144 : sliceWindow (auxiliaryRankSlice contact18) 144 4 = 924 :=
  contactRankWindow_of_rec contact18 144 4 924 (by decide +kernel)
private theorem contact18RanksSlice148 : sliceWindow (auxiliaryRankSlice contact18) 148 14 = 0 :=
  contactRankWindow_of_rec contact18 148 14 0 (by decide +kernel)
private theorem contact18RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact18) 0 8 = 51445352 :=
  combineSlices (auxiliaryRankSlice contact18) 0 4 4 26575668 24869684 contact18RanksSlice0 contact18RanksSlice4
private theorem contact18RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact18) 8 8 = 44865128 :=
  combineSlices (auxiliaryRankSlice contact18) 8 4 4 23224628 21640500 contact18RanksSlice8 contact18RanksSlice12
private theorem contact18RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact18) 16 8 = 38772328 :=
  combineSlices (auxiliaryRankSlice contact18) 16 4 4 20117300 18655028 contact18RanksSlice16 contact18RanksSlice20
private theorem contact18RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact18) 24 8 = 33166952 :=
  combineSlices (auxiliaryRankSlice contact18) 24 4 4 17253684 15913268 contact18RanksSlice24 contact18RanksSlice28
private theorem contact18RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact18) 32 8 = 28049000 :=
  combineSlices (auxiliaryRankSlice contact18) 32 4 4 14633780 13415220 contact18RanksSlice32 contact18RanksSlice36
private theorem contact18RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact18) 40 8 = 23418472 :=
  combineSlices (auxiliaryRankSlice contact18) 40 4 4 12257588 11160884 contact18RanksSlice40 contact18RanksSlice44
private theorem contact18RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact18) 48 8 = 19275284 :=
  combineSlices (auxiliaryRankSlice contact18) 48 4 4 10125108 9150176 contact18RanksSlice48 contact18RanksSlice52
private theorem contact18RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact18) 56 8 = 15614406 :=
  combineSlices (auxiliaryRankSlice contact18) 56 4 4 8235266 7379140 contact18RanksSlice56 contact18RanksSlice60
private theorem contact18RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact18) 64 8 = 12418342 :=
  combineSlices (auxiliaryRankSlice contact18) 64 4 4 6580522 5837820 contact18RanksSlice64 contact18RanksSlice68
private theorem contact18RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact18) 72 8 = 9662198 :=
  combineSlices (auxiliaryRankSlice contact18) 72 4 4 5149236 4512962 contact18RanksSlice72 contact18RanksSlice76
private theorem contact18RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact18) 80 8 = 7318032 :=
  combineSlices (auxiliaryRankSlice contact18) 80 4 4 3927404 3390628 contact18RanksSlice80 contact18RanksSlice84
private theorem contact18RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact18) 88 8 = 5357366 :=
  combineSlices (auxiliaryRankSlice contact18) 88 4 4 2900826 2456540 contact18RanksSlice88 contact18RanksSlice92
private theorem contact18RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact18) 96 8 = 3752198 :=
  combineSlices (auxiliaryRankSlice contact18) 96 4 4 2055700 1696498 contact18RanksSlice96 contact18RanksSlice100
private theorem contact18RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact18) 104 8 = 2474448 :=
  combineSlices (auxiliaryRankSlice contact18) 104 4 4 1377612 1096836 contact18RanksSlice104 contact18RanksSlice108
private theorem contact18RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact18) 112 8 = 1495366 :=
  combineSlices (auxiliaryRankSlice contact18) 112 4 4 852362 643004 contact18RanksSlice112 contact18RanksSlice116
private theorem contact18RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact18) 120 8 = 787222 :=
  combineSlices (auxiliaryRankSlice contact18) 120 4 4 466420 320802 contact18RanksSlice120 contact18RanksSlice124
private theorem contact18RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact18) 128 8 = 321936 :=
  combineSlices (auxiliaryRankSlice contact18) 128 4 4 205100 116836 contact18RanksSlice128 contact18RanksSlice132
private theorem contact18RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact18) 136 8 = 70626 :=
  combineSlices (auxiliaryRankSlice contact18) 136 4 4 54205 16421 contact18RanksSlice136 contact18RanksSlice140
private theorem contact18RanksJoin144_18 : sliceWindow (auxiliaryRankSlice contact18) 144 18 = 924 :=
  combineSlices (auxiliaryRankSlice contact18) 144 4 14 924 0 contact18RanksSlice144 contact18RanksSlice148
private theorem contact18RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact18) 0 16 = 96310480 :=
  combineSlices (auxiliaryRankSlice contact18) 0 8 8 51445352 44865128 contact18RanksJoin0_8 contact18RanksJoin8_8
private theorem contact18RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact18) 16 16 = 71939280 :=
  combineSlices (auxiliaryRankSlice contact18) 16 8 8 38772328 33166952 contact18RanksJoin16_8 contact18RanksJoin24_8
private theorem contact18RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact18) 32 16 = 51467472 :=
  combineSlices (auxiliaryRankSlice contact18) 32 8 8 28049000 23418472 contact18RanksJoin32_8 contact18RanksJoin40_8
private theorem contact18RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact18) 48 16 = 34889690 :=
  combineSlices (auxiliaryRankSlice contact18) 48 8 8 19275284 15614406 contact18RanksJoin48_8 contact18RanksJoin56_8
private theorem contact18RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact18) 64 16 = 22080540 :=
  combineSlices (auxiliaryRankSlice contact18) 64 8 8 12418342 9662198 contact18RanksJoin64_8 contact18RanksJoin72_8
private theorem contact18RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact18) 80 16 = 12675398 :=
  combineSlices (auxiliaryRankSlice contact18) 80 8 8 7318032 5357366 contact18RanksJoin80_8 contact18RanksJoin88_8
private theorem contact18RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact18) 96 16 = 6226646 :=
  combineSlices (auxiliaryRankSlice contact18) 96 8 8 3752198 2474448 contact18RanksJoin96_8 contact18RanksJoin104_8
private theorem contact18RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact18) 112 16 = 2282588 :=
  combineSlices (auxiliaryRankSlice contact18) 112 8 8 1495366 787222 contact18RanksJoin112_8 contact18RanksJoin120_8
private theorem contact18RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact18) 128 16 = 392562 :=
  combineSlices (auxiliaryRankSlice contact18) 128 8 8 321936 70626 contact18RanksJoin128_8 contact18RanksJoin136_8
private theorem contact18RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact18) 0 32 = 168249760 :=
  combineSlices (auxiliaryRankSlice contact18) 0 16 16 96310480 71939280 contact18RanksJoin0_16 contact18RanksJoin16_16
private theorem contact18RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact18) 32 32 = 86357162 :=
  combineSlices (auxiliaryRankSlice contact18) 32 16 16 51467472 34889690 contact18RanksJoin32_16 contact18RanksJoin48_16
private theorem contact18RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact18) 64 32 = 34755938 :=
  combineSlices (auxiliaryRankSlice contact18) 64 16 16 22080540 12675398 contact18RanksJoin64_16 contact18RanksJoin80_16
private theorem contact18RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact18) 96 32 = 8509234 :=
  combineSlices (auxiliaryRankSlice contact18) 96 16 16 6226646 2282588 contact18RanksJoin96_16 contact18RanksJoin112_16
private theorem contact18RanksJoin128_34 : sliceWindow (auxiliaryRankSlice contact18) 128 34 = 393486 :=
  combineSlices (auxiliaryRankSlice contact18) 128 16 18 392562 924 contact18RanksJoin128_16 contact18RanksJoin144_18
private theorem contact18RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact18) 0 64 = 254606922 :=
  combineSlices (auxiliaryRankSlice contact18) 0 32 32 168249760 86357162 contact18RanksJoin0_32 contact18RanksJoin32_32
private theorem contact18RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact18) 64 64 = 43265172 :=
  combineSlices (auxiliaryRankSlice contact18) 64 32 32 34755938 8509234 contact18RanksJoin64_32 contact18RanksJoin96_32
private theorem contact18RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact18) 0 128 = 297872094 :=
  combineSlices (auxiliaryRankSlice contact18) 0 64 64 254606922 43265172 contact18RanksJoin0_64 contact18RanksJoin64_64
private theorem contact18RanksJoin0_162 : sliceWindow (auxiliaryRankSlice contact18) 0 162 = 298265580 :=
  combineSlices (auxiliaryRankSlice contact18) 0 128 34 297872094 393486 contact18RanksJoin0_128 contact18RanksJoin128_34
theorem contact18_margin : sourceMargin contact18 :=
  margin_of_checked_counts contact18 162 2346616614913759 98295844443670 9028334050 298265580 rfl contact18OrdinaryColumns contact18ColumnsJoin0_162 contact18OrdinaryRanks contact18RanksJoin0_162 (by decide +kernel)

private theorem contact20OrdinaryColumns : ordinaryColumnCount contact20 = 53387126710766 := by decide +kernel
private theorem contact20ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact20) 0 4 = 448608130450 :=
  contactColumnsWindow_fast contact20 0 4 448608130450 (by decide +kernel)
private theorem contact20ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact20) 4 4 = 403901458290 :=
  contactColumnsWindow_fast contact20 4 4 403901458290 (by decide +kernel)
private theorem contact20ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact20) 8 4 = 361551802130 :=
  contactColumnsWindow_fast contact20 8 4 361551802130 (by decide +kernel)
private theorem contact20ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact20) 12 4 = 321568900556 :=
  contactColumnsWindow_fast contact20 12 4 321568900556 (by decide +kernel)
private theorem contact20ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact20) 16 4 = 283954108636 :=
  contactColumnsWindow_fast contact20 16 4 283954108636 (by decide +kernel)
private theorem contact20ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact20) 20 4 = 248698190630 :=
  contactColumnsWindow_fast contact20 20 4 248698190630 (by decide +kernel)
private theorem contact20ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact20) 24 4 = 215800617219 :=
  contactColumnsWindow_fast contact20 24 4 215800617219 (by decide +kernel)
private theorem contact20ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact20) 28 4 = 185262306440 :=
  contactColumnsWindow_fast contact20 28 4 185262306440 (by decide +kernel)
private theorem contact20ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact20) 32 4 = 157093652846 :=
  contactColumnsWindow_fast contact20 32 4 157093652846 (by decide +kernel)
private theorem contact20ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact20) 36 4 = 131291235083 :=
  contactColumnsWindow_fast contact20 36 4 131291235083 (by decide +kernel)
private theorem contact20ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact20) 40 4 = 107847873644 :=
  contactColumnsWindow_fast contact20 40 4 107847873644 (by decide +kernel)
private theorem contact20ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact20) 44 4 = 86762698932 :=
  contactColumnsWindow_fast contact20 44 4 86762698932 (by decide +kernel)
private theorem contact20ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact20) 48 4 = 68037082449 :=
  contactColumnsWindow_fast contact20 48 4 68037082449 (by decide +kernel)
private theorem contact20ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact20) 52 4 = 51682534316 :=
  contactColumnsWindow_fast contact20 52 4 51682534316 (by decide +kernel)
private theorem contact20ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact20) 56 4 = 37692510314 :=
  contactColumnsWindow_fast contact20 56 4 37692510314 (by decide +kernel)
private theorem contact20ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact20) 60 4 = 26061685838 :=
  contactColumnsWindow_fast contact20 60 4 26061685838 (by decide +kernel)
private theorem contact20ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact20) 64 4 = 16788731142 :=
  contactColumnsWindow_fast contact20 64 4 16788731142 (by decide +kernel)
private theorem contact20ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact20) 68 4 = 9851234892 :=
  contactColumnsWindow_fast contact20 68 4 9851234892 (by decide +kernel)
private theorem contact20ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact20) 72 4 = 5112943223 :=
  contactColumnsWindow_fast contact20 72 4 5112943223 (by decide +kernel)
private theorem contact20ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact20) 76 3 = 1870587991 :=
  contactColumnsWindow_fast contact20 76 3 1870587991 (by decide +kernel)
private theorem contact20ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact20) 0 8 = 852509588740 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 4 4 448608130450 403901458290 contact20ColumnsSlice0 contact20ColumnsSlice4
private theorem contact20ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact20) 8 8 = 683120702686 :=
  combineSlices (auxiliaryColumnSlice contact20) 8 4 4 361551802130 321568900556 contact20ColumnsSlice8 contact20ColumnsSlice12
private theorem contact20ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact20) 16 8 = 532652299266 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 4 4 283954108636 248698190630 contact20ColumnsSlice16 contact20ColumnsSlice20
private theorem contact20ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact20) 24 8 = 401062923659 :=
  combineSlices (auxiliaryColumnSlice contact20) 24 4 4 215800617219 185262306440 contact20ColumnsSlice24 contact20ColumnsSlice28
private theorem contact20ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact20) 32 8 = 288384887929 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 4 4 157093652846 131291235083 contact20ColumnsSlice32 contact20ColumnsSlice36
private theorem contact20ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact20) 40 8 = 194610572576 :=
  combineSlices (auxiliaryColumnSlice contact20) 40 4 4 107847873644 86762698932 contact20ColumnsSlice40 contact20ColumnsSlice44
private theorem contact20ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact20) 48 8 = 119719616765 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 4 4 68037082449 51682534316 contact20ColumnsSlice48 contact20ColumnsSlice52
private theorem contact20ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact20) 56 8 = 63754196152 :=
  combineSlices (auxiliaryColumnSlice contact20) 56 4 4 37692510314 26061685838 contact20ColumnsSlice56 contact20ColumnsSlice60
private theorem contact20ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact20) 64 8 = 26639966034 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 4 4 16788731142 9851234892 contact20ColumnsSlice64 contact20ColumnsSlice68
private theorem contact20ColumnsJoin72_7 : sliceWindow (auxiliaryColumnSlice contact20) 72 7 = 6983531214 :=
  combineSlices (auxiliaryColumnSlice contact20) 72 4 3 5112943223 1870587991 contact20ColumnsSlice72 contact20ColumnsSlice76
private theorem contact20ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact20) 0 16 = 1535630291426 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 8 8 852509588740 683120702686 contact20ColumnsJoin0_8 contact20ColumnsJoin8_8
private theorem contact20ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact20) 16 16 = 933715222925 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 8 8 532652299266 401062923659 contact20ColumnsJoin16_8 contact20ColumnsJoin24_8
private theorem contact20ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact20) 32 16 = 482995460505 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 8 8 288384887929 194610572576 contact20ColumnsJoin32_8 contact20ColumnsJoin40_8
private theorem contact20ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact20) 48 16 = 183473812917 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 8 8 119719616765 63754196152 contact20ColumnsJoin48_8 contact20ColumnsJoin56_8
private theorem contact20ColumnsJoin64_15 : sliceWindow (auxiliaryColumnSlice contact20) 64 15 = 33623497248 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 8 7 26639966034 6983531214 contact20ColumnsJoin64_8 contact20ColumnsJoin72_7
private theorem contact20ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact20) 0 32 = 2469345514351 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 16 16 1535630291426 933715222925 contact20ColumnsJoin0_16 contact20ColumnsJoin16_16
private theorem contact20ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact20) 32 32 = 666469273422 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 16 16 482995460505 183473812917 contact20ColumnsJoin32_16 contact20ColumnsJoin48_16
private theorem contact20ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact20) 0 64 = 3135814787773 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 32 32 2469345514351 666469273422 contact20ColumnsJoin0_32 contact20ColumnsJoin32_32
private theorem contact20ColumnsJoin0_79 : sliceWindow (auxiliaryColumnSlice contact20) 0 79 = 3169438285021 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 64 15 3135814787773 33623497248 contact20ColumnsJoin0_64 contact20ColumnsJoin64_15
private theorem contact20OrdinaryRanks : ordinaryRankBound contact20 = 206112375 := by decide +kernel
private theorem contact20RanksSlice0 : sliceWindow (auxiliaryRankSlice contact20) 0 4 = 1673300 :=
  contactRankWindow_of_rec contact20 0 4 1673300 (by decide +kernel)
private theorem contact20RanksSlice4 : sliceWindow (auxiliaryRankSlice contact20) 4 4 = 1457060 :=
  contactRankWindow_of_rec contact20 4 4 1457060 (by decide +kernel)
private theorem contact20RanksSlice8 : sliceWindow (auxiliaryRankSlice contact20) 8 4 = 1257140 :=
  contactRankWindow_of_rec contact20 8 4 1257140 (by decide +kernel)
private theorem contact20RanksSlice12 : sliceWindow (auxiliaryRankSlice contact20) 12 4 = 1073540 :=
  contactRankWindow_of_rec contact20 12 4 1073540 (by decide +kernel)
private theorem contact20RanksSlice16 : sliceWindow (auxiliaryRankSlice contact20) 16 4 = 906260 :=
  contactRankWindow_of_rec contact20 16 4 906260 (by decide +kernel)
private theorem contact20RanksSlice20 : sliceWindow (auxiliaryRankSlice contact20) 20 4 = 755300 :=
  contactRankWindow_of_rec contact20 20 4 755300 (by decide +kernel)
private theorem contact20RanksSlice24 : sliceWindow (auxiliaryRankSlice contact20) 24 4 = 620645 :=
  contactRankWindow_of_rec contact20 24 4 620645 (by decide +kernel)
private theorem contact20RanksSlice28 : sliceWindow (auxiliaryRankSlice contact20) 28 4 = 501975 :=
  contactRankWindow_of_rec contact20 28 4 501975 (by decide +kernel)
private theorem contact20RanksSlice32 : sliceWindow (auxiliaryRankSlice contact20) 32 4 = 398500 :=
  contactRankWindow_of_rec contact20 32 4 398500 (by decide +kernel)
private theorem contact20RanksSlice36 : sliceWindow (auxiliaryRankSlice contact20) 36 4 = 309345 :=
  contactRankWindow_of_rec contact20 36 4 309345 (by decide +kernel)
private theorem contact20RanksSlice40 : sliceWindow (auxiliaryRankSlice contact20) 40 4 = 233575 :=
  contactRankWindow_of_rec contact20 40 4 233575 (by decide +kernel)
private theorem contact20RanksSlice44 : sliceWindow (auxiliaryRankSlice contact20) 44 4 = 170248 :=
  contactRankWindow_of_rec contact20 44 4 170248 (by decide +kernel)
private theorem contact20RanksSlice48 : sliceWindow (auxiliaryRankSlice contact20) 48 4 = 118557 :=
  contactRankWindow_of_rec contact20 48 4 118557 (by decide +kernel)
private theorem contact20RanksSlice52 : sliceWindow (auxiliaryRankSlice contact20) 52 4 = 77495 :=
  contactRankWindow_of_rec contact20 52 4 77495 (by decide +kernel)
private theorem contact20RanksSlice56 : sliceWindow (auxiliaryRankSlice contact20) 56 4 = 46124 :=
  contactRankWindow_of_rec contact20 56 4 46124 (by decide +kernel)
private theorem contact20RanksSlice60 : sliceWindow (auxiliaryRankSlice contact20) 60 4 = 23705 :=
  contactRankWindow_of_rec contact20 60 4 23705 (by decide +kernel)
private theorem contact20RanksSlice64 : sliceWindow (auxiliaryRankSlice contact20) 64 4 = 9159 :=
  contactRankWindow_of_rec contact20 64 4 9159 (by decide +kernel)
private theorem contact20RanksSlice68 : sliceWindow (auxiliaryRankSlice contact20) 68 4 = 1567 :=
  contactRankWindow_of_rec contact20 68 4 1567 (by decide +kernel)
private theorem contact20RanksSlice72 : sliceWindow (auxiliaryRankSlice contact20) 72 7 = 0 :=
  contactRankWindow_of_rec contact20 72 7 0 (by decide +kernel)
private theorem contact20RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact20) 0 8 = 3130360 :=
  combineSlices (auxiliaryRankSlice contact20) 0 4 4 1673300 1457060 contact20RanksSlice0 contact20RanksSlice4
private theorem contact20RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact20) 8 8 = 2330680 :=
  combineSlices (auxiliaryRankSlice contact20) 8 4 4 1257140 1073540 contact20RanksSlice8 contact20RanksSlice12
private theorem contact20RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact20) 16 8 = 1661560 :=
  combineSlices (auxiliaryRankSlice contact20) 16 4 4 906260 755300 contact20RanksSlice16 contact20RanksSlice20
private theorem contact20RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact20) 24 8 = 1122620 :=
  combineSlices (auxiliaryRankSlice contact20) 24 4 4 620645 501975 contact20RanksSlice24 contact20RanksSlice28
private theorem contact20RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact20) 32 8 = 707845 :=
  combineSlices (auxiliaryRankSlice contact20) 32 4 4 398500 309345 contact20RanksSlice32 contact20RanksSlice36
private theorem contact20RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact20) 40 8 = 403823 :=
  combineSlices (auxiliaryRankSlice contact20) 40 4 4 233575 170248 contact20RanksSlice40 contact20RanksSlice44
private theorem contact20RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact20) 48 8 = 196052 :=
  combineSlices (auxiliaryRankSlice contact20) 48 4 4 118557 77495 contact20RanksSlice48 contact20RanksSlice52
private theorem contact20RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact20) 56 8 = 69829 :=
  combineSlices (auxiliaryRankSlice contact20) 56 4 4 46124 23705 contact20RanksSlice56 contact20RanksSlice60
private theorem contact20RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact20) 64 8 = 10726 :=
  combineSlices (auxiliaryRankSlice contact20) 64 4 4 9159 1567 contact20RanksSlice64 contact20RanksSlice68
private theorem contact20RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact20) 0 16 = 5461040 :=
  combineSlices (auxiliaryRankSlice contact20) 0 8 8 3130360 2330680 contact20RanksJoin0_8 contact20RanksJoin8_8
private theorem contact20RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact20) 16 16 = 2784180 :=
  combineSlices (auxiliaryRankSlice contact20) 16 8 8 1661560 1122620 contact20RanksJoin16_8 contact20RanksJoin24_8
private theorem contact20RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact20) 32 16 = 1111668 :=
  combineSlices (auxiliaryRankSlice contact20) 32 8 8 707845 403823 contact20RanksJoin32_8 contact20RanksJoin40_8
private theorem contact20RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact20) 48 16 = 265881 :=
  combineSlices (auxiliaryRankSlice contact20) 48 8 8 196052 69829 contact20RanksJoin48_8 contact20RanksJoin56_8
private theorem contact20RanksJoin64_15 : sliceWindow (auxiliaryRankSlice contact20) 64 15 = 10726 :=
  combineSlices (auxiliaryRankSlice contact20) 64 8 7 10726 0 contact20RanksJoin64_8 contact20RanksSlice72
private theorem contact20RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact20) 0 32 = 8245220 :=
  combineSlices (auxiliaryRankSlice contact20) 0 16 16 5461040 2784180 contact20RanksJoin0_16 contact20RanksJoin16_16
private theorem contact20RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact20) 32 32 = 1377549 :=
  combineSlices (auxiliaryRankSlice contact20) 32 16 16 1111668 265881 contact20RanksJoin32_16 contact20RanksJoin48_16
private theorem contact20RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact20) 0 64 = 9622769 :=
  combineSlices (auxiliaryRankSlice contact20) 0 32 32 8245220 1377549 contact20RanksJoin0_32 contact20RanksJoin32_32
private theorem contact20RanksJoin0_79 : sliceWindow (auxiliaryRankSlice contact20) 0 79 = 9633495 :=
  combineSlices (auxiliaryRankSlice contact20) 0 64 15 9622769 10726 contact20RanksJoin0_64 contact20RanksJoin64_15
theorem contact20_margin : sourceMargin contact20 :=
  margin_of_checked_counts contact20 79 53387126710766 3169438285021 206112375 9633495 rfl contact20OrdinaryColumns contact20ColumnsJoin0_79 contact20OrdinaryRanks contact20RanksJoin0_79 (by decide +kernel)

private theorem contact22OrdinaryColumns : ordinaryColumnCount contact22 = 156953335463893 := by decide +kernel
private theorem contact22ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact22) 0 4 = 1567133184762 :=
  contactColumnsWindow_fast contact22 0 4 1567133184762 (by decide +kernel)
private theorem contact22ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact22) 4 4 = 1451697329518 :=
  contactColumnsWindow_fast contact22 4 4 1451697329518 (by decide +kernel)
private theorem contact22ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact22) 8 4 = 1340706688433 :=
  contactColumnsWindow_fast contact22 8 4 1340706688433 (by decide +kernel)
private theorem contact22ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact22) 12 4 = 1234155908184 :=
  contactColumnsWindow_fast contact22 12 4 1234155908184 (by decide +kernel)
private theorem contact22ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact22) 16 4 = 1132043219059 :=
  contactColumnsWindow_fast contact22 16 4 1132043219059 (by decide +kernel)
private theorem contact22ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact22) 20 4 = 1034374128719 :=
  contactColumnsWindow_fast contact22 20 4 1034374128719 (by decide +kernel)
private theorem contact22ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact22) 24 4 = 941171949262 :=
  contactColumnsWindow_fast contact22 24 4 941171949262 (by decide +kernel)
private theorem contact22ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact22) 28 4 = 852416306867 :=
  contactColumnsWindow_fast contact22 28 4 852416306867 (by decide +kernel)
private theorem contact22ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact22) 32 4 = 768100678560 :=
  contactColumnsWindow_fast contact22 32 4 768100678560 (by decide +kernel)
private theorem contact22ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact22) 36 4 = 688223235508 :=
  contactColumnsWindow_fast contact22 36 4 688223235508 (by decide +kernel)
private theorem contact22ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact22) 40 4 = 612790985597 :=
  contactColumnsWindow_fast contact22 40 4 612790985597 (by decide +kernel)
private theorem contact22ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact22) 44 4 = 541825846867 :=
  contactColumnsWindow_fast contact22 44 4 541825846867 (by decide +kernel)
private theorem contact22ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact22) 48 4 = 475305501464 :=
  contactColumnsWindow_fast contact22 48 4 475305501464 (by decide +kernel)
private theorem contact22ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact22) 52 4 = 413224986216 :=
  contactColumnsWindow_fast contact22 52 4 413224986216 (by decide +kernel)
private theorem contact22ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact22) 56 4 = 355582806211 :=
  contactColumnsWindow_fast contact22 56 4 355582806211 (by decide +kernel)
private theorem contact22ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact22) 60 4 = 302387379755 :=
  contactColumnsWindow_fast contact22 60 4 302387379755 (by decide +kernel)
private theorem contact22ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact22) 64 4 = 253659340834 :=
  contactColumnsWindow_fast contact22 64 4 253659340834 (by decide +kernel)
private theorem contact22ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact22) 68 4 = 209374290749 :=
  contactColumnsWindow_fast contact22 68 4 209374290749 (by decide +kernel)
private theorem contact22ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact22) 72 4 = 169528831152 :=
  contactColumnsWindow_fast contact22 72 4 169528831152 (by decide +kernel)
private theorem contact22ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact22) 76 4 = 134121927150 :=
  contactColumnsWindow_fast contact22 76 4 134121927150 (by decide +kernel)
private theorem contact22ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact22) 80 4 = 103164168809 :=
  contactColumnsWindow_fast contact22 80 4 103164168809 (by decide +kernel)
private theorem contact22ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact22) 84 4 = 76672419166 :=
  contactColumnsWindow_fast contact22 84 4 76672419166 (by decide +kernel)
private theorem contact22ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact22) 88 4 = 54620692895 :=
  contactColumnsWindow_fast contact22 88 4 54620692895 (by decide +kernel)
private theorem contact22ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact22) 92 4 = 36951185569 :=
  contactColumnsWindow_fast contact22 92 4 36951185569 (by decide +kernel)
private theorem contact22ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact22) 96 4 = 23452238135 :=
  contactColumnsWindow_fast contact22 96 4 23452238135 (by decide +kernel)
private theorem contact22ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact22) 100 4 = 13756318545 :=
  contactColumnsWindow_fast contact22 100 4 13756318545 (by decide +kernel)
private theorem contact22ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact22) 104 1 = 2321980265 :=
  contactColumnsWindow_fast contact22 104 1 2321980265 (by decide +kernel)
private theorem contact22ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact22) 0 8 = 3018830514280 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 4 4 1567133184762 1451697329518 contact22ColumnsSlice0 contact22ColumnsSlice4
private theorem contact22ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact22) 8 8 = 2574862596617 :=
  combineSlices (auxiliaryColumnSlice contact22) 8 4 4 1340706688433 1234155908184 contact22ColumnsSlice8 contact22ColumnsSlice12
private theorem contact22ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact22) 16 8 = 2166417347778 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 4 4 1132043219059 1034374128719 contact22ColumnsSlice16 contact22ColumnsSlice20
private theorem contact22ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact22) 24 8 = 1793588256129 :=
  combineSlices (auxiliaryColumnSlice contact22) 24 4 4 941171949262 852416306867 contact22ColumnsSlice24 contact22ColumnsSlice28
private theorem contact22ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact22) 32 8 = 1456323914068 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 4 4 768100678560 688223235508 contact22ColumnsSlice32 contact22ColumnsSlice36
private theorem contact22ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact22) 40 8 = 1154616832464 :=
  combineSlices (auxiliaryColumnSlice contact22) 40 4 4 612790985597 541825846867 contact22ColumnsSlice40 contact22ColumnsSlice44
private theorem contact22ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact22) 48 8 = 888530487680 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 4 4 475305501464 413224986216 contact22ColumnsSlice48 contact22ColumnsSlice52
private theorem contact22ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact22) 56 8 = 657970185966 :=
  combineSlices (auxiliaryColumnSlice contact22) 56 4 4 355582806211 302387379755 contact22ColumnsSlice56 contact22ColumnsSlice60
private theorem contact22ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact22) 64 8 = 463033631583 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 4 4 253659340834 209374290749 contact22ColumnsSlice64 contact22ColumnsSlice68
private theorem contact22ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact22) 72 8 = 303650758302 :=
  combineSlices (auxiliaryColumnSlice contact22) 72 4 4 169528831152 134121927150 contact22ColumnsSlice72 contact22ColumnsSlice76
private theorem contact22ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact22) 80 8 = 179836587975 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 4 4 103164168809 76672419166 contact22ColumnsSlice80 contact22ColumnsSlice84
private theorem contact22ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact22) 88 8 = 91571878464 :=
  combineSlices (auxiliaryColumnSlice contact22) 88 4 4 54620692895 36951185569 contact22ColumnsSlice88 contact22ColumnsSlice92
private theorem contact22ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact22) 96 8 = 37208556680 :=
  combineSlices (auxiliaryColumnSlice contact22) 96 4 4 23452238135 13756318545 contact22ColumnsSlice96 contact22ColumnsSlice100
private theorem contact22ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact22) 0 16 = 5593693110897 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 8 8 3018830514280 2574862596617 contact22ColumnsJoin0_8 contact22ColumnsJoin8_8
private theorem contact22ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact22) 16 16 = 3960005603907 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 8 8 2166417347778 1793588256129 contact22ColumnsJoin16_8 contact22ColumnsJoin24_8
private theorem contact22ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact22) 32 16 = 2610940746532 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 8 8 1456323914068 1154616832464 contact22ColumnsJoin32_8 contact22ColumnsJoin40_8
private theorem contact22ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact22) 48 16 = 1546500673646 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 8 8 888530487680 657970185966 contact22ColumnsJoin48_8 contact22ColumnsJoin56_8
private theorem contact22ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact22) 64 16 = 766684389885 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 8 8 463033631583 303650758302 contact22ColumnsJoin64_8 contact22ColumnsJoin72_8
private theorem contact22ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact22) 80 16 = 271408466439 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 8 8 179836587975 91571878464 contact22ColumnsJoin80_8 contact22ColumnsJoin88_8
private theorem contact22ColumnsJoin96_9 : sliceWindow (auxiliaryColumnSlice contact22) 96 9 = 39530536945 :=
  combineSlices (auxiliaryColumnSlice contact22) 96 8 1 37208556680 2321980265 contact22ColumnsJoin96_8 contact22ColumnsSlice104
private theorem contact22ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact22) 0 32 = 9553698714804 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 16 16 5593693110897 3960005603907 contact22ColumnsJoin0_16 contact22ColumnsJoin16_16
private theorem contact22ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact22) 32 32 = 4157441420178 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 16 16 2610940746532 1546500673646 contact22ColumnsJoin32_16 contact22ColumnsJoin48_16
private theorem contact22ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact22) 64 32 = 1038092856324 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 16 16 766684389885 271408466439 contact22ColumnsJoin64_16 contact22ColumnsJoin80_16
private theorem contact22ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact22) 0 64 = 13711140134982 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 32 32 9553698714804 4157441420178 contact22ColumnsJoin0_32 contact22ColumnsJoin32_32
private theorem contact22ColumnsJoin64_41 : sliceWindow (auxiliaryColumnSlice contact22) 64 41 = 1077623393269 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 32 9 1038092856324 39530536945 contact22ColumnsJoin64_32 contact22ColumnsJoin96_9
private theorem contact22ColumnsJoin0_105 : sliceWindow (auxiliaryColumnSlice contact22) 0 105 = 14788763528251 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 64 41 13711140134982 1077623393269 contact22ColumnsJoin0_64 contact22ColumnsJoin64_41
private theorem contact22OrdinaryRanks : ordinaryRankBound contact22 = 610133261 := by decide +kernel
private theorem contact22RanksSlice0 : sliceWindow (auxiliaryRankSlice contact22) 0 4 = 5864884 :=
  contactRankWindow_of_rec contact22 0 4 5864884 (by decide +kernel)
private theorem contact22RanksSlice4 : sliceWindow (auxiliaryRankSlice contact22) 4 4 = 5304244 :=
  contactRankWindow_of_rec contact22 4 4 5304244 (by decide +kernel)
private theorem contact22RanksSlice8 : sliceWindow (auxiliaryRankSlice contact22) 8 4 = 4774324 :=
  contactRankWindow_of_rec contact22 8 4 4774324 (by decide +kernel)
private theorem contact22RanksSlice12 : sliceWindow (auxiliaryRankSlice contact22) 12 4 = 4275124 :=
  contactRankWindow_of_rec contact22 12 4 4275124 (by decide +kernel)
private theorem contact22RanksSlice16 : sliceWindow (auxiliaryRankSlice contact22) 16 4 = 3806644 :=
  contactRankWindow_of_rec contact22 16 4 3806644 (by decide +kernel)
private theorem contact22RanksSlice20 : sliceWindow (auxiliaryRankSlice contact22) 20 4 = 3368884 :=
  contactRankWindow_of_rec contact22 20 4 3368884 (by decide +kernel)
private theorem contact22RanksSlice24 : sliceWindow (auxiliaryRankSlice contact22) 24 4 = 2961844 :=
  contactRankWindow_of_rec contact22 24 4 2961844 (by decide +kernel)
private theorem contact22RanksSlice28 : sliceWindow (auxiliaryRankSlice contact22) 28 4 = 2585524 :=
  contactRankWindow_of_rec contact22 28 4 2585524 (by decide +kernel)
private theorem contact22RanksSlice32 : sliceWindow (auxiliaryRankSlice contact22) 32 4 = 2239864 :=
  contactRankWindow_of_rec contact22 32 4 2239864 (by decide +kernel)
private theorem contact22RanksSlice36 : sliceWindow (auxiliaryRankSlice contact22) 36 4 = 1924274 :=
  contactRankWindow_of_rec contact22 36 4 1924274 (by decide +kernel)
private theorem contact22RanksSlice40 : sliceWindow (auxiliaryRankSlice contact22) 40 4 = 1637836 :=
  contactRankWindow_of_rec contact22 40 4 1637836 (by decide +kernel)
private theorem contact22RanksSlice44 : sliceWindow (auxiliaryRankSlice contact22) 44 4 = 1379438 :=
  contactRankWindow_of_rec contact22 44 4 1379438 (by decide +kernel)
private theorem contact22RanksSlice48 : sliceWindow (auxiliaryRankSlice contact22) 48 4 = 1147802 :=
  contactRankWindow_of_rec contact22 48 4 1147802 (by decide +kernel)
private theorem contact22RanksSlice52 : sliceWindow (auxiliaryRankSlice contact22) 52 4 = 941632 :=
  contactRankWindow_of_rec contact22 52 4 941632 (by decide +kernel)
private theorem contact22RanksSlice56 : sliceWindow (auxiliaryRankSlice contact22) 56 4 = 759810 :=
  contactRankWindow_of_rec contact22 56 4 759810 (by decide +kernel)
private theorem contact22RanksSlice60 : sliceWindow (auxiliaryRankSlice contact22) 60 4 = 600962 :=
  contactRankWindow_of_rec contact22 60 4 600962 (by decide +kernel)
private theorem contact22RanksSlice64 : sliceWindow (auxiliaryRankSlice contact22) 64 4 = 463796 :=
  contactRankWindow_of_rec contact22 64 4 463796 (by decide +kernel)
private theorem contact22RanksSlice68 : sliceWindow (auxiliaryRankSlice contact22) 68 4 = 347286 :=
  contactRankWindow_of_rec contact22 68 4 347286 (by decide +kernel)
private theorem contact22RanksSlice72 : sliceWindow (auxiliaryRankSlice contact22) 72 4 = 249962 :=
  contactRankWindow_of_rec contact22 72 4 249962 (by decide +kernel)
private theorem contact22RanksSlice76 : sliceWindow (auxiliaryRankSlice contact22) 76 4 = 170536 :=
  contactRankWindow_of_rec contact22 76 4 170536 (by decide +kernel)
private theorem contact22RanksSlice80 : sliceWindow (auxiliaryRankSlice contact22) 80 4 = 108074 :=
  contactRankWindow_of_rec contact22 80 4 108074 (by decide +kernel)
private theorem contact22RanksSlice84 : sliceWindow (auxiliaryRankSlice contact22) 84 4 = 61010 :=
  contactRankWindow_of_rec contact22 84 4 61010 (by decide +kernel)
private theorem contact22RanksSlice88 : sliceWindow (auxiliaryRankSlice contact22) 88 4 = 28060 :=
  contactRankWindow_of_rec contact22 88 4 28060 (by decide +kernel)
private theorem contact22RanksSlice92 : sliceWindow (auxiliaryRankSlice contact22) 92 4 = 8406 :=
  contactRankWindow_of_rec contact22 92 4 8406 (by decide +kernel)
private theorem contact22RanksSlice96 : sliceWindow (auxiliaryRankSlice contact22) 96 4 = 465 :=
  contactRankWindow_of_rec contact22 96 4 465 (by decide +kernel)
private theorem contact22RanksSlice100 : sliceWindow (auxiliaryRankSlice contact22) 100 5 = 0 :=
  contactRankWindow_of_rec contact22 100 5 0 (by decide +kernel)
private theorem contact22RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact22) 0 8 = 11169128 :=
  combineSlices (auxiliaryRankSlice contact22) 0 4 4 5864884 5304244 contact22RanksSlice0 contact22RanksSlice4
private theorem contact22RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact22) 8 8 = 9049448 :=
  combineSlices (auxiliaryRankSlice contact22) 8 4 4 4774324 4275124 contact22RanksSlice8 contact22RanksSlice12
private theorem contact22RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact22) 16 8 = 7175528 :=
  combineSlices (auxiliaryRankSlice contact22) 16 4 4 3806644 3368884 contact22RanksSlice16 contact22RanksSlice20
private theorem contact22RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact22) 24 8 = 5547368 :=
  combineSlices (auxiliaryRankSlice contact22) 24 4 4 2961844 2585524 contact22RanksSlice24 contact22RanksSlice28
private theorem contact22RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact22) 32 8 = 4164138 :=
  combineSlices (auxiliaryRankSlice contact22) 32 4 4 2239864 1924274 contact22RanksSlice32 contact22RanksSlice36
private theorem contact22RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact22) 40 8 = 3017274 :=
  combineSlices (auxiliaryRankSlice contact22) 40 4 4 1637836 1379438 contact22RanksSlice40 contact22RanksSlice44
private theorem contact22RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact22) 48 8 = 2089434 :=
  combineSlices (auxiliaryRankSlice contact22) 48 4 4 1147802 941632 contact22RanksSlice48 contact22RanksSlice52
private theorem contact22RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact22) 56 8 = 1360772 :=
  combineSlices (auxiliaryRankSlice contact22) 56 4 4 759810 600962 contact22RanksSlice56 contact22RanksSlice60
private theorem contact22RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact22) 64 8 = 811082 :=
  combineSlices (auxiliaryRankSlice contact22) 64 4 4 463796 347286 contact22RanksSlice64 contact22RanksSlice68
private theorem contact22RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact22) 72 8 = 420498 :=
  combineSlices (auxiliaryRankSlice contact22) 72 4 4 249962 170536 contact22RanksSlice72 contact22RanksSlice76
private theorem contact22RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact22) 80 8 = 169084 :=
  combineSlices (auxiliaryRankSlice contact22) 80 4 4 108074 61010 contact22RanksSlice80 contact22RanksSlice84
private theorem contact22RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact22) 88 8 = 36466 :=
  combineSlices (auxiliaryRankSlice contact22) 88 4 4 28060 8406 contact22RanksSlice88 contact22RanksSlice92
private theorem contact22RanksJoin96_9 : sliceWindow (auxiliaryRankSlice contact22) 96 9 = 465 :=
  combineSlices (auxiliaryRankSlice contact22) 96 4 5 465 0 contact22RanksSlice96 contact22RanksSlice100
private theorem contact22RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact22) 0 16 = 20218576 :=
  combineSlices (auxiliaryRankSlice contact22) 0 8 8 11169128 9049448 contact22RanksJoin0_8 contact22RanksJoin8_8
private theorem contact22RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact22) 16 16 = 12722896 :=
  combineSlices (auxiliaryRankSlice contact22) 16 8 8 7175528 5547368 contact22RanksJoin16_8 contact22RanksJoin24_8
private theorem contact22RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact22) 32 16 = 7181412 :=
  combineSlices (auxiliaryRankSlice contact22) 32 8 8 4164138 3017274 contact22RanksJoin32_8 contact22RanksJoin40_8
private theorem contact22RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact22) 48 16 = 3450206 :=
  combineSlices (auxiliaryRankSlice contact22) 48 8 8 2089434 1360772 contact22RanksJoin48_8 contact22RanksJoin56_8
private theorem contact22RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact22) 64 16 = 1231580 :=
  combineSlices (auxiliaryRankSlice contact22) 64 8 8 811082 420498 contact22RanksJoin64_8 contact22RanksJoin72_8
private theorem contact22RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact22) 80 16 = 205550 :=
  combineSlices (auxiliaryRankSlice contact22) 80 8 8 169084 36466 contact22RanksJoin80_8 contact22RanksJoin88_8
private theorem contact22RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact22) 0 32 = 32941472 :=
  combineSlices (auxiliaryRankSlice contact22) 0 16 16 20218576 12722896 contact22RanksJoin0_16 contact22RanksJoin16_16
private theorem contact22RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact22) 32 32 = 10631618 :=
  combineSlices (auxiliaryRankSlice contact22) 32 16 16 7181412 3450206 contact22RanksJoin32_16 contact22RanksJoin48_16
private theorem contact22RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact22) 64 32 = 1437130 :=
  combineSlices (auxiliaryRankSlice contact22) 64 16 16 1231580 205550 contact22RanksJoin64_16 contact22RanksJoin80_16
private theorem contact22RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact22) 0 64 = 43573090 :=
  combineSlices (auxiliaryRankSlice contact22) 0 32 32 32941472 10631618 contact22RanksJoin0_32 contact22RanksJoin32_32
private theorem contact22RanksJoin64_41 : sliceWindow (auxiliaryRankSlice contact22) 64 41 = 1437595 :=
  combineSlices (auxiliaryRankSlice contact22) 64 32 9 1437130 465 contact22RanksJoin64_32 contact22RanksJoin96_9
private theorem contact22RanksJoin0_105 : sliceWindow (auxiliaryRankSlice contact22) 0 105 = 45010685 :=
  combineSlices (auxiliaryRankSlice contact22) 0 64 41 43573090 1437595 contact22RanksJoin0_64 contact22RanksJoin64_41
theorem contact22_margin : sourceMargin contact22 :=
  margin_of_checked_counts contact22 105 156953335463893 14788763528251 610133261 45010685 rfl contact22OrdinaryColumns contact22ColumnsJoin0_105 contact22OrdinaryRanks contact22RanksJoin0_105 (by decide +kernel)

private theorem contact24OrdinaryColumns : ordinaryColumnCount contact24 = 165576334565093 := by decide +kernel
private theorem contact24ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact24) 0 4 = 1369770771620 :=
  contactColumnsWindow_fast contact24 0 4 1369770771620 (by decide +kernel)
private theorem contact24ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact24) 4 4 = 1264227720260 :=
  contactColumnsWindow_fast contact24 4 4 1264227720260 (by decide +kernel)
private theorem contact24ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact24) 8 4 = 1162936540900 :=
  contactColumnsWindow_fast contact24 8 4 1162936540900 (by decide +kernel)
private theorem contact24ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact24) 12 4 = 1065915456724 :=
  contactColumnsWindow_fast contact24 12 4 1065915456724 (by decide +kernel)
private theorem contact24ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact24) 16 4 = 973164353345 :=
  contactColumnsWindow_fast contact24 16 4 973164353345 (by decide +kernel)
private theorem contact24ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact24) 20 4 = 884667677428 :=
  contactColumnsWindow_fast contact24 20 4 884667677428 (by decide +kernel)
private theorem contact24ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact24) 24 4 = 800424519224 :=
  contactColumnsWindow_fast contact24 24 4 800424519224 (by decide +kernel)
private theorem contact24ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact24) 28 4 = 720436205140 :=
  contactColumnsWindow_fast contact24 28 4 720436205140 (by decide +kernel)
private theorem contact24ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact24) 32 4 = 644722826800 :=
  contactColumnsWindow_fast contact24 32 4 644722826800 (by decide +kernel)
private theorem contact24ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact24) 36 4 = 573279530447 :=
  contactColumnsWindow_fast contact24 36 4 573279530447 (by decide +kernel)
private theorem contact24ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact24) 40 4 = 506091638716 :=
  contactColumnsWindow_fast contact24 40 4 506091638716 (by decide +kernel)
private theorem contact24ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact24) 44 4 = 443157081992 :=
  contactColumnsWindow_fast contact24 44 4 443157081992 (by decide +kernel)
private theorem contact24ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact24) 48 4 = 384478126174 :=
  contactColumnsWindow_fast contact24 48 4 384478126174 (by decide +kernel)
private theorem contact24ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact24) 52 4 = 330076256524 :=
  contactColumnsWindow_fast contact24 52 4 330076256524 (by decide +kernel)
private theorem contact24ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact24) 56 4 = 279941764109 :=
  contactColumnsWindow_fast contact24 56 4 279941764109 (by decide +kernel)
private theorem contact24ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact24) 60 4 = 234062656564 :=
  contactColumnsWindow_fast contact24 60 4 234062656564 (by decide +kernel)
private theorem contact24ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact24) 64 4 = 192436782420 :=
  contactColumnsWindow_fast contact24 64 4 192436782420 (by decide +kernel)
private theorem contact24ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact24) 68 4 = 155067383962 :=
  contactColumnsWindow_fast contact24 68 4 155067383962 (by decide +kernel)
private theorem contact24ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact24) 72 4 = 121976742808 :=
  contactColumnsWindow_fast contact24 72 4 121976742808 (by decide +kernel)
private theorem contact24ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact24) 76 4 = 93151091172 :=
  contactColumnsWindow_fast contact24 76 4 93151091172 (by decide +kernel)
private theorem contact24ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact24) 80 4 = 68580730972 :=
  contactColumnsWindow_fast contact24 80 4 68580730972 (by decide +kernel)
private theorem contact24ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact24) 84 4 = 48260796523 :=
  contactColumnsWindow_fast contact24 84 4 48260796523 (by decide +kernel)
private theorem contact24ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact24) 88 4 = 32131568247 :=
  contactColumnsWindow_fast contact24 88 4 32131568247 (by decide +kernel)
private theorem contact24ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact24) 92 4 = 19990031393 :=
  contactColumnsWindow_fast contact24 92 4 19990031393 (by decide +kernel)
private theorem contact24ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact24) 96 3 = 9195656015 :=
  contactColumnsWindow_fast contact24 96 3 9195656015 (by decide +kernel)
private theorem contact24ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact24) 0 8 = 2633998491880 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 4 4 1369770771620 1264227720260 contact24ColumnsSlice0 contact24ColumnsSlice4
private theorem contact24ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact24) 8 8 = 2228851997624 :=
  combineSlices (auxiliaryColumnSlice contact24) 8 4 4 1162936540900 1065915456724 contact24ColumnsSlice8 contact24ColumnsSlice12
private theorem contact24ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact24) 16 8 = 1857832030773 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 4 4 973164353345 884667677428 contact24ColumnsSlice16 contact24ColumnsSlice20
private theorem contact24ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact24) 24 8 = 1520860724364 :=
  combineSlices (auxiliaryColumnSlice contact24) 24 4 4 800424519224 720436205140 contact24ColumnsSlice24 contact24ColumnsSlice28
private theorem contact24ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact24) 32 8 = 1218002357247 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 4 4 644722826800 573279530447 contact24ColumnsSlice32 contact24ColumnsSlice36
private theorem contact24ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact24) 40 8 = 949248720708 :=
  combineSlices (auxiliaryColumnSlice contact24) 40 4 4 506091638716 443157081992 contact24ColumnsSlice40 contact24ColumnsSlice44
private theorem contact24ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact24) 48 8 = 714554382698 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 4 4 384478126174 330076256524 contact24ColumnsSlice48 contact24ColumnsSlice52
private theorem contact24ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact24) 56 8 = 514004420673 :=
  combineSlices (auxiliaryColumnSlice contact24) 56 4 4 279941764109 234062656564 contact24ColumnsSlice56 contact24ColumnsSlice60
private theorem contact24ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact24) 64 8 = 347504166382 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 4 4 192436782420 155067383962 contact24ColumnsSlice64 contact24ColumnsSlice68
private theorem contact24ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact24) 72 8 = 215127833980 :=
  combineSlices (auxiliaryColumnSlice contact24) 72 4 4 121976742808 93151091172 contact24ColumnsSlice72 contact24ColumnsSlice76
private theorem contact24ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact24) 80 8 = 116841527495 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 4 4 68580730972 48260796523 contact24ColumnsSlice80 contact24ColumnsSlice84
private theorem contact24ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact24) 88 8 = 52121599640 :=
  combineSlices (auxiliaryColumnSlice contact24) 88 4 4 32131568247 19990031393 contact24ColumnsSlice88 contact24ColumnsSlice92
private theorem contact24ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact24) 0 16 = 4862850489504 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 8 8 2633998491880 2228851997624 contact24ColumnsJoin0_8 contact24ColumnsJoin8_8
private theorem contact24ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact24) 16 16 = 3378692755137 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 8 8 1857832030773 1520860724364 contact24ColumnsJoin16_8 contact24ColumnsJoin24_8
private theorem contact24ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact24) 32 16 = 2167251077955 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 8 8 1218002357247 949248720708 contact24ColumnsJoin32_8 contact24ColumnsJoin40_8
private theorem contact24ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact24) 48 16 = 1228558803371 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 8 8 714554382698 514004420673 contact24ColumnsJoin48_8 contact24ColumnsJoin56_8
private theorem contact24ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact24) 64 16 = 562632000362 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 8 8 347504166382 215127833980 contact24ColumnsJoin64_8 contact24ColumnsJoin72_8
private theorem contact24ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact24) 80 16 = 168963127135 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 8 8 116841527495 52121599640 contact24ColumnsJoin80_8 contact24ColumnsJoin88_8
private theorem contact24ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact24) 0 32 = 8241543244641 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 16 16 4862850489504 3378692755137 contact24ColumnsJoin0_16 contact24ColumnsJoin16_16
private theorem contact24ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact24) 32 32 = 3395809881326 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 16 16 2167251077955 1228558803371 contact24ColumnsJoin32_16 contact24ColumnsJoin48_16
private theorem contact24ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact24) 64 32 = 731595127497 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 16 16 562632000362 168963127135 contact24ColumnsJoin64_16 contact24ColumnsJoin80_16
private theorem contact24ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact24) 0 64 = 11637353125967 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 32 32 8241543244641 3395809881326 contact24ColumnsJoin0_32 contact24ColumnsJoin32_32
private theorem contact24ColumnsJoin64_35 : sliceWindow (auxiliaryColumnSlice contact24) 64 35 = 740790783512 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 32 3 731595127497 9195656015 contact24ColumnsJoin64_32 contact24ColumnsSlice96
private theorem contact24ColumnsJoin0_99 : sliceWindow (auxiliaryColumnSlice contact24) 0 99 = 12378143909479 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 64 35 11637353125967 740790783512 contact24ColumnsJoin0_64 contact24ColumnsJoin64_35
private theorem contact24OrdinaryRanks : ordinaryRankBound contact24 = 640997733 := by decide +kernel
private theorem contact24RanksSlice0 : sliceWindow (auxiliaryRankSlice contact24) 0 4 = 5128436 :=
  contactRankWindow_of_rec contact24 0 4 5128436 (by decide +kernel)
private theorem contact24RanksSlice4 : sliceWindow (auxiliaryRankSlice contact24) 4 4 = 4616916 :=
  contactRankWindow_of_rec contact24 4 4 4616916 (by decide +kernel)
private theorem contact24RanksSlice8 : sliceWindow (auxiliaryRankSlice contact24) 8 4 = 4134836 :=
  contactRankWindow_of_rec contact24 8 4 4134836 (by decide +kernel)
private theorem contact24RanksSlice12 : sliceWindow (auxiliaryRankSlice contact24) 12 4 = 3682196 :=
  contactRankWindow_of_rec contact24 12 4 3682196 (by decide +kernel)
private theorem contact24RanksSlice16 : sliceWindow (auxiliaryRankSlice contact24) 16 4 = 3258996 :=
  contactRankWindow_of_rec contact24 16 4 3258996 (by decide +kernel)
private theorem contact24RanksSlice20 : sliceWindow (auxiliaryRankSlice contact24) 20 4 = 2865236 :=
  contactRankWindow_of_rec contact24 20 4 2865236 (by decide +kernel)
private theorem contact24RanksSlice24 : sliceWindow (auxiliaryRankSlice contact24) 24 4 = 2500916 :=
  contactRankWindow_of_rec contact24 24 4 2500916 (by decide +kernel)
private theorem contact24RanksSlice28 : sliceWindow (auxiliaryRankSlice contact24) 28 4 = 2166036 :=
  contactRankWindow_of_rec contact24 28 4 2166036 (by decide +kernel)
private theorem contact24RanksSlice32 : sliceWindow (auxiliaryRankSlice contact24) 32 4 = 1860314 :=
  contactRankWindow_of_rec contact24 32 4 1860314 (by decide +kernel)
private theorem contact24RanksSlice36 : sliceWindow (auxiliaryRankSlice contact24) 36 4 = 1582925 :=
  contactRankWindow_of_rec contact24 36 4 1582925 (by decide +kernel)
private theorem contact24RanksSlice40 : sliceWindow (auxiliaryRankSlice contact24) 40 4 = 1332762 :=
  contactRankWindow_of_rec contact24 40 4 1332762 (by decide +kernel)
private theorem contact24RanksSlice44 : sliceWindow (auxiliaryRankSlice contact24) 44 4 = 1108578 :=
  contactRankWindow_of_rec contact24 44 4 1108578 (by decide +kernel)
private theorem contact24RanksSlice48 : sliceWindow (auxiliaryRankSlice contact24) 48 4 = 909121 :=
  contactRankWindow_of_rec contact24 48 4 909121 (by decide +kernel)
private theorem contact24RanksSlice52 : sliceWindow (auxiliaryRankSlice contact24) 52 4 = 733282 :=
  contactRankWindow_of_rec contact24 52 4 733282 (by decide +kernel)
private theorem contact24RanksSlice56 : sliceWindow (auxiliaryRankSlice contact24) 56 4 = 579722 :=
  contactRankWindow_of_rec contact24 56 4 579722 (by decide +kernel)
private theorem contact24RanksSlice60 : sliceWindow (auxiliaryRankSlice contact24) 60 4 = 447189 :=
  contactRankWindow_of_rec contact24 60 4 447189 (by decide +kernel)
private theorem contact24RanksSlice64 : sliceWindow (auxiliaryRankSlice contact24) 64 4 = 334666 :=
  contactRankWindow_of_rec contact24 64 4 334666 (by decide +kernel)
private theorem contact24RanksSlice68 : sliceWindow (auxiliaryRankSlice contact24) 68 4 = 240722 :=
  contactRankWindow_of_rec contact24 68 4 240722 (by decide +kernel)
private theorem contact24RanksSlice72 : sliceWindow (auxiliaryRankSlice contact24) 72 4 = 164105 :=
  contactRankWindow_of_rec contact24 72 4 164105 (by decide +kernel)
private theorem contact24RanksSlice76 : sliceWindow (auxiliaryRankSlice contact24) 76 4 = 103890 :=
  contactRankWindow_of_rec contact24 76 4 103890 (by decide +kernel)
private theorem contact24RanksSlice80 : sliceWindow (auxiliaryRankSlice contact24) 80 4 = 58554 :=
  contactRankWindow_of_rec contact24 80 4 58554 (by decide +kernel)
private theorem contact24RanksSlice84 : sliceWindow (auxiliaryRankSlice contact24) 84 4 = 26845 :=
  contactRankWindow_of_rec contact24 84 4 26845 (by decide +kernel)
private theorem contact24RanksSlice88 : sliceWindow (auxiliaryRankSlice contact24) 88 4 = 7990 :=
  contactRankWindow_of_rec contact24 88 4 7990 (by decide +kernel)
private theorem contact24RanksSlice92 : sliceWindow (auxiliaryRankSlice contact24) 92 4 = 439 :=
  contactRankWindow_of_rec contact24 92 4 439 (by decide +kernel)
private theorem contact24RanksSlice96 : sliceWindow (auxiliaryRankSlice contact24) 96 3 = 0 :=
  contactRankWindow_of_rec contact24 96 3 0 (by decide +kernel)
private theorem contact24RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact24) 0 8 = 9745352 :=
  combineSlices (auxiliaryRankSlice contact24) 0 4 4 5128436 4616916 contact24RanksSlice0 contact24RanksSlice4
private theorem contact24RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact24) 8 8 = 7817032 :=
  combineSlices (auxiliaryRankSlice contact24) 8 4 4 4134836 3682196 contact24RanksSlice8 contact24RanksSlice12
private theorem contact24RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact24) 16 8 = 6124232 :=
  combineSlices (auxiliaryRankSlice contact24) 16 4 4 3258996 2865236 contact24RanksSlice16 contact24RanksSlice20
private theorem contact24RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact24) 24 8 = 4666952 :=
  combineSlices (auxiliaryRankSlice contact24) 24 4 4 2500916 2166036 contact24RanksSlice24 contact24RanksSlice28
private theorem contact24RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact24) 32 8 = 3443239 :=
  combineSlices (auxiliaryRankSlice contact24) 32 4 4 1860314 1582925 contact24RanksSlice32 contact24RanksSlice36
private theorem contact24RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact24) 40 8 = 2441340 :=
  combineSlices (auxiliaryRankSlice contact24) 40 4 4 1332762 1108578 contact24RanksSlice40 contact24RanksSlice44
private theorem contact24RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact24) 48 8 = 1642403 :=
  combineSlices (auxiliaryRankSlice contact24) 48 4 4 909121 733282 contact24RanksSlice48 contact24RanksSlice52
private theorem contact24RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact24) 56 8 = 1026911 :=
  combineSlices (auxiliaryRankSlice contact24) 56 4 4 579722 447189 contact24RanksSlice56 contact24RanksSlice60
private theorem contact24RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact24) 64 8 = 575388 :=
  combineSlices (auxiliaryRankSlice contact24) 64 4 4 334666 240722 contact24RanksSlice64 contact24RanksSlice68
private theorem contact24RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact24) 72 8 = 267995 :=
  combineSlices (auxiliaryRankSlice contact24) 72 4 4 164105 103890 contact24RanksSlice72 contact24RanksSlice76
private theorem contact24RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact24) 80 8 = 85399 :=
  combineSlices (auxiliaryRankSlice contact24) 80 4 4 58554 26845 contact24RanksSlice80 contact24RanksSlice84
private theorem contact24RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact24) 88 8 = 8429 :=
  combineSlices (auxiliaryRankSlice contact24) 88 4 4 7990 439 contact24RanksSlice88 contact24RanksSlice92
private theorem contact24RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact24) 0 16 = 17562384 :=
  combineSlices (auxiliaryRankSlice contact24) 0 8 8 9745352 7817032 contact24RanksJoin0_8 contact24RanksJoin8_8
private theorem contact24RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact24) 16 16 = 10791184 :=
  combineSlices (auxiliaryRankSlice contact24) 16 8 8 6124232 4666952 contact24RanksJoin16_8 contact24RanksJoin24_8
private theorem contact24RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact24) 32 16 = 5884579 :=
  combineSlices (auxiliaryRankSlice contact24) 32 8 8 3443239 2441340 contact24RanksJoin32_8 contact24RanksJoin40_8
private theorem contact24RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact24) 48 16 = 2669314 :=
  combineSlices (auxiliaryRankSlice contact24) 48 8 8 1642403 1026911 contact24RanksJoin48_8 contact24RanksJoin56_8
private theorem contact24RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact24) 64 16 = 843383 :=
  combineSlices (auxiliaryRankSlice contact24) 64 8 8 575388 267995 contact24RanksJoin64_8 contact24RanksJoin72_8
private theorem contact24RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact24) 80 16 = 93828 :=
  combineSlices (auxiliaryRankSlice contact24) 80 8 8 85399 8429 contact24RanksJoin80_8 contact24RanksJoin88_8
private theorem contact24RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact24) 0 32 = 28353568 :=
  combineSlices (auxiliaryRankSlice contact24) 0 16 16 17562384 10791184 contact24RanksJoin0_16 contact24RanksJoin16_16
private theorem contact24RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact24) 32 32 = 8553893 :=
  combineSlices (auxiliaryRankSlice contact24) 32 16 16 5884579 2669314 contact24RanksJoin32_16 contact24RanksJoin48_16
private theorem contact24RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact24) 64 32 = 937211 :=
  combineSlices (auxiliaryRankSlice contact24) 64 16 16 843383 93828 contact24RanksJoin64_16 contact24RanksJoin80_16
private theorem contact24RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact24) 0 64 = 36907461 :=
  combineSlices (auxiliaryRankSlice contact24) 0 32 32 28353568 8553893 contact24RanksJoin0_32 contact24RanksJoin32_32
private theorem contact24RanksJoin64_35 : sliceWindow (auxiliaryRankSlice contact24) 64 35 = 937211 :=
  combineSlices (auxiliaryRankSlice contact24) 64 32 3 937211 0 contact24RanksJoin64_32 contact24RanksSlice96
private theorem contact24RanksJoin0_99 : sliceWindow (auxiliaryRankSlice contact24) 0 99 = 37844672 :=
  combineSlices (auxiliaryRankSlice contact24) 0 64 35 36907461 937211 contact24RanksJoin0_64 contact24RanksJoin64_35
theorem contact24_margin : sourceMargin contact24 :=
  margin_of_checked_counts contact24 99 165576334565093 12378143909479 640997733 37844672 rfl contact24OrdinaryColumns contact24ColumnsJoin0_99 contact24OrdinaryRanks contact24RanksJoin0_99 (by decide +kernel)

private theorem contact26OrdinaryColumns : ordinaryColumnCount contact26 = 163023276300428 := by decide +kernel
private theorem contact26ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact26) 0 4 = 1856094140180 :=
  contactColumnsWindow_fast contact26 0 4 1856094140180 (by decide +kernel)
private theorem contact26ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact26) 4 4 = 1724608759140 :=
  contactColumnsWindow_fast contact26 4 4 1724608759140 (by decide +kernel)
private theorem contact26ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact26) 8 4 = 1597976058100 :=
  contactColumnsWindow_fast contact26 8 4 1597976058100 (by decide +kernel)
private theorem contact26ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact26) 12 4 = 1476208920857 :=
  contactColumnsWindow_fast contact26 12 4 1476208920857 (by decide +kernel)
private theorem contact26ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact26) 16 4 = 1359322891704 :=
  contactColumnsWindow_fast contact26 16 4 1359322891704 (by decide +kernel)
private theorem contact26ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact26) 20 4 = 1247292346614 :=
  contactColumnsWindow_fast contact26 20 4 1247292346614 (by decide +kernel)
private theorem contact26ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact26) 24 4 = 1140117051158 :=
  contactColumnsWindow_fast contact26 24 4 1140117051158 (by decide +kernel)
private theorem contact26ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact26) 28 4 = 1037796941140 :=
  contactColumnsWindow_fast contact26 28 4 1037796941140 (by decide +kernel)
private theorem contact26ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact26) 32 4 = 940347479474 :=
  contactColumnsWindow_fast contact26 32 4 940347479474 (by decide +kernel)
private theorem contact26ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact26) 36 4 = 847780301190 :=
  contactColumnsWindow_fast contact26 36 4 847780301190 (by decide +kernel)
private theorem contact26ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact26) 40 4 = 760069647816 :=
  contactColumnsWindow_fast contact26 40 4 760069647816 (by decide +kernel)
private theorem contact26ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact26) 44 4 = 677213853909 :=
  contactColumnsWindow_fast contact26 44 4 677213853909 (by decide +kernel)
private theorem contact26ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact26) 48 4 = 599213640610 :=
  contactColumnsWindow_fast contact26 48 4 599213640610 (by decide +kernel)
private theorem contact26ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact26) 52 4 = 526087671884 :=
  contactColumnsWindow_fast contact26 52 4 526087671884 (by decide +kernel)
private theorem contact26ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact26) 56 4 = 457840329576 :=
  contactColumnsWindow_fast contact26 56 4 457840329576 (by decide +kernel)
private theorem contact26ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact26) 60 4 = 394449567918 :=
  contactColumnsWindow_fast contact26 60 4 394449567918 (by decide +kernel)
private theorem contact26ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact26) 64 4 = 335913366978 :=
  contactColumnsWindow_fast contact26 64 4 335913366978 (by decide +kernel)
private theorem contact26ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact26) 68 4 = 282232958980 :=
  contactColumnsWindow_fast contact26 68 4 282232958980 (by decide +kernel)
private theorem contact26ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact26) 72 4 = 233430499055 :=
  contactColumnsWindow_fast contact26 72 4 233430499055 (by decide +kernel)
private theorem contact26ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact26) 76 4 = 189503048776 :=
  contactColumnsWindow_fast contact26 76 4 189503048776 (by decide +kernel)
private theorem contact26ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact26) 80 4 = 150432106920 :=
  contactColumnsWindow_fast contact26 80 4 150432106920 (by decide +kernel)
private theorem contact26ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact26) 84 4 = 116215498947 :=
  contactColumnsWindow_fast contact26 84 4 116215498947 (by decide +kernel)
private theorem contact26ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact26) 88 4 = 86855169469 :=
  contactColumnsWindow_fast contact26 88 4 86855169469 (by decide +kernel)
private theorem contact26ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact26) 92 4 = 62371950282 :=
  contactColumnsWindow_fast contact26 92 4 62371950282 (by decide +kernel)
private theorem contact26ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact26) 96 4 = 42680456370 :=
  contactColumnsWindow_fast contact26 96 4 42680456370 (by decide +kernel)
private theorem contact26ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact26) 100 4 = 27525195677 :=
  contactColumnsWindow_fast contact26 100 4 27525195677 (by decide +kernel)
private theorem contact26ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact26) 104 2 = 9390041151 :=
  contactColumnsWindow_fast contact26 104 2 9390041151 (by decide +kernel)
private theorem contact26ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact26) 0 8 = 3580702899320 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 4 4 1856094140180 1724608759140 contact26ColumnsSlice0 contact26ColumnsSlice4
private theorem contact26ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact26) 8 8 = 3074184978957 :=
  combineSlices (auxiliaryColumnSlice contact26) 8 4 4 1597976058100 1476208920857 contact26ColumnsSlice8 contact26ColumnsSlice12
private theorem contact26ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact26) 16 8 = 2606615238318 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 4 4 1359322891704 1247292346614 contact26ColumnsSlice16 contact26ColumnsSlice20
private theorem contact26ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact26) 24 8 = 2177913992298 :=
  combineSlices (auxiliaryColumnSlice contact26) 24 4 4 1140117051158 1037796941140 contact26ColumnsSlice24 contact26ColumnsSlice28
private theorem contact26ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact26) 32 8 = 1788127780664 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 4 4 940347479474 847780301190 contact26ColumnsSlice32 contact26ColumnsSlice36
private theorem contact26ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact26) 40 8 = 1437283501725 :=
  combineSlices (auxiliaryColumnSlice contact26) 40 4 4 760069647816 677213853909 contact26ColumnsSlice40 contact26ColumnsSlice44
private theorem contact26ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact26) 48 8 = 1125301312494 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 4 4 599213640610 526087671884 contact26ColumnsSlice48 contact26ColumnsSlice52
private theorem contact26ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact26) 56 8 = 852289897494 :=
  combineSlices (auxiliaryColumnSlice contact26) 56 4 4 457840329576 394449567918 contact26ColumnsSlice56 contact26ColumnsSlice60
private theorem contact26ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact26) 64 8 = 618146325958 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 4 4 335913366978 282232958980 contact26ColumnsSlice64 contact26ColumnsSlice68
private theorem contact26ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact26) 72 8 = 422933547831 :=
  combineSlices (auxiliaryColumnSlice contact26) 72 4 4 233430499055 189503048776 contact26ColumnsSlice72 contact26ColumnsSlice76
private theorem contact26ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact26) 80 8 = 266647605867 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 4 4 150432106920 116215498947 contact26ColumnsSlice80 contact26ColumnsSlice84
private theorem contact26ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact26) 88 8 = 149227119751 :=
  combineSlices (auxiliaryColumnSlice contact26) 88 4 4 86855169469 62371950282 contact26ColumnsSlice88 contact26ColumnsSlice92
private theorem contact26ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact26) 96 8 = 70205652047 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 4 4 42680456370 27525195677 contact26ColumnsSlice96 contact26ColumnsSlice100
private theorem contact26ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact26) 0 16 = 6654887878277 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 8 8 3580702899320 3074184978957 contact26ColumnsJoin0_8 contact26ColumnsJoin8_8
private theorem contact26ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact26) 16 16 = 4784529230616 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 8 8 2606615238318 2177913992298 contact26ColumnsJoin16_8 contact26ColumnsJoin24_8
private theorem contact26ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact26) 32 16 = 3225411282389 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 8 8 1788127780664 1437283501725 contact26ColumnsJoin32_8 contact26ColumnsJoin40_8
private theorem contact26ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact26) 48 16 = 1977591209988 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 8 8 1125301312494 852289897494 contact26ColumnsJoin48_8 contact26ColumnsJoin56_8
private theorem contact26ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact26) 64 16 = 1041079873789 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 8 8 618146325958 422933547831 contact26ColumnsJoin64_8 contact26ColumnsJoin72_8
private theorem contact26ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact26) 80 16 = 415874725618 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 8 8 266647605867 149227119751 contact26ColumnsJoin80_8 contact26ColumnsJoin88_8
private theorem contact26ColumnsJoin96_10 : sliceWindow (auxiliaryColumnSlice contact26) 96 10 = 79595693198 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 8 2 70205652047 9390041151 contact26ColumnsJoin96_8 contact26ColumnsSlice104
private theorem contact26ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact26) 0 32 = 11439417108893 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 16 16 6654887878277 4784529230616 contact26ColumnsJoin0_16 contact26ColumnsJoin16_16
private theorem contact26ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact26) 32 32 = 5203002492377 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 16 16 3225411282389 1977591209988 contact26ColumnsJoin32_16 contact26ColumnsJoin48_16
private theorem contact26ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact26) 64 32 = 1456954599407 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 16 16 1041079873789 415874725618 contact26ColumnsJoin64_16 contact26ColumnsJoin80_16
private theorem contact26ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact26) 0 64 = 16642419601270 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 32 32 11439417108893 5203002492377 contact26ColumnsJoin0_32 contact26ColumnsJoin32_32
private theorem contact26ColumnsJoin64_42 : sliceWindow (auxiliaryColumnSlice contact26) 64 42 = 1536550292605 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 32 10 1456954599407 79595693198 contact26ColumnsJoin64_32 contact26ColumnsJoin96_10
private theorem contact26ColumnsJoin0_106 : sliceWindow (auxiliaryColumnSlice contact26) 0 106 = 18178969893875 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 64 42 16642419601270 1536550292605 contact26ColumnsJoin0_64 contact26ColumnsJoin64_42
private theorem contact26OrdinaryRanks : ordinaryRankBound contact26 = 635890724 := by decide +kernel
private theorem contact26RanksSlice0 : sliceWindow (auxiliaryRankSlice contact26) 0 4 = 6943806 :=
  contactRankWindow_of_rec contact26 0 4 6943806 (by decide +kernel)
private theorem contact26RanksSlice4 : sliceWindow (auxiliaryRankSlice contact26) 4 4 = 6305406 :=
  contactRankWindow_of_rec contact26 4 4 6305406 (by decide +kernel)
private theorem contact26RanksSlice8 : sliceWindow (auxiliaryRankSlice contact26) 8 4 = 5700606 :=
  contactRankWindow_of_rec contact26 8 4 5700606 (by decide +kernel)
private theorem contact26RanksSlice12 : sliceWindow (auxiliaryRankSlice contact26) 12 4 = 5129406 :=
  contactRankWindow_of_rec contact26 12 4 5129406 (by decide +kernel)
private theorem contact26RanksSlice16 : sliceWindow (auxiliaryRankSlice contact26) 16 4 = 4591806 :=
  contactRankWindow_of_rec contact26 16 4 4591806 (by decide +kernel)
private theorem contact26RanksSlice20 : sliceWindow (auxiliaryRankSlice contact26) 20 4 = 4087806 :=
  contactRankWindow_of_rec contact26 20 4 4087806 (by decide +kernel)
private theorem contact26RanksSlice24 : sliceWindow (auxiliaryRankSlice contact26) 24 4 = 3617406 :=
  contactRankWindow_of_rec contact26 24 4 3617406 (by decide +kernel)
private theorem contact26RanksSlice28 : sliceWindow (auxiliaryRankSlice contact26) 28 4 = 3180606 :=
  contactRankWindow_of_rec contact26 28 4 3180606 (by decide +kernel)
private theorem contact26RanksSlice32 : sliceWindow (auxiliaryRankSlice contact26) 32 4 = 2777385 :=
  contactRankWindow_of_rec contact26 32 4 2777385 (by decide +kernel)
private theorem contact26RanksSlice36 : sliceWindow (auxiliaryRankSlice contact26) 36 4 = 2407297 :=
  contactRankWindow_of_rec contact26 36 4 2407297 (by decide +kernel)
private theorem contact26RanksSlice40 : sliceWindow (auxiliaryRankSlice contact26) 40 4 = 2069431 :=
  contactRankWindow_of_rec contact26 40 4 2069431 (by decide +kernel)
private theorem contact26RanksSlice44 : sliceWindow (auxiliaryRankSlice contact26) 44 4 = 1762634 :=
  contactRankWindow_of_rec contact26 44 4 1762634 (by decide +kernel)
private theorem contact26RanksSlice48 : sliceWindow (auxiliaryRankSlice contact26) 48 4 = 1485665 :=
  contactRankWindow_of_rec contact26 48 4 1485665 (by decide +kernel)
private theorem contact26RanksSlice52 : sliceWindow (auxiliaryRankSlice contact26) 52 4 = 1237163 :=
  contactRankWindow_of_rec contact26 52 4 1237163 (by decide +kernel)
private theorem contact26RanksSlice56 : sliceWindow (auxiliaryRankSlice contact26) 56 4 = 1015774 :=
  contactRankWindow_of_rec contact26 56 4 1015774 (by decide +kernel)
private theorem contact26RanksSlice60 : sliceWindow (auxiliaryRankSlice contact26) 60 4 = 820353 :=
  contactRankWindow_of_rec contact26 60 4 820353 (by decide +kernel)
private theorem contact26RanksSlice64 : sliceWindow (auxiliaryRankSlice contact26) 64 4 = 649439 :=
  contactRankWindow_of_rec contact26 64 4 649439 (by decide +kernel)
private theorem contact26RanksSlice68 : sliceWindow (auxiliaryRankSlice contact26) 68 4 = 501682 :=
  contactRankWindow_of_rec contact26 68 4 501682 (by decide +kernel)
private theorem contact26RanksSlice72 : sliceWindow (auxiliaryRankSlice contact26) 72 4 = 376033 :=
  contactRankWindow_of_rec contact26 72 4 376033 (by decide +kernel)
private theorem contact26RanksSlice76 : sliceWindow (auxiliaryRankSlice contact26) 76 4 = 270931 :=
  contactRankWindow_of_rec contact26 76 4 270931 (by decide +kernel)
private theorem contact26RanksSlice80 : sliceWindow (auxiliaryRankSlice contact26) 80 4 = 185030 :=
  contactRankWindow_of_rec contact26 80 4 185030 (by decide +kernel)
private theorem contact26RanksSlice84 : sliceWindow (auxiliaryRankSlice contact26) 84 4 = 117377 :=
  contactRankWindow_of_rec contact26 84 4 117377 (by decide +kernel)
private theorem contact26RanksSlice88 : sliceWindow (auxiliaryRankSlice contact26) 88 4 = 66311 :=
  contactRankWindow_of_rec contact26 88 4 66311 (by decide +kernel)
private theorem contact26RanksSlice92 : sliceWindow (auxiliaryRankSlice contact26) 92 4 = 30490 :=
  contactRankWindow_of_rec contact26 92 4 30490 (by decide +kernel)
private theorem contact26RanksSlice96 : sliceWindow (auxiliaryRankSlice contact26) 96 4 = 9117 :=
  contactRankWindow_of_rec contact26 96 4 9117 (by decide +kernel)
private theorem contact26RanksSlice100 : sliceWindow (auxiliaryRankSlice contact26) 100 4 = 504 :=
  contactRankWindow_of_rec contact26 100 4 504 (by decide +kernel)
private theorem contact26RanksSlice104 : sliceWindow (auxiliaryRankSlice contact26) 104 2 = 0 :=
  contactRankWindow_of_rec contact26 104 2 0 (by decide +kernel)
private theorem contact26RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact26) 0 8 = 13249212 :=
  combineSlices (auxiliaryRankSlice contact26) 0 4 4 6943806 6305406 contact26RanksSlice0 contact26RanksSlice4
private theorem contact26RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact26) 8 8 = 10830012 :=
  combineSlices (auxiliaryRankSlice contact26) 8 4 4 5700606 5129406 contact26RanksSlice8 contact26RanksSlice12
private theorem contact26RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact26) 16 8 = 8679612 :=
  combineSlices (auxiliaryRankSlice contact26) 16 4 4 4591806 4087806 contact26RanksSlice16 contact26RanksSlice20
private theorem contact26RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact26) 24 8 = 6798012 :=
  combineSlices (auxiliaryRankSlice contact26) 24 4 4 3617406 3180606 contact26RanksSlice24 contact26RanksSlice28
private theorem contact26RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact26) 32 8 = 5184682 :=
  combineSlices (auxiliaryRankSlice contact26) 32 4 4 2777385 2407297 contact26RanksSlice32 contact26RanksSlice36
private theorem contact26RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact26) 40 8 = 3832065 :=
  combineSlices (auxiliaryRankSlice contact26) 40 4 4 2069431 1762634 contact26RanksSlice40 contact26RanksSlice44
private theorem contact26RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact26) 48 8 = 2722828 :=
  combineSlices (auxiliaryRankSlice contact26) 48 4 4 1485665 1237163 contact26RanksSlice48 contact26RanksSlice52
private theorem contact26RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact26) 56 8 = 1836127 :=
  combineSlices (auxiliaryRankSlice contact26) 56 4 4 1015774 820353 contact26RanksSlice56 contact26RanksSlice60
private theorem contact26RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact26) 64 8 = 1151121 :=
  combineSlices (auxiliaryRankSlice contact26) 64 4 4 649439 501682 contact26RanksSlice64 contact26RanksSlice68
private theorem contact26RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact26) 72 8 = 646964 :=
  combineSlices (auxiliaryRankSlice contact26) 72 4 4 376033 270931 contact26RanksSlice72 contact26RanksSlice76
private theorem contact26RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact26) 80 8 = 302407 :=
  combineSlices (auxiliaryRankSlice contact26) 80 4 4 185030 117377 contact26RanksSlice80 contact26RanksSlice84
private theorem contact26RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact26) 88 8 = 96801 :=
  combineSlices (auxiliaryRankSlice contact26) 88 4 4 66311 30490 contact26RanksSlice88 contact26RanksSlice92
private theorem contact26RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact26) 96 8 = 9621 :=
  combineSlices (auxiliaryRankSlice contact26) 96 4 4 9117 504 contact26RanksSlice96 contact26RanksSlice100
private theorem contact26RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact26) 0 16 = 24079224 :=
  combineSlices (auxiliaryRankSlice contact26) 0 8 8 13249212 10830012 contact26RanksJoin0_8 contact26RanksJoin8_8
private theorem contact26RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact26) 16 16 = 15477624 :=
  combineSlices (auxiliaryRankSlice contact26) 16 8 8 8679612 6798012 contact26RanksJoin16_8 contact26RanksJoin24_8
private theorem contact26RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact26) 32 16 = 9016747 :=
  combineSlices (auxiliaryRankSlice contact26) 32 8 8 5184682 3832065 contact26RanksJoin32_8 contact26RanksJoin40_8
private theorem contact26RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact26) 48 16 = 4558955 :=
  combineSlices (auxiliaryRankSlice contact26) 48 8 8 2722828 1836127 contact26RanksJoin48_8 contact26RanksJoin56_8
private theorem contact26RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact26) 64 16 = 1798085 :=
  combineSlices (auxiliaryRankSlice contact26) 64 8 8 1151121 646964 contact26RanksJoin64_8 contact26RanksJoin72_8
private theorem contact26RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact26) 80 16 = 399208 :=
  combineSlices (auxiliaryRankSlice contact26) 80 8 8 302407 96801 contact26RanksJoin80_8 contact26RanksJoin88_8
private theorem contact26RanksJoin96_10 : sliceWindow (auxiliaryRankSlice contact26) 96 10 = 9621 :=
  combineSlices (auxiliaryRankSlice contact26) 96 8 2 9621 0 contact26RanksJoin96_8 contact26RanksSlice104
private theorem contact26RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact26) 0 32 = 39556848 :=
  combineSlices (auxiliaryRankSlice contact26) 0 16 16 24079224 15477624 contact26RanksJoin0_16 contact26RanksJoin16_16
private theorem contact26RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact26) 32 32 = 13575702 :=
  combineSlices (auxiliaryRankSlice contact26) 32 16 16 9016747 4558955 contact26RanksJoin32_16 contact26RanksJoin48_16
private theorem contact26RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact26) 64 32 = 2197293 :=
  combineSlices (auxiliaryRankSlice contact26) 64 16 16 1798085 399208 contact26RanksJoin64_16 contact26RanksJoin80_16
private theorem contact26RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact26) 0 64 = 53132550 :=
  combineSlices (auxiliaryRankSlice contact26) 0 32 32 39556848 13575702 contact26RanksJoin0_32 contact26RanksJoin32_32
private theorem contact26RanksJoin64_42 : sliceWindow (auxiliaryRankSlice contact26) 64 42 = 2206914 :=
  combineSlices (auxiliaryRankSlice contact26) 64 32 10 2197293 9621 contact26RanksJoin64_32 contact26RanksJoin96_10
private theorem contact26RanksJoin0_106 : sliceWindow (auxiliaryRankSlice contact26) 0 106 = 55339464 :=
  combineSlices (auxiliaryRankSlice contact26) 0 64 42 53132550 2206914 contact26RanksJoin0_64 contact26RanksJoin64_42
theorem contact26_margin : sourceMargin contact26 :=
  margin_of_checked_counts contact26 106 163023276300428 18178969893875 635890724 55339464 rfl contact26OrdinaryColumns contact26ColumnsJoin0_106 contact26OrdinaryRanks contact26RanksJoin0_106 (by decide +kernel)

private theorem contact28OrdinaryColumns : ordinaryColumnCount contact28 = 217183075684561 := by decide +kernel
private theorem contact28ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact28) 0 4 = 898954205464 :=
  contactColumnsWindow_fast contact28 0 4 898954205464 (by decide +kernel)
private theorem contact28ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact28) 4 4 = 823745565160 :=
  contactColumnsWindow_fast contact28 4 4 823745565160 (by decide +kernel)
private theorem contact28ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact28) 8 4 = 751837402785 :=
  contactColumnsWindow_fast contact28 8 4 751837402785 (by decide +kernel)
private theorem contact28ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact28) 12 4 = 683247199908 :=
  contactColumnsWindow_fast contact28 12 4 683247199908 (by decide +kernel)
private theorem contact28ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact28) 16 4 = 617965150857 :=
  contactColumnsWindow_fast contact28 16 4 617965150857 (by decide +kernel)
private theorem contact28ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact28) 20 4 = 555985532394 :=
  contactColumnsWindow_fast contact28 20 4 555985532394 (by decide +kernel)
private theorem contact28ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact28) 24 4 = 497306893715 :=
  contactColumnsWindow_fast contact28 24 4 497306893715 (by decide +kernel)
private theorem contact28ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact28) 28 4 = 441932159493 :=
  contactColumnsWindow_fast contact28 28 4 441932159493 (by decide +kernel)
private theorem contact28ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact28) 32 4 = 389877850209 :=
  contactColumnsWindow_fast contact28 32 4 389877850209 (by decide +kernel)
private theorem contact28ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact28) 36 4 = 341132937777 :=
  contactColumnsWindow_fast contact28 36 4 341132937777 (by decide +kernel)
private theorem contact28ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact28) 40 4 = 295690751244 :=
  contactColumnsWindow_fast contact28 40 4 295690751244 (by decide +kernel)
private theorem contact28ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact28) 44 4 = 253549536419 :=
  contactColumnsWindow_fast contact28 44 4 253549536419 (by decide +kernel)
private theorem contact28ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact28) 48 4 = 214713065540 :=
  contactColumnsWindow_fast contact28 48 4 214713065540 (by decide +kernel)
private theorem contact28ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact28) 52 4 = 179197924423 :=
  contactColumnsWindow_fast contact28 52 4 179197924423 (by decide +kernel)
private theorem contact28ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact28) 56 4 = 146990523501 :=
  contactColumnsWindow_fast contact28 56 4 146990523501 (by decide +kernel)
private theorem contact28ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact28) 60 4 = 118085750946 :=
  contactColumnsWindow_fast contact28 60 4 118085750946 (by decide +kernel)
private theorem contact28ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact28) 64 4 = 92482003515 :=
  contactColumnsWindow_fast contact28 64 4 92482003515 (by decide +kernel)
private theorem contact28ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact28) 68 4 = 70184157326 :=
  contactColumnsWindow_fast contact28 68 4 70184157326 (by decide +kernel)
private theorem contact28ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact28) 72 4 = 51207785668 :=
  contactColumnsWindow_fast contact28 72 4 51207785668 (by decide +kernel)
private theorem contact28ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact28) 76 4 = 35537851400 :=
  contactColumnsWindow_fast contact28 76 4 35537851400 (by decide +kernel)
private theorem contact28ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact28) 80 4 = 23154656235 :=
  contactColumnsWindow_fast contact28 80 4 23154656235 (by decide +kernel)
private theorem contact28ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact28) 84 4 = 13928758502 :=
  contactColumnsWindow_fast contact28 84 4 13928758502 (by decide +kernel)
private theorem contact28ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact28) 88 4 = 7567151467 :=
  contactColumnsWindow_fast contact28 88 4 7567151467 (by decide +kernel)
private theorem contact28ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact28) 92 3 = 2973171413 :=
  contactColumnsWindow_fast contact28 92 3 2973171413 (by decide +kernel)
private theorem contact28ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact28) 0 8 = 1722699770624 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 4 4 898954205464 823745565160 contact28ColumnsSlice0 contact28ColumnsSlice4
private theorem contact28ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact28) 8 8 = 1435084602693 :=
  combineSlices (auxiliaryColumnSlice contact28) 8 4 4 751837402785 683247199908 contact28ColumnsSlice8 contact28ColumnsSlice12
private theorem contact28ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact28) 16 8 = 1173950683251 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 4 4 617965150857 555985532394 contact28ColumnsSlice16 contact28ColumnsSlice20
private theorem contact28ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact28) 24 8 = 939239053208 :=
  combineSlices (auxiliaryColumnSlice contact28) 24 4 4 497306893715 441932159493 contact28ColumnsSlice24 contact28ColumnsSlice28
private theorem contact28ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact28) 32 8 = 731010787986 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 4 4 389877850209 341132937777 contact28ColumnsSlice32 contact28ColumnsSlice36
private theorem contact28ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact28) 40 8 = 549240287663 :=
  combineSlices (auxiliaryColumnSlice contact28) 40 4 4 295690751244 253549536419 contact28ColumnsSlice40 contact28ColumnsSlice44
private theorem contact28ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact28) 48 8 = 393910989963 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 4 4 214713065540 179197924423 contact28ColumnsSlice48 contact28ColumnsSlice52
private theorem contact28ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact28) 56 8 = 265076274447 :=
  combineSlices (auxiliaryColumnSlice contact28) 56 4 4 146990523501 118085750946 contact28ColumnsSlice56 contact28ColumnsSlice60
private theorem contact28ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact28) 64 8 = 162666160841 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 4 4 92482003515 70184157326 contact28ColumnsSlice64 contact28ColumnsSlice68
private theorem contact28ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact28) 72 8 = 86745637068 :=
  combineSlices (auxiliaryColumnSlice contact28) 72 4 4 51207785668 35537851400 contact28ColumnsSlice72 contact28ColumnsSlice76
private theorem contact28ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact28) 80 8 = 37083414737 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 4 4 23154656235 13928758502 contact28ColumnsSlice80 contact28ColumnsSlice84
private theorem contact28ColumnsJoin88_7 : sliceWindow (auxiliaryColumnSlice contact28) 88 7 = 10540322880 :=
  combineSlices (auxiliaryColumnSlice contact28) 88 4 3 7567151467 2973171413 contact28ColumnsSlice88 contact28ColumnsSlice92
private theorem contact28ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact28) 0 16 = 3157784373317 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 8 8 1722699770624 1435084602693 contact28ColumnsJoin0_8 contact28ColumnsJoin8_8
private theorem contact28ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact28) 16 16 = 2113189736459 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 8 8 1173950683251 939239053208 contact28ColumnsJoin16_8 contact28ColumnsJoin24_8
private theorem contact28ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact28) 32 16 = 1280251075649 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 8 8 731010787986 549240287663 contact28ColumnsJoin32_8 contact28ColumnsJoin40_8
private theorem contact28ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact28) 48 16 = 658987264410 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 8 8 393910989963 265076274447 contact28ColumnsJoin48_8 contact28ColumnsJoin56_8
private theorem contact28ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact28) 64 16 = 249411797909 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 8 8 162666160841 86745637068 contact28ColumnsJoin64_8 contact28ColumnsJoin72_8
private theorem contact28ColumnsJoin80_15 : sliceWindow (auxiliaryColumnSlice contact28) 80 15 = 47623737617 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 8 7 37083414737 10540322880 contact28ColumnsJoin80_8 contact28ColumnsJoin88_7
private theorem contact28ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact28) 0 32 = 5270974109776 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 16 16 3157784373317 2113189736459 contact28ColumnsJoin0_16 contact28ColumnsJoin16_16
private theorem contact28ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact28) 32 32 = 1939238340059 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 16 16 1280251075649 658987264410 contact28ColumnsJoin32_16 contact28ColumnsJoin48_16
private theorem contact28ColumnsJoin64_31 : sliceWindow (auxiliaryColumnSlice contact28) 64 31 = 297035535526 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 16 15 249411797909 47623737617 contact28ColumnsJoin64_16 contact28ColumnsJoin80_15
private theorem contact28ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact28) 0 64 = 7210212449835 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 32 32 5270974109776 1939238340059 contact28ColumnsJoin0_32 contact28ColumnsJoin32_32
private theorem contact28ColumnsJoin0_95 : sliceWindow (auxiliaryColumnSlice contact28) 0 95 = 7507247985361 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 64 31 7210212449835 297035535526 contact28ColumnsJoin0_64 contact28ColumnsJoin64_31
private theorem contact28OrdinaryRanks : ordinaryRankBound contact28 = 834257424 := by decide +kernel
private theorem contact28RanksSlice0 : sliceWindow (auxiliaryRankSlice contact28) 0 4 = 3368194 :=
  contactRankWindow_of_rec contact28 0 4 3368194 (by decide +kernel)
private theorem contact28RanksSlice4 : sliceWindow (auxiliaryRankSlice contact28) 4 4 = 3002626 :=
  contactRankWindow_of_rec contact28 4 4 3002626 (by decide +kernel)
private theorem contact28RanksSlice8 : sliceWindow (auxiliaryRankSlice contact28) 8 4 = 2659906 :=
  contactRankWindow_of_rec contact28 8 4 2659906 (by decide +kernel)
private theorem contact28RanksSlice12 : sliceWindow (auxiliaryRankSlice contact28) 12 4 = 2340034 :=
  contactRankWindow_of_rec contact28 12 4 2340034 (by decide +kernel)
private theorem contact28RanksSlice16 : sliceWindow (auxiliaryRankSlice contact28) 16 4 = 2043010 :=
  contactRankWindow_of_rec contact28 16 4 2043010 (by decide +kernel)
private theorem contact28RanksSlice20 : sliceWindow (auxiliaryRankSlice contact28) 20 4 = 1768834 :=
  contactRankWindow_of_rec contact28 20 4 1768834 (by decide +kernel)
private theorem contact28RanksSlice24 : sliceWindow (auxiliaryRankSlice contact28) 24 4 = 1517506 :=
  contactRankWindow_of_rec contact28 24 4 1517506 (by decide +kernel)
private theorem contact28RanksSlice28 : sliceWindow (auxiliaryRankSlice contact28) 28 4 = 1289009 :=
  contactRankWindow_of_rec contact28 28 4 1289009 (by decide +kernel)
private theorem contact28RanksSlice32 : sliceWindow (auxiliaryRankSlice contact28) 32 4 = 1082981 :=
  contactRankWindow_of_rec contact28 32 4 1082981 (by decide +kernel)
private theorem contact28RanksSlice36 : sliceWindow (auxiliaryRankSlice contact28) 36 4 = 898679 :=
  contactRankWindow_of_rec contact28 36 4 898679 (by decide +kernel)
private theorem contact28RanksSlice40 : sliceWindow (auxiliaryRankSlice contact28) 40 4 = 735154 :=
  contactRankWindow_of_rec contact28 40 4 735154 (by decide +kernel)
private theorem contact28RanksSlice44 : sliceWindow (auxiliaryRankSlice contact28) 44 4 = 591381 :=
  contactRankWindow_of_rec contact28 44 4 591381 (by decide +kernel)
private theorem contact28RanksSlice48 : sliceWindow (auxiliaryRankSlice contact28) 48 4 = 466235 :=
  contactRankWindow_of_rec contact28 48 4 466235 (by decide +kernel)
private theorem contact28RanksSlice52 : sliceWindow (auxiliaryRankSlice contact28) 52 4 = 358598 :=
  contactRankWindow_of_rec contact28 52 4 358598 (by decide +kernel)
private theorem contact28RanksSlice56 : sliceWindow (auxiliaryRankSlice contact28) 56 4 = 267525 :=
  contactRankWindow_of_rec contact28 56 4 267525 (by decide +kernel)
private theorem contact28RanksSlice60 : sliceWindow (auxiliaryRankSlice contact28) 60 4 = 191807 :=
  contactRankWindow_of_rec contact28 60 4 191807 (by decide +kernel)
private theorem contact28RanksSlice64 : sliceWindow (auxiliaryRankSlice contact28) 64 4 = 130330 :=
  contactRankWindow_of_rec contact28 64 4 130330 (by decide +kernel)
private theorem contact28RanksSlice68 : sliceWindow (auxiliaryRankSlice contact28) 68 4 = 82229 :=
  contactRankWindow_of_rec contact28 68 4 82229 (by decide +kernel)
private theorem contact28RanksSlice72 : sliceWindow (auxiliaryRankSlice contact28) 72 4 = 46211 :=
  contactRankWindow_of_rec contact28 72 4 46211 (by decide +kernel)
private theorem contact28RanksSlice76 : sliceWindow (auxiliaryRankSlice contact28) 76 4 = 21166 :=
  contactRankWindow_of_rec contact28 76 4 21166 (by decide +kernel)
private theorem contact28RanksSlice80 : sliceWindow (auxiliaryRankSlice contact28) 80 4 = 6316 :=
  contactRankWindow_of_rec contact28 80 4 6316 (by decide +kernel)
private theorem contact28RanksSlice84 : sliceWindow (auxiliaryRankSlice contact28) 84 4 = 347 :=
  contactRankWindow_of_rec contact28 84 4 347 (by decide +kernel)
private theorem contact28RanksSlice88 : sliceWindow (auxiliaryRankSlice contact28) 88 7 = 0 :=
  contactRankWindow_of_rec contact28 88 7 0 (by decide +kernel)
private theorem contact28RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact28) 0 8 = 6370820 :=
  combineSlices (auxiliaryRankSlice contact28) 0 4 4 3368194 3002626 contact28RanksSlice0 contact28RanksSlice4
private theorem contact28RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact28) 8 8 = 4999940 :=
  combineSlices (auxiliaryRankSlice contact28) 8 4 4 2659906 2340034 contact28RanksSlice8 contact28RanksSlice12
private theorem contact28RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact28) 16 8 = 3811844 :=
  combineSlices (auxiliaryRankSlice contact28) 16 4 4 2043010 1768834 contact28RanksSlice16 contact28RanksSlice20
private theorem contact28RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact28) 24 8 = 2806515 :=
  combineSlices (auxiliaryRankSlice contact28) 24 4 4 1517506 1289009 contact28RanksSlice24 contact28RanksSlice28
private theorem contact28RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact28) 32 8 = 1981660 :=
  combineSlices (auxiliaryRankSlice contact28) 32 4 4 1082981 898679 contact28RanksSlice32 contact28RanksSlice36
private theorem contact28RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact28) 40 8 = 1326535 :=
  combineSlices (auxiliaryRankSlice contact28) 40 4 4 735154 591381 contact28RanksSlice40 contact28RanksSlice44
private theorem contact28RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact28) 48 8 = 824833 :=
  combineSlices (auxiliaryRankSlice contact28) 48 4 4 466235 358598 contact28RanksSlice48 contact28RanksSlice52
private theorem contact28RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact28) 56 8 = 459332 :=
  combineSlices (auxiliaryRankSlice contact28) 56 4 4 267525 191807 contact28RanksSlice56 contact28RanksSlice60
private theorem contact28RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact28) 64 8 = 212559 :=
  combineSlices (auxiliaryRankSlice contact28) 64 4 4 130330 82229 contact28RanksSlice64 contact28RanksSlice68
private theorem contact28RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact28) 72 8 = 67377 :=
  combineSlices (auxiliaryRankSlice contact28) 72 4 4 46211 21166 contact28RanksSlice72 contact28RanksSlice76
private theorem contact28RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact28) 80 8 = 6663 :=
  combineSlices (auxiliaryRankSlice contact28) 80 4 4 6316 347 contact28RanksSlice80 contact28RanksSlice84
private theorem contact28RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact28) 0 16 = 11370760 :=
  combineSlices (auxiliaryRankSlice contact28) 0 8 8 6370820 4999940 contact28RanksJoin0_8 contact28RanksJoin8_8
private theorem contact28RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact28) 16 16 = 6618359 :=
  combineSlices (auxiliaryRankSlice contact28) 16 8 8 3811844 2806515 contact28RanksJoin16_8 contact28RanksJoin24_8
private theorem contact28RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact28) 32 16 = 3308195 :=
  combineSlices (auxiliaryRankSlice contact28) 32 8 8 1981660 1326535 contact28RanksJoin32_8 contact28RanksJoin40_8
private theorem contact28RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact28) 48 16 = 1284165 :=
  combineSlices (auxiliaryRankSlice contact28) 48 8 8 824833 459332 contact28RanksJoin48_8 contact28RanksJoin56_8
private theorem contact28RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact28) 64 16 = 279936 :=
  combineSlices (auxiliaryRankSlice contact28) 64 8 8 212559 67377 contact28RanksJoin64_8 contact28RanksJoin72_8
private theorem contact28RanksJoin80_15 : sliceWindow (auxiliaryRankSlice contact28) 80 15 = 6663 :=
  combineSlices (auxiliaryRankSlice contact28) 80 8 7 6663 0 contact28RanksJoin80_8 contact28RanksSlice88
private theorem contact28RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact28) 0 32 = 17989119 :=
  combineSlices (auxiliaryRankSlice contact28) 0 16 16 11370760 6618359 contact28RanksJoin0_16 contact28RanksJoin16_16
private theorem contact28RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact28) 32 32 = 4592360 :=
  combineSlices (auxiliaryRankSlice contact28) 32 16 16 3308195 1284165 contact28RanksJoin32_16 contact28RanksJoin48_16
private theorem contact28RanksJoin64_31 : sliceWindow (auxiliaryRankSlice contact28) 64 31 = 286599 :=
  combineSlices (auxiliaryRankSlice contact28) 64 16 15 279936 6663 contact28RanksJoin64_16 contact28RanksJoin80_15
private theorem contact28RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact28) 0 64 = 22581479 :=
  combineSlices (auxiliaryRankSlice contact28) 0 32 32 17989119 4592360 contact28RanksJoin0_32 contact28RanksJoin32_32
private theorem contact28RanksJoin0_95 : sliceWindow (auxiliaryRankSlice contact28) 0 95 = 22868078 :=
  combineSlices (auxiliaryRankSlice contact28) 0 64 31 22581479 286599 contact28RanksJoin0_64 contact28RanksJoin64_31
theorem contact28_margin : sourceMargin contact28 :=
  margin_of_checked_counts contact28 95 217183075684561 7507247985361 834257424 22868078 rfl contact28OrdinaryColumns contact28ColumnsJoin0_95 contact28OrdinaryRanks contact28RanksJoin0_95 (by decide +kernel)

private theorem contact30OrdinaryColumns : ordinaryColumnCount contact30 = 525554943071963 := by decide +kernel
private theorem contact30ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact30) 0 4 = 1936690736651 :=
  contactColumnsWindow_fast contact30 0 4 1936690736651 (by decide +kernel)
private theorem contact30ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact30) 4 4 = 1802319577524 :=
  contactColumnsWindow_fast contact30 4 4 1802319577524 (by decide +kernel)
private theorem contact30ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact30) 8 4 = 1672803503110 :=
  contactColumnsWindow_fast contact30 8 4 1672803503110 (by decide +kernel)
private theorem contact30ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact30) 12 4 = 1548142387622 :=
  contactColumnsWindow_fast contact30 12 4 1548142387622 (by decide +kernel)
private theorem contact30ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact30) 16 4 = 1428336514880 :=
  contactColumnsWindow_fast contact30 16 4 1428336514880 (by decide +kernel)
private theorem contact30ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact30) 20 4 = 1313401004429 :=
  contactColumnsWindow_fast contact30 20 4 1313401004429 (by decide +kernel)
private theorem contact30ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact30) 24 4 = 1203343636656 :=
  contactColumnsWindow_fast contact30 24 4 1203343636656 (by decide +kernel)
private theorem contact30ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact30) 28 4 = 1098142896226 :=
  contactColumnsWindow_fast contact30 28 4 1098142896226 (by decide +kernel)
private theorem contact30ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact30) 32 4 = 997800330651 :=
  contactColumnsWindow_fast contact30 32 4 997800330651 (by decide +kernel)
private theorem contact30ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact30) 36 4 = 902314292102 :=
  contactColumnsWindow_fast contact30 36 4 902314292102 (by decide +kernel)
private theorem contact30ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact30) 40 4 = 811701900350 :=
  contactColumnsWindow_fast contact30 40 4 811701900350 (by decide +kernel)
private theorem contact30ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact30) 44 4 = 725964351333 :=
  contactColumnsWindow_fast contact30 44 4 725964351333 (by decide +kernel)
private theorem contact30ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact30) 48 4 = 645083660617 :=
  contactColumnsWindow_fast contact30 48 4 645083660617 (by decide +kernel)
private theorem contact30ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact30) 52 4 = 569060936286 :=
  contactColumnsWindow_fast contact30 52 4 569060936286 (by decide +kernel)
private theorem contact30ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact30) 56 4 = 497894688224 :=
  contactColumnsWindow_fast contact30 56 4 497894688224 (by decide +kernel)
private theorem contact30ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact30) 60 4 = 431605446217 :=
  contactColumnsWindow_fast contact30 60 4 431605446217 (by decide +kernel)
private theorem contact30ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact30) 64 4 = 370187767746 :=
  contactColumnsWindow_fast contact30 64 4 370187767746 (by decide +kernel)
private theorem contact30ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact30) 68 4 = 313627074913 :=
  contactColumnsWindow_fast contact30 68 4 313627074913 (by decide +kernel)
private theorem contact30ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact30) 72 4 = 261924160821 :=
  contactColumnsWindow_fast contact30 72 4 261924160821 (by decide +kernel)
private theorem contact30ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact30) 76 4 = 215078328098 :=
  contactColumnsWindow_fast contact30 76 4 215078328098 (by decide +kernel)
private theorem contact30ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact30) 80 4 = 173111686105 :=
  contactColumnsWindow_fast contact30 80 4 173111686105 (by decide +kernel)
private theorem contact30ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact30) 84 4 = 136013803059 :=
  contactColumnsWindow_fast contact30 84 4 136013803059 (by decide +kernel)
private theorem contact30ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact30) 88 4 = 103773109954 :=
  contactColumnsWindow_fast contact30 88 4 103773109954 (by decide +kernel)
private theorem contact30ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact30) 92 4 = 76390051628 :=
  contactColumnsWindow_fast contact30 92 4 76390051628 (by decide +kernel)
private theorem contact30ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact30) 96 4 = 53849114818 :=
  contactColumnsWindow_fast contact30 96 4 53849114818 (by decide +kernel)
private theorem contact30ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact30) 100 4 = 36039817094 :=
  contactColumnsWindow_fast contact30 100 4 36039817094 (by decide +kernel)
private theorem contact30ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact30) 104 4 = 22634180285 :=
  contactColumnsWindow_fast contact30 104 4 22634180285 (by decide +kernel)
private theorem contact30ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact30) 108 4 = 13146396160 :=
  contactColumnsWindow_fast contact30 108 4 13146396160 (by decide +kernel)
private theorem contact30ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact30) 112 3 = 5634896463 :=
  contactColumnsWindow_fast contact30 112 3 5634896463 (by decide +kernel)
private theorem contact30ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact30) 0 8 = 3739010314175 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 4 4 1936690736651 1802319577524 contact30ColumnsSlice0 contact30ColumnsSlice4
private theorem contact30ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact30) 8 8 = 3220945890732 :=
  combineSlices (auxiliaryColumnSlice contact30) 8 4 4 1672803503110 1548142387622 contact30ColumnsSlice8 contact30ColumnsSlice12
private theorem contact30ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact30) 16 8 = 2741737519309 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 4 4 1428336514880 1313401004429 contact30ColumnsSlice16 contact30ColumnsSlice20
private theorem contact30ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact30) 24 8 = 2301486532882 :=
  combineSlices (auxiliaryColumnSlice contact30) 24 4 4 1203343636656 1098142896226 contact30ColumnsSlice24 contact30ColumnsSlice28
private theorem contact30ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact30) 32 8 = 1900114622753 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 4 4 997800330651 902314292102 contact30ColumnsSlice32 contact30ColumnsSlice36
private theorem contact30ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact30) 40 8 = 1537666251683 :=
  combineSlices (auxiliaryColumnSlice contact30) 40 4 4 811701900350 725964351333 contact30ColumnsSlice40 contact30ColumnsSlice44
private theorem contact30ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact30) 48 8 = 1214144596903 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 4 4 645083660617 569060936286 contact30ColumnsSlice48 contact30ColumnsSlice52
private theorem contact30ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact30) 56 8 = 929500134441 :=
  combineSlices (auxiliaryColumnSlice contact30) 56 4 4 497894688224 431605446217 contact30ColumnsSlice56 contact30ColumnsSlice60
private theorem contact30ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact30) 64 8 = 683814842659 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 4 4 370187767746 313627074913 contact30ColumnsSlice64 contact30ColumnsSlice68
private theorem contact30ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact30) 72 8 = 477002488919 :=
  combineSlices (auxiliaryColumnSlice contact30) 72 4 4 261924160821 215078328098 contact30ColumnsSlice72 contact30ColumnsSlice76
private theorem contact30ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact30) 80 8 = 309125489164 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 4 4 173111686105 136013803059 contact30ColumnsSlice80 contact30ColumnsSlice84
private theorem contact30ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact30) 88 8 = 180163161582 :=
  combineSlices (auxiliaryColumnSlice contact30) 88 4 4 103773109954 76390051628 contact30ColumnsSlice88 contact30ColumnsSlice92
private theorem contact30ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact30) 96 8 = 89888931912 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 4 4 53849114818 36039817094 contact30ColumnsSlice96 contact30ColumnsSlice100
private theorem contact30ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact30) 104 8 = 35780576445 :=
  combineSlices (auxiliaryColumnSlice contact30) 104 4 4 22634180285 13146396160 contact30ColumnsSlice104 contact30ColumnsSlice108
private theorem contact30ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact30) 0 16 = 6959956204907 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 8 8 3739010314175 3220945890732 contact30ColumnsJoin0_8 contact30ColumnsJoin8_8
private theorem contact30ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact30) 16 16 = 5043224052191 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 8 8 2741737519309 2301486532882 contact30ColumnsJoin16_8 contact30ColumnsJoin24_8
private theorem contact30ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact30) 32 16 = 3437780874436 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 8 8 1900114622753 1537666251683 contact30ColumnsJoin32_8 contact30ColumnsJoin40_8
private theorem contact30ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact30) 48 16 = 2143644731344 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 8 8 1214144596903 929500134441 contact30ColumnsJoin48_8 contact30ColumnsJoin56_8
private theorem contact30ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact30) 64 16 = 1160817331578 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 8 8 683814842659 477002488919 contact30ColumnsJoin64_8 contact30ColumnsJoin72_8
private theorem contact30ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact30) 80 16 = 489288650746 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 8 8 309125489164 180163161582 contact30ColumnsJoin80_8 contact30ColumnsJoin88_8
private theorem contact30ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact30) 96 16 = 125669508357 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 8 8 89888931912 35780576445 contact30ColumnsJoin96_8 contact30ColumnsJoin104_8
private theorem contact30ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact30) 0 32 = 12003180257098 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 16 16 6959956204907 5043224052191 contact30ColumnsJoin0_16 contact30ColumnsJoin16_16
private theorem contact30ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact30) 32 32 = 5581425605780 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 16 16 3437780874436 2143644731344 contact30ColumnsJoin32_16 contact30ColumnsJoin48_16
private theorem contact30ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact30) 64 32 = 1650105982324 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 16 16 1160817331578 489288650746 contact30ColumnsJoin64_16 contact30ColumnsJoin80_16
private theorem contact30ColumnsJoin96_19 : sliceWindow (auxiliaryColumnSlice contact30) 96 19 = 131304404820 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 16 3 125669508357 5634896463 contact30ColumnsJoin96_16 contact30ColumnsSlice112
private theorem contact30ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact30) 0 64 = 17584605862878 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 32 32 12003180257098 5581425605780 contact30ColumnsJoin0_32 contact30ColumnsJoin32_32
private theorem contact30ColumnsJoin64_51 : sliceWindow (auxiliaryColumnSlice contact30) 64 51 = 1781410387144 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 32 19 1650105982324 131304404820 contact30ColumnsJoin64_32 contact30ColumnsJoin96_19
private theorem contact30ColumnsJoin0_115 : sliceWindow (auxiliaryColumnSlice contact30) 0 115 = 19366016250022 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 64 51 17584605862878 1781410387144 contact30ColumnsJoin0_64 contact30ColumnsJoin64_51
private theorem contact30OrdinaryRanks : ordinaryRankBound contact30 = 2019643593 := by decide +kernel
private theorem contact30RanksSlice0 : sliceWindow (auxiliaryRankSlice contact30) 0 4 = 7275714 :=
  contactRankWindow_of_rec contact30 0 4 7275714 (by decide +kernel)
private theorem contact30RanksSlice4 : sliceWindow (auxiliaryRankSlice contact30) 4 4 = 6620514 :=
  contactRankWindow_of_rec contact30 4 4 6620514 (by decide +kernel)
private theorem contact30RanksSlice8 : sliceWindow (auxiliaryRankSlice contact30) 8 4 = 5998914 :=
  contactRankWindow_of_rec contact30 8 4 5998914 (by decide +kernel)
private theorem contact30RanksSlice12 : sliceWindow (auxiliaryRankSlice contact30) 12 4 = 5410914 :=
  contactRankWindow_of_rec contact30 12 4 5410914 (by decide +kernel)
private theorem contact30RanksSlice16 : sliceWindow (auxiliaryRankSlice contact30) 16 4 = 4856514 :=
  contactRankWindow_of_rec contact30 16 4 4856514 (by decide +kernel)
private theorem contact30RanksSlice20 : sliceWindow (auxiliaryRankSlice contact30) 20 4 = 4335714 :=
  contactRankWindow_of_rec contact30 20 4 4335714 (by decide +kernel)
private theorem contact30RanksSlice24 : sliceWindow (auxiliaryRankSlice contact30) 24 4 = 3848514 :=
  contactRankWindow_of_rec contact30 24 4 3848514 (by decide +kernel)
private theorem contact30RanksSlice28 : sliceWindow (auxiliaryRankSlice contact30) 28 4 = 3394914 :=
  contactRankWindow_of_rec contact30 28 4 3394914 (by decide +kernel)
private theorem contact30RanksSlice32 : sliceWindow (auxiliaryRankSlice contact30) 32 4 = 2974914 :=
  contactRankWindow_of_rec contact30 32 4 2974914 (by decide +kernel)
private theorem contact30RanksSlice36 : sliceWindow (auxiliaryRankSlice contact30) 36 4 = 2588366 :=
  contactRankWindow_of_rec contact30 36 4 2588366 (by decide +kernel)
private theorem contact30RanksSlice40 : sliceWindow (auxiliaryRankSlice contact30) 40 4 = 2234500 :=
  contactRankWindow_of_rec contact30 40 4 2234500 (by decide +kernel)
private theorem contact30RanksSlice44 : sliceWindow (auxiliaryRankSlice contact30) 44 4 = 1912341 :=
  contactRankWindow_of_rec contact30 44 4 1912341 (by decide +kernel)
private theorem contact30RanksSlice48 : sliceWindow (auxiliaryRankSlice contact30) 48 4 = 1620629 :=
  contactRankWindow_of_rec contact30 48 4 1620629 (by decide +kernel)
private theorem contact30RanksSlice52 : sliceWindow (auxiliaryRankSlice contact30) 52 4 = 1358008 :=
  contactRankWindow_of_rec contact30 52 4 1358008 (by decide +kernel)
private theorem contact30RanksSlice56 : sliceWindow (auxiliaryRankSlice contact30) 56 4 = 1123285 :=
  contactRankWindow_of_rec contact30 56 4 1123285 (by decide +kernel)
private theorem contact30RanksSlice60 : sliceWindow (auxiliaryRankSlice contact30) 60 4 = 915049 :=
  contactRankWindow_of_rec contact30 60 4 915049 (by decide +kernel)
private theorem contact30RanksSlice64 : sliceWindow (auxiliaryRankSlice contact30) 64 4 = 731948 :=
  contactRankWindow_of_rec contact30 64 4 731948 (by decide +kernel)
private theorem contact30RanksSlice68 : sliceWindow (auxiliaryRankSlice contact30) 68 4 = 572885 :=
  contactRankWindow_of_rec contact30 68 4 572885 (by decide +kernel)
private theorem contact30RanksSlice72 : sliceWindow (auxiliaryRankSlice contact30) 72 4 = 436349 :=
  contactRankWindow_of_rec contact30 72 4 436349 (by decide +kernel)
private theorem contact30RanksSlice76 : sliceWindow (auxiliaryRankSlice contact30) 76 4 = 320992 :=
  contactRankWindow_of_rec contact30 76 4 320992 (by decide +kernel)
private theorem contact30RanksSlice80 : sliceWindow (auxiliaryRankSlice contact30) 80 4 = 225813 :=
  contactRankWindow_of_rec contact30 80 4 225813 (by decide +kernel)
private theorem contact30RanksSlice84 : sliceWindow (auxiliaryRankSlice contact30) 84 4 = 149201 :=
  contactRankWindow_of_rec contact30 84 4 149201 (by decide +kernel)
private theorem contact30RanksSlice88 : sliceWindow (auxiliaryRankSlice contact30) 88 4 = 89812 :=
  contactRankWindow_of_rec contact30 88 4 89812 (by decide +kernel)
private theorem contact30RanksSlice92 : sliceWindow (auxiliaryRankSlice contact30) 92 4 = 46741 :=
  contactRankWindow_of_rec contact30 92 4 46741 (by decide +kernel)
private theorem contact30RanksSlice96 : sliceWindow (auxiliaryRankSlice contact30) 96 4 = 18279 :=
  contactRankWindow_of_rec contact30 96 4 18279 (by decide +kernel)
private theorem contact30RanksSlice100 : sliceWindow (auxiliaryRankSlice contact30) 100 4 = 3167 :=
  contactRankWindow_of_rec contact30 100 4 3167 (by decide +kernel)
private theorem contact30RanksSlice104 : sliceWindow (auxiliaryRankSlice contact30) 104 11 = 0 :=
  contactRankWindow_of_rec contact30 104 11 0 (by decide +kernel)
private theorem contact30RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact30) 0 8 = 13896228 :=
  combineSlices (auxiliaryRankSlice contact30) 0 4 4 7275714 6620514 contact30RanksSlice0 contact30RanksSlice4
private theorem contact30RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact30) 8 8 = 11409828 :=
  combineSlices (auxiliaryRankSlice contact30) 8 4 4 5998914 5410914 contact30RanksSlice8 contact30RanksSlice12
private theorem contact30RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact30) 16 8 = 9192228 :=
  combineSlices (auxiliaryRankSlice contact30) 16 4 4 4856514 4335714 contact30RanksSlice16 contact30RanksSlice20
private theorem contact30RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact30) 24 8 = 7243428 :=
  combineSlices (auxiliaryRankSlice contact30) 24 4 4 3848514 3394914 contact30RanksSlice24 contact30RanksSlice28
private theorem contact30RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact30) 32 8 = 5563280 :=
  combineSlices (auxiliaryRankSlice contact30) 32 4 4 2974914 2588366 contact30RanksSlice32 contact30RanksSlice36
private theorem contact30RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact30) 40 8 = 4146841 :=
  combineSlices (auxiliaryRankSlice contact30) 40 4 4 2234500 1912341 contact30RanksSlice40 contact30RanksSlice44
private theorem contact30RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact30) 48 8 = 2978637 :=
  combineSlices (auxiliaryRankSlice contact30) 48 4 4 1620629 1358008 contact30RanksSlice48 contact30RanksSlice52
private theorem contact30RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact30) 56 8 = 2038334 :=
  combineSlices (auxiliaryRankSlice contact30) 56 4 4 1123285 915049 contact30RanksSlice56 contact30RanksSlice60
private theorem contact30RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact30) 64 8 = 1304833 :=
  combineSlices (auxiliaryRankSlice contact30) 64 4 4 731948 572885 contact30RanksSlice64 contact30RanksSlice68
private theorem contact30RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact30) 72 8 = 757341 :=
  combineSlices (auxiliaryRankSlice contact30) 72 4 4 436349 320992 contact30RanksSlice72 contact30RanksSlice76
private theorem contact30RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact30) 80 8 = 375014 :=
  combineSlices (auxiliaryRankSlice contact30) 80 4 4 225813 149201 contact30RanksSlice80 contact30RanksSlice84
private theorem contact30RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact30) 88 8 = 136553 :=
  combineSlices (auxiliaryRankSlice contact30) 88 4 4 89812 46741 contact30RanksSlice88 contact30RanksSlice92
private theorem contact30RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact30) 96 8 = 21446 :=
  combineSlices (auxiliaryRankSlice contact30) 96 4 4 18279 3167 contact30RanksSlice96 contact30RanksSlice100
private theorem contact30RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact30) 0 16 = 25306056 :=
  combineSlices (auxiliaryRankSlice contact30) 0 8 8 13896228 11409828 contact30RanksJoin0_8 contact30RanksJoin8_8
private theorem contact30RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact30) 16 16 = 16435656 :=
  combineSlices (auxiliaryRankSlice contact30) 16 8 8 9192228 7243428 contact30RanksJoin16_8 contact30RanksJoin24_8
private theorem contact30RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact30) 32 16 = 9710121 :=
  combineSlices (auxiliaryRankSlice contact30) 32 8 8 5563280 4146841 contact30RanksJoin32_8 contact30RanksJoin40_8
private theorem contact30RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact30) 48 16 = 5016971 :=
  combineSlices (auxiliaryRankSlice contact30) 48 8 8 2978637 2038334 contact30RanksJoin48_8 contact30RanksJoin56_8
private theorem contact30RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact30) 64 16 = 2062174 :=
  combineSlices (auxiliaryRankSlice contact30) 64 8 8 1304833 757341 contact30RanksJoin64_8 contact30RanksJoin72_8
private theorem contact30RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact30) 80 16 = 511567 :=
  combineSlices (auxiliaryRankSlice contact30) 80 8 8 375014 136553 contact30RanksJoin80_8 contact30RanksJoin88_8
private theorem contact30RanksJoin96_19 : sliceWindow (auxiliaryRankSlice contact30) 96 19 = 21446 :=
  combineSlices (auxiliaryRankSlice contact30) 96 8 11 21446 0 contact30RanksJoin96_8 contact30RanksSlice104
private theorem contact30RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact30) 0 32 = 41741712 :=
  combineSlices (auxiliaryRankSlice contact30) 0 16 16 25306056 16435656 contact30RanksJoin0_16 contact30RanksJoin16_16
private theorem contact30RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact30) 32 32 = 14727092 :=
  combineSlices (auxiliaryRankSlice contact30) 32 16 16 9710121 5016971 contact30RanksJoin32_16 contact30RanksJoin48_16
private theorem contact30RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact30) 64 32 = 2573741 :=
  combineSlices (auxiliaryRankSlice contact30) 64 16 16 2062174 511567 contact30RanksJoin64_16 contact30RanksJoin80_16
private theorem contact30RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact30) 0 64 = 56468804 :=
  combineSlices (auxiliaryRankSlice contact30) 0 32 32 41741712 14727092 contact30RanksJoin0_32 contact30RanksJoin32_32
private theorem contact30RanksJoin64_51 : sliceWindow (auxiliaryRankSlice contact30) 64 51 = 2595187 :=
  combineSlices (auxiliaryRankSlice contact30) 64 32 19 2573741 21446 contact30RanksJoin64_32 contact30RanksJoin96_19
private theorem contact30RanksJoin0_115 : sliceWindow (auxiliaryRankSlice contact30) 0 115 = 59063991 :=
  combineSlices (auxiliaryRankSlice contact30) 0 64 51 56468804 2595187 contact30RanksJoin0_64 contact30RanksJoin64_51
theorem contact30_margin : sourceMargin contact30 :=
  margin_of_checked_counts contact30 115 525554943071963 19366016250022 2019643593 59063991 rfl contact30OrdinaryColumns contact30ColumnsJoin0_115 contact30OrdinaryRanks contact30RanksJoin0_115 (by decide +kernel)

private theorem contact32OrdinaryColumns : ordinaryColumnCount contact32 = 538927685149235 := by decide +kernel
private theorem contact32ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact32) 0 4 = 1997708599383 :=
  contactColumnsWindow_fast contact32 0 4 1997708599383 (by decide +kernel)
private theorem contact32ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact32) 4 4 = 1858570305546 :=
  contactColumnsWindow_fast contact32 4 4 1858570305546 (by decide +kernel)
private theorem contact32ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact32) 8 4 = 1724481276794 :=
  contactColumnsWindow_fast contact32 8 4 1724481276794 (by decide +kernel)
private theorem contact32ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact32) 12 4 = 1595441372682 :=
  contactColumnsWindow_fast contact32 12 4 1595441372682 (by decide +kernel)
private theorem contact32ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact32) 16 4 = 1471450880938 :=
  contactColumnsWindow_fast contact32 16 4 1471450880938 (by decide +kernel)
private theorem contact32ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact32) 20 4 = 1352525655064 :=
  contactColumnsWindow_fast contact32 20 4 1352525655064 (by decide +kernel)
private theorem contact32ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact32) 24 4 = 1238673817330 :=
  contactColumnsWindow_fast contact32 24 4 1238673817330 (by decide +kernel)
private theorem contact32ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact32) 28 4 = 1129872811043 :=
  contactColumnsWindow_fast contact32 28 4 1129872811043 (by decide +kernel)
private theorem contact32ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact32) 32 4 = 1026124215531 :=
  contactColumnsWindow_fast contact32 32 4 1026124215531 (by decide +kernel)
private theorem contact32ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact32) 36 4 = 927426345946 :=
  contactColumnsWindow_fast contact32 36 4 927426345946 (by decide +kernel)
private theorem contact32ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact32) 40 4 = 833797188604 :=
  contactColumnsWindow_fast contact32 40 4 833797188604 (by decide +kernel)
private theorem contact32ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact32) 44 4 = 745237956830 :=
  contactColumnsWindow_fast contact32 44 4 745237956830 (by decide +kernel)
private theorem contact32ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact32) 48 4 = 661729793506 :=
  contactColumnsWindow_fast contact32 48 4 661729793506 (by decide +kernel)
private theorem contact32ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact32) 52 4 = 583273826829 :=
  contactColumnsWindow_fast contact32 52 4 583273826829 (by decide +kernel)
private theorem contact32ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact32) 56 4 = 509868534610 :=
  contactColumnsWindow_fast contact32 56 4 509868534610 (by decide +kernel)
private theorem contact32ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact32) 60 4 = 441535477546 :=
  contactColumnsWindow_fast contact32 60 4 441535477546 (by decide +kernel)
private theorem contact32ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact32) 64 4 = 378268904966 :=
  contactColumnsWindow_fast contact32 64 4 378268904966 (by decide +kernel)
private theorem contact32ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact32) 68 4 = 320053531342 :=
  contactColumnsWindow_fast contact32 68 4 320053531342 (by decide +kernel)
private theorem contact32ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact32) 72 4 = 266890161783 :=
  contactColumnsWindow_fast contact32 72 4 266890161783 (by decide +kernel)
private theorem contact32ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact32) 76 4 = 218778101311 :=
  contactColumnsWindow_fast contact32 76 4 218778101311 (by decide +kernel)
private theorem contact32ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact32) 80 4 = 175740567034 :=
  contactColumnsWindow_fast contact32 80 4 175740567034 (by decide +kernel)
private theorem contact32ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact32) 84 4 = 137766576758 :=
  contactColumnsWindow_fast contact32 84 4 137766576758 (by decide +kernel)
private theorem contact32ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact32) 88 4 = 104843994697 :=
  contactColumnsWindow_fast contact32 88 4 104843994697 (by decide +kernel)
private theorem contact32ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact32) 92 4 = 76972926484 :=
  contactColumnsWindow_fast contact32 92 4 76972926484 (by decide +kernel)
private theorem contact32ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact32) 96 4 = 54122171354 :=
  contactColumnsWindow_fast contact32 96 4 54122171354 (by decide +kernel)
private theorem contact32ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact32) 100 4 = 36139606608 :=
  contactColumnsWindow_fast contact32 100 4 36139606608 (by decide +kernel)
private theorem contact32ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact32) 104 4 = 22656416559 :=
  contactColumnsWindow_fast contact32 104 4 22656416559 (by decide +kernel)
private theorem contact32ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact32) 108 4 = 13147685850 :=
  contactColumnsWindow_fast contact32 108 4 13147685850 (by decide +kernel)
private theorem contact32ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact32) 112 2 = 4069480658 :=
  contactColumnsWindow_fast contact32 112 2 4069480658 (by decide +kernel)
private theorem contact32ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact32) 0 8 = 3856278904929 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 4 4 1997708599383 1858570305546 contact32ColumnsSlice0 contact32ColumnsSlice4
private theorem contact32ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact32) 8 8 = 3319922649476 :=
  combineSlices (auxiliaryColumnSlice contact32) 8 4 4 1724481276794 1595441372682 contact32ColumnsSlice8 contact32ColumnsSlice12
private theorem contact32ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact32) 16 8 = 2823976536002 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 4 4 1471450880938 1352525655064 contact32ColumnsSlice16 contact32ColumnsSlice20
private theorem contact32ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact32) 24 8 = 2368546628373 :=
  combineSlices (auxiliaryColumnSlice contact32) 24 4 4 1238673817330 1129872811043 contact32ColumnsSlice24 contact32ColumnsSlice28
private theorem contact32ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact32) 32 8 = 1953550561477 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 4 4 1026124215531 927426345946 contact32ColumnsSlice32 contact32ColumnsSlice36
private theorem contact32ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact32) 40 8 = 1579035145434 :=
  combineSlices (auxiliaryColumnSlice contact32) 40 4 4 833797188604 745237956830 contact32ColumnsSlice40 contact32ColumnsSlice44
private theorem contact32ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact32) 48 8 = 1245003620335 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 4 4 661729793506 583273826829 contact32ColumnsSlice48 contact32ColumnsSlice52
private theorem contact32ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact32) 56 8 = 951404012156 :=
  combineSlices (auxiliaryColumnSlice contact32) 56 4 4 509868534610 441535477546 contact32ColumnsSlice56 contact32ColumnsSlice60
private theorem contact32ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact32) 64 8 = 698322436308 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 4 4 378268904966 320053531342 contact32ColumnsSlice64 contact32ColumnsSlice68
private theorem contact32ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact32) 72 8 = 485668263094 :=
  combineSlices (auxiliaryColumnSlice contact32) 72 4 4 266890161783 218778101311 contact32ColumnsSlice72 contact32ColumnsSlice76
private theorem contact32ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact32) 80 8 = 313507143792 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 4 4 175740567034 137766576758 contact32ColumnsSlice80 contact32ColumnsSlice84
private theorem contact32ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact32) 88 8 = 181816921181 :=
  combineSlices (auxiliaryColumnSlice contact32) 88 4 4 104843994697 76972926484 contact32ColumnsSlice88 contact32ColumnsSlice92
private theorem contact32ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact32) 96 8 = 90261777962 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 4 4 54122171354 36139606608 contact32ColumnsSlice96 contact32ColumnsSlice100
private theorem contact32ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact32) 104 8 = 35804102409 :=
  combineSlices (auxiliaryColumnSlice contact32) 104 4 4 22656416559 13147685850 contact32ColumnsSlice104 contact32ColumnsSlice108
private theorem contact32ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact32) 0 16 = 7176201554405 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 8 8 3856278904929 3319922649476 contact32ColumnsJoin0_8 contact32ColumnsJoin8_8
private theorem contact32ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact32) 16 16 = 5192523164375 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 8 8 2823976536002 2368546628373 contact32ColumnsJoin16_8 contact32ColumnsJoin24_8
private theorem contact32ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact32) 32 16 = 3532585706911 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 8 8 1953550561477 1579035145434 contact32ColumnsJoin32_8 contact32ColumnsJoin40_8
private theorem contact32ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact32) 48 16 = 2196407632491 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 8 8 1245003620335 951404012156 contact32ColumnsJoin48_8 contact32ColumnsJoin56_8
private theorem contact32ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact32) 64 16 = 1183990699402 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 8 8 698322436308 485668263094 contact32ColumnsJoin64_8 contact32ColumnsJoin72_8
private theorem contact32ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact32) 80 16 = 495324064973 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 8 8 313507143792 181816921181 contact32ColumnsJoin80_8 contact32ColumnsJoin88_8
private theorem contact32ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact32) 96 16 = 126065880371 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 8 8 90261777962 35804102409 contact32ColumnsJoin96_8 contact32ColumnsJoin104_8
private theorem contact32ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact32) 0 32 = 12368724718780 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 16 16 7176201554405 5192523164375 contact32ColumnsJoin0_16 contact32ColumnsJoin16_16
private theorem contact32ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact32) 32 32 = 5728993339402 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 16 16 3532585706911 2196407632491 contact32ColumnsJoin32_16 contact32ColumnsJoin48_16
private theorem contact32ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact32) 64 32 = 1679314764375 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 16 16 1183990699402 495324064973 contact32ColumnsJoin64_16 contact32ColumnsJoin80_16
private theorem contact32ColumnsJoin96_18 : sliceWindow (auxiliaryColumnSlice contact32) 96 18 = 130135361029 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 16 2 126065880371 4069480658 contact32ColumnsJoin96_16 contact32ColumnsSlice112
private theorem contact32ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact32) 0 64 = 18097718058182 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 32 32 12368724718780 5728993339402 contact32ColumnsJoin0_32 contact32ColumnsJoin32_32
private theorem contact32ColumnsJoin64_50 : sliceWindow (auxiliaryColumnSlice contact32) 64 50 = 1809450125404 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 32 18 1679314764375 130135361029 contact32ColumnsJoin64_32 contact32ColumnsJoin96_18
private theorem contact32ColumnsJoin0_114 : sliceWindow (auxiliaryColumnSlice contact32) 0 114 = 19907168183586 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 64 50 18097718058182 1809450125404 contact32ColumnsJoin0_64 contact32ColumnsJoin64_50
private theorem contact32OrdinaryRanks : ordinaryRankBound contact32 = 2070864769 := by decide +kernel
private theorem contact32RanksSlice0 : sliceWindow (auxiliaryRankSlice contact32) 0 4 = 7505346 :=
  contactRankWindow_of_rec contact32 0 4 7505346 (by decide +kernel)
private theorem contact32RanksSlice4 : sliceWindow (auxiliaryRankSlice contact32) 4 4 = 6828306 :=
  contactRankWindow_of_rec contact32 4 4 6828306 (by decide +kernel)
private theorem contact32RanksSlice8 : sliceWindow (auxiliaryRankSlice contact32) 8 4 = 6186210 :=
  contactRankWindow_of_rec contact32 8 4 6186210 (by decide +kernel)
private theorem contact32RanksSlice12 : sliceWindow (auxiliaryRankSlice contact32) 12 4 = 5579058 :=
  contactRankWindow_of_rec contact32 12 4 5579058 (by decide +kernel)
private theorem contact32RanksSlice16 : sliceWindow (auxiliaryRankSlice contact32) 16 4 = 5006850 :=
  contactRankWindow_of_rec contact32 16 4 5006850 (by decide +kernel)
private theorem contact32RanksSlice20 : sliceWindow (auxiliaryRankSlice contact32) 20 4 = 4469586 :=
  contactRankWindow_of_rec contact32 20 4 4469586 (by decide +kernel)
private theorem contact32RanksSlice24 : sliceWindow (auxiliaryRankSlice contact32) 24 4 = 3967266 :=
  contactRankWindow_of_rec contact32 24 4 3967266 (by decide +kernel)
private theorem contact32RanksSlice28 : sliceWindow (auxiliaryRankSlice contact32) 28 4 = 3499890 :=
  contactRankWindow_of_rec contact32 28 4 3499890 (by decide +kernel)
private theorem contact32RanksSlice32 : sliceWindow (auxiliaryRankSlice contact32) 32 4 = 3067437 :=
  contactRankWindow_of_rec contact32 32 4 3067437 (by decide +kernel)
private theorem contact32RanksSlice36 : sliceWindow (auxiliaryRankSlice contact32) 36 4 = 2669461 :=
  contactRankWindow_of_rec contact32 36 4 2669461 (by decide +kernel)
private theorem contact32RanksSlice40 : sliceWindow (auxiliaryRankSlice contact32) 40 4 = 2305051 :=
  contactRankWindow_of_rec contact32 40 4 2305051 (by decide +kernel)
private theorem contact32RanksSlice44 : sliceWindow (auxiliaryRankSlice contact32) 44 4 = 1973198 :=
  contactRankWindow_of_rec contact32 44 4 1973198 (by decide +kernel)
private theorem contact32RanksSlice48 : sliceWindow (auxiliaryRankSlice contact32) 48 4 = 1672634 :=
  contactRankWindow_of_rec contact32 48 4 1672634 (by decide +kernel)
private theorem contact32RanksSlice52 : sliceWindow (auxiliaryRankSlice contact32) 52 4 = 1401971 :=
  contactRankWindow_of_rec contact32 52 4 1401971 (by decide +kernel)
private theorem contact32RanksSlice56 : sliceWindow (auxiliaryRankSlice contact32) 56 4 = 1159978 :=
  contactRankWindow_of_rec contact32 56 4 1159978 (by decide +kernel)
private theorem contact32RanksSlice60 : sliceWindow (auxiliaryRankSlice contact32) 60 4 = 945226 :=
  contactRankWindow_of_rec contact32 60 4 945226 (by decide +kernel)
private theorem contact32RanksSlice64 : sliceWindow (auxiliaryRankSlice contact32) 64 4 = 756331 :=
  contactRankWindow_of_rec contact32 64 4 756331 (by decide +kernel)
private theorem contact32RanksSlice68 : sliceWindow (auxiliaryRankSlice contact32) 68 4 = 592166 :=
  contactRankWindow_of_rec contact32 68 4 592166 (by decide +kernel)
private theorem contact32RanksSlice72 : sliceWindow (auxiliaryRankSlice contact32) 72 4 = 451194 :=
  contactRankWindow_of_rec contact32 72 4 451194 (by decide +kernel)
private theorem contact32RanksSlice76 : sliceWindow (auxiliaryRankSlice contact32) 76 4 = 332035 :=
  contactRankWindow_of_rec contact32 76 4 332035 (by decide +kernel)
private theorem contact32RanksSlice80 : sliceWindow (auxiliaryRankSlice contact32) 80 4 = 233666 :=
  contactRankWindow_of_rec contact32 80 4 233666 (by decide +kernel)
private theorem contact32RanksSlice84 : sliceWindow (auxiliaryRankSlice contact32) 84 4 = 154442 :=
  contactRankWindow_of_rec contact32 84 4 154442 (by decide +kernel)
private theorem contact32RanksSlice88 : sliceWindow (auxiliaryRankSlice contact32) 88 4 = 92987 :=
  contactRankWindow_of_rec contact32 88 4 92987 (by decide +kernel)
private theorem contact32RanksSlice92 : sliceWindow (auxiliaryRankSlice contact32) 92 4 = 48382 :=
  contactRankWindow_of_rec contact32 92 4 48382 (by decide +kernel)
private theorem contact32RanksSlice96 : sliceWindow (auxiliaryRankSlice contact32) 96 4 = 18884 :=
  contactRankWindow_of_rec contact32 96 4 18884 (by decide +kernel)
private theorem contact32RanksSlice100 : sliceWindow (auxiliaryRankSlice contact32) 100 4 = 3262 :=
  contactRankWindow_of_rec contact32 100 4 3262 (by decide +kernel)
private theorem contact32RanksSlice104 : sliceWindow (auxiliaryRankSlice contact32) 104 10 = 0 :=
  contactRankWindow_of_rec contact32 104 10 0 (by decide +kernel)
private theorem contact32RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact32) 0 8 = 14333652 :=
  combineSlices (auxiliaryRankSlice contact32) 0 4 4 7505346 6828306 contact32RanksSlice0 contact32RanksSlice4
private theorem contact32RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact32) 8 8 = 11765268 :=
  combineSlices (auxiliaryRankSlice contact32) 8 4 4 6186210 5579058 contact32RanksSlice8 contact32RanksSlice12
private theorem contact32RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact32) 16 8 = 9476436 :=
  combineSlices (auxiliaryRankSlice contact32) 16 4 4 5006850 4469586 contact32RanksSlice16 contact32RanksSlice20
private theorem contact32RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact32) 24 8 = 7467156 :=
  combineSlices (auxiliaryRankSlice contact32) 24 4 4 3967266 3499890 contact32RanksSlice24 contact32RanksSlice28
private theorem contact32RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact32) 32 8 = 5736898 :=
  combineSlices (auxiliaryRankSlice contact32) 32 4 4 3067437 2669461 contact32RanksSlice32 contact32RanksSlice36
private theorem contact32RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact32) 40 8 = 4278249 :=
  combineSlices (auxiliaryRankSlice contact32) 40 4 4 2305051 1973198 contact32RanksSlice40 contact32RanksSlice44
private theorem contact32RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact32) 48 8 = 3074605 :=
  combineSlices (auxiliaryRankSlice contact32) 48 4 4 1672634 1401971 contact32RanksSlice48 contact32RanksSlice52
private theorem contact32RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact32) 56 8 = 2105204 :=
  combineSlices (auxiliaryRankSlice contact32) 56 4 4 1159978 945226 contact32RanksSlice56 contact32RanksSlice60
private theorem contact32RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact32) 64 8 = 1348497 :=
  combineSlices (auxiliaryRankSlice contact32) 64 4 4 756331 592166 contact32RanksSlice64 contact32RanksSlice68
private theorem contact32RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact32) 72 8 = 783229 :=
  combineSlices (auxiliaryRankSlice contact32) 72 4 4 451194 332035 contact32RanksSlice72 contact32RanksSlice76
private theorem contact32RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact32) 80 8 = 388108 :=
  combineSlices (auxiliaryRankSlice contact32) 80 4 4 233666 154442 contact32RanksSlice80 contact32RanksSlice84
private theorem contact32RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact32) 88 8 = 141369 :=
  combineSlices (auxiliaryRankSlice contact32) 88 4 4 92987 48382 contact32RanksSlice88 contact32RanksSlice92
private theorem contact32RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact32) 96 8 = 22146 :=
  combineSlices (auxiliaryRankSlice contact32) 96 4 4 18884 3262 contact32RanksSlice96 contact32RanksSlice100
private theorem contact32RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact32) 0 16 = 26098920 :=
  combineSlices (auxiliaryRankSlice contact32) 0 8 8 14333652 11765268 contact32RanksJoin0_8 contact32RanksJoin8_8
private theorem contact32RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact32) 16 16 = 16943592 :=
  combineSlices (auxiliaryRankSlice contact32) 16 8 8 9476436 7467156 contact32RanksJoin16_8 contact32RanksJoin24_8
private theorem contact32RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact32) 32 16 = 10015147 :=
  combineSlices (auxiliaryRankSlice contact32) 32 8 8 5736898 4278249 contact32RanksJoin32_8 contact32RanksJoin40_8
private theorem contact32RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact32) 48 16 = 5179809 :=
  combineSlices (auxiliaryRankSlice contact32) 48 8 8 3074605 2105204 contact32RanksJoin48_8 contact32RanksJoin56_8
private theorem contact32RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact32) 64 16 = 2131726 :=
  combineSlices (auxiliaryRankSlice contact32) 64 8 8 1348497 783229 contact32RanksJoin64_8 contact32RanksJoin72_8
private theorem contact32RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact32) 80 16 = 529477 :=
  combineSlices (auxiliaryRankSlice contact32) 80 8 8 388108 141369 contact32RanksJoin80_8 contact32RanksJoin88_8
private theorem contact32RanksJoin96_18 : sliceWindow (auxiliaryRankSlice contact32) 96 18 = 22146 :=
  combineSlices (auxiliaryRankSlice contact32) 96 8 10 22146 0 contact32RanksJoin96_8 contact32RanksSlice104
private theorem contact32RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact32) 0 32 = 43042512 :=
  combineSlices (auxiliaryRankSlice contact32) 0 16 16 26098920 16943592 contact32RanksJoin0_16 contact32RanksJoin16_16
private theorem contact32RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact32) 32 32 = 15194956 :=
  combineSlices (auxiliaryRankSlice contact32) 32 16 16 10015147 5179809 contact32RanksJoin32_16 contact32RanksJoin48_16
private theorem contact32RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact32) 64 32 = 2661203 :=
  combineSlices (auxiliaryRankSlice contact32) 64 16 16 2131726 529477 contact32RanksJoin64_16 contact32RanksJoin80_16
private theorem contact32RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact32) 0 64 = 58237468 :=
  combineSlices (auxiliaryRankSlice contact32) 0 32 32 43042512 15194956 contact32RanksJoin0_32 contact32RanksJoin32_32
private theorem contact32RanksJoin64_50 : sliceWindow (auxiliaryRankSlice contact32) 64 50 = 2683349 :=
  combineSlices (auxiliaryRankSlice contact32) 64 32 18 2661203 22146 contact32RanksJoin64_32 contact32RanksJoin96_18
private theorem contact32RanksJoin0_114 : sliceWindow (auxiliaryRankSlice contact32) 0 114 = 60920817 :=
  combineSlices (auxiliaryRankSlice contact32) 0 64 50 58237468 2683349 contact32RanksJoin0_64 contact32RanksJoin64_50
theorem contact32_margin : sourceMargin contact32 :=
  margin_of_checked_counts contact32 114 538927685149235 19907168183586 2070864769 60920817 rfl contact32OrdinaryColumns contact32ColumnsJoin0_114 contact32OrdinaryRanks contact32RanksJoin0_114 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts
