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



private theorem primaryWindow0 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 512 = 3665889792351420 :=
  firstJetWindow_of_closed primaryShape 0 0 512 (3665889792351420) (by decide +kernel) (by decide +kernel)

private theorem primaryWindow512 : contributionWindow (firstJetAuxContribution primaryShape 0) 512 236 = 408901092645876 :=
  firstJetWindow_of_closed primaryShape 0 512 236 (408901092645876) (by decide +kernel) (by decide +kernel)

private theorem primaryJoin0_748 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 748 = 4074790884997296 :=
  joinWindows (firstJetAuxContribution primaryShape 0) 0 512 236 (3665889792351420) (408901092645876) primaryWindow0 primaryWindow512

theorem primary_firstJetGap_eq : firstJetGap primaryShape 0 = 5531447 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum primaryShape 0 748 (4074790884997296) rfl primaryJoin0_748]
  decide +kernel
private theorem firstRoomWindow0 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 = 82223227846895580 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 0 512 (82223227846895580) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow512 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 512 512 = 170549265576059616 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 512 512 (170549265576059616) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 = 154700850848409288 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1024 512 (154700850848409288) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1536 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1536 512 = 76299644786815992 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1536 512 (76299644786815992) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 2048 512 = 8530042529499888 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 2048 512 (8530042529499888) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow2560 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 2560 4 = 329798959320 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 2560 4 (329798959320) (by decide +kernel) (by decide +kernel)

private theorem firstRoomJoin0_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 = 252772493422955196 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 512 (82223227846895580) (170549265576059616) firstRoomWindow0 firstRoomWindow512

private theorem firstRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 1024 = 231000495635225280 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 512 (154700850848409288) (76299644786815992) firstRoomWindow1024 firstRoomWindow1536

private theorem firstRoomJoin2048_516 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 2048 516 = 8530372328459208 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 2048 512 4 (8530042529499888) (329798959320) firstRoomWindow2048 firstRoomWindow2560

private theorem firstRoomJoin0_2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 = 483772989058180476 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 1024 (252772493422955196) (231000495635225280) firstRoomJoin0_1024 firstRoomJoin1024_1024

private theorem firstRoomJoin0_2564 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2564 = 492303361386639684 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 516 (483772989058180476) (8530372328459208) firstRoomJoin0_2048 firstRoomJoin2048_516

theorem firstRoom_firstJetGap_eq : firstJetGap firstRoomShape firstRoomCut = 214376357 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstRoomShape firstRoomCut 2564 (492303361386639684) rfl firstRoomJoin0_2564]
  decide +kernel
private theorem secondRoomWindow0 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 = 82439413974273252 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 0 512 (82439413974273252) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow512 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 512 512 = 170712360688376208 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 512 512 (170712360688376208) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 = 154810854906479712 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1024 512 (154810854906479712) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1536 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1536 512 = 76356557909474664 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1536 512 (76356557909474664) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 2048 451 = 8522645602090344 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 2048 451 (8522645602090344) (by decide +kernel) (by decide +kernel)

private theorem secondRoomJoin0_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 = 253151774662649460 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 512 (82439413974273252) (170712360688376208) secondRoomWindow0 secondRoomWindow512

private theorem secondRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 1024 = 231167412815954376 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 512 (154810854906479712) (76356557909474664) secondRoomWindow1024 secondRoomWindow1536

private theorem secondRoomJoin0_2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 = 484319187478603836 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 1024 (253151774662649460) (231167412815954376) secondRoomJoin0_1024 secondRoomJoin1024_1024

private theorem secondRoomJoin0_2499 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2499 = 492841833080694180 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 451 (484319187478603836) (8522645602090344) secondRoomJoin0_2048 secondRoomWindow2048

theorem secondRoom_firstJetGap_eq : firstJetGap secondRoomShape secondRoomCut = 4756624925 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondRoomShape secondRoomCut 2499 (492841833080694180) rfl secondRoomJoin0_2499]
  decide +kernel
private theorem firstAdaptiveWindow0 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 512 = 83412499822368564 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 0 512 (83412499822368564) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow512 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 512 512 = 171446537389610784 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 512 512 (171446537389610784) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 = 155306122552200744 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1024 512 (155306122552200744) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1536 512 = 76612916458126608 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1536 512 (76612916458126608) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 2048 352 = 8389933033842912 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 2048 352 (8389933033842912) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 = 254859037211979348 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 512 512 (83412499822368564) (171446537389610784) firstAdaptiveWindow0 firstAdaptiveWindow512

private theorem firstAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 1024 = 231919039010327352 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 512 (155306122552200744) (76612916458126608) firstAdaptiveWindow1024 firstAdaptiveWindow1536

private theorem firstAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 = 486778076222306700 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 1024 (254859037211979348) (231919039010327352) firstAdaptiveJoin0_1024 firstAdaptiveJoin1024_1024

private theorem firstAdaptiveJoin0_2400 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2400 = 495168009256149612 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 352 (486778076222306700) (8389933033842912) firstAdaptiveJoin0_2048 firstAdaptiveWindow2048

theorem firstAdaptive_firstJetGap_eq : firstJetGap firstAdaptiveShape 0 = firstAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstAdaptiveShape 0 2400 (495168009256149612) rfl firstAdaptiveJoin0_2400]
  decide +kernel
private theorem secondAdaptiveWindow0 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 512 = 89850660856095601680 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 0 512 (89850660856095601680) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 512 512 = 210221043633762338472 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 512 512 (210221043633762338472) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 = 327724230450296704860 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1024 512 (327724230450296704860) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1536 512 = 442360221305704710216 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1536 512 (442360221305704710216) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 = 554129016199978828908 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2048 512 (554129016199978828908) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2560 512 = 663030615133178425188 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2560 512 (663030615133178425188) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 = 769065018106954574388 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3072 512 (769065018106954574388) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3584 512 = 872232225121784058372 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3584 512 (872232225121784058372) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 = 972532236175669114320 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4096 512 (972532236175669114320) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4608 512 = 1069965051268418903376 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4608 512 (1069965051268418903376) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 = 1164530670400032587568 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5120 512 (1164530670400032587568) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5632 512 = 1256229093570515559504 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5632 512 (1256229093570515559504) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 = 1345060320779870765952 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6144 512 (1345060320779870765952) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6656 512 = 1431024352028092326192 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6656 512 (1431024352028092326192) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 = 1514121187315187700252 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7168 512 (1514121187315187700252) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7680 512 = 1594350826641150235188 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7680 512 (1594350826641150235188) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 = 1671713270006302399860 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8192 512 (1671713270006302399860) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8704 512 = 1746208517412788468556 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8704 512 (1746208517412788468556) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 = 1817836568859476952144 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9216 512 (1817836568859476952144) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9728 512 = 1886597424345037589316 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9728 512 (1886597424345037589316) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 = 1952491083869469296904 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10240 512 (1952491083869469296904) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10752 512 = 2015517547432771462548 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10752 512 (2015517547432771462548) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 = 2075676815034941080308 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11264 512 (2075676815034941080308) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11776 512 = 2132968886675984421960 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11776 512 (2132968886675984421960) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 = 2187393762355893434580 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12288 512 (2187393762355893434580) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12800 512 = 2238951442074665751552 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12800 512 (2238951442074665751552) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 = 2287641925832305741968 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13312 512 (2287641925832305741968) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13824 512 = 2333465213629797821436 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13824 512 (2333465213629797821436) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 = 2376421305468777355824 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14336 512 (2376421305468777355824) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14848 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14848 512 = 2416510201347157793172 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14848 512 (2416510201347157793172) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15360 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 = 2453731901264406911796 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15360 512 (2453731901264406911796) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15872 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15872 512 = 2488086405220525084236 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15872 512 (2488086405220525084236) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 = 2519573713215515722848 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16384 512 (2519573713215515722848) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16896 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16896 512 = 2548193825249371081248 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16896 512 (2548193825249371081248) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17408 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 = 2573946741322090347600 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17408 512 (2573946741322090347600) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17920 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17920 512 = 2596832461433678953680 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17920 512 (2596832461433678953680) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18432 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 = 2616851179883301219912 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18432 512 (2616851179883301219912) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18944 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18944 512 = 2634014850243535239408 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18944 512 (2634014850243535239408) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19456 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 = 2648367736310169059724 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19456 512 (2648367736310169059724) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19968 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19968 512 = 2659963782200764228704 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19968 512 (2659963782200764228704) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20480 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 = 2668857031108947191616 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20480 512 (2668857031108947191616) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20992 512 = 2675101526230114362252 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20992 512 (2675101526230114362252) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow21504 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 = 2678751310759787749596 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 21504 512 (2678751310759787749596) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22016 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22016 512 = 2679860427893495904300 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22016 512 (2679860427893495904300) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22528 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 = 2678482920826774033224 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22528 512 (2678482920826774033224) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23040 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23040 512 = 2674672832755149864996 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23040 512 (2674672832755149864996) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23552 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 = 2668484206874148932040 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23552 512 (2668484206874148932040) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24064 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24064 512 = 2659971086379305894808 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24064 512 (2659971086379305894808) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24576 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 = 2649187514466556268496 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24576 512 (2649187514466556268496) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25088 512 = 2636187534333567582288 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25088 512 (2636187534333567582288) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25600 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 = 2621025189174482835012 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25600 512 (2621025189174482835012) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26112 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26112 512 = 2603754522183660422736 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26112 512 (2603754522183660422736) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26624 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 = 2584429576556629260828 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26624 512 (2584429576556629260828) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27136 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27136 512 = 2563104395488925848476 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27136 512 (2563104395488925848476) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27648 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 = 2539833022176074376588 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27648 512 (2539833022176074376588) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28160 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28160 512 = 2514669499813603767300 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28160 512 (2514669499813603767300) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28672 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 = 2487667871597045775456 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28672 512 (2487667871597045775456) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29184 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29184 512 = 2458882180721921138784 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29184 512 (2458882180721921138784) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29696 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 = 2428366470383757894036 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29696 512 (2428366470383757894036) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30208 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30208 512 = 2396174783779243416108 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30208 512 (2396174783779243416108) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30720 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 = 2362361164105307546976 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30720 512 (2362361164105307546976) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31232 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31232 512 = 2326979654555341713144 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31232 512 (2326979654555341713144) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31744 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 = 2290084298324460595068 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31744 512 (2290084298324460595068) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32256 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32256 512 = 2251729138608185941632 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32256 512 (2251729138608185941632) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 = 2211968218602049945272 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32768 512 (2211968218602049945272) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33280 512 = 2170855581501580806996 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33280 512 (2170855581501580806996) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33792 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 = 2128445270502300575136 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33792 512 (2128445270502300575136) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34304 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34304 512 = 2084791328799737826948 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34304 512 (2084791328799737826948) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 = 2039947799589427807992 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34816 512 (2039947799589427807992) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35328 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35328 512 = 1993968726067026958176 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35328 512 (1993968726067026958176) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35840 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 = 1946908151429959674768 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35840 512 (1946908151429959674768) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36352 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36352 512 = 1898820118873615372008 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36352 512 (1898820118873615372008) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36864 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 = 1849758671591721669468 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36864 512 (1849758671591721669468) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37376 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37376 512 = 1799777852779724405796 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37376 512 (1799777852779724405796) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37888 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 = 1748931705633148235220 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37888 512 (1748931705633148235220) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38400 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38400 512 = 1697274273347516528436 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38400 512 (1697274273347516528436) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38912 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 = 1644859599118358791464 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38912 512 (1644859599118358791464) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39424 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39424 512 = 1591741726141211555604 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39424 512 (1591741726141211555604) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39936 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 = 1537974697611598911828 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39936 512 (1537974697611598911828) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40448 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40448 512 = 1483612556725049885484 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40448 512 (1483612556725049885484) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40960 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 = 1428709346677616666976 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40960 512 (1428709346677616666976) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41472 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41472 512 = 1373319110666918873544 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41472 512 (1373319110666918873544) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41984 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 = 1317495891886864239900 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41984 512 (1317495891886864239900) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow42496 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 42496 512 = 1261293733531985121216 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 42496 512 (1261293733531985121216) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43008 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 = 1204766678797805855712 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43008 512 (1204766678797805855712) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43520 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43520 512 = 1147968770879857795956 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43520 512 (1147968770879857795956) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44032 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 = 1090954052973677165244 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44032 512 (1090954052973677165244) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44544 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44544 512 = 1033776568274785665552 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44544 512 (1033776568274785665552) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45056 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 = 976490359978715578272 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45056 512 (976490359978715578272) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45568 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45568 512 = 919149471280994999436 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45568 512 (919149471280994999436) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46080 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 = 861807945377153086404 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46080 512 (861807945377153086404) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46592 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46592 512 = 804519825464038363176 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46592 512 (804519825464038363176) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47104 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 = 747339154738328200176 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47104 512 (747339154738328200176) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47616 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47616 512 = 690319976393405815548 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47616 512 (690319976393405815548) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48128 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 = 633516333624472143672 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48128 512 (633516333624472143672) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48640 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48640 512 = 576996076705404391920 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48640 512 (576996076705404391920) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49152 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 = 521913013431731038380 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49152 512 (521913013431731038380) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49664 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49664 512 = 470179380506042587812 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49664 512 (470179380506042587812) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50176 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 = 421958915607595015812 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50176 512 (421958915607595015812) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50688 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50688 512 = 377153476964802583524 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50688 512 (377153476964802583524) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51200 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 = 335638024965472640652 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51200 512 (335638024965472640652) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51712 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51712 512 = 297287090892429950304 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51712 512 (297287090892429950304) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52224 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 = 261975206030169157584 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52224 512 (261975206030169157584) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52736 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52736 512 = 229576901660200295352 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52736 512 (229576901660200295352) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53248 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 = 199966709063815676352 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53248 512 (199966709063815676352) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53760 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53760 512 = 173019159523650884484 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53760 512 (173019159523650884484) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54272 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 = 148608784322351433072 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54272 512 (148608784322351433072) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54784 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54784 512 = 126610114742558601120 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54784 512 (126610114742558601120) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55296 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 = 106897682066914073568 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55296 512 (106897682066914073568) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55808 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55808 512 = 89346017578065426156 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55808 512 (89346017578065426156) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56320 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 = 73829652558659339592 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56320 512 (73829652558659339592) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56832 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56832 512 = 60223118291335167024 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56832 512 (60223118291335167024) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57344 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 = 48400946059324119456 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57344 512 (48400946059324119456) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57856 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57856 512 = 38237667145745491440 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57856 512 (38237667145745491440) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58368 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 = 29607812831779665828 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58368 512 (29607812831779665828) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58880 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58880 410 = 18439071056081532468 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58880 410 (18439071056081532468) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 = 300071704489857940152 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 512 512 (89850660856095601680) (210221043633762338472) secondAdaptiveWindow0 secondAdaptiveWindow512

private theorem secondAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 1024 = 770084451756001415076 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 512 (327724230450296704860) (442360221305704710216) secondAdaptiveWindow1024 secondAdaptiveWindow1536

private theorem secondAdaptiveJoin2048_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 = 1217159631333157254096 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 512 (554129016199978828908) (663030615133178425188) secondAdaptiveWindow2048 secondAdaptiveWindow2560

private theorem secondAdaptiveJoin3072_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 1024 = 1641297243228738632760 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 512 (769065018106954574388) (872232225121784058372) secondAdaptiveWindow3072 secondAdaptiveWindow3584

private theorem secondAdaptiveJoin4096_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 = 2042497287444088017696 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 512 (972532236175669114320) (1069965051268418903376) secondAdaptiveWindow4096 secondAdaptiveWindow4608

private theorem secondAdaptiveJoin5120_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 1024 = 2420759763970548147072 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 512 (1164530670400032587568) (1256229093570515559504) secondAdaptiveWindow5120 secondAdaptiveWindow5632

private theorem secondAdaptiveJoin6144_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 = 2776084672807963092144 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 512 (1345060320779870765952) (1431024352028092326192) secondAdaptiveWindow6144 secondAdaptiveWindow6656

private theorem secondAdaptiveJoin7168_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 1024 = 3108472013956337935440 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 512 (1514121187315187700252) (1594350826641150235188) secondAdaptiveWindow7168 secondAdaptiveWindow7680

private theorem secondAdaptiveJoin8192_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 = 3417921787419090868416 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 512 (1671713270006302399860) (1746208517412788468556) secondAdaptiveWindow8192 secondAdaptiveWindow8704

private theorem secondAdaptiveJoin9216_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 1024 = 3704433993204514541460 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 512 (1817836568859476952144) (1886597424345037589316) secondAdaptiveWindow9216 secondAdaptiveWindow9728

private theorem secondAdaptiveJoin10240_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 = 3968008631302240759452 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 512 (1952491083869469296904) (2015517547432771462548) secondAdaptiveWindow10240 secondAdaptiveWindow10752

private theorem secondAdaptiveJoin11264_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 1024 = 4208645701710925502268 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 512 (2075676815034941080308) (2132968886675984421960) secondAdaptiveWindow11264 secondAdaptiveWindow11776

private theorem secondAdaptiveJoin12288_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 = 4426345204430559186132 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 512 (2187393762355893434580) (2238951442074665751552) secondAdaptiveWindow12288 secondAdaptiveWindow12800

private theorem secondAdaptiveJoin13312_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 1024 = 4621107139462103563404 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 512 (2287641925832305741968) (2333465213629797821436) secondAdaptiveWindow13312 secondAdaptiveWindow13824

private theorem secondAdaptiveJoin14336_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 = 4792931506815935148996 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 512 (2376421305468777355824) (2416510201347157793172) secondAdaptiveWindow14336 secondAdaptiveWindow14848

private theorem secondAdaptiveJoin15360_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 1024 = 4941818306484931996032 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 512 (2453731901264406911796) (2488086405220525084236) secondAdaptiveWindow15360 secondAdaptiveWindow15872

private theorem secondAdaptiveJoin16384_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 = 5067767538464886804096 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 512 (2519573713215515722848) (2548193825249371081248) secondAdaptiveWindow16384 secondAdaptiveWindow16896

private theorem secondAdaptiveJoin17408_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 1024 = 5170779202755769301280 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 512 (2573946741322090347600) (2596832461433678953680) secondAdaptiveWindow17408 secondAdaptiveWindow17920

private theorem secondAdaptiveJoin18432_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 = 5250866030126836459320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 512 (2616851179883301219912) (2634014850243535239408) secondAdaptiveWindow18432 secondAdaptiveWindow18944

private theorem secondAdaptiveJoin19456_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 1024 = 5308331518510933288428 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 512 (2648367736310169059724) (2659963782200764228704) secondAdaptiveWindow19456 secondAdaptiveWindow19968

private theorem secondAdaptiveJoin20480_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 = 5343958557339061553868 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 512 (2668857031108947191616) (2675101526230114362252) secondAdaptiveWindow20480 secondAdaptiveWindow20992

private theorem secondAdaptiveJoin21504_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 1024 = 5358611738653283653896 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 512 (2678751310759787749596) (2679860427893495904300) secondAdaptiveWindow21504 secondAdaptiveWindow22016

private theorem secondAdaptiveJoin22528_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 = 5353155753581923898220 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 512 (2678482920826774033224) (2674672832755149864996) secondAdaptiveWindow22528 secondAdaptiveWindow23040

private theorem secondAdaptiveJoin23552_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 1024 = 5328455293253454826848 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 512 (2668484206874148932040) (2659971086379305894808) secondAdaptiveWindow23552 secondAdaptiveWindow24064

private theorem secondAdaptiveJoin24576_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 = 5285375048800123850784 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 512 (2649187514466556268496) (2636187534333567582288) secondAdaptiveWindow24576 secondAdaptiveWindow25088

private theorem secondAdaptiveJoin25600_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 1024 = 5224779711358143257748 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 512 (2621025189174482835012) (2603754522183660422736) secondAdaptiveWindow25600 secondAdaptiveWindow26112

private theorem secondAdaptiveJoin26624_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 = 5147533972045555109304 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 512 (2584429576556629260828) (2563104395488925848476) secondAdaptiveWindow26624 secondAdaptiveWindow27136

private theorem secondAdaptiveJoin27648_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 1024 = 5054502521989678143888 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 512 (2539833022176074376588) (2514669499813603767300) secondAdaptiveWindow27648 secondAdaptiveWindow28160

private theorem secondAdaptiveJoin28672_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 = 4946550052318966914240 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 512 (2487667871597045775456) (2458882180721921138784) secondAdaptiveWindow28672 secondAdaptiveWindow29184

private theorem secondAdaptiveJoin29696_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 1024 = 4824541254163001310144 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 512 (2428366470383757894036) (2396174783779243416108) secondAdaptiveWindow29696 secondAdaptiveWindow30208

private theorem secondAdaptiveJoin30720_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 = 4689340818660649260120 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 512 (2362361164105307546976) (2326979654555341713144) secondAdaptiveWindow30720 secondAdaptiveWindow31232

private theorem secondAdaptiveJoin31744_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 1024 = 4541813436932646536700 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 512 (2290084298324460595068) (2251729138608185941632) secondAdaptiveWindow31744 secondAdaptiveWindow32256

private theorem secondAdaptiveJoin32768_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 = 4382823800103630752268 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 512 (2211968218602049945272) (2170855581501580806996) secondAdaptiveWindow32768 secondAdaptiveWindow33280

private theorem secondAdaptiveJoin33792_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 1024 = 4213236599302038402084 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 512 (2128445270502300575136) (2084791328799737826948) secondAdaptiveWindow33792 secondAdaptiveWindow34304

private theorem secondAdaptiveJoin34816_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 = 4033916525656454766168 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 512 (2039947799589427807992) (1993968726067026958176) secondAdaptiveWindow34816 secondAdaptiveWindow35328

private theorem secondAdaptiveJoin35840_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 1024 = 3845728270303575046776 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 512 (1946908151429959674768) (1898820118873615372008) secondAdaptiveWindow35840 secondAdaptiveWindow36352

private theorem secondAdaptiveJoin36864_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 = 3649536524371446075264 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 512 (1849758671591721669468) (1799777852779724405796) secondAdaptiveWindow36864 secondAdaptiveWindow37376

private theorem secondAdaptiveJoin37888_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 1024 = 3446205978980664763656 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 512 (1748931705633148235220) (1697274273347516528436) secondAdaptiveWindow37888 secondAdaptiveWindow38400

private theorem secondAdaptiveJoin38912_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 = 3236601325259570347068 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 512 (1644859599118358791464) (1591741726141211555604) secondAdaptiveWindow38912 secondAdaptiveWindow39424

private theorem secondAdaptiveJoin39936_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 1024 = 3021587254336648797312 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 512 (1537974697611598911828) (1483612556725049885484) secondAdaptiveWindow39936 secondAdaptiveWindow40448

private theorem secondAdaptiveJoin40960_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 = 2802028457344535540520 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 512 (1428709346677616666976) (1373319110666918873544) secondAdaptiveWindow40960 secondAdaptiveWindow41472

private theorem secondAdaptiveJoin41984_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 1024 = 2578789625418849361116 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 512 (1317495891886864239900) (1261293733531985121216) secondAdaptiveWindow41984 secondAdaptiveWindow42496

private theorem secondAdaptiveJoin43008_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 = 2352735449677663651668 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 512 (1204766678797805855712) (1147968770879857795956) secondAdaptiveWindow43008 secondAdaptiveWindow43520

private theorem secondAdaptiveJoin44032_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 1024 = 2124730621248462830796 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 512 (1090954052973677165244) (1033776568274785665552) secondAdaptiveWindow44032 secondAdaptiveWindow44544

private theorem secondAdaptiveJoin45056_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 = 1895639831259710577708 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 512 (976490359978715578272) (919149471280994999436) secondAdaptiveWindow45056 secondAdaptiveWindow45568

private theorem secondAdaptiveJoin46080_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 1024 = 1666327770841191449580 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 512 (861807945377153086404) (804519825464038363176) secondAdaptiveWindow46080 secondAdaptiveWindow46592

private theorem secondAdaptiveJoin47104_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 = 1437659131131734015724 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 512 (747339154738328200176) (690319976393405815548) secondAdaptiveWindow47104 secondAdaptiveWindow47616

private theorem secondAdaptiveJoin48128_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 1024 = 1210512410329876535592 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 512 (633516333624472143672) (576996076705404391920) secondAdaptiveWindow48128 secondAdaptiveWindow48640

private theorem secondAdaptiveJoin49152_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 = 992092393937773626192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 512 (521913013431731038380) (470179380506042587812) secondAdaptiveWindow49152 secondAdaptiveWindow49664

private theorem secondAdaptiveJoin50176_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 1024 = 799112392572397599336 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 512 (421958915607595015812) (377153476964802583524) secondAdaptiveWindow50176 secondAdaptiveWindow50688

private theorem secondAdaptiveJoin51200_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 = 632925115857902590956 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 512 (335638024965472640652) (297287090892429950304) secondAdaptiveWindow51200 secondAdaptiveWindow51712

private theorem secondAdaptiveJoin52224_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 1024 = 491552107690369452936 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 512 (261975206030169157584) (229576901660200295352) secondAdaptiveWindow52224 secondAdaptiveWindow52736

private theorem secondAdaptiveJoin53248_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 = 372985868587466560836 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 512 (199966709063815676352) (173019159523650884484) secondAdaptiveWindow53248 secondAdaptiveWindow53760

private theorem secondAdaptiveJoin54272_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 1024 = 275218899064910034192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 512 (148608784322351433072) (126610114742558601120) secondAdaptiveWindow54272 secondAdaptiveWindow54784

private theorem secondAdaptiveJoin55296_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 = 196243699644979499724 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 512 (106897682066914073568) (89346017578065426156) secondAdaptiveWindow55296 secondAdaptiveWindow55808

private theorem secondAdaptiveJoin56320_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 1024 = 134052770849994506616 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 512 (73829652558659339592) (60223118291335167024) secondAdaptiveWindow56320 secondAdaptiveWindow56832

private theorem secondAdaptiveJoin57344_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 = 86638613205069610896 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 512 (48400946059324119456) (38237667145745491440) secondAdaptiveWindow57344 secondAdaptiveWindow57856

private theorem secondAdaptiveJoin58368_922 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 922 = 48046883887861198296 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 410 (29607812831779665828) (18439071056081532468) secondAdaptiveWindow58368 secondAdaptiveWindow58880

private theorem secondAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 = 1070156156245859355228 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 1024 (300071704489857940152) (770084451756001415076) secondAdaptiveJoin0_1024 secondAdaptiveJoin1024_1024

private theorem secondAdaptiveJoin2048_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 2048 = 2858456874561895886856 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 1024 (1217159631333157254096) (1641297243228738632760) secondAdaptiveJoin2048_1024 secondAdaptiveJoin3072_1024

private theorem secondAdaptiveJoin4096_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 = 4463257051414636164768 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 1024 (2042497287444088017696) (2420759763970548147072) secondAdaptiveJoin4096_1024 secondAdaptiveJoin5120_1024

private theorem secondAdaptiveJoin6144_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 2048 = 5884556686764301027584 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 1024 (2776084672807963092144) (3108472013956337935440) secondAdaptiveJoin6144_1024 secondAdaptiveJoin7168_1024

private theorem secondAdaptiveJoin8192_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 = 7122355780623605409876 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 1024 (3417921787419090868416) (3704433993204514541460) secondAdaptiveJoin8192_1024 secondAdaptiveJoin9216_1024

private theorem secondAdaptiveJoin10240_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 2048 = 8176654333013166261720 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 1024 (3968008631302240759452) (4208645701710925502268) secondAdaptiveJoin10240_1024 secondAdaptiveJoin11264_1024

private theorem secondAdaptiveJoin12288_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 = 9047452343892662749536 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 1024 (4426345204430559186132) (4621107139462103563404) secondAdaptiveJoin12288_1024 secondAdaptiveJoin13312_1024

private theorem secondAdaptiveJoin14336_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 2048 = 9734749813300867145028 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 1024 (4792931506815935148996) (4941818306484931996032) secondAdaptiveJoin14336_1024 secondAdaptiveJoin15360_1024

private theorem secondAdaptiveJoin16384_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 = 10238546741220656105376 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 1024 (5067767538464886804096) (5170779202755769301280) secondAdaptiveJoin16384_1024 secondAdaptiveJoin17408_1024

private theorem secondAdaptiveJoin18432_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 2048 = 10559197548637769747748 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 1024 (5250866030126836459320) (5308331518510933288428) secondAdaptiveJoin18432_1024 secondAdaptiveJoin19456_1024

private theorem secondAdaptiveJoin20480_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 = 10702570295992345207764 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 1024 (5343958557339061553868) (5358611738653283653896) secondAdaptiveJoin20480_1024 secondAdaptiveJoin21504_1024

private theorem secondAdaptiveJoin22528_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 2048 = 10681611046835378725068 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 1024 (5353155753581923898220) (5328455293253454826848) secondAdaptiveJoin22528_1024 secondAdaptiveJoin23552_1024

private theorem secondAdaptiveJoin24576_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 = 10510154760158267108532 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 1024 (5285375048800123850784) (5224779711358143257748) secondAdaptiveJoin24576_1024 secondAdaptiveJoin25600_1024

private theorem secondAdaptiveJoin26624_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 2048 = 10202036494035233253192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 1024 (5147533972045555109304) (5054502521989678143888) secondAdaptiveJoin26624_1024 secondAdaptiveJoin27648_1024

private theorem secondAdaptiveJoin28672_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 = 9771091306481968224384 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 1024 (4946550052318966914240) (4824541254163001310144) secondAdaptiveJoin28672_1024 secondAdaptiveJoin29696_1024

private theorem secondAdaptiveJoin30720_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 2048 = 9231154255593295796820 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 1024 (4689340818660649260120) (4541813436932646536700) secondAdaptiveJoin30720_1024 secondAdaptiveJoin31744_1024

private theorem secondAdaptiveJoin32768_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 = 8596060399405669154352 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 1024 (4382823800103630752268) (4213236599302038402084) secondAdaptiveJoin32768_1024 secondAdaptiveJoin33792_1024

private theorem secondAdaptiveJoin34816_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 2048 = 7879644795960029812944 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 1024 (4033916525656454766168) (3845728270303575046776) secondAdaptiveJoin34816_1024 secondAdaptiveJoin35840_1024

private theorem secondAdaptiveJoin36864_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 = 7095742503352110838920 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 1024 (3649536524371446075264) (3446205978980664763656) secondAdaptiveJoin36864_1024 secondAdaptiveJoin37888_1024

private theorem secondAdaptiveJoin38912_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 2048 = 6258188579596219144380 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 1024 (3236601325259570347068) (3021587254336648797312) secondAdaptiveJoin38912_1024 secondAdaptiveJoin39936_1024

private theorem secondAdaptiveJoin40960_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 = 5380818082763384901636 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 1024 (2802028457344535540520) (2578789625418849361116) secondAdaptiveJoin40960_1024 secondAdaptiveJoin41984_1024

private theorem secondAdaptiveJoin43008_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 2048 = 4477466070926126482464 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 1024 (2352735449677663651668) (2124730621248462830796) secondAdaptiveJoin43008_1024 secondAdaptiveJoin44032_1024

private theorem secondAdaptiveJoin45056_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 = 3561967602100902027288 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 1024 (1895639831259710577708) (1666327770841191449580) secondAdaptiveJoin45056_1024 secondAdaptiveJoin46080_1024

private theorem secondAdaptiveJoin47104_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 2048 = 2648171541461610551316 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 1024 (1437659131131734015724) (1210512410329876535592) secondAdaptiveJoin47104_1024 secondAdaptiveJoin48128_1024

private theorem secondAdaptiveJoin49152_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 = 1791204786510171225528 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 1024 (992092393937773626192) (799112392572397599336) secondAdaptiveJoin49152_1024 secondAdaptiveJoin50176_1024

private theorem secondAdaptiveJoin51200_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 2048 = 1124477223548272043892 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 1024 (632925115857902590956) (491552107690369452936) secondAdaptiveJoin51200_1024 secondAdaptiveJoin52224_1024

private theorem secondAdaptiveJoin53248_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 = 648204767652376595028 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 1024 (372985868587466560836) (275218899064910034192) secondAdaptiveJoin53248_1024 secondAdaptiveJoin54272_1024

private theorem secondAdaptiveJoin55296_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 2048 = 330296470494974006340 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 1024 (196243699644979499724) (134052770849994506616) secondAdaptiveJoin55296_1024 secondAdaptiveJoin56320_1024

private theorem secondAdaptiveJoin57344_1946 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 1946 = 134685497092930809192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 922 (86638613205069610896) (48046883887861198296) secondAdaptiveJoin57344_1024 secondAdaptiveJoin58368_922

private theorem secondAdaptiveJoin0_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 = 3928613030807755242084 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 2048 (1070156156245859355228) (2858456874561895886856) secondAdaptiveJoin0_2048 secondAdaptiveJoin2048_2048

private theorem secondAdaptiveJoin4096_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 4096 = 10347813738178937192352 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 2048 (4463257051414636164768) (5884556686764301027584) secondAdaptiveJoin4096_2048 secondAdaptiveJoin6144_2048

private theorem secondAdaptiveJoin8192_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 = 15299010113636771671596 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 2048 (7122355780623605409876) (8176654333013166261720) secondAdaptiveJoin8192_2048 secondAdaptiveJoin10240_2048

private theorem secondAdaptiveJoin12288_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 4096 = 18782202157193529894564 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 2048 (9047452343892662749536) (9734749813300867145028) secondAdaptiveJoin12288_2048 secondAdaptiveJoin14336_2048

private theorem secondAdaptiveJoin16384_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 = 20797744289858425853124 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 2048 (10238546741220656105376) (10559197548637769747748) secondAdaptiveJoin16384_2048 secondAdaptiveJoin18432_2048

private theorem secondAdaptiveJoin20480_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 4096 = 21384181342827723932832 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 2048 (10702570295992345207764) (10681611046835378725068) secondAdaptiveJoin20480_2048 secondAdaptiveJoin22528_2048

private theorem secondAdaptiveJoin24576_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 = 20712191254193500361724 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 2048 (10510154760158267108532) (10202036494035233253192) secondAdaptiveJoin24576_2048 secondAdaptiveJoin26624_2048

private theorem secondAdaptiveJoin28672_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 4096 = 19002245562075264021204 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 2048 (9771091306481968224384) (9231154255593295796820) secondAdaptiveJoin28672_2048 secondAdaptiveJoin30720_2048

private theorem secondAdaptiveJoin32768_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 = 16475705195365698967296 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 2048 (8596060399405669154352) (7879644795960029812944) secondAdaptiveJoin32768_2048 secondAdaptiveJoin34816_2048

private theorem secondAdaptiveJoin36864_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 4096 = 13353931082948329983300 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 2048 (7095742503352110838920) (6258188579596219144380) secondAdaptiveJoin36864_2048 secondAdaptiveJoin38912_2048

private theorem secondAdaptiveJoin40960_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 = 9858284153689511384100 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 2048 (5380818082763384901636) (4477466070926126482464) secondAdaptiveJoin40960_2048 secondAdaptiveJoin43008_2048

private theorem secondAdaptiveJoin45056_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 4096 = 6210139143562512578604 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 2048 (3561967602100902027288) (2648171541461610551316) secondAdaptiveJoin45056_2048 secondAdaptiveJoin47104_2048

private theorem secondAdaptiveJoin49152_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 = 2915682010058443269420 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 2048 (1791204786510171225528) (1124477223548272043892) secondAdaptiveJoin49152_2048 secondAdaptiveJoin51200_2048

private theorem secondAdaptiveJoin53248_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 4096 = 978501238147350601368 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 2048 (648204767652376595028) (330296470494974006340) secondAdaptiveJoin53248_2048 secondAdaptiveJoin55296_2048

private theorem secondAdaptiveJoin0_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 = 14276426768986692434436 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 4096 (3928613030807755242084) (10347813738178937192352) secondAdaptiveJoin0_4096 secondAdaptiveJoin4096_4096

private theorem secondAdaptiveJoin8192_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 8192 = 34081212270830301566160 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 4096 (15299010113636771671596) (18782202157193529894564) secondAdaptiveJoin8192_4096 secondAdaptiveJoin12288_4096

private theorem secondAdaptiveJoin16384_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 = 42181925632686149785956 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 4096 (20797744289858425853124) (21384181342827723932832) secondAdaptiveJoin16384_4096 secondAdaptiveJoin20480_4096

private theorem secondAdaptiveJoin24576_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 8192 = 39714436816268764382928 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 4096 (20712191254193500361724) (19002245562075264021204) secondAdaptiveJoin24576_4096 secondAdaptiveJoin28672_4096

private theorem secondAdaptiveJoin32768_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 = 29829636278314028950596 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 4096 (16475705195365698967296) (13353931082948329983300) secondAdaptiveJoin32768_4096 secondAdaptiveJoin36864_4096

private theorem secondAdaptiveJoin40960_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 8192 = 16068423297252023962704 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 4096 (9858284153689511384100) (6210139143562512578604) secondAdaptiveJoin40960_4096 secondAdaptiveJoin45056_4096

private theorem secondAdaptiveJoin49152_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 = 3894183248205793870788 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 4096 (2915682010058443269420) (978501238147350601368) secondAdaptiveJoin49152_4096 secondAdaptiveJoin53248_4096

private theorem secondAdaptiveJoin0_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 = 48357639039816994000596 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 8192 (14276426768986692434436) (34081212270830301566160) secondAdaptiveJoin0_8192 secondAdaptiveJoin8192_8192

private theorem secondAdaptiveJoin16384_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 16384 = 81896362448954914168884 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 8192 (42181925632686149785956) (39714436816268764382928) secondAdaptiveJoin16384_8192 secondAdaptiveJoin24576_8192

private theorem secondAdaptiveJoin32768_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 = 45898059575566052913300 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 8192 (29829636278314028950596) (16068423297252023962704) secondAdaptiveJoin32768_8192 secondAdaptiveJoin40960_8192

private theorem secondAdaptiveJoin49152_10138 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 10138 = 4028868745298724679980 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 1946 (3894183248205793870788) (134685497092930809192) secondAdaptiveJoin49152_8192 secondAdaptiveJoin57344_1946

private theorem secondAdaptiveJoin0_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 = 130254001488771908169480 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 16384 (48357639039816994000596) (81896362448954914168884) secondAdaptiveJoin0_16384 secondAdaptiveJoin16384_16384

private theorem secondAdaptiveJoin32768_26522 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 26522 = 49926928320864777593280 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 10138 (45898059575566052913300) (4028868745298724679980) secondAdaptiveJoin32768_16384 secondAdaptiveJoin49152_10138

private theorem secondAdaptiveJoin0_59290 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 59290 = 180180929809636685762760 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 26522 (130254001488771908169480) (49926928320864777593280) secondAdaptiveJoin0_32768 secondAdaptiveJoin32768_26522

theorem secondAdaptive_firstJetGap_eq : firstJetGap secondAdaptiveShape 0 = secondAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondAdaptiveShape 0 59290 (180180929809636685762760) rfl secondAdaptiveJoin0_59290]
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

private theorem contact00OrdinaryColumns : ordinaryColumnCount contact00 = 2514639327658999 := by decide +kernel
private theorem contact00ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact00) 0 4 = 6881710040992 :=
  contactColumnsWindow_fast contact00 0 4 6881710040992 (by decide +kernel)
private theorem contact00ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact00) 4 4 = 6543766881184 :=
  contactColumnsWindow_fast contact00 4 4 6543766881184 (by decide +kernel)
private theorem contact00ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact00) 8 4 = 6214365516572 :=
  contactColumnsWindow_fast contact00 8 4 6214365516572 (by decide +kernel)
private theorem contact00ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact00) 12 4 = 5893508750616 :=
  contactColumnsWindow_fast contact00 12 4 5893508750616 (by decide +kernel)
private theorem contact00ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact00) 16 4 = 5581194672475 :=
  contactColumnsWindow_fast contact00 16 4 5581194672475 (by decide +kernel)
private theorem contact00ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact00) 20 4 = 5277425191804 :=
  contactColumnsWindow_fast contact00 20 4 5277425191804 (by decide +kernel)
private theorem contact00ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact00) 24 4 = 4982215122892 :=
  contactColumnsWindow_fast contact00 24 4 4982215122892 (by decide +kernel)
private theorem contact00ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact00) 28 4 = 4695582162250 :=
  contactColumnsWindow_fast contact00 28 4 4695582162250 (by decide +kernel)
private theorem contact00ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact00) 32 4 = 4417496871760 :=
  contactColumnsWindow_fast contact00 32 4 4417496871760 (by decide +kernel)
private theorem contact00ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact00) 36 4 = 4147957331421 :=
  contactColumnsWindow_fast contact00 36 4 4147957331421 (by decide +kernel)
private theorem contact00ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact00) 40 4 = 3886965432820 :=
  contactColumnsWindow_fast contact00 40 4 3886965432820 (by decide +kernel)
private theorem contact00ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact00) 44 4 = 3634539654169 :=
  contactColumnsWindow_fast contact00 44 4 3634539654169 (by decide +kernel)
private theorem contact00ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact00) 48 4 = 3390691499098 :=
  contactColumnsWindow_fast contact00 48 4 3390691499098 (by decide +kernel)
private theorem contact00ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact00) 52 4 = 3155392688752 :=
  contactColumnsWindow_fast contact00 52 4 3155392688752 (by decide +kernel)
private theorem contact00ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact00) 56 4 = 2928643879742 :=
  contactColumnsWindow_fast contact00 56 4 2928643879742 (by decide +kernel)
private theorem contact00ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact00) 60 4 = 2710444777710 :=
  contactColumnsWindow_fast contact00 60 4 2710444777710 (by decide +kernel)
private theorem contact00ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact00) 64 4 = 2500821126055 :=
  contactColumnsWindow_fast contact00 64 4 2500821126055 (by decide +kernel)
private theorem contact00ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact00) 68 4 = 2299772636065 :=
  contactColumnsWindow_fast contact00 68 4 2299772636065 (by decide +kernel)
private theorem contact00ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact00) 72 4 = 2107278372156 :=
  contactColumnsWindow_fast contact00 72 4 2107278372156 (by decide +kernel)
private theorem contact00ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact00) 76 4 = 1923334587530 :=
  contactColumnsWindow_fast contact00 76 4 1923334587530 (by decide +kernel)
private theorem contact00ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact00) 80 4 = 1747940288586 :=
  contactColumnsWindow_fast contact00 80 4 1747940288586 (by decide +kernel)
private theorem contact00ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact00) 84 4 = 1581126333742 :=
  contactColumnsWindow_fast contact00 84 4 1581126333742 (by decide +kernel)
private theorem contact00ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact00) 88 4 = 1422883297415 :=
  contactColumnsWindow_fast contact00 88 4 1422883297415 (by decide +kernel)
private theorem contact00ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact00) 92 4 = 1273194007836 :=
  contactColumnsWindow_fast contact00 92 4 1273194007836 (by decide +kernel)
private theorem contact00ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact00) 96 4 = 1132055218502 :=
  contactColumnsWindow_fast contact00 96 4 1132055218502 (by decide +kernel)
private theorem contact00ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact00) 100 4 = 999466840689 :=
  contactColumnsWindow_fast contact00 100 4 999466840689 (by decide +kernel)
private theorem contact00ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact00) 104 4 = 875461547962 :=
  contactColumnsWindow_fast contact00 104 4 875461547962 (by decide +kernel)
private theorem contact00ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact00) 108 4 = 760023926741 :=
  contactColumnsWindow_fast contact00 108 4 760023926741 (by decide +kernel)
private theorem contact00ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact00) 112 4 = 653139636263 :=
  contactColumnsWindow_fast contact00 112 4 653139636263 (by decide +kernel)
private theorem contact00ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact00) 116 4 = 554805902164 :=
  contactColumnsWindow_fast contact00 116 4 554805902164 (by decide +kernel)
private theorem contact00ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact00) 120 4 = 465023619231 :=
  contactColumnsWindow_fast contact00 120 4 465023619231 (by decide +kernel)
private theorem contact00ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact00) 124 4 = 383826686107 :=
  contactColumnsWindow_fast contact00 124 4 383826686107 (by decide +kernel)
private theorem contact00ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact00) 128 4 = 311194601386 :=
  contactColumnsWindow_fast contact00 128 4 311194601386 (by decide +kernel)
private theorem contact00ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact00) 132 4 = 247115376269 :=
  contactColumnsWindow_fast contact00 132 4 247115376269 (by decide +kernel)
private theorem contact00ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact00) 136 4 = 191579516252 :=
  contactColumnsWindow_fast contact00 136 4 191579516252 (by decide +kernel)
private theorem contact00ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact00) 140 4 = 144485903602 :=
  contactColumnsWindow_fast contact00 140 4 144485903602 (by decide +kernel)
private theorem contact00ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact00) 144 4 = 105564825670 :=
  contactColumnsWindow_fast contact00 144 4 105564825670 (by decide +kernel)
private theorem contact00ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact00) 148 4 = 74317532059 :=
  contactColumnsWindow_fast contact00 148 4 74317532059 (by decide +kernel)
private theorem contact00ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact00) 152 4 = 50100818710 :=
  contactColumnsWindow_fast contact00 152 4 50100818710 (by decide +kernel)
private theorem contact00ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact00) 156 4 = 32118270359 :=
  contactColumnsWindow_fast contact00 156 4 32118270359 (by decide +kernel)
private theorem contact00ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact00) 160 1 = 5861507185 :=
  contactColumnsWindow_fast contact00 160 1 5861507185 (by decide +kernel)
private theorem contact00ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact00) 0 8 = 13425476922176 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 4 4 6881710040992 6543766881184 contact00ColumnsSlice0 contact00ColumnsSlice4
private theorem contact00ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact00) 8 8 = 12107874267188 :=
  combineSlices (auxiliaryColumnSlice contact00) 8 4 4 6214365516572 5893508750616 contact00ColumnsSlice8 contact00ColumnsSlice12
private theorem contact00ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact00) 16 8 = 10858619864279 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 4 4 5581194672475 5277425191804 contact00ColumnsSlice16 contact00ColumnsSlice20
private theorem contact00ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact00) 24 8 = 9677797285142 :=
  combineSlices (auxiliaryColumnSlice contact00) 24 4 4 4982215122892 4695582162250 contact00ColumnsSlice24 contact00ColumnsSlice28
private theorem contact00ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact00) 32 8 = 8565454203181 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 4 4 4417496871760 4147957331421 contact00ColumnsSlice32 contact00ColumnsSlice36
private theorem contact00ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact00) 40 8 = 7521505086989 :=
  combineSlices (auxiliaryColumnSlice contact00) 40 4 4 3886965432820 3634539654169 contact00ColumnsSlice40 contact00ColumnsSlice44
private theorem contact00ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact00) 48 8 = 6546084187850 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 4 4 3390691499098 3155392688752 contact00ColumnsSlice48 contact00ColumnsSlice52
private theorem contact00ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact00) 56 8 = 5639088657452 :=
  combineSlices (auxiliaryColumnSlice contact00) 56 4 4 2928643879742 2710444777710 contact00ColumnsSlice56 contact00ColumnsSlice60
private theorem contact00ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact00) 64 8 = 4800593762120 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 4 4 2500821126055 2299772636065 contact00ColumnsSlice64 contact00ColumnsSlice68
private theorem contact00ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact00) 72 8 = 4030612959686 :=
  combineSlices (auxiliaryColumnSlice contact00) 72 4 4 2107278372156 1923334587530 contact00ColumnsSlice72 contact00ColumnsSlice76
private theorem contact00ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact00) 80 8 = 3329066622328 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 4 4 1747940288586 1581126333742 contact00ColumnsSlice80 contact00ColumnsSlice84
private theorem contact00ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact00) 88 8 = 2696077305251 :=
  combineSlices (auxiliaryColumnSlice contact00) 88 4 4 1422883297415 1273194007836 contact00ColumnsSlice88 contact00ColumnsSlice92
private theorem contact00ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact00) 96 8 = 2131522059191 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 4 4 1132055218502 999466840689 contact00ColumnsSlice96 contact00ColumnsSlice100
private theorem contact00ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact00) 104 8 = 1635485474703 :=
  combineSlices (auxiliaryColumnSlice contact00) 104 4 4 875461547962 760023926741 contact00ColumnsSlice104 contact00ColumnsSlice108
private theorem contact00ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact00) 112 8 = 1207945538427 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 4 4 653139636263 554805902164 contact00ColumnsSlice112 contact00ColumnsSlice116
private theorem contact00ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact00) 120 8 = 848850305338 :=
  combineSlices (auxiliaryColumnSlice contact00) 120 4 4 465023619231 383826686107 contact00ColumnsSlice120 contact00ColumnsSlice124
private theorem contact00ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact00) 128 8 = 558309977655 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 4 4 311194601386 247115376269 contact00ColumnsSlice128 contact00ColumnsSlice132
private theorem contact00ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact00) 136 8 = 336065419854 :=
  combineSlices (auxiliaryColumnSlice contact00) 136 4 4 191579516252 144485903602 contact00ColumnsSlice136 contact00ColumnsSlice140
private theorem contact00ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact00) 144 8 = 179882357729 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 4 4 105564825670 74317532059 contact00ColumnsSlice144 contact00ColumnsSlice148
private theorem contact00ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact00) 152 8 = 82219089069 :=
  combineSlices (auxiliaryColumnSlice contact00) 152 4 4 50100818710 32118270359 contact00ColumnsSlice152 contact00ColumnsSlice156
private theorem contact00ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact00) 0 16 = 25533351189364 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 8 8 13425476922176 12107874267188 contact00ColumnsJoin0_8 contact00ColumnsJoin8_8
private theorem contact00ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact00) 16 16 = 20536417149421 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 8 8 10858619864279 9677797285142 contact00ColumnsJoin16_8 contact00ColumnsJoin24_8
private theorem contact00ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact00) 32 16 = 16086959290170 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 8 8 8565454203181 7521505086989 contact00ColumnsJoin32_8 contact00ColumnsJoin40_8
private theorem contact00ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact00) 48 16 = 12185172845302 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 8 8 6546084187850 5639088657452 contact00ColumnsJoin48_8 contact00ColumnsJoin56_8
private theorem contact00ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact00) 64 16 = 8831206721806 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 8 8 4800593762120 4030612959686 contact00ColumnsJoin64_8 contact00ColumnsJoin72_8
private theorem contact00ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact00) 80 16 = 6025143927579 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 8 8 3329066622328 2696077305251 contact00ColumnsJoin80_8 contact00ColumnsJoin88_8
private theorem contact00ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact00) 96 16 = 3767007533894 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 8 8 2131522059191 1635485474703 contact00ColumnsJoin96_8 contact00ColumnsJoin104_8
private theorem contact00ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact00) 112 16 = 2056795843765 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 8 8 1207945538427 848850305338 contact00ColumnsJoin112_8 contact00ColumnsJoin120_8
private theorem contact00ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact00) 128 16 = 894375397509 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 8 8 558309977655 336065419854 contact00ColumnsJoin128_8 contact00ColumnsJoin136_8
private theorem contact00ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact00) 144 16 = 262101446798 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 8 8 179882357729 82219089069 contact00ColumnsJoin144_8 contact00ColumnsJoin152_8
private theorem contact00ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact00) 0 32 = 46069768338785 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 16 16 25533351189364 20536417149421 contact00ColumnsJoin0_16 contact00ColumnsJoin16_16
private theorem contact00ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact00) 32 32 = 28272132135472 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 16 16 16086959290170 12185172845302 contact00ColumnsJoin32_16 contact00ColumnsJoin48_16
private theorem contact00ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact00) 64 32 = 14856350649385 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 16 16 8831206721806 6025143927579 contact00ColumnsJoin64_16 contact00ColumnsJoin80_16
private theorem contact00ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact00) 96 32 = 5823803377659 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 16 16 3767007533894 2056795843765 contact00ColumnsJoin96_16 contact00ColumnsJoin112_16
private theorem contact00ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact00) 128 32 = 1156476844307 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 16 16 894375397509 262101446798 contact00ColumnsJoin128_16 contact00ColumnsJoin144_16
private theorem contact00ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact00) 0 64 = 74341900474257 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 32 32 46069768338785 28272132135472 contact00ColumnsJoin0_32 contact00ColumnsJoin32_32
private theorem contact00ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact00) 64 64 = 20680154027044 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 32 32 14856350649385 5823803377659 contact00ColumnsJoin64_32 contact00ColumnsJoin96_32
private theorem contact00ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact00) 128 33 = 1162338351492 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 32 1 1156476844307 5861507185 contact00ColumnsJoin128_32 contact00ColumnsSlice160
private theorem contact00ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact00) 0 128 = 95022054501301 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 64 64 74341900474257 20680154027044 contact00ColumnsJoin0_64 contact00ColumnsJoin64_64
private theorem contact00ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact00) 0 161 = 96184392852793 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 128 33 95022054501301 1162338351492 contact00ColumnsJoin0_128 contact00ColumnsJoin128_33
private theorem contact00OrdinaryRanks : ordinaryRankBound contact00 = 9668205087 := by decide +kernel
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
private theorem contact00RanksSlice148 : sliceWindow (auxiliaryRankSlice contact00) 148 13 = 0 :=
  contactRankWindow_of_rec contact00 148 13 0 (by decide +kernel)
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
private theorem contact00RanksJoin144_17 : sliceWindow (auxiliaryRankSlice contact00) 144 17 = 903 :=
  combineSlices (auxiliaryRankSlice contact00) 144 4 13 903 0 contact00RanksSlice144 contact00RanksSlice148
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
private theorem contact00RanksJoin128_33 : sliceWindow (auxiliaryRankSlice contact00) 128 33 = 383164 :=
  combineSlices (auxiliaryRankSlice contact00) 128 16 17 382261 903 contact00RanksJoin128_16 contact00RanksJoin144_17
private theorem contact00RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact00) 0 64 = 248692670 :=
  combineSlices (auxiliaryRankSlice contact00) 0 32 32 164323616 84369054 contact00RanksJoin0_32 contact00RanksJoin32_32
private theorem contact00RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact00) 64 64 = 42217762 :=
  combineSlices (auxiliaryRankSlice contact00) 64 32 32 33923973 8293789 contact00RanksJoin64_32 contact00RanksJoin96_32
private theorem contact00RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact00) 0 128 = 290910432 :=
  combineSlices (auxiliaryRankSlice contact00) 0 64 64 248692670 42217762 contact00RanksJoin0_64 contact00RanksJoin64_64
private theorem contact00RanksJoin0_161 : sliceWindow (auxiliaryRankSlice contact00) 0 161 = 291293596 :=
  combineSlices (auxiliaryRankSlice contact00) 0 128 33 290910432 383164 contact00RanksJoin0_128 contact00RanksJoin128_33
theorem contact00_margin : sourceMargin contact00 :=
  margin_of_checked_counts contact00 161 2514639327658999 96184392852793 9668205087 291293596 rfl contact00OrdinaryColumns contact00ColumnsJoin0_161 contact00OrdinaryRanks contact00RanksJoin0_161 (by decide +kernel)

private theorem contact02OrdinaryColumns : ordinaryColumnCount contact02 = 3647479744921410 := by decide +kernel
private theorem contact02ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact02) 0 4 = 11545475604498 :=
  contactColumnsWindow_fast contact02 0 4 11545475604498 (by decide +kernel)
private theorem contact02ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact02) 4 4 = 11028702586834 :=
  contactColumnsWindow_fast contact02 4 4 11028702586834 (by decide +kernel)
private theorem contact02ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact02) 8 4 = 10523826061778 :=
  contactColumnsWindow_fast contact02 8 4 10523826061778 (by decide +kernel)
private theorem contact02ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact02) 12 4 = 10030846029330 :=
  contactColumnsWindow_fast contact02 12 4 10030846029330 (by decide +kernel)
private theorem contact02ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact02) 16 4 = 9549762489490 :=
  contactColumnsWindow_fast contact02 16 4 9549762489490 (by decide +kernel)
private theorem contact02ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact02) 20 4 = 9080575442258 :=
  contactColumnsWindow_fast contact02 20 4 9080575442258 (by decide +kernel)
private theorem contact02ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact02) 24 4 = 8623284887634 :=
  contactColumnsWindow_fast contact02 24 4 8623284887634 (by decide +kernel)
private theorem contact02ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact02) 28 4 = 8177890825618 :=
  contactColumnsWindow_fast contact02 28 4 8177890825618 (by decide +kernel)
private theorem contact02ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact02) 32 4 = 7744393256210 :=
  contactColumnsWindow_fast contact02 32 4 7744393256210 (by decide +kernel)
private theorem contact02ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact02) 36 4 = 7322792179410 :=
  contactColumnsWindow_fast contact02 36 4 7322792179410 (by decide +kernel)
private theorem contact02ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact02) 40 4 = 6913087595218 :=
  contactColumnsWindow_fast contact02 40 4 6913087595218 (by decide +kernel)
private theorem contact02ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact02) 44 4 = 6515279503634 :=
  contactColumnsWindow_fast contact02 44 4 6515279503634 (by decide +kernel)
private theorem contact02ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact02) 48 4 = 6129367904658 :=
  contactColumnsWindow_fast contact02 48 4 6129367904658 (by decide +kernel)
private theorem contact02ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact02) 52 4 = 5755352798290 :=
  contactColumnsWindow_fast contact02 52 4 5755352798290 (by decide +kernel)
private theorem contact02ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact02) 56 4 = 5393242619372 :=
  contactColumnsWindow_fast contact02 56 4 5393242619372 (by decide +kernel)
private theorem contact02ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact02) 60 4 = 5043095626182 :=
  contactColumnsWindow_fast contact02 60 4 5043095626182 (by decide +kernel)
private theorem contact02ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact02) 64 4 = 4704859940256 :=
  contactColumnsWindow_fast contact02 64 4 4704859940256 (by decide +kernel)
private theorem contact02ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact02) 68 4 = 4378525476378 :=
  contactColumnsWindow_fast contact02 68 4 4378525476378 (by decide +kernel)
private theorem contact02ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact02) 72 4 = 4064089681582 :=
  contactColumnsWindow_fast contact02 72 4 4064089681582 (by decide +kernel)
private theorem contact02ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact02) 76 4 = 3761567648244 :=
  contactColumnsWindow_fast contact02 76 4 3761567648244 (by decide +kernel)
private theorem contact02ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact02) 80 4 = 3471011419143 :=
  contactColumnsWindow_fast contact02 80 4 3471011419143 (by decide +kernel)
private theorem contact02ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact02) 84 4 = 3192366984470 :=
  contactColumnsWindow_fast contact02 84 4 3192366984470 (by decide +kernel)
private theorem contact02ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact02) 88 4 = 2925626976594 :=
  contactColumnsWindow_fast contact02 88 4 2925626976594 (by decide +kernel)
private theorem contact02ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact02) 92 4 = 2670789538045 :=
  contactColumnsWindow_fast contact02 92 4 2670789538045 (by decide +kernel)
private theorem contact02ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact02) 96 4 = 2427874181393 :=
  contactColumnsWindow_fast contact02 96 4 2427874181393 (by decide +kernel)
private theorem contact02ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact02) 100 4 = 2196927910654 :=
  contactColumnsWindow_fast contact02 100 4 2196927910654 (by decide +kernel)
private theorem contact02ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact02) 104 4 = 1977894272195 :=
  contactColumnsWindow_fast contact02 104 4 1977894272195 (by decide +kernel)
private theorem contact02ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact02) 108 4 = 1770767966589 :=
  contactColumnsWindow_fast contact02 108 4 1770767966589 (by decide +kernel)
private theorem contact02ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact02) 112 4 = 1575549728490 :=
  contactColumnsWindow_fast contact02 112 4 1575549728490 (by decide +kernel)
private theorem contact02ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact02) 116 4 = 1392261367337 :=
  contactColumnsWindow_fast contact02 116 4 1392261367337 (by decide +kernel)
private theorem contact02ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact02) 120 4 = 1220938030135 :=
  contactColumnsWindow_fast contact02 120 4 1220938030135 (by decide +kernel)
private theorem contact02ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact02) 124 4 = 1061525443332 :=
  contactColumnsWindow_fast contact02 124 4 1061525443332 (by decide +kernel)
private theorem contact02ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact02) 128 4 = 914020250394 :=
  contactColumnsWindow_fast contact02 128 4 914020250394 (by decide +kernel)
private theorem contact02ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact02) 132 4 = 778423183413 :=
  contactColumnsWindow_fast contact02 132 4 778423183413 (by decide +kernel)
private theorem contact02ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact02) 136 4 = 654761660573 :=
  contactColumnsWindow_fast contact02 136 4 654761660573 (by decide +kernel)
private theorem contact02ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact02) 140 4 = 543061353094 :=
  contactColumnsWindow_fast contact02 140 4 543061353094 (by decide +kernel)
private theorem contact02ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact02) 144 4 = 443269793296 :=
  contactColumnsWindow_fast contact02 144 4 443269793296 (by decide +kernel)
private theorem contact02ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact02) 148 4 = 355360805577 :=
  contactColumnsWindow_fast contact02 148 4 355360805577 (by decide +kernel)
private theorem contact02ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact02) 152 4 = 279162185381 :=
  contactColumnsWindow_fast contact02 152 4 279162185381 (by decide +kernel)
private theorem contact02ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact02) 156 4 = 214331932828 :=
  contactColumnsWindow_fast contact02 156 4 214331932828 (by decide +kernel)
private theorem contact02ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact02) 160 4 = 160336795507 :=
  contactColumnsWindow_fast contact02 160 4 160336795507 (by decide +kernel)
private theorem contact02ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact02) 164 4 = 116422059037 :=
  contactColumnsWindow_fast contact02 164 4 116422059037 (by decide +kernel)
private theorem contact02ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact02) 168 4 = 81718285922 :=
  contactColumnsWindow_fast contact02 168 4 81718285922 (by decide +kernel)
private theorem contact02ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact02) 172 4 = 55196129172 :=
  contactColumnsWindow_fast contact02 172 4 55196129172 (by decide +kernel)
private theorem contact02ColumnsSlice176 : sliceWindow (auxiliaryColumnSlice contact02) 176 1 = 10504046328 :=
  contactColumnsWindow_fast contact02 176 1 10504046328 (by decide +kernel)
private theorem contact02ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact02) 0 8 = 22574178191332 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 4 4 11545475604498 11028702586834 contact02ColumnsSlice0 contact02ColumnsSlice4
private theorem contact02ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact02) 8 8 = 20554672091108 :=
  combineSlices (auxiliaryColumnSlice contact02) 8 4 4 10523826061778 10030846029330 contact02ColumnsSlice8 contact02ColumnsSlice12
private theorem contact02ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact02) 16 8 = 18630337931748 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 4 4 9549762489490 9080575442258 contact02ColumnsSlice16 contact02ColumnsSlice20
private theorem contact02ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact02) 24 8 = 16801175713252 :=
  combineSlices (auxiliaryColumnSlice contact02) 24 4 4 8623284887634 8177890825618 contact02ColumnsSlice24 contact02ColumnsSlice28
private theorem contact02ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact02) 32 8 = 15067185435620 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 4 4 7744393256210 7322792179410 contact02ColumnsSlice32 contact02ColumnsSlice36
private theorem contact02ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact02) 40 8 = 13428367098852 :=
  combineSlices (auxiliaryColumnSlice contact02) 40 4 4 6913087595218 6515279503634 contact02ColumnsSlice40 contact02ColumnsSlice44
private theorem contact02ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact02) 48 8 = 11884720702948 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 4 4 6129367904658 5755352798290 contact02ColumnsSlice48 contact02ColumnsSlice52
private theorem contact02ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact02) 56 8 = 10436338245554 :=
  combineSlices (auxiliaryColumnSlice contact02) 56 4 4 5393242619372 5043095626182 contact02ColumnsSlice56 contact02ColumnsSlice60
private theorem contact02ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact02) 64 8 = 9083385416634 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 4 4 4704859940256 4378525476378 contact02ColumnsSlice64 contact02ColumnsSlice68
private theorem contact02ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact02) 72 8 = 7825657329826 :=
  combineSlices (auxiliaryColumnSlice contact02) 72 4 4 4064089681582 3761567648244 contact02ColumnsSlice72 contact02ColumnsSlice76
private theorem contact02ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact02) 80 8 = 6663378403613 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 4 4 3471011419143 3192366984470 contact02ColumnsSlice80 contact02ColumnsSlice84
private theorem contact02ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact02) 88 8 = 5596416514639 :=
  combineSlices (auxiliaryColumnSlice contact02) 88 4 4 2925626976594 2670789538045 contact02ColumnsSlice88 contact02ColumnsSlice92
private theorem contact02ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact02) 96 8 = 4624802092047 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 4 4 2427874181393 2196927910654 contact02ColumnsSlice96 contact02ColumnsSlice100
private theorem contact02ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact02) 104 8 = 3748662238784 :=
  combineSlices (auxiliaryColumnSlice contact02) 104 4 4 1977894272195 1770767966589 contact02ColumnsSlice104 contact02ColumnsSlice108
private theorem contact02ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact02) 112 8 = 2967811095827 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 4 4 1575549728490 1392261367337 contact02ColumnsSlice112 contact02ColumnsSlice116
private theorem contact02ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact02) 120 8 = 2282463473467 :=
  combineSlices (auxiliaryColumnSlice contact02) 120 4 4 1220938030135 1061525443332 contact02ColumnsSlice120 contact02ColumnsSlice124
private theorem contact02ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact02) 128 8 = 1692443433807 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 4 4 914020250394 778423183413 contact02ColumnsSlice128 contact02ColumnsSlice132
private theorem contact02ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact02) 136 8 = 1197823013667 :=
  combineSlices (auxiliaryColumnSlice contact02) 136 4 4 654761660573 543061353094 contact02ColumnsSlice136 contact02ColumnsSlice140
private theorem contact02ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact02) 144 8 = 798630598873 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 4 4 443269793296 355360805577 contact02ColumnsSlice144 contact02ColumnsSlice148
private theorem contact02ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact02) 152 8 = 493494118209 :=
  combineSlices (auxiliaryColumnSlice contact02) 152 4 4 279162185381 214331932828 contact02ColumnsSlice152 contact02ColumnsSlice156
private theorem contact02ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact02) 160 8 = 276758854544 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 4 4 160336795507 116422059037 contact02ColumnsSlice160 contact02ColumnsSlice164
private theorem contact02ColumnsJoin168_8 : sliceWindow (auxiliaryColumnSlice contact02) 168 8 = 136914415094 :=
  combineSlices (auxiliaryColumnSlice contact02) 168 4 4 81718285922 55196129172 contact02ColumnsSlice168 contact02ColumnsSlice172
private theorem contact02ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact02) 0 16 = 43128850282440 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 8 8 22574178191332 20554672091108 contact02ColumnsJoin0_8 contact02ColumnsJoin8_8
private theorem contact02ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact02) 16 16 = 35431513645000 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 8 8 18630337931748 16801175713252 contact02ColumnsJoin16_8 contact02ColumnsJoin24_8
private theorem contact02ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact02) 32 16 = 28495552534472 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 8 8 15067185435620 13428367098852 contact02ColumnsJoin32_8 contact02ColumnsJoin40_8
private theorem contact02ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact02) 48 16 = 22321058948502 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 8 8 11884720702948 10436338245554 contact02ColumnsJoin48_8 contact02ColumnsJoin56_8
private theorem contact02ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact02) 64 16 = 16909042746460 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 8 8 9083385416634 7825657329826 contact02ColumnsJoin64_8 contact02ColumnsJoin72_8
private theorem contact02ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact02) 80 16 = 12259794918252 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 8 8 6663378403613 5596416514639 contact02ColumnsJoin80_8 contact02ColumnsJoin88_8
private theorem contact02ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact02) 96 16 = 8373464330831 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 8 8 4624802092047 3748662238784 contact02ColumnsJoin96_8 contact02ColumnsJoin104_8
private theorem contact02ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact02) 112 16 = 5250274569294 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 8 8 2967811095827 2282463473467 contact02ColumnsJoin112_8 contact02ColumnsJoin120_8
private theorem contact02ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact02) 128 16 = 2890266447474 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 8 8 1692443433807 1197823013667 contact02ColumnsJoin128_8 contact02ColumnsJoin136_8
private theorem contact02ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact02) 144 16 = 1292124717082 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 8 8 798630598873 493494118209 contact02ColumnsJoin144_8 contact02ColumnsJoin152_8
private theorem contact02ColumnsJoin160_16 : sliceWindow (auxiliaryColumnSlice contact02) 160 16 = 413673269638 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 8 8 276758854544 136914415094 contact02ColumnsJoin160_8 contact02ColumnsJoin168_8
private theorem contact02ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact02) 0 32 = 78560363927440 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 16 16 43128850282440 35431513645000 contact02ColumnsJoin0_16 contact02ColumnsJoin16_16
private theorem contact02ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact02) 32 32 = 50816611482974 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 16 16 28495552534472 22321058948502 contact02ColumnsJoin32_16 contact02ColumnsJoin48_16
private theorem contact02ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact02) 64 32 = 29168837664712 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 16 16 16909042746460 12259794918252 contact02ColumnsJoin64_16 contact02ColumnsJoin80_16
private theorem contact02ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact02) 96 32 = 13623738900125 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 16 16 8373464330831 5250274569294 contact02ColumnsJoin96_16 contact02ColumnsJoin112_16
private theorem contact02ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact02) 128 32 = 4182391164556 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 16 16 2890266447474 1292124717082 contact02ColumnsJoin128_16 contact02ColumnsJoin144_16
private theorem contact02ColumnsJoin160_17 : sliceWindow (auxiliaryColumnSlice contact02) 160 17 = 424177315966 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 16 1 413673269638 10504046328 contact02ColumnsJoin160_16 contact02ColumnsSlice176
private theorem contact02ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact02) 0 64 = 129376975410414 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 32 32 78560363927440 50816611482974 contact02ColumnsJoin0_32 contact02ColumnsJoin32_32
private theorem contact02ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact02) 64 64 = 42792576564837 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 32 32 29168837664712 13623738900125 contact02ColumnsJoin64_32 contact02ColumnsJoin96_32
private theorem contact02ColumnsJoin128_49 : sliceWindow (auxiliaryColumnSlice contact02) 128 49 = 4606568480522 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 32 17 4182391164556 424177315966 contact02ColumnsJoin128_32 contact02ColumnsJoin160_17
private theorem contact02ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact02) 0 128 = 172169551975251 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 64 64 129376975410414 42792576564837 contact02ColumnsJoin0_64 contact02ColumnsJoin64_64
private theorem contact02ColumnsJoin0_177 : sliceWindow (auxiliaryColumnSlice contact02) 0 177 = 176776120455773 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 128 49 172169551975251 4606568480522 contact02ColumnsJoin0_128 contact02ColumnsJoin128_49
private theorem contact02OrdinaryRanks : ordinaryRankBound contact02 = 14048344083 := by decide +kernel
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
private theorem contact02RanksSlice164 : sliceWindow (auxiliaryRankSlice contact02) 164 13 = 0 :=
  contactRankWindow_of_rec contact02 164 13 0 (by decide +kernel)
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
private theorem contact02RanksJoin160_17 : sliceWindow (auxiliaryRankSlice contact02) 160 17 = 1196 :=
  combineSlices (auxiliaryRankSlice contact02) 160 4 13 1196 0 contact02RanksSlice160 contact02RanksSlice164
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
private theorem contact02RanksJoin128_49 : sliceWindow (auxiliaryRankSlice contact02) 128 49 = 3521879 :=
  combineSlices (auxiliaryRankSlice contact02) 128 32 17 3520683 1196 contact02RanksJoin128_32 contact02RanksJoin160_17
private theorem contact02RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact02) 0 128 = 536509138 :=
  combineSlices (auxiliaryRankSlice contact02) 0 64 64 439045127 97464011 contact02RanksJoin0_64 contact02RanksJoin64_64
private theorem contact02RanksJoin0_177 : sliceWindow (auxiliaryRankSlice contact02) 0 177 = 540031017 :=
  combineSlices (auxiliaryRankSlice contact02) 0 128 49 536509138 3521879 contact02RanksJoin0_128 contact02RanksJoin128_49
theorem contact02_margin : sourceMargin contact02 :=
  margin_of_checked_counts contact02 177 3647479744921410 176776120455773 14048344083 540031017 rfl contact02OrdinaryColumns contact02ColumnsJoin0_177 contact02OrdinaryRanks contact02RanksJoin0_177 (by decide +kernel)

private theorem contact04OrdinaryColumns : ordinaryColumnCount contact04 = 1838397606788281 := by decide +kernel
private theorem contact04ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact04) 0 4 = 8026490419660 :=
  contactColumnsWindow_fast contact04 0 4 8026490419660 (by decide +kernel)
private theorem contact04ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact04) 4 4 = 7637397324588 :=
  contactColumnsWindow_fast contact04 4 4 7637397324588 (by decide +kernel)
private theorem contact04ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact04) 8 4 = 7258046793392 :=
  contactColumnsWindow_fast contact04 8 4 7258046793392 (by decide +kernel)
private theorem contact04ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact04) 12 4 = 6888434328789 :=
  contactColumnsWindow_fast contact04 12 4 6888434328789 (by decide +kernel)
private theorem contact04ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact04) 16 4 = 6528531353764 :=
  contactColumnsWindow_fast contact04 16 4 6528531353764 (by decide +kernel)
private theorem contact04ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact04) 20 4 = 6178339033556 :=
  contactColumnsWindow_fast contact04 20 4 6178339033556 (by decide +kernel)
private theorem contact04ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact04) 24 4 = 5837859483279 :=
  contactColumnsWindow_fast contact04 24 4 5837859483279 (by decide +kernel)
private theorem contact04ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact04) 28 4 = 5507130967458 :=
  contactColumnsWindow_fast contact04 28 4 5507130967458 (by decide +kernel)
private theorem contact04ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact04) 32 4 = 5186138814843 :=
  contactColumnsWindow_fast contact04 32 4 5186138814843 (by decide +kernel)
private theorem contact04ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact04) 36 4 = 4874858420536 :=
  contactColumnsWindow_fast contact04 36 4 4874858420536 (by decide +kernel)
private theorem contact04ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact04) 40 4 = 4573293756680 :=
  contactColumnsWindow_fast contact04 40 4 4573293756680 (by decide +kernel)
private theorem contact04ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact04) 44 4 = 4281445416024 :=
  contactColumnsWindow_fast contact04 44 4 4281445416024 (by decide +kernel)
private theorem contact04ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact04) 48 4 = 3999356001530 :=
  contactColumnsWindow_fast contact04 48 4 3999356001530 (by decide +kernel)
private theorem contact04ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact04) 52 4 = 3727000818717 :=
  contactColumnsWindow_fast contact04 52 4 3727000818717 (by decide +kernel)
private theorem contact04ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact04) 56 4 = 3464362237727 :=
  contactColumnsWindow_fast contact04 56 4 3464362237727 (by decide +kernel)
private theorem contact04ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact04) 60 4 = 3211439571284 :=
  contactColumnsWindow_fast contact04 60 4 3211439571284 (by decide +kernel)
private theorem contact04ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact04) 64 4 = 2968234658004 :=
  contactColumnsWindow_fast contact04 64 4 2968234658004 (by decide +kernel)
private theorem contact04ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact04) 68 4 = 2734791634874 :=
  contactColumnsWindow_fast contact04 68 4 2734791634874 (by decide +kernel)
private theorem contact04ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact04) 72 4 = 2511078603006 :=
  contactColumnsWindow_fast contact04 72 4 2511078603006 (by decide +kernel)
private theorem contact04ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact04) 76 4 = 2297082019793 :=
  contactColumnsWindow_fast contact04 76 4 2297082019793 (by decide +kernel)
private theorem contact04ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact04) 80 4 = 2092801207688 :=
  contactColumnsWindow_fast contact04 80 4 2092801207688 (by decide +kernel)
private theorem contact04ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact04) 84 4 = 1898240374086 :=
  contactColumnsWindow_fast contact04 84 4 1898240374086 (by decide +kernel)
private theorem contact04ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact04) 88 4 = 1713443231335 :=
  contactColumnsWindow_fast contact04 88 4 1713443231335 (by decide +kernel)
private theorem contact04ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact04) 92 4 = 1538372312070 :=
  contactColumnsWindow_fast contact04 92 4 1538372312070 (by decide +kernel)
private theorem contact04ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact04) 96 4 = 1373017623659 :=
  contactColumnsWindow_fast contact04 96 4 1373017623659 (by decide +kernel)
private theorem contact04ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact04) 100 4 = 1217378744992 :=
  contactColumnsWindow_fast contact04 100 4 1217378744992 (by decide +kernel)
private theorem contact04ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact04) 104 4 = 1071463050198 :=
  contactColumnsWindow_fast contact04 104 4 1071463050198 (by decide +kernel)
private theorem contact04ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact04) 108 4 = 935310654961 :=
  contactColumnsWindow_fast contact04 108 4 935310654961 (by decide +kernel)
private theorem contact04ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact04) 112 4 = 808881863913 :=
  contactColumnsWindow_fast contact04 112 4 808881863913 (by decide +kernel)
private theorem contact04ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact04) 116 4 = 692169284210 :=
  contactColumnsWindow_fast contact04 116 4 692169284210 (by decide +kernel)
private theorem contact04ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact04) 120 4 = 585172166620 :=
  contactColumnsWindow_fast contact04 120 4 585172166620 (by decide +kernel)
private theorem contact04ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact04) 124 4 = 487901548110 :=
  contactColumnsWindow_fast contact04 124 4 487901548110 (by decide +kernel)
private theorem contact04ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact04) 128 4 = 400394092556 :=
  contactColumnsWindow_fast contact04 128 4 400394092556 (by decide +kernel)
private theorem contact04ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact04) 132 4 = 322607353143 :=
  contactColumnsWindow_fast contact04 132 4 322607353143 (by decide +kernel)
private theorem contact04ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact04) 136 4 = 254530698635 :=
  contactColumnsWindow_fast contact04 136 4 254530698635 (by decide +kernel)
private theorem contact04ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact04) 140 4 = 196066214728 :=
  contactColumnsWindow_fast contact04 140 4 196066214728 (by decide +kernel)
private theorem contact04ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact04) 144 4 = 146936791084 :=
  contactColumnsWindow_fast contact04 144 4 146936791084 (by decide +kernel)
private theorem contact04ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact04) 148 4 = 106705422562 :=
  contactColumnsWindow_fast contact04 148 4 106705422562 (by decide +kernel)
private theorem contact04ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact04) 152 4 = 74701592368 :=
  contactColumnsWindow_fast contact04 152 4 74701592368 (by decide +kernel)
private theorem contact04ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact04) 156 4 = 50132747992 :=
  contactColumnsWindow_fast contact04 156 4 50132747992 (by decide +kernel)
private theorem contact04ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact04) 160 1 = 9477197432 :=
  contactColumnsWindow_fast contact04 160 1 9477197432 (by decide +kernel)
private theorem contact04ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact04) 0 8 = 15663887744248 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 4 4 8026490419660 7637397324588 contact04ColumnsSlice0 contact04ColumnsSlice4
private theorem contact04ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact04) 8 8 = 14146481122181 :=
  combineSlices (auxiliaryColumnSlice contact04) 8 4 4 7258046793392 6888434328789 contact04ColumnsSlice8 contact04ColumnsSlice12
private theorem contact04ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact04) 16 8 = 12706870387320 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 4 4 6528531353764 6178339033556 contact04ColumnsSlice16 contact04ColumnsSlice20
private theorem contact04ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact04) 24 8 = 11344990450737 :=
  combineSlices (auxiliaryColumnSlice contact04) 24 4 4 5837859483279 5507130967458 contact04ColumnsSlice24 contact04ColumnsSlice28
private theorem contact04ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact04) 32 8 = 10060997235379 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 4 4 5186138814843 4874858420536 contact04ColumnsSlice32 contact04ColumnsSlice36
private theorem contact04ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact04) 40 8 = 8854739172704 :=
  combineSlices (auxiliaryColumnSlice contact04) 40 4 4 4573293756680 4281445416024 contact04ColumnsSlice40 contact04ColumnsSlice44
private theorem contact04ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact04) 48 8 = 7726356820247 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 4 4 3999356001530 3727000818717 contact04ColumnsSlice48 contact04ColumnsSlice52
private theorem contact04ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact04) 56 8 = 6675801809011 :=
  combineSlices (auxiliaryColumnSlice contact04) 56 4 4 3464362237727 3211439571284 contact04ColumnsSlice56 contact04ColumnsSlice60
private theorem contact04ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact04) 64 8 = 5703026292878 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 4 4 2968234658004 2734791634874 contact04ColumnsSlice64 contact04ColumnsSlice68
private theorem contact04ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact04) 72 8 = 4808160622799 :=
  combineSlices (auxiliaryColumnSlice contact04) 72 4 4 2511078603006 2297082019793 contact04ColumnsSlice72 contact04ColumnsSlice76
private theorem contact04ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact04) 80 8 = 3991041581774 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 4 4 2092801207688 1898240374086 contact04ColumnsSlice80 contact04ColumnsSlice84
private theorem contact04ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact04) 88 8 = 3251815543405 :=
  combineSlices (auxiliaryColumnSlice contact04) 88 4 4 1713443231335 1538372312070 contact04ColumnsSlice88 contact04ColumnsSlice92
private theorem contact04ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact04) 96 8 = 2590396368651 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 4 4 1373017623659 1217378744992 contact04ColumnsSlice96 contact04ColumnsSlice100
private theorem contact04ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact04) 104 8 = 2006773705159 :=
  combineSlices (auxiliaryColumnSlice contact04) 104 4 4 1071463050198 935310654961 contact04ColumnsSlice104 contact04ColumnsSlice108
private theorem contact04ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact04) 112 8 = 1501051148123 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 4 4 808881863913 692169284210 contact04ColumnsSlice112 contact04ColumnsSlice116
private theorem contact04ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact04) 120 8 = 1073073714730 :=
  combineSlices (auxiliaryColumnSlice contact04) 120 4 4 585172166620 487901548110 contact04ColumnsSlice120 contact04ColumnsSlice124
private theorem contact04ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact04) 128 8 = 723001445699 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 4 4 400394092556 322607353143 contact04ColumnsSlice128 contact04ColumnsSlice132
private theorem contact04ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact04) 136 8 = 450596913363 :=
  combineSlices (auxiliaryColumnSlice contact04) 136 4 4 254530698635 196066214728 contact04ColumnsSlice136 contact04ColumnsSlice140
private theorem contact04ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact04) 144 8 = 253642213646 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 4 4 146936791084 106705422562 contact04ColumnsSlice144 contact04ColumnsSlice148
private theorem contact04ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact04) 152 8 = 124834340360 :=
  combineSlices (auxiliaryColumnSlice contact04) 152 4 4 74701592368 50132747992 contact04ColumnsSlice152 contact04ColumnsSlice156
private theorem contact04ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact04) 0 16 = 29810368866429 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 8 8 15663887744248 14146481122181 contact04ColumnsJoin0_8 contact04ColumnsJoin8_8
private theorem contact04ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact04) 16 16 = 24051860838057 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 8 8 12706870387320 11344990450737 contact04ColumnsJoin16_8 contact04ColumnsJoin24_8
private theorem contact04ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact04) 32 16 = 18915736408083 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 8 8 10060997235379 8854739172704 contact04ColumnsJoin32_8 contact04ColumnsJoin40_8
private theorem contact04ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact04) 48 16 = 14402158629258 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 8 8 7726356820247 6675801809011 contact04ColumnsJoin48_8 contact04ColumnsJoin56_8
private theorem contact04ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact04) 64 16 = 10511186915677 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 8 8 5703026292878 4808160622799 contact04ColumnsJoin64_8 contact04ColumnsJoin72_8
private theorem contact04ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact04) 80 16 = 7242857125179 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 8 8 3991041581774 3251815543405 contact04ColumnsJoin80_8 contact04ColumnsJoin88_8
private theorem contact04ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact04) 96 16 = 4597170073810 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 8 8 2590396368651 2006773705159 contact04ColumnsJoin96_8 contact04ColumnsJoin104_8
private theorem contact04ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact04) 112 16 = 2574124862853 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 8 8 1501051148123 1073073714730 contact04ColumnsJoin112_8 contact04ColumnsJoin120_8
private theorem contact04ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact04) 128 16 = 1173598359062 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 8 8 723001445699 450596913363 contact04ColumnsJoin128_8 contact04ColumnsJoin136_8
private theorem contact04ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact04) 144 16 = 378476554006 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 8 8 253642213646 124834340360 contact04ColumnsJoin144_8 contact04ColumnsJoin152_8
private theorem contact04ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact04) 0 32 = 53862229704486 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 16 16 29810368866429 24051860838057 contact04ColumnsJoin0_16 contact04ColumnsJoin16_16
private theorem contact04ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact04) 32 32 = 33317895037341 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 16 16 18915736408083 14402158629258 contact04ColumnsJoin32_16 contact04ColumnsJoin48_16
private theorem contact04ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact04) 64 32 = 17754044040856 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 16 16 10511186915677 7242857125179 contact04ColumnsJoin64_16 contact04ColumnsJoin80_16
private theorem contact04ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact04) 96 32 = 7171294936663 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 16 16 4597170073810 2574124862853 contact04ColumnsJoin96_16 contact04ColumnsJoin112_16
private theorem contact04ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact04) 128 32 = 1552074913068 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 16 16 1173598359062 378476554006 contact04ColumnsJoin128_16 contact04ColumnsJoin144_16
private theorem contact04ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact04) 0 64 = 87180124741827 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 32 32 53862229704486 33317895037341 contact04ColumnsJoin0_32 contact04ColumnsJoin32_32
private theorem contact04ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact04) 64 64 = 24925338977519 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 32 32 17754044040856 7171294936663 contact04ColumnsJoin64_32 contact04ColumnsJoin96_32
private theorem contact04ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact04) 128 33 = 1561552110500 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 32 1 1552074913068 9477197432 contact04ColumnsJoin128_32 contact04ColumnsSlice160
private theorem contact04ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact04) 0 128 = 112105463719346 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 64 64 87180124741827 24925338977519 contact04ColumnsJoin0_64 contact04ColumnsJoin64_64
private theorem contact04ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact04) 0 161 = 113667015829846 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 128 33 112105463719346 1561552110500 contact04ColumnsJoin0_128 contact04ColumnsJoin128_33
private theorem contact04OrdinaryRanks : ordinaryRankBound contact04 = 7100603773 := by decide +kernel
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
private theorem contact04RanksSlice148 : sliceWindow (auxiliaryRankSlice contact04) 148 13 = 0 :=
  contactRankWindow_of_rec contact04 148 13 0 (by decide +kernel)
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
private theorem contact04RanksJoin144_17 : sliceWindow (auxiliaryRankSlice contact04) 144 17 = 11531 :=
  combineSlices (auxiliaryRankSlice contact04) 144 4 13 11531 0 contact04RanksSlice144 contact04RanksSlice148
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
private theorem contact04RanksJoin128_33 : sliceWindow (auxiliaryRankSlice contact04) 128 33 = 682162 :=
  combineSlices (auxiliaryRankSlice contact04) 128 16 17 670631 11531 contact04RanksJoin128_16 contact04RanksJoin144_17
private theorem contact04RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact04) 0 64 = 292539634 :=
  combineSlices (auxiliaryRankSlice contact04) 0 32 32 192238512 100301122 contact04RanksJoin0_32 contact04RanksJoin32_32
private theorem contact04RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact04) 64 64 = 52702297 :=
  combineSlices (auxiliaryRankSlice contact04) 64 32 32 41695997 11006300 contact04RanksJoin64_32 contact04RanksJoin96_32
private theorem contact04RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact04) 0 128 = 345241931 :=
  combineSlices (auxiliaryRankSlice contact04) 0 64 64 292539634 52702297 contact04RanksJoin0_64 contact04RanksJoin64_64
private theorem contact04RanksJoin0_161 : sliceWindow (auxiliaryRankSlice contact04) 0 161 = 345924093 :=
  combineSlices (auxiliaryRankSlice contact04) 0 128 33 345241931 682162 contact04RanksJoin0_128 contact04RanksJoin128_33
theorem contact04_margin : sourceMargin contact04 :=
  margin_of_checked_counts contact04 161 1838397606788281 113667015829846 7100603773 345924093 rfl contact04OrdinaryColumns contact04ColumnsJoin0_161 contact04OrdinaryRanks contact04RanksJoin0_161 (by decide +kernel)

private theorem contact06OrdinaryColumns : ordinaryColumnCount contact06 = 2086140954083900 := by decide +kernel
private theorem contact06ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact06) 0 4 = 7926352207302 :=
  contactColumnsWindow_fast contact06 0 4 7926352207302 (by decide +kernel)
private theorem contact06ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact06) 4 4 = 7546121417062 :=
  contactColumnsWindow_fast contact06 4 4 7546121417062 (by decide +kernel)
private theorem contact06ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact06) 8 4 = 7175275657974 :=
  contactColumnsWindow_fast contact06 8 4 7175275657974 (by decide +kernel)
private theorem contact06ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact06) 12 4 = 6813815206159 :=
  contactColumnsWindow_fast contact06 12 4 6813815206159 (by decide +kernel)
private theorem contact06ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact06) 16 4 = 6461776386474 :=
  contactColumnsWindow_fast contact06 16 4 6461776386474 (by decide +kernel)
private theorem contact06ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact06) 20 4 = 6119143546612 :=
  contactColumnsWindow_fast contact06 20 4 6119143546612 (by decide +kernel)
private theorem contact06ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact06) 24 4 = 5785899519123 :=
  contactColumnsWindow_fast contact06 24 4 5785899519123 (by decide +kernel)
private theorem contact06ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact06) 28 4 = 5462042929960 :=
  contactColumnsWindow_fast contact06 28 4 5462042929960 (by decide +kernel)
private theorem contact06ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact06) 32 4 = 5147577009214 :=
  contactColumnsWindow_fast contact06 32 4 5147577009214 (by decide +kernel)
private theorem contact06ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact06) 36 4 = 4842537502842 :=
  contactColumnsWindow_fast contact06 36 4 4842537502842 (by decide +kernel)
private theorem contact06ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact06) 40 4 = 4546904849596 :=
  contactColumnsWindow_fast contact06 40 4 4546904849596 (by decide +kernel)
private theorem contact06ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact06) 44 4 = 4260662962977 :=
  contactColumnsWindow_fast contact06 44 4 4260662962977 (by decide +kernel)
private theorem contact06ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact06) 48 4 = 3983813163990 :=
  contactColumnsWindow_fast contact06 48 4 3983813163990 (by decide +kernel)
private theorem contact06ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact06) 52 4 = 3716357615143 :=
  contactColumnsWindow_fast contact06 52 4 3716357615143 (by decide +kernel)
private theorem contact06ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact06) 56 4 = 3458335724167 :=
  contactColumnsWindow_fast contact06 56 4 3458335724167 (by decide +kernel)
private theorem contact06ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact06) 60 4 = 3209720039146 :=
  contactColumnsWindow_fast contact06 60 4 3209720039146 (by decide +kernel)
private theorem contact06ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact06) 64 4 = 2970498664155 :=
  contactColumnsWindow_fast contact06 64 4 2970498664155 (by decide +kernel)
private theorem contact06ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact06) 68 4 = 2740669336332 :=
  contactColumnsWindow_fast contact06 68 4 2740669336332 (by decide +kernel)
private theorem contact06ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact06) 72 4 = 2520236871122 :=
  contactColumnsWindow_fast contact06 72 4 2520236871122 (by decide +kernel)
private theorem contact06ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact06) 76 4 = 2309238463333 :=
  contactColumnsWindow_fast contact06 76 4 2309238463333 (by decide +kernel)
private theorem contact06ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact06) 80 4 = 2107643856436 :=
  contactColumnsWindow_fast contact06 80 4 2107643856436 (by decide +kernel)
private theorem contact06ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact06) 84 4 = 1915443061250 :=
  contactColumnsWindow_fast contact06 84 4 1915443061250 (by decide +kernel)
private theorem contact06ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact06) 88 4 = 1732634270504 :=
  contactColumnsWindow_fast contact06 88 4 1732634270504 (by decide +kernel)
private theorem contact06ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact06) 92 4 = 1559225126588 :=
  contactColumnsWindow_fast contact06 92 4 1559225126588 (by decide +kernel)
private theorem contact06ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact06) 96 4 = 1395249878182 :=
  contactColumnsWindow_fast contact06 96 4 1395249878182 (by decide +kernel)
private theorem contact06ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact06) 100 4 = 1240676376408 :=
  contactColumnsWindow_fast contact06 100 4 1240676376408 (by decide +kernel)
private theorem contact06ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact06) 104 4 = 1095496291040 :=
  contactColumnsWindow_fast contact06 104 4 1095496291040 (by decide +kernel)
private theorem contact06ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact06) 108 4 = 959707837421 :=
  contactColumnsWindow_fast contact06 108 4 959707837421 (by decide +kernel)
private theorem contact06ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact06) 112 4 = 833322227314 :=
  contactColumnsWindow_fast contact06 112 4 833322227314 (by decide +kernel)
private theorem contact06ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact06) 116 4 = 716370254206 :=
  contactColumnsWindow_fast contact06 116 4 716370254206 (by decide +kernel)
private theorem contact06ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact06) 120 4 = 608817583215 :=
  contactColumnsWindow_fast contact06 120 4 608817583215 (by decide +kernel)
private theorem contact06ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact06) 124 4 = 510658148570 :=
  contactColumnsWindow_fast contact06 124 4 510658148570 (by decide +kernel)
private theorem contact06ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact06) 128 4 = 421890215184 :=
  contactColumnsWindow_fast contact06 128 4 421890215184 (by decide +kernel)
private theorem contact06ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact06) 132 4 = 342529182319 :=
  contactColumnsWindow_fast contact06 132 4 342529182319 (by decide +kernel)
private theorem contact06ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact06) 136 4 = 272599094823 :=
  contactColumnsWindow_fast contact06 136 4 272599094823 (by decide +kernel)
private theorem contact06ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact06) 140 4 = 212039510238 :=
  contactColumnsWindow_fast contact06 140 4 212039510238 (by decide +kernel)
private theorem contact06ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact06) 144 4 = 160663481871 :=
  contactColumnsWindow_fast contact06 144 4 160663481871 (by decide +kernel)
private theorem contact06ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact06) 148 4 = 118094695762 :=
  contactColumnsWindow_fast contact06 148 4 118094695762 (by decide +kernel)
private theorem contact06ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact06) 152 4 = 83816383690 :=
  contactColumnsWindow_fast contact06 152 4 83816383690 (by decide +kernel)
private theorem contact06ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact06) 156 4 = 57142737988 :=
  contactColumnsWindow_fast contact06 156 4 57142737988 (by decide +kernel)
private theorem contact06ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact06) 160 4 = 37180025855 :=
  contactColumnsWindow_fast contact06 160 4 37180025855 (by decide +kernel)
private theorem contact06ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact06) 0 8 = 15472473624364 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 4 4 7926352207302 7546121417062 contact06ColumnsSlice0 contact06ColumnsSlice4
private theorem contact06ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact06) 8 8 = 13989090864133 :=
  combineSlices (auxiliaryColumnSlice contact06) 8 4 4 7175275657974 6813815206159 contact06ColumnsSlice8 contact06ColumnsSlice12
private theorem contact06ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact06) 16 8 = 12580919933086 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 4 4 6461776386474 6119143546612 contact06ColumnsSlice16 contact06ColumnsSlice20
private theorem contact06ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact06) 24 8 = 11247942449083 :=
  combineSlices (auxiliaryColumnSlice contact06) 24 4 4 5785899519123 5462042929960 contact06ColumnsSlice24 contact06ColumnsSlice28
private theorem contact06ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact06) 32 8 = 9990114512056 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 4 4 5147577009214 4842537502842 contact06ColumnsSlice32 contact06ColumnsSlice36
private theorem contact06ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact06) 40 8 = 8807567812573 :=
  combineSlices (auxiliaryColumnSlice contact06) 40 4 4 4546904849596 4260662962977 contact06ColumnsSlice40 contact06ColumnsSlice44
private theorem contact06ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact06) 48 8 = 7700170779133 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 4 4 3983813163990 3716357615143 contact06ColumnsSlice48 contact06ColumnsSlice52
private theorem contact06ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact06) 56 8 = 6668055763313 :=
  combineSlices (auxiliaryColumnSlice contact06) 56 4 4 3458335724167 3209720039146 contact06ColumnsSlice56 contact06ColumnsSlice60
private theorem contact06ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact06) 64 8 = 5711168000487 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 4 4 2970498664155 2740669336332 contact06ColumnsSlice64 contact06ColumnsSlice68
private theorem contact06ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact06) 72 8 = 4829475334455 :=
  combineSlices (auxiliaryColumnSlice contact06) 72 4 4 2520236871122 2309238463333 contact06ColumnsSlice72 contact06ColumnsSlice76
private theorem contact06ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact06) 80 8 = 4023086917686 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 4 4 2107643856436 1915443061250 contact06ColumnsSlice80 contact06ColumnsSlice84
private theorem contact06ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact06) 88 8 = 3291859397092 :=
  combineSlices (auxiliaryColumnSlice contact06) 88 4 4 1732634270504 1559225126588 contact06ColumnsSlice88 contact06ColumnsSlice92
private theorem contact06ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact06) 96 8 = 2635926254590 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 4 4 1395249878182 1240676376408 contact06ColumnsSlice96 contact06ColumnsSlice100
private theorem contact06ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact06) 104 8 = 2055204128461 :=
  combineSlices (auxiliaryColumnSlice contact06) 104 4 4 1095496291040 959707837421 contact06ColumnsSlice104 contact06ColumnsSlice108
private theorem contact06ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact06) 112 8 = 1549692481520 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 4 4 833322227314 716370254206 contact06ColumnsSlice112 contact06ColumnsSlice116
private theorem contact06ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact06) 120 8 = 1119475731785 :=
  combineSlices (auxiliaryColumnSlice contact06) 120 4 4 608817583215 510658148570 contact06ColumnsSlice120 contact06ColumnsSlice124
private theorem contact06ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact06) 128 8 = 764419397503 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 4 4 421890215184 342529182319 contact06ColumnsSlice128 contact06ColumnsSlice132
private theorem contact06ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact06) 136 8 = 484638605061 :=
  combineSlices (auxiliaryColumnSlice contact06) 136 4 4 272599094823 212039510238 contact06ColumnsSlice136 contact06ColumnsSlice140
private theorem contact06ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact06) 144 8 = 278758177633 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 4 4 160663481871 118094695762 contact06ColumnsSlice144 contact06ColumnsSlice148
private theorem contact06ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact06) 152 8 = 140959121678 :=
  combineSlices (auxiliaryColumnSlice contact06) 152 4 4 83816383690 57142737988 contact06ColumnsSlice152 contact06ColumnsSlice156
private theorem contact06ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact06) 0 16 = 29461564488497 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 8 8 15472473624364 13989090864133 contact06ColumnsJoin0_8 contact06ColumnsJoin8_8
private theorem contact06ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact06) 16 16 = 23828862382169 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 8 8 12580919933086 11247942449083 contact06ColumnsJoin16_8 contact06ColumnsJoin24_8
private theorem contact06ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact06) 32 16 = 18797682324629 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 8 8 9990114512056 8807567812573 contact06ColumnsJoin32_8 contact06ColumnsJoin40_8
private theorem contact06ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact06) 48 16 = 14368226542446 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 8 8 7700170779133 6668055763313 contact06ColumnsJoin48_8 contact06ColumnsJoin56_8
private theorem contact06ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact06) 64 16 = 10540643334942 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 8 8 5711168000487 4829475334455 contact06ColumnsJoin64_8 contact06ColumnsJoin72_8
private theorem contact06ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact06) 80 16 = 7314946314778 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 8 8 4023086917686 3291859397092 contact06ColumnsJoin80_8 contact06ColumnsJoin88_8
private theorem contact06ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact06) 96 16 = 4691130383051 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 8 8 2635926254590 2055204128461 contact06ColumnsJoin96_8 contact06ColumnsJoin104_8
private theorem contact06ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact06) 112 16 = 2669168213305 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 8 8 1549692481520 1119475731785 contact06ColumnsJoin112_8 contact06ColumnsJoin120_8
private theorem contact06ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact06) 128 16 = 1249058002564 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 8 8 764419397503 484638605061 contact06ColumnsJoin128_8 contact06ColumnsJoin136_8
private theorem contact06ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact06) 144 16 = 419717299311 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 8 8 278758177633 140959121678 contact06ColumnsJoin144_8 contact06ColumnsJoin152_8
private theorem contact06ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact06) 0 32 = 53290426870666 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 16 16 29461564488497 23828862382169 contact06ColumnsJoin0_16 contact06ColumnsJoin16_16
private theorem contact06ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact06) 32 32 = 33165908867075 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 16 16 18797682324629 14368226542446 contact06ColumnsJoin32_16 contact06ColumnsJoin48_16
private theorem contact06ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact06) 64 32 = 17855589649720 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 16 16 10540643334942 7314946314778 contact06ColumnsJoin64_16 contact06ColumnsJoin80_16
private theorem contact06ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact06) 96 32 = 7360298596356 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 16 16 4691130383051 2669168213305 contact06ColumnsJoin96_16 contact06ColumnsJoin112_16
private theorem contact06ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact06) 128 32 = 1668775301875 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 16 16 1249058002564 419717299311 contact06ColumnsJoin128_16 contact06ColumnsJoin144_16
private theorem contact06ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact06) 0 64 = 86456335737741 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 32 32 53290426870666 33165908867075 contact06ColumnsJoin0_32 contact06ColumnsJoin32_32
private theorem contact06ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact06) 64 64 = 25215888246076 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 32 32 17855589649720 7360298596356 contact06ColumnsJoin64_32 contact06ColumnsJoin96_32
private theorem contact06ColumnsJoin128_36 : sliceWindow (auxiliaryColumnSlice contact06) 128 36 = 1705955327730 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 32 4 1668775301875 37180025855 contact06ColumnsJoin128_32 contact06ColumnsSlice160
private theorem contact06ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact06) 0 128 = 111672223983817 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 64 64 86456335737741 25215888246076 contact06ColumnsJoin0_64 contact06ColumnsJoin64_64
private theorem contact06ColumnsJoin0_164 : sliceWindow (auxiliaryColumnSlice contact06) 0 164 = 113378179311547 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 128 36 111672223983817 1705955327730 contact06ColumnsJoin0_128 contact06ColumnsJoin128_36
private theorem contact06OrdinaryRanks : ordinaryRankBound contact06 = 8046461851 := by decide +kernel
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
private theorem contact06RanksSlice152 : sliceWindow (auxiliaryRankSlice contact06) 152 12 = 0 :=
  contactRankWindow_of_rec contact06 152 12 0 (by decide +kernel)
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
private theorem contact06RanksJoin144_20 : sliceWindow (auxiliaryRankSlice contact06) 144 20 = 18497 :=
  combineSlices (auxiliaryRankSlice contact06) 144 8 12 18497 0 contact06RanksJoin144_8 contact06RanksSlice152
private theorem contact06RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact06) 0 32 = 190296960 :=
  combineSlices (auxiliaryRankSlice contact06) 0 16 16 108530240 81766720 contact06RanksJoin0_16 contact06RanksJoin16_16
private theorem contact06RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact06) 32 32 = 99868647 :=
  combineSlices (auxiliaryRankSlice contact06) 32 16 16 59160640 40708007 contact06RanksJoin32_16 contact06RanksJoin48_16
private theorem contact06RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact06) 64 32 = 41845999 :=
  combineSlices (auxiliaryRankSlice contact06) 64 16 16 26293583 15552416 contact06RanksJoin64_16 contact06RanksJoin80_16
private theorem contact06RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact06) 96 32 = 11266304 :=
  combineSlices (auxiliaryRankSlice contact06) 96 16 16 8024065 3242239 contact06RanksJoin96_16 contact06RanksJoin112_16
private theorem contact06RanksJoin128_36 : sliceWindow (auxiliaryRankSlice contact06) 128 36 = 759172 :=
  combineSlices (auxiliaryRankSlice contact06) 128 16 20 740675 18497 contact06RanksJoin128_16 contact06RanksJoin144_20
private theorem contact06RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact06) 0 64 = 290165607 :=
  combineSlices (auxiliaryRankSlice contact06) 0 32 32 190296960 99868647 contact06RanksJoin0_32 contact06RanksJoin32_32
private theorem contact06RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact06) 64 64 = 53112303 :=
  combineSlices (auxiliaryRankSlice contact06) 64 32 32 41845999 11266304 contact06RanksJoin64_32 contact06RanksJoin96_32
private theorem contact06RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact06) 0 128 = 343277910 :=
  combineSlices (auxiliaryRankSlice contact06) 0 64 64 290165607 53112303 contact06RanksJoin0_64 contact06RanksJoin64_64
private theorem contact06RanksJoin0_164 : sliceWindow (auxiliaryRankSlice contact06) 0 164 = 344037082 :=
  combineSlices (auxiliaryRankSlice contact06) 0 128 36 343277910 759172 contact06RanksJoin0_128 contact06RanksJoin128_36
theorem contact06_margin : sourceMargin contact06 :=
  margin_of_checked_counts contact06 164 2086140954083900 113378179311547 8046461851 344037082 rfl contact06OrdinaryColumns contact06ColumnsJoin0_164 contact06OrdinaryRanks contact06RanksJoin0_164 (by decide +kernel)

private theorem contact08OrdinaryColumns : ordinaryColumnCount contact08 = 2058418711215143 := by decide +kernel
private theorem contact08ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact08) 0 4 = 8338663233314 :=
  contactColumnsWindow_fast contact08 0 4 8338663233314 (by decide +kernel)
private theorem contact08ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact08) 4 4 = 7936490898386 :=
  contactColumnsWindow_fast contact08 4 4 7936490898386 (by decide +kernel)
private theorem contact08ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact08) 8 4 = 7544304541382 :=
  contactColumnsWindow_fast contact08 8 4 7544304541382 (by decide +kernel)
private theorem contact08ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact08) 12 4 = 7162104477423 :=
  contactColumnsWindow_fast contact08 12 4 7162104477423 (by decide +kernel)
private theorem contact08ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact08) 16 4 = 6789930257482 :=
  contactColumnsWindow_fast contact08 16 4 6789930257482 (by decide +kernel)
private theorem contact08ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact08) 20 4 = 6427764770541 :=
  contactColumnsWindow_fast contact08 20 4 6427764770541 (by decide +kernel)
private theorem contact08ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact08) 24 4 = 6075589189298 :=
  contactColumnsWindow_fast contact08 24 4 6075589189298 (by decide +kernel)
private theorem contact08ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact08) 28 4 = 5733402084910 :=
  contactColumnsWindow_fast contact08 28 4 5733402084910 (by decide +kernel)
private theorem contact08ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact08) 32 4 = 5401206898831 :=
  contactColumnsWindow_fast contact08 32 4 5401206898831 (by decide +kernel)
private theorem contact08ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact08) 36 4 = 5079042654504 :=
  contactColumnsWindow_fast contact08 36 4 5079042654504 (by decide +kernel)
private theorem contact08ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact08) 40 4 = 4766887831286 :=
  contactColumnsWindow_fast contact08 40 4 4766887831286 (by decide +kernel)
private theorem contact08ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact08) 44 4 = 4464724932545 :=
  contactColumnsWindow_fast contact08 44 4 4464724932545 (by decide +kernel)
private theorem contact08ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact08) 48 4 = 4172555318596 :=
  contactColumnsWindow_fast contact08 48 4 4172555318596 (by decide +kernel)
private theorem contact08ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact08) 52 4 = 3890381395884 :=
  contactColumnsWindow_fast contact08 52 4 3890381395884 (by decide +kernel)
private theorem contact08ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact08) 56 4 = 3618246049599 :=
  contactColumnsWindow_fast contact08 56 4 3618246049599 (by decide +kernel)
private theorem contact08ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact08) 60 4 = 3356119227344 :=
  contactColumnsWindow_fast contact08 60 4 3356119227344 (by decide +kernel)
private theorem contact08ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact08) 64 4 = 3103987982579 :=
  contactColumnsWindow_fast contact08 64 4 3103987982579 (by decide +kernel)
private theorem contact08ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact08) 68 4 = 2861849982142 :=
  contactColumnsWindow_fast contact08 68 4 2861849982142 (by decide +kernel)
private theorem contact08ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact08) 72 4 = 2629710504240 :=
  contactColumnsWindow_fast contact08 72 4 2629710504240 (by decide +kernel)
private theorem contact08ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact08) 76 4 = 2407610050233 :=
  contactColumnsWindow_fast contact08 76 4 2407610050233 (by decide +kernel)
private theorem contact08ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact08) 80 4 = 2195515468682 :=
  contactColumnsWindow_fast contact08 80 4 2195515468682 (by decide +kernel)
private theorem contact08ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact08) 84 4 = 1993415948604 :=
  contactColumnsWindow_fast contact08 84 4 1993415948604 (by decide +kernel)
private theorem contact08ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact08) 88 4 = 1801309629877 :=
  contactColumnsWindow_fast contact08 88 4 1801309629877 (by decide +kernel)
private theorem contact08ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact08) 92 4 = 1619204858640 :=
  contactColumnsWindow_fast contact08 92 4 1619204858640 (by decide +kernel)
private theorem contact08ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact08) 96 4 = 1447138945547 :=
  contactColumnsWindow_fast contact08 96 4 1447138945547 (by decide +kernel)
private theorem contact08ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact08) 100 4 = 1285076633015 :=
  contactColumnsWindow_fast contact08 100 4 1285076633015 (by decide +kernel)
private theorem contact08ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact08) 104 4 = 1133008972446 :=
  contactColumnsWindow_fast contact08 104 4 1133008972446 (by decide +kernel)
private theorem contact08ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact08) 108 4 = 990934128136 :=
  contactColumnsWindow_fast contact08 108 4 990934128136 (by decide +kernel)
private theorem contact08ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact08) 112 4 = 858864293669 :=
  contactColumnsWindow_fast contact08 112 4 858864293669 (by decide +kernel)
private theorem contact08ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact08) 116 4 = 736833031735 :=
  contactColumnsWindow_fast contact08 116 4 736833031735 (by decide +kernel)
private theorem contact08ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact08) 120 4 = 624802704008 :=
  contactColumnsWindow_fast contact08 120 4 624802704008 (by decide +kernel)
private theorem contact08ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact08) 124 4 = 522766841568 :=
  contactColumnsWindow_fast contact08 124 4 522766841568 (by decide +kernel)
private theorem contact08ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact08) 128 4 = 430723660825 :=
  contactColumnsWindow_fast contact08 128 4 430723660825 (by decide +kernel)
private theorem contact08ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact08) 132 4 = 348689906609 :=
  contactColumnsWindow_fast contact08 132 4 348689906609 (by decide +kernel)
private theorem contact08ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact08) 136 4 = 276687970531 :=
  contactColumnsWindow_fast contact08 136 4 276687970531 (by decide +kernel)
private theorem contact08ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact08) 140 4 = 214598293241 :=
  contactColumnsWindow_fast contact08 140 4 214598293241 (by decide +kernel)
private theorem contact08ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact08) 144 4 = 162135305961 :=
  contactColumnsWindow_fast contact08 144 4 162135305961 (by decide +kernel)
private theorem contact08ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact08) 148 4 = 118846247364 :=
  contactColumnsWindow_fast contact08 148 4 118846247364 (by decide +kernel)
private theorem contact08ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact08) 152 4 = 84138139669 :=
  contactColumnsWindow_fast contact08 152 4 84138139669 (by decide +kernel)
private theorem contact08ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact08) 156 4 = 57247552440 :=
  contactColumnsWindow_fast contact08 156 4 57247552440 (by decide +kernel)
private theorem contact08ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact08) 160 2 = 20719929490 :=
  contactColumnsWindow_fast contact08 160 2 20719929490 (by decide +kernel)
private theorem contact08ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact08) 0 8 = 16275154131700 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 4 4 8338663233314 7936490898386 contact08ColumnsSlice0 contact08ColumnsSlice4
private theorem contact08ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact08) 8 8 = 14706409018805 :=
  combineSlices (auxiliaryColumnSlice contact08) 8 4 4 7544304541382 7162104477423 contact08ColumnsSlice8 contact08ColumnsSlice12
private theorem contact08ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact08) 16 8 = 13217695028023 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 4 4 6789930257482 6427764770541 contact08ColumnsSlice16 contact08ColumnsSlice20
private theorem contact08ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact08) 24 8 = 11808991274208 :=
  combineSlices (auxiliaryColumnSlice contact08) 24 4 4 6075589189298 5733402084910 contact08ColumnsSlice24 contact08ColumnsSlice28
private theorem contact08ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact08) 32 8 = 10480249553335 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 4 4 5401206898831 5079042654504 contact08ColumnsSlice32 contact08ColumnsSlice36
private theorem contact08ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact08) 40 8 = 9231612763831 :=
  combineSlices (auxiliaryColumnSlice contact08) 40 4 4 4766887831286 4464724932545 contact08ColumnsSlice40 contact08ColumnsSlice44
private theorem contact08ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact08) 48 8 = 8062936714480 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 4 4 4172555318596 3890381395884 contact08ColumnsSlice48 contact08ColumnsSlice52
private theorem contact08ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact08) 56 8 = 6974365276943 :=
  combineSlices (auxiliaryColumnSlice contact08) 56 4 4 3618246049599 3356119227344 contact08ColumnsSlice56 contact08ColumnsSlice60
private theorem contact08ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact08) 64 8 = 5965837964721 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 4 4 3103987982579 2861849982142 contact08ColumnsSlice64 contact08ColumnsSlice68
private theorem contact08ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact08) 72 8 = 5037320554473 :=
  combineSlices (auxiliaryColumnSlice contact08) 72 4 4 2629710504240 2407610050233 contact08ColumnsSlice72 contact08ColumnsSlice76
private theorem contact08ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact08) 80 8 = 4188931417286 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 4 4 2195515468682 1993415948604 contact08ColumnsSlice80 contact08ColumnsSlice84
private theorem contact08ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact08) 88 8 = 3420514488517 :=
  combineSlices (auxiliaryColumnSlice contact08) 88 4 4 1801309629877 1619204858640 contact08ColumnsSlice88 contact08ColumnsSlice92
private theorem contact08ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact08) 96 8 = 2732215578562 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 4 4 1447138945547 1285076633015 contact08ColumnsSlice96 contact08ColumnsSlice100
private theorem contact08ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact08) 104 8 = 2123943100582 :=
  combineSlices (auxiliaryColumnSlice contact08) 104 4 4 1133008972446 990934128136 contact08ColumnsSlice104 contact08ColumnsSlice108
private theorem contact08ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact08) 112 8 = 1595697325404 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 4 4 858864293669 736833031735 contact08ColumnsSlice112 contact08ColumnsSlice116
private theorem contact08ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact08) 120 8 = 1147569545576 :=
  combineSlices (auxiliaryColumnSlice contact08) 120 4 4 624802704008 522766841568 contact08ColumnsSlice120 contact08ColumnsSlice124
private theorem contact08ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact08) 128 8 = 779413567434 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 4 4 430723660825 348689906609 contact08ColumnsSlice128 contact08ColumnsSlice132
private theorem contact08ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact08) 136 8 = 491286263772 :=
  combineSlices (auxiliaryColumnSlice contact08) 136 4 4 276687970531 214598293241 contact08ColumnsSlice136 contact08ColumnsSlice140
private theorem contact08ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact08) 144 8 = 280981553325 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 4 4 162135305961 118846247364 contact08ColumnsSlice144 contact08ColumnsSlice148
private theorem contact08ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact08) 152 8 = 141385692109 :=
  combineSlices (auxiliaryColumnSlice contact08) 152 4 4 84138139669 57247552440 contact08ColumnsSlice152 contact08ColumnsSlice156
private theorem contact08ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact08) 0 16 = 30981563150505 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 8 8 16275154131700 14706409018805 contact08ColumnsJoin0_8 contact08ColumnsJoin8_8
private theorem contact08ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact08) 16 16 = 25026686302231 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 8 8 13217695028023 11808991274208 contact08ColumnsJoin16_8 contact08ColumnsJoin24_8
private theorem contact08ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact08) 32 16 = 19711862317166 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 8 8 10480249553335 9231612763831 contact08ColumnsJoin32_8 contact08ColumnsJoin40_8
private theorem contact08ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact08) 48 16 = 15037301991423 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 8 8 8062936714480 6974365276943 contact08ColumnsJoin48_8 contact08ColumnsJoin56_8
private theorem contact08ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact08) 64 16 = 11003158519194 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 8 8 5965837964721 5037320554473 contact08ColumnsJoin64_8 contact08ColumnsJoin72_8
private theorem contact08ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact08) 80 16 = 7609445905803 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 8 8 4188931417286 3420514488517 contact08ColumnsJoin80_8 contact08ColumnsJoin88_8
private theorem contact08ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact08) 96 16 = 4856158679144 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 8 8 2732215578562 2123943100582 contact08ColumnsJoin96_8 contact08ColumnsJoin104_8
private theorem contact08ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact08) 112 16 = 2743266870980 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 8 8 1595697325404 1147569545576 contact08ColumnsJoin112_8 contact08ColumnsJoin120_8
private theorem contact08ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact08) 128 16 = 1270699831206 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 8 8 779413567434 491286263772 contact08ColumnsJoin128_8 contact08ColumnsJoin136_8
private theorem contact08ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact08) 144 16 = 422367245434 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 8 8 280981553325 141385692109 contact08ColumnsJoin144_8 contact08ColumnsJoin152_8
private theorem contact08ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact08) 0 32 = 56008249452736 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 16 16 30981563150505 25026686302231 contact08ColumnsJoin0_16 contact08ColumnsJoin16_16
private theorem contact08ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact08) 32 32 = 34749164308589 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 16 16 19711862317166 15037301991423 contact08ColumnsJoin32_16 contact08ColumnsJoin48_16
private theorem contact08ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact08) 64 32 = 18612604424997 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 16 16 11003158519194 7609445905803 contact08ColumnsJoin64_16 contact08ColumnsJoin80_16
private theorem contact08ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact08) 96 32 = 7599425550124 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 16 16 4856158679144 2743266870980 contact08ColumnsJoin96_16 contact08ColumnsJoin112_16
private theorem contact08ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact08) 128 32 = 1693067076640 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 16 16 1270699831206 422367245434 contact08ColumnsJoin128_16 contact08ColumnsJoin144_16
private theorem contact08ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact08) 0 64 = 90757413761325 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 32 32 56008249452736 34749164308589 contact08ColumnsJoin0_32 contact08ColumnsJoin32_32
private theorem contact08ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact08) 64 64 = 26212029975121 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 32 32 18612604424997 7599425550124 contact08ColumnsJoin64_32 contact08ColumnsJoin96_32
private theorem contact08ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact08) 128 34 = 1713787006130 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 32 2 1693067076640 20719929490 contact08ColumnsJoin128_32 contact08ColumnsSlice160
private theorem contact08ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact08) 0 128 = 116969443736446 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 64 64 90757413761325 26212029975121 contact08ColumnsJoin0_64 contact08ColumnsJoin64_64
private theorem contact08ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact08) 0 162 = 118683230742576 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 128 34 116969443736446 1713787006130 contact08ColumnsJoin0_128 contact08ColumnsJoin128_34
private theorem contact08OrdinaryRanks : ordinaryRankBound contact08 = 7943206464 := by decide +kernel
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
private theorem contact08RanksSlice152 : sliceWindow (auxiliaryRankSlice contact08) 152 10 = 0 :=
  contactRankWindow_of_rec contact08 152 10 0 (by decide +kernel)
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
private theorem contact08RanksJoin144_18 : sliceWindow (auxiliaryRankSlice contact08) 144 18 = 19439 :=
  combineSlices (auxiliaryRankSlice contact08) 144 8 10 19439 0 contact08RanksJoin144_8 contact08RanksSlice152
private theorem contact08RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact08) 0 32 = 200059968 :=
  combineSlices (auxiliaryRankSlice contact08) 0 16 16 114130464 85929504 contact08RanksJoin0_16 contact08RanksJoin16_16
private theorem contact08RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact08) 32 32 = 104940520 :=
  combineSlices (auxiliaryRankSlice contact08) 32 16 16 62152224 42788296 contact08RanksJoin32_16 contact08RanksJoin48_16
private theorem contact08RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact08) 64 32 = 44064098 :=
  combineSlices (auxiliaryRankSlice contact08) 64 16 16 27671826 16392272 contact08RanksJoin64_16 contact08RanksJoin80_16
private theorem contact08RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact08) 96 32 = 11900728 :=
  combineSlices (auxiliaryRankSlice contact08) 96 16 16 8471654 3429074 contact08RanksJoin96_16 contact08RanksJoin112_16
private theorem contact08RanksJoin128_34 : sliceWindow (auxiliaryRankSlice contact08) 128 34 = 803180 :=
  combineSlices (auxiliaryRankSlice contact08) 128 16 18 783741 19439 contact08RanksJoin128_16 contact08RanksJoin144_18
private theorem contact08RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact08) 0 64 = 305000488 :=
  combineSlices (auxiliaryRankSlice contact08) 0 32 32 200059968 104940520 contact08RanksJoin0_32 contact08RanksJoin32_32
private theorem contact08RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact08) 64 64 = 55964826 :=
  combineSlices (auxiliaryRankSlice contact08) 64 32 32 44064098 11900728 contact08RanksJoin64_32 contact08RanksJoin96_32
private theorem contact08RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact08) 0 128 = 360965314 :=
  combineSlices (auxiliaryRankSlice contact08) 0 64 64 305000488 55964826 contact08RanksJoin0_64 contact08RanksJoin64_64
private theorem contact08RanksJoin0_162 : sliceWindow (auxiliaryRankSlice contact08) 0 162 = 361768494 :=
  combineSlices (auxiliaryRankSlice contact08) 0 128 34 360965314 803180 contact08RanksJoin0_128 contact08RanksJoin128_34
theorem contact08_margin : sourceMargin contact08 :=
  margin_of_checked_counts contact08 162 2058418711215143 118683230742576 7943206464 361768494 rfl contact08OrdinaryColumns contact08ColumnsJoin0_162 contact08OrdinaryRanks contact08RanksJoin0_162 (by decide +kernel)

private theorem contact10OrdinaryColumns : ordinaryColumnCount contact10 = 3831477648122776 := by decide +kernel
private theorem contact10ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact10) 0 4 = 10383362700512 :=
  contactColumnsWindow_fast contact10 0 4 10383362700512 (by decide +kernel)
private theorem contact10ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact10) 4 4 = 9906983223264 :=
  contactColumnsWindow_fast contact10 4 4 9906983223264 (by decide +kernel)
private theorem contact10ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact10) 8 4 = 9441843944160 :=
  contactColumnsWindow_fast contact10 8 4 9441843944160 (by decide +kernel)
private theorem contact10ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact10) 12 4 = 8987944863200 :=
  contactColumnsWindow_fast contact10 12 4 8987944863200 (by decide +kernel)
private theorem contact10ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact10) 16 4 = 8545285980384 :=
  contactColumnsWindow_fast contact10 16 4 8545285980384 (by decide +kernel)
private theorem contact10ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact10) 20 4 = 8113867295712 :=
  contactColumnsWindow_fast contact10 20 4 8113867295712 (by decide +kernel)
private theorem contact10ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact10) 24 4 = 7693688809184 :=
  contactColumnsWindow_fast contact10 24 4 7693688809184 (by decide +kernel)
private theorem contact10ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact10) 28 4 = 7284784293300 :=
  contactColumnsWindow_fast contact10 28 4 7284784293300 (by decide +kernel)
private theorem contact10ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact10) 32 4 = 6887169035060 :=
  contactColumnsWindow_fast contact10 32 4 6887169035060 (by decide +kernel)
private theorem contact10ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact10) 36 4 = 6500797270932 :=
  contactColumnsWindow_fast contact10 36 4 6500797270932 (by decide +kernel)
private theorem contact10ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact10) 40 4 = 6125668578371 :=
  contactColumnsWindow_fast contact10 40 4 6125668578371 (by decide +kernel)
private theorem contact10ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact10) 44 4 = 5761784179616 :=
  contactColumnsWindow_fast contact10 44 4 5761784179616 (by decide +kernel)
private theorem contact10ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact10) 48 4 = 5409184021014 :=
  contactColumnsWindow_fast contact10 48 4 5409184021014 (by decide +kernel)
private theorem contact10ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact10) 52 4 = 5067869964365 :=
  contactColumnsWindow_fast contact10 52 4 5067869964365 (by decide +kernel)
private theorem contact10ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact10) 56 4 = 4737802140534 :=
  contactColumnsWindow_fast contact10 56 4 4737802140534 (by decide +kernel)
private theorem contact10ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact10) 60 4 = 4418982027194 :=
  contactColumnsWindow_fast contact10 60 4 4418982027194 (by decide +kernel)
private theorem contact10ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact10) 64 4 = 4111408671632 :=
  contactColumnsWindow_fast contact10 64 4 4111408671632 (by decide +kernel)
private theorem contact10ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact10) 68 4 = 3815132356530 :=
  contactColumnsWindow_fast contact10 68 4 3815132356530 (by decide +kernel)
private theorem contact10ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact10) 72 4 = 3530137061631 :=
  contactColumnsWindow_fast contact10 72 4 3530137061631 (by decide +kernel)
private theorem contact10ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact10) 76 4 = 3256393268220 :=
  contactColumnsWindow_fast contact10 76 4 3256393268220 (by decide +kernel)
private theorem contact10ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact10) 80 4 = 2993899770383 :=
  contactColumnsWindow_fast contact10 80 4 2993899770383 (by decide +kernel)
private theorem contact10ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact10) 84 4 = 2742659535825 :=
  contactColumnsWindow_fast contact10 84 4 2742659535825 (by decide +kernel)
private theorem contact10ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact10) 88 4 = 2502721200276 :=
  contactColumnsWindow_fast contact10 88 4 2502721200276 (by decide +kernel)
private theorem contact10ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact10) 92 4 = 2274057823197 :=
  contactColumnsWindow_fast contact10 92 4 2274057823197 (by decide +kernel)
private theorem contact10ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact10) 96 4 = 2056645914261 :=
  contactColumnsWindow_fast contact10 96 4 2056645914261 (by decide +kernel)
private theorem contact10ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact10) 100 4 = 1850484596064 :=
  contactColumnsWindow_fast contact10 100 4 1850484596064 (by decide +kernel)
private theorem contact10ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact10) 104 4 = 1655578154979 :=
  contactColumnsWindow_fast contact10 104 4 1655578154979 (by decide +kernel)
private theorem contact10ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact10) 108 4 = 1471977129078 :=
  contactColumnsWindow_fast contact10 108 4 1471977129078 (by decide +kernel)
private theorem contact10ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact10) 112 4 = 1299645773876 :=
  contactColumnsWindow_fast contact10 112 4 1299645773876 (by decide +kernel)
private theorem contact10ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact10) 116 4 = 1138565797566 :=
  contactColumnsWindow_fast contact10 116 4 1138565797566 (by decide +kernel)
private theorem contact10ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact10) 120 4 = 988736591922 :=
  contactColumnsWindow_fast contact10 120 4 988736591922 (by decide +kernel)
private theorem contact10ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact10) 124 4 = 850163982689 :=
  contactColumnsWindow_fast contact10 124 4 850163982689 (by decide +kernel)
private theorem contact10ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact10) 128 4 = 722900241634 :=
  contactColumnsWindow_fast contact10 128 4 722900241634 (by decide +kernel)
private theorem contact10ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact10) 132 4 = 606901019150 :=
  contactColumnsWindow_fast contact10 132 4 606901019150 (by decide +kernel)
private theorem contact10ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact10) 136 4 = 502152765927 :=
  contactColumnsWindow_fast contact10 136 4 502152765927 (by decide +kernel)
private theorem contact10ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact10) 140 4 = 408655681255 :=
  contactColumnsWindow_fast contact10 140 4 408655681255 (by decide +kernel)
private theorem contact10ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact10) 144 4 = 326404093133 :=
  contactColumnsWindow_fast contact10 144 4 326404093133 (by decide +kernel)
private theorem contact10ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact10) 148 4 = 255305717787 :=
  contactColumnsWindow_fast contact10 148 4 255305717787 (by decide +kernel)
private theorem contact10ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact10) 152 4 = 194966915289 :=
  contactColumnsWindow_fast contact10 152 4 194966915289 (by decide +kernel)
private theorem contact10ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact10) 156 4 = 144859788107 :=
  contactColumnsWindow_fast contact10 156 4 144859788107 (by decide +kernel)
private theorem contact10ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact10) 160 4 = 104305340719 :=
  contactColumnsWindow_fast contact10 160 4 104305340719 (by decide +kernel)
private theorem contact10ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact10) 164 4 = 72471423115 :=
  contactColumnsWindow_fast contact10 164 4 72471423115 (by decide +kernel)
private theorem contact10ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact10) 168 4 = 48378038060 :=
  contactColumnsWindow_fast contact10 168 4 48378038060 (by decide +kernel)
private theorem contact10ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact10) 172 1 = 9123408181 :=
  contactColumnsWindow_fast contact10 172 1 9123408181 (by decide +kernel)
private theorem contact10ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact10) 0 8 = 20290345923776 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 4 4 10383362700512 9906983223264 contact10ColumnsSlice0 contact10ColumnsSlice4
private theorem contact10ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact10) 8 8 = 18429788807360 :=
  combineSlices (auxiliaryColumnSlice contact10) 8 4 4 9441843944160 8987944863200 contact10ColumnsSlice8 contact10ColumnsSlice12
private theorem contact10ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact10) 16 8 = 16659153276096 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 4 4 8545285980384 8113867295712 contact10ColumnsSlice16 contact10ColumnsSlice20
private theorem contact10ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact10) 24 8 = 14978473102484 :=
  combineSlices (auxiliaryColumnSlice contact10) 24 4 4 7693688809184 7284784293300 contact10ColumnsSlice24 contact10ColumnsSlice28
private theorem contact10ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact10) 32 8 = 13387966305992 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 4 4 6887169035060 6500797270932 contact10ColumnsSlice32 contact10ColumnsSlice36
private theorem contact10ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact10) 40 8 = 11887452757987 :=
  combineSlices (auxiliaryColumnSlice contact10) 40 4 4 6125668578371 5761784179616 contact10ColumnsSlice40 contact10ColumnsSlice44
private theorem contact10ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact10) 48 8 = 10477053985379 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 4 4 5409184021014 5067869964365 contact10ColumnsSlice48 contact10ColumnsSlice52
private theorem contact10ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact10) 56 8 = 9156784167728 :=
  combineSlices (auxiliaryColumnSlice contact10) 56 4 4 4737802140534 4418982027194 contact10ColumnsSlice56 contact10ColumnsSlice60
private theorem contact10ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact10) 64 8 = 7926541028162 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 4 4 4111408671632 3815132356530 contact10ColumnsSlice64 contact10ColumnsSlice68
private theorem contact10ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact10) 72 8 = 6786530329851 :=
  combineSlices (auxiliaryColumnSlice contact10) 72 4 4 3530137061631 3256393268220 contact10ColumnsSlice72 contact10ColumnsSlice76
private theorem contact10ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact10) 80 8 = 5736559306208 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 4 4 2993899770383 2742659535825 contact10ColumnsSlice80 contact10ColumnsSlice84
private theorem contact10ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact10) 88 8 = 4776779023473 :=
  combineSlices (auxiliaryColumnSlice contact10) 88 4 4 2502721200276 2274057823197 contact10ColumnsSlice88 contact10ColumnsSlice92
private theorem contact10ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact10) 96 8 = 3907130510325 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 4 4 2056645914261 1850484596064 contact10ColumnsSlice96 contact10ColumnsSlice100
private theorem contact10ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact10) 104 8 = 3127555284057 :=
  combineSlices (auxiliaryColumnSlice contact10) 104 4 4 1655578154979 1471977129078 contact10ColumnsSlice104 contact10ColumnsSlice108
private theorem contact10ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact10) 112 8 = 2438211571442 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 4 4 1299645773876 1138565797566 contact10ColumnsSlice112 contact10ColumnsSlice116
private theorem contact10ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact10) 120 8 = 1838900574611 :=
  combineSlices (auxiliaryColumnSlice contact10) 120 4 4 988736591922 850163982689 contact10ColumnsSlice120 contact10ColumnsSlice124
private theorem contact10ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact10) 128 8 = 1329801260784 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 4 4 722900241634 606901019150 contact10ColumnsSlice128 contact10ColumnsSlice132
private theorem contact10ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact10) 136 8 = 910808447182 :=
  combineSlices (auxiliaryColumnSlice contact10) 136 4 4 502152765927 408655681255 contact10ColumnsSlice136 contact10ColumnsSlice140
private theorem contact10ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact10) 144 8 = 581709810920 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 4 4 326404093133 255305717787 contact10ColumnsSlice144 contact10ColumnsSlice148
private theorem contact10ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact10) 152 8 = 339826703396 :=
  combineSlices (auxiliaryColumnSlice contact10) 152 4 4 194966915289 144859788107 contact10ColumnsSlice152 contact10ColumnsSlice156
private theorem contact10ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact10) 160 8 = 176776763834 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 4 4 104305340719 72471423115 contact10ColumnsSlice160 contact10ColumnsSlice164
private theorem contact10ColumnsJoin168_5 : sliceWindow (auxiliaryColumnSlice contact10) 168 5 = 57501446241 :=
  combineSlices (auxiliaryColumnSlice contact10) 168 4 1 48378038060 9123408181 contact10ColumnsSlice168 contact10ColumnsSlice172
private theorem contact10ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact10) 0 16 = 38720134731136 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 8 8 20290345923776 18429788807360 contact10ColumnsJoin0_8 contact10ColumnsJoin8_8
private theorem contact10ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact10) 16 16 = 31637626378580 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 8 8 16659153276096 14978473102484 contact10ColumnsJoin16_8 contact10ColumnsJoin24_8
private theorem contact10ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact10) 32 16 = 25275419063979 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 8 8 13387966305992 11887452757987 contact10ColumnsJoin32_8 contact10ColumnsJoin40_8
private theorem contact10ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact10) 48 16 = 19633838153107 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 8 8 10477053985379 9156784167728 contact10ColumnsJoin48_8 contact10ColumnsJoin56_8
private theorem contact10ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact10) 64 16 = 14713071358013 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 8 8 7926541028162 6786530329851 contact10ColumnsJoin64_8 contact10ColumnsJoin72_8
private theorem contact10ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact10) 80 16 = 10513338329681 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 8 8 5736559306208 4776779023473 contact10ColumnsJoin80_8 contact10ColumnsJoin88_8
private theorem contact10ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact10) 96 16 = 7034685794382 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 8 8 3907130510325 3127555284057 contact10ColumnsJoin96_8 contact10ColumnsJoin104_8
private theorem contact10ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact10) 112 16 = 4277112146053 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 8 8 2438211571442 1838900574611 contact10ColumnsJoin112_8 contact10ColumnsJoin120_8
private theorem contact10ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact10) 128 16 = 2240609707966 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 8 8 1329801260784 910808447182 contact10ColumnsJoin128_8 contact10ColumnsJoin136_8
private theorem contact10ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact10) 144 16 = 921536514316 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 8 8 581709810920 339826703396 contact10ColumnsJoin144_8 contact10ColumnsJoin152_8
private theorem contact10ColumnsJoin160_13 : sliceWindow (auxiliaryColumnSlice contact10) 160 13 = 234278210075 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 8 5 176776763834 57501446241 contact10ColumnsJoin160_8 contact10ColumnsJoin168_5
private theorem contact10ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact10) 0 32 = 70357761109716 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 16 16 38720134731136 31637626378580 contact10ColumnsJoin0_16 contact10ColumnsJoin16_16
private theorem contact10ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact10) 32 32 = 44909257217086 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 16 16 25275419063979 19633838153107 contact10ColumnsJoin32_16 contact10ColumnsJoin48_16
private theorem contact10ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact10) 64 32 = 25226409687694 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 16 16 14713071358013 10513338329681 contact10ColumnsJoin64_16 contact10ColumnsJoin80_16
private theorem contact10ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact10) 96 32 = 11311797940435 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 16 16 7034685794382 4277112146053 contact10ColumnsJoin96_16 contact10ColumnsJoin112_16
private theorem contact10ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact10) 128 32 = 3162146222282 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 16 16 2240609707966 921536514316 contact10ColumnsJoin128_16 contact10ColumnsJoin144_16
private theorem contact10ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact10) 0 64 = 115267018326802 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 32 32 70357761109716 44909257217086 contact10ColumnsJoin0_32 contact10ColumnsJoin32_32
private theorem contact10ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact10) 64 64 = 36538207628129 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 32 32 25226409687694 11311797940435 contact10ColumnsJoin64_32 contact10ColumnsJoin96_32
private theorem contact10ColumnsJoin128_45 : sliceWindow (auxiliaryColumnSlice contact10) 128 45 = 3396424432357 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 32 13 3162146222282 234278210075 contact10ColumnsJoin128_32 contact10ColumnsJoin160_13
private theorem contact10ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact10) 0 128 = 151805225954931 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 64 64 115267018326802 36538207628129 contact10ColumnsJoin0_64 contact10ColumnsJoin64_64
private theorem contact10ColumnsJoin0_173 : sliceWindow (auxiliaryColumnSlice contact10) 0 173 = 155201650387288 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 128 45 151805225954931 3396424432357 contact10ColumnsJoin0_128 contact10ColumnsJoin128_45
private theorem contact10OrdinaryRanks : ordinaryRankBound contact10 = 14733741665 := by decide +kernel
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
  margin_of_checked_counts contact10 173 3831477648122776 155201650387288 14733741665 474228070 rfl contact10OrdinaryColumns contact10ColumnsJoin0_173 contact10OrdinaryRanks contact10RanksJoin0_173 (by decide +kernel)

private theorem contact12OrdinaryColumns : ordinaryColumnCount contact12 = 180073225975709 := by decide +kernel
private theorem contact12ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact12) 0 4 = 1141090173568 :=
  contactColumnsWindow_fast contact12 0 4 1141090173568 (by decide +kernel)
private theorem contact12ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact12) 4 4 = 1049347365680 :=
  contactColumnsWindow_fast contact12 4 4 1049347365680 (by decide +kernel)
private theorem contact12ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact12) 8 4 = 961472212738 :=
  contactColumnsWindow_fast contact12 8 4 961472212738 (by decide +kernel)
private theorem contact12ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact12) 12 4 = 877463608328 :=
  contactColumnsWindow_fast contact12 12 4 877463608328 (by decide +kernel)
private theorem contact12ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact12) 16 4 = 797320397357 :=
  contactColumnsWindow_fast contact12 16 4 797320397357 (by decide +kernel)
private theorem contact12ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact12) 20 4 = 721050737692 :=
  contactColumnsWindow_fast contact12 20 4 721050737692 (by decide +kernel)
private theorem contact12ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact12) 24 4 = 648670632212 :=
  contactColumnsWindow_fast contact12 24 4 648670632212 (by decide +kernel)
private theorem contact12ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact12) 28 4 = 580159518802 :=
  contactColumnsWindow_fast contact12 28 4 580159518802 (by decide +kernel)
private theorem contact12ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact12) 32 4 = 515514771836 :=
  contactColumnsWindow_fast contact12 32 4 515514771836 (by decide +kernel)
private theorem contact12ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact12) 36 4 = 454735674832 :=
  contactColumnsWindow_fast contact12 36 4 454735674832 (by decide +kernel)
private theorem contact12ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact12) 40 4 = 397832124856 :=
  contactColumnsWindow_fast contact12 40 4 397832124856 (by decide +kernel)
private theorem contact12ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact12) 44 4 = 344816959232 :=
  contactColumnsWindow_fast contact12 44 4 344816959232 (by decide +kernel)
private theorem contact12ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact12) 48 4 = 295669904632 :=
  contactColumnsWindow_fast contact12 48 4 295669904632 (by decide +kernel)
private theorem contact12ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact12) 52 4 = 250388995832 :=
  contactColumnsWindow_fast contact12 52 4 250388995832 (by decide +kernel)
private theorem contact12ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact12) 56 4 = 208974049636 :=
  contactColumnsWindow_fast contact12 56 4 208974049636 (by decide +kernel)
private theorem contact12ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact12) 60 4 = 171436610968 :=
  contactColumnsWindow_fast contact12 60 4 171436610968 (by decide +kernel)
private theorem contact12ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact12) 64 4 = 137786346740 :=
  contactColumnsWindow_fast contact12 64 4 137786346740 (by decide +kernel)
private theorem contact12ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact12) 68 4 = 108003422716 :=
  contactColumnsWindow_fast contact12 68 4 108003422716 (by decide +kernel)
private theorem contact12ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact12) 72 4 = 82086280316 :=
  contactColumnsWindow_fast contact12 72 4 82086280316 (by decide +kernel)
private theorem contact12ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact12) 76 4 = 60035484928 :=
  contactColumnsWindow_fast contact12 76 4 60035484928 (by decide +kernel)
private theorem contact12ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact12) 80 4 = 41863702865 :=
  contactColumnsWindow_fast contact12 80 4 41863702865 (by decide +kernel)
private theorem contact12ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact12) 84 4 = 27529229848 :=
  contactColumnsWindow_fast contact12 84 4 27529229848 (by decide +kernel)
private theorem contact12ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact12) 88 4 = 16817039886 :=
  contactColumnsWindow_fast contact12 88 4 16817039886 (by decide +kernel)
private theorem contact12ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact12) 92 4 = 9360891684 :=
  contactColumnsWindow_fast contact12 92 4 9360891684 (by decide +kernel)
private theorem contact12ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact12) 96 1 = 1509028930 :=
  contactColumnsWindow_fast contact12 96 1 1509028930 (by decide +kernel)
private theorem contact12ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact12) 0 8 = 2190437539248 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 4 4 1141090173568 1049347365680 contact12ColumnsSlice0 contact12ColumnsSlice4
private theorem contact12ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact12) 8 8 = 1838935821066 :=
  combineSlices (auxiliaryColumnSlice contact12) 8 4 4 961472212738 877463608328 contact12ColumnsSlice8 contact12ColumnsSlice12
private theorem contact12ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact12) 16 8 = 1518371135049 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 4 4 797320397357 721050737692 contact12ColumnsSlice16 contact12ColumnsSlice20
private theorem contact12ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact12) 24 8 = 1228830151014 :=
  combineSlices (auxiliaryColumnSlice contact12) 24 4 4 648670632212 580159518802 contact12ColumnsSlice24 contact12ColumnsSlice28
private theorem contact12ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact12) 32 8 = 970250446668 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 4 4 515514771836 454735674832 contact12ColumnsSlice32 contact12ColumnsSlice36
private theorem contact12ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact12) 40 8 = 742649084088 :=
  combineSlices (auxiliaryColumnSlice contact12) 40 4 4 397832124856 344816959232 contact12ColumnsSlice40 contact12ColumnsSlice44
private theorem contact12ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact12) 48 8 = 546058900464 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 4 4 295669904632 250388995832 contact12ColumnsSlice48 contact12ColumnsSlice52
private theorem contact12ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact12) 56 8 = 380410660604 :=
  combineSlices (auxiliaryColumnSlice contact12) 56 4 4 208974049636 171436610968 contact12ColumnsSlice56 contact12ColumnsSlice60
private theorem contact12ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact12) 64 8 = 245789769456 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 4 4 137786346740 108003422716 contact12ColumnsSlice64 contact12ColumnsSlice68
private theorem contact12ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact12) 72 8 = 142121765244 :=
  combineSlices (auxiliaryColumnSlice contact12) 72 4 4 82086280316 60035484928 contact12ColumnsSlice72 contact12ColumnsSlice76
private theorem contact12ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact12) 80 8 = 69392932713 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 4 4 41863702865 27529229848 contact12ColumnsSlice80 contact12ColumnsSlice84
private theorem contact12ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact12) 88 8 = 26177931570 :=
  combineSlices (auxiliaryColumnSlice contact12) 88 4 4 16817039886 9360891684 contact12ColumnsSlice88 contact12ColumnsSlice92
private theorem contact12ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact12) 0 16 = 4029373360314 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 8 8 2190437539248 1838935821066 contact12ColumnsJoin0_8 contact12ColumnsJoin8_8
private theorem contact12ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact12) 16 16 = 2747201286063 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 8 8 1518371135049 1228830151014 contact12ColumnsJoin16_8 contact12ColumnsJoin24_8
private theorem contact12ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact12) 32 16 = 1712899530756 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 8 8 970250446668 742649084088 contact12ColumnsJoin32_8 contact12ColumnsJoin40_8
private theorem contact12ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact12) 48 16 = 926469561068 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 8 8 546058900464 380410660604 contact12ColumnsJoin48_8 contact12ColumnsJoin56_8
private theorem contact12ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact12) 64 16 = 387911534700 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 8 8 245789769456 142121765244 contact12ColumnsJoin64_8 contact12ColumnsJoin72_8
private theorem contact12ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact12) 80 16 = 95570864283 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 8 8 69392932713 26177931570 contact12ColumnsJoin80_8 contact12ColumnsJoin88_8
private theorem contact12ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact12) 0 32 = 6776574646377 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 16 16 4029373360314 2747201286063 contact12ColumnsJoin0_16 contact12ColumnsJoin16_16
private theorem contact12ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact12) 32 32 = 2639369091824 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 16 16 1712899530756 926469561068 contact12ColumnsJoin32_16 contact12ColumnsJoin48_16
private theorem contact12ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact12) 64 32 = 483482398983 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 16 16 387911534700 95570864283 contact12ColumnsJoin64_16 contact12ColumnsJoin80_16
private theorem contact12ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact12) 0 64 = 9415943738201 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 32 32 6776574646377 2639369091824 contact12ColumnsJoin0_32 contact12ColumnsJoin32_32
private theorem contact12ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact12) 64 33 = 484991427913 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 32 1 483482398983 1509028930 contact12ColumnsJoin64_32 contact12ColumnsSlice96
private theorem contact12ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact12) 0 97 = 9900935166114 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 64 33 9415943738201 484991427913 contact12ColumnsJoin0_64 contact12ColumnsJoin64_33
private theorem contact12OrdinaryRanks : ordinaryRankBound contact12 = 694413958 := by decide +kernel
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
private theorem contact12RanksSlice92 : sliceWindow (auxiliaryRankSlice contact12) 92 5 = 0 :=
  contactRankWindow_of_rec contact12 92 5 0 (by decide +kernel)
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
private theorem contact12RanksJoin88_9 : sliceWindow (auxiliaryRankSlice contact12) 88 9 = 403 :=
  combineSlices (auxiliaryRankSlice contact12) 88 4 5 403 0 contact12RanksSlice88 contact12RanksSlice92
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
private theorem contact12RanksJoin80_17 : sliceWindow (auxiliaryRankSlice contact12) 80 17 = 32310 :=
  combineSlices (auxiliaryRankSlice contact12) 80 8 9 31907 403 contact12RanksJoin80_8 contact12RanksJoin88_9
private theorem contact12RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact12) 0 32 = 23237405 :=
  combineSlices (auxiliaryRankSlice contact12) 0 16 16 14534680 8702725 contact12RanksJoin0_16 contact12RanksJoin16_16
private theorem contact12RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact12) 32 32 = 6488997 :=
  combineSlices (auxiliaryRankSlice contact12) 32 16 16 4559828 1929169 contact12RanksJoin32_16 contact12RanksJoin48_16
private theorem contact12RanksJoin64_33 : sliceWindow (auxiliaryRankSlice contact12) 64 33 = 552565 :=
  combineSlices (auxiliaryRankSlice contact12) 64 16 17 520255 32310 contact12RanksJoin64_16 contact12RanksJoin80_17
private theorem contact12RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact12) 0 64 = 29726402 :=
  combineSlices (auxiliaryRankSlice contact12) 0 32 32 23237405 6488997 contact12RanksJoin0_32 contact12RanksJoin32_32
private theorem contact12RanksJoin0_97 : sliceWindow (auxiliaryRankSlice contact12) 0 97 = 30278967 :=
  combineSlices (auxiliaryRankSlice contact12) 0 64 33 29726402 552565 contact12RanksJoin0_64 contact12RanksJoin64_33
theorem contact12_margin : sourceMargin contact12 :=
  margin_of_checked_counts contact12 97 180073225975709 9900935166114 694413958 30278967 rfl contact12OrdinaryColumns contact12ColumnsJoin0_97 contact12OrdinaryRanks contact12RanksJoin0_97 (by decide +kernel)

private theorem contact14OrdinaryColumns : ordinaryColumnCount contact14 = 193989805145377 := by decide +kernel
private theorem contact14ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact14) 0 4 = 950134554142 :=
  contactColumnsWindow_fast contact14 0 4 950134554142 (by decide +kernel)
private theorem contact14ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact14) 4 4 = 872745625576 :=
  contactColumnsWindow_fast contact14 4 4 872745625576 (by decide +kernel)
private theorem contact14ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact14) 8 4 = 798676856818 :=
  contactColumnsWindow_fast contact14 8 4 798676856818 (by decide +kernel)
private theorem contact14ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact14) 12 4 = 727913245266 :=
  contactColumnsWindow_fast contact14 12 4 727913245266 (by decide +kernel)
private theorem contact14ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact14) 16 4 = 660452238482 :=
  contactColumnsWindow_fast contact14 16 4 660452238482 (by decide +kernel)
private theorem contact14ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact14) 20 4 = 596292391711 :=
  contactColumnsWindow_fast contact14 20 4 596292391711 (by decide +kernel)
private theorem contact14ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact14) 24 4 = 535438542656 :=
  contactColumnsWindow_fast contact14 24 4 535438542656 (by decide +kernel)
private theorem contact14ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact14) 28 4 = 477906309180 :=
  contactColumnsWindow_fast contact14 28 4 477906309180 (by decide +kernel)
private theorem contact14ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact14) 32 4 = 423680747961 :=
  contactColumnsWindow_fast contact14 32 4 423680747961 (by decide +kernel)
private theorem contact14ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact14) 36 4 = 372757858094 :=
  contactColumnsWindow_fast contact14 36 4 372757858094 (by decide +kernel)
private theorem contact14ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact14) 40 4 = 325136230468 :=
  contactColumnsWindow_fast contact14 40 4 325136230468 (by decide +kernel)
private theorem contact14ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact14) 44 4 = 280821698144 :=
  contactColumnsWindow_fast contact14 44 4 280821698144 (by decide +kernel)
private theorem contact14ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact14) 48 4 = 239828993398 :=
  contactColumnsWindow_fast contact14 48 4 239828993398 (by decide +kernel)
private theorem contact14ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact14) 52 4 = 202141709928 :=
  contactColumnsWindow_fast contact14 52 4 202141709928 (by decide +kernel)
private theorem contact14ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact14) 56 4 = 167756857118 :=
  contactColumnsWindow_fast contact14 56 4 167756857118 (by decide +kernel)
private theorem contact14ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact14) 60 4 = 136673448637 :=
  contactColumnsWindow_fast contact14 60 4 136673448637 (by decide +kernel)
private theorem contact14ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact14) 64 4 = 108898638589 :=
  contactColumnsWindow_fast contact14 64 4 108898638589 (by decide +kernel)
private theorem contact14ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact14) 68 4 = 84445130806 :=
  contactColumnsWindow_fast contact14 68 4 84445130806 (by decide +kernel)
private theorem contact14ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact14) 72 4 = 63296051307 :=
  contactColumnsWindow_fast contact14 72 4 63296051307 (by decide +kernel)
private theorem contact14ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact14) 76 4 = 45449235554 :=
  contactColumnsWindow_fast contact14 76 4 45449235554 (by decide +kernel)
private theorem contact14ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact14) 80 4 = 30903295647 :=
  contactColumnsWindow_fast contact14 80 4 30903295647 (by decide +kernel)
private theorem contact14ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact14) 84 4 = 19626573152 :=
  contactColumnsWindow_fast contact14 84 4 19626573152 (by decide +kernel)
private theorem contact14ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact14) 88 4 = 11441073634 :=
  contactColumnsWindow_fast contact14 88 4 11441073634 (by decide +kernel)
private theorem contact14ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact14) 92 4 = 5973094224 :=
  contactColumnsWindow_fast contact14 92 4 5973094224 (by decide +kernel)
private theorem contact14ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact14) 96 2 = 1647644234 :=
  contactColumnsWindow_fast contact14 96 2 1647644234 (by decide +kernel)
private theorem contact14ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact14) 0 8 = 1822880179718 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 4 4 950134554142 872745625576 contact14ColumnsSlice0 contact14ColumnsSlice4
private theorem contact14ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact14) 8 8 = 1526590102084 :=
  combineSlices (auxiliaryColumnSlice contact14) 8 4 4 798676856818 727913245266 contact14ColumnsSlice8 contact14ColumnsSlice12
private theorem contact14ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact14) 16 8 = 1256744630193 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 4 4 660452238482 596292391711 contact14ColumnsSlice16 contact14ColumnsSlice20
private theorem contact14ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact14) 24 8 = 1013344851836 :=
  combineSlices (auxiliaryColumnSlice contact14) 24 4 4 535438542656 477906309180 contact14ColumnsSlice24 contact14ColumnsSlice28
private theorem contact14ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact14) 32 8 = 796438606055 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 4 4 423680747961 372757858094 contact14ColumnsSlice32 contact14ColumnsSlice36
private theorem contact14ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact14) 40 8 = 605957928612 :=
  combineSlices (auxiliaryColumnSlice contact14) 40 4 4 325136230468 280821698144 contact14ColumnsSlice40 contact14ColumnsSlice44
private theorem contact14ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact14) 48 8 = 441970703326 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 4 4 239828993398 202141709928 contact14ColumnsSlice48 contact14ColumnsSlice52
private theorem contact14ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact14) 56 8 = 304430305755 :=
  combineSlices (auxiliaryColumnSlice contact14) 56 4 4 167756857118 136673448637 contact14ColumnsSlice56 contact14ColumnsSlice60
private theorem contact14ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact14) 64 8 = 193343769395 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 4 4 108898638589 84445130806 contact14ColumnsSlice64 contact14ColumnsSlice68
private theorem contact14ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact14) 72 8 = 108745286861 :=
  combineSlices (auxiliaryColumnSlice contact14) 72 4 4 63296051307 45449235554 contact14ColumnsSlice72 contact14ColumnsSlice76
private theorem contact14ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact14) 80 8 = 50529868799 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 4 4 30903295647 19626573152 contact14ColumnsSlice80 contact14ColumnsSlice84
private theorem contact14ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact14) 88 8 = 17414167858 :=
  combineSlices (auxiliaryColumnSlice contact14) 88 4 4 11441073634 5973094224 contact14ColumnsSlice88 contact14ColumnsSlice92
private theorem contact14ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact14) 0 16 = 3349470281802 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 8 8 1822880179718 1526590102084 contact14ColumnsJoin0_8 contact14ColumnsJoin8_8
private theorem contact14ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact14) 16 16 = 2270089482029 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 8 8 1256744630193 1013344851836 contact14ColumnsJoin16_8 contact14ColumnsJoin24_8
private theorem contact14ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact14) 32 16 = 1402396534667 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 8 8 796438606055 605957928612 contact14ColumnsJoin32_8 contact14ColumnsJoin40_8
private theorem contact14ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact14) 48 16 = 746401009081 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 8 8 441970703326 304430305755 contact14ColumnsJoin48_8 contact14ColumnsJoin56_8
private theorem contact14ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact14) 64 16 = 302089056256 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 8 8 193343769395 108745286861 contact14ColumnsJoin64_8 contact14ColumnsJoin72_8
private theorem contact14ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact14) 80 16 = 67944036657 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 8 8 50529868799 17414167858 contact14ColumnsJoin80_8 contact14ColumnsJoin88_8
private theorem contact14ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact14) 0 32 = 5619559763831 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 16 16 3349470281802 2270089482029 contact14ColumnsJoin0_16 contact14ColumnsJoin16_16
private theorem contact14ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact14) 32 32 = 2148797543748 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 16 16 1402396534667 746401009081 contact14ColumnsJoin32_16 contact14ColumnsJoin48_16
private theorem contact14ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact14) 64 32 = 370033092913 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 16 16 302089056256 67944036657 contact14ColumnsJoin64_16 contact14ColumnsJoin80_16
private theorem contact14ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact14) 0 64 = 7768357307579 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 32 32 5619559763831 2148797543748 contact14ColumnsJoin0_32 contact14ColumnsJoin32_32
private theorem contact14ColumnsJoin64_34 : sliceWindow (auxiliaryColumnSlice contact14) 64 34 = 371680737147 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 32 2 370033092913 1647644234 contact14ColumnsJoin64_32 contact14ColumnsSlice96
private theorem contact14ColumnsJoin0_98 : sliceWindow (auxiliaryColumnSlice contact14) 0 98 = 8140038044726 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 64 34 7768357307579 371680737147 contact14ColumnsJoin0_64 contact14ColumnsJoin64_34
private theorem contact14OrdinaryRanks : ordinaryRankBound contact14 = 746366759 := by decide +kernel
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
private theorem contact14RanksSlice88 : sliceWindow (auxiliaryRankSlice contact14) 88 10 = 0 :=
  contactRankWindow_of_rec contact14 88 10 0 (by decide +kernel)
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
private theorem contact14RanksJoin80_18 : sliceWindow (auxiliaryRankSlice contact14) 80 18 = 14838 :=
  combineSlices (auxiliaryRankSlice contact14) 80 8 10 14838 0 contact14RanksJoin80_8 contact14RanksSlice88
private theorem contact14RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact14) 0 32 = 19200432 :=
  combineSlices (auxiliaryRankSlice contact14) 0 16 16 12067800 7132632 contact14RanksJoin0_16 contact14RanksJoin16_16
private theorem contact14RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact14) 32 32 = 5122686 :=
  combineSlices (auxiliaryRankSlice contact14) 32 16 16 3646840 1475846 contact14RanksJoin32_16 contact14RanksJoin48_16
private theorem contact14RanksJoin64_34 : sliceWindow (auxiliaryRankSlice contact14) 64 34 = 374229 :=
  combineSlices (auxiliaryRankSlice contact14) 64 16 18 359391 14838 contact14RanksJoin64_16 contact14RanksJoin80_18
private theorem contact14RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact14) 0 64 = 24323118 :=
  combineSlices (auxiliaryRankSlice contact14) 0 32 32 19200432 5122686 contact14RanksJoin0_32 contact14RanksJoin32_32
private theorem contact14RanksJoin0_98 : sliceWindow (auxiliaryRankSlice contact14) 0 98 = 24697347 :=
  combineSlices (auxiliaryRankSlice contact14) 0 64 34 24323118 374229 contact14RanksJoin0_64 contact14RanksJoin64_34
theorem contact14_margin : sourceMargin contact14 :=
  margin_of_checked_counts contact14 98 193989805145377 8140038044726 746366759 24697347 rfl contact14OrdinaryColumns contact14ColumnsJoin0_98 contact14OrdinaryRanks contact14RanksJoin0_98 (by decide +kernel)

private theorem contact16OrdinaryColumns : ordinaryColumnCount contact16 = 173426310447711 := by decide +kernel
private theorem contact16ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact16) 0 4 = 1091422467834 :=
  contactColumnsWindow_fast contact16 0 4 1091422467834 (by decide +kernel)
private theorem contact16ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact16) 4 4 = 1004066589102 :=
  contactColumnsWindow_fast contact16 4 4 1004066589102 (by decide +kernel)
private theorem contact16ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact16) 8 4 = 920374799444 :=
  contactColumnsWindow_fast contact16 8 4 920374799444 (by decide +kernel)
private theorem contact16ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact16) 12 4 = 840346123590 :=
  contactColumnsWindow_fast contact16 12 4 840346123590 (by decide +kernel)
private theorem contact16ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact16) 16 4 = 763979440671 :=
  contactColumnsWindow_fast contact16 16 4 763979440671 (by decide +kernel)
private theorem contact16ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact16) 20 4 = 691282436987 :=
  contactColumnsWindow_fast contact16 20 4 691282436987 (by decide +kernel)
private theorem contact16ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact16) 24 4 = 622270096734 :=
  contactColumnsWindow_fast contact16 24 4 622270096734 (by decide +kernel)
private theorem contact16ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact16) 28 4 = 556923193421 :=
  contactColumnsWindow_fast contact16 28 4 556923193421 (by decide +kernel)
private theorem contact16ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact16) 32 4 = 495239226882 :=
  contactColumnsWindow_fast contact16 32 4 495239226882 (by decide +kernel)
private theorem contact16ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact16) 36 4 = 437217503202 :=
  contactColumnsWindow_fast contact16 36 4 437217503202 (by decide +kernel)
private theorem contact16ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact16) 40 4 = 382867318466 :=
  contactColumnsWindow_fast contact16 40 4 382867318466 (by decide +kernel)
private theorem contact16ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact16) 44 4 = 332200714302 :=
  contactColumnsWindow_fast contact16 44 4 332200714302 (by decide +kernel)
private theorem contact16ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact16) 48 4 = 285198716094 :=
  contactColumnsWindow_fast contact16 48 4 285198716094 (by decide +kernel)
private theorem contact16ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact16) 52 4 = 241859440110 :=
  contactColumnsWindow_fast contact16 52 4 241859440110 (by decide +kernel)
private theorem contact16ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact16) 56 4 = 202182711522 :=
  contactColumnsWindow_fast contact16 56 4 202182711522 (by decide +kernel)
private theorem contact16ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact16) 60 4 = 166179347399 :=
  contactColumnsWindow_fast contact16 60 4 166179347399 (by decide +kernel)
private theorem contact16ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact16) 64 4 = 133858441806 :=
  contactColumnsWindow_fast contact16 64 4 133858441806 (by decide +kernel)
private theorem contact16ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact16) 68 4 = 105201418458 :=
  contactColumnsWindow_fast contact16 68 4 105201418458 (by decide +kernel)
private theorem contact16ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact16) 72 4 = 80206763274 :=
  contactColumnsWindow_fast contact16 72 4 80206763274 (by decide +kernel)
private theorem contact16ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact16) 76 4 = 58875029778 :=
  contactColumnsWindow_fast contact16 76 4 58875029778 (by decide +kernel)
private theorem contact16ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact16) 80 4 = 41218932783 :=
  contactColumnsWindow_fast contact16 80 4 41218932783 (by decide +kernel)
private theorem contact16ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact16) 84 4 = 27217131227 :=
  contactColumnsWindow_fast contact16 84 4 27217131227 (by decide +kernel)
private theorem contact16ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact16) 88 4 = 16696992333 :=
  contactColumnsWindow_fast contact16 88 4 16696992333 (by decide +kernel)
private theorem contact16ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact16) 92 4 = 9331212479 :=
  contactColumnsWindow_fast contact16 92 4 9331212479 (by decide +kernel)
private theorem contact16ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact16) 96 3 = 3792093494 :=
  contactColumnsWindow_fast contact16 96 3 3792093494 (by decide +kernel)
private theorem contact16ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact16) 0 8 = 2095489056936 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 4 4 1091422467834 1004066589102 contact16ColumnsSlice0 contact16ColumnsSlice4
private theorem contact16ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact16) 8 8 = 1760720923034 :=
  combineSlices (auxiliaryColumnSlice contact16) 8 4 4 920374799444 840346123590 contact16ColumnsSlice8 contact16ColumnsSlice12
private theorem contact16ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact16) 16 8 = 1455261877658 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 4 4 763979440671 691282436987 contact16ColumnsSlice16 contact16ColumnsSlice20
private theorem contact16ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact16) 24 8 = 1179193290155 :=
  combineSlices (auxiliaryColumnSlice contact16) 24 4 4 622270096734 556923193421 contact16ColumnsSlice24 contact16ColumnsSlice28
private theorem contact16ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact16) 32 8 = 932456730084 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 4 4 495239226882 437217503202 contact16ColumnsSlice32 contact16ColumnsSlice36
private theorem contact16ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact16) 40 8 = 715068032768 :=
  combineSlices (auxiliaryColumnSlice contact16) 40 4 4 382867318466 332200714302 contact16ColumnsSlice40 contact16ColumnsSlice44
private theorem contact16ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact16) 48 8 = 527058156204 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 4 4 285198716094 241859440110 contact16ColumnsSlice48 contact16ColumnsSlice52
private theorem contact16ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact16) 56 8 = 368362058921 :=
  combineSlices (auxiliaryColumnSlice contact16) 56 4 4 202182711522 166179347399 contact16ColumnsSlice56 contact16ColumnsSlice60
private theorem contact16ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact16) 64 8 = 239059860264 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 4 4 133858441806 105201418458 contact16ColumnsSlice64 contact16ColumnsSlice68
private theorem contact16ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact16) 72 8 = 139081793052 :=
  combineSlices (auxiliaryColumnSlice contact16) 72 4 4 80206763274 58875029778 contact16ColumnsSlice72 contact16ColumnsSlice76
private theorem contact16ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact16) 80 8 = 68436064010 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 4 4 41218932783 27217131227 contact16ColumnsSlice80 contact16ColumnsSlice84
private theorem contact16ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact16) 88 8 = 26028204812 :=
  combineSlices (auxiliaryColumnSlice contact16) 88 4 4 16696992333 9331212479 contact16ColumnsSlice88 contact16ColumnsSlice92
private theorem contact16ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact16) 0 16 = 3856209979970 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 8 8 2095489056936 1760720923034 contact16ColumnsJoin0_8 contact16ColumnsJoin8_8
private theorem contact16ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact16) 16 16 = 2634455167813 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 8 8 1455261877658 1179193290155 contact16ColumnsJoin16_8 contact16ColumnsJoin24_8
private theorem contact16ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact16) 32 16 = 1647524762852 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 8 8 932456730084 715068032768 contact16ColumnsJoin32_8 contact16ColumnsJoin40_8
private theorem contact16ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact16) 48 16 = 895420215125 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 8 8 527058156204 368362058921 contact16ColumnsJoin48_8 contact16ColumnsJoin56_8
private theorem contact16ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact16) 64 16 = 378141653316 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 8 8 239059860264 139081793052 contact16ColumnsJoin64_8 contact16ColumnsJoin72_8
private theorem contact16ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact16) 80 16 = 94464268822 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 8 8 68436064010 26028204812 contact16ColumnsJoin80_8 contact16ColumnsJoin88_8
private theorem contact16ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact16) 0 32 = 6490665147783 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 16 16 3856209979970 2634455167813 contact16ColumnsJoin0_16 contact16ColumnsJoin16_16
private theorem contact16ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact16) 32 32 = 2542944977977 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 16 16 1647524762852 895420215125 contact16ColumnsJoin32_16 contact16ColumnsJoin48_16
private theorem contact16ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact16) 64 32 = 472605922138 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 16 16 378141653316 94464268822 contact16ColumnsJoin64_16 contact16ColumnsJoin80_16
private theorem contact16ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact16) 0 64 = 9033610125760 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 32 32 6490665147783 2542944977977 contact16ColumnsJoin0_32 contact16ColumnsJoin32_32
private theorem contact16ColumnsJoin64_35 : sliceWindow (auxiliaryColumnSlice contact16) 64 35 = 476398015632 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 32 3 472605922138 3792093494 contact16ColumnsJoin64_32 contact16ColumnsSlice96
private theorem contact16ColumnsJoin0_99 : sliceWindow (auxiliaryColumnSlice contact16) 0 99 = 9510008141392 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 64 35 9033610125760 476398015632 contact16ColumnsJoin0_64 contact16ColumnsJoin64_35
private theorem contact16OrdinaryRanks : ordinaryRankBound contact16 = 668886591 := by decide +kernel
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
private theorem contact16RanksSlice92 : sliceWindow (auxiliaryRankSlice contact16) 92 7 = 0 :=
  contactRankWindow_of_rec contact16 92 7 0 (by decide +kernel)
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
private theorem contact16RanksJoin88_11 : sliceWindow (auxiliaryRankSlice contact16) 88 11 = 386 :=
  combineSlices (auxiliaryRankSlice contact16) 88 4 7 386 0 contact16RanksSlice88 contact16RanksSlice92
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
private theorem contact16RanksJoin80_19 : sliceWindow (auxiliaryRankSlice contact16) 80 19 = 30763 :=
  combineSlices (auxiliaryRankSlice contact16) 80 8 11 30377 386 contact16RanksJoin80_8 contact16RanksJoin88_11
private theorem contact16RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact16) 0 32 = 22235232 :=
  combineSlices (auxiliaryRankSlice contact16) 0 16 16 13905456 8329776 contact16RanksJoin0_16 contact16RanksJoin16_16
private theorem contact16RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact16) 32 32 = 6198892 :=
  combineSlices (auxiliaryRankSlice contact16) 32 16 16 4358994 1839898 contact16RanksJoin32_16 contact16RanksJoin48_16
private theorem contact16RanksJoin64_35 : sliceWindow (auxiliaryRankSlice contact16) 64 35 = 525737 :=
  combineSlices (auxiliaryRankSlice contact16) 64 16 19 494974 30763 contact16RanksJoin64_16 contact16RanksJoin80_19
private theorem contact16RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact16) 0 64 = 28434124 :=
  combineSlices (auxiliaryRankSlice contact16) 0 32 32 22235232 6198892 contact16RanksJoin0_32 contact16RanksJoin32_32
private theorem contact16RanksJoin0_99 : sliceWindow (auxiliaryRankSlice contact16) 0 99 = 28959861 :=
  combineSlices (auxiliaryRankSlice contact16) 0 64 35 28434124 525737 contact16RanksJoin0_64 contact16RanksJoin64_35
theorem contact16_margin : sourceMargin contact16 :=
  margin_of_checked_counts contact16 99 173426310447711 9510008141392 668886591 28959861 rfl contact16OrdinaryColumns contact16ColumnsJoin0_99 contact16OrdinaryRanks contact16RanksJoin0_99 (by decide +kernel)

private theorem contact18OrdinaryColumns : ordinaryColumnCount contact18 = 2372005564305791 := by decide +kernel
private theorem contact18ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact18) 0 4 = 7049288734884 :=
  contactColumnsWindow_fast contact18 0 4 7049288734884 (by decide +kernel)
private theorem contact18ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact18) 4 4 = 6702165150404 :=
  contactColumnsWindow_fast contact18 4 4 6702165150404 (by decide +kernel)
private theorem contact18ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact18) 8 4 = 6363842197872 :=
  contactColumnsWindow_fast contact18 8 4 6363842197872 (by decide +kernel)
private theorem contact18ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact18) 12 4 = 6034322744508 :=
  contactColumnsWindow_fast contact18 12 4 6034322744508 (by decide +kernel)
private theorem contact18ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact18) 16 4 = 5713604834867 :=
  contactColumnsWindow_fast contact18 16 4 5713604834867 (by decide +kernel)
private theorem contact18ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact18) 20 4 = 5401690419744 :=
  contactColumnsWindow_fast contact18 20 4 5401690419744 (by decide +kernel)
private theorem contact18ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact18) 24 4 = 5098594959520 :=
  contactColumnsWindow_fast contact18 24 4 5098594959520 (by decide +kernel)
private theorem contact18ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact18) 28 4 = 4804336841925 :=
  contactColumnsWindow_fast contact18 28 4 4804336841925 (by decide +kernel)
private theorem contact18ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact18) 32 4 = 4518885370200 :=
  contactColumnsWindow_fast contact18 32 4 4518885370200 (by decide +kernel)
private theorem contact18ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact18) 36 4 = 4242238565948 :=
  contactColumnsWindow_fast contact18 36 4 4242238565948 (by decide +kernel)
private theorem contact18ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact18) 40 4 = 3974398358336 :=
  contactColumnsWindow_fast contact18 40 4 3974398358336 (by decide +kernel)
private theorem contact18ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact18) 44 4 = 3715384032233 :=
  contactColumnsWindow_fast contact18 44 4 3715384032233 (by decide +kernel)
private theorem contact18ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact18) 48 4 = 3465207497136 :=
  contactColumnsWindow_fast contact18 48 4 3465207497136 (by decide +kernel)
private theorem contact18ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact18) 52 4 = 3223839298092 :=
  contactColumnsWindow_fast contact18 52 4 3223839298092 (by decide +kernel)
private theorem contact18ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact18) 56 4 = 2991280093379 :=
  contactColumnsWindow_fast contact18 56 4 2991280093379 (by decide +kernel)
private theorem contact18ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact18) 60 4 = 2767529586642 :=
  contactColumnsWindow_fast contact18 60 4 2767529586642 (by decide +kernel)
private theorem contact18ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact18) 64 4 = 2552614565872 :=
  contactColumnsWindow_fast contact18 64 4 2552614565872 (by decide +kernel)
private theorem contact18ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact18) 68 4 = 2346534718876 :=
  contactColumnsWindow_fast contact18 68 4 2346534718876 (by decide +kernel)
private theorem contact18ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact18) 72 4 = 2149268170362 :=
  contactColumnsWindow_fast contact18 72 4 2149268170362 (by decide +kernel)
private theorem contact18ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact18) 76 4 = 1960811102684 :=
  contactColumnsWindow_fast contact18 76 4 1960811102684 (by decide +kernel)
private theorem contact18ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact18) 80 4 = 1781162506080 :=
  contactColumnsWindow_fast contact18 80 4 1781162506080 (by decide +kernel)
private theorem contact18ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact18) 84 4 = 1610354487386 :=
  contactColumnsWindow_fast contact18 84 4 1610354487386 (by decide +kernel)
private theorem contact18ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact18) 88 4 = 1448377214277 :=
  contactColumnsWindow_fast contact18 88 4 1448377214277 (by decide +kernel)
private theorem contact18ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact18) 92 4 = 1295212750704 :=
  contactColumnsWindow_fast contact18 92 4 1295212750704 (by decide +kernel)
private theorem contact18ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact18) 96 4 = 1150857790421 :=
  contactColumnsWindow_fast contact18 96 4 1150857790421 (by decide +kernel)
private theorem contact18ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact18) 100 4 = 1015312264175 :=
  contactColumnsWindow_fast contact18 100 4 1015312264175 (by decide +kernel)
private theorem contact18ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact18) 104 4 = 888610172252 :=
  contactColumnsWindow_fast contact18 104 4 888610172252 (by decide +kernel)
private theorem contact18ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact18) 108 4 = 770735433939 :=
  contactColumnsWindow_fast contact18 108 4 770735433939 (by decide +kernel)
private theorem contact18ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact18) 112 4 = 661673080417 :=
  contactColumnsWindow_fast contact18 112 4 661673080417 (by decide +kernel)
private theorem contact18ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact18) 116 4 = 561420288560 :=
  contactColumnsWindow_fast contact18 116 4 561420288560 (by decide +kernel)
private theorem contact18ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact18) 120 4 = 469978014884 :=
  contactColumnsWindow_fast contact18 120 4 469978014884 (by decide +kernel)
private theorem contact18ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact18) 124 4 = 387381536291 :=
  contactColumnsWindow_fast contact18 124 4 387381536291 (by decide +kernel)
private theorem contact18ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact18) 128 4 = 313609456392 :=
  contactColumnsWindow_fast contact18 128 4 313609456392 (by decide +kernel)
private theorem contact18ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact18) 132 4 = 248649233096 :=
  contactColumnsWindow_fast contact18 132 4 248649233096 (by decide +kernel)
private theorem contact18ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact18) 136 4 = 192481684428 :=
  contactColumnsWindow_fast contact18 136 4 192481684428 (by decide +kernel)
private theorem contact18ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact18) 140 4 = 144961035731 :=
  contactColumnsWindow_fast contact18 140 4 144961035731 (by decide +kernel)
private theorem contact18ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact18) 144 4 = 105775401765 :=
  contactColumnsWindow_fast contact18 144 4 105775401765 (by decide +kernel)
private theorem contact18ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact18) 148 4 = 74386748526 :=
  contactColumnsWindow_fast contact18 148 4 74386748526 (by decide +kernel)
private theorem contact18ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact18) 152 4 = 50112828925 :=
  contactColumnsWindow_fast contact18 152 4 50112828925 (by decide +kernel)
private theorem contact18ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact18) 156 4 = 32118543282 :=
  contactColumnsWindow_fast contact18 156 4 32118543282 (by decide +kernel)
private theorem contact18ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact18) 160 3 = 15504227021 :=
  contactColumnsWindow_fast contact18 160 3 15504227021 (by decide +kernel)
private theorem contact18ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact18) 0 8 = 13751453885288 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 4 4 7049288734884 6702165150404 contact18ColumnsSlice0 contact18ColumnsSlice4
private theorem contact18ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact18) 8 8 = 12398164942380 :=
  combineSlices (auxiliaryColumnSlice contact18) 8 4 4 6363842197872 6034322744508 contact18ColumnsSlice8 contact18ColumnsSlice12
private theorem contact18ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact18) 16 8 = 11115295254611 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 4 4 5713604834867 5401690419744 contact18ColumnsSlice16 contact18ColumnsSlice20
private theorem contact18ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact18) 24 8 = 9902931801445 :=
  combineSlices (auxiliaryColumnSlice contact18) 24 4 4 5098594959520 4804336841925 contact18ColumnsSlice24 contact18ColumnsSlice28
private theorem contact18ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact18) 32 8 = 8761123936148 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 4 4 4518885370200 4242238565948 contact18ColumnsSlice32 contact18ColumnsSlice36
private theorem contact18ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact18) 40 8 = 7689782390569 :=
  combineSlices (auxiliaryColumnSlice contact18) 40 4 4 3974398358336 3715384032233 contact18ColumnsSlice40 contact18ColumnsSlice44
private theorem contact18ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact18) 48 8 = 6689046795228 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 4 4 3465207497136 3223839298092 contact18ColumnsSlice48 contact18ColumnsSlice52
private theorem contact18ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact18) 56 8 = 5758809680021 :=
  combineSlices (auxiliaryColumnSlice contact18) 56 4 4 2991280093379 2767529586642 contact18ColumnsSlice56 contact18ColumnsSlice60
private theorem contact18ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact18) 64 8 = 4899149284748 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 4 4 2552614565872 2346534718876 contact18ColumnsSlice64 contact18ColumnsSlice68
private theorem contact18ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact18) 72 8 = 4110079273046 :=
  combineSlices (auxiliaryColumnSlice contact18) 72 4 4 2149268170362 1960811102684 contact18ColumnsSlice72 contact18ColumnsSlice76
private theorem contact18ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact18) 80 8 = 3391516993466 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 4 4 1781162506080 1610354487386 contact18ColumnsSlice80 contact18ColumnsSlice84
private theorem contact18ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact18) 88 8 = 2743589964981 :=
  combineSlices (auxiliaryColumnSlice contact18) 88 4 4 1448377214277 1295212750704 contact18ColumnsSlice88 contact18ColumnsSlice92
private theorem contact18ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact18) 96 8 = 2166170054596 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 4 4 1150857790421 1015312264175 contact18ColumnsSlice96 contact18ColumnsSlice100
private theorem contact18ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact18) 104 8 = 1659345606191 :=
  combineSlices (auxiliaryColumnSlice contact18) 104 4 4 888610172252 770735433939 contact18ColumnsSlice104 contact18ColumnsSlice108
private theorem contact18ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact18) 112 8 = 1223093368977 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 4 4 661673080417 561420288560 contact18ColumnsSlice112 contact18ColumnsSlice116
private theorem contact18ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact18) 120 8 = 857359551175 :=
  combineSlices (auxiliaryColumnSlice contact18) 120 4 4 469978014884 387381536291 contact18ColumnsSlice120 contact18ColumnsSlice124
private theorem contact18ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact18) 128 8 = 562258689488 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 4 4 313609456392 248649233096 contact18ColumnsSlice128 contact18ColumnsSlice132
private theorem contact18ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact18) 136 8 = 337442720159 :=
  combineSlices (auxiliaryColumnSlice contact18) 136 4 4 192481684428 144961035731 contact18ColumnsSlice136 contact18ColumnsSlice140
private theorem contact18ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact18) 144 8 = 180162150291 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 4 4 105775401765 74386748526 contact18ColumnsSlice144 contact18ColumnsSlice148
private theorem contact18ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact18) 152 8 = 82231372207 :=
  combineSlices (auxiliaryColumnSlice contact18) 152 4 4 50112828925 32118543282 contact18ColumnsSlice152 contact18ColumnsSlice156
private theorem contact18ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact18) 0 16 = 26149618827668 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 8 8 13751453885288 12398164942380 contact18ColumnsJoin0_8 contact18ColumnsJoin8_8
private theorem contact18ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact18) 16 16 = 21018227056056 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 8 8 11115295254611 9902931801445 contact18ColumnsJoin16_8 contact18ColumnsJoin24_8
private theorem contact18ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact18) 32 16 = 16450906326717 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 8 8 8761123936148 7689782390569 contact18ColumnsJoin32_8 contact18ColumnsJoin40_8
private theorem contact18ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact18) 48 16 = 12447856475249 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 8 8 6689046795228 5758809680021 contact18ColumnsJoin48_8 contact18ColumnsJoin56_8
private theorem contact18ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact18) 64 16 = 9009228557794 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 8 8 4899149284748 4110079273046 contact18ColumnsJoin64_8 contact18ColumnsJoin72_8
private theorem contact18ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact18) 80 16 = 6135106958447 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 8 8 3391516993466 2743589964981 contact18ColumnsJoin80_8 contact18ColumnsJoin88_8
private theorem contact18ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact18) 96 16 = 3825515660787 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 8 8 2166170054596 1659345606191 contact18ColumnsJoin96_8 contact18ColumnsJoin104_8
private theorem contact18ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact18) 112 16 = 2080452920152 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 8 8 1223093368977 857359551175 contact18ColumnsJoin112_8 contact18ColumnsJoin120_8
private theorem contact18ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact18) 128 16 = 899701409647 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 8 8 562258689488 337442720159 contact18ColumnsJoin128_8 contact18ColumnsJoin136_8
private theorem contact18ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact18) 144 16 = 262393522498 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 8 8 180162150291 82231372207 contact18ColumnsJoin144_8 contact18ColumnsJoin152_8
private theorem contact18ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact18) 0 32 = 47167845883724 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 16 16 26149618827668 21018227056056 contact18ColumnsJoin0_16 contact18ColumnsJoin16_16
private theorem contact18ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact18) 32 32 = 28898762801966 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 16 16 16450906326717 12447856475249 contact18ColumnsJoin32_16 contact18ColumnsJoin48_16
private theorem contact18ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact18) 64 32 = 15144335516241 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 16 16 9009228557794 6135106958447 contact18ColumnsJoin64_16 contact18ColumnsJoin80_16
private theorem contact18ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact18) 96 32 = 5905968580939 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 16 16 3825515660787 2080452920152 contact18ColumnsJoin96_16 contact18ColumnsJoin112_16
private theorem contact18ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact18) 128 32 = 1162094932145 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 16 16 899701409647 262393522498 contact18ColumnsJoin128_16 contact18ColumnsJoin144_16
private theorem contact18ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact18) 0 64 = 76066608685690 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 32 32 47167845883724 28898762801966 contact18ColumnsJoin0_32 contact18ColumnsJoin32_32
private theorem contact18ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact18) 64 64 = 21050304097180 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 32 32 15144335516241 5905968580939 contact18ColumnsJoin64_32 contact18ColumnsJoin96_32
private theorem contact18ColumnsJoin128_35 : sliceWindow (auxiliaryColumnSlice contact18) 128 35 = 1177599159166 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 32 3 1162094932145 15504227021 contact18ColumnsJoin128_32 contact18ColumnsSlice160
private theorem contact18ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact18) 0 128 = 97116912782870 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 64 64 76066608685690 21050304097180 contact18ColumnsJoin0_64 contact18ColumnsJoin64_64
private theorem contact18ColumnsJoin0_163 : sliceWindow (auxiliaryColumnSlice contact18) 0 163 = 98294511942036 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 128 35 97116912782870 1177599159166 contact18ColumnsJoin0_128 contact18ColumnsJoin128_35
private theorem contact18OrdinaryRanks : ordinaryRankBound contact18 = 9125180688 := by decide +kernel
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
private theorem contact18RanksSlice148 : sliceWindow (auxiliaryRankSlice contact18) 148 15 = 0 :=
  contactRankWindow_of_rec contact18 148 15 0 (by decide +kernel)
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
private theorem contact18RanksJoin144_19 : sliceWindow (auxiliaryRankSlice contact18) 144 19 = 924 :=
  combineSlices (auxiliaryRankSlice contact18) 144 4 15 924 0 contact18RanksSlice144 contact18RanksSlice148
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
private theorem contact18RanksJoin128_35 : sliceWindow (auxiliaryRankSlice contact18) 128 35 = 393486 :=
  combineSlices (auxiliaryRankSlice contact18) 128 16 19 392562 924 contact18RanksJoin128_16 contact18RanksJoin144_19
private theorem contact18RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact18) 0 64 = 254606922 :=
  combineSlices (auxiliaryRankSlice contact18) 0 32 32 168249760 86357162 contact18RanksJoin0_32 contact18RanksJoin32_32
private theorem contact18RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact18) 64 64 = 43265172 :=
  combineSlices (auxiliaryRankSlice contact18) 64 32 32 34755938 8509234 contact18RanksJoin64_32 contact18RanksJoin96_32
private theorem contact18RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact18) 0 128 = 297872094 :=
  combineSlices (auxiliaryRankSlice contact18) 0 64 64 254606922 43265172 contact18RanksJoin0_64 contact18RanksJoin64_64
private theorem contact18RanksJoin0_163 : sliceWindow (auxiliaryRankSlice contact18) 0 163 = 298265580 :=
  combineSlices (auxiliaryRankSlice contact18) 0 128 35 297872094 393486 contact18RanksJoin0_128 contact18RanksJoin128_35
theorem contact18_margin : sourceMargin contact18 :=
  margin_of_checked_counts contact18 163 2372005564305791 98294511942036 9125180688 298265580 rfl contact18OrdinaryColumns contact18ColumnsJoin0_163 contact18OrdinaryRanks contact18RanksJoin0_163 (by decide +kernel)

private theorem contact20OrdinaryColumns : ordinaryColumnCount contact20 = 53982875593426 := by decide +kernel
private theorem contact20ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact20) 0 4 = 448595813268 :=
  contactColumnsWindow_fast contact20 0 4 448595813268 (by decide +kernel)
private theorem contact20ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact20) 4 4 = 403888797220 :=
  contactColumnsWindow_fast contact20 4 4 403888797220 (by decide +kernel)
private theorem contact20ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact20) 8 4 = 361538895092 :=
  contactColumnsWindow_fast contact20 8 4 361538895092 (by decide +kernel)
private theorem contact20ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact20) 12 4 = 321555988600 :=
  contactColumnsWindow_fast contact20 12 4 321555988600 (by decide +kernel)
private theorem contact20ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact20) 16 4 = 283941155912 :=
  contactColumnsWindow_fast contact20 16 4 283941155912 (by decide +kernel)
private theorem contact20ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact20) 20 4 = 248685319360 :=
  contactColumnsWindow_fast contact20 20 4 248685319360 (by decide +kernel)
private theorem contact20ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact20) 24 4 = 215787909481 :=
  contactColumnsWindow_fast contact20 24 4 215787909481 (by decide +kernel)
private theorem contact20ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact20) 28 4 = 185249875220 :=
  contactColumnsWindow_fast contact20 28 4 185249875220 (by decide +kernel)
private theorem contact20ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact20) 32 4 = 157081765348 :=
  contactColumnsWindow_fast contact20 32 4 157081765348 (by decide +kernel)
private theorem contact20ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact20) 36 4 = 131279816255 :=
  contactColumnsWindow_fast contact20 36 4 131279816255 (by decide +kernel)
private theorem contact20ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact20) 40 4 = 107837037472 :=
  contactColumnsWindow_fast contact20 40 4 107837037472 (by decide +kernel)
private theorem contact20ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact20) 44 4 = 86752529992 :=
  contactColumnsWindow_fast contact20 44 4 86752529992 (by decide +kernel)
private theorem contact20ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact20) 48 4 = 68027755167 :=
  contactColumnsWindow_fast contact20 48 4 68027755167 (by decide +kernel)
private theorem contact20ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact20) 52 4 = 51674241676 :=
  contactColumnsWindow_fast contact20 52 4 51674241676 (by decide +kernel)
private theorem contact20ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact20) 56 4 = 37685189924 :=
  contactColumnsWindow_fast contact20 56 4 37685189924 (by decide +kernel)
private theorem contact20ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact20) 60 4 = 26055455164 :=
  contactColumnsWindow_fast contact20 60 4 26055455164 (by decide +kernel)
private theorem contact20ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact20) 64 4 = 16783680360 :=
  contactColumnsWindow_fast contact20 64 4 16783680360 (by decide +kernel)
private theorem contact20ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact20) 68 4 = 9847487551 :=
  contactColumnsWindow_fast contact20 68 4 9847487551 (by decide +kernel)
private theorem contact20ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact20) 72 4 = 5110552769 :=
  contactColumnsWindow_fast contact20 72 4 5110552769 (by decide +kernel)
private theorem contact20ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact20) 76 2 = 1382183482 :=
  contactColumnsWindow_fast contact20 76 2 1382183482 (by decide +kernel)
private theorem contact20ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact20) 0 8 = 852484610488 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 4 4 448595813268 403888797220 contact20ColumnsSlice0 contact20ColumnsSlice4
private theorem contact20ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact20) 8 8 = 683094883692 :=
  combineSlices (auxiliaryColumnSlice contact20) 8 4 4 361538895092 321555988600 contact20ColumnsSlice8 contact20ColumnsSlice12
private theorem contact20ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact20) 16 8 = 532626475272 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 4 4 283941155912 248685319360 contact20ColumnsSlice16 contact20ColumnsSlice20
private theorem contact20ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact20) 24 8 = 401037784701 :=
  combineSlices (auxiliaryColumnSlice contact20) 24 4 4 215787909481 185249875220 contact20ColumnsSlice24 contact20ColumnsSlice28
private theorem contact20ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact20) 32 8 = 288361581603 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 4 4 157081765348 131279816255 contact20ColumnsSlice32 contact20ColumnsSlice36
private theorem contact20ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact20) 40 8 = 194589567464 :=
  combineSlices (auxiliaryColumnSlice contact20) 40 4 4 107837037472 86752529992 contact20ColumnsSlice40 contact20ColumnsSlice44
private theorem contact20ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact20) 48 8 = 119701996843 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 4 4 68027755167 51674241676 contact20ColumnsSlice48 contact20ColumnsSlice52
private theorem contact20ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact20) 56 8 = 63740645088 :=
  combineSlices (auxiliaryColumnSlice contact20) 56 4 4 37685189924 26055455164 contact20ColumnsSlice56 contact20ColumnsSlice60
private theorem contact20ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact20) 64 8 = 26631167911 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 4 4 16783680360 9847487551 contact20ColumnsSlice64 contact20ColumnsSlice68
private theorem contact20ColumnsJoin72_6 : sliceWindow (auxiliaryColumnSlice contact20) 72 6 = 6492736251 :=
  combineSlices (auxiliaryColumnSlice contact20) 72 4 2 5110552769 1382183482 contact20ColumnsSlice72 contact20ColumnsSlice76
private theorem contact20ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact20) 0 16 = 1535579494180 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 8 8 852484610488 683094883692 contact20ColumnsJoin0_8 contact20ColumnsJoin8_8
private theorem contact20ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact20) 16 16 = 933664259973 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 8 8 532626475272 401037784701 contact20ColumnsJoin16_8 contact20ColumnsJoin24_8
private theorem contact20ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact20) 32 16 = 482951149067 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 8 8 288361581603 194589567464 contact20ColumnsJoin32_8 contact20ColumnsJoin40_8
private theorem contact20ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact20) 48 16 = 183442641931 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 8 8 119701996843 63740645088 contact20ColumnsJoin48_8 contact20ColumnsJoin56_8
private theorem contact20ColumnsJoin64_14 : sliceWindow (auxiliaryColumnSlice contact20) 64 14 = 33123904162 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 8 6 26631167911 6492736251 contact20ColumnsJoin64_8 contact20ColumnsJoin72_6
private theorem contact20ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact20) 0 32 = 2469243754153 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 16 16 1535579494180 933664259973 contact20ColumnsJoin0_16 contact20ColumnsJoin16_16
private theorem contact20ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact20) 32 32 = 666393790998 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 16 16 482951149067 183442641931 contact20ColumnsJoin32_16 contact20ColumnsJoin48_16
private theorem contact20ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact20) 0 64 = 3135637545151 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 32 32 2469243754153 666393790998 contact20ColumnsJoin0_32 contact20ColumnsJoin32_32
private theorem contact20ColumnsJoin0_78 : sliceWindow (auxiliaryColumnSlice contact20) 0 78 = 3168761449313 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 64 14 3135637545151 33123904162 contact20ColumnsJoin0_64 contact20ColumnsJoin64_14
private theorem contact20OrdinaryRanks : ordinaryRankBound contact20 = 208382500 := by decide +kernel
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
private theorem contact20RanksSlice72 : sliceWindow (auxiliaryRankSlice contact20) 72 6 = 0 :=
  contactRankWindow_of_rec contact20 72 6 0 (by decide +kernel)
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
private theorem contact20RanksJoin64_14 : sliceWindow (auxiliaryRankSlice contact20) 64 14 = 10726 :=
  combineSlices (auxiliaryRankSlice contact20) 64 8 6 10726 0 contact20RanksJoin64_8 contact20RanksSlice72
private theorem contact20RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact20) 0 32 = 8245220 :=
  combineSlices (auxiliaryRankSlice contact20) 0 16 16 5461040 2784180 contact20RanksJoin0_16 contact20RanksJoin16_16
private theorem contact20RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact20) 32 32 = 1377549 :=
  combineSlices (auxiliaryRankSlice contact20) 32 16 16 1111668 265881 contact20RanksJoin32_16 contact20RanksJoin48_16
private theorem contact20RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact20) 0 64 = 9622769 :=
  combineSlices (auxiliaryRankSlice contact20) 0 32 32 8245220 1377549 contact20RanksJoin0_32 contact20RanksJoin32_32
private theorem contact20RanksJoin0_78 : sliceWindow (auxiliaryRankSlice contact20) 0 78 = 9633495 :=
  combineSlices (auxiliaryRankSlice contact20) 0 64 14 9622769 10726 contact20RanksJoin0_64 contact20RanksJoin64_14
theorem contact20_margin : sourceMargin contact20 :=
  margin_of_checked_counts contact20 78 53982875593426 3168761449313 208382500 9633495 rfl contact20OrdinaryColumns contact20ColumnsJoin0_78 contact20OrdinaryRanks contact20RanksJoin0_78 (by decide +kernel)

private theorem contact22OrdinaryColumns : ordinaryColumnCount contact22 = 159001211266407 := by decide +kernel
private theorem contact22ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact22) 0 4 = 1567090760276 :=
  contactColumnsWindow_fast contact22 0 4 1567090760276 (by decide +kernel)
private theorem contact22ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact22) 4 4 = 1451654180084 :=
  contactColumnsWindow_fast contact22 4 4 1451654180084 (by decide +kernel)
private theorem contact22ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact22) 8 4 = 1340662806122 :=
  contactColumnsWindow_fast contact22 8 4 1340662806122 (by decide +kernel)
private theorem contact22ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact22) 12 4 = 1234111478720 :=
  contactColumnsWindow_fast contact22 12 4 1234111478720 (by decide +kernel)
private theorem contact22ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact22) 16 4 = 1131998430268 :=
  contactColumnsWindow_fast contact22 16 4 1131998430268 (by decide +kernel)
private theorem contact22ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact22) 20 4 = 1034329352394 :=
  contactColumnsWindow_fast contact22 20 4 1034329352394 (by decide +kernel)
private theorem contact22ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact22) 24 4 = 941127398095 :=
  contactColumnsWindow_fast contact22 24 4 941127398095 (by decide +kernel)
private theorem contact22ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact22) 28 4 = 852371983796 :=
  contactColumnsWindow_fast contact22 28 4 852371983796 (by decide +kernel)
private theorem contact22ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact22) 32 4 = 768056757656 :=
  contactColumnsWindow_fast contact22 32 4 768056757656 (by decide +kernel)
private theorem contact22ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact22) 36 4 = 688179917465 :=
  contactColumnsWindow_fast contact22 36 4 688179917465 (by decide +kernel)
private theorem contact22ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact22) 40 4 = 612748659792 :=
  contactColumnsWindow_fast contact22 40 4 612748659792 (by decide +kernel)
private theorem contact22ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact22) 44 4 = 541784741440 :=
  contactColumnsWindow_fast contact22 44 4 541784741440 (by decide +kernel)
private theorem contact22ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact22) 48 4 = 475265589371 :=
  contactColumnsWindow_fast contact22 48 4 475265589371 (by decide +kernel)
private theorem contact22ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact22) 52 4 = 413186412272 :=
  contactColumnsWindow_fast contact22 52 4 413186412272 (by decide +kernel)
private theorem contact22ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact22) 56 4 = 355545787148 :=
  contactColumnsWindow_fast contact22 56 4 355545787148 (by decide +kernel)
private theorem contact22ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact22) 60 4 = 302352453285 :=
  contactColumnsWindow_fast contact22 60 4 302352453285 (by decide +kernel)
private theorem contact22ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact22) 64 4 = 253626536360 :=
  contactColumnsWindow_fast contact22 64 4 253626536360 (by decide +kernel)
private theorem contact22ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact22) 68 4 = 209343617036 :=
  contactColumnsWindow_fast contact22 68 4 209343617036 (by decide +kernel)
private theorem contact22ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact22) 72 4 = 169500442568 :=
  contactColumnsWindow_fast contact22 72 4 169500442568 (by decide +kernel)
private theorem contact22ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact22) 76 4 = 134096062892 :=
  contactColumnsWindow_fast contact22 76 4 134096062892 (by decide +kernel)
private theorem contact22ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact22) 80 4 = 103141414896 :=
  contactColumnsWindow_fast contact22 80 4 103141414896 (by decide +kernel)
private theorem contact22ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact22) 84 4 = 76652739812 :=
  contactColumnsWindow_fast contact22 84 4 76652739812 (by decide +kernel)
private theorem contact22ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact22) 88 4 = 54604087045 :=
  contactColumnsWindow_fast contact22 88 4 54604087045 (by decide +kernel)
private theorem contact22ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact22) 92 4 = 36937702640 :=
  contactColumnsWindow_fast contact22 92 4 36937702640 (by decide +kernel)
private theorem contact22ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact22) 96 4 = 23441866688 :=
  contactColumnsWindow_fast contact22 96 4 23441866688 (by decide +kernel)
private theorem contact22ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact22) 100 3 = 11030437516 :=
  contactColumnsWindow_fast contact22 100 3 11030437516 (by decide +kernel)
private theorem contact22ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact22) 0 8 = 3018744940360 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 4 4 1567090760276 1451654180084 contact22ColumnsSlice0 contact22ColumnsSlice4
private theorem contact22ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact22) 8 8 = 2574774284842 :=
  combineSlices (auxiliaryColumnSlice contact22) 8 4 4 1340662806122 1234111478720 contact22ColumnsSlice8 contact22ColumnsSlice12
private theorem contact22ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact22) 16 8 = 2166327782662 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 4 4 1131998430268 1034329352394 contact22ColumnsSlice16 contact22ColumnsSlice20
private theorem contact22ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact22) 24 8 = 1793499381891 :=
  combineSlices (auxiliaryColumnSlice contact22) 24 4 4 941127398095 852371983796 contact22ColumnsSlice24 contact22ColumnsSlice28
private theorem contact22ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact22) 32 8 = 1456236675121 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 4 4 768056757656 688179917465 contact22ColumnsSlice32 contact22ColumnsSlice36
private theorem contact22ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact22) 40 8 = 1154533401232 :=
  combineSlices (auxiliaryColumnSlice contact22) 40 4 4 612748659792 541784741440 contact22ColumnsSlice40 contact22ColumnsSlice44
private theorem contact22ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact22) 48 8 = 888452001643 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 4 4 475265589371 413186412272 contact22ColumnsSlice48 contact22ColumnsSlice52
private theorem contact22ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact22) 56 8 = 657898240433 :=
  combineSlices (auxiliaryColumnSlice contact22) 56 4 4 355545787148 302352453285 contact22ColumnsSlice56 contact22ColumnsSlice60
private theorem contact22ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact22) 64 8 = 462970153396 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 4 4 253626536360 209343617036 contact22ColumnsSlice64 contact22ColumnsSlice68
private theorem contact22ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact22) 72 8 = 303596505460 :=
  combineSlices (auxiliaryColumnSlice contact22) 72 4 4 169500442568 134096062892 contact22ColumnsSlice72 contact22ColumnsSlice76
private theorem contact22ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact22) 80 8 = 179794154708 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 4 4 103141414896 76652739812 contact22ColumnsSlice80 contact22ColumnsSlice84
private theorem contact22ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact22) 88 8 = 91541789685 :=
  combineSlices (auxiliaryColumnSlice contact22) 88 4 4 54604087045 36937702640 contact22ColumnsSlice88 contact22ColumnsSlice92
private theorem contact22ColumnsJoin96_7 : sliceWindow (auxiliaryColumnSlice contact22) 96 7 = 34472304204 :=
  combineSlices (auxiliaryColumnSlice contact22) 96 4 3 23441866688 11030437516 contact22ColumnsSlice96 contact22ColumnsSlice100
private theorem contact22ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact22) 0 16 = 5593519225202 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 8 8 3018744940360 2574774284842 contact22ColumnsJoin0_8 contact22ColumnsJoin8_8
private theorem contact22ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact22) 16 16 = 3959827164553 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 8 8 2166327782662 1793499381891 contact22ColumnsJoin16_8 contact22ColumnsJoin24_8
private theorem contact22ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact22) 32 16 = 2610770076353 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 8 8 1456236675121 1154533401232 contact22ColumnsJoin32_8 contact22ColumnsJoin40_8
private theorem contact22ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact22) 48 16 = 1546350242076 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 8 8 888452001643 657898240433 contact22ColumnsJoin48_8 contact22ColumnsJoin56_8
private theorem contact22ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact22) 64 16 = 766566658856 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 8 8 462970153396 303596505460 contact22ColumnsJoin64_8 contact22ColumnsJoin72_8
private theorem contact22ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact22) 80 16 = 271335944393 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 8 8 179794154708 91541789685 contact22ColumnsJoin80_8 contact22ColumnsJoin88_8
private theorem contact22ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact22) 0 32 = 9553346389755 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 16 16 5593519225202 3959827164553 contact22ColumnsJoin0_16 contact22ColumnsJoin16_16
private theorem contact22ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact22) 32 32 = 4157120318429 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 16 16 2610770076353 1546350242076 contact22ColumnsJoin32_16 contact22ColumnsJoin48_16
private theorem contact22ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact22) 64 32 = 1037902603249 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 16 16 766566658856 271335944393 contact22ColumnsJoin64_16 contact22ColumnsJoin80_16
private theorem contact22ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact22) 0 64 = 13710466708184 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 32 32 9553346389755 4157120318429 contact22ColumnsJoin0_32 contact22ColumnsJoin32_32
private theorem contact22ColumnsJoin64_39 : sliceWindow (auxiliaryColumnSlice contact22) 64 39 = 1072374907453 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 32 7 1037902603249 34472304204 contact22ColumnsJoin64_32 contact22ColumnsJoin96_7
private theorem contact22ColumnsJoin0_103 : sliceWindow (auxiliaryColumnSlice contact22) 0 103 = 14782841615637 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 64 39 13710466708184 1072374907453 contact22ColumnsJoin0_64 contact22ColumnsJoin64_39
private theorem contact22OrdinaryRanks : ordinaryRankBound contact22 = 617920366 := by decide +kernel
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
private theorem contact22RanksSlice100 : sliceWindow (auxiliaryRankSlice contact22) 100 3 = 0 :=
  contactRankWindow_of_rec contact22 100 3 0 (by decide +kernel)
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
private theorem contact22RanksJoin96_7 : sliceWindow (auxiliaryRankSlice contact22) 96 7 = 465 :=
  combineSlices (auxiliaryRankSlice contact22) 96 4 3 465 0 contact22RanksSlice96 contact22RanksSlice100
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
private theorem contact22RanksJoin64_39 : sliceWindow (auxiliaryRankSlice contact22) 64 39 = 1437595 :=
  combineSlices (auxiliaryRankSlice contact22) 64 32 7 1437130 465 contact22RanksJoin64_32 contact22RanksJoin96_7
private theorem contact22RanksJoin0_103 : sliceWindow (auxiliaryRankSlice contact22) 0 103 = 45010685 :=
  combineSlices (auxiliaryRankSlice contact22) 0 64 39 43573090 1437595 contact22RanksJoin0_64 contact22RanksJoin64_39
theorem contact22_margin : sourceMargin contact22 :=
  margin_of_checked_counts contact22 103 159001211266407 14782841615637 617920366 45010685 rfl contact22OrdinaryColumns contact22ColumnsJoin0_103 contact22OrdinaryRanks contact22RanksJoin0_103 (by decide +kernel)

private theorem contact24OrdinaryColumns : ordinaryColumnCount contact24 = 166291141067477 := by decide +kernel
private theorem contact24ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact24) 0 4 = 1369733611528 :=
  contactColumnsWindow_fast contact24 0 4 1369733611528 (by decide +kernel)
private theorem contact24ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact24) 4 4 = 1264189710536 :=
  contactColumnsWindow_fast contact24 4 4 1264189710536 (by decide +kernel)
private theorem contact24ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact24) 8 4 = 1162897858184 :=
  contactColumnsWindow_fast contact24 8 4 1162897858184 (by decide +kernel)
private theorem contact24ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact24) 12 4 = 1065876584336 :=
  contactColumnsWindow_fast contact24 12 4 1065876584336 (by decide +kernel)
private theorem contact24ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact24) 16 4 = 973125186837 :=
  contactColumnsWindow_fast contact24 16 4 973125186837 (by decide +kernel)
private theorem contact24ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact24) 20 4 = 884628413124 :=
  contactColumnsWindow_fast contact24 20 4 884628413124 (by decide +kernel)
private theorem contact24ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact24) 24 4 = 800385317432 :=
  contactColumnsWindow_fast contact24 24 4 800385317432 (by decide +kernel)
private theorem contact24ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact24) 28 4 = 720397265300 :=
  contactColumnsWindow_fast contact24 28 4 720397265300 (by decide +kernel)
private theorem contact24ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact24) 32 4 = 644684706890 :=
  contactColumnsWindow_fast contact24 32 4 644684706890 (by decide +kernel)
private theorem contact24ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact24) 36 4 = 573242048211 :=
  contactColumnsWindow_fast contact24 36 4 573242048211 (by decide +kernel)
private theorem contact24ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact24) 40 4 = 506054970804 :=
  contactColumnsWindow_fast contact24 40 4 506054970804 (by decide +kernel)
private theorem contact24ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact24) 44 4 = 443121384272 :=
  contactColumnsWindow_fast contact24 44 4 443121384272 (by decide +kernel)
private theorem contact24ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact24) 48 4 = 384443717806 :=
  contactColumnsWindow_fast contact24 48 4 384443717806 (by decide +kernel)
private theorem contact24ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact24) 52 4 = 330043545086 :=
  contactColumnsWindow_fast contact24 52 4 330043545086 (by decide +kernel)
private theorem contact24ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact24) 56 4 = 279910602945 :=
  contactColumnsWindow_fast contact24 56 4 279910602945 (by decide +kernel)
private theorem contact24ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact24) 60 4 = 234033221844 :=
  contactColumnsWindow_fast contact24 60 4 234033221844 (by decide +kernel)
private theorem contact24ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact24) 64 4 = 192409241052 :=
  contactColumnsWindow_fast contact24 64 4 192409241052 (by decide +kernel)
private theorem contact24ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact24) 68 4 = 155042049346 :=
  contactColumnsWindow_fast contact24 68 4 155042049346 (by decide +kernel)
private theorem contact24ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact24) 72 4 = 121954076642 :=
  contactColumnsWindow_fast contact24 72 4 121954076642 (by decide +kernel)
private theorem contact24ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact24) 76 4 = 93130903878 :=
  contactColumnsWindow_fast contact24 76 4 93130903878 (by decide +kernel)
private theorem contact24ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact24) 80 4 = 68563166244 :=
  contactColumnsWindow_fast contact24 80 4 68563166244 (by decide +kernel)
private theorem contact24ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact24) 84 4 = 48246024446 :=
  contactColumnsWindow_fast contact24 84 4 48246024446 (by decide +kernel)
private theorem contact24ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact24) 88 4 = 32119928771 :=
  contactColumnsWindow_fast contact24 88 4 32119928771 (by decide +kernel)
private theorem contact24ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact24) 92 4 = 19981509378 :=
  contactColumnsWindow_fast contact24 92 4 19981509378 (by decide +kernel)
private theorem contact24ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact24) 96 4 = 11418750776 :=
  contactColumnsWindow_fast contact24 96 4 11418750776 (by decide +kernel)
private theorem contact24ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact24) 0 8 = 2633923322064 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 4 4 1369733611528 1264189710536 contact24ColumnsSlice0 contact24ColumnsSlice4
private theorem contact24ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact24) 8 8 = 2228774442520 :=
  combineSlices (auxiliaryColumnSlice contact24) 8 4 4 1162897858184 1065876584336 contact24ColumnsSlice8 contact24ColumnsSlice12
private theorem contact24ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact24) 16 8 = 1857753599961 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 4 4 973125186837 884628413124 contact24ColumnsSlice16 contact24ColumnsSlice20
private theorem contact24ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact24) 24 8 = 1520782582732 :=
  combineSlices (auxiliaryColumnSlice contact24) 24 4 4 800385317432 720397265300 contact24ColumnsSlice24 contact24ColumnsSlice28
private theorem contact24ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact24) 32 8 = 1217926755101 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 4 4 644684706890 573242048211 contact24ColumnsSlice32 contact24ColumnsSlice36
private theorem contact24ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact24) 40 8 = 949176355076 :=
  combineSlices (auxiliaryColumnSlice contact24) 40 4 4 506054970804 443121384272 contact24ColumnsSlice40 contact24ColumnsSlice44
private theorem contact24ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact24) 48 8 = 714487262892 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 4 4 384443717806 330043545086 contact24ColumnsSlice48 contact24ColumnsSlice52
private theorem contact24ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact24) 56 8 = 513943824789 :=
  combineSlices (auxiliaryColumnSlice contact24) 56 4 4 279910602945 234033221844 contact24ColumnsSlice56 contact24ColumnsSlice60
private theorem contact24ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact24) 64 8 = 347451290398 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 4 4 192409241052 155042049346 contact24ColumnsSlice64 contact24ColumnsSlice68
private theorem contact24ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact24) 72 8 = 215084980520 :=
  combineSlices (auxiliaryColumnSlice contact24) 72 4 4 121954076642 93130903878 contact24ColumnsSlice72 contact24ColumnsSlice76
private theorem contact24ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact24) 80 8 = 116809190690 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 4 4 68563166244 48246024446 contact24ColumnsSlice80 contact24ColumnsSlice84
private theorem contact24ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact24) 88 8 = 52101438149 :=
  combineSlices (auxiliaryColumnSlice contact24) 88 4 4 32119928771 19981509378 contact24ColumnsSlice88 contact24ColumnsSlice92
private theorem contact24ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact24) 0 16 = 4862697764584 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 8 8 2633923322064 2228774442520 contact24ColumnsJoin0_8 contact24ColumnsJoin8_8
private theorem contact24ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact24) 16 16 = 3378536182693 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 8 8 1857753599961 1520782582732 contact24ColumnsJoin16_8 contact24ColumnsJoin24_8
private theorem contact24ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact24) 32 16 = 2167103110177 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 8 8 1217926755101 949176355076 contact24ColumnsJoin32_8 contact24ColumnsJoin40_8
private theorem contact24ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact24) 48 16 = 1228431087681 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 8 8 714487262892 513943824789 contact24ColumnsJoin48_8 contact24ColumnsJoin56_8
private theorem contact24ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact24) 64 16 = 562536270918 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 8 8 347451290398 215084980520 contact24ColumnsJoin64_8 contact24ColumnsJoin72_8
private theorem contact24ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact24) 80 16 = 168910628839 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 8 8 116809190690 52101438149 contact24ColumnsJoin80_8 contact24ColumnsJoin88_8
private theorem contact24ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact24) 0 32 = 8241233947277 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 16 16 4862697764584 3378536182693 contact24ColumnsJoin0_16 contact24ColumnsJoin16_16
private theorem contact24ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact24) 32 32 = 3395534197858 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 16 16 2167103110177 1228431087681 contact24ColumnsJoin32_16 contact24ColumnsJoin48_16
private theorem contact24ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact24) 64 32 = 731446899757 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 16 16 562536270918 168910628839 contact24ColumnsJoin64_16 contact24ColumnsJoin80_16
private theorem contact24ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact24) 0 64 = 11636768145135 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 32 32 8241233947277 3395534197858 contact24ColumnsJoin0_32 contact24ColumnsJoin32_32
private theorem contact24ColumnsJoin64_36 : sliceWindow (auxiliaryColumnSlice contact24) 64 36 = 742865650533 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 32 4 731446899757 11418750776 contact24ColumnsJoin64_32 contact24ColumnsSlice96
private theorem contact24ColumnsJoin0_100 : sliceWindow (auxiliaryColumnSlice contact24) 0 100 = 12379633795668 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 64 36 11636768145135 742865650533 contact24ColumnsJoin0_64 contact24ColumnsJoin64_36
private theorem contact24OrdinaryRanks : ordinaryRankBound contact24 = 643728701 := by decide +kernel
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
private theorem contact24RanksSlice96 : sliceWindow (auxiliaryRankSlice contact24) 96 4 = 0 :=
  contactRankWindow_of_rec contact24 96 4 0 (by decide +kernel)
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
private theorem contact24RanksJoin64_36 : sliceWindow (auxiliaryRankSlice contact24) 64 36 = 937211 :=
  combineSlices (auxiliaryRankSlice contact24) 64 32 4 937211 0 contact24RanksJoin64_32 contact24RanksSlice96
private theorem contact24RanksJoin0_100 : sliceWindow (auxiliaryRankSlice contact24) 0 100 = 37844672 :=
  combineSlices (auxiliaryRankSlice contact24) 0 64 36 36907461 937211 contact24RanksJoin0_64 contact24RanksJoin64_36
theorem contact24_margin : sourceMargin contact24 :=
  margin_of_checked_counts contact24 100 166291141067477 12379633795668 643728701 37844672 rfl contact24OrdinaryColumns contact24ColumnsJoin0_100 contact24OrdinaryRanks contact24RanksJoin0_100 (by decide +kernel)

private theorem contact26OrdinaryColumns : ordinaryColumnCount contact26 = 163989631130354 := by decide +kernel
private theorem contact26ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact26) 0 4 = 1856044061942 :=
  contactColumnsWindow_fast contact26 0 4 1856044061942 (by decide +kernel)
private theorem contact26ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact26) 4 4 = 1724557605686 :=
  contactColumnsWindow_fast contact26 4 4 1724557605686 (by decide +kernel)
private theorem contact26ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact26) 8 4 = 1597924031030 :=
  contactColumnsWindow_fast contact26 8 4 1597924031030 (by decide +kernel)
private theorem contact26ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact26) 12 4 = 1476156510455 :=
  contactColumnsWindow_fast contact26 12 4 1476156510455 (by decide +kernel)
private theorem contact26ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact26) 16 4 = 1359270123746 :=
  contactColumnsWindow_fast contact26 16 4 1359270123746 (by decide +kernel)
private theorem contact26ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact26) 20 4 = 1247239372718 :=
  contactColumnsWindow_fast contact26 20 4 1247239372718 (by decide +kernel)
private theorem contact26ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact26) 24 4 = 1140064031022 :=
  contactColumnsWindow_fast contact26 24 4 1140064031022 (by decide +kernel)
private theorem contact26ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact26) 28 4 = 1037744126846 :=
  contactColumnsWindow_fast contact26 28 4 1037744126846 (by decide +kernel)
private theorem contact26ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact26) 32 4 = 940295499959 :=
  contactColumnsWindow_fast contact26 32 4 940295499959 (by decide +kernel)
private theorem contact26ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact26) 36 4 = 847728960638 :=
  contactColumnsWindow_fast contact26 36 4 847728960638 (by decide +kernel)
private theorem contact26ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact26) 40 4 = 760019144366 :=
  contactColumnsWindow_fast contact26 40 4 760019144366 (by decide +kernel)
private theorem contact26ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact26) 44 4 = 677164352297 :=
  contactColumnsWindow_fast contact26 44 4 677164352297 (by decide +kernel)
private theorem contact26ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact26) 48 4 = 599165373482 :=
  contactColumnsWindow_fast contact26 48 4 599165373482 (by decide +kernel)
private theorem contact26ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact26) 52 4 = 526041386336 :=
  contactColumnsWindow_fast contact26 52 4 526041386336 (by decide +kernel)
private theorem contact26ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact26) 56 4 = 457795708430 :=
  contactColumnsWindow_fast contact26 56 4 457795708430 (by decide +kernel)
private theorem contact26ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact26) 60 4 = 394406826914 :=
  contactColumnsWindow_fast contact26 60 4 394406826914 (by decide +kernel)
private theorem contact26ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact26) 64 4 = 335872663592 :=
  contactColumnsWindow_fast contact26 64 4 335872663592 (by decide +kernel)
private theorem contact26ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact26) 68 4 = 282194531018 :=
  contactColumnsWindow_fast contact26 68 4 282194531018 (by decide +kernel)
private theorem contact26ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact26) 72 4 = 233395187708 :=
  contactColumnsWindow_fast contact26 72 4 233395187708 (by decide +kernel)
private theorem contact26ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact26) 76 4 = 189470457076 :=
  contactColumnsWindow_fast contact26 76 4 189470457076 (by decide +kernel)
private theorem contact26ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact26) 80 4 = 150402420362 :=
  contactColumnsWindow_fast contact26 80 4 150402420362 (by decide +kernel)
private theorem contact26ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact26) 84 4 = 116188885787 :=
  contactColumnsWindow_fast contact26 84 4 116188885787 (by decide +kernel)
private theorem contact26ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact26) 88 4 = 86832060377 :=
  contactColumnsWindow_fast contact26 88 4 86832060377 (by decide +kernel)
private theorem contact26ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact26) 92 4 = 62352901350 :=
  contactColumnsWindow_fast contact26 92 4 62352901350 (by decide +kernel)
private theorem contact26ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact26) 96 4 = 42664994292 :=
  contactColumnsWindow_fast contact26 96 4 42664994292 (by decide +kernel)
private theorem contact26ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact26) 100 4 = 27513226441 :=
  contactColumnsWindow_fast contact26 100 4 27513226441 (by decide +kernel)
private theorem contact26ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact26) 104 2 = 9385279420 :=
  contactColumnsWindow_fast contact26 104 2 9385279420 (by decide +kernel)
private theorem contact26ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact26) 0 8 = 3580601667628 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 4 4 1856044061942 1724557605686 contact26ColumnsSlice0 contact26ColumnsSlice4
private theorem contact26ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact26) 8 8 = 3074080541485 :=
  combineSlices (auxiliaryColumnSlice contact26) 8 4 4 1597924031030 1476156510455 contact26ColumnsSlice8 contact26ColumnsSlice12
private theorem contact26ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact26) 16 8 = 2606509496464 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 4 4 1359270123746 1247239372718 contact26ColumnsSlice16 contact26ColumnsSlice20
private theorem contact26ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact26) 24 8 = 2177808157868 :=
  combineSlices (auxiliaryColumnSlice contact26) 24 4 4 1140064031022 1037744126846 contact26ColumnsSlice24 contact26ColumnsSlice28
private theorem contact26ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact26) 32 8 = 1788024460597 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 4 4 940295499959 847728960638 contact26ColumnsSlice32 contact26ColumnsSlice36
private theorem contact26ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact26) 40 8 = 1437183496663 :=
  combineSlices (auxiliaryColumnSlice contact26) 40 4 4 760019144366 677164352297 contact26ColumnsSlice40 contact26ColumnsSlice44
private theorem contact26ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact26) 48 8 = 1125206759818 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 4 4 599165373482 526041386336 contact26ColumnsSlice48 contact26ColumnsSlice52
private theorem contact26ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact26) 56 8 = 852202535344 :=
  combineSlices (auxiliaryColumnSlice contact26) 56 4 4 457795708430 394406826914 contact26ColumnsSlice56 contact26ColumnsSlice60
private theorem contact26ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact26) 64 8 = 618067194610 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 4 4 335872663592 282194531018 contact26ColumnsSlice64 contact26ColumnsSlice68
private theorem contact26ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact26) 72 8 = 422865644784 :=
  combineSlices (auxiliaryColumnSlice contact26) 72 4 4 233395187708 189470457076 contact26ColumnsSlice72 contact26ColumnsSlice76
private theorem contact26ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact26) 80 8 = 266591306149 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 4 4 150402420362 116188885787 contact26ColumnsSlice80 contact26ColumnsSlice84
private theorem contact26ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact26) 88 8 = 149184961727 :=
  combineSlices (auxiliaryColumnSlice contact26) 88 4 4 86832060377 62352901350 contact26ColumnsSlice88 contact26ColumnsSlice92
private theorem contact26ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact26) 96 8 = 70178220733 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 4 4 42664994292 27513226441 contact26ColumnsSlice96 contact26ColumnsSlice100
private theorem contact26ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact26) 0 16 = 6654682209113 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 8 8 3580601667628 3074080541485 contact26ColumnsJoin0_8 contact26ColumnsJoin8_8
private theorem contact26ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact26) 16 16 = 4784317654332 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 8 8 2606509496464 2177808157868 contact26ColumnsJoin16_8 contact26ColumnsJoin24_8
private theorem contact26ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact26) 32 16 = 3225207957260 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 8 8 1788024460597 1437183496663 contact26ColumnsJoin32_8 contact26ColumnsJoin40_8
private theorem contact26ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact26) 48 16 = 1977409295162 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 8 8 1125206759818 852202535344 contact26ColumnsJoin48_8 contact26ColumnsJoin56_8
private theorem contact26ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact26) 64 16 = 1040932839394 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 8 8 618067194610 422865644784 contact26ColumnsJoin64_8 contact26ColumnsJoin72_8
private theorem contact26ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact26) 80 16 = 415776267876 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 8 8 266591306149 149184961727 contact26ColumnsJoin80_8 contact26ColumnsJoin88_8
private theorem contact26ColumnsJoin96_10 : sliceWindow (auxiliaryColumnSlice contact26) 96 10 = 79563500153 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 8 2 70178220733 9385279420 contact26ColumnsJoin96_8 contact26ColumnsSlice104
private theorem contact26ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact26) 0 32 = 11438999863445 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 16 16 6654682209113 4784317654332 contact26ColumnsJoin0_16 contact26ColumnsJoin16_16
private theorem contact26ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact26) 32 32 = 5202617252422 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 16 16 3225207957260 1977409295162 contact26ColumnsJoin32_16 contact26ColumnsJoin48_16
private theorem contact26ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact26) 64 32 = 1456709107270 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 16 16 1040932839394 415776267876 contact26ColumnsJoin64_16 contact26ColumnsJoin80_16
private theorem contact26ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact26) 0 64 = 16641617115867 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 32 32 11438999863445 5202617252422 contact26ColumnsJoin0_32 contact26ColumnsJoin32_32
private theorem contact26ColumnsJoin64_42 : sliceWindow (auxiliaryColumnSlice contact26) 64 42 = 1536272607423 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 32 10 1456709107270 79563500153 contact26ColumnsJoin64_32 contact26ColumnsJoin96_10
private theorem contact26ColumnsJoin0_106 : sliceWindow (auxiliaryColumnSlice contact26) 0 106 = 18177889723290 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 64 42 16641617115867 1536272607423 contact26ColumnsJoin0_64 contact26ColumnsJoin64_42
private theorem contact26OrdinaryRanks : ordinaryRankBound contact26 = 639570002 := by decide +kernel
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
  margin_of_checked_counts contact26 106 163989631130354 18177889723290 639570002 55339464 rfl contact26OrdinaryColumns contact26ColumnsJoin0_106 contact26OrdinaryRanks contact26RanksJoin0_106 (by decide +kernel)

private theorem contact28OrdinaryColumns : ordinaryColumnCount contact28 = 220257022943224 := by decide +kernel
private theorem contact28ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact28) 0 4 = 898929887494 :=
  contactColumnsWindow_fast contact28 0 4 898929887494 (by decide +kernel)
private theorem contact28ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact28) 4 4 = 823720642854 :=
  contactColumnsWindow_fast contact28 4 4 823720642854 (by decide +kernel)
private theorem contact28ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact28) 8 4 = 751812064135 :=
  contactColumnsWindow_fast contact28 8 4 751812064135 (by decide +kernel)
private theorem contact28ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact28) 12 4 = 683221691370 :=
  contactColumnsWindow_fast contact28 12 4 683221691370 (by decide +kernel)
private theorem contact28ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact28) 16 4 = 617939468867 :=
  contactColumnsWindow_fast contact28 16 4 617939468867 (by decide +kernel)
private theorem contact28ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact28) 20 4 = 555959830078 :=
  contactColumnsWindow_fast contact28 20 4 555959830078 (by decide +kernel)
private theorem contact28ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact28) 24 4 = 497281303858 :=
  contactColumnsWindow_fast contact28 24 4 497281303858 (by decide +kernel)
private theorem contact28ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact28) 28 4 = 441906886467 :=
  contactColumnsWindow_fast contact28 28 4 441906886467 (by decide +kernel)
private theorem contact28ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact28) 32 4 = 389853178023 :=
  contactColumnsWindow_fast contact28 32 4 389853178023 (by decide +kernel)
private theorem contact28ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact28) 36 4 = 341108822306 :=
  contactColumnsWindow_fast contact28 36 4 341108822306 (by decide +kernel)
private theorem contact28ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact28) 40 4 = 295667314558 :=
  contactColumnsWindow_fast contact28 40 4 295667314558 (by decide +kernel)
private theorem contact28ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact28) 44 4 = 253526918968 :=
  contactColumnsWindow_fast contact28 44 4 253526918968 (by decide +kernel)
private theorem contact28ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact28) 48 4 = 214691567204 :=
  contactColumnsWindow_fast contact28 48 4 214691567204 (by decide +kernel)
private theorem contact28ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact28) 52 4 = 179177707314 :=
  contactColumnsWindow_fast contact28 52 4 179177707314 (by decide +kernel)
private theorem contact28ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact28) 56 4 = 146971565684 :=
  contactColumnsWindow_fast contact28 56 4 146971565684 (by decide +kernel)
private theorem contact28ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact28) 60 4 = 118068178450 :=
  contactColumnsWindow_fast contact28 60 4 118068178450 (by decide +kernel)
private theorem contact28ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact28) 64 4 = 92465969910 :=
  contactColumnsWindow_fast contact28 64 4 92465969910 (by decide +kernel)
private theorem contact28ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact28) 68 4 = 70169966972 :=
  contactColumnsWindow_fast contact28 68 4 70169966972 (by decide +kernel)
private theorem contact28ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact28) 72 4 = 51195616017 :=
  contactColumnsWindow_fast contact28 72 4 51195616017 (by decide +kernel)
private theorem contact28ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact28) 76 4 = 35527662651 :=
  contactColumnsWindow_fast contact28 76 4 35527662651 (by decide +kernel)
private theorem contact28ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact28) 80 4 = 23146509164 :=
  contactColumnsWindow_fast contact28 80 4 23146509164 (by decide +kernel)
private theorem contact28ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact28) 84 4 = 13922660756 :=
  contactColumnsWindow_fast contact28 84 4 13922660756 (by decide +kernel)
private theorem contact28ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact28) 88 4 = 7563092900 :=
  contactColumnsWindow_fast contact28 88 4 7563092900 (by decide +kernel)
private theorem contact28ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact28) 92 3 = 2971299138 :=
  contactColumnsWindow_fast contact28 92 3 2971299138 (by decide +kernel)
private theorem contact28ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact28) 0 8 = 1722650530348 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 4 4 898929887494 823720642854 contact28ColumnsSlice0 contact28ColumnsSlice4
private theorem contact28ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact28) 8 8 = 1435033755505 :=
  combineSlices (auxiliaryColumnSlice contact28) 8 4 4 751812064135 683221691370 contact28ColumnsSlice8 contact28ColumnsSlice12
private theorem contact28ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact28) 16 8 = 1173899298945 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 4 4 617939468867 555959830078 contact28ColumnsSlice16 contact28ColumnsSlice20
private theorem contact28ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact28) 24 8 = 939188190325 :=
  combineSlices (auxiliaryColumnSlice contact28) 24 4 4 497281303858 441906886467 contact28ColumnsSlice24 contact28ColumnsSlice28
private theorem contact28ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact28) 32 8 = 730962000329 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 4 4 389853178023 341108822306 contact28ColumnsSlice32 contact28ColumnsSlice36
private theorem contact28ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact28) 40 8 = 549194233526 :=
  combineSlices (auxiliaryColumnSlice contact28) 40 4 4 295667314558 253526918968 contact28ColumnsSlice40 contact28ColumnsSlice44
private theorem contact28ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact28) 48 8 = 393869274518 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 4 4 214691567204 179177707314 contact28ColumnsSlice48 contact28ColumnsSlice52
private theorem contact28ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact28) 56 8 = 265039744134 :=
  combineSlices (auxiliaryColumnSlice contact28) 56 4 4 146971565684 118068178450 contact28ColumnsSlice56 contact28ColumnsSlice60
private theorem contact28ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact28) 64 8 = 162635936882 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 4 4 92465969910 70169966972 contact28ColumnsSlice64 contact28ColumnsSlice68
private theorem contact28ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact28) 72 8 = 86723278668 :=
  combineSlices (auxiliaryColumnSlice contact28) 72 4 4 51195616017 35527662651 contact28ColumnsSlice72 contact28ColumnsSlice76
private theorem contact28ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact28) 80 8 = 37069169920 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 4 4 23146509164 13922660756 contact28ColumnsSlice80 contact28ColumnsSlice84
private theorem contact28ColumnsJoin88_7 : sliceWindow (auxiliaryColumnSlice contact28) 88 7 = 10534392038 :=
  combineSlices (auxiliaryColumnSlice contact28) 88 4 3 7563092900 2971299138 contact28ColumnsSlice88 contact28ColumnsSlice92
private theorem contact28ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact28) 0 16 = 3157684285853 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 8 8 1722650530348 1435033755505 contact28ColumnsJoin0_8 contact28ColumnsJoin8_8
private theorem contact28ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact28) 16 16 = 2113087489270 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 8 8 1173899298945 939188190325 contact28ColumnsJoin16_8 contact28ColumnsJoin24_8
private theorem contact28ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact28) 32 16 = 1280156233855 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 8 8 730962000329 549194233526 contact28ColumnsJoin32_8 contact28ColumnsJoin40_8
private theorem contact28ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact28) 48 16 = 658909018652 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 8 8 393869274518 265039744134 contact28ColumnsJoin48_8 contact28ColumnsJoin56_8
private theorem contact28ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact28) 64 16 = 249359215550 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 8 8 162635936882 86723278668 contact28ColumnsJoin64_8 contact28ColumnsJoin72_8
private theorem contact28ColumnsJoin80_15 : sliceWindow (auxiliaryColumnSlice contact28) 80 15 = 47603561958 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 8 7 37069169920 10534392038 contact28ColumnsJoin80_8 contact28ColumnsJoin88_7
private theorem contact28ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact28) 0 32 = 5270771775123 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 16 16 3157684285853 2113087489270 contact28ColumnsJoin0_16 contact28ColumnsJoin16_16
private theorem contact28ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact28) 32 32 = 1939065252507 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 16 16 1280156233855 658909018652 contact28ColumnsJoin32_16 contact28ColumnsJoin48_16
private theorem contact28ColumnsJoin64_31 : sliceWindow (auxiliaryColumnSlice contact28) 64 31 = 296962777508 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 16 15 249359215550 47603561958 contact28ColumnsJoin64_16 contact28ColumnsJoin80_15
private theorem contact28ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact28) 0 64 = 7209837027630 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 32 32 5270771775123 1939065252507 contact28ColumnsJoin0_32 contact28ColumnsJoin32_32
private theorem contact28ColumnsJoin0_95 : sliceWindow (auxiliaryColumnSlice contact28) 0 95 = 7506799805138 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 64 31 7209837027630 296962777508 contact28ColumnsJoin0_64 contact28ColumnsJoin64_31
private theorem contact28OrdinaryRanks : ordinaryRankBound contact28 = 845981422 := by decide +kernel
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
  margin_of_checked_counts contact28 95 220257022943224 7506799805138 845981422 22868078 rfl contact28OrdinaryColumns contact28ColumnsJoin0_95 contact28OrdinaryRanks contact28RanksJoin0_95 (by decide +kernel)

private theorem contact30OrdinaryColumns : ordinaryColumnCount contact30 = 533127799721112 := by decide +kernel
private theorem contact30ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact30) 0 4 = 1936638924350 :=
  contactColumnsWindow_fast contact30 0 4 1936638924350 (by decide +kernel)
private theorem contact30ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact30) 4 4 = 1802266726190 :=
  contactColumnsWindow_fast contact30 4 4 1802266726190 (by decide +kernel)
private theorem contact30ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact30) 8 4 = 1672749778298 :=
  contactColumnsWindow_fast contact30 8 4 1672749778298 (by decide +kernel)
private theorem contact30ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact30) 12 4 = 1548087956378 :=
  contactColumnsWindow_fast contact30 12 4 1548087956378 (by decide +kernel)
private theorem contact30ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact30) 16 4 = 1428281621362 :=
  contactColumnsWindow_fast contact30 16 4 1428281621362 (by decide +kernel)
private theorem contact30ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact30) 20 4 = 1313346203591 :=
  contactColumnsWindow_fast contact30 20 4 1313346203591 (by decide +kernel)
private theorem contact30ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact30) 24 4 = 1203288790442 :=
  contactColumnsWindow_fast contact30 24 4 1203288790442 (by decide +kernel)
private theorem contact30ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact30) 28 4 = 1098088230614 :=
  contactColumnsWindow_fast contact30 28 4 1098088230614 (by decide +kernel)
private theorem contact30ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact30) 32 4 = 997746044829 :=
  contactColumnsWindow_fast contact30 32 4 997746044829 (by decide +kernel)
private theorem contact30ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact30) 36 4 = 902260574254 :=
  contactColumnsWindow_fast contact30 36 4 902260574254 (by decide +kernel)
private theorem contact30ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact30) 40 4 = 811649396642 :=
  contactColumnsWindow_fast contact30 40 4 811649396642 (by decide +kernel)
private theorem contact30ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact30) 44 4 = 725912856683 :=
  contactColumnsWindow_fast contact30 44 4 725912856683 (by decide +kernel)
private theorem contact30ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact30) 48 4 = 645033394580 :=
  contactColumnsWindow_fast contact30 48 4 645033394580 (by decide +kernel)
private theorem contact30ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact30) 52 4 = 569012077554 :=
  contactColumnsWindow_fast contact30 52 4 569012077554 (by decide +kernel)
private theorem contact30ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact30) 56 4 = 497847438046 :=
  contactColumnsWindow_fast contact30 56 4 497847438046 (by decide +kernel)
private theorem contact30ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact30) 60 4 = 431560548624 :=
  contactColumnsWindow_fast contact30 60 4 431560548624 (by decide +kernel)
private theorem contact30ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact30) 64 4 = 370144905506 :=
  contactColumnsWindow_fast contact30 64 4 370144905506 (by decide +kernel)
private theorem contact30ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact30) 68 4 = 313586486906 :=
  contactColumnsWindow_fast contact30 68 4 313586486906 (by decide +kernel)
private theorem contact30ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact30) 72 4 = 261886024992 :=
  contactColumnsWindow_fast contact30 72 4 261886024992 (by decide +kernel)
private theorem contact30ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact30) 76 4 = 215042994670 :=
  contactColumnsWindow_fast contact30 76 4 215042994670 (by decide +kernel)
private theorem contact30ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact30) 80 4 = 173079672222 :=
  contactColumnsWindow_fast contact30 80 4 173079672222 (by decide +kernel)
private theorem contact30ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact30) 84 4 = 135984865229 :=
  contactColumnsWindow_fast contact30 84 4 135984865229 (by decide +kernel)
private theorem contact30ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact30) 88 4 = 103747513487 :=
  contactColumnsWindow_fast contact30 88 4 103747513487 (by decide +kernel)
private theorem contact30ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact30) 92 4 = 76367942629 :=
  contactColumnsWindow_fast contact30 92 4 76367942629 (by decide +kernel)
private theorem contact30ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact30) 96 4 = 53830806689 :=
  contactColumnsWindow_fast contact30 96 4 53830806689 (by decide +kernel)
private theorem contact30ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact30) 100 4 = 36025663219 :=
  contactColumnsWindow_fast contact30 100 4 36025663219 (by decide +kernel)
private theorem contact30ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact30) 104 4 = 22623516321 :=
  contactColumnsWindow_fast contact30 104 4 22623516321 (by decide +kernel)
private theorem contact30ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact30) 108 4 = 13138903192 :=
  contactColumnsWindow_fast contact30 108 4 13138903192 (by decide +kernel)
private theorem contact30ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact30) 112 2 = 4066752556 :=
  contactColumnsWindow_fast contact30 112 2 4066752556 (by decide +kernel)
private theorem contact30ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact30) 0 8 = 3738905650540 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 4 4 1936638924350 1802266726190 contact30ColumnsSlice0 contact30ColumnsSlice4
private theorem contact30ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact30) 8 8 = 3220837734676 :=
  combineSlices (auxiliaryColumnSlice contact30) 8 4 4 1672749778298 1548087956378 contact30ColumnsSlice8 contact30ColumnsSlice12
private theorem contact30ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact30) 16 8 = 2741627824953 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 4 4 1428281621362 1313346203591 contact30ColumnsSlice16 contact30ColumnsSlice20
private theorem contact30ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact30) 24 8 = 2301377021056 :=
  combineSlices (auxiliaryColumnSlice contact30) 24 4 4 1203288790442 1098088230614 contact30ColumnsSlice24 contact30ColumnsSlice28
private theorem contact30ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact30) 32 8 = 1900006619083 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 4 4 997746044829 902260574254 contact30ColumnsSlice32 contact30ColumnsSlice36
private theorem contact30ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact30) 40 8 = 1537562253325 :=
  combineSlices (auxiliaryColumnSlice contact30) 40 4 4 811649396642 725912856683 contact30ColumnsSlice40 contact30ColumnsSlice44
private theorem contact30ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact30) 48 8 = 1214045472134 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 4 4 645033394580 569012077554 contact30ColumnsSlice48 contact30ColumnsSlice52
private theorem contact30ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact30) 56 8 = 929407986670 :=
  combineSlices (auxiliaryColumnSlice contact30) 56 4 4 497847438046 431560548624 contact30ColumnsSlice56 contact30ColumnsSlice60
private theorem contact30ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact30) 64 8 = 683731392412 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 4 4 370144905506 313586486906 contact30ColumnsSlice64 contact30ColumnsSlice68
private theorem contact30ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact30) 72 8 = 476929019662 :=
  combineSlices (auxiliaryColumnSlice contact30) 72 4 4 261886024992 215042994670 contact30ColumnsSlice72 contact30ColumnsSlice76
private theorem contact30ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact30) 80 8 = 309064537451 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 4 4 173079672222 135984865229 contact30ColumnsSlice80 contact30ColumnsSlice84
private theorem contact30ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact30) 88 8 = 180115456116 :=
  combineSlices (auxiliaryColumnSlice contact30) 88 4 4 103747513487 76367942629 contact30ColumnsSlice88 contact30ColumnsSlice92
private theorem contact30ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact30) 96 8 = 89856469908 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 4 4 53830806689 36025663219 contact30ColumnsSlice96 contact30ColumnsSlice100
private theorem contact30ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact30) 104 8 = 35762419513 :=
  combineSlices (auxiliaryColumnSlice contact30) 104 4 4 22623516321 13138903192 contact30ColumnsSlice104 contact30ColumnsSlice108
private theorem contact30ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact30) 0 16 = 6959743385216 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 8 8 3738905650540 3220837734676 contact30ColumnsJoin0_8 contact30ColumnsJoin8_8
private theorem contact30ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact30) 16 16 = 5043004846009 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 8 8 2741627824953 2301377021056 contact30ColumnsJoin16_8 contact30ColumnsJoin24_8
private theorem contact30ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact30) 32 16 = 3437568872408 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 8 8 1900006619083 1537562253325 contact30ColumnsJoin32_8 contact30ColumnsJoin40_8
private theorem contact30ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact30) 48 16 = 2143453458804 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 8 8 1214045472134 929407986670 contact30ColumnsJoin48_8 contact30ColumnsJoin56_8
private theorem contact30ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact30) 64 16 = 1160660412074 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 8 8 683731392412 476929019662 contact30ColumnsJoin64_8 contact30ColumnsJoin72_8
private theorem contact30ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact30) 80 16 = 489179993567 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 8 8 309064537451 180115456116 contact30ColumnsJoin80_8 contact30ColumnsJoin88_8
private theorem contact30ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact30) 96 16 = 125618889421 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 8 8 89856469908 35762419513 contact30ColumnsJoin96_8 contact30ColumnsJoin104_8
private theorem contact30ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact30) 0 32 = 12002748231225 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 16 16 6959743385216 5043004846009 contact30ColumnsJoin0_16 contact30ColumnsJoin16_16
private theorem contact30ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact30) 32 32 = 5581022331212 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 16 16 3437568872408 2143453458804 contact30ColumnsJoin32_16 contact30ColumnsJoin48_16
private theorem contact30ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact30) 64 32 = 1649840405641 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 16 16 1160660412074 489179993567 contact30ColumnsJoin64_16 contact30ColumnsJoin80_16
private theorem contact30ColumnsJoin96_18 : sliceWindow (auxiliaryColumnSlice contact30) 96 18 = 129685641977 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 16 2 125618889421 4066752556 contact30ColumnsJoin96_16 contact30ColumnsSlice112
private theorem contact30ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact30) 0 64 = 17583770562437 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 32 32 12002748231225 5581022331212 contact30ColumnsJoin0_32 contact30ColumnsJoin32_32
private theorem contact30ColumnsJoin64_50 : sliceWindow (auxiliaryColumnSlice contact30) 64 50 = 1779526047618 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 32 18 1649840405641 129685641977 contact30ColumnsJoin64_32 contact30ColumnsJoin96_18
private theorem contact30ColumnsJoin0_114 : sliceWindow (auxiliaryColumnSlice contact30) 0 114 = 19363296610055 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 64 50 17583770562437 1779526047618 contact30ColumnsJoin0_64 contact30ColumnsJoin64_50
private theorem contact30OrdinaryRanks : ordinaryRankBound contact30 = 2048522208 := by decide +kernel
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
private theorem contact30RanksSlice104 : sliceWindow (auxiliaryRankSlice contact30) 104 10 = 0 :=
  contactRankWindow_of_rec contact30 104 10 0 (by decide +kernel)
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
private theorem contact30RanksJoin96_18 : sliceWindow (auxiliaryRankSlice contact30) 96 18 = 21446 :=
  combineSlices (auxiliaryRankSlice contact30) 96 8 10 21446 0 contact30RanksJoin96_8 contact30RanksSlice104
private theorem contact30RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact30) 0 32 = 41741712 :=
  combineSlices (auxiliaryRankSlice contact30) 0 16 16 25306056 16435656 contact30RanksJoin0_16 contact30RanksJoin16_16
private theorem contact30RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact30) 32 32 = 14727092 :=
  combineSlices (auxiliaryRankSlice contact30) 32 16 16 9710121 5016971 contact30RanksJoin32_16 contact30RanksJoin48_16
private theorem contact30RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact30) 64 32 = 2573741 :=
  combineSlices (auxiliaryRankSlice contact30) 64 16 16 2062174 511567 contact30RanksJoin64_16 contact30RanksJoin80_16
private theorem contact30RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact30) 0 64 = 56468804 :=
  combineSlices (auxiliaryRankSlice contact30) 0 32 32 41741712 14727092 contact30RanksJoin0_32 contact30RanksJoin32_32
private theorem contact30RanksJoin64_50 : sliceWindow (auxiliaryRankSlice contact30) 64 50 = 2595187 :=
  combineSlices (auxiliaryRankSlice contact30) 64 32 18 2573741 21446 contact30RanksJoin64_32 contact30RanksJoin96_18
private theorem contact30RanksJoin0_114 : sliceWindow (auxiliaryRankSlice contact30) 0 114 = 59063991 :=
  combineSlices (auxiliaryRankSlice contact30) 0 64 50 56468804 2595187 contact30RanksJoin0_64 contact30RanksJoin64_50
theorem contact30_margin : sourceMargin contact30 :=
  margin_of_checked_counts contact30 114 533127799721112 19363296610055 2048522208 59063991 rfl contact30OrdinaryColumns contact30ColumnsJoin0_114 contact30OrdinaryRanks contact30RanksJoin0_114 (by decide +kernel)

private theorem contact32OrdinaryColumns : ordinaryColumnCount contact32 = 544653492818409 := by decide +kernel
private theorem contact32ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact32) 0 4 = 1997654951471 :=
  contactColumnsWindow_fast contact32 0 4 1997654951471 (by decide +kernel)
private theorem contact32ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact32) 4 4 = 1858515590596 :=
  contactColumnsWindow_fast contact32 4 4 1858515590596 (by decide +kernel)
private theorem contact32ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact32) 8 4 = 1724425665908 :=
  contactColumnsWindow_fast contact32 8 4 1724425665908 (by decide +kernel)
private theorem contact32ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact32) 12 4 = 1595385040084 :=
  contactColumnsWindow_fast contact32 12 4 1595385040084 (by decide +kernel)
private theorem contact32ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact32) 16 4 = 1471394079888 :=
  contactColumnsWindow_fast contact32 16 4 1471394079888 (by decide +kernel)
private theorem contact32ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact32) 20 4 = 1352468966058 :=
  contactColumnsWindow_fast contact32 20 4 1352468966058 (by decide +kernel)
private theorem contact32ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact32) 24 4 = 1238617093588 :=
  contactColumnsWindow_fast contact32 24 4 1238617093588 (by decide +kernel)
private theorem contact32ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact32) 28 4 = 1129816287269 :=
  contactColumnsWindow_fast contact32 28 4 1129816287269 (by decide +kernel)
private theorem contact32ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact32) 32 4 = 1026068098801 :=
  contactColumnsWindow_fast contact32 32 4 1026068098801 (by decide +kernel)
private theorem contact32ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact32) 36 4 = 927370832268 :=
  contactColumnsWindow_fast contact32 36 4 927370832268 (by decide +kernel)
private theorem contact32ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact32) 40 4 = 833742953898 :=
  contactColumnsWindow_fast contact32 40 4 833742953898 (by decide +kernel)
private theorem contact32ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact32) 44 4 = 745184783676 :=
  contactColumnsWindow_fast contact32 44 4 745184783676 (by decide +kernel)
private theorem contact32ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact32) 48 4 = 661677909974 :=
  contactColumnsWindow_fast contact32 48 4 661677909974 (by decide +kernel)
private theorem contact32ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact32) 52 4 = 583223419063 :=
  contactColumnsWindow_fast contact32 52 4 583223419063 (by decide +kernel)
private theorem contact32ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact32) 56 4 = 509819811984 :=
  contactColumnsWindow_fast contact32 56 4 509819811984 (by decide +kernel)
private theorem contact32ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact32) 60 4 = 441489218200 :=
  contactColumnsWindow_fast contact32 60 4 441489218200 (by decide +kernel)
private theorem contact32ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact32) 64 4 = 378224774640 :=
  contactColumnsWindow_fast contact32 64 4 378224774640 (by decide +kernel)
private theorem contact32ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact32) 68 4 = 320011777886 :=
  contactColumnsWindow_fast contact32 68 4 320011777886 (by decide +kernel)
private theorem contact32ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact32) 72 4 = 266850970546 :=
  contactColumnsWindow_fast contact32 72 4 266850970546 (by decide +kernel)
private theorem contact32ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact32) 76 4 = 218741837977 :=
  contactColumnsWindow_fast contact32 76 4 218741837977 (by decide +kernel)
private theorem contact32ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact32) 80 4 = 175707771988 :=
  contactColumnsWindow_fast contact32 80 4 175707771988 (by decide +kernel)
private theorem contact32ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact32) 84 4 = 137736992940 :=
  contactColumnsWindow_fast contact32 84 4 137736992940 (by decide +kernel)
private theorem contact32ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact32) 88 4 = 104817896985 :=
  contactColumnsWindow_fast contact32 88 4 104817896985 (by decide +kernel)
private theorem contact32ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact32) 92 4 = 76950465257 :=
  contactColumnsWindow_fast contact32 92 4 76950465257 (by decide +kernel)
private theorem contact32ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact32) 96 4 = 54103645984 :=
  contactColumnsWindow_fast contact32 96 4 54103645984 (by decide +kernel)
private theorem contact32ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact32) 100 4 = 36125350368 :=
  contactColumnsWindow_fast contact32 100 4 36125350368 (by decide +kernel)
private theorem contact32ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact32) 104 4 = 22645714242 :=
  contactColumnsWindow_fast contact32 104 4 22645714242 (by decide +kernel)
private theorem contact32ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact32) 108 4 = 13140187597 :=
  contactColumnsWindow_fast contact32 108 4 13140187597 (by decide +kernel)
private theorem contact32ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact32) 112 4 = 6933872543 :=
  contactColumnsWindow_fast contact32 112 4 6933872543 (by decide +kernel)
private theorem contact32ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact32) 0 8 = 3856170542067 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 4 4 1997654951471 1858515590596 contact32ColumnsSlice0 contact32ColumnsSlice4
private theorem contact32ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact32) 8 8 = 3319810705992 :=
  combineSlices (auxiliaryColumnSlice contact32) 8 4 4 1724425665908 1595385040084 contact32ColumnsSlice8 contact32ColumnsSlice12
private theorem contact32ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact32) 16 8 = 2823863045946 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 4 4 1471394079888 1352468966058 contact32ColumnsSlice16 contact32ColumnsSlice20
private theorem contact32ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact32) 24 8 = 2368433380857 :=
  combineSlices (auxiliaryColumnSlice contact32) 24 4 4 1238617093588 1129816287269 contact32ColumnsSlice24 contact32ColumnsSlice28
private theorem contact32ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact32) 32 8 = 1953438931069 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 4 4 1026068098801 927370832268 contact32ColumnsSlice32 contact32ColumnsSlice36
private theorem contact32ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact32) 40 8 = 1578927737574 :=
  combineSlices (auxiliaryColumnSlice contact32) 40 4 4 833742953898 745184783676 contact32ColumnsSlice40 contact32ColumnsSlice44
private theorem contact32ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact32) 48 8 = 1244901329037 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 4 4 661677909974 583223419063 contact32ColumnsSlice48 contact32ColumnsSlice52
private theorem contact32ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact32) 56 8 = 951309030184 :=
  combineSlices (auxiliaryColumnSlice contact32) 56 4 4 509819811984 441489218200 contact32ColumnsSlice56 contact32ColumnsSlice60
private theorem contact32ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact32) 64 8 = 698236552526 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 4 4 378224774640 320011777886 contact32ColumnsSlice64 contact32ColumnsSlice68
private theorem contact32ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact32) 72 8 = 485592808523 :=
  combineSlices (auxiliaryColumnSlice contact32) 72 4 4 266850970546 218741837977 contact32ColumnsSlice72 contact32ColumnsSlice76
private theorem contact32ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact32) 80 8 = 313444764928 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 4 4 175707771988 137736992940 contact32ColumnsSlice80 contact32ColumnsSlice84
private theorem contact32ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact32) 88 8 = 181768362242 :=
  combineSlices (auxiliaryColumnSlice contact32) 88 4 4 104817896985 76950465257 contact32ColumnsSlice88 contact32ColumnsSlice92
private theorem contact32ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact32) 96 8 = 90228996352 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 4 4 54103645984 36125350368 contact32ColumnsSlice96 contact32ColumnsSlice100
private theorem contact32ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact32) 104 8 = 35785901839 :=
  combineSlices (auxiliaryColumnSlice contact32) 104 4 4 22645714242 13140187597 contact32ColumnsSlice104 contact32ColumnsSlice108
private theorem contact32ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact32) 0 16 = 7175981248059 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 8 8 3856170542067 3319810705992 contact32ColumnsJoin0_8 contact32ColumnsJoin8_8
private theorem contact32ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact32) 16 16 = 5192296426803 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 8 8 2823863045946 2368433380857 contact32ColumnsJoin16_8 contact32ColumnsJoin24_8
private theorem contact32ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact32) 32 16 = 3532366668643 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 8 8 1953438931069 1578927737574 contact32ColumnsJoin32_8 contact32ColumnsJoin40_8
private theorem contact32ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact32) 48 16 = 2196210359221 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 8 8 1244901329037 951309030184 contact32ColumnsJoin48_8 contact32ColumnsJoin56_8
private theorem contact32ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact32) 64 16 = 1183829361049 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 8 8 698236552526 485592808523 contact32ColumnsJoin64_8 contact32ColumnsJoin72_8
private theorem contact32ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact32) 80 16 = 495213127170 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 8 8 313444764928 181768362242 contact32ColumnsJoin80_8 contact32ColumnsJoin88_8
private theorem contact32ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact32) 96 16 = 126014898191 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 8 8 90228996352 35785901839 contact32ColumnsJoin96_8 contact32ColumnsJoin104_8
private theorem contact32ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact32) 0 32 = 12368277674862 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 16 16 7175981248059 5192296426803 contact32ColumnsJoin0_16 contact32ColumnsJoin16_16
private theorem contact32ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact32) 32 32 = 5728577027864 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 16 16 3532366668643 2196210359221 contact32ColumnsJoin32_16 contact32ColumnsJoin48_16
private theorem contact32ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact32) 64 32 = 1679042488219 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 16 16 1183829361049 495213127170 contact32ColumnsJoin64_16 contact32ColumnsJoin80_16
private theorem contact32ColumnsJoin96_20 : sliceWindow (auxiliaryColumnSlice contact32) 96 20 = 132948770734 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 16 4 126014898191 6933872543 contact32ColumnsJoin96_16 contact32ColumnsSlice112
private theorem contact32ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact32) 0 64 = 18096854702726 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 32 32 12368277674862 5728577027864 contact32ColumnsJoin0_32 contact32ColumnsJoin32_32
private theorem contact32ColumnsJoin64_52 : sliceWindow (auxiliaryColumnSlice contact32) 64 52 = 1811991258953 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 32 20 1679042488219 132948770734 contact32ColumnsJoin64_32 contact32ColumnsJoin96_20
private theorem contact32ColumnsJoin0_116 : sliceWindow (auxiliaryColumnSlice contact32) 0 116 = 19908845961679 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 64 52 18096854702726 1811991258953 contact32ColumnsJoin0_64 contact32ColumnsJoin64_52
private theorem contact32OrdinaryRanks : ordinaryRankBound contact32 = 2092713178 := by decide +kernel
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
private theorem contact32RanksSlice104 : sliceWindow (auxiliaryRankSlice contact32) 104 12 = 0 :=
  contactRankWindow_of_rec contact32 104 12 0 (by decide +kernel)
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
private theorem contact32RanksJoin96_20 : sliceWindow (auxiliaryRankSlice contact32) 96 20 = 22146 :=
  combineSlices (auxiliaryRankSlice contact32) 96 8 12 22146 0 contact32RanksJoin96_8 contact32RanksSlice104
private theorem contact32RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact32) 0 32 = 43042512 :=
  combineSlices (auxiliaryRankSlice contact32) 0 16 16 26098920 16943592 contact32RanksJoin0_16 contact32RanksJoin16_16
private theorem contact32RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact32) 32 32 = 15194956 :=
  combineSlices (auxiliaryRankSlice contact32) 32 16 16 10015147 5179809 contact32RanksJoin32_16 contact32RanksJoin48_16
private theorem contact32RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact32) 64 32 = 2661203 :=
  combineSlices (auxiliaryRankSlice contact32) 64 16 16 2131726 529477 contact32RanksJoin64_16 contact32RanksJoin80_16
private theorem contact32RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact32) 0 64 = 58237468 :=
  combineSlices (auxiliaryRankSlice contact32) 0 32 32 43042512 15194956 contact32RanksJoin0_32 contact32RanksJoin32_32
private theorem contact32RanksJoin64_52 : sliceWindow (auxiliaryRankSlice contact32) 64 52 = 2683349 :=
  combineSlices (auxiliaryRankSlice contact32) 64 32 20 2661203 22146 contact32RanksJoin64_32 contact32RanksJoin96_20
private theorem contact32RanksJoin0_116 : sliceWindow (auxiliaryRankSlice contact32) 0 116 = 60920817 :=
  combineSlices (auxiliaryRankSlice contact32) 0 64 52 58237468 2683349 contact32RanksJoin0_64 contact32RanksJoin64_52
theorem contact32_margin : sourceMargin contact32 :=
  margin_of_checked_counts contact32 116 544653492818409 19908845961679 2092713178 60920817 rfl contact32OrdinaryColumns contact32ColumnsJoin0_116 contact32OrdinaryRanks contact32RanksJoin0_116 (by decide +kernel)

private theorem contact34OrdinaryColumns : ordinaryColumnCount contact34 = 2275610325632433 := by decide +kernel
private theorem contact34ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact34) 0 4 = 6334248116956 :=
  contactColumnsWindow_fast contact34 0 4 6334248116956 (by decide +kernel)
private theorem contact34ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact34) 4 4 = 6010210389334 :=
  contactColumnsWindow_fast contact34 4 4 6010210389334 (by decide +kernel)
private theorem contact34ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact34) 8 4 = 5694754087428 :=
  contactColumnsWindow_fast contact34 8 4 5694754087428 (by decide +kernel)
private theorem contact34ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact34) 12 4 = 5387855563478 :=
  contactColumnsWindow_fast contact34 12 4 5387855563478 (by decide +kernel)
private theorem contact34ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact34) 16 4 = 5089502229705 :=
  contactColumnsWindow_fast contact34 16 4 5089502229705 (by decide +kernel)
private theorem contact34ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact34) 20 4 = 4799694981544 :=
  contactColumnsWindow_fast contact34 20 4 4799694981544 (by decide +kernel)
private theorem contact34ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact34) 24 4 = 4518437745058 :=
  contactColumnsWindow_fast contact34 24 4 4518437745058 (by decide +kernel)
private theorem contact34ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact34) 28 4 = 4245766547241 :=
  contactColumnsWindow_fast contact34 28 4 4245766547241 (by decide +kernel)
private theorem contact34ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact34) 32 4 = 3981653472782 :=
  contactColumnsWindow_fast contact34 32 4 3981653472782 (by decide +kernel)
private theorem contact34ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact34) 36 4 = 3726087867519 :=
  contactColumnsWindow_fast contact34 36 4 3726087867519 (by decide +kernel)
private theorem contact34ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact34) 40 4 = 3479072600308 :=
  contactColumnsWindow_fast contact34 40 4 3479072600308 (by decide +kernel)
private theorem contact34ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact34) 44 4 = 3240612093104 :=
  contactColumnsWindow_fast contact34 44 4 3240612093104 (by decide +kernel)
private theorem contact34ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact34) 48 4 = 3010742180067 :=
  contactColumnsWindow_fast contact34 48 4 3010742180067 (by decide +kernel)
private theorem contact34ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact34) 52 4 = 2789430731594 :=
  contactColumnsWindow_fast contact34 52 4 2789430731594 (by decide +kernel)
private theorem contact34ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact34) 56 4 = 2576670078782 :=
  contactColumnsWindow_fast contact34 56 4 2576670078782 (by decide +kernel)
private theorem contact34ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact34) 60 4 = 2372459753306 :=
  contactColumnsWindow_fast contact34 60 4 2372459753306 (by decide +kernel)
private theorem contact34ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact34) 64 4 = 2176806866792 :=
  contactColumnsWindow_fast contact34 64 4 2176806866792 (by decide +kernel)
private theorem contact34ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact34) 68 4 = 1989744283707 :=
  contactColumnsWindow_fast contact34 68 4 1989744283707 (by decide +kernel)
private theorem contact34ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact34) 72 4 = 1811237973965 :=
  contactColumnsWindow_fast contact34 72 4 1811237973965 (by decide +kernel)
private theorem contact34ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact34) 76 4 = 1641282428042 :=
  contactColumnsWindow_fast contact34 76 4 1641282428042 (by decide +kernel)
private theorem contact34ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact34) 80 4 = 1479876844958 :=
  contactColumnsWindow_fast contact34 80 4 1479876844958 (by decide +kernel)
private theorem contact34ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact34) 84 4 = 1327031659802 :=
  contactColumnsWindow_fast contact34 84 4 1327031659802 (by decide +kernel)
private theorem contact34ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact34) 88 4 = 1182776517210 :=
  contactColumnsWindow_fast contact34 88 4 1182776517210 (by decide +kernel)
private theorem contact34ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact34) 92 4 = 1047075205595 :=
  contactColumnsWindow_fast contact34 92 4 1047075205595 (by decide +kernel)
private theorem contact34ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact34) 96 4 = 919924700486 :=
  contactColumnsWindow_fast contact34 96 4 919924700486 (by decide +kernel)
private theorem contact34ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact34) 100 4 = 801324010939 :=
  contactColumnsWindow_fast contact34 100 4 801324010939 (by decide +kernel)
private theorem contact34ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact34) 104 4 = 691287665750 :=
  contactColumnsWindow_fast contact34 104 4 691287665750 (by decide +kernel)
private theorem contact34ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact34) 108 4 = 589838722254 :=
  contactColumnsWindow_fast contact34 108 4 589838722254 (by decide +kernel)
private theorem contact34ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact34) 112 4 = 496942418397 :=
  contactColumnsWindow_fast contact34 112 4 496942418397 (by decide +kernel)
private theorem contact34ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact34) 116 4 = 412596973785 :=
  contactColumnsWindow_fast contact34 116 4 412596973785 (by decide +kernel)
private theorem contact34ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact34) 120 4 = 336801227149 :=
  contactColumnsWindow_fast contact34 120 4 336801227149 (by decide +kernel)
private theorem contact34ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact34) 124 4 = 269573595623 :=
  contactColumnsWindow_fast contact34 124 4 269573595623 (by decide +kernel)
private theorem contact34ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact34) 128 4 = 210929738859 :=
  contactColumnsWindow_fast contact34 128 4 210929738859 (by decide +kernel)
private theorem contact34ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact34) 132 4 = 160785310143 :=
  contactColumnsWindow_fast contact34 132 4 160785310143 (by decide +kernel)
private theorem contact34ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact34) 136 4 = 118910721767 :=
  contactColumnsWindow_fast contact34 136 4 118910721767 (by decide +kernel)
private theorem contact34ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact34) 140 4 = 84894165127 :=
  contactColumnsWindow_fast contact34 140 4 84894165127 (by decide +kernel)
private theorem contact34ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact34) 144 4 = 58181709945 :=
  contactColumnsWindow_fast contact34 144 4 58181709945 (by decide +kernel)
private theorem contact34ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact34) 148 4 = 38038255793 :=
  contactColumnsWindow_fast contact34 148 4 38038255793 (by decide +kernel)
private theorem contact34ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact34) 152 4 = 23535271577 :=
  contactColumnsWindow_fast contact34 152 4 23535271577 (by decide +kernel)
private theorem contact34ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact34) 0 8 = 12344458506290 :=
  combineSlices (auxiliaryColumnSlice contact34) 0 4 4 6334248116956 6010210389334 contact34ColumnsSlice0 contact34ColumnsSlice4
private theorem contact34ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact34) 8 8 = 11082609650906 :=
  combineSlices (auxiliaryColumnSlice contact34) 8 4 4 5694754087428 5387855563478 contact34ColumnsSlice8 contact34ColumnsSlice12
private theorem contact34ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact34) 16 8 = 9889197211249 :=
  combineSlices (auxiliaryColumnSlice contact34) 16 4 4 5089502229705 4799694981544 contact34ColumnsSlice16 contact34ColumnsSlice20
private theorem contact34ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact34) 24 8 = 8764204292299 :=
  combineSlices (auxiliaryColumnSlice contact34) 24 4 4 4518437745058 4245766547241 contact34ColumnsSlice24 contact34ColumnsSlice28
private theorem contact34ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact34) 32 8 = 7707741340301 :=
  combineSlices (auxiliaryColumnSlice contact34) 32 4 4 3981653472782 3726087867519 contact34ColumnsSlice32 contact34ColumnsSlice36
private theorem contact34ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact34) 40 8 = 6719684693412 :=
  combineSlices (auxiliaryColumnSlice contact34) 40 4 4 3479072600308 3240612093104 contact34ColumnsSlice40 contact34ColumnsSlice44
private theorem contact34ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact34) 48 8 = 5800172911661 :=
  combineSlices (auxiliaryColumnSlice contact34) 48 4 4 3010742180067 2789430731594 contact34ColumnsSlice48 contact34ColumnsSlice52
private theorem contact34ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact34) 56 8 = 4949129832088 :=
  combineSlices (auxiliaryColumnSlice contact34) 56 4 4 2576670078782 2372459753306 contact34ColumnsSlice56 contact34ColumnsSlice60
private theorem contact34ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact34) 64 8 = 4166551150499 :=
  combineSlices (auxiliaryColumnSlice contact34) 64 4 4 2176806866792 1989744283707 contact34ColumnsSlice64 contact34ColumnsSlice68
private theorem contact34ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact34) 72 8 = 3452520402007 :=
  combineSlices (auxiliaryColumnSlice contact34) 72 4 4 1811237973965 1641282428042 contact34ColumnsSlice72 contact34ColumnsSlice76
private theorem contact34ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact34) 80 8 = 2806908504760 :=
  combineSlices (auxiliaryColumnSlice contact34) 80 4 4 1479876844958 1327031659802 contact34ColumnsSlice80 contact34ColumnsSlice84
private theorem contact34ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact34) 88 8 = 2229851722805 :=
  combineSlices (auxiliaryColumnSlice contact34) 88 4 4 1182776517210 1047075205595 contact34ColumnsSlice88 contact34ColumnsSlice92
private theorem contact34ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact34) 96 8 = 1721248711425 :=
  combineSlices (auxiliaryColumnSlice contact34) 96 4 4 919924700486 801324010939 contact34ColumnsSlice96 contact34ColumnsSlice100
private theorem contact34ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact34) 104 8 = 1281126388004 :=
  combineSlices (auxiliaryColumnSlice contact34) 104 4 4 691287665750 589838722254 contact34ColumnsSlice104 contact34ColumnsSlice108
private theorem contact34ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact34) 112 8 = 909539392182 :=
  combineSlices (auxiliaryColumnSlice contact34) 112 4 4 496942418397 412596973785 contact34ColumnsSlice112 contact34ColumnsSlice116
private theorem contact34ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact34) 120 8 = 606374822772 :=
  combineSlices (auxiliaryColumnSlice contact34) 120 4 4 336801227149 269573595623 contact34ColumnsSlice120 contact34ColumnsSlice124
private theorem contact34ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact34) 128 8 = 371715049002 :=
  combineSlices (auxiliaryColumnSlice contact34) 128 4 4 210929738859 160785310143 contact34ColumnsSlice128 contact34ColumnsSlice132
private theorem contact34ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact34) 136 8 = 203804886894 :=
  combineSlices (auxiliaryColumnSlice contact34) 136 4 4 118910721767 84894165127 contact34ColumnsSlice136 contact34ColumnsSlice140
private theorem contact34ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact34) 144 8 = 96219965738 :=
  combineSlices (auxiliaryColumnSlice contact34) 144 4 4 58181709945 38038255793 contact34ColumnsSlice144 contact34ColumnsSlice148
private theorem contact34ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact34) 0 16 = 23427068157196 :=
  combineSlices (auxiliaryColumnSlice contact34) 0 8 8 12344458506290 11082609650906 contact34ColumnsJoin0_8 contact34ColumnsJoin8_8
private theorem contact34ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact34) 16 16 = 18653401503548 :=
  combineSlices (auxiliaryColumnSlice contact34) 16 8 8 9889197211249 8764204292299 contact34ColumnsJoin16_8 contact34ColumnsJoin24_8
private theorem contact34ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact34) 32 16 = 14427426033713 :=
  combineSlices (auxiliaryColumnSlice contact34) 32 8 8 7707741340301 6719684693412 contact34ColumnsJoin32_8 contact34ColumnsJoin40_8
private theorem contact34ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact34) 48 16 = 10749302743749 :=
  combineSlices (auxiliaryColumnSlice contact34) 48 8 8 5800172911661 4949129832088 contact34ColumnsJoin48_8 contact34ColumnsJoin56_8
private theorem contact34ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact34) 64 16 = 7619071552506 :=
  combineSlices (auxiliaryColumnSlice contact34) 64 8 8 4166551150499 3452520402007 contact34ColumnsJoin64_8 contact34ColumnsJoin72_8
private theorem contact34ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact34) 80 16 = 5036760227565 :=
  combineSlices (auxiliaryColumnSlice contact34) 80 8 8 2806908504760 2229851722805 contact34ColumnsJoin80_8 contact34ColumnsJoin88_8
private theorem contact34ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact34) 96 16 = 3002375099429 :=
  combineSlices (auxiliaryColumnSlice contact34) 96 8 8 1721248711425 1281126388004 contact34ColumnsJoin96_8 contact34ColumnsJoin104_8
private theorem contact34ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact34) 112 16 = 1515914214954 :=
  combineSlices (auxiliaryColumnSlice contact34) 112 8 8 909539392182 606374822772 contact34ColumnsJoin112_8 contact34ColumnsJoin120_8
private theorem contact34ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact34) 128 16 = 575519935896 :=
  combineSlices (auxiliaryColumnSlice contact34) 128 8 8 371715049002 203804886894 contact34ColumnsJoin128_8 contact34ColumnsJoin136_8
private theorem contact34ColumnsJoin144_12 : sliceWindow (auxiliaryColumnSlice contact34) 144 12 = 119755237315 :=
  combineSlices (auxiliaryColumnSlice contact34) 144 8 4 96219965738 23535271577 contact34ColumnsJoin144_8 contact34ColumnsSlice152
private theorem contact34ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact34) 0 32 = 42080469660744 :=
  combineSlices (auxiliaryColumnSlice contact34) 0 16 16 23427068157196 18653401503548 contact34ColumnsJoin0_16 contact34ColumnsJoin16_16
private theorem contact34ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact34) 32 32 = 25176728777462 :=
  combineSlices (auxiliaryColumnSlice contact34) 32 16 16 14427426033713 10749302743749 contact34ColumnsJoin32_16 contact34ColumnsJoin48_16
private theorem contact34ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact34) 64 32 = 12655831780071 :=
  combineSlices (auxiliaryColumnSlice contact34) 64 16 16 7619071552506 5036760227565 contact34ColumnsJoin64_16 contact34ColumnsJoin80_16
private theorem contact34ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact34) 96 32 = 4518289314383 :=
  combineSlices (auxiliaryColumnSlice contact34) 96 16 16 3002375099429 1515914214954 contact34ColumnsJoin96_16 contact34ColumnsJoin112_16
private theorem contact34ColumnsJoin128_28 : sliceWindow (auxiliaryColumnSlice contact34) 128 28 = 695275173211 :=
  combineSlices (auxiliaryColumnSlice contact34) 128 16 12 575519935896 119755237315 contact34ColumnsJoin128_16 contact34ColumnsJoin144_12
private theorem contact34ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact34) 0 64 = 67257198438206 :=
  combineSlices (auxiliaryColumnSlice contact34) 0 32 32 42080469660744 25176728777462 contact34ColumnsJoin0_32 contact34ColumnsJoin32_32
private theorem contact34ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact34) 64 64 = 17174121094454 :=
  combineSlices (auxiliaryColumnSlice contact34) 64 32 32 12655831780071 4518289314383 contact34ColumnsJoin64_32 contact34ColumnsJoin96_32
private theorem contact34ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact34) 0 128 = 84431319532660 :=
  combineSlices (auxiliaryColumnSlice contact34) 0 64 64 67257198438206 17174121094454 contact34ColumnsJoin0_64 contact34ColumnsJoin64_64
private theorem contact34ColumnsJoin0_156 : sliceWindow (auxiliaryColumnSlice contact34) 0 156 = 85126594705871 :=
  combineSlices (auxiliaryColumnSlice contact34) 0 128 28 84431319532660 695275173211 contact34ColumnsJoin0_128 contact34ColumnsJoin128_28
private theorem contact34OrdinaryRanks : ordinaryRankBound contact34 = 8746376738 := by decide +kernel
private theorem contact34RanksSlice0 : sliceWindow (auxiliaryRankSlice contact34) 0 4 = 23877784 :=
  contactRankWindow_of_rec contact34 0 4 23877784 (by decide +kernel)
private theorem contact34RanksSlice4 : sliceWindow (auxiliaryRankSlice contact34) 4 4 = 22288504 :=
  contactRankWindow_of_rec contact34 4 4 22288504 (by decide +kernel)
private theorem contact34RanksSlice8 : sliceWindow (auxiliaryRankSlice contact34) 8 4 = 20758360 :=
  contactRankWindow_of_rec contact34 8 4 20758360 (by decide +kernel)
private theorem contact34RanksSlice12 : sliceWindow (auxiliaryRankSlice contact34) 12 4 = 19287352 :=
  contactRankWindow_of_rec contact34 12 4 19287352 (by decide +kernel)
private theorem contact34RanksSlice16 : sliceWindow (auxiliaryRankSlice contact34) 16 4 = 17875480 :=
  contactRankWindow_of_rec contact34 16 4 17875480 (by decide +kernel)
private theorem contact34RanksSlice20 : sliceWindow (auxiliaryRankSlice contact34) 20 4 = 16522744 :=
  contactRankWindow_of_rec contact34 20 4 16522744 (by decide +kernel)
private theorem contact34RanksSlice24 : sliceWindow (auxiliaryRankSlice contact34) 24 4 = 15229144 :=
  contactRankWindow_of_rec contact34 24 4 15229144 (by decide +kernel)
private theorem contact34RanksSlice28 : sliceWindow (auxiliaryRankSlice contact34) 28 4 = 13994680 :=
  contactRankWindow_of_rec contact34 28 4 13994680 (by decide +kernel)
private theorem contact34RanksSlice32 : sliceWindow (auxiliaryRankSlice contact34) 32 4 = 12819352 :=
  contactRankWindow_of_rec contact34 32 4 12819352 (by decide +kernel)
private theorem contact34RanksSlice36 : sliceWindow (auxiliaryRankSlice contact34) 36 4 = 11703160 :=
  contactRankWindow_of_rec contact34 36 4 11703160 (by decide +kernel)
private theorem contact34RanksSlice40 : sliceWindow (auxiliaryRankSlice contact34) 40 4 = 10646104 :=
  contactRankWindow_of_rec contact34 40 4 10646104 (by decide +kernel)
private theorem contact34RanksSlice44 : sliceWindow (auxiliaryRankSlice contact34) 44 4 = 9648184 :=
  contactRankWindow_of_rec contact34 44 4 9648184 (by decide +kernel)
private theorem contact34RanksSlice48 : sliceWindow (auxiliaryRankSlice contact34) 48 4 = 8709372 :=
  contactRankWindow_of_rec contact34 48 4 8709372 (by decide +kernel)
private theorem contact34RanksSlice52 : sliceWindow (auxiliaryRankSlice contact34) 52 4 = 7829075 :=
  contactRankWindow_of_rec contact34 52 4 7829075 (by decide +kernel)
private theorem contact34RanksSlice56 : sliceWindow (auxiliaryRankSlice contact34) 56 4 = 7006088 :=
  contactRankWindow_of_rec contact34 56 4 7006088 (by decide +kernel)
private theorem contact34RanksSlice60 : sliceWindow (auxiliaryRankSlice contact34) 60 4 = 6239087 :=
  contactRankWindow_of_rec contact34 60 4 6239087 (by decide +kernel)
private theorem contact34RanksSlice64 : sliceWindow (auxiliaryRankSlice contact34) 64 4 = 5526426 :=
  contactRankWindow_of_rec contact34 64 4 5526426 (by decide +kernel)
private theorem contact34RanksSlice68 : sliceWindow (auxiliaryRankSlice contact34) 68 4 = 4866304 :=
  contactRankWindow_of_rec contact34 68 4 4866304 (by decide +kernel)
private theorem contact34RanksSlice72 : sliceWindow (auxiliaryRankSlice contact34) 72 4 = 4257119 :=
  contactRankWindow_of_rec contact34 72 4 4257119 (by decide +kernel)
private theorem contact34RanksSlice76 : sliceWindow (auxiliaryRankSlice contact34) 76 4 = 3697022 :=
  contactRankWindow_of_rec contact34 76 4 3697022 (by decide +kernel)
private theorem contact34RanksSlice80 : sliceWindow (auxiliaryRankSlice contact34) 80 4 = 3184216 :=
  contactRankWindow_of_rec contact34 80 4 3184216 (by decide +kernel)
private theorem contact34RanksSlice84 : sliceWindow (auxiliaryRankSlice contact34) 84 4 = 2717231 :=
  contactRankWindow_of_rec contact34 84 4 2717231 (by decide +kernel)
private theorem contact34RanksSlice88 : sliceWindow (auxiliaryRankSlice contact34) 88 4 = 2294082 :=
  contactRankWindow_of_rec contact34 88 4 2294082 (by decide +kernel)
private theorem contact34RanksSlice92 : sliceWindow (auxiliaryRankSlice contact34) 92 4 = 1912976 :=
  contactRankWindow_of_rec contact34 92 4 1912976 (by decide +kernel)
private theorem contact34RanksSlice96 : sliceWindow (auxiliaryRankSlice contact34) 96 4 = 1572575 :=
  contactRankWindow_of_rec contact34 96 4 1572575 (by decide +kernel)
private theorem contact34RanksSlice100 : sliceWindow (auxiliaryRankSlice contact34) 100 4 = 1270758 :=
  contactRankWindow_of_rec contact34 100 4 1270758 (by decide +kernel)
private theorem contact34RanksSlice104 : sliceWindow (auxiliaryRankSlice contact34) 104 4 = 1005736 :=
  contactRankWindow_of_rec contact34 104 4 1005736 (by decide +kernel)
private theorem contact34RanksSlice108 : sliceWindow (auxiliaryRankSlice contact34) 108 4 = 776303 :=
  contactRankWindow_of_rec contact34 108 4 776303 (by decide +kernel)
private theorem contact34RanksSlice112 : sliceWindow (auxiliaryRankSlice contact34) 112 4 = 580202 :=
  contactRankWindow_of_rec contact34 112 4 580202 (by decide +kernel)
private theorem contact34RanksSlice116 : sliceWindow (auxiliaryRankSlice contact34) 116 4 = 415648 :=
  contactRankWindow_of_rec contact34 116 4 415648 (by decide +kernel)
private theorem contact34RanksSlice120 : sliceWindow (auxiliaryRankSlice contact34) 120 4 = 281567 :=
  contactRankWindow_of_rec contact34 120 4 281567 (by decide +kernel)
private theorem contact34RanksSlice124 : sliceWindow (auxiliaryRankSlice contact34) 124 4 = 175566 :=
  contactRankWindow_of_rec contact34 124 4 175566 (by decide +kernel)
private theorem contact34RanksSlice128 : sliceWindow (auxiliaryRankSlice contact34) 128 4 = 95864 :=
  contactRankWindow_of_rec contact34 128 4 95864 (by decide +kernel)
private theorem contact34RanksSlice132 : sliceWindow (auxiliaryRankSlice contact34) 132 4 = 41531 :=
  contactRankWindow_of_rec contact34 132 4 41531 (by decide +kernel)
private theorem contact34RanksSlice136 : sliceWindow (auxiliaryRankSlice contact34) 136 4 = 10202 :=
  contactRankWindow_of_rec contact34 136 4 10202 (by decide +kernel)
private theorem contact34RanksSlice140 : sliceWindow (auxiliaryRankSlice contact34) 140 16 = 0 :=
  contactRankWindow_of_rec contact34 140 16 0 (by decide +kernel)
private theorem contact34RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact34) 0 8 = 46166288 :=
  combineSlices (auxiliaryRankSlice contact34) 0 4 4 23877784 22288504 contact34RanksSlice0 contact34RanksSlice4
private theorem contact34RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact34) 8 8 = 40045712 :=
  combineSlices (auxiliaryRankSlice contact34) 8 4 4 20758360 19287352 contact34RanksSlice8 contact34RanksSlice12
private theorem contact34RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact34) 16 8 = 34398224 :=
  combineSlices (auxiliaryRankSlice contact34) 16 4 4 17875480 16522744 contact34RanksSlice16 contact34RanksSlice20
private theorem contact34RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact34) 24 8 = 29223824 :=
  combineSlices (auxiliaryRankSlice contact34) 24 4 4 15229144 13994680 contact34RanksSlice24 contact34RanksSlice28
private theorem contact34RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact34) 32 8 = 24522512 :=
  combineSlices (auxiliaryRankSlice contact34) 32 4 4 12819352 11703160 contact34RanksSlice32 contact34RanksSlice36
private theorem contact34RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact34) 40 8 = 20294288 :=
  combineSlices (auxiliaryRankSlice contact34) 40 4 4 10646104 9648184 contact34RanksSlice40 contact34RanksSlice44
private theorem contact34RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact34) 48 8 = 16538447 :=
  combineSlices (auxiliaryRankSlice contact34) 48 4 4 8709372 7829075 contact34RanksSlice48 contact34RanksSlice52
private theorem contact34RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact34) 56 8 = 13245175 :=
  combineSlices (auxiliaryRankSlice contact34) 56 4 4 7006088 6239087 contact34RanksSlice56 contact34RanksSlice60
private theorem contact34RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact34) 64 8 = 10392730 :=
  combineSlices (auxiliaryRankSlice contact34) 64 4 4 5526426 4866304 contact34RanksSlice64 contact34RanksSlice68
private theorem contact34RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact34) 72 8 = 7954141 :=
  combineSlices (auxiliaryRankSlice contact34) 72 4 4 4257119 3697022 contact34RanksSlice72 contact34RanksSlice76
private theorem contact34RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact34) 80 8 = 5901447 :=
  combineSlices (auxiliaryRankSlice contact34) 80 4 4 3184216 2717231 contact34RanksSlice80 contact34RanksSlice84
private theorem contact34RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact34) 88 8 = 4207058 :=
  combineSlices (auxiliaryRankSlice contact34) 88 4 4 2294082 1912976 contact34RanksSlice88 contact34RanksSlice92
private theorem contact34RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact34) 96 8 = 2843333 :=
  combineSlices (auxiliaryRankSlice contact34) 96 4 4 1572575 1270758 contact34RanksSlice96 contact34RanksSlice100
private theorem contact34RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact34) 104 8 = 1782039 :=
  combineSlices (auxiliaryRankSlice contact34) 104 4 4 1005736 776303 contact34RanksSlice104 contact34RanksSlice108
private theorem contact34RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact34) 112 8 = 995850 :=
  combineSlices (auxiliaryRankSlice contact34) 112 4 4 580202 415648 contact34RanksSlice112 contact34RanksSlice116
private theorem contact34RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact34) 120 8 = 457133 :=
  combineSlices (auxiliaryRankSlice contact34) 120 4 4 281567 175566 contact34RanksSlice120 contact34RanksSlice124
private theorem contact34RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact34) 128 8 = 137395 :=
  combineSlices (auxiliaryRankSlice contact34) 128 4 4 95864 41531 contact34RanksSlice128 contact34RanksSlice132
private theorem contact34RanksJoin136_20 : sliceWindow (auxiliaryRankSlice contact34) 136 20 = 10202 :=
  combineSlices (auxiliaryRankSlice contact34) 136 4 16 10202 0 contact34RanksSlice136 contact34RanksSlice140
private theorem contact34RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact34) 0 16 = 86212000 :=
  combineSlices (auxiliaryRankSlice contact34) 0 8 8 46166288 40045712 contact34RanksJoin0_8 contact34RanksJoin8_8
private theorem contact34RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact34) 16 16 = 63622048 :=
  combineSlices (auxiliaryRankSlice contact34) 16 8 8 34398224 29223824 contact34RanksJoin16_8 contact34RanksJoin24_8
private theorem contact34RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact34) 32 16 = 44816800 :=
  combineSlices (auxiliaryRankSlice contact34) 32 8 8 24522512 20294288 contact34RanksJoin32_8 contact34RanksJoin40_8
private theorem contact34RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact34) 48 16 = 29783622 :=
  combineSlices (auxiliaryRankSlice contact34) 48 8 8 16538447 13245175 contact34RanksJoin48_8 contact34RanksJoin56_8
private theorem contact34RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact34) 64 16 = 18346871 :=
  combineSlices (auxiliaryRankSlice contact34) 64 8 8 10392730 7954141 contact34RanksJoin64_8 contact34RanksJoin72_8
private theorem contact34RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact34) 80 16 = 10108505 :=
  combineSlices (auxiliaryRankSlice contact34) 80 8 8 5901447 4207058 contact34RanksJoin80_8 contact34RanksJoin88_8
private theorem contact34RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact34) 96 16 = 4625372 :=
  combineSlices (auxiliaryRankSlice contact34) 96 8 8 2843333 1782039 contact34RanksJoin96_8 contact34RanksJoin104_8
private theorem contact34RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact34) 112 16 = 1452983 :=
  combineSlices (auxiliaryRankSlice contact34) 112 8 8 995850 457133 contact34RanksJoin112_8 contact34RanksJoin120_8
private theorem contact34RanksJoin128_28 : sliceWindow (auxiliaryRankSlice contact34) 128 28 = 147597 :=
  combineSlices (auxiliaryRankSlice contact34) 128 8 20 137395 10202 contact34RanksJoin128_8 contact34RanksJoin136_20
private theorem contact34RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact34) 0 32 = 149834048 :=
  combineSlices (auxiliaryRankSlice contact34) 0 16 16 86212000 63622048 contact34RanksJoin0_16 contact34RanksJoin16_16
private theorem contact34RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact34) 32 32 = 74600422 :=
  combineSlices (auxiliaryRankSlice contact34) 32 16 16 44816800 29783622 contact34RanksJoin32_16 contact34RanksJoin48_16
private theorem contact34RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact34) 64 32 = 28455376 :=
  combineSlices (auxiliaryRankSlice contact34) 64 16 16 18346871 10108505 contact34RanksJoin64_16 contact34RanksJoin80_16
private theorem contact34RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact34) 96 32 = 6078355 :=
  combineSlices (auxiliaryRankSlice contact34) 96 16 16 4625372 1452983 contact34RanksJoin96_16 contact34RanksJoin112_16
private theorem contact34RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact34) 0 64 = 224434470 :=
  combineSlices (auxiliaryRankSlice contact34) 0 32 32 149834048 74600422 contact34RanksJoin0_32 contact34RanksJoin32_32
private theorem contact34RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact34) 64 64 = 34533731 :=
  combineSlices (auxiliaryRankSlice contact34) 64 32 32 28455376 6078355 contact34RanksJoin64_32 contact34RanksJoin96_32
private theorem contact34RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact34) 0 128 = 258968201 :=
  combineSlices (auxiliaryRankSlice contact34) 0 64 64 224434470 34533731 contact34RanksJoin0_64 contact34RanksJoin64_64
private theorem contact34RanksJoin0_156 : sliceWindow (auxiliaryRankSlice contact34) 0 156 = 259115798 :=
  combineSlices (auxiliaryRankSlice contact34) 0 128 28 258968201 147597 contact34RanksJoin0_128 contact34RanksJoin128_28
theorem contact34_margin : sourceMargin contact34 :=
  margin_of_checked_counts contact34 156 2275610325632433 85126594705871 8746376738 259115798 rfl contact34OrdinaryColumns contact34ColumnsJoin0_156 contact34OrdinaryRanks contact34RanksJoin0_156 (by decide +kernel)

private theorem contact36OrdinaryColumns : ordinaryColumnCount contact36 = 8916935253773229 := by decide +kernel
private theorem contact36ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact36) 0 4 = 27017039880140 :=
  contactColumnsWindow_fast contact36 0 4 27017039880140 (by decide +kernel)
private theorem contact36ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact36) 4 4 = 26041551260460 :=
  contactColumnsWindow_fast contact36 4 4 26041551260460 (by decide +kernel)
private theorem contact36ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact36) 8 4 = 25084087629580 :=
  contactColumnsWindow_fast contact36 8 4 25084087629580 (by decide +kernel)
private theorem contact36ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact36) 12 4 = 24144648987500 :=
  contactColumnsWindow_fast contact36 12 4 24144648987500 (by decide +kernel)
private theorem contact36ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact36) 16 4 = 23223235334220 :=
  contactColumnsWindow_fast contact36 16 4 23223235334220 (by decide +kernel)
private theorem contact36ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact36) 20 4 = 22319846669740 :=
  contactColumnsWindow_fast contact36 20 4 22319846669740 (by decide +kernel)
private theorem contact36ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact36) 24 4 = 21434482994060 :=
  contactColumnsWindow_fast contact36 24 4 21434482994060 (by decide +kernel)
private theorem contact36ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact36) 28 4 = 20567144307180 :=
  contactColumnsWindow_fast contact36 28 4 20567144307180 (by decide +kernel)
private theorem contact36ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact36) 32 4 = 19717830609100 :=
  contactColumnsWindow_fast contact36 32 4 19717830609100 (by decide +kernel)
private theorem contact36ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact36) 36 4 = 18886541899820 :=
  contactColumnsWindow_fast contact36 36 4 18886541899820 (by decide +kernel)
private theorem contact36ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact36) 40 4 = 18073336154920 :=
  contactColumnsWindow_fast contact36 40 4 18073336154920 (by decide +kernel)
private theorem contact36ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact36) 44 4 = 17278228885640 :=
  contactColumnsWindow_fast contact36 44 4 17278228885640 (by decide +kernel)
private theorem contact36ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact36) 48 4 = 16501151025240 :=
  contactColumnsWindow_fast contact36 48 4 16501151025240 (by decide +kernel)
private theorem contact36ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact36) 52 4 = 15742101591757 :=
  contactColumnsWindow_fast contact36 52 4 15742101591757 (by decide +kernel)
private theorem contact36ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact36) 56 4 = 15001082415948 :=
  contactColumnsWindow_fast contact36 56 4 15001082415948 (by decide +kernel)
private theorem contact36ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact36) 60 4 = 14278161561874 :=
  contactColumnsWindow_fast contact36 60 4 14278161561874 (by decide +kernel)
private theorem contact36ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact36) 64 4 = 13573332776780 :=
  contactColumnsWindow_fast contact36 64 4 13573332776780 (by decide +kernel)
private theorem contact36ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact36) 68 4 = 12886536624558 :=
  contactColumnsWindow_fast contact36 68 4 12886536624558 (by decide +kernel)
private theorem contact36ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact36) 72 4 = 12217774695235 :=
  contactColumnsWindow_fast contact36 72 4 12217774695235 (by decide +kernel)
private theorem contact36ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact36) 76 4 = 11567046248619 :=
  contactColumnsWindow_fast contact36 76 4 11567046248619 (by decide +kernel)
private theorem contact36ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact36) 80 4 = 10934434383304 :=
  contactColumnsWindow_fast contact36 80 4 10934434383304 (by decide +kernel)
private theorem contact36ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact36) 84 4 = 10319905650115 :=
  contactColumnsWindow_fast contact36 84 4 10319905650115 (by decide +kernel)
private theorem contact36ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact36) 88 4 = 9723415926186 :=
  contactColumnsWindow_fast contact36 88 4 9723415926186 (by decide +kernel)
private theorem contact36ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact36) 92 4 = 9144963754248 :=
  contactColumnsWindow_fast contact36 92 4 9144963754248 (by decide +kernel)
private theorem contact36ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact36) 96 4 = 8584554260473 :=
  contactColumnsWindow_fast contact36 96 4 8584554260473 (by decide +kernel)
private theorem contact36ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact36) 100 4 = 8042271760300 :=
  contactColumnsWindow_fast contact36 100 4 8042271760300 (by decide +kernel)
private theorem contact36ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact36) 104 4 = 7518068201233 :=
  contactColumnsWindow_fast contact36 104 4 7518068201233 (by decide +kernel)
private theorem contact36ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact36) 108 4 = 7011909629577 :=
  contactColumnsWindow_fast contact36 108 4 7011909629577 (by decide +kernel)
private theorem contact36ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact36) 112 4 = 6523792351590 :=
  contactColumnsWindow_fast contact36 112 4 6523792351590 (by decide +kernel)
private theorem contact36ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact36) 116 4 = 6053720315995 :=
  contactColumnsWindow_fast contact36 116 4 6053720315995 (by decide +kernel)
private theorem contact36ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact36) 120 4 = 5601781964707 :=
  contactColumnsWindow_fast contact36 120 4 5601781964707 (by decide +kernel)
private theorem contact36ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact36) 124 4 = 5167913443964 :=
  contactColumnsWindow_fast contact36 124 4 5167913443964 (by decide +kernel)
private theorem contact36ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact36) 128 4 = 4752089978079 :=
  contactColumnsWindow_fast contact36 128 4 4752089978079 (by decide +kernel)
private theorem contact36ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact36) 132 4 = 4354307481390 :=
  contactColumnsWindow_fast contact36 132 4 4354307481390 (by decide +kernel)
private theorem contact36ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact36) 136 4 = 3974574379741 :=
  contactColumnsWindow_fast contact36 136 4 3974574379741 (by decide +kernel)
private theorem contact36ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact36) 140 4 = 3612978885694 :=
  contactColumnsWindow_fast contact36 140 4 3612978885694 (by decide +kernel)
private theorem contact36ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact36) 144 4 = 3269445335048 :=
  contactColumnsWindow_fast contact36 144 4 3269445335048 (by decide +kernel)
private theorem contact36ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact36) 148 4 = 2943956922711 :=
  contactColumnsWindow_fast contact36 148 4 2943956922711 (by decide +kernel)
private theorem contact36ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact36) 152 4 = 2636509247317 :=
  contactColumnsWindow_fast contact36 152 4 2636509247317 (by decide +kernel)
private theorem contact36ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact36) 156 4 = 2347117018147 :=
  contactColumnsWindow_fast contact36 156 4 2347117018147 (by decide +kernel)
private theorem contact36ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact36) 160 4 = 2075862334534 :=
  contactColumnsWindow_fast contact36 160 4 2075862334534 (by decide +kernel)
private theorem contact36ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact36) 164 4 = 1822663896308 :=
  contactColumnsWindow_fast contact36 164 4 1822663896308 (by decide +kernel)
private theorem contact36ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact36) 168 4 = 1587510685146 :=
  contactColumnsWindow_fast contact36 168 4 1587510685146 (by decide +kernel)
private theorem contact36ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact36) 172 4 = 1370397616663 :=
  contactColumnsWindow_fast contact36 172 4 1370397616663 (by decide +kernel)
private theorem contact36ColumnsSlice176 : sliceWindow (auxiliaryColumnSlice contact36) 176 4 = 1171346202920 :=
  contactColumnsWindow_fast contact36 176 4 1171346202920 (by decide +kernel)
private theorem contact36ColumnsSlice180 : sliceWindow (auxiliaryColumnSlice contact36) 180 4 = 990431640670 :=
  contactColumnsWindow_fast contact36 180 4 990431640670 (by decide +kernel)
private theorem contact36ColumnsSlice184 : sliceWindow (auxiliaryColumnSlice contact36) 184 4 = 827520558717 :=
  contactColumnsWindow_fast contact36 184 4 827520558717 (by decide +kernel)
private theorem contact36ColumnsSlice188 : sliceWindow (auxiliaryColumnSlice contact36) 188 4 = 682376116894 :=
  contactColumnsWindow_fast contact36 188 4 682376116894 (by decide +kernel)
private theorem contact36ColumnsSlice192 : sliceWindow (auxiliaryColumnSlice contact36) 192 4 = 554550971938 :=
  contactColumnsWindow_fast contact36 192 4 554550971938 (by decide +kernel)
private theorem contact36ColumnsSlice196 : sliceWindow (auxiliaryColumnSlice contact36) 196 4 = 443463647946 :=
  contactColumnsWindow_fast contact36 196 4 443463647946 (by decide +kernel)
private theorem contact36ColumnsSlice200 : sliceWindow (auxiliaryColumnSlice contact36) 200 4 = 348393981936 :=
  contactColumnsWindow_fast contact36 200 4 348393981936 (by decide +kernel)
private theorem contact36ColumnsSlice204 : sliceWindow (auxiliaryColumnSlice contact36) 204 4 = 268319517320 :=
  contactColumnsWindow_fast contact36 204 4 268319517320 (by decide +kernel)
private theorem contact36ColumnsSlice208 : sliceWindow (auxiliaryColumnSlice contact36) 208 4 = 202137818992 :=
  contactColumnsWindow_fast contact36 208 4 202137818992 (by decide +kernel)
private theorem contact36ColumnsSlice212 : sliceWindow (auxiliaryColumnSlice contact36) 212 4 = 148583436837 :=
  contactColumnsWindow_fast contact36 212 4 148583436837 (by decide +kernel)
private theorem contact36ColumnsSlice216 : sliceWindow (auxiliaryColumnSlice contact36) 216 2 = 57773815492 :=
  contactColumnsWindow_fast contact36 216 2 57773815492 (by decide +kernel)
private theorem contact36ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact36) 0 8 = 53058591140600 :=
  combineSlices (auxiliaryColumnSlice contact36) 0 4 4 27017039880140 26041551260460 contact36ColumnsSlice0 contact36ColumnsSlice4
private theorem contact36ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact36) 8 8 = 49228736617080 :=
  combineSlices (auxiliaryColumnSlice contact36) 8 4 4 25084087629580 24144648987500 contact36ColumnsSlice8 contact36ColumnsSlice12
private theorem contact36ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact36) 16 8 = 45543082003960 :=
  combineSlices (auxiliaryColumnSlice contact36) 16 4 4 23223235334220 22319846669740 contact36ColumnsSlice16 contact36ColumnsSlice20
private theorem contact36ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact36) 24 8 = 42001627301240 :=
  combineSlices (auxiliaryColumnSlice contact36) 24 4 4 21434482994060 20567144307180 contact36ColumnsSlice24 contact36ColumnsSlice28
private theorem contact36ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact36) 32 8 = 38604372508920 :=
  combineSlices (auxiliaryColumnSlice contact36) 32 4 4 19717830609100 18886541899820 contact36ColumnsSlice32 contact36ColumnsSlice36
private theorem contact36ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact36) 40 8 = 35351565040560 :=
  combineSlices (auxiliaryColumnSlice contact36) 40 4 4 18073336154920 17278228885640 contact36ColumnsSlice40 contact36ColumnsSlice44
private theorem contact36ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact36) 48 8 = 32243252616997 :=
  combineSlices (auxiliaryColumnSlice contact36) 48 4 4 16501151025240 15742101591757 contact36ColumnsSlice48 contact36ColumnsSlice52
private theorem contact36ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact36) 56 8 = 29279243977822 :=
  combineSlices (auxiliaryColumnSlice contact36) 56 4 4 15001082415948 14278161561874 contact36ColumnsSlice56 contact36ColumnsSlice60
private theorem contact36ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact36) 64 8 = 26459869401338 :=
  combineSlices (auxiliaryColumnSlice contact36) 64 4 4 13573332776780 12886536624558 contact36ColumnsSlice64 contact36ColumnsSlice68
private theorem contact36ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact36) 72 8 = 23784820943854 :=
  combineSlices (auxiliaryColumnSlice contact36) 72 4 4 12217774695235 11567046248619 contact36ColumnsSlice72 contact36ColumnsSlice76
private theorem contact36ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact36) 80 8 = 21254340033419 :=
  combineSlices (auxiliaryColumnSlice contact36) 80 4 4 10934434383304 10319905650115 contact36ColumnsSlice80 contact36ColumnsSlice84
private theorem contact36ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact36) 88 8 = 18868379680434 :=
  combineSlices (auxiliaryColumnSlice contact36) 88 4 4 9723415926186 9144963754248 contact36ColumnsSlice88 contact36ColumnsSlice92
private theorem contact36ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact36) 96 8 = 16626826020773 :=
  combineSlices (auxiliaryColumnSlice contact36) 96 4 4 8584554260473 8042271760300 contact36ColumnsSlice96 contact36ColumnsSlice100
private theorem contact36ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact36) 104 8 = 14529977830810 :=
  combineSlices (auxiliaryColumnSlice contact36) 104 4 4 7518068201233 7011909629577 contact36ColumnsSlice104 contact36ColumnsSlice108
private theorem contact36ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact36) 112 8 = 12577512667585 :=
  combineSlices (auxiliaryColumnSlice contact36) 112 4 4 6523792351590 6053720315995 contact36ColumnsSlice112 contact36ColumnsSlice116
private theorem contact36ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact36) 120 8 = 10769695408671 :=
  combineSlices (auxiliaryColumnSlice contact36) 120 4 4 5601781964707 5167913443964 contact36ColumnsSlice120 contact36ColumnsSlice124
private theorem contact36ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact36) 128 8 = 9106397459469 :=
  combineSlices (auxiliaryColumnSlice contact36) 128 4 4 4752089978079 4354307481390 contact36ColumnsSlice128 contact36ColumnsSlice132
private theorem contact36ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact36) 136 8 = 7587553265435 :=
  combineSlices (auxiliaryColumnSlice contact36) 136 4 4 3974574379741 3612978885694 contact36ColumnsSlice136 contact36ColumnsSlice140
private theorem contact36ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact36) 144 8 = 6213402257759 :=
  combineSlices (auxiliaryColumnSlice contact36) 144 4 4 3269445335048 2943956922711 contact36ColumnsSlice144 contact36ColumnsSlice148
private theorem contact36ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact36) 152 8 = 4983626265464 :=
  combineSlices (auxiliaryColumnSlice contact36) 152 4 4 2636509247317 2347117018147 contact36ColumnsSlice152 contact36ColumnsSlice156
private theorem contact36ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact36) 160 8 = 3898526230842 :=
  combineSlices (auxiliaryColumnSlice contact36) 160 4 4 2075862334534 1822663896308 contact36ColumnsSlice160 contact36ColumnsSlice164
private theorem contact36ColumnsJoin168_8 : sliceWindow (auxiliaryColumnSlice contact36) 168 8 = 2957908301809 :=
  combineSlices (auxiliaryColumnSlice contact36) 168 4 4 1587510685146 1370397616663 contact36ColumnsSlice168 contact36ColumnsSlice172
private theorem contact36ColumnsJoin176_8 : sliceWindow (auxiliaryColumnSlice contact36) 176 8 = 2161777843590 :=
  combineSlices (auxiliaryColumnSlice contact36) 176 4 4 1171346202920 990431640670 contact36ColumnsSlice176 contact36ColumnsSlice180
private theorem contact36ColumnsJoin184_8 : sliceWindow (auxiliaryColumnSlice contact36) 184 8 = 1509896675611 :=
  combineSlices (auxiliaryColumnSlice contact36) 184 4 4 827520558717 682376116894 contact36ColumnsSlice184 contact36ColumnsSlice188
private theorem contact36ColumnsJoin192_8 : sliceWindow (auxiliaryColumnSlice contact36) 192 8 = 998014619884 :=
  combineSlices (auxiliaryColumnSlice contact36) 192 4 4 554550971938 443463647946 contact36ColumnsSlice192 contact36ColumnsSlice196
private theorem contact36ColumnsJoin200_8 : sliceWindow (auxiliaryColumnSlice contact36) 200 8 = 616713499256 :=
  combineSlices (auxiliaryColumnSlice contact36) 200 4 4 348393981936 268319517320 contact36ColumnsSlice200 contact36ColumnsSlice204
private theorem contact36ColumnsJoin208_8 : sliceWindow (auxiliaryColumnSlice contact36) 208 8 = 350721255829 :=
  combineSlices (auxiliaryColumnSlice contact36) 208 4 4 202137818992 148583436837 contact36ColumnsSlice208 contact36ColumnsSlice212
private theorem contact36ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact36) 0 16 = 102287327757680 :=
  combineSlices (auxiliaryColumnSlice contact36) 0 8 8 53058591140600 49228736617080 contact36ColumnsJoin0_8 contact36ColumnsJoin8_8
private theorem contact36ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact36) 16 16 = 87544709305200 :=
  combineSlices (auxiliaryColumnSlice contact36) 16 8 8 45543082003960 42001627301240 contact36ColumnsJoin16_8 contact36ColumnsJoin24_8
private theorem contact36ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact36) 32 16 = 73955937549480 :=
  combineSlices (auxiliaryColumnSlice contact36) 32 8 8 38604372508920 35351565040560 contact36ColumnsJoin32_8 contact36ColumnsJoin40_8
private theorem contact36ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact36) 48 16 = 61522496594819 :=
  combineSlices (auxiliaryColumnSlice contact36) 48 8 8 32243252616997 29279243977822 contact36ColumnsJoin48_8 contact36ColumnsJoin56_8
private theorem contact36ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact36) 64 16 = 50244690345192 :=
  combineSlices (auxiliaryColumnSlice contact36) 64 8 8 26459869401338 23784820943854 contact36ColumnsJoin64_8 contact36ColumnsJoin72_8
private theorem contact36ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact36) 80 16 = 40122719713853 :=
  combineSlices (auxiliaryColumnSlice contact36) 80 8 8 21254340033419 18868379680434 contact36ColumnsJoin80_8 contact36ColumnsJoin88_8
private theorem contact36ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact36) 96 16 = 31156803851583 :=
  combineSlices (auxiliaryColumnSlice contact36) 96 8 8 16626826020773 14529977830810 contact36ColumnsJoin96_8 contact36ColumnsJoin104_8
private theorem contact36ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact36) 112 16 = 23347208076256 :=
  combineSlices (auxiliaryColumnSlice contact36) 112 8 8 12577512667585 10769695408671 contact36ColumnsJoin112_8 contact36ColumnsJoin120_8
private theorem contact36ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact36) 128 16 = 16693950724904 :=
  combineSlices (auxiliaryColumnSlice contact36) 128 8 8 9106397459469 7587553265435 contact36ColumnsJoin128_8 contact36ColumnsJoin136_8
private theorem contact36ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact36) 144 16 = 11197028523223 :=
  combineSlices (auxiliaryColumnSlice contact36) 144 8 8 6213402257759 4983626265464 contact36ColumnsJoin144_8 contact36ColumnsJoin152_8
private theorem contact36ColumnsJoin160_16 : sliceWindow (auxiliaryColumnSlice contact36) 160 16 = 6856434532651 :=
  combineSlices (auxiliaryColumnSlice contact36) 160 8 8 3898526230842 2957908301809 contact36ColumnsJoin160_8 contact36ColumnsJoin168_8
private theorem contact36ColumnsJoin176_16 : sliceWindow (auxiliaryColumnSlice contact36) 176 16 = 3671674519201 :=
  combineSlices (auxiliaryColumnSlice contact36) 176 8 8 2161777843590 1509896675611 contact36ColumnsJoin176_8 contact36ColumnsJoin184_8
private theorem contact36ColumnsJoin192_16 : sliceWindow (auxiliaryColumnSlice contact36) 192 16 = 1614728119140 :=
  combineSlices (auxiliaryColumnSlice contact36) 192 8 8 998014619884 616713499256 contact36ColumnsJoin192_8 contact36ColumnsJoin200_8
private theorem contact36ColumnsJoin208_10 : sliceWindow (auxiliaryColumnSlice contact36) 208 10 = 408495071321 :=
  combineSlices (auxiliaryColumnSlice contact36) 208 8 2 350721255829 57773815492 contact36ColumnsJoin208_8 contact36ColumnsSlice216
private theorem contact36ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact36) 0 32 = 189832037062880 :=
  combineSlices (auxiliaryColumnSlice contact36) 0 16 16 102287327757680 87544709305200 contact36ColumnsJoin0_16 contact36ColumnsJoin16_16
private theorem contact36ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact36) 32 32 = 135478434144299 :=
  combineSlices (auxiliaryColumnSlice contact36) 32 16 16 73955937549480 61522496594819 contact36ColumnsJoin32_16 contact36ColumnsJoin48_16
private theorem contact36ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact36) 64 32 = 90367410059045 :=
  combineSlices (auxiliaryColumnSlice contact36) 64 16 16 50244690345192 40122719713853 contact36ColumnsJoin64_16 contact36ColumnsJoin80_16
private theorem contact36ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact36) 96 32 = 54504011927839 :=
  combineSlices (auxiliaryColumnSlice contact36) 96 16 16 31156803851583 23347208076256 contact36ColumnsJoin96_16 contact36ColumnsJoin112_16
private theorem contact36ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact36) 128 32 = 27890979248127 :=
  combineSlices (auxiliaryColumnSlice contact36) 128 16 16 16693950724904 11197028523223 contact36ColumnsJoin128_16 contact36ColumnsJoin144_16
private theorem contact36ColumnsJoin160_32 : sliceWindow (auxiliaryColumnSlice contact36) 160 32 = 10528109051852 :=
  combineSlices (auxiliaryColumnSlice contact36) 160 16 16 6856434532651 3671674519201 contact36ColumnsJoin160_16 contact36ColumnsJoin176_16
private theorem contact36ColumnsJoin192_26 : sliceWindow (auxiliaryColumnSlice contact36) 192 26 = 2023223190461 :=
  combineSlices (auxiliaryColumnSlice contact36) 192 16 10 1614728119140 408495071321 contact36ColumnsJoin192_16 contact36ColumnsJoin208_10
private theorem contact36ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact36) 0 64 = 325310471207179 :=
  combineSlices (auxiliaryColumnSlice contact36) 0 32 32 189832037062880 135478434144299 contact36ColumnsJoin0_32 contact36ColumnsJoin32_32
private theorem contact36ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact36) 64 64 = 144871421986884 :=
  combineSlices (auxiliaryColumnSlice contact36) 64 32 32 90367410059045 54504011927839 contact36ColumnsJoin64_32 contact36ColumnsJoin96_32
private theorem contact36ColumnsJoin128_64 : sliceWindow (auxiliaryColumnSlice contact36) 128 64 = 38419088299979 :=
  combineSlices (auxiliaryColumnSlice contact36) 128 32 32 27890979248127 10528109051852 contact36ColumnsJoin128_32 contact36ColumnsJoin160_32
private theorem contact36ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact36) 0 128 = 470181893194063 :=
  combineSlices (auxiliaryColumnSlice contact36) 0 64 64 325310471207179 144871421986884 contact36ColumnsJoin0_64 contact36ColumnsJoin64_64
private theorem contact36ColumnsJoin128_90 : sliceWindow (auxiliaryColumnSlice contact36) 128 90 = 40442311490440 :=
  combineSlices (auxiliaryColumnSlice contact36) 128 64 26 38419088299979 2023223190461 contact36ColumnsJoin128_64 contact36ColumnsJoin192_26
private theorem contact36ColumnsJoin0_218 : sliceWindow (auxiliaryColumnSlice contact36) 0 218 = 510624204684503 :=
  combineSlices (auxiliaryColumnSlice contact36) 0 128 90 470181893194063 40442311490440 contact36ColumnsJoin0_128 contact36ColumnsJoin128_90
private theorem contact36OrdinaryRanks : ordinaryRankBound contact36 = 34404168056 := by decide +kernel
private theorem contact36RanksSlice0 : sliceWindow (auxiliaryRankSlice contact36) 0 4 = 102038010 :=
  contactRankWindow_of_rec contact36 0 4 102038010 (by decide +kernel)
private theorem contact36RanksSlice4 : sliceWindow (auxiliaryRankSlice contact36) 4 4 = 97248810 :=
  contactRankWindow_of_rec contact36 4 4 97248810 (by decide +kernel)
private theorem contact36RanksSlice8 : sliceWindow (auxiliaryRankSlice contact36) 8 4 = 92584410 :=
  contactRankWindow_of_rec contact36 8 4 92584410 (by decide +kernel)
private theorem contact36RanksSlice12 : sliceWindow (auxiliaryRankSlice contact36) 12 4 = 88044810 :=
  contactRankWindow_of_rec contact36 12 4 88044810 (by decide +kernel)
private theorem contact36RanksSlice16 : sliceWindow (auxiliaryRankSlice contact36) 16 4 = 83630010 :=
  contactRankWindow_of_rec contact36 16 4 83630010 (by decide +kernel)
private theorem contact36RanksSlice20 : sliceWindow (auxiliaryRankSlice contact36) 20 4 = 79340010 :=
  contactRankWindow_of_rec contact36 20 4 79340010 (by decide +kernel)
private theorem contact36RanksSlice24 : sliceWindow (auxiliaryRankSlice contact36) 24 4 = 75174810 :=
  contactRankWindow_of_rec contact36 24 4 75174810 (by decide +kernel)
private theorem contact36RanksSlice28 : sliceWindow (auxiliaryRankSlice contact36) 28 4 = 71134410 :=
  contactRankWindow_of_rec contact36 28 4 71134410 (by decide +kernel)
private theorem contact36RanksSlice32 : sliceWindow (auxiliaryRankSlice contact36) 32 4 = 67218810 :=
  contactRankWindow_of_rec contact36 32 4 67218810 (by decide +kernel)
private theorem contact36RanksSlice36 : sliceWindow (auxiliaryRankSlice contact36) 36 4 = 63428010 :=
  contactRankWindow_of_rec contact36 36 4 63428010 (by decide +kernel)
private theorem contact36RanksSlice40 : sliceWindow (auxiliaryRankSlice contact36) 40 4 = 59762010 :=
  contactRankWindow_of_rec contact36 40 4 59762010 (by decide +kernel)
private theorem contact36RanksSlice44 : sliceWindow (auxiliaryRankSlice contact36) 44 4 = 56220810 :=
  contactRankWindow_of_rec contact36 44 4 56220810 (by decide +kernel)
private theorem contact36RanksSlice48 : sliceWindow (auxiliaryRankSlice contact36) 48 4 = 52804410 :=
  contactRankWindow_of_rec contact36 48 4 52804410 (by decide +kernel)
private theorem contact36RanksSlice52 : sliceWindow (auxiliaryRankSlice contact36) 52 4 = 49512810 :=
  contactRankWindow_of_rec contact36 52 4 49512810 (by decide +kernel)
private theorem contact36RanksSlice56 : sliceWindow (auxiliaryRankSlice contact36) 56 4 = 46346010 :=
  contactRankWindow_of_rec contact36 56 4 46346010 (by decide +kernel)
private theorem contact36RanksSlice60 : sliceWindow (auxiliaryRankSlice contact36) 60 4 = 43304010 :=
  contactRankWindow_of_rec contact36 60 4 43304010 (by decide +kernel)
private theorem contact36RanksSlice64 : sliceWindow (auxiliaryRankSlice contact36) 64 4 = 40386693 :=
  contactRankWindow_of_rec contact36 64 4 40386693 (by decide +kernel)
private theorem contact36RanksSlice68 : sliceWindow (auxiliaryRankSlice contact36) 68 4 = 37592918 :=
  contactRankWindow_of_rec contact36 68 4 37592918 (by decide +kernel)
private theorem contact36RanksSlice72 : sliceWindow (auxiliaryRankSlice contact36) 72 4 = 34920974 :=
  contactRankWindow_of_rec contact36 72 4 34920974 (by decide +kernel)
private theorem contact36RanksSlice76 : sliceWindow (auxiliaryRankSlice contact36) 76 4 = 32369157 :=
  contactRankWindow_of_rec contact36 76 4 32369157 (by decide +kernel)
private theorem contact36RanksSlice80 : sliceWindow (auxiliaryRankSlice contact36) 80 4 = 29935698 :=
  contactRankWindow_of_rec contact36 80 4 29935698 (by decide +kernel)
private theorem contact36RanksSlice84 : sliceWindow (auxiliaryRankSlice contact36) 84 4 = 27618802 :=
  contactRankWindow_of_rec contact36 84 4 27618802 (by decide +kernel)
private theorem contact36RanksSlice88 : sliceWindow (auxiliaryRankSlice contact36) 88 4 = 25416479 :=
  contactRankWindow_of_rec contact36 88 4 25416479 (by decide +kernel)
private theorem contact36RanksSlice92 : sliceWindow (auxiliaryRankSlice contact36) 92 4 = 23326148 :=
  contactRankWindow_of_rec contact36 92 4 23326148 (by decide +kernel)
private theorem contact36RanksSlice96 : sliceWindow (auxiliaryRankSlice contact36) 96 4 = 21345430 :=
  contactRankWindow_of_rec contact36 96 4 21345430 (by decide +kernel)
private theorem contact36RanksSlice100 : sliceWindow (auxiliaryRankSlice contact36) 100 4 = 19471671 :=
  contactRankWindow_of_rec contact36 100 4 19471671 (by decide +kernel)
private theorem contact36RanksSlice104 : sliceWindow (auxiliaryRankSlice contact36) 104 4 = 17702244 :=
  contactRankWindow_of_rec contact36 104 4 17702244 (by decide +kernel)
private theorem contact36RanksSlice108 : sliceWindow (auxiliaryRankSlice contact36) 108 4 = 16034970 :=
  contactRankWindow_of_rec contact36 108 4 16034970 (by decide +kernel)
private theorem contact36RanksSlice112 : sliceWindow (auxiliaryRankSlice contact36) 112 4 = 14466991 :=
  contactRankWindow_of_rec contact36 112 4 14466991 (by decide +kernel)
private theorem contact36RanksSlice116 : sliceWindow (auxiliaryRankSlice contact36) 116 4 = 12995684 :=
  contactRankWindow_of_rec contact36 116 4 12995684 (by decide +kernel)
private theorem contact36RanksSlice120 : sliceWindow (auxiliaryRankSlice contact36) 120 4 = 11619070 :=
  contactRankWindow_of_rec contact36 120 4 11619070 (by decide +kernel)
private theorem contact36RanksSlice124 : sliceWindow (auxiliaryRankSlice contact36) 124 4 = 10334087 :=
  contactRankWindow_of_rec contact36 124 4 10334087 (by decide +kernel)
private theorem contact36RanksSlice128 : sliceWindow (auxiliaryRankSlice contact36) 128 4 = 9138116 :=
  contactRankWindow_of_rec contact36 128 4 9138116 (by decide +kernel)
private theorem contact36RanksSlice132 : sliceWindow (auxiliaryRankSlice contact36) 132 4 = 8029378 :=
  contactRankWindow_of_rec contact36 132 4 8029378 (by decide +kernel)
private theorem contact36RanksSlice136 : sliceWindow (auxiliaryRankSlice contact36) 136 4 = 7004607 :=
  contactRankWindow_of_rec contact36 136 4 7004607 (by decide +kernel)
private theorem contact36RanksSlice140 : sliceWindow (auxiliaryRankSlice contact36) 140 4 = 6061188 :=
  contactRankWindow_of_rec contact36 140 4 6061188 (by decide +kernel)
private theorem contact36RanksSlice144 : sliceWindow (auxiliaryRankSlice contact36) 144 4 = 5197542 :=
  contactRankWindow_of_rec contact36 144 4 5197542 (by decide +kernel)
private theorem contact36RanksSlice148 : sliceWindow (auxiliaryRankSlice contact36) 148 4 = 4410199 :=
  contactRankWindow_of_rec contact36 148 4 4410199 (by decide +kernel)
private theorem contact36RanksSlice152 : sliceWindow (auxiliaryRankSlice contact36) 152 4 = 3696548 :=
  contactRankWindow_of_rec contact36 152 4 3696548 (by decide +kernel)
private theorem contact36RanksSlice156 : sliceWindow (auxiliaryRankSlice contact36) 156 4 = 3055210 :=
  contactRankWindow_of_rec contact36 156 4 3055210 (by decide +kernel)
private theorem contact36RanksSlice160 : sliceWindow (auxiliaryRankSlice contact36) 160 4 = 2482511 :=
  contactRankWindow_of_rec contact36 160 4 2482511 (by decide +kernel)
private theorem contact36RanksSlice164 : sliceWindow (auxiliaryRankSlice contact36) 164 4 = 1975844 :=
  contactRankWindow_of_rec contact36 164 4 1975844 (by decide +kernel)
private theorem contact36RanksSlice168 : sliceWindow (auxiliaryRankSlice contact36) 168 4 = 1534030 :=
  contactRankWindow_of_rec contact36 168 4 1534030 (by decide +kernel)
private theorem contact36RanksSlice172 : sliceWindow (auxiliaryRankSlice contact36) 172 4 = 1153191 :=
  contactRankWindow_of_rec contact36 172 4 1153191 (by decide +kernel)
private theorem contact36RanksSlice176 : sliceWindow (auxiliaryRankSlice contact36) 176 4 = 830724 :=
  contactRankWindow_of_rec contact36 176 4 830724 (by decide +kernel)
private theorem contact36RanksSlice180 : sliceWindow (auxiliaryRankSlice contact36) 180 4 = 565650 :=
  contactRankWindow_of_rec contact36 180 4 565650 (by decide +kernel)
private theorem contact36RanksSlice184 : sliceWindow (auxiliaryRankSlice contact36) 184 4 = 353917 :=
  contactRankWindow_of_rec contact36 184 4 353917 (by decide +kernel)
private theorem contact36RanksSlice188 : sliceWindow (auxiliaryRankSlice contact36) 188 4 = 193404 :=
  contactRankWindow_of_rec contact36 188 4 193404 (by decide +kernel)
private theorem contact36RanksSlice192 : sliceWindow (auxiliaryRankSlice contact36) 192 4 = 83866 :=
  contactRankWindow_of_rec contact36 192 4 83866 (by decide +kernel)
private theorem contact36RanksSlice196 : sliceWindow (auxiliaryRankSlice contact36) 196 4 = 20691 :=
  contactRankWindow_of_rec contact36 196 4 20691 (by decide +kernel)
private theorem contact36RanksSlice200 : sliceWindow (auxiliaryRankSlice contact36) 200 18 = 0 :=
  contactRankWindow_of_rec contact36 200 18 0 (by decide +kernel)
private theorem contact36RanksJoin0_8 : sliceWindow (auxiliaryRankSlice contact36) 0 8 = 199286820 :=
  combineSlices (auxiliaryRankSlice contact36) 0 4 4 102038010 97248810 contact36RanksSlice0 contact36RanksSlice4
private theorem contact36RanksJoin8_8 : sliceWindow (auxiliaryRankSlice contact36) 8 8 = 180629220 :=
  combineSlices (auxiliaryRankSlice contact36) 8 4 4 92584410 88044810 contact36RanksSlice8 contact36RanksSlice12
private theorem contact36RanksJoin16_8 : sliceWindow (auxiliaryRankSlice contact36) 16 8 = 162970020 :=
  combineSlices (auxiliaryRankSlice contact36) 16 4 4 83630010 79340010 contact36RanksSlice16 contact36RanksSlice20
private theorem contact36RanksJoin24_8 : sliceWindow (auxiliaryRankSlice contact36) 24 8 = 146309220 :=
  combineSlices (auxiliaryRankSlice contact36) 24 4 4 75174810 71134410 contact36RanksSlice24 contact36RanksSlice28
private theorem contact36RanksJoin32_8 : sliceWindow (auxiliaryRankSlice contact36) 32 8 = 130646820 :=
  combineSlices (auxiliaryRankSlice contact36) 32 4 4 67218810 63428010 contact36RanksSlice32 contact36RanksSlice36
private theorem contact36RanksJoin40_8 : sliceWindow (auxiliaryRankSlice contact36) 40 8 = 115982820 :=
  combineSlices (auxiliaryRankSlice contact36) 40 4 4 59762010 56220810 contact36RanksSlice40 contact36RanksSlice44
private theorem contact36RanksJoin48_8 : sliceWindow (auxiliaryRankSlice contact36) 48 8 = 102317220 :=
  combineSlices (auxiliaryRankSlice contact36) 48 4 4 52804410 49512810 contact36RanksSlice48 contact36RanksSlice52
private theorem contact36RanksJoin56_8 : sliceWindow (auxiliaryRankSlice contact36) 56 8 = 89650020 :=
  combineSlices (auxiliaryRankSlice contact36) 56 4 4 46346010 43304010 contact36RanksSlice56 contact36RanksSlice60
private theorem contact36RanksJoin64_8 : sliceWindow (auxiliaryRankSlice contact36) 64 8 = 77979611 :=
  combineSlices (auxiliaryRankSlice contact36) 64 4 4 40386693 37592918 contact36RanksSlice64 contact36RanksSlice68
private theorem contact36RanksJoin72_8 : sliceWindow (auxiliaryRankSlice contact36) 72 8 = 67290131 :=
  combineSlices (auxiliaryRankSlice contact36) 72 4 4 34920974 32369157 contact36RanksSlice72 contact36RanksSlice76
private theorem contact36RanksJoin80_8 : sliceWindow (auxiliaryRankSlice contact36) 80 8 = 57554500 :=
  combineSlices (auxiliaryRankSlice contact36) 80 4 4 29935698 27618802 contact36RanksSlice80 contact36RanksSlice84
private theorem contact36RanksJoin88_8 : sliceWindow (auxiliaryRankSlice contact36) 88 8 = 48742627 :=
  combineSlices (auxiliaryRankSlice contact36) 88 4 4 25416479 23326148 contact36RanksSlice88 contact36RanksSlice92
private theorem contact36RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact36) 96 8 = 40817101 :=
  combineSlices (auxiliaryRankSlice contact36) 96 4 4 21345430 19471671 contact36RanksSlice96 contact36RanksSlice100
private theorem contact36RanksJoin104_8 : sliceWindow (auxiliaryRankSlice contact36) 104 8 = 33737214 :=
  combineSlices (auxiliaryRankSlice contact36) 104 4 4 17702244 16034970 contact36RanksSlice104 contact36RanksSlice108
private theorem contact36RanksJoin112_8 : sliceWindow (auxiliaryRankSlice contact36) 112 8 = 27462675 :=
  combineSlices (auxiliaryRankSlice contact36) 112 4 4 14466991 12995684 contact36RanksSlice112 contact36RanksSlice116
private theorem contact36RanksJoin120_8 : sliceWindow (auxiliaryRankSlice contact36) 120 8 = 21953157 :=
  combineSlices (auxiliaryRankSlice contact36) 120 4 4 11619070 10334087 contact36RanksSlice120 contact36RanksSlice124
private theorem contact36RanksJoin128_8 : sliceWindow (auxiliaryRankSlice contact36) 128 8 = 17167494 :=
  combineSlices (auxiliaryRankSlice contact36) 128 4 4 9138116 8029378 contact36RanksSlice128 contact36RanksSlice132
private theorem contact36RanksJoin136_8 : sliceWindow (auxiliaryRankSlice contact36) 136 8 = 13065795 :=
  combineSlices (auxiliaryRankSlice contact36) 136 4 4 7004607 6061188 contact36RanksSlice136 contact36RanksSlice140
private theorem contact36RanksJoin144_8 : sliceWindow (auxiliaryRankSlice contact36) 144 8 = 9607741 :=
  combineSlices (auxiliaryRankSlice contact36) 144 4 4 5197542 4410199 contact36RanksSlice144 contact36RanksSlice148
private theorem contact36RanksJoin152_8 : sliceWindow (auxiliaryRankSlice contact36) 152 8 = 6751758 :=
  combineSlices (auxiliaryRankSlice contact36) 152 4 4 3696548 3055210 contact36RanksSlice152 contact36RanksSlice156
private theorem contact36RanksJoin160_8 : sliceWindow (auxiliaryRankSlice contact36) 160 8 = 4458355 :=
  combineSlices (auxiliaryRankSlice contact36) 160 4 4 2482511 1975844 contact36RanksSlice160 contact36RanksSlice164
private theorem contact36RanksJoin168_8 : sliceWindow (auxiliaryRankSlice contact36) 168 8 = 2687221 :=
  combineSlices (auxiliaryRankSlice contact36) 168 4 4 1534030 1153191 contact36RanksSlice168 contact36RanksSlice172
private theorem contact36RanksJoin176_8 : sliceWindow (auxiliaryRankSlice contact36) 176 8 = 1396374 :=
  combineSlices (auxiliaryRankSlice contact36) 176 4 4 830724 565650 contact36RanksSlice176 contact36RanksSlice180
private theorem contact36RanksJoin184_8 : sliceWindow (auxiliaryRankSlice contact36) 184 8 = 547321 :=
  combineSlices (auxiliaryRankSlice contact36) 184 4 4 353917 193404 contact36RanksSlice184 contact36RanksSlice188
private theorem contact36RanksJoin192_8 : sliceWindow (auxiliaryRankSlice contact36) 192 8 = 104557 :=
  combineSlices (auxiliaryRankSlice contact36) 192 4 4 83866 20691 contact36RanksSlice192 contact36RanksSlice196
private theorem contact36RanksJoin0_16 : sliceWindow (auxiliaryRankSlice contact36) 0 16 = 379916040 :=
  combineSlices (auxiliaryRankSlice contact36) 0 8 8 199286820 180629220 contact36RanksJoin0_8 contact36RanksJoin8_8
private theorem contact36RanksJoin16_16 : sliceWindow (auxiliaryRankSlice contact36) 16 16 = 309279240 :=
  combineSlices (auxiliaryRankSlice contact36) 16 8 8 162970020 146309220 contact36RanksJoin16_8 contact36RanksJoin24_8
private theorem contact36RanksJoin32_16 : sliceWindow (auxiliaryRankSlice contact36) 32 16 = 246629640 :=
  combineSlices (auxiliaryRankSlice contact36) 32 8 8 130646820 115982820 contact36RanksJoin32_8 contact36RanksJoin40_8
private theorem contact36RanksJoin48_16 : sliceWindow (auxiliaryRankSlice contact36) 48 16 = 191967240 :=
  combineSlices (auxiliaryRankSlice contact36) 48 8 8 102317220 89650020 contact36RanksJoin48_8 contact36RanksJoin56_8
private theorem contact36RanksJoin64_16 : sliceWindow (auxiliaryRankSlice contact36) 64 16 = 145269742 :=
  combineSlices (auxiliaryRankSlice contact36) 64 8 8 77979611 67290131 contact36RanksJoin64_8 contact36RanksJoin72_8
private theorem contact36RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact36) 80 16 = 106297127 :=
  combineSlices (auxiliaryRankSlice contact36) 80 8 8 57554500 48742627 contact36RanksJoin80_8 contact36RanksJoin88_8
private theorem contact36RanksJoin96_16 : sliceWindow (auxiliaryRankSlice contact36) 96 16 = 74554315 :=
  combineSlices (auxiliaryRankSlice contact36) 96 8 8 40817101 33737214 contact36RanksJoin96_8 contact36RanksJoin104_8
private theorem contact36RanksJoin112_16 : sliceWindow (auxiliaryRankSlice contact36) 112 16 = 49415832 :=
  combineSlices (auxiliaryRankSlice contact36) 112 8 8 27462675 21953157 contact36RanksJoin112_8 contact36RanksJoin120_8
private theorem contact36RanksJoin128_16 : sliceWindow (auxiliaryRankSlice contact36) 128 16 = 30233289 :=
  combineSlices (auxiliaryRankSlice contact36) 128 8 8 17167494 13065795 contact36RanksJoin128_8 contact36RanksJoin136_8
private theorem contact36RanksJoin144_16 : sliceWindow (auxiliaryRankSlice contact36) 144 16 = 16359499 :=
  combineSlices (auxiliaryRankSlice contact36) 144 8 8 9607741 6751758 contact36RanksJoin144_8 contact36RanksJoin152_8
private theorem contact36RanksJoin160_16 : sliceWindow (auxiliaryRankSlice contact36) 160 16 = 7145576 :=
  combineSlices (auxiliaryRankSlice contact36) 160 8 8 4458355 2687221 contact36RanksJoin160_8 contact36RanksJoin168_8
private theorem contact36RanksJoin176_16 : sliceWindow (auxiliaryRankSlice contact36) 176 16 = 1943695 :=
  combineSlices (auxiliaryRankSlice contact36) 176 8 8 1396374 547321 contact36RanksJoin176_8 contact36RanksJoin184_8
private theorem contact36RanksJoin192_26 : sliceWindow (auxiliaryRankSlice contact36) 192 26 = 104557 :=
  combineSlices (auxiliaryRankSlice contact36) 192 8 18 104557 0 contact36RanksJoin192_8 contact36RanksSlice200
private theorem contact36RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact36) 0 32 = 689195280 :=
  combineSlices (auxiliaryRankSlice contact36) 0 16 16 379916040 309279240 contact36RanksJoin0_16 contact36RanksJoin16_16
private theorem contact36RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact36) 32 32 = 438596880 :=
  combineSlices (auxiliaryRankSlice contact36) 32 16 16 246629640 191967240 contact36RanksJoin32_16 contact36RanksJoin48_16
private theorem contact36RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact36) 64 32 = 251566869 :=
  combineSlices (auxiliaryRankSlice contact36) 64 16 16 145269742 106297127 contact36RanksJoin64_16 contact36RanksJoin80_16
private theorem contact36RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact36) 96 32 = 123970147 :=
  combineSlices (auxiliaryRankSlice contact36) 96 16 16 74554315 49415832 contact36RanksJoin96_16 contact36RanksJoin112_16
private theorem contact36RanksJoin128_32 : sliceWindow (auxiliaryRankSlice contact36) 128 32 = 46592788 :=
  combineSlices (auxiliaryRankSlice contact36) 128 16 16 30233289 16359499 contact36RanksJoin128_16 contact36RanksJoin144_16
private theorem contact36RanksJoin160_32 : sliceWindow (auxiliaryRankSlice contact36) 160 32 = 9089271 :=
  combineSlices (auxiliaryRankSlice contact36) 160 16 16 7145576 1943695 contact36RanksJoin160_16 contact36RanksJoin176_16
private theorem contact36RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact36) 0 64 = 1127792160 :=
  combineSlices (auxiliaryRankSlice contact36) 0 32 32 689195280 438596880 contact36RanksJoin0_32 contact36RanksJoin32_32
private theorem contact36RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact36) 64 64 = 375537016 :=
  combineSlices (auxiliaryRankSlice contact36) 64 32 32 251566869 123970147 contact36RanksJoin64_32 contact36RanksJoin96_32
private theorem contact36RanksJoin128_64 : sliceWindow (auxiliaryRankSlice contact36) 128 64 = 55682059 :=
  combineSlices (auxiliaryRankSlice contact36) 128 32 32 46592788 9089271 contact36RanksJoin128_32 contact36RanksJoin160_32
private theorem contact36RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact36) 0 128 = 1503329176 :=
  combineSlices (auxiliaryRankSlice contact36) 0 64 64 1127792160 375537016 contact36RanksJoin0_64 contact36RanksJoin64_64
private theorem contact36RanksJoin128_90 : sliceWindow (auxiliaryRankSlice contact36) 128 90 = 55786616 :=
  combineSlices (auxiliaryRankSlice contact36) 128 64 26 55682059 104557 contact36RanksJoin128_64 contact36RanksJoin192_26
private theorem contact36RanksJoin0_218 : sliceWindow (auxiliaryRankSlice contact36) 0 218 = 1559115792 :=
  combineSlices (auxiliaryRankSlice contact36) 0 128 90 1503329176 55786616 contact36RanksJoin0_128 contact36RanksJoin128_90
theorem contact36_margin : sourceMargin contact36 :=
  margin_of_checked_counts contact36 218 8916935253773229 510624204684503 34404168056 1559115792 rfl contact36OrdinaryColumns contact36ColumnsJoin0_218 contact36OrdinaryRanks contact36RanksJoin0_218 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts
