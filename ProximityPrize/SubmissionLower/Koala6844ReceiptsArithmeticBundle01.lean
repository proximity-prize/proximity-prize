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



private theorem primaryWindow_00000 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 512 =
    3667842011637348 :=
  firstJetWindow_of_closed primaryShape 0 0 512 (3667842011637348) (by decide +kernel) (by decide +kernel)

private theorem primaryWindow_00512 : contributionWindow (firstJetAuxContribution primaryShape 0) 512 230 =
    408999784170768 :=
  firstJetWindow_of_closed primaryShape 0 512 230 (408999784170768) (by decide +kernel) (by decide +kernel)

private theorem primaryJoined_00000_742 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 742 = 4076841795808116 :=
  joinWindows (firstJetAuxContribution primaryShape 0) 0 512 230 3667842011637348 408999784170768 primaryWindow_00000 primaryWindow_00512

theorem primary_firstJetGap_eq : firstJetGap primaryShape 0 = 286412979784 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum primaryShape 0 742 4076841795808116 rfl primaryJoined_00000_742]
  decide +kernel


private theorem firstRoomWindow_00000 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 =
    82262039011358244 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 0 512 (82262039011358244) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow_00512 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 512 512 =
    170597170621787964 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 512 512 (170597170621787964) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow_01024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 =
    154745642341876800 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1024 512 (154745642341876800) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow_01536 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1536 512 =
    76329115281820908 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1536 512 (76329115281820908) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow_02048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 2048 352 =
    8337245804664756 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 2048 352 (8337245804664756) (by decide +kernel) (by decide +kernel)

private theorem firstRoomJoined_00000_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 = 252859209633146208 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 512 82262039011358244 170597170621787964 firstRoomWindow_00000 firstRoomWindow_00512

private theorem firstRoomJoined_01024_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 1024 = 231074757623697708 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 512 154745642341876800 76329115281820908 firstRoomWindow_01024 firstRoomWindow_01536

private theorem firstRoomJoined_00000_2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 = 483933967256843916 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 1024 252859209633146208 231074757623697708 firstRoomJoined_00000_1024 firstRoomJoined_01024_1024

private theorem firstRoomJoined_00000_2400 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2400 = 492271213061508672 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 352 483933967256843916 8337245804664756 firstRoomJoined_00000_2048 firstRoomWindow_02048

theorem firstRoom_firstJetGap_eq : firstJetGap firstRoomShape firstRoomCut = 1360614431327 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstRoomShape firstRoomCut 2400 492271213061508672 rfl firstRoomJoined_00000_2400]
  decide +kernel


private theorem secondRoomWindow_00000 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 =
    82490940243593940 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 0 512 (82490940243593940) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow_00512 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 512 512 =
    170769861895255392 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 512 512 (170769861895255392) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow_01024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 =
    154862123606029656 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1024 512 (154862123606029656) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow_01536 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1536 512 =
    76389386523198552 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1536 512 (76389386523198552) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow_02048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 2048 352 =
    8348640939398832 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 2048 352 (8348640939398832) (by decide +kernel) (by decide +kernel)

private theorem secondRoomJoined_00000_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 = 253260802138849332 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 512 82490940243593940 170769861895255392 secondRoomWindow_00000 secondRoomWindow_00512

private theorem secondRoomJoined_01024_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 1024 = 231251510129228208 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 512 154862123606029656 76389386523198552 secondRoomWindow_01024 secondRoomWindow_01536

private theorem secondRoomJoined_00000_2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 = 484512312268077540 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 1024 253260802138849332 231251510129228208 secondRoomJoined_00000_1024 secondRoomJoined_01024_1024

private theorem secondRoomJoined_00000_2400 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2400 = 492860953207476372 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 352 484512312268077540 8348640939398832 secondRoomJoined_00000_2048 secondRoomWindow_02048

theorem secondRoom_firstJetGap_eq : firstJetGap secondRoomShape secondRoomCut = 98466050573 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondRoomShape secondRoomCut 2400 492860953207476372 rfl secondRoomJoined_00000_2400]
  decide +kernel


private theorem firstAdaptiveWindow_00000 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 512 =
    83489206486226976 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 0 512 (83489206486226976) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow_00512 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 512 512 =
    171523054280266752 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 512 512 (171523054280266752) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow_01024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 =
    155370242130013512 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1024 512 (155370242130013512) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow_01536 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1536 512 =
    76652431195563564 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1536 512 (76652431195563564) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow_02048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 2048 352 =
    8398451569628592 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 2048 352 (8398451569628592) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveJoined_00000_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 = 255012260766493728 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 512 512 83489206486226976 171523054280266752 firstAdaptiveWindow_00000 firstAdaptiveWindow_00512

private theorem firstAdaptiveJoined_01024_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 1024 = 232022673325577076 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 512 155370242130013512 76652431195563564 firstAdaptiveWindow_01024 firstAdaptiveWindow_01536

private theorem firstAdaptiveJoined_00000_2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 = 487034934092070804 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 1024 255012260766493728 232022673325577076 firstAdaptiveJoined_00000_1024 firstAdaptiveJoined_01024_1024

private theorem firstAdaptiveJoined_00000_2400 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2400 = 495433385661699396 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 352 487034934092070804 8398451569628592 firstAdaptiveJoined_00000_2048 firstAdaptiveWindow_02048

theorem firstAdaptive_firstJetGap_eq : firstJetGap firstAdaptiveShape 0 = firstAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstAdaptiveShape 0 2400 495433385661699396 rfl firstAdaptiveJoined_00000_2400]
  decide +kernel


private theorem secondAdaptiveWindow_00000 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 512 =
    145959592796862313608 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 0 512 (145959592796862313608) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_00512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 512 512 =
    326679746383533721308 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 512 512 (326679746383533721308) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_01024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 =
    503905844323158249924 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1024 512 (503905844323158249924) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_01536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1536 512 =
    677637886614859729440 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1536 512 (677637886614859729440) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_02048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 =
    847875873258606396756 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2048 512 (847875873258606396756) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_02560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2560 512 =
    1014619804254358927272 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2560 512 (1014619804254358927272) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_03072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 =
    1177869679602150029820 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3072 512 (1177869679602150029820) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_03584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3584 512 =
    1337625499301973453084 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3584 512 (1337625499301973453084) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_04096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 =
    1493887263353807841420 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4096 512 (1493887263353807841420) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_04608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4608 512 =
    1646654971757688932904 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4608 512 (1646654971757688932904) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_05120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 =
    1795928624513583041892 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5120 512 (1795928624513583041892) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_05632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5632 512 =
    1941708221621507224080 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5632 512 (1941708221621507224080) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_06144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 =
    2083993763081471671224 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6144 512 (2083993763081471671224) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_06656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6656 512 =
    2222785248893441277720 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6656 512 (2222785248893441277720) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_07168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 =
    2358082679057754841848 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7168 512 (2358082679057754841848) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_07680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7680 512 =
    2489886053575394076972 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7680 512 (2489886053575394076972) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_08192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 =
    2618195372446171648512 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8192 512 (2618195372446171648512) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_08704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8704 512 =
    2743010635669091946408 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8704 512 (2743010635669091946408) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_09216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 =
    2864331843244048592676 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9216 512 (2864331843244048592676) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_09728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9728 512 =
    2982158995171039982388 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9728 512 (2982158995171039982388) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_10240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 =
    3096492091450040114952 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10240 512 (3096492091450040114952) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_10752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10752 512 =
    3207331132081086718392 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10752 512 (3207331132081086718392) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_11264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 =
    3314676117064149127152 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11264 512 (3314676117064149127152) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_11776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11776 512 =
    3418527046399238795616 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11776 512 (3418527046399238795616) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_12288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 =
    3518883920086370359128 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12288 512 (3518883920086370359128) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_12800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12800 512 =
    3615746738125506809472 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12800 512 (3615746738125506809472) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_13312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 =
    3709115500516686216300 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13312 512 (3709115500516686216300) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_13824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13824 512 =
    3798990207259890770292 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13824 512 (3798990207259890770292) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_14336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 =
    3885370858355286751044 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14336 512 (3885370858355286751044) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_14848 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14848 512 =
    3968257453803878787756 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14848 512 (3968257453803878787756) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_15360 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 =
    4047649993605752786364 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15360 512 (4047649993605752786364) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_15872 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15872 512 =
    4123548477759912040716 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15872 512 (4123548477759912040716) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 =
    4195952906266078168224 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16384 512 (4195952906266078168224) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_16896 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16896 512 =
    4264863279124290146988 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16896 512 (4264863279124290146988) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_17408 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 =
    4330279596334520767020 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17408 512 (4330279596334520767020) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_17920 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17920 512 =
    4392201857896776048864 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17920 512 (4392201857896776048864) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_18432 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 =
    4450630063811074534656 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18432 512 (4450630063811074534656) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_18944 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18944 512 =
    4505564214077377916352 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18944 512 (4505564214077377916352) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_19456 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 =
    4557004308695722922856 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19456 512 (4557004308695722922856) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_19968 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19968 512 =
    4604950347666095720472 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19968 512 (4604950347666095720472) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_20480 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 =
    4649402330988483768576 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20480 512 (4649402330988483768576) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_20992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20992 512 =
    4690360258662918374580 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20992 512 (4690360258662918374580) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_21504 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 =
    4727824130689443874380 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 21504 512 (4727824130689443874380) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_22016 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22016 512 =
    4761793947068997128772 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22016 512 (4761793947068997128772) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_22528 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 =
    4792269707801922000552 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22528 512 (4792269707801922000552) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_23040 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23040 512 =
    4819253691144111585696 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23040 512 (4819253691144111585696) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_23552 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 =
    4842773024246015209668 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23552 512 (4842773024246015209668) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_24064 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24064 512 =
    4862879524822908054120 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24064 512 (4862879524822908054120) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_24576 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 =
    4879627236070340878800 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24576 512 (4879627236070340878800) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_25088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25088 512 =
    4893070201183802954532 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25088 512 (4893070201183802954532) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_25600 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 =
    4903262463358857305940 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25600 512 (4903262463358857305940) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_26112 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26112 512 =
    4910258065791023141028 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26112 512 (4910258065791023141028) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_26624 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 =
    4914111051675810784380 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26624 512 (4914111051675810784380) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_27136 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27136 512 =
    4914875464208782877100 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27136 512 (4914875464208782877100) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_27648 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 =
    4912605346585432613940 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27648 512 (4912605346585432613940) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_28160 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28160 512 =
    4907354742001308780936 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28160 512 (4907354742001308780936) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_28672 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 =
    4899177693651971232432 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28672 512 (4899177693651971232432) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_29184 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29184 512 =
    4888128244733703352740 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29184 512 (4888128244733703352740) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_29696 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 =
    4874260438442626375032 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29696 512 (4874260438442626375032) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_30208 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30208 512 =
    4857628317973506348504 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30208 512 (4857628317973506348504) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_30720 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 =
    4838285926521270645252 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30720 512 (4838285926521270645252) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_31232 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31232 512 =
    4816287307281406639788 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31232 512 (4816287307281406639788) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_31744 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 =
    4791686503449474081780 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31744 512 (4791686503449474081780) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_32256 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32256 512 =
    4764537558220997071428 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32256 512 (4764537558220997071428) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 =
    4734894514791480710472 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32768 512 (4734894514791480710472) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_33280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33280 512 =
    4702811416356490114812 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33280 512 (4702811416356490114812) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_33792 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 =
    4668342306111521172864 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33792 512 (4668342306111521172864) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_34304 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34304 512 =
    4631541227252117142216 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34304 512 (4631541227252117142216) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_34816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 =
    4592462222973818544816 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34816 512 (4592462222973818544816) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_35328 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35328 512 =
    4551159336472117802292 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35328 512 (4551159336472117802292) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_35840 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 =
    4507686610942582743180 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35840 512 (4507686610942582743180) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_36352 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36352 512 =
    4462098089581318660344 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36352 512 (4462098089581318660344) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_36864 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 =
    4414447815584640779400 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36864 512 (4414447815584640779400) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_37376 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37376 512 =
    4364789832147517045260 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37376 512 (4364789832147517045260) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_37888 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 =
    4313178182464693959720 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37888 512 (4313178182464693959720) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_38400 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38400 512 =
    4259666909731670079840 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38400 512 (4259666909731670079840) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_38912 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 =
    4204310057143946167176 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38912 512 (4204310057143946167176) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_39424 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39424 512 =
    4147161667897088939124 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39424 512 (4147161667897088939124) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_39936 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 =
    4088275785186597565536 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39936 512 (4088275785186597565536) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_40448 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40448 512 =
    4027706452208009729916 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40448 512 (4027706452208009729916) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_40960 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 =
    3965507712156870104868 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40960 512 (3965507712156870104868) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_41472 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41472 512 =
    3901733608228669597692 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41472 512 (3901733608228669597692) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_41984 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 =
    3836438183618974201992 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41984 512 (3836438183618974201992) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_42496 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 42496 512 =
    3769675481523296110068 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 42496 512 (3769675481523296110068) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_43008 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 =
    3701499545137154568228 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43008 512 (3701499545137154568228) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_43520 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43520 512 =
    3631964417656489058244 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43520 512 (3631964417656489058244) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_44032 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 =
    3561124142277763702944 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44032 512 (3561124142277763702944) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_44544 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44544 512 =
    3489032762196196777500 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44544 512 (3489032762196196777500) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_45056 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 =
    3415744320606361779288 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45056 512 (3415744320606361779288) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_45568 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45568 512 =
    3341312860703734096368 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45568 512 (3341312860703734096368) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_46080 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 =
    3265792425683816360064 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46080 512 (3265792425683816360064) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_46592 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46592 512 =
    3189237058742140986864 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46592 512 (3189237058742140986864) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_47104 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 =
    3111700803074256463368 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47104 512 (3111700803074256463368) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_47616 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47616 512 =
    3033237701875652495484 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47616 512 (3033237701875652495484) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_48128 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 =
    2953901798341893567204 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48128 512 (2953901798341893567204) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_48640 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48640 512 =
    2873747135668496017356 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48640 512 (2873747135668496017356) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_49152 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 =
    2792827757050973518764 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49152 512 (2792827757050973518764) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_49664 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49664 512 =
    2711197705684887054984 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49664 512 (2711197705684887054984) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_50176 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 =
    2628911024765728387296 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50176 512 (2628911024765728387296) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_50688 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50688 512 =
    2546021757489280089768 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50688 512 (2546021757489280089768) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_51200 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 =
    2462583947052070697472 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51200 512 (2462583947052070697472) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_51712 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51712 512 =
    2378651636649580237128 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51712 512 (2378651636649580237128) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_52224 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 =
    2294278869476332289964 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52224 512 (2294278869476332289964) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_52736 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52736 512 =
    2209519688727665460924 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52736 512 (2209519688727665460924) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_53248 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 =
    2124428137599132076332 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53248 512 (2124428137599132076332) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_53760 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53760 512 =
    2039058259286221263648 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53760 512 (2039058259286221263648) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_54272 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 =
    1953464096984494843764 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54272 512 (1953464096984494843764) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_54784 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54784 512 =
    1867699693889474024376 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54784 512 (1867699693889474024376) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_55296 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 =
    1781819093196666948144 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55296 512 (1781819093196666948144) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_55808 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55808 512 =
    1695876338101637294592 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55808 512 (1695876338101637294592) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_56320 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 =
    1609925471799879296520 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56320 512 (1609925471799879296520) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_56832 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56832 512 =
    1524020537486939559156 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56832 512 (1524020537486939559156) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_57344 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 =
    1438215578358355732092 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57344 512 (1438215578358355732092) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_57856 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57856 512 =
    1352564637609744203136 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57856 512 (1352564637609744203136) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_58368 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 =
    1267121758437621032652 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58368 512 (1267121758437621032652) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_58880 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58880 512 =
    1181940984037737874608 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58880 512 (1181940984037737874608) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_59392 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 512 =
    1097076357604651470036 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 59392 512 (1097076357604651470036) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_59904 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59904 512 =
    1012928461134874396824 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 59904 512 (1012928461134874396824) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_60416 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60416 512 =
    932006438299413359088 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 60416 512 (932006438299413359088) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_60928 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60928 512 =
    855388789537357325448 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 60928 512 (855388789537357325448) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_61440 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 512 =
    783060746333991071700 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 61440 512 (783060746333991071700) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_61952 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61952 512 =
    714928956606781307988 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 61952 512 (714928956606781307988) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_62464 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62464 512 =
    650868683037486507624 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 62464 512 (650868683037486507624) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_62976 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62976 512 =
    590754473303123997048 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 62976 512 (590754473303123997048) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_63488 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 512 =
    534460875080623808172 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 63488 512 (534460875080623808172) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_64000 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64000 512 =
    481862436046951405452 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 64000 512 (481862436046951405452) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_64512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64512 512 =
    432833703879093725256 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 64512 512 (432833703879093725256) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_65024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65024 512 =
    387249226254026028264 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 65024 512 (387249226254026028264) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_65536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 512 =
    344983550849605963704 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 65536 512 (344983550849605963704) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_66048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66048 512 =
    305911225342819586340 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 66048 512 (305911225342819586340) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_66560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66560 512 =
    269906797409539282704 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 66560 512 (269906797409539282704) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_67072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67072 512 =
    236844814726622107620 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 67072 512 (236844814726622107620) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_67584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 512 =
    206599824970999499616 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 67584 512 (206599824970999499616) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_68096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68096 512 =
    179046375819682109568 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 68096 512 (179046375819682109568) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_68608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68608 512 =
    154059014949582086124 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 68608 512 (154059014949582086124) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_69120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69120 512 =
    131512290037703822016 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 69120 512 (131512290037703822016) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_69632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 512 =
    111280748760994767636 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 69632 512 (111280748760994767636) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_70144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70144 512 =
    93238938796401594600 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 70144 512 (93238938796401594600) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_70656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70656 512 =
    77261407820928570744 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 70656 512 (77261407820928570744) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_71168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71168 512 =
    63222703511489752464 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 71168 512 (63222703511489752464) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_71680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 512 =
    50997373545092010228 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 71680 512 (50997373545092010228) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_72192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72192 512 =
    40459965598678506180 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 72192 512 (40459965598678506180) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_72704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72704 512 =
    31485027349801502844 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 72704 512 (31485027349801502844) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_73216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73216 512 =
    23947106475012338448 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 73216 512 (23947106475012338448) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_73728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 512 =
    17720750650816720920 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 73728 512 (17720750650816720920) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_74240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74240 512 =
    12680507554218869520 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 74240 512 (12680507554218869520) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_74752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74752 512 =
    8700924862143702504 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 74752 512 (8700924862143702504) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_75264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75264 512 =
    5656550251578351336 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 75264 512 (5656550251578351336) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_75776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 512 =
    3421931399489142252 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 75776 512 (3421931399489142252) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_76288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76288 512 =
    1871615982805185864 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 76288 512 (1871615982805185864) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_76800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76800 512 =
    880151678543875692 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 76800 512 (880151678543875692) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_77312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77312 512 =
    322086163612423488 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 77312 512 (322086163612423488) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_77824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77824 512 =
    71967115018182108 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 77824 512 (71967115018182108) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow_78336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 78336 480 =
    4342231228738812 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 78336 480 (4342231228738812) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveJoined_00000_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 = 472639339180396034916 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 512 512 145959592796862313608 326679746383533721308 secondAdaptiveWindow_00000 secondAdaptiveWindow_00512

private theorem secondAdaptiveJoined_01024_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 1024 = 1181543730938017979364 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 512 503905844323158249924 677637886614859729440 secondAdaptiveWindow_01024 secondAdaptiveWindow_01536

private theorem secondAdaptiveJoined_02048_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 = 1862495677512965324028 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 512 847875873258606396756 1014619804254358927272 secondAdaptiveWindow_02048 secondAdaptiveWindow_02560

private theorem secondAdaptiveJoined_03072_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 1024 = 2515495178904123482904 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 512 1177869679602150029820 1337625499301973453084 secondAdaptiveWindow_03072 secondAdaptiveWindow_03584

private theorem secondAdaptiveJoined_04096_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 = 3140542235111496774324 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 512 1493887263353807841420 1646654971757688932904 secondAdaptiveWindow_04096 secondAdaptiveWindow_04608

private theorem secondAdaptiveJoined_05120_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 1024 = 3737636846135090265972 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 512 1795928624513583041892 1941708221621507224080 secondAdaptiveWindow_05120 secondAdaptiveWindow_05632

private theorem secondAdaptiveJoined_06144_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 = 4306779011974912948944 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 512 2083993763081471671224 2222785248893441277720 secondAdaptiveWindow_06144 secondAdaptiveWindow_06656

private theorem secondAdaptiveJoined_07168_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 1024 = 4847968732633148918820 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 512 2358082679057754841848 2489886053575394076972 secondAdaptiveWindow_07168 secondAdaptiveWindow_07680

private theorem secondAdaptiveJoined_08192_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 = 5361206008115263594920 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 512 2618195372446171648512 2743010635669091946408 secondAdaptiveWindow_08192 secondAdaptiveWindow_08704

private theorem secondAdaptiveJoined_09216_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 1024 = 5846490838415088575064 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 512 2864331843244048592676 2982158995171039982388 secondAdaptiveWindow_09216 secondAdaptiveWindow_09728

private theorem secondAdaptiveJoined_10240_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 = 6303823223531126833344 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 512 3096492091450040114952 3207331132081086718392 secondAdaptiveWindow_10240 secondAdaptiveWindow_10752

private theorem secondAdaptiveJoined_11264_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 1024 = 6733203163463387922768 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 512 3314676117064149127152 3418527046399238795616 secondAdaptiveWindow_11264 secondAdaptiveWindow_11776

private theorem secondAdaptiveJoined_12288_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 = 7134630658211877168600 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 512 3518883920086370359128 3615746738125506809472 secondAdaptiveWindow_12288 secondAdaptiveWindow_12800

private theorem secondAdaptiveJoined_13312_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 1024 = 7508105707776576986592 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 512 3709115500516686216300 3798990207259890770292 secondAdaptiveWindow_13312 secondAdaptiveWindow_13824

private theorem secondAdaptiveJoined_14336_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 = 7853628312159165538800 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 512 3885370858355286751044 3968257453803878787756 secondAdaptiveWindow_14336 secondAdaptiveWindow_14848

private theorem secondAdaptiveJoined_15360_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 1024 = 8171198471365664827080 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 512 4047649993605752786364 4123548477759912040716 secondAdaptiveWindow_15360 secondAdaptiveWindow_15872

private theorem secondAdaptiveJoined_16384_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 = 8460816185390368315212 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 512 4195952906266078168224 4264863279124290146988 secondAdaptiveWindow_16384 secondAdaptiveWindow_16896

private theorem secondAdaptiveJoined_17408_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 1024 = 8722481454231296815884 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 512 4330279596334520767020 4392201857896776048864 secondAdaptiveWindow_17408 secondAdaptiveWindow_17920

private theorem secondAdaptiveJoined_18432_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 = 8956194277888452451008 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 512 4450630063811074534656 4505564214077377916352 secondAdaptiveWindow_18432 secondAdaptiveWindow_18944

private theorem secondAdaptiveJoined_19456_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 1024 = 9161954656361818643328 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 512 4557004308695722922856 4604950347666095720472 secondAdaptiveWindow_19456 secondAdaptiveWindow_19968

private theorem secondAdaptiveJoined_20480_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 = 9339762589651402143156 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 512 4649402330988483768576 4690360258662918374580 secondAdaptiveWindow_20480 secondAdaptiveWindow_20992

private theorem secondAdaptiveJoined_21504_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 1024 = 9489618077758441003152 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 512 4727824130689443874380 4761793947068997128772 secondAdaptiveWindow_21504 secondAdaptiveWindow_22016

private theorem secondAdaptiveJoined_22528_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 = 9611523398946033586248 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 512 4792269707801922000552 4819253691144111585696 secondAdaptiveWindow_22528 secondAdaptiveWindow_23040

private theorem secondAdaptiveJoined_23552_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 1024 = 9705652549068923263788 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 512 4842773024246015209668 4862879524822908054120 secondAdaptiveWindow_23552 secondAdaptiveWindow_24064

private theorem secondAdaptiveJoined_24576_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 = 9772697437254143833332 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 512 4879627236070340878800 4893070201183802954532 secondAdaptiveWindow_24576 secondAdaptiveWindow_25088

private theorem secondAdaptiveJoined_25600_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 1024 = 9813520529149880446968 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 512 4903262463358857305940 4910258065791023141028 secondAdaptiveWindow_25600 secondAdaptiveWindow_26112

private theorem secondAdaptiveJoined_26624_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 = 9828986515884593661480 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 512 4914111051675810784380 4914875464208782877100 secondAdaptiveWindow_26624 secondAdaptiveWindow_27136

private theorem secondAdaptiveJoined_27648_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 1024 = 9819960088586741394876 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 512 4912605346585432613940 4907354742001308780936 secondAdaptiveWindow_27648 secondAdaptiveWindow_28160

private theorem secondAdaptiveJoined_28672_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 = 9787305938385674585172 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 512 4899177693651971232432 4888128244733703352740 secondAdaptiveWindow_28672 secondAdaptiveWindow_29184

private theorem secondAdaptiveJoined_29696_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 1024 = 9731888756416132723536 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 512 4874260438442626375032 4857628317973506348504 secondAdaptiveWindow_29696 secondAdaptiveWindow_30208

private theorem secondAdaptiveJoined_30720_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 = 9654573233802677285040 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 512 4838285926521270645252 4816287307281406639788 secondAdaptiveWindow_30720 secondAdaptiveWindow_31232

private theorem secondAdaptiveJoined_31744_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 1024 = 9556224061670471153208 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 512 4791686503449474081780 4764537558220997071428 secondAdaptiveWindow_31744 secondAdaptiveWindow_32256

private theorem secondAdaptiveJoined_32768_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 = 9437705931147970825284 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 512 4734894514791480710472 4702811416356490114812 secondAdaptiveWindow_32768 secondAdaptiveWindow_33280

private theorem secondAdaptiveJoined_33792_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 1024 = 9299883533363638315080 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 512 4668342306111521172864 4631541227252117142216 secondAdaptiveWindow_33792 secondAdaptiveWindow_34304

private theorem secondAdaptiveJoined_34816_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 = 9143621559445936347108 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 512 4592462222973818544816 4551159336472117802292 secondAdaptiveWindow_34816 secondAdaptiveWindow_35328

private theorem secondAdaptiveJoined_35840_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 1024 = 8969784700523901403524 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 512 4507686610942582743180 4462098089581318660344 secondAdaptiveWindow_35840 secondAdaptiveWindow_36352

private theorem secondAdaptiveJoined_36864_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 = 8779237647732157824660 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 512 4414447815584640779400 4364789832147517045260 secondAdaptiveWindow_36864 secondAdaptiveWindow_37376

private theorem secondAdaptiveJoined_37888_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 1024 = 8572845092196364039560 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 512 4313178182464693959720 4259666909731670079840 secondAdaptiveWindow_37888 secondAdaptiveWindow_38400

private theorem secondAdaptiveJoined_38912_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 = 8351471725041035106300 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 512 4204310057143946167176 4147161667897088939124 secondAdaptiveWindow_38912 secondAdaptiveWindow_39424

private theorem secondAdaptiveJoined_39936_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 1024 = 8115982237394607295452 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 512 4088275785186597565536 4027706452208009729916 secondAdaptiveWindow_39936 secondAdaptiveWindow_40448

private theorem secondAdaptiveJoined_40960_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 = 7867241320385539702560 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 512 3965507712156870104868 3901733608228669597692 secondAdaptiveWindow_40960 secondAdaptiveWindow_41472

private theorem secondAdaptiveJoined_41984_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 1024 = 7606113665142270312060 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 512 3836438183618974201992 3769675481523296110068 secondAdaptiveWindow_41984 secondAdaptiveWindow_42496

private theorem secondAdaptiveJoined_43008_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 = 7333463962793643626472 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 512 3701499545137154568228 3631964417656489058244 secondAdaptiveWindow_43008 secondAdaptiveWindow_43520

private theorem secondAdaptiveJoined_44032_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 1024 = 7050156904473960480444 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 512 3561124142277763702944 3489032762196196777500 secondAdaptiveWindow_44032 secondAdaptiveWindow_44544

private theorem secondAdaptiveJoined_45056_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 = 6757057181310095875656 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 512 3415744320606361779288 3341312860703734096368 secondAdaptiveWindow_45056 secondAdaptiveWindow_45568

private theorem secondAdaptiveJoined_46080_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 1024 = 6455029484425957346928 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 512 3265792425683816360064 3189237058742140986864 secondAdaptiveWindow_46080 secondAdaptiveWindow_46592

private theorem secondAdaptiveJoined_47104_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 = 6144938504949908958852 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 512 3111700803074256463368 3033237701875652495484 secondAdaptiveWindow_47104 secondAdaptiveWindow_47616

private theorem secondAdaptiveJoined_48128_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 1024 = 5827648934010389584560 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 512 2953901798341893567204 2873747135668496017356 secondAdaptiveWindow_48128 secondAdaptiveWindow_48640

private theorem secondAdaptiveJoined_49152_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 = 5504025462735860573748 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 512 2792827757050973518764 2711197705684887054984 secondAdaptiveWindow_49152 secondAdaptiveWindow_49664

private theorem secondAdaptiveJoined_50176_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 1024 = 5174932782255008477064 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 512 2628911024765728387296 2546021757489280089768 secondAdaptiveWindow_50176 secondAdaptiveWindow_50688

private theorem secondAdaptiveJoined_51200_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 = 4841235583701650934600 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 512 2462583947052070697472 2378651636649580237128 secondAdaptiveWindow_51200 secondAdaptiveWindow_51712

private theorem secondAdaptiveJoined_52224_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 1024 = 4503798558203997750888 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 512 2294278869476332289964 2209519688727665460924 secondAdaptiveWindow_52224 secondAdaptiveWindow_52736

private theorem secondAdaptiveJoined_53248_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 = 4163486396885353339980 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 512 2124428137599132076332 2039058259286221263648 secondAdaptiveWindow_53248 secondAdaptiveWindow_53760

private theorem secondAdaptiveJoined_54272_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 1024 = 3821163790873968868140 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 512 1953464096984494843764 1867699693889474024376 secondAdaptiveWindow_54272 secondAdaptiveWindow_54784

private theorem secondAdaptiveJoined_55296_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 = 3477695431298304242736 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 512 1781819093196666948144 1695876338101637294592 secondAdaptiveWindow_55296 secondAdaptiveWindow_55808

private theorem secondAdaptiveJoined_56320_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 1024 = 3133946009286818855676 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 512 1609925471799879296520 1524020537486939559156 secondAdaptiveWindow_56320 secondAdaptiveWindow_56832

private theorem secondAdaptiveJoined_57344_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 = 2790780215968099935228 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 512 1438215578358355732092 1352564637609744203136 secondAdaptiveWindow_57344 secondAdaptiveWindow_57856

private theorem secondAdaptiveJoined_58368_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 1024 = 2449062742475358907260 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 512 1267121758437621032652 1181940984037737874608 secondAdaptiveWindow_58368 secondAdaptiveWindow_58880

private theorem secondAdaptiveJoined_59392_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 1024 = 2110004818739525866860 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 59392 512 512 1097076357604651470036 1012928461134874396824 secondAdaptiveWindow_59392 secondAdaptiveWindow_59904

private theorem secondAdaptiveJoined_60416_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60416 1024 = 1787395227836770684536 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 60416 512 512 932006438299413359088 855388789537357325448 secondAdaptiveWindow_60416 secondAdaptiveWindow_60928

private theorem secondAdaptiveJoined_61440_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 1024 = 1497989702940772379688 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 512 512 783060746333991071700 714928956606781307988 secondAdaptiveWindow_61440 secondAdaptiveWindow_61952

private theorem secondAdaptiveJoined_62464_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62464 1024 = 1241623156340610504672 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 62464 512 512 650868683037486507624 590754473303123997048 secondAdaptiveWindow_62464 secondAdaptiveWindow_62976

private theorem secondAdaptiveJoined_63488_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 1024 = 1016323311127575213624 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 63488 512 512 534460875080623808172 481862436046951405452 secondAdaptiveWindow_63488 secondAdaptiveWindow_64000

private theorem secondAdaptiveJoined_64512_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64512 1024 = 820082930133119753520 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 64512 512 512 432833703879093725256 387249226254026028264 secondAdaptiveWindow_64512 secondAdaptiveWindow_65024

private theorem secondAdaptiveJoined_65536_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 1024 = 650894776192425550044 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 512 512 344983550849605963704 305911225342819586340 secondAdaptiveWindow_65536 secondAdaptiveWindow_66048

private theorem secondAdaptiveJoined_66560_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66560 1024 = 506751612136161390324 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 66560 512 512 269906797409539282704 236844814726622107620 secondAdaptiveWindow_66560 secondAdaptiveWindow_67072

private theorem secondAdaptiveJoined_67584_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 1024 = 385646200790681609184 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 67584 512 512 206599824970999499616 179046375819682109568 secondAdaptiveWindow_67584 secondAdaptiveWindow_68096

private theorem secondAdaptiveJoined_68608_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68608 1024 = 285571304987285908140 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 68608 512 512 154059014949582086124 131512290037703822016 secondAdaptiveWindow_68608 secondAdaptiveWindow_69120

private theorem secondAdaptiveJoined_69632_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 1024 = 204519687557396362236 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 512 512 111280748760994767636 93238938796401594600 secondAdaptiveWindow_69632 secondAdaptiveWindow_70144

private theorem secondAdaptiveJoined_70656_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70656 1024 = 140484111332418323208 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 70656 512 512 77261407820928570744 63222703511489752464 secondAdaptiveWindow_70656 secondAdaptiveWindow_71168

private theorem secondAdaptiveJoined_71680_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 1024 = 91457339143770516408 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 71680 512 512 50997373545092010228 40459965598678506180 secondAdaptiveWindow_71680 secondAdaptiveWindow_72192

private theorem secondAdaptiveJoined_72704_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72704 1024 = 55432133824813841292 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 72704 512 512 31485027349801502844 23947106475012338448 secondAdaptiveWindow_72704 secondAdaptiveWindow_73216

private theorem secondAdaptiveJoined_73728_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 1024 = 30401258205035590440 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 512 512 17720750650816720920 12680507554218869520 secondAdaptiveWindow_73728 secondAdaptiveWindow_74240

private theorem secondAdaptiveJoined_74752_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74752 1024 = 14357475113722053840 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 74752 512 512 8700924862143702504 5656550251578351336 secondAdaptiveWindow_74752 secondAdaptiveWindow_75264

private theorem secondAdaptiveJoined_75776_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 1024 = 5293547382294328116 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 75776 512 512 3421931399489142252 1871615982805185864 secondAdaptiveWindow_75776 secondAdaptiveWindow_76288

private theorem secondAdaptiveJoined_76800_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76800 1024 = 1202237842156299180 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 76800 512 512 880151678543875692 322086163612423488 secondAdaptiveWindow_76800 secondAdaptiveWindow_77312

private theorem secondAdaptiveJoined_77824_992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77824 992 = 76309346246920920 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 77824 512 480 71967115018182108 4342231228738812 secondAdaptiveWindow_77824 secondAdaptiveWindow_78336

private theorem secondAdaptiveJoined_00000_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 = 1654183070118414014280 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 1024 472639339180396034916 1181543730938017979364 secondAdaptiveJoined_00000_1024 secondAdaptiveJoined_01024_1024

private theorem secondAdaptiveJoined_02048_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 2048 = 4377990856417088806932 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 1024 1862495677512965324028 2515495178904123482904 secondAdaptiveJoined_02048_1024 secondAdaptiveJoined_03072_1024

private theorem secondAdaptiveJoined_04096_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 = 6878179081246587040296 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 1024 3140542235111496774324 3737636846135090265972 secondAdaptiveJoined_04096_1024 secondAdaptiveJoined_05120_1024

private theorem secondAdaptiveJoined_06144_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 2048 = 9154747744608061867764 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 1024 4306779011974912948944 4847968732633148918820 secondAdaptiveJoined_06144_1024 secondAdaptiveJoined_07168_1024

private theorem secondAdaptiveJoined_08192_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 = 11207696846530352169984 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 1024 5361206008115263594920 5846490838415088575064 secondAdaptiveJoined_08192_1024 secondAdaptiveJoined_09216_1024

private theorem secondAdaptiveJoined_10240_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 2048 = 13037026386994514756112 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 1024 6303823223531126833344 6733203163463387922768 secondAdaptiveJoined_10240_1024 secondAdaptiveJoined_11264_1024

private theorem secondAdaptiveJoined_12288_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 = 14642736365988454155192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 1024 7134630658211877168600 7508105707776576986592 secondAdaptiveJoined_12288_1024 secondAdaptiveJoined_13312_1024

private theorem secondAdaptiveJoined_14336_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 2048 = 16024826783524830365880 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 1024 7853628312159165538800 8171198471365664827080 secondAdaptiveJoined_14336_1024 secondAdaptiveJoined_15360_1024

private theorem secondAdaptiveJoined_16384_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 = 17183297639621665131096 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 1024 8460816185390368315212 8722481454231296815884 secondAdaptiveJoined_16384_1024 secondAdaptiveJoined_17408_1024

private theorem secondAdaptiveJoined_18432_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 2048 = 18118148934250271094336 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 1024 8956194277888452451008 9161954656361818643328 secondAdaptiveJoined_18432_1024 secondAdaptiveJoined_19456_1024

private theorem secondAdaptiveJoined_20480_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 = 18829380667409843146308 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 1024 9339762589651402143156 9489618077758441003152 secondAdaptiveJoined_20480_1024 secondAdaptiveJoined_21504_1024

private theorem secondAdaptiveJoined_22528_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 2048 = 19317175948014956850036 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 1024 9611523398946033586248 9705652549068923263788 secondAdaptiveJoined_22528_1024 secondAdaptiveJoined_23552_1024

private theorem secondAdaptiveJoined_24576_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 = 19586217966404024280300 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 1024 9772697437254143833332 9813520529149880446968 secondAdaptiveJoined_24576_1024 secondAdaptiveJoined_25600_1024

private theorem secondAdaptiveJoined_26624_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 2048 = 19648946604471335056356 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 1024 9828986515884593661480 9819960088586741394876 secondAdaptiveJoined_26624_1024 secondAdaptiveJoined_27648_1024

private theorem secondAdaptiveJoined_28672_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 = 19519194694801807308708 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 1024 9787305938385674585172 9731888756416132723536 secondAdaptiveJoined_28672_1024 secondAdaptiveJoined_29696_1024

private theorem secondAdaptiveJoined_30720_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 2048 = 19210797295473148438248 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 1024 9654573233802677285040 9556224061670471153208 secondAdaptiveJoined_30720_1024 secondAdaptiveJoined_31744_1024

private theorem secondAdaptiveJoined_32768_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 = 18737589464511609140364 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 1024 9437705931147970825284 9299883533363638315080 secondAdaptiveJoined_32768_1024 secondAdaptiveJoined_33792_1024

private theorem secondAdaptiveJoined_34816_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 2048 = 18113406259969837750632 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 1024 9143621559445936347108 8969784700523901403524 secondAdaptiveJoined_34816_1024 secondAdaptiveJoined_35840_1024

private theorem secondAdaptiveJoined_36864_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 = 17352082739928521864220 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 1024 8779237647732157824660 8572845092196364039560 secondAdaptiveJoined_36864_1024 secondAdaptiveJoined_37888_1024

private theorem secondAdaptiveJoined_38912_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 2048 = 16467453962435642401752 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 1024 8351471725041035106300 8115982237394607295452 secondAdaptiveJoined_38912_1024 secondAdaptiveJoined_39936_1024

private theorem secondAdaptiveJoined_40960_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 = 15473354985527810014620 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 1024 7867241320385539702560 7606113665142270312060 secondAdaptiveJoined_40960_1024 secondAdaptiveJoined_41984_1024

private theorem secondAdaptiveJoined_43008_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 2048 = 14383620867267604106916 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 1024 7333463962793643626472 7050156904473960480444 secondAdaptiveJoined_43008_1024 secondAdaptiveJoined_44032_1024

private theorem secondAdaptiveJoined_45056_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 = 13212086665736053222584 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 1024 6757057181310095875656 6455029484425957346928 secondAdaptiveJoined_45056_1024 secondAdaptiveJoined_46080_1024

private theorem secondAdaptiveJoined_47104_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 2048 = 11972587438960298543412 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 1024 6144938504949908958852 5827648934010389584560 secondAdaptiveJoined_47104_1024 secondAdaptiveJoined_48128_1024

private theorem secondAdaptiveJoined_49152_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 = 10678958244990869050812 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 1024 5504025462735860573748 5174932782255008477064 secondAdaptiveJoined_49152_1024 secondAdaptiveJoined_50176_1024

private theorem secondAdaptiveJoined_51200_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 2048 = 9345034141905648685488 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 1024 4841235583701650934600 4503798558203997750888 secondAdaptiveJoined_51200_1024 secondAdaptiveJoined_52224_1024

private theorem secondAdaptiveJoined_53248_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 = 7984650187759322208120 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 1024 4163486396885353339980 3821163790873968868140 secondAdaptiveJoined_53248_1024 secondAdaptiveJoined_54272_1024

private theorem secondAdaptiveJoined_55296_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 2048 = 6611641440585123098412 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 1024 3477695431298304242736 3133946009286818855676 secondAdaptiveJoined_55296_1024 secondAdaptiveJoined_56320_1024

private theorem secondAdaptiveJoined_57344_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 2048 = 5239842958443458842488 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 1024 2790780215968099935228 2449062742475358907260 secondAdaptiveJoined_57344_1024 secondAdaptiveJoined_58368_1024

private theorem secondAdaptiveJoined_59392_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 2048 = 3897400046576296551396 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 59392 1024 1024 2110004818739525866860 1787395227836770684536 secondAdaptiveJoined_59392_1024 secondAdaptiveJoined_60416_1024

private theorem secondAdaptiveJoined_61440_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 2048 = 2739612859281382884360 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 1024 1024 1497989702940772379688 1241623156340610504672 secondAdaptiveJoined_61440_1024 secondAdaptiveJoined_62464_1024

private theorem secondAdaptiveJoined_63488_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 2048 = 1836406241260694967144 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 63488 1024 1024 1016323311127575213624 820082930133119753520 secondAdaptiveJoined_63488_1024 secondAdaptiveJoined_64512_1024

private theorem secondAdaptiveJoined_65536_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 2048 = 1157646388328586940368 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 1024 1024 650894776192425550044 506751612136161390324 secondAdaptiveJoined_65536_1024 secondAdaptiveJoined_66560_1024

private theorem secondAdaptiveJoined_67584_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 2048 = 671217505777967517324 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 67584 1024 1024 385646200790681609184 285571304987285908140 secondAdaptiveJoined_67584_1024 secondAdaptiveJoined_68608_1024

private theorem secondAdaptiveJoined_69632_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 2048 = 345003798889814685444 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 1024 1024 204519687557396362236 140484111332418323208 secondAdaptiveJoined_69632_1024 secondAdaptiveJoined_70656_1024

private theorem secondAdaptiveJoined_71680_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 2048 = 146889472968584357700 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 71680 1024 1024 91457339143770516408 55432133824813841292 secondAdaptiveJoined_71680_1024 secondAdaptiveJoined_72704_1024

private theorem secondAdaptiveJoined_73728_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 2048 = 44758733318757644280 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 1024 1024 30401258205035590440 14357475113722053840 secondAdaptiveJoined_73728_1024 secondAdaptiveJoined_74752_1024

private theorem secondAdaptiveJoined_75776_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 2048 = 6495785224450627296 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 75776 1024 1024 5293547382294328116 1202237842156299180 secondAdaptiveJoined_75776_1024 secondAdaptiveJoined_76800_1024

private theorem secondAdaptiveJoined_00000_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 = 6032173926535502821212 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 2048 1654183070118414014280 4377990856417088806932 secondAdaptiveJoined_00000_2048 secondAdaptiveJoined_02048_2048

private theorem secondAdaptiveJoined_04096_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 4096 = 16032926825854648908060 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 2048 6878179081246587040296 9154747744608061867764 secondAdaptiveJoined_04096_2048 secondAdaptiveJoined_06144_2048

private theorem secondAdaptiveJoined_08192_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 = 24244723233524866926096 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 2048 11207696846530352169984 13037026386994514756112 secondAdaptiveJoined_08192_2048 secondAdaptiveJoined_10240_2048

private theorem secondAdaptiveJoined_12288_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 4096 = 30667563149513284521072 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 2048 14642736365988454155192 16024826783524830365880 secondAdaptiveJoined_12288_2048 secondAdaptiveJoined_14336_2048

private theorem secondAdaptiveJoined_16384_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 = 35301446573871936225432 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 2048 17183297639621665131096 18118148934250271094336 secondAdaptiveJoined_16384_2048 secondAdaptiveJoined_18432_2048

private theorem secondAdaptiveJoined_20480_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 4096 = 38146556615424799996344 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 2048 18829380667409843146308 19317175948014956850036 secondAdaptiveJoined_20480_2048 secondAdaptiveJoined_22528_2048

private theorem secondAdaptiveJoined_24576_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 = 39235164570875359336656 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 2048 19586217966404024280300 19648946604471335056356 secondAdaptiveJoined_24576_2048 secondAdaptiveJoined_26624_2048

private theorem secondAdaptiveJoined_28672_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 4096 = 38729991990274955746956 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 2048 19519194694801807308708 19210797295473148438248 secondAdaptiveJoined_28672_2048 secondAdaptiveJoined_30720_2048

private theorem secondAdaptiveJoined_32768_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 = 36850995724481446890996 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 2048 18737589464511609140364 18113406259969837750632 secondAdaptiveJoined_32768_2048 secondAdaptiveJoined_34816_2048

private theorem secondAdaptiveJoined_36864_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 4096 = 33819536702364164265972 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 2048 17352082739928521864220 16467453962435642401752 secondAdaptiveJoined_36864_2048 secondAdaptiveJoined_38912_2048

private theorem secondAdaptiveJoined_40960_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 = 29856975852795414121536 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 2048 15473354985527810014620 14383620867267604106916 secondAdaptiveJoined_40960_2048 secondAdaptiveJoined_43008_2048

private theorem secondAdaptiveJoined_45056_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 4096 = 25184674104696351765996 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 2048 13212086665736053222584 11972587438960298543412 secondAdaptiveJoined_45056_2048 secondAdaptiveJoined_47104_2048

private theorem secondAdaptiveJoined_49152_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 = 20023992386896517736300 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 2048 10678958244990869050812 9345034141905648685488 secondAdaptiveJoined_49152_2048 secondAdaptiveJoined_51200_2048

private theorem secondAdaptiveJoined_53248_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 4096 = 14596291628344445306532 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 2048 7984650187759322208120 6611641440585123098412 secondAdaptiveJoined_53248_2048 secondAdaptiveJoined_55296_2048

private theorem secondAdaptiveJoined_57344_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 4096 = 9137243005019755393884 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 2048 2048 5239842958443458842488 3897400046576296551396 secondAdaptiveJoined_57344_2048 secondAdaptiveJoined_59392_2048

private theorem secondAdaptiveJoined_61440_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 4096 = 4576019100542077851504 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 2048 2048 2739612859281382884360 1836406241260694967144 secondAdaptiveJoined_61440_2048 secondAdaptiveJoined_63488_2048

private theorem secondAdaptiveJoined_65536_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 4096 = 1828863894106554457692 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 2048 2048 1157646388328586940368 671217505777967517324 secondAdaptiveJoined_65536_2048 secondAdaptiveJoined_67584_2048

private theorem secondAdaptiveJoined_69632_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 4096 = 491893271858399043144 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 2048 2048 345003798889814685444 146889472968584357700 secondAdaptiveJoined_69632_2048 secondAdaptiveJoined_71680_2048

private theorem secondAdaptiveJoined_73728_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 4096 = 51254518543208271576 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 2048 2048 44758733318757644280 6495785224450627296 secondAdaptiveJoined_73728_2048 secondAdaptiveJoined_75776_2048

private theorem secondAdaptiveJoined_00000_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 = 22065100752390151729272 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 4096 6032173926535502821212 16032926825854648908060 secondAdaptiveJoined_00000_4096 secondAdaptiveJoined_04096_4096

private theorem secondAdaptiveJoined_08192_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 8192 = 54912286383038151447168 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 4096 24244723233524866926096 30667563149513284521072 secondAdaptiveJoined_08192_4096 secondAdaptiveJoined_12288_4096

private theorem secondAdaptiveJoined_16384_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 = 73448003189296736221776 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 4096 35301446573871936225432 38146556615424799996344 secondAdaptiveJoined_16384_4096 secondAdaptiveJoined_20480_4096

private theorem secondAdaptiveJoined_24576_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 8192 = 77965156561150315083612 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 4096 39235164570875359336656 38729991990274955746956 secondAdaptiveJoined_24576_4096 secondAdaptiveJoined_28672_4096

private theorem secondAdaptiveJoined_32768_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 = 70670532426845611156968 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 4096 36850995724481446890996 33819536702364164265972 secondAdaptiveJoined_32768_4096 secondAdaptiveJoined_36864_4096

private theorem secondAdaptiveJoined_40960_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 8192 = 55041649957491765887532 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 4096 29856975852795414121536 25184674104696351765996 secondAdaptiveJoined_40960_4096 secondAdaptiveJoined_45056_4096

private theorem secondAdaptiveJoined_49152_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 = 34620284015240963042832 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 4096 20023992386896517736300 14596291628344445306532 secondAdaptiveJoined_49152_4096 secondAdaptiveJoined_53248_4096

private theorem secondAdaptiveJoined_57344_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 8192 = 13713262105561833245388 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 4096 4096 9137243005019755393884 4576019100542077851504 secondAdaptiveJoined_57344_4096 secondAdaptiveJoined_61440_4096

private theorem secondAdaptiveJoined_65536_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 8192 = 2320757165964953500836 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 4096 4096 1828863894106554457692 491893271858399043144 secondAdaptiveJoined_65536_4096 secondAdaptiveJoined_69632_4096

private theorem secondAdaptiveJoined_73728_5088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 5088 = 51330827889455192496 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 4096 992 51254518543208271576 76309346246920920 secondAdaptiveJoined_73728_4096 secondAdaptiveJoined_77824_992

private theorem secondAdaptiveJoined_00000_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 = 76977387135428303176440 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 8192 22065100752390151729272 54912286383038151447168 secondAdaptiveJoined_00000_8192 secondAdaptiveJoined_08192_8192

private theorem secondAdaptiveJoined_16384_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 16384 = 151413159750447051305388 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 8192 73448003189296736221776 77965156561150315083612 secondAdaptiveJoined_16384_8192 secondAdaptiveJoined_24576_8192

private theorem secondAdaptiveJoined_32768_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 = 125712182384337377044500 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 8192 70670532426845611156968 55041649957491765887532 secondAdaptiveJoined_32768_8192 secondAdaptiveJoined_40960_8192

private theorem secondAdaptiveJoined_49152_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 16384 = 48333546120802796288220 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 8192 34620284015240963042832 13713262105561833245388 secondAdaptiveJoined_49152_8192 secondAdaptiveJoined_57344_8192

private theorem secondAdaptiveJoined_65536_13280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 13280 = 2372087993854408693332 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 8192 5088 2320757165964953500836 51330827889455192496 secondAdaptiveJoined_65536_8192 secondAdaptiveJoined_73728_5088

private theorem secondAdaptiveJoined_00000_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 = 228390546885875354481828 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 16384 76977387135428303176440 151413159750447051305388 secondAdaptiveJoined_00000_16384 secondAdaptiveJoined_16384_16384

private theorem secondAdaptiveJoined_32768_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 32768 = 174045728505140173332720 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 16384 125712182384337377044500 48333546120802796288220 secondAdaptiveJoined_32768_16384 secondAdaptiveJoined_49152_16384

private theorem secondAdaptiveJoined_00000_65536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 65536 = 402436275391015527814548 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 32768 228390546885875354481828 174045728505140173332720 secondAdaptiveJoined_00000_32768 secondAdaptiveJoined_32768_32768

private theorem secondAdaptiveJoined_00000_78816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 78816 = 404808363384869936507880 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 65536 13280 402436275391015527814548 2372087993854408693332 secondAdaptiveJoined_00000_65536 secondAdaptiveJoined_65536_13280

theorem secondAdaptive_firstJetGap_eq : firstJetGap secondAdaptiveShape 0 = secondAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondAdaptiveShape 0 78816 404808363384869936507880 rfl secondAdaptiveJoined_00000_78816]
  decide +kernel

end ProximityPrize.SubmissionLower.Koala6844Receipts






namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle01_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle01_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle01_sliceWindow f a b = x) (hy : arithBundle01_sliceWindow f (a+b) c = y) :
    arithBundle01_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle01_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle01_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle01_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle01_sliceWindow,Nat.zero_add]

private theorem arithBundle01_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle01_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle01_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle01_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle01_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle01_ordinary_columns : ordinaryColumnCount contact01 = 2367601771010451 := by decide +kernel
private theorem arithBundle01_columns_000 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 4 = 7339368721456 :=
  contactColumnsWindow_fast contact01 0 4 7339368721456 (by decide +kernel)
private theorem arithBundle01_columns_004 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 4 4 = 6990142830320 :=
  contactColumnsWindow_fast contact01 4 4 6990142830320 (by decide +kernel)
private theorem arithBundle01_columns_008 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 8 4 = 6649459806972 :=
  contactColumnsWindow_fast contact01 8 4 6649459806972 (by decide +kernel)
private theorem arithBundle01_columns_012 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 12 4 = 6317319766524 :=
  contactColumnsWindow_fast contact01 12 4 6317319766524 (by decide +kernel)
private theorem arithBundle01_columns_016 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 16 4 = 5993754154332 :=
  contactColumnsWindow_fast contact01 16 4 5993754154332 (by decide +kernel)
private theorem arithBundle01_columns_020 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 20 4 = 5678750843771 :=
  contactColumnsWindow_fast contact01 20 4 5678750843771 (by decide +kernel)
private theorem arithBundle01_columns_024 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 24 4 = 5372294119576 :=
  contactColumnsWindow_fast contact01 24 4 5372294119576 (by decide +kernel)
private theorem arithBundle01_columns_028 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 28 4 = 5074382544648 :=
  contactColumnsWindow_fast contact01 28 4 5074382544648 (by decide +kernel)
private theorem arithBundle01_columns_032 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 32 4 = 4785018888076 :=
  contactColumnsWindow_fast contact01 32 4 4785018888076 (by decide +kernel)
private theorem arithBundle01_columns_036 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 36 4 = 4504233870730 :=
  contactColumnsWindow_fast contact01 36 4 4504233870730 (by decide +kernel)
private theorem arithBundle01_columns_040 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 40 4 = 4232012381793 :=
  contactColumnsWindow_fast contact01 40 4 4232012381793 (by decide +kernel)
private theorem arithBundle01_columns_044 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 44 4 = 3968339301873 :=
  contactColumnsWindow_fast contact01 44 4 3968339301873 (by decide +kernel)
private theorem arithBundle01_columns_048 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 48 4 = 3713215905316 :=
  contactColumnsWindow_fast contact01 48 4 3713215905316 (by decide +kernel)
private theorem arithBundle01_columns_052 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 52 4 = 3466643551437 :=
  contactColumnsWindow_fast contact01 52 4 3466643551437 (by decide +kernel)
private theorem arithBundle01_columns_056 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 56 4 = 3228656416525 :=
  contactColumnsWindow_fast contact01 56 4 3228656416525 (by decide +kernel)
private theorem arithBundle01_columns_060 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 60 4 = 2999232621202 :=
  contactColumnsWindow_fast contact01 60 4 2999232621202 (by decide +kernel)
private theorem arithBundle01_columns_064 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 64 4 = 2778360792519 :=
  contactColumnsWindow_fast contact01 64 4 2778360792519 (by decide +kernel)
private theorem arithBundle01_columns_068 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 68 4 = 2566038592180 :=
  contactColumnsWindow_fast contact01 68 4 2566038592180 (by decide +kernel)
private theorem arithBundle01_columns_072 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 72 4 = 2362269112780 :=
  contactColumnsWindow_fast contact01 72 4 2362269112780 (by decide +kernel)
private theorem arithBundle01_columns_076 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 76 4 = 2167086221877 :=
  contactColumnsWindow_fast contact01 76 4 2167086221877 (by decide +kernel)
private theorem arithBundle01_columns_080 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 80 4 = 1980464172430 :=
  contactColumnsWindow_fast contact01 80 4 1980464172430 (by decide +kernel)
private theorem arithBundle01_columns_084 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 84 4 = 1802393578509 :=
  contactColumnsWindow_fast contact01 84 4 1802393578509 (by decide +kernel)
private theorem arithBundle01_columns_088 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 88 4 = 1632872642794 :=
  contactColumnsWindow_fast contact01 88 4 1632872642794 (by decide +kernel)
private theorem arithBundle01_columns_092 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 92 4 = 1471906811020 :=
  contactColumnsWindow_fast contact01 92 4 1471906811020 (by decide +kernel)
private theorem arithBundle01_columns_096 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 96 4 = 1319527322979 :=
  contactColumnsWindow_fast contact01 96 4 1319527322979 (by decide +kernel)
private theorem arithBundle01_columns_100 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 100 4 = 1175707030177 :=
  contactColumnsWindow_fast contact01 100 4 1175707030177 (by decide +kernel)
private theorem arithBundle01_columns_104 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 104 4 = 1040437857886 :=
  contactColumnsWindow_fast contact01 104 4 1040437857886 (by decide +kernel)
private theorem arithBundle01_columns_108 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 108 4 = 913718045614 :=
  contactColumnsWindow_fast contact01 108 4 913718045614 (by decide +kernel)
private theorem arithBundle01_columns_112 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 112 4 = 795555804604 :=
  contactColumnsWindow_fast contact01 112 4 795555804604 (by decide +kernel)
private theorem arithBundle01_columns_116 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 116 4 = 685979920846 :=
  contactColumnsWindow_fast contact01 116 4 685979920846 (by decide +kernel)
private theorem arithBundle01_columns_120 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 120 4 = 584961292543 :=
  contactColumnsWindow_fast contact01 120 4 584961292543 (by decide +kernel)
private theorem arithBundle01_columns_124 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 124 4 = 492493480282 :=
  contactColumnsWindow_fast contact01 124 4 492493480282 (by decide +kernel)
private theorem arithBundle01_columns_128 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 128 4 = 408574794789 :=
  contactColumnsWindow_fast contact01 128 4 408574794789 (by decide +kernel)
private theorem arithBundle01_columns_132 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 132 4 = 333216865612 :=
  contactColumnsWindow_fast contact01 132 4 333216865612 (by decide +kernel)
private theorem arithBundle01_columns_136 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 136 4 = 266443993258 :=
  contactColumnsWindow_fast contact01 136 4 266443993258 (by decide +kernel)
private theorem arithBundle01_columns_140 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 140 4 = 208225289156 :=
  contactColumnsWindow_fast contact01 140 4 208225289156 (by decide +kernel)
private theorem arithBundle01_columns_144 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 144 4 = 158499628599 :=
  contactColumnsWindow_fast contact01 144 4 158499628599 (by decide +kernel)
private theorem arithBundle01_columns_148 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 148 4 = 117024581113 :=
  contactColumnsWindow_fast contact01 148 4 117024581113 (by decide +kernel)
private theorem arithBundle01_columns_152 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 152 4 = 83393755507 :=
  contactColumnsWindow_fast contact01 152 4 83393755507 (by decide +kernel)
private theorem arithBundle01_columns_156 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 156 4 = 57041333654 :=
  contactColumnsWindow_fast contact01 156 4 57041333654 (by decide +kernel)
private theorem arithBundle01_columns_160 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 160 4 = 37193031032 :=
  contactColumnsWindow_fast contact01 160 4 37193031032 (by decide +kernel)
private theorem arithBundle01_columns_164 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 164 4 = 22939196028 :=
  contactColumnsWindow_fast contact01 164 4 22939196028 (by decide +kernel)
private theorem arithBundle01_columns_168 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 168 3 = 10630752089 :=
  contactColumnsWindow_fast contact01 168 3 10630752089 (by decide +kernel)
private theorem arithBundle01_prefix_columns_00 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 8 = 14329511551776 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 4 4 7339368721456 6990142830320 arithBundle01_columns_000 arithBundle01_columns_004
private theorem arithBundle01_prefix_columns_01 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 12 = 20978971358748 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 8 4 14329511551776 6649459806972 arithBundle01_prefix_columns_00 arithBundle01_columns_008
private theorem arithBundle01_prefix_columns_02 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 16 = 27296291125272 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 12 4 20978971358748 6317319766524 arithBundle01_prefix_columns_01 arithBundle01_columns_012
private theorem arithBundle01_prefix_columns_03 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 20 = 33290045279604 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 16 4 27296291125272 5993754154332 arithBundle01_prefix_columns_02 arithBundle01_columns_016
private theorem arithBundle01_prefix_columns_04 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 24 = 38968796123375 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 20 4 33290045279604 5678750843771 arithBundle01_prefix_columns_03 arithBundle01_columns_020
private theorem arithBundle01_prefix_columns_05 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 28 = 44341090242951 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 24 4 38968796123375 5372294119576 arithBundle01_prefix_columns_04 arithBundle01_columns_024
private theorem arithBundle01_prefix_columns_06 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 32 = 49415472787599 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 28 4 44341090242951 5074382544648 arithBundle01_prefix_columns_05 arithBundle01_columns_028
private theorem arithBundle01_prefix_columns_07 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 36 = 54200491675675 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 32 4 49415472787599 4785018888076 arithBundle01_prefix_columns_06 arithBundle01_columns_032
private theorem arithBundle01_prefix_columns_08 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 40 = 58704725546405 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 36 4 54200491675675 4504233870730 arithBundle01_prefix_columns_07 arithBundle01_columns_036
private theorem arithBundle01_prefix_columns_09 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 44 = 62936737928198 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 40 4 58704725546405 4232012381793 arithBundle01_prefix_columns_08 arithBundle01_columns_040
private theorem arithBundle01_prefix_columns_10 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 48 = 66905077230071 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 44 4 62936737928198 3968339301873 arithBundle01_prefix_columns_09 arithBundle01_columns_044
private theorem arithBundle01_prefix_columns_11 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 52 = 70618293135387 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 48 4 66905077230071 3713215905316 arithBundle01_prefix_columns_10 arithBundle01_columns_048
private theorem arithBundle01_prefix_columns_12 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 56 = 74084936686824 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 52 4 70618293135387 3466643551437 arithBundle01_prefix_columns_11 arithBundle01_columns_052
private theorem arithBundle01_prefix_columns_13 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 60 = 77313593103349 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 56 4 74084936686824 3228656416525 arithBundle01_prefix_columns_12 arithBundle01_columns_056
private theorem arithBundle01_prefix_columns_14 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 64 = 80312825724551 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 60 4 77313593103349 2999232621202 arithBundle01_prefix_columns_13 arithBundle01_columns_060
private theorem arithBundle01_prefix_columns_15 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 68 = 83091186517070 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 64 4 80312825724551 2778360792519 arithBundle01_prefix_columns_14 arithBundle01_columns_064
private theorem arithBundle01_prefix_columns_16 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 72 = 85657225109250 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 68 4 83091186517070 2566038592180 arithBundle01_prefix_columns_15 arithBundle01_columns_068
private theorem arithBundle01_prefix_columns_17 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 76 = 88019494222030 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 72 4 85657225109250 2362269112780 arithBundle01_prefix_columns_16 arithBundle01_columns_072
private theorem arithBundle01_prefix_columns_18 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 80 = 90186580443907 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 76 4 88019494222030 2167086221877 arithBundle01_prefix_columns_17 arithBundle01_columns_076
private theorem arithBundle01_prefix_columns_19 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 84 = 92167044616337 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 80 4 90186580443907 1980464172430 arithBundle01_prefix_columns_18 arithBundle01_columns_080
private theorem arithBundle01_prefix_columns_20 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 88 = 93969438194846 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 84 4 92167044616337 1802393578509 arithBundle01_prefix_columns_19 arithBundle01_columns_084
private theorem arithBundle01_prefix_columns_21 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 92 = 95602310837640 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 88 4 93969438194846 1632872642794 arithBundle01_prefix_columns_20 arithBundle01_columns_088
private theorem arithBundle01_prefix_columns_22 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 96 = 97074217648660 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 92 4 95602310837640 1471906811020 arithBundle01_prefix_columns_21 arithBundle01_columns_092
private theorem arithBundle01_prefix_columns_23 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 100 = 98393744971639 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 96 4 97074217648660 1319527322979 arithBundle01_prefix_columns_22 arithBundle01_columns_096
private theorem arithBundle01_prefix_columns_24 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 104 = 99569452001816 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 100 4 98393744971639 1175707030177 arithBundle01_prefix_columns_23 arithBundle01_columns_100
private theorem arithBundle01_prefix_columns_25 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 108 = 100609889859702 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 104 4 99569452001816 1040437857886 arithBundle01_prefix_columns_24 arithBundle01_columns_104
private theorem arithBundle01_prefix_columns_26 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 112 = 101523607905316 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 108 4 100609889859702 913718045614 arithBundle01_prefix_columns_25 arithBundle01_columns_108
private theorem arithBundle01_prefix_columns_27 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 116 = 102319163709920 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 112 4 101523607905316 795555804604 arithBundle01_prefix_columns_26 arithBundle01_columns_112
private theorem arithBundle01_prefix_columns_28 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 120 = 103005143630766 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 116 4 102319163709920 685979920846 arithBundle01_prefix_columns_27 arithBundle01_columns_116
private theorem arithBundle01_prefix_columns_29 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 124 = 103590104923309 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 120 4 103005143630766 584961292543 arithBundle01_prefix_columns_28 arithBundle01_columns_120
private theorem arithBundle01_prefix_columns_30 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 128 = 104082598403591 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 124 4 103590104923309 492493480282 arithBundle01_prefix_columns_29 arithBundle01_columns_124
private theorem arithBundle01_prefix_columns_31 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 132 = 104491173198380 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 128 4 104082598403591 408574794789 arithBundle01_prefix_columns_30 arithBundle01_columns_128
private theorem arithBundle01_prefix_columns_32 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 136 = 104824390063992 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 132 4 104491173198380 333216865612 arithBundle01_prefix_columns_31 arithBundle01_columns_132
private theorem arithBundle01_prefix_columns_33 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 140 = 105090834057250 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 136 4 104824390063992 266443993258 arithBundle01_prefix_columns_32 arithBundle01_columns_136
private theorem arithBundle01_prefix_columns_34 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 144 = 105299059346406 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 140 4 105090834057250 208225289156 arithBundle01_prefix_columns_33 arithBundle01_columns_140
private theorem arithBundle01_prefix_columns_35 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 148 = 105457558975005 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 144 4 105299059346406 158499628599 arithBundle01_prefix_columns_34 arithBundle01_columns_144
private theorem arithBundle01_prefix_columns_36 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 152 = 105574583556118 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 148 4 105457558975005 117024581113 arithBundle01_prefix_columns_35 arithBundle01_columns_148
private theorem arithBundle01_prefix_columns_37 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 156 = 105657977311625 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 152 4 105574583556118 83393755507 arithBundle01_prefix_columns_36 arithBundle01_columns_152
private theorem arithBundle01_prefix_columns_38 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 160 = 105715018645279 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 156 4 105657977311625 57041333654 arithBundle01_prefix_columns_37 arithBundle01_columns_156
private theorem arithBundle01_prefix_columns_39 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 164 = 105752211676311 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 160 4 105715018645279 37193031032 arithBundle01_prefix_columns_38 arithBundle01_columns_160
private theorem arithBundle01_prefix_columns_40 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 168 = 105775150872339 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 164 4 105752211676311 22939196028 arithBundle01_prefix_columns_39 arithBundle01_columns_164
private theorem arithBundle01_prefix_columns_41 : arithBundle01_sliceWindow (auxiliaryColumnSlice contact01) 0 171 = 105785781624428 :=
  arithBundle01_combineSlices (auxiliaryColumnSlice contact01) 0 168 3 105775150872339 10630752089 arithBundle01_prefix_columns_40 arithBundle01_columns_168

private theorem arithBundle01_ordinary_ranks : ordinaryRankBound contact01 = 9116253959 := by decide +kernel
private theorem arithBundle01_ranks_000 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 4 = 27670216 :=
  contactRankWindow_of_rec contact01 0 4 27670216 (by decide +kernel)
private theorem arithBundle01_ranks_004 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 4 4 = 25947880 :=
  contactRankWindow_of_rec contact01 4 4 25947880 (by decide +kernel)
private theorem arithBundle01_ranks_008 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 8 4 = 24284680 :=
  contactRankWindow_of_rec contact01 8 4 24284680 (by decide +kernel)
private theorem arithBundle01_ranks_012 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 12 4 = 22680616 :=
  contactRankWindow_of_rec contact01 12 4 22680616 (by decide +kernel)
private theorem arithBundle01_ranks_016 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 16 4 = 21135688 :=
  contactRankWindow_of_rec contact01 16 4 21135688 (by decide +kernel)
private theorem arithBundle01_ranks_020 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 20 4 = 19649896 :=
  contactRankWindow_of_rec contact01 20 4 19649896 (by decide +kernel)
private theorem arithBundle01_ranks_024 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 24 4 = 18223240 :=
  contactRankWindow_of_rec contact01 24 4 18223240 (by decide +kernel)
private theorem arithBundle01_ranks_028 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 28 4 = 16855720 :=
  contactRankWindow_of_rec contact01 28 4 16855720 (by decide +kernel)
private theorem arithBundle01_ranks_032 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 32 4 = 15547336 :=
  contactRankWindow_of_rec contact01 32 4 15547336 (by decide +kernel)
private theorem arithBundle01_ranks_036 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 36 4 = 14298088 :=
  contactRankWindow_of_rec contact01 36 4 14298088 (by decide +kernel)
private theorem arithBundle01_ranks_040 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 40 4 = 13107976 :=
  contactRankWindow_of_rec contact01 40 4 13107976 (by decide +kernel)
private theorem arithBundle01_ranks_044 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 44 4 = 11977000 :=
  contactRankWindow_of_rec contact01 44 4 11977000 (by decide +kernel)
private theorem arithBundle01_ranks_048 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 48 4 = 10905160 :=
  contactRankWindow_of_rec contact01 48 4 10905160 (by decide +kernel)
private theorem arithBundle01_ranks_052 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 52 4 = 9892456 :=
  contactRankWindow_of_rec contact01 52 4 9892456 (by decide +kernel)
private theorem arithBundle01_ranks_056 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 56 4 = 8938888 :=
  contactRankWindow_of_rec contact01 56 4 8938888 (by decide +kernel)
private theorem arithBundle01_ranks_060 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 60 4 = 8044062 :=
  contactRankWindow_of_rec contact01 60 4 8044062 (by decide +kernel)
private theorem arithBundle01_ranks_064 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 64 4 = 7206864 :=
  contactRankWindow_of_rec contact01 64 4 7206864 (by decide +kernel)
private theorem arithBundle01_ranks_068 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 68 4 = 6426007 :=
  contactRankWindow_of_rec contact01 68 4 6426007 (by decide +kernel)
private theorem arithBundle01_ranks_072 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 72 4 = 5699924 :=
  contactRankWindow_of_rec contact01 72 4 5699924 (by decide +kernel)
private theorem arithBundle01_ranks_076 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 76 4 = 5026868 :=
  contactRankWindow_of_rec contact01 76 4 5026868 (by decide +kernel)
private theorem arithBundle01_ranks_080 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 80 4 = 4405039 :=
  contactRankWindow_of_rec contact01 80 4 4405039 (by decide +kernel)
private theorem arithBundle01_ranks_084 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 84 4 = 3832868 :=
  contactRankWindow_of_rec contact01 84 4 3832868 (by decide +kernel)
private theorem arithBundle01_ranks_088 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 88 4 = 3308472 :=
  contactRankWindow_of_rec contact01 88 4 3308472 (by decide +kernel)
private theorem arithBundle01_ranks_092 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 92 4 = 2830055 :=
  contactRankWindow_of_rec contact01 92 4 2830055 (by decide +kernel)
private theorem arithBundle01_ranks_096 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 96 4 = 2396180 :=
  contactRankWindow_of_rec contact01 96 4 2396180 (by decide +kernel)
private theorem arithBundle01_ranks_100 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 100 4 = 2004828 :=
  contactRankWindow_of_rec contact01 100 4 2004828 (by decide +kernel)
private theorem arithBundle01_ranks_104 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 104 4 = 1654207 :=
  contactRankWindow_of_rec contact01 104 4 1654207 (by decide +kernel)
private theorem arithBundle01_ranks_108 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 108 4 = 1343012 :=
  contactRankWindow_of_rec contact01 108 4 1343012 (by decide +kernel)
private theorem arithBundle01_ranks_112 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 112 4 = 1069088 :=
  contactRankWindow_of_rec contact01 112 4 1069088 (by decide +kernel)
private theorem arithBundle01_ranks_116 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 116 4 = 830647 :=
  contactRankWindow_of_rec contact01 116 4 830647 (by decide +kernel)
private theorem arithBundle01_ranks_120 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 120 4 = 626516 :=
  contactRankWindow_of_rec contact01 120 4 626516 (by decide +kernel)
private theorem arithBundle01_ranks_124 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 124 4 = 454404 :=
  contactRankWindow_of_rec contact01 124 4 454404 (by decide +kernel)
private theorem arithBundle01_ranks_128 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 128 4 = 312527 :=
  contactRankWindow_of_rec contact01 128 4 312527 (by decide +kernel)
private theorem arithBundle01_ranks_132 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 132 4 = 199844 :=
  contactRankWindow_of_rec contact01 132 4 199844 (by decide +kernel)
private theorem arithBundle01_ranks_136 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 136 4 = 113928 :=
  contactRankWindow_of_rec contact01 136 4 113928 (by decide +kernel)
private theorem arithBundle01_ranks_140 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 140 4 = 52999 :=
  contactRankWindow_of_rec contact01 140 4 52999 (by decide +kernel)
private theorem arithBundle01_ranks_144 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 144 4 = 16157 :=
  contactRankWindow_of_rec contact01 144 4 16157 (by decide +kernel)
private theorem arithBundle01_ranks_148 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 148 4 = 914 :=
  contactRankWindow_of_rec contact01 148 4 914 (by decide +kernel)
private theorem arithBundle01_ranks_152 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 152 19 = 0 :=
  contactRankWindow_of_rec contact01 152 19 0 (by decide +kernel)
private theorem arithBundle01_prefix_ranks_00 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 8 = 53618096 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 4 4 27670216 25947880 arithBundle01_ranks_000 arithBundle01_ranks_004
private theorem arithBundle01_prefix_ranks_01 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 12 = 77902776 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 8 4 53618096 24284680 arithBundle01_prefix_ranks_00 arithBundle01_ranks_008
private theorem arithBundle01_prefix_ranks_02 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 16 = 100583392 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 12 4 77902776 22680616 arithBundle01_prefix_ranks_01 arithBundle01_ranks_012
private theorem arithBundle01_prefix_ranks_03 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 20 = 121719080 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 16 4 100583392 21135688 arithBundle01_prefix_ranks_02 arithBundle01_ranks_016
private theorem arithBundle01_prefix_ranks_04 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 24 = 141368976 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 20 4 121719080 19649896 arithBundle01_prefix_ranks_03 arithBundle01_ranks_020
private theorem arithBundle01_prefix_ranks_05 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 28 = 159592216 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 24 4 141368976 18223240 arithBundle01_prefix_ranks_04 arithBundle01_ranks_024
private theorem arithBundle01_prefix_ranks_06 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 32 = 176447936 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 28 4 159592216 16855720 arithBundle01_prefix_ranks_05 arithBundle01_ranks_028
private theorem arithBundle01_prefix_ranks_07 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 36 = 191995272 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 32 4 176447936 15547336 arithBundle01_prefix_ranks_06 arithBundle01_ranks_032
private theorem arithBundle01_prefix_ranks_08 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 40 = 206293360 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 36 4 191995272 14298088 arithBundle01_prefix_ranks_07 arithBundle01_ranks_036
private theorem arithBundle01_prefix_ranks_09 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 44 = 219401336 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 40 4 206293360 13107976 arithBundle01_prefix_ranks_08 arithBundle01_ranks_040
private theorem arithBundle01_prefix_ranks_10 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 48 = 231378336 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 44 4 219401336 11977000 arithBundle01_prefix_ranks_09 arithBundle01_ranks_044
private theorem arithBundle01_prefix_ranks_11 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 52 = 242283496 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 48 4 231378336 10905160 arithBundle01_prefix_ranks_10 arithBundle01_ranks_048
private theorem arithBundle01_prefix_ranks_12 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 56 = 252175952 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 52 4 242283496 9892456 arithBundle01_prefix_ranks_11 arithBundle01_ranks_052
private theorem arithBundle01_prefix_ranks_13 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 60 = 261114840 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 56 4 252175952 8938888 arithBundle01_prefix_ranks_12 arithBundle01_ranks_056
private theorem arithBundle01_prefix_ranks_14 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 64 = 269158902 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 60 4 261114840 8044062 arithBundle01_prefix_ranks_13 arithBundle01_ranks_060
private theorem arithBundle01_prefix_ranks_15 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 68 = 276365766 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 64 4 269158902 7206864 arithBundle01_prefix_ranks_14 arithBundle01_ranks_064
private theorem arithBundle01_prefix_ranks_16 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 72 = 282791773 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 68 4 276365766 6426007 arithBundle01_prefix_ranks_15 arithBundle01_ranks_068
private theorem arithBundle01_prefix_ranks_17 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 76 = 288491697 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 72 4 282791773 5699924 arithBundle01_prefix_ranks_16 arithBundle01_ranks_072
private theorem arithBundle01_prefix_ranks_18 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 80 = 293518565 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 76 4 288491697 5026868 arithBundle01_prefix_ranks_17 arithBundle01_ranks_076
private theorem arithBundle01_prefix_ranks_19 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 84 = 297923604 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 80 4 293518565 4405039 arithBundle01_prefix_ranks_18 arithBundle01_ranks_080
private theorem arithBundle01_prefix_ranks_20 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 88 = 301756472 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 84 4 297923604 3832868 arithBundle01_prefix_ranks_19 arithBundle01_ranks_084
private theorem arithBundle01_prefix_ranks_21 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 92 = 305064944 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 88 4 301756472 3308472 arithBundle01_prefix_ranks_20 arithBundle01_ranks_088
private theorem arithBundle01_prefix_ranks_22 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 96 = 307894999 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 92 4 305064944 2830055 arithBundle01_prefix_ranks_21 arithBundle01_ranks_092
private theorem arithBundle01_prefix_ranks_23 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 100 = 310291179 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 96 4 307894999 2396180 arithBundle01_prefix_ranks_22 arithBundle01_ranks_096
private theorem arithBundle01_prefix_ranks_24 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 104 = 312296007 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 100 4 310291179 2004828 arithBundle01_prefix_ranks_23 arithBundle01_ranks_100
private theorem arithBundle01_prefix_ranks_25 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 108 = 313950214 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 104 4 312296007 1654207 arithBundle01_prefix_ranks_24 arithBundle01_ranks_104
private theorem arithBundle01_prefix_ranks_26 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 112 = 315293226 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 108 4 313950214 1343012 arithBundle01_prefix_ranks_25 arithBundle01_ranks_108
private theorem arithBundle01_prefix_ranks_27 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 116 = 316362314 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 112 4 315293226 1069088 arithBundle01_prefix_ranks_26 arithBundle01_ranks_112
private theorem arithBundle01_prefix_ranks_28 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 120 = 317192961 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 116 4 316362314 830647 arithBundle01_prefix_ranks_27 arithBundle01_ranks_116
private theorem arithBundle01_prefix_ranks_29 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 124 = 317819477 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 120 4 317192961 626516 arithBundle01_prefix_ranks_28 arithBundle01_ranks_120
private theorem arithBundle01_prefix_ranks_30 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 128 = 318273881 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 124 4 317819477 454404 arithBundle01_prefix_ranks_29 arithBundle01_ranks_124
private theorem arithBundle01_prefix_ranks_31 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 132 = 318586408 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 128 4 318273881 312527 arithBundle01_prefix_ranks_30 arithBundle01_ranks_128
private theorem arithBundle01_prefix_ranks_32 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 136 = 318786252 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 132 4 318586408 199844 arithBundle01_prefix_ranks_31 arithBundle01_ranks_132
private theorem arithBundle01_prefix_ranks_33 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 140 = 318900180 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 136 4 318786252 113928 arithBundle01_prefix_ranks_32 arithBundle01_ranks_136
private theorem arithBundle01_prefix_ranks_34 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 144 = 318953179 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 140 4 318900180 52999 arithBundle01_prefix_ranks_33 arithBundle01_ranks_140
private theorem arithBundle01_prefix_ranks_35 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 148 = 318969336 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 144 4 318953179 16157 arithBundle01_prefix_ranks_34 arithBundle01_ranks_144
private theorem arithBundle01_prefix_ranks_36 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 152 = 318970250 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 148 4 318969336 914 arithBundle01_prefix_ranks_35 arithBundle01_ranks_148
private theorem arithBundle01_prefix_ranks_37 : arithBundle01_sliceWindow (auxiliaryRankSlice contact01) 0 171 = 318970250 :=
  arithBundle01_combineSlices (auxiliaryRankSlice contact01) 0 152 19 318970250 0 arithBundle01_prefix_ranks_36 arithBundle01_ranks_152

theorem contact01_margin : sourceMargin contact01 :=
  arithBundle01_margin_of_checked_counts contact01 171 2367601771010451 105785781624428 9116253959 318970250
    rfl arithBundle01_ordinary_columns arithBundle01_prefix_columns_41 arithBundle01_ordinary_ranks arithBundle01_prefix_ranks_37 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle02_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle02_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle02_sliceWindow f a b = x) (hy : arithBundle02_sliceWindow f (a+b) c = y) :
    arithBundle02_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle02_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle02_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle02_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle02_sliceWindow,Nat.zero_add]

private theorem arithBundle02_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle02_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle02_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle02_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle02_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle02_ordinary_columns : ordinaryColumnCount contact03 = 2204512883741133 := by decide +kernel
private theorem arithBundle02_columns_000 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 4 = 7519419757224 :=
  contactColumnsWindow_fast contact03 0 4 7519419757224 (by decide +kernel)
private theorem arithBundle02_columns_004 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 4 4 = 7160671460072 :=
  contactColumnsWindow_fast contact03 4 4 7160671460072 (by decide +kernel)
private theorem arithBundle02_columns_008 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 8 4 = 6810724883936 :=
  contactColumnsWindow_fast contact03 8 4 6810724883936 (by decide +kernel)
private theorem arithBundle02_columns_012 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 12 4 = 6469580150152 :=
  contactColumnsWindow_fast contact03 12 4 6469580150152 (by decide +kernel)
private theorem arithBundle02_columns_016 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 16 4 = 6137269994672 :=
  contactColumnsWindow_fast contact03 16 4 6137269994672 (by decide +kernel)
private theorem arithBundle02_columns_020 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 20 4 = 5813781769877 :=
  contactColumnsWindow_fast contact03 20 4 5813781769877 (by decide +kernel)
private theorem arithBundle02_columns_024 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 24 4 = 5499099061624 :=
  contactColumnsWindow_fast contact03 24 4 5499099061624 (by decide +kernel)
private theorem arithBundle02_columns_028 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 28 4 = 5193220401962 :=
  contactColumnsWindow_fast contact03 28 4 5193220401962 (by decide +kernel)
private theorem arithBundle02_columns_032 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 32 4 = 4896148638740 :=
  contactColumnsWindow_fast contact03 32 4 4896148638740 (by decide +kernel)
private theorem arithBundle02_columns_036 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 36 4 = 4607915794848 :=
  contactColumnsWindow_fast contact03 36 4 4607915794848 (by decide +kernel)
private theorem arithBundle02_columns_040 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 40 4 = 4328506056012 :=
  contactColumnsWindow_fast contact03 40 4 4328506056012 (by decide +kernel)
private theorem arithBundle02_columns_044 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 44 4 = 4057903688037 :=
  contactColumnsWindow_fast contact03 44 4 4057903688037 (by decide +kernel)
private theorem arithBundle02_columns_048 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 48 4 = 3796109984484 :=
  contactColumnsWindow_fast contact03 48 4 3796109984484 (by decide +kernel)
private theorem arithBundle02_columns_052 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 52 4 = 3543126381285 :=
  contactColumnsWindow_fast contact03 52 4 3543126381285 (by decide +kernel)
private theorem arithBundle02_columns_056 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 56 4 = 3298988445118 :=
  contactColumnsWindow_fast contact03 56 4 3298988445118 (by decide +kernel)
private theorem arithBundle02_columns_060 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 60 4 = 3063673341180 :=
  contactColumnsWindow_fast contact03 60 4 3063673341180 (by decide +kernel)
private theorem arithBundle02_columns_064 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 64 4 = 2837169223443 :=
  contactColumnsWindow_fast contact03 64 4 2837169223443 (by decide +kernel)
private theorem arithBundle02_columns_068 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 68 4 = 2619473714754 :=
  contactColumnsWindow_fast contact03 68 4 2619473714754 (by decide +kernel)
private theorem arithBundle02_columns_072 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 72 4 = 2410590050008 :=
  contactColumnsWindow_fast contact03 72 4 2410590050008 (by decide +kernel)
private theorem arithBundle02_columns_076 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 76 4 = 2210553479041 :=
  contactColumnsWindow_fast contact03 76 4 2210553479041 (by decide +kernel)
private theorem arithBundle02_columns_080 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 80 4 = 2019337129290 :=
  contactColumnsWindow_fast contact03 80 4 2019337129290 (by decide +kernel)
private theorem arithBundle02_columns_084 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 84 4 = 1836931244961 :=
  contactColumnsWindow_fast contact03 84 4 1836931244961 (by decide +kernel)
private theorem arithBundle02_columns_088 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 88 4 = 1663334000831 :=
  contactColumnsWindow_fast contact03 88 4 1663334000831 (by decide +kernel)
private theorem arithBundle02_columns_092 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 92 4 = 1498551077428 :=
  contactColumnsWindow_fast contact03 92 4 1498551077428 (by decide +kernel)
private theorem arithBundle02_columns_096 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 96 4 = 1342614999511 :=
  contactColumnsWindow_fast contact03 96 4 1342614999511 (by decide +kernel)
private theorem arithBundle02_columns_100 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 100 4 = 1195497414885 :=
  contactColumnsWindow_fast contact03 100 4 1195497414885 (by decide +kernel)
private theorem arithBundle02_columns_104 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 104 4 = 1057189954530 :=
  contactColumnsWindow_fast contact03 104 4 1057189954530 (by decide +kernel)
private theorem arithBundle02_columns_108 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 108 4 = 927690831002 :=
  contactColumnsWindow_fast contact03 108 4 927690831002 (by decide +kernel)
private theorem arithBundle02_columns_112 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 112 4 = 807008590960 :=
  contactColumnsWindow_fast contact03 112 4 807008590960 (by decide +kernel)
private theorem arithBundle02_columns_116 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 116 4 = 695173211169 :=
  contactColumnsWindow_fast contact03 116 4 695173211169 (by decide +kernel)
private theorem arithBundle02_columns_120 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 120 4 = 592154298078 :=
  contactColumnsWindow_fast contact03 120 4 592154298078 (by decide +kernel)
private theorem arithBundle02_columns_124 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 124 4 = 497945198808 :=
  contactColumnsWindow_fast contact03 124 4 497945198808 (by decide +kernel)
private theorem arithBundle02_columns_128 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 128 4 = 412544199146 :=
  contactColumnsWindow_fast contact03 128 4 412544199146 (by decide +kernel)
private theorem arithBundle02_columns_132 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 132 4 = 335963393004 :=
  contactColumnsWindow_fast contact03 132 4 335963393004 (by decide +kernel)
private theorem arithBundle02_columns_136 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 136 4 = 268228091712 :=
  contactColumnsWindow_fast contact03 136 4 268228091712 (by decide +kernel)
private theorem arithBundle02_columns_140 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 140 4 = 209302660496 :=
  contactColumnsWindow_fast contact03 140 4 209302660496 (by decide +kernel)
private theorem arithBundle02_columns_144 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 144 4 = 159091311713 :=
  contactColumnsWindow_fast contact03 144 4 159091311713 (by decide +kernel)
private theorem arithBundle02_columns_148 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 148 4 = 117303741020 :=
  contactColumnsWindow_fast contact03 148 4 117303741020 (by decide +kernel)
private theorem arithBundle02_columns_152 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 152 4 = 83496332432 :=
  contactColumnsWindow_fast contact03 152 4 83496332432 (by decide +kernel)
private theorem arithBundle02_columns_156 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 156 4 = 57064579827 :=
  contactColumnsWindow_fast contact03 156 4 57064579827 (by decide +kernel)
private theorem arithBundle02_columns_160 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 160 4 = 37194457297 :=
  contactColumnsWindow_fast contact03 160 4 37194457297 (by decide +kernel)
private theorem arithBundle02_columns_164 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 164 4 = 22939196028 :=
  contactColumnsWindow_fast contact03 164 4 22939196028 (by decide +kernel)
private theorem arithBundle02_columns_168 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 168 1 = 4065131807 :=
  contactColumnsWindow_fast contact03 168 1 4065131807 (by decide +kernel)
private theorem arithBundle02_prefix_columns_00 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 8 = 14680091217296 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 4 4 7519419757224 7160671460072 arithBundle02_columns_000 arithBundle02_columns_004
private theorem arithBundle02_prefix_columns_01 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 12 = 21490816101232 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 8 4 14680091217296 6810724883936 arithBundle02_prefix_columns_00 arithBundle02_columns_008
private theorem arithBundle02_prefix_columns_02 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 16 = 27960396251384 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 12 4 21490816101232 6469580150152 arithBundle02_prefix_columns_01 arithBundle02_columns_012
private theorem arithBundle02_prefix_columns_03 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 20 = 34097666246056 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 16 4 27960396251384 6137269994672 arithBundle02_prefix_columns_02 arithBundle02_columns_016
private theorem arithBundle02_prefix_columns_04 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 24 = 39911448015933 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 20 4 34097666246056 5813781769877 arithBundle02_prefix_columns_03 arithBundle02_columns_020
private theorem arithBundle02_prefix_columns_05 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 28 = 45410547077557 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 24 4 39911448015933 5499099061624 arithBundle02_prefix_columns_04 arithBundle02_columns_024
private theorem arithBundle02_prefix_columns_06 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 32 = 50603767479519 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 28 4 45410547077557 5193220401962 arithBundle02_prefix_columns_05 arithBundle02_columns_028
private theorem arithBundle02_prefix_columns_07 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 36 = 55499916118259 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 32 4 50603767479519 4896148638740 arithBundle02_prefix_columns_06 arithBundle02_columns_032
private theorem arithBundle02_prefix_columns_08 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 40 = 60107831913107 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 36 4 55499916118259 4607915794848 arithBundle02_prefix_columns_07 arithBundle02_columns_036
private theorem arithBundle02_prefix_columns_09 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 44 = 64436337969119 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 40 4 60107831913107 4328506056012 arithBundle02_prefix_columns_08 arithBundle02_columns_040
private theorem arithBundle02_prefix_columns_10 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 48 = 68494241657156 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 44 4 64436337969119 4057903688037 arithBundle02_prefix_columns_09 arithBundle02_columns_044
private theorem arithBundle02_prefix_columns_11 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 52 = 72290351641640 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 48 4 68494241657156 3796109984484 arithBundle02_prefix_columns_10 arithBundle02_columns_048
private theorem arithBundle02_prefix_columns_12 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 56 = 75833478022925 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 52 4 72290351641640 3543126381285 arithBundle02_prefix_columns_11 arithBundle02_columns_052
private theorem arithBundle02_prefix_columns_13 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 60 = 79132466468043 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 56 4 75833478022925 3298988445118 arithBundle02_prefix_columns_12 arithBundle02_columns_056
private theorem arithBundle02_prefix_columns_14 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 64 = 82196139809223 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 60 4 79132466468043 3063673341180 arithBundle02_prefix_columns_13 arithBundle02_columns_060
private theorem arithBundle02_prefix_columns_15 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 68 = 85033309032666 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 64 4 82196139809223 2837169223443 arithBundle02_prefix_columns_14 arithBundle02_columns_064
private theorem arithBundle02_prefix_columns_16 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 72 = 87652782747420 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 68 4 85033309032666 2619473714754 arithBundle02_prefix_columns_15 arithBundle02_columns_068
private theorem arithBundle02_prefix_columns_17 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 76 = 90063372797428 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 72 4 87652782747420 2410590050008 arithBundle02_prefix_columns_16 arithBundle02_columns_072
private theorem arithBundle02_prefix_columns_18 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 80 = 92273926276469 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 76 4 90063372797428 2210553479041 arithBundle02_prefix_columns_17 arithBundle02_columns_076
private theorem arithBundle02_prefix_columns_19 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 84 = 94293263405759 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 80 4 92273926276469 2019337129290 arithBundle02_prefix_columns_18 arithBundle02_columns_080
private theorem arithBundle02_prefix_columns_20 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 88 = 96130194650720 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 84 4 94293263405759 1836931244961 arithBundle02_prefix_columns_19 arithBundle02_columns_084
private theorem arithBundle02_prefix_columns_21 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 92 = 97793528651551 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 88 4 96130194650720 1663334000831 arithBundle02_prefix_columns_20 arithBundle02_columns_088
private theorem arithBundle02_prefix_columns_22 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 96 = 99292079728979 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 92 4 97793528651551 1498551077428 arithBundle02_prefix_columns_21 arithBundle02_columns_092
private theorem arithBundle02_prefix_columns_23 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 100 = 100634694728490 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 96 4 99292079728979 1342614999511 arithBundle02_prefix_columns_22 arithBundle02_columns_096
private theorem arithBundle02_prefix_columns_24 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 104 = 101830192143375 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 100 4 100634694728490 1195497414885 arithBundle02_prefix_columns_23 arithBundle02_columns_100
private theorem arithBundle02_prefix_columns_25 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 108 = 102887382097905 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 104 4 101830192143375 1057189954530 arithBundle02_prefix_columns_24 arithBundle02_columns_104
private theorem arithBundle02_prefix_columns_26 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 112 = 103815072928907 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 108 4 102887382097905 927690831002 arithBundle02_prefix_columns_25 arithBundle02_columns_108
private theorem arithBundle02_prefix_columns_27 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 116 = 104622081519867 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 112 4 103815072928907 807008590960 arithBundle02_prefix_columns_26 arithBundle02_columns_112
private theorem arithBundle02_prefix_columns_28 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 120 = 105317254731036 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 116 4 104622081519867 695173211169 arithBundle02_prefix_columns_27 arithBundle02_columns_116
private theorem arithBundle02_prefix_columns_29 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 124 = 105909409029114 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 120 4 105317254731036 592154298078 arithBundle02_prefix_columns_28 arithBundle02_columns_120
private theorem arithBundle02_prefix_columns_30 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 128 = 106407354227922 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 124 4 105909409029114 497945198808 arithBundle02_prefix_columns_29 arithBundle02_columns_124
private theorem arithBundle02_prefix_columns_31 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 132 = 106819898427068 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 128 4 106407354227922 412544199146 arithBundle02_prefix_columns_30 arithBundle02_columns_128
private theorem arithBundle02_prefix_columns_32 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 136 = 107155861820072 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 132 4 106819898427068 335963393004 arithBundle02_prefix_columns_31 arithBundle02_columns_132
private theorem arithBundle02_prefix_columns_33 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 140 = 107424089911784 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 136 4 107155861820072 268228091712 arithBundle02_prefix_columns_32 arithBundle02_columns_136
private theorem arithBundle02_prefix_columns_34 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 144 = 107633392572280 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 140 4 107424089911784 209302660496 arithBundle02_prefix_columns_33 arithBundle02_columns_140
private theorem arithBundle02_prefix_columns_35 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 148 = 107792483883993 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 144 4 107633392572280 159091311713 arithBundle02_prefix_columns_34 arithBundle02_columns_144
private theorem arithBundle02_prefix_columns_36 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 152 = 107909787625013 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 148 4 107792483883993 117303741020 arithBundle02_prefix_columns_35 arithBundle02_columns_148
private theorem arithBundle02_prefix_columns_37 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 156 = 107993283957445 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 152 4 107909787625013 83496332432 arithBundle02_prefix_columns_36 arithBundle02_columns_152
private theorem arithBundle02_prefix_columns_38 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 160 = 108050348537272 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 156 4 107993283957445 57064579827 arithBundle02_prefix_columns_37 arithBundle02_columns_156
private theorem arithBundle02_prefix_columns_39 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 164 = 108087542994569 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 160 4 108050348537272 37194457297 arithBundle02_prefix_columns_38 arithBundle02_columns_160
private theorem arithBundle02_prefix_columns_40 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 168 = 108110482190597 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 164 4 108087542994569 22939196028 arithBundle02_prefix_columns_39 arithBundle02_columns_164
private theorem arithBundle02_prefix_columns_41 : arithBundle02_sliceWindow (auxiliaryColumnSlice contact03) 0 169 = 108114547322404 :=
  arithBundle02_combineSlices (auxiliaryColumnSlice contact03) 0 168 1 108110482190597 4065131807 arithBundle02_prefix_columns_40 arithBundle02_columns_168

private theorem arithBundle02_ordinary_ranks : ordinaryRankBound contact03 = 8495355080 := by decide +kernel
private theorem arithBundle02_ranks_000 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 4 = 28342844 :=
  contactRankWindow_of_rec contact03 0 4 28342844 (by decide +kernel)
private theorem arithBundle02_ranks_004 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 4 4 = 26575932 :=
  contactRankWindow_of_rec contact03 4 4 26575932 (by decide +kernel)
private theorem arithBundle02_ranks_008 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 8 4 = 24869948 :=
  contactRankWindow_of_rec contact03 8 4 24869948 (by decide +kernel)
private theorem arithBundle02_ranks_012 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 12 4 = 23224892 :=
  contactRankWindow_of_rec contact03 12 4 23224892 (by decide +kernel)
private theorem arithBundle02_ranks_016 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 16 4 = 21640764 :=
  contactRankWindow_of_rec contact03 16 4 21640764 (by decide +kernel)
private theorem arithBundle02_ranks_020 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 20 4 = 20117564 :=
  contactRankWindow_of_rec contact03 20 4 20117564 (by decide +kernel)
private theorem arithBundle02_ranks_024 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 24 4 = 18655292 :=
  contactRankWindow_of_rec contact03 24 4 18655292 (by decide +kernel)
private theorem arithBundle02_ranks_028 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 28 4 = 17253948 :=
  contactRankWindow_of_rec contact03 28 4 17253948 (by decide +kernel)
private theorem arithBundle02_ranks_032 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 32 4 = 15913532 :=
  contactRankWindow_of_rec contact03 32 4 15913532 (by decide +kernel)
private theorem arithBundle02_ranks_036 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 36 4 = 14634044 :=
  contactRankWindow_of_rec contact03 36 4 14634044 (by decide +kernel)
private theorem arithBundle02_ranks_040 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 40 4 = 13415484 :=
  contactRankWindow_of_rec contact03 40 4 13415484 (by decide +kernel)
private theorem arithBundle02_ranks_044 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 44 4 = 12257852 :=
  contactRankWindow_of_rec contact03 44 4 12257852 (by decide +kernel)
private theorem arithBundle02_ranks_048 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 48 4 = 11161148 :=
  contactRankWindow_of_rec contact03 48 4 11161148 (by decide +kernel)
private theorem arithBundle02_ranks_052 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 52 4 = 10125372 :=
  contactRankWindow_of_rec contact03 52 4 10125372 (by decide +kernel)
private theorem arithBundle02_ranks_056 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 56 4 = 9150440 :=
  contactRankWindow_of_rec contact03 56 4 9150440 (by decide +kernel)
private theorem arithBundle02_ranks_060 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 60 4 = 8235530 :=
  contactRankWindow_of_rec contact03 60 4 8235530 (by decide +kernel)
private theorem arithBundle02_ranks_064 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 64 4 = 7379404 :=
  contactRankWindow_of_rec contact03 64 4 7379404 (by decide +kernel)
private theorem arithBundle02_ranks_068 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 68 4 = 6580786 :=
  contactRankWindow_of_rec contact03 68 4 6580786 (by decide +kernel)
private theorem arithBundle02_ranks_072 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 72 4 = 5838084 :=
  contactRankWindow_of_rec contact03 72 4 5838084 (by decide +kernel)
private theorem arithBundle02_ranks_076 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 76 4 = 5149500 :=
  contactRankWindow_of_rec contact03 76 4 5149500 (by decide +kernel)
private theorem arithBundle02_ranks_080 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 80 4 = 4513226 :=
  contactRankWindow_of_rec contact03 80 4 4513226 (by decide +kernel)
private theorem arithBundle02_ranks_084 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 84 4 = 3927668 :=
  contactRankWindow_of_rec contact03 84 4 3927668 (by decide +kernel)
private theorem arithBundle02_ranks_088 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 88 4 = 3390892 :=
  contactRankWindow_of_rec contact03 88 4 3390892 (by decide +kernel)
private theorem arithBundle02_ranks_092 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 92 4 = 2901090 :=
  contactRankWindow_of_rec contact03 92 4 2901090 (by decide +kernel)
private theorem arithBundle02_ranks_096 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 96 4 = 2456804 :=
  contactRankWindow_of_rec contact03 96 4 2456804 (by decide +kernel)
private theorem arithBundle02_ranks_100 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 100 4 = 2055964 :=
  contactRankWindow_of_rec contact03 100 4 2055964 (by decide +kernel)
private theorem arithBundle02_ranks_104 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 104 4 = 1696762 :=
  contactRankWindow_of_rec contact03 104 4 1696762 (by decide +kernel)
private theorem arithBundle02_ranks_108 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 108 4 = 1377876 :=
  contactRankWindow_of_rec contact03 108 4 1377876 (by decide +kernel)
private theorem arithBundle02_ranks_112 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 112 4 = 1097100 :=
  contactRankWindow_of_rec contact03 112 4 1097100 (by decide +kernel)
private theorem arithBundle02_ranks_116 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 116 4 = 852626 :=
  contactRankWindow_of_rec contact03 116 4 852626 (by decide +kernel)
private theorem arithBundle02_ranks_120 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 120 4 = 643268 :=
  contactRankWindow_of_rec contact03 120 4 643268 (by decide +kernel)
private theorem arithBundle02_ranks_124 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 124 4 = 466684 :=
  contactRankWindow_of_rec contact03 124 4 466684 (by decide +kernel)
private theorem arithBundle02_ranks_128 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 128 4 = 321066 :=
  contactRankWindow_of_rec contact03 128 4 321066 (by decide +kernel)
private theorem arithBundle02_ranks_132 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 132 4 = 205364 :=
  contactRankWindow_of_rec contact03 132 4 205364 (by decide +kernel)
private theorem arithBundle02_ranks_136 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 136 4 = 117100 :=
  contactRankWindow_of_rec contact03 136 4 117100 (by decide +kernel)
private theorem arithBundle02_ranks_140 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 140 4 = 54466 :=
  contactRankWindow_of_rec contact03 140 4 54466 (by decide +kernel)
private theorem arithBundle02_ranks_144 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 144 4 = 16582 :=
  contactRankWindow_of_rec contact03 144 4 16582 (by decide +kernel)
private theorem arithBundle02_ranks_148 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 148 4 = 937 :=
  contactRankWindow_of_rec contact03 148 4 937 (by decide +kernel)
private theorem arithBundle02_ranks_152 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 152 17 = 0 :=
  contactRankWindow_of_rec contact03 152 17 0 (by decide +kernel)
private theorem arithBundle02_prefix_ranks_00 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 8 = 54918776 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 4 4 28342844 26575932 arithBundle02_ranks_000 arithBundle02_ranks_004
private theorem arithBundle02_prefix_ranks_01 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 12 = 79788724 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 8 4 54918776 24869948 arithBundle02_prefix_ranks_00 arithBundle02_ranks_008
private theorem arithBundle02_prefix_ranks_02 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 16 = 103013616 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 12 4 79788724 23224892 arithBundle02_prefix_ranks_01 arithBundle02_ranks_012
private theorem arithBundle02_prefix_ranks_03 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 20 = 124654380 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 16 4 103013616 21640764 arithBundle02_prefix_ranks_02 arithBundle02_ranks_016
private theorem arithBundle02_prefix_ranks_04 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 24 = 144771944 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 20 4 124654380 20117564 arithBundle02_prefix_ranks_03 arithBundle02_ranks_020
private theorem arithBundle02_prefix_ranks_05 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 28 = 163427236 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 24 4 144771944 18655292 arithBundle02_prefix_ranks_04 arithBundle02_ranks_024
private theorem arithBundle02_prefix_ranks_06 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 32 = 180681184 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 28 4 163427236 17253948 arithBundle02_prefix_ranks_05 arithBundle02_ranks_028
private theorem arithBundle02_prefix_ranks_07 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 36 = 196594716 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 32 4 180681184 15913532 arithBundle02_prefix_ranks_06 arithBundle02_ranks_032
private theorem arithBundle02_prefix_ranks_08 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 40 = 211228760 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 36 4 196594716 14634044 arithBundle02_prefix_ranks_07 arithBundle02_ranks_036
private theorem arithBundle02_prefix_ranks_09 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 44 = 224644244 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 40 4 211228760 13415484 arithBundle02_prefix_ranks_08 arithBundle02_ranks_040
private theorem arithBundle02_prefix_ranks_10 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 48 = 236902096 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 44 4 224644244 12257852 arithBundle02_prefix_ranks_09 arithBundle02_ranks_044
private theorem arithBundle02_prefix_ranks_11 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 52 = 248063244 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 48 4 236902096 11161148 arithBundle02_prefix_ranks_10 arithBundle02_ranks_048
private theorem arithBundle02_prefix_ranks_12 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 56 = 258188616 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 52 4 248063244 10125372 arithBundle02_prefix_ranks_11 arithBundle02_ranks_052
private theorem arithBundle02_prefix_ranks_13 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 60 = 267339056 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 56 4 258188616 9150440 arithBundle02_prefix_ranks_12 arithBundle02_ranks_056
private theorem arithBundle02_prefix_ranks_14 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 64 = 275574586 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 60 4 267339056 8235530 arithBundle02_prefix_ranks_13 arithBundle02_ranks_060
private theorem arithBundle02_prefix_ranks_15 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 68 = 282953990 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 64 4 275574586 7379404 arithBundle02_prefix_ranks_14 arithBundle02_ranks_064
private theorem arithBundle02_prefix_ranks_16 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 72 = 289534776 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 68 4 282953990 6580786 arithBundle02_prefix_ranks_15 arithBundle02_ranks_068
private theorem arithBundle02_prefix_ranks_17 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 76 = 295372860 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 72 4 289534776 5838084 arithBundle02_prefix_ranks_16 arithBundle02_ranks_072
private theorem arithBundle02_prefix_ranks_18 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 80 = 300522360 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 76 4 295372860 5149500 arithBundle02_prefix_ranks_17 arithBundle02_ranks_076
private theorem arithBundle02_prefix_ranks_19 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 84 = 305035586 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 80 4 300522360 4513226 arithBundle02_prefix_ranks_18 arithBundle02_ranks_080
private theorem arithBundle02_prefix_ranks_20 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 88 = 308963254 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 84 4 305035586 3927668 arithBundle02_prefix_ranks_19 arithBundle02_ranks_084
private theorem arithBundle02_prefix_ranks_21 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 92 = 312354146 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 88 4 308963254 3390892 arithBundle02_prefix_ranks_20 arithBundle02_ranks_088
private theorem arithBundle02_prefix_ranks_22 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 96 = 315255236 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 92 4 312354146 2901090 arithBundle02_prefix_ranks_21 arithBundle02_ranks_092
private theorem arithBundle02_prefix_ranks_23 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 100 = 317712040 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 96 4 315255236 2456804 arithBundle02_prefix_ranks_22 arithBundle02_ranks_096
private theorem arithBundle02_prefix_ranks_24 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 104 = 319768004 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 100 4 317712040 2055964 arithBundle02_prefix_ranks_23 arithBundle02_ranks_100
private theorem arithBundle02_prefix_ranks_25 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 108 = 321464766 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 104 4 319768004 1696762 arithBundle02_prefix_ranks_24 arithBundle02_ranks_104
private theorem arithBundle02_prefix_ranks_26 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 112 = 322842642 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 108 4 321464766 1377876 arithBundle02_prefix_ranks_25 arithBundle02_ranks_108
private theorem arithBundle02_prefix_ranks_27 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 116 = 323939742 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 112 4 322842642 1097100 arithBundle02_prefix_ranks_26 arithBundle02_ranks_112
private theorem arithBundle02_prefix_ranks_28 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 120 = 324792368 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 116 4 323939742 852626 arithBundle02_prefix_ranks_27 arithBundle02_ranks_116
private theorem arithBundle02_prefix_ranks_29 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 124 = 325435636 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 120 4 324792368 643268 arithBundle02_prefix_ranks_28 arithBundle02_ranks_120
private theorem arithBundle02_prefix_ranks_30 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 128 = 325902320 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 124 4 325435636 466684 arithBundle02_prefix_ranks_29 arithBundle02_ranks_124
private theorem arithBundle02_prefix_ranks_31 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 132 = 326223386 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 128 4 325902320 321066 arithBundle02_prefix_ranks_30 arithBundle02_ranks_128
private theorem arithBundle02_prefix_ranks_32 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 136 = 326428750 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 132 4 326223386 205364 arithBundle02_prefix_ranks_31 arithBundle02_ranks_132
private theorem arithBundle02_prefix_ranks_33 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 140 = 326545850 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 136 4 326428750 117100 arithBundle02_prefix_ranks_32 arithBundle02_ranks_136
private theorem arithBundle02_prefix_ranks_34 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 144 = 326600316 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 140 4 326545850 54466 arithBundle02_prefix_ranks_33 arithBundle02_ranks_140
private theorem arithBundle02_prefix_ranks_35 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 148 = 326616898 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 144 4 326600316 16582 arithBundle02_prefix_ranks_34 arithBundle02_ranks_144
private theorem arithBundle02_prefix_ranks_36 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 152 = 326617835 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 148 4 326616898 937 arithBundle02_prefix_ranks_35 arithBundle02_ranks_148
private theorem arithBundle02_prefix_ranks_37 : arithBundle02_sliceWindow (auxiliaryRankSlice contact03) 0 169 = 326617835 :=
  arithBundle02_combineSlices (auxiliaryRankSlice contact03) 0 152 17 326617835 0 arithBundle02_prefix_ranks_36 arithBundle02_ranks_152

theorem contact03_margin : sourceMargin contact03 :=
  arithBundle02_margin_of_checked_counts contact03 169 2204512883741133 108114547322404 8495355080 326617835
    rfl arithBundle02_ordinary_columns arithBundle02_prefix_columns_41 arithBundle02_ordinary_ranks arithBundle02_prefix_ranks_37 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle03_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle03_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle03_sliceWindow f a b = x) (hy : arithBundle03_sliceWindow f (a+b) c = y) :
    arithBundle03_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle03_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle03_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle03_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle03_sliceWindow,Nat.zero_add]

private theorem arithBundle03_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle03_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle03_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle03_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle03_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle03_ordinary_columns : ordinaryColumnCount contact04 = 1803320126217323 := by decide +kernel
private theorem arithBundle03_columns_000 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 4 = 8026912718840 :=
  contactColumnsWindow_fast contact04 0 4 8026912718840 (by decide +kernel)
private theorem arithBundle03_columns_004 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 4 4 = 7637826411832 :=
  contactColumnsWindow_fast contact04 4 4 7637826411832 (by decide +kernel)
private theorem arithBundle03_columns_008 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 8 4 = 7258480221460 :=
  contactColumnsWindow_fast contact04 8 4 7258480221460 (by decide +kernel)
private theorem arithBundle03_columns_012 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 12 4 = 6888872833817 :=
  contactColumnsWindow_fast contact04 12 4 6888872833817 (by decide +kernel)
private theorem arithBundle03_columns_016 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 16 4 = 6528974053536 :=
  contactColumnsWindow_fast contact04 16 4 6528974053536 (by decide +kernel)
private theorem arithBundle03_columns_020 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 20 4 = 6178785047448 :=
  contactColumnsWindow_fast contact04 20 4 6178785047448 (by decide +kernel)
private theorem arithBundle03_columns_024 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 24 4 = 5838308010540 :=
  contactColumnsWindow_fast contact04 24 4 5838308010540 (by decide +kernel)
private theorem arithBundle03_columns_028 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 28 4 = 5507579372122 :=
  contactColumnsWindow_fast contact04 28 4 5507579372122 (by decide +kernel)
private theorem arithBundle03_columns_032 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 32 4 = 5186588086767 :=
  contactColumnsWindow_fast contact04 32 4 5186588086767 (by decide +kernel)
private theorem arithBundle03_columns_036 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 36 4 = 4875307653820 :=
  contactColumnsWindow_fast contact04 36 4 4875307653820 (by decide +kernel)
private theorem arithBundle03_columns_040 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 40 4 = 4573742026792 :=
  contactColumnsWindow_fast contact04 40 4 4573742026792 (by decide +kernel)
private theorem arithBundle03_columns_044 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 44 4 = 4281891414528 :=
  contactColumnsWindow_fast contact04 44 4 4281891414528 (by decide +kernel)
private theorem arithBundle03_columns_048 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 48 4 = 3999797883194 :=
  contactColumnsWindow_fast contact04 48 4 3999797883194 (by decide +kernel)
private theorem arithBundle03_columns_052 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 52 4 = 3727439242793 :=
  contactColumnsWindow_fast contact04 52 4 3727439242793 (by decide +kernel)
private theorem arithBundle03_columns_056 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 56 4 = 3464796296062 :=
  contactColumnsWindow_fast contact04 56 4 3464796296062 (by decide +kernel)
private theorem arithBundle03_columns_060 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 60 4 = 3211868565152 :=
  contactColumnsWindow_fast contact04 60 4 3211868565152 (by decide +kernel)
private theorem arithBundle03_columns_064 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 64 4 = 2968657152804 :=
  contactColumnsWindow_fast contact04 64 4 2968657152804 (by decide +kernel)
private theorem arithBundle03_columns_068 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 68 4 = 2735205626114 :=
  contactColumnsWindow_fast contact04 68 4 2735205626114 (by decide +kernel)
private theorem arithBundle03_columns_072 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 72 4 = 2511484838838 :=
  contactColumnsWindow_fast contact04 72 4 2511484838838 (by decide +kernel)
private theorem arithBundle03_columns_076 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 76 4 = 2297479823349 :=
  contactColumnsWindow_fast contact04 76 4 2297479823349 (by decide +kernel)
private theorem arithBundle03_columns_080 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 80 4 = 2093189775932 :=
  contactColumnsWindow_fast contact04 80 4 2093189775932 (by decide +kernel)
private theorem arithBundle03_columns_084 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 84 4 = 1898617544880 :=
  contactColumnsWindow_fast contact04 84 4 1898617544880 (by decide +kernel)
private theorem arithBundle03_columns_088 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 88 4 = 1713808098959 :=
  contactColumnsWindow_fast contact04 88 4 1713808098959 (by decide +kernel)
private theorem arithBundle03_columns_092 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 92 4 = 1538725299078 :=
  contactColumnsWindow_fast contact04 92 4 1538725299078 (by decide +kernel)
private theorem arithBundle03_columns_096 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 96 4 = 1373358005031 :=
  contactColumnsWindow_fast contact04 96 4 1373358005031 (by decide +kernel)
private theorem arithBundle03_columns_100 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 100 4 = 1217705652860 :=
  contactColumnsWindow_fast contact04 100 4 1217705652860 (by decide +kernel)
private theorem arithBundle03_columns_104 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 104 4 = 1071774173582 :=
  contactColumnsWindow_fast contact04 104 4 1071774173582 (by decide +kernel)
private theorem arithBundle03_columns_108 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 108 4 = 935605289201 :=
  contactColumnsWindow_fast contact04 108 4 935605289201 (by decide +kernel)
private theorem arithBundle03_columns_112 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 112 4 = 809160413118 :=
  contactColumnsWindow_fast contact04 112 4 809160413118 (by decide +kernel)
private theorem arithBundle03_columns_116 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 116 4 = 692430933898 :=
  contactColumnsWindow_fast contact04 116 4 692430933898 (by decide +kernel)
private theorem arithBundle03_columns_120 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 120 4 = 585416306144 :=
  contactColumnsWindow_fast contact04 120 4 585416306144 (by decide +kernel)
private theorem arithBundle03_columns_124 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 124 4 = 488125578830 :=
  contactColumnsWindow_fast contact04 124 4 488125578830 (by decide +kernel)
private theorem arithBundle03_columns_128 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 128 4 = 400597189339 :=
  contactColumnsWindow_fast contact04 128 4 400597189339 (by decide +kernel)
private theorem arithBundle03_columns_132 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 132 4 = 322790263983 :=
  contactColumnsWindow_fast contact04 132 4 322790263983 (by decide +kernel)
private theorem arithBundle03_columns_136 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 136 4 = 254692642635 :=
  contactColumnsWindow_fast contact04 136 4 254692642635 (by decide +kernel)
private theorem arithBundle03_columns_140 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 140 4 = 196206968833 :=
  contactColumnsWindow_fast contact04 140 4 196206968833 (by decide +kernel)
private theorem arithBundle03_columns_144 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 144 4 = 147053905280 :=
  contactColumnsWindow_fast contact04 144 4 147053905280 (by decide +kernel)
private theorem arithBundle03_columns_148 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 148 4 = 106801347422 :=
  contactColumnsWindow_fast contact04 148 4 106801347422 (by decide +kernel)
private theorem arithBundle03_columns_152 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 152 4 = 74778286362 :=
  contactColumnsWindow_fast contact04 152 4 74778286362 (by decide +kernel)
private theorem arithBundle03_columns_156 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 156 4 = 50191778467 :=
  contactColumnsWindow_fast contact04 156 4 50191778467 (by decide +kernel)
private theorem arithBundle03_columns_160 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 160 3 = 25450268765 :=
  contactColumnsWindow_fast contact04 160 3 25450268765 (by decide +kernel)
private theorem arithBundle03_prefix_columns_00 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 8 = 15664739130672 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 4 4 8026912718840 7637826411832 arithBundle03_columns_000 arithBundle03_columns_004
private theorem arithBundle03_prefix_columns_01 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 12 = 22923219352132 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 8 4 15664739130672 7258480221460 arithBundle03_prefix_columns_00 arithBundle03_columns_008
private theorem arithBundle03_prefix_columns_02 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 16 = 29812092185949 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 12 4 22923219352132 6888872833817 arithBundle03_prefix_columns_01 arithBundle03_columns_012
private theorem arithBundle03_prefix_columns_03 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 20 = 36341066239485 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 16 4 29812092185949 6528974053536 arithBundle03_prefix_columns_02 arithBundle03_columns_016
private theorem arithBundle03_prefix_columns_04 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 24 = 42519851286933 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 20 4 36341066239485 6178785047448 arithBundle03_prefix_columns_03 arithBundle03_columns_020
private theorem arithBundle03_prefix_columns_05 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 28 = 48358159297473 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 24 4 42519851286933 5838308010540 arithBundle03_prefix_columns_04 arithBundle03_columns_024
private theorem arithBundle03_prefix_columns_06 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 32 = 53865738669595 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 28 4 48358159297473 5507579372122 arithBundle03_prefix_columns_05 arithBundle03_columns_028
private theorem arithBundle03_prefix_columns_07 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 36 = 59052326756362 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 32 4 53865738669595 5186588086767 arithBundle03_prefix_columns_06 arithBundle03_columns_032
private theorem arithBundle03_prefix_columns_08 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 40 = 63927634410182 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 36 4 59052326756362 4875307653820 arithBundle03_prefix_columns_07 arithBundle03_columns_036
private theorem arithBundle03_prefix_columns_09 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 44 = 68501376436974 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 40 4 63927634410182 4573742026792 arithBundle03_prefix_columns_08 arithBundle03_columns_040
private theorem arithBundle03_prefix_columns_10 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 48 = 72783267851502 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 44 4 68501376436974 4281891414528 arithBundle03_prefix_columns_09 arithBundle03_columns_044
private theorem arithBundle03_prefix_columns_11 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 52 = 76783065734696 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 48 4 72783267851502 3999797883194 arithBundle03_prefix_columns_10 arithBundle03_columns_048
private theorem arithBundle03_prefix_columns_12 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 56 = 80510504977489 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 52 4 76783065734696 3727439242793 arithBundle03_prefix_columns_11 arithBundle03_columns_052
private theorem arithBundle03_prefix_columns_13 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 60 = 83975301273551 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 56 4 80510504977489 3464796296062 arithBundle03_prefix_columns_12 arithBundle03_columns_056
private theorem arithBundle03_prefix_columns_14 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 64 = 87187169838703 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 60 4 83975301273551 3211868565152 arithBundle03_prefix_columns_13 arithBundle03_columns_060
private theorem arithBundle03_prefix_columns_15 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 68 = 90155826991507 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 64 4 87187169838703 2968657152804 arithBundle03_prefix_columns_14 arithBundle03_columns_064
private theorem arithBundle03_prefix_columns_16 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 72 = 92891032617621 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 68 4 90155826991507 2735205626114 arithBundle03_prefix_columns_15 arithBundle03_columns_068
private theorem arithBundle03_prefix_columns_17 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 76 = 95402517456459 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 72 4 92891032617621 2511484838838 arithBundle03_prefix_columns_16 arithBundle03_columns_072
private theorem arithBundle03_prefix_columns_18 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 80 = 97699997279808 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 76 4 95402517456459 2297479823349 arithBundle03_prefix_columns_17 arithBundle03_columns_076
private theorem arithBundle03_prefix_columns_19 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 84 = 99793187055740 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 80 4 97699997279808 2093189775932 arithBundle03_prefix_columns_18 arithBundle03_columns_080
private theorem arithBundle03_prefix_columns_20 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 88 = 101691804600620 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 84 4 99793187055740 1898617544880 arithBundle03_prefix_columns_19 arithBundle03_columns_084
private theorem arithBundle03_prefix_columns_21 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 92 = 103405612699579 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 88 4 101691804600620 1713808098959 arithBundle03_prefix_columns_20 arithBundle03_columns_088
private theorem arithBundle03_prefix_columns_22 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 96 = 104944337998657 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 92 4 103405612699579 1538725299078 arithBundle03_prefix_columns_21 arithBundle03_columns_092
private theorem arithBundle03_prefix_columns_23 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 100 = 106317696003688 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 96 4 104944337998657 1373358005031 arithBundle03_prefix_columns_22 arithBundle03_columns_096
private theorem arithBundle03_prefix_columns_24 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 104 = 107535401656548 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 100 4 106317696003688 1217705652860 arithBundle03_prefix_columns_23 arithBundle03_columns_100
private theorem arithBundle03_prefix_columns_25 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 108 = 108607175830130 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 104 4 107535401656548 1071774173582 arithBundle03_prefix_columns_24 arithBundle03_columns_104
private theorem arithBundle03_prefix_columns_26 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 112 = 109542781119331 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 108 4 108607175830130 935605289201 arithBundle03_prefix_columns_25 arithBundle03_columns_108
private theorem arithBundle03_prefix_columns_27 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 116 = 110351941532449 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 112 4 109542781119331 809160413118 arithBundle03_prefix_columns_26 arithBundle03_columns_112
private theorem arithBundle03_prefix_columns_28 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 120 = 111044372466347 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 116 4 110351941532449 692430933898 arithBundle03_prefix_columns_27 arithBundle03_columns_116
private theorem arithBundle03_prefix_columns_29 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 124 = 111629788772491 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 120 4 111044372466347 585416306144 arithBundle03_prefix_columns_28 arithBundle03_columns_120
private theorem arithBundle03_prefix_columns_30 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 128 = 112117914351321 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 124 4 111629788772491 488125578830 arithBundle03_prefix_columns_29 arithBundle03_columns_124
private theorem arithBundle03_prefix_columns_31 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 132 = 112518511540660 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 128 4 112117914351321 400597189339 arithBundle03_prefix_columns_30 arithBundle03_columns_128
private theorem arithBundle03_prefix_columns_32 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 136 = 112841301804643 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 132 4 112518511540660 322790263983 arithBundle03_prefix_columns_31 arithBundle03_columns_132
private theorem arithBundle03_prefix_columns_33 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 140 = 113095994447278 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 136 4 112841301804643 254692642635 arithBundle03_prefix_columns_32 arithBundle03_columns_136
private theorem arithBundle03_prefix_columns_34 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 144 = 113292201416111 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 140 4 113095994447278 196206968833 arithBundle03_prefix_columns_33 arithBundle03_columns_140
private theorem arithBundle03_prefix_columns_35 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 148 = 113439255321391 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 144 4 113292201416111 147053905280 arithBundle03_prefix_columns_34 arithBundle03_columns_144
private theorem arithBundle03_prefix_columns_36 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 152 = 113546056668813 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 148 4 113439255321391 106801347422 arithBundle03_prefix_columns_35 arithBundle03_columns_148
private theorem arithBundle03_prefix_columns_37 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 156 = 113620834955175 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 152 4 113546056668813 74778286362 arithBundle03_prefix_columns_36 arithBundle03_columns_152
private theorem arithBundle03_prefix_columns_38 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 160 = 113671026733642 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 156 4 113620834955175 50191778467 arithBundle03_prefix_columns_37 arithBundle03_columns_156
private theorem arithBundle03_prefix_columns_39 : arithBundle03_sliceWindow (auxiliaryColumnSlice contact04) 0 163 = 113696477002407 :=
  arithBundle03_combineSlices (auxiliaryColumnSlice contact04) 0 160 3 113671026733642 25450268765 arithBundle03_prefix_columns_38 arithBundle03_columns_160

private theorem arithBundle03_ordinary_ranks : ordinaryRankBound contact04 = 6966913801 := by decide +kernel
private theorem arithBundle03_ranks_000 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 4 = 30233214 :=
  contactRankWindow_of_rec contact04 0 4 30233214 (by decide +kernel)
private theorem arithBundle03_ranks_004 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 4 4 = 28326414 :=
  contactRankWindow_of_rec contact04 4 4 28326414 (by decide +kernel)
private theorem arithBundle03_ranks_008 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 8 4 = 26486814 :=
  contactRankWindow_of_rec contact04 8 4 26486814 (by decide +kernel)
private theorem arithBundle03_ranks_012 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 12 4 = 24714414 :=
  contactRankWindow_of_rec contact04 12 4 24714414 (by decide +kernel)
private theorem arithBundle03_ranks_016 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 16 4 = 23009214 :=
  contactRankWindow_of_rec contact04 16 4 23009214 (by decide +kernel)
private theorem arithBundle03_ranks_020 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 20 4 = 21371214 :=
  contactRankWindow_of_rec contact04 20 4 21371214 (by decide +kernel)
private theorem arithBundle03_ranks_024 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 24 4 = 19800414 :=
  contactRankWindow_of_rec contact04 24 4 19800414 (by decide +kernel)
private theorem arithBundle03_ranks_028 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 28 4 = 18296814 :=
  contactRankWindow_of_rec contact04 28 4 18296814 (by decide +kernel)
private theorem arithBundle03_ranks_032 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 32 4 = 16860414 :=
  contactRankWindow_of_rec contact04 32 4 16860414 (by decide +kernel)
private theorem arithBundle03_ranks_036 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 36 4 = 15491214 :=
  contactRankWindow_of_rec contact04 36 4 15491214 (by decide +kernel)
private theorem arithBundle03_ranks_040 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 40 4 = 14189214 :=
  contactRankWindow_of_rec contact04 40 4 14189214 (by decide +kernel)
private theorem arithBundle03_ranks_044 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 44 4 = 12954414 :=
  contactRankWindow_of_rec contact04 44 4 12954414 (by decide +kernel)
private theorem arithBundle03_ranks_048 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 48 4 = 11786814 :=
  contactRankWindow_of_rec contact04 48 4 11786814 (by decide +kernel)
private theorem arithBundle03_ranks_052 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 52 4 = 10686203 :=
  contactRankWindow_of_rec contact04 52 4 10686203 (by decide +kernel)
private theorem arithBundle03_ranks_056 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 56 4 = 9651487 :=
  contactRankWindow_of_rec contact04 56 4 9651487 (by decide +kernel)
private theorem arithBundle03_ranks_060 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 60 4 = 8681362 :=
  contactRankWindow_of_rec contact04 60 4 8681362 (by decide +kernel)
private theorem arithBundle03_ranks_064 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 64 4 = 7774192 :=
  contactRankWindow_of_rec contact04 64 4 7774192 (by decide +kernel)
private theorem arithBundle03_ranks_068 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 68 4 = 6928199 :=
  contactRankWindow_of_rec contact04 68 4 6928199 (by decide +kernel)
private theorem arithBundle03_ranks_072 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 72 4 = 6141486 :=
  contactRankWindow_of_rec contact04 72 4 6141486 (by decide +kernel)
private theorem arithBundle03_ranks_076 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 76 4 = 5412136 :=
  contactRankWindow_of_rec contact04 76 4 5412136 (by decide +kernel)
private theorem arithBundle03_ranks_080 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 80 4 = 4738511 :=
  contactRankWindow_of_rec contact04 80 4 4738511 (by decide +kernel)
private theorem arithBundle03_ranks_084 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 84 4 = 4118570 :=
  contactRankWindow_of_rec contact04 84 4 4118570 (by decide +kernel)
private theorem arithBundle03_ranks_088 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 88 4 = 3550400 :=
  contactRankWindow_of_rec contact04 88 4 3550400 (by decide +kernel)
private theorem arithBundle03_ranks_092 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 92 4 = 3032503 :=
  contactRankWindow_of_rec contact04 92 4 3032503 (by decide +kernel)
private theorem arithBundle03_ranks_096 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 96 4 = 2562694 :=
  contactRankWindow_of_rec contact04 96 4 2562694 (by decide +kernel)
private theorem arithBundle03_ranks_100 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 100 4 = 2139064 :=
  contactRankWindow_of_rec contact04 100 4 2139064 (by decide +kernel)
private theorem arithBundle03_ranks_104 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 104 4 = 1760255 :=
  contactRankWindow_of_rec contact04 104 4 1760255 (by decide +kernel)
private theorem arithBundle03_ranks_108 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 108 4 = 1423938 :=
  contactRankWindow_of_rec contact04 108 4 1423938 (by decide +kernel)
private theorem arithBundle03_ranks_112 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 112 4 = 1128208 :=
  contactRankWindow_of_rec contact04 112 4 1128208 (by decide +kernel)
private theorem arithBundle03_ranks_116 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 116 4 = 871847 :=
  contactRankWindow_of_rec contact04 116 4 871847 (by decide +kernel)
private theorem arithBundle03_ranks_120 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 120 4 = 652382 :=
  contactRankWindow_of_rec contact04 120 4 652382 (by decide +kernel)
private theorem arithBundle03_ranks_124 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 124 4 = 467912 :=
  contactRankWindow_of_rec contact04 124 4 467912 (by decide +kernel)
private theorem arithBundle03_ranks_128 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 128 4 = 317359 :=
  contactRankWindow_of_rec contact04 128 4 317359 (by decide +kernel)
private theorem arithBundle03_ranks_132 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 132 4 = 198106 :=
  contactRankWindow_of_rec contact04 132 4 198106 (by decide +kernel)
private theorem arithBundle03_ranks_136 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 136 4 = 108256 :=
  contactRankWindow_of_rec contact04 136 4 108256 (by decide +kernel)
private theorem arithBundle03_ranks_140 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 140 4 = 46910 :=
  contactRankWindow_of_rec contact04 140 4 46910 (by decide +kernel)
private theorem arithBundle03_ranks_144 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 144 4 = 11531 :=
  contactRankWindow_of_rec contact04 144 4 11531 (by decide +kernel)
private theorem arithBundle03_ranks_148 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 148 15 = 0 :=
  contactRankWindow_of_rec contact04 148 15 0 (by decide +kernel)
private theorem arithBundle03_prefix_ranks_00 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 8 = 58559628 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 4 4 30233214 28326414 arithBundle03_ranks_000 arithBundle03_ranks_004
private theorem arithBundle03_prefix_ranks_01 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 12 = 85046442 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 8 4 58559628 26486814 arithBundle03_prefix_ranks_00 arithBundle03_ranks_008
private theorem arithBundle03_prefix_ranks_02 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 16 = 109760856 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 12 4 85046442 24714414 arithBundle03_prefix_ranks_01 arithBundle03_ranks_012
private theorem arithBundle03_prefix_ranks_03 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 20 = 132770070 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 16 4 109760856 23009214 arithBundle03_prefix_ranks_02 arithBundle03_ranks_016
private theorem arithBundle03_prefix_ranks_04 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 24 = 154141284 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 20 4 132770070 21371214 arithBundle03_prefix_ranks_03 arithBundle03_ranks_020
private theorem arithBundle03_prefix_ranks_05 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 28 = 173941698 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 24 4 154141284 19800414 arithBundle03_prefix_ranks_04 arithBundle03_ranks_024
private theorem arithBundle03_prefix_ranks_06 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 32 = 192238512 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 28 4 173941698 18296814 arithBundle03_prefix_ranks_05 arithBundle03_ranks_028
private theorem arithBundle03_prefix_ranks_07 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 36 = 209098926 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 32 4 192238512 16860414 arithBundle03_prefix_ranks_06 arithBundle03_ranks_032
private theorem arithBundle03_prefix_ranks_08 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 40 = 224590140 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 36 4 209098926 15491214 arithBundle03_prefix_ranks_07 arithBundle03_ranks_036
private theorem arithBundle03_prefix_ranks_09 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 44 = 238779354 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 40 4 224590140 14189214 arithBundle03_prefix_ranks_08 arithBundle03_ranks_040
private theorem arithBundle03_prefix_ranks_10 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 48 = 251733768 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 44 4 238779354 12954414 arithBundle03_prefix_ranks_09 arithBundle03_ranks_044
private theorem arithBundle03_prefix_ranks_11 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 52 = 263520582 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 48 4 251733768 11786814 arithBundle03_prefix_ranks_10 arithBundle03_ranks_048
private theorem arithBundle03_prefix_ranks_12 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 56 = 274206785 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 52 4 263520582 10686203 arithBundle03_prefix_ranks_11 arithBundle03_ranks_052
private theorem arithBundle03_prefix_ranks_13 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 60 = 283858272 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 56 4 274206785 9651487 arithBundle03_prefix_ranks_12 arithBundle03_ranks_056
private theorem arithBundle03_prefix_ranks_14 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 64 = 292539634 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 60 4 283858272 8681362 arithBundle03_prefix_ranks_13 arithBundle03_ranks_060
private theorem arithBundle03_prefix_ranks_15 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 68 = 300313826 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 64 4 292539634 7774192 arithBundle03_prefix_ranks_14 arithBundle03_ranks_064
private theorem arithBundle03_prefix_ranks_16 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 72 = 307242025 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 68 4 300313826 6928199 arithBundle03_prefix_ranks_15 arithBundle03_ranks_068
private theorem arithBundle03_prefix_ranks_17 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 76 = 313383511 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 72 4 307242025 6141486 arithBundle03_prefix_ranks_16 arithBundle03_ranks_072
private theorem arithBundle03_prefix_ranks_18 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 80 = 318795647 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 76 4 313383511 5412136 arithBundle03_prefix_ranks_17 arithBundle03_ranks_076
private theorem arithBundle03_prefix_ranks_19 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 84 = 323534158 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 80 4 318795647 4738511 arithBundle03_prefix_ranks_18 arithBundle03_ranks_080
private theorem arithBundle03_prefix_ranks_20 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 88 = 327652728 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 84 4 323534158 4118570 arithBundle03_prefix_ranks_19 arithBundle03_ranks_084
private theorem arithBundle03_prefix_ranks_21 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 92 = 331203128 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 88 4 327652728 3550400 arithBundle03_prefix_ranks_20 arithBundle03_ranks_088
private theorem arithBundle03_prefix_ranks_22 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 96 = 334235631 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 92 4 331203128 3032503 arithBundle03_prefix_ranks_21 arithBundle03_ranks_092
private theorem arithBundle03_prefix_ranks_23 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 100 = 336798325 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 96 4 334235631 2562694 arithBundle03_prefix_ranks_22 arithBundle03_ranks_096
private theorem arithBundle03_prefix_ranks_24 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 104 = 338937389 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 100 4 336798325 2139064 arithBundle03_prefix_ranks_23 arithBundle03_ranks_100
private theorem arithBundle03_prefix_ranks_25 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 108 = 340697644 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 104 4 338937389 1760255 arithBundle03_prefix_ranks_24 arithBundle03_ranks_104
private theorem arithBundle03_prefix_ranks_26 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 112 = 342121582 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 108 4 340697644 1423938 arithBundle03_prefix_ranks_25 arithBundle03_ranks_108
private theorem arithBundle03_prefix_ranks_27 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 116 = 343249790 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 112 4 342121582 1128208 arithBundle03_prefix_ranks_26 arithBundle03_ranks_112
private theorem arithBundle03_prefix_ranks_28 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 120 = 344121637 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 116 4 343249790 871847 arithBundle03_prefix_ranks_27 arithBundle03_ranks_116
private theorem arithBundle03_prefix_ranks_29 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 124 = 344774019 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 120 4 344121637 652382 arithBundle03_prefix_ranks_28 arithBundle03_ranks_120
private theorem arithBundle03_prefix_ranks_30 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 128 = 345241931 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 124 4 344774019 467912 arithBundle03_prefix_ranks_29 arithBundle03_ranks_124
private theorem arithBundle03_prefix_ranks_31 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 132 = 345559290 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 128 4 345241931 317359 arithBundle03_prefix_ranks_30 arithBundle03_ranks_128
private theorem arithBundle03_prefix_ranks_32 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 136 = 345757396 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 132 4 345559290 198106 arithBundle03_prefix_ranks_31 arithBundle03_ranks_132
private theorem arithBundle03_prefix_ranks_33 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 140 = 345865652 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 136 4 345757396 108256 arithBundle03_prefix_ranks_32 arithBundle03_ranks_136
private theorem arithBundle03_prefix_ranks_34 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 144 = 345912562 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 140 4 345865652 46910 arithBundle03_prefix_ranks_33 arithBundle03_ranks_140
private theorem arithBundle03_prefix_ranks_35 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 148 = 345924093 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 144 4 345912562 11531 arithBundle03_prefix_ranks_34 arithBundle03_ranks_144
private theorem arithBundle03_prefix_ranks_36 : arithBundle03_sliceWindow (auxiliaryRankSlice contact04) 0 163 = 345924093 :=
  arithBundle03_combineSlices (auxiliaryRankSlice contact04) 0 148 15 345924093 0 arithBundle03_prefix_ranks_35 arithBundle03_ranks_148

theorem contact04_margin : sourceMargin contact04 :=
  arithBundle03_margin_of_checked_counts contact04 163 1803320126217323 113696477002407 6966913801 345924093
    rfl arithBundle03_ordinary_columns arithBundle03_prefix_columns_39 arithBundle03_ordinary_ranks arithBundle03_prefix_ranks_36 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle04_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle04_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle04_sliceWindow f a b = x) (hy : arithBundle04_sliceWindow f (a+b) c = y) :
    arithBundle04_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle04_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle04_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle04_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle04_sliceWindow,Nat.zero_add]

private theorem arithBundle04_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle04_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle04_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle04_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle04_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle04_ordinary_columns : ordinaryColumnCount contact07 = 2017326801966088 := by decide +kernel
private theorem arithBundle04_columns_000 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 4 = 8153463572080 :=
  contactColumnsWindow_fast contact07 0 4 8153463572080 (by decide +kernel)
private theorem arithBundle04_columns_004 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 4 4 = 7761301417616 :=
  contactColumnsWindow_fast contact07 4 4 7761301417616 (by decide +kernel)
private theorem arithBundle04_columns_008 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 8 4 = 7378846943252 :=
  contactColumnsWindow_fast contact07 8 4 7378846943252 (by decide +kernel)
private theorem arithBundle04_columns_012 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 12 4 = 7006100294665 :=
  contactColumnsWindow_fast contact07 12 4 7006100294665 (by decide +kernel)
private theorem arithBundle04_columns_016 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 16 4 = 6643099019552 :=
  contactColumnsWindow_fast contact07 16 4 6643099019552 (by decide +kernel)
private theorem arithBundle04_columns_020 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 20 4 = 6289828505433 :=
  contactColumnsWindow_fast contact07 20 4 6289828505433 (by decide +kernel)
private theorem arithBundle04_columns_024 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 24 4 = 5946269697820 :=
  contactColumnsWindow_fast contact07 24 4 5946269697820 (by decide +kernel)
private theorem arithBundle04_columns_028 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 28 4 = 5612421036176 :=
  contactColumnsWindow_fast contact07 28 4 5612421036176 (by decide +kernel)
private theorem arithBundle04_columns_032 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 32 4 = 5288285644019 :=
  contactColumnsWindow_fast contact07 32 4 5288285644019 (by decide +kernel)
private theorem arithBundle04_columns_036 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 36 4 = 4973900423982 :=
  contactColumnsWindow_fast contact07 36 4 4973900423982 (by decide +kernel)
private theorem arithBundle04_columns_040 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 40 4 = 4669246880911 :=
  contactColumnsWindow_fast contact07 40 4 4669246880911 (by decide +kernel)
private theorem arithBundle04_columns_044 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 44 4 = 4374306993657 :=
  contactColumnsWindow_fast contact07 44 4 4374306993657 (by decide +kernel)
private theorem arithBundle04_columns_048 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 48 4 = 4089082113432 :=
  contactColumnsWindow_fast contact07 48 4 4089082113432 (by decide +kernel)
private theorem arithBundle04_columns_052 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 52 4 = 3813573979092 :=
  contactColumnsWindow_fast contact07 52 4 3813573979092 (by decide +kernel)
private theorem arithBundle04_columns_056 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 56 4 = 3547823335915 :=
  contactColumnsWindow_fast contact07 56 4 3547823335915 (by decide +kernel)
private theorem arithBundle04_columns_060 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 60 4 = 3291803743666 :=
  contactColumnsWindow_fast contact07 60 4 3291803743666 (by decide +kernel)
private theorem arithBundle04_columns_064 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 64 4 = 3045501595755 :=
  contactColumnsWindow_fast contact07 64 4 3045501595755 (by decide +kernel)
private theorem arithBundle04_columns_068 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 68 4 = 2808914398428 :=
  contactColumnsWindow_fast contact07 68 4 2808914398428 (by decide +kernel)
private theorem arithBundle04_columns_072 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 72 4 = 2582045933642 :=
  contactColumnsWindow_fast contact07 72 4 2582045933642 (by decide +kernel)
private theorem arithBundle04_columns_076 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 76 4 = 2364936599149 :=
  contactColumnsWindow_fast contact07 76 4 2364936599149 (by decide +kernel)
private theorem arithBundle04_columns_080 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 80 4 = 2157555278122 :=
  contactColumnsWindow_fast contact07 80 4 2157555278122 (by decide +kernel)
private theorem arithBundle04_columns_084 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 84 4 = 1959890851653 :=
  contactColumnsWindow_fast contact07 84 4 1959890851653 (by decide +kernel)
private theorem arithBundle04_columns_088 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 88 4 = 1771941410780 :=
  contactColumnsWindow_fast contact07 88 4 1771941410780 (by decide +kernel)
private theorem arithBundle04_columns_092 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 92 4 = 1593713528042 :=
  contactColumnsWindow_fast contact07 92 4 1593713528042 (by decide +kernel)
private theorem arithBundle04_columns_096 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 96 4 = 1425244516711 :=
  contactColumnsWindow_fast contact07 96 4 1425244516711 (by decide +kernel)
private theorem arithBundle04_columns_100 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 100 4 = 1266501478339 :=
  contactColumnsWindow_fast contact07 100 4 1266501478339 (by decide +kernel)
private theorem arithBundle04_columns_104 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 104 4 = 1117474974966 :=
  contactColumnsWindow_fast contact07 104 4 1117474974966 (by decide +kernel)
private theorem arithBundle04_columns_108 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 108 4 = 978163138280 :=
  contactColumnsWindow_fast contact07 108 4 978163138280 (by decide +kernel)
private theorem arithBundle04_columns_112 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 112 4 = 848575776242 :=
  contactColumnsWindow_fast contact07 112 4 848575776242 (by decide +kernel)
private theorem arithBundle04_columns_116 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 116 4 = 728747304096 :=
  contactColumnsWindow_fast contact07 116 4 728747304096 (by decide +kernel)
private theorem arithBundle04_columns_120 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 120 4 = 618642450481 :=
  contactColumnsWindow_fast contact07 120 4 618642450481 (by decide +kernel)
private theorem arithBundle04_columns_124 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 124 4 = 518253803454 :=
  contactColumnsWindow_fast contact07 124 4 518253803454 (by decide +kernel)
private theorem arithBundle04_columns_128 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 128 4 = 427579573985 :=
  contactColumnsWindow_fast contact07 128 4 427579573985 (by decide +kernel)
private theorem arithBundle04_columns_132 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 132 4 = 346633592707 :=
  contactColumnsWindow_fast contact07 132 4 346633592707 (by decide +kernel)
private theorem arithBundle04_columns_136 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 136 4 = 275443791237 :=
  contactColumnsWindow_fast contact07 136 4 275443791237 (by decide +kernel)
private theorem arithBundle04_columns_140 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 140 4 = 213924398474 :=
  contactColumnsWindow_fast contact07 140 4 213924398474 (by decide +kernel)
private theorem arithBundle04_columns_144 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 144 4 = 161838500502 :=
  contactColumnsWindow_fast contact07 144 4 161838500502 (by decide +kernel)
private theorem arithBundle04_columns_148 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 148 4 = 118771367381 :=
  contactColumnsWindow_fast contact07 148 4 118771367381 (by decide +kernel)
private theorem arithBundle04_columns_152 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 152 4 = 84166582616 :=
  contactColumnsWindow_fast contact07 152 4 84166582616 (by decide +kernel)
private theorem arithBundle04_columns_156 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 156 4 = 57303731514 :=
  contactColumnsWindow_fast contact07 156 4 57303731514 (by decide +kernel)
private theorem arithBundle04_columns_160 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 160 4 = 37249007980 :=
  contactColumnsWindow_fast contact07 160 4 37249007980 (by decide +kernel)
private theorem arithBundle04_columns_164 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 164 4 = 22943295848 :=
  contactColumnsWindow_fast contact07 164 4 22943295848 (by decide +kernel)
private theorem arithBundle04_prefix_columns_00 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 8 = 15914764989696 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 4 4 8153463572080 7761301417616 arithBundle04_columns_000 arithBundle04_columns_004
private theorem arithBundle04_prefix_columns_01 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 12 = 23293611932948 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 8 4 15914764989696 7378846943252 arithBundle04_prefix_columns_00 arithBundle04_columns_008
private theorem arithBundle04_prefix_columns_02 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 16 = 30299712227613 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 12 4 23293611932948 7006100294665 arithBundle04_prefix_columns_01 arithBundle04_columns_012
private theorem arithBundle04_prefix_columns_03 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 20 = 36942811247165 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 16 4 30299712227613 6643099019552 arithBundle04_prefix_columns_02 arithBundle04_columns_016
private theorem arithBundle04_prefix_columns_04 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 24 = 43232639752598 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 20 4 36942811247165 6289828505433 arithBundle04_prefix_columns_03 arithBundle04_columns_020
private theorem arithBundle04_prefix_columns_05 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 28 = 49178909450418 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 24 4 43232639752598 5946269697820 arithBundle04_prefix_columns_04 arithBundle04_columns_024
private theorem arithBundle04_prefix_columns_06 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 32 = 54791330486594 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 28 4 49178909450418 5612421036176 arithBundle04_prefix_columns_05 arithBundle04_columns_028
private theorem arithBundle04_prefix_columns_07 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 36 = 60079616130613 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 32 4 54791330486594 5288285644019 arithBundle04_prefix_columns_06 arithBundle04_columns_032
private theorem arithBundle04_prefix_columns_08 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 40 = 65053516554595 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 36 4 60079616130613 4973900423982 arithBundle04_prefix_columns_07 arithBundle04_columns_036
private theorem arithBundle04_prefix_columns_09 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 44 = 69722763435506 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 40 4 65053516554595 4669246880911 arithBundle04_prefix_columns_08 arithBundle04_columns_040
private theorem arithBundle04_prefix_columns_10 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 48 = 74097070429163 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 44 4 69722763435506 4374306993657 arithBundle04_prefix_columns_09 arithBundle04_columns_044
private theorem arithBundle04_prefix_columns_11 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 52 = 78186152542595 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 48 4 74097070429163 4089082113432 arithBundle04_prefix_columns_10 arithBundle04_columns_048
private theorem arithBundle04_prefix_columns_12 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 56 = 81999726521687 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 52 4 78186152542595 3813573979092 arithBundle04_prefix_columns_11 arithBundle04_columns_052
private theorem arithBundle04_prefix_columns_13 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 60 = 85547549857602 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 56 4 81999726521687 3547823335915 arithBundle04_prefix_columns_12 arithBundle04_columns_056
private theorem arithBundle04_prefix_columns_14 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 64 = 88839353601268 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 60 4 85547549857602 3291803743666 arithBundle04_prefix_columns_13 arithBundle04_columns_060
private theorem arithBundle04_prefix_columns_15 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 68 = 91884855197023 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 64 4 88839353601268 3045501595755 arithBundle04_prefix_columns_14 arithBundle04_columns_064
private theorem arithBundle04_prefix_columns_16 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 72 = 94693769595451 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 68 4 91884855197023 2808914398428 arithBundle04_prefix_columns_15 arithBundle04_columns_068
private theorem arithBundle04_prefix_columns_17 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 76 = 97275815529093 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 72 4 94693769595451 2582045933642 arithBundle04_prefix_columns_16 arithBundle04_columns_072
private theorem arithBundle04_prefix_columns_18 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 80 = 99640752128242 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 76 4 97275815529093 2364936599149 arithBundle04_prefix_columns_17 arithBundle04_columns_076
private theorem arithBundle04_prefix_columns_19 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 84 = 101798307406364 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 80 4 99640752128242 2157555278122 arithBundle04_prefix_columns_18 arithBundle04_columns_080
private theorem arithBundle04_prefix_columns_20 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 88 = 103758198258017 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 84 4 101798307406364 1959890851653 arithBundle04_prefix_columns_19 arithBundle04_columns_084
private theorem arithBundle04_prefix_columns_21 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 92 = 105530139668797 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 88 4 103758198258017 1771941410780 arithBundle04_prefix_columns_20 arithBundle04_columns_088
private theorem arithBundle04_prefix_columns_22 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 96 = 107123853196839 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 92 4 105530139668797 1593713528042 arithBundle04_prefix_columns_21 arithBundle04_columns_092
private theorem arithBundle04_prefix_columns_23 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 100 = 108549097713550 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 96 4 107123853196839 1425244516711 arithBundle04_prefix_columns_22 arithBundle04_columns_096
private theorem arithBundle04_prefix_columns_24 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 104 = 109815599191889 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 100 4 108549097713550 1266501478339 arithBundle04_prefix_columns_23 arithBundle04_columns_100
private theorem arithBundle04_prefix_columns_25 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 108 = 110933074166855 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 104 4 109815599191889 1117474974966 arithBundle04_prefix_columns_24 arithBundle04_columns_104
private theorem arithBundle04_prefix_columns_26 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 112 = 111911237305135 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 108 4 110933074166855 978163138280 arithBundle04_prefix_columns_25 arithBundle04_columns_108
private theorem arithBundle04_prefix_columns_27 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 116 = 112759813081377 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 112 4 111911237305135 848575776242 arithBundle04_prefix_columns_26 arithBundle04_columns_112
private theorem arithBundle04_prefix_columns_28 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 120 = 113488560385473 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 116 4 112759813081377 728747304096 arithBundle04_prefix_columns_27 arithBundle04_columns_116
private theorem arithBundle04_prefix_columns_29 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 124 = 114107202835954 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 120 4 113488560385473 618642450481 arithBundle04_prefix_columns_28 arithBundle04_columns_120
private theorem arithBundle04_prefix_columns_30 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 128 = 114625456639408 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 124 4 114107202835954 518253803454 arithBundle04_prefix_columns_29 arithBundle04_columns_124
private theorem arithBundle04_prefix_columns_31 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 132 = 115053036213393 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 128 4 114625456639408 427579573985 arithBundle04_prefix_columns_30 arithBundle04_columns_128
private theorem arithBundle04_prefix_columns_32 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 136 = 115399669806100 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 132 4 115053036213393 346633592707 arithBundle04_prefix_columns_31 arithBundle04_columns_132
private theorem arithBundle04_prefix_columns_33 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 140 = 115675113597337 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 136 4 115399669806100 275443791237 arithBundle04_prefix_columns_32 arithBundle04_columns_136
private theorem arithBundle04_prefix_columns_34 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 144 = 115889037995811 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 140 4 115675113597337 213924398474 arithBundle04_prefix_columns_33 arithBundle04_columns_140
private theorem arithBundle04_prefix_columns_35 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 148 = 116050876496313 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 144 4 115889037995811 161838500502 arithBundle04_prefix_columns_34 arithBundle04_columns_144
private theorem arithBundle04_prefix_columns_36 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 152 = 116169647863694 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 148 4 116050876496313 118771367381 arithBundle04_prefix_columns_35 arithBundle04_columns_148
private theorem arithBundle04_prefix_columns_37 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 156 = 116253814446310 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 152 4 116169647863694 84166582616 arithBundle04_prefix_columns_36 arithBundle04_columns_152
private theorem arithBundle04_prefix_columns_38 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 160 = 116311118177824 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 156 4 116253814446310 57303731514 arithBundle04_prefix_columns_37 arithBundle04_columns_156
private theorem arithBundle04_prefix_columns_39 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 164 = 116348367185804 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 160 4 116311118177824 37249007980 arithBundle04_prefix_columns_38 arithBundle04_columns_160
private theorem arithBundle04_prefix_columns_40 : arithBundle04_sliceWindow (auxiliaryColumnSlice contact07) 0 168 = 116371310481652 :=
  arithBundle04_combineSlices (auxiliaryColumnSlice contact07) 0 164 4 116348367185804 22943295848 arithBundle04_prefix_columns_39 arithBundle04_columns_164

private theorem arithBundle04_ordinary_ranks : ordinaryRankBound contact07 = 7785619784 := by decide +kernel
private theorem arithBundle04_ranks_000 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 4 = 30720414 :=
  contactRankWindow_of_rec contact07 0 4 30720414 (by decide +kernel)
private theorem arithBundle04_ranks_004 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 4 4 = 28796814 :=
  contactRankWindow_of_rec contact07 4 4 28796814 (by decide +kernel)
private theorem arithBundle04_ranks_008 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 8 4 = 26940414 :=
  contactRankWindow_of_rec contact07 8 4 26940414 (by decide +kernel)
private theorem arithBundle04_ranks_012 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 12 4 = 25151214 :=
  contactRankWindow_of_rec contact07 12 4 25151214 (by decide +kernel)
private theorem arithBundle04_ranks_016 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 16 4 = 23429214 :=
  contactRankWindow_of_rec contact07 16 4 23429214 (by decide +kernel)
private theorem arithBundle04_ranks_020 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 20 4 = 21774414 :=
  contactRankWindow_of_rec contact07 20 4 21774414 (by decide +kernel)
private theorem arithBundle04_ranks_024 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 24 4 = 20186814 :=
  contactRankWindow_of_rec contact07 24 4 20186814 (by decide +kernel)
private theorem arithBundle04_ranks_028 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 28 4 = 18666414 :=
  contactRankWindow_of_rec contact07 28 4 18666414 (by decide +kernel)
private theorem arithBundle04_ranks_032 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 32 4 = 17213214 :=
  contactRankWindow_of_rec contact07 32 4 17213214 (by decide +kernel)
private theorem arithBundle04_ranks_036 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 36 4 = 15827214 :=
  contactRankWindow_of_rec contact07 36 4 15827214 (by decide +kernel)
private theorem arithBundle04_ranks_040 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 40 4 = 14508414 :=
  contactRankWindow_of_rec contact07 40 4 14508414 (by decide +kernel)
private theorem arithBundle04_ranks_044 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 44 4 = 13256814 :=
  contactRankWindow_of_rec contact07 44 4 13256814 (by decide +kernel)
private theorem arithBundle04_ranks_048 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 48 4 = 12072414 :=
  contactRankWindow_of_rec contact07 48 4 12072414 (by decide +kernel)
private theorem arithBundle04_ranks_052 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 52 4 = 10955124 :=
  contactRankWindow_of_rec contact07 52 4 10955124 (by decide +kernel)
private theorem arithBundle04_ranks_056 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 56 4 = 9904064 :=
  contactRankWindow_of_rec contact07 56 4 9904064 (by decide +kernel)
private theorem arithBundle04_ranks_060 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 60 4 = 8917910 :=
  contactRankWindow_of_rec contact07 60 4 8917910 (by decide +kernel)
private theorem arithBundle04_ranks_064 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 64 4 = 7995198 :=
  contactRankWindow_of_rec contact07 64 4 7995198 (by decide +kernel)
private theorem arithBundle04_ranks_068 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 68 4 = 7134043 :=
  contactRankWindow_of_rec contact07 68 4 7134043 (by decide +kernel)
private theorem arithBundle04_ranks_072 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 72 4 = 6332702 :=
  contactRankWindow_of_rec contact07 72 4 6332702 (by decide +kernel)
private theorem arithBundle04_ranks_076 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 76 4 = 5589242 :=
  contactRankWindow_of_rec contact07 76 4 5589242 (by decide +kernel)
private theorem arithBundle04_ranks_080 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 80 4 = 4901747 :=
  contactRankWindow_of_rec contact07 80 4 4901747 (by decide +kernel)
private theorem arithBundle04_ranks_084 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 84 4 = 4268614 :=
  contactRankWindow_of_rec contact07 84 4 4268614 (by decide +kernel)
private theorem arithBundle04_ranks_088 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 88 4 = 3687766 :=
  contactRankWindow_of_rec contact07 88 4 3687766 (by decide +kernel)
private theorem arithBundle04_ranks_092 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 92 4 = 3157291 :=
  contactRankWindow_of_rec contact07 92 4 3157291 (by decide +kernel)
private theorem arithBundle04_ranks_096 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 96 4 = 2675726 :=
  contactRankWindow_of_rec contact07 96 4 2675726 (by decide +kernel)
private theorem arithBundle04_ranks_100 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 100 4 = 2240850 :=
  contactRankWindow_of_rec contact07 100 4 2240850 (by decide +kernel)
private theorem arithBundle04_ranks_104 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 104 4 = 1850755 :=
  contactRankWindow_of_rec contact07 104 4 1850755 (by decide +kernel)
private theorem arithBundle04_ranks_108 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 108 4 = 1504118 :=
  contactRankWindow_of_rec contact07 108 4 1504118 (by decide +kernel)
private theorem arithBundle04_ranks_112 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 112 4 = 1198574 :=
  contactRankWindow_of_rec contact07 112 4 1198574 (by decide +kernel)
private theorem arithBundle04_ranks_116 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 116 4 = 932219 :=
  contactRankWindow_of_rec contact07 116 4 932219 (by decide +kernel)
private theorem arithBundle04_ranks_120 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 120 4 = 703870 :=
  contactRankWindow_of_rec contact07 120 4 703870 (by decide +kernel)
private theorem arithBundle04_ranks_124 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 124 4 = 511018 :=
  contactRankWindow_of_rec contact07 124 4 511018 (by decide +kernel)
private theorem arithBundle04_ranks_128 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 128 4 = 351763 :=
  contactRankWindow_of_rec contact07 128 4 351763 (by decide +kernel)
private theorem arithBundle04_ranks_132 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 132 4 = 225062 :=
  contactRankWindow_of_rec contact07 132 4 225062 (by decide +kernel)
private theorem arithBundle04_ranks_136 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 136 4 = 128262 :=
  contactRankWindow_of_rec contact07 136 4 128262 (by decide +kernel)
private theorem arithBundle04_ranks_140 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 140 4 = 59482 :=
  contactRankWindow_of_rec contact07 140 4 59482 (by decide +kernel)
private theorem arithBundle04_ranks_144 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 144 4 = 18013 :=
  contactRankWindow_of_rec contact07 144 4 18013 (by decide +kernel)
private theorem arithBundle04_ranks_148 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 148 4 = 1014 :=
  contactRankWindow_of_rec contact07 148 4 1014 (by decide +kernel)
private theorem arithBundle04_ranks_152 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 152 16 = 0 :=
  contactRankWindow_of_rec contact07 152 16 0 (by decide +kernel)
private theorem arithBundle04_prefix_ranks_00 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 8 = 59517228 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 4 4 30720414 28796814 arithBundle04_ranks_000 arithBundle04_ranks_004
private theorem arithBundle04_prefix_ranks_01 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 12 = 86457642 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 8 4 59517228 26940414 arithBundle04_prefix_ranks_00 arithBundle04_ranks_008
private theorem arithBundle04_prefix_ranks_02 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 16 = 111608856 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 12 4 86457642 25151214 arithBundle04_prefix_ranks_01 arithBundle04_ranks_012
private theorem arithBundle04_prefix_ranks_03 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 20 = 135038070 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 16 4 111608856 23429214 arithBundle04_prefix_ranks_02 arithBundle04_ranks_016
private theorem arithBundle04_prefix_ranks_04 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 24 = 156812484 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 20 4 135038070 21774414 arithBundle04_prefix_ranks_03 arithBundle04_ranks_020
private theorem arithBundle04_prefix_ranks_05 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 28 = 176999298 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 24 4 156812484 20186814 arithBundle04_prefix_ranks_04 arithBundle04_ranks_024
private theorem arithBundle04_prefix_ranks_06 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 32 = 195665712 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 28 4 176999298 18666414 arithBundle04_prefix_ranks_05 arithBundle04_ranks_028
private theorem arithBundle04_prefix_ranks_07 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 36 = 212878926 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 32 4 195665712 17213214 arithBundle04_prefix_ranks_06 arithBundle04_ranks_032
private theorem arithBundle04_prefix_ranks_08 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 40 = 228706140 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 36 4 212878926 15827214 arithBundle04_prefix_ranks_07 arithBundle04_ranks_036
private theorem arithBundle04_prefix_ranks_09 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 44 = 243214554 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 40 4 228706140 14508414 arithBundle04_prefix_ranks_08 arithBundle04_ranks_040
private theorem arithBundle04_prefix_ranks_10 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 48 = 256471368 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 44 4 243214554 13256814 arithBundle04_prefix_ranks_09 arithBundle04_ranks_044
private theorem arithBundle04_prefix_ranks_11 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 52 = 268543782 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 48 4 256471368 12072414 arithBundle04_prefix_ranks_10 arithBundle04_ranks_048
private theorem arithBundle04_prefix_ranks_12 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 56 = 279498906 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 52 4 268543782 10955124 arithBundle04_prefix_ranks_11 arithBundle04_ranks_052
private theorem arithBundle04_prefix_ranks_13 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 60 = 289402970 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 56 4 279498906 9904064 arithBundle04_prefix_ranks_12 arithBundle04_ranks_056
private theorem arithBundle04_prefix_ranks_14 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 64 = 298320880 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 60 4 289402970 8917910 arithBundle04_prefix_ranks_13 arithBundle04_ranks_060
private theorem arithBundle04_prefix_ranks_15 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 68 = 306316078 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 64 4 298320880 7995198 arithBundle04_prefix_ranks_14 arithBundle04_ranks_064
private theorem arithBundle04_prefix_ranks_16 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 72 = 313450121 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 68 4 306316078 7134043 arithBundle04_prefix_ranks_15 arithBundle04_ranks_068
private theorem arithBundle04_prefix_ranks_17 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 76 = 319782823 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 72 4 313450121 6332702 arithBundle04_prefix_ranks_16 arithBundle04_ranks_072
private theorem arithBundle04_prefix_ranks_18 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 80 = 325372065 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 76 4 319782823 5589242 arithBundle04_prefix_ranks_17 arithBundle04_ranks_076
private theorem arithBundle04_prefix_ranks_19 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 84 = 330273812 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 80 4 325372065 4901747 arithBundle04_prefix_ranks_18 arithBundle04_ranks_080
private theorem arithBundle04_prefix_ranks_20 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 88 = 334542426 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 84 4 330273812 4268614 arithBundle04_prefix_ranks_19 arithBundle04_ranks_084
private theorem arithBundle04_prefix_ranks_21 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 92 = 338230192 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 88 4 334542426 3687766 arithBundle04_prefix_ranks_20 arithBundle04_ranks_088
private theorem arithBundle04_prefix_ranks_22 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 96 = 341387483 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 92 4 338230192 3157291 arithBundle04_prefix_ranks_21 arithBundle04_ranks_092
private theorem arithBundle04_prefix_ranks_23 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 100 = 344063209 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 96 4 341387483 2675726 arithBundle04_prefix_ranks_22 arithBundle04_ranks_096
private theorem arithBundle04_prefix_ranks_24 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 104 = 346304059 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 100 4 344063209 2240850 arithBundle04_prefix_ranks_23 arithBundle04_ranks_100
private theorem arithBundle04_prefix_ranks_25 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 108 = 348154814 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 104 4 346304059 1850755 arithBundle04_prefix_ranks_24 arithBundle04_ranks_104
private theorem arithBundle04_prefix_ranks_26 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 112 = 349658932 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 108 4 348154814 1504118 arithBundle04_prefix_ranks_25 arithBundle04_ranks_108
private theorem arithBundle04_prefix_ranks_27 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 116 = 350857506 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 112 4 349658932 1198574 arithBundle04_prefix_ranks_26 arithBundle04_ranks_112
private theorem arithBundle04_prefix_ranks_28 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 120 = 351789725 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 116 4 350857506 932219 arithBundle04_prefix_ranks_27 arithBundle04_ranks_116
private theorem arithBundle04_prefix_ranks_29 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 124 = 352493595 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 120 4 351789725 703870 arithBundle04_prefix_ranks_28 arithBundle04_ranks_120
private theorem arithBundle04_prefix_ranks_30 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 128 = 353004613 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 124 4 352493595 511018 arithBundle04_prefix_ranks_29 arithBundle04_ranks_124
private theorem arithBundle04_prefix_ranks_31 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 132 = 353356376 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 128 4 353004613 351763 arithBundle04_prefix_ranks_30 arithBundle04_ranks_128
private theorem arithBundle04_prefix_ranks_32 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 136 = 353581438 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 132 4 353356376 225062 arithBundle04_prefix_ranks_31 arithBundle04_ranks_132
private theorem arithBundle04_prefix_ranks_33 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 140 = 353709700 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 136 4 353581438 128262 arithBundle04_prefix_ranks_32 arithBundle04_ranks_136
private theorem arithBundle04_prefix_ranks_34 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 144 = 353769182 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 140 4 353709700 59482 arithBundle04_prefix_ranks_33 arithBundle04_ranks_140
private theorem arithBundle04_prefix_ranks_35 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 148 = 353787195 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 144 4 353769182 18013 arithBundle04_prefix_ranks_34 arithBundle04_ranks_144
private theorem arithBundle04_prefix_ranks_36 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 152 = 353788209 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 148 4 353787195 1014 arithBundle04_prefix_ranks_35 arithBundle04_ranks_148
private theorem arithBundle04_prefix_ranks_37 : arithBundle04_sliceWindow (auxiliaryRankSlice contact07) 0 168 = 353788209 :=
  arithBundle04_combineSlices (auxiliaryRankSlice contact07) 0 152 16 353788209 0 arithBundle04_prefix_ranks_36 arithBundle04_ranks_152

theorem contact07_margin : sourceMargin contact07 :=
  arithBundle04_margin_of_checked_counts contact07 168 2017326801966088 116371310481652 7785619784 353788209
    rfl arithBundle04_ordinary_columns arithBundle04_prefix_columns_40 arithBundle04_ordinary_ranks arithBundle04_prefix_ranks_37 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle05_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle05_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle05_sliceWindow f a b = x) (hy : arithBundle05_sliceWindow f (a+b) c = y) :
    arithBundle05_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle05_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle05_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle05_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle05_sliceWindow,Nat.zero_add]

private theorem arithBundle05_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle05_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle05_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle05_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle05_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle05_ordinary_columns : ordinaryColumnCount contact08 = 2013394915485440 := by decide +kernel
private theorem arithBundle05_columns_000 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 4 = 8339101519894 :=
  contactColumnsWindow_fast contact08 0 4 8339101519894 (by decide +kernel)
private theorem arithBundle05_columns_004 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 4 4 = 7936936157158 :=
  contactColumnsWindow_fast contact08 4 4 7936936157158 (by decide +kernel)
private theorem arithBundle05_columns_008 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 8 4 = 7544755813366 :=
  contactColumnsWindow_fast contact08 8 4 7544755813366 (by decide +kernel)
private theorem arithBundle05_columns_012 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 12 4 = 7162560641183 :=
  contactColumnsWindow_fast contact08 12 4 7162560641183 (by decide +kernel)
private theorem arithBundle05_columns_016 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 16 4 = 6790389613098 :=
  contactColumnsWindow_fast contact08 16 4 6790389613098 (by decide +kernel)
private theorem arithBundle05_columns_020 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 20 4 = 6428227538565 :=
  contactColumnsWindow_fast contact08 20 4 6428227538565 (by decide +kernel)
private theorem arithBundle05_columns_024 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 24 4 = 6076054586354 :=
  contactColumnsWindow_fast contact08 24 4 6076054586354 (by decide +kernel)
private theorem arithBundle05_columns_028 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 28 4 = 5733869165056 :=
  contactColumnsWindow_fast contact08 28 4 5733869165056 (by decide +kernel)
private theorem arithBundle05_columns_032 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 32 4 = 5401674482527 :=
  contactColumnsWindow_fast contact08 32 4 5401674482527 (by decide +kernel)
private theorem arithBundle05_columns_036 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 36 4 = 5079508882434 :=
  contactColumnsWindow_fast contact08 36 4 5079508882434 (by decide +kernel)
private theorem arithBundle05_columns_040 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 40 4 = 4767353085004 :=
  contactColumnsWindow_fast contact08 40 4 4767353085004 (by decide +kernel)
private theorem arithBundle05_columns_044 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 44 4 = 4465188390867 :=
  contactColumnsWindow_fast contact08 44 4 4465188390867 (by decide +kernel)
private theorem arithBundle05_columns_048 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 48 4 = 4173016170454 :=
  contactColumnsWindow_fast contact08 48 4 4173016170454 (by decide +kernel)
private theorem arithBundle05_columns_052 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 52 4 = 3890838249606 :=
  contactColumnsWindow_fast contact08 52 4 3890838249606 (by decide +kernel)
private theorem arithBundle05_columns_056 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 56 4 = 3618696907838 :=
  contactColumnsWindow_fast contact08 56 4 3618696907838 (by decide +kernel)
private theorem arithBundle05_columns_060 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 60 4 = 3356564644226 :=
  contactColumnsWindow_fast contact08 60 4 3356564644226 (by decide +kernel)
private theorem arithBundle05_columns_064 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 64 4 = 3104427330165 :=
  contactColumnsWindow_fast contact08 64 4 3104427330165 (by decide +kernel)
private theorem arithBundle05_columns_068 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 68 4 = 2862282433024 :=
  contactColumnsWindow_fast contact08 68 4 2862282433024 (by decide +kernel)
private theorem arithBundle05_columns_072 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 72 4 = 2630133894084 :=
  contactColumnsWindow_fast contact08 72 4 2630133894084 (by decide +kernel)
private theorem arithBundle05_columns_076 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 76 4 = 2408023636535 :=
  contactColumnsWindow_fast contact08 76 4 2408023636535 (by decide +kernel)
private theorem arithBundle05_columns_080 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 80 4 = 2195919294188 :=
  contactColumnsWindow_fast contact08 80 4 2195919294188 (by decide +kernel)
private theorem arithBundle05_columns_084 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 84 4 = 1993809341943 :=
  contactColumnsWindow_fast contact08 84 4 1993809341943 (by decide +kernel)
private theorem arithBundle05_columns_088 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 88 4 = 1801691842915 :=
  contactColumnsWindow_fast contact08 88 4 1801691842915 (by decide +kernel)
private theorem arithBundle05_columns_092 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 92 4 = 1619573631108 :=
  contactColumnsWindow_fast contact08 92 4 1619573631108 (by decide +kernel)
private theorem arithBundle05_columns_096 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 96 4 = 1447493438273 :=
  contactColumnsWindow_fast contact08 96 4 1447493438273 (by decide +kernel)
private theorem arithBundle05_columns_100 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 100 4 = 1285417028785 :=
  contactColumnsWindow_fast contact08 100 4 1285417028785 (by decide +kernel)
private theorem arithBundle05_columns_104 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 104 4 = 1133334643704 :=
  contactColumnsWindow_fast contact08 104 4 1133334643704 (by decide +kernel)
private theorem arithBundle05_columns_108 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 108 4 = 991244387758 :=
  contactColumnsWindow_fast contact08 108 4 991244387758 (by decide +kernel)
private theorem arithBundle05_columns_112 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 112 4 = 859156440612 :=
  contactColumnsWindow_fast contact08 112 4 859156440612 (by decide +kernel)
private theorem arithBundle05_columns_116 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 116 4 = 737106532157 :=
  contactColumnsWindow_fast contact08 116 4 737106532157 (by decide +kernel)
private theorem arithBundle05_columns_120 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 120 4 = 625057956202 :=
  contactColumnsWindow_fast contact08 120 4 625057956202 (by decide +kernel)
private theorem arithBundle05_columns_124 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 124 4 = 523003070250 :=
  contactColumnsWindow_fast contact08 124 4 523003070250 (by decide +kernel)
private theorem arithBundle05_columns_128 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 128 4 = 430940060332 :=
  contactColumnsWindow_fast contact08 128 4 430940060332 (by decide +kernel)
private theorem arithBundle05_columns_132 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 132 4 = 348883270325 :=
  contactColumnsWindow_fast contact08 132 4 348883270325 (by decide +kernel)
private theorem arithBundle05_columns_136 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 136 4 = 276858907729 :=
  contactColumnsWindow_fast contact08 136 4 276858907729 (by decide +kernel)
private theorem arithBundle05_columns_140 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 140 4 = 214747119574 :=
  contactColumnsWindow_fast contact08 140 4 214747119574 (by decide +kernel)
private theorem arithBundle05_columns_144 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 144 4 = 162262315287 :=
  contactColumnsWindow_fast contact08 144 4 162262315287 (by decide +kernel)
private theorem arithBundle05_columns_148 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 148 4 = 118952079186 :=
  contactColumnsWindow_fast contact08 148 4 118952079186 (by decide +kernel)
private theorem arithBundle05_columns_152 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 152 4 = 84221638741 :=
  contactColumnsWindow_fast contact08 152 4 84221638741 (by decide +kernel)
private theorem arithBundle05_columns_156 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 156 4 = 57311754457 :=
  contactColumnsWindow_fast contact08 156 4 57311754457 (by decide +kernel)
private theorem arithBundle05_columns_160 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 160 4 = 37249088412 :=
  contactColumnsWindow_fast contact08 160 4 37249088412 (by decide +kernel)
private theorem arithBundle05_columns_164 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 164 2 = 12945111425 :=
  contactColumnsWindow_fast contact08 164 2 12945111425 (by decide +kernel)
private theorem arithBundle05_prefix_columns_00 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 8 = 16276037677052 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 4 4 8339101519894 7936936157158 arithBundle05_columns_000 arithBundle05_columns_004
private theorem arithBundle05_prefix_columns_01 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 12 = 23820793490418 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 8 4 16276037677052 7544755813366 arithBundle05_prefix_columns_00 arithBundle05_columns_008
private theorem arithBundle05_prefix_columns_02 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 16 = 30983354131601 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 12 4 23820793490418 7162560641183 arithBundle05_prefix_columns_01 arithBundle05_columns_012
private theorem arithBundle05_prefix_columns_03 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 20 = 37773743744699 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 16 4 30983354131601 6790389613098 arithBundle05_prefix_columns_02 arithBundle05_columns_016
private theorem arithBundle05_prefix_columns_04 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 24 = 44201971283264 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 20 4 37773743744699 6428227538565 arithBundle05_prefix_columns_03 arithBundle05_columns_020
private theorem arithBundle05_prefix_columns_05 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 28 = 50278025869618 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 24 4 44201971283264 6076054586354 arithBundle05_prefix_columns_04 arithBundle05_columns_024
private theorem arithBundle05_prefix_columns_06 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 32 = 56011895034674 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 28 4 50278025869618 5733869165056 arithBundle05_prefix_columns_05 arithBundle05_columns_028
private theorem arithBundle05_prefix_columns_07 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 36 = 61413569517201 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 32 4 56011895034674 5401674482527 arithBundle05_prefix_columns_06 arithBundle05_columns_032
private theorem arithBundle05_prefix_columns_08 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 40 = 66493078399635 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 36 4 61413569517201 5079508882434 arithBundle05_prefix_columns_07 arithBundle05_columns_036
private theorem arithBundle05_prefix_columns_09 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 44 = 71260431484639 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 40 4 66493078399635 4767353085004 arithBundle05_prefix_columns_08 arithBundle05_columns_040
private theorem arithBundle05_prefix_columns_10 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 48 = 75725619875506 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 44 4 71260431484639 4465188390867 arithBundle05_prefix_columns_09 arithBundle05_columns_044
private theorem arithBundle05_prefix_columns_11 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 52 = 79898636045960 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 48 4 75725619875506 4173016170454 arithBundle05_prefix_columns_10 arithBundle05_columns_048
private theorem arithBundle05_prefix_columns_12 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 56 = 83789474295566 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 52 4 79898636045960 3890838249606 arithBundle05_prefix_columns_11 arithBundle05_columns_052
private theorem arithBundle05_prefix_columns_13 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 60 = 87408171203404 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 56 4 83789474295566 3618696907838 arithBundle05_prefix_columns_12 arithBundle05_columns_056
private theorem arithBundle05_prefix_columns_14 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 64 = 90764735847630 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 60 4 87408171203404 3356564644226 arithBundle05_prefix_columns_13 arithBundle05_columns_060
private theorem arithBundle05_prefix_columns_15 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 68 = 93869163177795 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 64 4 90764735847630 3104427330165 arithBundle05_prefix_columns_14 arithBundle05_columns_064
private theorem arithBundle05_prefix_columns_16 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 72 = 96731445610819 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 68 4 93869163177795 2862282433024 arithBundle05_prefix_columns_15 arithBundle05_columns_068
private theorem arithBundle05_prefix_columns_17 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 76 = 99361579504903 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 72 4 96731445610819 2630133894084 arithBundle05_prefix_columns_16 arithBundle05_columns_072
private theorem arithBundle05_prefix_columns_18 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 80 = 101769603141438 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 76 4 99361579504903 2408023636535 arithBundle05_prefix_columns_17 arithBundle05_columns_076
private theorem arithBundle05_prefix_columns_19 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 84 = 103965522435626 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 80 4 101769603141438 2195919294188 arithBundle05_prefix_columns_18 arithBundle05_columns_080
private theorem arithBundle05_prefix_columns_20 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 88 = 105959331777569 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 84 4 103965522435626 1993809341943 arithBundle05_prefix_columns_19 arithBundle05_columns_084
private theorem arithBundle05_prefix_columns_21 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 92 = 107761023620484 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 88 4 105959331777569 1801691842915 arithBundle05_prefix_columns_20 arithBundle05_columns_088
private theorem arithBundle05_prefix_columns_22 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 96 = 109380597251592 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 92 4 107761023620484 1619573631108 arithBundle05_prefix_columns_21 arithBundle05_columns_092
private theorem arithBundle05_prefix_columns_23 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 100 = 110828090689865 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 96 4 109380597251592 1447493438273 arithBundle05_prefix_columns_22 arithBundle05_columns_096
private theorem arithBundle05_prefix_columns_24 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 104 = 112113507718650 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 100 4 110828090689865 1285417028785 arithBundle05_prefix_columns_23 arithBundle05_columns_100
private theorem arithBundle05_prefix_columns_25 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 108 = 113246842362354 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 104 4 112113507718650 1133334643704 arithBundle05_prefix_columns_24 arithBundle05_columns_104
private theorem arithBundle05_prefix_columns_26 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 112 = 114238086750112 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 108 4 113246842362354 991244387758 arithBundle05_prefix_columns_25 arithBundle05_columns_108
private theorem arithBundle05_prefix_columns_27 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 116 = 115097243190724 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 112 4 114238086750112 859156440612 arithBundle05_prefix_columns_26 arithBundle05_columns_112
private theorem arithBundle05_prefix_columns_28 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 120 = 115834349722881 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 116 4 115097243190724 737106532157 arithBundle05_prefix_columns_27 arithBundle05_columns_116
private theorem arithBundle05_prefix_columns_29 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 124 = 116459407679083 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 120 4 115834349722881 625057956202 arithBundle05_prefix_columns_28 arithBundle05_columns_120
private theorem arithBundle05_prefix_columns_30 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 128 = 116982410749333 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 124 4 116459407679083 523003070250 arithBundle05_prefix_columns_29 arithBundle05_columns_124
private theorem arithBundle05_prefix_columns_31 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 132 = 117413350809665 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 128 4 116982410749333 430940060332 arithBundle05_prefix_columns_30 arithBundle05_columns_128
private theorem arithBundle05_prefix_columns_32 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 136 = 117762234079990 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 132 4 117413350809665 348883270325 arithBundle05_prefix_columns_31 arithBundle05_columns_132
private theorem arithBundle05_prefix_columns_33 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 140 = 118039092987719 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 136 4 117762234079990 276858907729 arithBundle05_prefix_columns_32 arithBundle05_columns_136
private theorem arithBundle05_prefix_columns_34 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 144 = 118253840107293 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 140 4 118039092987719 214747119574 arithBundle05_prefix_columns_33 arithBundle05_columns_140
private theorem arithBundle05_prefix_columns_35 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 148 = 118416102422580 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 144 4 118253840107293 162262315287 arithBundle05_prefix_columns_34 arithBundle05_columns_144
private theorem arithBundle05_prefix_columns_36 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 152 = 118535054501766 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 148 4 118416102422580 118952079186 arithBundle05_prefix_columns_35 arithBundle05_columns_148
private theorem arithBundle05_prefix_columns_37 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 156 = 118619276140507 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 152 4 118535054501766 84221638741 arithBundle05_prefix_columns_36 arithBundle05_columns_152
private theorem arithBundle05_prefix_columns_38 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 160 = 118676587894964 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 156 4 118619276140507 57311754457 arithBundle05_prefix_columns_37 arithBundle05_columns_156
private theorem arithBundle05_prefix_columns_39 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 164 = 118713836983376 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 160 4 118676587894964 37249088412 arithBundle05_prefix_columns_38 arithBundle05_columns_160
private theorem arithBundle05_prefix_columns_40 : arithBundle05_sliceWindow (auxiliaryColumnSlice contact08) 0 166 = 118726782094801 :=
  arithBundle05_combineSlices (auxiliaryColumnSlice contact08) 0 164 2 118713836983376 12945111425 arithBundle05_prefix_columns_39 arithBundle05_columns_164

private theorem arithBundle05_ordinary_ranks : ordinaryRankBound contact08 = 7771626090 := by decide +kernel
private theorem arithBundle05_ranks_000 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 4 = 31418376 :=
  contactRankWindow_of_rec contact08 0 4 31418376 (by decide +kernel)
private theorem arithBundle05_ranks_004 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 4 4 = 29448456 :=
  contactRankWindow_of_rec contact08 4 4 29448456 (by decide +kernel)
private theorem arithBundle05_ranks_008 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 8 4 = 27547656 :=
  contactRankWindow_of_rec contact08 8 4 27547656 (by decide +kernel)
private theorem arithBundle05_ranks_012 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 12 4 = 25715976 :=
  contactRankWindow_of_rec contact08 12 4 25715976 (by decide +kernel)
private theorem arithBundle05_ranks_016 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 16 4 = 23953416 :=
  contactRankWindow_of_rec contact08 16 4 23953416 (by decide +kernel)
private theorem arithBundle05_ranks_020 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 20 4 = 22259976 :=
  contactRankWindow_of_rec contact08 20 4 22259976 (by decide +kernel)
private theorem arithBundle05_ranks_024 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 24 4 = 20635656 :=
  contactRankWindow_of_rec contact08 24 4 20635656 (by decide +kernel)
private theorem arithBundle05_ranks_028 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 28 4 = 19080456 :=
  contactRankWindow_of_rec contact08 28 4 19080456 (by decide +kernel)
private theorem arithBundle05_ranks_032 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 32 4 = 17594376 :=
  contactRankWindow_of_rec contact08 32 4 17594376 (by decide +kernel)
private theorem arithBundle05_ranks_036 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 36 4 = 16177416 :=
  contactRankWindow_of_rec contact08 36 4 16177416 (by decide +kernel)
private theorem arithBundle05_ranks_040 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 40 4 = 14829576 :=
  contactRankWindow_of_rec contact08 40 4 14829576 (by decide +kernel)
private theorem arithBundle05_ranks_044 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 44 4 = 13550856 :=
  contactRankWindow_of_rec contact08 44 4 13550856 (by decide +kernel)
private theorem arithBundle05_ranks_048 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 48 4 = 12341256 :=
  contactRankWindow_of_rec contact08 48 4 12341256 (by decide +kernel)
private theorem arithBundle05_ranks_052 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 52 4 = 11200354 :=
  contactRankWindow_of_rec contact08 52 4 11200354 (by decide +kernel)
private theorem arithBundle05_ranks_056 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 56 4 = 10126958 :=
  contactRankWindow_of_rec contact08 56 4 10126958 (by decide +kernel)
private theorem arithBundle05_ranks_060 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 60 4 = 9119728 :=
  contactRankWindow_of_rec contact08 60 4 9119728 (by decide +kernel)
private theorem arithBundle05_ranks_064 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 64 4 = 8177156 :=
  contactRankWindow_of_rec contact08 64 4 8177156 (by decide +kernel)
private theorem arithBundle05_ranks_068 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 68 4 = 7297354 :=
  contactRankWindow_of_rec contact08 68 4 7297354 (by decide +kernel)
private theorem arithBundle05_ranks_072 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 72 4 = 6478552 :=
  contactRankWindow_of_rec contact08 72 4 6478552 (by decide +kernel)
private theorem arithBundle05_ranks_076 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 76 4 = 5718764 :=
  contactRankWindow_of_rec contact08 76 4 5718764 (by decide +kernel)
private theorem arithBundle05_ranks_080 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 80 4 = 5016066 :=
  contactRankWindow_of_rec contact08 80 4 5016066 (by decide +kernel)
private theorem arithBundle05_ranks_084 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 84 4 = 4368832 :=
  contactRankWindow_of_rec contact08 84 4 4368832 (by decide +kernel)
private theorem arithBundle05_ranks_088 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 88 4 = 3774932 :=
  contactRankWindow_of_rec contact08 88 4 3774932 (by decide +kernel)
private theorem arithBundle05_ranks_092 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 92 4 = 3232442 :=
  contactRankWindow_of_rec contact08 92 4 3232442 (by decide +kernel)
private theorem arithBundle05_ranks_096 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 96 4 = 2739880 :=
  contactRankWindow_of_rec contact08 96 4 2739880 (by decide +kernel)
private theorem arithBundle05_ranks_100 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 100 4 = 2294972 :=
  contactRankWindow_of_rec contact08 100 4 2294972 (by decide +kernel)
private theorem arithBundle05_ranks_104 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 104 4 = 1895794 :=
  contactRankWindow_of_rec contact08 104 4 1895794 (by decide +kernel)
private theorem arithBundle05_ranks_108 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 108 4 = 1541008 :=
  contactRankWindow_of_rec contact08 108 4 1541008 (by decide +kernel)
private theorem arithBundle05_ranks_112 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 112 4 = 1228196 :=
  contactRankWindow_of_rec contact08 112 4 1228196 (by decide +kernel)
private theorem arithBundle05_ranks_116 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 116 4 = 955434 :=
  contactRankWindow_of_rec contact08 116 4 955434 (by decide +kernel)
private theorem arithBundle05_ranks_120 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 120 4 = 721528 :=
  contactRankWindow_of_rec contact08 120 4 721528 (by decide +kernel)
private theorem arithBundle05_ranks_124 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 124 4 = 523916 :=
  contactRankWindow_of_rec contact08 124 4 523916 (by decide +kernel)
private theorem arithBundle05_ranks_128 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 128 4 = 360674 :=
  contactRankWindow_of_rec contact08 128 4 360674 (by decide +kernel)
private theorem arithBundle05_ranks_132 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 132 4 = 230752 :=
  contactRankWindow_of_rec contact08 132 4 230752 (by decide +kernel)
private theorem arithBundle05_ranks_136 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 136 4 = 131444 :=
  contactRankWindow_of_rec contact08 136 4 131444 (by decide +kernel)
private theorem arithBundle05_ranks_140 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 140 4 = 60871 :=
  contactRankWindow_of_rec contact08 140 4 60871 (by decide +kernel)
private theorem arithBundle05_ranks_144 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 144 4 = 18404 :=
  contactRankWindow_of_rec contact08 144 4 18404 (by decide +kernel)
private theorem arithBundle05_ranks_148 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 148 4 = 1035 :=
  contactRankWindow_of_rec contact08 148 4 1035 (by decide +kernel)
private theorem arithBundle05_ranks_152 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 152 14 = 0 :=
  contactRankWindow_of_rec contact08 152 14 0 (by decide +kernel)
private theorem arithBundle05_prefix_ranks_00 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 8 = 60866832 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 4 4 31418376 29448456 arithBundle05_ranks_000 arithBundle05_ranks_004
private theorem arithBundle05_prefix_ranks_01 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 12 = 88414488 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 8 4 60866832 27547656 arithBundle05_prefix_ranks_00 arithBundle05_ranks_008
private theorem arithBundle05_prefix_ranks_02 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 16 = 114130464 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 12 4 88414488 25715976 arithBundle05_prefix_ranks_01 arithBundle05_ranks_012
private theorem arithBundle05_prefix_ranks_03 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 20 = 138083880 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 16 4 114130464 23953416 arithBundle05_prefix_ranks_02 arithBundle05_ranks_016
private theorem arithBundle05_prefix_ranks_04 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 24 = 160343856 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 20 4 138083880 22259976 arithBundle05_prefix_ranks_03 arithBundle05_ranks_020
private theorem arithBundle05_prefix_ranks_05 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 28 = 180979512 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 24 4 160343856 20635656 arithBundle05_prefix_ranks_04 arithBundle05_ranks_024
private theorem arithBundle05_prefix_ranks_06 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 32 = 200059968 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 28 4 180979512 19080456 arithBundle05_prefix_ranks_05 arithBundle05_ranks_028
private theorem arithBundle05_prefix_ranks_07 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 36 = 217654344 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 32 4 200059968 17594376 arithBundle05_prefix_ranks_06 arithBundle05_ranks_032
private theorem arithBundle05_prefix_ranks_08 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 40 = 233831760 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 36 4 217654344 16177416 arithBundle05_prefix_ranks_07 arithBundle05_ranks_036
private theorem arithBundle05_prefix_ranks_09 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 44 = 248661336 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 40 4 233831760 14829576 arithBundle05_prefix_ranks_08 arithBundle05_ranks_040
private theorem arithBundle05_prefix_ranks_10 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 48 = 262212192 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 44 4 248661336 13550856 arithBundle05_prefix_ranks_09 arithBundle05_ranks_044
private theorem arithBundle05_prefix_ranks_11 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 52 = 274553448 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 48 4 262212192 12341256 arithBundle05_prefix_ranks_10 arithBundle05_ranks_048
private theorem arithBundle05_prefix_ranks_12 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 56 = 285753802 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 52 4 274553448 11200354 arithBundle05_prefix_ranks_11 arithBundle05_ranks_052
private theorem arithBundle05_prefix_ranks_13 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 60 = 295880760 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 56 4 285753802 10126958 arithBundle05_prefix_ranks_12 arithBundle05_ranks_056
private theorem arithBundle05_prefix_ranks_14 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 64 = 305000488 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 60 4 295880760 9119728 arithBundle05_prefix_ranks_13 arithBundle05_ranks_060
private theorem arithBundle05_prefix_ranks_15 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 68 = 313177644 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 64 4 305000488 8177156 arithBundle05_prefix_ranks_14 arithBundle05_ranks_064
private theorem arithBundle05_prefix_ranks_16 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 72 = 320474998 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 68 4 313177644 7297354 arithBundle05_prefix_ranks_15 arithBundle05_ranks_068
private theorem arithBundle05_prefix_ranks_17 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 76 = 326953550 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 72 4 320474998 6478552 arithBundle05_prefix_ranks_16 arithBundle05_ranks_072
private theorem arithBundle05_prefix_ranks_18 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 80 = 332672314 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 76 4 326953550 5718764 arithBundle05_prefix_ranks_17 arithBundle05_ranks_076
private theorem arithBundle05_prefix_ranks_19 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 84 = 337688380 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 80 4 332672314 5016066 arithBundle05_prefix_ranks_18 arithBundle05_ranks_080
private theorem arithBundle05_prefix_ranks_20 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 88 = 342057212 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 84 4 337688380 4368832 arithBundle05_prefix_ranks_19 arithBundle05_ranks_084
private theorem arithBundle05_prefix_ranks_21 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 92 = 345832144 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 88 4 342057212 3774932 arithBundle05_prefix_ranks_20 arithBundle05_ranks_088
private theorem arithBundle05_prefix_ranks_22 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 96 = 349064586 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 92 4 345832144 3232442 arithBundle05_prefix_ranks_21 arithBundle05_ranks_092
private theorem arithBundle05_prefix_ranks_23 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 100 = 351804466 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 96 4 349064586 2739880 arithBundle05_prefix_ranks_22 arithBundle05_ranks_096
private theorem arithBundle05_prefix_ranks_24 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 104 = 354099438 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 100 4 351804466 2294972 arithBundle05_prefix_ranks_23 arithBundle05_ranks_100
private theorem arithBundle05_prefix_ranks_25 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 108 = 355995232 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 104 4 354099438 1895794 arithBundle05_prefix_ranks_24 arithBundle05_ranks_104
private theorem arithBundle05_prefix_ranks_26 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 112 = 357536240 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 108 4 355995232 1541008 arithBundle05_prefix_ranks_25 arithBundle05_ranks_108
private theorem arithBundle05_prefix_ranks_27 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 116 = 358764436 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 112 4 357536240 1228196 arithBundle05_prefix_ranks_26 arithBundle05_ranks_112
private theorem arithBundle05_prefix_ranks_28 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 120 = 359719870 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 116 4 358764436 955434 arithBundle05_prefix_ranks_27 arithBundle05_ranks_116
private theorem arithBundle05_prefix_ranks_29 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 124 = 360441398 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 120 4 359719870 721528 arithBundle05_prefix_ranks_28 arithBundle05_ranks_120
private theorem arithBundle05_prefix_ranks_30 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 128 = 360965314 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 124 4 360441398 523916 arithBundle05_prefix_ranks_29 arithBundle05_ranks_124
private theorem arithBundle05_prefix_ranks_31 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 132 = 361325988 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 128 4 360965314 360674 arithBundle05_prefix_ranks_30 arithBundle05_ranks_128
private theorem arithBundle05_prefix_ranks_32 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 136 = 361556740 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 132 4 361325988 230752 arithBundle05_prefix_ranks_31 arithBundle05_ranks_132
private theorem arithBundle05_prefix_ranks_33 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 140 = 361688184 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 136 4 361556740 131444 arithBundle05_prefix_ranks_32 arithBundle05_ranks_136
private theorem arithBundle05_prefix_ranks_34 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 144 = 361749055 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 140 4 361688184 60871 arithBundle05_prefix_ranks_33 arithBundle05_ranks_140
private theorem arithBundle05_prefix_ranks_35 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 148 = 361767459 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 144 4 361749055 18404 arithBundle05_prefix_ranks_34 arithBundle05_ranks_144
private theorem arithBundle05_prefix_ranks_36 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 152 = 361768494 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 148 4 361767459 1035 arithBundle05_prefix_ranks_35 arithBundle05_ranks_148
private theorem arithBundle05_prefix_ranks_37 : arithBundle05_sliceWindow (auxiliaryRankSlice contact08) 0 166 = 361768494 :=
  arithBundle05_combineSlices (auxiliaryRankSlice contact08) 0 152 14 361768494 0 arithBundle05_prefix_ranks_36 arithBundle05_ranks_152

theorem contact08_margin : sourceMargin contact08 :=
  arithBundle05_margin_of_checked_counts contact08 166 2013394915485440 118726782094801 7771626090 361768494
    rfl arithBundle05_ordinary_columns arithBundle05_prefix_columns_40 arithBundle05_ordinary_ranks arithBundle05_prefix_ranks_37 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle06_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle06_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle06_sliceWindow f a b = x) (hy : arithBundle06_sliceWindow f (a+b) c = y) :
    arithBundle06_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle06_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle06_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle06_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle06_sliceWindow,Nat.zero_add]

private theorem arithBundle06_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle06_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle06_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle06_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle06_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle06_ordinary_columns : ordinaryColumnCount contact13 = 410536038925851 := by decide +kernel
private theorem arithBundle06_columns_000 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 4 = 3650446289535 :=
  contactColumnsWindow_fast contact13 0 4 3650446289535 (by decide +kernel)
private theorem arithBundle06_columns_004 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 4 4 = 3429489503160 :=
  contactColumnsWindow_fast contact13 4 4 3429489503160 (by decide +kernel)
private theorem arithBundle06_columns_008 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 8 4 = 3215476608648 :=
  contactColumnsWindow_fast contact13 8 4 3215476608648 (by decide +kernel)
private theorem arithBundle06_columns_012 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 12 4 = 3008399670360 :=
  contactColumnsWindow_fast contact13 12 4 3008399670360 (by decide +kernel)
private theorem arithBundle06_columns_016 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 16 4 = 2808256513041 :=
  contactColumnsWindow_fast contact13 16 4 2808256513041 (by decide +kernel)
private theorem arithBundle06_columns_020 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 20 4 = 2615055590546 :=
  contactColumnsWindow_fast contact13 20 4 2615055590546 (by decide +kernel)
private theorem arithBundle06_columns_024 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 24 4 = 2428832451518 :=
  contactColumnsWindow_fast contact13 24 4 2428832451518 (by decide +kernel)
private theorem arithBundle06_columns_028 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 28 4 = 2249554515936 :=
  contactColumnsWindow_fast contact13 28 4 2249554515936 (by decide +kernel)
private theorem arithBundle06_columns_032 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 32 4 = 2077214969484 :=
  contactColumnsWindow_fast contact13 32 4 2077214969484 (by decide +kernel)
private theorem arithBundle06_columns_036 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 36 4 = 1911812821515 :=
  contactColumnsWindow_fast contact13 36 4 1911812821515 (by decide +kernel)
private theorem arithBundle06_columns_040 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 40 4 = 1753355298098 :=
  contactColumnsWindow_fast contact13 40 4 1753355298098 (by decide +kernel)
private theorem arithBundle06_columns_044 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 44 4 = 1601875813502 :=
  contactColumnsWindow_fast contact13 44 4 1601875813502 (by decide +kernel)
private theorem arithBundle06_columns_048 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 48 4 = 1457338955820 :=
  contactColumnsWindow_fast contact13 48 4 1457338955820 (by decide +kernel)
private theorem arithBundle06_columns_052 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 52 4 = 1319740735608 :=
  contactColumnsWindow_fast contact13 52 4 1319740735608 (by decide +kernel)
private theorem arithBundle06_columns_056 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 56 4 = 1189079596989 :=
  contactColumnsWindow_fast contact13 56 4 1189079596989 (by decide +kernel)
private theorem arithBundle06_columns_060 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 60 4 = 1065365707059 :=
  contactColumnsWindow_fast contact13 60 4 1065365707059 (by decide +kernel)
private theorem arithBundle06_columns_064 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 64 4 = 948629739024 :=
  contactColumnsWindow_fast contact13 64 4 948629739024 (by decide +kernel)
private theorem arithBundle06_columns_068 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 68 4 = 838833904968 :=
  contactColumnsWindow_fast contact13 68 4 838833904968 (by decide +kernel)
private theorem arithBundle06_columns_072 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 72 4 = 735976968732 :=
  contactColumnsWindow_fast contact13 72 4 735976968732 (by decide +kernel)
private theorem arithBundle06_columns_076 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 76 4 = 640056877688 :=
  contactColumnsWindow_fast contact13 76 4 640056877688 (by decide +kernel)
private theorem arithBundle06_columns_080 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 80 4 = 551087663925 :=
  contactColumnsWindow_fast contact13 80 4 551087663925 (by decide +kernel)
private theorem arithBundle06_columns_084 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 84 4 = 469094160276 :=
  contactColumnsWindow_fast contact13 84 4 469094160276 (by decide +kernel)
private theorem arithBundle06_columns_088 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 88 4 = 394039380111 :=
  contactColumnsWindow_fast contact13 88 4 394039380111 (by decide +kernel)
private theorem arithBundle06_columns_092 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 92 4 = 325923668856 :=
  contactColumnsWindow_fast contact13 92 4 325923668856 (by decide +kernel)
private theorem arithBundle06_columns_096 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 96 4 = 264744707612 :=
  contactColumnsWindow_fast contact13 96 4 264744707612 (by decide +kernel)
private theorem arithBundle06_columns_100 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 100 4 = 210520088142 :=
  contactColumnsWindow_fast contact13 100 4 210520088142 (by decide +kernel)
private theorem arithBundle06_columns_104 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 104 4 = 163269048528 :=
  contactColumnsWindow_fast contact13 104 4 163269048528 (by decide +kernel)
private theorem arithBundle06_columns_108 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 108 4 = 122945004044 :=
  contactColumnsWindow_fast contact13 108 4 122945004044 (by decide +kernel)
private theorem arithBundle06_columns_112 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 112 4 = 89434997762 :=
  contactColumnsWindow_fast contact13 112 4 89434997762 (by decide +kernel)
private theorem arithBundle06_columns_116 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 116 4 = 62445473544 :=
  contactColumnsWindow_fast contact13 116 4 62445473544 (by decide +kernel)
private theorem arithBundle06_columns_120 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 120 4 = 41538733897 :=
  contactColumnsWindow_fast contact13 120 4 41538733897 (by decide +kernel)
private theorem arithBundle06_columns_124 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 124 4 = 26098874643 :=
  contactColumnsWindow_fast contact13 124 4 26098874643 (by decide +kernel)
private theorem arithBundle06_columns_128 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 128 3 = 12274656325 :=
  contactColumnsWindow_fast contact13 128 3 12274656325 (by decide +kernel)
private theorem arithBundle06_prefix_columns_00 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 8 = 7079935792695 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 4 4 3650446289535 3429489503160 arithBundle06_columns_000 arithBundle06_columns_004
private theorem arithBundle06_prefix_columns_01 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 12 = 10295412401343 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 8 4 7079935792695 3215476608648 arithBundle06_prefix_columns_00 arithBundle06_columns_008
private theorem arithBundle06_prefix_columns_02 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 16 = 13303812071703 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 12 4 10295412401343 3008399670360 arithBundle06_prefix_columns_01 arithBundle06_columns_012
private theorem arithBundle06_prefix_columns_03 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 20 = 16112068584744 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 16 4 13303812071703 2808256513041 arithBundle06_prefix_columns_02 arithBundle06_columns_016
private theorem arithBundle06_prefix_columns_04 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 24 = 18727124175290 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 20 4 16112068584744 2615055590546 arithBundle06_prefix_columns_03 arithBundle06_columns_020
private theorem arithBundle06_prefix_columns_05 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 28 = 21155956626808 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 24 4 18727124175290 2428832451518 arithBundle06_prefix_columns_04 arithBundle06_columns_024
private theorem arithBundle06_prefix_columns_06 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 32 = 23405511142744 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 28 4 21155956626808 2249554515936 arithBundle06_prefix_columns_05 arithBundle06_columns_028
private theorem arithBundle06_prefix_columns_07 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 36 = 25482726112228 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 32 4 23405511142744 2077214969484 arithBundle06_prefix_columns_06 arithBundle06_columns_032
private theorem arithBundle06_prefix_columns_08 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 40 = 27394538933743 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 36 4 25482726112228 1911812821515 arithBundle06_prefix_columns_07 arithBundle06_columns_036
private theorem arithBundle06_prefix_columns_09 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 44 = 29147894231841 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 40 4 27394538933743 1753355298098 arithBundle06_prefix_columns_08 arithBundle06_columns_040
private theorem arithBundle06_prefix_columns_10 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 48 = 30749770045343 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 44 4 29147894231841 1601875813502 arithBundle06_prefix_columns_09 arithBundle06_columns_044
private theorem arithBundle06_prefix_columns_11 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 52 = 32207109001163 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 48 4 30749770045343 1457338955820 arithBundle06_prefix_columns_10 arithBundle06_columns_048
private theorem arithBundle06_prefix_columns_12 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 56 = 33526849736771 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 52 4 32207109001163 1319740735608 arithBundle06_prefix_columns_11 arithBundle06_columns_052
private theorem arithBundle06_prefix_columns_13 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 60 = 34715929333760 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 56 4 33526849736771 1189079596989 arithBundle06_prefix_columns_12 arithBundle06_columns_056
private theorem arithBundle06_prefix_columns_14 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 64 = 35781295040819 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 60 4 34715929333760 1065365707059 arithBundle06_prefix_columns_13 arithBundle06_columns_060
private theorem arithBundle06_prefix_columns_15 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 68 = 36729924779843 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 64 4 35781295040819 948629739024 arithBundle06_prefix_columns_14 arithBundle06_columns_064
private theorem arithBundle06_prefix_columns_16 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 72 = 37568758684811 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 68 4 36729924779843 838833904968 arithBundle06_prefix_columns_15 arithBundle06_columns_068
private theorem arithBundle06_prefix_columns_17 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 76 = 38304735653543 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 72 4 37568758684811 735976968732 arithBundle06_prefix_columns_16 arithBundle06_columns_072
private theorem arithBundle06_prefix_columns_18 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 80 = 38944792531231 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 76 4 38304735653543 640056877688 arithBundle06_prefix_columns_17 arithBundle06_columns_076
private theorem arithBundle06_prefix_columns_19 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 84 = 39495880195156 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 80 4 38944792531231 551087663925 arithBundle06_prefix_columns_18 arithBundle06_columns_080
private theorem arithBundle06_prefix_columns_20 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 88 = 39964974355432 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 84 4 39495880195156 469094160276 arithBundle06_prefix_columns_19 arithBundle06_columns_084
private theorem arithBundle06_prefix_columns_21 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 92 = 40359013735543 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 88 4 39964974355432 394039380111 arithBundle06_prefix_columns_20 arithBundle06_columns_088
private theorem arithBundle06_prefix_columns_22 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 96 = 40684937404399 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 92 4 40359013735543 325923668856 arithBundle06_prefix_columns_21 arithBundle06_columns_092
private theorem arithBundle06_prefix_columns_23 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 100 = 40949682112011 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 96 4 40684937404399 264744707612 arithBundle06_prefix_columns_22 arithBundle06_columns_096
private theorem arithBundle06_prefix_columns_24 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 104 = 41160202200153 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 100 4 40949682112011 210520088142 arithBundle06_prefix_columns_23 arithBundle06_columns_100
private theorem arithBundle06_prefix_columns_25 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 108 = 41323471248681 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 104 4 41160202200153 163269048528 arithBundle06_prefix_columns_24 arithBundle06_columns_104
private theorem arithBundle06_prefix_columns_26 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 112 = 41446416252725 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 108 4 41323471248681 122945004044 arithBundle06_prefix_columns_25 arithBundle06_columns_108
private theorem arithBundle06_prefix_columns_27 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 116 = 41535851250487 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 112 4 41446416252725 89434997762 arithBundle06_prefix_columns_26 arithBundle06_columns_112
private theorem arithBundle06_prefix_columns_28 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 120 = 41598296724031 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 116 4 41535851250487 62445473544 arithBundle06_prefix_columns_27 arithBundle06_columns_116
private theorem arithBundle06_prefix_columns_29 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 124 = 41639835457928 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 120 4 41598296724031 41538733897 arithBundle06_prefix_columns_28 arithBundle06_columns_120
private theorem arithBundle06_prefix_columns_30 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 128 = 41665934332571 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 124 4 41639835457928 26098874643 arithBundle06_prefix_columns_29 arithBundle06_columns_124
private theorem arithBundle06_prefix_columns_31 : arithBundle06_sliceWindow (auxiliaryColumnSlice contact13) 0 131 = 41678208988896 :=
  arithBundle06_combineSlices (auxiliaryColumnSlice contact13) 0 128 3 41665934332571 12274656325 arithBundle06_prefix_columns_30 arithBundle06_columns_128

private theorem arithBundle06_ordinary_ranks : ordinaryRankBound contact13 = 1597734095 := by decide +kernel
private theorem arithBundle06_ranks_000 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 4 = 13693114 :=
  contactRankWindow_of_rec contact13 0 4 13693114 (by decide +kernel)
private theorem arithBundle06_ranks_004 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 4 4 = 12619114 :=
  contactRankWindow_of_rec contact13 4 4 12619114 (by decide +kernel)
private theorem arithBundle06_ranks_008 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 8 4 = 11593114 :=
  contactRankWindow_of_rec contact13 8 4 11593114 (by decide +kernel)
private theorem arithBundle06_ranks_012 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 12 4 = 10615114 :=
  contactRankWindow_of_rec contact13 12 4 10615114 (by decide +kernel)
private theorem arithBundle06_ranks_016 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 16 4 = 9685114 :=
  contactRankWindow_of_rec contact13 16 4 9685114 (by decide +kernel)
private theorem arithBundle06_ranks_020 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 20 4 = 8803114 :=
  contactRankWindow_of_rec contact13 20 4 8803114 (by decide +kernel)
private theorem arithBundle06_ranks_024 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 24 4 = 7969114 :=
  contactRankWindow_of_rec contact13 24 4 7969114 (by decide +kernel)
private theorem arithBundle06_ranks_028 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 28 4 = 7183114 :=
  contactRankWindow_of_rec contact13 28 4 7183114 (by decide +kernel)
private theorem arithBundle06_ranks_032 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 32 4 = 6445114 :=
  contactRankWindow_of_rec contact13 32 4 6445114 (by decide +kernel)
private theorem arithBundle06_ranks_036 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 36 4 = 5755089 :=
  contactRankWindow_of_rec contact13 36 4 5755089 (by decide +kernel)
private theorem arithBundle06_ranks_040 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 40 4 = 5112509 :=
  contactRankWindow_of_rec contact13 40 4 5112509 (by decide +kernel)
private theorem arithBundle06_ranks_044 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 44 4 = 4516295 :=
  contactRankWindow_of_rec contact13 44 4 4516295 (by decide +kernel)
private theorem arithBundle06_ranks_048 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 48 4 = 3965258 :=
  contactRankWindow_of_rec contact13 48 4 3965258 (by decide +kernel)
private theorem arithBundle06_ranks_052 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 52 4 = 3457914 :=
  contactRankWindow_of_rec contact13 52 4 3457914 (by decide +kernel)
private theorem arithBundle06_ranks_056 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 56 4 = 2992639 :=
  contactRankWindow_of_rec contact13 56 4 2992639 (by decide +kernel)
private theorem arithBundle06_ranks_060 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 60 4 = 2567990 :=
  contactRankWindow_of_rec contact13 60 4 2567990 (by decide +kernel)
private theorem arithBundle06_ranks_064 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 64 4 = 2182298 :=
  contactRankWindow_of_rec contact13 64 4 2182298 (by decide +kernel)
private theorem arithBundle06_ranks_068 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 68 4 = 1833943 :=
  contactRankWindow_of_rec contact13 68 4 1833943 (by decide +kernel)
private theorem arithBundle06_ranks_072 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 72 4 = 1521602 :=
  contactRankWindow_of_rec contact13 72 4 1521602 (by decide +kernel)
private theorem arithBundle06_ranks_076 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 76 4 = 1243482 :=
  contactRankWindow_of_rec contact13 76 4 1243482 (by decide +kernel)
private theorem arithBundle06_ranks_080 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 80 4 = 997967 :=
  contactRankWindow_of_rec contact13 80 4 997967 (by decide +kernel)
private theorem arithBundle06_ranks_084 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 84 4 = 783854 :=
  contactRankWindow_of_rec contact13 84 4 783854 (by decide +kernel)
private theorem arithBundle06_ranks_088 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 88 4 = 599226 :=
  contactRankWindow_of_rec contact13 88 4 599226 (by decide +kernel)
private theorem arithBundle06_ranks_092 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 92 4 = 442471 :=
  contactRankWindow_of_rec contact13 92 4 442471 (by decide +kernel)
private theorem arithBundle06_ranks_096 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 96 4 = 312506 :=
  contactRankWindow_of_rec contact13 96 4 312506 (by decide +kernel)
private theorem arithBundle06_ranks_100 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 100 4 = 207290 :=
  contactRankWindow_of_rec contact13 100 4 207290 (by decide +kernel)
private theorem arithBundle06_ranks_104 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 104 4 = 125215 :=
  contactRankWindow_of_rec contact13 104 4 125215 (by decide +kernel)
private theorem arithBundle06_ranks_108 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 108 4 = 65318 :=
  contactRankWindow_of_rec contact13 108 4 65318 (by decide +kernel)
private theorem arithBundle06_ranks_112 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 112 4 = 25517 :=
  contactRankWindow_of_rec contact13 112 4 25517 (by decide +kernel)
private theorem arithBundle06_ranks_116 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 116 4 = 4420 :=
  contactRankWindow_of_rec contact13 116 4 4420 (by decide +kernel)
private theorem arithBundle06_ranks_120 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 120 11 = 0 :=
  contactRankWindow_of_rec contact13 120 11 0 (by decide +kernel)
private theorem arithBundle06_prefix_ranks_00 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 8 = 26312228 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 4 4 13693114 12619114 arithBundle06_ranks_000 arithBundle06_ranks_004
private theorem arithBundle06_prefix_ranks_01 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 12 = 37905342 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 8 4 26312228 11593114 arithBundle06_prefix_ranks_00 arithBundle06_ranks_008
private theorem arithBundle06_prefix_ranks_02 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 16 = 48520456 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 12 4 37905342 10615114 arithBundle06_prefix_ranks_01 arithBundle06_ranks_012
private theorem arithBundle06_prefix_ranks_03 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 20 = 58205570 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 16 4 48520456 9685114 arithBundle06_prefix_ranks_02 arithBundle06_ranks_016
private theorem arithBundle06_prefix_ranks_04 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 24 = 67008684 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 20 4 58205570 8803114 arithBundle06_prefix_ranks_03 arithBundle06_ranks_020
private theorem arithBundle06_prefix_ranks_05 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 28 = 74977798 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 24 4 67008684 7969114 arithBundle06_prefix_ranks_04 arithBundle06_ranks_024
private theorem arithBundle06_prefix_ranks_06 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 32 = 82160912 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 28 4 74977798 7183114 arithBundle06_prefix_ranks_05 arithBundle06_ranks_028
private theorem arithBundle06_prefix_ranks_07 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 36 = 88606026 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 32 4 82160912 6445114 arithBundle06_prefix_ranks_06 arithBundle06_ranks_032
private theorem arithBundle06_prefix_ranks_08 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 40 = 94361115 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 36 4 88606026 5755089 arithBundle06_prefix_ranks_07 arithBundle06_ranks_036
private theorem arithBundle06_prefix_ranks_09 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 44 = 99473624 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 40 4 94361115 5112509 arithBundle06_prefix_ranks_08 arithBundle06_ranks_040
private theorem arithBundle06_prefix_ranks_10 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 48 = 103989919 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 44 4 99473624 4516295 arithBundle06_prefix_ranks_09 arithBundle06_ranks_044
private theorem arithBundle06_prefix_ranks_11 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 52 = 107955177 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 48 4 103989919 3965258 arithBundle06_prefix_ranks_10 arithBundle06_ranks_048
private theorem arithBundle06_prefix_ranks_12 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 56 = 111413091 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 52 4 107955177 3457914 arithBundle06_prefix_ranks_11 arithBundle06_ranks_052
private theorem arithBundle06_prefix_ranks_13 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 60 = 114405730 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 56 4 111413091 2992639 arithBundle06_prefix_ranks_12 arithBundle06_ranks_056
private theorem arithBundle06_prefix_ranks_14 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 64 = 116973720 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 60 4 114405730 2567990 arithBundle06_prefix_ranks_13 arithBundle06_ranks_060
private theorem arithBundle06_prefix_ranks_15 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 68 = 119156018 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 64 4 116973720 2182298 arithBundle06_prefix_ranks_14 arithBundle06_ranks_064
private theorem arithBundle06_prefix_ranks_16 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 72 = 120989961 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 68 4 119156018 1833943 arithBundle06_prefix_ranks_15 arithBundle06_ranks_068
private theorem arithBundle06_prefix_ranks_17 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 76 = 122511563 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 72 4 120989961 1521602 arithBundle06_prefix_ranks_16 arithBundle06_ranks_072
private theorem arithBundle06_prefix_ranks_18 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 80 = 123755045 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 76 4 122511563 1243482 arithBundle06_prefix_ranks_17 arithBundle06_ranks_076
private theorem arithBundle06_prefix_ranks_19 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 84 = 124753012 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 80 4 123755045 997967 arithBundle06_prefix_ranks_18 arithBundle06_ranks_080
private theorem arithBundle06_prefix_ranks_20 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 88 = 125536866 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 84 4 124753012 783854 arithBundle06_prefix_ranks_19 arithBundle06_ranks_084
private theorem arithBundle06_prefix_ranks_21 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 92 = 126136092 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 88 4 125536866 599226 arithBundle06_prefix_ranks_20 arithBundle06_ranks_088
private theorem arithBundle06_prefix_ranks_22 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 96 = 126578563 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 92 4 126136092 442471 arithBundle06_prefix_ranks_21 arithBundle06_ranks_092
private theorem arithBundle06_prefix_ranks_23 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 100 = 126891069 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 96 4 126578563 312506 arithBundle06_prefix_ranks_22 arithBundle06_ranks_096
private theorem arithBundle06_prefix_ranks_24 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 104 = 127098359 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 100 4 126891069 207290 arithBundle06_prefix_ranks_23 arithBundle06_ranks_100
private theorem arithBundle06_prefix_ranks_25 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 108 = 127223574 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 104 4 127098359 125215 arithBundle06_prefix_ranks_24 arithBundle06_ranks_104
private theorem arithBundle06_prefix_ranks_26 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 112 = 127288892 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 108 4 127223574 65318 arithBundle06_prefix_ranks_25 arithBundle06_ranks_108
private theorem arithBundle06_prefix_ranks_27 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 116 = 127314409 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 112 4 127288892 25517 arithBundle06_prefix_ranks_26 arithBundle06_ranks_112
private theorem arithBundle06_prefix_ranks_28 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 120 = 127318829 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 116 4 127314409 4420 arithBundle06_prefix_ranks_27 arithBundle06_ranks_116
private theorem arithBundle06_prefix_ranks_29 : arithBundle06_sliceWindow (auxiliaryRankSlice contact13) 0 131 = 127318829 :=
  arithBundle06_combineSlices (auxiliaryRankSlice contact13) 0 120 11 127318829 0 arithBundle06_prefix_ranks_28 arithBundle06_ranks_120

theorem contact13_margin : sourceMargin contact13 :=
  arithBundle06_margin_of_checked_counts contact13 131 410536038925851 41678208988896 1597734095 127318829
    rfl arithBundle06_ordinary_columns arithBundle06_prefix_columns_31 arithBundle06_ordinary_ranks arithBundle06_prefix_ranks_29 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle07_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle07_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle07_sliceWindow f a b = x) (hy : arithBundle07_sliceWindow f (a+b) c = y) :
    arithBundle07_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle07_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle07_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle07_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle07_sliceWindow,Nat.zero_add]

private theorem arithBundle07_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle07_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle07_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle07_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle07_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle07_ordinary_columns : ordinaryColumnCount contact14 = 189248871982219 := by decide +kernel
private theorem arithBundle07_columns_000 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 4 = 950185835014 :=
  contactColumnsWindow_fast contact14 0 4 950185835014 (by decide +kernel)
private theorem arithBundle07_columns_004 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 4 4 = 872797978200 :=
  contactColumnsWindow_fast contact14 4 4 872797978200 (by decide +kernel)
private theorem arithBundle07_columns_008 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 8 4 = 798729988874 :=
  contactColumnsWindow_fast contact14 8 4 798729988874 (by decide +kernel)
private theorem arithBundle07_columns_012 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 12 4 = 727967041728 :=
  contactColumnsWindow_fast contact14 12 4 727967041728 (by decide +kernel)
private theorem arithBundle07_columns_016 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 16 4 = 660506422798 :=
  contactColumnsWindow_fast contact14 16 4 660506422798 (by decide +kernel)
private theorem arithBundle07_columns_020 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 20 4 = 596346666725 :=
  contactColumnsWindow_fast contact14 20 4 596346666725 (by decide +kernel)
private theorem arithBundle07_columns_024 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 24 4 = 535492410752 :=
  contactColumnsWindow_fast contact14 24 4 535492410752 (by decide +kernel)
private theorem arithBundle07_columns_028 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 28 4 = 477959434910 :=
  contactColumnsWindow_fast contact14 28 4 477959434910 (by decide +kernel)
private theorem arithBundle07_columns_032 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 32 4 = 423733101966 :=
  contactColumnsWindow_fast contact14 32 4 423733101966 (by decide +kernel)
private theorem arithBundle07_columns_036 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 36 4 = 372809190478 :=
  contactColumnsWindow_fast contact14 36 4 372809190478 (by decide +kernel)
private theorem arithBundle07_columns_040 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 40 4 = 325186235798 :=
  contactColumnsWindow_fast contact14 40 4 325186235798 (by decide +kernel)
private theorem arithBundle07_columns_044 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 44 4 = 280869826724 :=
  contactColumnsWindow_fast contact14 44 4 280869826724 (by decide +kernel)
private theorem arithBundle07_columns_048 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 48 4 = 239874880865 :=
  contactColumnsWindow_fast contact14 48 4 239874880865 (by decide +kernel)
private theorem arithBundle07_columns_052 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 52 4 = 202185409506 :=
  contactColumnsWindow_fast contact14 52 4 202185409506 (by decide +kernel)
private theorem arithBundle07_columns_056 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 56 4 = 167798140450 :=
  contactColumnsWindow_fast contact14 56 4 167798140450 (by decide +kernel)
private theorem arithBundle07_columns_060 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 60 4 = 136711987163 :=
  contactColumnsWindow_fast contact14 60 4 136711987163 (by decide +kernel)
private theorem arithBundle07_columns_064 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 64 4 = 108933645061 :=
  contactColumnsWindow_fast contact14 64 4 108933645061 (by decide +kernel)
private theorem arithBundle07_columns_068 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 68 4 = 84476594138 :=
  contactColumnsWindow_fast contact14 68 4 84476594138 (by decide +kernel)
private theorem arithBundle07_columns_072 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 72 4 = 63323913825 :=
  contactColumnsWindow_fast contact14 72 4 63323913825 (by decide +kernel)
private theorem arithBundle07_columns_076 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 76 4 = 45473272714 :=
  contactColumnsWindow_fast contact14 76 4 45473272714 (by decide +kernel)
private theorem arithBundle07_columns_080 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 80 4 = 30923148727 :=
  contactColumnsWindow_fast contact14 80 4 30923148727 (by decide +kernel)
private theorem arithBundle07_columns_084 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 84 4 = 19641592796 :=
  contactColumnsWindow_fast contact14 84 4 19641592796 (by decide +kernel)
private theorem arithBundle07_columns_088 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 88 4 = 11451739216 :=
  contactColumnsWindow_fast contact14 88 4 11451739216 (by decide +kernel)
private theorem arithBundle07_columns_092 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 92 4 = 5980081046 :=
  contactColumnsWindow_fast contact14 92 4 5980081046 (by decide +kernel)
private theorem arithBundle07_columns_096 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 96 4 = 2709086910 :=
  contactColumnsWindow_fast contact14 96 4 2709086910 (by decide +kernel)
private theorem arithBundle07_prefix_columns_00 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 8 = 1822983813214 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 4 4 950185835014 872797978200 arithBundle07_columns_000 arithBundle07_columns_004
private theorem arithBundle07_prefix_columns_01 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 12 = 2621713802088 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 8 4 1822983813214 798729988874 arithBundle07_prefix_columns_00 arithBundle07_columns_008
private theorem arithBundle07_prefix_columns_02 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 16 = 3349680843816 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 12 4 2621713802088 727967041728 arithBundle07_prefix_columns_01 arithBundle07_columns_012
private theorem arithBundle07_prefix_columns_03 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 20 = 4010187266614 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 16 4 3349680843816 660506422798 arithBundle07_prefix_columns_02 arithBundle07_columns_016
private theorem arithBundle07_prefix_columns_04 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 24 = 4606533933339 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 20 4 4010187266614 596346666725 arithBundle07_prefix_columns_03 arithBundle07_columns_020
private theorem arithBundle07_prefix_columns_05 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 28 = 5142026344091 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 24 4 4606533933339 535492410752 arithBundle07_prefix_columns_04 arithBundle07_columns_024
private theorem arithBundle07_prefix_columns_06 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 32 = 5619985779001 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 28 4 5142026344091 477959434910 arithBundle07_prefix_columns_05 arithBundle07_columns_028
private theorem arithBundle07_prefix_columns_07 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 36 = 6043718880967 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 32 4 5619985779001 423733101966 arithBundle07_prefix_columns_06 arithBundle07_columns_032
private theorem arithBundle07_prefix_columns_08 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 40 = 6416528071445 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 36 4 6043718880967 372809190478 arithBundle07_prefix_columns_07 arithBundle07_columns_036
private theorem arithBundle07_prefix_columns_09 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 44 = 6741714307243 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 40 4 6416528071445 325186235798 arithBundle07_prefix_columns_08 arithBundle07_columns_040
private theorem arithBundle07_prefix_columns_10 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 48 = 7022584133967 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 44 4 6741714307243 280869826724 arithBundle07_prefix_columns_09 arithBundle07_columns_044
private theorem arithBundle07_prefix_columns_11 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 52 = 7262459014832 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 48 4 7022584133967 239874880865 arithBundle07_prefix_columns_10 arithBundle07_columns_048
private theorem arithBundle07_prefix_columns_12 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 56 = 7464644424338 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 52 4 7262459014832 202185409506 arithBundle07_prefix_columns_11 arithBundle07_columns_052
private theorem arithBundle07_prefix_columns_13 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 60 = 7632442564788 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 56 4 7464644424338 167798140450 arithBundle07_prefix_columns_12 arithBundle07_columns_056
private theorem arithBundle07_prefix_columns_14 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 64 = 7769154551951 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 60 4 7632442564788 136711987163 arithBundle07_prefix_columns_13 arithBundle07_columns_060
private theorem arithBundle07_prefix_columns_15 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 68 = 7878088197012 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 64 4 7769154551951 108933645061 arithBundle07_prefix_columns_14 arithBundle07_columns_064
private theorem arithBundle07_prefix_columns_16 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 72 = 7962564791150 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 68 4 7878088197012 84476594138 arithBundle07_prefix_columns_15 arithBundle07_columns_068
private theorem arithBundle07_prefix_columns_17 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 76 = 8025888704975 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 72 4 7962564791150 63323913825 arithBundle07_prefix_columns_16 arithBundle07_columns_072
private theorem arithBundle07_prefix_columns_18 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 80 = 8071361977689 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 76 4 8025888704975 45473272714 arithBundle07_prefix_columns_17 arithBundle07_columns_076
private theorem arithBundle07_prefix_columns_19 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 84 = 8102285126416 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 80 4 8071361977689 30923148727 arithBundle07_prefix_columns_18 arithBundle07_columns_080
private theorem arithBundle07_prefix_columns_20 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 88 = 8121926719212 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 84 4 8102285126416 19641592796 arithBundle07_prefix_columns_19 arithBundle07_columns_084
private theorem arithBundle07_prefix_columns_21 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 92 = 8133378458428 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 88 4 8121926719212 11451739216 arithBundle07_prefix_columns_20 arithBundle07_columns_088
private theorem arithBundle07_prefix_columns_22 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 96 = 8139358539474 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 92 4 8133378458428 5980081046 arithBundle07_prefix_columns_21 arithBundle07_columns_092
private theorem arithBundle07_prefix_columns_23 : arithBundle07_sliceWindow (auxiliaryColumnSlice contact14) 0 100 = 8142067626384 :=
  arithBundle07_combineSlices (auxiliaryColumnSlice contact14) 0 96 4 8139358539474 2709086910 arithBundle07_prefix_columns_22 arithBundle07_columns_096

private theorem arithBundle07_ordinary_ranks : ordinaryRankBound contact14 = 728288639 := by decide +kernel
private theorem arithBundle07_ranks_000 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 4 = 3559590 :=
  contactRankWindow_of_rec contact14 0 4 3559590 (by decide +kernel)
private theorem arithBundle07_ranks_004 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 4 4 = 3182598 :=
  contactRankWindow_of_rec contact14 4 4 3182598 (by decide +kernel)
private theorem arithBundle07_ranks_008 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 8 4 = 2828454 :=
  contactRankWindow_of_rec contact14 8 4 2828454 (by decide +kernel)
private theorem arithBundle07_ranks_012 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 12 4 = 2497158 :=
  contactRankWindow_of_rec contact14 12 4 2497158 (by decide +kernel)
private theorem arithBundle07_ranks_016 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 16 4 = 2188710 :=
  contactRankWindow_of_rec contact14 16 4 2188710 (by decide +kernel)
private theorem arithBundle07_ranks_020 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 20 4 = 1903110 :=
  contactRankWindow_of_rec contact14 20 4 1903110 (by decide +kernel)
private theorem arithBundle07_ranks_024 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 24 4 = 1640358 :=
  contactRankWindow_of_rec contact14 24 4 1640358 (by decide +kernel)
private theorem arithBundle07_ranks_028 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 28 4 = 1400454 :=
  contactRankWindow_of_rec contact14 28 4 1400454 (by decide +kernel)
private theorem arithBundle07_ranks_032 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 32 4 = 1183278 :=
  contactRankWindow_of_rec contact14 32 4 1183278 (by decide +kernel)
private theorem arithBundle07_ranks_036 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 36 4 = 988204 :=
  contactRankWindow_of_rec contact14 36 4 988204 (by decide +kernel)
private theorem arithBundle07_ranks_040 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 40 4 = 814433 :=
  contactRankWindow_of_rec contact14 40 4 814433 (by decide +kernel)
private theorem arithBundle07_ranks_044 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 44 4 = 660925 :=
  contactRankWindow_of_rec contact14 44 4 660925 (by decide +kernel)
private theorem arithBundle07_ranks_048 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 48 4 = 526560 :=
  contactRankWindow_of_rec contact14 48 4 526560 (by decide +kernel)
private theorem arithBundle07_ranks_052 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 52 4 = 410353 :=
  contactRankWindow_of_rec contact14 52 4 410353 (by decide +kernel)
private theorem arithBundle07_ranks_056 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 56 4 = 311137 :=
  contactRankWindow_of_rec contact14 56 4 311137 (by decide +kernel)
private theorem arithBundle07_ranks_060 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 60 4 = 227796 :=
  contactRankWindow_of_rec contact14 60 4 227796 (by decide +kernel)
private theorem arithBundle07_ranks_064 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 64 4 = 159425 :=
  contactRankWindow_of_rec contact14 64 4 159425 (by decide +kernel)
private theorem arithBundle07_ranks_068 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 68 4 = 104773 :=
  contactRankWindow_of_rec contact14 68 4 104773 (by decide +kernel)
private theorem arithBundle07_ranks_072 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 72 4 = 62728 :=
  contactRankWindow_of_rec contact14 72 4 62728 (by decide +kernel)
private theorem arithBundle07_ranks_076 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 76 4 = 32465 :=
  contactRankWindow_of_rec contact14 76 4 32465 (by decide +kernel)
private theorem arithBundle07_ranks_080 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 80 4 = 12649 :=
  contactRankWindow_of_rec contact14 80 4 12649 (by decide +kernel)
private theorem arithBundle07_ranks_084 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 84 4 = 2189 :=
  contactRankWindow_of_rec contact14 84 4 2189 (by decide +kernel)
private theorem arithBundle07_ranks_088 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 88 12 = 0 :=
  contactRankWindow_of_rec contact14 88 12 0 (by decide +kernel)
private theorem arithBundle07_prefix_ranks_00 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 8 = 6742188 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 4 4 3559590 3182598 arithBundle07_ranks_000 arithBundle07_ranks_004
private theorem arithBundle07_prefix_ranks_01 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 12 = 9570642 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 8 4 6742188 2828454 arithBundle07_prefix_ranks_00 arithBundle07_ranks_008
private theorem arithBundle07_prefix_ranks_02 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 16 = 12067800 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 12 4 9570642 2497158 arithBundle07_prefix_ranks_01 arithBundle07_ranks_012
private theorem arithBundle07_prefix_ranks_03 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 20 = 14256510 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 16 4 12067800 2188710 arithBundle07_prefix_ranks_02 arithBundle07_ranks_016
private theorem arithBundle07_prefix_ranks_04 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 24 = 16159620 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 20 4 14256510 1903110 arithBundle07_prefix_ranks_03 arithBundle07_ranks_020
private theorem arithBundle07_prefix_ranks_05 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 28 = 17799978 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 24 4 16159620 1640358 arithBundle07_prefix_ranks_04 arithBundle07_ranks_024
private theorem arithBundle07_prefix_ranks_06 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 32 = 19200432 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 28 4 17799978 1400454 arithBundle07_prefix_ranks_05 arithBundle07_ranks_028
private theorem arithBundle07_prefix_ranks_07 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 36 = 20383710 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 32 4 19200432 1183278 arithBundle07_prefix_ranks_06 arithBundle07_ranks_032
private theorem arithBundle07_prefix_ranks_08 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 40 = 21371914 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 36 4 20383710 988204 arithBundle07_prefix_ranks_07 arithBundle07_ranks_036
private theorem arithBundle07_prefix_ranks_09 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 44 = 22186347 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 40 4 21371914 814433 arithBundle07_prefix_ranks_08 arithBundle07_ranks_040
private theorem arithBundle07_prefix_ranks_10 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 48 = 22847272 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 44 4 22186347 660925 arithBundle07_prefix_ranks_09 arithBundle07_ranks_044
private theorem arithBundle07_prefix_ranks_11 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 52 = 23373832 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 48 4 22847272 526560 arithBundle07_prefix_ranks_10 arithBundle07_ranks_048
private theorem arithBundle07_prefix_ranks_12 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 56 = 23784185 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 52 4 23373832 410353 arithBundle07_prefix_ranks_11 arithBundle07_ranks_052
private theorem arithBundle07_prefix_ranks_13 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 60 = 24095322 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 56 4 23784185 311137 arithBundle07_prefix_ranks_12 arithBundle07_ranks_056
private theorem arithBundle07_prefix_ranks_14 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 64 = 24323118 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 60 4 24095322 227796 arithBundle07_prefix_ranks_13 arithBundle07_ranks_060
private theorem arithBundle07_prefix_ranks_15 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 68 = 24482543 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 64 4 24323118 159425 arithBundle07_prefix_ranks_14 arithBundle07_ranks_064
private theorem arithBundle07_prefix_ranks_16 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 72 = 24587316 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 68 4 24482543 104773 arithBundle07_prefix_ranks_15 arithBundle07_ranks_068
private theorem arithBundle07_prefix_ranks_17 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 76 = 24650044 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 72 4 24587316 62728 arithBundle07_prefix_ranks_16 arithBundle07_ranks_072
private theorem arithBundle07_prefix_ranks_18 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 80 = 24682509 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 76 4 24650044 32465 arithBundle07_prefix_ranks_17 arithBundle07_ranks_076
private theorem arithBundle07_prefix_ranks_19 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 84 = 24695158 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 80 4 24682509 12649 arithBundle07_prefix_ranks_18 arithBundle07_ranks_080
private theorem arithBundle07_prefix_ranks_20 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 88 = 24697347 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 84 4 24695158 2189 arithBundle07_prefix_ranks_19 arithBundle07_ranks_084
private theorem arithBundle07_prefix_ranks_21 : arithBundle07_sliceWindow (auxiliaryRankSlice contact14) 0 100 = 24697347 :=
  arithBundle07_combineSlices (auxiliaryRankSlice contact14) 0 88 12 24697347 0 arithBundle07_prefix_ranks_20 arithBundle07_ranks_088

theorem contact14_margin : sourceMargin contact14 :=
  arithBundle07_margin_of_checked_counts contact14 100 189248871982219 8142067626384 728288639 24697347
    rfl arithBundle07_ordinary_columns arithBundle07_prefix_columns_23 arithBundle07_ordinary_ranks arithBundle07_prefix_ranks_21 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle08_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle08_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle08_sliceWindow f a b = x) (hy : arithBundle08_sliceWindow f (a+b) c = y) :
    arithBundle08_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle08_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle08_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle08_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle08_sliceWindow,Nat.zero_add]

private theorem arithBundle08_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle08_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle08_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle08_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle08_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle08_ordinary_columns : ordinaryColumnCount contact16 = 169704479189907 := by decide +kernel
private theorem arithBundle08_columns_000 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 4 = 1091481552944 :=
  contactColumnsWindow_fast contact16 0 4 1091481552944 (by decide +kernel)
private theorem arithBundle08_columns_004 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 4 4 = 1004126873506 :=
  contactColumnsWindow_fast contact16 4 4 1004126873506 (by decide +kernel)
private theorem arithBundle08_columns_008 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 8 4 = 920436138614 :=
  contactColumnsWindow_fast contact16 8 4 920436138614 (by decide +kernel)
private theorem arithBundle08_columns_012 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 12 4 = 840408239718 :=
  contactColumnsWindow_fast contact16 12 4 840408239718 (by decide +kernel)
private theorem arithBundle08_columns_016 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 16 4 = 764041991669 :=
  contactColumnsWindow_fast contact16 16 4 764041991669 (by decide +kernel)
private theorem arithBundle08_columns_020 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 20 4 = 691344734869 :=
  contactColumnsWindow_fast contact16 20 4 691344734869 (by decide +kernel)
private theorem arithBundle08_columns_024 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 24 4 = 622332026434 :=
  contactColumnsWindow_fast contact16 24 4 622332026434 (by decide +kernel)
private theorem arithBundle08_columns_028 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 28 4 = 556984606631 :=
  contactColumnsWindow_fast contact16 28 4 556984606631 (by decide +kernel)
private theorem arithBundle08_columns_032 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 32 4 = 495299854194 :=
  contactColumnsWindow_fast contact16 32 4 495299854194 (by decide +kernel)
private theorem arithBundle08_columns_036 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 36 4 = 437276972022 :=
  contactColumnsWindow_fast contact16 36 4 437276972022 (by decide +kernel)
private theorem arithBundle08_columns_040 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 40 4 = 382924889860 :=
  contactColumnsWindow_fast contact16 40 4 382924889860 (by decide +kernel)
private theorem arithBundle08_columns_044 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 44 4 = 332256305938 :=
  contactColumnsWindow_fast contact16 44 4 332256305938 (by decide +kernel)
private theorem arithBundle08_columns_048 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 48 4 = 285252201224 :=
  contactColumnsWindow_fast contact16 48 4 285252201224 (by decide +kernel)
private theorem arithBundle08_columns_052 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 52 4 = 241910595246 :=
  contactColumnsWindow_fast contact16 52 4 241910595246 (by decide +kernel)
private theorem arithBundle08_columns_056 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 56 4 = 202231131750 :=
  contactColumnsWindow_fast contact16 56 4 202231131750 (by decide +kernel)
private theorem arithBundle08_columns_060 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 60 4 = 166224179929 :=
  contactColumnsWindow_fast contact16 60 4 166224179929 (by decide +kernel)
private theorem arithBundle08_columns_064 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 64 4 = 133899712018 :=
  contactColumnsWindow_fast contact16 64 4 133899712018 (by decide +kernel)
private theorem arithBundle08_columns_068 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 68 4 = 105239002858 :=
  contactColumnsWindow_fast contact16 68 4 105239002858 (by decide +kernel)
private theorem arithBundle08_columns_072 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 72 4 = 80240462874 :=
  contactColumnsWindow_fast contact16 72 4 80240462874 (by decide +kernel)
private theorem arithBundle08_columns_076 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 76 4 = 58904418054 :=
  contactColumnsWindow_fast contact16 76 4 58904418054 (by decide +kernel)
private theorem arithBundle08_columns_080 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 80 4 = 41242833187 :=
  contactColumnsWindow_fast contact16 80 4 41242833187 (by decide +kernel)
private theorem arithBundle08_columns_084 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 84 4 = 27236220427 :=
  contactColumnsWindow_fast contact16 84 4 27236220427 (by decide +kernel)
private theorem arithBundle08_columns_088 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 88 4 = 16711342249 :=
  contactColumnsWindow_fast contact16 88 4 16711342249 (by decide +kernel)
private theorem arithBundle08_columns_092 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 92 4 = 9341251231 :=
  contactColumnsWindow_fast contact16 92 4 9341251231 (by decide +kernel)
private theorem arithBundle08_columns_096 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 96 4 = 4639211326 :=
  contactColumnsWindow_fast contact16 96 4 4639211326 (by decide +kernel)
private theorem arithBundle08_columns_100 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 100 2 = 1221010554 :=
  contactColumnsWindow_fast contact16 100 2 1221010554 (by decide +kernel)
private theorem arithBundle08_prefix_columns_00 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 8 = 2095608426450 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 4 4 1091481552944 1004126873506 arithBundle08_columns_000 arithBundle08_columns_004
private theorem arithBundle08_prefix_columns_01 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 12 = 3016044565064 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 8 4 2095608426450 920436138614 arithBundle08_prefix_columns_00 arithBundle08_columns_008
private theorem arithBundle08_prefix_columns_02 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 16 = 3856452804782 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 12 4 3016044565064 840408239718 arithBundle08_prefix_columns_01 arithBundle08_columns_012
private theorem arithBundle08_prefix_columns_03 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 20 = 4620494796451 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 16 4 3856452804782 764041991669 arithBundle08_prefix_columns_02 arithBundle08_columns_016
private theorem arithBundle08_prefix_columns_04 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 24 = 5311839531320 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 20 4 4620494796451 691344734869 arithBundle08_prefix_columns_03 arithBundle08_columns_020
private theorem arithBundle08_prefix_columns_05 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 28 = 5934171557754 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 24 4 5311839531320 622332026434 arithBundle08_prefix_columns_04 arithBundle08_columns_024
private theorem arithBundle08_prefix_columns_06 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 32 = 6491156164385 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 28 4 5934171557754 556984606631 arithBundle08_prefix_columns_05 arithBundle08_columns_028
private theorem arithBundle08_prefix_columns_07 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 36 = 6986456018579 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 32 4 6491156164385 495299854194 arithBundle08_prefix_columns_06 arithBundle08_columns_032
private theorem arithBundle08_prefix_columns_08 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 40 = 7423732990601 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 36 4 6986456018579 437276972022 arithBundle08_prefix_columns_07 arithBundle08_columns_036
private theorem arithBundle08_prefix_columns_09 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 44 = 7806657880461 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 40 4 7423732990601 382924889860 arithBundle08_prefix_columns_08 arithBundle08_columns_040
private theorem arithBundle08_prefix_columns_10 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 48 = 8138914186399 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 44 4 7806657880461 332256305938 arithBundle08_prefix_columns_09 arithBundle08_columns_044
private theorem arithBundle08_prefix_columns_11 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 52 = 8424166387623 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 48 4 8138914186399 285252201224 arithBundle08_prefix_columns_10 arithBundle08_columns_048
private theorem arithBundle08_prefix_columns_12 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 56 = 8666076982869 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 52 4 8424166387623 241910595246 arithBundle08_prefix_columns_11 arithBundle08_columns_052
private theorem arithBundle08_prefix_columns_13 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 60 = 8868308114619 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 56 4 8666076982869 202231131750 arithBundle08_prefix_columns_12 arithBundle08_columns_056
private theorem arithBundle08_prefix_columns_14 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 64 = 9034532294548 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 60 4 8868308114619 166224179929 arithBundle08_prefix_columns_13 arithBundle08_columns_060
private theorem arithBundle08_prefix_columns_15 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 68 = 9168432006566 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 64 4 9034532294548 133899712018 arithBundle08_prefix_columns_14 arithBundle08_columns_064
private theorem arithBundle08_prefix_columns_16 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 72 = 9273671009424 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 68 4 9168432006566 105239002858 arithBundle08_prefix_columns_15 arithBundle08_columns_068
private theorem arithBundle08_prefix_columns_17 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 76 = 9353911472298 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 72 4 9273671009424 80240462874 arithBundle08_prefix_columns_16 arithBundle08_columns_072
private theorem arithBundle08_prefix_columns_18 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 80 = 9412815890352 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 76 4 9353911472298 58904418054 arithBundle08_prefix_columns_17 arithBundle08_columns_076
private theorem arithBundle08_prefix_columns_19 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 84 = 9454058723539 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 80 4 9412815890352 41242833187 arithBundle08_prefix_columns_18 arithBundle08_columns_080
private theorem arithBundle08_prefix_columns_20 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 88 = 9481294943966 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 84 4 9454058723539 27236220427 arithBundle08_prefix_columns_19 arithBundle08_columns_084
private theorem arithBundle08_prefix_columns_21 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 92 = 9498006286215 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 88 4 9481294943966 16711342249 arithBundle08_prefix_columns_20 arithBundle08_columns_088
private theorem arithBundle08_prefix_columns_22 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 96 = 9507347537446 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 92 4 9498006286215 9341251231 arithBundle08_prefix_columns_21 arithBundle08_columns_092
private theorem arithBundle08_prefix_columns_23 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 100 = 9511986748772 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 96 4 9507347537446 4639211326 arithBundle08_prefix_columns_22 arithBundle08_columns_096
private theorem arithBundle08_prefix_columns_24 : arithBundle08_sliceWindow (auxiliaryColumnSlice contact16) 0 102 = 9513207759326 :=
  arithBundle08_combineSlices (auxiliaryColumnSlice contact16) 0 100 2 9511986748772 1221010554 arithBundle08_prefix_columns_23 arithBundle08_columns_100

private theorem arithBundle08_ordinary_ranks : ordinaryRankBound contact16 = 654700380 := by decide +kernel
private theorem arithBundle08_ranks_000 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 4 = 4087788 :=
  contactRankWindow_of_rec contact16 0 4 4087788 (by decide +kernel)
private theorem arithBundle08_ranks_004 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 4 4 = 3663276 :=
  contactRankWindow_of_rec contact16 4 4 3663276 (by decide +kernel)
private theorem arithBundle08_ranks_008 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 8 4 = 3264108 :=
  contactRankWindow_of_rec contact16 8 4 3264108 (by decide +kernel)
private theorem arithBundle08_ranks_012 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 12 4 = 2890284 :=
  contactRankWindow_of_rec contact16 12 4 2890284 (by decide +kernel)
private theorem arithBundle08_ranks_016 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 16 4 = 2541804 :=
  contactRankWindow_of_rec contact16 16 4 2541804 (by decide +kernel)
private theorem arithBundle08_ranks_020 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 20 4 = 2218668 :=
  contactRankWindow_of_rec contact16 20 4 2218668 (by decide +kernel)
private theorem arithBundle08_ranks_024 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 24 4 = 1920876 :=
  contactRankWindow_of_rec contact16 24 4 1920876 (by decide +kernel)
private theorem arithBundle08_ranks_028 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 28 4 = 1648428 :=
  contactRankWindow_of_rec contact16 28 4 1648428 (by decide +kernel)
private theorem arithBundle08_ranks_032 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 32 4 = 1401070 :=
  contactRankWindow_of_rec contact16 32 4 1401070 (by decide +kernel)
private theorem arithBundle08_ranks_036 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 36 4 = 1178078 :=
  contactRankWindow_of_rec contact16 36 4 1178078 (by decide +kernel)
private theorem arithBundle08_ranks_040 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 40 4 = 978542 :=
  contactRankWindow_of_rec contact16 40 4 978542 (by decide +kernel)
private theorem arithBundle08_ranks_044 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 44 4 = 801304 :=
  contactRankWindow_of_rec contact16 44 4 801304 (by decide +kernel)
private theorem arithBundle08_ranks_048 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 48 4 = 645306 :=
  contactRankWindow_of_rec contact16 48 4 645306 (by decide +kernel)
private theorem arithBundle08_ranks_052 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 52 4 = 509342 :=
  contactRankWindow_of_rec contact16 52 4 509342 (by decide +kernel)
private theorem arithBundle08_ranks_056 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 56 4 = 392236 :=
  contactRankWindow_of_rec contact16 56 4 392236 (by decide +kernel)
private theorem arithBundle08_ranks_060 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 60 4 = 293014 :=
  contactRankWindow_of_rec contact16 60 4 293014 (by decide +kernel)
private theorem arithBundle08_ranks_064 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 64 4 = 210382 :=
  contactRankWindow_of_rec contact16 64 4 210382 (by decide +kernel)
private theorem arithBundle08_ranks_068 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 68 4 = 143168 :=
  contactRankWindow_of_rec contact16 68 4 143168 (by decide +kernel)
private theorem arithBundle08_ranks_072 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 72 4 = 90482 :=
  contactRankWindow_of_rec contact16 72 4 90482 (by decide +kernel)
private theorem arithBundle08_ranks_076 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 76 4 = 50942 :=
  contactRankWindow_of_rec contact16 76 4 50942 (by decide +kernel)
private theorem arithBundle08_ranks_080 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 80 4 = 23380 :=
  contactRankWindow_of_rec contact16 80 4 23380 (by decide +kernel)
private theorem arithBundle08_ranks_084 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 84 4 = 6997 :=
  contactRankWindow_of_rec contact16 84 4 6997 (by decide +kernel)
private theorem arithBundle08_ranks_088 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 88 4 = 386 :=
  contactRankWindow_of_rec contact16 88 4 386 (by decide +kernel)
private theorem arithBundle08_ranks_092 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 92 10 = 0 :=
  contactRankWindow_of_rec contact16 92 10 0 (by decide +kernel)
private theorem arithBundle08_prefix_ranks_00 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 8 = 7751064 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 4 4 4087788 3663276 arithBundle08_ranks_000 arithBundle08_ranks_004
private theorem arithBundle08_prefix_ranks_01 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 12 = 11015172 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 8 4 7751064 3264108 arithBundle08_prefix_ranks_00 arithBundle08_ranks_008
private theorem arithBundle08_prefix_ranks_02 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 16 = 13905456 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 12 4 11015172 2890284 arithBundle08_prefix_ranks_01 arithBundle08_ranks_012
private theorem arithBundle08_prefix_ranks_03 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 20 = 16447260 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 16 4 13905456 2541804 arithBundle08_prefix_ranks_02 arithBundle08_ranks_016
private theorem arithBundle08_prefix_ranks_04 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 24 = 18665928 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 20 4 16447260 2218668 arithBundle08_prefix_ranks_03 arithBundle08_ranks_020
private theorem arithBundle08_prefix_ranks_05 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 28 = 20586804 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 24 4 18665928 1920876 arithBundle08_prefix_ranks_04 arithBundle08_ranks_024
private theorem arithBundle08_prefix_ranks_06 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 32 = 22235232 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 28 4 20586804 1648428 arithBundle08_prefix_ranks_05 arithBundle08_ranks_028
private theorem arithBundle08_prefix_ranks_07 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 36 = 23636302 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 32 4 22235232 1401070 arithBundle08_prefix_ranks_06 arithBundle08_ranks_032
private theorem arithBundle08_prefix_ranks_08 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 40 = 24814380 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 36 4 23636302 1178078 arithBundle08_prefix_ranks_07 arithBundle08_ranks_036
private theorem arithBundle08_prefix_ranks_09 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 44 = 25792922 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 40 4 24814380 978542 arithBundle08_prefix_ranks_08 arithBundle08_ranks_040
private theorem arithBundle08_prefix_ranks_10 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 48 = 26594226 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 44 4 25792922 801304 arithBundle08_prefix_ranks_09 arithBundle08_ranks_044
private theorem arithBundle08_prefix_ranks_11 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 52 = 27239532 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 48 4 26594226 645306 arithBundle08_prefix_ranks_10 arithBundle08_ranks_048
private theorem arithBundle08_prefix_ranks_12 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 56 = 27748874 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 52 4 27239532 509342 arithBundle08_prefix_ranks_11 arithBundle08_ranks_052
private theorem arithBundle08_prefix_ranks_13 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 60 = 28141110 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 56 4 27748874 392236 arithBundle08_prefix_ranks_12 arithBundle08_ranks_056
private theorem arithBundle08_prefix_ranks_14 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 64 = 28434124 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 60 4 28141110 293014 arithBundle08_prefix_ranks_13 arithBundle08_ranks_060
private theorem arithBundle08_prefix_ranks_15 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 68 = 28644506 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 64 4 28434124 210382 arithBundle08_prefix_ranks_14 arithBundle08_ranks_064
private theorem arithBundle08_prefix_ranks_16 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 72 = 28787674 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 68 4 28644506 143168 arithBundle08_prefix_ranks_15 arithBundle08_ranks_068
private theorem arithBundle08_prefix_ranks_17 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 76 = 28878156 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 72 4 28787674 90482 arithBundle08_prefix_ranks_16 arithBundle08_ranks_072
private theorem arithBundle08_prefix_ranks_18 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 80 = 28929098 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 76 4 28878156 50942 arithBundle08_prefix_ranks_17 arithBundle08_ranks_076
private theorem arithBundle08_prefix_ranks_19 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 84 = 28952478 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 80 4 28929098 23380 arithBundle08_prefix_ranks_18 arithBundle08_ranks_080
private theorem arithBundle08_prefix_ranks_20 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 88 = 28959475 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 84 4 28952478 6997 arithBundle08_prefix_ranks_19 arithBundle08_ranks_084
private theorem arithBundle08_prefix_ranks_21 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 92 = 28959861 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 88 4 28959475 386 arithBundle08_prefix_ranks_20 arithBundle08_ranks_088
private theorem arithBundle08_prefix_ranks_22 : arithBundle08_sliceWindow (auxiliaryRankSlice contact16) 0 102 = 28959861 :=
  arithBundle08_combineSlices (auxiliaryRankSlice contact16) 0 92 10 28959861 0 arithBundle08_prefix_ranks_21 arithBundle08_ranks_092

theorem contact16_margin : sourceMargin contact16 :=
  arithBundle08_margin_of_checked_counts contact16 102 169704479189907 9513207759326 654700380 28959861
    rfl arithBundle08_ordinary_columns arithBundle08_prefix_columns_24 arithBundle08_ordinary_ranks arithBundle08_prefix_ranks_22 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle09_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle09_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle09_sliceWindow f a b = x) (hy : arithBundle09_sliceWindow f (a+b) c = y) :
    arithBundle09_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle09_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle09_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle09_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle09_sliceWindow,Nat.zero_add]

private theorem arithBundle09_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle09_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle09_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle09_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle09_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle09_ordinary_columns : ordinaryColumnCount contact18 = 2313955664777711 := by decide +kernel
private theorem arithBundle09_columns_000 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 4 = 7049656135860 :=
  contactColumnsWindow_fast contact18 0 4 7049656135860 (by decide +kernel)
private theorem arithBundle09_columns_004 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 4 4 = 6702538575444 :=
  contactColumnsWindow_fast contact18 4 4 6702538575444 (by decide +kernel)
private theorem arithBundle09_columns_008 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 8 4 = 6364220859950 :=
  contactColumnsWindow_fast contact18 8 4 6364220859950 (by decide +kernel)
private theorem arithBundle09_columns_012 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 12 4 = 6034705909248 :=
  contactColumnsWindow_fast contact18 12 4 6034705909248 (by decide +kernel)
private theorem arithBundle09_columns_016 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 16 4 = 5713991731473 :=
  contactColumnsWindow_fast contact18 16 4 5713991731473 (by decide +kernel)
private theorem arithBundle09_columns_020 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 20 4 = 5402080376112 :=
  contactColumnsWindow_fast contact18 20 4 5402080376112 (by decide +kernel)
private theorem arithBundle09_columns_024 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 24 4 = 5098986140456 :=
  contactColumnsWindow_fast contact18 24 4 5098986140456 (by decide +kernel)
private theorem arithBundle09_columns_028 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 28 4 = 4804729129579 :=
  contactColumnsWindow_fast contact18 28 4 4804729129579 (by decide +kernel)
private theorem arithBundle09_columns_032 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 32 4 = 4519278310280 :=
  contactColumnsWindow_fast contact18 32 4 4519278310280 (by decide +kernel)
private theorem arithBundle09_columns_036 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 36 4 = 4242631501262 :=
  contactColumnsWindow_fast contact18 36 4 4242631501262 (by decide +kernel)
private theorem arithBundle09_columns_040 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 40 4 = 3974790453584 :=
  contactColumnsWindow_fast contact18 40 4 3974790453584 (by decide +kernel)
private theorem arithBundle09_columns_044 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 44 4 = 3715772956389 :=
  contactColumnsWindow_fast contact18 44 4 3715772956389 (by decide +kernel)
private theorem arithBundle09_columns_048 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 48 4 = 3465594013574 :=
  contactColumnsWindow_fast contact18 48 4 3465594013574 (by decide +kernel)
private theorem arithBundle09_columns_052 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 52 4 = 3224222655288 :=
  contactColumnsWindow_fast contact18 52 4 3224222655288 (by decide +kernel)
private theorem arithBundle09_columns_056 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 56 4 = 2991659484002 :=
  contactColumnsWindow_fast contact18 56 4 2991659484002 (by decide +kernel)
private theorem arithBundle09_columns_060 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 60 4 = 2767904312604 :=
  contactColumnsWindow_fast contact18 60 4 2767904312604 (by decide +kernel)
private theorem arithBundle09_columns_064 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 64 4 = 2552982009424 :=
  contactColumnsWindow_fast contact18 64 4 2552982009424 (by decide +kernel)
private theorem arithBundle09_columns_068 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 68 4 = 2346895825399 :=
  contactColumnsWindow_fast contact18 68 4 2346895825399 (by decide +kernel)
private theorem arithBundle09_columns_072 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 72 4 = 2149622181756 :=
  contactColumnsWindow_fast contact18 72 4 2149622181756 (by decide +kernel)
private theorem arithBundle09_columns_076 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 76 4 = 1961157373520 :=
  contactColumnsWindow_fast contact18 76 4 1961157373520 (by decide +kernel)
private theorem arithBundle09_columns_080 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 80 4 = 1781500367898 :=
  contactColumnsWindow_fast contact18 80 4 1781500367898 (by decide +kernel)
private theorem arithBundle09_columns_084 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 84 4 = 1610680993267 :=
  contactColumnsWindow_fast contact18 84 4 1610680993267 (by decide +kernel)
private theorem arithBundle09_columns_088 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 88 4 = 1448693493751 :=
  contactColumnsWindow_fast contact18 88 4 1448693493751 (by decide +kernel)
private theorem arithBundle09_columns_092 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 92 4 = 1295518275618 :=
  contactColumnsWindow_fast contact18 92 4 1295518275618 (by decide +kernel)
private theorem arithBundle09_columns_096 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 96 4 = 1151151785105 :=
  contactColumnsWindow_fast contact18 96 4 1151151785105 (by decide +kernel)
private theorem arithBundle09_columns_100 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 100 4 = 1015593378785 :=
  contactColumnsWindow_fast contact18 100 4 1015593378785 (by decide +kernel)
private theorem arithBundle09_columns_104 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 104 4 = 888876589722 :=
  contactColumnsWindow_fast contact18 104 4 888876589722 (by decide +kernel)
private theorem arithBundle09_columns_108 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 108 4 = 770987821045 :=
  contactColumnsWindow_fast contact18 108 4 770987821045 (by decide +kernel)
private theorem arithBundle09_columns_112 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 112 4 = 661910855592 :=
  contactColumnsWindow_fast contact18 112 4 661910855592 (by decide +kernel)
private theorem arithBundle09_columns_116 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 116 4 = 561642746826 :=
  contactColumnsWindow_fast contact18 116 4 561642746826 (by decide +kernel)
private theorem arithBundle09_columns_120 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 120 4 = 470183810750 :=
  contactColumnsWindow_fast contact18 120 4 470183810750 (by decide +kernel)
private theorem arithBundle09_columns_124 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 124 4 = 387568678284 :=
  contactColumnsWindow_fast contact18 124 4 387568678284 (by decide +kernel)
private theorem arithBundle09_columns_128 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 128 4 = 313778640367 :=
  contactColumnsWindow_fast contact18 128 4 313778640367 (by decide +kernel)
private theorem arithBundle09_columns_132 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 132 4 = 248800066346 :=
  contactColumnsWindow_fast contact18 132 4 248800066346 (by decide +kernel)
private theorem arithBundle09_columns_136 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 136 4 = 192613615462 :=
  contactColumnsWindow_fast contact18 136 4 192613615462 (by decide +kernel)
private theorem arithBundle09_columns_140 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 140 4 = 145073039648 :=
  contactColumnsWindow_fast contact18 140 4 145073039648 (by decide +kernel)
private theorem arithBundle09_columns_144 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 144 4 = 105866867935 :=
  contactColumnsWindow_fast contact18 144 4 105866867935 (by decide +kernel)
private theorem arithBundle09_columns_148 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 148 4 = 74460194994 :=
  contactColumnsWindow_fast contact18 148 4 74460194994 (by decide +kernel)
private theorem arithBundle09_columns_152 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 152 4 = 50169815509 :=
  contactColumnsWindow_fast contact18 152 4 50169815509 (by decide +kernel)
private theorem arithBundle09_columns_156 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 156 4 = 32160841287 :=
  contactColumnsWindow_fast contact18 156 4 32160841287 (by decide +kernel)
private theorem arithBundle09_columns_160 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 160 4 = 19447648814 :=
  contactColumnsWindow_fast contact18 160 4 19447648814 (by decide +kernel)
private theorem arithBundle09_columns_164 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 164 2 = 6321987952 :=
  contactColumnsWindow_fast contact18 164 2 6321987952 (by decide +kernel)
private theorem arithBundle09_prefix_columns_00 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 8 = 13752194711304 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 4 4 7049656135860 6702538575444 arithBundle09_columns_000 arithBundle09_columns_004
private theorem arithBundle09_prefix_columns_01 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 12 = 20116415571254 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 8 4 13752194711304 6364220859950 arithBundle09_prefix_columns_00 arithBundle09_columns_008
private theorem arithBundle09_prefix_columns_02 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 16 = 26151121480502 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 12 4 20116415571254 6034705909248 arithBundle09_prefix_columns_01 arithBundle09_columns_012
private theorem arithBundle09_prefix_columns_03 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 20 = 31865113211975 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 16 4 26151121480502 5713991731473 arithBundle09_prefix_columns_02 arithBundle09_columns_016
private theorem arithBundle09_prefix_columns_04 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 24 = 37267193588087 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 20 4 31865113211975 5402080376112 arithBundle09_prefix_columns_03 arithBundle09_columns_020
private theorem arithBundle09_prefix_columns_05 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 28 = 42366179728543 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 24 4 37267193588087 5098986140456 arithBundle09_prefix_columns_04 arithBundle09_columns_024
private theorem arithBundle09_prefix_columns_06 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 32 = 47170908858122 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 28 4 42366179728543 4804729129579 arithBundle09_prefix_columns_05 arithBundle09_columns_028
private theorem arithBundle09_prefix_columns_07 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 36 = 51690187168402 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 32 4 47170908858122 4519278310280 arithBundle09_prefix_columns_06 arithBundle09_columns_032
private theorem arithBundle09_prefix_columns_08 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 40 = 55932818669664 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 36 4 51690187168402 4242631501262 arithBundle09_prefix_columns_07 arithBundle09_columns_036
private theorem arithBundle09_prefix_columns_09 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 44 = 59907609123248 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 40 4 55932818669664 3974790453584 arithBundle09_prefix_columns_08 arithBundle09_columns_040
private theorem arithBundle09_prefix_columns_10 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 48 = 63623382079637 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 44 4 59907609123248 3715772956389 arithBundle09_prefix_columns_09 arithBundle09_columns_044
private theorem arithBundle09_prefix_columns_11 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 52 = 67088976093211 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 48 4 63623382079637 3465594013574 arithBundle09_prefix_columns_10 arithBundle09_columns_048
private theorem arithBundle09_prefix_columns_12 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 56 = 70313198748499 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 52 4 67088976093211 3224222655288 arithBundle09_prefix_columns_11 arithBundle09_columns_052
private theorem arithBundle09_prefix_columns_13 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 60 = 73304858232501 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 56 4 70313198748499 2991659484002 arithBundle09_prefix_columns_12 arithBundle09_columns_056
private theorem arithBundle09_prefix_columns_14 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 64 = 76072762545105 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 60 4 73304858232501 2767904312604 arithBundle09_prefix_columns_13 arithBundle09_columns_060
private theorem arithBundle09_prefix_columns_15 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 68 = 78625744554529 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 64 4 76072762545105 2552982009424 arithBundle09_prefix_columns_14 arithBundle09_columns_064
private theorem arithBundle09_prefix_columns_16 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 72 = 80972640379928 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 68 4 78625744554529 2346895825399 arithBundle09_prefix_columns_15 arithBundle09_columns_068
private theorem arithBundle09_prefix_columns_17 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 76 = 83122262561684 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 72 4 80972640379928 2149622181756 arithBundle09_prefix_columns_16 arithBundle09_columns_072
private theorem arithBundle09_prefix_columns_18 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 80 = 85083419935204 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 76 4 83122262561684 1961157373520 arithBundle09_prefix_columns_17 arithBundle09_columns_076
private theorem arithBundle09_prefix_columns_19 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 84 = 86864920303102 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 80 4 85083419935204 1781500367898 arithBundle09_prefix_columns_18 arithBundle09_columns_080
private theorem arithBundle09_prefix_columns_20 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 88 = 88475601296369 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 84 4 86864920303102 1610680993267 arithBundle09_prefix_columns_19 arithBundle09_columns_084
private theorem arithBundle09_prefix_columns_21 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 92 = 89924294790120 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 88 4 88475601296369 1448693493751 arithBundle09_prefix_columns_20 arithBundle09_columns_088
private theorem arithBundle09_prefix_columns_22 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 96 = 91219813065738 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 92 4 89924294790120 1295518275618 arithBundle09_prefix_columns_21 arithBundle09_columns_092
private theorem arithBundle09_prefix_columns_23 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 100 = 92370964850843 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 96 4 91219813065738 1151151785105 arithBundle09_prefix_columns_22 arithBundle09_columns_096
private theorem arithBundle09_prefix_columns_24 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 104 = 93386558229628 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 100 4 92370964850843 1015593378785 arithBundle09_prefix_columns_23 arithBundle09_columns_100
private theorem arithBundle09_prefix_columns_25 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 108 = 94275434819350 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 104 4 93386558229628 888876589722 arithBundle09_prefix_columns_24 arithBundle09_columns_104
private theorem arithBundle09_prefix_columns_26 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 112 = 95046422640395 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 108 4 94275434819350 770987821045 arithBundle09_prefix_columns_25 arithBundle09_columns_108
private theorem arithBundle09_prefix_columns_27 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 116 = 95708333495987 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 112 4 95046422640395 661910855592 arithBundle09_prefix_columns_26 arithBundle09_columns_112
private theorem arithBundle09_prefix_columns_28 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 120 = 96269976242813 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 116 4 95708333495987 561642746826 arithBundle09_prefix_columns_27 arithBundle09_columns_116
private theorem arithBundle09_prefix_columns_29 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 124 = 96740160053563 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 120 4 96269976242813 470183810750 arithBundle09_prefix_columns_28 arithBundle09_columns_120
private theorem arithBundle09_prefix_columns_30 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 128 = 97127728731847 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 124 4 96740160053563 387568678284 arithBundle09_prefix_columns_29 arithBundle09_columns_124
private theorem arithBundle09_prefix_columns_31 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 132 = 97441507372214 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 128 4 97127728731847 313778640367 arithBundle09_prefix_columns_30 arithBundle09_columns_128
private theorem arithBundle09_prefix_columns_32 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 136 = 97690307438560 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 132 4 97441507372214 248800066346 arithBundle09_prefix_columns_31 arithBundle09_columns_132
private theorem arithBundle09_prefix_columns_33 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 140 = 97882921054022 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 136 4 97690307438560 192613615462 arithBundle09_prefix_columns_32 arithBundle09_columns_136
private theorem arithBundle09_prefix_columns_34 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 144 = 98027994093670 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 140 4 97882921054022 145073039648 arithBundle09_prefix_columns_33 arithBundle09_columns_140
private theorem arithBundle09_prefix_columns_35 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 148 = 98133860961605 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 144 4 98027994093670 105866867935 arithBundle09_prefix_columns_34 arithBundle09_columns_144
private theorem arithBundle09_prefix_columns_36 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 152 = 98208321156599 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 148 4 98133860961605 74460194994 arithBundle09_prefix_columns_35 arithBundle09_columns_148
private theorem arithBundle09_prefix_columns_37 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 156 = 98258490972108 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 152 4 98208321156599 50169815509 arithBundle09_prefix_columns_36 arithBundle09_columns_152
private theorem arithBundle09_prefix_columns_38 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 160 = 98290651813395 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 156 4 98258490972108 32160841287 arithBundle09_prefix_columns_37 arithBundle09_columns_156
private theorem arithBundle09_prefix_columns_39 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 164 = 98310099462209 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 160 4 98290651813395 19447648814 arithBundle09_prefix_columns_38 arithBundle09_columns_160
private theorem arithBundle09_prefix_columns_40 : arithBundle09_sliceWindow (auxiliaryColumnSlice contact18) 0 166 = 98316421450161 :=
  arithBundle09_combineSlices (auxiliaryColumnSlice contact18) 0 164 2 98310099462209 6321987952 arithBundle09_prefix_columns_39 arithBundle09_columns_164

private theorem arithBundle09_ordinary_ranks : ordinaryRankBound contact18 = 8903816944 := by decide +kernel
private theorem arithBundle09_ranks_000 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 4 = 26575668 :=
  contactRankWindow_of_rec contact18 0 4 26575668 (by decide +kernel)
private theorem arithBundle09_ranks_004 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 4 4 = 24869684 :=
  contactRankWindow_of_rec contact18 4 4 24869684 (by decide +kernel)
private theorem arithBundle09_ranks_008 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 8 4 = 23224628 :=
  contactRankWindow_of_rec contact18 8 4 23224628 (by decide +kernel)
private theorem arithBundle09_ranks_012 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 12 4 = 21640500 :=
  contactRankWindow_of_rec contact18 12 4 21640500 (by decide +kernel)
private theorem arithBundle09_ranks_016 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 16 4 = 20117300 :=
  contactRankWindow_of_rec contact18 16 4 20117300 (by decide +kernel)
private theorem arithBundle09_ranks_020 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 20 4 = 18655028 :=
  contactRankWindow_of_rec contact18 20 4 18655028 (by decide +kernel)
private theorem arithBundle09_ranks_024 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 24 4 = 17253684 :=
  contactRankWindow_of_rec contact18 24 4 17253684 (by decide +kernel)
private theorem arithBundle09_ranks_028 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 28 4 = 15913268 :=
  contactRankWindow_of_rec contact18 28 4 15913268 (by decide +kernel)
private theorem arithBundle09_ranks_032 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 32 4 = 14633780 :=
  contactRankWindow_of_rec contact18 32 4 14633780 (by decide +kernel)
private theorem arithBundle09_ranks_036 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 36 4 = 13415220 :=
  contactRankWindow_of_rec contact18 36 4 13415220 (by decide +kernel)
private theorem arithBundle09_ranks_040 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 40 4 = 12257588 :=
  contactRankWindow_of_rec contact18 40 4 12257588 (by decide +kernel)
private theorem arithBundle09_ranks_044 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 44 4 = 11160884 :=
  contactRankWindow_of_rec contact18 44 4 11160884 (by decide +kernel)
private theorem arithBundle09_ranks_048 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 48 4 = 10125108 :=
  contactRankWindow_of_rec contact18 48 4 10125108 (by decide +kernel)
private theorem arithBundle09_ranks_052 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 52 4 = 9150176 :=
  contactRankWindow_of_rec contact18 52 4 9150176 (by decide +kernel)
private theorem arithBundle09_ranks_056 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 56 4 = 8235266 :=
  contactRankWindow_of_rec contact18 56 4 8235266 (by decide +kernel)
private theorem arithBundle09_ranks_060 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 60 4 = 7379140 :=
  contactRankWindow_of_rec contact18 60 4 7379140 (by decide +kernel)
private theorem arithBundle09_ranks_064 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 64 4 = 6580522 :=
  contactRankWindow_of_rec contact18 64 4 6580522 (by decide +kernel)
private theorem arithBundle09_ranks_068 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 68 4 = 5837820 :=
  contactRankWindow_of_rec contact18 68 4 5837820 (by decide +kernel)
private theorem arithBundle09_ranks_072 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 72 4 = 5149236 :=
  contactRankWindow_of_rec contact18 72 4 5149236 (by decide +kernel)
private theorem arithBundle09_ranks_076 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 76 4 = 4512962 :=
  contactRankWindow_of_rec contact18 76 4 4512962 (by decide +kernel)
private theorem arithBundle09_ranks_080 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 80 4 = 3927404 :=
  contactRankWindow_of_rec contact18 80 4 3927404 (by decide +kernel)
private theorem arithBundle09_ranks_084 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 84 4 = 3390628 :=
  contactRankWindow_of_rec contact18 84 4 3390628 (by decide +kernel)
private theorem arithBundle09_ranks_088 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 88 4 = 2900826 :=
  contactRankWindow_of_rec contact18 88 4 2900826 (by decide +kernel)
private theorem arithBundle09_ranks_092 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 92 4 = 2456540 :=
  contactRankWindow_of_rec contact18 92 4 2456540 (by decide +kernel)
private theorem arithBundle09_ranks_096 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 96 4 = 2055700 :=
  contactRankWindow_of_rec contact18 96 4 2055700 (by decide +kernel)
private theorem arithBundle09_ranks_100 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 100 4 = 1696498 :=
  contactRankWindow_of_rec contact18 100 4 1696498 (by decide +kernel)
private theorem arithBundle09_ranks_104 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 104 4 = 1377612 :=
  contactRankWindow_of_rec contact18 104 4 1377612 (by decide +kernel)
private theorem arithBundle09_ranks_108 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 108 4 = 1096836 :=
  contactRankWindow_of_rec contact18 108 4 1096836 (by decide +kernel)
private theorem arithBundle09_ranks_112 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 112 4 = 852362 :=
  contactRankWindow_of_rec contact18 112 4 852362 (by decide +kernel)
private theorem arithBundle09_ranks_116 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 116 4 = 643004 :=
  contactRankWindow_of_rec contact18 116 4 643004 (by decide +kernel)
private theorem arithBundle09_ranks_120 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 120 4 = 466420 :=
  contactRankWindow_of_rec contact18 120 4 466420 (by decide +kernel)
private theorem arithBundle09_ranks_124 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 124 4 = 320802 :=
  contactRankWindow_of_rec contact18 124 4 320802 (by decide +kernel)
private theorem arithBundle09_ranks_128 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 128 4 = 205100 :=
  contactRankWindow_of_rec contact18 128 4 205100 (by decide +kernel)
private theorem arithBundle09_ranks_132 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 132 4 = 116836 :=
  contactRankWindow_of_rec contact18 132 4 116836 (by decide +kernel)
private theorem arithBundle09_ranks_136 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 136 4 = 54205 :=
  contactRankWindow_of_rec contact18 136 4 54205 (by decide +kernel)
private theorem arithBundle09_ranks_140 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 140 4 = 16421 :=
  contactRankWindow_of_rec contact18 140 4 16421 (by decide +kernel)
private theorem arithBundle09_ranks_144 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 144 4 = 924 :=
  contactRankWindow_of_rec contact18 144 4 924 (by decide +kernel)
private theorem arithBundle09_ranks_148 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 148 18 = 0 :=
  contactRankWindow_of_rec contact18 148 18 0 (by decide +kernel)
private theorem arithBundle09_prefix_ranks_00 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 8 = 51445352 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 4 4 26575668 24869684 arithBundle09_ranks_000 arithBundle09_ranks_004
private theorem arithBundle09_prefix_ranks_01 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 12 = 74669980 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 8 4 51445352 23224628 arithBundle09_prefix_ranks_00 arithBundle09_ranks_008
private theorem arithBundle09_prefix_ranks_02 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 16 = 96310480 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 12 4 74669980 21640500 arithBundle09_prefix_ranks_01 arithBundle09_ranks_012
private theorem arithBundle09_prefix_ranks_03 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 20 = 116427780 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 16 4 96310480 20117300 arithBundle09_prefix_ranks_02 arithBundle09_ranks_016
private theorem arithBundle09_prefix_ranks_04 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 24 = 135082808 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 20 4 116427780 18655028 arithBundle09_prefix_ranks_03 arithBundle09_ranks_020
private theorem arithBundle09_prefix_ranks_05 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 28 = 152336492 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 24 4 135082808 17253684 arithBundle09_prefix_ranks_04 arithBundle09_ranks_024
private theorem arithBundle09_prefix_ranks_06 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 32 = 168249760 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 28 4 152336492 15913268 arithBundle09_prefix_ranks_05 arithBundle09_ranks_028
private theorem arithBundle09_prefix_ranks_07 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 36 = 182883540 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 32 4 168249760 14633780 arithBundle09_prefix_ranks_06 arithBundle09_ranks_032
private theorem arithBundle09_prefix_ranks_08 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 40 = 196298760 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 36 4 182883540 13415220 arithBundle09_prefix_ranks_07 arithBundle09_ranks_036
private theorem arithBundle09_prefix_ranks_09 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 44 = 208556348 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 40 4 196298760 12257588 arithBundle09_prefix_ranks_08 arithBundle09_ranks_040
private theorem arithBundle09_prefix_ranks_10 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 48 = 219717232 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 44 4 208556348 11160884 arithBundle09_prefix_ranks_09 arithBundle09_ranks_044
private theorem arithBundle09_prefix_ranks_11 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 52 = 229842340 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 48 4 219717232 10125108 arithBundle09_prefix_ranks_10 arithBundle09_ranks_048
private theorem arithBundle09_prefix_ranks_12 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 56 = 238992516 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 52 4 229842340 9150176 arithBundle09_prefix_ranks_11 arithBundle09_ranks_052
private theorem arithBundle09_prefix_ranks_13 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 60 = 247227782 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 56 4 238992516 8235266 arithBundle09_prefix_ranks_12 arithBundle09_ranks_056
private theorem arithBundle09_prefix_ranks_14 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 64 = 254606922 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 60 4 247227782 7379140 arithBundle09_prefix_ranks_13 arithBundle09_ranks_060
private theorem arithBundle09_prefix_ranks_15 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 68 = 261187444 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 64 4 254606922 6580522 arithBundle09_prefix_ranks_14 arithBundle09_ranks_064
private theorem arithBundle09_prefix_ranks_16 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 72 = 267025264 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 68 4 261187444 5837820 arithBundle09_prefix_ranks_15 arithBundle09_ranks_068
private theorem arithBundle09_prefix_ranks_17 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 76 = 272174500 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 72 4 267025264 5149236 arithBundle09_prefix_ranks_16 arithBundle09_ranks_072
private theorem arithBundle09_prefix_ranks_18 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 80 = 276687462 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 76 4 272174500 4512962 arithBundle09_prefix_ranks_17 arithBundle09_ranks_076
private theorem arithBundle09_prefix_ranks_19 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 84 = 280614866 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 80 4 276687462 3927404 arithBundle09_prefix_ranks_18 arithBundle09_ranks_080
private theorem arithBundle09_prefix_ranks_20 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 88 = 284005494 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 84 4 280614866 3390628 arithBundle09_prefix_ranks_19 arithBundle09_ranks_084
private theorem arithBundle09_prefix_ranks_21 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 92 = 286906320 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 88 4 284005494 2900826 arithBundle09_prefix_ranks_20 arithBundle09_ranks_088
private theorem arithBundle09_prefix_ranks_22 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 96 = 289362860 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 92 4 286906320 2456540 arithBundle09_prefix_ranks_21 arithBundle09_ranks_092
private theorem arithBundle09_prefix_ranks_23 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 100 = 291418560 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 96 4 289362860 2055700 arithBundle09_prefix_ranks_22 arithBundle09_ranks_096
private theorem arithBundle09_prefix_ranks_24 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 104 = 293115058 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 100 4 291418560 1696498 arithBundle09_prefix_ranks_23 arithBundle09_ranks_100
private theorem arithBundle09_prefix_ranks_25 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 108 = 294492670 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 104 4 293115058 1377612 arithBundle09_prefix_ranks_24 arithBundle09_ranks_104
private theorem arithBundle09_prefix_ranks_26 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 112 = 295589506 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 108 4 294492670 1096836 arithBundle09_prefix_ranks_25 arithBundle09_ranks_108
private theorem arithBundle09_prefix_ranks_27 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 116 = 296441868 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 112 4 295589506 852362 arithBundle09_prefix_ranks_26 arithBundle09_ranks_112
private theorem arithBundle09_prefix_ranks_28 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 120 = 297084872 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 116 4 296441868 643004 arithBundle09_prefix_ranks_27 arithBundle09_ranks_116
private theorem arithBundle09_prefix_ranks_29 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 124 = 297551292 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 120 4 297084872 466420 arithBundle09_prefix_ranks_28 arithBundle09_ranks_120
private theorem arithBundle09_prefix_ranks_30 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 128 = 297872094 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 124 4 297551292 320802 arithBundle09_prefix_ranks_29 arithBundle09_ranks_124
private theorem arithBundle09_prefix_ranks_31 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 132 = 298077194 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 128 4 297872094 205100 arithBundle09_prefix_ranks_30 arithBundle09_ranks_128
private theorem arithBundle09_prefix_ranks_32 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 136 = 298194030 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 132 4 298077194 116836 arithBundle09_prefix_ranks_31 arithBundle09_ranks_132
private theorem arithBundle09_prefix_ranks_33 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 140 = 298248235 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 136 4 298194030 54205 arithBundle09_prefix_ranks_32 arithBundle09_ranks_136
private theorem arithBundle09_prefix_ranks_34 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 144 = 298264656 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 140 4 298248235 16421 arithBundle09_prefix_ranks_33 arithBundle09_ranks_140
private theorem arithBundle09_prefix_ranks_35 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 148 = 298265580 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 144 4 298264656 924 arithBundle09_prefix_ranks_34 arithBundle09_ranks_144
private theorem arithBundle09_prefix_ranks_36 : arithBundle09_sliceWindow (auxiliaryRankSlice contact18) 0 166 = 298265580 :=
  arithBundle09_combineSlices (auxiliaryRankSlice contact18) 0 148 18 298265580 0 arithBundle09_prefix_ranks_35 arithBundle09_ranks_148

theorem contact18_margin : sourceMargin contact18 :=
  arithBundle09_margin_of_checked_counts contact18 166 2313955664777711 98316421450161 8903816944 298265580
    rfl arithBundle09_ordinary_columns arithBundle09_prefix_columns_40 arithBundle09_ordinary_ranks arithBundle09_prefix_ranks_36 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle10_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle10_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle10_sliceWindow f a b = x) (hy : arithBundle10_sliceWindow f (a+b) c = y) :
    arithBundle10_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle10_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle10_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle10_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle10_sliceWindow,Nat.zero_add]

private theorem arithBundle10_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle10_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle10_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle10_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle10_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle10_ordinary_columns : ordinaryColumnCount contact19 = 156745256302232 := by decide +kernel
private theorem arithBundle10_columns_000 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 4 = 1313272788656 :=
  contactColumnsWindow_fast contact19 0 4 1313272788656 (by decide +kernel)
private theorem arithBundle10_columns_004 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 4 4 = 1212521196224 :=
  contactColumnsWindow_fast contact19 4 4 1212521196224 (by decide +kernel)
private theorem arithBundle10_columns_008 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 8 4 = 1115808714384 :=
  contactColumnsWindow_fast contact19 8 4 1115808714384 (by decide +kernel)
private theorem arithBundle10_columns_012 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 12 4 = 1023152206656 :=
  contactColumnsWindow_fast contact19 12 4 1023152206656 (by decide +kernel)
private theorem arithBundle10_columns_016 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 16 4 = 934552116985 :=
  contactColumnsWindow_fast contact19 16 4 934552116985 (by decide +kernel)
private theorem arithBundle10_columns_020 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 20 4 = 849993606484 :=
  contactColumnsWindow_fast contact19 20 4 849993606484 (by decide +kernel)
private theorem arithBundle10_columns_024 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 24 4 = 769475825283 :=
  contactColumnsWindow_fast contact19 24 4 769475825283 (by decide +kernel)
private theorem arithBundle10_columns_028 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 28 4 = 693000030300 :=
  contactColumnsWindow_fast contact19 28 4 693000030300 (by decide +kernel)
private theorem arithBundle10_columns_032 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 32 4 = 620584745718 :=
  contactColumnsWindow_fast contact19 32 4 620584745718 (by decide +kernel)
private theorem arithBundle10_columns_036 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 36 4 = 552226168161 :=
  contactColumnsWindow_fast contact19 36 4 552226168161 (by decide +kernel)
private theorem arithBundle10_columns_040 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 40 4 = 487910142880 :=
  contactColumnsWindow_fast contact19 40 4 487910142880 (by decide +kernel)
private theorem arithBundle10_columns_044 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 44 4 = 427634673198 :=
  contactColumnsWindow_fast contact19 44 4 427634673198 (by decide +kernel)
private theorem arithBundle10_columns_048 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 48 4 = 371401796076 :=
  contactColumnsWindow_fast contact19 48 4 371401796076 (by decide +kernel)
private theorem arithBundle10_columns_052 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 52 4 = 319231591680 :=
  contactColumnsWindow_fast contact19 52 4 319231591680 (by decide +kernel)
private theorem arithBundle10_columns_056 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 56 4 = 271115518362 :=
  contactColumnsWindow_fast contact19 56 4 271115518362 (by decide +kernel)
private theorem arithBundle10_columns_060 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 60 4 = 227041978048 :=
  contactColumnsWindow_fast contact19 60 4 227041978048 (by decide +kernel)
private theorem arithBundle10_columns_064 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 64 4 = 187008883884 :=
  contactColumnsWindow_fast contact19 64 4 187008883884 (by decide +kernel)
private theorem arithBundle10_columns_068 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 68 4 = 151019213064 :=
  contactColumnsWindow_fast contact19 68 4 151019213064 (by decide +kernel)
private theorem arithBundle10_columns_072 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 72 4 = 119093736414 :=
  contactColumnsWindow_fast contact19 72 4 119093736414 (by decide +kernel)
private theorem arithBundle10_columns_076 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 76 4 = 91220187648 :=
  contactColumnsWindow_fast contact19 76 4 91220187648 (by decide +kernel)
private theorem arithBundle10_columns_080 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 80 4 = 67389111988 :=
  contactColumnsWindow_fast contact19 80 4 67389111988 (by decide +kernel)
private theorem arithBundle10_columns_084 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 84 4 = 47597703545 :=
  contactColumnsWindow_fast contact19 84 4 47597703545 (by decide +kernel)
private theorem arithBundle10_columns_088 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 88 4 = 31811583169 :=
  contactColumnsWindow_fast contact19 88 4 31811583169 (by decide +kernel)
private theorem arithBundle10_columns_092 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 92 4 = 19868090801 :=
  contactColumnsWindow_fast contact19 92 4 19868090801 (by decide +kernel)
private theorem arithBundle10_columns_096 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 96 4 = 11396746093 :=
  contactColumnsWindow_fast contact19 96 4 11396746093 (by decide +kernel)
private theorem arithBundle10_columns_100 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 100 4 = 5874730044 :=
  contactColumnsWindow_fast contact19 100 4 5874730044 (by decide +kernel)
private theorem arithBundle10_prefix_columns_00 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 8 = 2525793984880 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 4 4 1313272788656 1212521196224 arithBundle10_columns_000 arithBundle10_columns_004
private theorem arithBundle10_prefix_columns_01 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 12 = 3641602699264 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 8 4 2525793984880 1115808714384 arithBundle10_prefix_columns_00 arithBundle10_columns_008
private theorem arithBundle10_prefix_columns_02 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 16 = 4664754905920 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 12 4 3641602699264 1023152206656 arithBundle10_prefix_columns_01 arithBundle10_columns_012
private theorem arithBundle10_prefix_columns_03 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 20 = 5599307022905 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 16 4 4664754905920 934552116985 arithBundle10_prefix_columns_02 arithBundle10_columns_016
private theorem arithBundle10_prefix_columns_04 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 24 = 6449300629389 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 20 4 5599307022905 849993606484 arithBundle10_prefix_columns_03 arithBundle10_columns_020
private theorem arithBundle10_prefix_columns_05 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 28 = 7218776454672 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 24 4 6449300629389 769475825283 arithBundle10_prefix_columns_04 arithBundle10_columns_024
private theorem arithBundle10_prefix_columns_06 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 32 = 7911776484972 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 28 4 7218776454672 693000030300 arithBundle10_prefix_columns_05 arithBundle10_columns_028
private theorem arithBundle10_prefix_columns_07 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 36 = 8532361230690 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 32 4 7911776484972 620584745718 arithBundle10_prefix_columns_06 arithBundle10_columns_032
private theorem arithBundle10_prefix_columns_08 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 40 = 9084587398851 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 36 4 8532361230690 552226168161 arithBundle10_prefix_columns_07 arithBundle10_columns_036
private theorem arithBundle10_prefix_columns_09 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 44 = 9572497541731 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 40 4 9084587398851 487910142880 arithBundle10_prefix_columns_08 arithBundle10_columns_040
private theorem arithBundle10_prefix_columns_10 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 48 = 10000132214929 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 44 4 9572497541731 427634673198 arithBundle10_prefix_columns_09 arithBundle10_columns_044
private theorem arithBundle10_prefix_columns_11 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 52 = 10371534011005 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 48 4 10000132214929 371401796076 arithBundle10_prefix_columns_10 arithBundle10_columns_048
private theorem arithBundle10_prefix_columns_12 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 56 = 10690765602685 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 52 4 10371534011005 319231591680 arithBundle10_prefix_columns_11 arithBundle10_columns_052
private theorem arithBundle10_prefix_columns_13 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 60 = 10961881121047 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 56 4 10690765602685 271115518362 arithBundle10_prefix_columns_12 arithBundle10_columns_056
private theorem arithBundle10_prefix_columns_14 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 64 = 11188923099095 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 60 4 10961881121047 227041978048 arithBundle10_prefix_columns_13 arithBundle10_columns_060
private theorem arithBundle10_prefix_columns_15 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 68 = 11375931982979 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 64 4 11188923099095 187008883884 arithBundle10_prefix_columns_14 arithBundle10_columns_064
private theorem arithBundle10_prefix_columns_16 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 72 = 11526951196043 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 68 4 11375931982979 151019213064 arithBundle10_prefix_columns_15 arithBundle10_columns_068
private theorem arithBundle10_prefix_columns_17 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 76 = 11646044932457 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 72 4 11526951196043 119093736414 arithBundle10_prefix_columns_16 arithBundle10_columns_072
private theorem arithBundle10_prefix_columns_18 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 80 = 11737265120105 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 76 4 11646044932457 91220187648 arithBundle10_prefix_columns_17 arithBundle10_columns_076
private theorem arithBundle10_prefix_columns_19 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 84 = 11804654232093 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 80 4 11737265120105 67389111988 arithBundle10_prefix_columns_18 arithBundle10_columns_080
private theorem arithBundle10_prefix_columns_20 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 88 = 11852251935638 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 84 4 11804654232093 47597703545 arithBundle10_prefix_columns_19 arithBundle10_columns_084
private theorem arithBundle10_prefix_columns_21 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 92 = 11884063518807 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 88 4 11852251935638 31811583169 arithBundle10_prefix_columns_20 arithBundle10_columns_088
private theorem arithBundle10_prefix_columns_22 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 96 = 11903931609608 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 92 4 11884063518807 19868090801 arithBundle10_prefix_columns_21 arithBundle10_columns_092
private theorem arithBundle10_prefix_columns_23 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 100 = 11915328355701 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 96 4 11903931609608 11396746093 arithBundle10_prefix_columns_22 arithBundle10_columns_096
private theorem arithBundle10_prefix_columns_24 : arithBundle10_sliceWindow (auxiliaryColumnSlice contact19) 0 104 = 11921203085745 :=
  arithBundle10_combineSlices (auxiliaryColumnSlice contact19) 0 100 4 11915328355701 5874730044 arithBundle10_prefix_columns_23 arithBundle10_columns_100

private theorem arithBundle10_ordinary_ranks : ordinaryRankBound contact19 = 607130443 := by decide +kernel
private theorem arithBundle10_ranks_000 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 4 = 4916474 :=
  contactRankWindow_of_rec contact19 0 4 4916474 (by decide +kernel)
private theorem arithBundle10_ranks_004 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 4 4 = 4427034 :=
  contactRankWindow_of_rec contact19 4 4 4427034 (by decide +kernel)
private theorem arithBundle10_ranks_008 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 8 4 = 3965562 :=
  contactRankWindow_of_rec contact19 8 4 3965562 (by decide +kernel)
private theorem arithBundle10_ranks_012 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 12 4 = 3532058 :=
  contactRankWindow_of_rec contact19 12 4 3532058 (by decide +kernel)
private theorem arithBundle10_ranks_016 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 16 4 = 3126522 :=
  contactRankWindow_of_rec contact19 16 4 3126522 (by decide +kernel)
private theorem arithBundle10_ranks_020 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 20 4 = 2748954 :=
  contactRankWindow_of_rec contact19 20 4 2748954 (by decide +kernel)
private theorem arithBundle10_ranks_024 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 24 4 = 2399354 :=
  contactRankWindow_of_rec contact19 24 4 2399354 (by decide +kernel)
private theorem arithBundle10_ranks_028 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 28 4 = 2077722 :=
  contactRankWindow_of_rec contact19 28 4 2077722 (by decide +kernel)
private theorem arithBundle10_ranks_032 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 32 4 = 1783924 :=
  contactRankWindow_of_rec contact19 32 4 1783924 (by decide +kernel)
private theorem arithBundle10_ranks_036 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 36 4 = 1517262 :=
  contactRankWindow_of_rec contact19 36 4 1517262 (by decide +kernel)
private theorem arithBundle10_ranks_040 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 40 4 = 1276849 :=
  contactRankWindow_of_rec contact19 40 4 1276849 (by decide +kernel)
private theorem arithBundle10_ranks_044 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 44 4 = 1061535 :=
  contactRankWindow_of_rec contact19 44 4 1061535 (by decide +kernel)
private theorem arithBundle10_ranks_048 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 48 4 = 870082 :=
  contactRankWindow_of_rec contact19 48 4 870082 (by decide +kernel)
private theorem arithBundle10_ranks_052 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 52 4 = 701401 :=
  contactRankWindow_of_rec contact19 52 4 701401 (by decide +kernel)
private theorem arithBundle10_ranks_056 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 56 4 = 554203 :=
  contactRankWindow_of_rec contact19 56 4 554203 (by decide +kernel)
private theorem arithBundle10_ranks_060 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 60 4 = 427254 :=
  contactRankWindow_of_rec contact19 60 4 427254 (by decide +kernel)
private theorem arithBundle10_ranks_064 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 64 4 = 319553 :=
  contactRankWindow_of_rec contact19 64 4 319553 (by decide +kernel)
private theorem arithBundle10_ranks_068 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 68 4 = 229719 :=
  contactRankWindow_of_rec contact19 68 4 229719 (by decide +kernel)
private theorem arithBundle10_ranks_072 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 72 4 = 156522 :=
  contactRankWindow_of_rec contact19 72 4 156522 (by decide +kernel)
private theorem arithBundle10_ranks_076 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 76 4 = 99049 :=
  contactRankWindow_of_rec contact19 76 4 99049 (by decide +kernel)
private theorem arithBundle10_ranks_080 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 80 4 = 55827 :=
  contactRankWindow_of_rec contact19 80 4 55827 (by decide +kernel)
private theorem arithBundle10_ranks_084 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 84 4 = 25630 :=
  contactRankWindow_of_rec contact19 84 4 25630 (by decide +kernel)
private theorem arithBundle10_ranks_088 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 88 4 = 7657 :=
  contactRankWindow_of_rec contact19 88 4 7657 (by decide +kernel)
private theorem arithBundle10_ranks_092 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 92 4 = 422 :=
  contactRankWindow_of_rec contact19 92 4 422 (by decide +kernel)
private theorem arithBundle10_ranks_096 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 96 8 = 0 :=
  contactRankWindow_of_rec contact19 96 8 0 (by decide +kernel)
private theorem arithBundle10_prefix_ranks_00 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 8 = 9343508 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 4 4 4916474 4427034 arithBundle10_ranks_000 arithBundle10_ranks_004
private theorem arithBundle10_prefix_ranks_01 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 12 = 13309070 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 8 4 9343508 3965562 arithBundle10_prefix_ranks_00 arithBundle10_ranks_008
private theorem arithBundle10_prefix_ranks_02 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 16 = 16841128 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 12 4 13309070 3532058 arithBundle10_prefix_ranks_01 arithBundle10_ranks_012
private theorem arithBundle10_prefix_ranks_03 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 20 = 19967650 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 16 4 16841128 3126522 arithBundle10_prefix_ranks_02 arithBundle10_ranks_016
private theorem arithBundle10_prefix_ranks_04 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 24 = 22716604 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 20 4 19967650 2748954 arithBundle10_prefix_ranks_03 arithBundle10_ranks_020
private theorem arithBundle10_prefix_ranks_05 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 28 = 25115958 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 24 4 22716604 2399354 arithBundle10_prefix_ranks_04 arithBundle10_ranks_024
private theorem arithBundle10_prefix_ranks_06 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 32 = 27193680 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 28 4 25115958 2077722 arithBundle10_prefix_ranks_05 arithBundle10_ranks_028
private theorem arithBundle10_prefix_ranks_07 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 36 = 28977604 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 32 4 27193680 1783924 arithBundle10_prefix_ranks_06 arithBundle10_ranks_032
private theorem arithBundle10_prefix_ranks_08 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 40 = 30494866 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 36 4 28977604 1517262 arithBundle10_prefix_ranks_07 arithBundle10_ranks_036
private theorem arithBundle10_prefix_ranks_09 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 44 = 31771715 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 40 4 30494866 1276849 arithBundle10_prefix_ranks_08 arithBundle10_ranks_040
private theorem arithBundle10_prefix_ranks_10 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 48 = 32833250 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 44 4 31771715 1061535 arithBundle10_prefix_ranks_09 arithBundle10_ranks_044
private theorem arithBundle10_prefix_ranks_11 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 52 = 33703332 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 48 4 32833250 870082 arithBundle10_prefix_ranks_10 arithBundle10_ranks_048
private theorem arithBundle10_prefix_ranks_12 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 56 = 34404733 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 52 4 33703332 701401 arithBundle10_prefix_ranks_11 arithBundle10_ranks_052
private theorem arithBundle10_prefix_ranks_13 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 60 = 34958936 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 56 4 34404733 554203 arithBundle10_prefix_ranks_12 arithBundle10_ranks_056
private theorem arithBundle10_prefix_ranks_14 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 64 = 35386190 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 60 4 34958936 427254 arithBundle10_prefix_ranks_13 arithBundle10_ranks_060
private theorem arithBundle10_prefix_ranks_15 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 68 = 35705743 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 64 4 35386190 319553 arithBundle10_prefix_ranks_14 arithBundle10_ranks_064
private theorem arithBundle10_prefix_ranks_16 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 72 = 35935462 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 68 4 35705743 229719 arithBundle10_prefix_ranks_15 arithBundle10_ranks_068
private theorem arithBundle10_prefix_ranks_17 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 76 = 36091984 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 72 4 35935462 156522 arithBundle10_prefix_ranks_16 arithBundle10_ranks_072
private theorem arithBundle10_prefix_ranks_18 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 80 = 36191033 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 76 4 36091984 99049 arithBundle10_prefix_ranks_17 arithBundle10_ranks_076
private theorem arithBundle10_prefix_ranks_19 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 84 = 36246860 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 80 4 36191033 55827 arithBundle10_prefix_ranks_18 arithBundle10_ranks_080
private theorem arithBundle10_prefix_ranks_20 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 88 = 36272490 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 84 4 36246860 25630 arithBundle10_prefix_ranks_19 arithBundle10_ranks_084
private theorem arithBundle10_prefix_ranks_21 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 92 = 36280147 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 88 4 36272490 7657 arithBundle10_prefix_ranks_20 arithBundle10_ranks_088
private theorem arithBundle10_prefix_ranks_22 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 96 = 36280569 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 92 4 36280147 422 arithBundle10_prefix_ranks_21 arithBundle10_ranks_092
private theorem arithBundle10_prefix_ranks_23 : arithBundle10_sliceWindow (auxiliaryRankSlice contact19) 0 104 = 36280569 :=
  arithBundle10_combineSlices (auxiliaryRankSlice contact19) 0 96 8 36280569 0 arithBundle10_prefix_ranks_22 arithBundle10_ranks_096

theorem contact19_margin : sourceMargin contact19 :=
  arithBundle10_margin_of_checked_counts contact19 104 156745256302232 11921203085745 607130443 36280569
    rfl arithBundle10_ordinary_columns arithBundle10_prefix_columns_24 arithBundle10_ordinary_ranks arithBundle10_prefix_ranks_23 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle11_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle11_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle11_sliceWindow f a b = x) (hy : arithBundle11_sliceWindow f (a+b) c = y) :
    arithBundle11_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle11_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle11_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle11_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle11_sliceWindow,Nat.zero_add]

private theorem arithBundle11_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle11_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle11_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle11_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle11_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle11_ordinary_columns : ordinaryColumnCount contact21 = 51103680090556 := by decide +kernel
private theorem arithBundle11_columns_000 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 4 = 510940728279 :=
  contactColumnsWindow_fast contact21 0 4 510940728279 (by decide +kernel)
private theorem arithBundle11_columns_004 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 4 4 = 463133563284 :=
  contactColumnsWindow_fast contact21 4 4 463133563284 (by decide +kernel)
private theorem arithBundle11_columns_008 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 8 4 = 417688601482 :=
  contactColumnsWindow_fast contact21 8 4 417688601482 (by decide +kernel)
private theorem arithBundle11_columns_012 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 12 4 = 374602880312 :=
  contactColumnsWindow_fast contact21 12 4 374602880312 (by decide +kernel)
private theorem arithBundle11_columns_016 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 16 4 = 333875088368 :=
  contactColumnsWindow_fast contact21 16 4 333875088368 (by decide +kernel)
private theorem arithBundle11_columns_020 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 20 4 = 295508209990 :=
  contactColumnsWindow_fast contact21 20 4 295508209990 (by decide +kernel)
private theorem arithBundle11_columns_024 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 24 4 = 259514168916 :=
  contactColumnsWindow_fast contact21 24 4 259514168916 (by decide +kernel)
private theorem arithBundle11_columns_028 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 28 4 = 225881167156 :=
  contactColumnsWindow_fast contact21 28 4 225881167156 (by decide +kernel)
private theorem arithBundle11_columns_032 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 32 4 = 194607406028 :=
  contactColumnsWindow_fast contact21 32 4 194607406028 (by decide +kernel)
private theorem arithBundle11_columns_036 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 36 4 = 165691610856 :=
  contactColumnsWindow_fast contact21 36 4 165691610856 (by decide +kernel)
private theorem arithBundle11_columns_040 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 40 4 = 139137614572 :=
  contactColumnsWindow_fast contact21 40 4 139137614572 (by decide +kernel)
private theorem arithBundle11_columns_044 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 44 4 = 114956333328 :=
  contactColumnsWindow_fast contact21 44 4 114956333328 (by decide +kernel)
private theorem arithBundle11_columns_048 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 48 4 = 93135291610 :=
  contactColumnsWindow_fast contact21 48 4 93135291610 (by decide +kernel)
private theorem arithBundle11_columns_052 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 52 4 = 73673490524 :=
  contactColumnsWindow_fast contact21 52 4 73673490524 (by decide +kernel)
private theorem arithBundle11_columns_056 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 56 4 = 56569739709 :=
  contactColumnsWindow_fast contact21 56 4 56569739709 (by decide +kernel)
private theorem arithBundle11_columns_060 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 60 4 = 41828577934 :=
  contactColumnsWindow_fast contact21 60 4 41828577934 (by decide +kernel)
private theorem arithBundle11_columns_064 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 64 4 = 29460056520 :=
  contactColumnsWindow_fast contact21 64 4 29460056520 (by decide +kernel)
private theorem arithBundle11_columns_068 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 68 4 = 19451038383 :=
  contactColumnsWindow_fast contact21 68 4 19451038383 (by decide +kernel)
private theorem arithBundle11_columns_072 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 72 4 = 11791961357 :=
  contactColumnsWindow_fast contact21 72 4 11791961357 (by decide +kernel)
private theorem arithBundle11_columns_076 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 76 4 = 6383463022 :=
  contactColumnsWindow_fast contact21 76 4 6383463022 (by decide +kernel)
private theorem arithBundle11_columns_080 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 80 4 = 2969870277 :=
  contactColumnsWindow_fast contact21 80 4 2969870277 (by decide +kernel)
private theorem arithBundle11_columns_084 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 84 1 = 405613201 :=
  contactColumnsWindow_fast contact21 84 1 405613201 (by decide +kernel)
private theorem arithBundle11_prefix_columns_00 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 8 = 974074291563 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 4 4 510940728279 463133563284 arithBundle11_columns_000 arithBundle11_columns_004
private theorem arithBundle11_prefix_columns_01 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 12 = 1391762893045 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 8 4 974074291563 417688601482 arithBundle11_prefix_columns_00 arithBundle11_columns_008
private theorem arithBundle11_prefix_columns_02 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 16 = 1766365773357 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 12 4 1391762893045 374602880312 arithBundle11_prefix_columns_01 arithBundle11_columns_012
private theorem arithBundle11_prefix_columns_03 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 20 = 2100240861725 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 16 4 1766365773357 333875088368 arithBundle11_prefix_columns_02 arithBundle11_columns_016
private theorem arithBundle11_prefix_columns_04 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 24 = 2395749071715 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 20 4 2100240861725 295508209990 arithBundle11_prefix_columns_03 arithBundle11_columns_020
private theorem arithBundle11_prefix_columns_05 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 28 = 2655263240631 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 24 4 2395749071715 259514168916 arithBundle11_prefix_columns_04 arithBundle11_columns_024
private theorem arithBundle11_prefix_columns_06 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 32 = 2881144407787 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 28 4 2655263240631 225881167156 arithBundle11_prefix_columns_05 arithBundle11_columns_028
private theorem arithBundle11_prefix_columns_07 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 36 = 3075751813815 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 32 4 2881144407787 194607406028 arithBundle11_prefix_columns_06 arithBundle11_columns_032
private theorem arithBundle11_prefix_columns_08 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 40 = 3241443424671 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 36 4 3075751813815 165691610856 arithBundle11_prefix_columns_07 arithBundle11_columns_036
private theorem arithBundle11_prefix_columns_09 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 44 = 3380581039243 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 40 4 3241443424671 139137614572 arithBundle11_prefix_columns_08 arithBundle11_columns_040
private theorem arithBundle11_prefix_columns_10 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 48 = 3495537372571 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 44 4 3380581039243 114956333328 arithBundle11_prefix_columns_09 arithBundle11_columns_044
private theorem arithBundle11_prefix_columns_11 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 52 = 3588672664181 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 48 4 3495537372571 93135291610 arithBundle11_prefix_columns_10 arithBundle11_columns_048
private theorem arithBundle11_prefix_columns_12 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 56 = 3662346154705 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 52 4 3588672664181 73673490524 arithBundle11_prefix_columns_11 arithBundle11_columns_052
private theorem arithBundle11_prefix_columns_13 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 60 = 3718915894414 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 56 4 3662346154705 56569739709 arithBundle11_prefix_columns_12 arithBundle11_columns_056
private theorem arithBundle11_prefix_columns_14 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 64 = 3760744472348 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 60 4 3718915894414 41828577934 arithBundle11_prefix_columns_13 arithBundle11_columns_060
private theorem arithBundle11_prefix_columns_15 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 68 = 3790204528868 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 64 4 3760744472348 29460056520 arithBundle11_prefix_columns_14 arithBundle11_columns_064
private theorem arithBundle11_prefix_columns_16 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 72 = 3809655567251 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 68 4 3790204528868 19451038383 arithBundle11_prefix_columns_15 arithBundle11_columns_068
private theorem arithBundle11_prefix_columns_17 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 76 = 3821447528608 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 72 4 3809655567251 11791961357 arithBundle11_prefix_columns_16 arithBundle11_columns_072
private theorem arithBundle11_prefix_columns_18 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 80 = 3827830991630 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 76 4 3821447528608 6383463022 arithBundle11_prefix_columns_17 arithBundle11_columns_076
private theorem arithBundle11_prefix_columns_19 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 84 = 3830800861907 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 80 4 3827830991630 2969870277 arithBundle11_prefix_columns_18 arithBundle11_columns_080
private theorem arithBundle11_prefix_columns_20 : arithBundle11_sliceWindow (auxiliaryColumnSlice contact21) 0 85 = 3831206475108 :=
  arithBundle11_combineSlices (auxiliaryColumnSlice contact21) 0 84 1 3830800861907 405613201 arithBundle11_prefix_columns_19 arithBundle11_columns_084

private theorem arithBundle11_ordinary_ranks : ordinaryRankBound contact21 = 198019334 := by decide +kernel
private theorem arithBundle11_ranks_000 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 4 = 1905896 :=
  contactRankWindow_of_rec contact21 0 4 1905896 (by decide +kernel)
private theorem arithBundle11_ranks_004 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 4 4 = 1673336 :=
  contactRankWindow_of_rec contact21 4 4 1673336 (by decide +kernel)
private theorem arithBundle11_ranks_008 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 8 4 = 1457096 :=
  contactRankWindow_of_rec contact21 8 4 1457096 (by decide +kernel)
private theorem arithBundle11_ranks_012 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 12 4 = 1257176 :=
  contactRankWindow_of_rec contact21 12 4 1257176 (by decide +kernel)
private theorem arithBundle11_ranks_016 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 16 4 = 1073576 :=
  contactRankWindow_of_rec contact21 16 4 1073576 (by decide +kernel)
private theorem arithBundle11_ranks_020 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 20 4 = 906296 :=
  contactRankWindow_of_rec contact21 20 4 906296 (by decide +kernel)
private theorem arithBundle11_ranks_024 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 24 4 = 755336 :=
  contactRankWindow_of_rec contact21 24 4 755336 (by decide +kernel)
private theorem arithBundle11_ranks_028 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 28 4 = 620681 :=
  contactRankWindow_of_rec contact21 28 4 620681 (by decide +kernel)
private theorem arithBundle11_ranks_032 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 32 4 = 502011 :=
  contactRankWindow_of_rec contact21 32 4 502011 (by decide +kernel)
private theorem arithBundle11_ranks_036 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 36 4 = 398536 :=
  contactRankWindow_of_rec contact21 36 4 398536 (by decide +kernel)
private theorem arithBundle11_ranks_040 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 40 4 = 309381 :=
  contactRankWindow_of_rec contact21 40 4 309381 (by decide +kernel)
private theorem arithBundle11_ranks_044 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 44 4 = 233611 :=
  contactRankWindow_of_rec contact21 44 4 233611 (by decide +kernel)
private theorem arithBundle11_ranks_048 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 48 4 = 170284 :=
  contactRankWindow_of_rec contact21 48 4 170284 (by decide +kernel)
private theorem arithBundle11_ranks_052 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 52 4 = 118593 :=
  contactRankWindow_of_rec contact21 52 4 118593 (by decide +kernel)
private theorem arithBundle11_ranks_056 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 56 4 = 77531 :=
  contactRankWindow_of_rec contact21 56 4 77531 (by decide +kernel)
private theorem arithBundle11_ranks_060 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 60 4 = 46160 :=
  contactRankWindow_of_rec contact21 60 4 46160 (by decide +kernel)
private theorem arithBundle11_ranks_064 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 64 4 = 23741 :=
  contactRankWindow_of_rec contact21 64 4 23741 (by decide +kernel)
private theorem arithBundle11_ranks_068 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 68 4 = 9195 :=
  contactRankWindow_of_rec contact21 68 4 9195 (by decide +kernel)
private theorem arithBundle11_ranks_072 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 72 4 = 1589 :=
  contactRankWindow_of_rec contact21 72 4 1589 (by decide +kernel)
private theorem arithBundle11_ranks_076 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 76 9 = 0 :=
  contactRankWindow_of_rec contact21 76 9 0 (by decide +kernel)
private theorem arithBundle11_prefix_ranks_00 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 8 = 3579232 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 4 4 1905896 1673336 arithBundle11_ranks_000 arithBundle11_ranks_004
private theorem arithBundle11_prefix_ranks_01 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 12 = 5036328 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 8 4 3579232 1457096 arithBundle11_prefix_ranks_00 arithBundle11_ranks_008
private theorem arithBundle11_prefix_ranks_02 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 16 = 6293504 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 12 4 5036328 1257176 arithBundle11_prefix_ranks_01 arithBundle11_ranks_012
private theorem arithBundle11_prefix_ranks_03 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 20 = 7367080 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 16 4 6293504 1073576 arithBundle11_prefix_ranks_02 arithBundle11_ranks_016
private theorem arithBundle11_prefix_ranks_04 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 24 = 8273376 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 20 4 7367080 906296 arithBundle11_prefix_ranks_03 arithBundle11_ranks_020
private theorem arithBundle11_prefix_ranks_05 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 28 = 9028712 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 24 4 8273376 755336 arithBundle11_prefix_ranks_04 arithBundle11_ranks_024
private theorem arithBundle11_prefix_ranks_06 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 32 = 9649393 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 28 4 9028712 620681 arithBundle11_prefix_ranks_05 arithBundle11_ranks_028
private theorem arithBundle11_prefix_ranks_07 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 36 = 10151404 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 32 4 9649393 502011 arithBundle11_prefix_ranks_06 arithBundle11_ranks_032
private theorem arithBundle11_prefix_ranks_08 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 40 = 10549940 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 36 4 10151404 398536 arithBundle11_prefix_ranks_07 arithBundle11_ranks_036
private theorem arithBundle11_prefix_ranks_09 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 44 = 10859321 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 40 4 10549940 309381 arithBundle11_prefix_ranks_08 arithBundle11_ranks_040
private theorem arithBundle11_prefix_ranks_10 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 48 = 11092932 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 44 4 10859321 233611 arithBundle11_prefix_ranks_09 arithBundle11_ranks_044
private theorem arithBundle11_prefix_ranks_11 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 52 = 11263216 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 48 4 11092932 170284 arithBundle11_prefix_ranks_10 arithBundle11_ranks_048
private theorem arithBundle11_prefix_ranks_12 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 56 = 11381809 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 52 4 11263216 118593 arithBundle11_prefix_ranks_11 arithBundle11_ranks_052
private theorem arithBundle11_prefix_ranks_13 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 60 = 11459340 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 56 4 11381809 77531 arithBundle11_prefix_ranks_12 arithBundle11_ranks_056
private theorem arithBundle11_prefix_ranks_14 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 64 = 11505500 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 60 4 11459340 46160 arithBundle11_prefix_ranks_13 arithBundle11_ranks_060
private theorem arithBundle11_prefix_ranks_15 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 68 = 11529241 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 64 4 11505500 23741 arithBundle11_prefix_ranks_14 arithBundle11_ranks_064
private theorem arithBundle11_prefix_ranks_16 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 72 = 11538436 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 68 4 11529241 9195 arithBundle11_prefix_ranks_15 arithBundle11_ranks_068
private theorem arithBundle11_prefix_ranks_17 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 76 = 11540025 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 72 4 11538436 1589 arithBundle11_prefix_ranks_16 arithBundle11_ranks_072
private theorem arithBundle11_prefix_ranks_18 : arithBundle11_sliceWindow (auxiliaryRankSlice contact21) 0 85 = 11540025 :=
  arithBundle11_combineSlices (auxiliaryRankSlice contact21) 0 76 9 11540025 0 arithBundle11_prefix_ranks_17 arithBundle11_ranks_076

theorem contact21_margin : sourceMargin contact21 :=
  arithBundle11_margin_of_checked_counts contact21 85 51103680090556 3831206475108 198019334 11540025
    rfl arithBundle11_ordinary_columns arithBundle11_prefix_columns_20 arithBundle11_ordinary_ranks arithBundle11_prefix_ranks_18 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle12_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle12_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle12_sliceWindow f a b = x) (hy : arithBundle12_sliceWindow f (a+b) c = y) :
    arithBundle12_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle12_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle12_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle12_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle12_sliceWindow,Nat.zero_add]

private theorem arithBundle12_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle12_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle12_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle12_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle12_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle12_ordinary_columns : ordinaryColumnCount contact24 = 163064285528947 := by decide +kernel
private theorem arithBundle12_columns_000 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 4 = 1369807931712 :=
  contactColumnsWindow_fast contact24 0 4 1369807931712 (by decide +kernel)
private theorem arithBundle12_columns_004 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 4 4 = 1264265729984 :=
  contactColumnsWindow_fast contact24 4 4 1264265729984 (by decide +kernel)
private theorem arithBundle12_columns_008 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 8 4 = 1162975223616 :=
  contactColumnsWindow_fast contact24 8 4 1162975223616 (by decide +kernel)
private theorem arithBundle12_columns_012 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 12 4 = 1065954329112 :=
  contactColumnsWindow_fast contact24 12 4 1065954329112 (by decide +kernel)
private theorem arithBundle12_columns_016 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 16 4 = 973203520129 :=
  contactColumnsWindow_fast contact24 16 4 973203520129 (by decide +kernel)
private theorem arithBundle12_columns_020 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 20 4 = 884706941732 :=
  contactColumnsWindow_fast contact24 20 4 884706941732 (by decide +kernel)
private theorem arithBundle12_columns_024 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 24 4 = 800463721016 :=
  contactColumnsWindow_fast contact24 24 4 800463721016 (by decide +kernel)
private theorem arithBundle12_columns_028 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 28 4 = 720475144980 :=
  contactColumnsWindow_fast contact24 28 4 720475144980 (by decide +kernel)
private theorem arithBundle12_columns_032 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 32 4 = 644760946710 :=
  contactColumnsWindow_fast contact24 32 4 644760946710 (by decide +kernel)
private theorem arithBundle12_columns_036 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 36 4 = 573317012683 :=
  contactColumnsWindow_fast contact24 36 4 573317012683 (by decide +kernel)
private theorem arithBundle12_columns_040 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 40 4 = 506128306628 :=
  contactColumnsWindow_fast contact24 40 4 506128306628 (by decide +kernel)
private theorem arithBundle12_columns_044 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 44 4 = 443192779712 :=
  contactColumnsWindow_fast contact24 44 4 443192779712 (by decide +kernel)
private theorem arithBundle12_columns_048 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 48 4 = 384512534542 :=
  contactColumnsWindow_fast contact24 48 4 384512534542 (by decide +kernel)
private theorem arithBundle12_columns_052 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 52 4 = 330108967962 :=
  contactColumnsWindow_fast contact24 52 4 330108967962 (by decide +kernel)
private theorem arithBundle12_columns_056 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 56 4 = 279972925273 :=
  contactColumnsWindow_fast contact24 56 4 279972925273 (by decide +kernel)
private theorem arithBundle12_columns_060 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 60 4 = 234092091284 :=
  contactColumnsWindow_fast contact24 60 4 234092091284 (by decide +kernel)
private theorem arithBundle12_columns_064 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 64 4 = 192464323788 :=
  contactColumnsWindow_fast contact24 64 4 192464323788 (by decide +kernel)
private theorem arithBundle12_columns_068 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 68 4 = 155092718578 :=
  contactColumnsWindow_fast contact24 68 4 155092718578 (by decide +kernel)
private theorem arithBundle12_columns_072 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 72 4 = 121999408974 :=
  contactColumnsWindow_fast contact24 72 4 121999408974 (by decide +kernel)
private theorem arithBundle12_columns_076 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 76 4 = 93171278466 :=
  contactColumnsWindow_fast contact24 76 4 93171278466 (by decide +kernel)
private theorem arithBundle12_columns_080 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 80 4 = 68598295700 :=
  contactColumnsWindow_fast contact24 80 4 68598295700 (by decide +kernel)
private theorem arithBundle12_columns_084 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 84 4 = 48275568600 :=
  contactColumnsWindow_fast contact24 84 4 48275568600 (by decide +kernel)
private theorem arithBundle12_columns_088 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 88 4 = 32143325174 :=
  contactColumnsWindow_fast contact24 88 4 32143325174 (by decide +kernel)
private theorem arithBundle12_columns_092 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 92 4 = 19998553408 :=
  contactColumnsWindow_fast contact24 92 4 19998553408 (by decide +kernel)
private theorem arithBundle12_columns_096 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 96 4 = 11430696088 :=
  contactColumnsWindow_fast contact24 96 4 11430696088 (by decide +kernel)
private theorem arithBundle12_columns_100 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 100 2 = 3470727767 :=
  contactColumnsWindow_fast contact24 100 2 3470727767 (by decide +kernel)
private theorem arithBundle12_prefix_columns_00 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 8 = 2634073661696 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 4 4 1369807931712 1264265729984 arithBundle12_columns_000 arithBundle12_columns_004
private theorem arithBundle12_prefix_columns_01 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 12 = 3797048885312 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 8 4 2634073661696 1162975223616 arithBundle12_prefix_columns_00 arithBundle12_columns_008
private theorem arithBundle12_prefix_columns_02 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 16 = 4863003214424 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 12 4 3797048885312 1065954329112 arithBundle12_prefix_columns_01 arithBundle12_columns_012
private theorem arithBundle12_prefix_columns_03 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 20 = 5836206734553 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 16 4 4863003214424 973203520129 arithBundle12_prefix_columns_02 arithBundle12_columns_016
private theorem arithBundle12_prefix_columns_04 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 24 = 6720913676285 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 20 4 5836206734553 884706941732 arithBundle12_prefix_columns_03 arithBundle12_columns_020
private theorem arithBundle12_prefix_columns_05 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 28 = 7521377397301 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 24 4 6720913676285 800463721016 arithBundle12_prefix_columns_04 arithBundle12_columns_024
private theorem arithBundle12_prefix_columns_06 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 32 = 8241852542281 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 28 4 7521377397301 720475144980 arithBundle12_prefix_columns_05 arithBundle12_columns_028
private theorem arithBundle12_prefix_columns_07 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 36 = 8886613488991 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 32 4 8241852542281 644760946710 arithBundle12_prefix_columns_06 arithBundle12_columns_032
private theorem arithBundle12_prefix_columns_08 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 40 = 9459930501674 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 36 4 8886613488991 573317012683 arithBundle12_prefix_columns_07 arithBundle12_columns_036
private theorem arithBundle12_prefix_columns_09 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 44 = 9966058808302 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 40 4 9459930501674 506128306628 arithBundle12_prefix_columns_08 arithBundle12_columns_040
private theorem arithBundle12_prefix_columns_10 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 48 = 10409251588014 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 44 4 9966058808302 443192779712 arithBundle12_prefix_columns_09 arithBundle12_columns_044
private theorem arithBundle12_prefix_columns_11 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 52 = 10793764122556 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 48 4 10409251588014 384512534542 arithBundle12_prefix_columns_10 arithBundle12_columns_048
private theorem arithBundle12_prefix_columns_12 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 56 = 11123873090518 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 52 4 10793764122556 330108967962 arithBundle12_prefix_columns_11 arithBundle12_columns_052
private theorem arithBundle12_prefix_columns_13 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 60 = 11403846015791 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 56 4 11123873090518 279972925273 arithBundle12_prefix_columns_12 arithBundle12_columns_056
private theorem arithBundle12_prefix_columns_14 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 64 = 11637938107075 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 60 4 11403846015791 234092091284 arithBundle12_prefix_columns_13 arithBundle12_columns_060
private theorem arithBundle12_prefix_columns_15 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 68 = 11830402430863 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 64 4 11637938107075 192464323788 arithBundle12_prefix_columns_14 arithBundle12_columns_064
private theorem arithBundle12_prefix_columns_16 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 72 = 11985495149441 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 68 4 11830402430863 155092718578 arithBundle12_prefix_columns_15 arithBundle12_columns_068
private theorem arithBundle12_prefix_columns_17 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 76 = 12107494558415 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 72 4 11985495149441 121999408974 arithBundle12_prefix_columns_16 arithBundle12_columns_072
private theorem arithBundle12_prefix_columns_18 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 80 = 12200665836881 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 76 4 12107494558415 93171278466 arithBundle12_prefix_columns_17 arithBundle12_columns_076
private theorem arithBundle12_prefix_columns_19 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 84 = 12269264132581 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 80 4 12200665836881 68598295700 arithBundle12_prefix_columns_18 arithBundle12_columns_080
private theorem arithBundle12_prefix_columns_20 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 88 = 12317539701181 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 84 4 12269264132581 48275568600 arithBundle12_prefix_columns_19 arithBundle12_columns_084
private theorem arithBundle12_prefix_columns_21 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 92 = 12349683026355 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 88 4 12317539701181 32143325174 arithBundle12_prefix_columns_20 arithBundle12_columns_088
private theorem arithBundle12_prefix_columns_22 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 96 = 12369681579763 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 92 4 12349683026355 19998553408 arithBundle12_prefix_columns_21 arithBundle12_columns_092
private theorem arithBundle12_prefix_columns_23 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 100 = 12381112275851 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 96 4 12369681579763 11430696088 arithBundle12_prefix_columns_22 arithBundle12_columns_096
private theorem arithBundle12_prefix_columns_24 : arithBundle12_sliceWindow (auxiliaryColumnSlice contact24) 0 102 = 12384583003618 :=
  arithBundle12_combineSlices (auxiliaryColumnSlice contact24) 0 100 2 12381112275851 3470727767 arithBundle12_prefix_columns_23 arithBundle12_columns_100

private theorem arithBundle12_ordinary_ranks : ordinaryRankBound contact24 = 631439345 := by decide +kernel
private theorem arithBundle12_ranks_000 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 4 = 5128436 :=
  contactRankWindow_of_rec contact24 0 4 5128436 (by decide +kernel)
private theorem arithBundle12_ranks_004 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 4 4 = 4616916 :=
  contactRankWindow_of_rec contact24 4 4 4616916 (by decide +kernel)
private theorem arithBundle12_ranks_008 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 8 4 = 4134836 :=
  contactRankWindow_of_rec contact24 8 4 4134836 (by decide +kernel)
private theorem arithBundle12_ranks_012 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 12 4 = 3682196 :=
  contactRankWindow_of_rec contact24 12 4 3682196 (by decide +kernel)
private theorem arithBundle12_ranks_016 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 16 4 = 3258996 :=
  contactRankWindow_of_rec contact24 16 4 3258996 (by decide +kernel)
private theorem arithBundle12_ranks_020 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 20 4 = 2865236 :=
  contactRankWindow_of_rec contact24 20 4 2865236 (by decide +kernel)
private theorem arithBundle12_ranks_024 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 24 4 = 2500916 :=
  contactRankWindow_of_rec contact24 24 4 2500916 (by decide +kernel)
private theorem arithBundle12_ranks_028 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 28 4 = 2166036 :=
  contactRankWindow_of_rec contact24 28 4 2166036 (by decide +kernel)
private theorem arithBundle12_ranks_032 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 32 4 = 1860314 :=
  contactRankWindow_of_rec contact24 32 4 1860314 (by decide +kernel)
private theorem arithBundle12_ranks_036 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 36 4 = 1582925 :=
  contactRankWindow_of_rec contact24 36 4 1582925 (by decide +kernel)
private theorem arithBundle12_ranks_040 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 40 4 = 1332762 :=
  contactRankWindow_of_rec contact24 40 4 1332762 (by decide +kernel)
private theorem arithBundle12_ranks_044 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 44 4 = 1108578 :=
  contactRankWindow_of_rec contact24 44 4 1108578 (by decide +kernel)
private theorem arithBundle12_ranks_048 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 48 4 = 909121 :=
  contactRankWindow_of_rec contact24 48 4 909121 (by decide +kernel)
private theorem arithBundle12_ranks_052 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 52 4 = 733282 :=
  contactRankWindow_of_rec contact24 52 4 733282 (by decide +kernel)
private theorem arithBundle12_ranks_056 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 56 4 = 579722 :=
  contactRankWindow_of_rec contact24 56 4 579722 (by decide +kernel)
private theorem arithBundle12_ranks_060 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 60 4 = 447189 :=
  contactRankWindow_of_rec contact24 60 4 447189 (by decide +kernel)
private theorem arithBundle12_ranks_064 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 64 4 = 334666 :=
  contactRankWindow_of_rec contact24 64 4 334666 (by decide +kernel)
private theorem arithBundle12_ranks_068 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 68 4 = 240722 :=
  contactRankWindow_of_rec contact24 68 4 240722 (by decide +kernel)
private theorem arithBundle12_ranks_072 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 72 4 = 164105 :=
  contactRankWindow_of_rec contact24 72 4 164105 (by decide +kernel)
private theorem arithBundle12_ranks_076 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 76 4 = 103890 :=
  contactRankWindow_of_rec contact24 76 4 103890 (by decide +kernel)
private theorem arithBundle12_ranks_080 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 80 4 = 58554 :=
  contactRankWindow_of_rec contact24 80 4 58554 (by decide +kernel)
private theorem arithBundle12_ranks_084 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 84 4 = 26845 :=
  contactRankWindow_of_rec contact24 84 4 26845 (by decide +kernel)
private theorem arithBundle12_ranks_088 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 88 4 = 7990 :=
  contactRankWindow_of_rec contact24 88 4 7990 (by decide +kernel)
private theorem arithBundle12_ranks_092 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 92 4 = 439 :=
  contactRankWindow_of_rec contact24 92 4 439 (by decide +kernel)
private theorem arithBundle12_ranks_096 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 96 6 = 0 :=
  contactRankWindow_of_rec contact24 96 6 0 (by decide +kernel)
private theorem arithBundle12_prefix_ranks_00 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 8 = 9745352 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 4 4 5128436 4616916 arithBundle12_ranks_000 arithBundle12_ranks_004
private theorem arithBundle12_prefix_ranks_01 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 12 = 13880188 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 8 4 9745352 4134836 arithBundle12_prefix_ranks_00 arithBundle12_ranks_008
private theorem arithBundle12_prefix_ranks_02 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 16 = 17562384 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 12 4 13880188 3682196 arithBundle12_prefix_ranks_01 arithBundle12_ranks_012
private theorem arithBundle12_prefix_ranks_03 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 20 = 20821380 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 16 4 17562384 3258996 arithBundle12_prefix_ranks_02 arithBundle12_ranks_016
private theorem arithBundle12_prefix_ranks_04 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 24 = 23686616 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 20 4 20821380 2865236 arithBundle12_prefix_ranks_03 arithBundle12_ranks_020
private theorem arithBundle12_prefix_ranks_05 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 28 = 26187532 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 24 4 23686616 2500916 arithBundle12_prefix_ranks_04 arithBundle12_ranks_024
private theorem arithBundle12_prefix_ranks_06 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 32 = 28353568 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 28 4 26187532 2166036 arithBundle12_prefix_ranks_05 arithBundle12_ranks_028
private theorem arithBundle12_prefix_ranks_07 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 36 = 30213882 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 32 4 28353568 1860314 arithBundle12_prefix_ranks_06 arithBundle12_ranks_032
private theorem arithBundle12_prefix_ranks_08 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 40 = 31796807 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 36 4 30213882 1582925 arithBundle12_prefix_ranks_07 arithBundle12_ranks_036
private theorem arithBundle12_prefix_ranks_09 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 44 = 33129569 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 40 4 31796807 1332762 arithBundle12_prefix_ranks_08 arithBundle12_ranks_040
private theorem arithBundle12_prefix_ranks_10 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 48 = 34238147 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 44 4 33129569 1108578 arithBundle12_prefix_ranks_09 arithBundle12_ranks_044
private theorem arithBundle12_prefix_ranks_11 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 52 = 35147268 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 48 4 34238147 909121 arithBundle12_prefix_ranks_10 arithBundle12_ranks_048
private theorem arithBundle12_prefix_ranks_12 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 56 = 35880550 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 52 4 35147268 733282 arithBundle12_prefix_ranks_11 arithBundle12_ranks_052
private theorem arithBundle12_prefix_ranks_13 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 60 = 36460272 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 56 4 35880550 579722 arithBundle12_prefix_ranks_12 arithBundle12_ranks_056
private theorem arithBundle12_prefix_ranks_14 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 64 = 36907461 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 60 4 36460272 447189 arithBundle12_prefix_ranks_13 arithBundle12_ranks_060
private theorem arithBundle12_prefix_ranks_15 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 68 = 37242127 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 64 4 36907461 334666 arithBundle12_prefix_ranks_14 arithBundle12_ranks_064
private theorem arithBundle12_prefix_ranks_16 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 72 = 37482849 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 68 4 37242127 240722 arithBundle12_prefix_ranks_15 arithBundle12_ranks_068
private theorem arithBundle12_prefix_ranks_17 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 76 = 37646954 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 72 4 37482849 164105 arithBundle12_prefix_ranks_16 arithBundle12_ranks_072
private theorem arithBundle12_prefix_ranks_18 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 80 = 37750844 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 76 4 37646954 103890 arithBundle12_prefix_ranks_17 arithBundle12_ranks_076
private theorem arithBundle12_prefix_ranks_19 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 84 = 37809398 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 80 4 37750844 58554 arithBundle12_prefix_ranks_18 arithBundle12_ranks_080
private theorem arithBundle12_prefix_ranks_20 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 88 = 37836243 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 84 4 37809398 26845 arithBundle12_prefix_ranks_19 arithBundle12_ranks_084
private theorem arithBundle12_prefix_ranks_21 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 92 = 37844233 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 88 4 37836243 7990 arithBundle12_prefix_ranks_20 arithBundle12_ranks_088
private theorem arithBundle12_prefix_ranks_22 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 96 = 37844672 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 92 4 37844233 439 arithBundle12_prefix_ranks_21 arithBundle12_ranks_092
private theorem arithBundle12_prefix_ranks_23 : arithBundle12_sliceWindow (auxiliaryRankSlice contact24) 0 102 = 37844672 :=
  arithBundle12_combineSlices (auxiliaryRankSlice contact24) 0 96 6 37844672 0 arithBundle12_prefix_ranks_22 arithBundle12_ranks_096

theorem contact24_margin : sourceMargin contact24 :=
  arithBundle12_margin_of_checked_counts contact24 102 163064285528947 12384583003618 631439345 37844672
    rfl arithBundle12_ordinary_columns arithBundle12_prefix_columns_24 arithBundle12_ordinary_ranks arithBundle12_prefix_ranks_23 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle13_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle13_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle13_sliceWindow f a b = x) (hy : arithBundle13_sliceWindow f (a+b) c = y) :
    arithBundle13_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle13_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle13_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle13_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle13_sliceWindow,Nat.zero_add]

private theorem arithBundle13_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle13_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle13_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle13_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle13_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle13_ordinary_columns : ordinaryColumnCount contact25 = 2241732209085489 := by decide +kernel
private theorem arithBundle13_columns_000 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 4 = 7596798762600 :=
  contactColumnsWindow_fast contact25 0 4 7596798762600 (by decide +kernel)
private theorem arithBundle13_columns_004 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 4 4 = 7219627279912 :=
  contactColumnsWindow_fast contact25 4 4 7219627279912 (by decide +kernel)
private theorem arithBundle13_columns_008 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 8 4 = 6852106026680 :=
  contactColumnsWindow_fast contact25 8 4 6852106026680 (by decide +kernel)
private theorem arithBundle13_columns_012 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 12 4 = 6494238117576 :=
  contactColumnsWindow_fast contact25 12 4 6494238117576 (by decide +kernel)
private theorem arithBundle13_columns_016 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 16 4 = 6146021424757 :=
  contactColumnsWindow_fast contact25 16 4 6146021424757 (by decide +kernel)
private theorem arithBundle13_columns_020 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 20 4 = 5807458127292 :=
  contactColumnsWindow_fast contact25 20 4 5807458127292 (by decide +kernel)
private theorem arithBundle13_columns_024 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 24 4 = 5478564598448 :=
  contactColumnsWindow_fast contact25 24 4 5478564598448 (by decide +kernel)
private theorem arithBundle13_columns_028 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 28 4 = 5159363518339 :=
  contactColumnsWindow_fast contact25 28 4 5159363518339 (by decide +kernel)
private theorem arithBundle13_columns_032 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 32 4 = 4849819489304 :=
  contactColumnsWindow_fast contact25 32 4 4849819489304 (by decide +kernel)
private theorem arithBundle13_columns_036 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 36 4 = 4549930104651 :=
  contactColumnsWindow_fast contact25 36 4 4549930104651 (by decide +kernel)
private theorem arithBundle13_columns_040 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 40 4 = 4259697218660 :=
  contactColumnsWindow_fast contact25 40 4 4259697218660 (by decide +kernel)
private theorem arithBundle13_columns_044 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 44 4 = 3979141183435 :=
  contactColumnsWindow_fast contact25 44 4 3979141183435 (by decide +kernel)
private theorem arithBundle13_columns_048 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 48 4 = 3708278790080 :=
  contactColumnsWindow_fast contact25 48 4 3708278790080 (by decide +kernel)
private theorem arithBundle13_columns_052 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 52 4 = 3447074832354 :=
  contactColumnsWindow_fast contact25 52 4 3447074832354 (by decide +kernel)
private theorem arithBundle13_columns_056 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 56 4 = 3195529914609 :=
  contactColumnsWindow_fast contact25 56 4 3195529914609 (by decide +kernel)
private theorem arithBundle13_columns_060 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 60 4 = 2953643850222 :=
  contactColumnsWindow_fast contact25 60 4 2953643850222 (by decide +kernel)
private theorem arithBundle13_columns_064 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 64 4 = 2721444822821 :=
  contactColumnsWindow_fast contact25 64 4 2721444822821 (by decide +kernel)
private theorem arithBundle13_columns_068 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 68 4 = 2498936484040 :=
  contactColumnsWindow_fast contact25 68 4 2498936484040 (by decide +kernel)
private theorem arithBundle13_columns_072 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 72 4 = 2286091779864 :=
  contactColumnsWindow_fast contact25 72 4 2286091779864 (by decide +kernel)
private theorem arithBundle13_columns_076 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 76 4 = 2082906797244 :=
  contactColumnsWindow_fast contact25 76 4 2082906797244 (by decide +kernel)
private theorem arithBundle13_columns_080 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 80 4 = 1889380456626 :=
  contactColumnsWindow_fast contact25 80 4 1889380456626 (by decide +kernel)
private theorem arithBundle13_columns_084 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 84 4 = 1705546554191 :=
  contactColumnsWindow_fast contact25 84 4 1705546554191 (by decide +kernel)
private theorem arithBundle13_columns_088 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 88 4 = 1531398488479 :=
  contactColumnsWindow_fast contact25 88 4 1531398488479 (by decide +kernel)
private theorem arithBundle13_columns_092 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 92 4 = 1366913783088 :=
  contactColumnsWindow_fast contact25 92 4 1366913783088 (by decide +kernel)
private theorem arithBundle13_columns_096 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 96 4 = 1212088688268 :=
  contactColumnsWindow_fast contact25 96 4 1212088688268 (by decide +kernel)
private theorem arithBundle13_columns_100 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 100 4 = 1066922561231 :=
  contactColumnsWindow_fast contact25 100 4 1066922561231 (by decide +kernel)
private theorem arithBundle13_columns_104 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 104 4 = 931453388938 :=
  contactColumnsWindow_fast contact25 104 4 931453388938 (by decide +kernel)
private theorem arithBundle13_columns_108 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 108 4 = 805665646237 :=
  contactColumnsWindow_fast contact25 108 4 805665646237 (by decide +kernel)
private theorem arithBundle13_columns_112 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 112 4 = 689540756376 :=
  contactColumnsWindow_fast contact25 112 4 689540756376 (by decide +kernel)
private theorem arithBundle13_columns_116 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 116 4 = 583075616920 :=
  contactColumnsWindow_fast contact25 116 4 583075616920 (by decide +kernel)
private theorem arithBundle13_columns_120 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 120 4 = 486270683249 :=
  contactColumnsWindow_fast contact25 120 4 486270683249 (by decide +kernel)
private theorem arithBundle13_columns_124 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 124 4 = 399165200158 :=
  contactColumnsWindow_fast contact25 124 4 399165200158 (by decide +kernel)
private theorem arithBundle13_columns_128 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 128 4 = 321737780242 :=
  contactColumnsWindow_fast contact25 128 4 321737780242 (by decide +kernel)
private theorem arithBundle13_columns_132 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 132 4 = 253967228500 :=
  contactColumnsWindow_fast contact25 132 4 253967228500 (by decide +kernel)
private theorem arithBundle13_columns_136 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 136 4 = 195755546761 :=
  contactColumnsWindow_fast contact25 136 4 195755546761 (by decide +kernel)
private theorem arithBundle13_columns_140 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 140 4 = 146810872521 :=
  contactColumnsWindow_fast contact25 140 4 146810872521 (by decide +kernel)
private theorem arithBundle13_columns_144 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 144 4 = 106708798706 :=
  contactColumnsWindow_fast contact25 144 4 106708798706 (by decide +kernel)
private theorem arithBundle13_columns_148 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 148 4 = 74794798937 :=
  contactColumnsWindow_fast contact25 148 4 74794798937 (by decide +kernel)
private theorem arithBundle13_columns_152 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 152 4 = 50268298928 :=
  contactColumnsWindow_fast contact25 152 4 50268298928 (by decide +kernel)
private theorem arithBundle13_columns_156 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 156 4 = 32179057735 :=
  contactColumnsWindow_fast contact25 156 4 32179057735 (by decide +kernel)
private theorem arithBundle13_columns_160 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 160 4 = 19448391567 :=
  contactColumnsWindow_fast contact25 160 4 19448391567 (by decide +kernel)
private theorem arithBundle13_columns_164 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 164 1 = 3395746304 :=
  contactColumnsWindow_fast contact25 164 1 3395746304 (by decide +kernel)
private theorem arithBundle13_prefix_columns_00 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 8 = 14816426042512 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 4 4 7596798762600 7219627279912 arithBundle13_columns_000 arithBundle13_columns_004
private theorem arithBundle13_prefix_columns_01 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 12 = 21668532069192 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 8 4 14816426042512 6852106026680 arithBundle13_prefix_columns_00 arithBundle13_columns_008
private theorem arithBundle13_prefix_columns_02 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 16 = 28162770186768 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 12 4 21668532069192 6494238117576 arithBundle13_prefix_columns_01 arithBundle13_columns_012
private theorem arithBundle13_prefix_columns_03 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 20 = 34308791611525 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 16 4 28162770186768 6146021424757 arithBundle13_prefix_columns_02 arithBundle13_columns_016
private theorem arithBundle13_prefix_columns_04 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 24 = 40116249738817 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 20 4 34308791611525 5807458127292 arithBundle13_prefix_columns_03 arithBundle13_columns_020
private theorem arithBundle13_prefix_columns_05 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 28 = 45594814337265 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 24 4 40116249738817 5478564598448 arithBundle13_prefix_columns_04 arithBundle13_columns_024
private theorem arithBundle13_prefix_columns_06 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 32 = 50754177855604 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 28 4 45594814337265 5159363518339 arithBundle13_prefix_columns_05 arithBundle13_columns_028
private theorem arithBundle13_prefix_columns_07 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 36 = 55603997344908 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 32 4 50754177855604 4849819489304 arithBundle13_prefix_columns_06 arithBundle13_columns_032
private theorem arithBundle13_prefix_columns_08 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 40 = 60153927449559 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 36 4 55603997344908 4549930104651 arithBundle13_prefix_columns_07 arithBundle13_columns_036
private theorem arithBundle13_prefix_columns_09 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 44 = 64413624668219 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 40 4 60153927449559 4259697218660 arithBundle13_prefix_columns_08 arithBundle13_columns_040
private theorem arithBundle13_prefix_columns_10 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 48 = 68392765851654 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 44 4 64413624668219 3979141183435 arithBundle13_prefix_columns_09 arithBundle13_columns_044
private theorem arithBundle13_prefix_columns_11 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 52 = 72101044641734 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 48 4 68392765851654 3708278790080 arithBundle13_prefix_columns_10 arithBundle13_columns_048
private theorem arithBundle13_prefix_columns_12 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 56 = 75548119474088 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 52 4 72101044641734 3447074832354 arithBundle13_prefix_columns_11 arithBundle13_columns_052
private theorem arithBundle13_prefix_columns_13 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 60 = 78743649388697 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 56 4 75548119474088 3195529914609 arithBundle13_prefix_columns_12 arithBundle13_columns_056
private theorem arithBundle13_prefix_columns_14 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 64 = 81697293238919 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 60 4 78743649388697 2953643850222 arithBundle13_prefix_columns_13 arithBundle13_columns_060
private theorem arithBundle13_prefix_columns_15 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 68 = 84418738061740 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 64 4 81697293238919 2721444822821 arithBundle13_prefix_columns_14 arithBundle13_columns_064
private theorem arithBundle13_prefix_columns_16 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 72 = 86917674545780 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 68 4 84418738061740 2498936484040 arithBundle13_prefix_columns_15 arithBundle13_columns_068
private theorem arithBundle13_prefix_columns_17 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 76 = 89203766325644 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 72 4 86917674545780 2286091779864 arithBundle13_prefix_columns_16 arithBundle13_columns_072
private theorem arithBundle13_prefix_columns_18 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 80 = 91286673122888 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 76 4 89203766325644 2082906797244 arithBundle13_prefix_columns_17 arithBundle13_columns_076
private theorem arithBundle13_prefix_columns_19 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 84 = 93176053579514 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 80 4 91286673122888 1889380456626 arithBundle13_prefix_columns_18 arithBundle13_columns_080
private theorem arithBundle13_prefix_columns_20 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 88 = 94881600133705 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 84 4 93176053579514 1705546554191 arithBundle13_prefix_columns_19 arithBundle13_columns_084
private theorem arithBundle13_prefix_columns_21 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 92 = 96412998622184 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 88 4 94881600133705 1531398488479 arithBundle13_prefix_columns_20 arithBundle13_columns_088
private theorem arithBundle13_prefix_columns_22 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 96 = 97779912405272 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 92 4 96412998622184 1366913783088 arithBundle13_prefix_columns_21 arithBundle13_columns_092
private theorem arithBundle13_prefix_columns_23 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 100 = 98992001093540 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 96 4 97779912405272 1212088688268 arithBundle13_prefix_columns_22 arithBundle13_columns_096
private theorem arithBundle13_prefix_columns_24 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 104 = 100058923654771 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 100 4 98992001093540 1066922561231 arithBundle13_prefix_columns_23 arithBundle13_columns_100
private theorem arithBundle13_prefix_columns_25 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 108 = 100990377043709 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 104 4 100058923654771 931453388938 arithBundle13_prefix_columns_24 arithBundle13_columns_104
private theorem arithBundle13_prefix_columns_26 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 112 = 101796042689946 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 108 4 100990377043709 805665646237 arithBundle13_prefix_columns_25 arithBundle13_columns_108
private theorem arithBundle13_prefix_columns_27 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 116 = 102485583446322 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 112 4 101796042689946 689540756376 arithBundle13_prefix_columns_26 arithBundle13_columns_112
private theorem arithBundle13_prefix_columns_28 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 120 = 103068659063242 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 116 4 102485583446322 583075616920 arithBundle13_prefix_columns_27 arithBundle13_columns_116
private theorem arithBundle13_prefix_columns_29 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 124 = 103554929746491 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 120 4 103068659063242 486270683249 arithBundle13_prefix_columns_28 arithBundle13_columns_120
private theorem arithBundle13_prefix_columns_30 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 128 = 103954094946649 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 124 4 103554929746491 399165200158 arithBundle13_prefix_columns_29 arithBundle13_columns_124
private theorem arithBundle13_prefix_columns_31 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 132 = 104275832726891 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 128 4 103954094946649 321737780242 arithBundle13_prefix_columns_30 arithBundle13_columns_128
private theorem arithBundle13_prefix_columns_32 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 136 = 104529799955391 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 132 4 104275832726891 253967228500 arithBundle13_prefix_columns_31 arithBundle13_columns_132
private theorem arithBundle13_prefix_columns_33 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 140 = 104725555502152 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 136 4 104529799955391 195755546761 arithBundle13_prefix_columns_32 arithBundle13_columns_136
private theorem arithBundle13_prefix_columns_34 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 144 = 104872366374673 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 140 4 104725555502152 146810872521 arithBundle13_prefix_columns_33 arithBundle13_columns_140
private theorem arithBundle13_prefix_columns_35 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 148 = 104979075173379 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 144 4 104872366374673 106708798706 arithBundle13_prefix_columns_34 arithBundle13_columns_144
private theorem arithBundle13_prefix_columns_36 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 152 = 105053869972316 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 148 4 104979075173379 74794798937 arithBundle13_prefix_columns_35 arithBundle13_columns_148
private theorem arithBundle13_prefix_columns_37 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 156 = 105104138271244 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 152 4 105053869972316 50268298928 arithBundle13_prefix_columns_36 arithBundle13_columns_152
private theorem arithBundle13_prefix_columns_38 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 160 = 105136317328979 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 156 4 105104138271244 32179057735 arithBundle13_prefix_columns_37 arithBundle13_columns_156
private theorem arithBundle13_prefix_columns_39 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 164 = 105155765720546 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 160 4 105136317328979 19448391567 arithBundle13_prefix_columns_38 arithBundle13_columns_160
private theorem arithBundle13_prefix_columns_40 : arithBundle13_sliceWindow (auxiliaryColumnSlice contact25) 0 165 = 105159161466850 :=
  arithBundle13_combineSlices (auxiliaryColumnSlice contact25) 0 164 1 105155765720546 3395746304 arithBundle13_prefix_columns_39 arithBundle13_columns_164

private theorem arithBundle13_ordinary_ranks : ordinaryRankBound contact25 = 8631470379 := by decide +kernel
private theorem arithBundle13_ranks_000 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 4 = 28633648 :=
  contactRankWindow_of_rec contact25 0 4 28633648 (by decide +kernel)
private theorem arithBundle13_ranks_004 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 4 4 = 26787856 :=
  contactRankWindow_of_rec contact25 4 4 26787856 (by decide +kernel)
private theorem arithBundle13_ranks_008 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 8 4 = 25008880 :=
  contactRankWindow_of_rec contact25 8 4 25008880 (by decide +kernel)
private theorem arithBundle13_ranks_012 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 12 4 = 23296720 :=
  contactRankWindow_of_rec contact25 12 4 23296720 (by decide +kernel)
private theorem arithBundle13_ranks_016 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 16 4 = 21651376 :=
  contactRankWindow_of_rec contact25 16 4 21651376 (by decide +kernel)
private theorem arithBundle13_ranks_020 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 20 4 = 20072848 :=
  contactRankWindow_of_rec contact25 20 4 20072848 (by decide +kernel)
private theorem arithBundle13_ranks_024 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 24 4 = 18561136 :=
  contactRankWindow_of_rec contact25 24 4 18561136 (by decide +kernel)
private theorem arithBundle13_ranks_028 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 28 4 = 17116240 :=
  contactRankWindow_of_rec contact25 28 4 17116240 (by decide +kernel)
private theorem arithBundle13_ranks_032 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 32 4 = 15738160 :=
  contactRankWindow_of_rec contact25 32 4 15738160 (by decide +kernel)
private theorem arithBundle13_ranks_036 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 36 4 = 14426896 :=
  contactRankWindow_of_rec contact25 36 4 14426896 (by decide +kernel)
private theorem arithBundle13_ranks_040 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 40 4 = 13182448 :=
  contactRankWindow_of_rec contact25 40 4 13182448 (by decide +kernel)
private theorem arithBundle13_ranks_044 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 44 4 = 12004816 :=
  contactRankWindow_of_rec contact25 44 4 12004816 (by decide +kernel)
private theorem arithBundle13_ranks_048 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 48 4 = 10893796 :=
  contactRankWindow_of_rec contact25 48 4 10893796 (by decide +kernel)
private theorem arithBundle13_ranks_052 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 52 4 = 9848330 :=
  contactRankWindow_of_rec contact25 52 4 9848330 (by decide +kernel)
private theorem arithBundle13_ranks_056 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 56 4 = 8867156 :=
  contactRankWindow_of_rec contact25 56 4 8867156 (by decide +kernel)
private theorem arithBundle13_ranks_060 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 60 4 = 7948956 :=
  contactRankWindow_of_rec contact25 60 4 7948956 (by decide +kernel)
private theorem arithBundle13_ranks_064 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 64 4 = 7092103 :=
  contactRankWindow_of_rec contact25 64 4 7092103 (by decide +kernel)
private theorem arithBundle13_ranks_068 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 68 4 = 6294844 :=
  contactRankWindow_of_rec contact25 68 4 6294844 (by decide +kernel)
private theorem arithBundle13_ranks_072 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 72 4 = 5555256 :=
  contactRankWindow_of_rec contact25 72 4 5555256 (by decide +kernel)
private theorem arithBundle13_ranks_076 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 76 4 = 4871423 :=
  contactRankWindow_of_rec contact25 76 4 4871423 (by decide +kernel)
private theorem arithBundle13_ranks_080 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 80 4 = 4241732 :=
  contactRankWindow_of_rec contact25 80 4 4241732 (by decide +kernel)
private theorem arithBundle13_ranks_084 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 84 4 = 3664116 :=
  contactRankWindow_of_rec contact25 84 4 3664116 (by decide +kernel)
private theorem arithBundle13_ranks_088 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 88 4 = 3136663 :=
  contactRankWindow_of_rec contact25 88 4 3136663 (by decide +kernel)
private theorem arithBundle13_ranks_092 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 92 4 = 2657900 :=
  contactRankWindow_of_rec contact25 92 4 2657900 (by decide +kernel)
private theorem arithBundle13_ranks_096 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 96 4 = 2225616 :=
  contactRankWindow_of_rec contact25 96 4 2225616 (by decide +kernel)
private theorem arithBundle13_ranks_100 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 100 4 = 1837903 :=
  contactRankWindow_of_rec contact25 100 4 1837903 (by decide +kernel)
private theorem arithBundle13_ranks_104 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 104 4 = 1493428 :=
  contactRankWindow_of_rec contact25 104 4 1493428 (by decide +kernel)
private theorem arithBundle13_ranks_108 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 108 4 = 1189836 :=
  contactRankWindow_of_rec contact25 108 4 1189836 (by decide +kernel)
private theorem arithBundle13_ranks_112 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 112 4 = 925223 :=
  contactRankWindow_of_rec contact25 112 4 925223 (by decide +kernel)
private theorem arithBundle13_ranks_116 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 116 4 = 698396 :=
  contactRankWindow_of_rec contact25 116 4 698396 (by decide +kernel)
private theorem arithBundle13_ranks_120 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 120 4 = 506856 :=
  contactRankWindow_of_rec contact25 120 4 506856 (by decide +kernel)
private theorem arithBundle13_ranks_124 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 124 4 = 348703 :=
  contactRankWindow_of_rec contact25 124 4 348703 (by decide +kernel)
private theorem arithBundle13_ranks_128 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 128 4 = 222884 :=
  contactRankWindow_of_rec contact25 128 4 222884 (by decide +kernel)
private theorem arithBundle13_ranks_132 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 132 4 = 126756 :=
  contactRankWindow_of_rec contact25 132 4 126756 (by decide +kernel)
private theorem arithBundle13_ranks_136 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 136 4 = 58534 :=
  contactRankWindow_of_rec contact25 136 4 58534 (by decide +kernel)
private theorem arithBundle13_ranks_140 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 140 4 = 17638 :=
  contactRankWindow_of_rec contact25 140 4 17638 (by decide +kernel)
private theorem arithBundle13_ranks_144 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 144 4 = 989 :=
  contactRankWindow_of_rec contact25 144 4 989 (by decide +kernel)
private theorem arithBundle13_ranks_148 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 148 17 = 0 :=
  contactRankWindow_of_rec contact25 148 17 0 (by decide +kernel)
private theorem arithBundle13_prefix_ranks_00 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 8 = 55421504 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 4 4 28633648 26787856 arithBundle13_ranks_000 arithBundle13_ranks_004
private theorem arithBundle13_prefix_ranks_01 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 12 = 80430384 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 8 4 55421504 25008880 arithBundle13_prefix_ranks_00 arithBundle13_ranks_008
private theorem arithBundle13_prefix_ranks_02 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 16 = 103727104 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 12 4 80430384 23296720 arithBundle13_prefix_ranks_01 arithBundle13_ranks_012
private theorem arithBundle13_prefix_ranks_03 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 20 = 125378480 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 16 4 103727104 21651376 arithBundle13_prefix_ranks_02 arithBundle13_ranks_016
private theorem arithBundle13_prefix_ranks_04 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 24 = 145451328 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 20 4 125378480 20072848 arithBundle13_prefix_ranks_03 arithBundle13_ranks_020
private theorem arithBundle13_prefix_ranks_05 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 28 = 164012464 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 24 4 145451328 18561136 arithBundle13_prefix_ranks_04 arithBundle13_ranks_024
private theorem arithBundle13_prefix_ranks_06 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 32 = 181128704 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 28 4 164012464 17116240 arithBundle13_prefix_ranks_05 arithBundle13_ranks_028
private theorem arithBundle13_prefix_ranks_07 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 36 = 196866864 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 32 4 181128704 15738160 arithBundle13_prefix_ranks_06 arithBundle13_ranks_032
private theorem arithBundle13_prefix_ranks_08 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 40 = 211293760 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 36 4 196866864 14426896 arithBundle13_prefix_ranks_07 arithBundle13_ranks_036
private theorem arithBundle13_prefix_ranks_09 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 44 = 224476208 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 40 4 211293760 13182448 arithBundle13_prefix_ranks_08 arithBundle13_ranks_040
private theorem arithBundle13_prefix_ranks_10 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 48 = 236481024 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 44 4 224476208 12004816 arithBundle13_prefix_ranks_09 arithBundle13_ranks_044
private theorem arithBundle13_prefix_ranks_11 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 52 = 247374820 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 48 4 236481024 10893796 arithBundle13_prefix_ranks_10 arithBundle13_ranks_048
private theorem arithBundle13_prefix_ranks_12 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 56 = 257223150 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 52 4 247374820 9848330 arithBundle13_prefix_ranks_11 arithBundle13_ranks_052
private theorem arithBundle13_prefix_ranks_13 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 60 = 266090306 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 56 4 257223150 8867156 arithBundle13_prefix_ranks_12 arithBundle13_ranks_056
private theorem arithBundle13_prefix_ranks_14 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 64 = 274039262 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 60 4 266090306 7948956 arithBundle13_prefix_ranks_13 arithBundle13_ranks_060
private theorem arithBundle13_prefix_ranks_15 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 68 = 281131365 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 64 4 274039262 7092103 arithBundle13_prefix_ranks_14 arithBundle13_ranks_064
private theorem arithBundle13_prefix_ranks_16 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 72 = 287426209 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 68 4 281131365 6294844 arithBundle13_prefix_ranks_15 arithBundle13_ranks_068
private theorem arithBundle13_prefix_ranks_17 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 76 = 292981465 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 72 4 287426209 5555256 arithBundle13_prefix_ranks_16 arithBundle13_ranks_072
private theorem arithBundle13_prefix_ranks_18 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 80 = 297852888 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 76 4 292981465 4871423 arithBundle13_prefix_ranks_17 arithBundle13_ranks_076
private theorem arithBundle13_prefix_ranks_19 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 84 = 302094620 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 80 4 297852888 4241732 arithBundle13_prefix_ranks_18 arithBundle13_ranks_080
private theorem arithBundle13_prefix_ranks_20 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 88 = 305758736 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 84 4 302094620 3664116 arithBundle13_prefix_ranks_19 arithBundle13_ranks_084
private theorem arithBundle13_prefix_ranks_21 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 92 = 308895399 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 88 4 305758736 3136663 arithBundle13_prefix_ranks_20 arithBundle13_ranks_088
private theorem arithBundle13_prefix_ranks_22 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 96 = 311553299 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 92 4 308895399 2657900 arithBundle13_prefix_ranks_21 arithBundle13_ranks_092
private theorem arithBundle13_prefix_ranks_23 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 100 = 313778915 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 96 4 311553299 2225616 arithBundle13_prefix_ranks_22 arithBundle13_ranks_096
private theorem arithBundle13_prefix_ranks_24 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 104 = 315616818 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 100 4 313778915 1837903 arithBundle13_prefix_ranks_23 arithBundle13_ranks_100
private theorem arithBundle13_prefix_ranks_25 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 108 = 317110246 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 104 4 315616818 1493428 arithBundle13_prefix_ranks_24 arithBundle13_ranks_104
private theorem arithBundle13_prefix_ranks_26 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 112 = 318300082 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 108 4 317110246 1189836 arithBundle13_prefix_ranks_25 arithBundle13_ranks_108
private theorem arithBundle13_prefix_ranks_27 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 116 = 319225305 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 112 4 318300082 925223 arithBundle13_prefix_ranks_26 arithBundle13_ranks_112
private theorem arithBundle13_prefix_ranks_28 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 120 = 319923701 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 116 4 319225305 698396 arithBundle13_prefix_ranks_27 arithBundle13_ranks_116
private theorem arithBundle13_prefix_ranks_29 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 124 = 320430557 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 120 4 319923701 506856 arithBundle13_prefix_ranks_28 arithBundle13_ranks_120
private theorem arithBundle13_prefix_ranks_30 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 128 = 320779260 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 124 4 320430557 348703 arithBundle13_prefix_ranks_29 arithBundle13_ranks_124
private theorem arithBundle13_prefix_ranks_31 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 132 = 321002144 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 128 4 320779260 222884 arithBundle13_prefix_ranks_30 arithBundle13_ranks_128
private theorem arithBundle13_prefix_ranks_32 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 136 = 321128900 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 132 4 321002144 126756 arithBundle13_prefix_ranks_31 arithBundle13_ranks_132
private theorem arithBundle13_prefix_ranks_33 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 140 = 321187434 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 136 4 321128900 58534 arithBundle13_prefix_ranks_32 arithBundle13_ranks_136
private theorem arithBundle13_prefix_ranks_34 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 144 = 321205072 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 140 4 321187434 17638 arithBundle13_prefix_ranks_33 arithBundle13_ranks_140
private theorem arithBundle13_prefix_ranks_35 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 148 = 321206061 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 144 4 321205072 989 arithBundle13_prefix_ranks_34 arithBundle13_ranks_144
private theorem arithBundle13_prefix_ranks_36 : arithBundle13_sliceWindow (auxiliaryRankSlice contact25) 0 165 = 321206061 :=
  arithBundle13_combineSlices (auxiliaryRankSlice contact25) 0 148 17 321206061 0 arithBundle13_prefix_ranks_35 arithBundle13_ranks_148

theorem contact25_margin : sourceMargin contact25 :=
  arithBundle13_margin_of_checked_counts contact25 165 2241732209085489 105159161466850 8631470379 321206061
    rfl arithBundle13_ordinary_columns arithBundle13_prefix_columns_40 arithBundle13_ordinary_ranks arithBundle13_prefix_ranks_36 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle14_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle14_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle14_sliceWindow f a b = x) (hy : arithBundle14_sliceWindow f (a+b) c = y) :
    arithBundle14_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle14_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle14_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle14_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle14_sliceWindow,Nat.zero_add]

private theorem arithBundle14_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle14_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle14_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle14_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle14_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle14_ordinary_columns : ordinaryColumnCount contact28 = 213398325526845 := by decide +kernel
private theorem arithBundle14_columns_000 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 4 = 898978523434 :=
  contactColumnsWindow_fast contact28 0 4 898978523434 (by decide +kernel)
private theorem arithBundle14_columns_004 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 4 4 = 823770487466 :=
  contactColumnsWindow_fast contact28 4 4 823770487466 (by decide +kernel)
private theorem arithBundle14_columns_008 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 8 4 = 751862741435 :=
  contactColumnsWindow_fast contact28 8 4 751862741435 (by decide +kernel)
private theorem arithBundle14_columns_012 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 12 4 = 683272708446 :=
  contactColumnsWindow_fast contact28 12 4 683272708446 (by decide +kernel)
private theorem arithBundle14_columns_016 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 16 4 = 617990832847 :=
  contactColumnsWindow_fast contact28 16 4 617990832847 (by decide +kernel)
private theorem arithBundle14_columns_020 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 20 4 = 556011234710 :=
  contactColumnsWindow_fast contact28 20 4 556011234710 (by decide +kernel)
private theorem arithBundle14_columns_024 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 24 4 = 497332483572 :=
  contactColumnsWindow_fast contact28 24 4 497332483572 (by decide +kernel)
private theorem arithBundle14_columns_028 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 28 4 = 441957432519 :=
  contactColumnsWindow_fast contact28 28 4 441957432519 (by decide +kernel)
private theorem arithBundle14_columns_032 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 32 4 = 389902526354 :=
  contactColumnsWindow_fast contact28 32 4 389902526354 (by decide +kernel)
private theorem arithBundle14_columns_036 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 36 4 = 341157053248 :=
  contactColumnsWindow_fast contact28 36 4 341157053248 (by decide +kernel)
private theorem arithBundle14_columns_040 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 40 4 = 295714187930 :=
  contactColumnsWindow_fast contact28 40 4 295714187930 (by decide +kernel)
private theorem arithBundle14_columns_044 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 44 4 = 253572153870 :=
  contactColumnsWindow_fast contact28 44 4 253572153870 (by decide +kernel)
private theorem arithBundle14_columns_048 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 48 4 = 214734563876 :=
  contactColumnsWindow_fast contact28 48 4 214734563876 (by decide +kernel)
private theorem arithBundle14_columns_052 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 52 4 = 179218141532 :=
  contactColumnsWindow_fast contact28 52 4 179218141532 (by decide +kernel)
private theorem arithBundle14_columns_056 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 56 4 = 147009481318 :=
  contactColumnsWindow_fast contact28 56 4 147009481318 (by decide +kernel)
private theorem arithBundle14_columns_060 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 60 4 = 118103323442 :=
  contactColumnsWindow_fast contact28 60 4 118103323442 (by decide +kernel)
private theorem arithBundle14_columns_064 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 64 4 = 92498037120 :=
  contactColumnsWindow_fast contact28 64 4 92498037120 (by decide +kernel)
private theorem arithBundle14_columns_068 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 68 4 = 70198347680 :=
  contactColumnsWindow_fast contact28 68 4 70198347680 (by decide +kernel)
private theorem arithBundle14_columns_072 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 72 4 = 51219955319 :=
  contactColumnsWindow_fast contact28 72 4 51219955319 (by decide +kernel)
private theorem arithBundle14_columns_076 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 76 4 = 35548047277 :=
  contactColumnsWindow_fast contact28 76 4 35548047277 (by decide +kernel)
private theorem arithBundle14_columns_080 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 80 4 = 23162803306 :=
  contactColumnsWindow_fast contact28 80 4 23162803306 (by decide +kernel)
private theorem arithBundle14_columns_084 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 84 4 = 13934856248 :=
  contactColumnsWindow_fast contact28 84 4 13934856248 (by decide +kernel)
private theorem arithBundle14_columns_088 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 88 4 = 7571210034 :=
  contactColumnsWindow_fast contact28 88 4 7571210034 (by decide +kernel)
private theorem arithBundle14_columns_092 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 92 4 = 3618209538 :=
  contactColumnsWindow_fast contact28 92 4 3618209538 (by decide +kernel)
private theorem arithBundle14_columns_096 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 96 3 = 1221818574 :=
  contactColumnsWindow_fast contact28 96 3 1221818574 (by decide +kernel)
private theorem arithBundle14_prefix_columns_00 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 8 = 1722749010900 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 4 4 898978523434 823770487466 arithBundle14_columns_000 arithBundle14_columns_004
private theorem arithBundle14_prefix_columns_01 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 12 = 2474611752335 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 8 4 1722749010900 751862741435 arithBundle14_prefix_columns_00 arithBundle14_columns_008
private theorem arithBundle14_prefix_columns_02 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 16 = 3157884460781 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 12 4 2474611752335 683272708446 arithBundle14_prefix_columns_01 arithBundle14_columns_012
private theorem arithBundle14_prefix_columns_03 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 20 = 3775875293628 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 16 4 3157884460781 617990832847 arithBundle14_prefix_columns_02 arithBundle14_columns_016
private theorem arithBundle14_prefix_columns_04 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 24 = 4331886528338 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 20 4 3775875293628 556011234710 arithBundle14_prefix_columns_03 arithBundle14_columns_020
private theorem arithBundle14_prefix_columns_05 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 28 = 4829219011910 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 24 4 4331886528338 497332483572 arithBundle14_prefix_columns_04 arithBundle14_columns_024
private theorem arithBundle14_prefix_columns_06 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 32 = 5271176444429 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 28 4 4829219011910 441957432519 arithBundle14_prefix_columns_05 arithBundle14_columns_028
private theorem arithBundle14_prefix_columns_07 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 36 = 5661078970783 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 32 4 5271176444429 389902526354 arithBundle14_prefix_columns_06 arithBundle14_columns_032
private theorem arithBundle14_prefix_columns_08 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 40 = 6002236024031 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 36 4 5661078970783 341157053248 arithBundle14_prefix_columns_07 arithBundle14_columns_036
private theorem arithBundle14_prefix_columns_09 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 44 = 6297950211961 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 40 4 6002236024031 295714187930 arithBundle14_prefix_columns_08 arithBundle14_columns_040
private theorem arithBundle14_prefix_columns_10 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 48 = 6551522365831 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 44 4 6297950211961 253572153870 arithBundle14_prefix_columns_09 arithBundle14_columns_044
private theorem arithBundle14_prefix_columns_11 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 52 = 6766256929707 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 48 4 6551522365831 214734563876 arithBundle14_prefix_columns_10 arithBundle14_columns_048
private theorem arithBundle14_prefix_columns_12 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 56 = 6945475071239 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 52 4 6766256929707 179218141532 arithBundle14_prefix_columns_11 arithBundle14_columns_052
private theorem arithBundle14_prefix_columns_13 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 60 = 7092484552557 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 56 4 6945475071239 147009481318 arithBundle14_prefix_columns_12 arithBundle14_columns_056
private theorem arithBundle14_prefix_columns_14 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 64 = 7210587875999 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 60 4 7092484552557 118103323442 arithBundle14_prefix_columns_13 arithBundle14_columns_060
private theorem arithBundle14_prefix_columns_15 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 68 = 7303085913119 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 64 4 7210587875999 92498037120 arithBundle14_prefix_columns_14 arithBundle14_columns_064
private theorem arithBundle14_prefix_columns_16 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 72 = 7373284260799 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 68 4 7303085913119 70198347680 arithBundle14_prefix_columns_15 arithBundle14_columns_068
private theorem arithBundle14_prefix_columns_17 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 76 = 7424504216118 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 72 4 7373284260799 51219955319 arithBundle14_prefix_columns_16 arithBundle14_columns_072
private theorem arithBundle14_prefix_columns_18 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 80 = 7460052263395 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 76 4 7424504216118 35548047277 arithBundle14_prefix_columns_17 arithBundle14_columns_076
private theorem arithBundle14_prefix_columns_19 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 84 = 7483215066701 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 80 4 7460052263395 23162803306 arithBundle14_prefix_columns_18 arithBundle14_columns_080
private theorem arithBundle14_prefix_columns_20 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 88 = 7497149922949 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 84 4 7483215066701 13934856248 arithBundle14_prefix_columns_19 arithBundle14_columns_084
private theorem arithBundle14_prefix_columns_21 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 92 = 7504721132983 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 88 4 7497149922949 7571210034 arithBundle14_prefix_columns_20 arithBundle14_columns_088
private theorem arithBundle14_prefix_columns_22 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 96 = 7508339342521 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 92 4 7504721132983 3618209538 arithBundle14_prefix_columns_21 arithBundle14_columns_092
private theorem arithBundle14_prefix_columns_23 : arithBundle14_sliceWindow (auxiliaryColumnSlice contact28) 0 99 = 7509561161095 :=
  arithBundle14_combineSlices (auxiliaryColumnSlice contact28) 0 96 3 7508339342521 1221818574 arithBundle14_prefix_columns_22 arithBundle14_columns_096

private theorem arithBundle14_ordinary_ranks : ordinaryRankBound contact28 = 819827888 := by decide +kernel
private theorem arithBundle14_ranks_000 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 4 = 3368194 :=
  contactRankWindow_of_rec contact28 0 4 3368194 (by decide +kernel)
private theorem arithBundle14_ranks_004 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 4 4 = 3002626 :=
  contactRankWindow_of_rec contact28 4 4 3002626 (by decide +kernel)
private theorem arithBundle14_ranks_008 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 8 4 = 2659906 :=
  contactRankWindow_of_rec contact28 8 4 2659906 (by decide +kernel)
private theorem arithBundle14_ranks_012 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 12 4 = 2340034 :=
  contactRankWindow_of_rec contact28 12 4 2340034 (by decide +kernel)
private theorem arithBundle14_ranks_016 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 16 4 = 2043010 :=
  contactRankWindow_of_rec contact28 16 4 2043010 (by decide +kernel)
private theorem arithBundle14_ranks_020 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 20 4 = 1768834 :=
  contactRankWindow_of_rec contact28 20 4 1768834 (by decide +kernel)
private theorem arithBundle14_ranks_024 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 24 4 = 1517506 :=
  contactRankWindow_of_rec contact28 24 4 1517506 (by decide +kernel)
private theorem arithBundle14_ranks_028 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 28 4 = 1289009 :=
  contactRankWindow_of_rec contact28 28 4 1289009 (by decide +kernel)
private theorem arithBundle14_ranks_032 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 32 4 = 1082981 :=
  contactRankWindow_of_rec contact28 32 4 1082981 (by decide +kernel)
private theorem arithBundle14_ranks_036 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 36 4 = 898679 :=
  contactRankWindow_of_rec contact28 36 4 898679 (by decide +kernel)
private theorem arithBundle14_ranks_040 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 40 4 = 735154 :=
  contactRankWindow_of_rec contact28 40 4 735154 (by decide +kernel)
private theorem arithBundle14_ranks_044 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 44 4 = 591381 :=
  contactRankWindow_of_rec contact28 44 4 591381 (by decide +kernel)
private theorem arithBundle14_ranks_048 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 48 4 = 466235 :=
  contactRankWindow_of_rec contact28 48 4 466235 (by decide +kernel)
private theorem arithBundle14_ranks_052 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 52 4 = 358598 :=
  contactRankWindow_of_rec contact28 52 4 358598 (by decide +kernel)
private theorem arithBundle14_ranks_056 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 56 4 = 267525 :=
  contactRankWindow_of_rec contact28 56 4 267525 (by decide +kernel)
private theorem arithBundle14_ranks_060 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 60 4 = 191807 :=
  contactRankWindow_of_rec contact28 60 4 191807 (by decide +kernel)
private theorem arithBundle14_ranks_064 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 64 4 = 130330 :=
  contactRankWindow_of_rec contact28 64 4 130330 (by decide +kernel)
private theorem arithBundle14_ranks_068 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 68 4 = 82229 :=
  contactRankWindow_of_rec contact28 68 4 82229 (by decide +kernel)
private theorem arithBundle14_ranks_072 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 72 4 = 46211 :=
  contactRankWindow_of_rec contact28 72 4 46211 (by decide +kernel)
private theorem arithBundle14_ranks_076 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 76 4 = 21166 :=
  contactRankWindow_of_rec contact28 76 4 21166 (by decide +kernel)
private theorem arithBundle14_ranks_080 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 80 4 = 6316 :=
  contactRankWindow_of_rec contact28 80 4 6316 (by decide +kernel)
private theorem arithBundle14_ranks_084 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 84 4 = 347 :=
  contactRankWindow_of_rec contact28 84 4 347 (by decide +kernel)
private theorem arithBundle14_ranks_088 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 88 11 = 0 :=
  contactRankWindow_of_rec contact28 88 11 0 (by decide +kernel)
private theorem arithBundle14_prefix_ranks_00 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 8 = 6370820 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 4 4 3368194 3002626 arithBundle14_ranks_000 arithBundle14_ranks_004
private theorem arithBundle14_prefix_ranks_01 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 12 = 9030726 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 8 4 6370820 2659906 arithBundle14_prefix_ranks_00 arithBundle14_ranks_008
private theorem arithBundle14_prefix_ranks_02 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 16 = 11370760 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 12 4 9030726 2340034 arithBundle14_prefix_ranks_01 arithBundle14_ranks_012
private theorem arithBundle14_prefix_ranks_03 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 20 = 13413770 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 16 4 11370760 2043010 arithBundle14_prefix_ranks_02 arithBundle14_ranks_016
private theorem arithBundle14_prefix_ranks_04 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 24 = 15182604 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 20 4 13413770 1768834 arithBundle14_prefix_ranks_03 arithBundle14_ranks_020
private theorem arithBundle14_prefix_ranks_05 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 28 = 16700110 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 24 4 15182604 1517506 arithBundle14_prefix_ranks_04 arithBundle14_ranks_024
private theorem arithBundle14_prefix_ranks_06 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 32 = 17989119 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 28 4 16700110 1289009 arithBundle14_prefix_ranks_05 arithBundle14_ranks_028
private theorem arithBundle14_prefix_ranks_07 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 36 = 19072100 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 32 4 17989119 1082981 arithBundle14_prefix_ranks_06 arithBundle14_ranks_032
private theorem arithBundle14_prefix_ranks_08 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 40 = 19970779 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 36 4 19072100 898679 arithBundle14_prefix_ranks_07 arithBundle14_ranks_036
private theorem arithBundle14_prefix_ranks_09 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 44 = 20705933 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 40 4 19970779 735154 arithBundle14_prefix_ranks_08 arithBundle14_ranks_040
private theorem arithBundle14_prefix_ranks_10 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 48 = 21297314 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 44 4 20705933 591381 arithBundle14_prefix_ranks_09 arithBundle14_ranks_044
private theorem arithBundle14_prefix_ranks_11 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 52 = 21763549 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 48 4 21297314 466235 arithBundle14_prefix_ranks_10 arithBundle14_ranks_048
private theorem arithBundle14_prefix_ranks_12 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 56 = 22122147 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 52 4 21763549 358598 arithBundle14_prefix_ranks_11 arithBundle14_ranks_052
private theorem arithBundle14_prefix_ranks_13 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 60 = 22389672 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 56 4 22122147 267525 arithBundle14_prefix_ranks_12 arithBundle14_ranks_056
private theorem arithBundle14_prefix_ranks_14 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 64 = 22581479 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 60 4 22389672 191807 arithBundle14_prefix_ranks_13 arithBundle14_ranks_060
private theorem arithBundle14_prefix_ranks_15 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 68 = 22711809 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 64 4 22581479 130330 arithBundle14_prefix_ranks_14 arithBundle14_ranks_064
private theorem arithBundle14_prefix_ranks_16 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 72 = 22794038 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 68 4 22711809 82229 arithBundle14_prefix_ranks_15 arithBundle14_ranks_068
private theorem arithBundle14_prefix_ranks_17 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 76 = 22840249 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 72 4 22794038 46211 arithBundle14_prefix_ranks_16 arithBundle14_ranks_072
private theorem arithBundle14_prefix_ranks_18 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 80 = 22861415 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 76 4 22840249 21166 arithBundle14_prefix_ranks_17 arithBundle14_ranks_076
private theorem arithBundle14_prefix_ranks_19 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 84 = 22867731 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 80 4 22861415 6316 arithBundle14_prefix_ranks_18 arithBundle14_ranks_080
private theorem arithBundle14_prefix_ranks_20 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 88 = 22868078 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 84 4 22867731 347 arithBundle14_prefix_ranks_19 arithBundle14_ranks_084
private theorem arithBundle14_prefix_ranks_21 : arithBundle14_sliceWindow (auxiliaryRankSlice contact28) 0 99 = 22868078 :=
  arithBundle14_combineSlices (auxiliaryRankSlice contact28) 0 88 11 22868078 0 arithBundle14_prefix_ranks_20 arithBundle14_ranks_088

theorem contact28_margin : sourceMargin contact28 :=
  arithBundle14_margin_of_checked_counts contact28 99 213398325526845 7509561161095 819827888 22868078
    rfl arithBundle14_ordinary_columns arithBundle14_prefix_columns_23 arithBundle14_ordinary_ranks arithBundle14_prefix_ranks_21 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle15_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle15_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle15_sliceWindow f a b = x) (hy : arithBundle15_sliceWindow f (a+b) c = y) :
    arithBundle15_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle15_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle15_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle15_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle15_sliceWindow,Nat.zero_add]

private theorem arithBundle15_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle15_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle15_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle15_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle15_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle15_ordinary_columns : ordinaryColumnCount contact29 = 189765944780064 := by decide +kernel
private theorem arithBundle15_columns_000 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 4 = 1033684393978 :=
  contactColumnsWindow_fast contact29 0 4 1033684393978 (by decide +kernel)
private theorem arithBundle15_columns_004 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 4 4 = 948724267494 :=
  contactColumnsWindow_fast contact29 4 4 948724267494 (by decide +kernel)
private theorem arithBundle15_columns_008 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 8 4 = 867447121226 :=
  contactColumnsWindow_fast contact29 8 4 867447121226 (by decide +kernel)
private theorem arithBundle15_columns_012 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 12 4 = 789836155894 :=
  contactColumnsWindow_fast contact29 12 4 789836155894 (by decide +kernel)
private theorem arithBundle15_columns_016 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 16 4 = 715888148778 :=
  contactColumnsWindow_fast contact29 16 4 715888148778 (by decide +kernel)
private theorem arithBundle15_columns_020 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 20 4 = 645601543004 :=
  contactColumnsWindow_fast contact29 20 4 645601543004 (by decide +kernel)
private theorem arithBundle15_columns_024 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 24 4 = 578981464404 :=
  contactColumnsWindow_fast contact29 24 4 578981464404 (by decide +kernel)
private theorem arithBundle15_columns_028 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 28 4 = 516045855593 :=
  contactColumnsWindow_fast contact29 28 4 516045855593 (by decide +kernel)
private theorem arithBundle15_columns_032 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 32 4 = 456778022716 :=
  contactColumnsWindow_fast contact29 32 4 456778022716 (by decide +kernel)
private theorem arithBundle15_columns_036 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 36 4 = 401173246374 :=
  contactColumnsWindow_fast contact29 36 4 401173246374 (by decide +kernel)
private theorem arithBundle15_columns_040 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 40 4 = 349229970143 :=
  contactColumnsWindow_fast contact29 40 4 349229970143 (by decide +kernel)
private theorem arithBundle15_columns_044 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 44 4 = 300954415950 :=
  contactColumnsWindow_fast contact29 44 4 300954415950 (by decide +kernel)
private theorem arithBundle15_columns_048 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 48 4 = 256363524266 :=
  contactColumnsWindow_fast contact29 48 4 256363524266 (by decide +kernel)
private theorem arithBundle15_columns_052 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 52 4 = 215439085029 :=
  contactColumnsWindow_fast contact29 52 4 215439085029 (by decide +kernel)
private theorem arithBundle15_columns_056 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 56 4 = 178177470546 :=
  contactColumnsWindow_fast contact29 56 4 178177470546 (by decide +kernel)
private theorem arithBundle15_columns_060 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 60 4 = 144577523858 :=
  contactColumnsWindow_fast contact29 60 4 144577523858 (by decide +kernel)
private theorem arithBundle15_columns_064 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 64 4 = 114646742582 :=
  contactColumnsWindow_fast contact29 64 4 114646742582 (by decide +kernel)
private theorem arithBundle15_columns_068 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 68 4 = 88400409098 :=
  contactColumnsWindow_fast contact29 68 4 88400409098 (by decide +kernel)
private theorem arithBundle15_columns_072 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 72 4 = 65819289318 :=
  contactColumnsWindow_fast contact29 72 4 65819289318 (by decide +kernel)
private theorem arithBundle15_columns_076 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 76 4 = 46900821294 :=
  contactColumnsWindow_fast contact29 76 4 46900821294 (by decide +kernel)
private theorem arithBundle15_columns_080 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 80 4 = 31635982491 :=
  contactColumnsWindow_fast contact29 80 4 31635982491 (by decide +kernel)
private theorem arithBundle15_columns_084 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 84 4 = 19934518901 :=
  contactColumnsWindow_fast contact29 84 4 19934518901 (by decide +kernel)
private theorem arithBundle15_columns_088 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 88 4 = 11538073006 :=
  contactColumnsWindow_fast contact29 88 4 11538073006 (by decide +kernel)
private theorem arithBundle15_columns_092 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 92 4 = 5993436124 :=
  contactColumnsWindow_fast contact29 92 4 5993436124 (by decide +kernel)
private theorem arithBundle15_columns_096 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 96 3 = 2241814120 :=
  contactColumnsWindow_fast contact29 96 3 2241814120 (by decide +kernel)
private theorem arithBundle15_prefix_columns_00 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 8 = 1982408661472 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 4 4 1033684393978 948724267494 arithBundle15_columns_000 arithBundle15_columns_004
private theorem arithBundle15_prefix_columns_01 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 12 = 2849855782698 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 8 4 1982408661472 867447121226 arithBundle15_prefix_columns_00 arithBundle15_columns_008
private theorem arithBundle15_prefix_columns_02 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 16 = 3639691938592 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 12 4 2849855782698 789836155894 arithBundle15_prefix_columns_01 arithBundle15_columns_012
private theorem arithBundle15_prefix_columns_03 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 20 = 4355580087370 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 16 4 3639691938592 715888148778 arithBundle15_prefix_columns_02 arithBundle15_columns_016
private theorem arithBundle15_prefix_columns_04 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 24 = 5001181630374 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 20 4 4355580087370 645601543004 arithBundle15_prefix_columns_03 arithBundle15_columns_020
private theorem arithBundle15_prefix_columns_05 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 28 = 5580163094778 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 24 4 5001181630374 578981464404 arithBundle15_prefix_columns_04 arithBundle15_columns_024
private theorem arithBundle15_prefix_columns_06 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 32 = 6096208950371 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 28 4 5580163094778 516045855593 arithBundle15_prefix_columns_05 arithBundle15_columns_028
private theorem arithBundle15_prefix_columns_07 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 36 = 6552986973087 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 32 4 6096208950371 456778022716 arithBundle15_prefix_columns_06 arithBundle15_columns_032
private theorem arithBundle15_prefix_columns_08 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 40 = 6954160219461 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 36 4 6552986973087 401173246374 arithBundle15_prefix_columns_07 arithBundle15_columns_036
private theorem arithBundle15_prefix_columns_09 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 44 = 7303390189604 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 40 4 6954160219461 349229970143 arithBundle15_prefix_columns_08 arithBundle15_columns_040
private theorem arithBundle15_prefix_columns_10 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 48 = 7604344605554 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 44 4 7303390189604 300954415950 arithBundle15_prefix_columns_09 arithBundle15_columns_044
private theorem arithBundle15_prefix_columns_11 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 52 = 7860708129820 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 48 4 7604344605554 256363524266 arithBundle15_prefix_columns_10 arithBundle15_columns_048
private theorem arithBundle15_prefix_columns_12 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 56 = 8076147214849 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 52 4 7860708129820 215439085029 arithBundle15_prefix_columns_11 arithBundle15_columns_052
private theorem arithBundle15_prefix_columns_13 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 60 = 8254324685395 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 56 4 8076147214849 178177470546 arithBundle15_prefix_columns_12 arithBundle15_columns_056
private theorem arithBundle15_prefix_columns_14 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 64 = 8398902209253 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 60 4 8254324685395 144577523858 arithBundle15_prefix_columns_13 arithBundle15_columns_060
private theorem arithBundle15_prefix_columns_15 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 68 = 8513548951835 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 64 4 8398902209253 114646742582 arithBundle15_prefix_columns_14 arithBundle15_columns_064
private theorem arithBundle15_prefix_columns_16 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 72 = 8601949360933 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 68 4 8513548951835 88400409098 arithBundle15_prefix_columns_15 arithBundle15_columns_068
private theorem arithBundle15_prefix_columns_17 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 76 = 8667768650251 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 72 4 8601949360933 65819289318 arithBundle15_prefix_columns_16 arithBundle15_columns_072
private theorem arithBundle15_prefix_columns_18 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 80 = 8714669471545 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 76 4 8667768650251 46900821294 arithBundle15_prefix_columns_17 arithBundle15_columns_076
private theorem arithBundle15_prefix_columns_19 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 84 = 8746305454036 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 80 4 8714669471545 31635982491 arithBundle15_prefix_columns_18 arithBundle15_columns_080
private theorem arithBundle15_prefix_columns_20 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 88 = 8766239972937 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 84 4 8746305454036 19934518901 arithBundle15_prefix_columns_19 arithBundle15_columns_084
private theorem arithBundle15_prefix_columns_21 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 92 = 8777778045943 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 88 4 8766239972937 11538073006 arithBundle15_prefix_columns_20 arithBundle15_columns_088
private theorem arithBundle15_prefix_columns_22 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 96 = 8783771482067 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 92 4 8777778045943 5993436124 arithBundle15_prefix_columns_21 arithBundle15_columns_092
private theorem arithBundle15_prefix_columns_23 : arithBundle15_sliceWindow (auxiliaryColumnSlice contact29) 0 99 = 8786013296187 :=
  arithBundle15_combineSlices (auxiliaryColumnSlice contact29) 0 96 3 8783771482067 2241814120 arithBundle15_prefix_columns_22 arithBundle15_columns_096

private theorem arithBundle15_ordinary_ranks : ordinaryRankBound contact29 = 730555077 := by decide +kernel
private theorem arithBundle15_ranks_000 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 4 = 3872292 :=
  contactRankWindow_of_rec contact29 0 4 3872292 (by decide +kernel)
private theorem arithBundle15_ranks_004 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 4 4 = 3460452 :=
  contactRankWindow_of_rec contact29 4 4 3460452 (by decide +kernel)
private theorem arithBundle15_ranks_008 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 8 4 = 3073956 :=
  contactRankWindow_of_rec contact29 8 4 3073956 (by decide +kernel)
private theorem arithBundle15_ranks_012 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 12 4 = 2712804 :=
  contactRankWindow_of_rec contact29 12 4 2712804 (by decide +kernel)
private theorem arithBundle15_ranks_016 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 16 4 = 2376996 :=
  contactRankWindow_of_rec contact29 16 4 2376996 (by decide +kernel)
private theorem arithBundle15_ranks_020 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 20 4 = 2066532 :=
  contactRankWindow_of_rec contact29 20 4 2066532 (by decide +kernel)
private theorem arithBundle15_ranks_024 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 24 4 = 1781412 :=
  contactRankWindow_of_rec contact29 24 4 1781412 (by decide +kernel)
private theorem arithBundle15_ranks_028 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 28 4 = 1521582 :=
  contactRankWindow_of_rec contact29 28 4 1521582 (by decide +kernel)
private theorem arithBundle15_ranks_032 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 32 4 = 1286510 :=
  contactRankWindow_of_rec contact29 32 4 1286510 (by decide +kernel)
private theorem arithBundle15_ranks_036 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 36 4 = 1075366 :=
  contactRankWindow_of_rec contact29 36 4 1075366 (by decide +kernel)
private theorem arithBundle15_ranks_040 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 40 4 = 887140 :=
  contactRankWindow_of_rec contact29 40 4 887140 (by decide +kernel)
private theorem arithBundle15_ranks_044 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 44 4 = 720670 :=
  contactRankWindow_of_rec contact29 44 4 720670 (by decide +kernel)
private theorem arithBundle15_ranks_048 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 48 4 = 574778 :=
  contactRankWindow_of_rec contact29 48 4 574778 (by decide +kernel)
private theorem arithBundle15_ranks_052 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 52 4 = 448448 :=
  contactRankWindow_of_rec contact29 52 4 448448 (by decide +kernel)
private theorem arithBundle15_ranks_056 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 56 4 = 340430 :=
  contactRankWindow_of_rec contact29 56 4 340430 (by decide +kernel)
private theorem arithBundle15_ranks_060 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 60 4 = 249550 :=
  contactRankWindow_of_rec contact29 60 4 249550 (by decide +kernel)
private theorem arithBundle15_ranks_064 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 64 4 = 174876 :=
  contactRankWindow_of_rec contact29 64 4 174876 (by decide +kernel)
private theorem arithBundle15_ranks_068 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 68 4 = 115070 :=
  contactRankWindow_of_rec contact29 68 4 115070 (by decide +kernel)
private theorem arithBundle15_ranks_072 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 72 4 = 68962 :=
  contactRankWindow_of_rec contact29 72 4 68962 (by decide +kernel)
private theorem arithBundle15_ranks_076 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 76 4 = 35704 :=
  contactRankWindow_of_rec contact29 76 4 35704 (by decide +kernel)
private theorem arithBundle15_ranks_080 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 80 4 = 13872 :=
  contactRankWindow_of_rec contact29 80 4 13872 (by decide +kernel)
private theorem arithBundle15_ranks_084 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 84 4 = 2381 :=
  contactRankWindow_of_rec contact29 84 4 2381 (by decide +kernel)
private theorem arithBundle15_ranks_088 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 88 11 = 0 :=
  contactRankWindow_of_rec contact29 88 11 0 (by decide +kernel)
private theorem arithBundle15_prefix_ranks_00 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 8 = 7332744 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 4 4 3872292 3460452 arithBundle15_ranks_000 arithBundle15_ranks_004
private theorem arithBundle15_prefix_ranks_01 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 12 = 10406700 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 8 4 7332744 3073956 arithBundle15_prefix_ranks_00 arithBundle15_ranks_008
private theorem arithBundle15_prefix_ranks_02 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 16 = 13119504 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 12 4 10406700 2712804 arithBundle15_prefix_ranks_01 arithBundle15_ranks_012
private theorem arithBundle15_prefix_ranks_03 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 20 = 15496500 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 16 4 13119504 2376996 arithBundle15_prefix_ranks_02 arithBundle15_ranks_016
private theorem arithBundle15_prefix_ranks_04 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 24 = 17563032 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 20 4 15496500 2066532 arithBundle15_prefix_ranks_03 arithBundle15_ranks_020
private theorem arithBundle15_prefix_ranks_05 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 28 = 19344444 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 24 4 17563032 1781412 arithBundle15_prefix_ranks_04 arithBundle15_ranks_024
private theorem arithBundle15_prefix_ranks_06 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 32 = 20866026 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 28 4 19344444 1521582 arithBundle15_prefix_ranks_05 arithBundle15_ranks_028
private theorem arithBundle15_prefix_ranks_07 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 36 = 22152536 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 32 4 20866026 1286510 arithBundle15_prefix_ranks_06 arithBundle15_ranks_032
private theorem arithBundle15_prefix_ranks_08 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 40 = 23227902 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 36 4 22152536 1075366 arithBundle15_prefix_ranks_07 arithBundle15_ranks_036
private theorem arithBundle15_prefix_ranks_09 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 44 = 24115042 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 40 4 23227902 887140 arithBundle15_prefix_ranks_08 arithBundle15_ranks_040
private theorem arithBundle15_prefix_ranks_10 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 48 = 24835712 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 44 4 24115042 720670 arithBundle15_prefix_ranks_09 arithBundle15_ranks_044
private theorem arithBundle15_prefix_ranks_11 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 52 = 25410490 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 48 4 24835712 574778 arithBundle15_prefix_ranks_10 arithBundle15_ranks_048
private theorem arithBundle15_prefix_ranks_12 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 56 = 25858938 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 52 4 25410490 448448 arithBundle15_prefix_ranks_11 arithBundle15_ranks_052
private theorem arithBundle15_prefix_ranks_13 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 60 = 26199368 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 56 4 25858938 340430 arithBundle15_prefix_ranks_12 arithBundle15_ranks_056
private theorem arithBundle15_prefix_ranks_14 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 64 = 26448918 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 60 4 26199368 249550 arithBundle15_prefix_ranks_13 arithBundle15_ranks_060
private theorem arithBundle15_prefix_ranks_15 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 68 = 26623794 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 64 4 26448918 174876 arithBundle15_prefix_ranks_14 arithBundle15_ranks_064
private theorem arithBundle15_prefix_ranks_16 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 72 = 26738864 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 68 4 26623794 115070 arithBundle15_prefix_ranks_15 arithBundle15_ranks_068
private theorem arithBundle15_prefix_ranks_17 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 76 = 26807826 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 72 4 26738864 68962 arithBundle15_prefix_ranks_16 arithBundle15_ranks_072
private theorem arithBundle15_prefix_ranks_18 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 80 = 26843530 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 76 4 26807826 35704 arithBundle15_prefix_ranks_17 arithBundle15_ranks_076
private theorem arithBundle15_prefix_ranks_19 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 84 = 26857402 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 80 4 26843530 13872 arithBundle15_prefix_ranks_18 arithBundle15_ranks_080
private theorem arithBundle15_prefix_ranks_20 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 88 = 26859783 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 84 4 26857402 2381 arithBundle15_prefix_ranks_19 arithBundle15_ranks_084
private theorem arithBundle15_prefix_ranks_21 : arithBundle15_sliceWindow (auxiliaryRankSlice contact29) 0 99 = 26859783 :=
  arithBundle15_combineSlices (auxiliaryRankSlice contact29) 0 88 11 26859783 0 arithBundle15_prefix_ranks_20 arithBundle15_ranks_088

theorem contact29_margin : sourceMargin contact29 :=
  arithBundle15_margin_of_checked_counts contact29 99 189765944780064 8786013296187 730555077 26859783
    rfl arithBundle15_ordinary_columns arithBundle15_prefix_columns_23 arithBundle15_ordinary_ranks arithBundle15_prefix_ranks_21 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

private def arithBundle16_sliceWindow (f : Nat → Nat) (start length : Nat) : Nat :=
  sumRange length (fun i => f (start+i+1))

private theorem arithBundle16_combineSlices (f : Nat → Nat) (a b c x y : Nat)
    (hx : arithBundle16_sliceWindow f a b = x) (hy : arithBundle16_sliceWindow f (a+b) c = y) :
    arithBundle16_sliceWindow f a (b+c) = x+y := by
  simp only [arithBundle16_sliceWindow, sumRange_add, Nat.add_assoc] at hx hy ⊢
  rw [hx,hy]

private theorem arithBundle16_sliceWindow_zero (f : Nat → Nat) (length : Nat) :
    arithBundle16_sliceWindow f 0 length = sumRange length (fun i => f (i+1)) := by
  simp only [arithBundle16_sliceWindow,Nat.zero_add]

private theorem arithBundle16_margin_of_checked_counts (src : SourceShape) (q c0 c1 r0 r1 : Nat)
    (hq : src.q = q) (hc0 : ordinaryColumnCount src = c0)
    (hc1 : arithBundle16_sliceWindow (auxiliaryColumnSlice src) 0 q = c1)
    (hr0 : ordinaryRankBound src = r0)
    (hr1 : arithBundle16_sliceWindow (auxiliaryRankSlice src) 0 q = r1)
    (hm : nodes * (r0 + r1) < c0 + c1) : sourceMargin src := by
  unfold sourceMargin globalColumnCount localRankBound
  rw [hq, ← arithBundle16_sliceWindow_zero (auxiliaryRankSlice src),
    ← arithBundle16_sliceWindow_zero (auxiliaryColumnSlice src), hc0, hc1, hr0, hr1]
  exact hm

private theorem arithBundle16_ordinary_columns : ordinaryColumnCount contact32 = 529549160571811 := by decide +kernel
private theorem arithBundle16_columns_000 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 4 = 1997762247295 :=
  contactColumnsWindow_fast contact32 0 4 1997762247295 (by decide +kernel)
private theorem arithBundle16_columns_004 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 4 4 = 1858625020496 :=
  contactColumnsWindow_fast contact32 4 4 1858625020496 (by decide +kernel)
private theorem arithBundle16_columns_008 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 8 4 = 1724536887680 :=
  contactColumnsWindow_fast contact32 8 4 1724536887680 (by decide +kernel)
private theorem arithBundle16_columns_012 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 12 4 = 1595497705280 :=
  contactColumnsWindow_fast contact32 12 4 1595497705280 (by decide +kernel)
private theorem arithBundle16_columns_016 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 16 4 = 1471507681988 :=
  contactColumnsWindow_fast contact32 16 4 1471507681988 (by decide +kernel)
private theorem arithBundle16_columns_020 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 20 4 = 1352582344070 :=
  contactColumnsWindow_fast contact32 20 4 1352582344070 (by decide +kernel)
private theorem arithBundle16_columns_024 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 24 4 = 1238730541072 :=
  contactColumnsWindow_fast contact32 24 4 1238730541072 (by decide +kernel)
private theorem arithBundle16_columns_028 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 28 4 = 1129929334817 :=
  contactColumnsWindow_fast contact32 28 4 1129929334817 (by decide +kernel)
private theorem arithBundle16_columns_032 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 32 4 = 1026180332261 :=
  contactColumnsWindow_fast contact32 32 4 1026180332261 (by decide +kernel)
private theorem arithBundle16_columns_036 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 36 4 = 927481859624 :=
  contactColumnsWindow_fast contact32 36 4 927481859624 (by decide +kernel)
private theorem arithBundle16_columns_040 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 40 4 = 833851423310 :=
  contactColumnsWindow_fast contact32 40 4 833851423310 (by decide +kernel)
private theorem arithBundle16_columns_044 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 44 4 = 745291130215 :=
  contactColumnsWindow_fast contact32 44 4 745291130215 (by decide +kernel)
private theorem arithBundle16_columns_048 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 48 4 = 661781677038 :=
  contactColumnsWindow_fast contact32 48 4 661781677038 (by decide +kernel)
private theorem arithBundle16_columns_052 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 52 4 = 583324234595 :=
  contactColumnsWindow_fast contact32 52 4 583324234595 (by decide +kernel)
private theorem arithBundle16_columns_056 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 56 4 = 509917257236 :=
  contactColumnsWindow_fast contact32 56 4 509917257236 (by decide +kernel)
private theorem arithBundle16_columns_060 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 60 4 = 441581736892 :=
  contactColumnsWindow_fast contact32 60 4 441581736892 (by decide +kernel)
private theorem arithBundle16_columns_064 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 64 4 = 378313035292 :=
  contactColumnsWindow_fast contact32 64 4 378313035292 (by decide +kernel)
private theorem arithBundle16_columns_068 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 68 4 = 320095284798 :=
  contactColumnsWindow_fast contact32 68 4 320095284798 (by decide +kernel)
private theorem arithBundle16_columns_072 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 72 4 = 266929356905 :=
  contactColumnsWindow_fast contact32 72 4 266929356905 (by decide +kernel)
private theorem arithBundle16_columns_076 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 76 4 = 218814364645 :=
  contactColumnsWindow_fast contact32 76 4 218814364645 (by decide +kernel)
private theorem arithBundle16_columns_080 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 80 4 = 175773362080 :=
  contactColumnsWindow_fast contact32 80 4 175773362080 (by decide +kernel)
private theorem arithBundle16_columns_084 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 84 4 = 137796160576 :=
  contactColumnsWindow_fast contact32 84 4 137796160576 (by decide +kernel)
private theorem arithBundle16_columns_088 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 88 4 = 104870112534 :=
  contactColumnsWindow_fast contact32 88 4 104870112534 (by decide +kernel)
private theorem arithBundle16_columns_092 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 92 4 = 76995387711 :=
  contactColumnsWindow_fast contact32 92 4 76995387711 (by decide +kernel)
private theorem arithBundle16_columns_096 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 96 4 = 54140696724 :=
  contactColumnsWindow_fast contact32 96 4 54140696724 (by decide +kernel)
private theorem arithBundle16_columns_100 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 100 4 = 36153862848 :=
  contactColumnsWindow_fast contact32 100 4 36153862848 (by decide +kernel)
private theorem arithBundle16_columns_104 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 104 4 = 22667118876 :=
  contactColumnsWindow_fast contact32 104 4 22667118876 (by decide +kernel)
private theorem arithBundle16_columns_108 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 108 4 = 13155184103 :=
  contactColumnsWindow_fast contact32 108 4 13155184103 (by decide +kernel)
private theorem arithBundle16_columns_112 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 112 4 = 6943589927 :=
  contactColumnsWindow_fast contact32 112 4 6943589927 (by decide +kernel)
private theorem arithBundle16_columns_116 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 116 3 = 2673063666 :=
  contactColumnsWindow_fast contact32 116 3 2673063666 (by decide +kernel)
private theorem arithBundle16_prefix_columns_00 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 8 = 3856387267791 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 4 4 1997762247295 1858625020496 arithBundle16_columns_000 arithBundle16_columns_004
private theorem arithBundle16_prefix_columns_01 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 12 = 5580924155471 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 8 4 3856387267791 1724536887680 arithBundle16_prefix_columns_00 arithBundle16_columns_008
private theorem arithBundle16_prefix_columns_02 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 16 = 7176421860751 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 12 4 5580924155471 1595497705280 arithBundle16_prefix_columns_01 arithBundle16_columns_012
private theorem arithBundle16_prefix_columns_03 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 20 = 8647929542739 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 16 4 7176421860751 1471507681988 arithBundle16_prefix_columns_02 arithBundle16_columns_016
private theorem arithBundle16_prefix_columns_04 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 24 = 10000511886809 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 20 4 8647929542739 1352582344070 arithBundle16_prefix_columns_03 arithBundle16_columns_020
private theorem arithBundle16_prefix_columns_05 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 28 = 11239242427881 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 24 4 10000511886809 1238730541072 arithBundle16_prefix_columns_04 arithBundle16_columns_024
private theorem arithBundle16_prefix_columns_06 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 32 = 12369171762698 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 28 4 11239242427881 1129929334817 arithBundle16_prefix_columns_05 arithBundle16_columns_028
private theorem arithBundle16_prefix_columns_07 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 36 = 13395352094959 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 32 4 12369171762698 1026180332261 arithBundle16_prefix_columns_06 arithBundle16_columns_032
private theorem arithBundle16_prefix_columns_08 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 40 = 14322833954583 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 36 4 13395352094959 927481859624 arithBundle16_prefix_columns_07 arithBundle16_columns_036
private theorem arithBundle16_prefix_columns_09 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 44 = 15156685377893 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 40 4 14322833954583 833851423310 arithBundle16_prefix_columns_08 arithBundle16_columns_040
private theorem arithBundle16_prefix_columns_10 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 48 = 15901976508108 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 44 4 15156685377893 745291130215 arithBundle16_prefix_columns_09 arithBundle16_columns_044
private theorem arithBundle16_prefix_columns_11 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 52 = 16563758185146 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 48 4 15901976508108 661781677038 arithBundle16_prefix_columns_10 arithBundle16_columns_048
private theorem arithBundle16_prefix_columns_12 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 56 = 17147082419741 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 52 4 16563758185146 583324234595 arithBundle16_prefix_columns_11 arithBundle16_columns_052
private theorem arithBundle16_prefix_columns_13 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 60 = 17656999676977 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 56 4 17147082419741 509917257236 arithBundle16_prefix_columns_12 arithBundle16_columns_056
private theorem arithBundle16_prefix_columns_14 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 64 = 18098581413869 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 60 4 17656999676977 441581736892 arithBundle16_prefix_columns_13 arithBundle16_columns_060
private theorem arithBundle16_prefix_columns_15 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 68 = 18476894449161 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 64 4 18098581413869 378313035292 arithBundle16_prefix_columns_14 arithBundle16_columns_064
private theorem arithBundle16_prefix_columns_16 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 72 = 18796989733959 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 68 4 18476894449161 320095284798 arithBundle16_prefix_columns_15 arithBundle16_columns_068
private theorem arithBundle16_prefix_columns_17 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 76 = 19063919090864 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 72 4 18796989733959 266929356905 arithBundle16_prefix_columns_16 arithBundle16_columns_072
private theorem arithBundle16_prefix_columns_18 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 80 = 19282733455509 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 76 4 19063919090864 218814364645 arithBundle16_prefix_columns_17 arithBundle16_columns_076
private theorem arithBundle16_prefix_columns_19 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 84 = 19458506817589 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 80 4 19282733455509 175773362080 arithBundle16_prefix_columns_18 arithBundle16_columns_080
private theorem arithBundle16_prefix_columns_20 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 88 = 19596302978165 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 84 4 19458506817589 137796160576 arithBundle16_prefix_columns_19 arithBundle16_columns_084
private theorem arithBundle16_prefix_columns_21 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 92 = 19701173090699 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 88 4 19596302978165 104870112534 arithBundle16_prefix_columns_20 arithBundle16_columns_088
private theorem arithBundle16_prefix_columns_22 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 96 = 19778168478410 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 92 4 19701173090699 76995387711 arithBundle16_prefix_columns_21 arithBundle16_columns_092
private theorem arithBundle16_prefix_columns_23 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 100 = 19832309175134 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 96 4 19778168478410 54140696724 arithBundle16_prefix_columns_22 arithBundle16_columns_096
private theorem arithBundle16_prefix_columns_24 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 104 = 19868463037982 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 100 4 19832309175134 36153862848 arithBundle16_prefix_columns_23 arithBundle16_columns_100
private theorem arithBundle16_prefix_columns_25 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 108 = 19891130156858 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 104 4 19868463037982 22667118876 arithBundle16_prefix_columns_24 arithBundle16_columns_104
private theorem arithBundle16_prefix_columns_26 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 112 = 19904285340961 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 108 4 19891130156858 13155184103 arithBundle16_prefix_columns_25 arithBundle16_columns_108
private theorem arithBundle16_prefix_columns_27 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 116 = 19911228930888 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 112 4 19904285340961 6943589927 arithBundle16_prefix_columns_26 arithBundle16_columns_112
private theorem arithBundle16_prefix_columns_28 : arithBundle16_sliceWindow (auxiliaryColumnSlice contact32) 0 119 = 19913901994554 :=
  arithBundle16_combineSlices (auxiliaryColumnSlice contact32) 0 116 3 19911228930888 2673063666 arithBundle16_prefix_columns_27 arithBundle16_columns_116

private theorem arithBundle16_ordinary_ranks : ordinaryRankBound contact32 = 2035112827 := by decide +kernel
private theorem arithBundle16_ranks_000 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 4 = 7505346 :=
  contactRankWindow_of_rec contact32 0 4 7505346 (by decide +kernel)
private theorem arithBundle16_ranks_004 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 4 4 = 6828306 :=
  contactRankWindow_of_rec contact32 4 4 6828306 (by decide +kernel)
private theorem arithBundle16_ranks_008 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 8 4 = 6186210 :=
  contactRankWindow_of_rec contact32 8 4 6186210 (by decide +kernel)
private theorem arithBundle16_ranks_012 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 12 4 = 5579058 :=
  contactRankWindow_of_rec contact32 12 4 5579058 (by decide +kernel)
private theorem arithBundle16_ranks_016 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 16 4 = 5006850 :=
  contactRankWindow_of_rec contact32 16 4 5006850 (by decide +kernel)
private theorem arithBundle16_ranks_020 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 20 4 = 4469586 :=
  contactRankWindow_of_rec contact32 20 4 4469586 (by decide +kernel)
private theorem arithBundle16_ranks_024 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 24 4 = 3967266 :=
  contactRankWindow_of_rec contact32 24 4 3967266 (by decide +kernel)
private theorem arithBundle16_ranks_028 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 28 4 = 3499890 :=
  contactRankWindow_of_rec contact32 28 4 3499890 (by decide +kernel)
private theorem arithBundle16_ranks_032 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 32 4 = 3067437 :=
  contactRankWindow_of_rec contact32 32 4 3067437 (by decide +kernel)
private theorem arithBundle16_ranks_036 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 36 4 = 2669461 :=
  contactRankWindow_of_rec contact32 36 4 2669461 (by decide +kernel)
private theorem arithBundle16_ranks_040 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 40 4 = 2305051 :=
  contactRankWindow_of_rec contact32 40 4 2305051 (by decide +kernel)
private theorem arithBundle16_ranks_044 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 44 4 = 1973198 :=
  contactRankWindow_of_rec contact32 44 4 1973198 (by decide +kernel)
private theorem arithBundle16_ranks_048 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 48 4 = 1672634 :=
  contactRankWindow_of_rec contact32 48 4 1672634 (by decide +kernel)
private theorem arithBundle16_ranks_052 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 52 4 = 1401971 :=
  contactRankWindow_of_rec contact32 52 4 1401971 (by decide +kernel)
private theorem arithBundle16_ranks_056 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 56 4 = 1159978 :=
  contactRankWindow_of_rec contact32 56 4 1159978 (by decide +kernel)
private theorem arithBundle16_ranks_060 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 60 4 = 945226 :=
  contactRankWindow_of_rec contact32 60 4 945226 (by decide +kernel)
private theorem arithBundle16_ranks_064 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 64 4 = 756331 :=
  contactRankWindow_of_rec contact32 64 4 756331 (by decide +kernel)
private theorem arithBundle16_ranks_068 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 68 4 = 592166 :=
  contactRankWindow_of_rec contact32 68 4 592166 (by decide +kernel)
private theorem arithBundle16_ranks_072 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 72 4 = 451194 :=
  contactRankWindow_of_rec contact32 72 4 451194 (by decide +kernel)
private theorem arithBundle16_ranks_076 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 76 4 = 332035 :=
  contactRankWindow_of_rec contact32 76 4 332035 (by decide +kernel)
private theorem arithBundle16_ranks_080 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 80 4 = 233666 :=
  contactRankWindow_of_rec contact32 80 4 233666 (by decide +kernel)
private theorem arithBundle16_ranks_084 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 84 4 = 154442 :=
  contactRankWindow_of_rec contact32 84 4 154442 (by decide +kernel)
private theorem arithBundle16_ranks_088 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 88 4 = 92987 :=
  contactRankWindow_of_rec contact32 88 4 92987 (by decide +kernel)
private theorem arithBundle16_ranks_092 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 92 4 = 48382 :=
  contactRankWindow_of_rec contact32 92 4 48382 (by decide +kernel)
private theorem arithBundle16_ranks_096 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 96 4 = 18884 :=
  contactRankWindow_of_rec contact32 96 4 18884 (by decide +kernel)
private theorem arithBundle16_ranks_100 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 100 4 = 3262 :=
  contactRankWindow_of_rec contact32 100 4 3262 (by decide +kernel)
private theorem arithBundle16_ranks_104 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 104 15 = 0 :=
  contactRankWindow_of_rec contact32 104 15 0 (by decide +kernel)
private theorem arithBundle16_prefix_ranks_00 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 8 = 14333652 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 4 4 7505346 6828306 arithBundle16_ranks_000 arithBundle16_ranks_004
private theorem arithBundle16_prefix_ranks_01 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 12 = 20519862 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 8 4 14333652 6186210 arithBundle16_prefix_ranks_00 arithBundle16_ranks_008
private theorem arithBundle16_prefix_ranks_02 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 16 = 26098920 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 12 4 20519862 5579058 arithBundle16_prefix_ranks_01 arithBundle16_ranks_012
private theorem arithBundle16_prefix_ranks_03 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 20 = 31105770 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 16 4 26098920 5006850 arithBundle16_prefix_ranks_02 arithBundle16_ranks_016
private theorem arithBundle16_prefix_ranks_04 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 24 = 35575356 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 20 4 31105770 4469586 arithBundle16_prefix_ranks_03 arithBundle16_ranks_020
private theorem arithBundle16_prefix_ranks_05 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 28 = 39542622 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 24 4 35575356 3967266 arithBundle16_prefix_ranks_04 arithBundle16_ranks_024
private theorem arithBundle16_prefix_ranks_06 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 32 = 43042512 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 28 4 39542622 3499890 arithBundle16_prefix_ranks_05 arithBundle16_ranks_028
private theorem arithBundle16_prefix_ranks_07 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 36 = 46109949 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 32 4 43042512 3067437 arithBundle16_prefix_ranks_06 arithBundle16_ranks_032
private theorem arithBundle16_prefix_ranks_08 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 40 = 48779410 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 36 4 46109949 2669461 arithBundle16_prefix_ranks_07 arithBundle16_ranks_036
private theorem arithBundle16_prefix_ranks_09 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 44 = 51084461 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 40 4 48779410 2305051 arithBundle16_prefix_ranks_08 arithBundle16_ranks_040
private theorem arithBundle16_prefix_ranks_10 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 48 = 53057659 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 44 4 51084461 1973198 arithBundle16_prefix_ranks_09 arithBundle16_ranks_044
private theorem arithBundle16_prefix_ranks_11 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 52 = 54730293 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 48 4 53057659 1672634 arithBundle16_prefix_ranks_10 arithBundle16_ranks_048
private theorem arithBundle16_prefix_ranks_12 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 56 = 56132264 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 52 4 54730293 1401971 arithBundle16_prefix_ranks_11 arithBundle16_ranks_052
private theorem arithBundle16_prefix_ranks_13 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 60 = 57292242 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 56 4 56132264 1159978 arithBundle16_prefix_ranks_12 arithBundle16_ranks_056
private theorem arithBundle16_prefix_ranks_14 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 64 = 58237468 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 60 4 57292242 945226 arithBundle16_prefix_ranks_13 arithBundle16_ranks_060
private theorem arithBundle16_prefix_ranks_15 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 68 = 58993799 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 64 4 58237468 756331 arithBundle16_prefix_ranks_14 arithBundle16_ranks_064
private theorem arithBundle16_prefix_ranks_16 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 72 = 59585965 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 68 4 58993799 592166 arithBundle16_prefix_ranks_15 arithBundle16_ranks_068
private theorem arithBundle16_prefix_ranks_17 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 76 = 60037159 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 72 4 59585965 451194 arithBundle16_prefix_ranks_16 arithBundle16_ranks_072
private theorem arithBundle16_prefix_ranks_18 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 80 = 60369194 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 76 4 60037159 332035 arithBundle16_prefix_ranks_17 arithBundle16_ranks_076
private theorem arithBundle16_prefix_ranks_19 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 84 = 60602860 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 80 4 60369194 233666 arithBundle16_prefix_ranks_18 arithBundle16_ranks_080
private theorem arithBundle16_prefix_ranks_20 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 88 = 60757302 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 84 4 60602860 154442 arithBundle16_prefix_ranks_19 arithBundle16_ranks_084
private theorem arithBundle16_prefix_ranks_21 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 92 = 60850289 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 88 4 60757302 92987 arithBundle16_prefix_ranks_20 arithBundle16_ranks_088
private theorem arithBundle16_prefix_ranks_22 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 96 = 60898671 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 92 4 60850289 48382 arithBundle16_prefix_ranks_21 arithBundle16_ranks_092
private theorem arithBundle16_prefix_ranks_23 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 100 = 60917555 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 96 4 60898671 18884 arithBundle16_prefix_ranks_22 arithBundle16_ranks_096
private theorem arithBundle16_prefix_ranks_24 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 104 = 60920817 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 100 4 60917555 3262 arithBundle16_prefix_ranks_23 arithBundle16_ranks_100
private theorem arithBundle16_prefix_ranks_25 : arithBundle16_sliceWindow (auxiliaryRankSlice contact32) 0 119 = 60920817 :=
  arithBundle16_combineSlices (auxiliaryRankSlice contact32) 0 104 15 60920817 0 arithBundle16_prefix_ranks_24 arithBundle16_ranks_104

theorem contact32_margin : sourceMargin contact32 :=
  arithBundle16_margin_of_checked_counts contact32 119 529549160571811 19913901994554 2035112827 60920817
    rfl arithBundle16_ordinary_columns arithBundle16_prefix_columns_28 arithBundle16_ordinary_ranks arithBundle16_prefix_ranks_25 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts
