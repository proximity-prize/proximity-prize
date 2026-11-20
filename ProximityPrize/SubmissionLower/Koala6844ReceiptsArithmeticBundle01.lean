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



private theorem primaryWindow0 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 512 = 3667298442899748 :=
  firstJetWindow_of_closed primaryShape 0 0 512 (3667298442899748) (by decide +kernel) (by decide +kernel)

private theorem primaryWindow512 : contributionWindow (firstJetAuxContribution primaryShape 0) 512 232 = 408983504683680 :=
  firstJetWindow_of_closed primaryShape 0 512 232 (408983504683680) (by decide +kernel) (by decide +kernel)

private theorem primaryJoin0_744 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 744 = 4076281947583428 :=
  joinWindows (firstJetAuxContribution primaryShape 0) 0 512 232 (3667298442899748) (408983504683680) primaryWindow0 primaryWindow512

theorem primary_firstJetGap_eq : firstJetGap primaryShape 0 = 316435203 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum primaryShape 0 744 (4076281947583428) rfl primaryJoin0_744]
  decide +kernel
private theorem firstRoomWindow0 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 = 82280444742335988 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 0 512 (82280444742335988) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow512 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 512 512 = 170604847730586288 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 512 512 (170604847730586288) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 = 154746659953152864 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1024 512 (154746659953152864) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1536 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1536 512 = 76327542493542936 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1536 512 (76327542493542936) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 2048 352 = 8336607464420424 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 2048 352 (8336607464420424) (by decide +kernel) (by decide +kernel)

private theorem firstRoomJoin0_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 = 252885292472922276 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 512 (82280444742335988) (170604847730586288) firstRoomWindow0 firstRoomWindow512

private theorem firstRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 1024 = 231074202446695800 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 512 (154746659953152864) (76327542493542936) firstRoomWindow1024 firstRoomWindow1536

private theorem firstRoomJoin0_2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 = 483959494919618076 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 1024 (252885292472922276) (231074202446695800) firstRoomJoin0_1024 firstRoomJoin1024_1024

private theorem firstRoomJoin0_2400 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2400 = 492296102384038500 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 352 (483959494919618076) (8336607464420424) firstRoomJoin0_2048 firstRoomWindow2048

theorem firstRoom_firstJetGap_eq : firstJetGap firstRoomShape firstRoomCut = 4089764012323173 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstRoomShape firstRoomCut 2400 (492296102384038500) rfl firstRoomJoin0_2400]
  decide +kernel
private theorem secondRoomWindow0 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 = 82496506730927940 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 0 512 (82496506730927940) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow512 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 512 512 = 170767852133190816 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 512 512 (170767852133190816) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 = 154856606691472692 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1024 512 (154856606691472692) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1536 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1536 512 = 76384431543241764 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1536 512 (76384431543241764) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 2048 352 = 8347362523047996 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 2048 352 (8347362523047996) (by decide +kernel) (by decide +kernel)

private theorem secondRoomJoin0_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 = 253264358864118756 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 512 (82496506730927940) (170767852133190816) secondRoomWindow0 secondRoomWindow512

private theorem secondRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 1024 = 231241038234714456 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 512 (154856606691472692) (76384431543241764) secondRoomWindow1024 secondRoomWindow1536

private theorem secondRoomJoin0_2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 = 484505397098833212 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 1024 (253264358864118756) (231241038234714456) secondRoomJoin0_1024 secondRoomJoin1024_1024

private theorem secondRoomJoin0_2400 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2400 = 492852759621881208 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 352 (484505397098833212) (8347362523047996) secondRoomJoin0_2048 secondRoomWindow2048

theorem secondRoom_firstJetGap_eq : firstJetGap secondRoomShape secondRoomCut = 345816184972556 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondRoomShape secondRoomCut 2400 (492852759621881208) rfl secondRoomJoin0_2400]
  decide +kernel
private theorem firstAdaptiveWindow0 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 512 = 83469033811631316 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 0 512 (83469033811631316) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow512 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 512 512 = 171501620071809528 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 512 512 (171501620071809528) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 = 155351615471201880 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1024 512 (155351615471201880) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1536 512 = 76640681241754668 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1536 512 (76640681241754668) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 2048 352 = 8395881100492524 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 2048 352 (8395881100492524) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 = 254970653883440844 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 512 512 (83469033811631316) (171501620071809528) firstAdaptiveWindow0 firstAdaptiveWindow512

private theorem firstAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 1024 = 231992296712956548 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 512 (155351615471201880) (76640681241754668) firstAdaptiveWindow1024 firstAdaptiveWindow1536

private theorem firstAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 = 486962950596397392 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 1024 (254970653883440844) (231992296712956548) firstAdaptiveJoin0_1024 firstAdaptiveJoin1024_1024

private theorem firstAdaptiveJoin0_2400 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2400 = 495358831696889916 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 352 (486962950596397392) (8395881100492524) firstAdaptiveJoin0_2048 firstAdaptiveWindow2048

theorem firstAdaptive_firstJetGap_eq : firstJetGap firstAdaptiveShape 0 = firstAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstAdaptiveShape 0 2400 (495358831696889916) rfl firstAdaptiveJoin0_2400]
  decide +kernel
private theorem secondAdaptiveWindow0 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 512 = 145455749672460453456 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 0 512 (145455749672460453456) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 512 512 = 326171136863953350864 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 512 512 (326171136863953350864) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 = 503392593533778453024 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1024 512 (503392593533778453024) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1536 512 = 677120119681987366848 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1536 512 (677120119681987366848) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 = 847353715308535915788 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2048 512 (847353715308535915788) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2560 512 = 1014093380413458281856 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2560 512 (1014093380413458281856) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 = 1177339114996731016512 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3072 512 (1177339114996731016512) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3584 512 = 1337090919059124992460 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3584 512 (1337090919059124992460) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 = 1493348792601710318628 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4096 512 (1493348792601710318628) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4608 512 = 1646112735623551071264 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4608 512 (1646112735623551071264) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 = 1795382748123767317068 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5120 512 (1795382748123767317068) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5632 512 = 1941158830102340226360 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5632 512 (1941158830102340226360) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 = 2083440981559271212092 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6144 512 (2083440981559271212092) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6656 512 = 2222229202494566889888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6656 512 (2222229202494566889888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 = 2357523492908211542484 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7168 512 (2357523492908211542484) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7680 512 = 2489323852800231037416 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7680 512 (2489323852800231037416) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 = 2617630282170589204104 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8192 512 (2617630282170589204104) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8704 512 = 2742442781019331891224 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8704 512 (2742442781019331891224) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 = 2863761349346406558456 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9216 512 (2863761349346406558456) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9728 512 = 2981585987151910382592 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9728 512 (2981585987151910382592) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 = 3095916694436861817264 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10240 512 (3095916694436861817264) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10752 512 = 3206753471201979433680 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10752 512 (3206753471201979433680) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 = 3314096317446020005776 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11264 512 (3314096317446020005776) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11776 512 = 3417945233168394453408 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11776 512 (3417945233168394453408) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 = 3518300218369149543036 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12288 512 (3518300218369149543036) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12800 512 = 3615161273048247983064 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12800 512 (3615161273048247983064) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 = 3708528397205716486164 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13312 512 (3708528397205716486164) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13824 512 = 3798401590841538122808 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13824 512 (3798401590841538122808) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 = 3884780853955720913820 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14336 512 (3884780853955720913820) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14848 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14848 512 = 3967666186548265318560 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14848 512 (3967666186548265318560) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15360 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 = 4047057588619162318488 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15360 512 (4047057588619162318488) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15872 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15872 512 = 4122955060168430000232 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15872 512 (4122955060168430000232) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 = 4195358601196194247824 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16384 512 (4195358601196194247824) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16896 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16896 512 = 4264268211703760912028 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16896 512 (4264268211703760912028) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17408 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 = 4329683891691333445932 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17408 512 (4329683891691333445932) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17920 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17920 512 = 4391605641157524242412 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17920 512 (4391605641157524242412) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18432 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 = 4450033460102093615772 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18432 512 (4450033460102093615772) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18944 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18944 512 = 4504967348524998384108 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18944 512 (4504967348524998384108) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19456 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 = 4556407306426289555724 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19456 512 (4556407306426289555724) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19968 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19968 512 = 4604353333805912829948 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19968 512 (4604353333805912829948) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20480 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 = 4648805430663920206308 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20480 512 (4648805430663920206308) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20992 512 = 4689763597000266833148 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20992 512 (4689763597000266833148) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow21504 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 = 4727227832814987683412 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 21504 512 (4727227832814987683412) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22016 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22016 512 = 4761198138108058045776 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22016 512 (4761198138108058045776) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22528 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 = 4791674512879492643460 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22528 512 (4791674512879492643460) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23040 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23040 512 = 4818659235386434662960 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23040 512 (4818659235386434662960) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23552 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 = 4842179432781144482088 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23552 512 (4842179432781144482088) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24064 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24064 512 = 4862286922778517430752 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24064 512 (4862286922778517430752) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24576 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 = 4879035748572856000596 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24576 512 (4879035748572856000596) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25088 512 = 4892479953359576907504 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25088 512 (4892479953359576907504) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25600 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 = 4902673580334214613868 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25600 512 (4902673580334214613868) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26112 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26112 512 = 4909670672692282499316 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26112 512 (4909670672692282499316) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26624 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 = 4913525273629334120148 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26624 512 (4913525273629334120148) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27136 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27136 512 = 4914291426340862535144 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27136 512 (4914291426340862535144) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27648 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 = 4912023174022441390272 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27648 512 (4912023174022441390272) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28160 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28160 512 = 4906774559869546937496 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28160 512 (4906774559869546937496) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28672 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 = 4898599627077761896080 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28672 512 (4898599627077761896080) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29184 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29184 512 = 4887552418842563944788 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29184 512 (4887552418842563944788) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29696 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 = 4873686978360164970396 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29696 512 (4873686978360164970396) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30208 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30208 512 = 4857057348827262707340 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30208 512 (4857057348827262707340) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30720 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 = 4837717573438544537304 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30720 512 (4837717573438544537304) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31232 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31232 512 = 4815721695388595911944 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31232 512 (4815721695388595911944) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31744 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 = 4791123757872883989552 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31744 512 (4791123757872883989552) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32256 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32256 512 = 4763977804086964739520 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32256 512 (4763977804086964739520) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 = 4734337877226348920172 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32768 512 (4734337877226348920172) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33280 512 = 4702258020486573651960 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33280 512 (4702258020486573651960) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33792 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 = 4667792277063167238276 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33792 512 (4667792277063167238276) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34304 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34304 512 = 4630994690151649760208 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34304 512 (4630994690151649760208) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 = 4591919302947566992236 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34816 512 (4591919302947566992236) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35328 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35328 512 = 4550620158646420240920 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35328 512 (4550620158646420240920) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35840 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 = 4507151300443798663800 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35840 512 (4507151300443798663800) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36352 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36352 512 = 4461566771536172910672 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36352 512 (4461566771536172910672) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36864 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 = 4413920615119913817996 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36864 512 (4413920615119913817996) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37376 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37376 512 = 4364266874389381610604 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37376 512 (4364266874389381610604) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37888 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 = 4312659592539420228852 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37888 512 (4312659592539420228852) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38400 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38400 512 = 4259152812765608660700 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38400 512 (4259152812765608660700) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38912 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 = 4203800578263421111620 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38912 512 (4203800578263421111620) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39424 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39424 512 = 4146656932228438389384 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39424 512 (4146656932228438389384) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39936 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 = 4087775917856143430508 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39936 512 (4087775917856143430508) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40448 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40448 512 = 4027211578342100439744 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40448 512 (4027211578342100439744) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40960 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 = 3965017956881812394028 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40960 512 (3965017956881812394028) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41472 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41472 512 = 3901249096670823113976 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41472 512 (3901249096670823113976) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41984 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 = 3835959040904654745276 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41984 512 (3835959040904654745276) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow42496 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 42496 512 = 3769201832778947291688 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 42496 512 (3769201832778947291688) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43008 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 = 3701031515490454139676 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43008 512 (3701031515490454139676) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43520 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43520 512 = 3631502132235084837360 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43520 512 (3631502132235084837360) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44032 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 = 3560667726206988220452 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44032 512 (3560667726206988220452) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44544 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44544 512 = 3488582340601360603488 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44544 512 (3488582340601360603488) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45056 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 = 3415300018613716018836 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45056 512 (3415300018613716018836) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45568 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45568 512 = 3340874803439607263808 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45568 512 (3340874803439607263808) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46080 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 = 3265360738274528185524 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46080 512 (3265360738274528185524) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46592 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46592 512 = 3188811866314051763964 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46592 512 (3188811866314051763964) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47104 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 = 3111282230753654627748 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47104 512 (3111282230753654627748) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47616 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47616 512 = 3032825874788919539916 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47616 512 (3032825874788919539916) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48128 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 = 2953496841615323728596 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48128 512 (2953496841615323728596) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48640 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48640 512 = 2873349174428439149976 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48640 512 (2873349174428439149976) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49152 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 = 2792436916424032837200 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49152 512 (2792436916424032837200) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49664 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49664 512 = 2710814110799020799856 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49664 512 (2710814110799020799856) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50176 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 = 2628534800748730324500 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50176 512 (2628534800748730324500) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50688 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50688 512 = 2545653029467383028488 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50688 512 (2545653029467383028488) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51200 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 = 2462222840150381310444 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51200 512 (2462222840150381310444) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51712 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51712 512 = 2378298275993235170592 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51712 512 (2378298275993235170592) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52224 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 = 2293933380191482382748 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52224 512 (2293933380191482382748) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52736 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52736 512 = 2209182195940650649320 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52736 512 (2209182195940650649320) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53248 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 = 2124098766436260704136 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53248 512 (2124098766436260704136) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53760 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53760 512 = 2038737134873857563888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53760 512 (2038737134873857563888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54272 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 = 1953151344448943345904 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54272 512 (1953151344448943345904) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54784 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54784 512 = 1867395438357083421612 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54784 512 (1867395438357083421612) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55296 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 = 1781523459793759760700 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55296 512 (1781523459793759760700) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55808 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55808 512 = 1695589451955088501716 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55808 512 (1695589451955088501716) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56320 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 = 1609647458037842229504 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56320 512 (1609647458037842229504) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56832 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56832 512 = 1523751521236832546664 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56832 512 (1523751521236832546664) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57344 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 = 1437955684746568286784 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57344 512 (1437955684746568286784) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57856 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57856 512 = 1352313991762480478712 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57856 512 (1352313991762480478712) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58368 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 = 1266880485480150262188 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58368 512 (1266880485480150262188) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58880 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58880 512 = 1181709209095059933276 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58880 512 (1181709209095059933276) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow59392 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 512 = 1096854205802774478084 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 59392 512 (1096854205802774478084) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow59904 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59904 512 = 1012716057600140136804 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 59904 512 (1012716057600140136804) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow60416 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60416 512 = 931803908158149873132 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 60416 512 (931803908158149873132) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow60928 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60928 512 = 855196254623020315704 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 60928 512 (855196254623020315704) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow61440 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 512 = 782878194513433094640 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 61440 512 (782878194513433094640) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow61952 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61952 512 = 714756195584297785776 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 61952 512 (714756195584297785776) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow62464 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62464 512 = 650705502993486902112 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 62464 512 (650705502993486902112) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow62976 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62976 512 = 590600658954186304296 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 62976 512 (590600658954186304296) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow63488 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 512 = 534316205677289363568 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 63488 512 (534316205677289363568) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow64000 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64000 512 = 481726685374524465792 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 64000 512 (481726685374524465792) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow64512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64512 512 = 432706640258288435844 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 64512 512 (432706640258288435844) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow65024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65024 512 = 387130612540899780312 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 65024 512 (387130612540899780312) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow65536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 512 = 344873144434715845860 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 65536 512 (344873144434715845860) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow66048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66048 512 = 305808778152079497360 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 66048 512 (305808778152079497360) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow66560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66560 512 = 269812055905343797248 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 66560 512 (269812055905343797248) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow67072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67072 512 = 236757519906838509852 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 67072 512 (236757519906838509852) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow67584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 512 = 206519712368939276484 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 67584 512 (206519712368939276484) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow68096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68096 512 = 178973175503963223108 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 68096 512 (178973175503963223108) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow68608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68608 512 = 153992451524349050976 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 68608 512 (153992451524349050976) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow69120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69120 512 = 131452082643506506728 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 69120 512 (131452082643506506728) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow69632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 512 = 111226611073102477140 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 69632 512 (111226611073102477140) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow70144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70144 512 = 93190579024684534992 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 70144 512 (93190579024684534992) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow70656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70656 512 = 77218528710638762556 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 70656 512 (77218528710638762556) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow71168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71168 512 = 63185002343261755488 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 71168 512 (63185002343261755488) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow71680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 512 = 50964542134942874640 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 71680 512 (50964542134942874640) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow72192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72192 512 = 40431690298005462948 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 72192 512 (40431690298005462948) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow72704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72704 512 = 31460989044804555396 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 72704 512 (31460989044804555396) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow73216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73216 512 = 23926980587680744584 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 73216 512 (23926980587680744584) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow73728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 512 = 17704207138996362288 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 73728 512 (17704207138996362288) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow74240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74240 512 = 12667210911064608060 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 74240 512 (12667210911064608060) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow74752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74752 512 = 8690534116283214444 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 74752 512 (8690534116283214444) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow75264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75264 512 = 5648718967113670872 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 75264 512 (5648718967113670872) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow75776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 512 = 3416307676056778032 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 75776 512 (3416307676056778032) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow76288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76288 512 = 1867842454872282624 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 76288 512 (1867842454872282624) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow76800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76800 512 = 877865515865017152 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 76800 512 (877865515865017152) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow77312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77312 512 = 320919071388849528 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 77312 512 (320919071388849528) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow77824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77824 512 = 71545333802629524 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 77824 512 (71545333802629524) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow78336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 78336 480 = 4286543847258888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 78336 480 (4286543847258888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 = 471626886536413804320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 512 512 (145455749672460453456) (326171136863953350864) secondAdaptiveWindow0 secondAdaptiveWindow512

private theorem secondAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 1024 = 1180512713215765819872 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 512 (503392593533778453024) (677120119681987366848) secondAdaptiveWindow1024 secondAdaptiveWindow1536

private theorem secondAdaptiveJoin2048_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 = 1861447095721994197644 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 512 (847353715308535915788) (1014093380413458281856) secondAdaptiveWindow2048 secondAdaptiveWindow2560

private theorem secondAdaptiveJoin3072_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 1024 = 2514430034055856008972 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 512 (1177339114996731016512) (1337090919059124992460) secondAdaptiveWindow3072 secondAdaptiveWindow3584

private theorem secondAdaptiveJoin4096_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 = 3139461528225261389892 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 512 (1493348792601710318628) (1646112735623551071264) secondAdaptiveWindow4096 secondAdaptiveWindow4608

private theorem secondAdaptiveJoin5120_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 1024 = 3736541578226107543428 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 512 (1795382748123767317068) (1941158830102340226360) secondAdaptiveWindow5120 secondAdaptiveWindow5632

private theorem secondAdaptiveJoin6144_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 = 4305670184053838101980 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 512 (2083440981559271212092) (2222229202494566889888) secondAdaptiveWindow6144 secondAdaptiveWindow6656

private theorem secondAdaptiveJoin7168_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 1024 = 4846847345708442579900 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 512 (2357523492908211542484) (2489323852800231037416) secondAdaptiveWindow7168 secondAdaptiveWindow7680

private theorem secondAdaptiveJoin8192_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 = 5360073063189921095328 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 512 (2617630282170589204104) (2742442781019331891224) secondAdaptiveWindow8192 secondAdaptiveWindow8704

private theorem secondAdaptiveJoin9216_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 1024 = 5845347336498316941048 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 512 (2863761349346406558456) (2981585987151910382592) secondAdaptiveWindow9216 secondAdaptiveWindow9728

private theorem secondAdaptiveJoin10240_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 = 6302670165638841250944 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 512 (3095916694436861817264) (3206753471201979433680) secondAdaptiveWindow10240 secondAdaptiveWindow10752

private theorem secondAdaptiveJoin11264_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 1024 = 6732041550614414459184 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 512 (3314096317446020005776) (3417945233168394453408) secondAdaptiveWindow11264 secondAdaptiveWindow11776

private theorem secondAdaptiveJoin12288_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 = 7133461491417397526100 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 512 (3518300218369149543036) (3615161273048247983064) secondAdaptiveWindow12288 secondAdaptiveWindow12800

private theorem secondAdaptiveJoin13312_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 1024 = 7506929988047254608972 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 512 (3708528397205716486164) (3798401590841538122808) secondAdaptiveWindow13312 secondAdaptiveWindow13824

private theorem secondAdaptiveJoin14336_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 = 7852447040503986232380 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 512 (3884780853955720913820) (3967666186548265318560) secondAdaptiveWindow14336 secondAdaptiveWindow14848

private theorem secondAdaptiveJoin15360_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 1024 = 8170012648787592318720 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 512 (4047057588619162318488) (4122955060168430000232) secondAdaptiveWindow15360 secondAdaptiveWindow15872

private theorem secondAdaptiveJoin16384_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 = 8459626812899955159852 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 512 (4195358601196194247824) (4264268211703760912028) secondAdaptiveWindow16384 secondAdaptiveWindow16896

private theorem secondAdaptiveJoin17408_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 1024 = 8721289532848857688344 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 512 (4329683891691333445932) (4391605641157524242412) secondAdaptiveWindow17408 secondAdaptiveWindow17920

private theorem secondAdaptiveJoin18432_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 = 8955000808627091999880 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 512 (4450033460102093615772) (4504967348524998384108) secondAdaptiveWindow18432 secondAdaptiveWindow18944

private theorem secondAdaptiveJoin19456_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 1024 = 9160760640232202385672 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 512 (4556407306426289555724) (4604353333805912829948) secondAdaptiveWindow19456 secondAdaptiveWindow19968

private theorem secondAdaptiveJoin20480_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 = 9338569027664187039456 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 512 (4648805430663920206308) (4689763597000266833148) secondAdaptiveWindow20480 secondAdaptiveWindow20992

private theorem secondAdaptiveJoin21504_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 1024 = 9488425970923045729188 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 512 (4727227832814987683412) (4761198138108058045776) secondAdaptiveWindow21504 secondAdaptiveWindow22016

private theorem secondAdaptiveJoin22528_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 = 9610333748265927306420 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 512 (4791674512879492643460) (4818659235386434662960) secondAdaptiveWindow22528 secondAdaptiveWindow23040

private theorem secondAdaptiveJoin23552_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 1024 = 9704466355559661912840 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 512 (4842179432781144482088) (4862286922778517430752) secondAdaptiveWindow23552 secondAdaptiveWindow24064

private theorem secondAdaptiveJoin24576_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 = 9771515701932432908100 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 512 (4879035748572856000596) (4892479953359576907504) secondAdaptiveWindow24576 secondAdaptiveWindow25088

private theorem secondAdaptiveJoin25600_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 1024 = 9812344253026497113184 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 512 (4902673580334214613868) (4909670672692282499316) secondAdaptiveWindow25600 secondAdaptiveWindow26112

private theorem secondAdaptiveJoin26624_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 = 9827816699970196655292 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 512 (4913525273629334120148) (4914291426340862535144) secondAdaptiveWindow26624 secondAdaptiveWindow27136

private theorem secondAdaptiveJoin27648_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 1024 = 9818797733891988327768 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 512 (4912023174022441390272) (4906774559869546937496) secondAdaptiveWindow27648 secondAdaptiveWindow28160

private theorem secondAdaptiveJoin28672_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 = 9786152045920325840868 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 512 (4898599627077761896080) (4887552418842563944788) secondAdaptiveWindow28672 secondAdaptiveWindow29184

private theorem secondAdaptiveJoin29696_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 1024 = 9730744327187427677736 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 512 (4873686978360164970396) (4857057348827262707340) secondAdaptiveWindow29696 secondAdaptiveWindow30208

private theorem secondAdaptiveJoin30720_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 = 9653439268827140449248 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 512 (4837717573438544537304) (4815721695388595911944) secondAdaptiveWindow30720 secondAdaptiveWindow31232

private theorem secondAdaptiveJoin31744_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 1024 = 9555101561959848729072 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 512 (4791123757872883989552) (4763977804086964739520) secondAdaptiveWindow31744 secondAdaptiveWindow32256

private theorem secondAdaptiveJoin32768_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 = 9436595897712922572132 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 512 (4734337877226348920172) (4702258020486573651960) secondAdaptiveWindow32768 secondAdaptiveWindow33280

private theorem secondAdaptiveJoin33792_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 1024 = 9298786967214816998484 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 512 (4667792277063167238276) (4630994690151649760208) secondAdaptiveWindow33792 secondAdaptiveWindow34304

private theorem secondAdaptiveJoin34816_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 = 9142539461593987233156 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 512 (4591919302947566992236) (4550620158646420240920) secondAdaptiveWindow34816 secondAdaptiveWindow35328

private theorem secondAdaptiveJoin35840_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 1024 = 8968718071979971574472 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 512 (4507151300443798663800) (4461566771536172910672) secondAdaptiveWindow35840 secondAdaptiveWindow36352

private theorem secondAdaptiveJoin36864_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 = 8778187489509295428600 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 512 (4413920615119913817996) (4364266874389381610604) secondAdaptiveWindow36864 secondAdaptiveWindow37376

private theorem secondAdaptiveJoin37888_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 1024 = 8571812405305028889552 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 512 (4312659592539420228852) (4259152812765608660700) secondAdaptiveWindow37888 secondAdaptiveWindow38400

private theorem secondAdaptiveJoin38912_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 = 8350457510491859501004 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 512 (4203800578263421111620) (4146656932228438389384) secondAdaptiveWindow38912 secondAdaptiveWindow39424

private theorem secondAdaptiveJoin39936_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 1024 = 8114987496198243870252 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 512 (4087775917856143430508) (4027211578342100439744) secondAdaptiveWindow39936 secondAdaptiveWindow40448

private theorem secondAdaptiveJoin40960_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 = 7866267053552635508004 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 512 (3965017956881812394028) (3901249096670823113976) secondAdaptiveWindow40960 secondAdaptiveWindow41472

private theorem secondAdaptiveJoin41984_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 1024 = 7605160873683602036964 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 512 (3835959040904654745276) (3769201832778947291688) secondAdaptiveWindow41984 secondAdaptiveWindow42496

private theorem secondAdaptiveJoin43008_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 = 7332533647725538977036 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 512 (3701031515490454139676) (3631502132235084837360) secondAdaptiveWindow43008 secondAdaptiveWindow43520

private theorem secondAdaptiveJoin44032_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 1024 = 7049250066808348823940 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 512 (3560667726206988220452) (3488582340601360603488) secondAdaptiveWindow44032 secondAdaptiveWindow44544

private theorem secondAdaptiveJoin45056_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 = 6756174822053323282644 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 512 (3415300018613716018836) (3340874803439607263808) secondAdaptiveWindow45056 secondAdaptiveWindow45568

private theorem secondAdaptiveJoin46080_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 1024 = 6454172604588579949488 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 512 (3265360738274528185524) (3188811866314051763964) secondAdaptiveWindow46080 secondAdaptiveWindow46592

private theorem secondAdaptiveJoin47104_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 = 6144108105542574167664 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 512 (3111282230753654627748) (3032825874788919539916) secondAdaptiveWindow47104 secondAdaptiveWindow47616

private theorem secondAdaptiveJoin48128_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 1024 = 5826846016043762878572 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 512 (2953496841615323728596) (2873349174428439149976) secondAdaptiveWindow48128 secondAdaptiveWindow48640

private theorem secondAdaptiveJoin49152_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 = 5503251027223053637056 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 512 (2792436916424032837200) (2710814110799020799856) secondAdaptiveWindow49152 secondAdaptiveWindow49664

private theorem secondAdaptiveJoin50176_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 1024 = 5174187830216113352988 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 512 (2628534800748730324500) (2545653029467383028488) secondAdaptiveWindow50176 secondAdaptiveWindow50688

private theorem secondAdaptiveJoin51200_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 = 4840521116143616481036 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 512 (2462222840150381310444) (2378298275993235170592) secondAdaptiveWindow51200 secondAdaptiveWindow51712

private theorem secondAdaptiveJoin52224_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 1024 = 4503115576132133032068 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 512 (2293933380191482382748) (2209182195940650649320) secondAdaptiveWindow52224 secondAdaptiveWindow52736

private theorem secondAdaptiveJoin53248_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 = 4162835901310118268024 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 512 (2124098766436260704136) (2038737134873857563888) secondAdaptiveWindow53248 secondAdaptiveWindow53760

private theorem secondAdaptiveJoin54272_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 1024 = 3820546782806026767516 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 512 (1953151344448943345904) (1867395438357083421612) secondAdaptiveWindow54272 secondAdaptiveWindow54784

private theorem secondAdaptiveJoin55296_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 = 3477112911748848262416 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 512 (1781523459793759760700) (1695589451955088501716) secondAdaptiveWindow55296 secondAdaptiveWindow55808

private theorem secondAdaptiveJoin56320_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 1024 = 3133398979274674776168 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 512 (1609647458037842229504) (1523751521236832546664) secondAdaptiveWindow56320 secondAdaptiveWindow56832

private theorem secondAdaptiveJoin57344_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 = 2790269676509048765496 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 512 (1437955684746568286784) (1352313991762480478712) secondAdaptiveWindow57344 secondAdaptiveWindow57856

private theorem secondAdaptiveJoin58368_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 1024 = 2448589694575210195464 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 512 (1266880485480150262188) (1181709209095059933276) secondAdaptiveWindow58368 secondAdaptiveWindow58880

private theorem secondAdaptiveJoin59392_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 1024 = 2109570263402914614888 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 59392 512 512 (1096854205802774478084) (1012716057600140136804) secondAdaptiveWindow59392 secondAdaptiveWindow59904

private theorem secondAdaptiveJoin60416_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 60416 1024 = 1787000162781170188836 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 60416 512 512 (931803908158149873132) (855196254623020315704) secondAdaptiveWindow60416 secondAdaptiveWindow60928

private theorem secondAdaptiveJoin61440_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 1024 = 1497634390097730880416 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 512 512 (782878194513433094640) (714756195584297785776) secondAdaptiveWindow61440 secondAdaptiveWindow61952

private theorem secondAdaptiveJoin62464_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 62464 1024 = 1241306161947673206408 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 62464 512 512 (650705502993486902112) (590600658954186304296) secondAdaptiveWindow62464 secondAdaptiveWindow62976

private theorem secondAdaptiveJoin63488_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 1024 = 1016042891051813829360 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 63488 512 512 (534316205677289363568) (481726685374524465792) secondAdaptiveWindow63488 secondAdaptiveWindow64000

private theorem secondAdaptiveJoin64512_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 64512 1024 = 819837252799188216156 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 64512 512 512 (432706640258288435844) (387130612540899780312) secondAdaptiveWindow64512 secondAdaptiveWindow65024

private theorem secondAdaptiveJoin65536_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 1024 = 650681922586795343220 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 512 512 (344873144434715845860) (305808778152079497360) secondAdaptiveWindow65536 secondAdaptiveWindow66048

private theorem secondAdaptiveJoin66560_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 66560 1024 = 506569575812182307100 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 66560 512 512 (269812055905343797248) (236757519906838509852) secondAdaptiveWindow66560 secondAdaptiveWindow67072

private theorem secondAdaptiveJoin67584_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 1024 = 385492887872902499592 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 67584 512 512 (206519712368939276484) (178973175503963223108) secondAdaptiveWindow67584 secondAdaptiveWindow68096

private theorem secondAdaptiveJoin68608_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 68608 1024 = 285444534167855557704 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 68608 512 512 (153992451524349050976) (131452082643506506728) secondAdaptiveWindow68608 secondAdaptiveWindow69120

private theorem secondAdaptiveJoin69632_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 1024 = 204417190097787012132 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 512 512 (111226611073102477140) (93190579024684534992) secondAdaptiveWindow69632 secondAdaptiveWindow70144

private theorem secondAdaptiveJoin70656_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 70656 1024 = 140403531053900518044 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 70656 512 512 (77218528710638762556) (63185002343261755488) secondAdaptiveWindow70656 secondAdaptiveWindow71168

private theorem secondAdaptiveJoin71680_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 1024 = 91396232432948337588 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 71680 512 512 (50964542134942874640) (40431690298005462948) secondAdaptiveWindow71680 secondAdaptiveWindow72192

private theorem secondAdaptiveJoin72704_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 72704 1024 = 55387969632485299980 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 72704 512 512 (31460989044804555396) (23926980587680744584) secondAdaptiveWindow72704 secondAdaptiveWindow73216

private theorem secondAdaptiveJoin73728_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 1024 = 30371418050060970348 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 512 512 (17704207138996362288) (12667210911064608060) secondAdaptiveWindow73728 secondAdaptiveWindow74240

private theorem secondAdaptiveJoin74752_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 74752 1024 = 14339253083396885316 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 74752 512 512 (8690534116283214444) (5648718967113670872) secondAdaptiveWindow74752 secondAdaptiveWindow75264

private theorem secondAdaptiveJoin75776_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 1024 = 5284150130929060656 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 75776 512 512 (3416307676056778032) (1867842454872282624) secondAdaptiveWindow75776 secondAdaptiveWindow76288

private theorem secondAdaptiveJoin76800_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 76800 1024 = 1198784587253866680 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 76800 512 512 (877865515865017152) (320919071388849528) secondAdaptiveWindow76800 secondAdaptiveWindow77312

private theorem secondAdaptiveJoin77824_992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 77824 992 = 75831877649888412 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 77824 512 480 (71545333802629524) (4286543847258888) secondAdaptiveWindow77824 secondAdaptiveWindow78336

private theorem secondAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 = 1652139599752179624192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 1024 (471626886536413804320) (1180512713215765819872) secondAdaptiveJoin0_1024 secondAdaptiveJoin1024_1024

private theorem secondAdaptiveJoin2048_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 2048 = 4375877129777850206616 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 1024 (1861447095721994197644) (2514430034055856008972) secondAdaptiveJoin2048_1024 secondAdaptiveJoin3072_1024

private theorem secondAdaptiveJoin4096_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 = 6876003106451368933320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 1024 (3139461528225261389892) (3736541578226107543428) secondAdaptiveJoin4096_1024 secondAdaptiveJoin5120_1024

private theorem secondAdaptiveJoin6144_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 2048 = 9152517529762280681880 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 1024 (4305670184053838101980) (4846847345708442579900) secondAdaptiveJoin6144_1024 secondAdaptiveJoin7168_1024

private theorem secondAdaptiveJoin8192_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 = 11205420399688238036376 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 1024 (5360073063189921095328) (5845347336498316941048) secondAdaptiveJoin8192_1024 secondAdaptiveJoin9216_1024

private theorem secondAdaptiveJoin10240_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 2048 = 13034711716253255710128 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 1024 (6302670165638841250944) (6732041550614414459184) secondAdaptiveJoin10240_1024 secondAdaptiveJoin11264_1024

private theorem secondAdaptiveJoin12288_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 = 14640391479464652135072 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 1024 (7133461491417397526100) (7506929988047254608972) secondAdaptiveJoin12288_1024 secondAdaptiveJoin13312_1024

private theorem secondAdaptiveJoin14336_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 2048 = 16022459689291578551100 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 1024 (7852447040503986232380) (8170012648787592318720) secondAdaptiveJoin14336_1024 secondAdaptiveJoin15360_1024

private theorem secondAdaptiveJoin16384_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 = 17180916345748812848196 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 1024 (8459626812899955159852) (8721289532848857688344) secondAdaptiveJoin16384_1024 secondAdaptiveJoin17408_1024

private theorem secondAdaptiveJoin18432_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 2048 = 18115761448859294385552 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 1024 (8955000808627091999880) (9160760640232202385672) secondAdaptiveJoin18432_1024 secondAdaptiveJoin19456_1024

private theorem secondAdaptiveJoin20480_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 = 18826994998587232768644 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 1024 (9338569027664187039456) (9488425970923045729188) secondAdaptiveJoin20480_1024 secondAdaptiveJoin21504_1024

private theorem secondAdaptiveJoin22528_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 2048 = 19314800103825589219260 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 1024 (9610333748265927306420) (9704466355559661912840) secondAdaptiveJoin22528_1024 secondAdaptiveJoin23552_1024

private theorem secondAdaptiveJoin24576_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 = 19583859954958930021284 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 1024 (9771515701932432908100) (9812344253026497113184) secondAdaptiveJoin24576_1024 secondAdaptiveJoin25600_1024

private theorem secondAdaptiveJoin26624_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 2048 = 19646614433862184983060 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 1024 (9827816699970196655292) (9818797733891988327768) secondAdaptiveJoin26624_1024 secondAdaptiveJoin27648_1024

private theorem secondAdaptiveJoin28672_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 = 19516896373107753518604 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 1024 (9786152045920325840868) (9730744327187427677736) secondAdaptiveJoin28672_1024 secondAdaptiveJoin29696_1024

private theorem secondAdaptiveJoin30720_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 2048 = 19208540830786989178320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 1024 (9653439268827140449248) (9555101561959848729072) secondAdaptiveJoin30720_1024 secondAdaptiveJoin31744_1024

private theorem secondAdaptiveJoin32768_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 = 18735382864927739570616 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 1024 (9436595897712922572132) (9298786967214816998484) secondAdaptiveJoin32768_1024 secondAdaptiveJoin33792_1024

private theorem secondAdaptiveJoin34816_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 2048 = 18111257533573958807628 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 1024 (9142539461593987233156) (8968718071979971574472) secondAdaptiveJoin34816_1024 secondAdaptiveJoin35840_1024

private theorem secondAdaptiveJoin36864_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 = 17349999894814324318152 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 1024 (8778187489509295428600) (8571812405305028889552) secondAdaptiveJoin36864_1024 secondAdaptiveJoin37888_1024

private theorem secondAdaptiveJoin38912_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 2048 = 16465445006690103371256 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 1024 (8350457510491859501004) (8114987496198243870252) secondAdaptiveJoin38912_1024 secondAdaptiveJoin39936_1024

private theorem secondAdaptiveJoin40960_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 = 15471427927236237544968 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 1024 (7866267053552635508004) (7605160873683602036964) secondAdaptiveJoin40960_1024 secondAdaptiveJoin41984_1024

private theorem secondAdaptiveJoin43008_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 2048 = 14381783714533887800976 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 1024 (7332533647725538977036) (7049250066808348823940) secondAdaptiveJoin43008_1024 secondAdaptiveJoin44032_1024

private theorem secondAdaptiveJoin45056_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 = 13210347426641903232132 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 1024 (6756174822053323282644) (6454172604588579949488) secondAdaptiveJoin45056_1024 secondAdaptiveJoin46080_1024

private theorem secondAdaptiveJoin47104_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 2048 = 11970954121586337046236 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 1024 (6144108105542574167664) (5826846016043762878572) secondAdaptiveJoin47104_1024 secondAdaptiveJoin48128_1024

private theorem secondAdaptiveJoin49152_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 = 10677438857439166990044 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 1024 (5503251027223053637056) (5174187830216113352988) secondAdaptiveJoin49152_1024 secondAdaptiveJoin50176_1024

private theorem secondAdaptiveJoin51200_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 2048 = 9343636692275749513104 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 1024 (4840521116143616481036) (4503115576132133032068) secondAdaptiveJoin51200_1024 secondAdaptiveJoin52224_1024

private theorem secondAdaptiveJoin53248_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 = 7983382684116145035540 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 1024 (4162835901310118268024) (3820546782806026767516) secondAdaptiveJoin53248_1024 secondAdaptiveJoin54272_1024

private theorem secondAdaptiveJoin55296_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 2048 = 6610511891023523038584 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 1024 (3477112911748848262416) (3133398979274674776168) secondAdaptiveJoin55296_1024 secondAdaptiveJoin56320_1024

private theorem secondAdaptiveJoin57344_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 2048 = 5238859371084258960960 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 1024 (2790269676509048765496) (2448589694575210195464) secondAdaptiveJoin57344_1024 secondAdaptiveJoin58368_1024

private theorem secondAdaptiveJoin59392_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 59392 2048 = 3896570426184084803724 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 59392 1024 1024 (2109570263402914614888) (1787000162781170188836) secondAdaptiveJoin59392_1024 secondAdaptiveJoin60416_1024

private theorem secondAdaptiveJoin61440_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 2048 = 2738940552045404086824 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 1024 1024 (1497634390097730880416) (1241306161947673206408) secondAdaptiveJoin61440_1024 secondAdaptiveJoin62464_1024

private theorem secondAdaptiveJoin63488_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 63488 2048 = 1835880143851002045516 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 63488 1024 1024 (1016042891051813829360) (819837252799188216156) secondAdaptiveJoin63488_1024 secondAdaptiveJoin64512_1024

private theorem secondAdaptiveJoin65536_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 2048 = 1157251498398977650320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 1024 1024 (650681922586795343220) (506569575812182307100) secondAdaptiveJoin65536_1024 secondAdaptiveJoin66560_1024

private theorem secondAdaptiveJoin67584_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 67584 2048 = 670937422040758057296 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 67584 1024 1024 (385492887872902499592) (285444534167855557704) secondAdaptiveJoin67584_1024 secondAdaptiveJoin68608_1024

private theorem secondAdaptiveJoin69632_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 2048 = 344820721151687530176 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 1024 1024 (204417190097787012132) (140403531053900518044) secondAdaptiveJoin69632_1024 secondAdaptiveJoin70656_1024

private theorem secondAdaptiveJoin71680_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 71680 2048 = 146784202065433637568 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 71680 1024 1024 (91396232432948337588) (55387969632485299980) secondAdaptiveJoin71680_1024 secondAdaptiveJoin72704_1024

private theorem secondAdaptiveJoin73728_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 2048 = 44710671133457855664 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 1024 1024 (30371418050060970348) (14339253083396885316) secondAdaptiveJoin73728_1024 secondAdaptiveJoin74752_1024

private theorem secondAdaptiveJoin75776_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 75776 2048 = 6482934718182927336 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 75776 1024 1024 (5284150130929060656) (1198784587253866680) secondAdaptiveJoin75776_1024 secondAdaptiveJoin76800_1024

private theorem secondAdaptiveJoin0_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 = 6028016729530029830808 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 2048 (1652139599752179624192) (4375877129777850206616) secondAdaptiveJoin0_2048 secondAdaptiveJoin2048_2048

private theorem secondAdaptiveJoin4096_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 4096 = 16028520636213649615200 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 2048 (6876003106451368933320) (9152517529762280681880) secondAdaptiveJoin4096_2048 secondAdaptiveJoin6144_2048

private theorem secondAdaptiveJoin8192_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 = 24240132115941493746504 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 2048 (11205420399688238036376) (13034711716253255710128) secondAdaptiveJoin8192_2048 secondAdaptiveJoin10240_2048

private theorem secondAdaptiveJoin12288_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 4096 = 30662851168756230686172 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 2048 (14640391479464652135072) (16022459689291578551100) secondAdaptiveJoin12288_2048 secondAdaptiveJoin14336_2048

private theorem secondAdaptiveJoin16384_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 = 35296677794608107233748 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 2048 (17180916345748812848196) (18115761448859294385552) secondAdaptiveJoin16384_2048 secondAdaptiveJoin18432_2048

private theorem secondAdaptiveJoin20480_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 4096 = 38141795102412821987904 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 2048 (18826994998587232768644) (19314800103825589219260) secondAdaptiveJoin20480_2048 secondAdaptiveJoin22528_2048

private theorem secondAdaptiveJoin24576_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 = 39230474388821115004344 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 2048 (19583859954958930021284) (19646614433862184983060) secondAdaptiveJoin24576_2048 secondAdaptiveJoin26624_2048

private theorem secondAdaptiveJoin28672_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 4096 = 38725437203894742696924 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 2048 (19516896373107753518604) (19208540830786989178320) secondAdaptiveJoin28672_2048 secondAdaptiveJoin30720_2048

private theorem secondAdaptiveJoin32768_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 = 36846640398501698378244 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 2048 (18735382864927739570616) (18111257533573958807628) secondAdaptiveJoin32768_2048 secondAdaptiveJoin34816_2048

private theorem secondAdaptiveJoin36864_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 4096 = 33815444901504427689408 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 2048 (17349999894814324318152) (16465445006690103371256) secondAdaptiveJoin36864_2048 secondAdaptiveJoin38912_2048

private theorem secondAdaptiveJoin40960_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 = 29853211641770125345944 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 2048 (15471427927236237544968) (14381783714533887800976) secondAdaptiveJoin40960_2048 secondAdaptiveJoin43008_2048

private theorem secondAdaptiveJoin45056_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 4096 = 25181301548228240278368 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 2048 (13210347426641903232132) (11970954121586337046236) secondAdaptiveJoin45056_2048 secondAdaptiveJoin47104_2048

private theorem secondAdaptiveJoin49152_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 = 20021075549714916503148 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 2048 (10677438857439166990044) (9343636692275749513104) secondAdaptiveJoin49152_2048 secondAdaptiveJoin51200_2048

private theorem secondAdaptiveJoin53248_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 4096 = 14593894575139668074124 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 2048 (7983382684116145035540) (6610511891023523038584) secondAdaptiveJoin53248_2048 secondAdaptiveJoin55296_2048

private theorem secondAdaptiveJoin57344_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 4096 = 9135429797268343764684 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 2048 2048 (5238859371084258960960) (3896570426184084803724) secondAdaptiveJoin57344_2048 secondAdaptiveJoin59392_2048

private theorem secondAdaptiveJoin61440_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 61440 4096 = 4574820695896406132340 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 61440 2048 2048 (2738940552045404086824) (1835880143851002045516) secondAdaptiveJoin61440_2048 secondAdaptiveJoin63488_2048

private theorem secondAdaptiveJoin65536_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 4096 = 1828188920439735707616 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 2048 2048 (1157251498398977650320) (670937422040758057296) secondAdaptiveJoin65536_2048 secondAdaptiveJoin67584_2048

private theorem secondAdaptiveJoin69632_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 69632 4096 = 491604923217121167744 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 69632 2048 2048 (344820721151687530176) (146784202065433637568) secondAdaptiveJoin69632_2048 secondAdaptiveJoin71680_2048

private theorem secondAdaptiveJoin73728_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 4096 = 51193605851640783000 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 2048 2048 (44710671133457855664) (6482934718182927336) secondAdaptiveJoin73728_2048 secondAdaptiveJoin75776_2048

private theorem secondAdaptiveJoin0_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 = 22056537365743679446008 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 4096 (6028016729530029830808) (16028520636213649615200) secondAdaptiveJoin0_4096 secondAdaptiveJoin4096_4096

private theorem secondAdaptiveJoin8192_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 8192 = 54902983284697724432676 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 4096 (24240132115941493746504) (30662851168756230686172) secondAdaptiveJoin8192_4096 secondAdaptiveJoin12288_4096

private theorem secondAdaptiveJoin16384_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 = 73438472897020929221652 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 4096 (35296677794608107233748) (38141795102412821987904) secondAdaptiveJoin16384_4096 secondAdaptiveJoin20480_4096

private theorem secondAdaptiveJoin24576_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 8192 = 77955911592715857701268 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 4096 (39230474388821115004344) (38725437203894742696924) secondAdaptiveJoin24576_4096 secondAdaptiveJoin28672_4096

private theorem secondAdaptiveJoin32768_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 = 70662085300006126067652 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 4096 (36846640398501698378244) (33815444901504427689408) secondAdaptiveJoin32768_4096 secondAdaptiveJoin36864_4096

private theorem secondAdaptiveJoin40960_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 8192 = 55034513189998365624312 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 4096 (29853211641770125345944) (25181301548228240278368) secondAdaptiveJoin40960_4096 secondAdaptiveJoin45056_4096

private theorem secondAdaptiveJoin49152_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 = 34614970124854584577272 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 4096 (20021075549714916503148) (14593894575139668074124) secondAdaptiveJoin49152_4096 secondAdaptiveJoin53248_4096

private theorem secondAdaptiveJoin57344_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 8192 = 13710250493164749897024 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 4096 4096 (9135429797268343764684) (4574820695896406132340) secondAdaptiveJoin57344_4096 secondAdaptiveJoin61440_4096

private theorem secondAdaptiveJoin65536_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 8192 = 2319793843656856875360 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 4096 4096 (1828188920439735707616) (491604923217121167744) secondAdaptiveJoin65536_4096 secondAdaptiveJoin69632_4096

private theorem secondAdaptiveJoin73728_5088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 73728 5088 = 51269437729290671412 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 73728 4096 992 (51193605851640783000) (75831877649888412) secondAdaptiveJoin73728_4096 secondAdaptiveJoin77824_992

private theorem secondAdaptiveJoin0_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 = 76959520650441403878684 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 8192 (22056537365743679446008) (54902983284697724432676) secondAdaptiveJoin0_8192 secondAdaptiveJoin8192_8192

private theorem secondAdaptiveJoin16384_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 16384 = 151394384489736786922920 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 8192 (73438472897020929221652) (77955911592715857701268) secondAdaptiveJoin16384_8192 secondAdaptiveJoin24576_8192

private theorem secondAdaptiveJoin32768_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 = 125696598490004491691964 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 8192 (70662085300006126067652) (55034513189998365624312) secondAdaptiveJoin32768_8192 secondAdaptiveJoin40960_8192

private theorem secondAdaptiveJoin49152_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 16384 = 48325220618019334474296 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 8192 (34614970124854584577272) (13710250493164749897024) secondAdaptiveJoin49152_8192 secondAdaptiveJoin57344_8192

private theorem secondAdaptiveJoin65536_13280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 65536 13280 = 2371063281386147546772 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 65536 8192 5088 (2319793843656856875360) (51269437729290671412) secondAdaptiveJoin65536_8192 secondAdaptiveJoin73728_5088

private theorem secondAdaptiveJoin0_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 = 228353905140178190801604 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 16384 (76959520650441403878684) (151394384489736786922920) secondAdaptiveJoin0_16384 secondAdaptiveJoin16384_16384

private theorem secondAdaptiveJoin32768_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 32768 = 174021819108023826166260 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 16384 (125696598490004491691964) (48325220618019334474296) secondAdaptiveJoin32768_16384 secondAdaptiveJoin49152_16384

private theorem secondAdaptiveJoin0_65536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 65536 = 402375724248202016967864 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 32768 (228353905140178190801604) (174021819108023826166260) secondAdaptiveJoin0_32768 secondAdaptiveJoin32768_32768

private theorem secondAdaptiveJoin0_78816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 78816 = 404746787529588164514636 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 65536 13280 (402375724248202016967864) (2371063281386147546772) secondAdaptiveJoin0_65536 secondAdaptiveJoin65536_13280

theorem secondAdaptive_firstJetGap_eq : firstJetGap secondAdaptiveShape 0 = secondAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondAdaptiveShape 0 78816 (404746787529588164514636) rfl secondAdaptiveJoin0_78816]
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

private theorem contact00OrdinaryColumns : ordinaryColumnCount contact00 = 2468599665131471 := by decide +kernel
private theorem contact00ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact00) 0 4 = 6881977548496 :=
  contactColumnsWindow_fast contact00 0 4 6881977548496 (by decide +kernel)
private theorem contact00ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact00) 4 4 = 6544037620048 :=
  contactColumnsWindow_fast contact00 4 4 6544037620048 (by decide +kernel)
private theorem contact00ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact00) 8 4 = 6214638973228 :=
  contactColumnsWindow_fast contact00 8 4 6214638973228 (by decide +kernel)
private theorem contact00ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact00) 12 4 = 5893784449864 :=
  contactColumnsWindow_fast contact00 12 4 5893784449864 (by decide +kernel)
private theorem contact00ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact00) 16 4 = 5581472112969 :=
  contactColumnsWindow_fast contact00 16 4 5581472112969 (by decide +kernel)
private theorem contact00ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact00) 20 4 = 5277703943236 :=
  contactColumnsWindow_fast contact00 20 4 5277703943236 (by decide +kernel)
private theorem contact00ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact00) 24 4 = 4982493936148 :=
  contactColumnsWindow_fast contact00 24 4 4982493936148 (by decide +kernel)
private theorem contact00ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact00) 28 4 = 4695860997226 :=
  contactColumnsWindow_fast contact00 28 4 4695860997226 (by decide +kernel)
private theorem contact00ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact00) 32 4 = 4417775450128 :=
  contactColumnsWindow_fast contact00 32 4 4417775450128 (by decide +kernel)
private theorem contact00ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact00) 36 4 = 4148235233339 :=
  contactColumnsWindow_fast contact00 36 4 4148235233339 (by decide +kernel)
private theorem contact00ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact00) 40 4 = 3887242111372 :=
  contactColumnsWindow_fast contact00 40 4 3887242111372 (by decide +kernel)
private theorem contact00ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact00) 44 4 = 3634813527667 :=
  contactColumnsWindow_fast contact00 44 4 3634813527667 (by decide +kernel)
private theorem contact00ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact00) 48 4 = 3390963133090 :=
  contactColumnsWindow_fast contact00 48 4 3390963133090 (by decide +kernel)
private theorem contact00ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact00) 52 4 = 3155661596440 :=
  contactColumnsWindow_fast contact00 52 4 3155661596440 (by decide +kernel)
private theorem contact00ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact00) 56 4 = 2928909533279 :=
  contactColumnsWindow_fast contact00 56 4 2928909533279 (by decide +kernel)
private theorem contact00ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact00) 60 4 = 2710706731386 :=
  contactColumnsWindow_fast contact00 60 4 2710706731386 (by decide +kernel)
private theorem contact00ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact00) 64 4 = 2501077609345 :=
  contactColumnsWindow_fast contact00 64 4 2501077609345 (by decide +kernel)
private theorem contact00ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact00) 68 4 = 2300024320738 :=
  contactColumnsWindow_fast contact00 68 4 2300024320738 (by decide +kernel)
private theorem contact00ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact00) 72 4 = 2107524783012 :=
  contactColumnsWindow_fast contact00 72 4 2107524783012 (by decide +kernel)
private theorem contact00ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact00) 76 4 = 1923575304802 :=
  contactColumnsWindow_fast contact00 76 4 1923575304802 (by decide +kernel)
private theorem contact00ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact00) 80 4 = 1748174883190 :=
  contactColumnsWindow_fast contact00 80 4 1748174883190 (by decide +kernel)
private theorem contact00ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact00) 84 4 = 1581352816546 :=
  contactColumnsWindow_fast contact00 84 4 1581352816546 (by decide +kernel)
private theorem contact00ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact00) 88 4 = 1423102472529 :=
  contactColumnsWindow_fast contact00 88 4 1423102472529 (by decide +kernel)
private theorem contact00ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact00) 92 4 = 1273405539812 :=
  contactColumnsWindow_fast contact00 92 4 1273405539812 (by decide +kernel)
private theorem contact00ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact00) 96 4 = 1132258604478 :=
  contactColumnsWindow_fast contact00 96 4 1132258604478 (by decide +kernel)
private theorem contact00ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact00) 100 4 = 999661187423 :=
  contactColumnsWindow_fast contact00 100 4 999661187423 (by decide +kernel)
private theorem contact00ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact00) 104 4 = 875645649358 :=
  contactColumnsWindow_fast contact00 104 4 875645649358 (by decide +kernel)
private theorem contact00ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact00) 108 4 = 760198254751 :=
  contactColumnsWindow_fast contact00 108 4 760198254751 (by decide +kernel)
private theorem contact00ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact00) 112 4 = 653303808573 :=
  contactColumnsWindow_fast contact00 112 4 653303808573 (by decide +kernel)
private theorem contact00ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact00) 116 4 = 554959491380 :=
  contactColumnsWindow_fast contact00 116 4 554959491380 (by decide +kernel)
private theorem contact00ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact00) 120 4 = 465165724813 :=
  contactColumnsWindow_fast contact00 120 4 465165724813 (by decide +kernel)
private theorem contact00ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact00) 124 4 = 383955986794 :=
  contactColumnsWindow_fast contact00 124 4 383955986794 (by decide +kernel)
private theorem contact00ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact00) 128 4 = 311311567572 :=
  contactColumnsWindow_fast contact00 128 4 311311567572 (by decide +kernel)
private theorem contact00ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact00) 132 4 = 247219796391 :=
  contactColumnsWindow_fast contact00 132 4 247219796391 (by decide +kernel)
private theorem contact00ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact00) 136 4 = 191670981497 :=
  contactColumnsWindow_fast contact00 136 4 191670981497 (by decide +kernel)
private theorem contact00ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact00) 140 4 = 144563600024 :=
  contactColumnsWindow_fast contact00 140 4 144563600024 (by decide +kernel)
private theorem contact00ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact00) 144 4 = 105628445076 :=
  contactColumnsWindow_fast contact00 144 4 105628445076 (by decide +kernel)
private theorem contact00ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact00) 148 4 = 74368686384 :=
  contactColumnsWindow_fast contact00 148 4 74368686384 (by decide +kernel)
private theorem contact00ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact00) 152 4 = 50140556427 :=
  contactColumnsWindow_fast contact00 152 4 50140556427 (by decide +kernel)
private theorem contact00ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact00) 156 4 = 32147772780 :=
  contactColumnsWindow_fast contact00 156 4 32147772780 (by decide +kernel)
private theorem contact00ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact00) 160 1 = 5867444649 :=
  contactColumnsWindow_fast contact00 160 1 5867444649 (by decide +kernel)
private theorem contact00ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact00) 0 8 = 13426015168544 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 4 4 6881977548496 6544037620048 contact00ColumnsSlice0 contact00ColumnsSlice4
private theorem contact00ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact00) 8 8 = 12108423423092 :=
  combineSlices (auxiliaryColumnSlice contact00) 8 4 4 6214638973228 5893784449864 contact00ColumnsSlice8 contact00ColumnsSlice12
private theorem contact00ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact00) 16 8 = 10859176056205 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 4 4 5581472112969 5277703943236 contact00ColumnsSlice16 contact00ColumnsSlice20
private theorem contact00ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact00) 24 8 = 9678354933374 :=
  combineSlices (auxiliaryColumnSlice contact00) 24 4 4 4982493936148 4695860997226 contact00ColumnsSlice24 contact00ColumnsSlice28
private theorem contact00ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact00) 32 8 = 8566010683467 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 4 4 4417775450128 4148235233339 contact00ColumnsSlice32 contact00ColumnsSlice36
private theorem contact00ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact00) 40 8 = 7522055639039 :=
  combineSlices (auxiliaryColumnSlice contact00) 40 4 4 3887242111372 3634813527667 contact00ColumnsSlice40 contact00ColumnsSlice44
private theorem contact00ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact00) 48 8 = 6546624729530 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 4 4 3390963133090 3155661596440 contact00ColumnsSlice48 contact00ColumnsSlice52
private theorem contact00ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact00) 56 8 = 5639616264665 :=
  combineSlices (auxiliaryColumnSlice contact00) 56 4 4 2928909533279 2710706731386 contact00ColumnsSlice56 contact00ColumnsSlice60
private theorem contact00ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact00) 64 8 = 4801101930083 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 4 4 2501077609345 2300024320738 contact00ColumnsSlice64 contact00ColumnsSlice68
private theorem contact00ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact00) 72 8 = 4031100087814 :=
  combineSlices (auxiliaryColumnSlice contact00) 72 4 4 2107524783012 1923575304802 contact00ColumnsSlice72 contact00ColumnsSlice76
private theorem contact00ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact00) 80 8 = 3329527699736 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 4 4 1748174883190 1581352816546 contact00ColumnsSlice80 contact00ColumnsSlice84
private theorem contact00ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact00) 88 8 = 2696508012341 :=
  combineSlices (auxiliaryColumnSlice contact00) 88 4 4 1423102472529 1273405539812 contact00ColumnsSlice88 contact00ColumnsSlice92
private theorem contact00ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact00) 96 8 = 2131919791901 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 4 4 1132258604478 999661187423 contact00ColumnsSlice96 contact00ColumnsSlice100
private theorem contact00ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact00) 104 8 = 1635843904109 :=
  combineSlices (auxiliaryColumnSlice contact00) 104 4 4 875645649358 760198254751 contact00ColumnsSlice104 contact00ColumnsSlice108
private theorem contact00ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact00) 112 8 = 1208263299953 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 4 4 653303808573 554959491380 contact00ColumnsSlice112 contact00ColumnsSlice116
private theorem contact00ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact00) 120 8 = 849121711607 :=
  combineSlices (auxiliaryColumnSlice contact00) 120 4 4 465165724813 383955986794 contact00ColumnsSlice120 contact00ColumnsSlice124
private theorem contact00ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact00) 128 8 = 558531363963 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 4 4 311311567572 247219796391 contact00ColumnsSlice128 contact00ColumnsSlice132
private theorem contact00ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact00) 136 8 = 336234581521 :=
  combineSlices (auxiliaryColumnSlice contact00) 136 4 4 191670981497 144563600024 contact00ColumnsSlice136 contact00ColumnsSlice140
private theorem contact00ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact00) 144 8 = 179997131460 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 4 4 105628445076 74368686384 contact00ColumnsSlice144 contact00ColumnsSlice148
private theorem contact00ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact00) 152 8 = 82288329207 :=
  combineSlices (auxiliaryColumnSlice contact00) 152 4 4 50140556427 32147772780 contact00ColumnsSlice152 contact00ColumnsSlice156
private theorem contact00ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact00) 0 16 = 25534438591636 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 8 8 13426015168544 12108423423092 contact00ColumnsJoin0_8 contact00ColumnsJoin8_8
private theorem contact00ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact00) 16 16 = 20537530989579 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 8 8 10859176056205 9678354933374 contact00ColumnsJoin16_8 contact00ColumnsJoin24_8
private theorem contact00ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact00) 32 16 = 16088066322506 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 8 8 8566010683467 7522055639039 contact00ColumnsJoin32_8 contact00ColumnsJoin40_8
private theorem contact00ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact00) 48 16 = 12186240994195 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 8 8 6546624729530 5639616264665 contact00ColumnsJoin48_8 contact00ColumnsJoin56_8
private theorem contact00ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact00) 64 16 = 8832202017897 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 8 8 4801101930083 4031100087814 contact00ColumnsJoin64_8 contact00ColumnsJoin72_8
private theorem contact00ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact00) 80 16 = 6026035712077 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 8 8 3329527699736 2696508012341 contact00ColumnsJoin80_8 contact00ColumnsJoin88_8
private theorem contact00ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact00) 96 16 = 3767763696010 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 8 8 2131919791901 1635843904109 contact00ColumnsJoin96_8 contact00ColumnsJoin104_8
private theorem contact00ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact00) 112 16 = 2057385011560 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 8 8 1208263299953 849121711607 contact00ColumnsJoin112_8 contact00ColumnsJoin120_8
private theorem contact00ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact00) 128 16 = 894765945484 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 8 8 558531363963 336234581521 contact00ColumnsJoin128_8 contact00ColumnsJoin136_8
private theorem contact00ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact00) 144 16 = 262285460667 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 8 8 179997131460 82288329207 contact00ColumnsJoin144_8 contact00ColumnsJoin152_8
private theorem contact00ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact00) 0 32 = 46071969581215 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 16 16 25534438591636 20537530989579 contact00ColumnsJoin0_16 contact00ColumnsJoin16_16
private theorem contact00ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact00) 32 32 = 28274307316701 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 16 16 16088066322506 12186240994195 contact00ColumnsJoin32_16 contact00ColumnsJoin48_16
private theorem contact00ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact00) 64 32 = 14858237729974 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 16 16 8832202017897 6026035712077 contact00ColumnsJoin64_16 contact00ColumnsJoin80_16
private theorem contact00ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact00) 96 32 = 5825148707570 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 16 16 3767763696010 2057385011560 contact00ColumnsJoin96_16 contact00ColumnsJoin112_16
private theorem contact00ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact00) 128 32 = 1157051406151 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 16 16 894765945484 262285460667 contact00ColumnsJoin128_16 contact00ColumnsJoin144_16
private theorem contact00ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact00) 0 64 = 74346276897916 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 32 32 46071969581215 28274307316701 contact00ColumnsJoin0_32 contact00ColumnsJoin32_32
private theorem contact00ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact00) 64 64 = 20683386437544 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 32 32 14858237729974 5825148707570 contact00ColumnsJoin64_32 contact00ColumnsJoin96_32
private theorem contact00ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact00) 128 33 = 1162918850800 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 32 1 1157051406151 5867444649 contact00ColumnsJoin128_32 contact00ColumnsSlice160
private theorem contact00ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact00) 0 128 = 95029663335460 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 64 64 74346276897916 20683386437544 contact00ColumnsJoin0_64 contact00ColumnsJoin64_64
private theorem contact00ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact00) 0 161 = 96192582186260 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 128 33 95029663335460 1162918850800 contact00ColumnsJoin0_128 contact00ColumnsJoin128_33
private theorem contact00OrdinaryRanks : ordinaryRankBound contact00 = 9492608107 := by decide +kernel
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
  margin_of_checked_counts contact00 161 2468599665131471 96192582186260 9492608107 291293596 rfl contact00OrdinaryColumns contact00ColumnsJoin0_161 contact00OrdinaryRanks contact00RanksJoin0_161 (by decide +kernel)

private theorem contact02OrdinaryColumns : ordinaryColumnCount contact02 = 3597146375399756 := by decide +kernel
private theorem contact02ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact02) 0 4 = 11545923486636 :=
  contactColumnsWindow_fast contact02 0 4 11545923486636 (by decide +kernel)
private theorem contact02ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact02) 4 4 = 11029155218044 :=
  contactColumnsWindow_fast contact02 4 4 11029155218044 (by decide +kernel)
private theorem contact02ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact02) 8 4 = 10524282783116 :=
  contactColumnsWindow_fast contact02 8 4 10524282783116 (by decide +kernel)
private theorem contact02ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact02) 12 4 = 10031306181852 :=
  contactColumnsWindow_fast contact02 12 4 10031306181852 (by decide +kernel)
private theorem contact02ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact02) 16 4 = 9550225414252 :=
  contactColumnsWindow_fast contact02 16 4 9550225414252 (by decide +kernel)
private theorem contact02ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact02) 20 4 = 9081040480316 :=
  contactColumnsWindow_fast contact02 20 4 9081040480316 (by decide +kernel)
private theorem contact02ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact02) 24 4 = 8623751380044 :=
  contactColumnsWindow_fast contact02 24 4 8623751380044 (by decide +kernel)
private theorem contact02ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact02) 28 4 = 8178358113436 :=
  contactColumnsWindow_fast contact02 28 4 8178358113436 (by decide +kernel)
private theorem contact02ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact02) 32 4 = 7744860680492 :=
  contactColumnsWindow_fast contact02 32 4 7744860680492 (by decide +kernel)
private theorem contact02ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact02) 36 4 = 7323259081212 :=
  contactColumnsWindow_fast contact02 36 4 7323259081212 (by decide +kernel)
private theorem contact02ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact02) 40 4 = 6913553315596 :=
  contactColumnsWindow_fast contact02 40 4 6913553315596 (by decide +kernel)
private theorem contact02ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact02) 44 4 = 6515743383644 :=
  contactColumnsWindow_fast contact02 44 4 6515743383644 (by decide +kernel)
private theorem contact02ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact02) 48 4 = 6129829285356 :=
  contactColumnsWindow_fast contact02 48 4 6129829285356 (by decide +kernel)
private theorem contact02ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact02) 52 4 = 5755811020732 :=
  contactColumnsWindow_fast contact02 52 4 5755811020732 (by decide +kernel)
private theorem contact02ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact02) 56 4 = 5393695854822 :=
  contactColumnsWindow_fast contact02 56 4 5393695854822 (by decide +kernel)
private theorem contact02ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact02) 60 4 = 5043543175760 :=
  contactColumnsWindow_fast contact02 60 4 5043543175760 (by decide +kernel)
private theorem contact02ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact02) 64 4 = 4705302214414 :=
  contactColumnsWindow_fast contact02 64 4 4705302214414 (by decide +kernel)
private theorem contact02ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact02) 68 4 = 4378961813340 :=
  contactColumnsWindow_fast contact02 68 4 4378961813340 (by decide +kernel)
private theorem contact02ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact02) 72 4 = 4064519367451 :=
  contactColumnsWindow_fast contact02 72 4 4064519367451 (by decide +kernel)
private theorem contact02ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact02) 76 4 = 3761988811810 :=
  contactColumnsWindow_fast contact02 76 4 3761988811810 (by decide +kernel)
private theorem contact02ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact02) 80 4 = 3471423255735 :=
  contactColumnsWindow_fast contact02 80 4 3471423255735 (by decide +kernel)
private theorem contact02ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact02) 84 4 = 3192770078340 :=
  contactColumnsWindow_fast contact02 84 4 3192770078340 (by decide +kernel)
private theorem contact02ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact02) 88 4 = 2926020593916 :=
  contactColumnsWindow_fast contact02 88 4 2926020593916 (by decide +kernel)
private theorem contact02ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact02) 92 4 = 2671173125794 :=
  contactColumnsWindow_fast contact02 92 4 2671173125794 (by decide +kernel)
private theorem contact02ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact02) 96 4 = 2428245421730 :=
  contactColumnsWindow_fast contact02 96 4 2428245421730 (by decide +kernel)
private theorem contact02ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact02) 100 4 = 2197286279341 :=
  contactColumnsWindow_fast contact02 100 4 2197286279341 (by decide +kernel)
private theorem contact02ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact02) 104 4 = 1978240377293 :=
  contactColumnsWindow_fast contact02 104 4 1978240377293 (by decide +kernel)
private theorem contact02ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact02) 108 4 = 1771101130761 :=
  contactColumnsWindow_fast contact02 108 4 1771101130761 (by decide +kernel)
private theorem contact02ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact02) 112 4 = 1575869177813 :=
  contactColumnsWindow_fast contact02 112 4 1575869177813 (by decide +kernel)
private theorem contact02ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact02) 116 4 = 1392564338483 :=
  contactColumnsWindow_fast contact02 116 4 1392564338483 (by decide +kernel)
private theorem contact02ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact02) 120 4 = 1221225284290 :=
  contactColumnsWindow_fast contact02 120 4 1221225284290 (by decide +kernel)
private theorem contact02ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact02) 124 4 = 1061796963236 :=
  contactColumnsWindow_fast contact02 124 4 1061796963236 (by decide +kernel)
private theorem contact02ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact02) 128 4 = 914275412228 :=
  contactColumnsWindow_fast contact02 128 4 914275412228 (by decide +kernel)
private theorem contact02ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact02) 132 4 = 778661259859 :=
  contactColumnsWindow_fast contact02 132 4 778661259859 (by decide +kernel)
private theorem contact02ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact02) 136 4 = 654979689235 :=
  contactColumnsWindow_fast contact02 136 4 654979689235 (by decide +kernel)
private theorem contact02ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact02) 140 4 = 543260122642 :=
  contactColumnsWindow_fast contact02 140 4 543260122642 (by decide +kernel)
private theorem contact02ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact02) 144 4 = 443449427270 :=
  contactColumnsWindow_fast contact02 144 4 443449427270 (by decide +kernel)
private theorem contact02ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact02) 148 4 = 355520883704 :=
  contactColumnsWindow_fast contact02 148 4 355520883704 (by decide +kernel)
private theorem contact02ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact02) 152 4 = 279302440026 :=
  contactColumnsWindow_fast contact02 152 4 279302440026 (by decide +kernel)
private theorem contact02ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact02) 156 4 = 214449394948 :=
  contactColumnsWindow_fast contact02 156 4 214449394948 (by decide +kernel)
private theorem contact02ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact02) 160 4 = 160435411969 :=
  contactColumnsWindow_fast contact02 160 4 160435411969 (by decide +kernel)
private theorem contact02ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact02) 164 4 = 116502753426 :=
  contactColumnsWindow_fast contact02 164 4 116502753426 (by decide +kernel)
private theorem contact02ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact02) 168 4 = 81782376645 :=
  contactColumnsWindow_fast contact02 168 4 81782376645 (by decide +kernel)
private theorem contact02ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact02) 172 4 = 55245339261 :=
  contactColumnsWindow_fast contact02 172 4 55245339261 (by decide +kernel)
private theorem contact02ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact02) 0 8 = 22575078704680 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 4 4 11545923486636 11029155218044 contact02ColumnsSlice0 contact02ColumnsSlice4
private theorem contact02ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact02) 8 8 = 20555588964968 :=
  combineSlices (auxiliaryColumnSlice contact02) 8 4 4 10524282783116 10031306181852 contact02ColumnsSlice8 contact02ColumnsSlice12
private theorem contact02ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact02) 16 8 = 18631265894568 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 4 4 9550225414252 9081040480316 contact02ColumnsSlice16 contact02ColumnsSlice20
private theorem contact02ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact02) 24 8 = 16802109493480 :=
  combineSlices (auxiliaryColumnSlice contact02) 24 4 4 8623751380044 8178358113436 contact02ColumnsSlice24 contact02ColumnsSlice28
private theorem contact02ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact02) 32 8 = 15068119761704 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 4 4 7744860680492 7323259081212 contact02ColumnsSlice32 contact02ColumnsSlice36
private theorem contact02ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact02) 40 8 = 13429296699240 :=
  combineSlices (auxiliaryColumnSlice contact02) 40 4 4 6913553315596 6515743383644 contact02ColumnsSlice40 contact02ColumnsSlice44
private theorem contact02ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact02) 48 8 = 11885640306088 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 4 4 6129829285356 5755811020732 contact02ColumnsSlice48 contact02ColumnsSlice52
private theorem contact02ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact02) 56 8 = 10437239030582 :=
  combineSlices (auxiliaryColumnSlice contact02) 56 4 4 5393695854822 5043543175760 contact02ColumnsSlice56 contact02ColumnsSlice60
private theorem contact02ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact02) 64 8 = 9084264027754 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 4 4 4705302214414 4378961813340 contact02ColumnsSlice64 contact02ColumnsSlice68
private theorem contact02ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact02) 72 8 = 7826508179261 :=
  combineSlices (auxiliaryColumnSlice contact02) 72 4 4 4064519367451 3761988811810 contact02ColumnsSlice72 contact02ColumnsSlice76
private theorem contact02ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact02) 80 8 = 6664193334075 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 4 4 3471423255735 3192770078340 contact02ColumnsSlice80 contact02ColumnsSlice84
private theorem contact02ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact02) 88 8 = 5597193719710 :=
  combineSlices (auxiliaryColumnSlice contact02) 88 4 4 2926020593916 2671173125794 contact02ColumnsSlice88 contact02ColumnsSlice92
private theorem contact02ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact02) 96 8 = 4625531701071 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 4 4 2428245421730 2197286279341 contact02ColumnsSlice96 contact02ColumnsSlice100
private theorem contact02ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact02) 104 8 = 3749341508054 :=
  combineSlices (auxiliaryColumnSlice contact02) 104 4 4 1978240377293 1771101130761 contact02ColumnsSlice104 contact02ColumnsSlice108
private theorem contact02ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact02) 112 8 = 2968433516296 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 4 4 1575869177813 1392564338483 contact02ColumnsSlice112 contact02ColumnsSlice116
private theorem contact02ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact02) 120 8 = 2283022247526 :=
  combineSlices (auxiliaryColumnSlice contact02) 120 4 4 1221225284290 1061796963236 contact02ColumnsSlice120 contact02ColumnsSlice124
private theorem contact02ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact02) 128 8 = 1692936672087 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 4 4 914275412228 778661259859 contact02ColumnsSlice128 contact02ColumnsSlice132
private theorem contact02ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact02) 136 8 = 1198239811877 :=
  combineSlices (auxiliaryColumnSlice contact02) 136 4 4 654979689235 543260122642 contact02ColumnsSlice136 contact02ColumnsSlice140
private theorem contact02ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact02) 144 8 = 798970310974 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 4 4 443449427270 355520883704 contact02ColumnsSlice144 contact02ColumnsSlice148
private theorem contact02ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact02) 152 8 = 493751834974 :=
  combineSlices (auxiliaryColumnSlice contact02) 152 4 4 279302440026 214449394948 contact02ColumnsSlice152 contact02ColumnsSlice156
private theorem contact02ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact02) 160 8 = 276938165395 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 4 4 160435411969 116502753426 contact02ColumnsSlice160 contact02ColumnsSlice164
private theorem contact02ColumnsJoin168_8 : sliceWindow (auxiliaryColumnSlice contact02) 168 8 = 137027715906 :=
  combineSlices (auxiliaryColumnSlice contact02) 168 4 4 81782376645 55245339261 contact02ColumnsSlice168 contact02ColumnsSlice172
private theorem contact02ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact02) 0 16 = 43130667669648 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 8 8 22575078704680 20555588964968 contact02ColumnsJoin0_8 contact02ColumnsJoin8_8
private theorem contact02ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact02) 16 16 = 35433375388048 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 8 8 18631265894568 16802109493480 contact02ColumnsJoin16_8 contact02ColumnsJoin24_8
private theorem contact02ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact02) 32 16 = 28497416460944 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 8 8 15068119761704 13429296699240 contact02ColumnsJoin32_8 contact02ColumnsJoin40_8
private theorem contact02ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact02) 48 16 = 22322879336670 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 8 8 11885640306088 10437239030582 contact02ColumnsJoin48_8 contact02ColumnsJoin56_8
private theorem contact02ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact02) 64 16 = 16910772207015 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 8 8 9084264027754 7826508179261 contact02ColumnsJoin64_8 contact02ColumnsJoin72_8
private theorem contact02ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact02) 80 16 = 12261387053785 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 8 8 6664193334075 5597193719710 contact02ColumnsJoin80_8 contact02ColumnsJoin88_8
private theorem contact02ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact02) 96 16 = 8374873209125 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 8 8 4625531701071 3749341508054 contact02ColumnsJoin96_8 contact02ColumnsJoin104_8
private theorem contact02ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact02) 112 16 = 5251455763822 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 8 8 2968433516296 2283022247526 contact02ColumnsJoin112_8 contact02ColumnsJoin120_8
private theorem contact02ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact02) 128 16 = 2891176483964 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 8 8 1692936672087 1198239811877 contact02ColumnsJoin128_8 contact02ColumnsJoin136_8
private theorem contact02ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact02) 144 16 = 1292722145948 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 8 8 798970310974 493751834974 contact02ColumnsJoin144_8 contact02ColumnsJoin152_8
private theorem contact02ColumnsJoin160_16 : sliceWindow (auxiliaryColumnSlice contact02) 160 16 = 413965881301 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 8 8 276938165395 137027715906 contact02ColumnsJoin160_8 contact02ColumnsJoin168_8
private theorem contact02ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact02) 0 32 = 78564043057696 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 16 16 43130667669648 35433375388048 contact02ColumnsJoin0_16 contact02ColumnsJoin16_16
private theorem contact02ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact02) 32 32 = 50820295797614 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 16 16 28497416460944 22322879336670 contact02ColumnsJoin32_16 contact02ColumnsJoin48_16
private theorem contact02ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact02) 64 32 = 29172159260800 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 16 16 16910772207015 12261387053785 contact02ColumnsJoin64_16 contact02ColumnsJoin80_16
private theorem contact02ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact02) 96 32 = 13626328972947 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 16 16 8374873209125 5251455763822 contact02ColumnsJoin96_16 contact02ColumnsJoin112_16
private theorem contact02ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact02) 128 32 = 4183898629912 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 16 16 2891176483964 1292722145948 contact02ColumnsJoin128_16 contact02ColumnsJoin144_16
private theorem contact02ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact02) 0 64 = 129384338855310 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 32 32 78564043057696 50820295797614 contact02ColumnsJoin0_32 contact02ColumnsJoin32_32
private theorem contact02ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact02) 64 64 = 42798488233747 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 32 32 29172159260800 13626328972947 contact02ColumnsJoin64_32 contact02ColumnsJoin96_32
private theorem contact02ColumnsJoin128_48 : sliceWindow (auxiliaryColumnSlice contact02) 128 48 = 4597864511213 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 32 16 4183898629912 413965881301 contact02ColumnsJoin128_32 contact02ColumnsJoin160_16
private theorem contact02ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact02) 0 128 = 172182827089057 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 64 64 129384338855310 42798488233747 contact02ColumnsJoin0_64 contact02ColumnsJoin64_64
private theorem contact02ColumnsJoin0_176 : sliceWindow (auxiliaryColumnSlice contact02) 0 176 = 176780691600270 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 128 48 172182827089057 4597864511213 contact02ColumnsJoin0_128 contact02ColumnsJoin128_48
private theorem contact02OrdinaryRanks : ordinaryRankBound contact02 = 13856348361 := by decide +kernel
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
  margin_of_checked_counts contact02 176 3597146375399756 176780691600270 13856348361 540031017 rfl contact02OrdinaryColumns contact02ColumnsJoin0_176 contact02OrdinaryRanks contact02RanksJoin0_176 (by decide +kernel)

private theorem contact04OrdinaryColumns : ordinaryColumnCount contact04 = 1815709939543055 := by decide +kernel
private theorem contact04ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact04) 0 4 = 8026806254420 :=
  contactColumnsWindow_fast contact04 0 4 8026806254420 (by decide +kernel)
private theorem contact04ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact04) 4 4 = 7637716877396 :=
  contactColumnsWindow_fast contact04 4 4 7637716877396 (by decide +kernel)
private theorem contact04ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact04) 8 4 = 7258368309584 :=
  contactColumnsWindow_fast contact04 8 4 7258368309584 (by decide +kernel)
private theorem contact04ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact04) 12 4 = 6888758419701 :=
  contactColumnsWindow_fast contact04 12 4 6888758419701 (by decide +kernel)
private theorem contact04ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact04) 16 4 = 6528857426068 :=
  contactColumnsWindow_fast contact04 16 4 6528857426068 (by decide +kernel)
private theorem contact04ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact04) 20 4 = 6178666495772 :=
  contactColumnsWindow_fast contact04 20 4 6178666495772 (by decide +kernel)
private theorem contact04ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact04) 24 4 = 5838187790392 :=
  contactColumnsWindow_fast contact04 24 4 5838187790392 (by decide +kernel)
private theorem contact04ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact04) 28 4 = 5507458271930 :=
  contactColumnsWindow_fast contact04 28 4 5507458271930 (by decide +kernel)
private theorem contact04ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact04) 32 4 = 5186465881923 :=
  contactColumnsWindow_fast contact04 32 4 5186465881923 (by decide +kernel)
private theorem contact04ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact04) 36 4 = 4875184640872 :=
  contactColumnsWindow_fast contact04 36 4 4875184640872 (by decide +kernel)
private theorem contact04ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact04) 40 4 = 4573618500084 :=
  contactColumnsWindow_fast contact04 40 4 4573618500084 (by decide +kernel)
private theorem contact04ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact04) 44 4 = 4281767799042 :=
  contactColumnsWindow_fast contact04 44 4 4281767799042 (by decide +kernel)
private theorem contact04ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact04) 48 4 = 3999674731578 :=
  contactColumnsWindow_fast contact04 48 4 3999674731578 (by decide +kernel)
private theorem contact04ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact04) 52 4 = 3727316418605 :=
  contactColumnsWindow_fast contact04 52 4 3727316418605 (by decide +kernel)
private theorem contact04ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact04) 56 4 = 3464674097255 :=
  contactColumnsWindow_fast contact04 56 4 3464674097255 (by decide +kernel)
private theorem contact04ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact04) 60 4 = 3211747232116 :=
  contactColumnsWindow_fast contact04 60 4 3211747232116 (by decide +kernel)
private theorem contact04ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact04) 64 4 = 2968537133414 :=
  contactColumnsWindow_fast contact04 64 4 2968537133414 (by decide +kernel)
private theorem contact04ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact04) 68 4 = 2735087532834 :=
  contactColumnsWindow_fast contact04 68 4 2735087532834 (by decide +kernel)
private theorem contact04ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact04) 72 4 = 2511368499822 :=
  contactColumnsWindow_fast contact04 72 4 2511368499822 (by decide +kernel)
private theorem contact04ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact04) 76 4 = 2297365471393 :=
  contactColumnsWindow_fast contact04 76 4 2297365471393 (by decide +kernel)
private theorem contact04ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact04) 80 4 = 2093077679632 :=
  contactColumnsWindow_fast contact04 80 4 2093077679632 (by decide +kernel)
private theorem contact04ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact04) 84 4 = 1898508307269 :=
  contactColumnsWindow_fast contact04 84 4 1898508307269 (by decide +kernel)
private theorem contact04ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact04) 88 4 = 1713702138923 :=
  contactColumnsWindow_fast contact04 88 4 1713702138923 (by decide +kernel)
private theorem contact04ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact04) 92 4 = 1538622471198 :=
  contactColumnsWindow_fast contact04 92 4 1538622471198 (by decide +kernel)
private theorem contact04ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact04) 96 4 = 1373258555331 :=
  contactColumnsWindow_fast contact04 96 4 1373258555331 (by decide +kernel)
private theorem contact04ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact04) 100 4 = 1217609868840 :=
  contactColumnsWindow_fast contact04 100 4 1217609868840 (by decide +kernel)
private theorem contact04ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact04) 104 4 = 1071682767202 :=
  contactColumnsWindow_fast contact04 104 4 1071682767202 (by decide +kernel)
private theorem contact04ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact04) 108 4 = 935518501821 :=
  contactColumnsWindow_fast contact04 108 4 935518501821 (by decide +kernel)
private theorem contact04ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact04) 112 4 = 809078152374 :=
  contactColumnsWindow_fast contact04 112 4 809078152374 (by decide +kernel)
private theorem contact04ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact04) 116 4 = 692353484314 :=
  contactColumnsWindow_fast contact04 116 4 692353484314 (by decide +kernel)
private theorem contact04ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact04) 120 4 = 585343873100 :=
  contactColumnsWindow_fast contact04 120 4 585343873100 (by decide +kernel)
private theorem contact04ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact04) 124 4 = 488058964866 :=
  contactColumnsWindow_fast contact04 124 4 488058964866 (by decide +kernel)
private theorem contact04ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact04) 128 4 = 400536657047 :=
  contactColumnsWindow_fast contact04 128 4 400536657047 (by decide +kernel)
private theorem contact04ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact04) 132 4 = 322735648623 :=
  contactColumnsWindow_fast contact04 132 4 322735648623 (by decide +kernel)
private theorem contact04ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact04) 136 4 = 254644192076 :=
  contactColumnsWindow_fast contact04 136 4 254644192076 (by decide +kernel)
private theorem contact04ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact04) 140 4 = 196164769758 :=
  contactColumnsWindow_fast contact04 140 4 196164769758 (by decide +kernel)
private theorem contact04ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact04) 144 4 = 147018736557 :=
  contactColumnsWindow_fast contact04 144 4 147018736557 (by decide +kernel)
private theorem contact04ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact04) 148 4 = 106772491060 :=
  contactColumnsWindow_fast contact04 148 4 106772491060 (by decide +kernel)
private theorem contact04ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact04) 152 4 = 74755173353 :=
  contactColumnsWindow_fast contact04 152 4 74755173353 (by decide +kernel)
private theorem contact04ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact04) 156 4 = 50173953768 :=
  contactColumnsWindow_fast contact04 156 4 50173953768 (by decide +kernel)
private theorem contact04ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact04) 160 1 = 9485731516 :=
  contactColumnsWindow_fast contact04 160 1 9485731516 (by decide +kernel)
private theorem contact04ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact04) 0 8 = 15664523131816 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 4 4 8026806254420 7637716877396 contact04ColumnsSlice0 contact04ColumnsSlice4
private theorem contact04ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact04) 8 8 = 14147126729285 :=
  combineSlices (auxiliaryColumnSlice contact04) 8 4 4 7258368309584 6888758419701 contact04ColumnsSlice8 contact04ColumnsSlice12
private theorem contact04ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact04) 16 8 = 12707523921840 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 4 4 6528857426068 6178666495772 contact04ColumnsSlice16 contact04ColumnsSlice20
private theorem contact04ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact04) 24 8 = 11345646062322 :=
  combineSlices (auxiliaryColumnSlice contact04) 24 4 4 5838187790392 5507458271930 contact04ColumnsSlice24 contact04ColumnsSlice28
private theorem contact04ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact04) 32 8 = 10061650522795 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 4 4 5186465881923 4875184640872 contact04ColumnsSlice32 contact04ColumnsSlice36
private theorem contact04ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact04) 40 8 = 8855386299126 :=
  combineSlices (auxiliaryColumnSlice contact04) 40 4 4 4573618500084 4281767799042 contact04ColumnsSlice40 contact04ColumnsSlice44
private theorem contact04ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact04) 48 8 = 7726991150183 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 4 4 3999674731578 3727316418605 contact04ColumnsSlice48 contact04ColumnsSlice52
private theorem contact04ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact04) 56 8 = 6676421329371 :=
  combineSlices (auxiliaryColumnSlice contact04) 56 4 4 3464674097255 3211747232116 contact04ColumnsSlice56 contact04ColumnsSlice60
private theorem contact04ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact04) 64 8 = 5703624666248 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 4 4 2968537133414 2735087532834 contact04ColumnsSlice64 contact04ColumnsSlice68
private theorem contact04ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact04) 72 8 = 4808733971215 :=
  combineSlices (auxiliaryColumnSlice contact04) 72 4 4 2511368499822 2297365471393 contact04ColumnsSlice72 contact04ColumnsSlice76
private theorem contact04ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact04) 80 8 = 3991585986901 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 4 4 2093077679632 1898508307269 contact04ColumnsSlice80 contact04ColumnsSlice84
private theorem contact04ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact04) 88 8 = 3252324610121 :=
  combineSlices (auxiliaryColumnSlice contact04) 88 4 4 1713702138923 1538622471198 contact04ColumnsSlice88 contact04ColumnsSlice92
private theorem contact04ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact04) 96 8 = 2590868424171 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 4 4 1373258555331 1217609868840 contact04ColumnsSlice96 contact04ColumnsSlice100
private theorem contact04ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact04) 104 8 = 2007201269023 :=
  combineSlices (auxiliaryColumnSlice contact04) 104 4 4 1071682767202 935518501821 contact04ColumnsSlice104 contact04ColumnsSlice108
private theorem contact04ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact04) 112 8 = 1501431636688 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 4 4 809078152374 692353484314 contact04ColumnsSlice112 contact04ColumnsSlice116
private theorem contact04ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact04) 120 8 = 1073402837966 :=
  combineSlices (auxiliaryColumnSlice contact04) 120 4 4 585343873100 488058964866 contact04ColumnsSlice120 contact04ColumnsSlice124
private theorem contact04ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact04) 128 8 = 723272305670 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 4 4 400536657047 322735648623 contact04ColumnsSlice128 contact04ColumnsSlice132
private theorem contact04ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact04) 136 8 = 450808961834 :=
  combineSlices (auxiliaryColumnSlice contact04) 136 4 4 254644192076 196164769758 contact04ColumnsSlice136 contact04ColumnsSlice140
private theorem contact04ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact04) 144 8 = 253791227617 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 4 4 147018736557 106772491060 contact04ColumnsSlice144 contact04ColumnsSlice148
private theorem contact04ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact04) 152 8 = 124929127121 :=
  combineSlices (auxiliaryColumnSlice contact04) 152 4 4 74755173353 50173953768 contact04ColumnsSlice152 contact04ColumnsSlice156
private theorem contact04ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact04) 0 16 = 29811649861101 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 8 8 15664523131816 14147126729285 contact04ColumnsJoin0_8 contact04ColumnsJoin8_8
private theorem contact04ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact04) 16 16 = 24053169984162 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 8 8 12707523921840 11345646062322 contact04ColumnsJoin16_8 contact04ColumnsJoin24_8
private theorem contact04ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact04) 32 16 = 18917036821921 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 8 8 10061650522795 8855386299126 contact04ColumnsJoin32_8 contact04ColumnsJoin40_8
private theorem contact04ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact04) 48 16 = 14403412479554 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 8 8 7726991150183 6676421329371 contact04ColumnsJoin48_8 contact04ColumnsJoin56_8
private theorem contact04ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact04) 64 16 = 10512358637463 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 8 8 5703624666248 4808733971215 contact04ColumnsJoin64_8 contact04ColumnsJoin72_8
private theorem contact04ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact04) 80 16 = 7243910597022 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 8 8 3991585986901 3252324610121 contact04ColumnsJoin80_8 contact04ColumnsJoin88_8
private theorem contact04ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact04) 96 16 = 4598069693194 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 8 8 2590868424171 2007201269023 contact04ColumnsJoin96_8 contact04ColumnsJoin104_8
private theorem contact04ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact04) 112 16 = 2574834474654 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 8 8 1501431636688 1073402837966 contact04ColumnsJoin112_8 contact04ColumnsJoin120_8
private theorem contact04ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact04) 128 16 = 1174081267504 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 8 8 723272305670 450808961834 contact04ColumnsJoin128_8 contact04ColumnsJoin136_8
private theorem contact04ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact04) 144 16 = 378720354738 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 8 8 253791227617 124929127121 contact04ColumnsJoin144_8 contact04ColumnsJoin152_8
private theorem contact04ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact04) 0 32 = 53864819845263 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 16 16 29811649861101 24053169984162 contact04ColumnsJoin0_16 contact04ColumnsJoin16_16
private theorem contact04ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact04) 32 32 = 33320449301475 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 16 16 18917036821921 14403412479554 contact04ColumnsJoin32_16 contact04ColumnsJoin48_16
private theorem contact04ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact04) 64 32 = 17756269234485 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 16 16 10512358637463 7243910597022 contact04ColumnsJoin64_16 contact04ColumnsJoin80_16
private theorem contact04ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact04) 96 32 = 7172904167848 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 16 16 4598069693194 2574834474654 contact04ColumnsJoin96_16 contact04ColumnsJoin112_16
private theorem contact04ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact04) 128 32 = 1552801622242 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 16 16 1174081267504 378720354738 contact04ColumnsJoin128_16 contact04ColumnsJoin144_16
private theorem contact04ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact04) 0 64 = 87185269146738 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 32 32 53864819845263 33320449301475 contact04ColumnsJoin0_32 contact04ColumnsJoin32_32
private theorem contact04ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact04) 64 64 = 24929173402333 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 32 32 17756269234485 7172904167848 contact04ColumnsJoin64_32 contact04ColumnsJoin96_32
private theorem contact04ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact04) 128 33 = 1562287353758 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 32 1 1552801622242 9485731516 contact04ColumnsJoin128_32 contact04ColumnsSlice160
private theorem contact04ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact04) 0 128 = 112114442549071 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 64 64 87185269146738 24929173402333 contact04ColumnsJoin0_64 contact04ColumnsJoin64_64
private theorem contact04ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact04) 0 161 = 113676729902829 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 128 33 112114442549071 1562287353758 contact04ColumnsJoin0_128 contact04ColumnsJoin128_33
private theorem contact04OrdinaryRanks : ordinaryRankBound contact04 = 7014098497 := by decide +kernel
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
  margin_of_checked_counts contact04 161 1815709939543055 113676729902829 7014098497 345924093 rfl contact04OrdinaryColumns contact04ColumnsJoin0_161 contact04OrdinaryRanks contact04RanksJoin0_161 (by decide +kernel)

private theorem contact06OrdinaryColumns : ordinaryColumnCount contact06 = 2055584577555503 := by decide +kernel
private theorem contact06ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact06) 0 4 = 7926662149594 :=
  contactColumnsWindow_fast contact06 0 4 7926662149594 (by decide +kernel)
private theorem contact06ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact06) 4 4 = 7546435005786 :=
  contactColumnsWindow_fast contact06 4 4 7546435005786 (by decide +kernel)
private theorem contact06ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact06) 8 4 = 7175592281134 :=
  contactColumnsWindow_fast contact06 8 4 7175592281134 (by decide +kernel)
private theorem contact06ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact06) 12 4 = 6814134150039 :=
  contactColumnsWindow_fast contact06 12 4 6814134150039 (by decide +kernel)
private theorem contact06ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact06) 16 4 = 6462096542122 :=
  contactColumnsWindow_fast contact06 16 4 6462096542122 (by decide +kernel)
private theorem contact06ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact06) 20 4 = 6119465105141 :=
  contactColumnsWindow_fast contact06 20 4 6119465105141 (by decide +kernel)
private theorem contact06ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact06) 24 4 = 5786221992478 :=
  contactColumnsWindow_fast contact06 24 4 5786221992478 (by decide +kernel)
private theorem contact06ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact06) 28 4 = 5462365719520 :=
  contactColumnsWindow_fast contact06 28 4 5462365719520 (by decide +kernel)
private theorem contact06ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact06) 32 4 = 5147899364654 :=
  contactColumnsWindow_fast contact06 32 4 5147899364654 (by decide +kernel)
private theorem contact06ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact06) 36 4 = 4842858216724 :=
  contactColumnsWindow_fast contact06 36 4 4842858216724 (by decide +kernel)
private theorem contact06ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact06) 40 4 = 4547224201186 :=
  contactColumnsWindow_fast contact06 40 4 4547224201186 (by decide +kernel)
private theorem contact06ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact06) 44 4 = 4260980453572 :=
  contactColumnsWindow_fast contact06 44 4 4260980453572 (by decide +kernel)
private theorem contact06ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact06) 48 4 = 3984128280530 :=
  contactColumnsWindow_fast contact06 48 4 3984128280530 (by decide +kernel)
private theorem contact06ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact06) 52 4 = 3716669465598 :=
  contactColumnsWindow_fast contact06 52 4 3716669465598 (by decide +kernel)
private theorem contact06ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact06) 56 4 = 3458643017714 :=
  contactColumnsWindow_fast contact06 56 4 3458643017714 (by decide +kernel)
private theorem contact06ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact06) 60 4 = 3210023166396 :=
  contactColumnsWindow_fast contact06 60 4 3210023166396 (by decide +kernel)
private theorem contact06ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact06) 64 4 = 2970797245790 :=
  contactColumnsWindow_fast contact06 64 4 2970797245790 (by decide +kernel)
private theorem contact06ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact06) 68 4 = 2740962855272 :=
  contactColumnsWindow_fast contact06 68 4 2740962855272 (by decide +kernel)
private theorem contact06ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact06) 72 4 = 2520523928446 :=
  contactColumnsWindow_fast contact06 72 4 2520523928446 (by decide +kernel)
private theorem contact06ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact06) 76 4 = 2309518604080 :=
  contactColumnsWindow_fast contact06 76 4 2309518604080 (by decide +kernel)
private theorem contact06ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact06) 80 4 = 2107917123046 :=
  contactColumnsWindow_fast contact06 80 4 2107917123046 (by decide +kernel)
private theorem contact06ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact06) 84 4 = 1915709034487 :=
  contactColumnsWindow_fast contact06 84 4 1915709034487 (by decide +kernel)
private theorem contact06ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact06) 88 4 = 1732892506354 :=
  contactColumnsWindow_fast contact06 88 4 1732892506354 (by decide +kernel)
private theorem contact06ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact06) 92 4 = 1559474161672 :=
  contactColumnsWindow_fast contact06 92 4 1559474161672 (by decide +kernel)
private theorem contact06ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact06) 96 4 = 1395489176586 :=
  contactColumnsWindow_fast contact06 96 4 1395489176586 (by decide +kernel)
private theorem contact06ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact06) 100 4 = 1240906096099 :=
  contactColumnsWindow_fast contact06 100 4 1240906096099 (by decide +kernel)
private theorem contact06ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact06) 104 4 = 1095716036986 :=
  contactColumnsWindow_fast contact06 104 4 1095716036986 (by decide +kernel)
private theorem contact06ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact06) 108 4 = 959917188071 :=
  contactColumnsWindow_fast contact06 108 4 959917188071 (by decide +kernel)
private theorem contact06ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact06) 112 4 = 833519381038 :=
  contactColumnsWindow_fast contact06 112 4 833519381038 (by decide +kernel)
private theorem contact06ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact06) 116 4 = 716555011756 :=
  contactColumnsWindow_fast contact06 116 4 716555011756 (by decide +kernel)
private theorem contact06ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact06) 120 4 = 608990154826 :=
  contactColumnsWindow_fast contact06 120 4 608990154826 (by decide +kernel)
private theorem contact06ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact06) 124 4 = 510818052116 :=
  contactColumnsWindow_fast contact06 124 4 510818052116 (by decide +kernel)
private theorem contact06ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact06) 128 4 = 422036934679 :=
  contactColumnsWindow_fast contact06 128 4 422036934679 (by decide +kernel)
private theorem contact06ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact06) 132 4 = 342660695395 :=
  contactColumnsWindow_fast contact06 132 4 342660695395 (by decide +kernel)
private theorem contact06ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact06) 136 4 = 272715765450 :=
  contactColumnsWindow_fast contact06 136 4 272715765450 (by decide +kernel)
private theorem contact06ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact06) 140 4 = 212141391752 :=
  contactColumnsWindow_fast contact06 140 4 212141391752 (by decide +kernel)
private theorem contact06ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact06) 144 4 = 160750697497 :=
  contactColumnsWindow_fast contact06 144 4 160750697497 (by decide +kernel)
private theorem contact06ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact06) 148 4 = 118167603969 :=
  contactColumnsWindow_fast contact06 148 4 118167603969 (by decide +kernel)
private theorem contact06ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact06) 152 4 = 83874152524 :=
  contactColumnsWindow_fast contact06 152 4 83874152524 (by decide +kernel)
private theorem contact06ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact06) 156 4 = 57187310911 :=
  contactColumnsWindow_fast contact06 156 4 57187310911 (by decide +kernel)
private theorem contact06ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact06) 160 4 = 37213320557 :=
  contactColumnsWindow_fast contact06 160 4 37213320557 (by decide +kernel)
private theorem contact06ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact06) 164 1 = 6873640211 :=
  contactColumnsWindow_fast contact06 164 1 6873640211 (by decide +kernel)
private theorem contact06ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact06) 0 8 = 15473097155380 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 4 4 7926662149594 7546435005786 contact06ColumnsSlice0 contact06ColumnsSlice4
private theorem contact06ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact06) 8 8 = 13989726431173 :=
  combineSlices (auxiliaryColumnSlice contact06) 8 4 4 7175592281134 6814134150039 contact06ColumnsSlice8 contact06ColumnsSlice12
private theorem contact06ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact06) 16 8 = 12581561647263 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 4 4 6462096542122 6119465105141 contact06ColumnsSlice16 contact06ColumnsSlice20
private theorem contact06ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact06) 24 8 = 11248587711998 :=
  combineSlices (auxiliaryColumnSlice contact06) 24 4 4 5786221992478 5462365719520 contact06ColumnsSlice24 contact06ColumnsSlice28
private theorem contact06ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact06) 32 8 = 9990757581378 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 4 4 5147899364654 4842858216724 contact06ColumnsSlice32 contact06ColumnsSlice36
private theorem contact06ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact06) 40 8 = 8808204654758 :=
  combineSlices (auxiliaryColumnSlice contact06) 40 4 4 4547224201186 4260980453572 contact06ColumnsSlice40 contact06ColumnsSlice44
private theorem contact06ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact06) 48 8 = 7700797746128 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 4 4 3984128280530 3716669465598 contact06ColumnsSlice48 contact06ColumnsSlice52
private theorem contact06ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact06) 56 8 = 6668666184110 :=
  combineSlices (auxiliaryColumnSlice contact06) 56 4 4 3458643017714 3210023166396 contact06ColumnsSlice56 contact06ColumnsSlice60
private theorem contact06ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact06) 64 8 = 5711760101062 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 4 4 2970797245790 2740962855272 contact06ColumnsSlice64 contact06ColumnsSlice68
private theorem contact06ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact06) 72 8 = 4830042532526 :=
  combineSlices (auxiliaryColumnSlice contact06) 72 4 4 2520523928446 2309518604080 contact06ColumnsSlice72 contact06ColumnsSlice76
private theorem contact06ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact06) 80 8 = 4023626157533 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 4 4 2107917123046 1915709034487 contact06ColumnsSlice80 contact06ColumnsSlice84
private theorem contact06ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact06) 88 8 = 3292366668026 :=
  combineSlices (auxiliaryColumnSlice contact06) 88 4 4 1732892506354 1559474161672 contact06ColumnsSlice88 contact06ColumnsSlice92
private theorem contact06ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact06) 96 8 = 2636395272685 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 4 4 1395489176586 1240906096099 contact06ColumnsSlice96 contact06ColumnsSlice100
private theorem contact06ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact06) 104 8 = 2055633225057 :=
  combineSlices (auxiliaryColumnSlice contact06) 104 4 4 1095716036986 959917188071 contact06ColumnsSlice104 contact06ColumnsSlice108
private theorem contact06ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact06) 112 8 = 1550074392794 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 4 4 833519381038 716555011756 contact06ColumnsSlice112 contact06ColumnsSlice116
private theorem contact06ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact06) 120 8 = 1119808206942 :=
  combineSlices (auxiliaryColumnSlice contact06) 120 4 4 608990154826 510818052116 contact06ColumnsSlice120 contact06ColumnsSlice124
private theorem contact06ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact06) 128 8 = 764697630074 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 4 4 422036934679 342660695395 contact06ColumnsSlice128 contact06ColumnsSlice132
private theorem contact06ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact06) 136 8 = 484857157202 :=
  combineSlices (auxiliaryColumnSlice contact06) 136 4 4 272715765450 212141391752 contact06ColumnsSlice136 contact06ColumnsSlice140
private theorem contact06ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact06) 144 8 = 278918301466 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 4 4 160750697497 118167603969 contact06ColumnsSlice144 contact06ColumnsSlice148
private theorem contact06ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact06) 152 8 = 141061463435 :=
  combineSlices (auxiliaryColumnSlice contact06) 152 4 4 83874152524 57187310911 contact06ColumnsSlice152 contact06ColumnsSlice156
private theorem contact06ColumnsJoin160_5 : sliceWindow (auxiliaryColumnSlice contact06) 160 5 = 44086960768 :=
  combineSlices (auxiliaryColumnSlice contact06) 160 4 1 37213320557 6873640211 contact06ColumnsSlice160 contact06ColumnsSlice164
private theorem contact06ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact06) 0 16 = 29462823586553 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 8 8 15473097155380 13989726431173 contact06ColumnsJoin0_8 contact06ColumnsJoin8_8
private theorem contact06ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact06) 16 16 = 23830149359261 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 8 8 12581561647263 11248587711998 contact06ColumnsJoin16_8 contact06ColumnsJoin24_8
private theorem contact06ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact06) 32 16 = 18798962236136 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 8 8 9990757581378 8808204654758 contact06ColumnsJoin32_8 contact06ColumnsJoin40_8
private theorem contact06ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact06) 48 16 = 14369463930238 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 8 8 7700797746128 6668666184110 contact06ColumnsJoin48_8 contact06ColumnsJoin56_8
private theorem contact06ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact06) 64 16 = 10541802633588 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 8 8 5711760101062 4830042532526 contact06ColumnsJoin64_8 contact06ColumnsJoin72_8
private theorem contact06ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact06) 80 16 = 7315992825559 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 8 8 4023626157533 3292366668026 contact06ColumnsJoin80_8 contact06ColumnsJoin88_8
private theorem contact06ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact06) 96 16 = 4692028497742 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 8 8 2636395272685 2055633225057 contact06ColumnsJoin96_8 contact06ColumnsJoin104_8
private theorem contact06ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact06) 112 16 = 2669882599736 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 8 8 1550074392794 1119808206942 contact06ColumnsJoin112_8 contact06ColumnsJoin120_8
private theorem contact06ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact06) 128 16 = 1249554787276 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 8 8 764697630074 484857157202 contact06ColumnsJoin128_8 contact06ColumnsJoin136_8
private theorem contact06ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact06) 144 16 = 419979764901 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 8 8 278918301466 141061463435 contact06ColumnsJoin144_8 contact06ColumnsJoin152_8
private theorem contact06ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact06) 0 32 = 53292972945814 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 16 16 29462823586553 23830149359261 contact06ColumnsJoin0_16 contact06ColumnsJoin16_16
private theorem contact06ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact06) 32 32 = 33168426166374 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 16 16 18798962236136 14369463930238 contact06ColumnsJoin32_16 contact06ColumnsJoin48_16
private theorem contact06ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact06) 64 32 = 17857795459147 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 16 16 10541802633588 7315992825559 contact06ColumnsJoin64_16 contact06ColumnsJoin80_16
private theorem contact06ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact06) 96 32 = 7361911097478 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 16 16 4692028497742 2669882599736 contact06ColumnsJoin96_16 contact06ColumnsJoin112_16
private theorem contact06ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact06) 128 32 = 1669534552177 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 16 16 1249554787276 419979764901 contact06ColumnsJoin128_16 contact06ColumnsJoin144_16
private theorem contact06ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact06) 0 64 = 86461399112188 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 32 32 53292972945814 33168426166374 contact06ColumnsJoin0_32 contact06ColumnsJoin32_32
private theorem contact06ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact06) 64 64 = 25219706556625 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 32 32 17857795459147 7361911097478 contact06ColumnsJoin64_32 contact06ColumnsJoin96_32
private theorem contact06ColumnsJoin128_37 : sliceWindow (auxiliaryColumnSlice contact06) 128 37 = 1713621512945 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 32 5 1669534552177 44086960768 contact06ColumnsJoin128_32 contact06ColumnsJoin160_5
private theorem contact06ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact06) 0 128 = 111681105668813 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 64 64 86461399112188 25219706556625 contact06ColumnsJoin0_64 contact06ColumnsJoin64_64
private theorem contact06ColumnsJoin0_165 : sliceWindow (auxiliaryColumnSlice contact06) 0 165 = 113394727181758 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 128 37 111681105668813 1713621512945 contact06ColumnsJoin0_128 contact06ColumnsJoin128_37
private theorem contact06OrdinaryRanks : ordinaryRankBound contact06 = 7929961726 := by decide +kernel
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
private theorem contact06RanksSlice152 : sliceWindow (auxiliaryRankSlice contact06) 152 13 = 0 :=
  contactRankWindow_of_rec contact06 152 13 0 (by decide +kernel)
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
private theorem contact06RanksJoin144_21 : sliceWindow (auxiliaryRankSlice contact06) 144 21 = 18497 :=
  combineSlices (auxiliaryRankSlice contact06) 144 8 13 18497 0 contact06RanksJoin144_8 contact06RanksSlice152
private theorem contact06RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact06) 0 32 = 190296960 :=
  combineSlices (auxiliaryRankSlice contact06) 0 16 16 108530240 81766720 contact06RanksJoin0_16 contact06RanksJoin16_16
private theorem contact06RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact06) 32 32 = 99868647 :=
  combineSlices (auxiliaryRankSlice contact06) 32 16 16 59160640 40708007 contact06RanksJoin32_16 contact06RanksJoin48_16
private theorem contact06RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact06) 64 32 = 41845999 :=
  combineSlices (auxiliaryRankSlice contact06) 64 16 16 26293583 15552416 contact06RanksJoin64_16 contact06RanksJoin80_16
private theorem contact06RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact06) 96 32 = 11266304 :=
  combineSlices (auxiliaryRankSlice contact06) 96 16 16 8024065 3242239 contact06RanksJoin96_16 contact06RanksJoin112_16
private theorem contact06RanksJoin128_37 : sliceWindow (auxiliaryRankSlice contact06) 128 37 = 759172 :=
  combineSlices (auxiliaryRankSlice contact06) 128 16 21 740675 18497 contact06RanksJoin128_16 contact06RanksJoin144_21
private theorem contact06RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact06) 0 64 = 290165607 :=
  combineSlices (auxiliaryRankSlice contact06) 0 32 32 190296960 99868647 contact06RanksJoin0_32 contact06RanksJoin32_32
private theorem contact06RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact06) 64 64 = 53112303 :=
  combineSlices (auxiliaryRankSlice contact06) 64 32 32 41845999 11266304 contact06RanksJoin64_32 contact06RanksJoin96_32
private theorem contact06RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact06) 0 128 = 343277910 :=
  combineSlices (auxiliaryRankSlice contact06) 0 64 64 290165607 53112303 contact06RanksJoin0_64 contact06RanksJoin64_64
private theorem contact06RanksJoin0_165 : sliceWindow (auxiliaryRankSlice contact06) 0 165 = 344037082 :=
  combineSlices (auxiliaryRankSlice contact06) 0 128 37 343277910 759172 contact06RanksJoin0_128 contact06RanksJoin128_37
theorem contact06_margin : sourceMargin contact06 :=
  margin_of_checked_counts contact06 165 2055584577555503 113394727181758 7929961726 344037082 rfl contact06OrdinaryColumns contact06ColumnsJoin0_165 contact06OrdinaryRanks contact06RanksJoin0_165 (by decide +kernel)

private theorem contact08OrdinaryColumns : ordinaryColumnCount contact08 = 2028411615571947 := by decide +kernel
private theorem contact08ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact08) 0 4 = 8338991030494 :=
  contactColumnsWindow_fast contact08 0 4 8338991030494 (by decide +kernel)
private theorem contact08ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact08) 4 4 = 7936822508142 :=
  contactColumnsWindow_fast contact08 4 4 7936822508142 (by decide +kernel)
private theorem contact08ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact08) 8 4 = 7544639314670 :=
  contactColumnsWindow_fast contact08 8 4 7544639314670 (by decide +kernel)
private theorem contact08ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact08) 12 4 = 7162441646583 :=
  contactColumnsWindow_fast contact08 12 4 7162441646583 (by decide +kernel)
private theorem contact08ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact08) 16 4 = 6790268629714 :=
  contactColumnsWindow_fast contact08 16 4 6790268629714 (by decide +kernel)
private theorem contact08ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact08) 20 4 = 6428104570224 :=
  contactColumnsWindow_fast contact08 20 4 6428104570224 (by decide +kernel)
private theorem contact08ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact08) 24 4 = 6075929896782 :=
  contactColumnsWindow_fast contact08 24 4 6075929896782 (by decide +kernel)
private theorem contact08ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact08) 28 4 = 5733743064990 :=
  contactColumnsWindow_fast contact08 28 4 5733743064990 (by decide +kernel)
private theorem contact08ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact08) 32 4 = 5401547343751 :=
  contactColumnsWindow_fast contact08 32 4 5401547343751 (by decide +kernel)
private theorem contact08ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact08) 36 4 = 5079381264966 :=
  contactColumnsWindow_fast contact08 36 4 5079381264966 (by decide +kernel)
private theorem contact08ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact08) 40 4 = 4767224929727 :=
  contactColumnsWindow_fast contact08 40 4 4767224929727 (by decide +kernel)
private theorem contact08ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact08) 44 4 = 4465059988346 :=
  contactColumnsWindow_fast contact08 44 4 4465059988346 (by decide +kernel)
private theorem contact08ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact08) 48 4 = 4172887785352 :=
  contactColumnsWindow_fast contact08 48 4 4172887785352 (by decide +kernel)
private theorem contact08ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact08) 52 4 = 3890710316969 :=
  contactColumnsWindow_fast contact08 52 4 3890710316969 (by decide +kernel)
private theorem contact08ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact08) 56 4 = 3618570034368 :=
  contactColumnsWindow_fast contact08 56 4 3618570034368 (by decide +kernel)
private theorem contact08ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact08) 60 4 = 3356438721198 :=
  contactColumnsWindow_fast contact08 60 4 3356438721198 (by decide +kernel)
private theorem contact08ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact08) 64 4 = 3104302577908 :=
  contactColumnsWindow_fast contact08 64 4 3104302577908 (by decide +kernel)
private theorem contact08ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact08) 68 4 = 2862159128266 :=
  contactColumnsWindow_fast contact08 68 4 2862159128266 (by decide +kernel)
private theorem contact08ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact08) 72 4 = 2630012696536 :=
  contactColumnsWindow_fast contact08 72 4 2630012696536 (by decide +kernel)
private theorem contact08ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact08) 76 4 = 2407904800770 :=
  contactColumnsWindow_fast contact08 76 4 2407904800770 (by decide +kernel)
private theorem contact08ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact08) 80 4 = 2195802848304 :=
  contactColumnsWindow_fast contact08 80 4 2195802848304 (by decide +kernel)
private theorem contact08ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact08) 84 4 = 1993695508260 :=
  contactColumnsWindow_fast contact08 84 4 1993695508260 (by decide +kernel)
private theorem contact08ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact08) 88 4 = 1801580894683 :=
  contactColumnsWindow_fast contact08 88 4 1801580894683 (by decide +kernel)
private theorem contact08ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact08) 92 4 = 1619466252704 :=
  contactColumnsWindow_fast contact08 92 4 1619466252704 (by decide +kernel)
private theorem contact08ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact08) 96 4 = 1447389897252 :=
  contactColumnsWindow_fast contact08 96 4 1447389897252 (by decide +kernel)
private theorem contact08ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact08) 100 4 = 1285317336840 :=
  contactColumnsWindow_fast contact08 100 4 1285317336840 (by decide +kernel)
private theorem contact08ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact08) 104 4 = 1133239004820 :=
  contactColumnsWindow_fast contact08 104 4 1133239004820 (by decide +kernel)
private theorem contact08ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact08) 108 4 = 991153037350 :=
  contactColumnsWindow_fast contact08 108 4 991153037350 (by decide +kernel)
private theorem contact08ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact08) 112 4 = 859070138952 :=
  contactColumnsWindow_fast contact08 112 4 859070138952 (by decide +kernel)
private theorem contact08ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact08) 116 4 = 737025609929 :=
  contactColumnsWindow_fast contact08 116 4 737025609929 (by decide +kernel)
private theorem contact08ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact08) 120 4 = 624982258801 :=
  contactColumnsWindow_fast contact08 120 4 624982258801 (by decide +kernel)
private theorem contact08ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact08) 124 4 = 522932858910 :=
  contactColumnsWindow_fast contact08 124 4 522932858910 (by decide +kernel)
private theorem contact08ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact08) 128 4 = 430875591367 :=
  contactColumnsWindow_fast contact08 128 4 430875591367 (by decide +kernel)
private theorem contact08ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact08) 132 4 = 348825558449 :=
  contactColumnsWindow_fast contact08 132 4 348825558449 (by decide +kernel)
private theorem contact08ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact08) 136 4 = 276807788233 :=
  contactColumnsWindow_fast contact08 136 4 276807788233 (by decide +kernel)
private theorem contact08ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact08) 140 4 = 214702519482 :=
  contactColumnsWindow_fast contact08 140 4 214702519482 (by decide +kernel)
private theorem contact08ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact08) 144 4 = 162224190307 :=
  contactColumnsWindow_fast contact08 144 4 162224190307 (by decide +kernel)
private theorem contact08ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact08) 148 4 = 118920255107 :=
  contactColumnsWindow_fast contact08 148 4 118920255107 (by decide +kernel)
private theorem contact08ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact08) 152 4 = 84196485407 :=
  contactColumnsWindow_fast contact08 152 4 84196485407 (by decide +kernel)
private theorem contact08ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact08) 156 4 = 57292376659 :=
  contactColumnsWindow_fast contact08 156 4 57292376659 (by decide +kernel)
private theorem contact08ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact08) 160 3 = 29471993151 :=
  contactColumnsWindow_fast contact08 160 3 29471993151 (by decide +kernel)
private theorem contact08ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact08) 0 8 = 16275813538636 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 4 4 8338991030494 7936822508142 contact08ColumnsSlice0 contact08ColumnsSlice4
private theorem contact08ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact08) 8 8 = 14707080961253 :=
  combineSlices (auxiliaryColumnSlice contact08) 8 4 4 7544639314670 7162441646583 contact08ColumnsSlice8 contact08ColumnsSlice12
private theorem contact08ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact08) 16 8 = 13218373199938 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 4 4 6790268629714 6428104570224 contact08ColumnsSlice16 contact08ColumnsSlice20
private theorem contact08ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact08) 24 8 = 11809672961772 :=
  combineSlices (auxiliaryColumnSlice contact08) 24 4 4 6075929896782 5733743064990 contact08ColumnsSlice24 contact08ColumnsSlice28
private theorem contact08ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact08) 32 8 = 10480928608717 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 4 4 5401547343751 5079381264966 contact08ColumnsSlice32 contact08ColumnsSlice36
private theorem contact08ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact08) 40 8 = 9232284918073 :=
  combineSlices (auxiliaryColumnSlice contact08) 40 4 4 4767224929727 4465059988346 contact08ColumnsSlice40 contact08ColumnsSlice44
private theorem contact08ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact08) 48 8 = 8063598102321 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 4 4 4172887785352 3890710316969 contact08ColumnsSlice48 contact08ColumnsSlice52
private theorem contact08ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact08) 56 8 = 6975008755566 :=
  combineSlices (auxiliaryColumnSlice contact08) 56 4 4 3618570034368 3356438721198 contact08ColumnsSlice56 contact08ColumnsSlice60
private theorem contact08ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact08) 64 8 = 5966461706174 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 4 4 3104302577908 2862159128266 contact08ColumnsSlice64 contact08ColumnsSlice68
private theorem contact08ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact08) 72 8 = 5037917497306 :=
  combineSlices (auxiliaryColumnSlice contact08) 72 4 4 2630012696536 2407904800770 contact08ColumnsSlice72 contact08ColumnsSlice76
private theorem contact08ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact08) 80 8 = 4189498356564 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 4 4 2195802848304 1993695508260 contact08ColumnsSlice80 contact08ColumnsSlice84
private theorem contact08ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact08) 88 8 = 3421047147387 :=
  combineSlices (auxiliaryColumnSlice contact08) 88 4 4 1801580894683 1619466252704 contact08ColumnsSlice88 contact08ColumnsSlice92
private theorem contact08ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact08) 96 8 = 2732707234092 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 4 4 1447389897252 1285317336840 contact08ColumnsSlice96 contact08ColumnsSlice100
private theorem contact08ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact08) 104 8 = 2124392042170 :=
  combineSlices (auxiliaryColumnSlice contact08) 104 4 4 1133239004820 991153037350 contact08ColumnsSlice104 contact08ColumnsSlice108
private theorem contact08ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact08) 112 8 = 1596095748881 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 4 4 859070138952 737025609929 contact08ColumnsSlice112 contact08ColumnsSlice116
private theorem contact08ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact08) 120 8 = 1147915117711 :=
  combineSlices (auxiliaryColumnSlice contact08) 120 4 4 624982258801 522932858910 contact08ColumnsSlice120 contact08ColumnsSlice124
private theorem contact08ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact08) 128 8 = 779701149816 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 4 4 430875591367 348825558449 contact08ColumnsSlice128 contact08ColumnsSlice132
private theorem contact08ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact08) 136 8 = 491510307715 :=
  combineSlices (auxiliaryColumnSlice contact08) 136 4 4 276807788233 214702519482 contact08ColumnsSlice136 contact08ColumnsSlice140
private theorem contact08ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact08) 144 8 = 281144445414 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 4 4 162224190307 118920255107 contact08ColumnsSlice144 contact08ColumnsSlice148
private theorem contact08ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact08) 152 8 = 141488862066 :=
  combineSlices (auxiliaryColumnSlice contact08) 152 4 4 84196485407 57292376659 contact08ColumnsSlice152 contact08ColumnsSlice156
private theorem contact08ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact08) 0 16 = 30982894499889 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 8 8 16275813538636 14707080961253 contact08ColumnsJoin0_8 contact08ColumnsJoin8_8
private theorem contact08ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact08) 16 16 = 25028046161710 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 8 8 13218373199938 11809672961772 contact08ColumnsJoin16_8 contact08ColumnsJoin24_8
private theorem contact08ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact08) 32 16 = 19713213526790 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 8 8 10480928608717 9232284918073 contact08ColumnsJoin32_8 contact08ColumnsJoin40_8
private theorem contact08ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact08) 48 16 = 15038606857887 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 8 8 8063598102321 6975008755566 contact08ColumnsJoin48_8 contact08ColumnsJoin56_8
private theorem contact08ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact08) 64 16 = 11004379203480 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 8 8 5966461706174 5037917497306 contact08ColumnsJoin64_8 contact08ColumnsJoin72_8
private theorem contact08ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact08) 80 16 = 7610545503951 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 8 8 4189498356564 3421047147387 contact08ColumnsJoin80_8 contact08ColumnsJoin88_8
private theorem contact08ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact08) 96 16 = 4857099276262 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 8 8 2732707234092 2124392042170 contact08ColumnsJoin96_8 contact08ColumnsJoin104_8
private theorem contact08ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact08) 112 16 = 2744010866592 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 8 8 1596095748881 1147915117711 contact08ColumnsJoin112_8 contact08ColumnsJoin120_8
private theorem contact08ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact08) 128 16 = 1271211457531 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 8 8 779701149816 491510307715 contact08ColumnsJoin128_8 contact08ColumnsJoin136_8
private theorem contact08ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact08) 144 16 = 422633307480 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 8 8 281144445414 141488862066 contact08ColumnsJoin144_8 contact08ColumnsJoin152_8
private theorem contact08ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact08) 0 32 = 56010940661599 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 16 16 30982894499889 25028046161710 contact08ColumnsJoin0_16 contact08ColumnsJoin16_16
private theorem contact08ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact08) 32 32 = 34751820384677 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 16 16 19713213526790 15038606857887 contact08ColumnsJoin32_16 contact08ColumnsJoin48_16
private theorem contact08ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact08) 64 32 = 18614924707431 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 16 16 11004379203480 7610545503951 contact08ColumnsJoin64_16 contact08ColumnsJoin80_16
private theorem contact08ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact08) 96 32 = 7601110142854 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 16 16 4857099276262 2744010866592 contact08ColumnsJoin96_16 contact08ColumnsJoin112_16
private theorem contact08ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact08) 128 32 = 1693844765011 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 16 16 1271211457531 422633307480 contact08ColumnsJoin128_16 contact08ColumnsJoin144_16
private theorem contact08ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact08) 0 64 = 90762761046276 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 32 32 56010940661599 34751820384677 contact08ColumnsJoin0_32 contact08ColumnsJoin32_32
private theorem contact08ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact08) 64 64 = 26216034850285 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 32 32 18614924707431 7601110142854 contact08ColumnsJoin64_32 contact08ColumnsJoin96_32
private theorem contact08ColumnsJoin128_35 : sliceWindow (auxiliaryColumnSlice contact08) 128 35 = 1723316758162 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 32 3 1693844765011 29471993151 contact08ColumnsJoin128_32 contact08ColumnsSlice160
private theorem contact08ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact08) 0 128 = 116978795896561 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 64 64 90762761046276 26216034850285 contact08ColumnsJoin0_64 contact08ColumnsJoin64_64
private theorem contact08ColumnsJoin0_163 : sliceWindow (auxiliaryColumnSlice contact08) 0 163 = 118702112654723 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 128 35 116978795896561 1723316758162 contact08ColumnsJoin0_128 contact08ColumnsJoin128_35
private theorem contact08OrdinaryRanks : ordinaryRankBound contact08 = 7828819548 := by decide +kernel
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
private theorem contact08RanksSlice152 : sliceWindow (auxiliaryRankSlice contact08) 152 11 = 0 :=
  contactRankWindow_of_rec contact08 152 11 0 (by decide +kernel)
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
private theorem contact08RanksJoin144_19 : sliceWindow (auxiliaryRankSlice contact08) 144 19 = 19439 :=
  combineSlices (auxiliaryRankSlice contact08) 144 8 11 19439 0 contact08RanksJoin144_8 contact08RanksSlice152
private theorem contact08RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact08) 0 32 = 200059968 :=
  combineSlices (auxiliaryRankSlice contact08) 0 16 16 114130464 85929504 contact08RanksJoin0_16 contact08RanksJoin16_16
private theorem contact08RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact08) 32 32 = 104940520 :=
  combineSlices (auxiliaryRankSlice contact08) 32 16 16 62152224 42788296 contact08RanksJoin32_16 contact08RanksJoin48_16
private theorem contact08RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact08) 64 32 = 44064098 :=
  combineSlices (auxiliaryRankSlice contact08) 64 16 16 27671826 16392272 contact08RanksJoin64_16 contact08RanksJoin80_16
private theorem contact08RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact08) 96 32 = 11900728 :=
  combineSlices (auxiliaryRankSlice contact08) 96 16 16 8471654 3429074 contact08RanksJoin96_16 contact08RanksJoin112_16
private theorem contact08RanksJoin128_35 : sliceWindow (auxiliaryRankSlice contact08) 128 35 = 803180 :=
  combineSlices (auxiliaryRankSlice contact08) 128 16 19 783741 19439 contact08RanksJoin128_16 contact08RanksJoin144_19
private theorem contact08RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact08) 0 64 = 305000488 :=
  combineSlices (auxiliaryRankSlice contact08) 0 32 32 200059968 104940520 contact08RanksJoin0_32 contact08RanksJoin32_32
private theorem contact08RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact08) 64 64 = 55964826 :=
  combineSlices (auxiliaryRankSlice contact08) 64 32 32 44064098 11900728 contact08RanksJoin64_32 contact08RanksJoin96_32
private theorem contact08RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact08) 0 128 = 360965314 :=
  combineSlices (auxiliaryRankSlice contact08) 0 64 64 305000488 55964826 contact08RanksJoin0_64 contact08RanksJoin64_64
private theorem contact08RanksJoin0_163 : sliceWindow (auxiliaryRankSlice contact08) 0 163 = 361768494 :=
  combineSlices (auxiliaryRankSlice contact08) 0 128 35 360965314 803180 contact08RanksJoin0_128 contact08RanksJoin128_35
theorem contact08_margin : sourceMargin contact08 :=
  margin_of_checked_counts contact08 163 2028411615571947 118702112654723 7828819548 361768494 rfl contact08OrdinaryColumns contact08ColumnsJoin0_163 contact08OrdinaryRanks contact08RanksJoin0_163 (by decide +kernel)

private theorem contact10OrdinaryColumns : ordinaryColumnCount contact10 = 3764826654441018 := by decide +kernel
private theorem contact10ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact10) 0 4 = 10383768562344 :=
  contactColumnsWindow_fast contact10 0 4 10383768562344 (by decide +kernel)
private theorem contact10ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact10) 4 4 = 9907393569896 :=
  contactColumnsWindow_fast contact10 4 4 9907393569896 (by decide +kernel)
private theorem contact10ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact10) 8 4 = 9442258153000 :=
  contactColumnsWindow_fast contact10 8 4 9442258153000 (by decide +kernel)
private theorem contact10ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact10) 12 4 = 8988362311656 :=
  contactColumnsWindow_fast contact10 12 4 8988362311656 (by decide +kernel)
private theorem contact10ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact10) 16 4 = 8545706045864 :=
  contactColumnsWindow_fast contact10 16 4 8545706045864 (by decide +kernel)
private theorem contact10ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact10) 20 4 = 8114289355624 :=
  contactColumnsWindow_fast contact10 20 4 8114289355624 (by decide +kernel)
private theorem contact10ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact10) 24 4 = 7694112240936 :=
  contactColumnsWindow_fast contact10 24 4 7694112240936 (by decide +kernel)
private theorem contact10ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact10) 28 4 = 7285206691800 :=
  contactColumnsWindow_fast contact10 28 4 7285206691800 (by decide +kernel)
private theorem contact10ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact10) 32 4 = 6887591510616 :=
  contactColumnsWindow_fast contact10 32 4 6887591510616 (by decide +kernel)
private theorem contact10ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact10) 36 4 = 6501219061872 :=
  contactColumnsWindow_fast contact10 36 4 6501219061872 (by decide +kernel)
private theorem contact10ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact10) 40 4 = 6126089160070 :=
  contactColumnsWindow_fast contact10 40 4 6126089160070 (by decide +kernel)
private theorem contact10ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact10) 44 4 = 5762202852192 :=
  contactColumnsWindow_fast contact10 44 4 5762202852192 (by decide +kernel)
private theorem contact10ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact10) 48 4 = 5409598201484 :=
  contactColumnsWindow_fast contact10 48 4 5409598201484 (by decide +kernel)
private theorem contact10ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact10) 52 4 = 5068280910612 :=
  contactColumnsWindow_fast contact10 52 4 5068280910612 (by decide +kernel)
private theorem contact10ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact10) 56 4 = 4738209137704 :=
  contactColumnsWindow_fast contact10 56 4 4738209137704 (by decide +kernel)
private theorem contact10ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact10) 60 4 = 4419384544913 :=
  contactColumnsWindow_fast contact10 60 4 4419384544913 (by decide +kernel)
private theorem contact10ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact10) 64 4 = 4111805992208 :=
  contactColumnsWindow_fast contact10 64 4 4111805992208 (by decide +kernel)
private theorem contact10ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact10) 68 4 = 3815521611769 :=
  contactColumnsWindow_fast contact10 68 4 3815521611769 (by decide +kernel)
private theorem contact10ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact10) 72 4 = 3530519747252 :=
  contactColumnsWindow_fast contact10 72 4 3530519747252 (by decide +kernel)
private theorem contact10ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact10) 76 4 = 3256768766030 :=
  contactColumnsWindow_fast contact10 76 4 3256768766030 (by decide +kernel)
private theorem contact10ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact10) 80 4 = 2994267420732 :=
  contactColumnsWindow_fast contact10 80 4 2994267420732 (by decide +kernel)
private theorem contact10ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact10) 84 4 = 2743018041970 :=
  contactColumnsWindow_fast contact10 84 4 2743018041970 (by decide +kernel)
private theorem contact10ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact10) 88 4 = 2503068856660 :=
  contactColumnsWindow_fast contact10 88 4 2503068856660 (by decide +kernel)
private theorem contact10ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact10) 92 4 = 2274395690914 :=
  contactColumnsWindow_fast contact10 92 4 2274395690914 (by decide +kernel)
private theorem contact10ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact10) 96 4 = 2056973367144 :=
  contactColumnsWindow_fast contact10 96 4 2056973367144 (by decide +kernel)
private theorem contact10ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact10) 100 4 = 1850800874490 :=
  contactColumnsWindow_fast contact10 100 4 1850800874490 (by decide +kernel)
private theorem contact10ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact10) 104 4 = 1655882113108 :=
  contactColumnsWindow_fast contact10 104 4 1655882113108 (by decide +kernel)
private theorem contact10ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact10) 108 4 = 1472266845702 :=
  contactColumnsWindow_fast contact10 108 4 1472266845702 (by decide +kernel)
private theorem contact10ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact10) 112 4 = 1299922392324 :=
  contactColumnsWindow_fast contact10 112 4 1299922392324 (by decide +kernel)
private theorem contact10ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact10) 116 4 = 1138828817689 :=
  contactColumnsWindow_fast contact10 116 4 1138828817689 (by decide +kernel)
private theorem contact10ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact10) 120 4 = 988985257116 :=
  contactColumnsWindow_fast contact10 120 4 988985257116 (by decide +kernel)
private theorem contact10ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact10) 124 4 = 850396926262 :=
  contactColumnsWindow_fast contact10 124 4 850396926262 (by decide +kernel)
private theorem contact10ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact10) 128 4 = 723115615556 :=
  contactColumnsWindow_fast contact10 128 4 723115615556 (by decide +kernel)
private theorem contact10ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact10) 132 4 = 607100097966 :=
  contactColumnsWindow_fast contact10 132 4 607100097966 (by decide +kernel)
private theorem contact10ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact10) 136 4 = 502335057122 :=
  contactColumnsWindow_fast contact10 136 4 502335057122 (by decide +kernel)
private theorem contact10ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact10) 140 4 = 408820356181 :=
  contactColumnsWindow_fast contact10 140 4 408820356181 (by decide +kernel)
private theorem contact10ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact10) 144 4 = 326549150730 :=
  contactColumnsWindow_fast contact10 144 4 326549150730 (by decide +kernel)
private theorem contact10ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact10) 148 4 = 255431133636 :=
  contactColumnsWindow_fast contact10 148 4 255431133636 (by decide +kernel)
private theorem contact10ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact10) 152 4 = 195074265634 :=
  contactColumnsWindow_fast contact10 152 4 195074265634 (by decide +kernel)
private theorem contact10ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact10) 156 4 = 144949635245 :=
  contactColumnsWindow_fast contact10 156 4 144949635245 (by decide +kernel)
private theorem contact10ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact10) 160 4 = 104378603789 :=
  contactColumnsWindow_fast contact10 160 4 104378603789 (by decide +kernel)
private theorem contact10ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact10) 164 4 = 72528180934 :=
  contactColumnsWindow_fast contact10 164 4 72528180934 (by decide +kernel)
private theorem contact10ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact10) 168 4 = 48420221582 :=
  contactColumnsWindow_fast contact10 168 4 48420221582 (by decide +kernel)
private theorem contact10ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact10) 172 1 = 9132086075 :=
  contactColumnsWindow_fast contact10 172 1 9132086075 (by decide +kernel)
private theorem contact10ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact10) 0 8 = 20291162132240 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 4 4 10383768562344 9907393569896 contact10ColumnsSlice0 contact10ColumnsSlice4
private theorem contact10ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact10) 8 8 = 18430620464656 :=
  combineSlices (auxiliaryColumnSlice contact10) 8 4 4 9442258153000 8988362311656 contact10ColumnsSlice8 contact10ColumnsSlice12
private theorem contact10ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact10) 16 8 = 16659995401488 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 4 4 8545706045864 8114289355624 contact10ColumnsSlice16 contact10ColumnsSlice20
private theorem contact10ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact10) 24 8 = 14979318932736 :=
  combineSlices (auxiliaryColumnSlice contact10) 24 4 4 7694112240936 7285206691800 contact10ColumnsSlice24 contact10ColumnsSlice28
private theorem contact10ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact10) 32 8 = 13388810572488 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 4 4 6887591510616 6501219061872 contact10ColumnsSlice32 contact10ColumnsSlice36
private theorem contact10ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact10) 40 8 = 11888292012262 :=
  combineSlices (auxiliaryColumnSlice contact10) 40 4 4 6126089160070 5762202852192 contact10ColumnsSlice40 contact10ColumnsSlice44
private theorem contact10ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact10) 48 8 = 10477879112096 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 4 4 5409598201484 5068280910612 contact10ColumnsSlice48 contact10ColumnsSlice52
private theorem contact10ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact10) 56 8 = 9157593682617 :=
  combineSlices (auxiliaryColumnSlice contact10) 56 4 4 4738209137704 4419384544913 contact10ColumnsSlice56 contact10ColumnsSlice60
private theorem contact10ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact10) 64 8 = 7927327603977 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 4 4 4111805992208 3815521611769 contact10ColumnsSlice64 contact10ColumnsSlice68
private theorem contact10ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact10) 72 8 = 6787288513282 :=
  combineSlices (auxiliaryColumnSlice contact10) 72 4 4 3530519747252 3256768766030 contact10ColumnsSlice72 contact10ColumnsSlice76
private theorem contact10ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact10) 80 8 = 5737285462702 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 4 4 2994267420732 2743018041970 contact10ColumnsSlice80 contact10ColumnsSlice84
private theorem contact10ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact10) 88 8 = 4777464547574 :=
  combineSlices (auxiliaryColumnSlice contact10) 88 4 4 2503068856660 2274395690914 contact10ColumnsSlice88 contact10ColumnsSlice92
private theorem contact10ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact10) 96 8 = 3907774241634 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 4 4 2056973367144 1850800874490 contact10ColumnsSlice96 contact10ColumnsSlice100
private theorem contact10ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact10) 104 8 = 3128148958810 :=
  combineSlices (auxiliaryColumnSlice contact10) 104 4 4 1655882113108 1472266845702 contact10ColumnsSlice104 contact10ColumnsSlice108
private theorem contact10ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact10) 112 8 = 2438751210013 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 4 4 1299922392324 1138828817689 contact10ColumnsSlice112 contact10ColumnsSlice116
private theorem contact10ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact10) 120 8 = 1839382183378 :=
  combineSlices (auxiliaryColumnSlice contact10) 120 4 4 988985257116 850396926262 contact10ColumnsSlice120 contact10ColumnsSlice124
private theorem contact10ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact10) 128 8 = 1330215713522 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 4 4 723115615556 607100097966 contact10ColumnsSlice128 contact10ColumnsSlice132
private theorem contact10ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact10) 136 8 = 911155413303 :=
  combineSlices (auxiliaryColumnSlice contact10) 136 4 4 502335057122 408820356181 contact10ColumnsSlice136 contact10ColumnsSlice140
private theorem contact10ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact10) 144 8 = 581980284366 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 4 4 326549150730 255431133636 contact10ColumnsSlice144 contact10ColumnsSlice148
private theorem contact10ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact10) 152 8 = 340023900879 :=
  combineSlices (auxiliaryColumnSlice contact10) 152 4 4 195074265634 144949635245 contact10ColumnsSlice152 contact10ColumnsSlice156
private theorem contact10ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact10) 160 8 = 176906784723 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 4 4 104378603789 72528180934 contact10ColumnsSlice160 contact10ColumnsSlice164
private theorem contact10ColumnsJoin168_5 : sliceWindow (auxiliaryColumnSlice contact10) 168 5 = 57552307657 :=
  combineSlices (auxiliaryColumnSlice contact10) 168 4 1 48420221582 9132086075 contact10ColumnsSlice168 contact10ColumnsSlice172
private theorem contact10ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact10) 0 16 = 38721782596896 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 8 8 20291162132240 18430620464656 contact10ColumnsJoin0_8 contact10ColumnsJoin8_8
private theorem contact10ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact10) 16 16 = 31639314334224 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 8 8 16659995401488 14979318932736 contact10ColumnsJoin16_8 contact10ColumnsJoin24_8
private theorem contact10ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact10) 32 16 = 25277102584750 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 8 8 13388810572488 11888292012262 contact10ColumnsJoin32_8 contact10ColumnsJoin40_8
private theorem contact10ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact10) 48 16 = 19635472794713 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 8 8 10477879112096 9157593682617 contact10ColumnsJoin48_8 contact10ColumnsJoin56_8
private theorem contact10ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact10) 64 16 = 14714616117259 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 8 8 7927327603977 6787288513282 contact10ColumnsJoin64_8 contact10ColumnsJoin72_8
private theorem contact10ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact10) 80 16 = 10514750010276 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 8 8 5737285462702 4777464547574 contact10ColumnsJoin80_8 contact10ColumnsJoin88_8
private theorem contact10ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact10) 96 16 = 7035923200444 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 8 8 3907774241634 3128148958810 contact10ColumnsJoin96_8 contact10ColumnsJoin104_8
private theorem contact10ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact10) 112 16 = 4278133393391 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 8 8 2438751210013 1839382183378 contact10ColumnsJoin112_8 contact10ColumnsJoin120_8
private theorem contact10ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact10) 128 16 = 2241371126825 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 8 8 1330215713522 911155413303 contact10ColumnsJoin128_8 contact10ColumnsJoin136_8
private theorem contact10ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact10) 144 16 = 922004185245 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 8 8 581980284366 340023900879 contact10ColumnsJoin144_8 contact10ColumnsJoin152_8
private theorem contact10ColumnsJoin160_13 : sliceWindow (auxiliaryColumnSlice contact10) 160 13 = 234459092380 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 8 5 176906784723 57552307657 contact10ColumnsJoin160_8 contact10ColumnsJoin168_5
private theorem contact10ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact10) 0 32 = 70361096931120 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 16 16 38721782596896 31639314334224 contact10ColumnsJoin0_16 contact10ColumnsJoin16_16
private theorem contact10ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact10) 32 32 = 44912575379463 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 16 16 25277102584750 19635472794713 contact10ColumnsJoin32_16 contact10ColumnsJoin48_16
private theorem contact10ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact10) 64 32 = 25229366127535 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 16 16 14714616117259 10514750010276 contact10ColumnsJoin64_16 contact10ColumnsJoin80_16
private theorem contact10ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact10) 96 32 = 11314056593835 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 16 16 7035923200444 4278133393391 contact10ColumnsJoin96_16 contact10ColumnsJoin112_16
private theorem contact10ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact10) 128 32 = 3163375312070 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 16 16 2241371126825 922004185245 contact10ColumnsJoin128_16 contact10ColumnsJoin144_16
private theorem contact10ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact10) 0 64 = 115273672310583 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 32 32 70361096931120 44912575379463 contact10ColumnsJoin0_32 contact10ColumnsJoin32_32
private theorem contact10ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact10) 64 64 = 36543422721370 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 32 32 25229366127535 11314056593835 contact10ColumnsJoin64_32 contact10ColumnsJoin96_32
private theorem contact10ColumnsJoin128_45 : sliceWindow (auxiliaryColumnSlice contact10) 128 45 = 3397834404450 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 32 13 3163375312070 234459092380 contact10ColumnsJoin128_32 contact10ColumnsJoin160_13
private theorem contact10ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact10) 0 128 = 151817095031953 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 64 64 115273672310583 36543422721370 contact10ColumnsJoin0_64 contact10ColumnsJoin64_64
private theorem contact10ColumnsJoin0_173 : sliceWindow (auxiliaryColumnSlice contact10) 0 173 = 155214929436403 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 128 45 151817095031953 3397834404450 contact10ColumnsJoin0_128 contact10ColumnsJoin128_45
private theorem contact10OrdinaryRanks : ordinaryRankBound contact10 = 14479533990 := by decide +kernel
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
  margin_of_checked_counts contact10 173 3764826654441018 155214929436403 14479533990 474228070 rfl contact10OrdinaryColumns contact10ColumnsJoin0_173 contact10OrdinaryRanks contact10RanksJoin0_173 (by decide +kernel)

private theorem contact12OrdinaryColumns : ordinaryColumnCount contact12 = 177679305039527 := by decide +kernel
private theorem contact12ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact12) 0 4 = 1141136499400 :=
  contactColumnsWindow_fast contact12 0 4 1141136499400 (by decide +kernel)
private theorem contact12ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact12) 4 4 = 1049394307832 :=
  contactColumnsWindow_fast contact12 4 4 1049394307832 (by decide +kernel)
private theorem contact12ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact12) 8 4 = 961519686266 :=
  contactColumnsWindow_fast contact12 8 4 961519686266 (by decide +kernel)
private theorem contact12ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact12) 12 4 = 877511419376 :=
  contactColumnsWindow_fast contact12 12 4 877511419376 (by decide +kernel)
private theorem contact12ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact12) 16 4 = 797368303607 :=
  contactColumnsWindow_fast contact12 16 4 797368303607 (by decide +kernel)
private theorem contact12ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact12) 20 4 = 721098227132 :=
  contactColumnsWindow_fast contact12 20 4 721098227132 (by decide +kernel)
private theorem contact12ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact12) 24 4 = 648717640996 :=
  contactColumnsWindow_fast contact12 24 4 648717640996 (by decide +kernel)
private theorem contact12ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact12) 28 4 = 580205953490 :=
  contactColumnsWindow_fast contact12 28 4 580205953490 (by decide +kernel)
private theorem contact12ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact12) 32 4 = 515560444332 :=
  contactColumnsWindow_fast contact12 32 4 515560444332 (by decide +kernel)
private theorem contact12ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact12) 36 4 = 454780320808 :=
  contactColumnsWindow_fast contact12 36 4 454780320808 (by decide +kernel)
private theorem contact12ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact12) 40 4 = 397875196960 :=
  contactColumnsWindow_fast contact12 40 4 397875196960 (by decide +kernel)
private theorem contact12ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact12) 44 4 = 344858416728 :=
  contactColumnsWindow_fast contact12 44 4 344858416728 (by decide +kernel)
private theorem contact12ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact12) 48 4 = 295709666000 :=
  contactColumnsWindow_fast contact12 48 4 295709666000 (by decide +kernel)
private theorem contact12ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact12) 52 4 = 250426911856 :=
  contactColumnsWindow_fast contact12 52 4 250426911856 (by decide +kernel)
private theorem contact12ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact12) 56 4 = 209009830148 :=
  contactColumnsWindow_fast contact12 56 4 209009830148 (by decide +kernel)
private theorem contact12ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact12) 60 4 = 171469626776 :=
  contactColumnsWindow_fast contact12 60 4 171469626776 (by decide +kernel)
private theorem contact12ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact12) 64 4 = 137816635028 :=
  contactColumnsWindow_fast contact12 64 4 137816635028 (by decide +kernel)
private theorem contact12ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact12) 68 4 = 108030906524 :=
  contactColumnsWindow_fast contact12 68 4 108030906524 (by decide +kernel)
private theorem contact12ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact12) 72 4 = 82110821948 :=
  contactColumnsWindow_fast contact12 72 4 82110821948 (by decide +kernel)
private theorem contact12ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact12) 76 4 = 60056782056 :=
  contactColumnsWindow_fast contact12 76 4 60056782056 (by decide +kernel)
private theorem contact12ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact12) 80 4 = 41880892300 :=
  contactColumnsWindow_fast contact12 80 4 41880892300 (by decide +kernel)
private theorem contact12ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact12) 84 4 = 27542871597 :=
  contactColumnsWindow_fast contact12 84 4 27542871597 (by decide +kernel)
private theorem contact12ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact12) 88 4 = 16827227759 :=
  contactColumnsWindow_fast contact12 88 4 16827227759 (by decide +kernel)
private theorem contact12ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact12) 92 4 = 9367967964 :=
  contactColumnsWindow_fast contact12 92 4 9367967964 (by decide +kernel)
private theorem contact12ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact12) 96 1 = 1510355443 :=
  contactColumnsWindow_fast contact12 96 1 1510355443 (by decide +kernel)
private theorem contact12ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact12) 0 8 = 2190530807232 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 4 4 1141136499400 1049394307832 contact12ColumnsSlice0 contact12ColumnsSlice4
private theorem contact12ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact12) 8 8 = 1839031105642 :=
  combineSlices (auxiliaryColumnSlice contact12) 8 4 4 961519686266 877511419376 contact12ColumnsSlice8 contact12ColumnsSlice12
private theorem contact12ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact12) 16 8 = 1518466530739 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 4 4 797368303607 721098227132 contact12ColumnsSlice16 contact12ColumnsSlice20
private theorem contact12ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact12) 24 8 = 1228923594486 :=
  combineSlices (auxiliaryColumnSlice contact12) 24 4 4 648717640996 580205953490 contact12ColumnsSlice24 contact12ColumnsSlice28
private theorem contact12ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact12) 32 8 = 970340765140 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 4 4 515560444332 454780320808 contact12ColumnsSlice32 contact12ColumnsSlice36
private theorem contact12ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact12) 40 8 = 742733613688 :=
  combineSlices (auxiliaryColumnSlice contact12) 40 4 4 397875196960 344858416728 contact12ColumnsSlice40 contact12ColumnsSlice44
private theorem contact12ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact12) 48 8 = 546136577856 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 4 4 295709666000 250426911856 contact12ColumnsSlice48 contact12ColumnsSlice52
private theorem contact12ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact12) 56 8 = 380479456924 :=
  combineSlices (auxiliaryColumnSlice contact12) 56 4 4 209009830148 171469626776 contact12ColumnsSlice56 contact12ColumnsSlice60
private theorem contact12ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact12) 64 8 = 245847541552 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 4 4 137816635028 108030906524 contact12ColumnsSlice64 contact12ColumnsSlice68
private theorem contact12ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact12) 72 8 = 142167604004 :=
  combineSlices (auxiliaryColumnSlice contact12) 72 4 4 82110821948 60056782056 contact12ColumnsSlice72 contact12ColumnsSlice76
private theorem contact12ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact12) 80 8 = 69423763897 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 4 4 41880892300 27542871597 contact12ColumnsSlice80 contact12ColumnsSlice84
private theorem contact12ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact12) 88 8 = 26195195723 :=
  combineSlices (auxiliaryColumnSlice contact12) 88 4 4 16827227759 9367967964 contact12ColumnsSlice88 contact12ColumnsSlice92
private theorem contact12ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact12) 0 16 = 4029561912874 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 8 8 2190530807232 1839031105642 contact12ColumnsJoin0_8 contact12ColumnsJoin8_8
private theorem contact12ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact12) 16 16 = 2747390125225 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 8 8 1518466530739 1228923594486 contact12ColumnsJoin16_8 contact12ColumnsJoin24_8
private theorem contact12ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact12) 32 16 = 1713074378828 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 8 8 970340765140 742733613688 contact12ColumnsJoin32_8 contact12ColumnsJoin40_8
private theorem contact12ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact12) 48 16 = 926616034780 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 8 8 546136577856 380479456924 contact12ColumnsJoin48_8 contact12ColumnsJoin56_8
private theorem contact12ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact12) 64 16 = 388015145556 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 8 8 245847541552 142167604004 contact12ColumnsJoin64_8 contact12ColumnsJoin72_8
private theorem contact12ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact12) 80 16 = 95618959620 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 8 8 69423763897 26195195723 contact12ColumnsJoin80_8 contact12ColumnsJoin88_8
private theorem contact12ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact12) 0 32 = 6776952038099 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 16 16 4029561912874 2747390125225 contact12ColumnsJoin0_16 contact12ColumnsJoin16_16
private theorem contact12ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact12) 32 32 = 2639690413608 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 16 16 1713074378828 926616034780 contact12ColumnsJoin32_16 contact12ColumnsJoin48_16
private theorem contact12ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact12) 64 32 = 483634105176 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 16 16 388015145556 95618959620 contact12ColumnsJoin64_16 contact12ColumnsJoin80_16
private theorem contact12ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact12) 0 64 = 9416642451707 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 32 32 6776952038099 2639690413608 contact12ColumnsJoin0_32 contact12ColumnsJoin32_32
private theorem contact12ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact12) 64 33 = 485144460619 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 32 1 483634105176 1510355443 contact12ColumnsJoin64_32 contact12ColumnsSlice96
private theorem contact12ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact12) 0 97 = 9901786912326 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 64 33 9416642451707 485144460619 contact12ColumnsJoin0_64 contact12ColumnsJoin64_33
private theorem contact12OrdinaryRanks : ordinaryRankBound contact12 = 685284846 := by decide +kernel
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
  margin_of_checked_counts contact12 97 177679305039527 9901786912326 685284846 30278967 rfl contact12OrdinaryColumns contact12ColumnsJoin0_97 contact12OrdinaryRanks contact12RanksJoin0_97 (by decide +kernel)

private theorem contact14OrdinaryColumns : ordinaryColumnCount contact14 = 190746677793092 := by decide +kernel
private theorem contact14ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact14) 0 4 = 950172836296 :=
  contactColumnsWindow_fast contact14 0 4 950172836296 (by decide +kernel)
private theorem contact14ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact14) 4 4 = 872784444970 :=
  contactColumnsWindow_fast contact14 4 4 872784444970 (by decide +kernel)
private theorem contact14ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact14) 8 4 = 798716018572 :=
  contactColumnsWindow_fast contact14 8 4 798716018572 (by decide +kernel)
private theorem contact14ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact14) 12 4 = 727952685084 :=
  contactColumnsWindow_fast contact14 12 4 727952685084 (by decide +kernel)
private theorem contact14ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact14) 16 4 = 660491771996 :=
  contactColumnsWindow_fast contact14 16 4 660491771996 (by decide +kernel)
private theorem contact14ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact14) 20 4 = 596331819664 :=
  contactColumnsWindow_fast contact14 20 4 596331819664 (by decide +kernel)
private theorem contact14ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact14) 24 4 = 535477521054 :=
  contactColumnsWindow_fast contact14 24 4 535477521054 (by decide +kernel)
private theorem contact14ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact14) 28 4 = 477944612150 :=
  contactColumnsWindow_fast contact14 28 4 477944612150 (by decide +kernel)
private theorem contact14ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact14) 32 4 = 423718369290 :=
  contactColumnsWindow_fast contact14 32 4 423718369290 (by decide +kernel)
private theorem contact14ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact14) 36 4 = 372794634668 :=
  contactColumnsWindow_fast contact14 36 4 372794634668 (by decide +kernel)
private theorem contact14ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact14) 40 4 = 325171956313 :=
  contactColumnsWindow_fast contact14 40 4 325171956313 (by decide +kernel)
private theorem contact14ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact14) 44 4 = 280855994546 :=
  contactColumnsWindow_fast contact14 44 4 280855994546 (by decide +kernel)
private theorem contact14ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact14) 48 4 = 239861611384 :=
  contactColumnsWindow_fast contact14 48 4 239861611384 (by decide +kernel)
private theorem contact14ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact14) 52 4 = 202172706240 :=
  contactColumnsWindow_fast contact14 52 4 202172706240 (by decide +kernel)
private theorem contact14ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact14) 56 4 = 167786078672 :=
  contactColumnsWindow_fast contact14 56 4 167786078672 (by decide +kernel)
private theorem contact14ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact14) 60 4 = 136700674294 :=
  contactColumnsWindow_fast contact14 60 4 136700674294 (by decide +kernel)
private theorem contact14ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact14) 64 4 = 108923324127 :=
  contactColumnsWindow_fast contact14 64 4 108923324127 (by decide +kernel)
private theorem contact14ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact14) 68 4 = 84467279788 :=
  contactColumnsWindow_fast contact14 68 4 84467279788 (by decide +kernel)
private theorem contact14ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact14) 72 4 = 63315633927 :=
  contactColumnsWindow_fast contact14 72 4 63315633927 (by decide +kernel)
private theorem contact14ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact14) 76 4 = 45466104008 :=
  contactColumnsWindow_fast contact14 76 4 45466104008 (by decide +kernel)
private theorem contact14ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact14) 80 4 = 30917207935 :=
  contactColumnsWindow_fast contact14 80 4 30917207935 (by decide +kernel)
private theorem contact14ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact14) 84 4 = 19637084364 :=
  contactColumnsWindow_fast contact14 84 4 19637084364 (by decide +kernel)
private theorem contact14ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact14) 88 4 = 11448528247 :=
  contactColumnsWindow_fast contact14 88 4 11448528247 (by decide +kernel)
private theorem contact14ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact14) 92 4 = 5977971821 :=
  contactColumnsWindow_fast contact14 92 4 5977971821 (by decide +kernel)
private theorem contact14ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact14) 96 2 = 1649289434 :=
  contactColumnsWindow_fast contact14 96 2 1649289434 (by decide +kernel)
private theorem contact14ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact14) 0 8 = 1822957281266 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 4 4 950172836296 872784444970 contact14ColumnsSlice0 contact14ColumnsSlice4
private theorem contact14ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact14) 8 8 = 1526668703656 :=
  combineSlices (auxiliaryColumnSlice contact14) 8 4 4 798716018572 727952685084 contact14ColumnsSlice8 contact14ColumnsSlice12
private theorem contact14ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact14) 16 8 = 1256823591660 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 4 4 660491771996 596331819664 contact14ColumnsSlice16 contact14ColumnsSlice20
private theorem contact14ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact14) 24 8 = 1013422133204 :=
  combineSlices (auxiliaryColumnSlice contact14) 24 4 4 535477521054 477944612150 contact14ColumnsSlice24 contact14ColumnsSlice28
private theorem contact14ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact14) 32 8 = 796513003958 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 4 4 423718369290 372794634668 contact14ColumnsSlice32 contact14ColumnsSlice36
private theorem contact14ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact14) 40 8 = 606027950859 :=
  combineSlices (auxiliaryColumnSlice contact14) 40 4 4 325171956313 280855994546 contact14ColumnsSlice40 contact14ColumnsSlice44
private theorem contact14ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact14) 48 8 = 442034317624 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 4 4 239861611384 202172706240 contact14ColumnsSlice48 contact14ColumnsSlice52
private theorem contact14ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact14) 56 8 = 304486752966 :=
  combineSlices (auxiliaryColumnSlice contact14) 56 4 4 167786078672 136700674294 contact14ColumnsSlice56 contact14ColumnsSlice60
private theorem contact14ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact14) 64 8 = 193390603915 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 4 4 108923324127 84467279788 contact14ColumnsSlice64 contact14ColumnsSlice68
private theorem contact14ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact14) 72 8 = 108781737935 :=
  combineSlices (auxiliaryColumnSlice contact14) 72 4 4 63315633927 45466104008 contact14ColumnsSlice72 contact14ColumnsSlice76
private theorem contact14ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact14) 80 8 = 50554292299 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 4 4 30917207935 19637084364 contact14ColumnsSlice80 contact14ColumnsSlice84
private theorem contact14ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact14) 88 8 = 17426500068 :=
  combineSlices (auxiliaryColumnSlice contact14) 88 4 4 11448528247 5977971821 contact14ColumnsSlice88 contact14ColumnsSlice92
private theorem contact14ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact14) 0 16 = 3349625984922 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 8 8 1822957281266 1526668703656 contact14ColumnsJoin0_8 contact14ColumnsJoin8_8
private theorem contact14ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact14) 16 16 = 2270245724864 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 8 8 1256823591660 1013422133204 contact14ColumnsJoin16_8 contact14ColumnsJoin24_8
private theorem contact14ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact14) 32 16 = 1402540954817 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 8 8 796513003958 606027950859 contact14ColumnsJoin32_8 contact14ColumnsJoin40_8
private theorem contact14ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact14) 48 16 = 746521070590 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 8 8 442034317624 304486752966 contact14ColumnsJoin48_8 contact14ColumnsJoin56_8
private theorem contact14ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact14) 64 16 = 302172341850 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 8 8 193390603915 108781737935 contact14ColumnsJoin64_8 contact14ColumnsJoin72_8
private theorem contact14ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact14) 80 16 = 67980792367 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 8 8 50554292299 17426500068 contact14ColumnsJoin80_8 contact14ColumnsJoin88_8
private theorem contact14ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact14) 0 32 = 5619871709786 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 16 16 3349625984922 2270245724864 contact14ColumnsJoin0_16 contact14ColumnsJoin16_16
private theorem contact14ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact14) 32 32 = 2149062025407 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 16 16 1402540954817 746521070590 contact14ColumnsJoin32_16 contact14ColumnsJoin48_16
private theorem contact14ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact14) 64 32 = 370153134217 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 16 16 302172341850 67980792367 contact14ColumnsJoin64_16 contact14ColumnsJoin80_16
private theorem contact14ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact14) 0 64 = 7768933735193 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 32 32 5619871709786 2149062025407 contact14ColumnsJoin0_32 contact14ColumnsJoin32_32
private theorem contact14ColumnsJoin64_34 : sliceWindow (auxiliaryColumnSlice contact14) 64 34 = 371802423651 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 32 2 370153134217 1649289434 contact14ColumnsJoin64_32 contact14ColumnsSlice96
private theorem contact14ColumnsJoin0_98 : sliceWindow (auxiliaryColumnSlice contact14) 0 98 = 8140736158844 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 64 34 7768933735193 371802423651 contact14ColumnsJoin0_64 contact14ColumnsJoin64_34
private theorem contact14OrdinaryRanks : ordinaryRankBound contact14 = 733997519 := by decide +kernel
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
  margin_of_checked_counts contact14 98 190746677793092 8140736158844 733997519 24697347 rfl contact14OrdinaryColumns contact14ColumnsJoin0_98 contact14OrdinaryRanks contact14RanksJoin0_98 (by decide +kernel)

private theorem contact16OrdinaryColumns : ordinaryColumnCount contact16 = 171424079411487 := by decide +kernel
private theorem contact16ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact16) 0 4 = 1091466580704 :=
  contactColumnsWindow_fast contact16 0 4 1091466580704 (by decide +kernel)
private theorem contact16ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact16) 4 4 = 1004111300022 :=
  contactColumnsWindow_fast contact16 4 4 1004111300022 (by decide +kernel)
private theorem contact16ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact16) 8 4 = 920420025512 :=
  contactColumnsWindow_fast contact16 8 4 920420025512 (by decide +kernel)
private theorem contact16ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact16) 12 4 = 840391681654 :=
  contactColumnsWindow_fast contact16 12 4 840391681654 (by decide +kernel)
private theorem contact16ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact16) 16 4 = 764025100406 :=
  contactColumnsWindow_fast contact16 16 4 764025100406 (by decide +kernel)
private theorem contact16ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact16) 20 4 = 691327717136 :=
  contactColumnsWindow_fast contact16 20 4 691327717136 (by decide +kernel)
private theorem contact16ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact16) 24 4 = 622314933534 :=
  contactColumnsWindow_fast contact16 24 4 622314933534 (by decide +kernel)
private theorem contact16ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact16) 28 4 = 556967497865 :=
  contactColumnsWindow_fast contact16 28 4 556967497865 (by decide +kernel)
private theorem contact16ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact16) 32 4 = 495282821418 :=
  contactColumnsWindow_fast contact16 32 4 495282821418 (by decide +kernel)
private theorem contact16ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact16) 36 4 = 437260136070 :=
  contactColumnsWindow_fast contact16 36 4 437260136070 (by decide +kernel)
private theorem contact16ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact16) 40 4 = 382908476639 :=
  contactColumnsWindow_fast contact16 40 4 382908476639 (by decide +kernel)
private theorem contact16ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact16) 44 4 = 332240354742 :=
  contactColumnsWindow_fast contact16 44 4 332240354742 (by decide +kernel)
private theorem contact16ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact16) 48 4 = 285236760574 :=
  contactColumnsWindow_fast contact16 48 4 285236760574 (by decide +kernel)
private theorem contact16ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact16) 52 4 = 241895748878 :=
  contactColumnsWindow_fast contact16 52 4 241895748878 (by decide +kernel)
private theorem contact16ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact16) 56 4 = 202217007678 :=
  contactColumnsWindow_fast contact16 56 4 202217007678 (by decide +kernel)
private theorem contact16ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact16) 60 4 = 166211040842 :=
  contactColumnsWindow_fast contact16 60 4 166211040842 (by decide +kernel)
private theorem contact16ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact16) 64 4 = 133887563646 :=
  contactColumnsWindow_fast contact16 64 4 133887563646 (by decide +kernel)
private theorem contact16ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact16) 68 4 = 105227894034 :=
  contactColumnsWindow_fast contact16 68 4 105227894034 (by decide +kernel)
private theorem contact16ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact16) 72 4 = 80230464034 :=
  contactColumnsWindow_fast contact16 72 4 80230464034 (by decide +kernel)
private theorem contact16ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact16) 76 4 = 58895666982 :=
  contactColumnsWindow_fast contact16 76 4 58895666982 (by decide +kernel)
private theorem contact16ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact16) 80 4 = 41235692346 :=
  contactColumnsWindow_fast contact16 80 4 41235692346 (by decide +kernel)
private theorem contact16ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact16) 84 4 = 27230498912 :=
  contactColumnsWindow_fast contact16 84 4 27230498912 (by decide +kernel)
private theorem contact16ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact16) 88 4 = 16707028414 :=
  contactColumnsWindow_fast contact16 88 4 16707028414 (by decide +kernel)
private theorem contact16ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact16) 92 4 = 9338224999 :=
  contactColumnsWindow_fast contact16 92 4 9338224999 (by decide +kernel)
private theorem contact16ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact16) 96 2 = 2762946664 :=
  contactColumnsWindow_fast contact16 96 2 2762946664 (by decide +kernel)
private theorem contact16ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact16) 0 8 = 2095577880726 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 4 4 1091466580704 1004111300022 contact16ColumnsSlice0 contact16ColumnsSlice4
private theorem contact16ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact16) 8 8 = 1760811707166 :=
  combineSlices (auxiliaryColumnSlice contact16) 8 4 4 920420025512 840391681654 contact16ColumnsSlice8 contact16ColumnsSlice12
private theorem contact16ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact16) 16 8 = 1455352817542 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 4 4 764025100406 691327717136 contact16ColumnsSlice16 contact16ColumnsSlice20
private theorem contact16ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact16) 24 8 = 1179282431399 :=
  combineSlices (auxiliaryColumnSlice contact16) 24 4 4 622314933534 556967497865 contact16ColumnsSlice24 contact16ColumnsSlice28
private theorem contact16ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact16) 32 8 = 932542957488 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 4 4 495282821418 437260136070 contact16ColumnsSlice32 contact16ColumnsSlice36
private theorem contact16ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact16) 40 8 = 715148831381 :=
  combineSlices (auxiliaryColumnSlice contact16) 40 4 4 382908476639 332240354742 contact16ColumnsSlice40 contact16ColumnsSlice44
private theorem contact16ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact16) 48 8 = 527132509452 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 4 4 285236760574 241895748878 contact16ColumnsSlice48 contact16ColumnsSlice52
private theorem contact16ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact16) 56 8 = 368428048520 :=
  combineSlices (auxiliaryColumnSlice contact16) 56 4 4 202217007678 166211040842 contact16ColumnsSlice56 contact16ColumnsSlice60
private theorem contact16ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact16) 64 8 = 239115457680 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 4 4 133887563646 105227894034 contact16ColumnsSlice64 contact16ColumnsSlice68
private theorem contact16ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact16) 72 8 = 139126131016 :=
  combineSlices (auxiliaryColumnSlice contact16) 72 4 4 80230464034 58895666982 contact16ColumnsSlice72 contact16ColumnsSlice76
private theorem contact16ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact16) 80 8 = 68466191258 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 4 4 41235692346 27230498912 contact16ColumnsSlice80 contact16ColumnsSlice84
private theorem contact16ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact16) 88 8 = 26045253413 :=
  combineSlices (auxiliaryColumnSlice contact16) 88 4 4 16707028414 9338224999 contact16ColumnsSlice88 contact16ColumnsSlice92
private theorem contact16ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact16) 0 16 = 3856389587892 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 8 8 2095577880726 1760811707166 contact16ColumnsJoin0_8 contact16ColumnsJoin8_8
private theorem contact16ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact16) 16 16 = 2634635248941 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 8 8 1455352817542 1179282431399 contact16ColumnsJoin16_8 contact16ColumnsJoin24_8
private theorem contact16ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact16) 32 16 = 1647691788869 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 8 8 932542957488 715148831381 contact16ColumnsJoin32_8 contact16ColumnsJoin40_8
private theorem contact16ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact16) 48 16 = 895560557972 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 8 8 527132509452 368428048520 contact16ColumnsJoin48_8 contact16ColumnsJoin56_8
private theorem contact16ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact16) 64 16 = 378241588696 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 8 8 239115457680 139126131016 contact16ColumnsJoin64_8 contact16ColumnsJoin72_8
private theorem contact16ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact16) 80 16 = 94511444671 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 8 8 68466191258 26045253413 contact16ColumnsJoin80_8 contact16ColumnsJoin88_8
private theorem contact16ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact16) 0 32 = 6491024836833 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 16 16 3856389587892 2634635248941 contact16ColumnsJoin0_16 contact16ColumnsJoin16_16
private theorem contact16ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact16) 32 32 = 2543252346841 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 16 16 1647691788869 895560557972 contact16ColumnsJoin32_16 contact16ColumnsJoin48_16
private theorem contact16ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact16) 64 32 = 472753033367 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 16 16 378241588696 94511444671 contact16ColumnsJoin64_16 contact16ColumnsJoin80_16
private theorem contact16ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact16) 0 64 = 9034277183674 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 32 32 6491024836833 2543252346841 contact16ColumnsJoin0_32 contact16ColumnsJoin32_32
private theorem contact16ColumnsJoin64_34 : sliceWindow (auxiliaryColumnSlice contact16) 64 34 = 475515980031 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 32 2 472753033367 2762946664 contact16ColumnsJoin64_32 contact16ColumnsSlice96
private theorem contact16ColumnsJoin0_98 : sliceWindow (auxiliaryColumnSlice contact16) 0 98 = 9509793163705 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 64 34 9034277183674 475515980031 contact16ColumnsJoin0_64 contact16ColumnsJoin64_34
private theorem contact16OrdinaryRanks : ordinaryRankBound contact16 = 661247862 := by decide +kernel
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
  margin_of_checked_counts contact16 98 171424079411487 9509793163705 661247862 28959861 rfl contact16OrdinaryColumns contact16ColumnsJoin0_98 contact16OrdinaryRanks contact16RanksJoin0_98 (by decide +kernel)

private theorem contact18OrdinaryColumns : ordinaryColumnCount contact18 = 2335739322994011 := by decide +kernel
private theorem contact18ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact18) 0 4 = 7049563495456 :=
  contactColumnsWindow_fast contact18 0 4 7049563495456 (by decide +kernel)
private theorem contact18ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact18) 4 4 = 6702443210464 :=
  contactColumnsWindow_fast contact18 4 4 6702443210464 (by decide +kernel)
private theorem contact18ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact18) 8 4 = 6364123028596 :=
  contactColumnsWindow_fast contact18 8 4 6364123028596 (by decide +kernel)
private theorem contact18ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact18) 12 4 = 6034605856312 :=
  contactColumnsWindow_fast contact18 12 4 6034605856312 (by decide +kernel)
private theorem contact18ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact18) 16 4 = 5713889711494 :=
  contactColumnsWindow_fast contact18 16 4 5713889711494 (by decide +kernel)
private theorem contact18ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact18) 20 4 = 5401976617480 :=
  contactColumnsWindow_fast contact18 20 4 5401976617480 (by decide +kernel)
private theorem contact18ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact18) 24 4 = 5098881183720 :=
  contactColumnsWindow_fast contact18 24 4 5098881183720 (by decide +kernel)
private theorem contact18ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact18) 28 4 = 4804623056535 :=
  contactColumnsWindow_fast contact18 28 4 4804623056535 (by decide +kernel)
private theorem contact18ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact18) 32 4 = 4519171291732 :=
  contactColumnsWindow_fast contact18 32 4 4519171291732 (by decide +kernel)
private theorem contact18ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact18) 36 4 = 4242523761215 :=
  contactColumnsWindow_fast contact18 36 4 4242523761215 (by decide +kernel)
private theorem contact18ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact18) 40 4 = 3974682264792 :=
  contactColumnsWindow_fast contact18 40 4 3974682264792 (by decide +kernel)
private theorem contact18ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact18) 44 4 = 3715665007638 :=
  contactColumnsWindow_fast contact18 44 4 3715665007638 (by decide +kernel)
private theorem contact18ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact18) 48 4 = 3465486136766 :=
  contactColumnsWindow_fast contact18 48 4 3465486136766 (by decide +kernel)
private theorem contact18ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact18) 52 4 = 3224115100612 :=
  contactColumnsWindow_fast contact18 52 4 3224115100612 (by decide +kernel)
private theorem contact18ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact18) 56 4 = 2991552515629 :=
  contactColumnsWindow_fast contact18 56 4 2991552515629 (by decide +kernel)
private theorem contact18ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact18) 60 4 = 2767798169240 :=
  contactColumnsWindow_fast contact18 60 4 2767798169240 (by decide +kernel)
private theorem contact18ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact18) 64 4 = 2552877470837 :=
  contactColumnsWindow_fast contact18 64 4 2552877470837 (by decide +kernel)
private theorem contact18ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact18) 68 4 = 2346792653085 :=
  contactColumnsWindow_fast contact18 68 4 2346792653085 (by decide +kernel)
private theorem contact18ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact18) 72 4 = 2149520644366 :=
  contactColumnsWindow_fast contact18 72 4 2149520644366 (by decide +kernel)
private theorem contact18ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact18) 76 4 = 1961057683070 :=
  contactColumnsWindow_fast contact18 76 4 1961057683070 (by decide +kernel)
private theorem contact18ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact18) 80 4 = 1781402750670 :=
  contactColumnsWindow_fast contact18 80 4 1781402750670 (by decide +kernel)
private theorem contact18ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact18) 84 4 = 1610586332040 :=
  contactColumnsWindow_fast contact18 84 4 1610586332040 (by decide +kernel)
private theorem contact18ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact18) 88 4 = 1448601503942 :=
  contactColumnsWindow_fast contact18 88 4 1448601503942 (by decide +kernel)
private theorem contact18ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact18) 92 4 = 1295429138476 :=
  contactColumnsWindow_fast contact18 92 4 1295429138476 (by decide +kernel)
private theorem contact18ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact18) 96 4 = 1151065758127 :=
  contactColumnsWindow_fast contact18 96 4 1151065758127 (by decide +kernel)
private theorem contact18ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact18) 100 4 = 1015510888076 :=
  contactColumnsWindow_fast contact18 100 4 1015510888076 (by decide +kernel)
private theorem contact18ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact18) 104 4 = 888798200050 :=
  contactColumnsWindow_fast contact18 104 4 888798200050 (by decide +kernel)
private theorem contact18ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact18) 108 4 = 770913366780 :=
  contactColumnsWindow_fast contact18 108 4 770913366780 (by decide +kernel)
private theorem contact18ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact18) 112 4 = 661840523611 :=
  contactColumnsWindow_fast contact18 112 4 661840523611 (by decide +kernel)
private theorem contact18ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact18) 116 4 = 561576800900 :=
  contactColumnsWindow_fast contact18 116 4 561576800900 (by decide +kernel)
private theorem contact18ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact18) 120 4 = 470122664377 :=
  contactColumnsWindow_fast contact18 120 4 470122664377 (by decide +kernel)
private theorem contact18ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact18) 124 4 = 387512951612 :=
  contactColumnsWindow_fast contact18 124 4 387512951612 (by decide +kernel)
private theorem contact18ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact18) 128 4 = 313728139639 :=
  contactColumnsWindow_fast contact18 128 4 313728139639 (by decide +kernel)
private theorem contact18ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact18) 132 4 = 248754964403 :=
  contactColumnsWindow_fast contact18 132 4 248754964403 (by decide +kernel)
private theorem contact18ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact18) 136 4 = 192574088133 :=
  contactColumnsWindow_fast contact18 136 4 192574088133 (by decide +kernel)
private theorem contact18ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact18) 140 4 = 145039352251 :=
  contactColumnsWindow_fast contact18 140 4 145039352251 (by decide +kernel)
private theorem contact18ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact18) 144 4 = 105839362951 :=
  contactColumnsWindow_fast contact18 144 4 105839362951 (by decide +kernel)
private theorem contact18ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact18) 148 4 = 74438070279 :=
  contactColumnsWindow_fast contact18 148 4 74438070279 (by decide +kernel)
private theorem contact18ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact18) 152 4 = 50152620518 :=
  contactColumnsWindow_fast contact18 152 4 50152620518 (by decide +kernel)
private theorem contact18ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact18) 156 4 = 32148049899 :=
  contactColumnsWindow_fast contact18 156 4 32148049899 (by decide +kernel)
private theorem contact18ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact18) 160 1 = 5867444649 :=
  contactColumnsWindow_fast contact18 160 1 5867444649 (by decide +kernel)
private theorem contact18ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact18) 0 8 = 13752006705920 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 4 4 7049563495456 6702443210464 contact18ColumnsSlice0 contact18ColumnsSlice4
private theorem contact18ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact18) 8 8 = 12398728884908 :=
  combineSlices (auxiliaryColumnSlice contact18) 8 4 4 6364123028596 6034605856312 contact18ColumnsSlice8 contact18ColumnsSlice12
private theorem contact18ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact18) 16 8 = 11115866328974 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 4 4 5713889711494 5401976617480 contact18ColumnsSlice16 contact18ColumnsSlice20
private theorem contact18ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact18) 24 8 = 9903504240255 :=
  combineSlices (auxiliaryColumnSlice contact18) 24 4 4 5098881183720 4804623056535 contact18ColumnsSlice24 contact18ColumnsSlice28
private theorem contact18ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact18) 32 8 = 8761695052947 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 4 4 4519171291732 4242523761215 contact18ColumnsSlice32 contact18ColumnsSlice36
private theorem contact18ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact18) 40 8 = 7690347272430 :=
  combineSlices (auxiliaryColumnSlice contact18) 40 4 4 3974682264792 3715665007638 contact18ColumnsSlice40 contact18ColumnsSlice44
private theorem contact18ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact18) 48 8 = 6689601237378 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 4 4 3465486136766 3224115100612 contact18ColumnsSlice48 contact18ColumnsSlice52
private theorem contact18ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact18) 56 8 = 5759350684869 :=
  combineSlices (auxiliaryColumnSlice contact18) 56 4 4 2991552515629 2767798169240 contact18ColumnsSlice56 contact18ColumnsSlice60
private theorem contact18ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact18) 64 8 = 4899670123922 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 4 4 2552877470837 2346792653085 contact18ColumnsSlice64 contact18ColumnsSlice68
private theorem contact18ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact18) 72 8 = 4110578327436 :=
  combineSlices (auxiliaryColumnSlice contact18) 72 4 4 2149520644366 1961057683070 contact18ColumnsSlice72 contact18ColumnsSlice76
private theorem contact18ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact18) 80 8 = 3391989082710 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 4 4 1781402750670 1610586332040 contact18ColumnsSlice80 contact18ColumnsSlice84
private theorem contact18ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact18) 88 8 = 2744030642418 :=
  combineSlices (auxiliaryColumnSlice contact18) 88 4 4 1448601503942 1295429138476 contact18ColumnsSlice88 contact18ColumnsSlice92
private theorem contact18ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact18) 96 8 = 2166576646203 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 4 4 1151065758127 1015510888076 contact18ColumnsSlice96 contact18ColumnsSlice100
private theorem contact18ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact18) 104 8 = 1659711566830 :=
  combineSlices (auxiliaryColumnSlice contact18) 104 4 4 888798200050 770913366780 contact18ColumnsSlice104 contact18ColumnsSlice108
private theorem contact18ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact18) 112 8 = 1223417324511 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 4 4 661840523611 561576800900 contact18ColumnsSlice112 contact18ColumnsSlice116
private theorem contact18ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact18) 120 8 = 857635615989 :=
  combineSlices (auxiliaryColumnSlice contact18) 120 4 4 470122664377 387512951612 contact18ColumnsSlice120 contact18ColumnsSlice124
private theorem contact18ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact18) 128 8 = 562483104042 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 4 4 313728139639 248754964403 contact18ColumnsSlice128 contact18ColumnsSlice132
private theorem contact18ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact18) 136 8 = 337613440384 :=
  combineSlices (auxiliaryColumnSlice contact18) 136 4 4 192574088133 145039352251 contact18ColumnsSlice136 contact18ColumnsSlice140
private theorem contact18ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact18) 144 8 = 180277433230 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 4 4 105839362951 74438070279 contact18ColumnsSlice144 contact18ColumnsSlice148
private theorem contact18ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact18) 152 8 = 82300670417 :=
  combineSlices (auxiliaryColumnSlice contact18) 152 4 4 50152620518 32148049899 contact18ColumnsSlice152 contact18ColumnsSlice156
private theorem contact18ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact18) 0 16 = 26150735590828 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 8 8 13752006705920 12398728884908 contact18ColumnsJoin0_8 contact18ColumnsJoin8_8
private theorem contact18ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact18) 16 16 = 21019370569229 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 8 8 11115866328974 9903504240255 contact18ColumnsJoin16_8 contact18ColumnsJoin24_8
private theorem contact18ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact18) 32 16 = 16452042325377 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 8 8 8761695052947 7690347272430 contact18ColumnsJoin32_8 contact18ColumnsJoin40_8
private theorem contact18ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact18) 48 16 = 12448951922247 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 8 8 6689601237378 5759350684869 contact18ColumnsJoin48_8 contact18ColumnsJoin56_8
private theorem contact18ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact18) 64 16 = 9010248451358 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 8 8 4899670123922 4110578327436 contact18ColumnsJoin64_8 contact18ColumnsJoin72_8
private theorem contact18ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact18) 80 16 = 6136019725128 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 8 8 3391989082710 2744030642418 contact18ColumnsJoin80_8 contact18ColumnsJoin88_8
private theorem contact18ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact18) 96 16 = 3826288213033 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 8 8 2166576646203 1659711566830 contact18ColumnsJoin96_8 contact18ColumnsJoin104_8
private theorem contact18ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact18) 112 16 = 2081052940500 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 8 8 1223417324511 857635615989 contact18ColumnsJoin112_8 contact18ColumnsJoin120_8
private theorem contact18ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact18) 128 16 = 900096544426 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 8 8 562483104042 337613440384 contact18ColumnsJoin128_8 contact18ColumnsJoin136_8
private theorem contact18ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact18) 144 16 = 262578103647 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 8 8 180277433230 82300670417 contact18ColumnsJoin144_8 contact18ColumnsJoin152_8
private theorem contact18ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact18) 0 32 = 47170106160057 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 16 16 26150735590828 21019370569229 contact18ColumnsJoin0_16 contact18ColumnsJoin16_16
private theorem contact18ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact18) 32 32 = 28900994247624 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 16 16 16452042325377 12448951922247 contact18ColumnsJoin32_16 contact18ColumnsJoin48_16
private theorem contact18ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact18) 64 32 = 15146268176486 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 16 16 9010248451358 6136019725128 contact18ColumnsJoin64_16 contact18ColumnsJoin80_16
private theorem contact18ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact18) 96 32 = 5907341153533 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 16 16 3826288213033 2081052940500 contact18ColumnsJoin96_16 contact18ColumnsJoin112_16
private theorem contact18ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact18) 128 32 = 1162674648073 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 16 16 900096544426 262578103647 contact18ColumnsJoin128_16 contact18ColumnsJoin144_16
private theorem contact18ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact18) 0 64 = 76071100407681 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 32 32 47170106160057 28900994247624 contact18ColumnsJoin0_32 contact18ColumnsJoin32_32
private theorem contact18ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact18) 64 64 = 21053609330019 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 32 32 15146268176486 5907341153533 contact18ColumnsJoin64_32 contact18ColumnsJoin96_32
private theorem contact18ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact18) 128 33 = 1168542092722 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 32 1 1162674648073 5867444649 contact18ColumnsJoin128_32 contact18ColumnsSlice160
private theorem contact18ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact18) 0 128 = 97124709737700 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 64 64 76071100407681 21053609330019 contact18ColumnsJoin0_64 contact18ColumnsJoin64_64
private theorem contact18ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact18) 0 161 = 98293251830422 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 128 33 97124709737700 1168542092722 contact18ColumnsJoin0_128 contact18ColumnsJoin128_33
private theorem contact18OrdinaryRanks : ordinaryRankBound contact18 = 8986828348 := by decide +kernel
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
private theorem contact18RanksSlice148 : sliceWindow (auxiliaryRankSlice contact18) 148 13 = 0 :=
  contactRankWindow_of_rec contact18 148 13 0 (by decide +kernel)
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
private theorem contact18RanksJoin144_17 : sliceWindow (auxiliaryRankSlice contact18) 144 17 = 924 :=
  combineSlices (auxiliaryRankSlice contact18) 144 4 13 924 0 contact18RanksSlice144 contact18RanksSlice148
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
private theorem contact18RanksJoin128_33 : sliceWindow (auxiliaryRankSlice contact18) 128 33 = 393486 :=
  combineSlices (auxiliaryRankSlice contact18) 128 16 17 392562 924 contact18RanksJoin128_16 contact18RanksJoin144_17
private theorem contact18RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact18) 0 64 = 254606922 :=
  combineSlices (auxiliaryRankSlice contact18) 0 32 32 168249760 86357162 contact18RanksJoin0_32 contact18RanksJoin32_32
private theorem contact18RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact18) 64 64 = 43265172 :=
  combineSlices (auxiliaryRankSlice contact18) 64 32 32 34755938 8509234 contact18RanksJoin64_32 contact18RanksJoin96_32
private theorem contact18RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact18) 0 128 = 297872094 :=
  combineSlices (auxiliaryRankSlice contact18) 0 64 64 254606922 43265172 contact18RanksJoin0_64 contact18RanksJoin64_64
private theorem contact18RanksJoin0_161 : sliceWindow (auxiliaryRankSlice contact18) 0 161 = 298265580 :=
  combineSlices (auxiliaryRankSlice contact18) 0 128 33 297872094 393486 contact18RanksJoin0_128 contact18RanksJoin128_33
theorem contact18_margin : sourceMargin contact18 :=
  margin_of_checked_counts contact18 161 2335739322994011 98293251830422 8986828348 298265580 rfl contact18OrdinaryColumns contact18ColumnsJoin0_161 contact18OrdinaryRanks contact18RanksJoin0_161 (by decide +kernel)

private theorem contact20OrdinaryColumns : ordinaryColumnCount contact20 = 53148948551603 := by decide +kernel
private theorem contact20ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact20) 0 4 = 448614185766 :=
  contactColumnsWindow_fast contact20 0 4 448614185766 (by decide +kernel)
private theorem contact20ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact20) 4 4 = 403907532550 :=
  contactColumnsWindow_fast contact20 4 4 403907532550 (by decide +kernel)
private theorem contact20ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact20) 8 4 = 361557862694 :=
  contactColumnsWindow_fast contact20 8 4 361557862694 (by decide +kernel)
private theorem contact20ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact20) 12 4 = 321574848874 :=
  contactColumnsWindow_fast contact20 12 4 321574848874 (by decide +kernel)
private theorem contact20ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact20) 16 4 = 283959974858 :=
  contactColumnsWindow_fast contact20 16 4 283959974858 (by decide +kernel)
private theorem contact20ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact20) 20 4 = 248703931270 :=
  contactColumnsWindow_fast contact20 20 4 248703931270 (by decide +kernel)
private theorem contact20ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact20) 24 4 = 215806206919 :=
  contactColumnsWindow_fast contact20 24 4 215806206919 (by decide +kernel)
private theorem contact20ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact20) 28 4 = 185267706050 :=
  contactColumnsWindow_fast contact20 28 4 185267706050 (by decide +kernel)
private theorem contact20ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact20) 32 4 = 157098757330 :=
  contactColumnsWindow_fast contact20 32 4 157098757330 (by decide +kernel)
private theorem contact20ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact20) 36 4 = 131296086972 :=
  contactColumnsWindow_fast contact20 36 4 131296086972 (by decide +kernel)
private theorem contact20ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact20) 40 4 = 107852433570 :=
  contactColumnsWindow_fast contact20 40 4 107852433570 (by decide +kernel)
private theorem contact20ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact20) 44 4 = 86766940018 :=
  contactColumnsWindow_fast contact20 44 4 86766940018 (by decide +kernel)
private theorem contact20ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact20) 48 4 = 68040940515 :=
  contactColumnsWindow_fast contact20 48 4 68040940515 (by decide +kernel)
private theorem contact20ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact20) 52 4 = 51685938166 :=
  contactColumnsWindow_fast contact20 52 4 51685938166 (by decide +kernel)
private theorem contact20ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact20) 56 4 = 37695493709 :=
  contactColumnsWindow_fast contact20 56 4 37695493709 (by decide +kernel)
private theorem contact20ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact20) 60 4 = 26064208250 :=
  contactColumnsWindow_fast contact20 60 4 26064208250 (by decide +kernel)
private theorem contact20ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact20) 64 4 = 16790763203 :=
  contactColumnsWindow_fast contact20 64 4 16790763203 (by decide +kernel)
private theorem contact20ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact20) 68 4 = 9852733849 :=
  contactColumnsWindow_fast contact20 68 4 9852733849 (by decide +kernel)
private theorem contact20ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact20) 72 4 = 5113894259 :=
  contactColumnsWindow_fast contact20 72 4 5113894259 (by decide +kernel)
private theorem contact20ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact20) 76 3 = 1871034265 :=
  contactColumnsWindow_fast contact20 76 3 1871034265 (by decide +kernel)
private theorem contact20ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact20) 0 8 = 852521718316 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 4 4 448614185766 403907532550 contact20ColumnsSlice0 contact20ColumnsSlice4
private theorem contact20ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact20) 8 8 = 683132711568 :=
  combineSlices (auxiliaryColumnSlice contact20) 8 4 4 361557862694 321574848874 contact20ColumnsSlice8 contact20ColumnsSlice12
private theorem contact20ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact20) 16 8 = 532663906128 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 4 4 283959974858 248703931270 contact20ColumnsSlice16 contact20ColumnsSlice20
private theorem contact20ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact20) 24 8 = 401073912969 :=
  combineSlices (auxiliaryColumnSlice contact20) 24 4 4 215806206919 185267706050 contact20ColumnsSlice24 contact20ColumnsSlice28
private theorem contact20ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact20) 32 8 = 288394844302 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 4 4 157098757330 131296086972 contact20ColumnsSlice32 contact20ColumnsSlice36
private theorem contact20ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact20) 40 8 = 194619373588 :=
  combineSlices (auxiliaryColumnSlice contact20) 40 4 4 107852433570 86766940018 contact20ColumnsSlice40 contact20ColumnsSlice44
private theorem contact20ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact20) 48 8 = 119726878681 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 4 4 68040940515 51685938166 contact20ColumnsSlice48 contact20ColumnsSlice52
private theorem contact20ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact20) 56 8 = 63759701959 :=
  combineSlices (auxiliaryColumnSlice contact20) 56 4 4 37695493709 26064208250 contact20ColumnsSlice56 contact20ColumnsSlice60
private theorem contact20ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact20) 64 8 = 26643497052 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 4 4 16790763203 9852733849 contact20ColumnsSlice64 contact20ColumnsSlice68
private theorem contact20ColumnsJoin72_7 : sliceWindow (auxiliaryColumnSlice contact20) 72 7 = 6984928524 :=
  combineSlices (auxiliaryColumnSlice contact20) 72 4 3 5113894259 1871034265 contact20ColumnsSlice72 contact20ColumnsSlice76
private theorem contact20ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact20) 0 16 = 1535654429884 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 8 8 852521718316 683132711568 contact20ColumnsJoin0_8 contact20ColumnsJoin8_8
private theorem contact20ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact20) 16 16 = 933737819097 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 8 8 532663906128 401073912969 contact20ColumnsJoin16_8 contact20ColumnsJoin24_8
private theorem contact20ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact20) 32 16 = 483014217890 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 8 8 288394844302 194619373588 contact20ColumnsJoin32_8 contact20ColumnsJoin40_8
private theorem contact20ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact20) 48 16 = 183486580640 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 8 8 119726878681 63759701959 contact20ColumnsJoin48_8 contact20ColumnsJoin56_8
private theorem contact20ColumnsJoin64_15 : sliceWindow (auxiliaryColumnSlice contact20) 64 15 = 33628425576 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 8 7 26643497052 6984928524 contact20ColumnsJoin64_8 contact20ColumnsJoin72_7
private theorem contact20ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact20) 0 32 = 2469392248981 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 16 16 1535654429884 933737819097 contact20ColumnsJoin0_16 contact20ColumnsJoin16_16
private theorem contact20ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact20) 32 32 = 666500798530 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 16 16 483014217890 183486580640 contact20ColumnsJoin32_16 contact20ColumnsJoin48_16
private theorem contact20ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact20) 0 64 = 3135893047511 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 32 32 2469392248981 666500798530 contact20ColumnsJoin0_32 contact20ColumnsJoin32_32
private theorem contact20ColumnsJoin0_79 : sliceWindow (auxiliaryColumnSlice contact20) 0 79 = 3169521473087 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 64 15 3135893047511 33628425576 contact20ColumnsJoin0_64 contact20ColumnsJoin64_15
private theorem contact20OrdinaryRanks : ordinaryRankBound contact20 = 205204325 := by decide +kernel
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
  margin_of_checked_counts contact20 79 53148948551603 3169521473087 205204325 9633495 rfl contact20OrdinaryColumns contact20ColumnsJoin0_79 contact20OrdinaryRanks contact20RanksJoin0_79 (by decide +kernel)

private theorem contact22OrdinaryColumns : ordinaryColumnCount contact22 = 156955232083886 := by decide +kernel
private theorem contact22ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact22) 0 4 = 1567154131319 :=
  contactColumnsWindow_fast contact22 0 4 1567154131319 (by decide +kernel)
private theorem contact22ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact22) 4 4 = 1451718239276 :=
  contactColumnsWindow_fast contact22 4 4 1451718239276 (by decide +kernel)
private theorem contact22ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact22) 8 4 = 1340727595454 :=
  contactColumnsWindow_fast contact22 8 4 1340727595454 (by decide +kernel)
private theorem contact22ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact22) 12 4 = 1234176750560 :=
  contactColumnsWindow_fast contact22 12 4 1234176750560 (by decide +kernel)
private theorem contact22ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact22) 16 4 = 1132063934026 :=
  contactColumnsWindow_fast contact22 16 4 1132063934026 (by decide +kernel)
private theorem contact22ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact22) 20 4 = 1034394569736 :=
  contactColumnsWindow_fast contact22 20 4 1034394569736 (by decide +kernel)
private theorem contact22ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact22) 24 4 = 941192043869 :=
  contactColumnsWindow_fast contact22 24 4 941192043869 (by decide +kernel)
private theorem contact22ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact22) 28 4 = 852436077008 :=
  contactColumnsWindow_fast contact22 28 4 852436077008 (by decide +kernel)
private theorem contact22ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact22) 32 4 = 768120067616 :=
  contactColumnsWindow_fast contact22 32 4 768120067616 (by decide +kernel)
private theorem contact22ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact22) 36 4 = 688242175100 :=
  contactColumnsWindow_fast contact22 36 4 688242175100 (by decide +kernel)
private theorem contact22ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact22) 40 4 = 612809325974 :=
  contactColumnsWindow_fast contact22 40 4 612809325974 (by decide +kernel)
private theorem contact22ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact22) 44 4 = 541843509094 :=
  contactColumnsWindow_fast contact22 44 4 541843509094 (by decide +kernel)
private theorem contact22ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact22) 48 4 = 475322516231 :=
  contactColumnsWindow_fast contact22 48 4 475322516231 (by decide +kernel)
private theorem contact22ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact22) 52 4 = 413241309152 :=
  contactColumnsWindow_fast contact22 52 4 413241309152 (by decide +kernel)
private theorem contact22ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact22) 56 4 = 355598362343 :=
  contactColumnsWindow_fast contact22 56 4 355598362343 (by decide +kernel)
private theorem contact22ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact22) 60 4 = 302402006692 :=
  contactColumnsWindow_fast contact22 60 4 302402006692 (by decide +kernel)
private theorem contact22ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact22) 64 4 = 253672950872 :=
  contactColumnsWindow_fast contact22 64 4 253672950872 (by decide +kernel)
private theorem contact22ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact22) 68 4 = 209386942256 :=
  contactColumnsWindow_fast contact22 68 4 209386942256 (by decide +kernel)
private theorem contact22ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact22) 72 4 = 169540475168 :=
  contactColumnsWindow_fast contact22 72 4 169540475168 (by decide +kernel)
private theorem contact22ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact22) 76 4 = 134132479888 :=
  contactColumnsWindow_fast contact22 76 4 134132479888 (by decide +kernel)
private theorem contact22ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact22) 80 4 = 103173406317 :=
  contactColumnsWindow_fast contact22 80 4 103173406317 (by decide +kernel)
private theorem contact22ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact22) 84 4 = 76680370364 :=
  contactColumnsWindow_fast contact22 84 4 76680370364 (by decide +kernel)
private theorem contact22ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact22) 88 4 = 54627371930 :=
  contactColumnsWindow_fast contact22 88 4 54627371930 (by decide +kernel)
private theorem contact22ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact22) 92 4 = 36956585181 :=
  contactColumnsWindow_fast contact22 92 4 36956585181 (by decide +kernel)
private theorem contact22ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact22) 96 4 = 23456374639 :=
  contactColumnsWindow_fast contact22 96 4 23456374639 (by decide +kernel)
private theorem contact22ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact22) 100 4 = 13759151526 :=
  contactColumnsWindow_fast contact22 100 4 13759151526 (by decide +kernel)
private theorem contact22ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact22) 0 8 = 3018872370595 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 4 4 1567154131319 1451718239276 contact22ColumnsSlice0 contact22ColumnsSlice4
private theorem contact22ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact22) 8 8 = 2574904346014 :=
  combineSlices (auxiliaryColumnSlice contact22) 8 4 4 1340727595454 1234176750560 contact22ColumnsSlice8 contact22ColumnsSlice12
private theorem contact22ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact22) 16 8 = 2166458503762 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 4 4 1132063934026 1034394569736 contact22ColumnsSlice16 contact22ColumnsSlice20
private theorem contact22ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact22) 24 8 = 1793628120877 :=
  combineSlices (auxiliaryColumnSlice contact22) 24 4 4 941192043869 852436077008 contact22ColumnsSlice24 contact22ColumnsSlice28
private theorem contact22ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact22) 32 8 = 1456362242716 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 4 4 768120067616 688242175100 contact22ColumnsSlice32 contact22ColumnsSlice36
private theorem contact22ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact22) 40 8 = 1154652835068 :=
  combineSlices (auxiliaryColumnSlice contact22) 40 4 4 612809325974 541843509094 contact22ColumnsSlice40 contact22ColumnsSlice44
private theorem contact22ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact22) 48 8 = 888563825383 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 4 4 475322516231 413241309152 contact22ColumnsSlice48 contact22ColumnsSlice52
private theorem contact22ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact22) 56 8 = 658000369035 :=
  combineSlices (auxiliaryColumnSlice contact22) 56 4 4 355598362343 302402006692 contact22ColumnsSlice56 contact22ColumnsSlice60
private theorem contact22ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact22) 64 8 = 463059893128 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 4 4 253672950872 209386942256 contact22ColumnsSlice64 contact22ColumnsSlice68
private theorem contact22ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact22) 72 8 = 303672955056 :=
  combineSlices (auxiliaryColumnSlice contact22) 72 4 4 169540475168 134132479888 contact22ColumnsSlice72 contact22ColumnsSlice76
private theorem contact22ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact22) 80 8 = 179853776681 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 4 4 103173406317 76680370364 contact22ColumnsSlice80 contact22ColumnsSlice84
private theorem contact22ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact22) 88 8 = 91583957111 :=
  combineSlices (auxiliaryColumnSlice contact22) 88 4 4 54627371930 36956585181 contact22ColumnsSlice88 contact22ColumnsSlice92
private theorem contact22ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact22) 96 8 = 37215526165 :=
  combineSlices (auxiliaryColumnSlice contact22) 96 4 4 23456374639 13759151526 contact22ColumnsSlice96 contact22ColumnsSlice100
private theorem contact22ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact22) 0 16 = 5593776716609 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 8 8 3018872370595 2574904346014 contact22ColumnsJoin0_8 contact22ColumnsJoin8_8
private theorem contact22ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact22) 16 16 = 3960086624639 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 8 8 2166458503762 1793628120877 contact22ColumnsJoin16_8 contact22ColumnsJoin24_8
private theorem contact22ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact22) 32 16 = 2611015077784 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 8 8 1456362242716 1154652835068 contact22ColumnsJoin32_8 contact22ColumnsJoin40_8
private theorem contact22ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact22) 48 16 = 1546564194418 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 8 8 888563825383 658000369035 contact22ColumnsJoin48_8 contact22ColumnsJoin56_8
private theorem contact22ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact22) 64 16 = 766732848184 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 8 8 463059893128 303672955056 contact22ColumnsJoin64_8 contact22ColumnsJoin72_8
private theorem contact22ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact22) 80 16 = 271437733792 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 8 8 179853776681 91583957111 contact22ColumnsJoin80_8 contact22ColumnsJoin88_8
private theorem contact22ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact22) 0 32 = 9553863341248 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 16 16 5593776716609 3960086624639 contact22ColumnsJoin0_16 contact22ColumnsJoin16_16
private theorem contact22ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact22) 32 32 = 4157579272202 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 16 16 2611015077784 1546564194418 contact22ColumnsJoin32_16 contact22ColumnsJoin48_16
private theorem contact22ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact22) 64 32 = 1038170581976 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 16 16 766732848184 271437733792 contact22ColumnsJoin64_16 contact22ColumnsJoin80_16
private theorem contact22ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact22) 0 64 = 13711442613450 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 32 32 9553863341248 4157579272202 contact22ColumnsJoin0_32 contact22ColumnsJoin32_32
private theorem contact22ColumnsJoin64_40 : sliceWindow (auxiliaryColumnSlice contact22) 64 40 = 1075386108141 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 32 8 1038170581976 37215526165 contact22ColumnsJoin64_32 contact22ColumnsJoin96_8
private theorem contact22ColumnsJoin0_104 : sliceWindow (auxiliaryColumnSlice contact22) 0 104 = 14786828721591 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 64 40 13711442613450 1075386108141 contact22ColumnsJoin0_64 contact22ColumnsJoin64_40
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
private theorem contact22RanksSlice100 : sliceWindow (auxiliaryRankSlice contact22) 100 4 = 0 :=
  contactRankWindow_of_rec contact22 100 4 0 (by decide +kernel)
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
private theorem contact22RanksJoin96_8 : sliceWindow (auxiliaryRankSlice contact22) 96 8 = 465 :=
  combineSlices (auxiliaryRankSlice contact22) 96 4 4 465 0 contact22RanksSlice96 contact22RanksSlice100
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
private theorem contact22RanksJoin64_40 : sliceWindow (auxiliaryRankSlice contact22) 64 40 = 1437595 :=
  combineSlices (auxiliaryRankSlice contact22) 64 32 8 1437130 465 contact22RanksJoin64_32 contact22RanksJoin96_8
private theorem contact22RanksJoin0_104 : sliceWindow (auxiliaryRankSlice contact22) 0 104 = 45010685 :=
  combineSlices (auxiliaryRankSlice contact22) 0 64 40 43573090 1437595 contact22RanksJoin0_64 contact22RanksJoin64_40
theorem contact22_margin : sourceMargin contact22 :=
  margin_of_checked_counts contact22 104 156955232083886 14786828721591 610133261 45010685 rfl contact22OrdinaryColumns contact22ColumnsJoin0_104 contact22OrdinaryRanks contact22RanksJoin0_104 (by decide +kernel)

private theorem contact24OrdinaryColumns : ordinaryColumnCount contact24 = 164500044350621 := by decide +kernel
private theorem contact24ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact24) 0 4 = 1369789109016 :=
  contactColumnsWindow_fast contact24 0 4 1369789109016 (by decide +kernel)
private theorem contact24ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact24) 4 4 = 1264246116312 :=
  contactColumnsWindow_fast contact24 4 4 1264246116312 (by decide +kernel)
private theorem contact24ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact24) 8 4 = 1162954936728 :=
  contactColumnsWindow_fast contact24 8 4 1162954936728 (by decide +kernel)
private theorem contact24ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact24) 12 4 = 1065933649968 :=
  contactColumnsWindow_fast contact24 12 4 1065933649968 (by decide +kernel)
private theorem contact24ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact24) 16 4 = 973182418909 :=
  contactColumnsWindow_fast contact24 16 4 973182418909 (by decide +kernel)
private theorem contact24ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact24) 20 4 = 884685547540 :=
  contactColumnsWindow_fast contact24 20 4 884685547540 (by decide +kernel)
private theorem contact24ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact24) 24 4 = 800442142704 :=
  contactColumnsWindow_fast contact24 24 4 800442142704 (by decide +kernel)
private theorem contact24ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact24) 28 4 = 720453513028 :=
  contactColumnsWindow_fast contact24 28 4 720453513028 (by decide +kernel)
private theorem contact24ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact24) 32 4 = 644739592938 :=
  contactColumnsWindow_fast contact24 32 4 644739592938 (by decide +kernel)
private theorem contact24ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact24) 36 4 = 573295855675 :=
  contactColumnsWindow_fast contact24 36 4 573295855675 (by decide +kernel)
private theorem contact24ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact24) 40 4 = 506107464452 :=
  contactColumnsWindow_fast contact24 40 4 506107464452 (by decide +kernel)
private theorem contact24ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact24) 44 4 = 443172358536 :=
  contactColumnsWindow_fast contact24 44 4 443172358536 (by decide +kernel)
private theorem contact24ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact24) 48 4 = 384492734346 :=
  contactColumnsWindow_fast contact24 48 4 384492734346 (by decide +kernel)
private theorem contact24ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact24) 52 4 = 330090040926 :=
  contactColumnsWindow_fast contact24 52 4 330090040926 (by decide +kernel)
private theorem contact24ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact24) 56 4 = 279954803401 :=
  contactColumnsWindow_fast contact24 56 4 279954803401 (by decide +kernel)
private theorem contact24ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact24) 60 4 = 234074892324 :=
  contactColumnsWindow_fast contact24 60 4 234074892324 (by decide +kernel)
private theorem contact24ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact24) 64 4 = 192448160028 :=
  contactColumnsWindow_fast contact24 64 4 192448160028 (by decide +kernel)
private theorem contact24ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact24) 68 4 = 155077788638 :=
  contactColumnsWindow_fast contact24 68 4 155077788638 (by decide +kernel)
private theorem contact24ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact24) 72 4 = 121985999874 :=
  contactColumnsWindow_fast contact24 72 4 121985999874 (by decide +kernel)
private theorem contact24ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact24) 76 4 = 93159292430 :=
  contactColumnsWindow_fast contact24 76 4 93159292430 (by decide +kernel)
private theorem contact24ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact24) 80 4 = 68587831156 :=
  contactColumnsWindow_fast contact24 80 4 68587831156 (by decide +kernel)
private theorem contact24ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact24) 84 4 = 48266739534 :=
  contactColumnsWindow_fast contact24 84 4 48266739534 (by decide +kernel)
private theorem contact24ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact24) 88 4 = 32136277052 :=
  contactColumnsWindow_fast contact24 88 4 32136277052 (by decide +kernel)
private theorem contact24ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact24) 92 4 = 19993430035 :=
  contactColumnsWindow_fast contact24 92 4 19993430035 (by decide +kernel)
private theorem contact24ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact24) 96 4 = 11427095763 :=
  contactColumnsWindow_fast contact24 96 4 11427095763 (by decide +kernel)
private theorem contact24ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact24) 0 8 = 2634035225328 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 4 4 1369789109016 1264246116312 contact24ColumnsSlice0 contact24ColumnsSlice4
private theorem contact24ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact24) 8 8 = 2228888586696 :=
  combineSlices (auxiliaryColumnSlice contact24) 8 4 4 1162954936728 1065933649968 contact24ColumnsSlice8 contact24ColumnsSlice12
private theorem contact24ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact24) 16 8 = 1857867966449 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 4 4 973182418909 884685547540 contact24ColumnsSlice16 contact24ColumnsSlice20
private theorem contact24ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact24) 24 8 = 1520895655732 :=
  combineSlices (auxiliaryColumnSlice contact24) 24 4 4 800442142704 720453513028 contact24ColumnsSlice24 contact24ColumnsSlice28
private theorem contact24ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact24) 32 8 = 1218035448613 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 4 4 644739592938 573295855675 contact24ColumnsSlice32 contact24ColumnsSlice36
private theorem contact24ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact24) 40 8 = 949279822988 :=
  combineSlices (auxiliaryColumnSlice contact24) 40 4 4 506107464452 443172358536 contact24ColumnsSlice40 contact24ColumnsSlice44
private theorem contact24ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact24) 48 8 = 714582775272 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 4 4 384492734346 330090040926 contact24ColumnsSlice48 contact24ColumnsSlice52
private theorem contact24ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact24) 56 8 = 514029695725 :=
  combineSlices (auxiliaryColumnSlice contact24) 56 4 4 279954803401 234074892324 contact24ColumnsSlice56 contact24ColumnsSlice60
private theorem contact24ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact24) 64 8 = 347525948666 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 4 4 192448160028 155077788638 contact24ColumnsSlice64 contact24ColumnsSlice68
private theorem contact24ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact24) 72 8 = 215145292304 :=
  combineSlices (auxiliaryColumnSlice contact24) 72 4 4 121985999874 93159292430 contact24ColumnsSlice72 contact24ColumnsSlice76
private theorem contact24ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact24) 80 8 = 116854570690 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 4 4 68587831156 48266739534 contact24ColumnsSlice80 contact24ColumnsSlice84
private theorem contact24ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact24) 88 8 = 52129707087 :=
  combineSlices (auxiliaryColumnSlice contact24) 88 4 4 32136277052 19993430035 contact24ColumnsSlice88 contact24ColumnsSlice92
private theorem contact24ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact24) 0 16 = 4862923812024 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 8 8 2634035225328 2228888586696 contact24ColumnsJoin0_8 contact24ColumnsJoin8_8
private theorem contact24ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact24) 16 16 = 3378763622181 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 8 8 1857867966449 1520895655732 contact24ColumnsJoin16_8 contact24ColumnsJoin24_8
private theorem contact24ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact24) 32 16 = 2167315271601 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 8 8 1218035448613 949279822988 contact24ColumnsJoin32_8 contact24ColumnsJoin40_8
private theorem contact24ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact24) 48 16 = 1228612470997 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 8 8 714582775272 514029695725 contact24ColumnsJoin48_8 contact24ColumnsJoin56_8
private theorem contact24ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact24) 64 16 = 562671240970 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 8 8 347525948666 215145292304 contact24ColumnsJoin64_8 contact24ColumnsJoin72_8
private theorem contact24ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact24) 80 16 = 168984277777 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 8 8 116854570690 52129707087 contact24ColumnsJoin80_8 contact24ColumnsJoin88_8
private theorem contact24ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact24) 0 32 = 8241687434205 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 16 16 4862923812024 3378763622181 contact24ColumnsJoin0_16 contact24ColumnsJoin16_16
private theorem contact24ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact24) 32 32 = 3395927742598 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 16 16 2167315271601 1228612470997 contact24ColumnsJoin32_16 contact24ColumnsJoin48_16
private theorem contact24ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact24) 64 32 = 731655518747 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 16 16 562671240970 168984277777 contact24ColumnsJoin64_16 contact24ColumnsJoin80_16
private theorem contact24ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact24) 0 64 = 11637615176803 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 32 32 8241687434205 3395927742598 contact24ColumnsJoin0_32 contact24ColumnsJoin32_32
private theorem contact24ColumnsJoin64_36 : sliceWindow (auxiliaryColumnSlice contact24) 64 36 = 743082614510 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 32 4 731655518747 11427095763 contact24ColumnsJoin64_32 contact24ColumnsSlice96
private theorem contact24ColumnsJoin0_100 : sliceWindow (auxiliaryColumnSlice contact24) 0 100 = 12380697791313 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 64 36 11637615176803 743082614510 contact24ColumnsJoin0_64 contact24ColumnsJoin64_36
private theorem contact24OrdinaryRanks : ordinaryRankBound contact24 = 636901281 := by decide +kernel
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
  margin_of_checked_counts contact24 100 164500044350621 12380697791313 636901281 37844672 rfl contact24OrdinaryColumns contact24ColumnsJoin0_100 contact24OrdinaryRanks contact24RanksJoin0_100 (by decide +kernel)

private theorem contact26OrdinaryColumns : ordinaryColumnCount contact26 = 162054937430331 := by decide +kernel
private theorem contact26ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact26) 0 4 = 1856118877424 :=
  contactColumnsWindow_fast contact26 0 4 1856118877424 (by decide +kernel)
private theorem contact26ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact26) 4 4 = 1724633576192 :=
  contactColumnsWindow_fast contact26 4 4 1724633576192 (by decide +kernel)
private theorem contact26ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact26) 8 4 = 1598000887760 :=
  contactColumnsWindow_fast contact26 8 4 1598000887760 (by decide +kernel)
private theorem contact26ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact26) 12 4 = 1476233560493 :=
  contactColumnsWindow_fast contact26 12 4 1476233560493 (by decide +kernel)
private theorem contact26ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact26) 16 4 = 1359347358860 :=
  contactColumnsWindow_fast contact26 16 4 1359347358860 (by decide +kernel)
private theorem contact26ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact26) 20 4 = 1247316598352 :=
  contactColumnsWindow_fast contact26 20 4 1247316598352 (by decide +kernel)
private theorem contact26ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact26) 24 4 = 1140141039712 :=
  contactColumnsWindow_fast contact26 24 4 1140141039712 (by decide +kernel)
private theorem contact26ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact26) 28 4 = 1037820576692 :=
  contactColumnsWindow_fast contact26 28 4 1037820576692 (by decide +kernel)
private theorem contact26ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact26) 32 4 = 940370551352 :=
  contactColumnsWindow_fast contact26 32 4 940370551352 (by decide +kernel)
private theorem contact26ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact26) 36 4 = 847802829908 :=
  contactColumnsWindow_fast contact26 36 4 847802829908 (by decide +kernel)
private theorem contact26ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact26) 40 4 = 760091613436 :=
  contactColumnsWindow_fast contact26 40 4 760091613436 (by decide +kernel)
private theorem contact26ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact26) 44 4 = 677235205538 :=
  contactColumnsWindow_fast contact26 44 4 677235205538 (by decide +kernel)
private theorem contact26ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact26) 48 4 = 599234297804 :=
  contactColumnsWindow_fast contact26 48 4 599234297804 (by decide +kernel)
private theorem contact26ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact26) 52 4 = 526107336152 :=
  contactColumnsWindow_fast contact26 52 4 526107336152 (by decide +kernel)
private theorem contact26ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact26) 56 4 = 457859155856 :=
  contactColumnsWindow_fast contact26 56 4 457859155856 (by decide +kernel)
private theorem contact26ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact26) 60 4 = 394467483420 :=
  contactColumnsWindow_fast contact26 60 4 394467483420 (by decide +kernel)
private theorem contact26ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact26) 64 4 = 335930323229 :=
  contactColumnsWindow_fast contact26 64 4 335930323229 (by decide +kernel)
private theorem contact26ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact26) 68 4 = 282248873816 :=
  contactColumnsWindow_fast contact26 68 4 282248873816 (by decide +kernel)
private theorem contact26ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact26) 72 4 = 233445043985 :=
  contactColumnsWindow_fast contact26 72 4 233445043985 (by decide +kernel)
private theorem contact26ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact26) 76 4 = 189516401238 :=
  contactColumnsWindow_fast contact26 76 4 189516401238 (by decide +kernel)
private theorem contact26ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact26) 80 4 = 150444208304 :=
  contactColumnsWindow_fast contact26 80 4 150444208304 (by decide +kernel)
private theorem contact26ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact26) 84 4 = 116226295820 :=
  contactColumnsWindow_fast contact26 84 4 116226295820 (by decide +kernel)
private theorem contact26ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact26) 88 4 = 86864502311 :=
  contactColumnsWindow_fast contact26 88 4 86864502311 (by decide +kernel)
private theorem contact26ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact26) 92 4 = 62379610089 :=
  contactColumnsWindow_fast contact26 92 4 62379610089 (by decide +kernel)
private theorem contact26ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact26) 96 4 = 42686648173 :=
  contactColumnsWindow_fast contact26 96 4 42686648173 (by decide +kernel)
private theorem contact26ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact26) 100 4 = 27529969918 :=
  contactColumnsWindow_fast contact26 100 4 27529969918 (by decide +kernel)
private theorem contact26ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact26) 104 3 = 13204831714 :=
  contactColumnsWindow_fast contact26 104 3 13204831714 (by decide +kernel)
private theorem contact26ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact26) 0 8 = 3580752453616 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 4 4 1856118877424 1724633576192 contact26ColumnsSlice0 contact26ColumnsSlice4
private theorem contact26ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact26) 8 8 = 3074234448253 :=
  combineSlices (auxiliaryColumnSlice contact26) 8 4 4 1598000887760 1476233560493 contact26ColumnsSlice8 contact26ColumnsSlice12
private theorem contact26ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact26) 16 8 = 2606663957212 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 4 4 1359347358860 1247316598352 contact26ColumnsSlice16 contact26ColumnsSlice20
private theorem contact26ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact26) 24 8 = 2177961616404 :=
  combineSlices (auxiliaryColumnSlice contact26) 24 4 4 1140141039712 1037820576692 contact26ColumnsSlice24 contact26ColumnsSlice28
private theorem contact26ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact26) 32 8 = 1788173381260 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 4 4 940370551352 847802829908 contact26ColumnsSlice32 contact26ColumnsSlice36
private theorem contact26ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact26) 40 8 = 1437326818974 :=
  combineSlices (auxiliaryColumnSlice contact26) 40 4 4 760091613436 677235205538 contact26ColumnsSlice40 contact26ColumnsSlice44
private theorem contact26ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact26) 48 8 = 1125341633956 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 4 4 599234297804 526107336152 contact26ColumnsSlice48 contact26ColumnsSlice52
private theorem contact26ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact26) 56 8 = 852326639276 :=
  combineSlices (auxiliaryColumnSlice contact26) 56 4 4 457859155856 394467483420 contact26ColumnsSlice56 contact26ColumnsSlice60
private theorem contact26ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact26) 64 8 = 618179197045 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 4 4 335930323229 282248873816 contact26ColumnsSlice64 contact26ColumnsSlice68
private theorem contact26ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact26) 72 8 = 422961445223 :=
  combineSlices (auxiliaryColumnSlice contact26) 72 4 4 233445043985 189516401238 contact26ColumnsSlice72 contact26ColumnsSlice76
private theorem contact26ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact26) 80 8 = 266670504124 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 4 4 150444208304 116226295820 contact26ColumnsSlice80 contact26ColumnsSlice84
private theorem contact26ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact26) 88 8 = 149244112400 :=
  combineSlices (auxiliaryColumnSlice contact26) 88 4 4 86864502311 62379610089 contact26ColumnsSlice88 contact26ColumnsSlice92
private theorem contact26ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact26) 96 8 = 70216618091 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 4 4 42686648173 27529969918 contact26ColumnsSlice96 contact26ColumnsSlice100
private theorem contact26ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact26) 0 16 = 6654986901869 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 8 8 3580752453616 3074234448253 contact26ColumnsJoin0_8 contact26ColumnsJoin8_8
private theorem contact26ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact26) 16 16 = 4784625573616 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 8 8 2606663957212 2177961616404 contact26ColumnsJoin16_8 contact26ColumnsJoin24_8
private theorem contact26ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact26) 32 16 = 3225500200234 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 8 8 1788173381260 1437326818974 contact26ColumnsJoin32_8 contact26ColumnsJoin40_8
private theorem contact26ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact26) 48 16 = 1977668273232 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 8 8 1125341633956 852326639276 contact26ColumnsJoin48_8 contact26ColumnsJoin56_8
private theorem contact26ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact26) 64 16 = 1041140642268 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 8 8 618179197045 422961445223 contact26ColumnsJoin64_8 contact26ColumnsJoin72_8
private theorem contact26ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact26) 80 16 = 415914616524 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 8 8 266670504124 149244112400 contact26ColumnsJoin80_8 contact26ColumnsJoin88_8
private theorem contact26ColumnsJoin96_11 : sliceWindow (auxiliaryColumnSlice contact26) 96 11 = 83421449805 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 8 3 70216618091 13204831714 contact26ColumnsJoin96_8 contact26ColumnsSlice104
private theorem contact26ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact26) 0 32 = 11439612475485 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 16 16 6654986901869 4784625573616 contact26ColumnsJoin0_16 contact26ColumnsJoin16_16
private theorem contact26ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact26) 32 32 = 5203168473466 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 16 16 3225500200234 1977668273232 contact26ColumnsJoin32_16 contact26ColumnsJoin48_16
private theorem contact26ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact26) 64 32 = 1457055258792 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 16 16 1041140642268 415914616524 contact26ColumnsJoin64_16 contact26ColumnsJoin80_16
private theorem contact26ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact26) 0 64 = 16642780948951 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 32 32 11439612475485 5203168473466 contact26ColumnsJoin0_32 contact26ColumnsJoin32_32
private theorem contact26ColumnsJoin64_43 : sliceWindow (auxiliaryColumnSlice contact26) 64 43 = 1540476708597 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 32 11 1457055258792 83421449805 contact26ColumnsJoin64_32 contact26ColumnsJoin96_11
private theorem contact26ColumnsJoin0_107 : sliceWindow (auxiliaryColumnSlice contact26) 0 107 = 18183257657548 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 64 43 16642780948951 1540476708597 contact26ColumnsJoin0_64 contact26ColumnsJoin64_43
private theorem contact26OrdinaryRanks : ordinaryRankBound contact26 = 632211446 := by decide +kernel
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
private theorem contact26RanksSlice104 : sliceWindow (auxiliaryRankSlice contact26) 104 3 = 0 :=
  contactRankWindow_of_rec contact26 104 3 0 (by decide +kernel)
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
private theorem contact26RanksJoin96_11 : sliceWindow (auxiliaryRankSlice contact26) 96 11 = 9621 :=
  combineSlices (auxiliaryRankSlice contact26) 96 8 3 9621 0 contact26RanksJoin96_8 contact26RanksSlice104
private theorem contact26RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact26) 0 32 = 39556848 :=
  combineSlices (auxiliaryRankSlice contact26) 0 16 16 24079224 15477624 contact26RanksJoin0_16 contact26RanksJoin16_16
private theorem contact26RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact26) 32 32 = 13575702 :=
  combineSlices (auxiliaryRankSlice contact26) 32 16 16 9016747 4558955 contact26RanksJoin32_16 contact26RanksJoin48_16
private theorem contact26RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact26) 64 32 = 2197293 :=
  combineSlices (auxiliaryRankSlice contact26) 64 16 16 1798085 399208 contact26RanksJoin64_16 contact26RanksJoin80_16
private theorem contact26RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact26) 0 64 = 53132550 :=
  combineSlices (auxiliaryRankSlice contact26) 0 32 32 39556848 13575702 contact26RanksJoin0_32 contact26RanksJoin32_32
private theorem contact26RanksJoin64_43 : sliceWindow (auxiliaryRankSlice contact26) 64 43 = 2206914 :=
  combineSlices (auxiliaryRankSlice contact26) 64 32 11 2197293 9621 contact26RanksJoin64_32 contact26RanksJoin96_11
private theorem contact26RanksJoin0_107 : sliceWindow (auxiliaryRankSlice contact26) 0 107 = 55339464 :=
  combineSlices (auxiliaryRankSlice contact26) 0 64 43 53132550 2206914 contact26RanksJoin0_64 contact26RanksJoin64_43
theorem contact26_margin : sourceMargin contact26 :=
  margin_of_checked_counts contact26 107 162054937430331 18183257657548 632211446 55339464 rfl contact26OrdinaryColumns contact26ColumnsJoin0_107 contact26OrdinaryRanks contact26RanksJoin0_107 (by decide +kernel)

private theorem contact28OrdinaryColumns : ordinaryColumnCount contact28 = 215764483649405 := by decide +kernel
private theorem contact28ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact28) 0 4 = 898966191304 :=
  contactColumnsWindow_fast contact28 0 4 898966191304 (by decide +kernel)
private theorem contact28ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact28) 4 4 = 823757593272 :=
  contactColumnsWindow_fast contact28 4 4 823757593272 (by decide +kernel)
private theorem contact28ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact28) 8 4 = 751849403533 :=
  contactColumnsWindow_fast contact28 8 4 751849403533 (by decide +kernel)
private theorem contact28ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact28) 12 4 = 683259077196 :=
  contactColumnsWindow_fast contact28 12 4 683259077196 (by decide +kernel)
private theorem contact28ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact28) 16 4 = 617976925865 :=
  contactColumnsWindow_fast contact28 16 4 617976925865 (by decide +kernel)
private theorem contact28ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact28) 20 4 = 555997152232 :=
  contactColumnsWindow_fast contact28 20 4 555997152232 (by decide +kernel)
private theorem contact28ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact28) 24 4 = 497318314910 :=
  contactColumnsWindow_fast contact28 24 4 497318314910 (by decide +kernel)
private theorem contact28ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact28) 28 4 = 441943306949 :=
  contactColumnsWindow_fast contact28 28 4 441943306949 (by decide +kernel)
private theorem contact28ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact28) 32 4 = 389888616494 :=
  contactColumnsWindow_fast contact28 32 4 389888616494 (by decide +kernel)
private theorem contact28ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact28) 36 4 = 341143354028 :=
  contactColumnsWindow_fast contact28 36 4 341143354028 (by decide +kernel)
private theorem contact28ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact28) 40 4 = 295700780212 :=
  contactColumnsWindow_fast contact28 40 4 295700780212 (by decide +kernel)
private theorem contact28ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact28) 44 4 = 253559131152 :=
  contactColumnsWindow_fast contact28 44 4 253559131152 (by decide +kernel)
private theorem contact28ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact28) 48 4 = 214722112134 :=
  contactColumnsWindow_fast contact28 48 4 214722112134 (by decide +kernel)
private theorem contact28ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact28) 52 4 = 179206367642 :=
  contactColumnsWindow_fast contact28 52 4 179206367642 (by decide +kernel)
private theorem contact28ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact28) 56 4 = 146998384874 :=
  contactColumnsWindow_fast contact28 56 4 146998384874 (by decide +kernel)
private theorem contact28ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact28) 60 4 = 118092989524 :=
  contactColumnsWindow_fast contact28 60 4 118092989524 (by decide +kernel)
private theorem contact28ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact28) 64 4 = 92488566981 :=
  contactColumnsWindow_fast contact28 64 4 92488566981 (by decide +kernel)
private theorem contact28ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact28) 68 4 = 70189932266 :=
  contactColumnsWindow_fast contact28 68 4 70189932266 (by decide +kernel)
private theorem contact28ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact28) 72 4 = 51212710741 :=
  contactColumnsWindow_fast contact28 72 4 51212710741 (by decide +kernel)
private theorem contact28ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact28) 76 4 = 35541953195 :=
  contactColumnsWindow_fast contact28 76 4 35541953195 (by decide +kernel)
private theorem contact28ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact28) 80 4 = 23157919861 :=
  contactColumnsWindow_fast contact28 80 4 23157919861 (by decide +kernel)
private theorem contact28ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact28) 84 4 = 13931189790 :=
  contactColumnsWindow_fast contact28 84 4 13931189790 (by decide +kernel)
private theorem contact28ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact28) 88 4 = 7568762715 :=
  contactColumnsWindow_fast contact28 88 4 7568762715 (by decide +kernel)
private theorem contact28ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact28) 92 3 = 2973911947 :=
  contactColumnsWindow_fast contact28 92 3 2973911947 (by decide +kernel)
private theorem contact28ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact28) 0 8 = 1722723784576 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 4 4 898966191304 823757593272 contact28ColumnsSlice0 contact28ColumnsSlice4
private theorem contact28ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact28) 8 8 = 1435108480729 :=
  combineSlices (auxiliaryColumnSlice contact28) 8 4 4 751849403533 683259077196 contact28ColumnsSlice8 contact28ColumnsSlice12
private theorem contact28ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact28) 16 8 = 1173974078097 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 4 4 617976925865 555997152232 contact28ColumnsSlice16 contact28ColumnsSlice20
private theorem contact28ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact28) 24 8 = 939261621859 :=
  combineSlices (auxiliaryColumnSlice contact28) 24 4 4 497318314910 441943306949 contact28ColumnsSlice24 contact28ColumnsSlice28
private theorem contact28ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact28) 32 8 = 731031970522 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 4 4 389888616494 341143354028 contact28ColumnsSlice32 contact28ColumnsSlice36
private theorem contact28ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact28) 40 8 = 549259911364 :=
  combineSlices (auxiliaryColumnSlice contact28) 40 4 4 295700780212 253559131152 contact28ColumnsSlice40 contact28ColumnsSlice44
private theorem contact28ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact28) 48 8 = 393928479776 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 4 4 214722112134 179206367642 contact28ColumnsSlice48 contact28ColumnsSlice52
private theorem contact28ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact28) 56 8 = 265091374398 :=
  combineSlices (auxiliaryColumnSlice contact28) 56 4 4 146998384874 118092989524 contact28ColumnsSlice56 contact28ColumnsSlice60
private theorem contact28ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact28) 64 8 = 162678499247 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 4 4 92488566981 70189932266 contact28ColumnsSlice64 contact28ColumnsSlice68
private theorem contact28ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact28) 72 8 = 86754663936 :=
  combineSlices (auxiliaryColumnSlice contact28) 72 4 4 51212710741 35541953195 contact28ColumnsSlice72 contact28ColumnsSlice76
private theorem contact28ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact28) 80 8 = 37089109651 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 4 4 23157919861 13931189790 contact28ColumnsSlice80 contact28ColumnsSlice84
private theorem contact28ColumnsJoin88_7 : sliceWindow (auxiliaryColumnSlice contact28) 88 7 = 10542674662 :=
  combineSlices (auxiliaryColumnSlice contact28) 88 4 3 7568762715 2973911947 contact28ColumnsSlice88 contact28ColumnsSlice92
private theorem contact28ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact28) 0 16 = 3157832265305 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 8 8 1722723784576 1435108480729 contact28ColumnsJoin0_8 contact28ColumnsJoin8_8
private theorem contact28ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact28) 16 16 = 2113235699956 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 8 8 1173974078097 939261621859 contact28ColumnsJoin16_8 contact28ColumnsJoin24_8
private theorem contact28ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact28) 32 16 = 1280291881886 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 8 8 731031970522 549259911364 contact28ColumnsJoin32_8 contact28ColumnsJoin40_8
private theorem contact28ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact28) 48 16 = 659019854174 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 8 8 393928479776 265091374398 contact28ColumnsJoin48_8 contact28ColumnsJoin56_8
private theorem contact28ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact28) 64 16 = 249433163183 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 8 8 162678499247 86754663936 contact28ColumnsJoin64_8 contact28ColumnsJoin72_8
private theorem contact28ColumnsJoin80_15 : sliceWindow (auxiliaryColumnSlice contact28) 80 15 = 47631784313 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 8 7 37089109651 10542674662 contact28ColumnsJoin80_8 contact28ColumnsJoin88_7
private theorem contact28ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact28) 0 32 = 5271067965261 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 16 16 3157832265305 2113235699956 contact28ColumnsJoin0_16 contact28ColumnsJoin16_16
private theorem contact28ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact28) 32 32 = 1939311736060 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 16 16 1280291881886 659019854174 contact28ColumnsJoin32_16 contact28ColumnsJoin48_16
private theorem contact28ColumnsJoin64_31 : sliceWindow (auxiliaryColumnSlice contact28) 64 31 = 297064947496 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 16 15 249433163183 47631784313 contact28ColumnsJoin64_16 contact28ColumnsJoin80_15
private theorem contact28ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact28) 0 64 = 7210379701321 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 32 32 5271067965261 1939311736060 contact28ColumnsJoin0_32 contact28ColumnsJoin32_32
private theorem contact28ColumnsJoin0_95 : sliceWindow (auxiliaryColumnSlice contact28) 0 95 = 7507444648817 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 64 31 7210379701321 297064947496 contact28ColumnsJoin0_64 contact28ColumnsJoin64_31
private theorem contact28OrdinaryRanks : ordinaryRankBound contact28 = 828846348 := by decide +kernel
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
  margin_of_checked_counts contact28 95 215764483649405 7507444648817 828846348 22868078 rfl contact28OrdinaryColumns contact28ColumnsJoin0_95 contact28OrdinaryRanks contact28RanksJoin0_95 (by decide +kernel)

private theorem contact30OrdinaryColumns : ordinaryColumnCount contact30 = 521515497672206 := by decide +kernel
private theorem contact30ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact30) 0 4 = 1936716334658 :=
  contactColumnsWindow_fast contact30 0 4 1936716334658 (by decide +kernel)
private theorem contact30ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact30) 4 4 = 1802345227682 :=
  contactColumnsWindow_fast contact30 4 4 1802345227682 (by decide +kernel)
private theorem contact30ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact30) 8 4 = 1672829156882 :=
  contactColumnsWindow_fast contact30 8 4 1672829156882 (by decide +kernel)
private theorem contact30ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact30) 12 4 = 1548167994578 :=
  contactColumnsWindow_fast contact30 12 4 1548167994578 (by decide +kernel)
private theorem contact30ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact30) 16 4 = 1428361988058 :=
  contactColumnsWindow_fast contact30 16 4 1428361988058 (by decide +kernel)
private theorem contact30ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact30) 20 4 = 1313426115344 :=
  contactColumnsWindow_fast contact30 20 4 1313426115344 (by decide +kernel)
private theorem contact30ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact30) 24 4 = 1203368475974 :=
  contactColumnsWindow_fast contact30 24 4 1203368475974 (by decide +kernel)
private theorem contact30ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact30) 28 4 = 1098167386238 :=
  contactColumnsWindow_fast contact30 28 4 1098167386238 (by decide +kernel)
private theorem contact30ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact30) 32 4 = 997824405699 :=
  contactColumnsWindow_fast contact30 32 4 997824405699 (by decide +kernel)
private theorem contact30ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact30) 36 4 = 902337891350 :=
  contactColumnsWindow_fast contact30 36 4 902337891350 (by decide +kernel)
private theorem contact30ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact30) 40 4 = 811724763515 :=
  contactColumnsWindow_fast contact30 40 4 811724763515 (by decide +kernel)
private theorem contact30ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact30) 44 4 = 725986590110 :=
  contactColumnsWindow_fast contact30 44 4 725986590110 (by decide +kernel)
private theorem contact30ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact30) 48 4 = 645105200504 :=
  contactColumnsWindow_fast contact30 48 4 645105200504 (by decide +kernel)
private theorem contact30ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact30) 52 4 = 569081720264 :=
  contactColumnsWindow_fast contact30 52 4 569081720264 (by decide +kernel)
private theorem contact30ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact30) 56 4 = 497914649542 :=
  contactColumnsWindow_fast contact30 56 4 497914649542 (by decide +kernel)
private theorem contact30ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact30) 60 4 = 431624290494 :=
  contactColumnsWindow_fast contact30 60 4 431624290494 (by decide +kernel)
private theorem contact30ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact30) 64 4 = 370205647013 :=
  contactColumnsWindow_fast contact30 64 4 370205647013 (by decide +kernel)
private theorem contact30ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact30) 68 4 = 313643906750 :=
  contactColumnsWindow_fast contact30 68 4 313643906750 (by decide +kernel)
private theorem contact30ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact30) 72 4 = 261939889729 :=
  contactColumnsWindow_fast contact30 72 4 261939889729 (by decide +kernel)
private theorem contact30ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact30) 76 4 = 215092823226 :=
  contactColumnsWindow_fast contact30 76 4 215092823226 (by decide +kernel)
private theorem contact30ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact30) 80 4 = 173124753772 :=
  contactColumnsWindow_fast contact30 80 4 173124753772 (by decide +kernel)
private theorem contact30ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact30) 84 4 = 136025558816 :=
  contactColumnsWindow_fast contact30 84 4 136025558816 (by decide +kernel)
private theorem contact30ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact30) 88 4 = 103783467896 :=
  contactColumnsWindow_fast contact30 88 4 103783467896 (by decide +kernel)
private theorem contact30ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact30) 92 4 = 76398953589 :=
  contactColumnsWindow_fast contact30 92 4 76398953589 (by decide +kernel)
private theorem contact30ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact30) 96 4 = 53856456055 :=
  contactColumnsWindow_fast contact30 96 4 53856456055 (by decide +kernel)
private theorem contact30ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact30) 100 4 = 36045470300 :=
  contactColumnsWindow_fast contact30 100 4 36045470300 (by decide +kernel)
private theorem contact30ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact30) 104 4 = 22638423648 :=
  contactColumnsWindow_fast contact30 104 4 22638423648 (by decide +kernel)
private theorem contact30ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact30) 108 4 = 13149367130 :=
  contactColumnsWindow_fast contact30 108 4 13149367130 (by decide +kernel)
private theorem contact30ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact30) 112 4 = 6940651251 :=
  contactColumnsWindow_fast contact30 112 4 6940651251 (by decide +kernel)
private theorem contact30ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact30) 0 8 = 3739061562340 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 4 4 1936716334658 1802345227682 contact30ColumnsSlice0 contact30ColumnsSlice4
private theorem contact30ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact30) 8 8 = 3220997151460 :=
  combineSlices (auxiliaryColumnSlice contact30) 8 4 4 1672829156882 1548167994578 contact30ColumnsSlice8 contact30ColumnsSlice12
private theorem contact30ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact30) 16 8 = 2741788103402 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 4 4 1428361988058 1313426115344 contact30ColumnsSlice16 contact30ColumnsSlice20
private theorem contact30ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact30) 24 8 = 2301535862212 :=
  combineSlices (auxiliaryColumnSlice contact30) 24 4 4 1203368475974 1098167386238 contact30ColumnsSlice24 contact30ColumnsSlice28
private theorem contact30ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact30) 32 8 = 1900162297049 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 4 4 997824405699 902337891350 contact30ColumnsSlice32 contact30ColumnsSlice36
private theorem contact30ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact30) 40 8 = 1537711353625 :=
  combineSlices (auxiliaryColumnSlice contact30) 40 4 4 811724763515 725986590110 contact30ColumnsSlice40 contact30ColumnsSlice44
private theorem contact30ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact30) 48 8 = 1214186920768 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 4 4 645105200504 569081720264 contact30ColumnsSlice48 contact30ColumnsSlice52
private theorem contact30ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact30) 56 8 = 929538940036 :=
  combineSlices (auxiliaryColumnSlice contact30) 56 4 4 497914649542 431624290494 contact30ColumnsSlice56 contact30ColumnsSlice60
private theorem contact30ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact30) 64 8 = 683849553763 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 4 4 370205647013 313643906750 contact30ColumnsSlice64 contact30ColumnsSlice68
private theorem contact30ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact30) 72 8 = 477032712955 :=
  combineSlices (auxiliaryColumnSlice contact30) 72 4 4 261939889729 215092823226 contact30ColumnsSlice72 contact30ColumnsSlice76
private theorem contact30ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact30) 80 8 = 309150312588 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 4 4 173124753772 136025558816 contact30ColumnsSlice80 contact30ColumnsSlice84
private theorem contact30ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact30) 88 8 = 180182421485 :=
  combineSlices (auxiliaryColumnSlice contact30) 88 4 4 103783467896 76398953589 contact30ColumnsSlice88 contact30ColumnsSlice92
private theorem contact30ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact30) 96 8 = 89901926355 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 4 4 53856456055 36045470300 contact30ColumnsSlice96 contact30ColumnsSlice100
private theorem contact30ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact30) 104 8 = 35787790778 :=
  combineSlices (auxiliaryColumnSlice contact30) 104 4 4 22638423648 13149367130 contact30ColumnsSlice104 contact30ColumnsSlice108
private theorem contact30ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact30) 0 16 = 6960058713800 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 8 8 3739061562340 3220997151460 contact30ColumnsJoin0_8 contact30ColumnsJoin8_8
private theorem contact30ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact30) 16 16 = 5043323965614 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 8 8 2741788103402 2301535862212 contact30ColumnsJoin16_8 contact30ColumnsJoin24_8
private theorem contact30ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact30) 32 16 = 3437873650674 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 8 8 1900162297049 1537711353625 contact30ColumnsJoin32_8 contact30ColumnsJoin40_8
private theorem contact30ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact30) 48 16 = 2143725860804 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 8 8 1214186920768 929538940036 contact30ColumnsJoin48_8 contact30ColumnsJoin56_8
private theorem contact30ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact30) 64 16 = 1160882266718 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 8 8 683849553763 477032712955 contact30ColumnsJoin64_8 contact30ColumnsJoin72_8
private theorem contact30ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact30) 80 16 = 489332734073 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 8 8 309150312588 180182421485 contact30ColumnsJoin80_8 contact30ColumnsJoin88_8
private theorem contact30ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact30) 96 16 = 125689717133 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 8 8 89901926355 35787790778 contact30ColumnsJoin96_8 contact30ColumnsJoin104_8
private theorem contact30ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact30) 0 32 = 12003382679414 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 16 16 6960058713800 5043323965614 contact30ColumnsJoin0_16 contact30ColumnsJoin16_16
private theorem contact30ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact30) 32 32 = 5581599511478 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 16 16 3437873650674 2143725860804 contact30ColumnsJoin32_16 contact30ColumnsJoin48_16
private theorem contact30ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact30) 64 32 = 1650215000791 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 16 16 1160882266718 489332734073 contact30ColumnsJoin64_16 contact30ColumnsJoin80_16
private theorem contact30ColumnsJoin96_20 : sliceWindow (auxiliaryColumnSlice contact30) 96 20 = 132630368384 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 16 4 125689717133 6940651251 contact30ColumnsJoin96_16 contact30ColumnsSlice112
private theorem contact30ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact30) 0 64 = 17584982190892 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 32 32 12003382679414 5581599511478 contact30ColumnsJoin0_32 contact30ColumnsJoin32_32
private theorem contact30ColumnsJoin64_52 : sliceWindow (auxiliaryColumnSlice contact30) 64 52 = 1782845369175 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 32 20 1650215000791 132630368384 contact30ColumnsJoin64_32 contact30ColumnsJoin96_20
private theorem contact30ColumnsJoin0_116 : sliceWindow (auxiliaryColumnSlice contact30) 0 116 = 19367827560067 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 64 52 17584982190892 1782845369175 contact30ColumnsJoin0_64 contact30ColumnsJoin64_52
private theorem contact30OrdinaryRanks : ordinaryRankBound contact30 = 2004241665 := by decide +kernel
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
private theorem contact30RanksSlice104 : sliceWindow (auxiliaryRankSlice contact30) 104 12 = 0 :=
  contactRankWindow_of_rec contact30 104 12 0 (by decide +kernel)
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
private theorem contact30RanksJoin96_20 : sliceWindow (auxiliaryRankSlice contact30) 96 20 = 21446 :=
  combineSlices (auxiliaryRankSlice contact30) 96 8 12 21446 0 contact30RanksJoin96_8 contact30RanksSlice104
private theorem contact30RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact30) 0 32 = 41741712 :=
  combineSlices (auxiliaryRankSlice contact30) 0 16 16 25306056 16435656 contact30RanksJoin0_16 contact30RanksJoin16_16
private theorem contact30RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact30) 32 32 = 14727092 :=
  combineSlices (auxiliaryRankSlice contact30) 32 16 16 9710121 5016971 contact30RanksJoin32_16 contact30RanksJoin48_16
private theorem contact30RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact30) 64 32 = 2573741 :=
  combineSlices (auxiliaryRankSlice contact30) 64 16 16 2062174 511567 contact30RanksJoin64_16 contact30RanksJoin80_16
private theorem contact30RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact30) 0 64 = 56468804 :=
  combineSlices (auxiliaryRankSlice contact30) 0 32 32 41741712 14727092 contact30RanksJoin0_32 contact30RanksJoin32_32
private theorem contact30RanksJoin64_52 : sliceWindow (auxiliaryRankSlice contact30) 64 52 = 2595187 :=
  combineSlices (auxiliaryRankSlice contact30) 64 32 20 2573741 21446 contact30RanksJoin64_32 contact30RanksJoin96_20
private theorem contact30RanksJoin0_116 : sliceWindow (auxiliaryRankSlice contact30) 0 116 = 59063991 :=
  combineSlices (auxiliaryRankSlice contact30) 0 64 52 56468804 2595187 contact30RanksJoin0_64 contact30RanksJoin64_52
theorem contact30_margin : sourceMargin contact30 :=
  margin_of_checked_counts contact30 116 521515497672206 19367827560067 2004241665 59063991 rfl contact30OrdinaryColumns contact30ColumnsJoin0_116 contact30OrdinaryRanks contact30RanksJoin0_116 (by decide +kernel)

private theorem contact32OrdinaryColumns : ordinaryColumnCount contact32 = 534760250931393 := by decide +kernel
private theorem contact32ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact32) 0 4 = 1997735104247 :=
  contactColumnsWindow_fast contact32 0 4 1997735104247 (by decide +kernel)
private theorem contact32ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact32) 4 4 = 1858596860076 :=
  contactColumnsWindow_fast contact32 4 4 1858596860076 (by decide +kernel)
private theorem contact32ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact32) 8 4 = 1724507831036 :=
  contactColumnsWindow_fast contact32 8 4 1724507831036 (by decide +kernel)
private theorem contact32ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact32) 12 4 = 1595467873948 :=
  contactColumnsWindow_fast contact32 12 4 1595467873948 (by decide +kernel)
private theorem contact32ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact32) 16 4 = 1471477239096 :=
  contactColumnsWindow_fast contact32 16 4 1471477239096 (by decide +kernel)
private theorem contact32ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact32) 20 4 = 1352551630950 :=
  contactColumnsWindow_fast contact32 20 4 1352551630950 (by decide +kernel)
private theorem contact32ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact32) 24 4 = 1238699506716 :=
  contactColumnsWindow_fast contact32 24 4 1238699506716 (by decide +kernel)
private theorem contact32ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact32) 28 4 = 1129898133245 :=
  contactColumnsWindow_fast contact32 28 4 1129898133245 (by decide +kernel)
private theorem contact32ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact32) 32 4 = 1026149102293 :=
  contactColumnsWindow_fast contact32 32 4 1026149102293 (by decide +kernel)
private theorem contact32ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact32) 36 4 = 927450733860 :=
  contactColumnsWindow_fast contact32 36 4 927450733860 (by decide +kernel)
private theorem contact32ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact32) 40 4 = 833820805270 :=
  contactColumnsWindow_fast contact32 40 4 833820805270 (by decide +kernel)
private theorem contact32ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact32) 44 4 = 745260920220 :=
  contactColumnsWindow_fast contact32 44 4 745260920220 (by decide +kernel)
private theorem contact32ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact32) 48 4 = 661752026246 :=
  contactColumnsWindow_fast contact32 48 4 661752026246 (by decide +kernel)
private theorem contact32ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact32) 52 4 = 583295269483 :=
  contactColumnsWindow_fast contact32 52 4 583295269483 (by decide +kernel)
private theorem contact32ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact32) 56 4 = 509889117720 :=
  contactColumnsWindow_fast contact32 56 4 509889117720 (by decide +kernel)
private theorem contact32ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact32) 60 4 = 441554893128 :=
  contactColumnsWindow_fast contact32 60 4 441554893128 (by decide +kernel)
private theorem contact32ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact32) 64 4 = 378287312960 :=
  contactColumnsWindow_fast contact32 64 4 378287312960 (by decide +kernel)
private theorem contact32ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact32) 68 4 = 320070846270 :=
  contactColumnsWindow_fast contact32 68 4 320070846270 (by decide +kernel)
private theorem contact32ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact32) 72 4 = 266906325769 :=
  contactColumnsWindow_fast contact32 72 4 266906325769 (by decide +kernel)
private theorem contact32ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact32) 76 4 = 218792977737 :=
  contactColumnsWindow_fast contact32 76 4 218792977737 (by decide +kernel)
private theorem contact32ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact32) 80 4 = 175753953396 :=
  contactColumnsWindow_fast contact32 80 4 175753953396 (by decide +kernel)
private theorem contact32ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact32) 84 4 = 137778594796 :=
  contactColumnsWindow_fast contact32 84 4 137778594796 (by decide +kernel)
private theorem contact32ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact32) 88 4 = 104854555390 :=
  contactColumnsWindow_fast contact32 88 4 104854555390 (by decide +kernel)
private theorem contact32ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact32) 92 4 = 76981970164 :=
  contactColumnsWindow_fast contact32 92 4 76981970164 (by decide +kernel)
private theorem contact32ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact32) 96 4 = 54129599638 :=
  contactColumnsWindow_fast contact32 96 4 54129599638 (by decide +kernel)
private theorem contact32ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact32) 100 4 = 36145300669 :=
  contactColumnsWindow_fast contact32 100 4 36145300669 (by decide +kernel)
private theorem contact32ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact32) 104 4 = 22660675173 :=
  contactColumnsWindow_fast contact32 104 4 22660675173 (by decide +kernel)
private theorem contact32ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact32) 108 4 = 13150658915 :=
  contactColumnsWindow_fast contact32 108 4 13150658915 (by decide +kernel)
private theorem contact32ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact32) 112 3 = 5636422399 :=
  contactColumnsWindow_fast contact32 112 3 5636422399 (by decide +kernel)
private theorem contact32ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact32) 0 8 = 3856331964323 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 4 4 1997735104247 1858596860076 contact32ColumnsSlice0 contact32ColumnsSlice4
private theorem contact32ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact32) 8 8 = 3319975704984 :=
  combineSlices (auxiliaryColumnSlice contact32) 8 4 4 1724507831036 1595467873948 contact32ColumnsSlice8 contact32ColumnsSlice12
private theorem contact32ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact32) 16 8 = 2824028870046 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 4 4 1471477239096 1352551630950 contact32ColumnsSlice16 contact32ColumnsSlice20
private theorem contact32ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact32) 24 8 = 2368597639961 :=
  combineSlices (auxiliaryColumnSlice contact32) 24 4 4 1238699506716 1129898133245 contact32ColumnsSlice24 contact32ColumnsSlice28
private theorem contact32ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact32) 32 8 = 1953599836153 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 4 4 1026149102293 927450733860 contact32ColumnsSlice32 contact32ColumnsSlice36
private theorem contact32ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact32) 40 8 = 1579081725490 :=
  combineSlices (auxiliaryColumnSlice contact32) 40 4 4 833820805270 745260920220 contact32ColumnsSlice40 contact32ColumnsSlice44
private theorem contact32ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact32) 48 8 = 1245047295729 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 4 4 661752026246 583295269483 contact32ColumnsSlice48 contact32ColumnsSlice52
private theorem contact32ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact32) 56 8 = 951444010848 :=
  combineSlices (auxiliaryColumnSlice contact32) 56 4 4 509889117720 441554893128 contact32ColumnsSlice56 contact32ColumnsSlice60
private theorem contact32ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact32) 64 8 = 698358159230 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 4 4 378287312960 320070846270 contact32ColumnsSlice64 contact32ColumnsSlice68
private theorem contact32ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact32) 72 8 = 485699303506 :=
  combineSlices (auxiliaryColumnSlice contact32) 72 4 4 266906325769 218792977737 contact32ColumnsSlice72 contact32ColumnsSlice76
private theorem contact32ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact32) 80 8 = 313532548192 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 4 4 175753953396 137778594796 contact32ColumnsSlice80 contact32ColumnsSlice84
private theorem contact32ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact32) 88 8 = 181836525554 :=
  combineSlices (auxiliaryColumnSlice contact32) 88 4 4 104854555390 76981970164 contact32ColumnsSlice88 contact32ColumnsSlice92
private theorem contact32ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact32) 96 8 = 90274900307 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 4 4 54129599638 36145300669 contact32ColumnsSlice96 contact32ColumnsSlice100
private theorem contact32ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact32) 104 8 = 35811334088 :=
  combineSlices (auxiliaryColumnSlice contact32) 104 4 4 22660675173 13150658915 contact32ColumnsSlice104 contact32ColumnsSlice108
private theorem contact32ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact32) 0 16 = 7176307669307 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 8 8 3856331964323 3319975704984 contact32ColumnsJoin0_8 contact32ColumnsJoin8_8
private theorem contact32ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact32) 16 16 = 5192626510007 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 8 8 2824028870046 2368597639961 contact32ColumnsJoin16_8 contact32ColumnsJoin24_8
private theorem contact32ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact32) 32 16 = 3532681561643 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 8 8 1953599836153 1579081725490 contact32ColumnsJoin32_8 contact32ColumnsJoin40_8
private theorem contact32ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact32) 48 16 = 2196491306577 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 8 8 1245047295729 951444010848 contact32ColumnsJoin48_8 contact32ColumnsJoin56_8
private theorem contact32ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact32) 64 16 = 1184057462736 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 8 8 698358159230 485699303506 contact32ColumnsJoin64_8 contact32ColumnsJoin72_8
private theorem contact32ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact32) 80 16 = 495369073746 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 8 8 313532548192 181836525554 contact32ColumnsJoin80_8 contact32ColumnsJoin88_8
private theorem contact32ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact32) 96 16 = 126086234395 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 8 8 90274900307 35811334088 contact32ColumnsJoin96_8 contact32ColumnsJoin104_8
private theorem contact32ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact32) 0 32 = 12368934179314 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 16 16 7176307669307 5192626510007 contact32ColumnsJoin0_16 contact32ColumnsJoin16_16
private theorem contact32ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact32) 32 32 = 5729172868220 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 16 16 3532681561643 2196491306577 contact32ColumnsJoin32_16 contact32ColumnsJoin48_16
private theorem contact32ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact32) 64 32 = 1679426536482 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 16 16 1184057462736 495369073746 contact32ColumnsJoin64_16 contact32ColumnsJoin80_16
private theorem contact32ColumnsJoin96_19 : sliceWindow (auxiliaryColumnSlice contact32) 96 19 = 131722656794 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 16 3 126086234395 5636422399 contact32ColumnsJoin96_16 contact32ColumnsSlice112
private theorem contact32ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact32) 0 64 = 18098107047534 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 32 32 12368934179314 5729172868220 contact32ColumnsJoin0_32 contact32ColumnsJoin32_32
private theorem contact32ColumnsJoin64_51 : sliceWindow (auxiliaryColumnSlice contact32) 64 51 = 1811149193276 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 32 19 1679426536482 131722656794 contact32ColumnsJoin64_32 contact32ColumnsJoin96_19
private theorem contact32ColumnsJoin0_115 : sliceWindow (auxiliaryColumnSlice contact32) 0 115 = 19909256240810 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 64 51 18098107047534 1811149193276 contact32ColumnsJoin0_64 contact32ColumnsJoin64_51
private theorem contact32OrdinaryRanks : ordinaryRankBound contact32 = 2054975017 := by decide +kernel
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
private theorem contact32RanksSlice104 : sliceWindow (auxiliaryRankSlice contact32) 104 11 = 0 :=
  contactRankWindow_of_rec contact32 104 11 0 (by decide +kernel)
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
private theorem contact32RanksJoin96_19 : sliceWindow (auxiliaryRankSlice contact32) 96 19 = 22146 :=
  combineSlices (auxiliaryRankSlice contact32) 96 8 11 22146 0 contact32RanksJoin96_8 contact32RanksSlice104
private theorem contact32RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact32) 0 32 = 43042512 :=
  combineSlices (auxiliaryRankSlice contact32) 0 16 16 26098920 16943592 contact32RanksJoin0_16 contact32RanksJoin16_16
private theorem contact32RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact32) 32 32 = 15194956 :=
  combineSlices (auxiliaryRankSlice contact32) 32 16 16 10015147 5179809 contact32RanksJoin32_16 contact32RanksJoin48_16
private theorem contact32RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact32) 64 32 = 2661203 :=
  combineSlices (auxiliaryRankSlice contact32) 64 16 16 2131726 529477 contact32RanksJoin64_16 contact32RanksJoin80_16
private theorem contact32RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact32) 0 64 = 58237468 :=
  combineSlices (auxiliaryRankSlice contact32) 0 32 32 43042512 15194956 contact32RanksJoin0_32 contact32RanksJoin32_32
private theorem contact32RanksJoin64_51 : sliceWindow (auxiliaryRankSlice contact32) 64 51 = 2683349 :=
  combineSlices (auxiliaryRankSlice contact32) 64 32 19 2661203 22146 contact32RanksJoin64_32 contact32RanksJoin96_19
private theorem contact32RanksJoin0_115 : sliceWindow (auxiliaryRankSlice contact32) 0 115 = 60920817 :=
  combineSlices (auxiliaryRankSlice contact32) 0 64 51 58237468 2683349 contact32RanksJoin0_64 contact32RanksJoin64_51
theorem contact32_margin : sourceMargin contact32 :=
  margin_of_checked_counts contact32 115 534760250931393 19909256240810 2054975017 60920817 rfl contact32OrdinaryColumns contact32ColumnsJoin0_115 contact32OrdinaryRanks contact32RanksJoin0_115 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts
