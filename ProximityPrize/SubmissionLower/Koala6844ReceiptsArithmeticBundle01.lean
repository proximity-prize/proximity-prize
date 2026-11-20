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



private theorem primaryWindow0 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 512 = 3666322335980796 :=
  firstJetWindow_of_closed primaryShape 0 0 512 (3666322335980796) (by decide +kernel) (by decide +kernel)

private theorem primaryWindow512 : contributionWindow (firstJetAuxContribution primaryShape 0) 512 232 = 408850771330164 :=
  firstJetWindow_of_closed primaryShape 0 512 232 (408850771330164) (by decide +kernel) (by decide +kernel)

private theorem primaryJoin0_744 : contributionWindow (firstJetAuxContribution primaryShape 0) 0 744 = 4075173107310960 :=
  joinWindows (firstJetAuxContribution primaryShape 0) 0 512 232 (3666322335980796) (408850771330164) primaryWindow0 primaryWindow512

theorem primary_firstJetGap_eq : firstJetGap primaryShape 0 = 226541787 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum primaryShape 0 744 (4075173107310960) rfl primaryJoin0_744]
  decide +kernel
private theorem firstRoomWindow0 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 = 82241577169109712 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 0 512 (82241577169109712) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow512 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 512 512 = 170566212664817760 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 512 512 (170566212664817760) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 = 154714361103113352 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1024 512 (154714361103113352) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow1536 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1536 512 = 76307683599020172 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 1536 512 (76307683599020172) (by decide +kernel) (by decide +kernel)

private theorem firstRoomWindow2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 2048 505 = 8531104822330020 :=
  firstJetWindow_of_closed firstRoomShape firstRoomCut 2048 505 (8531104822330020) (by decide +kernel) (by decide +kernel)

private theorem firstRoomJoin0_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 = 252807789833927472 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 512 512 (82241577169109712) (170566212664817760) firstRoomWindow0 firstRoomWindow512

private theorem firstRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 1024 = 231022044702133524 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 1024 512 512 (154714361103113352) (76307683599020172) firstRoomWindow1024 firstRoomWindow1536

private theorem firstRoomJoin0_2048 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 = 483829834536060996 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 1024 1024 (252807789833927472) (231022044702133524) firstRoomJoin0_1024 firstRoomJoin1024_1024

private theorem firstRoomJoin0_2553 : contributionWindow (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2553 = 492360939358391016 :=
  joinWindows (firstJetAuxContribution firstRoomShape firstRoomCut) 0 2048 505 (483829834536060996) (8531104822330020) firstRoomJoin0_2048 firstRoomWindow2048

theorem firstRoom_firstJetGap_eq : firstJetGap firstRoomShape firstRoomCut = 503187856 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstRoomShape firstRoomCut 2553 (492360939358391016) rfl firstRoomJoin0_2553]
  decide +kernel
private theorem secondRoomWindow0 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 = 82457732641866960 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 0 512 (82457732641866960) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow512 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 512 512 = 170729285483562660 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 512 512 (170729285483562660) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 = 154824351219042300 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1024 512 (154824351219042300) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow1536 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1536 512 = 76364591066230380 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 1536 512 (76364591066230380) (by decide +kernel) (by decide +kernel)

private theorem secondRoomWindow2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 2048 449 = 8523125391255828 :=
  firstJetWindow_of_closed secondRoomShape secondRoomCut 2048 449 (8523125391255828) (by decide +kernel) (by decide +kernel)

private theorem secondRoomJoin0_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 = 253187018125429620 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 512 512 (82457732641866960) (170729285483562660) secondRoomWindow0 secondRoomWindow512

private theorem secondRoomJoin1024_1024 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 1024 = 231188942285272680 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 1024 512 512 (154824351219042300) (76364591066230380) secondRoomWindow1024 secondRoomWindow1536

private theorem secondRoomJoin0_2048 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 = 484375960410702300 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 1024 1024 (253187018125429620) (231188942285272680) secondRoomJoin0_1024 secondRoomJoin1024_1024

private theorem secondRoomJoin0_2497 : contributionWindow (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2497 = 492899085801958128 :=
  joinWindows (firstJetAuxContribution secondRoomShape secondRoomCut) 0 2048 449 (484375960410702300) (8523125391255828) secondRoomJoin0_2048 secondRoomWindow2048

theorem secondRoom_firstJetGap_eq : firstJetGap secondRoomShape secondRoomCut = 4578005902 := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondRoomShape secondRoomCut 2497 (492899085801958128) rfl secondRoomJoin0_2497]
  decide +kernel
private theorem firstAdaptiveWindow0 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 512 = 83430680498244348 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 0 512 (83430680498244348) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow512 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 512 512 = 171463361694527328 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 512 512 (171463361694527328) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 = 155319555824945388 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1024 512 (155319555824945388) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1536 512 = 76620924120411840 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 1536 512 (76620924120411840) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 2048 352 = 8391621986581404 :=
  firstJetWindow_of_closed firstAdaptiveShape 0 2048 352 (8391621986581404) (by decide +kernel) (by decide +kernel)

private theorem firstAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 = 254894042192771676 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 512 512 (83430680498244348) (171463361694527328) firstAdaptiveWindow0 firstAdaptiveWindow512

private theorem firstAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 1024 1024 = 231940479945357228 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 1024 512 512 (155319555824945388) (76620924120411840) firstAdaptiveWindow1024 firstAdaptiveWindow1536

private theorem firstAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 = 486834522138128904 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 1024 1024 (254894042192771676) (231940479945357228) firstAdaptiveJoin0_1024 firstAdaptiveJoin1024_1024

private theorem firstAdaptiveJoin0_2400 : contributionWindow (firstJetAuxContribution firstAdaptiveShape 0) 0 2400 = 495226144124710308 :=
  joinWindows (firstJetAuxContribution firstAdaptiveShape 0) 0 2048 352 (486834522138128904) (8391621986581404) firstAdaptiveJoin0_2048 firstAdaptiveWindow2048

theorem firstAdaptive_firstJetGap_eq : firstJetGap firstAdaptiveShape 0 = firstAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum firstAdaptiveShape 0 2400 (495226144124710308) rfl firstAdaptiveJoin0_2400]
  decide +kernel
private theorem secondAdaptiveWindow0 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 512 = 90125131332878925948 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 0 512 (90125131332878925948) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow512 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 512 512 = 210495871610782434228 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 512 512 (210495871610782434228) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 = 327999364581516914808 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1024 512 (327999364581516914808) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow1536 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1536 512 = 442635610245070289208 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 1536 512 (442635610245070289208) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 = 554404608601438502436 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2048 512 (554404608601438502436) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow2560 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2560 512 = 663306359650639115196 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 2560 512 (663306359650639115196) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3072 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 = 769340863392667367964 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3072 512 (769340863392667367964) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow3584 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3584 512 = 872508119827522226448 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 3584 512 (872508119827522226448) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 = 972808128955188132840 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4096 512 (972808128955188132840) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow4608 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4608 512 = 1070240890775684859312 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 4608 512 (1070240890775684859312) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5120 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 = 1164806405289657589344 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5120 512 (1164806405289657589344) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow5632 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5632 512 = 1256504672498869200720 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 5632 512 (1256504672498869200720) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6144 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 = 1345335692401639569420 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6144 512 (1345335692401639569420) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow6656 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6656 512 = 1431299464997234351520 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 6656 512 (1431299464997234351520) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7168 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 = 1514395990285641155676 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7168 512 (1514395990285641155676) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow7680 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7680 512 = 1594625268266879794044 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 7680 512 (1594625268266879794044) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 = 1671987298940943947556 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8192 512 (1671987298940943947556) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow8704 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8704 512 = 1746482082307838632764 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 8704 512 (1746482082307838632764) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9216 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 = 1818109618367544247992 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9216 512 (1818109618367544247992) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow9728 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9728 512 = 1886869907120076937188 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 9728 512 (1886869907120076937188) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10240 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 = 1952762948565436927092 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10240 512 (1952762948565436927092) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow10752 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10752 512 = 2015788742704102030944 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 10752 512 (2015788742704102030944) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11264 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 = 2075947289537948307264 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11264 512 (2075947289537948307264) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow11776 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11776 512 = 2133238589065583570592 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 11776 512 (2133238589065583570592) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12288 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 = 2187662641286029538388 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12288 512 (2187662641286029538388) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow12800 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12800 512 = 2239219446199304651040 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 12800 512 (2239219446199304651040) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13312 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 = 2287909003805405750304 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13312 512 (2287909003805405750304) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow13824 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13824 512 = 2333731314104339303088 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 13824 512 (2333731314104339303088) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14336 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 = 2376686377096086162792 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14336 512 (2376686377096086162792) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow14848 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14848 512 = 2416774192780654886652 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 14848 512 (2416774192780654886652) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15360 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 = 2453994761158053300852 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15360 512 (2453994761158053300852) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow15872 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15872 512 = 2488348082228282874552 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 15872 512 (2488348082228282874552) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 = 2519834155991662886760 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16384 512 (2519834155991662886760) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow16896 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16896 512 = 2548452982450123935108 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 16896 512 (2548452982450123935108) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17408 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 = 2574204561602603203092 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17408 512 (2574204561602603203092) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow17920 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17920 512 = 2597088893447914311216 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 17920 512 (2597088893447914311216) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18432 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 = 2617106172285215428008 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18432 512 (2617106172285215428008) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow18944 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18944 512 = 2634268351687007213460 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 18944 512 (2634268351687007213460) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19456 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 = 2648619695447269465092 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19456 512 (2648619695447269465092) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow19968 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19968 512 = 2660214147683405417028 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 19968 512 (2660214147683405417028) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20480 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 = 2669105751590958079344 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20480 512 (2669105751590958079344) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow20992 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20992 512 = 2675348550365453160888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 20992 512 (2675348550365453160888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow21504 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 = 2678996587202413995840 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 21504 512 (2678996587202413995840) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22016 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22016 512 = 2680103905297584865104 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22016 512 (2680103905297584865104) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow22528 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 = 2678724547848382672236 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 22528 512 (2678724547848382672236) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23040 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23040 512 = 2674912558049665072800 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23040 512 (2674912558049665072800) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow23552 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 = 2668721979095566730700 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 23552 512 (2668721979095566730700) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24064 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24064 512 = 2660206854181582685976 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24064 512 (2660206854181582685976) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow24576 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 = 2649421226503232186400 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 24576 512 (2649421226503232186400) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25088 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25088 512 = 2636419139256036458352 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25088 512 (2636419139256036458352) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow25600 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 = 2621254635635542921152 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 25600 512 (2621254635635542921152) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26112 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26112 512 = 2603981758837273696896 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26112 512 (2603981758837273696896) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow26624 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 = 2584654552056759343200 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 26624 512 (2584654552056759343200) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27136 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27136 512 = 2563327058489510579220 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27136 512 (2563327058489510579220) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow27648 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 = 2540053321331219040444 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 27648 512 (2540053321331219040444) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28160 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28160 512 = 2514887383779163280640 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28160 512 (2514887383779163280640) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow28672 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 = 2487883289028648168420 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 28672 512 (2487883289028648168420) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29184 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29184 512 = 2459095080273606550644 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29184 512 (2459095080273606550644) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow29696 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 = 2428576800709488334044 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 29696 512 (2428576800709488334044) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30208 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30208 512 = 2396382493531806796680 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30208 512 (2396382493531806796680) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow30720 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 = 2362566201936110241852 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 30720 512 (2362566201936110241852) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31232 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31232 512 = 2327181969117921553908 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31232 512 (2327181969117921553908) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow31744 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 = 2290283838272775275868 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 31744 512 (2290283838272775275868) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32256 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32256 512 = 2251925852596179885012 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32256 512 (2251925852596179885012) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 = 2212162055283677546496 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 32768 512 (2212162055283677546496) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33280 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33280 512 = 2171046489530879988216 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33280 512 (2171046489530879988216) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow33792 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 = 2128633198534920651024 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 33792 512 (2128633198534920651024) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34304 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34304 512 = 2084976225491525868816 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34304 512 (2084976225491525868816) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow34816 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 = 2040129613594483030224 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 34816 512 (2040129613594483030224) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35328 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35328 512 = 1994147406039161057772 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35328 512 (1994147406039161057772) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow35840 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 = 1947083646021104916084 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 35840 512 (1947083646021104916084) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36352 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36352 512 = 1898992376735842735800 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36352 512 (1898992376735842735800) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow36864 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 = 1849927641378908524584 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 36864 512 (1849927641378908524584) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37376 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37376 512 = 1799943483145812381768 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37376 512 (1799943483145812381768) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow37888 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 = 1749093945232088177376 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 37888 512 (1749093945232088177376) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38400 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38400 512 = 1697433070833275284044 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38400 512 (1697433070833275284044) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow38912 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 = 1645014903144936633000 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 38912 512 (1645014903144936633000) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39424 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39424 512 = 1591893485364007659096 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39424 512 (1591893485364007659096) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow39936 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 = 1538122860686661939708 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 39936 512 (1538122860686661939708) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40448 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40448 512 = 1483757072306545642716 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40448 512 (1483757072306545642716) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow40960 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 = 1428850163418974527764 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 40960 512 (1428850163418974527764) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41472 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41472 512 = 1373456177219484279936 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41472 512 (1373456177219484279936) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow41984 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 = 1317629156903605105284 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 41984 512 (1317629156903605105284) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow42496 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 42496 512 = 1261423145666852286900 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 42496 512 (1261423145666852286900) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43008 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 = 1204892186704751615124 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43008 512 (1204892186704751615124) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow43520 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43520 512 = 1148090323212848229900 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 43520 512 (1148090323212848229900) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44032 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 = 1091071598386666512828 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44032 512 (1091071598386666512828) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow44544 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44544 512 = 1033890055421740744440 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 44544 512 (1033890055421740744440) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45056 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 = 976599737514797180040 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45056 512 (976599737514797180040) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow45568 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45568 512 = 919254687862406210760 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 45568 512 (919254687862406210760) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46080 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 = 861908949658164840432 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46080 512 (861908949658164840432) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow46592 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46592 512 = 804616566097290826512 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 46592 512 (804616566097290826512) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47104 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 = 747431580375310143024 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47104 512 (747431580375310143024) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow47616 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47616 512 = 690408035687745527448 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 47616 512 (690408035687745527448) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48128 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 = 633599975230114652916 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48128 512 (633599975230114652916) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow48640 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48640 512 = 577075249276308119760 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 48640 512 (577075249276308119760) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49152 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 = 521987665621855503888 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49152 512 (521987665621855503888) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow49664 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49664 512 = 470249463905826880500 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 49664 512 (470249463905826880500) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50176 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 = 422024462638858286892 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50176 512 (422024462638858286892) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow50688 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50688 512 = 377214610419026363892 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 50688 512 (377214610419026363892) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51200 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 = 335694874874450775696 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51200 512 (335694874874450775696) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow51712 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51712 512 = 297339790018123870812 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 51712 512 (297339790018123870812) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52224 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 = 262023889864798815324 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52224 512 (262023889864798815324) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow52736 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52736 512 = 229621708429601740332 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 52736 512 (229621708429601740332) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53248 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 = 200007779727655303104 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53248 512 (200007779727655303104) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow53760 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53760 512 = 173056637774103426216 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 53760 512 (173056637774103426216) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54272 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 = 148642816584066343512 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54272 512 (148642816584066343512) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow54784 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54784 512 = 126640850172669070488 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 54784 512 (126640850172669070488) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55296 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 = 106925272555031059800 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55296 512 (106925272555031059800) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow55808 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55808 512 = 89370617746294227132 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 55808 512 (89370617746294227132) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56320 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 = 73851419762290314780 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56320 512 (73851419762290314780) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow56832 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56832 512 = 60242212618522115856 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 56832 512 (60242212618522115856) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57344 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 = 48417530328671624904 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57344 512 (48417530328671624904) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow57856 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57856 512 = 38251906907808103092 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 57856 512 (38251906907808103092) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58368 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 = 29619876371055596040 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58368 512 (29619876371055596040) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveWindow58880 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58880 410 = 18447277246141702536 :=
  firstJetWindow_of_closed secondAdaptiveShape 0 58880 410 (18447277246141702536) (by decide +kernel) (by decide +kernel)

private theorem secondAdaptiveJoin0_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 = 300621002943661360176 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 512 512 (90125131332878925948) (210495871610782434228) secondAdaptiveWindow0 secondAdaptiveWindow512

private theorem secondAdaptiveJoin1024_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 1024 1024 = 770634974826587204016 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 1024 512 512 (327999364581516914808) (442635610245070289208) secondAdaptiveWindow1024 secondAdaptiveWindow1536

private theorem secondAdaptiveJoin2048_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 = 1217710968252077617632 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 512 512 (554404608601438502436) (663306359650639115196) secondAdaptiveWindow2048 secondAdaptiveWindow2560

private theorem secondAdaptiveJoin3072_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 3072 1024 = 1641848983220189594412 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 3072 512 512 (769340863392667367964) (872508119827522226448) secondAdaptiveWindow3072 secondAdaptiveWindow3584

private theorem secondAdaptiveJoin4096_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 = 2043049019730872992152 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 512 512 (972808128955188132840) (1070240890775684859312) secondAdaptiveWindow4096 secondAdaptiveWindow4608

private theorem secondAdaptiveJoin5120_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 5120 1024 = 2421311077788526790064 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 5120 512 512 (1164806405289657589344) (1256504672498869200720) secondAdaptiveWindow5120 secondAdaptiveWindow5632

private theorem secondAdaptiveJoin6144_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 = 2776635157398873920940 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 512 512 (1345335692401639569420) (1431299464997234351520) secondAdaptiveWindow6144 secondAdaptiveWindow6656

private theorem secondAdaptiveJoin7168_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 7168 1024 = 3109021258552520949720 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 7168 512 512 (1514395990285641155676) (1594625268266879794044) secondAdaptiveWindow7168 secondAdaptiveWindow7680

private theorem secondAdaptiveJoin8192_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 = 3418469381248782580320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 512 512 (1671987298940943947556) (1746482082307838632764) secondAdaptiveWindow8192 secondAdaptiveWindow8704

private theorem secondAdaptiveJoin9216_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 9216 1024 = 3704979525487621185180 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 9216 512 512 (1818109618367544247992) (1886869907120076937188) secondAdaptiveWindow9216 secondAdaptiveWindow9728

private theorem secondAdaptiveJoin10240_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 = 3968551691269538958036 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 512 512 (1952762948565436927092) (2015788742704102030944) secondAdaptiveWindow10240 secondAdaptiveWindow10752

private theorem secondAdaptiveJoin11264_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 11264 1024 = 4209185878603531877856 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 11264 512 512 (2075947289537948307264) (2133238589065583570592) secondAdaptiveWindow11264 secondAdaptiveWindow11776

private theorem secondAdaptiveJoin12288_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 = 4426882087485334189428 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 512 512 (2187662641286029538388) (2239219446199304651040) secondAdaptiveWindow12288 secondAdaptiveWindow12800

private theorem secondAdaptiveJoin13312_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 13312 1024 = 4621640317909745053392 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 13312 512 512 (2287909003805405750304) (2333731314104339303088) secondAdaptiveWindow13312 secondAdaptiveWindow13824

private theorem secondAdaptiveJoin14336_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 = 4793460569876741049444 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 512 512 (2376686377096086162792) (2416774192780654886652) secondAdaptiveWindow14336 secondAdaptiveWindow14848

private theorem secondAdaptiveJoin15360_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 15360 1024 = 4942342843386336175404 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 15360 512 512 (2453994761158053300852) (2488348082228282874552) secondAdaptiveWindow15360 secondAdaptiveWindow15872

private theorem secondAdaptiveJoin16384_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 = 5068287138441786821868 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 512 512 (2519834155991662886760) (2548452982450123935108) secondAdaptiveWindow16384 secondAdaptiveWindow16896

private theorem secondAdaptiveJoin17408_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 17408 1024 = 5171293455050517514308 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 17408 512 512 (2574204561602603203092) (2597088893447914311216) secondAdaptiveWindow17408 secondAdaptiveWindow17920

private theorem secondAdaptiveJoin18432_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 = 5251374523972222641468 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 512 512 (2617106172285215428008) (2634268351687007213460) secondAdaptiveWindow18432 secondAdaptiveWindow18944

private theorem secondAdaptiveJoin19456_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 19456 1024 = 5308833843130674882120 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 19456 512 512 (2648619695447269465092) (2660214147683405417028) secondAdaptiveWindow19456 secondAdaptiveWindow19968

private theorem secondAdaptiveJoin20480_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 = 5344454301956411240232 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 512 512 (2669105751590958079344) (2675348550365453160888) secondAdaptiveWindow20480 secondAdaptiveWindow20992

private theorem secondAdaptiveJoin21504_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 21504 1024 = 5359100492499998860944 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 21504 512 512 (2678996587202413995840) (2680103905297584865104) secondAdaptiveWindow21504 secondAdaptiveWindow22016

private theorem secondAdaptiveJoin22528_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 = 5353637105898047745036 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 512 512 (2678724547848382672236) (2674912558049665072800) secondAdaptiveWindow22528 secondAdaptiveWindow23040

private theorem secondAdaptiveJoin23552_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 23552 1024 = 5328928833277149416676 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 23552 512 512 (2668721979095566730700) (2660206854181582685976) secondAdaptiveWindow23552 secondAdaptiveWindow24064

private theorem secondAdaptiveJoin24576_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 = 5285840365759268644752 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 512 512 (2649421226503232186400) (2636419139256036458352) secondAdaptiveWindow24576 secondAdaptiveWindow25088

private theorem secondAdaptiveJoin25600_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 25600 1024 = 5225236394472816618048 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 25600 512 512 (2621254635635542921152) (2603981758837273696896) secondAdaptiveWindow25600 secondAdaptiveWindow26112

private theorem secondAdaptiveJoin26624_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 = 5147981610546269922420 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 512 512 (2584654552056759343200) (2563327058489510579220) secondAdaptiveWindow26624 secondAdaptiveWindow27136

private theorem secondAdaptiveJoin27648_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 27648 1024 = 5054940705110382321084 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 27648 512 512 (2540053321331219040444) (2514887383779163280640) secondAdaptiveWindow27648 secondAdaptiveWindow28160

private theorem secondAdaptiveJoin28672_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 = 4946978369302254719064 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 512 512 (2487883289028648168420) (2459095080273606550644) secondAdaptiveWindow28672 secondAdaptiveWindow29184

private theorem secondAdaptiveJoin29696_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 29696 1024 = 4824959294241295130724 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 29696 512 512 (2428576800709488334044) (2396382493531806796680) secondAdaptiveWindow29696 secondAdaptiveWindow30208

private theorem secondAdaptiveJoin30720_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 = 4689748171054031795760 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 512 512 (2362566201936110241852) (2327181969117921553908) secondAdaptiveWindow30720 secondAdaptiveWindow31232

private theorem secondAdaptiveJoin31744_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 31744 1024 = 4542209690868955160880 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 31744 512 512 (2290283838272775275868) (2251925852596179885012) secondAdaptiveWindow31744 secondAdaptiveWindow32256

private theorem secondAdaptiveJoin32768_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 = 4383208544814557534712 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 512 512 (2212162055283677546496) (2171046489530879988216) secondAdaptiveWindow32768 secondAdaptiveWindow33280

private theorem secondAdaptiveJoin33792_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 33792 1024 = 4213609424026446519840 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 33792 512 512 (2128633198534920651024) (2084976225491525868816) secondAdaptiveWindow33792 secondAdaptiveWindow34304

private theorem secondAdaptiveJoin34816_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 = 4034277019633644087996 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 512 512 (2040129613594483030224) (1994147406039161057772) secondAdaptiveWindow34816 secondAdaptiveWindow35328

private theorem secondAdaptiveJoin35840_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 35840 1024 = 3846076022756947651884 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 35840 512 512 (1947083646021104916084) (1898992376735842735800) secondAdaptiveWindow35840 secondAdaptiveWindow36352

private theorem secondAdaptiveJoin36864_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 = 3649871124524720906352 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 512 512 (1849927641378908524584) (1799943483145812381768) secondAdaptiveWindow36864 secondAdaptiveWindow37376

private theorem secondAdaptiveJoin37888_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 37888 1024 = 3446527016065363461420 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 37888 512 512 (1749093945232088177376) (1697433070833275284044) secondAdaptiveWindow37888 secondAdaptiveWindow38400

private theorem secondAdaptiveJoin38912_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 = 3236908388508944292096 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 512 512 (1645014903144936633000) (1591893485364007659096) secondAdaptiveWindow38912 secondAdaptiveWindow39424

private theorem secondAdaptiveJoin39936_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 39936 1024 = 3021879932993207582424 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 39936 512 512 (1538122860686661939708) (1483757072306545642716) secondAdaptiveWindow39936 secondAdaptiveWindow40448

private theorem secondAdaptiveJoin40960_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 = 2802306340638458807700 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 512 512 (1428850163418974527764) (1373456177219484279936) secondAdaptiveWindow40960 secondAdaptiveWindow41472

private theorem secondAdaptiveJoin41984_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 41984 1024 = 2579052302570457392184 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 41984 512 512 (1317629156903605105284) (1261423145666852286900) secondAdaptiveWindow41984 secondAdaptiveWindow42496

private theorem secondAdaptiveJoin43008_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 = 2352982509917599845024 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 512 512 (1204892186704751615124) (1148090323212848229900) secondAdaptiveWindow43008 secondAdaptiveWindow43520

private theorem secondAdaptiveJoin44032_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 44032 1024 = 2124961653808407257268 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 44032 512 512 (1091071598386666512828) (1033890055421740744440) secondAdaptiveWindow44032 secondAdaptiveWindow44544

private theorem secondAdaptiveJoin45056_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 = 1895854425377203390800 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 512 512 (976599737514797180040) (919254687862406210760) secondAdaptiveWindow45056 secondAdaptiveWindow45568

private theorem secondAdaptiveJoin46080_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 46080 1024 = 1666525515755455666944 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 46080 512 512 (861908949658164840432) (804616566097290826512) secondAdaptiveWindow46080 secondAdaptiveWindow46592

private theorem secondAdaptiveJoin47104_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 = 1437839616063055670472 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 512 512 (747431580375310143024) (690408035687745527448) secondAdaptiveWindow47104 secondAdaptiveWindow47616

private theorem secondAdaptiveJoin48128_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 48128 1024 = 1210675224506422772676 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 48128 512 512 (633599975230114652916) (577075249276308119760) secondAdaptiveWindow48128 secondAdaptiveWindow48640

private theorem secondAdaptiveJoin49152_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 = 992237129527682384388 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 512 512 (521987665621855503888) (470249463905826880500) secondAdaptiveWindow49152 secondAdaptiveWindow49664

private theorem secondAdaptiveJoin50176_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 50176 1024 = 799239073057884650784 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 50176 512 512 (422024462638858286892) (377214610419026363892) secondAdaptiveWindow50176 secondAdaptiveWindow50688

private theorem secondAdaptiveJoin51200_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 = 633034664892574646508 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 512 512 (335694874874450775696) (297339790018123870812) secondAdaptiveWindow51200 secondAdaptiveWindow51712

private theorem secondAdaptiveJoin52224_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 52224 1024 = 491645598294400555656 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 52224 512 512 (262023889864798815324) (229621708429601740332) secondAdaptiveWindow52224 secondAdaptiveWindow52736

private theorem secondAdaptiveJoin53248_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 = 373064417501758729320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 512 512 (200007779727655303104) (173056637774103426216) secondAdaptiveWindow53248 secondAdaptiveWindow53760

private theorem secondAdaptiveJoin54272_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 54272 1024 = 275283666756735414000 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 54272 512 512 (148642816584066343512) (126640850172669070488) secondAdaptiveWindow54272 secondAdaptiveWindow54784

private theorem secondAdaptiveJoin55296_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 = 196295890301325286932 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 512 512 (106925272555031059800) (89370617746294227132) secondAdaptiveWindow55296 secondAdaptiveWindow55808

private theorem secondAdaptiveJoin56320_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 56320 1024 = 134093632380812430636 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 56320 512 512 (73851419762290314780) (60242212618522115856) secondAdaptiveWindow56320 secondAdaptiveWindow56832

private theorem secondAdaptiveJoin57344_1024 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 = 86669437236479727996 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 512 512 (48417530328671624904) (38251906907808103092) secondAdaptiveWindow57344 secondAdaptiveWindow57856

private theorem secondAdaptiveJoin58368_922 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 58368 922 = 48067153617197298576 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 58368 512 410 (29619876371055596040) (18447277246141702536) secondAdaptiveWindow58368 secondAdaptiveWindow58880

private theorem secondAdaptiveJoin0_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 = 1071255977770248564192 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 1024 1024 (300621002943661360176) (770634974826587204016) secondAdaptiveJoin0_1024 secondAdaptiveJoin1024_1024

private theorem secondAdaptiveJoin2048_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 2048 2048 = 2859559951472267212044 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 2048 1024 1024 (1217710968252077617632) (1641848983220189594412) secondAdaptiveJoin2048_1024 secondAdaptiveJoin3072_1024

private theorem secondAdaptiveJoin4096_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 = 4464360097519399782216 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 1024 1024 (2043049019730872992152) (2421311077788526790064) secondAdaptiveJoin4096_1024 secondAdaptiveJoin5120_1024

private theorem secondAdaptiveJoin6144_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 6144 2048 = 5885656415951394870660 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 6144 1024 1024 (2776635157398873920940) (3109021258552520949720) secondAdaptiveJoin6144_1024 secondAdaptiveJoin7168_1024

private theorem secondAdaptiveJoin8192_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 = 7123448906736403765500 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 1024 1024 (3418469381248782580320) (3704979525487621185180) secondAdaptiveJoin8192_1024 secondAdaptiveJoin9216_1024

private theorem secondAdaptiveJoin10240_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 10240 2048 = 8177737569873070835892 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 10240 1024 1024 (3968551691269538958036) (4209185878603531877856) secondAdaptiveJoin10240_1024 secondAdaptiveJoin11264_1024

private theorem secondAdaptiveJoin12288_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 = 9048522405395079242820 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 1024 1024 (4426882087485334189428) (4621640317909745053392) secondAdaptiveJoin12288_1024 secondAdaptiveJoin13312_1024

private theorem secondAdaptiveJoin14336_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 14336 2048 = 9735803413263077224848 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 14336 1024 1024 (4793460569876741049444) (4942342843386336175404) secondAdaptiveJoin14336_1024 secondAdaptiveJoin15360_1024

private theorem secondAdaptiveJoin16384_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 = 10239580593492304336176 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 1024 1024 (5068287138441786821868) (5171293455050517514308) secondAdaptiveJoin16384_1024 secondAdaptiveJoin17408_1024

private theorem secondAdaptiveJoin18432_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 18432 2048 = 10560208367102897523588 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 18432 1024 1024 (5251374523972222641468) (5308833843130674882120) secondAdaptiveJoin18432_1024 secondAdaptiveJoin19456_1024

private theorem secondAdaptiveJoin20480_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 = 10703554794456410101176 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 1024 1024 (5344454301956411240232) (5359100492499998860944) secondAdaptiveJoin20480_1024 secondAdaptiveJoin21504_1024

private theorem secondAdaptiveJoin22528_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 22528 2048 = 10682565939175197161712 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 22528 1024 1024 (5353637105898047745036) (5328928833277149416676) secondAdaptiveJoin22528_1024 secondAdaptiveJoin23552_1024

private theorem secondAdaptiveJoin24576_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 = 10511076760232085262800 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 1024 1024 (5285840365759268644752) (5225236394472816618048) secondAdaptiveJoin24576_1024 secondAdaptiveJoin25600_1024

private theorem secondAdaptiveJoin26624_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 26624 2048 = 10202922315656652243504 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 26624 1024 1024 (5147981610546269922420) (5054940705110382321084) secondAdaptiveJoin26624_1024 secondAdaptiveJoin27648_1024

private theorem secondAdaptiveJoin28672_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 = 9771937663543549849788 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 1024 1024 (4946978369302254719064) (4824959294241295130724) secondAdaptiveJoin28672_1024 secondAdaptiveJoin29696_1024

private theorem secondAdaptiveJoin30720_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 30720 2048 = 9231957861922986956640 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 30720 1024 1024 (4689748171054031795760) (4542209690868955160880) secondAdaptiveJoin30720_1024 secondAdaptiveJoin31744_1024

private theorem secondAdaptiveJoin32768_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 = 8596817968841004054552 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 1024 1024 (4383208544814557534712) (4213609424026446519840) secondAdaptiveJoin32768_1024 secondAdaptiveJoin33792_1024

private theorem secondAdaptiveJoin34816_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 34816 2048 = 7880353042390591739880 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 34816 1024 1024 (4034277019633644087996) (3846076022756947651884) secondAdaptiveJoin34816_1024 secondAdaptiveJoin35840_1024

private theorem secondAdaptiveJoin36864_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 = 7096398140590084367772 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 1024 1024 (3649871124524720906352) (3446527016065363461420) secondAdaptiveJoin36864_1024 secondAdaptiveJoin37888_1024

private theorem secondAdaptiveJoin38912_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 38912 2048 = 6258788321502151874520 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 38912 1024 1024 (3236908388508944292096) (3021879932993207582424) secondAdaptiveJoin38912_1024 secondAdaptiveJoin39936_1024

private theorem secondAdaptiveJoin40960_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 = 5381358643208916199884 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 1024 1024 (2802306340638458807700) (2579052302570457392184) secondAdaptiveJoin40960_1024 secondAdaptiveJoin41984_1024

private theorem secondAdaptiveJoin43008_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 43008 2048 = 4477944163726007102292 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 43008 1024 1024 (2352982509917599845024) (2124961653808407257268) secondAdaptiveJoin43008_1024 secondAdaptiveJoin44032_1024

private theorem secondAdaptiveJoin45056_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 = 3562379941132659057744 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 1024 1024 (1895854425377203390800) (1666525515755455666944) secondAdaptiveJoin45056_1024 secondAdaptiveJoin46080_1024

private theorem secondAdaptiveJoin47104_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 47104 2048 = 2648514840569478443148 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 47104 1024 1024 (1437839616063055670472) (1210675224506422772676) secondAdaptiveJoin47104_1024 secondAdaptiveJoin48128_1024

private theorem secondAdaptiveJoin49152_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 = 1791476202585567035172 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 1024 1024 (992237129527682384388) (799239073057884650784) secondAdaptiveJoin49152_1024 secondAdaptiveJoin50176_1024

private theorem secondAdaptiveJoin51200_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 51200 2048 = 1124680263186975202164 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 51200 1024 1024 (633034664892574646508) (491645598294400555656) secondAdaptiveJoin51200_1024 secondAdaptiveJoin52224_1024

private theorem secondAdaptiveJoin53248_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 = 648348084258494143320 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 1024 1024 (373064417501758729320) (275283666756735414000) secondAdaptiveJoin53248_1024 secondAdaptiveJoin54272_1024

private theorem secondAdaptiveJoin55296_2048 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 55296 2048 = 330389522682137717568 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 55296 1024 1024 (196295890301325286932) (134093632380812430636) secondAdaptiveJoin55296_1024 secondAdaptiveJoin56320_1024

private theorem secondAdaptiveJoin57344_1946 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 57344 1946 = 134736590853677026572 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 57344 1024 922 (86669437236479727996) (48067153617197298576) secondAdaptiveJoin57344_1024 secondAdaptiveJoin58368_922

private theorem secondAdaptiveJoin0_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 = 3930815929242515776236 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 2048 2048 (1071255977770248564192) (2859559951472267212044) secondAdaptiveJoin0_2048 secondAdaptiveJoin2048_2048

private theorem secondAdaptiveJoin4096_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 4096 4096 = 10350016513470794652876 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 4096 2048 2048 (4464360097519399782216) (5885656415951394870660) secondAdaptiveJoin4096_2048 secondAdaptiveJoin6144_2048

private theorem secondAdaptiveJoin8192_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 = 15301186476609474601392 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 2048 2048 (7123448906736403765500) (8177737569873070835892) secondAdaptiveJoin8192_2048 secondAdaptiveJoin10240_2048

private theorem secondAdaptiveJoin12288_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 12288 4096 = 18784325818658156467668 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 12288 2048 2048 (9048522405395079242820) (9735803413263077224848) secondAdaptiveJoin12288_2048 secondAdaptiveJoin14336_2048

private theorem secondAdaptiveJoin16384_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 = 20799788960595201859764 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 2048 2048 (10239580593492304336176) (10560208367102897523588) secondAdaptiveJoin16384_2048 secondAdaptiveJoin18432_2048

private theorem secondAdaptiveJoin20480_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 20480 4096 = 21386120733631607262888 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 20480 2048 2048 (10703554794456410101176) (10682565939175197161712) secondAdaptiveJoin20480_2048 secondAdaptiveJoin22528_2048

private theorem secondAdaptiveJoin24576_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 = 20713999075888737506304 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 2048 2048 (10511076760232085262800) (10202922315656652243504) secondAdaptiveJoin24576_2048 secondAdaptiveJoin26624_2048

private theorem secondAdaptiveJoin28672_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 28672 4096 = 19003895525466536806428 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 28672 2048 2048 (9771937663543549849788) (9231957861922986956640) secondAdaptiveJoin28672_2048 secondAdaptiveJoin30720_2048

private theorem secondAdaptiveJoin32768_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 = 16477171011231595794432 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 2048 2048 (8596817968841004054552) (7880353042390591739880) secondAdaptiveJoin32768_2048 secondAdaptiveJoin34816_2048

private theorem secondAdaptiveJoin36864_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 36864 4096 = 13355186462092236242292 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 36864 2048 2048 (7096398140590084367772) (6258788321502151874520) secondAdaptiveJoin36864_2048 secondAdaptiveJoin38912_2048

private theorem secondAdaptiveJoin40960_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 = 9859302806934923302176 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 2048 2048 (5381358643208916199884) (4477944163726007102292) secondAdaptiveJoin40960_2048 secondAdaptiveJoin43008_2048

private theorem secondAdaptiveJoin45056_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 45056 4096 = 6210894781702137500892 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 45056 2048 2048 (3562379941132659057744) (2648514840569478443148) secondAdaptiveJoin45056_2048 secondAdaptiveJoin47104_2048

private theorem secondAdaptiveJoin49152_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 = 2916156465772542237336 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 2048 2048 (1791476202585567035172) (1124680263186975202164) secondAdaptiveJoin49152_2048 secondAdaptiveJoin51200_2048

private theorem secondAdaptiveJoin53248_4096 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 53248 4096 = 978737606940631860888 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 53248 2048 2048 (648348084258494143320) (330389522682137717568) secondAdaptiveJoin53248_2048 secondAdaptiveJoin55296_2048

private theorem secondAdaptiveJoin0_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 = 14280832442713310429112 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 4096 4096 (3930815929242515776236) (10350016513470794652876) secondAdaptiveJoin0_4096 secondAdaptiveJoin4096_4096

private theorem secondAdaptiveJoin8192_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 8192 8192 = 34085512295267631069060 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 8192 4096 4096 (15301186476609474601392) (18784325818658156467668) secondAdaptiveJoin8192_4096 secondAdaptiveJoin12288_4096

private theorem secondAdaptiveJoin16384_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 = 42185909694226809122652 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 4096 4096 (20799788960595201859764) (21386120733631607262888) secondAdaptiveJoin16384_4096 secondAdaptiveJoin20480_4096

private theorem secondAdaptiveJoin24576_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 24576 8192 = 39717894601355274312732 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 24576 4096 4096 (20713999075888737506304) (19003895525466536806428) secondAdaptiveJoin24576_4096 secondAdaptiveJoin28672_4096

private theorem secondAdaptiveJoin32768_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 = 29832357473323832036724 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 4096 4096 (16477171011231595794432) (13355186462092236242292) secondAdaptiveJoin32768_4096 secondAdaptiveJoin36864_4096

private theorem secondAdaptiveJoin40960_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 40960 8192 = 16070197588637060803068 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 40960 4096 4096 (9859302806934923302176) (6210894781702137500892) secondAdaptiveJoin40960_4096 secondAdaptiveJoin45056_4096

private theorem secondAdaptiveJoin49152_8192 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 = 3894894072713174098224 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 4096 4096 (2916156465772542237336) (978737606940631860888) secondAdaptiveJoin49152_4096 secondAdaptiveJoin53248_4096

private theorem secondAdaptiveJoin0_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 = 48366344737980941498172 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 8192 8192 (14280832442713310429112) (34085512295267631069060) secondAdaptiveJoin0_8192 secondAdaptiveJoin8192_8192

private theorem secondAdaptiveJoin16384_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 16384 16384 = 81903804295582083435384 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 16384 8192 8192 (42185909694226809122652) (39717894601355274312732) secondAdaptiveJoin16384_8192 secondAdaptiveJoin24576_8192

private theorem secondAdaptiveJoin32768_16384 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 = 45902555061960892839792 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 8192 8192 (29832357473323832036724) (16070197588637060803068) secondAdaptiveJoin32768_8192 secondAdaptiveJoin40960_8192

private theorem secondAdaptiveJoin49152_10138 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 49152 10138 = 4029630663566851124796 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 49152 8192 1946 (3894894072713174098224) (134736590853677026572) secondAdaptiveJoin49152_8192 secondAdaptiveJoin57344_1946

private theorem secondAdaptiveJoin0_32768 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 = 130270149033563024933556 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 16384 16384 (48366344737980941498172) (81903804295582083435384) secondAdaptiveJoin0_16384 secondAdaptiveJoin16384_16384

private theorem secondAdaptiveJoin32768_26522 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 32768 26522 = 49932185725527743964588 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 32768 16384 10138 (45902555061960892839792) (4029630663566851124796) secondAdaptiveJoin32768_16384 secondAdaptiveJoin49152_10138

private theorem secondAdaptiveJoin0_59290 : contributionWindow (firstJetAuxContribution secondAdaptiveShape 0) 0 59290 = 180202334759090768898144 :=
  joinWindows (firstJetAuxContribution secondAdaptiveShape 0) 0 32768 26522 (130270149033563024933556) (49932185725527743964588) secondAdaptiveJoin0_32768 secondAdaptiveJoin32768_26522

theorem secondAdaptive_firstJetGap_eq : firstJetGap secondAdaptiveShape 0 = secondAdaptiveGap := by
  unfold firstJetGap firstJetGapTwelve
  rw [contributionSum secondAdaptiveShape 0 59290 (180202334759090768898144) rfl secondAdaptiveJoin0_59290]
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

private theorem contact00OrdinaryColumns : ordinaryColumnCount contact00 = 2496927484456951 := by decide +kernel
private theorem contact00ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact00) 0 4 = 6881798697340 :=
  contactColumnsWindow_fast contact00 0 4 6881798697340 (by decide +kernel)
private theorem contact00ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact00) 4 4 = 6543855823708 :=
  contactColumnsWindow_fast contact00 4 4 6543855823708 (by decide +kernel)
private theorem contact00ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact00) 8 4 = 6214454613844 :=
  contactColumnsWindow_fast contact00 8 4 6214454613844 (by decide +kernel)
private theorem contact00ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact00) 12 4 = 5893597883836 :=
  contactColumnsWindow_fast contact00 12 4 5893597883836 (by decide +kernel)
private theorem contact00ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact00) 16 4 = 5581283714547 :=
  contactColumnsWindow_fast contact00 16 4 5581283714547 (by decide +kernel)
private theorem contact00ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact00) 20 4 = 5277514038348 :=
  contactColumnsWindow_fast contact00 20 4 5277514038348 (by decide +kernel)
private theorem contact00ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact00) 24 4 = 4982303410308 :=
  contactColumnsWindow_fast contact00 24 4 4982303410308 (by decide +kernel)
private theorem contact00ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact00) 28 4 = 4695669911238 :=
  contactColumnsWindow_fast contact00 28 4 4695669911238 (by decide +kernel)
private theorem contact00ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact00) 32 4 = 4417584026364 :=
  contactColumnsWindow_fast contact00 32 4 4417584026364 (by decide +kernel)
private theorem contact00ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact00) 36 4 = 4148043790453 :=
  contactColumnsWindow_fast contact00 36 4 4148043790453 (by decide +kernel)
private theorem contact00ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact00) 40 4 = 3887051055364 :=
  contactColumnsWindow_fast contact00 40 4 3887051055364 (by decide +kernel)
private theorem contact00ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact00) 44 4 = 3634623981295 :=
  contactColumnsWindow_fast contact00 44 4 3634623981295 (by decide +kernel)
private theorem contact00ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact00) 48 4 = 3390774734338 :=
  contactColumnsWindow_fast contact00 48 4 3390774734338 (by decide +kernel)
private theorem contact00ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact00) 52 4 = 3155474710168 :=
  contactColumnsWindow_fast contact00 52 4 3155474710168 (by decide +kernel)
private theorem contact00ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact00) 56 4 = 2928724548661 :=
  contactColumnsWindow_fast contact00 56 4 2928724548661 (by decide +kernel)
private theorem contact00ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact00) 60 4 = 2710523993264 :=
  contactColumnsWindow_fast contact00 60 4 2710523993264 (by decide +kernel)
private theorem contact00ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact00) 64 4 = 2500898375653 :=
  contactColumnsWindow_fast contact00 64 4 2500898375653 (by decide +kernel)
private theorem contact00ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact00) 68 4 = 2299848145963 :=
  contactColumnsWindow_fast contact00 68 4 2299848145963 (by decide +kernel)
private theorem contact00ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact00) 72 4 = 2107352028612 :=
  contactColumnsWindow_fast contact00 72 4 2107352028612 (by decide +kernel)
private theorem contact00ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact00) 76 4 = 1923406286654 :=
  contactColumnsWindow_fast contact00 76 4 1923406286654 (by decide +kernel)
private theorem contact00ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact00) 80 4 = 1748009925636 :=
  contactColumnsWindow_fast contact00 80 4 1748009925636 (by decide +kernel)
private theorem contact00ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact00) 84 4 = 1581193342552 :=
  contactColumnsWindow_fast contact00 84 4 1581193342552 (by decide +kernel)
private theorem contact00ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact00) 88 4 = 1422947939373 :=
  contactColumnsWindow_fast contact00 88 4 1422947939373 (by decide +kernel)
private theorem contact00ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact00) 92 4 = 1273256205836 :=
  contactColumnsWindow_fast contact00 92 4 1273256205836 (by decide +kernel)
private theorem contact00ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact00) 96 4 = 1132114846066 :=
  contactColumnsWindow_fast contact00 96 4 1132114846066 (by decide +kernel)
private theorem contact00ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact00) 100 4 = 999523657293 :=
  contactColumnsWindow_fast contact00 100 4 999523657293 (by decide +kernel)
private theorem contact00ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact00) 104 4 = 875515222684 :=
  contactColumnsWindow_fast contact00 104 4 875515222684 (by decide +kernel)
private theorem contact00ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact00) 108 4 = 760074618187 :=
  contactColumnsWindow_fast contact00 108 4 760074618187 (by decide +kernel)
private theorem contact00ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact00) 112 4 = 653187244989 :=
  contactColumnsWindow_fast contact00 112 4 653187244989 (by decide +kernel)
private theorem contact00ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact00) 116 4 = 554850339956 :=
  contactColumnsWindow_fast contact00 116 4 554850339956 (by decide +kernel)
private theorem contact00ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact00) 120 4 = 465064636811 :=
  contactColumnsWindow_fast contact00 120 4 465064636811 (by decide +kernel)
private theorem contact00ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact00) 124 4 = 383863921360 :=
  contactColumnsWindow_fast contact00 124 4 383863921360 (by decide +kernel)
private theorem contact00ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact00) 128 4 = 311228207580 :=
  contactColumnsWindow_fast contact00 128 4 311228207580 (by decide +kernel)
private theorem contact00ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact00) 132 4 = 247145315219 :=
  contactColumnsWindow_fast contact00 132 4 247145315219 (by decide +kernel)
private theorem contact00ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact00) 136 4 = 191605686088 :=
  contactColumnsWindow_fast contact00 136 4 191605686088 (by decide +kernel)
private theorem contact00ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact00) 140 4 = 144508009802 :=
  contactColumnsWindow_fast contact00 140 4 144508009802 (by decide +kernel)
private theorem contact00ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact00) 144 4 = 105582956426 :=
  contactColumnsWindow_fast contact00 144 4 105582956426 (by decide +kernel)
private theorem contact00ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact00) 148 4 = 74332082981 :=
  contactColumnsWindow_fast contact00 148 4 74332082981 (by decide +kernel)
private theorem contact00ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact00) 152 4 = 50112101722 :=
  contactColumnsWindow_fast contact00 152 4 50112101722 (by decide +kernel)
private theorem contact00ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact00) 156 4 = 32126631109 :=
  contactColumnsWindow_fast contact00 156 4 32126631109 (by decide +kernel)
private theorem contact00ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact00) 160 2 = 11009919243 :=
  contactColumnsWindow_fast contact00 160 2 11009919243 (by decide +kernel)
private theorem contact00ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact00) 0 8 = 13425654521048 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 4 4 6881798697340 6543855823708 contact00ColumnsSlice0 contact00ColumnsSlice4
private theorem contact00ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact00) 8 8 = 12108052497680 :=
  combineSlices (auxiliaryColumnSlice contact00) 8 4 4 6214454613844 5893597883836 contact00ColumnsSlice8 contact00ColumnsSlice12
private theorem contact00ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact00) 16 8 = 10858797752895 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 4 4 5581283714547 5277514038348 contact00ColumnsSlice16 contact00ColumnsSlice20
private theorem contact00ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact00) 24 8 = 9677973321546 :=
  combineSlices (auxiliaryColumnSlice contact00) 24 4 4 4982303410308 4695669911238 contact00ColumnsSlice24 contact00ColumnsSlice28
private theorem contact00ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact00) 32 8 = 8565627816817 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 4 4 4417584026364 4148043790453 contact00ColumnsSlice32 contact00ColumnsSlice36
private theorem contact00ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact00) 40 8 = 7521675036659 :=
  combineSlices (auxiliaryColumnSlice contact00) 40 4 4 3887051055364 3634623981295 contact00ColumnsSlice40 contact00ColumnsSlice44
private theorem contact00ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact00) 48 8 = 6546249444506 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 4 4 3390774734338 3155474710168 contact00ColumnsSlice48 contact00ColumnsSlice52
private theorem contact00ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact00) 56 8 = 5639248541925 :=
  combineSlices (auxiliaryColumnSlice contact00) 56 4 4 2928724548661 2710523993264 contact00ColumnsSlice56 contact00ColumnsSlice60
private theorem contact00ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact00) 64 8 = 4800746521616 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 4 4 2500898375653 2299848145963 contact00ColumnsSlice64 contact00ColumnsSlice68
private theorem contact00ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact00) 72 8 = 4030758315266 :=
  combineSlices (auxiliaryColumnSlice contact00) 72 4 4 2107352028612 1923406286654 contact00ColumnsSlice72 contact00ColumnsSlice76
private theorem contact00ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact00) 80 8 = 3329203268188 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 4 4 1748009925636 1581193342552 contact00ColumnsSlice80 contact00ColumnsSlice84
private theorem contact00ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact00) 88 8 = 2696204145209 :=
  combineSlices (auxiliaryColumnSlice contact00) 88 4 4 1422947939373 1273256205836 contact00ColumnsSlice88 contact00ColumnsSlice92
private theorem contact00ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact00) 96 8 = 2131638503359 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 4 4 1132114846066 999523657293 contact00ColumnsSlice96 contact00ColumnsSlice100
private theorem contact00ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact00) 104 8 = 1635589840871 :=
  combineSlices (auxiliaryColumnSlice contact00) 104 4 4 875515222684 760074618187 contact00ColumnsSlice104 contact00ColumnsSlice108
private theorem contact00ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact00) 112 8 = 1208037584945 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 4 4 653187244989 554850339956 contact00ColumnsSlice112 contact00ColumnsSlice116
private theorem contact00ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact00) 120 8 = 848928558171 :=
  combineSlices (auxiliaryColumnSlice contact00) 120 4 4 465064636811 383863921360 contact00ColumnsSlice120 contact00ColumnsSlice124
private theorem contact00ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact00) 128 8 = 558373522799 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 4 4 311228207580 247145315219 contact00ColumnsSlice128 contact00ColumnsSlice132
private theorem contact00ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact00) 136 8 = 336113695890 :=
  combineSlices (auxiliaryColumnSlice contact00) 136 4 4 191605686088 144508009802 contact00ColumnsSlice136 contact00ColumnsSlice140
private theorem contact00ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact00) 144 8 = 179915039407 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 4 4 105582956426 74332082981 contact00ColumnsSlice144 contact00ColumnsSlice148
private theorem contact00ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact00) 152 8 = 82238732831 :=
  combineSlices (auxiliaryColumnSlice contact00) 152 4 4 50112101722 32126631109 contact00ColumnsSlice152 contact00ColumnsSlice156
private theorem contact00ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact00) 0 16 = 25533707018728 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 8 8 13425654521048 12108052497680 contact00ColumnsJoin0_8 contact00ColumnsJoin8_8
private theorem contact00ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact00) 16 16 = 20536771074441 :=
  combineSlices (auxiliaryColumnSlice contact00) 16 8 8 10858797752895 9677973321546 contact00ColumnsJoin16_8 contact00ColumnsJoin24_8
private theorem contact00ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact00) 32 16 = 16087302853476 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 8 8 8565627816817 7521675036659 contact00ColumnsJoin32_8 contact00ColumnsJoin40_8
private theorem contact00ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact00) 48 16 = 12185497986431 :=
  combineSlices (auxiliaryColumnSlice contact00) 48 8 8 6546249444506 5639248541925 contact00ColumnsJoin48_8 contact00ColumnsJoin56_8
private theorem contact00ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact00) 64 16 = 8831504836882 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 8 8 4800746521616 4030758315266 contact00ColumnsJoin64_8 contact00ColumnsJoin72_8
private theorem contact00ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact00) 80 16 = 6025407413397 :=
  combineSlices (auxiliaryColumnSlice contact00) 80 8 8 3329203268188 2696204145209 contact00ColumnsJoin80_8 contact00ColumnsJoin88_8
private theorem contact00ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact00) 96 16 = 3767228344230 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 8 8 2131638503359 1635589840871 contact00ColumnsJoin96_8 contact00ColumnsJoin104_8
private theorem contact00ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact00) 112 16 = 2056966143116 :=
  combineSlices (auxiliaryColumnSlice contact00) 112 8 8 1208037584945 848928558171 contact00ColumnsJoin112_8 contact00ColumnsJoin120_8
private theorem contact00ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact00) 128 16 = 894487218689 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 8 8 558373522799 336113695890 contact00ColumnsJoin128_8 contact00ColumnsJoin136_8
private theorem contact00ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact00) 144 16 = 262153772238 :=
  combineSlices (auxiliaryColumnSlice contact00) 144 8 8 179915039407 82238732831 contact00ColumnsJoin144_8 contact00ColumnsJoin152_8
private theorem contact00ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact00) 0 32 = 46070478093169 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 16 16 25533707018728 20536771074441 contact00ColumnsJoin0_16 contact00ColumnsJoin16_16
private theorem contact00ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact00) 32 32 = 28272800839907 :=
  combineSlices (auxiliaryColumnSlice contact00) 32 16 16 16087302853476 12185497986431 contact00ColumnsJoin32_16 contact00ColumnsJoin48_16
private theorem contact00ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact00) 64 32 = 14856912250279 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 16 16 8831504836882 6025407413397 contact00ColumnsJoin64_16 contact00ColumnsJoin80_16
private theorem contact00ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact00) 96 32 = 5824194487346 :=
  combineSlices (auxiliaryColumnSlice contact00) 96 16 16 3767228344230 2056966143116 contact00ColumnsJoin96_16 contact00ColumnsJoin112_16
private theorem contact00ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact00) 128 32 = 1156640990927 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 16 16 894487218689 262153772238 contact00ColumnsJoin128_16 contact00ColumnsJoin144_16
private theorem contact00ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact00) 0 64 = 74343278933076 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 32 32 46070478093169 28272800839907 contact00ColumnsJoin0_32 contact00ColumnsJoin32_32
private theorem contact00ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact00) 64 64 = 20681106737625 :=
  combineSlices (auxiliaryColumnSlice contact00) 64 32 32 14856912250279 5824194487346 contact00ColumnsJoin64_32 contact00ColumnsJoin96_32
private theorem contact00ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact00) 128 34 = 1167650910170 :=
  combineSlices (auxiliaryColumnSlice contact00) 128 32 2 1156640990927 11009919243 contact00ColumnsJoin128_32 contact00ColumnsSlice160
private theorem contact00ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact00) 0 128 = 95024385670701 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 64 64 74343278933076 20681106737625 contact00ColumnsJoin0_64 contact00ColumnsJoin64_64
private theorem contact00ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact00) 0 162 = 96192036580871 :=
  combineSlices (auxiliaryColumnSlice contact00) 0 128 34 95024385670701 1167650910170 contact00ColumnsJoin0_128 contact00ColumnsJoin128_34
private theorem contact00OrdinaryRanks : ordinaryRankBound contact00 = 9600667787 := by decide +kernel
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
  margin_of_checked_counts contact00 162 2496927484456951 96192036580871 9600667787 291293596 rfl contact00OrdinaryColumns contact00ColumnsJoin0_162 contact00OrdinaryRanks contact00RanksJoin0_162 (by decide +kernel)

private theorem contact02OrdinaryColumns : ordinaryColumnCount contact02 = 3629712859700402 := by decide +kernel
private theorem contact02ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact02) 0 4 = 11545624122054 :=
  contactColumnsWindow_fast contact02 0 4 11545624122054 (by decide +kernel)
private theorem contact02ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact02) 4 4 = 11028851486214 :=
  contactColumnsWindow_fast contact02 4 4 11028851486214 (by decide +kernel)
private theorem contact02ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact02) 8 4 = 10523975178246 :=
  contactColumnsWindow_fast contact02 8 4 10523975178246 (by decide +kernel)
private theorem contact02ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact02) 12 4 = 10030995198150 :=
  contactColumnsWindow_fast contact02 12 4 10030995198150 (by decide +kernel)
private theorem contact02ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact02) 16 4 = 9549911545926 :=
  contactColumnsWindow_fast contact02 16 4 9549911545926 (by decide +kernel)
private theorem contact02ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact02) 20 4 = 9080724221574 :=
  contactColumnsWindow_fast contact02 20 4 9080724221574 (by decide +kernel)
private theorem contact02ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact02) 24 4 = 8623433225094 :=
  contactColumnsWindow_fast contact02 24 4 8623433225094 (by decide +kernel)
private theorem contact02ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact02) 28 4 = 8178038556486 :=
  contactColumnsWindow_fast contact02 28 4 8178038556486 (by decide +kernel)
private theorem contact02ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact02) 32 4 = 7744540215750 :=
  contactColumnsWindow_fast contact02 32 4 7744540215750 (by decide +kernel)
private theorem contact02ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact02) 36 4 = 7322938202886 :=
  contactColumnsWindow_fast contact02 36 4 7322938202886 (by decide +kernel)
private theorem contact02ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact02) 40 4 = 6913232517894 :=
  contactColumnsWindow_fast contact02 40 4 6913232517894 (by decide +kernel)
private theorem contact02ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact02) 44 4 = 6515423160774 :=
  contactColumnsWindow_fast contact02 44 4 6515423160774 (by decide +kernel)
private theorem contact02ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact02) 48 4 = 6129510131526 :=
  contactColumnsWindow_fast contact02 48 4 6129510131526 (by decide +kernel)
private theorem contact02ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact02) 52 4 = 5755493430150 :=
  contactColumnsWindow_fast contact02 52 4 5755493430150 (by decide +kernel)
private theorem contact02ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact02) 56 4 = 5393381134560 :=
  contactColumnsWindow_fast contact02 56 4 5393381134560 (by decide +kernel)
private theorem contact02ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact02) 60 4 = 5043231849978 :=
  contactColumnsWindow_fast contact02 60 4 5043231849978 (by decide +kernel)
private theorem contact02ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact02) 64 4 = 4704994035151 :=
  contactColumnsWindow_fast contact02 64 4 4704994035151 (by decide +kernel)
private theorem contact02ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact02) 68 4 = 4378657276928 :=
  contactColumnsWindow_fast contact02 68 4 4378657276928 (by decide +kernel)
private theorem contact02ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact02) 72 4 = 4064219006732 :=
  contactColumnsWindow_fast contact02 72 4 4064219006732 (by decide +kernel)
private theorem contact02ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact02) 76 4 = 3761693970500 :=
  contactColumnsWindow_fast contact02 76 4 3761693970500 (by decide +kernel)
private theorem contact02ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact02) 80 4 = 3471134532266 :=
  contactColumnsWindow_fast contact02 80 4 3471134532266 (by decide +kernel)
private theorem contact02ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact02) 84 4 = 3192487097077 :=
  contactColumnsWindow_fast contact02 84 4 3192487097077 (by decide +kernel)
private theorem contact02ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact02) 88 4 = 2925743901984 :=
  contactColumnsWindow_fast contact02 88 4 2925743901984 (by decide +kernel)
private theorem contact02ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact02) 92 4 = 2670903143415 :=
  contactColumnsWindow_fast contact02 92 4 2670903143415 (by decide +kernel)
private theorem contact02ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact02) 96 4 = 2427983750094 :=
  contactColumnsWindow_fast contact02 96 4 2427983750094 (by decide +kernel)
private theorem contact02ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact02) 100 4 = 2197033445565 :=
  contactColumnsWindow_fast contact02 100 4 2197033445565 (by decide +kernel)
private theorem contact02ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact02) 104 4 = 1977995920530 :=
  contactColumnsWindow_fast contact02 104 4 1977995920530 (by decide +kernel)
private theorem contact02ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact02) 108 4 = 1770865558737 :=
  contactColumnsWindow_fast contact02 108 4 1770865558737 (by decide +kernel)
private theorem contact02ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact02) 112 4 = 1575643059788 :=
  contactColumnsWindow_fast contact02 112 4 1575643059788 (by decide +kernel)
private theorem contact02ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact02) 116 4 = 1392349674697 :=
  contactColumnsWindow_fast contact02 116 4 1392349674697 (by decide +kernel)
private theorem contact02ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact02) 120 4 = 1221021557832 :=
  contactColumnsWindow_fast contact02 120 4 1221021557832 (by decide +kernel)
private theorem contact02ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact02) 124 4 = 1061604213846 :=
  contactColumnsWindow_fast contact02 124 4 1061604213846 (by decide +kernel)
private theorem contact02ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact02) 128 4 = 914094110501 :=
  contactColumnsWindow_fast contact02 128 4 914094110501 (by decide +kernel)
private theorem contact02ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact02) 132 4 = 778491948721 :=
  contactColumnsWindow_fast contact02 132 4 778491948721 (by decide +kernel)
private theorem contact02ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact02) 136 4 = 654824503731 :=
  contactColumnsWindow_fast contact02 136 4 654824503731 (by decide +kernel)
private theorem contact02ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact02) 140 4 = 543118528281 :=
  contactColumnsWindow_fast contact02 140 4 543118528281 (by decide +kernel)
private theorem contact02ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact02) 144 4 = 443321361884 :=
  contactColumnsWindow_fast contact02 144 4 443321361884 (by decide +kernel)
private theorem contact02ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact02) 148 4 = 355406671709 :=
  contactColumnsWindow_fast contact02 148 4 355406671709 (by decide +kernel)
private theorem contact02ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact02) 152 4 = 279202284328 :=
  contactColumnsWindow_fast contact02 152 4 279202284328 (by decide +kernel)
private theorem contact02ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact02) 156 4 = 214365447627 :=
  contactColumnsWindow_fast contact02 156 4 214365447627 (by decide +kernel)
private theorem contact02ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact02) 160 4 = 160364899053 :=
  contactColumnsWindow_fast contact02 160 4 160364899053 (by decide +kernel)
private theorem contact02ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact02) 164 4 = 116445016298 :=
  contactColumnsWindow_fast contact02 164 4 116445016298 (by decide +kernel)
private theorem contact02ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact02) 168 4 = 81736484981 :=
  contactColumnsWindow_fast contact02 168 4 81736484981 (by decide +kernel)
private theorem contact02ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact02) 172 4 = 55210084323 :=
  contactColumnsWindow_fast contact02 172 4 55210084323 (by decide +kernel)
private theorem contact02ColumnsSlice176 : sliceWindow (auxiliaryColumnSlice contact02) 176 1 = 10506802407 :=
  contactColumnsWindow_fast contact02 176 1 10506802407 (by decide +kernel)
private theorem contact02ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact02) 0 8 = 22574475608268 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 4 4 11545624122054 11028851486214 contact02ColumnsSlice0 contact02ColumnsSlice4
private theorem contact02ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact02) 8 8 = 20554970376396 :=
  combineSlices (auxiliaryColumnSlice contact02) 8 4 4 10523975178246 10030995198150 contact02ColumnsSlice8 contact02ColumnsSlice12
private theorem contact02ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact02) 16 8 = 18630635767500 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 4 4 9549911545926 9080724221574 contact02ColumnsSlice16 contact02ColumnsSlice20
private theorem contact02ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact02) 24 8 = 16801471781580 :=
  combineSlices (auxiliaryColumnSlice contact02) 24 4 4 8623433225094 8178038556486 contact02ColumnsSlice24 contact02ColumnsSlice28
private theorem contact02ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact02) 32 8 = 15067478418636 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 4 4 7744540215750 7322938202886 contact02ColumnsSlice32 contact02ColumnsSlice36
private theorem contact02ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact02) 40 8 = 13428655678668 :=
  combineSlices (auxiliaryColumnSlice contact02) 40 4 4 6913232517894 6515423160774 contact02ColumnsSlice40 contact02ColumnsSlice44
private theorem contact02ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact02) 48 8 = 11885003561676 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 4 4 6129510131526 5755493430150 contact02ColumnsSlice48 contact02ColumnsSlice52
private theorem contact02ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact02) 56 8 = 10436612984538 :=
  combineSlices (auxiliaryColumnSlice contact02) 56 4 4 5393381134560 5043231849978 contact02ColumnsSlice56 contact02ColumnsSlice60
private theorem contact02ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact02) 64 8 = 9083651312079 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 4 4 4704994035151 4378657276928 contact02ColumnsSlice64 contact02ColumnsSlice68
private theorem contact02ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact02) 72 8 = 7825912977232 :=
  combineSlices (auxiliaryColumnSlice contact02) 72 4 4 4064219006732 3761693970500 contact02ColumnsSlice72 contact02ColumnsSlice76
private theorem contact02ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact02) 80 8 = 6663621629343 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 4 4 3471134532266 3192487097077 contact02ColumnsSlice80 contact02ColumnsSlice84
private theorem contact02ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact02) 88 8 = 5596647045399 :=
  combineSlices (auxiliaryColumnSlice contact02) 88 4 4 2925743901984 2670903143415 contact02ColumnsSlice88 contact02ColumnsSlice92
private theorem contact02ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact02) 96 8 = 4625017195659 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 4 4 2427983750094 2197033445565 contact02ColumnsSlice96 contact02ColumnsSlice100
private theorem contact02ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact02) 104 8 = 3748861479267 :=
  combineSlices (auxiliaryColumnSlice contact02) 104 4 4 1977995920530 1770865558737 contact02ColumnsSlice104 contact02ColumnsSlice108
private theorem contact02ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact02) 112 8 = 2967992734485 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 4 4 1575643059788 1392349674697 contact02ColumnsSlice112 contact02ColumnsSlice116
private theorem contact02ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact02) 120 8 = 2282625771678 :=
  combineSlices (auxiliaryColumnSlice contact02) 120 4 4 1221021557832 1061604213846 contact02ColumnsSlice120 contact02ColumnsSlice124
private theorem contact02ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact02) 128 8 = 1692586059222 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 4 4 914094110501 778491948721 contact02ColumnsSlice128 contact02ColumnsSlice132
private theorem contact02ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact02) 136 8 = 1197943032012 :=
  combineSlices (auxiliaryColumnSlice contact02) 136 4 4 654824503731 543118528281 contact02ColumnsSlice136 contact02ColumnsSlice140
private theorem contact02ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact02) 144 8 = 798728033593 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 4 4 443321361884 355406671709 contact02ColumnsSlice144 contact02ColumnsSlice148
private theorem contact02ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact02) 152 8 = 493567731955 :=
  combineSlices (auxiliaryColumnSlice contact02) 152 4 4 279202284328 214365447627 contact02ColumnsSlice152 contact02ColumnsSlice156
private theorem contact02ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact02) 160 8 = 276809915351 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 4 4 160364899053 116445016298 contact02ColumnsSlice160 contact02ColumnsSlice164
private theorem contact02ColumnsJoin168_8 : sliceWindow (auxiliaryColumnSlice contact02) 168 8 = 136946569304 :=
  combineSlices (auxiliaryColumnSlice contact02) 168 4 4 81736484981 55210084323 contact02ColumnsSlice168 contact02ColumnsSlice172
private theorem contact02ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact02) 0 16 = 43129445984664 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 8 8 22574475608268 20554970376396 contact02ColumnsJoin0_8 contact02ColumnsJoin8_8
private theorem contact02ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact02) 16 16 = 35432107549080 :=
  combineSlices (auxiliaryColumnSlice contact02) 16 8 8 18630635767500 16801471781580 contact02ColumnsJoin16_8 contact02ColumnsJoin24_8
private theorem contact02ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact02) 32 16 = 28496134097304 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 8 8 15067478418636 13428655678668 contact02ColumnsJoin32_8 contact02ColumnsJoin40_8
private theorem contact02ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact02) 48 16 = 22321616546214 :=
  combineSlices (auxiliaryColumnSlice contact02) 48 8 8 11885003561676 10436612984538 contact02ColumnsJoin48_8 contact02ColumnsJoin56_8
private theorem contact02ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact02) 64 16 = 16909564289311 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 8 8 9083651312079 7825912977232 contact02ColumnsJoin64_8 contact02ColumnsJoin72_8
private theorem contact02ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact02) 80 16 = 12260268674742 :=
  combineSlices (auxiliaryColumnSlice contact02) 80 8 8 6663621629343 5596647045399 contact02ColumnsJoin80_8 contact02ColumnsJoin88_8
private theorem contact02ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact02) 96 16 = 8373878674926 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 8 8 4625017195659 3748861479267 contact02ColumnsJoin96_8 contact02ColumnsJoin104_8
private theorem contact02ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact02) 112 16 = 5250618506163 :=
  combineSlices (auxiliaryColumnSlice contact02) 112 8 8 2967992734485 2282625771678 contact02ColumnsJoin112_8 contact02ColumnsJoin120_8
private theorem contact02ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact02) 128 16 = 2890529091234 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 8 8 1692586059222 1197943032012 contact02ColumnsJoin128_8 contact02ColumnsJoin136_8
private theorem contact02ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact02) 144 16 = 1292295765548 :=
  combineSlices (auxiliaryColumnSlice contact02) 144 8 8 798728033593 493567731955 contact02ColumnsJoin144_8 contact02ColumnsJoin152_8
private theorem contact02ColumnsJoin160_16 : sliceWindow (auxiliaryColumnSlice contact02) 160 16 = 413756484655 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 8 8 276809915351 136946569304 contact02ColumnsJoin160_8 contact02ColumnsJoin168_8
private theorem contact02ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact02) 0 32 = 78561553533744 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 16 16 43129445984664 35432107549080 contact02ColumnsJoin0_16 contact02ColumnsJoin16_16
private theorem contact02ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact02) 32 32 = 50817750643518 :=
  combineSlices (auxiliaryColumnSlice contact02) 32 16 16 28496134097304 22321616546214 contact02ColumnsJoin32_16 contact02ColumnsJoin48_16
private theorem contact02ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact02) 64 32 = 29169832964053 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 16 16 16909564289311 12260268674742 contact02ColumnsJoin64_16 contact02ColumnsJoin80_16
private theorem contact02ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact02) 96 32 = 13624497181089 :=
  combineSlices (auxiliaryColumnSlice contact02) 96 16 16 8373878674926 5250618506163 contact02ColumnsJoin96_16 contact02ColumnsJoin112_16
private theorem contact02ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact02) 128 32 = 4182824856782 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 16 16 2890529091234 1292295765548 contact02ColumnsJoin128_16 contact02ColumnsJoin144_16
private theorem contact02ColumnsJoin160_17 : sliceWindow (auxiliaryColumnSlice contact02) 160 17 = 424263287062 :=
  combineSlices (auxiliaryColumnSlice contact02) 160 16 1 413756484655 10506802407 contact02ColumnsJoin160_16 contact02ColumnsSlice176
private theorem contact02ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact02) 0 64 = 129379304177262 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 32 32 78561553533744 50817750643518 contact02ColumnsJoin0_32 contact02ColumnsJoin32_32
private theorem contact02ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact02) 64 64 = 42794330145142 :=
  combineSlices (auxiliaryColumnSlice contact02) 64 32 32 29169832964053 13624497181089 contact02ColumnsJoin64_32 contact02ColumnsJoin96_32
private theorem contact02ColumnsJoin128_49 : sliceWindow (auxiliaryColumnSlice contact02) 128 49 = 4607088143844 :=
  combineSlices (auxiliaryColumnSlice contact02) 128 32 17 4182824856782 424263287062 contact02ColumnsJoin128_32 contact02ColumnsJoin160_17
private theorem contact02ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact02) 0 128 = 172173634322404 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 64 64 129379304177262 42794330145142 contact02ColumnsJoin0_64 contact02ColumnsJoin64_64
private theorem contact02ColumnsJoin0_177 : sliceWindow (auxiliaryColumnSlice contact02) 0 177 = 176780722466248 :=
  combineSlices (auxiliaryColumnSlice contact02) 0 128 49 172173634322404 4607088143844 contact02ColumnsJoin0_128 contact02ColumnsJoin128_49
private theorem contact02OrdinaryRanks : ordinaryRankBound contact02 = 13980580887 := by decide +kernel
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
  margin_of_checked_counts contact02 177 3629712859700402 176780722466248 13980580887 540031017 rfl contact02OrdinaryColumns contact02ColumnsJoin0_177 contact02OrdinaryRanks contact02RanksJoin0_177 (by decide +kernel)

private theorem contact04OrdinaryColumns : ordinaryColumnCount contact04 = 1828077132918269 := by decide +kernel
private theorem contact04ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact04) 0 4 = 8026595104830 :=
  contactColumnsWindow_fast contact04 0 4 8026595104830 (by decide +kernel)
private theorem contact04ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact04) 4 4 = 7637502333774 :=
  contactColumnsWindow_fast contact04 4 4 7637502333774 (by decide +kernel)
private theorem contact04ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact04) 8 4 = 7258151595550 :=
  contactColumnsWindow_fast contact04 8 4 7258151595550 (by decide +kernel)
private theorem contact04ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact04) 12 4 = 6888539167187 :=
  contactColumnsWindow_fast contact04 12 4 6888539167187 (by decide +kernel)
private theorem contact04ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact04) 16 4 = 6528636076182 :=
  contactColumnsWindow_fast contact04 16 4 6528636076182 (by decide +kernel)
private theorem contact04ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact04) 20 4 = 6178443488826 :=
  contactColumnsWindow_fast contact04 20 4 6178443488826 (by decide +kernel)
private theorem contact04ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact04) 24 4 = 5837963503910 :=
  contactColumnsWindow_fast contact04 24 4 5837963503910 (by decide +kernel)
private theorem contact04ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact04) 28 4 = 5507234069598 :=
  contactColumnsWindow_fast contact04 28 4 5507234069598 (by decide +kernel)
private theorem contact04ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact04) 32 4 = 5186241245961 :=
  contactColumnsWindow_fast contact04 32 4 5186241245961 (by decide +kernel)
private theorem contact04ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact04) 36 4 = 4874960024230 :=
  contactColumnsWindow_fast contact04 36 4 4874960024230 (by decide +kernel)
private theorem contact04ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact04) 40 4 = 4573394368654 :=
  contactColumnsWindow_fast contact04 40 4 4573394368654 (by decide +kernel)
private theorem contact04ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact04) 44 4 = 4281544799790 :=
  contactColumnsWindow_fast contact04 44 4 4281544799790 (by decide +kernel)
private theorem contact04ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact04) 48 4 = 3999453790746 :=
  contactColumnsWindow_fast contact04 48 4 3999453790746 (by decide +kernel)
private theorem contact04ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact04) 52 4 = 3727097206567 :=
  contactColumnsWindow_fast contact04 52 4 3727097206567 (by decide +kernel)
private theorem contact04ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact04) 56 4 = 3464457068385 :=
  contactColumnsWindow_fast contact04 56 4 3464457068385 (by decide +kernel)
private theorem contact04ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact04) 60 4 = 3211532735182 :=
  contactColumnsWindow_fast contact04 60 4 3211532735182 (by decide +kernel)
private theorem contact04ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact04) 64 4 = 2968325886014 :=
  contactColumnsWindow_fast contact04 64 4 2968325886014 (by decide +kernel)
private theorem contact04ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact04) 68 4 = 2734880537214 :=
  contactColumnsWindow_fast contact04 68 4 2734880537214 (by decide +kernel)
private theorem contact04ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact04) 72 4 = 2511165381906 :=
  contactColumnsWindow_fast contact04 72 4 2511165381906 (by decide +kernel)
private theorem contact04ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact04) 76 4 = 2297166569615 :=
  contactColumnsWindow_fast contact04 76 4 2297166569615 (by decide +kernel)
private theorem contact04ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact04) 80 4 = 2092883395510 :=
  contactColumnsWindow_fast contact04 80 4 2092883395510 (by decide +kernel)
private theorem contact04ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact04) 84 4 = 1898319755314 :=
  contactColumnsWindow_fast contact04 84 4 1898319755314 (by decide +kernel)
private theorem contact04ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact04) 88 4 = 1713519705111 :=
  contactColumnsWindow_fast contact04 88 4 1713519705111 (by decide +kernel)
private theorem contact04ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact04) 92 4 = 1538445977694 :=
  contactColumnsWindow_fast contact04 92 4 1538445977694 (by decide +kernel)
private theorem contact04ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact04) 96 4 = 1373088364645 :=
  contactColumnsWindow_fast contact04 96 4 1373088364645 (by decide +kernel)
private theorem contact04ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact04) 100 4 = 1217446414906 :=
  contactColumnsWindow_fast contact04 100 4 1217446414906 (by decide +kernel)
private theorem contact04ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact04) 104 4 = 1071527205510 :=
  contactColumnsWindow_fast contact04 104 4 1071527205510 (by decide +kernel)
private theorem contact04ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact04) 108 4 = 935371184701 :=
  contactColumnsWindow_fast contact04 108 4 935371184701 (by decide +kernel)
private theorem contact04ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact04) 112 4 = 808938874329 :=
  contactColumnsWindow_fast contact04 112 4 808938874329 (by decide +kernel)
private theorem contact04ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact04) 116 4 = 692222659470 :=
  contactColumnsWindow_fast contact04 116 4 692222659470 (by decide +kernel)
private theorem contact04ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact04) 120 4 = 585221803338 :=
  contactColumnsWindow_fast contact04 120 4 585221803338 (by decide +kernel)
private theorem contact04ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact04) 124 4 = 487946949506 :=
  contactColumnsWindow_fast contact04 124 4 487946949506 (by decide +kernel)
private theorem contact04ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact04) 128 4 = 400435116326 :=
  contactColumnsWindow_fast contact04 128 4 400435116326 (by decide +kernel)
private theorem contact04ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact04) 132 4 = 322644193203 :=
  contactColumnsWindow_fast contact04 132 4 322644193203 (by decide +kernel)
private theorem contact04ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact04) 136 4 = 254563220076 :=
  contactColumnsWindow_fast contact04 136 4 254563220076 (by decide +kernel)
private theorem contact04ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact04) 140 4 = 196094398416 :=
  contactColumnsWindow_fast contact04 140 4 196094398416 (by decide +kernel)
private theorem contact04ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact04) 144 4 = 146960179459 :=
  contactColumnsWindow_fast contact04 144 4 146960179459 (by decide +kernel)
private theorem contact04ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact04) 148 4 = 106724528630 :=
  contactColumnsWindow_fast contact04 148 4 106724528630 (by decide +kernel)
private theorem contact04ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact04) 152 4 = 74716821826 :=
  contactColumnsWindow_fast contact04 152 4 74716821826 (by decide +kernel)
private theorem contact04ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact04) 156 4 = 50144442855 :=
  contactColumnsWindow_fast contact04 156 4 50144442855 (by decide +kernel)
private theorem contact04ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact04) 160 2 = 17925140098 :=
  contactColumnsWindow_fast contact04 160 2 17925140098 (by decide +kernel)
private theorem contact04ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact04) 0 8 = 15664097438604 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 4 4 8026595104830 7637502333774 contact04ColumnsSlice0 contact04ColumnsSlice4
private theorem contact04ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact04) 8 8 = 14146690762737 :=
  combineSlices (auxiliaryColumnSlice contact04) 8 4 4 7258151595550 6888539167187 contact04ColumnsSlice8 contact04ColumnsSlice12
private theorem contact04ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact04) 16 8 = 12707079565008 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 4 4 6528636076182 6178443488826 contact04ColumnsSlice16 contact04ColumnsSlice20
private theorem contact04ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact04) 24 8 = 11345197573508 :=
  combineSlices (auxiliaryColumnSlice contact04) 24 4 4 5837963503910 5507234069598 contact04ColumnsSlice24 contact04ColumnsSlice28
private theorem contact04ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact04) 32 8 = 10061201270191 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 4 4 5186241245961 4874960024230 contact04ColumnsSlice32 contact04ColumnsSlice36
private theorem contact04ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact04) 40 8 = 8854939168444 :=
  combineSlices (auxiliaryColumnSlice contact04) 40 4 4 4573394368654 4281544799790 contact04ColumnsSlice40 contact04ColumnsSlice44
private theorem contact04ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact04) 48 8 = 7726550997313 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 4 4 3999453790746 3727097206567 contact04ColumnsSlice48 contact04ColumnsSlice52
private theorem contact04ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact04) 56 8 = 6675989803567 :=
  combineSlices (auxiliaryColumnSlice contact04) 56 4 4 3464457068385 3211532735182 contact04ColumnsSlice56 contact04ColumnsSlice60
private theorem contact04ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact04) 64 8 = 5703206423228 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 4 4 2968325886014 2734880537214 contact04ColumnsSlice64 contact04ColumnsSlice68
private theorem contact04ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact04) 72 8 = 4808331951521 :=
  combineSlices (auxiliaryColumnSlice contact04) 72 4 4 2511165381906 2297166569615 contact04ColumnsSlice72 contact04ColumnsSlice76
private theorem contact04ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact04) 80 8 = 3991203150824 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 4 4 2092883395510 1898319755314 contact04ColumnsSlice80 contact04ColumnsSlice84
private theorem contact04ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact04) 88 8 = 3251965682805 :=
  combineSlices (auxiliaryColumnSlice contact04) 88 4 4 1713519705111 1538445977694 contact04ColumnsSlice88 contact04ColumnsSlice92
private theorem contact04ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact04) 96 8 = 2590534779551 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 4 4 1373088364645 1217446414906 contact04ColumnsSlice96 contact04ColumnsSlice100
private theorem contact04ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact04) 104 8 = 2006898390211 :=
  combineSlices (auxiliaryColumnSlice contact04) 104 4 4 1071527205510 935371184701 contact04ColumnsSlice104 contact04ColumnsSlice108
private theorem contact04ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact04) 112 8 = 1501161533799 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 4 4 808938874329 692222659470 contact04ColumnsSlice112 contact04ColumnsSlice116
private theorem contact04ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact04) 120 8 = 1073168752844 :=
  combineSlices (auxiliaryColumnSlice contact04) 120 4 4 585221803338 487946949506 contact04ColumnsSlice120 contact04ColumnsSlice124
private theorem contact04ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact04) 128 8 = 723079309529 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 4 4 400435116326 322644193203 contact04ColumnsSlice128 contact04ColumnsSlice132
private theorem contact04ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact04) 136 8 = 450657618492 :=
  combineSlices (auxiliaryColumnSlice contact04) 136 4 4 254563220076 196094398416 contact04ColumnsSlice136 contact04ColumnsSlice140
private theorem contact04ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact04) 144 8 = 253684708089 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 4 4 146960179459 106724528630 contact04ColumnsSlice144 contact04ColumnsSlice148
private theorem contact04ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact04) 152 8 = 124861264681 :=
  combineSlices (auxiliaryColumnSlice contact04) 152 4 4 74716821826 50144442855 contact04ColumnsSlice152 contact04ColumnsSlice156
private theorem contact04ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact04) 0 16 = 29810788201341 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 8 8 15664097438604 14146690762737 contact04ColumnsJoin0_8 contact04ColumnsJoin8_8
private theorem contact04ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact04) 16 16 = 24052277138516 :=
  combineSlices (auxiliaryColumnSlice contact04) 16 8 8 12707079565008 11345197573508 contact04ColumnsJoin16_8 contact04ColumnsJoin24_8
private theorem contact04ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact04) 32 16 = 18916140438635 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 8 8 10061201270191 8854939168444 contact04ColumnsJoin32_8 contact04ColumnsJoin40_8
private theorem contact04ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact04) 48 16 = 14402540800880 :=
  combineSlices (auxiliaryColumnSlice contact04) 48 8 8 7726550997313 6675989803567 contact04ColumnsJoin48_8 contact04ColumnsJoin56_8
private theorem contact04ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact04) 64 16 = 10511538374749 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 8 8 5703206423228 4808331951521 contact04ColumnsJoin64_8 contact04ColumnsJoin72_8
private theorem contact04ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact04) 80 16 = 7243168833629 :=
  combineSlices (auxiliaryColumnSlice contact04) 80 8 8 3991203150824 3251965682805 contact04ColumnsJoin80_8 contact04ColumnsJoin88_8
private theorem contact04ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact04) 96 16 = 4597433169762 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 8 8 2590534779551 2006898390211 contact04ColumnsJoin96_8 contact04ColumnsJoin104_8
private theorem contact04ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact04) 112 16 = 2574330286643 :=
  combineSlices (auxiliaryColumnSlice contact04) 112 8 8 1501161533799 1073168752844 contact04ColumnsJoin112_8 contact04ColumnsJoin120_8
private theorem contact04ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact04) 128 16 = 1173736928021 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 8 8 723079309529 450657618492 contact04ColumnsJoin128_8 contact04ColumnsJoin136_8
private theorem contact04ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact04) 144 16 = 378545972770 :=
  combineSlices (auxiliaryColumnSlice contact04) 144 8 8 253684708089 124861264681 contact04ColumnsJoin144_8 contact04ColumnsJoin152_8
private theorem contact04ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact04) 0 32 = 53863065339857 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 16 16 29810788201341 24052277138516 contact04ColumnsJoin0_16 contact04ColumnsJoin16_16
private theorem contact04ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact04) 32 32 = 33318681239515 :=
  combineSlices (auxiliaryColumnSlice contact04) 32 16 16 18916140438635 14402540800880 contact04ColumnsJoin32_16 contact04ColumnsJoin48_16
private theorem contact04ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact04) 64 32 = 17754707208378 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 16 16 10511538374749 7243168833629 contact04ColumnsJoin64_16 contact04ColumnsJoin80_16
private theorem contact04ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact04) 96 32 = 7171763456405 :=
  combineSlices (auxiliaryColumnSlice contact04) 96 16 16 4597433169762 2574330286643 contact04ColumnsJoin96_16 contact04ColumnsJoin112_16
private theorem contact04ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact04) 128 32 = 1552282900791 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 16 16 1173736928021 378545972770 contact04ColumnsJoin128_16 contact04ColumnsJoin144_16
private theorem contact04ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact04) 0 64 = 87181746579372 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 32 32 53863065339857 33318681239515 contact04ColumnsJoin0_32 contact04ColumnsJoin32_32
private theorem contact04ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact04) 64 64 = 24926470664783 :=
  combineSlices (auxiliaryColumnSlice contact04) 64 32 32 17754707208378 7171763456405 contact04ColumnsJoin64_32 contact04ColumnsJoin96_32
private theorem contact04ColumnsJoin128_34 : sliceWindow (auxiliaryColumnSlice contact04) 128 34 = 1570208040889 :=
  combineSlices (auxiliaryColumnSlice contact04) 128 32 2 1552282900791 17925140098 contact04ColumnsJoin128_32 contact04ColumnsSlice160
private theorem contact04ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact04) 0 128 = 112108217244155 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 64 64 87181746579372 24926470664783 contact04ColumnsJoin0_64 contact04ColumnsJoin64_64
private theorem contact04ColumnsJoin0_162 : sliceWindow (auxiliaryColumnSlice contact04) 0 162 = 113678425285044 :=
  combineSlices (auxiliaryColumnSlice contact04) 0 128 34 112108217244155 1570208040889 contact04ColumnsJoin0_128 contact04ColumnsJoin128_34
private theorem contact04OrdinaryRanks : ordinaryRankBound contact04 = 7061283193 := by decide +kernel
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
private theorem contact04RanksSlice148 : sliceWindow (auxiliaryRankSlice contact04) 148 14 = 0 :=
  contactRankWindow_of_rec contact04 148 14 0 (by decide +kernel)
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
private theorem contact04RanksJoin144_18 : sliceWindow (auxiliaryRankSlice contact04) 144 18 = 11531 :=
  combineSlices (auxiliaryRankSlice contact04) 144 4 14 11531 0 contact04RanksSlice144 contact04RanksSlice148
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
private theorem contact04RanksJoin128_34 : sliceWindow (auxiliaryRankSlice contact04) 128 34 = 682162 :=
  combineSlices (auxiliaryRankSlice contact04) 128 16 18 670631 11531 contact04RanksJoin128_16 contact04RanksJoin144_18
private theorem contact04RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact04) 0 64 = 292539634 :=
  combineSlices (auxiliaryRankSlice contact04) 0 32 32 192238512 100301122 contact04RanksJoin0_32 contact04RanksJoin32_32
private theorem contact04RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact04) 64 64 = 52702297 :=
  combineSlices (auxiliaryRankSlice contact04) 64 32 32 41695997 11006300 contact04RanksJoin64_32 contact04RanksJoin96_32
private theorem contact04RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact04) 0 128 = 345241931 :=
  combineSlices (auxiliaryRankSlice contact04) 0 64 64 292539634 52702297 contact04RanksJoin0_64 contact04RanksJoin64_64
private theorem contact04RanksJoin0_162 : sliceWindow (auxiliaryRankSlice contact04) 0 162 = 345924093 :=
  combineSlices (auxiliaryRankSlice contact04) 0 128 34 345241931 682162 contact04RanksJoin0_128 contact04RanksJoin128_34
theorem contact04_margin : sourceMargin contact04 :=
  margin_of_checked_counts contact04 162 1828077132918269 113678425285044 7061283193 345924093 rfl contact04OrdinaryColumns contact04ColumnsJoin0_162 contact04OrdinaryRanks contact04RanksJoin0_162 (by decide +kernel)

private theorem contact06OrdinaryColumns : ordinaryColumnCount contact06 = 2080040000492531 := by decide +kernel
private theorem contact06ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact06) 0 4 = 7926454943006 :=
  contactColumnsWindow_fast contact06 0 4 7926454943006 (by decide +kernel)
private theorem contact06ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact06) 4 4 = 7546224475294 :=
  contactColumnsWindow_fast contact06 4 4 7546224475294 (by decide +kernel)
private theorem contact06ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact06) 8 4 = 7175378878728 :=
  contactColumnsWindow_fast contact06 8 4 7175378878728 (by decide +kernel)
private theorem contact06ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact06) 12 4 = 6813918397457 :=
  contactColumnsWindow_fast contact06 12 4 6813918397457 (by decide +kernel)
private theorem contact06ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact06) 16 4 = 6461879229966 :=
  contactColumnsWindow_fast contact06 16 4 6461879229966 (by decide +kernel)
private theorem contact06ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact06) 20 4 = 6119246143149 :=
  contactColumnsWindow_fast contact06 20 4 6119246143149 (by decide +kernel)
private theorem contact06ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact06) 24 4 = 5786001746546 :=
  contactColumnsWindow_fast contact06 24 4 5786001746546 (by decide +kernel)
private theorem contact06ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact06) 28 4 = 5462144639309 :=
  contactColumnsWindow_fast contact06 28 4 5462144639309 (by decide +kernel)
private theorem contact06ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact06) 32 4 = 5147677996382 :=
  contactColumnsWindow_fast contact06 32 4 5147677996382 (by decide +kernel)
private theorem contact06ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact06) 36 4 = 4842637424683 :=
  contactColumnsWindow_fast contact06 36 4 4842637424683 (by decide +kernel)
private theorem contact06ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact06) 40 4 = 4547003825753 :=
  contactColumnsWindow_fast contact06 40 4 4547003825753 (by decide +kernel)
private theorem contact06ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact06) 44 4 = 4260760873987 :=
  contactColumnsWindow_fast contact06 44 4 4260760873987 (by decide +kernel)
private theorem contact06ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact06) 48 4 = 3983909880953 :=
  contactColumnsWindow_fast contact06 48 4 3983909880953 (by decide +kernel)
private theorem contact06ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact06) 52 4 = 3716452895117 :=
  contactColumnsWindow_fast contact06 52 4 3716452895117 (by decide +kernel)
private theorem contact06ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact06) 56 4 = 3458429203941 :=
  contactColumnsWindow_fast contact06 56 4 3458429203941 (by decide +kernel)
private theorem contact06ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact06) 60 4 = 3209811867873 :=
  contactColumnsWindow_fast contact06 60 4 3209811867873 (by decide +kernel)
private theorem contact06ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact06) 64 4 = 2970588755255 :=
  contactColumnsWindow_fast contact06 64 4 2970588755255 (by decide +kernel)
private theorem contact06ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact06) 68 4 = 2740757561225 :=
  contactColumnsWindow_fast contact06 68 4 2740757561225 (by decide +kernel)
private theorem contact06ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact06) 72 4 = 2520322837315 :=
  contactColumnsWindow_fast contact06 72 4 2520322837315 (by decide +kernel)
private theorem contact06ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact06) 76 4 = 2309322062237 :=
  contactColumnsWindow_fast contact06 76 4 2309322062237 (by decide +kernel)
private theorem contact06ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact06) 80 4 = 2107725127333 :=
  contactColumnsWindow_fast contact06 80 4 2107725127333 (by decide +kernel)
private theorem contact06ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact06) 84 4 = 1915521897023 :=
  contactColumnsWindow_fast contact06 84 4 1915521897023 (by decide +kernel)
private theorem contact06ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact06) 88 4 = 1732710579947 :=
  contactColumnsWindow_fast contact06 88 4 1732710579947 (by decide +kernel)
private theorem contact06ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact06) 92 4 = 1559298494551 :=
  contactColumnsWindow_fast contact06 92 4 1559298494551 (by decide +kernel)
private theorem contact06ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact06) 96 4 = 1395320170066 :=
  contactColumnsWindow_fast contact06 96 4 1395320170066 (by decide +kernel)
private theorem contact06ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact06) 100 4 = 1240743665984 :=
  contactColumnsWindow_fast contact06 100 4 1240743665984 (by decide +kernel)
private theorem contact06ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact06) 104 4 = 1095560483943 :=
  contactColumnsWindow_fast contact06 104 4 1095560483943 (by decide +kernel)
private theorem contact06ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact06) 108 4 = 959768832894 :=
  contactColumnsWindow_fast contact06 108 4 959768832894 (by decide +kernel)
private theorem contact06ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact06) 112 4 = 833379439329 :=
  contactColumnsWindow_fast contact06 112 4 833379439329 (by decide +kernel)
private theorem contact06ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact06) 116 4 = 716423815845 :=
  contactColumnsWindow_fast contact06 116 4 716423815845 (by decide +kernel)
private theorem contact06ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact06) 120 4 = 608867493101 :=
  contactColumnsWindow_fast contact06 120 4 608867493101 (by decide +kernel)
private theorem contact06ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact06) 124 4 = 510704288203 :=
  contactColumnsWindow_fast contact06 124 4 510704288203 (by decide +kernel)
private theorem contact06ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact06) 128 4 = 421932454021 :=
  contactColumnsWindow_fast contact06 128 4 421932454021 (by decide +kernel)
private theorem contact06ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact06) 132 4 = 342566963884 :=
  contactColumnsWindow_fast contact06 132 4 342566963884 (by decide +kernel)
private theorem contact06ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact06) 136 4 = 272632542211 :=
  contactColumnsWindow_fast contact06 136 4 272632542211 (by decide +kernel)
private theorem contact06ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact06) 140 4 = 212068658566 :=
  contactColumnsWindow_fast contact06 140 4 212068658566 (by decide +kernel)
private theorem contact06ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact06) 144 4 = 160688385334 :=
  contactColumnsWindow_fast contact06 144 4 160688385334 (by decide +kernel)
private theorem contact06ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact06) 148 4 = 118115474406 :=
  contactColumnsWindow_fast contact06 148 4 118115474406 (by decide +kernel)
private theorem contact06ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact06) 152 4 = 83832811336 :=
  contactColumnsWindow_fast contact06 152 4 83832811336 (by decide +kernel)
private theorem contact06ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact06) 156 4 = 57155394203 :=
  contactColumnsWindow_fast contact06 156 4 57155394203 (by decide +kernel)
private theorem contact06ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact06) 160 3 = 29434001588 :=
  contactColumnsWindow_fast contact06 160 3 29434001588 (by decide +kernel)
private theorem contact06ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact06) 0 8 = 15472679418300 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 4 4 7926454943006 7546224475294 contact06ColumnsSlice0 contact06ColumnsSlice4
private theorem contact06ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact06) 8 8 = 13989297276185 :=
  combineSlices (auxiliaryColumnSlice contact06) 8 4 4 7175378878728 6813918397457 contact06ColumnsSlice8 contact06ColumnsSlice12
private theorem contact06ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact06) 16 8 = 12581125373115 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 4 4 6461879229966 6119246143149 contact06ColumnsSlice16 contact06ColumnsSlice20
private theorem contact06ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact06) 24 8 = 11248146385855 :=
  combineSlices (auxiliaryColumnSlice contact06) 24 4 4 5786001746546 5462144639309 contact06ColumnsSlice24 contact06ColumnsSlice28
private theorem contact06ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact06) 32 8 = 9990315421065 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 4 4 5147677996382 4842637424683 contact06ColumnsSlice32 contact06ColumnsSlice36
private theorem contact06ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact06) 40 8 = 8807764699740 :=
  combineSlices (auxiliaryColumnSlice contact06) 40 4 4 4547003825753 4260760873987 contact06ColumnsSlice40 contact06ColumnsSlice44
private theorem contact06ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact06) 48 8 = 7700362776070 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 4 4 3983909880953 3716452895117 contact06ColumnsSlice48 contact06ColumnsSlice52
private theorem contact06ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact06) 56 8 = 6668241071814 :=
  combineSlices (auxiliaryColumnSlice contact06) 56 4 4 3458429203941 3209811867873 contact06ColumnsSlice56 contact06ColumnsSlice60
private theorem contact06ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact06) 64 8 = 5711346316480 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 4 4 2970588755255 2740757561225 contact06ColumnsSlice64 contact06ColumnsSlice68
private theorem contact06ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact06) 72 8 = 4829644899552 :=
  combineSlices (auxiliaryColumnSlice contact06) 72 4 4 2520322837315 2309322062237 contact06ColumnsSlice72 contact06ColumnsSlice76
private theorem contact06ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact06) 80 8 = 4023247024356 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 4 4 2107725127333 1915521897023 contact06ColumnsSlice80 contact06ColumnsSlice84
private theorem contact06ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact06) 88 8 = 3292009074498 :=
  combineSlices (auxiliaryColumnSlice contact06) 88 4 4 1732710579947 1559298494551 contact06ColumnsSlice88 contact06ColumnsSlice92
private theorem contact06ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact06) 96 8 = 2636063836050 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 4 4 1395320170066 1240743665984 contact06ColumnsSlice96 contact06ColumnsSlice100
private theorem contact06ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact06) 104 8 = 2055329316837 :=
  combineSlices (auxiliaryColumnSlice contact06) 104 4 4 1095560483943 959768832894 contact06ColumnsSlice104 contact06ColumnsSlice108
private theorem contact06ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact06) 112 8 = 1549803255174 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 4 4 833379439329 716423815845 contact06ColumnsSlice112 contact06ColumnsSlice116
private theorem contact06ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact06) 120 8 = 1119571781304 :=
  combineSlices (auxiliaryColumnSlice contact06) 120 4 4 608867493101 510704288203 contact06ColumnsSlice120 contact06ColumnsSlice124
private theorem contact06ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact06) 128 8 = 764499417905 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 4 4 421932454021 342566963884 contact06ColumnsSlice128 contact06ColumnsSlice132
private theorem contact06ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact06) 136 8 = 484701200777 :=
  combineSlices (auxiliaryColumnSlice contact06) 136 4 4 272632542211 212068658566 contact06ColumnsSlice136 contact06ColumnsSlice140
private theorem contact06ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact06) 144 8 = 278803859740 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 4 4 160688385334 118115474406 contact06ColumnsSlice144 contact06ColumnsSlice148
private theorem contact06ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact06) 152 8 = 140988205539 :=
  combineSlices (auxiliaryColumnSlice contact06) 152 4 4 83832811336 57155394203 contact06ColumnsSlice152 contact06ColumnsSlice156
private theorem contact06ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact06) 0 16 = 29461976694485 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 8 8 15472679418300 13989297276185 contact06ColumnsJoin0_8 contact06ColumnsJoin8_8
private theorem contact06ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact06) 16 16 = 23829271758970 :=
  combineSlices (auxiliaryColumnSlice contact06) 16 8 8 12581125373115 11248146385855 contact06ColumnsJoin16_8 contact06ColumnsJoin24_8
private theorem contact06ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact06) 32 16 = 18798080120805 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 8 8 9990315421065 8807764699740 contact06ColumnsJoin32_8 contact06ColumnsJoin40_8
private theorem contact06ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact06) 48 16 = 14368603847884 :=
  combineSlices (auxiliaryColumnSlice contact06) 48 8 8 7700362776070 6668241071814 contact06ColumnsJoin48_8 contact06ColumnsJoin56_8
private theorem contact06ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact06) 64 16 = 10540991216032 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 8 8 5711346316480 4829644899552 contact06ColumnsJoin64_8 contact06ColumnsJoin72_8
private theorem contact06ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact06) 80 16 = 7315256098854 :=
  combineSlices (auxiliaryColumnSlice contact06) 80 8 8 4023247024356 3292009074498 contact06ColumnsJoin80_8 contact06ColumnsJoin88_8
private theorem contact06ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact06) 96 16 = 4691393152887 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 8 8 2636063836050 2055329316837 contact06ColumnsJoin96_8 contact06ColumnsJoin104_8
private theorem contact06ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact06) 112 16 = 2669375036478 :=
  combineSlices (auxiliaryColumnSlice contact06) 112 8 8 1549803255174 1119571781304 contact06ColumnsJoin112_8 contact06ColumnsJoin120_8
private theorem contact06ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact06) 128 16 = 1249200618682 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 8 8 764499417905 484701200777 contact06ColumnsJoin128_8 contact06ColumnsJoin136_8
private theorem contact06ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact06) 144 16 = 419792065279 :=
  combineSlices (auxiliaryColumnSlice contact06) 144 8 8 278803859740 140988205539 contact06ColumnsJoin144_8 contact06ColumnsJoin152_8
private theorem contact06ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact06) 0 32 = 53291248453455 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 16 16 29461976694485 23829271758970 contact06ColumnsJoin0_16 contact06ColumnsJoin16_16
private theorem contact06ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact06) 32 32 = 33166683968689 :=
  combineSlices (auxiliaryColumnSlice contact06) 32 16 16 18798080120805 14368603847884 contact06ColumnsJoin32_16 contact06ColumnsJoin48_16
private theorem contact06ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact06) 64 32 = 17856247314886 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 16 16 10540991216032 7315256098854 contact06ColumnsJoin64_16 contact06ColumnsJoin80_16
private theorem contact06ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact06) 96 32 = 7360768189365 :=
  combineSlices (auxiliaryColumnSlice contact06) 96 16 16 4691393152887 2669375036478 contact06ColumnsJoin96_16 contact06ColumnsJoin112_16
private theorem contact06ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact06) 128 32 = 1668992683961 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 16 16 1249200618682 419792065279 contact06ColumnsJoin128_16 contact06ColumnsJoin144_16
private theorem contact06ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact06) 0 64 = 86457932422144 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 32 32 53291248453455 33166683968689 contact06ColumnsJoin0_32 contact06ColumnsJoin32_32
private theorem contact06ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact06) 64 64 = 25217015504251 :=
  combineSlices (auxiliaryColumnSlice contact06) 64 32 32 17856247314886 7360768189365 contact06ColumnsJoin64_32 contact06ColumnsJoin96_32
private theorem contact06ColumnsJoin128_35 : sliceWindow (auxiliaryColumnSlice contact06) 128 35 = 1698426685549 :=
  combineSlices (auxiliaryColumnSlice contact06) 128 32 3 1668992683961 29434001588 contact06ColumnsJoin128_32 contact06ColumnsSlice160
private theorem contact06ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact06) 0 128 = 111674947926395 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 64 64 86457932422144 25217015504251 contact06ColumnsJoin0_64 contact06ColumnsJoin64_64
private theorem contact06ColumnsJoin0_163 : sliceWindow (auxiliaryColumnSlice contact06) 0 163 = 113373374611944 :=
  combineSlices (auxiliaryColumnSlice contact06) 0 128 35 111674947926395 1698426685549 contact06ColumnsJoin0_128 contact06ColumnsJoin128_35
private theorem contact06OrdinaryRanks : ordinaryRankBound contact06 = 8023161826 := by decide +kernel
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
  margin_of_checked_counts contact06 163 2080040000492531 113373374611944 8023161826 344037082 rfl contact06OrdinaryColumns contact06ColumnsJoin0_163 contact06OrdinaryRanks contact06RanksJoin0_163 (by decide +kernel)

private theorem contact08OrdinaryColumns : ordinaryColumnCount contact08 = 2051997769837574 := by decide +kernel
private theorem contact08ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact08) 0 4 = 8338771887204 :=
  contactColumnsWindow_fast contact08 0 4 8338771887204 (by decide +kernel)
private theorem contact08ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact08) 4 4 = 7936599878756 :=
  contactColumnsWindow_fast contact08 4 4 7936599878756 (by decide +kernel)
private theorem contact08ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact08) 8 4 = 7544413678678 :=
  contactColumnsWindow_fast contact08 8 4 7544413678678 (by decide +kernel)
private theorem contact08ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact08) 12 4 = 7162213564703 :=
  contactColumnsWindow_fast contact08 12 4 7162213564703 (by decide +kernel)
private theorem contact08ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact08) 16 4 = 6790038951906 :=
  contactColumnsWindow_fast contact08 16 4 6790038951906 (by decide +kernel)
private theorem contact08ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact08) 20 4 = 6427873186212 :=
  contactColumnsWindow_fast contact08 20 4 6427873186212 (by decide +kernel)
private theorem contact08ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact08) 24 4 = 6075697196214 :=
  contactColumnsWindow_fast contact08 24 4 6075697196214 (by decide +kernel)
private theorem contact08ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact08) 28 4 = 5733509524917 :=
  contactColumnsWindow_fast contact08 28 4 5733509524917 (by decide +kernel)
private theorem contact08ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact08) 32 4 = 5401313551903 :=
  contactColumnsWindow_fast contact08 32 4 5401313551903 (by decide +kernel)
private theorem contact08ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact08) 36 4 = 5079148151001 :=
  contactColumnsWindow_fast contact08 36 4 5079148151001 (by decide +kernel)
private theorem contact08ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact08) 40 4 = 4766992306443 :=
  contactColumnsWindow_fast contact08 40 4 4766992306443 (by decide +kernel)
private theorem contact08ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact08) 44 4 = 4464828259185 :=
  contactColumnsWindow_fast contact08 44 4 4464828259185 (by decide +kernel)
private theorem contact08ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact08) 48 4 = 4172657359423 :=
  contactColumnsWindow_fast contact08 48 4 4172657359423 (by decide +kernel)
private theorem contact08ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact08) 52 4 = 3890481890108 :=
  contactColumnsWindow_fast contact08 52 4 3890481890108 (by decide +kernel)
private theorem contact08ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact08) 56 4 = 3618344605529 :=
  contactColumnsWindow_fast contact08 56 4 3618344605529 (by decide +kernel)
private theorem contact08ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact08) 60 4 = 3356216012757 :=
  contactColumnsWindow_fast contact08 60 4 3356216012757 (by decide +kernel)
private theorem contact08ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact08) 64 4 = 3104082904115 :=
  contactColumnsWindow_fast contact08 64 4 3104082904115 (by decide +kernel)
private theorem contact08ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact08) 68 4 = 2861942902825 :=
  contactColumnsWindow_fast contact08 68 4 2861942902825 (by decide +kernel)
private theorem contact08ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact08) 72 4 = 2629801001614 :=
  contactColumnsWindow_fast contact08 72 4 2629801001614 (by decide +kernel)
private theorem contact08ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact08) 76 4 = 2407698007619 :=
  contactColumnsWindow_fast contact08 76 4 2407698007619 (by decide +kernel)
private theorem contact08ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact08) 80 4 = 2195600935551 :=
  contactColumnsWindow_fast contact08 80 4 2195600935551 (by decide +kernel)
private theorem contact08ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact08) 84 4 = 1993498810293 :=
  contactColumnsWindow_fast contact08 84 4 1993498810293 (by decide +kernel)
private theorem contact08ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact08) 88 4 = 1801389788164 :=
  contactColumnsWindow_fast contact08 88 4 1801389788164 (by decide +kernel)
private theorem contact08ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact08) 92 4 = 1619281866470 :=
  contactColumnsWindow_fast contact08 92 4 1619281866470 (by decide +kernel)
private theorem contact08ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact08) 96 4 = 1447212659339 :=
  contactColumnsWindow_fast contact08 96 4 1447212659339 (by decide +kernel)
private theorem contact08ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact08) 100 4 = 1285147138955 :=
  contactColumnsWindow_fast contact08 100 4 1285147138955 (by decide +kernel)
private theorem contact08ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact08) 104 4 = 1133076169191 :=
  contactColumnsWindow_fast contact08 104 4 1133076169191 (by decide +kernel)
private theorem contact08ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact08) 108 4 = 990997907539 :=
  contactColumnsWindow_fast contact08 108 4 990997907539 (by decide +kernel)
private theorem contact08ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact08) 112 4 = 858924023195 :=
  contactColumnsWindow_fast contact08 112 4 858924023195 (by decide +kernel)
private theorem contact08ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact08) 116 4 = 736888859718 :=
  contactColumnsWindow_fast contact08 116 4 736888859718 (by decide +kernel)
private theorem contact08ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact08) 120 4 = 624854632704 :=
  contactColumnsWindow_fast contact08 120 4 624854632704 (by decide +kernel)
private theorem contact08ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact08) 124 4 = 522814744569 :=
  contactColumnsWindow_fast contact08 124 4 522814744569 (by decide +kernel)
private theorem contact08ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact08) 128 4 = 430767399166 :=
  contactColumnsWindow_fast contact08 128 4 430767399166 (by decide +kernel)
private theorem contact08ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact08) 132 4 = 348728876591 :=
  contactColumnsWindow_fast contact08 132 4 348728876591 (by decide +kernel)
private theorem contact08ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact08) 136 4 = 276722319634 :=
  contactColumnsWindow_fast contact08 136 4 276722319634 (by decide +kernel)
private theorem contact08ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact08) 140 4 = 214628112026 :=
  contactColumnsWindow_fast contact08 140 4 214628112026 (by decide +kernel)
private theorem contact08ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact08) 144 4 = 162160685644 :=
  contactColumnsWindow_fast contact08 144 4 162160685644 (by decide +kernel)
private theorem contact08ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact08) 148 4 = 118867339196 :=
  contactColumnsWindow_fast contact08 148 4 118867339196 (by decide +kernel)
private theorem contact08ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact08) 152 4 = 84154731341 :=
  contactColumnsWindow_fast contact08 152 4 84154731341 (by decide +kernel)
private theorem contact08ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact08) 156 4 = 57260279975 :=
  contactColumnsWindow_fast contact08 156 4 57260279975 (by decide +kernel)
private theorem contact08ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact08) 160 1 = 10937977305 :=
  contactColumnsWindow_fast contact08 160 1 10937977305 (by decide +kernel)
private theorem contact08ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact08) 0 8 = 16275371765960 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 4 4 8338771887204 7936599878756 contact08ColumnsSlice0 contact08ColumnsSlice4
private theorem contact08ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact08) 8 8 = 14706627243381 :=
  combineSlices (auxiliaryColumnSlice contact08) 8 4 4 7544413678678 7162213564703 contact08ColumnsSlice8 contact08ColumnsSlice12
private theorem contact08ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact08) 16 8 = 13217912138118 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 4 4 6790038951906 6427873186212 contact08ColumnsSlice16 contact08ColumnsSlice20
private theorem contact08ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact08) 24 8 = 11809206721131 :=
  combineSlices (auxiliaryColumnSlice contact08) 24 4 4 6075697196214 5733509524917 contact08ColumnsSlice24 contact08ColumnsSlice28
private theorem contact08ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact08) 32 8 = 10480461702904 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 4 4 5401313551903 5079148151001 contact08ColumnsSlice32 contact08ColumnsSlice36
private theorem contact08ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact08) 40 8 = 9231820565628 :=
  combineSlices (auxiliaryColumnSlice contact08) 40 4 4 4766992306443 4464828259185 contact08ColumnsSlice40 contact08ColumnsSlice44
private theorem contact08ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact08) 48 8 = 8063139249531 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 4 4 4172657359423 3890481890108 contact08ColumnsSlice48 contact08ColumnsSlice52
private theorem contact08ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact08) 56 8 = 6974560618286 :=
  combineSlices (auxiliaryColumnSlice contact08) 56 4 4 3618344605529 3356216012757 contact08ColumnsSlice56 contact08ColumnsSlice60
private theorem contact08ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact08) 64 8 = 5966025806940 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 4 4 3104082904115 2861942902825 contact08ColumnsSlice64 contact08ColumnsSlice68
private theorem contact08ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact08) 72 8 = 5037499009233 :=
  combineSlices (auxiliaryColumnSlice contact08) 72 4 4 2629801001614 2407698007619 contact08ColumnsSlice72 contact08ColumnsSlice76
private theorem contact08ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact08) 80 8 = 4189099745844 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 4 4 2195600935551 1993498810293 contact08ColumnsSlice80 contact08ColumnsSlice84
private theorem contact08ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact08) 88 8 = 3420671654634 :=
  combineSlices (auxiliaryColumnSlice contact08) 88 4 4 1801389788164 1619281866470 contact08ColumnsSlice88 contact08ColumnsSlice92
private theorem contact08ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact08) 96 8 = 2732359798294 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 4 4 1447212659339 1285147138955 contact08ColumnsSlice96 contact08ColumnsSlice100
private theorem contact08ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact08) 104 8 = 2124074076730 :=
  combineSlices (auxiliaryColumnSlice contact08) 104 4 4 1133076169191 990997907539 contact08ColumnsSlice104 contact08ColumnsSlice108
private theorem contact08ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact08) 112 8 = 1595812882913 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 4 4 858924023195 736888859718 contact08ColumnsSlice112 contact08ColumnsSlice116
private theorem contact08ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact08) 120 8 = 1147669377273 :=
  combineSlices (auxiliaryColumnSlice contact08) 120 4 4 624854632704 522814744569 contact08ColumnsSlice120 contact08ColumnsSlice124
private theorem contact08ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact08) 128 8 = 779496275757 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 4 4 430767399166 348728876591 contact08ColumnsSlice128 contact08ColumnsSlice132
private theorem contact08ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact08) 136 8 = 491350431660 :=
  combineSlices (auxiliaryColumnSlice contact08) 136 4 4 276722319634 214628112026 contact08ColumnsSlice136 contact08ColumnsSlice140
private theorem contact08ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact08) 144 8 = 281028024840 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 4 4 162160685644 118867339196 contact08ColumnsSlice144 contact08ColumnsSlice148
private theorem contact08ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact08) 152 8 = 141415011316 :=
  combineSlices (auxiliaryColumnSlice contact08) 152 4 4 84154731341 57260279975 contact08ColumnsSlice152 contact08ColumnsSlice156
private theorem contact08ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact08) 0 16 = 30981999009341 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 8 8 16275371765960 14706627243381 contact08ColumnsJoin0_8 contact08ColumnsJoin8_8
private theorem contact08ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact08) 16 16 = 25027118859249 :=
  combineSlices (auxiliaryColumnSlice contact08) 16 8 8 13217912138118 11809206721131 contact08ColumnsJoin16_8 contact08ColumnsJoin24_8
private theorem contact08ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact08) 32 16 = 19712282268532 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 8 8 10480461702904 9231820565628 contact08ColumnsJoin32_8 contact08ColumnsJoin40_8
private theorem contact08ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact08) 48 16 = 15037699867817 :=
  combineSlices (auxiliaryColumnSlice contact08) 48 8 8 8063139249531 6974560618286 contact08ColumnsJoin48_8 contact08ColumnsJoin56_8
private theorem contact08ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact08) 64 16 = 11003524816173 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 8 8 5966025806940 5037499009233 contact08ColumnsJoin64_8 contact08ColumnsJoin72_8
private theorem contact08ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact08) 80 16 = 7609771400478 :=
  combineSlices (auxiliaryColumnSlice contact08) 80 8 8 4189099745844 3420671654634 contact08ColumnsJoin80_8 contact08ColumnsJoin88_8
private theorem contact08ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact08) 96 16 = 4856433875024 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 8 8 2732359798294 2124074076730 contact08ColumnsJoin96_8 contact08ColumnsJoin104_8
private theorem contact08ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact08) 112 16 = 2743482260186 :=
  combineSlices (auxiliaryColumnSlice contact08) 112 8 8 1595812882913 1147669377273 contact08ColumnsJoin112_8 contact08ColumnsJoin120_8
private theorem contact08ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact08) 128 16 = 1270846707417 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 8 8 779496275757 491350431660 contact08ColumnsJoin128_8 contact08ColumnsJoin136_8
private theorem contact08ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact08) 144 16 = 422443036156 :=
  combineSlices (auxiliaryColumnSlice contact08) 144 8 8 281028024840 141415011316 contact08ColumnsJoin144_8 contact08ColumnsJoin152_8
private theorem contact08ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact08) 0 32 = 56009117868590 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 16 16 30981999009341 25027118859249 contact08ColumnsJoin0_16 contact08ColumnsJoin16_16
private theorem contact08ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact08) 32 32 = 34749982136349 :=
  combineSlices (auxiliaryColumnSlice contact08) 32 16 16 19712282268532 15037699867817 contact08ColumnsJoin32_16 contact08ColumnsJoin48_16
private theorem contact08ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact08) 64 32 = 18613296216651 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 16 16 11003524816173 7609771400478 contact08ColumnsJoin64_16 contact08ColumnsJoin80_16
private theorem contact08ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact08) 96 32 = 7599916135210 :=
  combineSlices (auxiliaryColumnSlice contact08) 96 16 16 4856433875024 2743482260186 contact08ColumnsJoin96_16 contact08ColumnsJoin112_16
private theorem contact08ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact08) 128 32 = 1693289743573 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 16 16 1270846707417 422443036156 contact08ColumnsJoin128_16 contact08ColumnsJoin144_16
private theorem contact08ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact08) 0 64 = 90759100004939 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 32 32 56009117868590 34749982136349 contact08ColumnsJoin0_32 contact08ColumnsJoin32_32
private theorem contact08ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact08) 64 64 = 26213212351861 :=
  combineSlices (auxiliaryColumnSlice contact08) 64 32 32 18613296216651 7599916135210 contact08ColumnsJoin64_32 contact08ColumnsJoin96_32
private theorem contact08ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact08) 128 33 = 1704227720878 :=
  combineSlices (auxiliaryColumnSlice contact08) 128 32 1 1693289743573 10937977305 contact08ColumnsJoin128_32 contact08ColumnsSlice160
private theorem contact08ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact08) 0 128 = 116972312356800 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 64 64 90759100004939 26213212351861 contact08ColumnsJoin0_64 contact08ColumnsJoin64_64
private theorem contact08ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact08) 0 161 = 118676540077678 :=
  combineSlices (auxiliaryColumnSlice contact08) 0 128 33 116972312356800 1704227720878 contact08ColumnsJoin0_128 contact08ColumnsJoin128_33
private theorem contact08OrdinaryRanks : ordinaryRankBound contact08 = 7918694982 := by decide +kernel
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
private theorem contact08RanksSlice152 : sliceWindow (auxiliaryRankSlice contact08) 152 9 = 0 :=
  contactRankWindow_of_rec contact08 152 9 0 (by decide +kernel)
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
private theorem contact08RanksJoin144_17 : sliceWindow (auxiliaryRankSlice contact08) 144 17 = 19439 :=
  combineSlices (auxiliaryRankSlice contact08) 144 8 9 19439 0 contact08RanksJoin144_8 contact08RanksSlice152
private theorem contact08RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact08) 0 32 = 200059968 :=
  combineSlices (auxiliaryRankSlice contact08) 0 16 16 114130464 85929504 contact08RanksJoin0_16 contact08RanksJoin16_16
private theorem contact08RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact08) 32 32 = 104940520 :=
  combineSlices (auxiliaryRankSlice contact08) 32 16 16 62152224 42788296 contact08RanksJoin32_16 contact08RanksJoin48_16
private theorem contact08RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact08) 64 32 = 44064098 :=
  combineSlices (auxiliaryRankSlice contact08) 64 16 16 27671826 16392272 contact08RanksJoin64_16 contact08RanksJoin80_16
private theorem contact08RanksJoin96_32 : sliceWindow (auxiliaryRankSlice contact08) 96 32 = 11900728 :=
  combineSlices (auxiliaryRankSlice contact08) 96 16 16 8471654 3429074 contact08RanksJoin96_16 contact08RanksJoin112_16
private theorem contact08RanksJoin128_33 : sliceWindow (auxiliaryRankSlice contact08) 128 33 = 803180 :=
  combineSlices (auxiliaryRankSlice contact08) 128 16 17 783741 19439 contact08RanksJoin128_16 contact08RanksJoin144_17
private theorem contact08RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact08) 0 64 = 305000488 :=
  combineSlices (auxiliaryRankSlice contact08) 0 32 32 200059968 104940520 contact08RanksJoin0_32 contact08RanksJoin32_32
private theorem contact08RanksJoin64_64 : sliceWindow (auxiliaryRankSlice contact08) 64 64 = 55964826 :=
  combineSlices (auxiliaryRankSlice contact08) 64 32 32 44064098 11900728 contact08RanksJoin64_32 contact08RanksJoin96_32
private theorem contact08RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact08) 0 128 = 360965314 :=
  combineSlices (auxiliaryRankSlice contact08) 0 64 64 305000488 55964826 contact08RanksJoin0_64 contact08RanksJoin64_64
private theorem contact08RanksJoin0_161 : sliceWindow (auxiliaryRankSlice contact08) 0 161 = 361768494 :=
  combineSlices (auxiliaryRankSlice contact08) 0 128 33 360965314 803180 contact08RanksJoin0_128 contact08RanksJoin128_33
theorem contact08_margin : sourceMargin contact08 :=
  margin_of_checked_counts contact08 161 2051997769837574 118676540077678 7918694982 361768494 rfl contact08OrdinaryColumns contact08ColumnsJoin0_161 contact08OrdinaryRanks contact08RanksJoin0_161 (by decide +kernel)

private theorem contact10OrdinaryColumns : ordinaryColumnCount contact10 = 3802136874312566 := by decide +kernel
private theorem contact10ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact10) 0 4 = 10383497266296 :=
  contactColumnsWindow_fast contact10 0 4 10383497266296 (by decide +kernel)
private theorem contact10ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact10) 4 4 = 9907118168504 :=
  contactColumnsWindow_fast contact10 4 4 9907118168504 (by decide +kernel)
private theorem contact10ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact10) 8 4 = 9441979113208 :=
  contactColumnsWindow_fast contact10 8 4 9441979113208 (by decide +kernel)
private theorem contact10ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact10) 12 4 = 8988080100408 :=
  contactColumnsWindow_fast contact10 12 4 8988080100408 (by decide +kernel)
private theorem contact10ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact10) 16 4 = 8545421130104 :=
  contactColumnsWindow_fast contact10 16 4 8545421130104 (by decide +kernel)
private theorem contact10ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact10) 20 4 = 8114002202296 :=
  contactColumnsWindow_fast contact10 20 4 8114002202296 (by decide +kernel)
private theorem contact10ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact10) 24 4 = 7693823316984 :=
  contactColumnsWindow_fast contact10 24 4 7693823316984 (by decide +kernel)
private theorem contact10ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact10) 28 4 = 7284917684018 :=
  contactColumnsWindow_fast contact10 28 4 7284917684018 (by decide +kernel)
private theorem contact10ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact10) 32 4 = 6887301703298 :=
  contactColumnsWindow_fast contact10 32 4 6887301703298 (by decide +kernel)
private theorem contact10ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact10) 36 4 = 6500929017608 :=
  contactColumnsWindow_fast contact10 36 4 6500929017608 (by decide +kernel)
private theorem contact10ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact10) 40 4 = 6125799278736 :=
  contactColumnsWindow_fast contact10 40 4 6125799278736 (by decide +kernel)
private theorem contact10ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact10) 44 4 = 5761913654186 :=
  contactColumnsWindow_fast contact10 44 4 5761913654186 (by decide +kernel)
private theorem contact10ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact10) 48 4 = 5409311511440 :=
  contactColumnsWindow_fast contact10 48 4 5409311511440 (by decide +kernel)
private theorem contact10ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact10) 52 4 = 5067995889651 :=
  contactColumnsWindow_fast contact10 52 4 5067995889651 (by decide +kernel)
private theorem contact10ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact10) 56 4 = 4737926331055 :=
  contactColumnsWindow_fast contact10 56 4 4737926331055 (by decide +kernel)
private theorem contact10ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact10) 60 4 = 4419104348969 :=
  contactColumnsWindow_fast contact10 60 4 4419104348969 (by decide +kernel)
private theorem contact10ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact10) 64 4 = 4111528940537 :=
  contactColumnsWindow_fast contact10 64 4 4111528940537 (by decide +kernel)
private theorem contact10ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact10) 68 4 = 3815249740031 :=
  contactColumnsWindow_fast contact10 68 4 3815249740031 (by decide +kernel)
private theorem contact10ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact10) 72 4 = 3530252046765 :=
  contactColumnsWindow_fast contact10 72 4 3530252046765 (by decide +kernel)
private theorem contact10ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact10) 76 4 = 3256505700647 :=
  contactColumnsWindow_fast contact10 76 4 3256505700647 (by decide +kernel)
private theorem contact10ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact10) 80 4 = 2994009483885 :=
  contactColumnsWindow_fast contact10 80 4 2994009483885 (by decide +kernel)
private theorem contact10ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact10) 84 4 = 2742766175175 :=
  contactColumnsWindow_fast contact10 84 4 2742766175175 (by decide +kernel)
private theorem contact10ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact10) 88 4 = 2502824290441 :=
  contactColumnsWindow_fast contact10 88 4 2502824290441 (by decide +kernel)
private theorem contact10ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact10) 92 4 = 2274157709699 :=
  contactColumnsWindow_fast contact10 92 4 2274157709699 (by decide +kernel)
private theorem contact10ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact10) 96 4 = 2056742435961 :=
  contactColumnsWindow_fast contact10 96 4 2056742435961 (by decide +kernel)
private theorem contact10ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact10) 100 4 = 1850577567447 :=
  contactColumnsWindow_fast contact10 100 4 1850577567447 (by decide +kernel)
private theorem contact10ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact10) 104 4 = 1655667263169 :=
  contactColumnsWindow_fast contact10 104 4 1655667263169 (by decide +kernel)
private theorem contact10ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact10) 108 4 = 1472061840147 :=
  contactColumnsWindow_fast contact10 108 4 1472061840147 (by decide +kernel)
private theorem contact10ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact10) 112 4 = 1299726442677 :=
  contactColumnsWindow_fast contact10 112 4 1299726442677 (by decide +kernel)
private theorem contact10ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact10) 116 4 = 1138642319818 :=
  contactColumnsWindow_fast contact10 116 4 1138642319818 (by decide +kernel)
private theorem contact10ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact10) 120 4 = 988808765841 :=
  contactColumnsWindow_fast contact10 120 4 988808765841 (by decide +kernel)
private theorem contact10ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact10) 124 4 = 850231350459 :=
  contactColumnsWindow_fast contact10 124 4 850231350459 (by decide +kernel)
private theorem contact10ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact10) 128 4 = 722962470523 :=
  contactColumnsWindow_fast contact10 128 4 722962470523 (by decide +kernel)
private theorem contact10ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact10) 132 4 = 606958415319 :=
  contactColumnsWindow_fast contact10 132 4 606958415319 (by decide +kernel)
private theorem contact10ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact10) 136 4 = 502205211791 :=
  contactColumnsWindow_fast contact10 136 4 502205211791 (by decide +kernel)
private theorem contact10ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact10) 140 4 = 408702954847 :=
  contactColumnsWindow_fast contact10 140 4 408702954847 (by decide +kernel)
private theorem contact10ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact10) 144 4 = 326445659765 :=
  contactColumnsWindow_fast contact10 144 4 326445659765 (by decide +kernel)
private theorem contact10ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact10) 148 4 = 255341587410 :=
  contactColumnsWindow_fast contact10 148 4 255341587410 (by decide +kernel)
private theorem contact10ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact10) 152 4 = 194997561121 :=
  contactColumnsWindow_fast contact10 152 4 194997561121 (by decide +kernel)
private theorem contact10ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact10) 156 4 = 144885390247 :=
  contactColumnsWindow_fast contact10 156 4 144885390247 (by decide +kernel)
private theorem contact10ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact10) 160 4 = 104326181735 :=
  contactColumnsWindow_fast contact10 160 4 104326181735 (by decide +kernel)
private theorem contact10ColumnsSlice164 : sliceWindow (auxiliaryColumnSlice contact10) 164 4 = 72487542341 :=
  contactColumnsWindow_fast contact10 164 4 72487542341 (by decide +kernel)
private theorem contact10ColumnsSlice168 : sliceWindow (auxiliaryColumnSlice contact10) 168 4 = 48389998906 :=
  contactColumnsWindow_fast contact10 168 4 48389998906 (by decide +kernel)
private theorem contact10ColumnsSlice172 : sliceWindow (auxiliaryColumnSlice contact10) 172 3 = 24459474314 :=
  contactColumnsWindow_fast contact10 172 3 24459474314 (by decide +kernel)
private theorem contact10ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact10) 0 8 = 20290615434800 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 4 4 10383497266296 9907118168504 contact10ColumnsSlice0 contact10ColumnsSlice4
private theorem contact10ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact10) 8 8 = 18430059213616 :=
  combineSlices (auxiliaryColumnSlice contact10) 8 4 4 9441979113208 8988080100408 contact10ColumnsSlice8 contact10ColumnsSlice12
private theorem contact10ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact10) 16 8 = 16659423332400 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 4 4 8545421130104 8114002202296 contact10ColumnsSlice16 contact10ColumnsSlice20
private theorem contact10ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact10) 24 8 = 14978741001002 :=
  combineSlices (auxiliaryColumnSlice contact10) 24 4 4 7693823316984 7284917684018 contact10ColumnsSlice24 contact10ColumnsSlice28
private theorem contact10ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact10) 32 8 = 13388230720906 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 4 4 6887301703298 6500929017608 contact10ColumnsSlice32 contact10ColumnsSlice36
private theorem contact10ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact10) 40 8 = 11887712932922 :=
  combineSlices (auxiliaryColumnSlice contact10) 40 4 4 6125799278736 5761913654186 contact10ColumnsSlice40 contact10ColumnsSlice44
private theorem contact10ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact10) 48 8 = 10477307401091 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 4 4 5409311511440 5067995889651 contact10ColumnsSlice48 contact10ColumnsSlice52
private theorem contact10ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact10) 56 8 = 9157030680024 :=
  combineSlices (auxiliaryColumnSlice contact10) 56 4 4 4737926331055 4419104348969 contact10ColumnsSlice56 contact10ColumnsSlice60
private theorem contact10ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact10) 64 8 = 7926778680568 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 4 4 4111528940537 3815249740031 contact10ColumnsSlice64 contact10ColumnsSlice68
private theorem contact10ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact10) 72 8 = 6786757747412 :=
  combineSlices (auxiliaryColumnSlice contact10) 72 4 4 3530252046765 3256505700647 contact10ColumnsSlice72 contact10ColumnsSlice76
private theorem contact10ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact10) 80 8 = 5736775659060 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 4 4 2994009483885 2742766175175 contact10ColumnsSlice80 contact10ColumnsSlice84
private theorem contact10ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact10) 88 8 = 4776982000140 :=
  combineSlices (auxiliaryColumnSlice contact10) 88 4 4 2502824290441 2274157709699 contact10ColumnsSlice88 contact10ColumnsSlice92
private theorem contact10ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact10) 96 8 = 3907320003408 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 4 4 2056742435961 1850577567447 contact10ColumnsSlice96 contact10ColumnsSlice100
private theorem contact10ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact10) 104 8 = 3127729103316 :=
  combineSlices (auxiliaryColumnSlice contact10) 104 4 4 1655667263169 1472061840147 contact10ColumnsSlice104 contact10ColumnsSlice108
private theorem contact10ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact10) 112 8 = 2438368762495 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 4 4 1299726442677 1138642319818 contact10ColumnsSlice112 contact10ColumnsSlice116
private theorem contact10ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact10) 120 8 = 1839040116300 :=
  combineSlices (auxiliaryColumnSlice contact10) 120 4 4 988808765841 850231350459 contact10ColumnsSlice120 contact10ColumnsSlice124
private theorem contact10ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact10) 128 8 = 1329920885842 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 4 4 722962470523 606958415319 contact10ColumnsSlice128 contact10ColumnsSlice132
private theorem contact10ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact10) 136 8 = 910908166638 :=
  combineSlices (auxiliaryColumnSlice contact10) 136 4 4 502205211791 408702954847 contact10ColumnsSlice136 contact10ColumnsSlice140
private theorem contact10ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact10) 144 8 = 581787247175 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 4 4 326445659765 255341587410 contact10ColumnsSlice144 contact10ColumnsSlice148
private theorem contact10ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact10) 152 8 = 339882951368 :=
  combineSlices (auxiliaryColumnSlice contact10) 152 4 4 194997561121 144885390247 contact10ColumnsSlice152 contact10ColumnsSlice156
private theorem contact10ColumnsJoin160_8 : sliceWindow (auxiliaryColumnSlice contact10) 160 8 = 176813724076 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 4 4 104326181735 72487542341 contact10ColumnsSlice160 contact10ColumnsSlice164
private theorem contact10ColumnsJoin168_7 : sliceWindow (auxiliaryColumnSlice contact10) 168 7 = 72849473220 :=
  combineSlices (auxiliaryColumnSlice contact10) 168 4 3 48389998906 24459474314 contact10ColumnsSlice168 contact10ColumnsSlice172
private theorem contact10ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact10) 0 16 = 38720674648416 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 8 8 20290615434800 18430059213616 contact10ColumnsJoin0_8 contact10ColumnsJoin8_8
private theorem contact10ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact10) 16 16 = 31638164333402 :=
  combineSlices (auxiliaryColumnSlice contact10) 16 8 8 16659423332400 14978741001002 contact10ColumnsJoin16_8 contact10ColumnsJoin24_8
private theorem contact10ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact10) 32 16 = 25275943653828 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 8 8 13388230720906 11887712932922 contact10ColumnsJoin32_8 contact10ColumnsJoin40_8
private theorem contact10ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact10) 48 16 = 19634338081115 :=
  combineSlices (auxiliaryColumnSlice contact10) 48 8 8 10477307401091 9157030680024 contact10ColumnsJoin48_8 contact10ColumnsJoin56_8
private theorem contact10ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact10) 64 16 = 14713536427980 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 8 8 7926778680568 6786757747412 contact10ColumnsJoin64_8 contact10ColumnsJoin72_8
private theorem contact10ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact10) 80 16 = 10513757659200 :=
  combineSlices (auxiliaryColumnSlice contact10) 80 8 8 5736775659060 4776982000140 contact10ColumnsJoin80_8 contact10ColumnsJoin88_8
private theorem contact10ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact10) 96 16 = 7035049106724 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 8 8 3907320003408 3127729103316 contact10ColumnsJoin96_8 contact10ColumnsJoin104_8
private theorem contact10ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact10) 112 16 = 4277408878795 :=
  combineSlices (auxiliaryColumnSlice contact10) 112 8 8 2438368762495 1839040116300 contact10ColumnsJoin112_8 contact10ColumnsJoin120_8
private theorem contact10ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact10) 128 16 = 2240829052480 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 8 8 1329920885842 910908166638 contact10ColumnsJoin128_8 contact10ColumnsJoin136_8
private theorem contact10ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact10) 144 16 = 921670198543 :=
  combineSlices (auxiliaryColumnSlice contact10) 144 8 8 581787247175 339882951368 contact10ColumnsJoin144_8 contact10ColumnsJoin152_8
private theorem contact10ColumnsJoin160_15 : sliceWindow (auxiliaryColumnSlice contact10) 160 15 = 249663197296 :=
  combineSlices (auxiliaryColumnSlice contact10) 160 8 7 176813724076 72849473220 contact10ColumnsJoin160_8 contact10ColumnsJoin168_7
private theorem contact10ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact10) 0 32 = 70358838981818 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 16 16 38720674648416 31638164333402 contact10ColumnsJoin0_16 contact10ColumnsJoin16_16
private theorem contact10ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact10) 32 32 = 44910281734943 :=
  combineSlices (auxiliaryColumnSlice contact10) 32 16 16 25275943653828 19634338081115 contact10ColumnsJoin32_16 contact10ColumnsJoin48_16
private theorem contact10ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact10) 64 32 = 25227294087180 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 16 16 14713536427980 10513757659200 contact10ColumnsJoin64_16 contact10ColumnsJoin80_16
private theorem contact10ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact10) 96 32 = 11312457985519 :=
  combineSlices (auxiliaryColumnSlice contact10) 96 16 16 7035049106724 4277408878795 contact10ColumnsJoin96_16 contact10ColumnsJoin112_16
private theorem contact10ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact10) 128 32 = 3162499251023 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 16 16 2240829052480 921670198543 contact10ColumnsJoin128_16 contact10ColumnsJoin144_16
private theorem contact10ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact10) 0 64 = 115269120716761 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 32 32 70358838981818 44910281734943 contact10ColumnsJoin0_32 contact10ColumnsJoin32_32
private theorem contact10ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact10) 64 64 = 36539752072699 :=
  combineSlices (auxiliaryColumnSlice contact10) 64 32 32 25227294087180 11312457985519 contact10ColumnsJoin64_32 contact10ColumnsJoin96_32
private theorem contact10ColumnsJoin128_47 : sliceWindow (auxiliaryColumnSlice contact10) 128 47 = 3412162448319 :=
  combineSlices (auxiliaryColumnSlice contact10) 128 32 15 3162499251023 249663197296 contact10ColumnsJoin128_32 contact10ColumnsJoin160_15
private theorem contact10ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact10) 0 128 = 151808872789460 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 64 64 115269120716761 36539752072699 contact10ColumnsJoin0_64 contact10ColumnsJoin64_64
private theorem contact10ColumnsJoin0_175 : sliceWindow (auxiliaryColumnSlice contact10) 0 175 = 155221035237779 :=
  combineSlices (auxiliaryColumnSlice contact10) 0 128 47 151808872789460 3412162448319 contact10ColumnsJoin0_128 contact10ColumnsJoin128_47
private theorem contact10OrdinaryRanks : ordinaryRankBound contact10 = 14621890288 := by decide +kernel
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
private theorem contact10RanksSlice160 : sliceWindow (auxiliaryRankSlice contact10) 160 15 = 0 :=
  contactRankWindow_of_rec contact10 160 15 0 (by decide +kernel)
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
private theorem contact10RanksJoin128_47 : sliceWindow (auxiliaryRankSlice contact10) 128 47 = 2284692 :=
  combineSlices (auxiliaryRankSlice contact10) 128 32 15 2284692 0 contact10RanksJoin128_32 contact10RanksSlice160
private theorem contact10RanksJoin0_128 : sliceWindow (auxiliaryRankSlice contact10) 0 128 = 471943378 :=
  combineSlices (auxiliaryRankSlice contact10) 0 64 64 390249686 81693692 contact10RanksJoin0_64 contact10RanksJoin64_64
private theorem contact10RanksJoin0_175 : sliceWindow (auxiliaryRankSlice contact10) 0 175 = 474228070 :=
  combineSlices (auxiliaryRankSlice contact10) 0 128 47 471943378 2284692 contact10RanksJoin0_128 contact10RanksJoin128_47
theorem contact10_margin : sourceMargin contact10 :=
  margin_of_checked_counts contact10 175 3802136874312566 155221035237779 14621890288 474228070 rfl contact10OrdinaryColumns contact10ColumnsJoin0_175 contact10OrdinaryRanks contact10RanksJoin0_175 (by decide +kernel)

private theorem contact12OrdinaryColumns : ordinaryColumnCount contact12 = 178875183008795 := by decide +kernel
private theorem contact12ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact12) 0 4 = 1141105474798 :=
  contactColumnsWindow_fast contact12 0 4 1141105474798 (by decide +kernel)
private theorem contact12ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact12) 4 4 = 1049362661374 :=
  contactColumnsWindow_fast contact12 4 4 1049362661374 (by decide +kernel)
private theorem contact12ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact12) 8 4 = 961487492508 :=
  contactColumnsWindow_fast contact12 8 4 961487492508 (by decide +kernel)
private theorem contact12ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact12) 12 4 = 877478825294 :=
  contactColumnsWindow_fast contact12 12 4 877478825294 (by decide +kernel)
private theorem contact12ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact12) 16 4 = 797335489195 :=
  contactColumnsWindow_fast contact12 16 4 797335489195 (by decide +kernel)
private theorem contact12ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact12) 20 4 = 721065558254 :=
  contactColumnsWindow_fast contact12 20 4 721065558254 (by decide +kernel)
private theorem contact12ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact12) 24 4 = 648685176006 :=
  contactColumnsWindow_fast contact12 24 4 648685176006 (by decide +kernel)
private theorem contact12ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact12) 28 4 = 580173770304 :=
  contactColumnsWindow_fast contact12 28 4 580173770304 (by decide +kernel)
private theorem contact12ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact12) 32 4 = 515528685606 :=
  contactColumnsWindow_fast contact12 32 4 515528685606 (by decide +kernel)
private theorem contact12ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact12) 36 4 = 454749182198 :=
  contactColumnsWindow_fast contact12 36 4 454749182198 (by decide +kernel)
private theorem contact12ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact12) 40 4 = 397845072526 :=
  contactColumnsWindow_fast contact12 40 4 397845072526 (by decide +kernel)
private theorem contact12ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact12) 44 4 = 344829346646 :=
  contactColumnsWindow_fast contact12 44 4 344829346646 (by decide +kernel)
private theorem contact12ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact12) 48 4 = 295681718454 :=
  contactColumnsWindow_fast contact12 48 4 295681718454 (by decide +kernel)
private theorem contact12ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact12) 52 4 = 250400201926 :=
  contactColumnsWindow_fast contact12 52 4 250400201926 (by decide +kernel)
private theorem contact12ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact12) 56 4 = 208984572078 :=
  contactColumnsWindow_fast contact12 56 4 208984572078 (by decide +kernel)
private theorem contact12ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact12) 60 4 = 171446275106 :=
  contactColumnsWindow_fast contact12 60 4 171446275106 (by decide +kernel)
private theorem contact12ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact12) 64 4 = 137795173294 :=
  contactColumnsWindow_fast contact12 64 4 137795173294 (by decide +kernel)
private theorem contact12ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact12) 68 4 = 108011398590 :=
  contactColumnsWindow_fast contact12 68 4 108011398590 (by decide +kernel)
private theorem contact12ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact12) 72 4 = 82093374254 :=
  contactColumnsWindow_fast contact12 72 4 82093374254 (by decide +kernel)
private theorem contact12ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact12) 76 4 = 60041617966 :=
  contactColumnsWindow_fast contact12 76 4 60041617966 (by decide +kernel)
private theorem contact12ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact12) 80 4 = 41868635530 :=
  contactColumnsWindow_fast contact12 80 4 41868635530 (by decide +kernel)
private theorem contact12ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact12) 84 4 = 27533131280 :=
  contactColumnsWindow_fast contact12 84 4 27533131280 (by decide +kernel)
private theorem contact12ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact12) 88 4 = 16819944264 :=
  contactColumnsWindow_fast contact12 88 4 16819944264 (by decide +kernel)
private theorem contact12ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact12) 92 4 = 9362902943 :=
  contactColumnsWindow_fast contact12 92 4 9362902943 (by decide +kernel)
private theorem contact12ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact12) 96 2 = 2763316429 :=
  contactColumnsWindow_fast contact12 96 2 2763316429 (by decide +kernel)
private theorem contact12ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact12) 0 8 = 2190468136172 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 4 4 1141105474798 1049362661374 contact12ColumnsSlice0 contact12ColumnsSlice4
private theorem contact12ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact12) 8 8 = 1838966317802 :=
  combineSlices (auxiliaryColumnSlice contact12) 8 4 4 961487492508 877478825294 contact12ColumnsSlice8 contact12ColumnsSlice12
private theorem contact12ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact12) 16 8 = 1518401047449 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 4 4 797335489195 721065558254 contact12ColumnsSlice16 contact12ColumnsSlice20
private theorem contact12ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact12) 24 8 = 1228858946310 :=
  combineSlices (auxiliaryColumnSlice contact12) 24 4 4 648685176006 580173770304 contact12ColumnsSlice24 contact12ColumnsSlice28
private theorem contact12ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact12) 32 8 = 970277867804 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 4 4 515528685606 454749182198 contact12ColumnsSlice32 contact12ColumnsSlice36
private theorem contact12ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact12) 40 8 = 742674419172 :=
  combineSlices (auxiliaryColumnSlice contact12) 40 4 4 397845072526 344829346646 contact12ColumnsSlice40 contact12ColumnsSlice44
private theorem contact12ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact12) 48 8 = 546081920380 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 4 4 295681718454 250400201926 contact12ColumnsSlice48 contact12ColumnsSlice52
private theorem contact12ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact12) 56 8 = 380430847184 :=
  combineSlices (auxiliaryColumnSlice contact12) 56 4 4 208984572078 171446275106 contact12ColumnsSlice56 contact12ColumnsSlice60
private theorem contact12ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact12) 64 8 = 245806571884 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 4 4 137795173294 108011398590 contact12ColumnsSlice64 contact12ColumnsSlice68
private theorem contact12ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact12) 72 8 = 142134992220 :=
  combineSlices (auxiliaryColumnSlice contact12) 72 4 4 82093374254 60041617966 contact12ColumnsSlice72 contact12ColumnsSlice76
private theorem contact12ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact12) 80 8 = 69401766810 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 4 4 41868635530 27533131280 contact12ColumnsSlice80 contact12ColumnsSlice84
private theorem contact12ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact12) 88 8 = 26182847207 :=
  combineSlices (auxiliaryColumnSlice contact12) 88 4 4 16819944264 9362902943 contact12ColumnsSlice88 contact12ColumnsSlice92
private theorem contact12ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact12) 0 16 = 4029434453974 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 8 8 2190468136172 1838966317802 contact12ColumnsJoin0_8 contact12ColumnsJoin8_8
private theorem contact12ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact12) 16 16 = 2747259993759 :=
  combineSlices (auxiliaryColumnSlice contact12) 16 8 8 1518401047449 1228858946310 contact12ColumnsJoin16_8 contact12ColumnsJoin24_8
private theorem contact12ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact12) 32 16 = 1712952286976 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 8 8 970277867804 742674419172 contact12ColumnsJoin32_8 contact12ColumnsJoin40_8
private theorem contact12ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact12) 48 16 = 926512767564 :=
  combineSlices (auxiliaryColumnSlice contact12) 48 8 8 546081920380 380430847184 contact12ColumnsJoin48_8 contact12ColumnsJoin56_8
private theorem contact12ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact12) 64 16 = 387941564104 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 8 8 245806571884 142134992220 contact12ColumnsJoin64_8 contact12ColumnsJoin72_8
private theorem contact12ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact12) 80 16 = 95584614017 :=
  combineSlices (auxiliaryColumnSlice contact12) 80 8 8 69401766810 26182847207 contact12ColumnsJoin80_8 contact12ColumnsJoin88_8
private theorem contact12ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact12) 0 32 = 6776694447733 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 16 16 4029434453974 2747259993759 contact12ColumnsJoin0_16 contact12ColumnsJoin16_16
private theorem contact12ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact12) 32 32 = 2639465054540 :=
  combineSlices (auxiliaryColumnSlice contact12) 32 16 16 1712952286976 926512767564 contact12ColumnsJoin32_16 contact12ColumnsJoin48_16
private theorem contact12ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact12) 64 32 = 483526178121 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 16 16 387941564104 95584614017 contact12ColumnsJoin64_16 contact12ColumnsJoin80_16
private theorem contact12ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact12) 0 64 = 9416159502273 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 32 32 6776694447733 2639465054540 contact12ColumnsJoin0_32 contact12ColumnsJoin32_32
private theorem contact12ColumnsJoin64_34 : sliceWindow (auxiliaryColumnSlice contact12) 64 34 = 486289494550 :=
  combineSlices (auxiliaryColumnSlice contact12) 64 32 2 483526178121 2763316429 contact12ColumnsJoin64_32 contact12ColumnsSlice96
private theorem contact12ColumnsJoin0_98 : sliceWindow (auxiliaryColumnSlice contact12) 0 98 = 9902448996823 :=
  combineSlices (auxiliaryColumnSlice contact12) 0 64 34 9416159502273 486289494550 contact12ColumnsJoin0_64 contact12ColumnsJoin64_34
private theorem contact12OrdinaryRanks : ordinaryRankBound contact12 = 689849402 := by decide +kernel
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
  margin_of_checked_counts contact12 98 178875183008795 9902448996823 689849402 30278967 rfl contact12OrdinaryColumns contact12ColumnsJoin0_98 contact12OrdinaryRanks contact12RanksJoin0_98 (by decide +kernel)

private theorem contact14OrdinaryColumns : ordinaryColumnCount contact14 = 193242144424996 := by decide +kernel
private theorem contact14ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact14) 0 4 = 950147195860 :=
  contactColumnsWindow_fast contact14 0 4 950147195860 (by decide +kernel)
private theorem contact14ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact14) 4 4 = 872758268658 :=
  contactColumnsWindow_fast contact14 4 4 872758268658 (by decide +kernel)
private theorem contact14ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact14) 8 4 = 798689452544 :=
  contactColumnsWindow_fast contact14 8 4 798689452544 (by decide +kernel)
private theorem contact14ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact14) 12 4 = 727925786853 :=
  contactColumnsWindow_fast contact14 12 4 727925786853 (by decide +kernel)
private theorem contact14ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact14) 16 4 = 660464679838 :=
  contactColumnsWindow_fast contact14 16 4 660464679838 (by decide +kernel)
private theorem contact14ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact14) 20 4 = 596304682157 :=
  contactColumnsWindow_fast contact14 20 4 596304682157 (by decide +kernel)
private theorem contact14ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact14) 24 4 = 535450587006 :=
  contactColumnsWindow_fast contact14 24 4 535450587006 (by decide +kernel)
private theorem contact14ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact14) 28 4 = 477918049285 :=
  contactColumnsWindow_fast contact14 28 4 477918049285 (by decide +kernel)
private theorem contact14ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact14) 32 4 = 423692190504 :=
  contactColumnsWindow_fast contact14 32 4 423692190504 (by decide +kernel)
private theorem contact14ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact14) 36 4 = 372768968476 :=
  contactColumnsWindow_fast contact14 36 4 372768968476 (by decide +kernel)
private theorem contact14ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact14) 40 4 = 325146953648 :=
  contactColumnsWindow_fast contact14 40 4 325146953648 (by decide +kernel)
private theorem contact14ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact14) 44 4 = 280831930256 :=
  contactColumnsWindow_fast contact14 44 4 280831930256 (by decide +kernel)
private theorem contact14ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact14) 48 4 = 239838669704 :=
  contactColumnsWindow_fast contact14 48 4 239838669704 (by decide +kernel)
private theorem contact14ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact14) 52 4 = 202150856451 :=
  contactColumnsWindow_fast contact14 52 4 202150856451 (by decide +kernel)
private theorem contact14ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact14) 56 4 = 167765437006 :=
  contactColumnsWindow_fast contact14 56 4 167765437006 (by decide +kernel)
private theorem contact14ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact14) 60 4 = 136681405031 :=
  contactColumnsWindow_fast contact14 60 4 136681405031 (by decide +kernel)
private theorem contact14ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact14) 64 4 = 108905820891 :=
  contactColumnsWindow_fast contact14 64 4 108905820891 (by decide +kernel)
private theorem contact14ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact14) 68 4 = 84451548122 :=
  contactColumnsWindow_fast contact14 68 4 84451548122 (by decide +kernel)
private theorem contact14ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact14) 72 4 = 63301702668 :=
  contactColumnsWindow_fast contact14 72 4 63301702668 (by decide +kernel)
private theorem contact14ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact14) 76 4 = 45454085428 :=
  contactColumnsWindow_fast contact14 76 4 45454085428 (by decide +kernel)
private theorem contact14ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact14) 80 4 = 30907281395 :=
  contactColumnsWindow_fast contact14 80 4 30907281395 (by decide +kernel)
private theorem contact14ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact14) 84 4 = 19629574542 :=
  contactColumnsWindow_fast contact14 84 4 19629574542 (by decide +kernel)
private theorem contact14ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact14) 88 4 = 11443195456 :=
  contactColumnsWindow_fast contact14 88 4 11443195456 (by decide +kernel)
private theorem contact14ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact14) 92 4 = 5974478410 :=
  contactColumnsWindow_fast contact14 92 4 5974478410 (by decide +kernel)
private theorem contact14ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact14) 96 1 = 910432502 :=
  contactColumnsWindow_fast contact14 96 1 910432502 (by decide +kernel)
private theorem contact14ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact14) 0 8 = 1822905464518 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 4 4 950147195860 872758268658 contact14ColumnsSlice0 contact14ColumnsSlice4
private theorem contact14ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact14) 8 8 = 1526615239397 :=
  combineSlices (auxiliaryColumnSlice contact14) 8 4 4 798689452544 727925786853 contact14ColumnsSlice8 contact14ColumnsSlice12
private theorem contact14ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact14) 16 8 = 1256769361995 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 4 4 660464679838 596304682157 contact14ColumnsSlice16 contact14ColumnsSlice20
private theorem contact14ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact14) 24 8 = 1013368636291 :=
  combineSlices (auxiliaryColumnSlice contact14) 24 4 4 535450587006 477918049285 contact14ColumnsSlice24 contact14ColumnsSlice28
private theorem contact14ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact14) 32 8 = 796461158980 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 4 4 423692190504 372768968476 contact14ColumnsSlice32 contact14ColumnsSlice36
private theorem contact14ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact14) 40 8 = 605978883904 :=
  combineSlices (auxiliaryColumnSlice contact14) 40 4 4 325146953648 280831930256 contact14ColumnsSlice40 contact14ColumnsSlice44
private theorem contact14ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact14) 48 8 = 441989526155 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 4 4 239838669704 202150856451 contact14ColumnsSlice48 contact14ColumnsSlice52
private theorem contact14ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact14) 56 8 = 304446842037 :=
  combineSlices (auxiliaryColumnSlice contact14) 56 4 4 167765437006 136681405031 contact14ColumnsSlice56 contact14ColumnsSlice60
private theorem contact14ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact14) 64 8 = 193357369013 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 4 4 108905820891 84451548122 contact14ColumnsSlice64 contact14ColumnsSlice68
private theorem contact14ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact14) 72 8 = 108755788096 :=
  combineSlices (auxiliaryColumnSlice contact14) 72 4 4 63301702668 45454085428 contact14ColumnsSlice72 contact14ColumnsSlice76
private theorem contact14ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact14) 80 8 = 50536855937 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 4 4 30907281395 19629574542 contact14ColumnsSlice80 contact14ColumnsSlice84
private theorem contact14ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact14) 88 8 = 17417673866 :=
  combineSlices (auxiliaryColumnSlice contact14) 88 4 4 11443195456 5974478410 contact14ColumnsSlice88 contact14ColumnsSlice92
private theorem contact14ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact14) 0 16 = 3349520703915 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 8 8 1822905464518 1526615239397 contact14ColumnsJoin0_8 contact14ColumnsJoin8_8
private theorem contact14ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact14) 16 16 = 2270137998286 :=
  combineSlices (auxiliaryColumnSlice contact14) 16 8 8 1256769361995 1013368636291 contact14ColumnsJoin16_8 contact14ColumnsJoin24_8
private theorem contact14ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact14) 32 16 = 1402440042884 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 8 8 796461158980 605978883904 contact14ColumnsJoin32_8 contact14ColumnsJoin40_8
private theorem contact14ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact14) 48 16 = 746436368192 :=
  combineSlices (auxiliaryColumnSlice contact14) 48 8 8 441989526155 304446842037 contact14ColumnsJoin48_8 contact14ColumnsJoin56_8
private theorem contact14ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact14) 64 16 = 302113157109 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 8 8 193357369013 108755788096 contact14ColumnsJoin64_8 contact14ColumnsJoin72_8
private theorem contact14ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact14) 80 16 = 67954529803 :=
  combineSlices (auxiliaryColumnSlice contact14) 80 8 8 50536855937 17417673866 contact14ColumnsJoin80_8 contact14ColumnsJoin88_8
private theorem contact14ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact14) 0 32 = 5619658702201 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 16 16 3349520703915 2270137998286 contact14ColumnsJoin0_16 contact14ColumnsJoin16_16
private theorem contact14ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact14) 32 32 = 2148876411076 :=
  combineSlices (auxiliaryColumnSlice contact14) 32 16 16 1402440042884 746436368192 contact14ColumnsJoin32_16 contact14ColumnsJoin48_16
private theorem contact14ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact14) 64 32 = 370067686912 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 16 16 302113157109 67954529803 contact14ColumnsJoin64_16 contact14ColumnsJoin80_16
private theorem contact14ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact14) 0 64 = 7768535113277 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 32 32 5619658702201 2148876411076 contact14ColumnsJoin0_32 contact14ColumnsJoin32_32
private theorem contact14ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact14) 64 33 = 370978119414 :=
  combineSlices (auxiliaryColumnSlice contact14) 64 32 1 370067686912 910432502 contact14ColumnsJoin64_32 contact14ColumnsSlice96
private theorem contact14ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact14) 0 97 = 8139513232691 :=
  combineSlices (auxiliaryColumnSlice contact14) 0 64 33 7768535113277 370978119414 contact14ColumnsJoin0_64 contact14ColumnsJoin64_33
private theorem contact14OrdinaryRanks : ordinaryRankBound contact14 = 743512319 := by decide +kernel
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
private theorem contact14RanksSlice88 : sliceWindow (auxiliaryRankSlice contact14) 88 9 = 0 :=
  contactRankWindow_of_rec contact14 88 9 0 (by decide +kernel)
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
private theorem contact14RanksJoin80_17 : sliceWindow (auxiliaryRankSlice contact14) 80 17 = 14838 :=
  combineSlices (auxiliaryRankSlice contact14) 80 8 9 14838 0 contact14RanksJoin80_8 contact14RanksSlice88
private theorem contact14RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact14) 0 32 = 19200432 :=
  combineSlices (auxiliaryRankSlice contact14) 0 16 16 12067800 7132632 contact14RanksJoin0_16 contact14RanksJoin16_16
private theorem contact14RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact14) 32 32 = 5122686 :=
  combineSlices (auxiliaryRankSlice contact14) 32 16 16 3646840 1475846 contact14RanksJoin32_16 contact14RanksJoin48_16
private theorem contact14RanksJoin64_33 : sliceWindow (auxiliaryRankSlice contact14) 64 33 = 374229 :=
  combineSlices (auxiliaryRankSlice contact14) 64 16 17 359391 14838 contact14RanksJoin64_16 contact14RanksJoin80_17
private theorem contact14RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact14) 0 64 = 24323118 :=
  combineSlices (auxiliaryRankSlice contact14) 0 32 32 19200432 5122686 contact14RanksJoin0_32 contact14RanksJoin32_32
private theorem contact14RanksJoin0_97 : sliceWindow (auxiliaryRankSlice contact14) 0 97 = 24697347 :=
  combineSlices (auxiliaryRankSlice contact14) 0 64 33 24323118 374229 contact14RanksJoin0_64 contact14RanksJoin64_33
theorem contact14_margin : sourceMargin contact14 :=
  margin_of_checked_counts contact14 97 193242144424996 8139513232691 743512319 24697347 rfl contact14OrdinaryColumns contact14ColumnsJoin0_97 contact14OrdinaryRanks contact14RanksJoin0_97 (by decide +kernel)

private theorem contact16OrdinaryColumns : ordinaryColumnCount contact16 = 173428445355477 := by decide +kernel
private theorem contact16ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact16) 0 4 = 1091437038149 :=
  contactColumnsWindow_fast contact16 0 4 1091437038149 (by decide +kernel)
private theorem contact16ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact16) 4 4 = 1004081157820 :=
  contactColumnsWindow_fast contact16 4 4 1004081157820 (by decide +kernel)
private theorem contact16ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact16) 8 4 = 920389355927 :=
  contactColumnsWindow_fast contact16 8 4 920389355927 (by decide +kernel)
private theorem contact16ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact16) 12 4 = 840360623590 :=
  contactColumnsWindow_fast contact16 12 4 840360623590 (by decide +kernel)
private theorem contact16ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact16) 16 4 = 763993824907 :=
  contactColumnsWindow_fast contact16 16 4 763993824907 (by decide +kernel)
private theorem contact16ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact16) 20 4 = 691296568195 :=
  contactColumnsWindow_fast contact16 20 4 691296568195 (by decide +kernel)
private theorem contact16ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact16) 24 4 = 622283968684 :=
  contactColumnsWindow_fast contact16 24 4 622283968684 (by decide +kernel)
private theorem contact16ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact16) 28 4 = 556936791260 :=
  contactColumnsWindow_fast contact16 28 4 556936791260 (by decide +kernel)
private theorem contact16ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact16) 32 4 = 495252507762 :=
  contactColumnsWindow_fast contact16 32 4 495252507762 (by decide +kernel)
private theorem contact16ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact16) 36 4 = 437230401660 :=
  contactColumnsWindow_fast contact16 36 4 437230401660 (by decide +kernel)
private theorem contact16ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact16) 40 4 = 382879690942 :=
  contactColumnsWindow_fast contact16 40 4 382879690942 (by decide +kernel)
private theorem contact16ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact16) 44 4 = 332212558924 :=
  contactColumnsWindow_fast contact16 44 4 332212558924 (by decide +kernel)
private theorem contact16ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact16) 48 4 = 285210019934 :=
  contactColumnsWindow_fast contact16 48 4 285210019934 (by decide +kernel)
private theorem contact16ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact16) 52 4 = 241870171310 :=
  contactColumnsWindow_fast contact16 52 4 241870171310 (by decide +kernel)
private theorem contact16ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact16) 56 4 = 202192797564 :=
  contactColumnsWindow_fast contact16 56 4 202192797564 (by decide +kernel)
private theorem contact16ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact16) 60 4 = 166188624577 :=
  contactColumnsWindow_fast contact16 60 4 166188624577 (by decide +kernel)
private theorem contact16ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact16) 64 4 = 133866928540 :=
  contactColumnsWindow_fast contact16 64 4 133866928540 (by decide +kernel)
private theorem contact16ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact16) 68 4 = 105209101834 :=
  contactColumnsWindow_fast contact16 68 4 105209101834 (by decide +kernel)
private theorem contact16ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact16) 72 4 = 80213614234 :=
  contactColumnsWindow_fast contact16 72 4 80213614234 (by decide +kernel)
private theorem contact16ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact16) 76 4 = 58880972844 :=
  contactColumnsWindow_fast contact16 76 4 58880972844 (by decide +kernel)
private theorem contact16ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact16) 80 4 = 41223742144 :=
  contactColumnsWindow_fast contact16 80 4 41223742144 (by decide +kernel)
private theorem contact16ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact16) 84 4 = 27220954312 :=
  contactColumnsWindow_fast contact16 84 4 27220954312 (by decide +kernel)
private theorem contact16ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact16) 88 4 = 16699853456 :=
  contactColumnsWindow_fast contact16 88 4 16699853456 (by decide +kernel)
private theorem contact16ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact16) 92 4 = 9333205623 :=
  contactColumnsWindow_fast contact16 92 4 9333205623 (by decide +kernel)
private theorem contact16ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact16) 96 1 = 1507871038 :=
  contactColumnsWindow_fast contact16 96 1 1507871038 (by decide +kernel)
private theorem contact16ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact16) 0 8 = 2095518195969 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 4 4 1091437038149 1004081157820 contact16ColumnsSlice0 contact16ColumnsSlice4
private theorem contact16ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact16) 8 8 = 1760749979517 :=
  combineSlices (auxiliaryColumnSlice contact16) 8 4 4 920389355927 840360623590 contact16ColumnsSlice8 contact16ColumnsSlice12
private theorem contact16ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact16) 16 8 = 1455290393102 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 4 4 763993824907 691296568195 contact16ColumnsSlice16 contact16ColumnsSlice20
private theorem contact16ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact16) 24 8 = 1179220759944 :=
  combineSlices (auxiliaryColumnSlice contact16) 24 4 4 622283968684 556936791260 contact16ColumnsSlice24 contact16ColumnsSlice28
private theorem contact16ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact16) 32 8 = 932482909422 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 4 4 495252507762 437230401660 contact16ColumnsSlice32 contact16ColumnsSlice36
private theorem contact16ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact16) 40 8 = 715092249866 :=
  combineSlices (auxiliaryColumnSlice contact16) 40 4 4 382879690942 332212558924 contact16ColumnsSlice40 contact16ColumnsSlice44
private theorem contact16ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact16) 48 8 = 527080191244 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 4 4 285210019934 241870171310 contact16ColumnsSlice48 contact16ColumnsSlice52
private theorem contact16ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact16) 56 8 = 368381422141 :=
  combineSlices (auxiliaryColumnSlice contact16) 56 4 4 202192797564 166188624577 contact16ColumnsSlice56 contact16ColumnsSlice60
private theorem contact16ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact16) 64 8 = 239076030374 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 4 4 133866928540 105209101834 contact16ColumnsSlice64 contact16ColumnsSlice68
private theorem contact16ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact16) 72 8 = 139094587078 :=
  combineSlices (auxiliaryColumnSlice contact16) 72 4 4 80213614234 58880972844 contact16ColumnsSlice72 contact16ColumnsSlice76
private theorem contact16ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact16) 80 8 = 68444696456 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 4 4 41223742144 27220954312 contact16ColumnsSlice80 contact16ColumnsSlice84
private theorem contact16ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact16) 88 8 = 26033059079 :=
  combineSlices (auxiliaryColumnSlice contact16) 88 4 4 16699853456 9333205623 contact16ColumnsSlice88 contact16ColumnsSlice92
private theorem contact16ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact16) 0 16 = 3856268175486 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 8 8 2095518195969 1760749979517 contact16ColumnsJoin0_8 contact16ColumnsJoin8_8
private theorem contact16ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact16) 16 16 = 2634511153046 :=
  combineSlices (auxiliaryColumnSlice contact16) 16 8 8 1455290393102 1179220759944 contact16ColumnsJoin16_8 contact16ColumnsJoin24_8
private theorem contact16ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact16) 32 16 = 1647575159288 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 8 8 932482909422 715092249866 contact16ColumnsJoin32_8 contact16ColumnsJoin40_8
private theorem contact16ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact16) 48 16 = 895461613385 :=
  combineSlices (auxiliaryColumnSlice contact16) 48 8 8 527080191244 368381422141 contact16ColumnsJoin48_8 contact16ColumnsJoin56_8
private theorem contact16ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact16) 64 16 = 378170617452 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 8 8 239076030374 139094587078 contact16ColumnsJoin64_8 contact16ColumnsJoin72_8
private theorem contact16ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact16) 80 16 = 94477755535 :=
  combineSlices (auxiliaryColumnSlice contact16) 80 8 8 68444696456 26033059079 contact16ColumnsJoin80_8 contact16ColumnsJoin88_8
private theorem contact16ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact16) 0 32 = 6490779328532 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 16 16 3856268175486 2634511153046 contact16ColumnsJoin0_16 contact16ColumnsJoin16_16
private theorem contact16ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact16) 32 32 = 2543036772673 :=
  combineSlices (auxiliaryColumnSlice contact16) 32 16 16 1647575159288 895461613385 contact16ColumnsJoin32_16 contact16ColumnsJoin48_16
private theorem contact16ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact16) 64 32 = 472648372987 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 16 16 378170617452 94477755535 contact16ColumnsJoin64_16 contact16ColumnsJoin80_16
private theorem contact16ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact16) 0 64 = 9033816101205 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 32 32 6490779328532 2543036772673 contact16ColumnsJoin0_32 contact16ColumnsJoin32_32
private theorem contact16ColumnsJoin64_33 : sliceWindow (auxiliaryColumnSlice contact16) 64 33 = 474156244025 :=
  combineSlices (auxiliaryColumnSlice contact16) 64 32 1 472648372987 1507871038 contact16ColumnsJoin64_32 contact16ColumnsSlice96
private theorem contact16ColumnsJoin0_97 : sliceWindow (auxiliaryColumnSlice contact16) 0 97 = 9507972345230 :=
  combineSlices (auxiliaryColumnSlice contact16) 0 64 33 9033816101205 474156244025 contact16ColumnsJoin0_64 contact16ColumnsJoin64_33
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
private theorem contact16RanksSlice92 : sliceWindow (auxiliaryRankSlice contact16) 92 5 = 0 :=
  contactRankWindow_of_rec contact16 92 5 0 (by decide +kernel)
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
private theorem contact16RanksJoin88_9 : sliceWindow (auxiliaryRankSlice contact16) 88 9 = 386 :=
  combineSlices (auxiliaryRankSlice contact16) 88 4 5 386 0 contact16RanksSlice88 contact16RanksSlice92
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
private theorem contact16RanksJoin80_17 : sliceWindow (auxiliaryRankSlice contact16) 80 17 = 30763 :=
  combineSlices (auxiliaryRankSlice contact16) 80 8 9 30377 386 contact16RanksJoin80_8 contact16RanksJoin88_9
private theorem contact16RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact16) 0 32 = 22235232 :=
  combineSlices (auxiliaryRankSlice contact16) 0 16 16 13905456 8329776 contact16RanksJoin0_16 contact16RanksJoin16_16
private theorem contact16RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact16) 32 32 = 6198892 :=
  combineSlices (auxiliaryRankSlice contact16) 32 16 16 4358994 1839898 contact16RanksJoin32_16 contact16RanksJoin48_16
private theorem contact16RanksJoin64_33 : sliceWindow (auxiliaryRankSlice contact16) 64 33 = 525737 :=
  combineSlices (auxiliaryRankSlice contact16) 64 16 17 494974 30763 contact16RanksJoin64_16 contact16RanksJoin80_17
private theorem contact16RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact16) 0 64 = 28434124 :=
  combineSlices (auxiliaryRankSlice contact16) 0 32 32 22235232 6198892 contact16RanksJoin0_32 contact16RanksJoin32_32
private theorem contact16RanksJoin0_97 : sliceWindow (auxiliaryRankSlice contact16) 0 97 = 28959861 :=
  combineSlices (auxiliaryRankSlice contact16) 0 64 33 28434124 525737 contact16RanksJoin0_64 contact16RanksJoin64_33
theorem contact16_margin : sourceMargin contact16 :=
  margin_of_checked_counts contact16 97 173428445355477 9507972345230 668886591 28959861 rfl contact16OrdinaryColumns contact16ColumnsJoin0_97 contact16OrdinaryRanks contact16RanksJoin0_97 (by decide +kernel)

private theorem contact18OrdinaryColumns : ordinaryColumnCount contact18 = 2362946476924481 := by decide +kernel
private theorem contact18ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact18) 0 4 = 7049379794968 :=
  contactColumnsWindow_fast contact18 0 4 7049379794968 (by decide +kernel)
private theorem contact18ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact18) 4 4 = 6702256497944 :=
  contactColumnsWindow_fast contact18 4 4 6702256497944 (by decide +kernel)
private theorem contact18ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact18) 8 4 = 6363933697557 :=
  contactColumnsWindow_fast contact18 8 4 6363933697557 (by decide +kernel)
private theorem contact18ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact18) 12 4 = 6034414273942 :=
  contactColumnsWindow_fast contact18 12 4 6034414273942 (by decide +kernel)
private theorem contact18ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact18) 16 4 = 5713696263191 :=
  contactColumnsWindow_fast contact18 16 4 5713696263191 (by decide +kernel)
private theorem contact18ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact18) 20 4 = 5401781639296 :=
  contactColumnsWindow_fast contact18 20 4 5401781639296 (by decide +kernel)
private theorem contact18ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact18) 24 4 = 5098685593252 :=
  contactColumnsWindow_fast contact18 24 4 5098685593252 (by decide +kernel)
private theorem contact18ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact18) 28 4 = 4804426912846 :=
  contactColumnsWindow_fast contact18 28 4 4804426912846 (by decide +kernel)
private theorem contact18ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact18) 32 4 = 4518974821692 :=
  contactColumnsWindow_fast contact18 32 4 4518974821692 (by decide +kernel)
private theorem contact18ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact18) 36 4 = 4242327293558 :=
  contactColumnsWindow_fast contact18 36 4 4242327293558 (by decide +kernel)
private theorem contact18ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact18) 40 4 = 3974486217168 :=
  contactColumnsWindow_fast contact18 40 4 3974486217168 (by decide +kernel)
private theorem contact18ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact18) 44 4 = 3715470545560 :=
  contactColumnsWindow_fast contact18 44 4 3715470545560 (by decide +kernel)
private theorem contact18ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact18) 48 4 = 3465292878547 :=
  contactColumnsWindow_fast contact18 48 4 3465292878547 (by decide +kernel)
private theorem contact18ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact18) 52 4 = 3223923422014 :=
  contactColumnsWindow_fast contact18 52 4 3223923422014 (by decide +kernel)
private theorem contact18ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact18) 56 4 = 2991362817192 :=
  contactColumnsWindow_fast contact18 56 4 2991362817192 (by decide +kernel)
private theorem contact18ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact18) 60 4 = 2767610806259 :=
  contactColumnsWindow_fast contact18 60 4 2767610806259 (by decide +kernel)
private theorem contact18ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact18) 64 4 = 2552693749061 :=
  contactColumnsWindow_fast contact18 64 4 2552693749061 (by decide +kernel)
private theorem contact18ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact18) 68 4 = 2346612103215 :=
  contactColumnsWindow_fast contact18 68 4 2346612103215 (by decide +kernel)
private theorem contact18ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact18) 72 4 = 2149343638669 :=
  contactColumnsWindow_fast contact18 72 4 2149343638669 (by decide +kernel)
private theorem contact18ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact18) 76 4 = 1960884547652 :=
  contactColumnsWindow_fast contact18 76 4 1960884547652 (by decide +kernel)
private theorem contact18ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact18) 80 4 = 1781233819761 :=
  contactColumnsWindow_fast contact18 80 4 1781233819761 (by decide +kernel)
private theorem contact18ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact18) 84 4 = 1610423082097 :=
  contactColumnsWindow_fast contact18 84 4 1610423082097 (by decide +kernel)
private theorem contact18ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact18) 88 4 = 1448443364205 :=
  contactColumnsWindow_fast contact18 88 4 1448443364205 (by decide +kernel)
private theorem contact18ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact18) 92 4 = 1295276376019 :=
  contactColumnsWindow_fast contact18 92 4 1295276376019 (by decide +kernel)
private theorem contact18ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact18) 96 4 = 1150918760785 :=
  contactColumnsWindow_fast contact18 96 4 1150918760785 (by decide +kernel)
private theorem contact18ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact18) 100 4 = 1015370330771 :=
  contactColumnsWindow_fast contact18 100 4 1015370330771 (by decide +kernel)
private theorem contact18ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact18) 104 4 = 888664991315 :=
  contactColumnsWindow_fast contact18 104 4 888664991315 (by decide +kernel)
private theorem contact18ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact18) 108 4 = 770787173227 :=
  contactColumnsWindow_fast contact18 108 4 770787173227 (by decide +kernel)
private theorem contact18ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact18) 112 4 = 661721637329 :=
  contactColumnsWindow_fast contact18 112 4 661721637329 (by decide +kernel)
private theorem contact18ColumnsSlice116 : sliceWindow (auxiliaryColumnSlice contact18) 116 4 = 561465571767 :=
  contactColumnsWindow_fast contact18 116 4 561465571767 (by decide +kernel)
private theorem contact18ColumnsSlice120 : sliceWindow (auxiliaryColumnSlice contact18) 120 4 = 470019766444 :=
  contactColumnsWindow_fast contact18 120 4 470019766444 (by decide +kernel)
private theorem contact18ColumnsSlice124 : sliceWindow (auxiliaryColumnSlice contact18) 124 4 = 387419380245 :=
  contactColumnsWindow_fast contact18 124 4 387419380245 (by decide +kernel)
private theorem contact18ColumnsSlice128 : sliceWindow (auxiliaryColumnSlice contact18) 128 4 = 313643555673 :=
  contactColumnsWindow_fast contact18 128 4 313643555673 (by decide +kernel)
private theorem contact18ColumnsSlice132 : sliceWindow (auxiliaryColumnSlice contact18) 132 4 = 248679547778 :=
  contactColumnsWindow_fast contact18 132 4 248679547778 (by decide +kernel)
private theorem contact18ColumnsSlice136 : sliceWindow (auxiliaryColumnSlice contact18) 136 4 = 192508122616 :=
  contactColumnsWindow_fast contact18 136 4 192508122616 (by decide +kernel)
private theorem contact18ColumnsSlice140 : sliceWindow (auxiliaryColumnSlice contact18) 140 4 = 144983316111 :=
  contactColumnsWindow_fast contact18 140 4 144983316111 (by decide +kernel)
private theorem contact18ColumnsSlice144 : sliceWindow (auxiliaryColumnSlice contact18) 144 4 = 105793629866 :=
  contactColumnsWindow_fast contact18 144 4 105793629866 (by decide +kernel)
private theorem contact18ColumnsSlice148 : sliceWindow (auxiliaryColumnSlice contact18) 148 4 = 74401347045 :=
  contactColumnsWindow_fast contact18 148 4 74401347045 (by decide +kernel)
private theorem contact18ColumnsSlice152 : sliceWindow (auxiliaryColumnSlice contact18) 152 4 = 50124127226 :=
  contactColumnsWindow_fast contact18 152 4 50124127226 (by decide +kernel)
private theorem contact18ColumnsSlice156 : sliceWindow (auxiliaryColumnSlice contact18) 156 4 = 32126905221 :=
  contactColumnsWindow_fast contact18 156 4 32126905221 (by decide +kernel)
private theorem contact18ColumnsSlice160 : sliceWindow (auxiliaryColumnSlice contact18) 160 1 = 5863188275 :=
  contactColumnsWindow_fast contact18 160 1 5863188275 (by decide +kernel)
private theorem contact18ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact18) 0 8 = 13751636292912 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 4 4 7049379794968 6702256497944 contact18ColumnsSlice0 contact18ColumnsSlice4
private theorem contact18ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact18) 8 8 = 12398347971499 :=
  combineSlices (auxiliaryColumnSlice contact18) 8 4 4 6363933697557 6034414273942 contact18ColumnsSlice8 contact18ColumnsSlice12
private theorem contact18ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact18) 16 8 = 11115477902487 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 4 4 5713696263191 5401781639296 contact18ColumnsSlice16 contact18ColumnsSlice20
private theorem contact18ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact18) 24 8 = 9903112506098 :=
  combineSlices (auxiliaryColumnSlice contact18) 24 4 4 5098685593252 4804426912846 contact18ColumnsSlice24 contact18ColumnsSlice28
private theorem contact18ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact18) 32 8 = 8761302115250 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 4 4 4518974821692 4242327293558 contact18ColumnsSlice32 contact18ColumnsSlice36
private theorem contact18ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact18) 40 8 = 7689956762728 :=
  combineSlices (auxiliaryColumnSlice contact18) 40 4 4 3974486217168 3715470545560 contact18ColumnsSlice40 contact18ColumnsSlice44
private theorem contact18ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact18) 48 8 = 6689216300561 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 4 4 3465292878547 3223923422014 contact18ColumnsSlice48 contact18ColumnsSlice52
private theorem contact18ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact18) 56 8 = 5758973623451 :=
  combineSlices (auxiliaryColumnSlice contact18) 56 4 4 2991362817192 2767610806259 contact18ColumnsSlice56 contact18ColumnsSlice60
private theorem contact18ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact18) 64 8 = 4899305852276 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 4 4 2552693749061 2346612103215 contact18ColumnsSlice64 contact18ColumnsSlice68
private theorem contact18ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact18) 72 8 = 4110228186321 :=
  combineSlices (auxiliaryColumnSlice contact18) 72 4 4 2149343638669 1960884547652 contact18ColumnsSlice72 contact18ColumnsSlice76
private theorem contact18ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact18) 80 8 = 3391656901858 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 4 4 1781233819761 1610423082097 contact18ColumnsSlice80 contact18ColumnsSlice84
private theorem contact18ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact18) 88 8 = 2743719740224 :=
  combineSlices (auxiliaryColumnSlice contact18) 88 4 4 1448443364205 1295276376019 contact18ColumnsSlice88 contact18ColumnsSlice92
private theorem contact18ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact18) 96 8 = 2166289091556 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 4 4 1150918760785 1015370330771 contact18ColumnsSlice96 contact18ColumnsSlice100
private theorem contact18ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact18) 104 8 = 1659452164542 :=
  combineSlices (auxiliaryColumnSlice contact18) 104 4 4 888664991315 770787173227 contact18ColumnsSlice104 contact18ColumnsSlice108
private theorem contact18ColumnsJoin112_8 : sliceWindow (auxiliaryColumnSlice contact18) 112 8 = 1223187209096 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 4 4 661721637329 561465571767 contact18ColumnsSlice112 contact18ColumnsSlice116
private theorem contact18ColumnsJoin120_8 : sliceWindow (auxiliaryColumnSlice contact18) 120 8 = 857439146689 :=
  combineSlices (auxiliaryColumnSlice contact18) 120 4 4 470019766444 387419380245 contact18ColumnsSlice120 contact18ColumnsSlice124
private theorem contact18ColumnsJoin128_8 : sliceWindow (auxiliaryColumnSlice contact18) 128 8 = 562323103451 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 4 4 313643555673 248679547778 contact18ColumnsSlice128 contact18ColumnsSlice132
private theorem contact18ColumnsJoin136_8 : sliceWindow (auxiliaryColumnSlice contact18) 136 8 = 337491438727 :=
  combineSlices (auxiliaryColumnSlice contact18) 136 4 4 192508122616 144983316111 contact18ColumnsSlice136 contact18ColumnsSlice140
private theorem contact18ColumnsJoin144_8 : sliceWindow (auxiliaryColumnSlice contact18) 144 8 = 180194976911 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 4 4 105793629866 74401347045 contact18ColumnsSlice144 contact18ColumnsSlice148
private theorem contact18ColumnsJoin152_8 : sliceWindow (auxiliaryColumnSlice contact18) 152 8 = 82251032447 :=
  combineSlices (auxiliaryColumnSlice contact18) 152 4 4 50124127226 32126905221 contact18ColumnsSlice152 contact18ColumnsSlice156
private theorem contact18ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact18) 0 16 = 26149984264411 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 8 8 13751636292912 12398347971499 contact18ColumnsJoin0_8 contact18ColumnsJoin8_8
private theorem contact18ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact18) 16 16 = 21018590408585 :=
  combineSlices (auxiliaryColumnSlice contact18) 16 8 8 11115477902487 9903112506098 contact18ColumnsJoin16_8 contact18ColumnsJoin24_8
private theorem contact18ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact18) 32 16 = 16451258877978 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 8 8 8761302115250 7689956762728 contact18ColumnsJoin32_8 contact18ColumnsJoin40_8
private theorem contact18ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact18) 48 16 = 12448189924012 :=
  combineSlices (auxiliaryColumnSlice contact18) 48 8 8 6689216300561 5758973623451 contact18ColumnsJoin48_8 contact18ColumnsJoin56_8
private theorem contact18ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact18) 64 16 = 9009534038597 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 8 8 4899305852276 4110228186321 contact18ColumnsJoin64_8 contact18ColumnsJoin72_8
private theorem contact18ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact18) 80 16 = 6135376642082 :=
  combineSlices (auxiliaryColumnSlice contact18) 80 8 8 3391656901858 2743719740224 contact18ColumnsJoin80_8 contact18ColumnsJoin88_8
private theorem contact18ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact18) 96 16 = 3825741256098 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 8 8 2166289091556 1659452164542 contact18ColumnsJoin96_8 contact18ColumnsJoin104_8
private theorem contact18ColumnsJoin112_16 : sliceWindow (auxiliaryColumnSlice contact18) 112 16 = 2080626355785 :=
  combineSlices (auxiliaryColumnSlice contact18) 112 8 8 1223187209096 857439146689 contact18ColumnsJoin112_8 contact18ColumnsJoin120_8
private theorem contact18ColumnsJoin128_16 : sliceWindow (auxiliaryColumnSlice contact18) 128 16 = 899814542178 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 8 8 562323103451 337491438727 contact18ColumnsJoin128_8 contact18ColumnsJoin136_8
private theorem contact18ColumnsJoin144_16 : sliceWindow (auxiliaryColumnSlice contact18) 144 16 = 262446009358 :=
  combineSlices (auxiliaryColumnSlice contact18) 144 8 8 180194976911 82251032447 contact18ColumnsJoin144_8 contact18ColumnsJoin152_8
private theorem contact18ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact18) 0 32 = 47168574672996 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 16 16 26149984264411 21018590408585 contact18ColumnsJoin0_16 contact18ColumnsJoin16_16
private theorem contact18ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact18) 32 32 = 28899448801990 :=
  combineSlices (auxiliaryColumnSlice contact18) 32 16 16 16451258877978 12448189924012 contact18ColumnsJoin32_16 contact18ColumnsJoin48_16
private theorem contact18ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact18) 64 32 = 15144910680679 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 16 16 9009534038597 6135376642082 contact18ColumnsJoin64_16 contact18ColumnsJoin80_16
private theorem contact18ColumnsJoin96_32 : sliceWindow (auxiliaryColumnSlice contact18) 96 32 = 5906367611883 :=
  combineSlices (auxiliaryColumnSlice contact18) 96 16 16 3825741256098 2080626355785 contact18ColumnsJoin96_16 contact18ColumnsJoin112_16
private theorem contact18ColumnsJoin128_32 : sliceWindow (auxiliaryColumnSlice contact18) 128 32 = 1162260551536 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 16 16 899814542178 262446009358 contact18ColumnsJoin128_16 contact18ColumnsJoin144_16
private theorem contact18ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact18) 0 64 = 76068023474986 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 32 32 47168574672996 28899448801990 contact18ColumnsJoin0_32 contact18ColumnsJoin32_32
private theorem contact18ColumnsJoin64_64 : sliceWindow (auxiliaryColumnSlice contact18) 64 64 = 21051278292562 :=
  combineSlices (auxiliaryColumnSlice contact18) 64 32 32 15144910680679 5906367611883 contact18ColumnsJoin64_32 contact18ColumnsJoin96_32
private theorem contact18ColumnsJoin128_33 : sliceWindow (auxiliaryColumnSlice contact18) 128 33 = 1168123739811 :=
  combineSlices (auxiliaryColumnSlice contact18) 128 32 1 1162260551536 5863188275 contact18ColumnsJoin128_32 contact18ColumnsSlice160
private theorem contact18ColumnsJoin0_128 : sliceWindow (auxiliaryColumnSlice contact18) 0 128 = 97119301767548 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 64 64 76068023474986 21051278292562 contact18ColumnsJoin0_64 contact18ColumnsJoin64_64
private theorem contact18ColumnsJoin0_161 : sliceWindow (auxiliaryColumnSlice contact18) 0 161 = 98287425507359 :=
  combineSlices (auxiliaryColumnSlice contact18) 0 128 33 97119301767548 1168123739811 contact18ColumnsJoin0_128 contact18ColumnsJoin128_33
private theorem contact18OrdinaryRanks : ordinaryRankBound contact18 = 9090592603 := by decide +kernel
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
  margin_of_checked_counts contact18 161 2362946476924481 98287425507359 9090592603 298265580 rfl contact18OrdinaryColumns contact18ColumnsJoin0_161 contact18OrdinaryRanks contact18RanksJoin0_161 (by decide +kernel)

private theorem contact20OrdinaryColumns : ordinaryColumnCount contact20 = 53744710997659 := by decide +kernel
private theorem contact20ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact20) 0 4 = 448601868584 :=
  contactColumnsWindow_fast contact20 0 4 448601868584 (by decide +kernel)
private theorem contact20ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact20) 4 4 = 403894871480 :=
  contactColumnsWindow_fast contact20 4 4 403894871480 (by decide +kernel)
private theorem contact20ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact20) 8 4 = 361544955656 :=
  contactColumnsWindow_fast contact20 8 4 361544955656 (by decide +kernel)
private theorem contact20ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact20) 12 4 = 321561936918 :=
  contactColumnsWindow_fast contact20 12 4 321561936918 (by decide +kernel)
private theorem contact20ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact20) 16 4 = 283947022134 :=
  contactColumnsWindow_fast contact20 16 4 283947022134 (by decide +kernel)
private theorem contact20ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact20) 20 4 = 248691060000 :=
  contactColumnsWindow_fast contact20 20 4 248691060000 (by decide +kernel)
private theorem contact20ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact20) 24 4 = 215793499181 :=
  contactColumnsWindow_fast contact20 24 4 215793499181 (by decide +kernel)
private theorem contact20ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact20) 28 4 = 185255274830 :=
  contactColumnsWindow_fast contact20 28 4 185255274830 (by decide +kernel)
private theorem contact20ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact20) 32 4 = 157086869832 :=
  contactColumnsWindow_fast contact20 32 4 157086869832 (by decide +kernel)
private theorem contact20ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact20) 36 4 = 131284668144 :=
  contactColumnsWindow_fast contact20 36 4 131284668144 (by decide +kernel)
private theorem contact20ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact20) 40 4 = 107841597398 :=
  contactColumnsWindow_fast contact20 40 4 107841597398 (by decide +kernel)
private theorem contact20ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact20) 44 4 = 86756771078 :=
  contactColumnsWindow_fast contact20 44 4 86756771078 (by decide +kernel)
private theorem contact20ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact20) 48 4 = 68031613233 :=
  contactColumnsWindow_fast contact20 48 4 68031613233 (by decide +kernel)
private theorem contact20ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact20) 52 4 = 51677645526 :=
  contactColumnsWindow_fast contact20 52 4 51677645526 (by decide +kernel)
private theorem contact20ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact20) 56 4 = 37688173319 :=
  contactColumnsWindow_fast contact20 56 4 37688173319 (by decide +kernel)
private theorem contact20ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact20) 60 4 = 26057977576 :=
  contactColumnsWindow_fast contact20 60 4 26057977576 (by decide +kernel)
private theorem contact20ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact20) 64 4 = 16785712421 :=
  contactColumnsWindow_fast contact20 64 4 16785712421 (by decide +kernel)
private theorem contact20ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact20) 68 4 = 9848986508 :=
  contactColumnsWindow_fast contact20 68 4 9848986508 (by decide +kernel)
private theorem contact20ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact20) 72 4 = 5111503805 :=
  contactColumnsWindow_fast contact20 72 4 5111503805 (by decide +kernel)
private theorem contact20ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact20) 76 2 = 1382503930 :=
  contactColumnsWindow_fast contact20 76 2 1382503930 (by decide +kernel)
private theorem contact20ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact20) 0 8 = 852496740064 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 4 4 448601868584 403894871480 contact20ColumnsSlice0 contact20ColumnsSlice4
private theorem contact20ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact20) 8 8 = 683106892574 :=
  combineSlices (auxiliaryColumnSlice contact20) 8 4 4 361544955656 321561936918 contact20ColumnsSlice8 contact20ColumnsSlice12
private theorem contact20ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact20) 16 8 = 532638082134 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 4 4 283947022134 248691060000 contact20ColumnsSlice16 contact20ColumnsSlice20
private theorem contact20ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact20) 24 8 = 401048774011 :=
  combineSlices (auxiliaryColumnSlice contact20) 24 4 4 215793499181 185255274830 contact20ColumnsSlice24 contact20ColumnsSlice28
private theorem contact20ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact20) 32 8 = 288371537976 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 4 4 157086869832 131284668144 contact20ColumnsSlice32 contact20ColumnsSlice36
private theorem contact20ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact20) 40 8 = 194598368476 :=
  combineSlices (auxiliaryColumnSlice contact20) 40 4 4 107841597398 86756771078 contact20ColumnsSlice40 contact20ColumnsSlice44
private theorem contact20ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact20) 48 8 = 119709258759 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 4 4 68031613233 51677645526 contact20ColumnsSlice48 contact20ColumnsSlice52
private theorem contact20ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact20) 56 8 = 63746150895 :=
  combineSlices (auxiliaryColumnSlice contact20) 56 4 4 37688173319 26057977576 contact20ColumnsSlice56 contact20ColumnsSlice60
private theorem contact20ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact20) 64 8 = 26634698929 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 4 4 16785712421 9848986508 contact20ColumnsSlice64 contact20ColumnsSlice68
private theorem contact20ColumnsJoin72_6 : sliceWindow (auxiliaryColumnSlice contact20) 72 6 = 6494007735 :=
  combineSlices (auxiliaryColumnSlice contact20) 72 4 2 5111503805 1382503930 contact20ColumnsSlice72 contact20ColumnsSlice76
private theorem contact20ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact20) 0 16 = 1535603632638 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 8 8 852496740064 683106892574 contact20ColumnsJoin0_8 contact20ColumnsJoin8_8
private theorem contact20ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact20) 16 16 = 933686856145 :=
  combineSlices (auxiliaryColumnSlice contact20) 16 8 8 532638082134 401048774011 contact20ColumnsJoin16_8 contact20ColumnsJoin24_8
private theorem contact20ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact20) 32 16 = 482969906452 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 8 8 288371537976 194598368476 contact20ColumnsJoin32_8 contact20ColumnsJoin40_8
private theorem contact20ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact20) 48 16 = 183455409654 :=
  combineSlices (auxiliaryColumnSlice contact20) 48 8 8 119709258759 63746150895 contact20ColumnsJoin48_8 contact20ColumnsJoin56_8
private theorem contact20ColumnsJoin64_14 : sliceWindow (auxiliaryColumnSlice contact20) 64 14 = 33128706664 :=
  combineSlices (auxiliaryColumnSlice contact20) 64 8 6 26634698929 6494007735 contact20ColumnsJoin64_8 contact20ColumnsJoin72_6
private theorem contact20ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact20) 0 32 = 2469290488783 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 16 16 1535603632638 933686856145 contact20ColumnsJoin0_16 contact20ColumnsJoin16_16
private theorem contact20ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact20) 32 32 = 666425316106 :=
  combineSlices (auxiliaryColumnSlice contact20) 32 16 16 482969906452 183455409654 contact20ColumnsJoin32_16 contact20ColumnsJoin48_16
private theorem contact20ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact20) 0 64 = 3135715804889 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 32 32 2469290488783 666425316106 contact20ColumnsJoin0_32 contact20ColumnsJoin32_32
private theorem contact20ColumnsJoin0_78 : sliceWindow (auxiliaryColumnSlice contact20) 0 78 = 3168844511553 :=
  combineSlices (auxiliaryColumnSlice contact20) 0 64 14 3135715804889 33128706664 contact20ColumnsJoin0_64 contact20ColumnsJoin64_14
private theorem contact20OrdinaryRanks : ordinaryRankBound contact20 = 207474450 := by decide +kernel
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
  margin_of_checked_counts contact20 78 53744710997659 3168844511553 207474450 9633495 rfl contact20OrdinaryColumns contact20ColumnsJoin0_78 contact20OrdinaryRanks contact20RanksJoin0_78 (by decide +kernel)

private theorem contact22OrdinaryColumns : ordinaryColumnCount contact22 = 158592794985500 := by decide +kernel
private theorem contact22ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact22) 0 4 = 1567111706833 :=
  contactColumnsWindow_fast contact22 0 4 1567111706833 (by decide +kernel)
private theorem contact22ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact22) 4 4 = 1451675089842 :=
  contactColumnsWindow_fast contact22 4 4 1451675089842 (by decide +kernel)
private theorem contact22ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact22) 8 4 = 1340683713143 :=
  contactColumnsWindow_fast contact22 8 4 1340683713143 (by decide +kernel)
private theorem contact22ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact22) 12 4 = 1234132321096 :=
  contactColumnsWindow_fast contact22 12 4 1234132321096 (by decide +kernel)
private theorem contact22ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact22) 16 4 = 1132019145235 :=
  contactColumnsWindow_fast contact22 16 4 1132019145235 (by decide +kernel)
private theorem contact22ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact22) 20 4 = 1034349793411 :=
  contactColumnsWindow_fast contact22 20 4 1034349793411 (by decide +kernel)
private theorem contact22ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact22) 24 4 = 941147492702 :=
  contactColumnsWindow_fast contact22 24 4 941147492702 (by decide +kernel)
private theorem contact22ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact22) 28 4 = 852391753937 :=
  contactColumnsWindow_fast contact22 28 4 852391753937 (by decide +kernel)
private theorem contact22ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact22) 32 4 = 768076146712 :=
  contactColumnsWindow_fast contact22 32 4 768076146712 (by decide +kernel)
private theorem contact22ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact22) 36 4 = 688198857057 :=
  contactColumnsWindow_fast contact22 36 4 688198857057 (by decide +kernel)
private theorem contact22ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact22) 40 4 = 612767000169 :=
  contactColumnsWindow_fast contact22 40 4 612767000169 (by decide +kernel)
private theorem contact22ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact22) 44 4 = 541802403667 :=
  contactColumnsWindow_fast contact22 44 4 541802403667 (by decide +kernel)
private theorem contact22ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact22) 48 4 = 475282604138 :=
  contactColumnsWindow_fast contact22 48 4 475282604138 (by decide +kernel)
private theorem contact22ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact22) 52 4 = 413202735208 :=
  contactColumnsWindow_fast contact22 52 4 413202735208 (by decide +kernel)
private theorem contact22ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact22) 56 4 = 355561343280 :=
  contactColumnsWindow_fast contact22 56 4 355561343280 (by decide +kernel)
private theorem contact22ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact22) 60 4 = 302367024173 :=
  contactColumnsWindow_fast contact22 60 4 302367024173 (by decide +kernel)
private theorem contact22ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact22) 64 4 = 253640146398 :=
  contactColumnsWindow_fast contact22 64 4 253640146398 (by decide +kernel)
private theorem contact22ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact22) 68 4 = 209356268543 :=
  contactColumnsWindow_fast contact22 68 4 209356268543 (by decide +kernel)
private theorem contact22ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact22) 72 4 = 169512086584 :=
  contactColumnsWindow_fast contact22 72 4 169512086584 (by decide +kernel)
private theorem contact22ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact22) 76 4 = 134106615630 :=
  contactColumnsWindow_fast contact22 76 4 134106615630 (by decide +kernel)
private theorem contact22ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact22) 80 4 = 103150652404 :=
  contactColumnsWindow_fast contact22 80 4 103150652404 (by decide +kernel)
private theorem contact22ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact22) 84 4 = 76660691010 :=
  contactColumnsWindow_fast contact22 84 4 76660691010 (by decide +kernel)
private theorem contact22ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact22) 88 4 = 54610766080 :=
  contactColumnsWindow_fast contact22 88 4 54610766080 (by decide +kernel)
private theorem contact22ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact22) 92 4 = 36943102252 :=
  contactColumnsWindow_fast contact22 92 4 36943102252 (by decide +kernel)
private theorem contact22ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact22) 96 4 = 23446003192 :=
  contactColumnsWindow_fast contact22 96 4 23446003192 (by decide +kernel)
private theorem contact22ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact22) 100 3 = 11032673204 :=
  contactColumnsWindow_fast contact22 100 3 11032673204 (by decide +kernel)
private theorem contact22ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact22) 0 8 = 3018786796675 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 4 4 1567111706833 1451675089842 contact22ColumnsSlice0 contact22ColumnsSlice4
private theorem contact22ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact22) 8 8 = 2574816034239 :=
  combineSlices (auxiliaryColumnSlice contact22) 8 4 4 1340683713143 1234132321096 contact22ColumnsSlice8 contact22ColumnsSlice12
private theorem contact22ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact22) 16 8 = 2166368938646 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 4 4 1132019145235 1034349793411 contact22ColumnsSlice16 contact22ColumnsSlice20
private theorem contact22ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact22) 24 8 = 1793539246639 :=
  combineSlices (auxiliaryColumnSlice contact22) 24 4 4 941147492702 852391753937 contact22ColumnsSlice24 contact22ColumnsSlice28
private theorem contact22ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact22) 32 8 = 1456275003769 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 4 4 768076146712 688198857057 contact22ColumnsSlice32 contact22ColumnsSlice36
private theorem contact22ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact22) 40 8 = 1154569403836 :=
  combineSlices (auxiliaryColumnSlice contact22) 40 4 4 612767000169 541802403667 contact22ColumnsSlice40 contact22ColumnsSlice44
private theorem contact22ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact22) 48 8 = 888485339346 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 4 4 475282604138 413202735208 contact22ColumnsSlice48 contact22ColumnsSlice52
private theorem contact22ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact22) 56 8 = 657928367453 :=
  combineSlices (auxiliaryColumnSlice contact22) 56 4 4 355561343280 302367024173 contact22ColumnsSlice56 contact22ColumnsSlice60
private theorem contact22ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact22) 64 8 = 462996414941 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 4 4 253640146398 209356268543 contact22ColumnsSlice64 contact22ColumnsSlice68
private theorem contact22ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact22) 72 8 = 303618702214 :=
  combineSlices (auxiliaryColumnSlice contact22) 72 4 4 169512086584 134106615630 contact22ColumnsSlice72 contact22ColumnsSlice76
private theorem contact22ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact22) 80 8 = 179811343414 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 4 4 103150652404 76660691010 contact22ColumnsSlice80 contact22ColumnsSlice84
private theorem contact22ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact22) 88 8 = 91553868332 :=
  combineSlices (auxiliaryColumnSlice contact22) 88 4 4 54610766080 36943102252 contact22ColumnsSlice88 contact22ColumnsSlice92
private theorem contact22ColumnsJoin96_7 : sliceWindow (auxiliaryColumnSlice contact22) 96 7 = 34478676396 :=
  combineSlices (auxiliaryColumnSlice contact22) 96 4 3 23446003192 11032673204 contact22ColumnsSlice96 contact22ColumnsSlice100
private theorem contact22ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact22) 0 16 = 5593602830914 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 8 8 3018786796675 2574816034239 contact22ColumnsJoin0_8 contact22ColumnsJoin8_8
private theorem contact22ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact22) 16 16 = 3959908185285 :=
  combineSlices (auxiliaryColumnSlice contact22) 16 8 8 2166368938646 1793539246639 contact22ColumnsJoin16_8 contact22ColumnsJoin24_8
private theorem contact22ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact22) 32 16 = 2610844407605 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 8 8 1456275003769 1154569403836 contact22ColumnsJoin32_8 contact22ColumnsJoin40_8
private theorem contact22ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact22) 48 16 = 1546413706799 :=
  combineSlices (auxiliaryColumnSlice contact22) 48 8 8 888485339346 657928367453 contact22ColumnsJoin48_8 contact22ColumnsJoin56_8
private theorem contact22ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact22) 64 16 = 766615117155 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 8 8 462996414941 303618702214 contact22ColumnsJoin64_8 contact22ColumnsJoin72_8
private theorem contact22ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact22) 80 16 = 271365211746 :=
  combineSlices (auxiliaryColumnSlice contact22) 80 8 8 179811343414 91553868332 contact22ColumnsJoin80_8 contact22ColumnsJoin88_8
private theorem contact22ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact22) 0 32 = 9553511016199 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 16 16 5593602830914 3959908185285 contact22ColumnsJoin0_16 contact22ColumnsJoin16_16
private theorem contact22ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact22) 32 32 = 4157258114404 :=
  combineSlices (auxiliaryColumnSlice contact22) 32 16 16 2610844407605 1546413706799 contact22ColumnsJoin32_16 contact22ColumnsJoin48_16
private theorem contact22ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact22) 64 32 = 1037980328901 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 16 16 766615117155 271365211746 contact22ColumnsJoin64_16 contact22ColumnsJoin80_16
private theorem contact22ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact22) 0 64 = 13710769130603 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 32 32 9553511016199 4157258114404 contact22ColumnsJoin0_32 contact22ColumnsJoin32_32
private theorem contact22ColumnsJoin64_39 : sliceWindow (auxiliaryColumnSlice contact22) 64 39 = 1072459005297 :=
  combineSlices (auxiliaryColumnSlice contact22) 64 32 7 1037980328901 34478676396 contact22ColumnsJoin64_32 contact22ColumnsJoin96_7
private theorem contact22ColumnsJoin0_103 : sliceWindow (auxiliaryColumnSlice contact22) 0 103 = 14783228135900 :=
  combineSlices (auxiliaryColumnSlice contact22) 0 64 39 13710769130603 1072459005297 contact22ColumnsJoin0_64 contact22ColumnsJoin64_39
private theorem contact22OrdinaryRanks : ordinaryRankBound contact22 = 616362945 := by decide +kernel
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
  margin_of_checked_counts contact22 103 158592794985500 14783228135900 616362945 45010685 rfl contact22OrdinaryColumns contact22ColumnsJoin0_103 contact22OrdinaryRanks contact22RanksJoin0_103 (by decide +kernel)

private theorem contact24OrdinaryColumns : ordinaryColumnCount contact24 = 165214887399277 := by decide +kernel
private theorem contact24ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact24) 0 4 = 1369751948924 :=
  contactColumnsWindow_fast contact24 0 4 1369751948924 (by decide +kernel)
private theorem contact24ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact24) 4 4 = 1264208106588 :=
  contactColumnsWindow_fast contact24 4 4 1264208106588 (by decide +kernel)
private theorem contact24ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact24) 8 4 = 1162916254012 :=
  contactColumnsWindow_fast contact24 8 4 1162916254012 (by decide +kernel)
private theorem contact24ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact24) 12 4 = 1065894777580 :=
  contactColumnsWindow_fast contact24 12 4 1065894777580 (by decide +kernel)
private theorem contact24ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact24) 16 4 = 973143252401 :=
  contactColumnsWindow_fast contact24 16 4 973143252401 (by decide +kernel)
private theorem contact24ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact24) 20 4 = 884646283236 :=
  contactColumnsWindow_fast contact24 20 4 884646283236 (by decide +kernel)
private theorem contact24ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact24) 24 4 = 800402940912 :=
  contactColumnsWindow_fast contact24 24 4 800402940912 (by decide +kernel)
private theorem contact24ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact24) 28 4 = 720414573188 :=
  contactColumnsWindow_fast contact24 28 4 720414573188 (by decide +kernel)
private theorem contact24ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact24) 32 4 = 644701473028 :=
  contactColumnsWindow_fast contact24 32 4 644701473028 (by decide +kernel)
private theorem contact24ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact24) 36 4 = 573258373439 :=
  contactColumnsWindow_fast contact24 36 4 573258373439 (by decide +kernel)
private theorem contact24ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact24) 40 4 = 506070796540 :=
  contactColumnsWindow_fast contact24 40 4 506070796540 (by decide +kernel)
private theorem contact24ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact24) 44 4 = 443136660816 :=
  contactColumnsWindow_fast contact24 44 4 443136660816 (by decide +kernel)
private theorem contact24ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact24) 48 4 = 384458325978 :=
  contactColumnsWindow_fast contact24 48 4 384458325978 (by decide +kernel)
private theorem contact24ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact24) 52 4 = 330057329488 :=
  contactColumnsWindow_fast contact24 52 4 330057329488 (by decide +kernel)
private theorem contact24ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact24) 56 4 = 279923642237 :=
  contactColumnsWindow_fast contact24 56 4 279923642237 (by decide +kernel)
private theorem contact24ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact24) 60 4 = 234045457604 :=
  contactColumnsWindow_fast contact24 60 4 234045457604 (by decide +kernel)
private theorem contact24ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact24) 64 4 = 192420618660 :=
  contactColumnsWindow_fast contact24 64 4 192420618660 (by decide +kernel)
private theorem contact24ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact24) 68 4 = 155052454022 :=
  contactColumnsWindow_fast contact24 68 4 155052454022 (by decide +kernel)
private theorem contact24ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact24) 72 4 = 121963333708 :=
  contactColumnsWindow_fast contact24 72 4 121963333708 (by decide +kernel)
private theorem contact24ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact24) 76 4 = 93139105136 :=
  contactColumnsWindow_fast contact24 76 4 93139105136 (by decide +kernel)
private theorem contact24ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact24) 80 4 = 68570266428 :=
  contactColumnsWindow_fast contact24 80 4 68570266428 (by decide +kernel)
private theorem contact24ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact24) 84 4 = 48251967457 :=
  contactColumnsWindow_fast contact24 84 4 48251967457 (by decide +kernel)
private theorem contact24ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact24) 88 4 = 32124578426 :=
  contactColumnsWindow_fast contact24 88 4 32124578426 (by decide +kernel)
private theorem contact24ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact24) 92 4 = 19984908020 :=
  contactColumnsWindow_fast contact24 92 4 19984908020 (by decide +kernel)
private theorem contact24ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact24) 96 4 = 11421123107 :=
  contactColumnsWindow_fast contact24 96 4 11421123107 (by decide +kernel)
private theorem contact24ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact24) 100 1 = 1884972356 :=
  contactColumnsWindow_fast contact24 100 1 1884972356 (by decide +kernel)
private theorem contact24ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact24) 0 8 = 2633960055512 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 4 4 1369751948924 1264208106588 contact24ColumnsSlice0 contact24ColumnsSlice4
private theorem contact24ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact24) 8 8 = 2228811031592 :=
  combineSlices (auxiliaryColumnSlice contact24) 8 4 4 1162916254012 1065894777580 contact24ColumnsSlice8 contact24ColumnsSlice12
private theorem contact24ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact24) 16 8 = 1857789535637 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 4 4 973143252401 884646283236 contact24ColumnsSlice16 contact24ColumnsSlice20
private theorem contact24ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact24) 24 8 = 1520817514100 :=
  combineSlices (auxiliaryColumnSlice contact24) 24 4 4 800402940912 720414573188 contact24ColumnsSlice24 contact24ColumnsSlice28
private theorem contact24ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact24) 32 8 = 1217959846467 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 4 4 644701473028 573258373439 contact24ColumnsSlice32 contact24ColumnsSlice36
private theorem contact24ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact24) 40 8 = 949207457356 :=
  combineSlices (auxiliaryColumnSlice contact24) 40 4 4 506070796540 443136660816 contact24ColumnsSlice40 contact24ColumnsSlice44
private theorem contact24ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact24) 48 8 = 714515655466 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 4 4 384458325978 330057329488 contact24ColumnsSlice48 contact24ColumnsSlice52
private theorem contact24ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact24) 56 8 = 513969099841 :=
  combineSlices (auxiliaryColumnSlice contact24) 56 4 4 279923642237 234045457604 contact24ColumnsSlice56 contact24ColumnsSlice60
private theorem contact24ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact24) 64 8 = 347473072682 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 4 4 192420618660 155052454022 contact24ColumnsSlice64 contact24ColumnsSlice68
private theorem contact24ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact24) 72 8 = 215102438844 :=
  combineSlices (auxiliaryColumnSlice contact24) 72 4 4 121963333708 93139105136 contact24ColumnsSlice72 contact24ColumnsSlice76
private theorem contact24ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact24) 80 8 = 116822233885 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 4 4 68570266428 48251967457 contact24ColumnsSlice80 contact24ColumnsSlice84
private theorem contact24ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact24) 88 8 = 52109486446 :=
  combineSlices (auxiliaryColumnSlice contact24) 88 4 4 32124578426 19984908020 contact24ColumnsSlice88 contact24ColumnsSlice92
private theorem contact24ColumnsJoin96_5 : sliceWindow (auxiliaryColumnSlice contact24) 96 5 = 13306095463 :=
  combineSlices (auxiliaryColumnSlice contact24) 96 4 1 11421123107 1884972356 contact24ColumnsSlice96 contact24ColumnsSlice100
private theorem contact24ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact24) 0 16 = 4862771087104 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 8 8 2633960055512 2228811031592 contact24ColumnsJoin0_8 contact24ColumnsJoin8_8
private theorem contact24ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact24) 16 16 = 3378607049737 :=
  combineSlices (auxiliaryColumnSlice contact24) 16 8 8 1857789535637 1520817514100 contact24ColumnsJoin16_8 contact24ColumnsJoin24_8
private theorem contact24ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact24) 32 16 = 2167167303823 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 8 8 1217959846467 949207457356 contact24ColumnsJoin32_8 contact24ColumnsJoin40_8
private theorem contact24ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact24) 48 16 = 1228484755307 :=
  combineSlices (auxiliaryColumnSlice contact24) 48 8 8 714515655466 513969099841 contact24ColumnsJoin48_8 contact24ColumnsJoin56_8
private theorem contact24ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact24) 64 16 = 562575511526 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 8 8 347473072682 215102438844 contact24ColumnsJoin64_8 contact24ColumnsJoin72_8
private theorem contact24ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact24) 80 16 = 168931720331 :=
  combineSlices (auxiliaryColumnSlice contact24) 80 8 8 116822233885 52109486446 contact24ColumnsJoin80_8 contact24ColumnsJoin88_8
private theorem contact24ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact24) 0 32 = 8241378136841 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 16 16 4862771087104 3378607049737 contact24ColumnsJoin0_16 contact24ColumnsJoin16_16
private theorem contact24ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact24) 32 32 = 3395652059130 :=
  combineSlices (auxiliaryColumnSlice contact24) 32 16 16 2167167303823 1228484755307 contact24ColumnsJoin32_16 contact24ColumnsJoin48_16
private theorem contact24ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact24) 64 32 = 731507231857 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 16 16 562575511526 168931720331 contact24ColumnsJoin64_16 contact24ColumnsJoin80_16
private theorem contact24ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact24) 0 64 = 11637030195971 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 32 32 8241378136841 3395652059130 contact24ColumnsJoin0_32 contact24ColumnsJoin32_32
private theorem contact24ColumnsJoin64_37 : sliceWindow (auxiliaryColumnSlice contact24) 64 37 = 744813327320 :=
  combineSlices (auxiliaryColumnSlice contact24) 64 32 5 731507231857 13306095463 contact24ColumnsJoin64_32 contact24ColumnsJoin96_5
private theorem contact24ColumnsJoin0_101 : sliceWindow (auxiliaryColumnSlice contact24) 0 101 = 12381843523291 :=
  combineSlices (auxiliaryColumnSlice contact24) 0 64 37 11637030195971 744813327320 contact24ColumnsJoin0_64 contact24ColumnsJoin64_37
private theorem contact24OrdinaryRanks : ordinaryRankBound contact24 = 639632249 := by decide +kernel
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
private theorem contact24RanksSlice96 : sliceWindow (auxiliaryRankSlice contact24) 96 5 = 0 :=
  contactRankWindow_of_rec contact24 96 5 0 (by decide +kernel)
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
private theorem contact24RanksJoin64_37 : sliceWindow (auxiliaryRankSlice contact24) 64 37 = 937211 :=
  combineSlices (auxiliaryRankSlice contact24) 64 32 5 937211 0 contact24RanksJoin64_32 contact24RanksSlice96
private theorem contact24RanksJoin0_101 : sliceWindow (auxiliaryRankSlice contact24) 0 101 = 37844672 :=
  combineSlices (auxiliaryRankSlice contact24) 0 64 37 36907461 937211 contact24RanksJoin0_64 contact24RanksJoin64_37
theorem contact24_margin : sourceMargin contact24 :=
  margin_of_checked_counts contact24 101 165214887399277 12381843523291 639632249 37844672 rfl contact24OrdinaryColumns contact24ColumnsJoin0_101 contact24OrdinaryRanks contact24RanksJoin0_101 (by decide +kernel)

private theorem contact26OrdinaryColumns : ordinaryColumnCount contact26 = 163506459879357 := by decide +kernel
private theorem contact26ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact26) 0 4 = 1856068799186 :=
  contactColumnsWindow_fast contact26 0 4 1856068799186 (by decide +kernel)
private theorem contact26ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact26) 4 4 = 1724582422738 :=
  contactColumnsWindow_fast contact26 4 4 1724582422738 (by decide +kernel)
private theorem contact26ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact26) 8 4 = 1597948860690 :=
  contactColumnsWindow_fast contact26 8 4 1597948860690 (by decide +kernel)
private theorem contact26ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact26) 12 4 = 1476181150091 :=
  contactColumnsWindow_fast contact26 12 4 1476181150091 (by decide +kernel)
private theorem contact26ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact26) 16 4 = 1359294590902 :=
  contactColumnsWindow_fast contact26 16 4 1359294590902 (by decide +kernel)
private theorem contact26ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact26) 20 4 = 1247263624456 :=
  contactColumnsWindow_fast contact26 20 4 1247263624456 (by decide +kernel)
private theorem contact26ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact26) 24 4 = 1140088019576 :=
  contactColumnsWindow_fast contact26 24 4 1140088019576 (by decide +kernel)
private theorem contact26ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact26) 28 4 = 1037767762398 :=
  contactColumnsWindow_fast contact26 28 4 1037767762398 (by decide +kernel)
private theorem contact26ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact26) 32 4 = 940318519565 :=
  contactColumnsWindow_fast contact26 32 4 940318519565 (by decide +kernel)
private theorem contact26ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact26) 36 4 = 847751489356 :=
  contactColumnsWindow_fast contact26 36 4 847751489356 (by decide +kernel)
private theorem contact26ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact26) 40 4 = 760041109986 :=
  contactColumnsWindow_fast contact26 40 4 760041109986 (by decide +kernel)
private theorem contact26ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact26) 44 4 = 677185703926 :=
  contactColumnsWindow_fast contact26 44 4 677185703926 (by decide +kernel)
private theorem contact26ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact26) 48 4 = 599186030676 :=
  contactColumnsWindow_fast contact26 48 4 599186030676 (by decide +kernel)
private theorem contact26ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact26) 52 4 = 526061050604 :=
  contactColumnsWindow_fast contact26 52 4 526061050604 (by decide +kernel)
private theorem contact26ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact26) 56 4 = 457814534710 :=
  contactColumnsWindow_fast contact26 56 4 457814534710 (by decide +kernel)
private theorem contact26ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact26) 60 4 = 394424742416 :=
  contactColumnsWindow_fast contact26 60 4 394424742416 (by decide +kernel)
private theorem contact26ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact26) 64 4 = 335889619843 :=
  contactColumnsWindow_fast contact26 64 4 335889619843 (by decide +kernel)
private theorem contact26ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact26) 68 4 = 282210445854 :=
  contactColumnsWindow_fast contact26 68 4 282210445854 (by decide +kernel)
private theorem contact26ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact26) 72 4 = 233409728543 :=
  contactColumnsWindow_fast contact26 72 4 233409728543 (by decide +kernel)
private theorem contact26ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact26) 76 4 = 189483809538 :=
  contactColumnsWindow_fast contact26 76 4 189483809538 (by decide +kernel)
private theorem contact26ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact26) 80 4 = 150414521746 :=
  contactColumnsWindow_fast contact26 80 4 150414521746 (by decide +kernel)
private theorem contact26ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact26) 84 4 = 116199682660 :=
  contactColumnsWindow_fast contact26 84 4 116199682660 (by decide +kernel)
private theorem contact26ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact26) 88 4 = 86841393219 :=
  contactColumnsWindow_fast contact26 88 4 86841393219 (by decide +kernel)
private theorem contact26ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact26) 92 4 = 62360561157 :=
  contactColumnsWindow_fast contact26 92 4 62360561157 (by decide +kernel)
private theorem contact26ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact26) 96 4 = 42671186095 :=
  contactColumnsWindow_fast contact26 96 4 42671186095 (by decide +kernel)
private theorem contact26ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact26) 100 4 = 27518000682 :=
  contactColumnsWindow_fast contact26 100 4 27518000682 (by decide +kernel)
private theorem contact26ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact26) 104 2 = 9387173241 :=
  contactColumnsWindow_fast contact26 104 2 9387173241 (by decide +kernel)
private theorem contact26ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact26) 0 8 = 3580651221924 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 4 4 1856068799186 1724582422738 contact26ColumnsSlice0 contact26ColumnsSlice4
private theorem contact26ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact26) 8 8 = 3074130010781 :=
  combineSlices (auxiliaryColumnSlice contact26) 8 4 4 1597948860690 1476181150091 contact26ColumnsSlice8 contact26ColumnsSlice12
private theorem contact26ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact26) 16 8 = 2606558215358 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 4 4 1359294590902 1247263624456 contact26ColumnsSlice16 contact26ColumnsSlice20
private theorem contact26ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact26) 24 8 = 2177855781974 :=
  combineSlices (auxiliaryColumnSlice contact26) 24 4 4 1140088019576 1037767762398 contact26ColumnsSlice24 contact26ColumnsSlice28
private theorem contact26ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact26) 32 8 = 1788070008921 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 4 4 940318519565 847751489356 contact26ColumnsSlice32 contact26ColumnsSlice36
private theorem contact26ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact26) 40 8 = 1437226813912 :=
  combineSlices (auxiliaryColumnSlice contact26) 40 4 4 760041109986 677185703926 contact26ColumnsSlice40 contact26ColumnsSlice44
private theorem contact26ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact26) 48 8 = 1125247081280 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 4 4 599186030676 526061050604 contact26ColumnsSlice48 contact26ColumnsSlice52
private theorem contact26ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact26) 56 8 = 852239277126 :=
  combineSlices (auxiliaryColumnSlice contact26) 56 4 4 457814534710 394424742416 contact26ColumnsSlice56 contact26ColumnsSlice60
private theorem contact26ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact26) 64 8 = 618100065697 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 4 4 335889619843 282210445854 contact26ColumnsSlice64 contact26ColumnsSlice68
private theorem contact26ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact26) 72 8 = 422893538081 :=
  combineSlices (auxiliaryColumnSlice contact26) 72 4 4 233409728543 189483809538 contact26ColumnsSlice72 contact26ColumnsSlice76
private theorem contact26ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact26) 80 8 = 266614204406 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 4 4 150414521746 116199682660 contact26ColumnsSlice80 contact26ColumnsSlice84
private theorem contact26ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact26) 88 8 = 149201954376 :=
  combineSlices (auxiliaryColumnSlice contact26) 88 4 4 86841393219 62360561157 contact26ColumnsSlice88 contact26ColumnsSlice92
private theorem contact26ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact26) 96 8 = 70189186777 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 4 4 42671186095 27518000682 contact26ColumnsSlice96 contact26ColumnsSlice100
private theorem contact26ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact26) 0 16 = 6654781232705 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 8 8 3580651221924 3074130010781 contact26ColumnsJoin0_8 contact26ColumnsJoin8_8
private theorem contact26ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact26) 16 16 = 4784413997332 :=
  combineSlices (auxiliaryColumnSlice contact26) 16 8 8 2606558215358 2177855781974 contact26ColumnsJoin16_8 contact26ColumnsJoin24_8
private theorem contact26ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact26) 32 16 = 3225296822833 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 8 8 1788070008921 1437226813912 contact26ColumnsJoin32_8 contact26ColumnsJoin40_8
private theorem contact26ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact26) 48 16 = 1977486358406 :=
  combineSlices (auxiliaryColumnSlice contact26) 48 8 8 1125247081280 852239277126 contact26ColumnsJoin48_8 contact26ColumnsJoin56_8
private theorem contact26ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact26) 64 16 = 1040993603778 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 8 8 618100065697 422893538081 contact26ColumnsJoin64_8 contact26ColumnsJoin72_8
private theorem contact26ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact26) 80 16 = 415816158782 :=
  combineSlices (auxiliaryColumnSlice contact26) 80 8 8 266614204406 149201954376 contact26ColumnsJoin80_8 contact26ColumnsJoin88_8
private theorem contact26ColumnsJoin96_10 : sliceWindow (auxiliaryColumnSlice contact26) 96 10 = 79576360018 :=
  combineSlices (auxiliaryColumnSlice contact26) 96 8 2 70189186777 9387173241 contact26ColumnsJoin96_8 contact26ColumnsSlice104
private theorem contact26ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact26) 0 32 = 11439195230037 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 16 16 6654781232705 4784413997332 contact26ColumnsJoin0_16 contact26ColumnsJoin16_16
private theorem contact26ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact26) 32 32 = 5202783181239 :=
  combineSlices (auxiliaryColumnSlice contact26) 32 16 16 3225296822833 1977486358406 contact26ColumnsJoin32_16 contact26ColumnsJoin48_16
private theorem contact26ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact26) 64 32 = 1456809762560 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 16 16 1040993603778 415816158782 contact26ColumnsJoin64_16 contact26ColumnsJoin80_16
private theorem contact26ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact26) 0 64 = 16641978411276 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 32 32 11439195230037 5202783181239 contact26ColumnsJoin0_32 contact26ColumnsJoin32_32
private theorem contact26ColumnsJoin64_42 : sliceWindow (auxiliaryColumnSlice contact26) 64 42 = 1536386122578 :=
  combineSlices (auxiliaryColumnSlice contact26) 64 32 10 1456809762560 79576360018 contact26ColumnsJoin64_32 contact26ColumnsJoin96_10
private theorem contact26ColumnsJoin0_106 : sliceWindow (auxiliaryColumnSlice contact26) 0 106 = 18178364533854 :=
  combineSlices (auxiliaryColumnSlice contact26) 0 64 42 16641978411276 1536386122578 contact26ColumnsJoin0_64 contact26ColumnsJoin64_42
private theorem contact26OrdinaryRanks : ordinaryRankBound contact26 = 637730363 := by decide +kernel
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
  margin_of_checked_counts contact26 106 163506459879357 18178364533854 637730363 55339464 rfl contact26OrdinaryColumns contact26ColumnsJoin0_106 contact26OrdinaryRanks contact26RanksJoin0_106 (by decide +kernel)

private theorem contact28OrdinaryColumns : ordinaryColumnCount contact28 = 218364758290866 := by decide +kernel
private theorem contact28ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact28) 0 4 = 898941873334 :=
  contactColumnsWindow_fast contact28 0 4 898941873334 (by decide +kernel)
private theorem contact28ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact28) 4 4 = 823732670966 :=
  contactColumnsWindow_fast contact28 4 4 823732670966 (by decide +kernel)
private theorem contact28ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact28) 8 4 = 751824064883 :=
  contactColumnsWindow_fast contact28 8 4 751824064883 (by decide +kernel)
private theorem contact28ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact28) 12 4 = 683233568658 :=
  contactColumnsWindow_fast contact28 12 4 683233568658 (by decide +kernel)
private theorem contact28ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact28) 16 4 = 617951243875 :=
  contactColumnsWindow_fast contact28 16 4 617951243875 (by decide +kernel)
private theorem contact28ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact28) 20 4 = 555971449916 :=
  contactColumnsWindow_fast contact28 20 4 555971449916 (by decide +kernel)
private theorem contact28ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact28) 24 4 = 497292725053 :=
  contactColumnsWindow_fast contact28 24 4 497292725053 (by decide +kernel)
private theorem contact28ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact28) 28 4 = 441918033923 :=
  contactColumnsWindow_fast contact28 28 4 441918033923 (by decide +kernel)
private theorem contact28ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact28) 32 4 = 389863940364 :=
  contactColumnsWindow_fast contact28 32 4 389863940364 (by decide +kernel)
private theorem contact28ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact28) 36 4 = 341119238557 :=
  contactColumnsWindow_fast contact28 36 4 341119238557 (by decide +kernel)
private theorem contact28ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact28) 40 4 = 295677343526 :=
  contactColumnsWindow_fast contact28 40 4 295677343526 (by decide +kernel)
private theorem contact28ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact28) 44 4 = 253536513701 :=
  contactColumnsWindow_fast contact28 44 4 253536513701 (by decide +kernel)
private theorem contact28ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact28) 48 4 = 214700613798 :=
  contactColumnsWindow_fast contact28 48 4 214700613798 (by decide +kernel)
private theorem contact28ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact28) 52 4 = 179186150533 :=
  contactColumnsWindow_fast contact28 52 4 179186150533 (by decide +kernel)
private theorem contact28ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact28) 56 4 = 146979427057 :=
  contactColumnsWindow_fast contact28 56 4 146979427057 (by decide +kernel)
private theorem contact28ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact28) 60 4 = 118075417028 :=
  contactColumnsWindow_fast contact28 60 4 118075417028 (by decide +kernel)
private theorem contact28ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact28) 64 4 = 92472533376 :=
  contactColumnsWindow_fast contact28 64 4 92472533376 (by decide +kernel)
private theorem contact28ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact28) 68 4 = 70175741912 :=
  contactColumnsWindow_fast contact28 68 4 70175741912 (by decide +kernel)
private theorem contact28ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact28) 72 4 = 51200541090 :=
  contactColumnsWindow_fast contact28 72 4 51200541090 (by decide +kernel)
private theorem contact28ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact28) 76 4 = 35531764446 :=
  contactColumnsWindow_fast contact28 76 4 35531764446 (by decide +kernel)
private theorem contact28ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact28) 80 4 = 23149772790 :=
  contactColumnsWindow_fast contact28 80 4 23149772790 (by decide +kernel)
private theorem contact28ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact28) 84 4 = 13925092044 :=
  contactColumnsWindow_fast contact28 84 4 13925092044 (by decide +kernel)
private theorem contact28ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact28) 88 4 = 7564704148 :=
  contactColumnsWindow_fast contact28 88 4 7564704148 (by decide +kernel)
private theorem contact28ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact28) 92 4 = 3614459077 :=
  contactColumnsWindow_fast contact28 92 4 3614459077 (by decide +kernel)
private theorem contact28ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact28) 0 8 = 1722674544300 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 4 4 898941873334 823732670966 contact28ColumnsSlice0 contact28ColumnsSlice4
private theorem contact28ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact28) 8 8 = 1435057633541 :=
  combineSlices (auxiliaryColumnSlice contact28) 8 4 4 751824064883 683233568658 contact28ColumnsSlice8 contact28ColumnsSlice12
private theorem contact28ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact28) 16 8 = 1173922693791 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 4 4 617951243875 555971449916 contact28ColumnsSlice16 contact28ColumnsSlice20
private theorem contact28ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact28) 24 8 = 939210758976 :=
  combineSlices (auxiliaryColumnSlice contact28) 24 4 4 497292725053 441918033923 contact28ColumnsSlice24 contact28ColumnsSlice28
private theorem contact28ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact28) 32 8 = 730983178921 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 4 4 389863940364 341119238557 contact28ColumnsSlice32 contact28ColumnsSlice36
private theorem contact28ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact28) 40 8 = 549213857227 :=
  combineSlices (auxiliaryColumnSlice contact28) 40 4 4 295677343526 253536513701 contact28ColumnsSlice40 contact28ColumnsSlice44
private theorem contact28ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact28) 48 8 = 393886764331 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 4 4 214700613798 179186150533 contact28ColumnsSlice48 contact28ColumnsSlice52
private theorem contact28ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact28) 56 8 = 265054844085 :=
  combineSlices (auxiliaryColumnSlice contact28) 56 4 4 146979427057 118075417028 contact28ColumnsSlice56 contact28ColumnsSlice60
private theorem contact28ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact28) 64 8 = 162648275288 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 4 4 92472533376 70175741912 contact28ColumnsSlice64 contact28ColumnsSlice68
private theorem contact28ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact28) 72 8 = 86732305536 :=
  combineSlices (auxiliaryColumnSlice contact28) 72 4 4 51200541090 35531764446 contact28ColumnsSlice72 contact28ColumnsSlice76
private theorem contact28ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact28) 80 8 = 37074864834 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 4 4 23149772790 13925092044 contact28ColumnsSlice80 contact28ColumnsSlice84
private theorem contact28ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact28) 88 8 = 11179163225 :=
  combineSlices (auxiliaryColumnSlice contact28) 88 4 4 7564704148 3614459077 contact28ColumnsSlice88 contact28ColumnsSlice92
private theorem contact28ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact28) 0 16 = 3157732177841 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 8 8 1722674544300 1435057633541 contact28ColumnsJoin0_8 contact28ColumnsJoin8_8
private theorem contact28ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact28) 16 16 = 2113133452767 :=
  combineSlices (auxiliaryColumnSlice contact28) 16 8 8 1173922693791 939210758976 contact28ColumnsJoin16_8 contact28ColumnsJoin24_8
private theorem contact28ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact28) 32 16 = 1280197036148 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 8 8 730983178921 549213857227 contact28ColumnsJoin32_8 contact28ColumnsJoin40_8
private theorem contact28ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact28) 48 16 = 658941608416 :=
  combineSlices (auxiliaryColumnSlice contact28) 48 8 8 393886764331 265054844085 contact28ColumnsJoin48_8 contact28ColumnsJoin56_8
private theorem contact28ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact28) 64 16 = 249380580824 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 8 8 162648275288 86732305536 contact28ColumnsJoin64_8 contact28ColumnsJoin72_8
private theorem contact28ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact28) 80 16 = 48254028059 :=
  combineSlices (auxiliaryColumnSlice contact28) 80 8 8 37074864834 11179163225 contact28ColumnsJoin80_8 contact28ColumnsJoin88_8
private theorem contact28ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact28) 0 32 = 5270865630608 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 16 16 3157732177841 2113133452767 contact28ColumnsJoin0_16 contact28ColumnsJoin16_16
private theorem contact28ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact28) 32 32 = 1939138644564 :=
  combineSlices (auxiliaryColumnSlice contact28) 32 16 16 1280197036148 658941608416 contact28ColumnsJoin32_16 contact28ColumnsJoin48_16
private theorem contact28ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact28) 64 32 = 297634608883 :=
  combineSlices (auxiliaryColumnSlice contact28) 64 16 16 249380580824 48254028059 contact28ColumnsJoin64_16 contact28ColumnsJoin80_16
private theorem contact28ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact28) 0 64 = 7210004275172 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 32 32 5270865630608 1939138644564 contact28ColumnsJoin0_32 contact28ColumnsJoin32_32
private theorem contact28ColumnsJoin0_96 : sliceWindow (auxiliaryColumnSlice contact28) 0 96 = 7507638884055 :=
  combineSlices (auxiliaryColumnSlice contact28) 0 64 32 7210004275172 297634608883 contact28ColumnsJoin0_64 contact28ColumnsJoin64_32
private theorem contact28OrdinaryRanks : ordinaryRankBound contact28 = 838766654 := by decide +kernel
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
private theorem contact28RanksSlice88 : sliceWindow (auxiliaryRankSlice contact28) 88 8 = 0 :=
  contactRankWindow_of_rec contact28 88 8 0 (by decide +kernel)
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
private theorem contact28RanksJoin80_16 : sliceWindow (auxiliaryRankSlice contact28) 80 16 = 6663 :=
  combineSlices (auxiliaryRankSlice contact28) 80 8 8 6663 0 contact28RanksJoin80_8 contact28RanksSlice88
private theorem contact28RanksJoin0_32 : sliceWindow (auxiliaryRankSlice contact28) 0 32 = 17989119 :=
  combineSlices (auxiliaryRankSlice contact28) 0 16 16 11370760 6618359 contact28RanksJoin0_16 contact28RanksJoin16_16
private theorem contact28RanksJoin32_32 : sliceWindow (auxiliaryRankSlice contact28) 32 32 = 4592360 :=
  combineSlices (auxiliaryRankSlice contact28) 32 16 16 3308195 1284165 contact28RanksJoin32_16 contact28RanksJoin48_16
private theorem contact28RanksJoin64_32 : sliceWindow (auxiliaryRankSlice contact28) 64 32 = 286599 :=
  combineSlices (auxiliaryRankSlice contact28) 64 16 16 279936 6663 contact28RanksJoin64_16 contact28RanksJoin80_16
private theorem contact28RanksJoin0_64 : sliceWindow (auxiliaryRankSlice contact28) 0 64 = 22581479 :=
  combineSlices (auxiliaryRankSlice contact28) 0 32 32 17989119 4592360 contact28RanksJoin0_32 contact28RanksJoin32_32
private theorem contact28RanksJoin0_96 : sliceWindow (auxiliaryRankSlice contact28) 0 96 = 22868078 :=
  combineSlices (auxiliaryRankSlice contact28) 0 64 32 22581479 286599 contact28RanksJoin0_64 contact28RanksJoin64_32
theorem contact28_margin : sourceMargin contact28 :=
  margin_of_checked_counts contact28 96 218364758290866 7507638884055 838766654 22868078 rfl contact28OrdinaryColumns contact28ColumnsJoin0_96 contact28OrdinaryRanks contact28RanksJoin0_96 (by decide +kernel)

private theorem contact30OrdinaryColumns : ordinaryColumnCount contact30 = 529088552861785 := by decide +kernel
private theorem contact30ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact30) 0 4 = 1936664522357 :=
  contactColumnsWindow_fast contact30 0 4 1936664522357 (by decide +kernel)
private theorem contact30ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact30) 4 4 = 1802292376348 :=
  contactColumnsWindow_fast contact30 4 4 1802292376348 (by decide +kernel)
private theorem contact30ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact30) 8 4 = 1672775432070 :=
  contactColumnsWindow_fast contact30 8 4 1672775432070 (by decide +kernel)
private theorem contact30ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact30) 12 4 = 1548113563334 :=
  contactColumnsWindow_fast contact30 12 4 1548113563334 (by decide +kernel)
private theorem contact30ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact30) 16 4 = 1428307094540 :=
  contactColumnsWindow_fast contact30 16 4 1428307094540 (by decide +kernel)
private theorem contact30ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact30) 20 4 = 1313371314506 :=
  contactColumnsWindow_fast contact30 20 4 1313371314506 (by decide +kernel)
private theorem contact30ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact30) 24 4 = 1203313629760 :=
  contactColumnsWindow_fast contact30 24 4 1203313629760 (by decide +kernel)
private theorem contact30ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact30) 28 4 = 1098112720626 :=
  contactColumnsWindow_fast contact30 28 4 1098112720626 (by decide +kernel)
private theorem contact30ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact30) 32 4 = 997770119877 :=
  contactColumnsWindow_fast contact30 32 4 997770119877 (by decide +kernel)
private theorem contact30ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact30) 36 4 = 902284173502 :=
  contactColumnsWindow_fast contact30 36 4 902284173502 (by decide +kernel)
private theorem contact30ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact30) 40 4 = 811672259807 :=
  contactColumnsWindow_fast contact30 40 4 811672259807 (by decide +kernel)
private theorem contact30ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact30) 44 4 = 725935095460 :=
  contactColumnsWindow_fast contact30 44 4 725935095460 (by decide +kernel)
private theorem contact30ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact30) 48 4 = 645054934467 :=
  contactColumnsWindow_fast contact30 48 4 645054934467 (by decide +kernel)
private theorem contact30ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact30) 52 4 = 569032861532 :=
  contactColumnsWindow_fast contact30 52 4 569032861532 (by decide +kernel)
private theorem contact30ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact30) 56 4 = 497867399364 :=
  contactColumnsWindow_fast contact30 56 4 497867399364 (by decide +kernel)
private theorem contact30ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact30) 60 4 = 431579392901 :=
  contactColumnsWindow_fast contact30 60 4 431579392901 (by decide +kernel)
private theorem contact30ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact30) 64 4 = 370162784773 :=
  contactColumnsWindow_fast contact30 64 4 370162784773 (by decide +kernel)
private theorem contact30ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact30) 68 4 = 313603318743 :=
  contactColumnsWindow_fast contact30 68 4 313603318743 (by decide +kernel)
private theorem contact30ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact30) 72 4 = 261901750087 :=
  contactColumnsWindow_fast contact30 72 4 261901750087 (by decide +kernel)
private theorem contact30ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact30) 76 4 = 215057489798 :=
  contactColumnsWindow_fast contact30 76 4 215057489798 (by decide +kernel)
private theorem contact30ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact30) 80 4 = 173092739889 :=
  contactColumnsWindow_fast contact30 80 4 173092739889 (by decide +kernel)
private theorem contact30ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact30) 84 4 = 135996620986 :=
  contactColumnsWindow_fast contact30 84 4 135996620986 (by decide +kernel)
private theorem contact30ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact30) 88 4 = 103757864544 :=
  contactColumnsWindow_fast contact30 88 4 103757864544 (by decide +kernel)
private theorem contact30ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact30) 92 4 = 76376844590 :=
  contactColumnsWindow_fast contact30 92 4 76376844590 (by decide +kernel)
private theorem contact30ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact30) 96 4 = 53838147926 :=
  contactColumnsWindow_fast contact30 96 4 53838147926 (by decide +kernel)
private theorem contact30ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact30) 100 4 = 36031316425 :=
  contactColumnsWindow_fast contact30 100 4 36031316425 (by decide +kernel)
private theorem contact30ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact30) 104 4 = 22627759684 :=
  contactColumnsWindow_fast contact30 104 4 22627759684 (by decide +kernel)
private theorem contact30ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact30) 108 4 = 13141874162 :=
  contactColumnsWindow_fast contact30 108 4 13141874162 (by decide +kernel)
private theorem contact30ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact30) 112 3 = 5632562291 :=
  contactColumnsWindow_fast contact30 112 3 5632562291 (by decide +kernel)
private theorem contact30ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact30) 0 8 = 3738956898705 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 4 4 1936664522357 1802292376348 contact30ColumnsSlice0 contact30ColumnsSlice4
private theorem contact30ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact30) 8 8 = 3220888995404 :=
  combineSlices (auxiliaryColumnSlice contact30) 8 4 4 1672775432070 1548113563334 contact30ColumnsSlice8 contact30ColumnsSlice12
private theorem contact30ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact30) 16 8 = 2741678409046 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 4 4 1428307094540 1313371314506 contact30ColumnsSlice16 contact30ColumnsSlice20
private theorem contact30ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact30) 24 8 = 2301426350386 :=
  combineSlices (auxiliaryColumnSlice contact30) 24 4 4 1203313629760 1098112720626 contact30ColumnsSlice24 contact30ColumnsSlice28
private theorem contact30ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact30) 32 8 = 1900054293379 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 4 4 997770119877 902284173502 contact30ColumnsSlice32 contact30ColumnsSlice36
private theorem contact30ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact30) 40 8 = 1537607355267 :=
  combineSlices (auxiliaryColumnSlice contact30) 40 4 4 811672259807 725935095460 contact30ColumnsSlice40 contact30ColumnsSlice44
private theorem contact30ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact30) 48 8 = 1214087795999 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 4 4 645054934467 569032861532 contact30ColumnsSlice48 contact30ColumnsSlice52
private theorem contact30ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact30) 56 8 = 929446792265 :=
  combineSlices (auxiliaryColumnSlice contact30) 56 4 4 497867399364 431579392901 contact30ColumnsSlice56 contact30ColumnsSlice60
private theorem contact30ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact30) 64 8 = 683766103516 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 4 4 370162784773 313603318743 contact30ColumnsSlice64 contact30ColumnsSlice68
private theorem contact30ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact30) 72 8 = 476959239885 :=
  combineSlices (auxiliaryColumnSlice contact30) 72 4 4 261901750087 215057489798 contact30ColumnsSlice72 contact30ColumnsSlice76
private theorem contact30ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact30) 80 8 = 309089360875 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 4 4 173092739889 135996620986 contact30ColumnsSlice80 contact30ColumnsSlice84
private theorem contact30ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact30) 88 8 = 180134709134 :=
  combineSlices (auxiliaryColumnSlice contact30) 88 4 4 103757864544 76376844590 contact30ColumnsSlice88 contact30ColumnsSlice92
private theorem contact30ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact30) 96 8 = 89869464351 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 4 4 53838147926 36031316425 contact30ColumnsSlice96 contact30ColumnsSlice100
private theorem contact30ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact30) 104 8 = 35769633846 :=
  combineSlices (auxiliaryColumnSlice contact30) 104 4 4 22627759684 13141874162 contact30ColumnsSlice104 contact30ColumnsSlice108
private theorem contact30ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact30) 0 16 = 6959845894109 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 8 8 3738956898705 3220888995404 contact30ColumnsJoin0_8 contact30ColumnsJoin8_8
private theorem contact30ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact30) 16 16 = 5043104759432 :=
  combineSlices (auxiliaryColumnSlice contact30) 16 8 8 2741678409046 2301426350386 contact30ColumnsJoin16_8 contact30ColumnsJoin24_8
private theorem contact30ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact30) 32 16 = 3437661648646 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 8 8 1900054293379 1537607355267 contact30ColumnsJoin32_8 contact30ColumnsJoin40_8
private theorem contact30ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact30) 48 16 = 2143534588264 :=
  combineSlices (auxiliaryColumnSlice contact30) 48 8 8 1214087795999 929446792265 contact30ColumnsJoin48_8 contact30ColumnsJoin56_8
private theorem contact30ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact30) 64 16 = 1160725343401 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 8 8 683766103516 476959239885 contact30ColumnsJoin64_8 contact30ColumnsJoin72_8
private theorem contact30ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact30) 80 16 = 489224070009 :=
  combineSlices (auxiliaryColumnSlice contact30) 80 8 8 309089360875 180134709134 contact30ColumnsJoin80_8 contact30ColumnsJoin88_8
private theorem contact30ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact30) 96 16 = 125639098197 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 8 8 89869464351 35769633846 contact30ColumnsJoin96_8 contact30ColumnsJoin104_8
private theorem contact30ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact30) 0 32 = 12002950653541 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 16 16 6959845894109 5043104759432 contact30ColumnsJoin0_16 contact30ColumnsJoin16_16
private theorem contact30ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact30) 32 32 = 5581196236910 :=
  combineSlices (auxiliaryColumnSlice contact30) 32 16 16 3437661648646 2143534588264 contact30ColumnsJoin32_16 contact30ColumnsJoin48_16
private theorem contact30ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact30) 64 32 = 1649949413410 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 16 16 1160725343401 489224070009 contact30ColumnsJoin64_16 contact30ColumnsJoin80_16
private theorem contact30ColumnsJoin96_19 : sliceWindow (auxiliaryColumnSlice contact30) 96 19 = 131271660488 :=
  combineSlices (auxiliaryColumnSlice contact30) 96 16 3 125639098197 5632562291 contact30ColumnsJoin96_16 contact30ColumnsSlice112
private theorem contact30ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact30) 0 64 = 17584146890451 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 32 32 12002950653541 5581196236910 contact30ColumnsJoin0_32 contact30ColumnsJoin32_32
private theorem contact30ColumnsJoin64_51 : sliceWindow (auxiliaryColumnSlice contact30) 64 51 = 1781221073898 :=
  combineSlices (auxiliaryColumnSlice contact30) 64 32 19 1649949413410 131271660488 contact30ColumnsJoin64_32 contact30ColumnsJoin96_19
private theorem contact30ColumnsJoin0_115 : sliceWindow (auxiliaryColumnSlice contact30) 0 115 = 19365367964349 :=
  combineSlices (auxiliaryColumnSlice contact30) 0 64 51 17584146890451 1781221073898 contact30ColumnsJoin0_64 contact30ColumnsJoin64_51
private theorem contact30OrdinaryRanks : ordinaryRankBound contact30 = 2033120280 := by decide +kernel
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
  margin_of_checked_counts contact30 115 529088552861785 19365367964349 2033120280 59063991 rfl contact30OrdinaryColumns contact30ColumnsJoin0_115 contact30OrdinaryRanks contact30RanksJoin0_115 (by decide +kernel)

private theorem contact32OrdinaryColumns : ordinaryColumnCount contact32 = 542573258134607 := by decide +kernel
private theorem contact32ColumnsSlice0 : sliceWindow (auxiliaryColumnSlice contact32) 0 4 = 1997681456335 :=
  contactColumnsWindow_fast contact32 0 4 1997681456335 (by decide +kernel)
private theorem contact32ColumnsSlice4 : sliceWindow (auxiliaryColumnSlice contact32) 4 4 = 1858542145126 :=
  contactColumnsWindow_fast contact32 4 4 1858542145126 (by decide +kernel)
private theorem contact32ColumnsSlice8 : sliceWindow (auxiliaryColumnSlice contact32) 8 4 = 1724452220150 :=
  contactColumnsWindow_fast contact32 8 4 1724452220150 (by decide +kernel)
private theorem contact32ColumnsSlice12 : sliceWindow (auxiliaryColumnSlice contact32) 12 4 = 1595411541350 :=
  contactColumnsWindow_fast contact32 12 4 1595411541350 (by decide +kernel)
private theorem contact32ColumnsSlice16 : sliceWindow (auxiliaryColumnSlice contact32) 16 4 = 1471420438046 :=
  contactColumnsWindow_fast contact32 16 4 1471420438046 (by decide +kernel)
private theorem contact32ColumnsSlice20 : sliceWindow (auxiliaryColumnSlice contact32) 20 4 = 1352494941944 :=
  contactColumnsWindow_fast contact32 20 4 1352494941944 (by decide +kernel)
private theorem contact32ColumnsSlice24 : sliceWindow (auxiliaryColumnSlice contact32) 24 4 = 1238642782974 :=
  contactColumnsWindow_fast contact32 24 4 1238642782974 (by decide +kernel)
private theorem contact32ColumnsSlice28 : sliceWindow (auxiliaryColumnSlice contact32) 28 4 = 1129841609471 :=
  contactColumnsWindow_fast contact32 28 4 1129841609471 (by decide +kernel)
private theorem contact32ColumnsSlice32 : sliceWindow (auxiliaryColumnSlice contact32) 32 4 = 1026092985563 :=
  contactColumnsWindow_fast contact32 32 4 1026092985563 (by decide +kernel)
private theorem contact32ColumnsSlice36 : sliceWindow (auxiliaryColumnSlice contact32) 36 4 = 927395220182 :=
  contactColumnsWindow_fast contact32 36 4 927395220182 (by decide +kernel)
private theorem contact32ColumnsSlice40 : sliceWindow (auxiliaryColumnSlice contact32) 40 4 = 833766570564 :=
  contactColumnsWindow_fast contact32 40 4 833766570564 (by decide +kernel)
private theorem contact32ColumnsSlice44 : sliceWindow (auxiliaryColumnSlice contact32) 44 4 = 745207747066 :=
  contactColumnsWindow_fast contact32 44 4 745207747066 (by decide +kernel)
private theorem contact32ColumnsSlice48 : sliceWindow (auxiliaryColumnSlice contact32) 48 4 = 661700142714 :=
  contactColumnsWindow_fast contact32 48 4 661700142714 (by decide +kernel)
private theorem contact32ColumnsSlice52 : sliceWindow (auxiliaryColumnSlice contact32) 52 4 = 583244861717 :=
  contactColumnsWindow_fast contact32 52 4 583244861717 (by decide +kernel)
private theorem contact32ColumnsSlice56 : sliceWindow (auxiliaryColumnSlice contact32) 56 4 = 509840395094 :=
  contactColumnsWindow_fast contact32 56 4 509840395094 (by decide +kernel)
private theorem contact32ColumnsSlice60 : sliceWindow (auxiliaryColumnSlice contact32) 60 4 = 441508633782 :=
  contactColumnsWindow_fast contact32 60 4 441508633782 (by decide +kernel)
private theorem contact32ColumnsSlice64 : sliceWindow (auxiliaryColumnSlice contact32) 64 4 = 378243182634 :=
  contactColumnsWindow_fast contact32 64 4 378243182634 (by decide +kernel)
private theorem contact32ColumnsSlice68 : sliceWindow (auxiliaryColumnSlice contact32) 68 4 = 320029092814 :=
  contactColumnsWindow_fast contact32 68 4 320029092814 (by decide +kernel)
private theorem contact32ColumnsSlice72 : sliceWindow (auxiliaryColumnSlice contact32) 72 4 = 266867130647 :=
  contactColumnsWindow_fast contact32 72 4 266867130647 (by decide +kernel)
private theorem contact32ColumnsSlice76 : sliceWindow (auxiliaryColumnSlice contact32) 76 4 = 218756714403 :=
  contactColumnsWindow_fast contact32 76 4 218756714403 (by decide +kernel)
private theorem contact32ColumnsSlice80 : sliceWindow (auxiliaryColumnSlice contact32) 80 4 = 175721158350 :=
  contactColumnsWindow_fast contact32 80 4 175721158350 (by decide +kernel)
private theorem contact32ColumnsSlice84 : sliceWindow (auxiliaryColumnSlice contact32) 84 4 = 137749010978 :=
  contactColumnsWindow_fast contact32 84 4 137749010978 (by decide +kernel)
private theorem contact32ColumnsSlice88 : sliceWindow (auxiliaryColumnSlice contact32) 88 4 = 104828450617 :=
  contactColumnsWindow_fast contact32 88 4 104828450617 (by decide +kernel)
private theorem contact32ColumnsSlice92 : sliceWindow (auxiliaryColumnSlice contact32) 92 4 = 76959508937 :=
  contactColumnsWindow_fast contact32 92 4 76959508937 (by decide +kernel)
private theorem contact32ColumnsSlice96 : sliceWindow (auxiliaryColumnSlice contact32) 96 4 = 54111074268 :=
  contactColumnsWindow_fast contact32 96 4 54111074268 (by decide +kernel)
private theorem contact32ColumnsSlice100 : sliceWindow (auxiliaryColumnSlice contact32) 100 4 = 36131044429 :=
  contactColumnsWindow_fast contact32 100 4 36131044429 (by decide +kernel)
private theorem contact32ColumnsSlice104 : sliceWindow (auxiliaryColumnSlice contact32) 104 4 = 22649972856 :=
  contactColumnsWindow_fast contact32 104 4 22649972856 (by decide +kernel)
private theorem contact32ColumnsSlice108 : sliceWindow (auxiliaryColumnSlice contact32) 108 4 = 13143160662 :=
  contactColumnsWindow_fast contact32 108 4 13143160662 (by decide +kernel)
private theorem contact32ColumnsSlice112 : sliceWindow (auxiliaryColumnSlice contact32) 112 2 = 4067831399 :=
  contactColumnsWindow_fast contact32 112 2 4067831399 (by decide +kernel)
private theorem contact32ColumnsJoin0_8 : sliceWindow (auxiliaryColumnSlice contact32) 0 8 = 3856223601461 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 4 4 1997681456335 1858542145126 contact32ColumnsSlice0 contact32ColumnsSlice4
private theorem contact32ColumnsJoin8_8 : sliceWindow (auxiliaryColumnSlice contact32) 8 8 = 3319863761500 :=
  combineSlices (auxiliaryColumnSlice contact32) 8 4 4 1724452220150 1595411541350 contact32ColumnsSlice8 contact32ColumnsSlice12
private theorem contact32ColumnsJoin16_8 : sliceWindow (auxiliaryColumnSlice contact32) 16 8 = 2823915379990 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 4 4 1471420438046 1352494941944 contact32ColumnsSlice16 contact32ColumnsSlice20
private theorem contact32ColumnsJoin24_8 : sliceWindow (auxiliaryColumnSlice contact32) 24 8 = 2368484392445 :=
  combineSlices (auxiliaryColumnSlice contact32) 24 4 4 1238642782974 1129841609471 contact32ColumnsSlice24 contact32ColumnsSlice28
private theorem contact32ColumnsJoin32_8 : sliceWindow (auxiliaryColumnSlice contact32) 32 8 = 1953488205745 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 4 4 1026092985563 927395220182 contact32ColumnsSlice32 contact32ColumnsSlice36
private theorem contact32ColumnsJoin40_8 : sliceWindow (auxiliaryColumnSlice contact32) 40 8 = 1578974317630 :=
  combineSlices (auxiliaryColumnSlice contact32) 40 4 4 833766570564 745207747066 contact32ColumnsSlice40 contact32ColumnsSlice44
private theorem contact32ColumnsJoin48_8 : sliceWindow (auxiliaryColumnSlice contact32) 48 8 = 1244945004431 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 4 4 661700142714 583244861717 contact32ColumnsSlice48 contact32ColumnsSlice52
private theorem contact32ColumnsJoin56_8 : sliceWindow (auxiliaryColumnSlice contact32) 56 8 = 951349028876 :=
  combineSlices (auxiliaryColumnSlice contact32) 56 4 4 509840395094 441508633782 contact32ColumnsSlice56 contact32ColumnsSlice60
private theorem contact32ColumnsJoin64_8 : sliceWindow (auxiliaryColumnSlice contact32) 64 8 = 698272275448 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 4 4 378243182634 320029092814 contact32ColumnsSlice64 contact32ColumnsSlice68
private theorem contact32ColumnsJoin72_8 : sliceWindow (auxiliaryColumnSlice contact32) 72 8 = 485623845050 :=
  combineSlices (auxiliaryColumnSlice contact32) 72 4 4 266867130647 218756714403 contact32ColumnsSlice72 contact32ColumnsSlice76
private theorem contact32ColumnsJoin80_8 : sliceWindow (auxiliaryColumnSlice contact32) 80 8 = 313470169328 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 4 4 175721158350 137749010978 contact32ColumnsSlice80 contact32ColumnsSlice84
private theorem contact32ColumnsJoin88_8 : sliceWindow (auxiliaryColumnSlice contact32) 88 8 = 181787959554 :=
  combineSlices (auxiliaryColumnSlice contact32) 88 4 4 104828450617 76959508937 contact32ColumnsSlice88 contact32ColumnsSlice92
private theorem contact32ColumnsJoin96_8 : sliceWindow (auxiliaryColumnSlice contact32) 96 8 = 90242118697 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 4 4 54111074268 36131044429 contact32ColumnsSlice96 contact32ColumnsSlice100
private theorem contact32ColumnsJoin104_8 : sliceWindow (auxiliaryColumnSlice contact32) 104 8 = 35793133518 :=
  combineSlices (auxiliaryColumnSlice contact32) 104 4 4 22649972856 13143160662 contact32ColumnsSlice104 contact32ColumnsSlice108
private theorem contact32ColumnsJoin0_16 : sliceWindow (auxiliaryColumnSlice contact32) 0 16 = 7176087362961 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 8 8 3856223601461 3319863761500 contact32ColumnsJoin0_8 contact32ColumnsJoin8_8
private theorem contact32ColumnsJoin16_16 : sliceWindow (auxiliaryColumnSlice contact32) 16 16 = 5192399772435 :=
  combineSlices (auxiliaryColumnSlice contact32) 16 8 8 2823915379990 2368484392445 contact32ColumnsJoin16_8 contact32ColumnsJoin24_8
private theorem contact32ColumnsJoin32_16 : sliceWindow (auxiliaryColumnSlice contact32) 32 16 = 3532462523375 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 8 8 1953488205745 1578974317630 contact32ColumnsJoin32_8 contact32ColumnsJoin40_8
private theorem contact32ColumnsJoin48_16 : sliceWindow (auxiliaryColumnSlice contact32) 48 16 = 2196294033307 :=
  combineSlices (auxiliaryColumnSlice contact32) 48 8 8 1244945004431 951349028876 contact32ColumnsJoin48_8 contact32ColumnsJoin56_8
private theorem contact32ColumnsJoin64_16 : sliceWindow (auxiliaryColumnSlice contact32) 64 16 = 1183896120498 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 8 8 698272275448 485623845050 contact32ColumnsJoin64_8 contact32ColumnsJoin72_8
private theorem contact32ColumnsJoin80_16 : sliceWindow (auxiliaryColumnSlice contact32) 80 16 = 495258128882 :=
  combineSlices (auxiliaryColumnSlice contact32) 80 8 8 313470169328 181787959554 contact32ColumnsJoin80_8 contact32ColumnsJoin88_8
private theorem contact32ColumnsJoin96_16 : sliceWindow (auxiliaryColumnSlice contact32) 96 16 = 126035252215 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 8 8 90242118697 35793133518 contact32ColumnsJoin96_8 contact32ColumnsJoin104_8
private theorem contact32ColumnsJoin0_32 : sliceWindow (auxiliaryColumnSlice contact32) 0 32 = 12368487135396 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 16 16 7176087362961 5192399772435 contact32ColumnsJoin0_16 contact32ColumnsJoin16_16
private theorem contact32ColumnsJoin32_32 : sliceWindow (auxiliaryColumnSlice contact32) 32 32 = 5728756556682 :=
  combineSlices (auxiliaryColumnSlice contact32) 32 16 16 3532462523375 2196294033307 contact32ColumnsJoin32_16 contact32ColumnsJoin48_16
private theorem contact32ColumnsJoin64_32 : sliceWindow (auxiliaryColumnSlice contact32) 64 32 = 1679154249380 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 16 16 1183896120498 495258128882 contact32ColumnsJoin64_16 contact32ColumnsJoin80_16
private theorem contact32ColumnsJoin96_18 : sliceWindow (auxiliaryColumnSlice contact32) 96 18 = 130103083614 :=
  combineSlices (auxiliaryColumnSlice contact32) 96 16 2 126035252215 4067831399 contact32ColumnsJoin96_16 contact32ColumnsSlice112
private theorem contact32ColumnsJoin0_64 : sliceWindow (auxiliaryColumnSlice contact32) 0 64 = 18097243692078 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 32 32 12368487135396 5728756556682 contact32ColumnsJoin0_32 contact32ColumnsJoin32_32
private theorem contact32ColumnsJoin64_50 : sliceWindow (auxiliaryColumnSlice contact32) 64 50 = 1809257332994 :=
  combineSlices (auxiliaryColumnSlice contact32) 64 32 18 1679154249380 130103083614 contact32ColumnsJoin64_32 contact32ColumnsJoin96_18
private theorem contact32ColumnsJoin0_114 : sliceWindow (auxiliaryColumnSlice contact32) 0 114 = 19906501025072 :=
  combineSlices (auxiliaryColumnSlice contact32) 0 64 50 18097243692078 1809257332994 contact32ColumnsJoin0_64 contact32ColumnsJoin64_50
private theorem contact32OrdinaryRanks : ordinaryRankBound contact32 = 2084768302 := by decide +kernel
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
  margin_of_checked_counts contact32 114 542573258134607 19906501025072 2084768302 60920817 rfl contact32OrdinaryColumns contact32ColumnsJoin0_114 contact32OrdinaryRanks contact32RanksJoin0_114 (by decide +kernel)

end ProximityPrize.SubmissionLower.Koala6844Receipts
