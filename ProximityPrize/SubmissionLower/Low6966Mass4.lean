import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6966Allocation.Group4

private def m0 : MassCell 4 :=
  ⟨⟨2,6,8⟩,mass_cell 4 2 6 8 190 (by decide)
    (by decide +kernel) [4650400383274, 3837982824048, 3059873359428, 2397490772736, 1840663309476, 1379445963312, 1004120476068, 705195337728, 473405786436, 299713808496, 175308138372, 91604258688, 40244400228, 13097541936, 2259410916, 56516924] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 4 :=
  ⟨⟨3,7,15⟩,mass_cell 4 3 7 15 179 (by decide)
    (by decide +kernel) [4711930693262, 4113694093722, 3214297860052, 2457095064052, 1832568168212, 1326704014132, 925890339412, 616915777652, 386969858452, 223643007412, 114926546132, 49212692212, 15294559252, 2366156852, 38113326] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 4 :=
  ⟨⟨3,9,24⟩,mass_cell 4 3 9 24 160 (by decide)
    (by decide +kernel) [4711930693262, 4358646215871, 3552519857654, 2607965638742, 1850298179510, 1257794695190, 809162382710, 483538420694, 260489969462, 120014171030, 42538149110, 8919009110, 443961001, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 4 :=
  ⟨⟨2,12,32⟩,mass_cell 4 2 12 32 141 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 3930281682411, 2850787013569, 1887979928065, 1169760459841, 661073234497, 326372989633, 129624574849, 34302951745, 3393193921, 2895727] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 4 :=
  ⟨⟨1,15,37⟩,mass_cell 4 1 15 37 127 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3109221096150, 1928688837582, 1087565593926, 532570586430, 207278795190, 52120959150, 4383576102, 350718] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 4 :=
  ⟨⟨5,16,39⟩,mass_cell 4 5 16 39 124 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3243331885968, 1952908705347, 1056823138451, 489065794907, 174076891035, 36628509011, 1825142003, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 4 :=
  ⟨⟨3,18,41⟩,mass_cell 4 3 18 41 118 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3376971293684, 1993321526771, 1017245233019, 425221423859, 123861878939, 15745619891, 87547297] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 4 :=
  ⟨⟨7,21,44⟩,mass_cell 4 7 21 44 111 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3550323116627, 2066302823858, 949307922242, 333227091410, 67864340834, 3027704005, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 4 :=
  ⟨⟨8,24,46⟩,mass_cell 4 8 24 46 106 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3644943186620, 2139358628724, 891148412400, 259892202444, 33591806664, 213113013] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 4 :=
  ⟨⟨1,27,47⟩,mass_cell 4 1 27 47 101 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3682318098718, 2181536417796, 836412473076, 198913081956, 13612196436, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 4 :=
  ⟨⟨1,29,48⟩,mass_cell 4 1 29 48 98 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3710338983552, 2245612304718, 809716187902, 167339514030, 7235808208, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 4 :=
  ⟨⟨4,31,49⟩,mass_cell 4 4 31 49 96 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2318829724161, 781548665365, 139385116425, 3600636934] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 4 :=
  ⟨⟨4,34,50⟩,mass_cell 4 4 34 50 93 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2403772977407, 737086166911, 103065949159, 883259464] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 4 :=
  ⟨⟨1,38,51⟩,mass_cell 4 1 38 51 90 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2489172858864, 683009005488, 66865973068, 34270520] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 4 :=
  ⟨⟨4,42,52⟩,mass_cell 4 4 42 52 87 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2574462045762, 632582822547, 42496828155, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 4 :=
  ⟨⟨10,47,53⟩,mass_cell 4 10 47 53 85 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2655947768530, 570839068565, 22854339652, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 4 :=
  ⟨⟨2,55,54⟩,mass_cell 4 2 55 54 81 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2744600628456, 496956902949, 7317010958] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 4 :=
  ⟨⟨22,5,19⟩,mass_cell 4 22 5 19 224 (by decide)
    (by decide +kernel) [4711930693262, 4250944058712, 3301346411376, 2460400909104, 1789920600304, 1265344255152, 864007517808, 565142906416, 349879813104, 201244503984, 104160119152, 45446672688, 13838415176, 1212686720, 3060, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 4 :=
  ⟨⟨20,36,51⟩,mass_cell 4 20 36 51 92 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2475860487678, 690490380889, 80681696713, 312850115] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 4 :=
  ⟨⟨30,45,53⟩,mass_cell 4 30 45 53 86 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2645211204606, 574993897700, 28524084050, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 4 :=
  ⟨⟨23,53,54⟩,mass_cell 4 23 53 54 82 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2735561966963, 502169477536, 9957893389] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 4 :=
  ⟨⟨47,33,51⟩,mass_cell 4 47 33 51 95 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2455286731698, 689301610644, 97047079428, 1682942926] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 4 :=
  ⟨⟨15,41,52⟩,mass_cell 4 15 41 52 88 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2565759572389, 632981866598, 46863574790, 6325] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 4 :=
  ⟨⟨48,43,53⟩,mass_cell 4 48 43 53 87 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2636782981060, 578058099499, 34292563895, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 4 :=
  ⟨⟨42,51,54⟩,mass_cell 4 42 51 54 83 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2728339968220, 506841837147, 12936845358] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 4 :=
  ⟨⟨63,16,46⟩,mass_cell 4 63 16 46 131 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3640559642918, 2102325874333, 884737138285, 285991236965, 52392851761, 818631946, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 4 :=
  ⟨⟨55,25,49⟩,mass_cell 4 55 25 49 106 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2269601066984, 775982074040, 178975249800, 17849760344, 107761362] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 4 :=
  ⟨⟨34,39,52⟩,mass_cell 4 34 39 52 90 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2553734208972, 636202463177, 56013078845, 28225453] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 4 :=
  ⟨⟨65,4,40⟩,mass_cell 4 65 4 40 274 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3357134988996, 2084825148738, 1099394516174, 381578222010, 21408232729, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 4 :=
  ⟨⟨63,27,50⟩,mass_cell 4 63 27 50 104 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2356696784924, 733742570708, 142456516172, 9470595716, 5370914] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 4 :=
  ⟨⟨62,31,51⟩,mass_cell 4 62 31 51 98 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2447589930275, 688155360297, 104381229621, 3118630696, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 4 :=
  ⟨⟨65,41,53⟩,mass_cell 4 65 41 53 89 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2628931757602, 577604140442, 39303775290, 3940596] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 4 :=
  ⟨⟨63,12,44⟩,mass_cell 4 63 12 44 153 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3545479638910, 2048719930374, 949004578578, 341710838742, 60797675791, 134279606, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 4 :=
  ⟨⟨62,21,48⟩,mass_cell 4 62 21 48 115 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3709032352438, 2198590793512, 814766545384, 218488181416, 31290192232, 843937500, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 4 :=
  ⟨⟨51,37,52⟩,mass_cell 4 51 37 52 92 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2544570716545, 637878738664, 64424086664, 207853860] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 4 :=
  ⟨⟨68,48,54⟩,mass_cell 4 68 48 54 85 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2719395414270, 510769645090, 17546880394, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 4 :=
  ⟨⟨68,30,51⟩,mass_cell 4 68 30 51 100 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2447678944347, 690903569485, 107744660605, 3853570135, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 4 :=
  ⟨⟨59,36,52⟩,mass_cell 4 59 36 52 93 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2540543340766, 637468520452, 67845463360, 386367374] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 4 :=
  ⟨⟨61,24,49⟩,mass_cell 4 61 24 49 109 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2269162559445, 777098747373, 181313400093, 19255387749, 203231702, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 4 :=
  ⟨⟨83,16,48⟩,mass_cell 4 83 16 48 133 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3709728379262, 2230610690937, 828645353417, 187302276353, 4385259438, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 4 :=
  ⟨⟨75,25,50⟩,mass_cell 4 75 25 50 107 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2354958960142, 731389475438, 141362992078, 9181020237, 20475] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 4 :=
  ⟨⟨86,27,51⟩,mass_cell 4 86 27 51 105 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2445328790177, 686523633871, 104830545091, 3030371218, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 4 :=
  ⟨⟨86,15,48⟩,mass_cell 4 86 15 48 138 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3709975949753, 2242444513671, 834523284555, 175492247455, 1625137189, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 4 :=
  ⟨⟨76,47,54⟩,mass_cell 4 76 47 54 86 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2716969338259, 511285417107, 18973000036, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 4 :=
  ⟨⟨77,21,49⟩,mass_cell 4 77 21 49 116 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2273086639720, 776397046312, 173482185448, 12314955937, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 4 :=
  ⟨⟨90,45,54⟩,mass_cell 4 90 45 54 87 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2714587591302, 513848705264, 21657606416, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 4 :=
  ⟨⟨92,6,46⟩,mass_cell 4 92 6 46 228 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3654914510174, 2245765261002, 920743730494, 120993907676, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 4 :=
  ⟨⟨91,55,55⟩,mass_cell 4 91 55 55 82 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2805403383480, 437546878200, 6357809611] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 4 :=
  ⟨⟨79,39,53⟩,mass_cell 4 79 39 53 91 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2625805831998, 579974283284, 43789916948, 48513122] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 4 :=
  ⟨⟨97,44,54⟩,mass_cell 4 97 44 54 88 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2713121587237, 513443716600, 22532968340, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 4 :=
  ⟨⟨98,36,53⟩,mass_cell 4 98 36 53 94 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2623273856760, 579291268351, 45994095895, 139011192] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 4 :=
  ⟨⟨99,54,55⟩,mass_cell 4 99 54 55 82 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2803445918018, 437265157886, 6925671624] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 4 :=
  ⟨⟨94,12,48⟩,mass_cell 4 94 12 48 157 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3710808770334, 2281924393469, 849669717581, 131892688332, 4598141, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 4 :=
  ⟨⟨66,35,52⟩,mass_cell 4 66 35 52 94 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2538608956420, 638771078573, 71146376329, 625454047] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 4 :=
  ⟨⟨73,34,52⟩,mass_cell 4 73 34 52 95 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2536297463759, 638235833438, 73301147618, 883149156] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 4 :=
  ⟨⟨104,43,54⟩,mass_cell 4 104 43 54 88 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2711467914182, 511799662877, 22925802849, 105566] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 4 :=
  ⟨⟨102,9,48⟩,mass_cell 4 102 9 48 184 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3711637911834, 2318000591216, 843548480948, 81394425024, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 4 :=
  ⟨⟨97,15,49⟩,mass_cell 4 97 15 49 139 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2327317274802, 801971346090, 117361745055, 2225895, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 4 :=
  ⟨⟨104,35,53⟩,mass_cell 4 104 35 53 95 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2622643371394, 577240925771, 44672306183, 62759108] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 4 :=
  ⟨⟨106,53,55⟩,mass_cell 4 106 53 55 83 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2802500564348, 438065121904, 7495143760] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 4 :=
  ⟨⟨80,33,52⟩,mass_cell 4 80 33 52 96 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2533600578912, 635719889244, 73963707420, 1078447400] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 4 :=
  ⟨⟨109,34,53⟩,mass_cell 4 109 34 53 96 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2623931259100, 577666704413, 43071923196, 1502501] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 4 :=
  ⟨⟨113,52,55⟩,mass_cell 4 113 52 55 84 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2801436462679, 438048441806, 7949260232] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 4 :=
  ⟨⟨115,41,54⟩,mass_cell 4 115 41 54 90 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2712467627627, 513835923212, 23324049712, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 4 :=
  ⟨⟨121,40,54⟩,mass_cell 4 121 40 54 91 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2711932414464, 511616975881, 22164762267, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 4 :=
  ⟨⟨119,51,55⟩,mass_cell 4 119 51 55 84 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2801426218996, 439333011234, 8386559505] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 4 :=
  ⟨⟨122,31,53⟩,mass_cell 4 122 31 53 100 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2631127693018, 579760803157, 34168537611, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 4 :=
  ⟨⟨117,25,52⟩,mass_cell 4 117 25 52 109 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2552515772854, 640430821574, 47483199384, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 4 :=
  ⟨⟨126,30,53⟩,mass_cell 4 126 30 53 102 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2633962210280, 579470201043, 30142252487, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 4 :=
  ⟨⟨126,39,54⟩,mass_cell 4 126 39 54 92 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2712898351456, 511503404037, 20878368621, 0] (by decide +kernel) (by decide +kernel)⟩
private def m70 : MassCell 4 :=
  ⟨⟨125,50,55⟩,mass_cell 4 125 50 55 85 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2801316731865, 439861046775, 8645672711, 0] (by decide +kernel) (by decide +kernel)⟩
private def m71 : MassCell 4 :=
  ⟨⟨129,21,52⟩,mass_cell 4 129 21 52 119 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2575845473091, 644200726506, 26042611507, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m72 : MassCell 4 :=
  ⟨⟨130,38,54⟩,mass_cell 4 130 38 54 93 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2715418491579, 513855718494, 19712406767, 0] (by decide +kernel) (by decide +kernel)⟩
private def m73 : MassCell 4 :=
  ⟨⟨126,15,51⟩,mass_cell 4 126 15 51 141 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2519516501995, 696908873385, 24867494940, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m74 : MassCell 4 :=
  ⟨⟨131,49,55⟩,mass_cell 4 131 49 55 85 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2801106470860, 439575829316, 8660563510, 0] (by decide +kernel) (by decide +kernel)⟩
private def m75 : MassCell 4 :=
  ⟨⟨129,29,53⟩,mass_cell 4 129 29 53 103 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2638945734406, 582976584044, 27238393898, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m76 : MassCell 4 :=
  ⟨⟨137,18,52⟩,mass_cell 4 137 18 52 129 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2595010666078, 639738767770, 12953833590, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m77 : MassCell 4 :=
  ⟨⟨135,37,54⟩,mass_cell 4 135 37 54 94 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2716143201439, 511623398040, 17229976316, 0] (by decide +kernel) (by decide +kernel)⟩
private def m78 : MassCell 4 :=
  ⟨⟨137,48,55⟩,mass_cell 4 137 48 55 86 (by decide)
    (by decide +kernel) [4711930693262, 4364481494834, 4036113266390, 3726141113402, 2800793881629, 438418768879, 8356082834, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 4) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69, m70, m71, m72, m73, m74, m75, m76, m77, m78]

end Low6966Allocation.Group4
