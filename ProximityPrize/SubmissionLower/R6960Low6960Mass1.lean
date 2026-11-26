import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6960Allocation.Group1

private def m0 : MassCell 1 :=
  ⟨⟨2,6,8⟩,mass_cell 1 2 6 8 190 (by decide)
    (by decide +kernel) [4677853166212, 3903441583584, 3146863739844, 2493299062632, 1935743973132, 1467058843632, 1079967997524, 767059709304, 520786204572, 333463660032, 197272203492, 104255913864, 46322821164, 15244906512, 2658102132, 67127756] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 1 :=
  ⟨⟨3,7,15⟩,mass_cell 1 3 7 15 179 (by decide)
    (by decide +kernel) [4740005313959, 4183975781943, 3306018505969, 2555866863589, 1927997012729, 1411832268589, 996699178369, 671827521269, 426350308489, 249303783229, 129627420689, 56163928069, 17659244569, 2762541389, 44944602] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 1 :=
  ⟨⟨3,9,24⟩,mass_cell 1 3 9 24 160 (by decide)
    (by decide +kernel) [4740005313959, 4433739636828, 3653605056914, 2712160195586, 1945726192754, 1337437713122, 869999439698, 525686073794, 286342335026, 133382961314, 47792708882, 10126352258, 508826329, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 1 :=
  ⟨⟨1,12,32⟩,mass_cell 1 1 12 32 141 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4044055761956, 2973822782921, 1997421450713, 1254750448265, 718725578777, 359533269449, 144630571481, 38745160073, 3875334425, 3340522] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 1 :=
  ⟨⟨4,15,38⟩,mass_cell 1 4 15 38 128 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3313823784258, 2066100348522, 1173720506898, 581448407610, 230903957730, 60562823178, 5756428722, 2969650] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 1 :=
  ⟨⟨1,18,41⟩,mass_cell 1 1 18 41 118 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3517565511673, 2111785321116, 1095834809424, 465445826364, 137643537504, 17738906556, 99818652] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 1 :=
  ⟨⟨1,21,44⟩,mass_cell 1 1 21 44 111 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3700546985081, 2215095109604, 1049741737892, 379591680356, 79486422308, 3633265222, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 1 :=
  ⟨⟨1,24,46⟩,mass_cell 1 1 24 46 106 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3795589824856, 2290832500794, 987436779990, 297433715874, 39587283294, 257652168] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 1 :=
  ⟨⟨1,26,47⟩,mass_cell 1 1 26 47 102 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3832627831069, 2332045560886, 941852688850, 247923229382, 22632041746, 5228122] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 1 :=
  ⟨⟨8,27,48⟩,mass_cell 1 8 27 48 102 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3860844192907, 2397569222620, 927484727932, 228870844444, 18027988156, 186125] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 1 :=
  ⟨⟨1,30,49⟩,mass_cell 1 1 30 49 98 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2480091881147, 888717844835, 178536576275, 6839778474, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 1 :=
  ⟨⟨9,32,50⟩,mass_cell 1 9 32 50 96 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2560940667038, 847282144258, 145890673078, 3342225172] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 1 :=
  ⟨⟨1,36,51⟩,mass_cell 1 1 36 51 92 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2659012970398, 799579720275, 100121895771, 412691865] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 1 :=
  ⟨⟨13,39,52⟩,mass_cell 1 13 39 52 90 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2737575023745, 744040801799, 71510094251, 39255040] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 1 :=
  ⟨⟨1,45,53⟩,mass_cell 1 1 45 53 86 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2836778791965, 682989408756, 37349833422, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 1 :=
  ⟨⟨5,51,54⟩,mass_cell 1 5 51 54 83 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2924242249111, 614337903405, 17813976330] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 1 :=
  ⟨⟨22,5,18⟩,mass_cell 1 22 5 18 223 (by decide)
    (by decide +kernel) [4740005313959, 4286727580181, 3347793229466, 2532065950474, 1875065904250, 1354771753706, 950804231770, 644426141386, 418542355514, 257699817130, 148087539226, 77536604810, 35520166906, 13153448554, 3193907282, 185187413, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 1 :=
  ⟨⟨46,12,41⟩,mass_cell 1 46 12 41 150 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3494586754525, 2065406291666, 1095132059846, 513915400466, 200897055926, 57682632626, 8348166654, 40136737, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 1 :=
  ⟨⟨44,21,47⟩,mass_cell 1 44 21 47 114 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3829412061326, 2288095789786, 949282890154, 303898343290, 59995526218, 3597830170, 1132] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 1 :=
  ⟨⟨30,30,50⟩,mass_cell 1 30 30 50 99 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2537567643030, 842585507394, 162896873838, 7064871434, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 1 :=
  ⟨⟨40,26,49⟩,mass_cell 1 40 26 49 104 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2435575194699, 884153583315, 216730128091, 21469362723, 49395375] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 1 :=
  ⟨⟨59,30,51⟩,mass_cell 1 59 30 51 100 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2611792594299, 793166699623, 139073171071, 6051214843, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 1 :=
  ⟨⟨60,34,52⟩,mass_cell 1 60 34 52 95 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2708344914535, 744647608637, 98532029005, 1497125524] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 1 :=
  ⟨⟨61,39,53⟩,mass_cell 1 61 39 53 91 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2804273699223, 687812481125, 61363806641, 89813513] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 1 :=
  ⟨⟨37,48,54⟩,mass_cell 1 37 48 54 85 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2909997783345, 620266541360, 25078017202, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 1 :=
  ⟨⟨59,21,48⟩,mass_cell 1 59 21 48 115 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3859538078311, 2343925417828, 912736287940, 266835679780, 45978558340, 2288438500, 95930] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 1 :=
  ⟨⟨39,29,50⟩,mass_cell 1 39 29 50 100 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2529895313000, 841787702504, 170432998248, 9436625384, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 1 :=
  ⟨⟨55,27,50⟩,mass_cell 1 55 27 50 104 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2519561481909, 840503916681, 181784676093, 14466243345, 11809185] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 1 :=
  ⟨⟨64,4,39⟩,mass_cell 1 64 4 39 273 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3426461824274, 2179270105538, 1221374764534, 516232131320, 73943826219, 18128825, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 1 :=
  ⟨⟨65,45,54⟩,mass_cell 1 65 45 54 87 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2899361932685, 623167023004, 32467327036, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 1 :=
  ⟨⟨67,15,46⟩,mass_cell 1 67 15 46 136 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3789856322011, 2244241244163, 985529418159, 340581686331, 71108008236, 1929535718, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 1 :=
  ⟨⟨56,24,49⟩,mass_cell 1 56 24 49 109 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2421936380589, 877304027877, 224153265525, 28079968605, 425079622, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 1 :=
  ⟨⟨66,29,51⟩,mass_cell 1 66 29 51 101 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2609941050046, 794152649114, 143060327402, 7372794426, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 1 :=
  ⟨⟨73,44,54⟩,mass_cell 1 73 44 54 88 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2897405440975, 624865200079, 34901171183, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 1 :=
  ⟨⟨60,54,55⟩,mass_cell 1 60 54 55 82 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2997265797494, 548271113942, 11352307752] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 1 :=
  ⟨⟨77,15,47⟩,mass_cell 1 77 15 47 137 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3830224098097, 2302324584807, 954192915795, 287042246175, 32579656351, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 1 :=
  ⟨⟨75,24,50⟩,mass_cell 1 75 24 50 110 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2514196325724, 837955426272, 185843858820, 17448954504, 96127557, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 1 :=
  ⟨⟨78,52,55⟩,mass_cell 1 78 52 55 84 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2992444181717, 550230066556, 13847318464] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 1 :=
  ⟨⟨81,43,54⟩,mass_cell 1 81 43 54 88 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2895234650887, 625246162697, 37007821573, 416740] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 1 :=
  ⟨⟨86,51,55⟩,mass_cell 1 86 51 55 84 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2990969202166, 551818729566, 15115148343] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 1 :=
  ⟨⟨87,18,49⟩,mass_cell 1 87 18 49 126 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2442695659958, 892274217410, 212325709718, 11161471244, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 1 :=
  ⟨⟨79,27,51⟩,mass_cell 1 79 27 51 105 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2607999060281, 793971832401, 145875008061, 8695274121, 4377024] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 1 :=
  ⟨⟨94,6,46⟩,mass_cell 1 94 6 46 228 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3803628024070, 2387482206132, 1042105514376, 186674869514, 35672785, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 1 :=
  ⟨⟨94,50,55⟩,mass_cell 1 94 50 55 85 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2989355198499, 552440436819, 16265212355, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 1 :=
  ⟨⟨88,30,52⟩,mass_cell 1 88 30 52 101 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2701316451558, 743038995512, 106497889724, 3177525644, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 1 :=
  ⟨⟨77,37,53⟩,mass_cell 1 77 37 53 93 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2798509384069, 687150767936, 67216795264, 329774644] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 1 :=
  ⟨⟨87,15,48⟩,mass_cell 1 87 15 48 138 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3860274292331, 2378377293927, 928768044291, 232854855965, 8846062715, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 1 :=
  ⟨⟨90,25,51⟩,mass_cell 1 90 25 51 108 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2610965159085, 795508042438, 142657312774, 6298782360, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 1 :=
  ⟨⟨96,41,54⟩,mass_cell 1 96 41 54 90 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2891863198089, 624789475790, 40157300718, 16272970] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 1 :=
  ⟨⟨97,34,53⟩,mass_cell 1 97 34 53 96 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2796050678812, 687844012406, 71398932802, 719667385] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 1 :=
  ⟨⟨96,12,48⟩,mass_cell 1 96 12 48 157 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3861093840109, 2417958931008, 947076020436, 186464352234, 312349526, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 1 :=
  ⟨⟨102,49,55⟩,mass_cell 1 102 49 55 85 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2987600130380, 552021813232, 17227098262, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 1 :=
  ⟨⟨103,40,54⟩,mass_cell 1 103 40 54 91 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2890691752650, 624021480994, 40976485334, 33066976] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 1 :=
  ⟨⟨103,33,53⟩,mass_cell 1 103 33 53 97 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2796157594941, 687451381140, 70703668308, 604349980, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 1 :=
  ⟨⟨109,48,55⟩,mass_cell 1 109 48 55 86 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2986911228422, 552958605800, 18168585152, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 1 :=
  ⟨⟨94,29,52⟩,mass_cell 1 94 29 52 102 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2701329343567, 742067030112, 105031095392, 2716338560, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 1 :=
  ⟨⟨108,32,53⟩,mass_cell 1 108 32 53 99 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2798239415461, 689860512299, 69867248899, 344065799, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 1 :=
  ⟨⟨115,38,54⟩,mass_cell 1 115 38 54 93 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2891135735427, 625194731865, 41384007081, 33405938] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 1 :=
  ⟨⟨116,47,55⟩,mass_cell 1 116 47 55 87 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2986100748574, 552908918198, 18821262308, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 1 :=
  ⟨⟨114,9,49⟩,mass_cell 1 114 9 49 185 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2544409959998, 917207718378, 82130253100, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 1 :=
  ⟨⟨104,27,52⟩,mass_cell 1 104 27 52 106 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2706015212226, 744775320820, 99387289720, 805950886, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 1 :=
  ⟨⟨118,30,53⟩,mass_cell 1 118 30 53 102 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2801842259053, 690392645162, 62768652931, 66045, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 1 :=
  ⟨⟨122,29,53⟩,mass_cell 1 122 29 53 103 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2805651287101, 693429885524, 58956530697, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 1 :=
  ⟨⟨121,37,54⟩,mass_cell 1 121 37 54 94 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2891117929355, 623834107632, 39955640007, 455126] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 1 :=
  ⟨⟨116,24,52⟩,mass_cell 1 116 24 52 112 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2719874376907, 753551561481, 82048169623, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 1 :=
  ⟨⟨127,21,52⟩,mass_cell 1 127 21 52 119 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2734964863500, 754580588672, 56946457005, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 1 :=
  ⟨⟨123,46,55⟩,mass_cell 1 123 46 55 87 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2985166874906, 551802810877, 19081149685, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 1 :=
  ⟨⟨129,45,55⟩,mass_cell 1 129 45 55 88 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2985352805618, 552362461616, 19226536400, 0] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 1 :=
  ⟨⟨133,6,50⟩,mass_cell 1 133 6 50 232 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2673256736949, 847559704672, 19895826162, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 1 :=
  ⟨⟨126,15,51⟩,mass_cell 1 126 15 51 141 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2675564253031, 813677701122, 54942874967, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m70 : MassCell 1 :=
  ⟨⟨130,27,53⟩,mass_cell 1 130 27 53 107 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2812845818481, 695670801270, 48417983617, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m71 : MassCell 1 :=
  ⟨⟨126,36,54⟩,mass_cell 1 126 36 54 95 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2892657286457, 624937469648, 38365328678, 0] (by decide +kernel) (by decide +kernel)⟩
private def m72 : MassCell 1 :=
  ⟨⟨133,12,51⟩,mass_cell 1 133 12 51 160 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2705748352046, 817774822930, 33349048264, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m73 : MassCell 1 :=
  ⟨⟨131,35,54⟩,mass_cell 1 131 35 54 96 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2894068407737, 624864723175, 35770069692, 0] (by decide +kernel) (by decide +kernel)⟩
private def m74 : MassCell 1 :=
  ⟨⟨135,44,55⟩,mass_cell 1 135 44 55 89 (by decide)
    (by decide +kernel) [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2985435847136, 551949187825, 18841338389, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 1) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69, m70, m71, m72, m73, m74]

end Low6960Allocation.Group1
