import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6960Allocation.Group5

private def m0 : MassCell 5 :=
  ⟨⟨2,5,4⟩,mass_cell 5 2 5 4 209 (by decide)
    (by decide +kernel) [4547458861555, 3747150808088, 3043146224984, 2437576569240, 1921851533528, 1487663926040, 1126989670488, 832087806104, 595500487640, 410052985368, 268853685080, 165294088088, 93048811224, 46075586840, 18615262808, 5191802520, 612284888, 2396357] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 5 :=
  ⟨⟨2,6,12⟩,mass_cell 5 2 6 12 194 (by decide)
    (by decide +kernel) [4698471960466, 3994787087448, 3183872611452, 2495105640384, 1917207972708, 1439249087400, 1050646143948, 741163982352, 500915123124, 320359767288, 190305796380, 101908772448, 46671938052, 16446216264, 3430210668, 170248502, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 5 :=
  ⟨⟨3,7,19⟩,mass_cell 5 3 7 19 183 (by decide)
    (by decide +kernel) [4702572486363, 4243801829621, 3371083694943, 2580022494515, 1928314769447, 1400705562939, 982506702191, 659596798403, 418421246775, 245992226507, 129888700799, 58256416851, 19807905863, 3822483035, 146954626, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 5 :=
  ⟨⟨2,9,27⟩,mass_cell 5 2 9 27 163 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3707970307082, 2741560479572, 1958573240132, 1343114895668, 874007603492, 530503502612, 292284713732, 139463339252, 52581463268, 12611151572, 954451652, 2966] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 5 :=
  ⟨⟨4,10,31⟩,mass_cell 5 4 10 31 156 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3870477887709, 2860293355571, 1985412581851, 1314557929027, 818312721707, 468368837971, 237526709371, 99695320931, 29892211147, 4243471987, 46485982] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 5 :=
  ⟨⟨1,12,35⟩,mass_cell 5 1 12 35 144 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3976633847910, 3034776768145, 2032511255953, 1278367734481, 737883360529, 376105402897, 157591242385, 46408371793, 6134395921, 43731136] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 5 :=
  ⟨⟨4,15,41⟩,mass_cell 5 4 15 41 131 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3381933078621, 2145206992302, 1228118642550, 620260071102, 257016450438, 74498547150, 9542721942, 58585386] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 5 :=
  ⟨⟨2,16,42⟩,mass_cell 5 2 16 42 127 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3436899736009, 2174676837061, 1216024897597, 589639121789, 226528424197, 55757933653, 4448993261, 100586] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 5 :=
  ⟨⟨1,17,43⟩,mass_cell 5 1 17 43 124 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3487021274152, 2202854380678, 1199432174614, 556162403750, 196593740086, 40072359622, 1745303633, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 5 :=
  ⟨⟨1,18,44⟩,mass_cell 5 1 18 44 121 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3532731980756, 2231906606602, 1180135075894, 521550809530, 168487805590, 27711015370, 539365078, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 5 :=
  ⟨⟨3,21,47⟩,mass_cell 5 3 21 47 114 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3641557753817, 2369154082136, 1147510337144, 438350666648, 106011864248, 7951016408, 3279] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 5 :=
  ⟨⟨2,24,49⟩,mass_cell 5 2 24 49 109 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2500009937619, 1118977502451, 367885932603, 62532581163, 1366416354, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 5 :=
  ⟨⟨1,26,50⟩,mass_cell 5 1 26 50 105 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2578570922812, 1095242192576, 323349772348, 41377975984, 221788703] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 5 :=
  ⟨⟨6,30,52⟩,mass_cell 5 6 30 52 101 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2733779165148, 1049763622454, 245328085538, 16436854574, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 5 :=
  ⟨⟨5,33,53⟩,mass_cell 5 5 33 53 97 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2814048877209, 1023496521516, 199758337740, 7259402952, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 5 :=
  ⟨⟨9,36,54⟩,mass_cell 5 9 36 54 95 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2891545732443, 995338376043, 160002079251, 2814680144] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 5 :=
  ⟨⟨11,40,55⟩,mass_cell 5 11 40 55 92 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2969625913321, 962848192522, 118304016486, 523203672] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 5 :=
  ⟨⟨14,45,56⟩,mass_cell 5 14 45 56 89 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3046314192658, 924426494264, 79551967736, 9957980] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 5 :=
  ⟨⟨12,52,57⟩,mass_cell 5 12 52 57 86 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3123176975622, 881724205714, 44982676564, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 5 :=
  ⟨⟨55,17,49⟩,mass_cell 5 55 17 49 130 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2449582009924, 1083942510404, 388116214084, 96380496964, 10482660888, 7507933, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 5 :=
  ⟨⟨55,27,53⟩,mass_cell 5 55 27 53 107 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2786092672959, 1004667638095, 235072461115, 24016974535, 151904300] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 5 :=
  ⟨⟨47,36,55⟩,mass_cell 5 47 36 55 96 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2955533619733, 952783936157, 140541515453, 2887543326] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 5 :=
  ⟨⟨62,4,43⟩,mass_cell 5 62 4 43 277 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3509046687031, 2309193575920, 1292158369356, 541643512499, 73741087760, 8811661, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 5 :=
  ⟨⟨37,33,54⟩,mass_cell 5 37 33 54 98 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2876258422089, 983668627188, 179422137108, 7162401714, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 5 :=
  ⟨⟨50,41,56⟩,mass_cell 5 50 41 56 92 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3036045469643, 917976153018, 97556667770, 404056183] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 5 :=
  ⟨⟨40,49,57⟩,mass_cell 5 40 49 57 87 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3117442958994, 880194344084, 54739245316, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 5 :=
  ⟨⟨48,25,52⟩,mass_cell 5 48 25 52 109 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2704188294256, 1030056674684, 276264519308, 38028341148, 762887010, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 5 :=
  ⟨⟨63,34,55⟩,mass_cell 5 63 34 55 98 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2950144757384, 944663074926, 146009631842, 4546808168, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 5 :=
  ⟨⟨69,33,55⟩,mass_cell 5 69 33 55 99 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2949996258765, 946657972266, 149635543866, 5434637373, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 5 :=
  ⟨⟨57,21,51⟩,mass_cell 5 57 21 51 118 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2616655236046, 1046445111548, 316519000604, 58407074108, 3504146012, 1347123] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 5 :=
  ⟨⟨60,30,54⟩,mass_cell 5 60 30 54 103 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2867511836757, 974356320908, 190095084416, 12186268004, 1870280] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 5 :=
  ⟨⟨66,39,56⟩,mass_cell 5 66 39 56 94 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3032223979063, 912880275566, 103652924414, 926411101] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 5 :=
  ⟨⟨66,46,57⟩,mass_cell 5 66 46 57 89 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3112463256426, 874209950894, 62866071970, 12420258] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 5 :=
  ⟨⟨70,13,49⟩,mass_cell 5 70 13 49 151 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2482731151542, 1116338173574, 378642510422, 53768972488, 4097875, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 5 :=
  ⟨⟨73,24,53⟩,mass_cell 5 73 24 53 113 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2784061971449, 1000778786490, 233910117822, 24036325266, 98815532, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 5 :=
  ⟨⟨78,16,51⟩,mass_cell 5 78 16 51 136 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2639368801473, 1072276249817, 303893548537, 26526673692, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 5 :=
  ⟨⟨78,27,54⟩,mass_cell 5 78 27 54 108 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2866095582661, 972479487738, 191544629826, 13254807258, 3319611] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 5 :=
  ⟨⟨71,21,52⟩,mass_cell 5 71 21 52 119 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2703473749104, 1028632333464, 274800637368, 36012610853, 203086426, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 5 :=
  ⟨⟨82,31,55⟩,mass_cell 5 82 31 55 102 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2947931387334, 941715056852, 149476076292, 5999575604, 5] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 5 :=
  ⟨⟨76,54,58⟩,mass_cell 5 76 54 58 85 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3188801238884, 828326705950, 32518126612, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 5 :=
  ⟨⟨83,53,58⟩,mass_cell 5 83 53 58 86 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3188391767248, 829350946864, 34257977412, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 5 :=
  ⟨⟨88,43,57⟩,mass_cell 5 88 43 57 91 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3109665323656, 870245622450, 68647283362, 127579517] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 5 :=
  ⟨⟨91,52,58⟩,mass_cell 5 91 52 58 87 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3187545111351, 827180810367, 35445741167, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 5 :=
  ⟨⟨98,51,58⟩,mass_cell 5 98 51 58 87 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3187089033888, 826728542682, 36672614178, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 5 :=
  ⟨⟨100,41,57⟩,mass_cell 5 100 41 57 93 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3109391177737, 871272583848, 71045647096, 241366658] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 5 :=
  ⟨⟨103,6,51⟩,mass_cell 5 103 6 51 233 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2736538346633, 1151257597317, 162626153278, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 5 :=
  ⟨⟨86,36,56⟩,mass_cell 5 86 36 56 97 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3029813170894, 909924296588, 108885565160, 1779982010, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 5 :=
  ⟨⟨105,50,58⟩,mass_cell 5 105 50 58 88 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3186610452823, 825517016782, 37546172274, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 5 :=
  ⟨⟨111,49,58⟩,mass_cell 5 111 49 58 88 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3186530556044, 826251134308, 38477591268, 241252] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 5 :=
  ⟨⟨112,12,53⟩,mass_cell 5 112 12 53 162 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2843682569957, 1065866927332, 131892538184, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 5 :=
  ⟨⟨97,34,56⟩,mass_cell 5 97 34 56 99 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3030213978255, 911307573104, 109128784116, 1698270339, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 5 :=
  ⟨⟨112,39,57⟩,mass_cell 5 112 39 57 95 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3108959576740, 868539849958, 69573056302, 159676646] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 5 :=
  ⟨⟨102,33,56⟩,mass_cell 5 102 33 56 100 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3030839774034, 912516434532, 107882716788, 1239496498, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 5 :=
  ⟨⟨117,38,57⟩,mass_cell 5 117 38 57 96 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3109388282788, 869424416439, 68343121660, 47244877] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 5 :=
  ⟨⟨117,48,58⟩,mass_cell 5 117 48 58 89 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3186432088598, 826309446692, 38977084184, 1295956] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 5 :=
  ⟨⟨107,9,52⟩,mass_cell 5 107 9 52 188 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2784457709355, 1105406771318, 149272217145, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 5 :=
  ⟨⟨123,47,58⟩,mass_cell 5 123 47 58 90 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3186314905289, 825657280265, 38940629717, 1682298] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 5 :=
  ⟨⟨105,26,55⟩,mass_cell 5 105 26 55 110 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2954602535056, 952157087698, 135830889278, 568598143, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 5 :=
  ⟨⟨115,30,56⟩,mass_cell 5 115 30 56 105 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3034509132857, 919325120983, 98520763567, 15783180, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 5 :=
  ⟨⟨121,37,57⟩,mass_cell 5 121 37 57 97 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3110494674480, 873358771252, 67461161246, 1749060, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 5 :=
  ⟨⟨124,20,55⟩,mass_cell 5 124 20 55 125 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2973274886259, 978486152282, 93234178795, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 5 :=
  ⟨⟨126,27,56⟩,mass_cell 5 126 27 56 110 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3039935368302, 927764728098, 82461336835, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 5 :=
  ⟨⟨129,46,58⟩,mass_cell 5 129 46 58 90 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 3186178872241, 824259224493, 38251569789, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 5 :=
  ⟨⟨129,4,53⟩,mass_cell 5 129 4 53 287 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2900817149160, 1084889706449, 50032825555, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 5 :=
  ⟨⟨122,14,54⟩,mass_cell 5 122 14 54 150 (by decide)
    (by decide +kernel) [4702572486363, 4339405589691, 3997449907059, 3675875397123, 2914068668743, 1026950362978, 95451899963, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 5) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64]

end Low6960Allocation.Group5
