import ProximityPrize.SubmissionLower.High6966Rates
import ProximityPrize.SubmissionLower.High6966RescueBills

set_option Elab.async false

-- merged module High6966RescueInvoice
section Merged_High6966RescueInvoice
noncomputable section
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 6000000
namespace Lower6960.Rescue6966
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) := [[150464807, 122771898, 122771898, 118888370, 107792950, 105679363, 86580683, 86967597, 110067573, 103936882, 77329110, 75811593, 109920404, 109030583, 109030583, 109030583, 118805636], [148344704, 117212797, 104190415, 111133015, 116928093, 103936882, 92389223, 64888529, 92389223, 72286102, 114460217, 81954206, 81954206, 81954206, 81954206, 81954206, 106186837], [137084500, 121853956, 108315682, 108315682, 104088402, 96281771, 77334756, 80404006, 55437230, 65560191, 104423884, 97675863, 73660247, 73660247, 73660247, 73660247, 104917799], [112048472, 88535775, 88973645, 94698049, 94698049, 86967597, 77305283, 61759601, 77305283, 60283149, 94698049, 64348526, 65560191, 65560191, 65560191, 65560191, 98893096], [79482872, 70653206, 70653206, 62803685, 74761620, 61759601, 52610031, 61759601, 74905219, 76709349, 54792393, 51361812, 74761620, 63688618, 63688618, 77878079, 94398643], [47881040, 50685999, 50134265, 50769062, 50134265, 45821641, 45821641, 49736132, 40747993, 72969392, 58375514, 45513952, 55783958, 55783958, 55783958, 55783958, 71459715], [47881040, 46994354, 50134265, 50134265, 51411571, 50134265, 50134265, 42192204, 35587226, 50546813, 52610031, 51351418, 41923619, 47881040, 49144763, 68178616, 69859220], [50134265, 53562833, 53562833, 55343020, 55343020, 59848652, 53209673, 43932089, 36407193, 50766776, 52610031, 52563907, 43932089, 41291648, 42353162, 52666614, 80404006], [48651217, 50134265, 58375514, 56878706, 50134265, 49032413, 55343020, 58375514, 29220782, 50134265, 61759601, 60630950, 85684406, 55560982, 53500695, 45882618, 86967597], [75414165, 75414165, 67036224, 75668082, 75414165, 69175492, 54658196, 86967597, 42623494, 74761620, 58375514, 53898721, 65560191, 65560191, 65560191, 65560191, 94188120], [78529830, 69805670, 68241217, 73753606, 65560191, 74761620, 71579398, 56557607, 32058558, 44688377, 69859220, 41853448, 49064800, 49064800, 49064800, 49064800, 93299213], [68912352, 69859220, 65560191, 69859220, 62098390, 66582624, 52610031, 85746074, 64548962, 80404006, 64323205, 61759601, 60634840, 60634840, 60634840, 60634840, 92698890], [61759601, 63658706, 63658706, 63658706, 69859220, 55199658, 69613534, 67421314, 93182529, 74761620, 61519226, 54684280, 74761620, 64789234, 64789234, 64789234, 84993586], [52941200, 52941200, 58375514, 55343020, 61759601, 50134265, 60901773, 51047160, 38309654, 68680602, 54944482, 45524672, 65560191, 61105930, 61105930, 61105930, 80132786], [50134265, 50134265, 50134265, 50134265, 45914923, 52610031, 52610031, 45821641, 38654210, 56053967, 47881040, 42561987, 59547296, 45821853, 47030048, 60093952, 69859220], [43932089, 48784456, 47881040, 47881040, 47881040, 43932089, 42840608, 58375514, 30695306, 52610031, 43044571, 43044571, 63987427, 45821641, 45333625, 51206999, 65560191], [45821641, 50134265, 49032413, 50134265, 50134265, 52610031, 50407975, 40584882, 29942690, 40584882, 52610031, 52610031, 77921648, 52534272, 46698901, 48943287, 74761620], [52610031, 50181876, 50181876, 50181876, 48895161, 56829841, 55343020, 55343020, 26305018, 47881040, 47881040, 33693231, 41442988, 74761620, 58375514, 55343020, 80404006], [55343020, 58375514, 51890820, 49863886, 52610031, 50134265, 43653183, 65560191, 34294058, 58375514, 43977528, 43977528, 69859220, 49899443, 49834743, 35046188, 69859220], [52610031, 52610031, 52610031, 56051172, 49825152, 58375514, 55343020, 46175771, 38669956, 56879449, 50134265, 45588489, 38079769, 55343020, 47376616, 61685845, 69859220], [52610031, 52610031, 56815345, 52610031, 56817079, 50505985, 40369537, 50134265, 62573594, 58375514, 46517987, 45270889, 69037758, 50312266, 50226868, 62936234, 69859220], [47881040, 47881040, 49482432, 53506044, 47562069, 55343020, 55343020, 46359233, 28281783, 36630727, 61759601, 53417962, 59917700, 43932089, 56395864, 54960978, 65560191], [52610031, 52610031, 52610031, 52610031, 50134265, 58375514, 55343020, 45983538, 38358004, 59483897, 52610031, 44858978, 65112744, 46141483, 41015148, 57889794, 65560191], [47881040, 50134265, 45821641, 45821641, 44727175, 45821641, 55243548, 50134265, 27838420, 39614278, 58788794, 51170944, 76810499, 51206999, 49898965, 57987653, 65560191], [45821641, 45821641, 45821641, 44973092, 52610031, 42557159, 42557159, 45821641, 30409565, 44636598, 47881040, 33660302, 42192204, 61759601, 39300821, 50134265, 61759601], [47881040, 47881040, 50134265, 50134265, 47881040, 46977624, 52610031, 52610031, 26305018, 42192204, 48387841, 49603745, 40584882, 58375514, 70290874, 61759601, 69859220], [50134265, 50134265, 50134265, 48814943, 48814943, 55343020, 52610031, 50134265, 41075883, 61731184, 51313071, 52610031, 44873262, 57429272, 69859220, 57690194, 74761620], [42192204, 43932089, 43932089, 43979355, 39095529, 43932089, 50134265, 50134265, 26947513, 44564792, 35218287, 33791031, 50134265, 34091301, 35067861, 39773922, 58375514], [43025893, 43807419, 50134265, 49925888, 45510948, 47881040, 50134265, 40584882, 26305018, 32068588, 45267598, 26305018, 36609770, 55343020, 61759601, 54623267, 61759601], [45821641, 44806890, 44806890, 45656434, 40584882, 43932089, 50134265, 38225267, 38225267, 45785553, 49478158, 45561220, 39095529, 45821641, 40730744, 64459320, 58375514], [45821641, 45821641, 45821641, 45821641, 48482051, 52610031, 50134265, 42192204, 26305018, 33339261, 41585408, 40487846, 55343020, 58375514, 56869049, 51622710, 58375514], [45821641, 44806890, 44806890, 43932089, 42879957, 43932089, 43932089, 42192204, 42192204, 49317157, 50134265, 48934881, 39613775, 45821641, 40731137, 52610031, 58375514], [45432662, 45432662, 50134265, 50134265, 57991135, 47881040, 45821641, 47723755, 26305018, 37711616, 51097833, 49749210, 40584882, 52610031, 63765700, 53138084, 61759601], [42192204, 45821641, 44814572, 45821641, 45821641, 47881040, 47881040, 39095529, 26305018, 32040697, 45549812, 45549812, 67549072, 45541149, 40481930, 40323123, 61759601], [44917745, 44917745, 43932089, 43932089, 51745156, 42192204, 43188870, 47027473, 30077702, 45821641, 45821641, 33800460, 42192204, 50134265, 58909213, 74954883, 65560191], [47101327, 45652056, 45821641, 45821641, 45821641, 50134265, 50134265, 58375514, 32750233, 58375514, 41850093, 36417519, 52201471, 40584882, 40584882, 36422330, 69859220], [36422330, 37711616, 39204492, 35218287, 35414833, 42192204, 45821641, 43932089, 26305018, 39051682, 29592407, 26305018, 27961587, 42192204, 35192690, 47881040, 52610031], [37711616, 38371538, 37711616, 39095529, 40985093, 33894335, 40584882, 43996005, 26305018, 39108498, 32040697, 31088177, 37711616, 37711616, 37065167, 47881040, 52610031], [40555292, 39831523, 39831523, 42192204, 37505397, 42421766, 37711616, 32040697, 31901432, 37844463, 42682478, 39095529, 33725717, 39095529, 34752255, 53882434, 52610031], [40584882, 39861671, 39861671, 41350635, 44243340, 37062602, 42192204, 37711616, 37711616, 44732037, 35750904, 35791133, 45821641, 43328756, 38515196, 52610031, 55343020], [40584882, 40584882, 43932089, 42520715, 40584882, 41539468, 45821641, 41804530, 26305018, 33034207, 38178241, 37220364, 52610031, 50134265, 49921072, 69859220, 55343020], [47881040, 47881040, 47881040, 47881040, 45821641, 47881040, 44504392, 37711616, 26305018, 34091301, 52610031, 46765734, 35218287, 50134265, 29806136, 37128693, 58375514], [43932089, 43932089, 43932089, 42966548, 42192204, 41442052, 45821641, 40584882, 33726194, 48939286, 47881040, 26305018, 36422330, 43932089, 45158383, 67631364, 58375514], [43932089, 45157582, 45157582, 46345940, 52139182, 43932089, 43932089, 58375514, 30823709, 53643392, 43932089, 52605248, 44207422, 41904835, 41667830, 34409563, 65560191], [45821641, 45821641, 44411744, 47881040, 47881040, 50134265, 47881040, 43932089, 36806017, 54072058, 49466722, 26305018, 42192204, 43932089, 45004992, 64423206, 69859220], [34057447, 35218287, 34091301, 36218880, 37711616, 34091301, 27876664, 39617767, 26305018, 35218287, 28528075, 26305018, 26305018, 44698986, 44698986, 43932089, 45821641], [34755475, 36005215, 35218287, 37415542, 39095529, 36422330, 34987658, 29647437, 26305018, 35218287, 32040697, 28951095, 26305018, 29389053, 30192963, 42232763, 47881040], [39115595, 40584882, 40584882, 42315954, 37614182, 43820188, 43932089, 39706237, 31443602, 47881040, 36422330, 32376632, 39612974, 36422330, 35596348, 45821641, 50134265], [37711616, 38700064, 38700064, 38700064, 40972601, 36422330, 33034207, 45821641, 26305018, 40731738, 32994168, 28114070, 41454691, 33034207, 38866051, 49615182, 50134265], [42192204, 43932089, 42805625, 45656939, 40584882, 45821641, 43932089, 38017766, 31578774, 45821641, 42192204, 26305018, 29635610, 42192204, 37504921, 54826401, 52610031], [42192204, 40584882, 43302525, 43932089, 47464285, 47881040, 40717735, 42192204, 31450867, 46713877, 38257055, 45821641, 50134265, 50134265, 50134265, 73151611, 55343020], [42192204, 43932089, 43932089, 43932089, 43932089, 43932089, 42532854, 35218287, 26305018, 34343298, 55343020, 49198204, 46508140, 40584882, 26305018, 30584275, 58375514], [42192204, 43932089, 45821641, 45821641, 44646727, 50134265, 47881040, 53209673, 26305018, 43932089, 36925678, 28620475, 35218287, 63776687, 65560191, 47881040, 61759601], [49091083, 49401073, 47881040, 47881040, 47881040, 47881040, 47881040, 43932089, 36806017, 55379050, 42192204, 37505397, 42192204, 52610031, 51412674, 77172834, 65560191]]

def heightRates : List (List ℕ) := [[2560846, 3188131, 3188131, 3296764, 3657057, 3730477, 4594263, 4571273, 3578043, 3791006, 5173777, 5278651, 3583155, 3614065, 3614065, 3614065, 3299078], [2596119, 3343634, 3782199, 3541032, 3351598, 3791006, 4297696, 6199838, 4297696, 5548091, 3425454, 4869164, 4869164, 4869164, 4869164, 4869164, 3712849], [2835740, 3213809, 3638899, 3638899, 3785743, 4114306, 5173387, 4961275, 7288195, 6130948, 3774089, 4055429, 5438806, 5438806, 5438806, 5438806, 3756932], [3509232, 4492142, 4470047, 4181191, 4181191, 4571273, 5175424, 6520760, 5175424, 6690820, 4181191, 6255224, 6130948, 6130948, 6130948, 6130948, 4004021], [5024933, 5677955, 5677955, 6413672, 5351213, 6520760, 7690043, 6520760, 5341289, 5216608, 7378826, 7886530, 5351213, 6322908, 6322908, 5135839, 4196299], [8469470, 7992913, 8079764, 7979838, 8079764, 8859163, 8859163, 8148623, 9988635, 5493749, 6910544, 8922618, 7243631, 7243631, 7243631, 7243631, 5613814], [8469470, 8637255, 8079764, 8079764, 7878698, 8079764, 8079764, 9638516, 11467362, 8014823, 7690043, 7888167, 9703628, 8469470, 8250903, 5893502, 5741101], [8079764, 7554168, 7554168, 7300303, 7300303, 6740866, 7604530, 9248844, 11202017, 7980198, 7690043, 7697303, 9248844, 9856837, 9602467, 7681974, 4961275], [8336264, 8079764, 6910544, 7102925, 8079764, 8270335, 7300303, 6910544, 14007558, 8079764, 6520760, 6650760, 4647519, 7272289, 7563029, 8847625, 4571273], [5306117, 5306117, 5997097, 5288569, 5306117, 5803103, 7397963, 4571273, 9541922, 5351213, 6910544, 7506268, 6130948, 6130948, 6130948, 6130948, 4206923], [5090797, 5745957, 5887826, 5431381, 6130948, 5351213, 5604295, 7144195, 12748621, 9092876, 5741101, 9720640, 8264733, 8264733, 8264733, 8264733, 4251777], [5826966, 5741101, 6130948, 5741101, 6486012, 6038231, 7690043, 4643855, 6234666, 4961275, 6257821, 6520760, 6650311, 6650311, 6650311, 6650311, 4282070], [6520760, 6325976, 6325976, 6325976, 5741101, 7320748, 5763381, 5962177, 4257665, 5351213, 6548447, 7394243, 5351213, 6210022, 6210022, 6210022, 4688567], [7642816, 7642816, 6910544, 7300303, 6520760, 8079764, 6619566, 7936061, 10639098, 5847981, 7357137, 8920407, 6130948, 6596051, 6596051, 6596051, 4980018], [8079764, 8079764, 8079764, 8079764, 8841512, 7690043, 7690043, 8859163, 10542087, 7208927, 8469470, 9555698, 6775576, 8859123, 8630500, 6712612, 5741101], [9248844, 8313220, 8469470, 8469470, 8469470, 9248844, 9493297, 6910544, 13326222, 7690043, 9447616, 9447616, 6292260, 8859163, 8959806, 7910900, 6130948], [8859163, 8079764, 8270335, 8079764, 8079764, 7690043, 8036678, 10028177, 13665744, 10028177, 7690043, 7690043, 5132828, 7701968, 8693162, 8285749, 5351213], [7690043, 8072269, 8072269, 8072269, 8294073, 7109206, 7300303, 7300303, 15582072, 8469470, 8469470, 12123102, 9820147, 5351213, 6910544, 7300303, 4961275], [7300303, 6910544, 7803257, 8126527, 7690043, 8079764, 9311309, 6130948, 11906283, 6910544, 9239474, 9239474, 5741101, 8120378, 8131568, 11646251, 5741101], [7690043, 7690043, 7690043, 7209286, 8133227, 6910544, 7300303, 8792152, 10537653, 7102830, 8079764, 8907246, 10703823, 7300303, 8564921, 6529255, 5741101], [7690043, 7690043, 7111069, 7690043, 7110846, 8021250, 10084517, 8079764, 6437272, 6910544, 8727396, 8972744, 5815593, 8051744, 8065187, 6400077, 5741101], [8469470, 8469470, 8192502, 7562266, 8529828, 7300303, 7300303, 8757436, 14479922, 11134138, 6520760, 7574827, 6732913, 9248844, 7164984, 7354785, 6130948], [7690043, 7690043, 7690043, 7690043, 8079764, 6910544, 7300303, 8828528, 10625485, 6782879, 7690043, 9057693, 6176841, 8798641, 9923868, 6972972, 6130948], [8469470, 8079764, 8859163, 8859163, 9084874, 8859163, 7314489, 8079764, 14711331, 10282113, 6862942, 7916576, 5209618, 7910900, 8120460, 6960395, 6130948], [8859163, 8859163, 8859163, 9034159, 7690043, 9556779, 9556779, 8859163, 13452385, 9103554, 8469470, 12135239, 9638516, 6520760, 10364121, 8079764, 6520760], [8469470, 8469470, 8079764, 8079764, 8469470, 8640420, 7690043, 7690043, 15582072, 9638516, 8381817, 8171520, 10028177, 6910544, 5706772, 6520760, 5741101], [8079764, 8079764, 8079764, 8307947, 8307947, 7300303, 7690043, 8079764, 9909144, 6524033, 7894203, 7690043, 9054747, 7032162, 5741101, 6998626, 5351213], [9638516, 9248844, 9248844, 9239097, 10417831, 9248844, 8079764, 8079764, 15206070, 9118362, 11586752, 12087055, 8079764, 11976381, 11638758, 10240346, 6910544], [9451799, 9276766, 8079764, 8115804, 8923237, 8469470, 8079764, 10028177, 15582072, 12744687, 8973423, 15582072, 11140471, 7300303, 6520760, 7402944, 6520760], [8859163, 9068435, 9068435, 8893234, 10028177, 9248844, 8079764, 10662857, 10662857, 8866606, 8193241, 8912870, 10417831, 8859163, 9992816, 6243860, 6910544], [8859163, 8859163, 8859163, 8859163, 8365522, 7690043, 8079764, 9638516, 15582072, 12253569, 9785621, 10053565, 7300303, 6910544, 7104166, 7845461, 6910544], [8859163, 9068435, 9068435, 9248844, 9484484, 9248844, 9248844, 9638516, 9638516, 8221087, 8079764, 8287203, 10282244, 8859163, 9992721, 7690043, 6910544], [8939382, 8939382, 8079764, 8079764, 6959947, 8469470, 8859163, 8499233, 15582072, 10807478, 7928084, 8146361, 10028177, 7690043, 6315002, 7614739, 6520760], [9638516, 8859163, 9066850, 8859163, 8859163, 8469470, 8469470, 10417831, 15582072, 12755625, 8915222, 8915222, 5950591, 8917009, 10055112, 10096660, 6520760], [9045573, 9045573, 9248844, 9248844, 7826186, 9638516, 9415298, 8630988, 13602652, 8859163, 8859163, 12083580, 9638516, 8079764, 6849072, 5337857, 6130948], [8617013, 8894137, 8859163, 8859163, 8859163, 8079764, 8079764, 6910544, 12477370, 6910544, 9721453, 11198675, 7754356, 10028177, 10028177, 11197118, 5741101], [11197118, 10807478, 10389324, 11586752, 11523149, 9638516, 8859163, 9248844, 15582072, 10430177, 13829434, 15582072, 14646763, 9638516, 11595602, 8469470, 7690043], [10807478, 10621674, 10807478, 10417831, 9931155, 12048979, 10028177, 9235663, 15582072, 10414438, 12755625, 13152758, 10807478, 10807478, 11002844, 8469470, 7690043], [10035919, 10225276, 10225276, 9638516, 10869800, 9587102, 10807478, 12755625, 12813627, 10770074, 9528712, 10417831, 12111129, 10417831, 11747872, 7508591, 7690043], [10028177, 10217388, 10217388, 9842536, 9184655, 11003619, 9638516, 10807478, 10807478, 9083872, 11414395, 11401376, 8859163, 9383969, 10581227, 7690043, 7300303], [10028177, 10028177, 9248844, 9564941, 10028177, 9796758, 8859163, 9732499, 15582072, 12366005, 10676098, 10955941, 7690043, 8079764, 8116637, 5741101, 7300303], [8469470, 8469470, 8469470, 8469470, 8859163, 8469470, 9130819, 10807478, 15582072, 11976381, 7690043, 8680516, 11586752, 8079764, 13729557, 10983645, 6910544], [9248844, 9248844, 9248844, 9465091, 9638516, 9820374, 8859163, 10028177, 12110953, 8286441, 8469470, 15582072, 11197118, 9248844, 8995946, 5943129, 6910544], [9248844, 8996112, 8996112, 8759952, 7764161, 9248844, 9248844, 6910544, 13269529, 7542680, 9248844, 7690795, 9192063, 9708182, 9765639, 11866350, 6130948], [8859163, 8859163, 9149925, 8469470, 8469470, 8079764, 8469470, 9248844, 11081163, 7481550, 8195219, 15582072, 9638516, 9248844, 9027580, 6247564, 5741101], [11988859, 11586752, 11976381, 11262956, 10807478, 11976381, 14691013, 10281200, 15582072, 11586752, 14351590, 15582072, 15582072, 9090688, 9090688, 9248844, 8859163], [11746759, 11332099, 11586752, 10896956, 10417831, 11197118, 11666487, 13803718, 15582072, 11586752, 12755625, 14140734, 15582072, 13924463, 13548790, 9629432, 8469470], [10412581, 10028177, 10028177, 9610800, 10836924, 9273906, 9248844, 10258054, 13004304, 8469470, 11197118, 12623883, 10282454, 11197118, 11464410, 8859163, 8079764], [10807478, 10529176, 10529176, 10529176, 9934183, 11197118, 12366005, 8859163, 15582072, 9992575, 12381707, 14567311, 9817310, 12366005, 10482442, 8169542, 8079764], [9638516, 9248844, 9501131, 8893130, 10028177, 8859163, 9248844, 10721280, 12948008, 8859163, 9638516, 15582072, 13809245, 9638516, 10869944, 7373976, 7690043], [9638516, 10028177, 9389844, 9248844, 8548331, 8469470, 9995970, 9638516, 13001278, 8690328, 10653907, 8859163, 8079764, 8079764, 8079764, 5479257, 7300303], [9638516, 9248844, 9248844, 9248844, 9248844, 9248844, 9562222, 11586752, 15582072, 11889259, 7300303, 8241660, 8729259, 10028177, 15582072, 13375245, 6910544], [9638516, 9248844, 8859163, 8859163, 9101465, 8079764, 8469470, 7604530, 15582072, 9248844, 11044999, 14303999, 11586752, 6313875, 6130948, 8469470, 6520760], [8260187, 8206573, 8469470, 8469470, 8469470, 8469470, 8469470, 9248844, 11081163, 7295673, 9638516, 10869800, 9638516, 7690043, 7878524, 5184577, 6130948]]

def degreeRate (rect : Fin 54) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 54) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem rate0 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 0 i.val : ℚ) ∧
    min (seedLimit 0) (dotQ (cutWeight 0 0 i.val) (history 0 i.val)) ≤ (degreeRate 0 i.val : ℚ) ∧
    heightBound (degreeRate 0 i.val) ≤ (heightRate 0 i.val : ℚ) := by
  have hs : seedLimit 0 = (3039012894213 / 10472 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate1 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 1 i.val : ℚ) ∧
    min (seedLimit 1) (dotQ (cutWeight 1 0 i.val) (history 1 i.val)) ≤ (degreeRate 1 i.val : ℚ) ∧
    heightBound (degreeRate 1 i.val) ≤ (heightRate 1 i.val : ℚ) := by
  have hs : seedLimit 1 = (2094691531153 / 7480 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate2 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 2 i.val : ℚ) ∧
    min (seedLimit 2) (dotQ (cutWeight 2 0 i.val) (history 2 i.val)) ≤ (degreeRate 2 i.val : ℚ) ∧
    heightBound (degreeRate 2 i.val) ≤ (heightRate 2 i.val : ℚ) := by
  have hs : seedLimit 2 = (22247900547721 / 85680 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate3 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 3 i.val : ℚ) ∧
    min (seedLimit 3) (dotQ (cutWeight 3 0 i.val) (history 3 i.val)) ≤ (degreeRate 3 i.val : ℚ) ∧
    heightBound (degreeRate 3 i.val) ≤ (heightRate 3 i.val : ℚ) := by
  have hs : seedLimit 3 = (280423920587 / 1224 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate4 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 4 i.val : ℚ) ∧
    min (seedLimit 4) (dotQ (cutWeight 4 0 i.val) (history 4 i.val)) ≤ (degreeRate 4 i.val : ℚ) ∧
    heightBound (degreeRate 4 i.val) ≤ (heightRate 4 i.val : ℚ) := by
  have hs : seedLimit 4 = (3000518655100553 / 13948704 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate5 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 5 i.val : ℚ) ∧
    min (seedLimit 5) (dotQ (cutWeight 5 0 i.val) (history 5 i.val)) ≤ (degreeRate 5 i.val : ℚ) ∧
    heightBound (degreeRate 5 i.val) ≤ (heightRate 5 i.val : ℚ) := by
  have hs : seedLimit 5 = (245025020577 / 2380 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate6 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 6 i.val : ℚ) ∧
    min (seedLimit 6) (dotQ (cutWeight 6 0 i.val) (history 6 i.val)) ≤ (degreeRate 6 i.val : ℚ) ∧
    heightBound (degreeRate 6 i.val) ≤ (heightRate 6 i.val : ℚ) := by
  have hs : seedLimit 6 = (713861083786297 / 16190460 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate7 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 7 i.val : ℚ) ∧
    min (seedLimit 7) (dotQ (cutWeight 7 0 i.val) (history 7 i.val)) ≤ (degreeRate 7 i.val : ℚ) ∧
    heightBound (degreeRate 7 i.val) ≤ (heightRate 7 i.val : ℚ) := by
  have hs : seedLimit 7 = (9796456131619 / 278460 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate8 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 8 i.val : ℚ) ∧
    min (seedLimit 8) (dotQ (cutWeight 8 0 i.val) (history 8 i.val)) ≤ (degreeRate 8 i.val : ℚ) ∧
    heightBound (degreeRate 8 i.val) ≤ (heightRate 8 i.val : ℚ) := by
  have hs : seedLimit 8 = (726426143291903 / 25185160 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate9 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 9 i.val : ℚ) ∧
    min (seedLimit 9) (dotQ (cutWeight 9 0 i.val) (history 9 i.val)) ≤ (degreeRate 9 i.val : ℚ) ∧
    heightBound (degreeRate 9 i.val) ≤ (heightRate 9 i.val : ℚ) := by
  have hs : seedLimit 9 = (86075514658327 / 471240 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate10 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 10 i.val : ℚ) ∧
    min (seedLimit 10) (dotQ (cutWeight 10 0 i.val) (history 10 i.val)) ≤ (degreeRate 10 i.val : ℚ) ∧
    heightBound (degreeRate 10 i.val) ≤ (heightRate 10 i.val : ℚ) := by
  have hs : seedLimit 10 = (171501477245957 / 942480 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate11 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 11 i.val : ℚ) ∧
    min (seedLimit 11) (dotQ (cutWeight 11 0 i.val) (history 11 i.val)) ≤ (degreeRate 11 i.val : ℚ) ∧
    heightBound (degreeRate 11 i.val) ≤ (heightRate 11 i.val : ℚ) := by
  have hs : seedLimit 11 = (8999606782627 / 52360 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate12 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 12 i.val : ℚ) ∧
    min (seedLimit 12) (dotQ (cutWeight 12 0 i.val) (history 12 i.val)) ≤ (degreeRate 12 i.val : ℚ) ∧
    heightBound (degreeRate 12 i.val) ≤ (heightRate 12 i.val : ℚ) := by
  have hs : seedLimit 12 = (46780103736761 / 314160 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate13 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 13 i.val : ℚ) ∧
    min (seedLimit 13) (dotQ (cutWeight 13 0 i.val) (history 13 i.val)) ≤ (degreeRate 13 i.val : ℚ) ∧
    heightBound (degreeRate 13 i.val) ≤ (heightRate 13 i.val : ℚ) := by
  have hs : seedLimit 13 = (220645636039 / 1760 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate14 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 14 i.val : ℚ) ∧
    min (seedLimit 14) (dotQ (cutWeight 14 0 i.val) (history 14 i.val)) ≤ (degreeRate 14 i.val : ℚ) ∧
    heightBound (degreeRate 14 i.val) ≤ (heightRate 14 i.val : ℚ) := by
  have hs : seedLimit 14 = (705685134251 / 8976 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate15 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 15 i.val : ℚ) ∧
    min (seedLimit 15) (dotQ (cutWeight 15 0 i.val) (history 15 i.val)) ≤ (degreeRate 15 i.val : ℚ) ∧
    heightBound (degreeRate 15 i.val) ≤ (heightRate 15 i.val : ℚ) := by
  have hs : seedLimit 15 = (1461997293375737 / 32380920 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate16 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 16 i.val : ℚ) ∧
    min (seedLimit 16) (dotQ (cutWeight 16 0 i.val) (history 16 i.val)) ≤ (degreeRate 16 i.val : ℚ) ∧
    heightBound (degreeRate 16 i.val) ≤ (heightRate 16 i.val : ℚ) := by
  have hs : seedLimit 16 = (6993864086195 / 179894 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate17 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 17 i.val : ℚ) ∧
    min (seedLimit 17) (dotQ (cutWeight 17 0 i.val) (history 17 i.val)) ≤ (degreeRate 17 i.val : ℚ) ∧
    heightBound (degreeRate 17 i.val) ≤ (heightRate 17 i.val : ℚ) := by
  have hs : seedLimit 17 = (877067309519 / 27846 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate18 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 18 i.val : ℚ) ∧
    min (seedLimit 18) (dotQ (cutWeight 18 0 i.val) (history 18 i.val)) ≤ (degreeRate 18 i.val : ℚ) ∧
    heightBound (degreeRate 18 i.val) ≤ (heightRate 18 i.val : ℚ) := by
  have hs : seedLimit 18 = (1792675682901199 / 17435880 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate19 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 19 i.val : ℚ) ∧
    min (seedLimit 19) (dotQ (cutWeight 19 0 i.val) (history 19 i.val)) ≤ (degreeRate 19 i.val : ℚ) ∧
    heightBound (degreeRate 19 i.val) ≤ (heightRate 19 i.val : ℚ) := by
  have hs : seedLimit 19 = (1475757395124183 / 14391520 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate20 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 20 i.val : ℚ) ∧
    min (seedLimit 20) (dotQ (cutWeight 20 0 i.val) (history 20 i.val)) ≤ (degreeRate 20 i.val : ℚ) ∧
    heightBound (degreeRate 20 i.val) ≤ (heightRate 20 i.val : ℚ) := by
  have hs : seedLimit 20 = (11464437405020191 / 113333220 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate21 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 21 i.val : ℚ) ∧
    min (seedLimit 21) (dotQ (cutWeight 21 0 i.val) (history 21 i.val)) ≤ (degreeRate 21 i.val : ℚ) ∧
    heightBound (degreeRate 21 i.val) ≤ (heightRate 21 i.val : ℚ) := by
  have hs : seedLimit 21 = (4908882740467081 / 50370320 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate22 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 22 i.val : ℚ) ∧
    min (seedLimit 22) (dotQ (cutWeight 22 0 i.val) (history 22 i.val)) ≤ (degreeRate 22 i.val : ℚ) ∧
    heightBound (degreeRate 22 i.val) ≤ (heightRate 22 i.val : ℚ) := by
  have hs : seedLimit 22 = (24825290015927 / 311355 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate23 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 23 i.val : ℚ) ∧
    min (seedLimit 23) (dotQ (cutWeight 23 0 i.val) (history 23 i.val)) ≤ (degreeRate 23 i.val : ℚ) ∧
    heightBound (degreeRate 23 i.val) ≤ (heightRate 23 i.val : ℚ) := by
  have hs : seedLimit 23 = (2884254369546845 / 45333288 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate24 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 24 i.val : ℚ) ∧
    min (seedLimit 24) (dotQ (cutWeight 24 0 i.val) (history 24 i.val)) ≤ (degreeRate 24 i.val : ℚ) ∧
    heightBound (degreeRate 24 i.val) ≤ (heightRate 24 i.val : ℚ) := by
  have hs : seedLimit 24 = (99619488094433 / 2042040 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate25 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 25 i.val : ℚ) ∧
    min (seedLimit 25) (dotQ (cutWeight 25 0 i.val) (history 25 i.val)) ≤ (degreeRate 25 i.val : ℚ) ∧
    heightBound (degreeRate 25 i.val) ≤ (heightRate 25 i.val : ℚ) := by
  have hs : seedLimit 25 = (646084451980667 / 16190460 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate26 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 26 i.val : ℚ) ∧
    min (seedLimit 26) (dotQ (cutWeight 26 0 i.val) (history 26 i.val)) ≤ (degreeRate 26 i.val : ℚ) ∧
    heightBound (degreeRate 26 i.val) ≤ (heightRate 26 i.val : ℚ) := by
  have hs : seedLimit 26 = (2543506502127053 / 75555480 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate27 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 27 i.val : ℚ) ∧
    min (seedLimit 27) (dotQ (cutWeight 27 0 i.val) (history 27 i.val)) ≤ (degreeRate 27 i.val : ℚ) ∧
    heightBound (degreeRate 27 i.val) ≤ (heightRate 27 i.val : ℚ) := by
  have hs : seedLimit 27 = (260799969145609 / 3597880 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate28 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 28 i.val : ℚ) ∧
    min (seedLimit 28) (dotQ (cutWeight 28 0 i.val) (history 28 i.val)) ≤ (degreeRate 28 i.val : ℚ) ∧
    heightBound (degreeRate 28 i.val) ≤ (heightRate 28 i.val : ℚ) := by
  have hs : seedLimit 28 = (157571512368317 / 2324784 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate29 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 29 i.val : ℚ) ∧
    min (seedLimit 29) (dotQ (cutWeight 29 0 i.val) (history 29 i.val)) ≤ (degreeRate 29 i.val : ℚ) ∧
    heightBound (degreeRate 29 i.val) ≤ (heightRate 29 i.val : ℚ) := by
  have hs : seedLimit 29 = (2470968312656579 / 34871760 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate30 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 30 i.val : ℚ) ∧
    min (seedLimit 30) (dotQ (cutWeight 30 0 i.val) (history 30 i.val)) ≤ (degreeRate 30 i.val : ℚ) ∧
    heightBound (degreeRate 30 i.val) ≤ (heightRate 30 i.val : ℚ) := by
  have hs : seedLimit 30 = (321835826656133 / 4649568 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate31 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 31 i.val : ℚ) ∧
    min (seedLimit 31) (dotQ (cutWeight 31 0 i.val) (history 31 i.val)) ≤ (degreeRate 31 i.val : ℚ) ∧
    heightBound (degreeRate 31 i.val) ≤ (heightRate 31 i.val : ℚ) := by
  have hs : seedLimit 31 = (62817093976687 / 942480 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate32 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 32 i.val : ℚ) ∧
    min (seedLimit 32) (dotQ (cutWeight 32 0 i.val) (history 32 i.val)) ≤ (degreeRate 32 i.val : ℚ) ∧
    heightBound (degreeRate 32 i.val) ≤ (heightRate 32 i.val : ℚ) := by
  have hs : seedLimit 32 = (12465351885882221 / 226666440 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate33 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 33 i.val : ℚ) ∧
    min (seedLimit 33) (dotQ (cutWeight 33 0 i.val) (history 33 i.val)) ≤ (degreeRate 33 i.val : ℚ) ∧
    heightBound (degreeRate 33 i.val) ≤ (heightRate 33 i.val : ℚ) := by
  have hs : seedLimit 33 = (3482899944722651 / 75555480 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate34 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 34 i.val : ℚ) ∧
    min (seedLimit 34) (dotQ (cutWeight 34 0 i.val) (history 34 i.val)) ≤ (degreeRate 34 i.val : ℚ) ∧
    heightBound (degreeRate 34 i.val) ≤ (heightRate 34 i.val : ℚ) := by
  have hs : seedLimit 34 = (27231757590593 / 622710 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate35 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 35 i.val : ℚ) ∧
    min (seedLimit 35) (dotQ (cutWeight 35 0 i.val) (history 35 i.val)) ≤ (degreeRate 35 i.val : ℚ) ∧
    heightBound (degreeRate 35 i.val) ≤ (heightRate 35 i.val : ℚ) := by
  have hs : seedLimit 35 = (5885739186426083 / 151110960 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate36 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 36 i.val : ℚ) ∧
    min (seedLimit 36) (dotQ (cutWeight 36 0 i.val) (history 36 i.val)) ≤ (degreeRate 36 i.val : ℚ) ∧
    heightBound (degreeRate 36 i.val) ≤ (heightRate 36 i.val : ℚ) := by
  have hs : seedLimit 36 = (412491890219549 / 7195760 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate37 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 37 i.val : ℚ) ∧
    min (seedLimit 37) (dotQ (cutWeight 37 0 i.val) (history 37 i.val)) ≤ (degreeRate 37 i.val : ℚ) ∧
    heightBound (degreeRate 37 i.val) ≤ (heightRate 37 i.val : ℚ) := by
  have hs : seedLimit 37 = (579867624741785 / 10074064 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate38 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 38 i.val : ℚ) ∧
    min (seedLimit 38) (dotQ (cutWeight 38 0 i.val) (history 38 i.val)) ≤ (degreeRate 38 i.val : ℚ) ∧
    heightBound (degreeRate 38 i.val) ≤ (heightRate 38 i.val : ℚ) := by
  have hs : seedLimit 38 = (1651297129104398 / 28333305 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate39 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 39 i.val : ℚ) ∧
    min (seedLimit 39) (dotQ (cutWeight 39 0 i.val) (history 39 i.val)) ≤ (degreeRate 39 i.val : ℚ) ∧
    heightBound (degreeRate 39 i.val) ≤ (heightRate 39 i.val : ℚ) := by
  have hs : seedLimit 39 = (6432230807919713 / 113333220 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate40 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 40 i.val : ℚ) ∧
    min (seedLimit 40) (dotQ (cutWeight 40 0 i.val) (history 40 i.val)) ≤ (degreeRate 40 i.val : ℚ) ∧
    heightBound (degreeRate 40 i.val) ≤ (heightRate 40 i.val : ℚ) := by
  have hs : seedLimit 40 = (10235951927427491 / 181333152 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate41 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 41 i.val : ℚ) ∧
    min (seedLimit 41) (dotQ (cutWeight 41 0 i.val) (history 41 i.val)) ≤ (degreeRate 41 i.val : ℚ) ∧
    heightBound (degreeRate 41 i.val) ≤ (heightRate 41 i.val : ℚ) := by
  have hs : seedLimit 41 = (514492432988461 / 10074064 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate42 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 42 i.val : ℚ) ∧
    min (seedLimit 42) (dotQ (cutWeight 42 0 i.val) (history 42 i.val)) ≤ (degreeRate 42 i.val : ℚ) ∧
    heightBound (degreeRate 42 i.val) ≤ (heightRate 42 i.val : ℚ) := by
  have hs : seedLimit 42 = (788382340194763 / 17435880 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate43 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 43 i.val : ℚ) ∧
    min (seedLimit 43) (dotQ (cutWeight 43 0 i.val) (history 43 i.val)) ≤ (degreeRate 43 i.val : ℚ) ∧
    heightBound (degreeRate 43 i.val) ≤ (heightRate 43 i.val : ℚ) := by
  have hs : seedLimit 43 = (3181856151381289 / 75555480 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate44 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 44 i.val : ℚ) ∧
    min (seedLimit 44) (dotQ (cutWeight 44 0 i.val) (history 44 i.val)) ≤ (degreeRate 44 i.val : ℚ) ∧
    heightBound (degreeRate 44 i.val) ≤ (heightRate 44 i.val : ℚ) := by
  have hs : seedLimit 44 = (168964806622709 / 4358970 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate45 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 45 i.val : ℚ) ∧
    min (seedLimit 45) (dotQ (cutWeight 45 0 i.val) (history 45 i.val)) ≤ (degreeRate 45 i.val : ℚ) ∧
    heightBound (degreeRate 45 i.val) ≤ (heightRate 45 i.val : ℚ) := by
  have hs : seedLimit 45 = (41796519484312 / 765765 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate46 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 46 i.val : ℚ) ∧
    min (seedLimit 46) (dotQ (cutWeight 46 0 i.val) (history 46 i.val)) ≤ (degreeRate 46 i.val : ℚ) ∧
    heightBound (degreeRate 46 i.val) ≤ (heightRate 46 i.val : ℚ) := by
  have hs : seedLimit 46 = (224665799281169 / 4317456 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate47 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 47 i.val : ℚ) ∧
    min (seedLimit 47) (dotQ (cutWeight 47 0 i.val) (history 47 i.val)) ≤ (degreeRate 47 i.val : ℚ) ∧
    heightBound (degreeRate 47 i.val) ≤ (heightRate 47 i.val : ℚ) := by
  have hs : seedLimit 47 = (4495068559249469 / 90666576 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate48 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 48 i.val : ℚ) ∧
    min (seedLimit 48) (dotQ (cutWeight 48 0 i.val) (history 48 i.val)) ≤ (degreeRate 48 i.val : ℚ) ∧
    heightBound (degreeRate 48 i.val) ≤ (heightRate 48 i.val : ℚ) := by
  have hs : seedLimit 48 = (491243016503563 / 9444435 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate49 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 49 i.val : ℚ) ∧
    min (seedLimit 49) (dotQ (cutWeight 49 0 i.val) (history 49 i.val)) ≤ (degreeRate 49 i.val : ℚ) ∧
    heightBound (degreeRate 49 i.val) ≤ (heightRate 49 i.val : ℚ) := by
  have hs : seedLimit 49 = (1405341518785066 / 28333305 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate50 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 50 i.val : ℚ) ∧
    min (seedLimit 50) (dotQ (cutWeight 50 0 i.val) (history 50 i.val)) ≤ (degreeRate 50 i.val : ℚ) ∧
    heightBound (degreeRate 50 i.val) ≤ (heightRate 50 i.val : ℚ) := by
  have hs : seedLimit 50 = (383072136242297 / 7749280 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate51 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 51 i.val : ℚ) ∧
    min (seedLimit 51) (dotQ (cutWeight 51 0 i.val) (history 51 i.val)) ≤ (degreeRate 51 i.val : ℚ) ∧
    heightBound (degreeRate 51 i.val) ≤ (heightRate 51 i.val : ℚ) := by
  have hs : seedLimit 51 = (10100146801986173 / 226666440 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate52 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 52 i.val : ℚ) ∧
    min (seedLimit 52) (dotQ (cutWeight 52 0 i.val) (history 52 i.val)) ≤ (degreeRate 52 i.val : ℚ) ∧
    heightBound (degreeRate 52 i.val) ≤ (heightRate 52 i.val : ℚ) := by
  have hs : seedLimit 52 = (1446643450099531 / 32380920 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem rate53 (i:Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate 53 i.val : ℚ) ∧
    min (seedLimit 53) (dotQ (cutWeight 53 0 i.val) (history 53 i.val)) ≤ (degreeRate 53 i.val : ℚ) ∧
    heightBound (degreeRate 53 i.val) ≤ (heightRate 53 i.val : ℚ) := by
  have hs : seedLimit 53 = (7464861551383 / 181152 : ℚ) := by decide +kernel
  fin_cases i <;> (rw [hs]; decide +kernel)
private theorem checked_rates (rect : Fin 54) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect
  · exact rate0 i
  · exact rate1 i
  · exact rate2 i
  · exact rate3 i
  · exact rate4 i
  · exact rate5 i
  · exact rate6 i
  · exact rate7 i
  · exact rate8 i
  · exact rate9 i
  · exact rate10 i
  · exact rate11 i
  · exact rate12 i
  · exact rate13 i
  · exact rate14 i
  · exact rate15 i
  · exact rate16 i
  · exact rate17 i
  · exact rate18 i
  · exact rate19 i
  · exact rate20 i
  · exact rate21 i
  · exact rate22 i
  · exact rate23 i
  · exact rate24 i
  · exact rate25 i
  · exact rate26 i
  · exact rate27 i
  · exact rate28 i
  · exact rate29 i
  · exact rate30 i
  · exact rate31 i
  · exact rate32 i
  · exact rate33 i
  · exact rate34 i
  · exact rate35 i
  · exact rate36 i
  · exact rate37 i
  · exact rate38 i
  · exact rate39 i
  · exact rate40 i
  · exact rate41 i
  · exact rate42 i
  · exact rate43 i
  · exact rate44 i
  · exact rate45 i
  · exact rate46 i
  · exact rate47 i
  · exact rate48 i
  · exact rate49 i
  · exact rate50 i
  · exact rate51 i
  · exact rate52 i
  · exact rate53 i

theorem rate_spec (rect : Fin 54) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179769)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179769-endpointDegree : ℕ)

def rankB (rect : Fin 54) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 54) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 54) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 54) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 54) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 54) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 54) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 54) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

def paidCap : Fin 54 → ℕ := ![55793924646092275,52966495969959153,49288464967547301,38810346942555605,28105265459992834,13206613370585709,5933515518403897,5235984048072161,4561869216803883,27875885778979703,27281212382701115,25923318675865290,21737866497188014,16642479830436074,9940541874649818,5744268724374942,5327907282339369,4722732019234886,12971243220374339,12752171936355248,12637645649694967,11670208228550418,9840921658962126,7878171165247421,5828038718101279,5365702251384505,4877651877782013,7837859755555625,7712204582539976,7933252180329457,7765540692437988,7415482185496329,6578449850475856,5373350808195588,5501308014295807,5183184408781634,5611203065645877,5705330680314931,5962380426836631,5930963484758957,6034727864104571,5854587034500465,5205644515912856,5193076709205624,5115030531490045,4817022442938847,4777699928008097,4917739195484850,5048245675359167,5137483949503584,5374518812809944,4968408715399305,5294229975626841,5223746972126276]
def retainedCredit : Fin 54 → ℕ := ![2203492493860,2359182270245,2376099868615,2475696935960,2554050539555,3176395990275,3234294189700,2882821816310,2712702142845,2558545636200,2577523319005,2590340332650,2763866044610,2891191446610,3234294189700,3414264917535,3056948333700,2882821816310,3234294189700,3234294189700,3234294189700,3414264917535,3414264917535,3414264917535,3596403450385,3234294189700,3056948333700,3780354068890,3596403450385,3780354068890,3780354068890,3780354068890,3596403450385,3596403450385,3414264917535,3234294189700,4152616915935,4152616915935,4152616915935,3965833672700,3965833672700,3780354068890,3780354068890,3414264917535,3234294189700,4719101025785,4529388060400,4340518392025,4340518392025,4152616915935,3965833672700,3780354068890,3596403450385,3414264917535]
theorem rescue_fee_bound (r : Fin 54) : rescueFee r≤paidCap r := by
  fin_cases r <;> decide +kernel
theorem credit_guard (r : Fin 54) : (retainedCredit r:ℚ)≤
    P1_7_4.running (beforeCuts (rankWeight r) (lossWeight r)) 18 1 := by
  fin_cases r <;> decide +kernel
theorem rank_guard (rect : Fin 54) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel


end Lower6960.Rescue6966

end
end Merged_High6966RescueInvoice

-- merged module High6966Credit
section Merged_High6966Credit

namespace Lower6960.Rescue6966
open P1_7_4 (Mass running dotQ massQ)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass)
theorem credit_one (v : ℕ → Mass) (n C : ℕ) (S : Finset (Ideal Ambient))
    (h : (C:ℚ)≤running v n 1) : (C:ℚ)*(mass S 1:ℚ)≤dotQ (running v n) (massQ S) := by
  have nonneg (i : ℕ) (k : Fin 4) : 0≤running v i k := by
    induction i with
    | zero => rfl
    | succ i ih => exact ih.trans (le_max_left _ _)
  exact (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)).trans
    (Finset.single_le_sum (f:=fun k => running v n k * massQ S k)
      (fun k _ => mul_nonneg (nonneg _ _) (Nat.cast_nonneg _)) (Finset.mem_univ 1))
end Lower6960.Rescue6966

end Merged_High6966Credit

-- merged module High6966RescueCharge
section Merged_High6966RescueCharge
section Merged_R6960Rescue6966Fee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open P1_7_4_3 (mix)
open HighCore82268JointRank (fixed_fee_linear)
open Lower6960.Rescue6966 (persistentTotal persistentTop siteRatio density)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>∃ J∈ini.rankExit,OnMark F J γ)
theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) (hi : M.overhead.toNat≤2499) :
    (ini.rankMarks.card : ℚ)≤dotQ (rankWeight rect) (massQ ini.rankExit)+rankRound rect := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap rect k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB rect := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ rect := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard rect
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau (pivot rect) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight rect 1 * J + rankWeight rect 2 * B + 2*lambda*pivot rect^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ (rankWeight rect) (massQ ini.rankExit) =
      rankWeight rect 1 * (mass S 1 : ℚ)+rankWeight rect 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hiM : M.overhead.toNat≤2499) {i : ℕ} (hi : i<17) :
    ((curveMarks F (C.cover i)).card : ℚ)≤
      dotQ (lossWeight R.rect i) (massQ (R.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit R.rect :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight R.rect 0 i) (history R.rect i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (R.live_history hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt (seed_limit_small R.rect)
  obtain ⟨ok,degree⟩ := rate_spec R.rect hi
  have count := rated_curve_count F (curve_tariff F hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate R.rect i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate R.rect i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate R.rect i : ℚ)*dotQ (cutWeight R.rect 0 i) (massQ (R.lost i)) +
          (heightRate R.rect i : ℚ)*dotQ (cutWeight R.rect 1 i) (massQ (R.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := R.initial.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks F (C.cover i))
theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤2499) : C.lossMarks.card + (retainedCredit R.rect)*K1_14_2_2.mass R.final 1 ≤ (lossLimit R.rect).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (R.initial.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks F (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ R.initial.rankMarks.card +
      ∑ i∈range 17,(curveMarks F (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (R.initial.rank_count hi) sum_cuts
  have joint := R.joint_bill_with_final (rankWeight R.rect) (lossWeight R.rect)
  have seed := C.seed_bill
  have total := cum.trans both
  have keep:=Lower6960.Rescue6966.credit_one (beforeCuts (rankWeight R.rect) (lossWeight R.rect)) 18 ((retainedCredit R.rect)) R.final (credit_guard R.rect)
  push_cast
  unfold lossLimit
  linarith only [total,joint,seed,keep]
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := ((C.lossMarks ∪ C.pointMarks) ∪ R.initial.seedMarks) ∪ R.initial.ordinateMarks
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤2499) : C.paid.card+(retainedCredit R.rect)*K1_14_2_2.mass R.final 1≤rescueFee R.rect := by
  have h1 := card_union_le ((C.lossMarks∪C.pointMarks)∪R.initial.seedMarks) R.initial.ordinateMarks
  have h2 := card_union_le (C.lossMarks∪C.pointMarks) R.initial.seedMarks
  have h3 := card_union_le C.lossMarks C.pointMarks
  have rate := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := R.initial.seed_count
  have ordinates := R.initial.ordinate_count
  unfold rescueFee CutBooks.paid
  omega
theorem Run.paid_packet {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (C : CutBooks R) (S : Finset Surface),
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈R.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈C.paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨C⟩:=R.cutBooks noPole residues
  obtain ⟨S,geo,orig,surf⟩:=R.terminal_surfaces_with_origins
  refine ⟨C,S,geo,orig,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hγ,seed⟩)))
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases R.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surf γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,on⟩
      · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩))))
      · have part : γ∈(range 17).biUnion (fun j => curveMarks F (C.cover j)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=F) hγ hQ on⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ part))))
end Lower6960.Rescue6966
end
end Merged_R6960Rescue6966Fee

end Merged_High6966RescueCharge
