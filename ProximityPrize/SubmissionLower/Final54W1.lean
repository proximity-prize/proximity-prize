import ProximityPrize.SubmissionLower.FadicVarCert

set_option autoImplicit false
set_option maxRecDepth 100000

namespace FadicGate.Final54W1

open FadicGate

def lvl1 : List Entry := [some (57, 23, 6)]
def lvl2 : List Entry := [some (122, 45, 10), none]
def lvl3 : List Entry := [some (178, 68, 17), some (88, 29, 7), none]
def lvl4 : List Entry := [some (230, 92, 23), some (146, 58, 15), none, none]
def lvl5 : List Entry := [some (298, 113, 29), some (217, 85, 21), some (120, 47, 12), none, none]
def lvl6 : List Entry := [some (354, 136, 36), some (280, 110, 28), some (170, 62, 16), none, none, none]
def lvl7 : List Entry := [some (410, 159, 43), some (336, 133, 35), some (265, 97, 25), some (136, 49, 13), none, none, none]
def lvl8 : List Entry := [some (479, 180, 48), some (415, 155, 42), some (299, 118, 30), some (210, 79, 19), none, none, none, none]
def lvl9 : List Entry := [some (535, 203, 55), some (471, 178, 49), some (387, 146, 38), some (252, 93, 24), some (136, 49, 13), none, none, none, none]
def lvl10 : List Entry := [some (603, 224, 61), some (536, 200, 53), some (440, 168, 46), some (353, 135, 36), some (252, 93, 24), none, none, none, none, none]
def lvl11 : List Entry := [some (659, 247, 68), some (603, 224, 61), some (511, 195, 52), some (411, 155, 40), some (285, 110, 28), some (136, 49, 13), none, none, none, none, none]
def lvl12 : List Entry := [some (715, 270, 75), some (659, 247, 68), some (579, 216, 58), some (459, 176, 48), some (328, 126, 33), some (267, 99, 26), none, none, none, none, none, none]
def lvl13 : List Entry := [some (783, 291, 81), some (715, 270, 75), some (646, 240, 66), some (559, 207, 56), some (435, 168, 45), some (328, 126, 33), some (136, 49, 13), none, none, none, none, none, none]
def lvl14 : List Entry := [some (839, 314, 88), some (783, 291, 81), some (698, 264, 72), some (615, 230, 63), some (517, 196, 52), some (367, 143, 37), some (267, 99, 26), none, none, none, none, none, none, none]
def lvl15 : List Entry := [some (895, 337, 95), some (839, 314, 88), some (765, 288, 80), some (672, 250, 68), some (570, 213, 59), some (410, 159, 42), some (367, 143, 37), some (136, 49, 13), none, none, none, none, none, none, none]
def lvl16 : List Entry := [some (951, 360, 102), some (895, 337, 95), some (821, 311, 87), some (741, 280, 77), some (615, 235, 65), some (529, 197, 52), some (410, 159, 42), some (267, 99, 26), none, none, none, none, none, none, none, none]
def lvl17 : List Entry := [some (1019, 381, 108), some (951, 360, 102), some (900, 333, 94), some (800, 302, 86), some (713, 269, 76), some (615, 235, 65), some (452, 173, 47), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none]
def lvl18 : List Entry := [some (1075, 404, 115), some (1019, 381, 108), some (945, 355, 100), some (869, 323, 91), some (782, 290, 81), some (666, 253, 69), some (501, 187, 51), some (452, 173, 47), some (267, 99, 26), none, none, none, none, none, none, none, none, none]
def lvl19 : List Entry := [some (1131, 427, 122), some (1075, 404, 115), some (1012, 379, 108), some (943, 349, 99), some (834, 314, 87), some (727, 272, 75), some (609, 229, 62), some (501, 187, 51), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none]
def lvl20 : List Entry := [some (1203, 447, 129), some (1131, 427, 122), some (1064, 403, 114), some (999, 372, 106), some (883, 335, 94), some (775, 293, 83), some (719, 270, 76), some (544, 203, 56), some (501, 187, 51), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none]
def lvl21 : List Entry := [some (1259, 470, 136), some (1203, 447, 129), some (1131, 427, 122), some (1044, 394, 112), some (986, 365, 104), some (870, 328, 92), some (775, 293, 83), some (583, 220, 60), some (544, 203, 56), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none]
def lvl22 : List Entry := [some (1327, 491, 142), some (1259, 470, 136), some (1203, 447, 129), some (1118, 420, 120), some (1031, 387, 110), some (944, 354, 100), some (838, 309, 86), some (694, 261, 73), some (583, 220, 60), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none]
def lvl23 : List Entry := [some (1383, 514, 149), some (1327, 491, 142), some (1259, 470, 136), some (1174, 443, 127), some (1087, 410, 117), some (1000, 377, 107), some (883, 331, 92), some (801, 301, 84), some (626, 236, 65), some (583, 220, 60), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none]
def lvl24 : List Entry := [some (1439, 537, 156), some (1383, 514, 149), some (1327, 491, 142), some (1246, 463, 134), some (1155, 431, 123), some (1061, 396, 113), some (924, 350, 100), some (883, 331, 92), some (668, 250, 70), some (626, 236, 65), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none]
def lvl25 : List Entry := [some (1495, 560, 163), some (1439, 537, 156), some (1383, 514, 149), some (1309, 488, 141), some (1224, 461, 132), some (1122, 415, 119), some (1042, 384, 109), some (924, 350, 100), some (769, 292, 82), some (668, 250, 70), some (626, 236, 65), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none, none]
def lvl26 : List Entry := [some (1547, 584, 169), some (1495, 560, 163), some (1439, 537, 156), some (1365, 511, 148), some (1285, 480, 138), some (1209, 448, 129), some (1122, 415, 119), some (985, 369, 106), some (880, 333, 95), some (701, 267, 74), some (668, 250, 70), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl27 : List Entry := [some (1619, 604, 176), some (1547, 584, 169), some (1495, 560, 163), some (1421, 534, 155), some (1341, 503, 145), some (1272, 473, 136), some (1167, 437, 125), some (1030, 391, 112), some (985, 369, 106), some (744, 283, 79), some (701, 267, 74), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl28 : List Entry := [some (1675, 627, 183), some (1619, 604, 176), some (1547, 584, 169), some (1500, 556, 162), some (1397, 526, 152), some (1317, 495, 142), some (1223, 460, 132), some (1093, 407, 115), some (1030, 391, 112), some (855, 324, 92), some (744, 283, 79), some (701, 267, 74), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl29 : List Entry := [some (1731, 650, 190), some (1675, 627, 183), some (1619, 604, 176), some (1556, 579, 169), some (1471, 552, 160), some (1389, 515, 149), some (1284, 479, 138), some (1189, 444, 129), some (1093, 407, 115), some (978, 363, 104), some (787, 299, 84), some (744, 283, 79), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl30 : List Entry := [some (1803, 670, 197), some (1731, 650, 190), some (1675, 627, 183), some (1612, 602, 176), some (1543, 572, 167), some (1445, 538, 156), some (1345, 498, 144), some (1284, 479, 138), some (1142, 428, 122), some (1085, 403, 115), some (842, 313, 88), some (787, 299, 84), some (744, 283, 79), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl31 : List Entry := [some (1855, 694, 203), some (1803, 670, 197), some (1731, 650, 190), some (1675, 627, 183), some (1599, 595, 174), some (1521, 570, 165), some (1427, 535, 155), some (1345, 498, 144), some (1179, 448, 129), some (1142, 428, 122), some (936, 355, 101), some (842, 313, 88), some (787, 299, 84), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl32 : List Entry := [some (1911, 717, 210), some (1855, 694, 203), some (1803, 670, 197), some (1731, 650, 190), some (1651, 619, 180), some (1570, 591, 172), some (1490, 560, 162), some (1401, 521, 151), some (1253, 465, 133), some (1179, 448, 129), some (1053, 394, 113), some (868, 330, 93), some (842, 313, 88), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl33 : List Entry := [some (1983, 737, 217), some (1911, 717, 210), some (1855, 694, 203), some (1803, 670, 197), some (1729, 644, 189), some (1638, 612, 178), some (1562, 580, 169), some (1446, 543, 157), some (1346, 503, 145), some (1253, 465, 133), some (1164, 435, 126), some (917, 344, 97), some (868, 330, 93), some (842, 313, 88), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl34 : List Entry := [some (2039, 760, 224), some (1983, 737, 217), some (1911, 717, 210), some (1855, 694, 203), some (1781, 668, 195), some (1694, 635, 185), some (1607, 602, 175), some (1507, 562, 163), some (1440, 538, 155), some (1298, 487, 139), some (1253, 465, 133), some (1028, 385, 110), some (917, 344, 97), some (868, 330, 93), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl35 : List Entry := [some (2104, 782, 228), some (2039, 760, 224), some (1983, 737, 217), some (1911, 717, 210), some (1826, 690, 201), some (1766, 655, 192), some (1663, 625, 182), some (1555, 583, 171), some (1507, 562, 163), some (1339, 506, 147), some (1298, 487, 139), some (1139, 426, 123), some (960, 360, 102), some (917, 344, 97), some (868, 330, 93), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl36 : List Entry := [some (2147, 807, 237), some (2104, 782, 228), some (2039, 760, 224), some (1983, 737, 217), some (1898, 710, 208), some (1835, 685, 201), some (1735, 645, 189), some (1650, 618, 180), some (1555, 583, 171), some (1400, 525, 153), some (1339, 506, 147), some (1259, 466, 133), some (1003, 376, 107), some (960, 360, 102), some (917, 344, 97), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none, none]
def lvl37 : List Entry := [some (2219, 827, 244), some (2147, 807, 237), some (2104, 782, 228), some (2039, 760, 224), some (1972, 736, 216), some (1896, 704, 207), some (1811, 677, 198), some (1735, 645, 189), some (1624, 604, 176), some (1495, 560, 162), some (1400, 525, 153), some (1339, 506, 147), some (1114, 417, 120), some (1003, 376, 107), some (960, 360, 102), some (917, 344, 97), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none, none]
def lvl38 : List Entry := [some (2275, 850, 251), some (2219, 827, 244), some (2147, 807, 237), some (2104, 782, 228), some (2028, 759, 223), some (1952, 727, 214), some (1867, 700, 205), some (1780, 667, 195), some (1669, 626, 182), some (1600, 596, 173), some (1463, 541, 156), some (1400, 525, 153), some (1233, 455, 130), some (1042, 393, 111), some (1003, 376, 107), some (960, 360, 102), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none, none]
def lvl39 : List Entry := [some (2340, 872, 255), some (2275, 850, 251), some (2219, 827, 244), some (2147, 807, 237), some (2084, 782, 230), some (2004, 751, 220), some (1939, 720, 212), some (1832, 691, 201), some (1730, 645, 188), some (1669, 626, 182), some (1508, 563, 162), some (1463, 541, 156), some (1334, 497, 142), some (1084, 407, 116), some (1042, 393, 111), some (1003, 376, 107), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none, none]
def lvl40 : List Entry := [some (2396, 895, 262), some (2340, 872, 255), some (2275, 850, 251), some (2219, 827, 244), some (2156, 802, 237), some (2076, 771, 227), some (1991, 744, 218), some (1897, 709, 208), some (1781, 667, 195), some (1730, 645, 188), some (1560, 583, 171), some (1508, 563, 162), some (1432, 540, 157), some (1185, 449, 128), some (1084, 407, 116), some (1042, 393, 111), some (1003, 376, 107), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none, none]
def lvl41 : List Entry := [some (2455, 917, 271), some (2396, 895, 262), some (2340, 872, 255), some (2275, 850, 251), some (2219, 827, 244), some (2134, 800, 235), some (2047, 767, 225), some (1953, 732, 215), some (1873, 701, 205), some (1781, 667, 195), some (1667, 616, 179), some (1560, 583, 171), some (1508, 563, 162), some (1312, 487, 141), some (1133, 421, 120), some (1084, 407, 116), some (1042, 393, 111), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none, none]
def lvl42 : List Entry := [some (2511, 940, 278), some (2455, 917, 271), some (2396, 895, 262), some (2340, 872, 255), some (2275, 850, 251), some (2190, 823, 242), some (2108, 786, 231), some (2021, 753, 221), some (1953, 732, 215), some (1847, 687, 201), some (1760, 654, 191), some (1610, 601, 176), some (1560, 583, 171), some (1407, 531, 154), some (1176, 437, 125), some (1133, 421, 120), some (1084, 407, 116), some (1042, 393, 111), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none, none]
def lvl43 : List Entry := [some (2583, 960, 285), some (2511, 940, 278), some (2455, 917, 271), some (2396, 895, 262), some (2340, 872, 255), some (2262, 843, 249), some (2188, 817, 241), some (2101, 784, 231), some (2021, 753, 221), some (1892, 709, 207), some (1847, 687, 201), some (1668, 621, 180), some (1610, 601, 176), some (1518, 572, 167), some (1287, 478, 138), some (1176, 437, 125), some (1133, 421, 120), some (1084, 407, 116), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none, none]
def lvl44 : List Entry := [some (2648, 982, 289), some (2583, 960, 285), some (2511, 940, 278), some (2455, 917, 271), some (2396, 895, 262), some (2318, 866, 256), some (2244, 840, 248), some (2164, 809, 238), some (2082, 772, 227), some (1953, 728, 213), some (1892, 709, 207), some (1709, 640, 188), some (1668, 621, 180), some (1610, 601, 176), some (1398, 519, 151), some (1219, 453, 130), some (1176, 437, 125), some (1133, 421, 120), some (1062, 395, 114), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none, none]
def lvl45 : List Entry := [some (2704, 1005, 296), some (2648, 982, 289), some (2583, 960, 285), some (2511, 940, 278), some (2455, 917, 271), some (2383, 888, 260), some (2305, 859, 254), some (2220, 832, 245), some (2138, 795, 234), some (2009, 751, 220), some (1953, 728, 213), some (1811, 677, 197), some (1709, 640, 188), some (1668, 621, 180), some (1501, 560, 161), some (1262, 469, 135), some (1219, 453, 130), some (1176, 437, 125), some (1133, 421, 120), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none, none]
def lvl46 : List Entry := [some (2763, 1027, 305), some (2704, 1005, 296), some (2648, 982, 289), some (2583, 960, 285), some (2511, 940, 278), some (2453, 911, 270), some (2370, 881, 258), some (2292, 852, 252), some (2183, 817, 240), some (2096, 784, 230), some (2009, 751, 220), some (1920, 712, 209), some (1770, 659, 194), some (1709, 640, 188), some (1618, 599, 173), some (1356, 511, 148), some (1262, 469, 135), some (1219, 453, 130), some (1176, 437, 125), some (1062, 395, 114), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none, none]
def lvl47 : List Entry := [some (2819, 1050, 312), some (2763, 1027, 305), some (2704, 1005, 296), some (2648, 982, 289), some (2583, 960, 285), some (2518, 933, 274), some (2429, 903, 267), some (2337, 874, 258), some (2255, 837, 247), some (2183, 817, 240), some (2070, 770, 226), some (2014, 747, 219), some (1815, 681, 200), some (1770, 659, 194), some (1709, 640, 188), some (1473, 550, 160), some (1288, 486, 140), some (1262, 469, 135), some (1219, 453, 130), some (1176, 437, 125), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none, none]
def lvl48 : List Entry := [some (2888, 1071, 317), some (2819, 1050, 312), some (2763, 1027, 305), some (2704, 1005, 296), some (2648, 982, 289), some (2574, 956, 281), some (2485, 926, 274), some (2393, 897, 265), some (2311, 860, 254), some (2255, 837, 247), some (2131, 789, 232), some (2070, 770, 226), some (1878, 697, 203), some (1815, 681, 200), some (1770, 659, 194), some (1584, 591, 173), some (1337, 500, 144), some (1288, 486, 140), some (1262, 469, 135), some (1219, 453, 130), some (1062, 395, 114), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none, none]
def lvl49 : List Entry := [some (2940, 1095, 323), some (2888, 1071, 317), some (2819, 1050, 312), some (2763, 1027, 305), some (2704, 1005, 296), some (2617, 981, 290), some (2567, 954, 281), some (2461, 918, 271), some (2387, 892, 263), some (2311, 860, 254), some (2176, 811, 238), some (2131, 789, 232), some (1971, 735, 215), some (1878, 697, 203), some (1815, 681, 200), some (1691, 633, 185), some (1444, 542, 156), some (1337, 500, 144), some (1288, 486, 140), some (1262, 469, 135), some (1180, 447, 129), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none, none]
def lvl50 : List Entry := [some (2983, 1120, 332), some (2940, 1095, 323), some (2888, 1071, 317), some (2819, 1050, 312), some (2763, 1027, 305), some (2689, 1001, 297), some (2635, 975, 287), some (2541, 949, 281), some (2461, 918, 271), some (2356, 882, 260), some (2232, 834, 245), some (2176, 811, 238), some (2069, 769, 226), some (1939, 716, 209), some (1878, 697, 203), some (1802, 674, 198), some (1555, 583, 169), some (1392, 514, 148), some (1337, 500, 144), some (1288, 486, 140), some (1262, 469, 135), some (1062, 395, 114), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none, none]
def lvl51 : List Entry := [some (3055, 1140, 339), some (2983, 1120, 332), some (2940, 1095, 323), some (2888, 1071, 317), some (2819, 1050, 312), some (2763, 1027, 305), some (2691, 998, 294), some (2606, 971, 285), some (2517, 941, 278), some (2428, 902, 267), some (2319, 867, 255), some (2232, 834, 245), some (2158, 808, 237), some (1964, 738, 217), some (1939, 716, 209), some (1878, 697, 203), some (1666, 624, 182), some (1435, 530, 153), some (1392, 514, 148), some (1337, 500, 144), some (1288, 486, 140), some (1180, 447, 129), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none, none]
def lvl52 : List Entry := [some (3111, 1163, 346), some (3055, 1140, 339), some (2983, 1120, 332), some (2940, 1095, 323), some (2888, 1071, 317), some (2819, 1050, 312), some (2736, 1020, 300), some (2649, 996, 294), some (2578, 960, 284), some (2473, 924, 273), some (2406, 900, 265), some (2293, 853, 251), some (2232, 834, 245), some (2025, 757, 223), some (1964, 738, 217), some (1923, 719, 209), some (1776, 663, 195), some (1530, 574, 166), some (1435, 530, 153), some (1392, 514, 148), some (1337, 500, 144), some (1234, 495, 145), some (1062, 395, 114), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none, none]
def lvl53 : List Entry := [some (3176, 1185, 350), some (3111, 1163, 346), some (3055, 1140, 339), some (2983, 1120, 332), some (2940, 1095, 323), some (2888, 1071, 317), some (2795, 1042, 309), some (2734, 1014, 299), some (2634, 983, 291), some (2529, 947, 280), some (2473, 924, 273), some (2354, 872, 257), some (2293, 853, 251), some (2127, 794, 232), some (2025, 757, 223), some (1948, 741, 217), some (1848, 710, 209), some (1640, 613, 179), some (1465, 548, 160), some (1435, 530, 153), some (1351, 521, 151), some (1240, 495, 165), some (1108, 440, 146), some (924, 347, 98), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none, none]
def lvl54 : List Entry := [some (3248, 1205, 357), some (3176, 1185, 350), some (3111, 1163, 346), some (3055, 1140, 339), some (2983, 1120, 332), some (2940, 1095, 323), some (2851, 1065, 316), some (2766, 1038, 307), some (2690, 1006, 298), some (2581, 971, 286), some (2529, 947, 280), some (2410, 895, 264), some (2322, 878, 257), some (2200, 832, 246), some (2070, 779, 229), some (1964, 768, 225), some (1858, 757, 221), some (1712, 660, 193), some (1504, 563, 163), some (1465, 548, 160), some (1349, 545, 158), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (789, 298, 84), some (520, 200, 55), some (267, 99, 26), none, none, none, none]
def lvl55 : List Entry := [some (3291, 1230, 366), some (3248, 1205, 357), some (3176, 1185, 350), some (3111, 1163, 346), some (3055, 1140, 339), some (2983, 1120, 332), some (2925, 1091, 324), some (2838, 1058, 314), some (2771, 1025, 302), some (2677, 999, 296), some (2581, 971, 286), some (2439, 920, 270), some (2349, 906, 266), some (2215, 884, 261), some (2095, 801, 237), some (1971, 796, 236), some (1900, 770, 256), some (1749, 714, 210), some (1592, 607, 177), some (1475, 568, 165), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (655, 249, 69), some (386, 151, 40), some (136, 49, 13), none, none, none]
def lvl56 : List Entry := [some (3360, 1251, 371), some (3291, 1230, 366), some (3248, 1205, 357), some (3176, 1185, 350), some (3111, 1163, 346), some (3055, 1140, 339), some (2981, 1114, 331), some (2894, 1081, 321), some (2798, 1053, 311), some (2701, 1037, 307), some (2588, 999, 297), some (2472, 962, 285), some (2340, 937, 277), some (2221, 928, 275), some (2095, 831, 245), some (1973, 823, 241), some (1900, 770, 256), some (1768, 715, 238), some (1633, 660, 195), some (1479, 590, 171), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (520, 200, 55), some (267, 99, 26), none, none, none]
def lvl57 : List Entry := [some (3419, 1273, 380), some (3360, 1251, 371), some (3291, 1230, 366), some (3248, 1205, 357), some (3176, 1185, 350), some (3111, 1163, 346), some (3046, 1136, 335), some (2934, 1116, 332), some (2838, 1088, 322), some (2715, 1067, 318), some (2599, 1030, 306), some (2469, 1011, 299), some (2356, 964, 285), some (2296, 935, 311), some (2107, 880, 261), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 195), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (386, 151, 40), some (136, 49, 13), none, none]
def lvl58 : List Entry := [some (3484, 1295, 384), some (3419, 1273, 380), some (3360, 1251, 371), some (3291, 1230, 366), some (3248, 1205, 357), some (3176, 1185, 350), some (3064, 1165, 347), some (2954, 1146, 338), some (2847, 1122, 334), some (2715, 1097, 326), some (2599, 1060, 314), some (2513, 1045, 311), some (2376, 990, 294), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (267, 99, 26), none, none]
def lvl59 : List Entry := [some (3540, 1318, 391), some (3484, 1295, 384), some (3419, 1273, 380), some (3360, 1251, 371), some (3291, 1230, 366), some (3203, 1213, 359), some (3084, 1195, 353), some (2965, 1177, 347), some (2842, 1156, 343), some (2726, 1128, 335), some (2594, 1094, 323), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (136, 49, 13), none]
def lvl60 : List Entry := [some (3599, 1340, 400), some (3540, 1318, 391), some (3484, 1295, 384), some (3403, 1276, 380), some (3318, 1258, 375), some (3214, 1244, 368), some (3086, 1227, 365), some (2967, 1209, 359), some (2840, 1189, 354), some (2757, 1155, 345), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), none]
def lvl61 : List Entry := [some (3655, 1363, 407), some (3599, 1340, 400), some (3511, 1323, 393), some (3430, 1304, 389), some (3329, 1289, 384), some (3216, 1276, 380), some (3086, 1266, 377), some (2965, 1242, 370), some (2903, 1210, 364), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl62 : List Entry := [some (3711, 1386, 414), some (3655, 1363, 407), some (3551, 1349, 400), some (3450, 1334, 395), some (3340, 1320, 393), some (3223, 1308, 388), some (3097, 1297, 386), some (3021, 1265, 377), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl63 : List Entry := [some (3760, 1411, 418), some (3682, 1391, 416), some (3565, 1379, 411), some (3461, 1365, 404), some (3335, 1354, 402), some (3218, 1342, 397), some (3147, 1320, 398), some (3088, 1265, 421), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl64 : List Entry := [some (3803, 1436, 427), some (3693, 1422, 425), some (3576, 1410, 420), some (3463, 1397, 416), some (3349, 1384, 413), some (3229, 1373, 406), some (3220, 1320, 440), some (3088, 1265, 421), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl65 : List Entry := [some (3814, 1467, 436), some (3704, 1453, 434), some (3587, 1441, 429), some (3474, 1428, 425), some (3344, 1418, 422), some (3352, 1375, 450), some (3220, 1320, 440), some (3088, 1265, 421), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl66 : List Entry := [some (3825, 1498, 445), some (3715, 1484, 443), some (3598, 1472, 438), some (3472, 1461, 436), some (3455, 1430, 432), some (3352, 1375, 458), some (3220, 1320, 440), some (3088, 1265, 421), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl67 : List Entry := [some (3823, 1531, 456), some (3713, 1517, 454), some (3596, 1505, 449), some (3519, 1485, 446), some (3484, 1430, 476), some (3352, 1375, 458), some (3220, 1320, 440), some (3088, 1265, 421), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl68 : List Entry := [some (3834, 1562, 465), some (3724, 1548, 463), some (3591, 1539, 458), some (3616, 1485, 495), some (3484, 1430, 476), some (3352, 1375, 458), some (3220, 1320, 440), some (3088, 1265, 421), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl69 : List Entry := [some (3845, 1593, 474), some (3719, 1582, 472), some (3748, 1540, 478), some (3616, 1485, 495), some (3484, 1430, 476), some (3352, 1375, 458), some (3220, 1320, 440), some (3088, 1265, 421), some (2956, 1210, 403), some (2824, 1155, 385), some (2692, 1100, 366), some (2560, 1045, 348), some (2428, 990, 330), some (2296, 935, 311), some (2164, 880, 293), some (2032, 825, 275), some (1900, 770, 256), some (1768, 715, 238), some (1636, 660, 220), some (1504, 605, 201), some (1372, 550, 183), some (1240, 495, 165), some (1108, 440, 146), some (976, 385, 128), some (844, 330, 110), some (712, 275, 91), some (580, 220, 73), some (448, 165, 55), some (316, 110, 36), some (184, 55, 18), some (52, 0, 0)]
def lvl70 : List Entry := []
def lvl71 : List Entry := []
def lvl72 : List Entry := []

def boxes : ℕ → List Entry
  | 1 => lvl1
  | 2 => lvl2
  | 3 => lvl3
  | 4 => lvl4
  | 5 => lvl5
  | 6 => lvl6
  | 7 => lvl7
  | 8 => lvl8
  | 9 => lvl9
  | 10 => lvl10
  | 11 => lvl11
  | 12 => lvl12
  | 13 => lvl13
  | 14 => lvl14
  | 15 => lvl15
  | 16 => lvl16
  | 17 => lvl17
  | 18 => lvl18
  | 19 => lvl19
  | 20 => lvl20
  | 21 => lvl21
  | 22 => lvl22
  | 23 => lvl23
  | 24 => lvl24
  | 25 => lvl25
  | 26 => lvl26
  | 27 => lvl27
  | 28 => lvl28
  | 29 => lvl29
  | 30 => lvl30
  | 31 => lvl31
  | 32 => lvl32
  | 33 => lvl33
  | 34 => lvl34
  | 35 => lvl35
  | 36 => lvl36
  | 37 => lvl37
  | 38 => lvl38
  | 39 => lvl39
  | 40 => lvl40
  | 41 => lvl41
  | 42 => lvl42
  | 43 => lvl43
  | 44 => lvl44
  | 45 => lvl45
  | 46 => lvl46
  | 47 => lvl47
  | 48 => lvl48
  | 49 => lvl49
  | 50 => lvl50
  | 51 => lvl51
  | 52 => lvl52
  | 53 => lvl53
  | 54 => lvl54
  | 55 => lvl55
  | 56 => lvl56
  | 57 => lvl57
  | 58 => lvl58
  | 59 => lvl59
  | 60 => lvl60
  | 61 => lvl61
  | 62 => lvl62
  | 63 => lvl63
  | 64 => lvl64
  | 65 => lvl65
  | 66 => lvl66
  | 67 => lvl67
  | 68 => lvl68
  | 69 => lvl69
  | 70 => lvl70
  | 71 => lvl71
  | 72 => lvl72
  | _ => []

def plainT : ℕ → ℕ × ℕ × ℕ
  | 70 => (3914, 1630, 408)
  | 71 => (3980, 1650, 420)
  | 72 => (4012, 1650, 549)
  | _ => (0, 0, 0)

def terminal : ℕ := 73

private abbrev lossAt := varCertLoss ((((406807694511 : ℕ)) : ℤ)) 8 113 132 53 55 2 2938 4257 73 plainT boxes
private abbrev verifyLevel := varCertLoss_row 406807694511 8 113 132 53 55 2 2938 4257 73 plainT boxes

theorem row0 : lossAt 0 = ((406807672145 : ℕ) : ℤ) :=
  verifyLevel 0 0 0 0 lvl1 406807672145
    (by decide) rfl rfl (by decide +kernel)
theorem row1 : lossAt 1 = ((406807392435 : ℕ) : ℤ) :=
  verifyLevel 1 0 0 0 lvl2 406807392435
    (by decide) rfl rfl (by decide +kernel)
theorem row2 : lossAt 2 = ((406806196835 : ℕ) : ℤ) :=
  verifyLevel 2 0 0 0 lvl3 406806196835
    (by decide) rfl rfl (by decide +kernel)
theorem row3 : lossAt 3 = ((406802759363 : ℕ) : ℤ) :=
  verifyLevel 3 0 0 0 lvl4 406802759363
    (by decide) rfl rfl (by decide +kernel)
theorem row4 : lossAt 4 = ((406794738625 : ℕ) : ℤ) :=
  verifyLevel 4 0 0 0 lvl5 406794738625
    (by decide) rfl rfl (by decide +kernel)
theorem row5 : lossAt 5 = ((406780550675 : ℕ) : ℤ) :=
  verifyLevel 5 0 0 0 lvl6 406780550675
    (by decide) rfl rfl (by decide +kernel)
theorem row6 : lossAt 6 = ((406755234070 : ℕ) : ℤ) :=
  verifyLevel 6 0 0 0 lvl7 406755234070
    (by decide) rfl rfl (by decide +kernel)
theorem row7 : lossAt 7 = ((406717865160 : ℕ) : ℤ) :=
  verifyLevel 7 0 0 0 lvl8 406717865160
    (by decide) rfl rfl (by decide +kernel)
theorem row8 : lossAt 8 = ((406662464225 : ℕ) : ℤ) :=
  verifyLevel 8 0 0 0 lvl9 406662464225
    (by decide) rfl rfl (by decide +kernel)
theorem row9 : lossAt 9 = ((406579288866 : ℕ) : ℤ) :=
  verifyLevel 9 0 0 0 lvl10 406579288866
    (by decide) rfl rfl (by decide +kernel)
theorem row10 : lossAt 10 = ((406471452826 : ℕ) : ℤ) :=
  verifyLevel 10 0 0 0 lvl11 406471452826
    (by decide) rfl rfl (by decide +kernel)
theorem row11 : lossAt 11 = ((406337046161 : ℕ) : ℤ) :=
  verifyLevel 11 0 0 0 lvl12 406337046161
    (by decide) rfl rfl (by decide +kernel)
theorem row12 : lossAt 12 = ((406135639806 : ℕ) : ℤ) :=
  verifyLevel 12 0 0 0 lvl13 406135639806
    (by decide) rfl rfl (by decide +kernel)
theorem row13 : lossAt 13 = ((405905884138 : ℕ) : ℤ) :=
  verifyLevel 13 0 0 0 lvl14 405905884138
    (by decide) rfl rfl (by decide +kernel)
theorem row14 : lossAt 14 = ((405631028347 : ℕ) : ℤ) :=
  verifyLevel 14 0 0 0 lvl15 405631028347
    (by decide) rfl rfl (by decide +kernel)
theorem row15 : lossAt 15 = ((405270509106 : ℕ) : ℤ) :=
  verifyLevel 15 0 0 0 lvl16 405270509106
    (by decide) rfl rfl (by decide +kernel)
theorem row16 : lossAt 16 = ((404805390709 : ℕ) : ℤ) :=
  verifyLevel 16 0 0 0 lvl17 404805390709
    (by decide) rfl rfl (by decide +kernel)
theorem row17 : lossAt 17 = ((404333876334 : ℕ) : ℤ) :=
  verifyLevel 17 0 0 0 lvl18 404333876334
    (by decide) rfl rfl (by decide +kernel)
theorem row18 : lossAt 18 = ((403710958013 : ℕ) : ℤ) :=
  verifyLevel 18 0 0 0 lvl19 403710958013
    (by decide) rfl rfl (by decide +kernel)
theorem row19 : lossAt 19 = ((403002549282 : ℕ) : ℤ) :=
  verifyLevel 19 0 0 0 lvl20 403002549282
    (by decide) rfl rfl (by decide +kernel)
theorem row20 : lossAt 20 = ((402138154477 : ℕ) : ℤ) :=
  verifyLevel 20 0 0 0 lvl21 402138154477
    (by decide) rfl rfl (by decide +kernel)
theorem row21 : lossAt 21 = ((401157455163 : ℕ) : ℤ) :=
  verifyLevel 21 0 0 0 lvl22 401157455163
    (by decide) rfl rfl (by decide +kernel)
theorem row22 : lossAt 22 = ((400074389196 : ℕ) : ℤ) :=
  verifyLevel 22 0 0 0 lvl23 400074389196
    (by decide) rfl rfl (by decide +kernel)
theorem row23 : lossAt 23 = ((398884031889 : ℕ) : ℤ) :=
  verifyLevel 23 0 0 0 lvl24 398884031889
    (by decide) rfl rfl (by decide +kernel)
theorem row24 : lossAt 24 = ((397385631505 : ℕ) : ℤ) :=
  verifyLevel 24 0 0 0 lvl25 397385631505
    (by decide) rfl rfl (by decide +kernel)
theorem row25 : lossAt 25 = ((395718513731 : ℕ) : ℤ) :=
  verifyLevel 25 0 0 0 lvl26 395718513731
    (by decide) rfl rfl (by decide +kernel)
theorem row26 : lossAt 26 = ((393929052276 : ℕ) : ℤ) :=
  verifyLevel 26 0 0 0 lvl27 393929052276
    (by decide) rfl rfl (by decide +kernel)
theorem row27 : lossAt 27 = ((391985038546 : ℕ) : ℤ) :=
  verifyLevel 27 0 0 0 lvl28 391985038546
    (by decide) rfl rfl (by decide +kernel)
theorem row28 : lossAt 28 = ((389673336849 : ℕ) : ℤ) :=
  verifyLevel 28 0 0 0 lvl29 389673336849
    (by decide) rfl rfl (by decide +kernel)
theorem row29 : lossAt 29 = ((387146967784 : ℕ) : ℤ) :=
  verifyLevel 29 0 0 0 lvl30 387146967784
    (by decide) rfl rfl (by decide +kernel)
theorem row30 : lossAt 30 = ((384257982673 : ℕ) : ℤ) :=
  verifyLevel 30 0 0 0 lvl31 384257982673
    (by decide) rfl rfl (by decide +kernel)
theorem row31 : lossAt 31 = ((381283219189 : ℕ) : ℤ) :=
  verifyLevel 31 0 0 0 lvl32 381283219189
    (by decide) rfl rfl (by decide +kernel)
theorem row32 : lossAt 32 = ((377882482414 : ℕ) : ℤ) :=
  verifyLevel 32 0 0 0 lvl33 377882482414
    (by decide) rfl rfl (by decide +kernel)
theorem row33 : lossAt 33 = ((374178365865 : ℕ) : ℤ) :=
  verifyLevel 33 0 0 0 lvl34 374178365865
    (by decide) rfl rfl (by decide +kernel)
theorem row34 : lossAt 34 = ((370337577346 : ℕ) : ℤ) :=
  verifyLevel 34 0 0 0 lvl35 370337577346
    (by decide) rfl rfl (by decide +kernel)
theorem row35 : lossAt 35 = ((365900618914 : ℕ) : ℤ) :=
  verifyLevel 35 0 0 0 lvl36 365900618914
    (by decide) rfl rfl (by decide +kernel)
theorem row36 : lossAt 36 = ((360754384404 : ℕ) : ℤ) :=
  verifyLevel 36 0 0 0 lvl37 360754384404
    (by decide) rfl rfl (by decide +kernel)
theorem row37 : lossAt 37 = ((355691449108 : ℕ) : ℤ) :=
  verifyLevel 37 0 0 0 lvl38 355691449108
    (by decide) rfl rfl (by decide +kernel)
theorem row38 : lossAt 38 = ((350233752900 : ℕ) : ℤ) :=
  verifyLevel 38 0 0 0 lvl39 350233752900
    (by decide) rfl rfl (by decide +kernel)
theorem row39 : lossAt 39 = ((344330897462 : ℕ) : ℤ) :=
  verifyLevel 39 0 0 0 lvl40 344330897462
    (by decide) rfl rfl (by decide +kernel)
theorem row40 : lossAt 40 = ((337558961709 : ℕ) : ℤ) :=
  verifyLevel 40 0 0 0 lvl41 337558961709
    (by decide) rfl rfl (by decide +kernel)
theorem row41 : lossAt 41 = ((330477382640 : ℕ) : ℤ) :=
  verifyLevel 41 0 0 0 lvl42 330477382640
    (by decide) rfl rfl (by decide +kernel)
theorem row42 : lossAt 42 = ((322596573608 : ℕ) : ℤ) :=
  verifyLevel 42 0 0 0 lvl43 322596573608
    (by decide) rfl rfl (by decide +kernel)
theorem row43 : lossAt 43 = ((314751501674 : ℕ) : ℤ) :=
  verifyLevel 43 0 0 0 lvl44 314751501674
    (by decide) rfl rfl (by decide +kernel)
theorem row44 : lossAt 44 = ((306326136087 : ℕ) : ℤ) :=
  verifyLevel 44 0 0 0 lvl45 306326136087
    (by decide) rfl rfl (by decide +kernel)
theorem row45 : lossAt 45 = ((296780864393 : ℕ) : ℤ) :=
  verifyLevel 45 0 0 0 lvl46 296780864393
    (by decide) rfl rfl (by decide +kernel)
theorem row46 : lossAt 46 = ((286636642842 : ℕ) : ℤ) :=
  verifyLevel 46 0 0 0 lvl47 286636642842
    (by decide) rfl rfl (by decide +kernel)
theorem row47 : lossAt 47 = ((276639187679 : ℕ) : ℤ) :=
  verifyLevel 47 0 0 0 lvl48 276639187679
    (by decide) rfl rfl (by decide +kernel)
theorem row48 : lossAt 48 = ((265029577232 : ℕ) : ℤ) :=
  verifyLevel 48 0 0 0 lvl49 265029577232
    (by decide) rfl rfl (by decide +kernel)
theorem row49 : lossAt 49 = ((252817481908 : ℕ) : ℤ) :=
  verifyLevel 49 0 0 0 lvl50 252817481908
    (by decide) rfl rfl (by decide +kernel)
theorem row50 : lossAt 50 = ((239891345195 : ℕ) : ℤ) :=
  verifyLevel 50 0 0 0 lvl51 239891345195
    (by decide) rfl rfl (by decide +kernel)
theorem row51 : lossAt 51 = ((226617503307 : ℕ) : ℤ) :=
  verifyLevel 51 0 0 0 lvl52 226617503307
    (by decide) rfl rfl (by decide +kernel)
theorem row52 : lossAt 52 = ((212655628974 : ℕ) : ℤ) :=
  verifyLevel 52 0 0 0 lvl53 212655628974
    (by decide) rfl rfl (by decide +kernel)
theorem row53 : lossAt 53 = ((198393561005 : ℕ) : ℤ) :=
  verifyLevel 53 0 0 0 lvl54 198393561005
    (by decide) rfl rfl (by decide +kernel)
theorem row54 : lossAt 54 = ((183151504089 : ℕ) : ℤ) :=
  verifyLevel 54 0 0 0 lvl55 183151504089
    (by decide) rfl rfl (by decide +kernel)
theorem row55 : lossAt 55 = ((168411465234 : ℕ) : ℤ) :=
  verifyLevel 55 0 0 0 lvl56 168411465234
    (by decide) rfl rfl (by decide +kernel)
theorem row56 : lossAt 56 = ((153650776738 : ℕ) : ℤ) :=
  verifyLevel 56 0 0 0 lvl57 153650776738
    (by decide) rfl rfl (by decide +kernel)
theorem row57 : lossAt 57 = ((140552300124 : ℕ) : ℤ) :=
  verifyLevel 57 0 0 0 lvl58 140552300124
    (by decide) rfl rfl (by decide +kernel)
theorem row58 : lossAt 58 = ((128256408951 : ℕ) : ℤ) :=
  verifyLevel 58 0 0 0 lvl59 128256408951
    (by decide) rfl rfl (by decide +kernel)
theorem row59 : lossAt 59 = ((116243585652 : ℕ) : ℤ) :=
  verifyLevel 59 0 0 0 lvl60 116243585652
    (by decide) rfl rfl (by decide +kernel)
theorem row60 : lossAt 60 = ((104868203597 : ℕ) : ℤ) :=
  verifyLevel 60 0 0 0 lvl61 104868203597
    (by decide) rfl rfl (by decide +kernel)
theorem row61 : lossAt 61 = ((94423174629 : ℕ) : ℤ) :=
  verifyLevel 61 0 0 0 lvl62 94423174629
    (by decide) rfl rfl (by decide +kernel)
theorem row62 : lossAt 62 = ((84685295914 : ℕ) : ℤ) :=
  verifyLevel 62 0 0 0 lvl63 84685295914
    (by decide) rfl rfl (by decide +kernel)
theorem row63 : lossAt 63 = ((75836952900 : ℕ) : ℤ) :=
  verifyLevel 63 0 0 0 lvl64 75836952900
    (by decide) rfl rfl (by decide +kernel)
theorem row64 : lossAt 64 = ((67571630025 : ℕ) : ℤ) :=
  verifyLevel 64 0 0 0 lvl65 67571630025
    (by decide) rfl rfl (by decide +kernel)
theorem row65 : lossAt 65 = ((60228557196 : ℕ) : ℤ) :=
  verifyLevel 65 0 0 0 lvl66 60228557196
    (by decide) rfl rfl (by decide +kernel)
theorem row66 : lossAt 66 = ((53747185903 : ℕ) : ℤ) :=
  verifyLevel 66 0 0 0 lvl67 53747185903
    (by decide) rfl rfl (by decide +kernel)
theorem row67 : lossAt 67 = ((48085414493 : ℕ) : ℤ) :=
  verifyLevel 67 0 0 0 lvl68 48085414493
    (by decide) rfl rfl (by decide +kernel)
theorem row68 : lossAt 68 = ((43356729165 : ℕ) : ℤ) :=
  verifyLevel 68 0 0 0 lvl69 43356729165
    (by decide) rfl rfl (by decide +kernel)
theorem row69 : lossAt 69 = ((30731245688 : ℕ) : ℤ) :=
  verifyLevel 69 3914 1630 408 lvl70 30731245688
    (by decide) rfl rfl (by decide +kernel)
theorem row70 : lossAt 70 = ((9634212085 : ℕ) : ℤ) :=
  verifyLevel 70 3980 1650 420 lvl71 9634212085
    (by decide) rfl rfl (by decide +kernel)
theorem row71 : lossAt 71 = ((493790373 : ℕ) : ℤ) :=
  verifyLevel 71 4012 1650 549 lvl72 493790373
    (by decide) rfl rfl (by decide +kernel)
theorem row72 : lossAt 72 = ((0 : ℕ) : ℤ) :=
  varCertLoss_terminal _ 8 113 132 53 55 2 2938 4257 73 plainT boxes 72 (by decide)

theorem total : ∑ i ∈ Finset.range 73, lossAt i = ((21173162579821 : ℕ) : ℤ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41, row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72]
  norm_num

/-- Variable gate loss for tilted group 1: grade [113, 132], index [53, 55], top >= 2, taper [2938, 4257], terminal level 73, blocks of 8 grades. -/
theorem loss (N : ℕ) :
    ∑ i ∈ Finset.range N, max 0 ((((406807694511 : ℕ)) : ℤ) - varGateDim ((((406807694511 : ℕ)) : ℤ)) 113 132 53 55 2 2938 4257 73 plainT
      (fun r => (boxes r).length) (fun r a => (boxes r).getD a none) (i + 1)) ≤ ((21173162579821 : ℕ) : ℤ) :=
  loss_of_varCert ((((406807694511 : ℕ)) : ℤ)) 8 113 132 53 55 2 2938 4257 73 plainT boxes ((21173162579821 : ℕ) : ℤ) (by norm_num) total N

end FadicGate.Final54W1

#print axioms FadicGate.Final54W1.loss
