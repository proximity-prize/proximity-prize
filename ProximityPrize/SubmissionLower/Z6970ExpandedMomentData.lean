import ProximityPrize.SubmissionLower.Z6970ExpandedMomentCompute

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace ExpandedColumns6970

private theorem m0_31 : compute 0 31 = (46376, 1113024, 40068864) := by decide +kernel
private theorem m31_62 : compute 31 31 = (630664, 31926528, 1149355008) := by decide +kernel
private theorem m0_62 : compute 0 62 = (677040, 33039552, 1189423872) := by
  rw [show 62 = 31+31 by decide, compute_add, m0_31]
  change addMoment _ (compute 31 31) = _
  rw [m31_62]
  rfl
private theorem m62_93 : compute 62 31 = (2644920, 211456704, 7612441344) := by decide +kernel
private theorem m93_125 : compute 93 32 = (7346040, 813769344, 29295696384) := by decide +kernel
private theorem m62_125 : compute 62 63 = (9990960, 1025226048, 36908137728) := by
  rw [show 63 = 31+32 by decide, compute_add, m62_93]
  change addMoment _ (compute 93 32) = _
  rw [m93_125]
  rfl
private theorem m0_125 : compute 0 125 = (10668000, 1058265600, 38097561600) := by
  rw [show 125 = 62+63 by decide, compute_add, m0_62]
  change addMoment _ (compute 62 63) = _
  rw [m62_125]
  rfl
private theorem m125_156 : compute 125 31 = (14969001, 2120722524, 76346010864) := by decide +kernel
private theorem m156_188 : compute 156 32 = (28090344, 4858622688, 174910416768) := by decide +kernel
private theorem m125_188 : compute 125 63 = (43059345, 6979345212, 251256427632) := by
  rw [show 63 = 31+32 by decide, compute_add, m125_156]
  change addMoment _ (compute 156 32) = _
  rw [m156_188]
  rfl
private theorem m188_219 : compute 188 31 = (44764620, 9139387884, 329017963824) := by decide +kernel
private theorem m219_251 : compute 219 32 = (70870536, 16695501504, 601038054144) := by decide +kernel
private theorem m188_251 : compute 188 63 = (115635156, 25834889388, 930056017968) := by
  rw [show 63 = 31+32 by decide, compute_add, m188_219]
  change addMoment _ (compute 219 32) = _
  rw [m219_251]
  rfl
private theorem m125_251 : compute 125 126 = (158694501, 32814234600, 1181312445600) := by
  rw [show 126 = 63+63 by decide, compute_add, m125_188]
  change addMoment _ (compute 188 63) = _
  rw [m188_251]
  rfl
private theorem m0_251 : compute 0 251 = (169362501, 33872500200, 1219410007200) := by
  rw [show 251 = 125+126 by decide, compute_add, m0_125]
  change addMoment _ (compute 125 126) = _
  rw [m125_251]
  rfl
private theorem m251_282 : compute 251 31 = (99783234, 26631461028, 958732597008) := by decide +kernel
private theorem m282_314 : compute 282 32 = (143688120, 42869636064, 1543306898304) := by decide +kernel
private theorem m251_314 : compute 251 63 = (243471354, 69501097092, 2502039495312) := by
  rw [show 63 = 31+32 by decide, compute_add, m251_282]
  change addMoment _ (compute 282 32) = _
  rw [m282_314]
  rfl
private theorem m314_345 : compute 314 31 = (187776300, 61914317364, 2228915425104) := by decide +kernel
private theorem m345_377 : compute 345 32 = (254544600, 91942635648, 3309934883328) := by decide +kernel
private theorem m314_377 : compute 314 63 = (442320900, 153856953012, 5538850308432) := by
  rw [show 63 = 31+32 by decide, compute_add, m314_345]
  change addMoment _ (compute 345 32) = _
  rw [m345_377]
  rfl
private theorem m251_377 : compute 251 126 = (685792254, 223358050104, 8040889803744) := by
  rw [show 126 = 63+63 by decide, compute_add, m251_314]
  change addMoment _ (compute 314 63) = _
  rw [m314_377]
  rfl
private theorem m377_408 : compute 377 31 = (316495275, 124258699464, 4473313180704) := by decide +kernel
private theorem m408_440 : compute 408 32 = (411441480, 174492488544, 6281729587584) := by decide +kernel
private theorem m377_440 : compute 377 63 = (727936755, 298751188008, 10755042768288) := by
  rw [show 63 = 31+32 by decide, compute_add, m377_408]
  change addMoment _ (compute 408 32) = _
  rw [m408_440]
  rfl
private theorem m440_471 : compute 440 31 = (493691616, 224888717064, 8095993814304) := by decide +kernel
private theorem m471_503 : compute 471 32 = (622380259, 303113559539, 10912088053224) := by decide +kernel
private theorem m440_503 : compute 440 63 = (1116071875, 528002276603, 19008081867528) := by
  rw [show 63 = 31+32 by decide, compute_add, m440_471]
  change addMoment _ (compute 471 32) = _
  rw [m471_503]
  rfl
private theorem m377_503 : compute 377 126 = (1844008630, 826753464611, 29763124635816) := by
  rw [show 126 = 63+63 by decide, compute_add, m377_440]
  change addMoment _ (compute 440 63) = _
  rw [m440_503]
  rfl
private theorem m251_503 : compute 251 252 = (2529800884, 1050111514715, 37804014439560) := by
  rw [show 252 = 126+126 by decide, compute_add, m251_377]
  change addMoment _ (compute 377 126) = _
  rw [m377_503]
  rfl
private theorem m0_503 : compute 0 503 = (2699163385, 1083984014915, 39023424446760) := by
  rw [show 503 = 251+252 by decide, compute_add, m0_251]
  change addMoment _ (compute 251 252) = _
  rw [m251_503]
  rfl
private theorem m503_534 : compute 503 31 = (727057880, 376950830200, 13569167566800) := by decide +kernel
private theorem m534_565 : compute 534 31 = (864274265, 474859936725, 17082195899400) := by decide +kernel
private theorem m503_565 : compute 503 62 = (1591332145, 851810766925, 30651363466200) := by
  rw [show 62 = 31+31 by decide, compute_add, m503_534]
  change addMoment _ (compute 534 31) = _
  rw [m534_565]
  rfl
private theorem m565_596 : compute 565 31 = (1016415605, 589932928274, 21186252190608) := by decide +kernel
private theorem m596_628 : compute 596 32 = (1224234560, 749112453968, 26821440580416) := by decide +kernel
private theorem m565_628 : compute 565 63 = (2240650165, 1339045382242, 48007692771024) := by
  rw [show 63 = 31+32 by decide, compute_add, m565_596]
  change addMoment _ (compute 596 32) = _
  rw [m596_628]
  rfl
private theorem m503_628 : compute 503 125 = (3831982310, 2190856149167, 78659056237224) := by
  rw [show 125 = 62+63 by decide, compute_add, m503_565]
  change addMoment _ (compute 565 63) = _
  rw [m565_628]
  rfl
private theorem m628_659 : compute 628 31 = (1368026125, 880116122119, 31339523384688) := by decide +kernel
private theorem m659_691 : compute 659 32 = (1609143140, 1085908883553, 38332059300072) := by decide +kernel
private theorem m628_691 : compute 628 63 = (2977169265, 1966025005672, 69671582684760) := by
  rw [show 63 = 31+32 by decide, compute_add, m628_659]
  change addMoment _ (compute 659 32) = _
  rw [m659_691]
  rfl
private theorem m691_722 : compute 691 31 = (1754592872, 1239243075528, 43231872096456) := by decide +kernel
private theorem m722_754 : compute 722 32 = (2014705784, 1486395253736, 51106585586112) := by decide +kernel
private theorem m691_754 : compute 691 63 = (3769298656, 2725638329264, 94338457682568) := by
  rw [show 63 = 31+32 by decide, compute_add, m691_722]
  change addMoment _ (compute 722 32) = _
  rw [m722_754]
  rfl
private theorem m628_754 : compute 628 126 = (6746467921, 4691663334936, 164010040367328) := by
  rw [show 126 = 63+63 by decide, compute_add, m628_691]
  change addMoment _ (compute 691 63) = _
  rw [m691_754]
  rfl
private theorem m503_754 : compute 503 251 = (10578450231, 6882519484103, 242669096604552) := by
  rw [show 251 = 125+126 by decide, compute_add, m503_628]
  change addMoment _ (compute 628 126) = _
  rw [m628_754]
  rfl
private theorem m754_785 : compute 754 31 = (2146926078, 1651476584398, 55839750976344) := by decide +kernel
private theorem m785_817 : compute 785 32 = (2412079712, 1931389514256, 64093923786816) := by decide +kernel
private theorem m754_817 : compute 754 63 = (4559005790, 3582866098654, 119933674763160) := by
  rw [show 63 = 31+32 by decide, compute_add, m754_785]
  change addMoment _ (compute 785 32) = _
  rw [m785_817]
  rfl
private theorem m817_848 : compute 817 31 = (2517758975, 2095221379674, 68127842296032) := by decide +kernel
private theorem m848_880 : compute 848 32 = (2773692664, 2395538877304, 76203264166656) := by decide +kernel
private theorem m817_880 : compute 817 63 = (5291451639, 4490760256978, 144331106462688) := by
  rw [show 63 = 31+32 by decide, compute_add, m817_848]
  change addMoment _ (compute 848 32) = _
  rw [m848_880]
  rfl
private theorem m754_880 : compute 754 126 = (9850457429, 8073626355632, 264264781225848) := by
  rw [show 126 = 63+63 by decide, compute_add, m754_817]
  change addMoment _ (compute 817 63) = _
  rw [m817_880]
  rfl
private theorem m880_911 : compute 880 31 = (2843816215, 2545598088137, 79136546639712) := by decide +kernel
private theorem m911_943 : compute 911 32 = (3084875200, 2858524635152, 86788305825792) := by decide +kernel
private theorem m880_943 : compute 880 63 = (5928691415, 5404122723289, 165924852465504) := by
  rw [show 63 = 31+32 by decide, compute_add, m880_911]
  change addMoment _ (compute 911 32) = _
  rw [m911_943]
  rfl
private theorem m943_974 : compute 943 31 = (3121594416, 2990811123760, 88655254801992) := by decide +kernel
private theorem m974_1006 : compute 974 32 = (3348175720, 3313345551424, 95877124406592) := by decide +kernel
private theorem m943_1006 : compute 943 63 = (6469770136, 6304156675184, 184532379208584) := by
  rw [show 63 = 31+32 by decide, compute_add, m943_974]
  change addMoment _ (compute 974 32) = _
  rw [m974_1006]
  rfl
private theorem m880_1006 : compute 880 126 = (12398461551, 11708279398473, 350457231674088) := by
  rw [show 126 = 63+63 by decide, compute_add, m880_943]
  change addMoment _ (compute 943 63) = _
  rw [m943_1006]
  rfl
private theorem m754_1006 : compute 754 252 = (22248918980, 19781905754105, 614722012899936) := by
  rw [show 252 = 126+126 by decide, compute_add, m754_880]
  change addMoment _ (compute 880 126) = _
  rw [m880_1006]
  rfl
private theorem m503_1006 : compute 503 503 = (32827369211, 26664425238208, 857391109504488) := by
  rw [show 503 = 251+252 by decide, compute_add, m503_754]
  change addMoment _ (compute 754 252) = _
  rw [m754_1006]
  rfl
private theorem m0_1006 : compute 0 1006 = (35526532596, 27748409253123, 896414533951248) := by
  rw [show 1006 = 503+503 by decide, compute_add, m0_503]
  change addMoment _ (compute 503 503) = _
  rw [m503_1006]
  rfl
private theorem m1006_1037 : compute 1006 31 = (3354924778, 3425647890650, 96768269324736) := by decide +kernel
private theorem m1037_1068 : compute 1037 31 = (3454603422, 3634487736896, 100272176266968) := by decide +kernel
private theorem m1006_1068 : compute 1006 62 = (6809528200, 7060135627546, 197040445591704) := by
  rw [show 62 = 31+31 by decide, compute_add, m1006_1037]
  change addMoment _ (compute 1037 31) = _
  rw [m1037_1068]
  rfl
private theorem m1068_1099 : compute 1068 31 = (3544920244, 3839369997484, 103469376602016) := by decide +kernel
private theorem m1099_1131 : compute 1099 32 = (3744574720, 4173547042672, 109848133454592) := by decide +kernel
private theorem m1068_1131 : compute 1068 63 = (7289494964, 8012917040156, 213317510056608) := by
  rw [show 63 = 31+32 by decide, compute_add, m1068_1099]
  change addMoment _ (compute 1099 32) = _
  rw [m1099_1131]
  rfl
private theorem m1006_1131 : compute 1006 125 = (14099023164, 15073052667702, 410357955648312) := by
  rw [show 125 = 62+63 by decide, compute_add, m1006_1068]
  change addMoment _ (compute 1068 63) = _
  rw [m1068_1131]
  rfl
private theorem m1131_1162 : compute 1131 31 = (3701534325, 4242135493762, 109071213725712) := by decide +kernel
private theorem m1162_1194 : compute 1162 32 = (3888771976, 4579201588320, 115042057372992) := by decide +kernel
private theorem m1131_1194 : compute 1131 63 = (7590306301, 8821337082082, 224113271098704) := by
  rw [show 63 = 31+32 by decide, compute_add, m1131_1162]
  change addMoment _ (compute 1162 32) = _
  rw [m1162_1194]
  rfl
private theorem m1194_1225 : compute 1194 31 = (3825266233, 4624884738649, 113559089569056) := by decide +kernel
private theorem m1225_1257 : compute 1225 32 = (4001026720, 4963405715800, 119141816261952) := by decide +kernel
private theorem m1194_1257 : compute 1194 63 = (7826292953, 9588290454449, 232700905831008) := by
  rw [show 63 = 31+32 by decide, compute_add, m1194_1225]
  change addMoment _ (compute 1225 32) = _
  rw [m1225_1257]
  rfl
private theorem m1131_1257 : compute 1131 126 = (15416599254, 18409627536531, 456814176929712) := by
  rw [show 126 = 63+63 by decide, compute_add, m1131_1194]
  change addMoment _ (compute 1194 63) = _
  rw [m1194_1257]
  rfl
private theorem m1006_1257 : compute 1006 251 = (29515622418, 33482680204233, 867172132578024) := by
  rw [show 251 = 125+126 by decide, compute_add, m1006_1131]
  change addMoment _ (compute 1131 126) = _
  rw [m1131_1257]
  rfl
private theorem m1257_1288 : compute 1257 31 = (3919991697, 4986332928736, 117042439222128) := by decide +kernel
private theorem m1288_1320 : compute 1288 32 = (4085339704, 5325337270584, 122263399923456) := by decide +kernel
private theorem m1257_1320 : compute 1257 63 = (8005331401, 10311670199320, 239305839145584) := by
  rw [show 63 = 31+32 by decide, compute_add, m1257_1288]
  change addMoment _ (compute 1288 32) = _
  rw [m1288_1320]
  rfl
private theorem m1320_1351 : compute 1320 31 = (3989586445, 5326171942987, 119636557836192) := by decide +kernel
private theorem m1351_1383 : compute 1351 32 = (4145711680, 5665182287632, 124528847296512) := by decide +kernel
private theorem m1320_1383 : compute 1320 63 = (8135298125, 10991354230619, 244165405132704) := by
  rw [show 63 = 31+32 by decide, compute_add, m1320_1351]
  change addMoment _ (compute 1351 32) = _
  rw [m1351_1383]
  rfl
private theorem m1257_1383 : compute 1257 126 = (16140629526, 21303024429939, 483471244278288) := by
  rw [show 126 = 63+63 by decide, compute_add, m1257_1320]
  change addMoment _ (compute 1320 63) = _
  rw [m1320_1383]
  rfl
private theorem m1383_1414 : compute 1383 31 = (4037926206, 5645070345220, 121462600704312) := by decide +kernel
private theorem m1414_1446 : compute 1414 32 = (4186143400, 5984134991424, 126066246457152) := by decide +kernel
private theorem m1383_1446 : compute 1383 63 = (8224069606, 11629205336644, 247528847161464) := by
  rw [show 63 = 31+32 by decide, compute_add, m1383_1414]
  change addMoment _ (compute 1414 32) = _
  rw [m1414_1446]
  rfl
private theorem m1446_1477 : compute 1446 31 = (4068886708, 5944673381500, 122647583180736) := by decide +kernel
private theorem m1477_1509 : compute 1477 32 = (4210635616, 6284397795928, 127009734618432) := by decide +kernel
private theorem m1446_1509 : compute 1446 63 = (8279522324, 12229071177428, 249657317799168) := by
  rw [show 63 = 31+32 by decide, compute_add, m1446_1477]
  change addMoment _ (compute 1477 32) = _
  rw [m1477_1509]
  rfl
private theorem m1383_1509 : compute 1383 126 = (16503591930, 23858276514072, 497186164960632) := by
  rw [show 126 = 63+63 by decide, compute_add, m1383_1446]
  change addMoment _ (compute 1446 63) = _
  rw [m1446_1509]
  rfl
private theorem m1257_1509 : compute 1257 252 = (32644221456, 45161300944011, 980657409238920) := by
  rw [show 252 = 126+126 by decide, compute_add, m1257_1383]
  change addMoment _ (compute 1383 126) = _
  rw [m1383_1509]
  rfl
private theorem m1006_1509 : compute 1006 503 = (62159843874, 78643981148244, 1847829541816944) := by
  rw [show 503 = 251+252 by decide, compute_add, m1006_1257]
  change addMoment _ (compute 1257 252) = _
  rw [m1257_1509]
  rfl
private theorem m1509_1540 : compute 1509 31 = (4086343680, 6227602982872, 123324380761512) := by decide +kernel
private theorem m1540_1571 : compute 1540 31 = (4091158410, 6361761122062, 123512935297632) := by decide +kernel
private theorem m1509_1571 : compute 1509 62 = (8177502090, 12589364104934, 246837316059144) := by
  rw [show 62 = 31+31 by decide, compute_add, m1509_1540]
  change addMoment _ (compute 1540 31) = _
  rw [m1540_1571]
  rfl
private theorem m1571_1602 : compute 1571 31 = (4094103755, 6493254121542, 123628996811712) := by decide +kernel
private theorem m1602_1634 : compute 1602 32 = (4227772616, 6838424947680, 127680502170432) := by decide +kernel
private theorem m1571_1634 : compute 1571 63 = (8321876371, 13331679069222, 251309498982144) := by
  rw [show 63 = 31+32 by decide, compute_add, m1571_1602]
  change addMoment _ (compute 1602 32) = _
  rw [m1602_1634]
  rfl
private theorem m1509_1634 : compute 1509 125 = (16499378461, 25921043174156, 498146815041288) := by
  rw [show 125 = 62+63 by decide, compute_add, m1509_1571]
  change addMoment _ (compute 1571 63) = _
  rw [m1571_1634]
  rfl
private theorem m1634_1665 : compute 1634 31 = (4096241883, 6754703509619, 123713900869536) := by decide +kernel
private theorem m1665_1697 : compute 1665 32 = (4228480736, 7105961894068, 127708760597664) := by decide +kernel
private theorem m1634_1697 : compute 1634 63 = (8324722619, 13860665403687, 251422661467200) := by
  rw [show 63 = 31+32 by decide, compute_add, m1634_1665]
  change addMoment _ (compute 1665 32) = _
  rw [m1665_1697]
  rfl
private theorem m1697_1728 : compute 1697 31 = (4096342015, 7012937529680, 123717914210400) := by decide +kernel
private theorem m1728_1760 : compute 1728 32 = (4228482080, 7372358506480, 127708814668800) := by decide +kernel
private theorem m1697_1760 : compute 1697 63 = (8324824095, 14385296036160, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m1697_1728]
  change addMoment _ (compute 1728 32) = _
  rw [m1728_1760]
  rfl
private theorem m1634_1760 : compute 1634 126 = (16649546714, 28245961439847, 502849390346400) := by
  rw [show 126 = 63+63 by decide, compute_add, m1634_1697]
  change addMoment _ (compute 1697 63) = _
  rw [m1697_1760]
  rfl
private theorem m1509_1760 : compute 1509 251 = (33148925175, 54167004614003, 1000996205387688) := by
  rw [show 251 = 125+126 by decide, compute_add, m1509_1634]
  change addMoment _ (compute 1634 126) = _
  rw [m1634_1760]
  rfl
private theorem m1760_1791 : compute 1760 31 = (4096342015, 7271007076625, 123717914210400) := by decide +kernel
private theorem m1791_1823 : compute 1791 32 = (4228482080, 7638752877520, 127708814668800) := by decide +kernel
private theorem m1760_1823 : compute 1760 63 = (8324824095, 14909759954145, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m1760_1791]
  change addMoment _ (compute 1791 32) = _
  rw [m1791_1823]
  rfl
private theorem m1823_1854 : compute 1823 31 = (4096342015, 7529076623570, 123717914210400) := by decide +kernel
private theorem m1854_1886 : compute 1854 32 = (4228482080, 7905147248560, 127708814668800) := by decide +kernel
private theorem m1823_1886 : compute 1823 63 = (8324824095, 15434223872130, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m1823_1854]
  change addMoment _ (compute 1854 32) = _
  rw [m1854_1886]
  rfl
private theorem m1760_1886 : compute 1760 126 = (16649648190, 30343983826275, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m1760_1823]
  change addMoment _ (compute 1823 63) = _
  rw [m1823_1886]
  rfl
private theorem m1886_1917 : compute 1886 31 = (4096342015, 7787146170515, 123717914210400) := by decide +kernel
private theorem m1917_1949 : compute 1917 32 = (4228482080, 8171541619600, 127708814668800) := by decide +kernel
private theorem m1886_1949 : compute 1886 63 = (8324824095, 15958687790115, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m1886_1917]
  change addMoment _ (compute 1917 32) = _
  rw [m1917_1949]
  rfl
private theorem m1949_1980 : compute 1949 31 = (4096342015, 8045215717460, 123717914210400) := by decide +kernel
private theorem m1980_2012 : compute 1980 32 = (4228482080, 8437935990640, 127708814668800) := by decide +kernel
private theorem m1949_2012 : compute 1949 63 = (8324824095, 16483151708100, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m1949_1980]
  change addMoment _ (compute 1980 32) = _
  rw [m1980_2012]
  rfl
private theorem m1886_2012 : compute 1886 126 = (16649648190, 32441839498215, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m1886_1949]
  change addMoment _ (compute 1949 63) = _
  rw [m1949_2012]
  rfl
private theorem m1760_2012 : compute 1760 252 = (33299296380, 62785823324490, 1005706915516800) := by
  rw [show 252 = 126+126 by decide, compute_add, m1760_1886]
  change addMoment _ (compute 1886 126) = _
  rw [m1886_2012]
  rfl
private theorem m1509_2012 : compute 1509 503 = (66448221555, 116952827938493, 2006703120904488) := by
  rw [show 503 = 251+252 by decide, compute_add, m1509_1760]
  change addMoment _ (compute 1760 252) = _
  rw [m1760_2012]
  rfl
private theorem m1006_2012 : compute 1006 1006 = (128608065429, 195596809086737, 3854532662721432) := by
  rw [show 1006 = 503+503 by decide, compute_add, m1006_1509]
  change addMoment _ (compute 1509 503) = _
  rw [m1509_2012]
  rfl
private theorem m0_2012 : compute 0 2012 = (164134598025, 223345218339860, 4750947196672680) := by
  rw [show 2012 = 1006+1006 by decide, compute_add, m0_1006]
  change addMoment _ (compute 1006 1006) = _
  rw [m1006_2012]
  rfl
private theorem m2012_2043 : compute 2012 31 = (4096342015, 8303285264405, 123717914210400) := by decide +kernel
private theorem m2043_2074 : compute 2043 31 = (4096342015, 8430271866870, 123717914210400) := by decide +kernel
private theorem m2012_2074 : compute 2012 62 = (8192684030, 16733557131275, 247435828420800) := by
  rw [show 62 = 31+31 by decide, compute_add, m2012_2043]
  change addMoment _ (compute 2043 31) = _
  rw [m2043_2074]
  rfl
private theorem m2074_2105 : compute 2074 31 = (4096342015, 8557258469335, 123717914210400) := by decide +kernel
private theorem m2105_2137 : compute 2105 32 = (4228482080, 8966496250640, 127708814668800) := by decide +kernel
private theorem m2074_2137 : compute 2074 63 = (8324824095, 17523754719975, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2074_2105]
  change addMoment _ (compute 2105 32) = _
  rw [m2105_2137]
  rfl
private theorem m2012_2137 : compute 2012 125 = (16517508125, 34257311851250, 498862557300000) := by
  rw [show 125 = 62+63 by decide, compute_add, m2012_2074]
  change addMoment _ (compute 2074 63) = _
  rw [m2074_2137]
  rfl
private theorem m2137_2168 : compute 2137 31 = (4096342015, 8815328016280, 123717914210400) := by decide +kernel
private theorem m2168_2200 : compute 2168 32 = (4228482080, 9232890621680, 127708814668800) := by decide +kernel
private theorem m2137_2200 : compute 2137 63 = (8324824095, 18048218637960, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2137_2168]
  change addMoment _ (compute 2168 32) = _
  rw [m2168_2200]
  rfl
private theorem m2200_2231 : compute 2200 31 = (4096342015, 9073397563225, 123717914210400) := by decide +kernel
private theorem m2231_2263 : compute 2231 32 = (4228482080, 9499284992720, 127708814668800) := by decide +kernel
private theorem m2200_2263 : compute 2200 63 = (8324824095, 18572682555945, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2200_2231]
  change addMoment _ (compute 2231 32) = _
  rw [m2231_2263]
  rfl
private theorem m2137_2263 : compute 2137 126 = (16649648190, 36620901193905, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m2137_2200]
  change addMoment _ (compute 2200 63) = _
  rw [m2200_2263]
  rfl
private theorem m2012_2263 : compute 2012 251 = (33167156315, 70878213045155, 1001716015058400) := by
  rw [show 251 = 125+126 by decide, compute_add, m2012_2137]
  change addMoment _ (compute 2137 126) = _
  rw [m2137_2263]
  rfl
private theorem m2263_2294 : compute 2263 31 = (4096342015, 9331467110170, 123717914210400) := by decide +kernel
private theorem m2294_2326 : compute 2294 32 = (4228482080, 9765679363760, 127708814668800) := by decide +kernel
private theorem m2263_2326 : compute 2263 63 = (8324824095, 19097146473930, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2263_2294]
  change addMoment _ (compute 2294 32) = _
  rw [m2294_2326]
  rfl
private theorem m2326_2357 : compute 2326 31 = (4096342015, 9589536657115, 123717914210400) := by decide +kernel
private theorem m2357_2389 : compute 2357 32 = (4228482080, 10032073734800, 127708814668800) := by decide +kernel
private theorem m2326_2389 : compute 2326 63 = (8324824095, 19621610391915, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2326_2357]
  change addMoment _ (compute 2357 32) = _
  rw [m2357_2389]
  rfl
private theorem m2263_2389 : compute 2263 126 = (16649648190, 38718756865845, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m2263_2326]
  change addMoment _ (compute 2326 63) = _
  rw [m2326_2389]
  rfl
private theorem m2389_2420 : compute 2389 31 = (4096342015, 9847606204060, 123717914210400) := by decide +kernel
private theorem m2420_2452 : compute 2420 32 = (4228482080, 10298468105840, 127708814668800) := by decide +kernel
private theorem m2389_2452 : compute 2389 63 = (8324824095, 20146074309900, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2389_2420]
  change addMoment _ (compute 2420 32) = _
  rw [m2420_2452]
  rfl
private theorem m2452_2483 : compute 2452 31 = (4096342015, 10105675751005, 123717914210400) := by decide +kernel
private theorem m2483_2515 : compute 2483 32 = (4228482080, 10564862476880, 127708814668800) := by decide +kernel
private theorem m2452_2515 : compute 2452 63 = (8324824095, 20670538227885, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2452_2483]
  change addMoment _ (compute 2483 32) = _
  rw [m2483_2515]
  rfl
private theorem m2389_2515 : compute 2389 126 = (16649648190, 40816612537785, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m2389_2452]
  change addMoment _ (compute 2452 63) = _
  rw [m2452_2515]
  rfl
private theorem m2263_2515 : compute 2263 252 = (33299296380, 79535369403630, 1005706915516800) := by
  rw [show 252 = 126+126 by decide, compute_add, m2263_2389]
  change addMoment _ (compute 2389 126) = _
  rw [m2389_2515]
  rfl
private theorem m2012_2515 : compute 2012 503 = (66466452695, 150413582448785, 2007422930575200) := by
  rw [show 503 = 251+252 by decide, compute_add, m2012_2263]
  change addMoment _ (compute 2263 252) = _
  rw [m2263_2515]
  rfl
private theorem m2515_2546 : compute 2515 31 = (4096342015, 10363745297950, 123717914210400) := by decide +kernel
private theorem m2546_2577 : compute 2546 31 = (4096342015, 10490731900415, 123717914210400) := by decide +kernel
private theorem m2515_2577 : compute 2515 62 = (8192684030, 20854477198365, 247435828420800) := by
  rw [show 62 = 31+31 by decide, compute_add, m2515_2546]
  change addMoment _ (compute 2546 31) = _
  rw [m2546_2577]
  rfl
private theorem m2577_2608 : compute 2577 31 = (4096342015, 10617718502880, 123717914210400) := by decide +kernel
private theorem m2608_2640 : compute 2608 32 = (4228482080, 11093422736880, 127708814668800) := by decide +kernel
private theorem m2577_2640 : compute 2577 63 = (8324824095, 21711141239760, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2577_2608]
  change addMoment _ (compute 2608 32) = _
  rw [m2608_2640]
  rfl
private theorem m2515_2640 : compute 2515 125 = (16517508125, 42565618438125, 498862557300000) := by
  rw [show 125 = 62+63 by decide, compute_add, m2515_2577]
  change addMoment _ (compute 2577 63) = _
  rw [m2577_2640]
  rfl
private theorem m2640_2671 : compute 2640 31 = (4096342015, 10875788049825, 123717914210400) := by decide +kernel
private theorem m2671_2703 : compute 2671 32 = (4228482080, 11359817107920, 127708814668800) := by decide +kernel
private theorem m2640_2703 : compute 2640 63 = (8324824095, 22235605157745, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2640_2671]
  change addMoment _ (compute 2671 32) = _
  rw [m2671_2703]
  rfl
private theorem m2703_2734 : compute 2703 31 = (4096342015, 11133857596770, 123717914210400) := by decide +kernel
private theorem m2734_2766 : compute 2734 32 = (4228482080, 11626211478960, 127708814668800) := by decide +kernel
private theorem m2703_2766 : compute 2703 63 = (8324824095, 22760069075730, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2703_2734]
  change addMoment _ (compute 2734 32) = _
  rw [m2734_2766]
  rfl
private theorem m2640_2766 : compute 2640 126 = (16649648190, 44995674233475, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m2640_2703]
  change addMoment _ (compute 2703 63) = _
  rw [m2703_2766]
  rfl
private theorem m2515_2766 : compute 2515 251 = (33167156315, 87561292671600, 1001716015058400) := by
  rw [show 251 = 125+126 by decide, compute_add, m2515_2640]
  change addMoment _ (compute 2640 126) = _
  rw [m2640_2766]
  rfl
private theorem m2766_2797 : compute 2766 31 = (4096342015, 11391927143715, 123717914210400) := by decide +kernel
private theorem m2797_2829 : compute 2797 32 = (4228482080, 11892605850000, 127708814668800) := by decide +kernel
private theorem m2766_2829 : compute 2766 63 = (8324824095, 23284532993715, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2766_2797]
  change addMoment _ (compute 2797 32) = _
  rw [m2797_2829]
  rfl
private theorem m2829_2860 : compute 2829 31 = (4096342015, 11649996690660, 123717914210400) := by decide +kernel
private theorem m2860_2892 : compute 2860 32 = (4228482080, 12159000221040, 127708814668800) := by decide +kernel
private theorem m2829_2892 : compute 2829 63 = (8324824095, 23808996911700, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2829_2860]
  change addMoment _ (compute 2860 32) = _
  rw [m2860_2892]
  rfl
private theorem m2766_2892 : compute 2766 126 = (16649648190, 47093529905415, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m2766_2829]
  change addMoment _ (compute 2829 63) = _
  rw [m2829_2892]
  rfl
private theorem m2892_2923 : compute 2892 31 = (4096342015, 11908066237605, 123717914210400) := by decide +kernel
private theorem m2923_2955 : compute 2923 32 = (4228482080, 12425394592080, 127708814668800) := by decide +kernel
private theorem m2892_2955 : compute 2892 63 = (8324824095, 24333460829685, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2892_2923]
  change addMoment _ (compute 2923 32) = _
  rw [m2923_2955]
  rfl
private theorem m2955_2986 : compute 2955 31 = (4096342015, 12166135784550, 123717914210400) := by decide +kernel
private theorem m2986_3018 : compute 2986 32 = (4228482080, 12691788963120, 127708814668800) := by decide +kernel
private theorem m2955_3018 : compute 2955 63 = (8324824095, 24857924747670, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m2955_2986]
  change addMoment _ (compute 2986 32) = _
  rw [m2986_3018]
  rfl
private theorem m2892_3018 : compute 2892 126 = (16649648190, 49191385577355, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m2892_2955]
  change addMoment _ (compute 2955 63) = _
  rw [m2955_3018]
  rfl
private theorem m2766_3018 : compute 2766 252 = (33299296380, 96284915482770, 1005706915516800) := by
  rw [show 252 = 126+126 by decide, compute_add, m2766_2892]
  change addMoment _ (compute 2892 126) = _
  rw [m2892_3018]
  rfl
private theorem m2515_3018 : compute 2515 503 = (66466452695, 183846208154370, 2007422930575200) := by
  rw [show 503 = 251+252 by decide, compute_add, m2515_2766]
  change addMoment _ (compute 2766 252) = _
  rw [m2766_3018]
  rfl
private theorem m2012_3018 : compute 2012 1006 = (132932905390, 334259790603155, 4014845861150400) := by
  rw [show 1006 = 503+503 by decide, compute_add, m2012_2515]
  change addMoment _ (compute 2515 503) = _
  rw [m2515_3018]
  rfl
private theorem m3018_3049 : compute 3018 31 = (4096342015, 12424205331495, 123717914210400) := by decide +kernel
private theorem m3049_3080 : compute 3049 31 = (4096342015, 12551191933960, 123717914210400) := by decide +kernel
private theorem m3018_3080 : compute 3018 62 = (8192684030, 24975397265455, 247435828420800) := by
  rw [show 62 = 31+31 by decide, compute_add, m3018_3049]
  change addMoment _ (compute 3049 31) = _
  rw [m3049_3080]
  rfl
private theorem m3080_3111 : compute 3080 31 = (4096342015, 12678178536425, 123717914210400) := by decide +kernel
private theorem m3111_3143 : compute 3111 32 = (4228482080, 13220349223120, 127708814668800) := by decide +kernel
private theorem m3080_3143 : compute 3080 63 = (8324824095, 25898527759545, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m3080_3111]
  change addMoment _ (compute 3111 32) = _
  rw [m3111_3143]
  rfl
private theorem m3018_3143 : compute 3018 125 = (16517508125, 50873925025000, 498862557300000) := by
  rw [show 125 = 62+63 by decide, compute_add, m3018_3080]
  change addMoment _ (compute 3080 63) = _
  rw [m3080_3143]
  rfl
private theorem m3143_3174 : compute 3143 31 = (4096342015, 12936248083370, 123717914210400) := by decide +kernel
private theorem m3174_3206 : compute 3174 32 = (4228482080, 13486743594160, 127708814668800) := by decide +kernel
private theorem m3143_3206 : compute 3143 63 = (8324824095, 26422991677530, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m3143_3174]
  change addMoment _ (compute 3174 32) = _
  rw [m3174_3206]
  rfl
private theorem m3206_3237 : compute 3206 31 = (4096342015, 13194317630315, 123717914210400) := by decide +kernel
private theorem m3237_3269 : compute 3237 32 = (4228482080, 13753137965200, 127708814668800) := by decide +kernel
private theorem m3206_3269 : compute 3206 63 = (8324824095, 26947455595515, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m3206_3237]
  change addMoment _ (compute 3237 32) = _
  rw [m3237_3269]
  rfl
private theorem m3143_3269 : compute 3143 126 = (16649648190, 53370447273045, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m3143_3206]
  change addMoment _ (compute 3206 63) = _
  rw [m3206_3269]
  rfl
private theorem m3018_3269 : compute 3018 251 = (33167156315, 104244372298045, 1001716015058400) := by
  rw [show 251 = 125+126 by decide, compute_add, m3018_3143]
  change addMoment _ (compute 3143 126) = _
  rw [m3143_3269]
  rfl
private theorem m3269_3300 : compute 3269 31 = (4096342015, 13452387177260, 123717914210400) := by decide +kernel
private theorem m3300_3332 : compute 3300 32 = (4228482080, 14019532336240, 127708814668800) := by decide +kernel
private theorem m3269_3332 : compute 3269 63 = (8324824095, 27471919513500, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m3269_3300]
  change addMoment _ (compute 3300 32) = _
  rw [m3300_3332]
  rfl
private theorem m3332_3363 : compute 3332 31 = (4096342015, 13710456724205, 123717914210400) := by decide +kernel
private theorem m3363_3395 : compute 3363 32 = (4228482080, 14285926707280, 127708814668800) := by decide +kernel
private theorem m3332_3395 : compute 3332 63 = (8324824095, 27996383431485, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m3332_3363]
  change addMoment _ (compute 3363 32) = _
  rw [m3363_3395]
  rfl
private theorem m3269_3395 : compute 3269 126 = (16649648190, 55468302944985, 502853457758400) := by
  rw [show 126 = 63+63 by decide, compute_add, m3269_3332]
  change addMoment _ (compute 3332 63) = _
  rw [m3332_3395]
  rfl
private theorem m3395_3426 : compute 3395 31 = (4096342015, 13968526271150, 123717914210400) := by decide +kernel
private theorem m3426_3458 : compute 3426 32 = (4228482080, 14552321078320, 127708814668800) := by decide +kernel
private theorem m3395_3458 : compute 3395 63 = (8324824095, 28520847349470, 251426728879200) := by
  rw [show 63 = 31+32 by decide, compute_add, m3395_3426]
  change addMoment _ (compute 3426 32) = _
  rw [m3426_3458]
  rfl
private theorem m3458_3489 : compute 3458 31 = (4096342015, 14226595818095, 123717914210400) := by decide +kernel
private theorem m3489_3521 : compute 3489 32 = (4228104021, 14817385763469, 127693772373960) := by decide +kernel
private theorem m3458_3521 : compute 3458 63 = (8324446036, 29043981581564, 251411686584360) := by
  rw [show 63 = 31+32 by decide, compute_add, m3458_3489]
  change addMoment _ (compute 3489 32) = _
  rw [m3489_3521]
  rfl
private theorem m3395_3521 : compute 3395 126 = (16649270131, 57564828931034, 502838415463560) := by
  rw [show 126 = 63+63 by decide, compute_add, m3395_3458]
  change addMoment _ (compute 3458 63) = _
  rw [m3458_3521]
  rfl
private theorem m3269_3521 : compute 3269 252 = (33298918321, 113033131876019, 1005691873221960) := by
  rw [show 252 = 126+126 by decide, compute_add, m3269_3395]
  change addMoment _ (compute 3395 126) = _
  rw [m3395_3521]
  rfl
private theorem m3018_3521 : compute 3018 503 = (66466074636, 217277504174064, 2007407888280360) := by
  rw [show 503 = 251+252 by decide, compute_add, m3018_3269]
  change addMoment _ (compute 3269 252) = _
  rw [m3269_3521]
  rfl
private theorem m3521_3552 : compute 3521 31 = (4093197684, 14473539676990, 123593217432192) := by decide +kernel
private theorem m3552_3584 : compute 3552 32 = (4221271362, 15059371906250, 127424249201160) := by decide +kernel
private theorem m3521_3584 : compute 3521 63 = (8314469046, 29532911583240, 251017466633352) := by
  rw [show 63 = 31+32 by decide, compute_add, m3521_3552]
  change addMoment _ (compute 3552 32) = _
  rw [m3552_3584]
  rfl
private theorem m3584_3615 : compute 3584 31 = (4083213024, 14695464821707, 123202332138816) := by decide +kernel
private theorem m3615_3647 : compute 3615 32 = (4205599810, 15268400479788, 126814706991672) := by decide +kernel
private theorem m3584_3647 : compute 3584 63 = (8288812834, 29963865301495, 250017039130488) := by
  rw [show 63 = 31+32 by decide, compute_add, m3584_3615]
  change addMoment _ (compute 3615 32) = _
  rw [m3615_3647]
  rfl
private theorem m3521_3647 : compute 3521 126 = (16603281880, 59496776884735, 501034505763840) := by
  rw [show 126 = 63+63 by decide, compute_add, m3521_3584]
  change addMoment _ (compute 3584 63) = _
  rw [m3584_3647]
  rfl
private theorem m3647_3678 : compute 3647 31 = (4061799018, 14874271460968, 122374901276256) := by decide +kernel
private theorem m3678_3710 : compute 3678 32 = (4175978275, 15423924179310, 125677770166272) := by decide +kernel
private theorem m3647_3710 : compute 3647 63 = (8237777293, 30298195640278, 248052671442528) := by
  rw [show 63 = 31+32 by decide, compute_add, m3647_3678]
  change addMoment _ (compute 3678 32) = _
  rw [m3678_3710]
  rfl
private theorem m3710_3741 : compute 3710 31 = (4024634352, 14991704271889, 120958034572800) := by decide +kernel
private theorem m3741_3773 : compute 3741 32 = (4127700665, 15505627659963, 123849774964992) := by decide +kernel
private theorem m3710_3773 : compute 3710 63 = (8152335017, 30497331931852, 244807809537792) := by
  rw [show 63 = 31+32 by decide, compute_add, m3710_3741]
  change addMoment _ (compute 3741 32) = _
  rw [m3741_3773]
  rfl
private theorem m3647_3773 : compute 3647 126 = (16390112310, 60795527572130, 492860480980320) := by
  rw [show 126 = 63+63 by decide, compute_add, m3647_3710]
  change addMoment _ (compute 3710 63) = _
  rw [m3710_3773]
  rfl
private theorem m3521_3773 : compute 3521 252 = (32993394190, 120292304456865, 993894986744160) := by
  rw [show 252 = 126+126 by decide, compute_add, m3521_3647]
  change addMoment _ (compute 3647 126) = _
  rw [m3647_3773]
  rfl
private theorem m3773_3804 : compute 3773 31 = (3967332715, 15028168265724, 118803225074592) := by decide +kernel
private theorem m3804_3836 : compute 3804 32 = (4056601086, 15494074243334, 121194597034560) := by decide +kernel
private theorem m3773_3836 : compute 3773 63 = (8023933801, 30522242509058, 239997822109152) := by
  rw [show 63 = 31+32 by decide, compute_add, m3773_3804]
  change addMoment _ (compute 3804 32) = _
  rw [m3804_3836]
  rfl
private theorem m3836_3867 : compute 3836 31 = (3885513089, 14962990390324, 115769015602176) := by decide +kernel
private theorem m3867_3899 : compute 3867 32 = (3957688189, 15365569662550, 117552318881496) := by decide +kernel
private theorem m3836_3899 : compute 3836 63 = (7843201278, 30328560052874, 233321334483672) := by
  rw [show 63 = 31+32 by decide, compute_add, m3836_3867]
  change addMoment _ (compute 3867 32) = _
  rw [m3867_3899]
  rfl
private theorem m3773_3899 : compute 3773 126 = (15867135079, 60850802561932, 473319156592824) := by
  rw [show 126 = 63+63 by decide, compute_add, m3773_3836]
  change addMoment _ (compute 3836 63) = _
  rw [m3836_3899]
  rfl
private theorem m3899_3930 : compute 3899 31 = (3774927819, 14774905661819, 111725773473312) := by decide +kernel
private theorem m3930_3962 : compute 3930 32 = (3827144794, 15099800261588, 112813414483776) := by decide +kernel
private theorem m3899_3962 : compute 3899 63 = (7602072613, 29874705923407, 224539187957088) := by
  rw [show 63 = 31+32 by decide, compute_add, m3899_3930]
  change addMoment _ (compute 3930 32) = _
  rw [m3930_3962]
  rfl
private theorem m3962_3993 : compute 3962 31 = (3630952733, 14440094858398, 106536899289576) := by decide +kernel
private theorem m3993_4025 : compute 3993 32 = (3659567381, 14669121625893, 106817723133312) := by decide +kernel
private theorem m3962_4025 : compute 3962 63 = (7290520114, 29109216484291, 213354622422888) := by
  rw [show 63 = 31+32 by decide, compute_add, m3962_3993]
  change addMoment _ (compute 3993 32) = _
  rw [m3993_4025]
  rfl
private theorem m3899_4025 : compute 3899 126 = (14892592727, 58983922407698, 437893810379976) := by
  rw [show 126 = 63+63 by decide, compute_add, m3899_3962]
  change addMoment _ (compute 3962 63) = _
  rw [m3962_4025]
  rfl
private theorem m3773_4025 : compute 3773 252 = (30759727806, 119834724969630, 911212966972800) := by
  rw [show 252 = 126+126 by decide, compute_add, m3773_3899]
  change addMoment _ (compute 3899 126) = _
  rw [m3899_4025]
  rfl
private theorem m3521_4025 : compute 3521 504 = (63753121996, 240127029426495, 1905107953716960) := by
  rw [show 504 = 252+252 by decide, compute_add, m3521_3773]
  change addMoment _ (compute 3773 252) = _
  rw [m3773_4025]
  rfl
private theorem m3018_4025 : compute 3018 1007 = (130219196632, 457404533600559, 3912515841997320) := by
  rw [show 1007 = 503+504 by decide, compute_add, m3018_3521]
  change addMoment _ (compute 3521 504) = _
  rw [m3521_4025]
  rfl
private theorem m2012_4025 : compute 2012 2013 = (263152102022, 791664324203714, 7927361703147720) := by
  rw [show 2013 = 1006+1007 by decide, compute_add, m2012_3018]
  change addMoment _ (compute 3018 1007) = _
  rw [m3018_4025]
  rfl
private theorem m0_4025 : compute 0 4025 = (427286700047, 1015009542543574, 12678308899820400) := by
  rw [show 4025 = 2012+2013 by decide, compute_add, m0_2012]
  change addMoment _ (compute 2012 2013) = _
  rw [m2012_4025]
  rfl

theorem exact_moments :
    (sourceCount,sourceDegree,sourceIndex24) = (427286700047,1015009542543574,12678308899820400) := by
  have h := (compute_eq 0 4025).symm.trans m0_4025
  simpa [sourceCount,sourceDegree,sourceIndex24] using h

end ExpandedColumns6970
