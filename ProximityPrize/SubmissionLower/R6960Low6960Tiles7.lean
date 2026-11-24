import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass7

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 973148169, 1677923337, 6510286857, 2198544397, 2198545421], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1946888209, 1745562641, 1577791505, 1426797589, 1309358101, 1225473045], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1124810777, 1057702937, 990595097, 923487261, 873156637, 839603229], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [789272609, 755719201, 722165793, 688612389, 655058981, 638282789], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [2082893865, 2082894889, 2049341481, 1982233645, 1915125805, 1864795181], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1797687345, 1747356721, 1713803313, 1646695477, 1613142069, 1579588661], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1529258041, 1495704633, 1462151225, 1428597821, 1395044413, 1378268221], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1344714817, 1311161409, 1294385217, 1260831813, 1244055621, 1227279429], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1193726025, 1176949833, 1160173641, 1126620237, 1126621261, 5740326081], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [5723547845, 9984959693, 9968181457, 14229593305, 14196037857, 14162482409], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [18423894257, 14110757109, 18373561597, 18323228937, 22551086361, 22483976489], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [22400089405, 26611169617, 1100303687007, 1100303688031, 1100286908771, 1100270130535], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100253352299, 26493728109, 1100236574063, 1100219795827, 1100203017591, 1100186304891], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1100169526655, 1100135971207, 1100119192971, 588329357, 1100102414735, 557231509], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [540453273, 4801865121, 9063408041, 9029721521, 4715523509, 8996166073], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [13257577921, 13207245261, 13173689813, 17418324449, 4514195941, 17367991789], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [21612626425, 21545516553, 21495183893], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i3 : checks (tilesOf batches) 134 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 134 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 134 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6510286857, 2198544397, 2198545421, 1946888209, 1728785425, 1561014289], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1410020373, 1292580885, 1191918613, 1091256345, 1007371289, 957040665], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [873155613, 822824989, 789271581, 738940961, 705387553, 671834145], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [621503525, 604727333, 587951141, 2082893865, 2082894889, 2015787049], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1931901997, 1864794157, 1814463533, 1747355697, 1697025073, 1646694449], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1596363829, 1562810421, 1512479797, 1462149177, 1445372985, 1411819577], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1361488957, 1327935549, 1311159357, 1277605953, 1244052545, 1227276353], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1193722949, 1176946757, 1160170565, 1126617161, 1109840969, 1093064777], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1059511373, 1042735181, 2518196, 5773879481, 5757101245, 10018513093], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [9984957645, 14246369493, 14212814045, 18474225893, 18423893233, 18356783361], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [22601417997, 22517530913, 22433643829, 1100236579147, 26627946829, 1100253355343], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100253354323, 1100270130519, 1100286906715, 1100303682911, 1100286904675, 1100270126439], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [26510505321, 1100253348203, 1100236569967, 1100203014519, 1100186301819, 1100169523583], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1100135968135, 605106569, 590784909, 3581332, 4835418521, 4801863073], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [9046497709, 4732300721, 9012942261, 8979386813, 13224021449, 13173688789], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [17418323425, 4514195941, 17367990765, 1099649638907, 17300880893, 1099616083459], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099599305223, 21528738317, 1099565749775, 1099532194327], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i6 : checks (tilesOf batches) 134 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 134 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 134 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2198545421, 1963665425, 1745562641, 1577791505, 1410020373, 1292580885], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1191918613, 1074479129, 1007371289, 940263449, 856378397, 806047773], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [755717149, 705386529, 671833121, 638279713, 587949093, 554395685], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [537619493, 2082893865, 2049340457, 1982232617, 1898347565, 1831239725], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1780909101, 1713801265, 1663470641, 1613140017, 1546032181, 1512478773], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1478925365, 1428594745, 1395041337, 1361487929, 1311157309, 1277603901], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1260827709, 1210497089, 1193720897, 1176944705, 1126614085, 1109837893], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1093061701, 1059508297, 1042732105, 1025955913, 992402509, 992403533], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [2518184, 5824211117, 5790655669, 10052067517, 10018512069, 14279923917], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [14246368469, 14196035809, 18440670445, 18373560573, 22601417997, 22534308125], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [22433643829, 1100253355327, 1100219801919, 1100270131523, 1100270130503, 1100286906699], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [26627946829, 1100303682895, 1100320459091, 1100337235287, 1100303679839, 1100286901603], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100270123367, 26510505321, 1100236567919, 1100219789683, 1100186299771, 1100152744323], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [607561097, 588329357, 574005649, 4835417497, 4801862049, 9063273897], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [4715523509, 9012941237, 8962608577, 13207243213, 13156910553, 17401545189], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [4497418729, 1099649638891, 1099649637875, 17334435317, 1099649636859, 1099632858623], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [21562292741, 1099599303175, 1099565747727, 57868, 57872, 21495182869], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [1099532192279, 16834068, 16834072], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i9 : checks (tilesOf batches) 134 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 134 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 134 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1594568721, 1426797589, 1292580885, 1191918613, 1074479129, 1007371289], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [923486233, 856378397, 789270557, 755717149, 688609313, 655055905], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [604725281, 571171877, 537618469, 504065061, 2082893865, 2032563241], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1965455401, 1881570349, 1814462509, 1747354669, 1680246833, 1629916209], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1579585585, 1512477749, 1478924341, 1428593717, 1378263097, 1344709689], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1311156281, 1260825661, 1244049469, 1210496061, 1176942657, 1143389249], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1126613057, 1076282437, 1059506245, 1042730053, 1009176649, 992400457], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [975624265, 942070861, 925294669, 1579576481, 5840988329, 5807432881], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [10085621941, 10035289281, 14296701129, 14246368469, 14212813021, 18440670445], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18390337785, 22601417997, 22534308125, 1100236579119, 1100253355315, 22433643829], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100253354295, 1100270130491, 1100286906687, 1100303682883, 1100337236295, 1100354012491], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [26627946829, 1100354011475, 1100337233239, 1100303677791, 1100286899555, 1100253344107], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [26493728109, 1100236565871, 1100203010423, 1100169520511, 624337285, 590781837], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [571552145, 4835416473, 4801861025, 9046495661, 8996163001, 13240797637], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13190464977, 1099649638879, 13123355105, 1099649637863, 1099666414059, 17351212529], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099666413043, 1099649634811, 17284102657, 1099616079363, 57856, 57860], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [16834056, 1099565746703, 16834060, 21511960081, 33610256, 1099532191255], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [33610260, 50386456], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i12 : checks (tilesOf batches) 134 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 134 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 134 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1208695829, 1091256345, 1007371289, 940263449, 856378397, 806047773], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [738939933, 688609313, 638278689, 604725281, 554394661, 520841253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [487287845, 2082893865, 2032563241, 1948678185, 1864793133, 1797685293], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1730577453, 1663469617, 1613138993, 1562808369, 1495700533, 1445369909], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1411816501, 1361485881, 1311155257, 1277601849, 1227271229, 1210495037], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1176941629, 1126611009, 1109834817, 1076281409, 1042728005, 1025951813], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1009175621, 958845001, 942068809, 925292617, 891739213, 874963021], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1596353693, 5857765541, 5824210093, 10085621941, 10052066493, 14296701129], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [14263145681, 14196035809, 18440670445, 18373560573, 22601417997, 22517530913], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100236579107, 1100253355303, 1100270131499, 1100286907695, 1100303683891, 22416866617], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100303682875, 1100320459071, 1100354012483, 1100370788679, 1100370787663, 1100354009427], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100320453979, 1100286898531, 1100270120295, 1100236564847, 1100203009399, 641114497], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [607559049, 4868970897, 4818638237, 9063272873, 9012940213, 8962607553], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13207242189, 1099649638867, 1099649637851, 13140132317, 1099649636835, 1099649635819], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17367989741, 1099666412019, 57844, 1099649633787, 57848, 17300879869], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [16834044, 1099616078339, 16834048, 33610244, 33610248, 1099565745679], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [50386444, 21511960081, 50386448, 1099532190231, 50386452, 67162648], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [940263449, 873155613, 806047773, 755717149, 688609313, 638278689], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [604725281, 554394661, 520841253, 487287845, 2082893865, 2032563241], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1948678185, 1864793133, 1797685293, 1730577453, 1646692401, 1596361777], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1546031153, 1478923317, 1428592693, 1395039285, 1327931449, 1294378041], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1260824633, 1210494013, 1176940605, 1143387197, 1109833793, 1076280385], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1059504193, 1009173573, 992397381, 975621189, 925290569, 908514377], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [891738185, 858184781, 841408589, 1596353693, 5857765541, 5824210093], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [10085621941, 10052066493, 14296701129, 14246368469, 14196035809, 18423893233], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [18373560573, 1100236579099, 1100253355295, 1100270131491, 1100286907687, 1100303683883], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100303682867, 1100320459063, 1100354012475, 1100370788675, 1100387564871, 1100370786639], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100354008403, 1100320452955, 1100286897507, 1100253342059, 1100219786611, 674668921], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [624336261, 4885748109, 4835415449, 4785082789, 9029717425, 8979384765], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099649638859, 13207242189, 1099649637843, 1099649636827, 13140132317, 1099666413027], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099666412011, 17367989741, 57836, 1099666410995, 57840, 16834036], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099649632763, 16834040, 17300879869, 33610236, 33610240, 1099599300103], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [33610244, 50386440, 50386444, 21511960081, 1099548967443, 67162640], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [67162644, 3718680, 83938840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [755717149, 688609313, 655055905, 604725281, 554394661, 520841253], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [487287845, 2082893865, 2049340457, 1965455401, 1864793133, 1797685293], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1730577453, 1646692401, 1596361777, 1546031153, 1478923317, 1428592693], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1378262069, 1327931449, 1277600825, 1244047417, 1193716797, 1160163389], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1126609981, 1076279361, 1059503169, 1025949761, 992396357, 958842949], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [942066757, 908513353, 874959945, 858183753, 824630349, 807854157], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1596353693, 5857765541, 5824210093, 10085621941, 10035289281, 14296701129], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14246368469, 1100236579091, 1100253355287, 1100270131483, 1100286907679, 1100286906663], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100320460075, 1100337236271, 1100354012471, 1100370788667, 1100387564867, 1100404341063], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100370785615, 1100337230167, 1100303674719, 1100270119271, 1100236563823, 674668921], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [641113473, 590780813, 4835415449, 4785082789, 9029717425, 8979384765], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099649638851, 1099649637835, 13207242189, 1099666414035, 1099666413019, 13140132317], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099666412003, 57828, 57832, 17367989741, 1099666410991, 16834028], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [16834032, 1099666409975, 16834036, 33610232, 33610236, 17284102657], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099616077315, 50386432, 50386436, 1099582521867, 67162632, 67162636], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [67162640, 21495182869, 1099532123671, 83938836, 83938840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [621502497, 554394661, 520841253, 487287845, 2082893865, 2049340457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1965455401, 1881570349, 1814462509, 1747354669, 1663469617, 1596361777], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1546031153, 1478923317, 1428592693, 1378262069, 1311154233, 1277600825], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1244047417, 1193716797, 1143386173, 1109832765, 1076279361, 1042725953], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1009172545, 975619141, 942065733, 925289541, 874958921, 858182729], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [841406537, 807853133, 774299725, 1596353693, 5857765541, 5824210093], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [10068844729, 1100253356299, 1100253355283, 1100270131479, 1100286907675, 1100303683871], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100320460071, 1100337236267, 1100354012467, 1100370788663, 1100387564863, 1100404341063], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100387562827, 1100354007379, 1100303674719, 1100270119271, 1100236563823, 1100203008375], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [641113473, 590780813, 4835415449, 4785082789, 9029717425, 1099649638847], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [8962607553, 1099649637831, 1099649636815, 13190464977, 1099666413015, 1099666411999], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13123355105, 57824, 57828, 1099666410987, 16834024, 16834028], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17351212529, 1099683187187, 33610224, 33610228, 33610232, 1099632854527], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [50386428, 17284102657, 50386432, 1099599299079, 67162628, 67162632], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [67162636, 1099548900883, 83938832, 21495182869, 83938836, 83938840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 134 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [504065061, 2082893865, 2066117673, 1982232617, 1898347565, 1814462509], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1747354669, 1663469617, 1613138993, 1546031153, 1478923317, 1428592693], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1378262069, 1311154233, 1277600825, 1227270201, 1176939581, 1143386173], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1109832765, 1059502145, 1025948737, 992395329, 958841925, 925288517], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [908512325, 858181705, 841405513, 824629321, 774298701, 757522509], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1579576481, 1100236579079, 1100270132491, 1100270131475, 1100286907671, 1100303683867], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100320460067, 1100337236263, 1100354012463, 1100387565875, 1100404342075, 1100421118275], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100387562827, 1100354007379, 1100320451931, 1100286896483, 1100236563823, 1100203008375], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [641113473, 4885748109, 4835415449, 9080050085, 9012940213, 1099666416055], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8962607553, 1099649637827, 1099649636811, 13190464977, 1099666413011, 1099666411995], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57820, 13123355105, 57824, 1099666410983, 16834020, 16834024], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099683187183, 33610220, 33610224, 17334435317, 33610228, 1099649631739], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50386424, 50386428, 67162624, 17267325445, 1099599299079, 67162628], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [67162632, 83938828, 1099548900883, 83938832, 83938836, 21478405657], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [100715032], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1999009833, 1898347565, 1831239725, 1764131885, 1680246833, 1613138993], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1562808369, 1478923317, 1428592693, 1378262069, 1327931449, 1277600825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1244047417, 1176939581, 1143386173, 1109832765, 1059502145, 1025948737], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [992395329, 942064709, 925288517, 891735109, 858181705, 824628297], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [807852105, 774298701, 740745293, 1099665170691, 1100253355275, 1100270131471], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100286907667, 1100303683867, 1100320460063, 1100337236263, 1100370789675, 1100085584171], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100387565875, 1100404342075, 1100421118275, 1100387562827, 1100354007379, 1100320451931], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100270119271, 1100236563823, 674668921, 641113473, 4885748109, 4835415449], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9063272873, 9012940213, 1099649638839, 1099649637823, 13240797637, 1099666414023], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099666413007, 13173687765, 1099666411995, 57816, 57820, 1099683188195], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16834016, 13106577893, 16834020, 16834024, 1099683187183, 33610220], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610224, 17334435317, 50386420, 1099649631739, 50386424, 50386428], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67162624, 1099599299079, 67162628, 17250548233, 67162632, 83938828], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099548900883, 83938832, 83938836, 100715032], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1764131885, 1697024049, 1629916209, 1562808369, 1495700533, 1445369909], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1395039285, 1327931449, 1277600825, 1244047417, 1176939581, 1143386173], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1109832765, 1059502145, 1025948737, 992395329, 942064709, 908511301], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [891735109, 841404489, 824628297, 791074889, 757521485, 740745293], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099648393475, 1100253355271, 1100286908683, 1100286907667, 1100303683863, 1100320460063], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100354013475, 1100085584167, 1100370789675, 1100387565875, 1100404342075, 1100421118275], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100387562827, 1100354007379, 1100320451931, 1100270119271, 1100236563823, 674668921], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [624336261, 4868970897, 4818638237, 9063272873, 1099666416051, 8996163001], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099666415035, 1099649636807, 13224020425, 1099666413007, 13173687765, 1099683189207], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57816, 57820, 1099683188195, 16834016, 16834020, 33610216], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099683187183, 33610220, 33610224, 50386420, 1099649631739, 50386424], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [50386428, 67162624, 1099599299079, 67162628, 67162632, 83938828], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099548900883, 83938832, 83938836, 100715032], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1579585585, 1495700533, 1445369909, 1395039285, 1327931449, 1294378041], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1244047417, 1193716797, 1143386173, 1109832765, 1059502145, 1025948737], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [992395329, 942064709, 908511301, 891735109, 841404489, 807851081], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [791074889, 740744269, 723968077, 1099665170687, 1099681946883, 1100270131467], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100303684879, 1100303683863, 1100320460063, 1100354013475, 1100085584167, 1100370789675], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100085583151, 1100387565875, 1100404342075, 1100421118275, 1100387562827, 1100354007379], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100303674719, 1100270119271, 1100219786611, 674668921, 624336261, 4868970897], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4818638237, 9046495661, 1099649638835, 1099666415035, 1099666414019, 1099666413007], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099683189207, 57812, 57816, 57820, 1099683188195, 16834016], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16834020, 33610216, 1099683187183, 33610220, 33610224, 50386420], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099649631739, 50386424, 50386428, 67162624, 1099599299079, 67162628], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162632, 83938828, 1099548900883, 83938832, 83938836, 100715032], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1411816501, 1344708665, 1294378041, 1244047417, 1193716797, 1160163389], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1109832765, 1059502145, 1025948737, 992395329, 942064709, 908511301], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [874957893, 841404489, 807851081, 791074889, 740744269, 723968077], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099665170687, 1099665169667, 1100270131467, 1100303684879, 1100303683863, 1100337237275], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100354013475, 1100068806951, 1100370789675, 1100102360363, 1100387565875, 1100421119291], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100421118275, 1100387562827, 1100337230167, 1100303674719, 1100270119271, 641049969], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [657891709, 607559049, 1099666416047, 1099666415035, 1099666414019, 1099666413007], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099683189207, 57812, 57816, 57820, 1099683188195, 16834016], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16834020, 33610216, 1099683187183, 33610220, 33610224, 50386420], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099649631739, 50386424, 50386428, 67162624, 1099599299079, 67162628], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67162632, 54044173, 83938828, 83938832, 1099532123671, 83938836], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [100715032], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 7 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
    · exact Top13.exact a ha h13 (by omega) (by omega)
end Low6960Allocation.Group7
