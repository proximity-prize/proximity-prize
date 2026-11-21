import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableEmpty1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .empty 1 := packedBatch [285181444,294160904,287311880,306515468,1943082000,7098933272] (by decide +kernel)
private def b1 : PaidBatch .empty 1 := packedBatch [7958837800,298389036,571019308,575214124,8277611576,290490952] (by decide +kernel)
private def b2 : PaidBatch .empty 1 := packedBatch [563121224,1112608332,832572040,1918930572,3554710668,557811972] (by decide +kernel)
private def b3 : PaidBatch .empty 1 := packedBatch [1639942916,3263139592,6777967880,8954814732,10053725964,9276832532] (by decide +kernel)
private def b4 : PaidBatch .empty 1 := packedBatch [10107308308,10937783572,11768258836,12036958092,11462563212,12012018572] (by decide +kernel)
private def b5 : PaidBatch .empty 1 := packedBatch [12561473932,10338941836,10888397708,11706288524,12255743884,12569864108] (by decide +kernel)
private def b6 : PaidBatch .empty 1 := packedBatch [12574059436,12838365640,12842560456,12561606088,12834236360,12268099016] (by decide +kernel)
private def b7 : PaidBatch .empty 1 := packedBatch [12817554376,12553314760,12825945032,12838398416,1010641,1010133] (by decide +kernel)
private def b8 : PaidBatch .empty 1 := packedBatch [1010645,12834269144,1010137,1043417,12830107096,1009629] (by decide +kernel)
private def b9 : PaidBatch .empty 1 := packedBatch [1042909,1043421,1009121,1009633,1042913,1043425] (by decide +kernel)
private def b10 : PaidBatch .empty 1 := packedBatch [12825977828,1009125,1042405,1042917,1076197,12821815780] (by decide +kernel)
private def b11 : PaidBatch .empty 1 := packedBatch [12817686500,12532569572,12536764900,12809395172,12813589988,1008617] (by decide +kernel)
private def b12 : PaidBatch .empty 1 := packedBatch [1009129,1042409,1042921,1076201,12821848556,1008621] (by decide +kernel)
private def b13 : PaidBatch .empty 1 := packedBatch [1041901,1042413,1075693,1076205,1008113,1041393] (by decide +kernel)
private def b14 : PaidBatch .empty 1 := packedBatch [1041905,1075185,1075697,1108977,12817719284,1008117] (by decide +kernel)
private def b15 : PaidBatch .empty 1 := packedBatch [1041397,1041909,1075189,1075701,1108981,1007609] (by decide +kernel)
private def b16 : PaidBatch .empty 1 := packedBatch [1040889,1041401,1074681,1075193,1108473,1108985] (by decide +kernel)
private def b17 : PaidBatch .empty 1 := packedBatch [1007613,1040893,1041405,1074685,1075197,1108477] (by decide +kernel)
private def b18 : PaidBatch .empty 1 := packedBatch [1141757] (by decide +kernel)
private def batches : List (PaidBatch .empty 1) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 127 3 14 = true := by decide +kernel
private theorem i17 : checks tiles 127 17 14 = true := by decide +kernel
private theorem i31 : checks tiles 127 31 14 = true := by decide +kernel
private theorem i45 : checks tiles 127 45 9 = true := by decide +kernel
def receipt : Certificate .empty 1 := ⟨batches, checks_join i3 (checks_join i17 (checks_join i31 i45))⟩
end Top1

namespace Top2
private def b0 : PaidBatch .empty 2 := packedBatch [302287880,1120997900,3831535632,7103128600,298355752,570986536] (by decide +kernel)
private def b1 : PaidBatch .empty 2 := packedBatch [8495709224,9082917944,567315528,839946312,1646267528,2195755660] (by decide +kernel)
private def b2 : PaidBatch .empty 2 := packedBatch [2990509316,4076835592,7323228424,8959010060,10594791692,9276833044] (by decide +kernel)
private def b3 : PaidBatch .empty 2 := packedBatch [10375743764,11474654484,12305129748,12292809100,12842264460,11181543308] (by decide +kernel)
private def b4 : PaidBatch .empty 2 := packedBatch [11999434124,12548889484,10338942348,11156833164,11974723980,12569766316] (by decide +kernel)
private def b5 : PaidBatch .empty 2 := packedBatch [12842396588,12557279660,12561474988,12834105260,12842429372,12838267324] (by decide +kernel)
private def b6 : PaidBatch .empty 2 := packedBatch [1469377,1468869,1469381,12834138056,1468873,1502153] (by decide +kernel)
private def b7 : PaidBatch .empty 2 := packedBatch [12829976008,12553216456,12825846728,11987079112,12263904712,11999664584] (by decide +kernel)
private def b8 : PaidBatch .empty 2 := packedBatch [12813360072,12817555400,1468365,1501645,1502157,1467857] (by decide +kernel)
private def b9 : PaidBatch .empty 2 := packedBatch [1468369,1501649,1534929,1467861,1501141,1534421] (by decide +kernel)
private def b10 : PaidBatch .empty 2 := packedBatch [1534933,1467353,1500633,1501145,1534425,1567705] (by decide +kernel)
private def b11 : PaidBatch .empty 2 := packedBatch [12821717464,1467357,1500637,1533917,1567197,1567709] (by decide +kernel)
private def b12 : PaidBatch .empty 2 := packedBatch [1466849,1500129,1500641,1533921,1567201,95707852411294694939585506] (by decide +kernel)
private def b13 : PaidBatch .empty 2 := packedBatch [12817588196,1466853,1500133,1533413,1566693,1567205] (by decide +kernel)
private def b14 : PaidBatch .empty 2 := packedBatch [96640221445776519268953062,12813426148,12809296868,12251549668,11987309540,12259939812] (by decide +kernel)
private def b15 : PaidBatch .empty 2 := packedBatch [12532570084,12805200356,1466345,1499625,1532905,1533417] (by decide +kernel)
private def b16 : PaidBatch .empty 2 := packedBatch [1566697,94214881694013608076274154,97572590480258343598353386,12813458924,1466349,1499629] (by decide +kernel)
private def b17 : PaidBatch .empty 2 := packedBatch [1532909,1566189,91758024443180472847034350,95111033331351663108188654,98504959514740167927720942,1465841] (by decide +kernel)
private def b18 : PaidBatch .empty 2 := packedBatch [1499121,1532401,1532913,1566193,92618675859437589195941874,96007184968689718140135922] (by decide +kernel)
private def b19 : PaidBatch .empty 2 := packedBatch [99437328549221992257121266,12809329652,1465845,1499125,1532405,1565685] (by decide +kernel)
private def b20 : PaidBatch .empty 2 := packedBatch [90098745356798856388437494,93479327275694704991201270,96903336606027773708954102,100369697583703816586521590,1465337,1498617] (by decide +kernel)
private def b21 : PaidBatch .empty 2 := packedBatch [1531897,1532409,1565689,90924613728037863594943994,94339978691951821340076026,97799488243365828740868602] (by decide +kernel)
private def b22 : PaidBatch .empty 2 := packedBatch [101302066618185640379018234,1465341,1498621,1531901,1565181,79317199134751653281031166] (by decide +kernel)
private def b23 : PaidBatch .empty 2 := packedBatch [91750482099276871338354174,95200630108208937688983550,98695639880703883756038654,102234435652667464708418558] (by decide +kernel)
private def batches : List (PaidBatch .empty 2) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 127 6 11 = true := by decide +kernel
private theorem i17 : checks tiles 127 17 11 = true := by decide +kernel
private theorem i28 : checks tiles 127 28 11 = true := by decide +kernel
private theorem i39 : checks tiles 127 39 11 = true := by decide +kernel
private theorem i50 : checks tiles 127 50 4 = true := by decide +kernel
def receipt : Certificate .empty 2 := ⟨batches, checks_join i6 (checks_join i17 (checks_join i28 (checks_join i39 i50)))⟩
end Top2

namespace Top3
private def b0 : PaidBatch .empty 3 := packedBatch [1120997900,2745210896,4381023764,7379986972,8768372780,9619822140] (by decide +kernel)
private def b1 : PaidBatch .empty 3 := packedBatch [2195755660,6505337608,8141119244,10045336336,10871617296,10090529048] (by decide +kernel)
private def b2 : PaidBatch .empty 3 := packedBatch [10648374552,12015720216,12573565720,12573698444,12284419468,12833874828] (by decide +kernel)
private def b3 : PaidBatch .empty 3 := packedBatch [11445783948,11454174092,12540499852,11152638348,11970529164,12569635228] (by decide +kernel)
private def b4 : PaidBatch .empty 3 := packedBatch [12842265500,12842298284,12838136236,12561376684,12834006956,12548890028] (by decide +kernel)
private def b5 : PaidBatch .empty 3 := packedBatch [12553085356,12825715628,1469361,12838169012,1469365,1468857] (by decide +kernel)
private def b6 : PaidBatch .empty 3 := packedBatch [1502137,1468349,1501629,1502141,12829877692,1468353] (by decide +kernel)
private def b7 : PaidBatch .empty 3 := packedBatch [1501633,1534913,1467845,1501125,1534405,1534917] (by decide +kernel)
private def b8 : PaidBatch .empty 3 := packedBatch [12825748424,1500617,1501129,1534409,1567689,12821586376] (by decide +kernel)
private def b9 : PaidBatch .empty 3 := packedBatch [12817457096,12259709896,12263905224,12536535496,12809165768,12813360584] (by decide +kernel)
private def b10 : PaidBatch .empty 3 := packedBatch [12247354824,12251550152,1467341,1500621,1533901,1534413] (by decide +kernel)
private def b11 : PaidBatch .empty 3 := packedBatch [1567693,12821619152,1500113,1500625,1533905,1567185] (by decide +kernel)
private def b12 : PaidBatch .empty 3 := packedBatch [79378433108893230697671634,1466837,1500117,1533397,1566677,1567189] (by decide +kernel)
private def b13 : PaidBatch .empty 3 := packedBatch [80122264554058494914980822,12817489880,1499609,1500121,1533401,1566681] (by decide +kernel)
private def b14 : PaidBatch .empty 3 := packedBatch [78162269291755383355992538,80866095999223758595451866,1466333,1499613,1532893,1566173] (by decide +kernel)
private def b15 : PaidBatch .empty 3 := packedBatch [76179147488310952258004958,78878484670688351023655390,81609927444389022812761054,1499105,1499617,1532897] (by decide +kernel)
private def b16 : PaidBatch .empty 3 := packedBatch [1566177,76868263167776862105626594,79594700049621319228221922,82353758889554286493232098,1465829,1499109] (by decide +kernel)
private def b17 : PaidBatch .empty 3 := packedBatch [1532389,1565669,74837755140932861292570086,77557378847242771416344550,80310915428554286895884774,83097590334719550710541286] (by decide +kernel)
private def b18 : PaidBatch .empty 3 := packedBatch [12809231332,12259841508,12532471780,12805102052,12524180452,1498601] (by decide +kernel)
private def b19 : PaidBatch .empty 3 := packedBatch [1499113,1532393,1565673,75500287487696949885396458,78246494526708681263966186,81027130807487255100451306] (by decide +kernel)
private def b20 : PaidBatch .empty 3 := packedBatch [83841421779884814391012330,1465325,1498605,1531885,1565165,73425749621427423583265774] (by decide +kernel)
private def b21 : PaidBatch .empty 3 := packedBatch [76162819834461039031870958,78935610206174590574684142,81743346186420222768114158,84585253225050078608321518,1465329,1498609] (by decide +kernel)
private def b22 : PaidBatch .empty 3 := packedBatch [1531889,1565169,74062215002254929147585522,76825352181225127641507314,79624725885640500422305778,82459561565353190972680690] (by decide +kernel)
private def b23 : PaidBatch .empty 3 := packedBatch [85329084670215342288792562,1464821,1498101,1531381,1564661,71947003680533922119279094] (by decide +kernel)
private def b24 : PaidBatch .empty 3 := packedBatch [74698680383082435248808950,77487884527989216787981814,80313841565106409716246518,83175776944286158640343542,86072916115380606506101750,12528342516] (by decide +kernel)
private def b25 : PaidBatch .empty 3 := packedBatch [12800972788,1464825,1498105,1531385,1564665,72557918462190082831016442] (by decide +kernel)
private def b26 : PaidBatch .empty 3 := packedBatch [75335145763909940813128698,78150416874753305397618170,81002957244572319563868154,83891992323219126844910074,86816747560545870186572794,12796810748] (by decide +kernel)
private def b27 : PaidBatch .empty 3 := packedBatch [1464317,1497597,1530877,1564157,1564669,73168833243846243005915646] (by decide +kernel)
private def b28 : PaidBatch .empty 3 := packedBatch [75971611144737446914319358,78812949221517394544092670,81692072924038228874586110,84608207702152094495795710,87560579005711134403881982] (by decide +kernel)
private def batches : List (PaidBatch .empty 3) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 127 9 9 = true := by decide +kernel
private theorem i18 : checks tiles 127 18 9 = true := by decide +kernel
private theorem i27 : checks tiles 127 27 9 = true := by decide +kernel
private theorem i36 : checks tiles 127 36 9 = true := by decide +kernel
private theorem i45 : checks tiles 127 45 9 = true := by decide +kernel
def receipt : Certificate .empty 3 := ⟨batches, checks_join i9 (checks_join i18 (checks_join i27 (checks_join i36 i45)))⟩
end Top3

namespace Top4
private def b0 : PaidBatch .empty 4 := packedBatch [3831535632,4389413912,7384182304,9309438508,10156693564,7323228424] (by decide +kernel)
private def b1 : PaidBatch .empty 4 := packedBatch [8417944844,9781096208,11412683024,11230929688,10363159320,11189440280] (by decide +kernel)
private def b2 : PaidBatch .empty 4 := packedBatch [12284156184,12296741716,12305131860,12842133900,12276029836,12284419980] (by decide +kernel)
private def b3 : PaidBatch .empty 4 := packedBatch [12829680524,12833875852,11168958860,11718414220,11995239820,11425268620] (by decide +kernel)
private def b4 : PaidBatch .empty 4 := packedBatch [12842199964,12838070684,1469349,1502121,12833908652,1468845] (by decide +kernel)
private def b5 : PaidBatch .empty 4 := packedBatch [1502125,12829746604,12825617324,12540500396,12544695724,12817325996] (by decide +kernel)
private def b6 : PaidBatch .empty 4 := packedBatch [12821520812,1468337,1501617,1534897,12829779380,1501109] (by decide +kernel)
private def b7 : PaidBatch .empty 4 := packedBatch [1501621,1534901,1467833,1501113,1534393,1567673] (by decide +kernel)
private def b8 : PaidBatch .empty 4 := packedBatch [12825650108,1500605,1501117,1534397,1567677,1467329] (by decide +kernel)
private def b9 : PaidBatch .empty 4 := packedBatch [1500609,1533889,1567169,1567681,1500101,1500613] (by decide +kernel)
private def b10 : PaidBatch .empty 4 := packedBatch [1533893,1567173,83250754122619045970832326,1466825,1500105,1533385] (by decide +kernel)
private def b11 : PaidBatch .empty 4 := packedBatch [1566665,81201762130401458587298250,84019787132625951703329738,12817391560,12268001736,12540632008] (by decide +kernel)
private def b12 : PaidBatch .empty 4 := packedBatch [12813262280,11982884808,12259710408,12532340680,11702094280,11706289608] (by decide +kernel)
private def b13 : PaidBatch .empty 4 := packedBatch [12524180424,1499597,1532877,1533389,1566669,81942576646283291041851854] (by decide +kernel)
private def b14 : PaidBatch .empty 4 := packedBatch [84788820142632857435794382,1466321,1499601,1532881,1566161,79843315382893557299931090] (by decide +kernel)
private def b15 : PaidBatch .empty 4 := packedBatch [82683391162165123496438226,85557853152639763168291794,1499093,1532373,1532885,1566165] (by decide +kernel)
private def b16 : PaidBatch .empty 4 := packedBatch [80556427771415554132436950,83424205678046955950991830,86326886162646668900756438,1465817,1499097,1532377] (by decide +kernel)
private def b17 : PaidBatch .empty 4 := packedBatch [1565657,78410253620827717184382426,81269540159937550964910042,84165020193928788405578202,87095919172653574633253850,12809133016] (by decide +kernel)
private def b18 : PaidBatch .empty 4 := packedBatch [12804970968,1498589,1499101,1532381,1565661,79096180248755116050638302] (by decide +kernel)
private def b19 : PaidBatch .empty 4 := packedBatch [81982652548459547797383134,84905834709810620860131806,87864952182660480365718494,1465313,1498593,1531873] (by decide +kernel)
private def b20 : PaidBatch .empty 4 := packedBatch [1565153,76906449594943222253216738,79782106876682514916861410,82695764936981544629888994,85646649225692453314718178,88633985192667386098215906] (by decide +kernel)
private def b21 : PaidBatch .empty 4 := packedBatch [12532373476,1465317,1498597,1531877,1565157,77565706829041260809053158] (by decide +kernel)
private def b22 : PaidBatch .empty 4 := packedBatch [80468033504609913783117286,83408877325503541462362086,86387463741574285769271782,89403018202674291830680550,12805036516,12528276964] (by decide +kernel)
private def b23 : PaidBatch .empty 4 := packedBatch [11978919908,12251550180,12800841704,1498089,1531369,1564649] (by decide +kernel)
private def b24 : PaidBatch .empty 4 := packedBatch [75335776055979353348104682,78224964063139299364856810,81153960132537312632563178,84121989714025538294867946,87128278257456118223858154,90172051212681197563177962] (by decide +kernel)
private def b25 : PaidBatch .empty 4 := packedBatch [1464813,1498093,1531373,1564653,75968880263013269249352174,78884221297237337920693230] (by decide +kernel)
private def b26 : PaidBatch .empty 4 := packedBatch [81839886760464711498786286,84835102102547535127341038,87869092773337950678411758,90941084222688103295642606,12800907244,1497585] (by decide +kernel)
private def b27 : PaidBatch .empty 4 := packedBatch [1530865,1531377,1564657,76601984470047185150566898,79543478531335376476496882,82525813388392110365042162] (by decide +kernel)
private def b28 : PaidBatch .empty 4 := packedBatch [85548214491069531959846898,88609907289219783132998130,91710117232695009028140018,1431029,1464309,1497589] (by decide +kernel)
private def b29 : PaidBatch .empty 4 := packedBatch [1530869,1564149,74309573301410425384099830,77235088677081101051814390,80202735765433415032300534,83211740016319509231265270] (by decide +kernel)
private def b30 : PaidBatch .empty 4 := packedBatch [86261326879591528775542774,89350721805101615587551734,92479150242701914760604662,1431033,1464313,1497593] (by decide +kernel)
private def b31 : PaidBatch .empty 4 := packedBatch [1530873,1564153,74917040848145456286556154,77868192884115016953029114,80861992999531453588136954,83897666644246908097521146] (by decide +kernel)
private def b32 : PaidBatch .empty 4 := packedBatch [86974439268113525608048634,90091536320983448042138106,93248183252708820493102074,12796810748,1497085,1530365] (by decide +kernel)
private def b33 : PaidBatch .empty 4 := packedBatch [1563645,72591658694972010021379582,75524508394880487189012478,78501297091148932854243838,81521250233629492143940606,84583593272174306963744254] (by decide +kernel)
private def b34 : PaidBatch .empty 4 := packedBatch [87687551656635522440521726,90832350836865280479914494,94017216262715726225566718] (by decide +kernel)
private def batches : List (PaidBatch .empty 4) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 127 12 7 = true := by decide +kernel
private theorem i19 : checks tiles 127 19 7 = true := by decide +kernel
private theorem i26 : checks tiles 127 26 7 = true := by decide +kernel
private theorem i33 : checks tiles 127 33 7 = true := by decide +kernel
private theorem i40 : checks tiles 127 40 7 = true := by decide +kernel
private theorem i47 : checks tiles 127 47 7 = true := by decide +kernel
def receipt : Certificate .empty 4 := ⟨batches, checks_join i12 (checks_join i19 (checks_join i26 (checks_join i33 (checks_join i40 i47))))⟩
end Top4


end Low52At2390PriceTableEmpty1
