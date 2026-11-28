import ProximityPrize.SubmissionLower.Bundle6970_885d50e662cbb4eb
import ProximityPrize.SubmissionLower.Bundle6970_62eb21ad8feecd27

section Pack_Z6970PlateauChunkedBatch080

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range80To82 : chunk 80 2 = 2018180687436 :=
  join_chunk (f := 80) (a := 1) (b := 1) (u := 1010773389408) (v := 1007407298028) oneChunk80 oneChunk81

theorem range83To85 : chunk 83 2 = 1998029411426 :=
  join_chunk (f := 83) (a := 1) (b := 1) (u := 1000690220982) (v := 997339190444) oneChunk83 oneChunk84

theorem range82To85 : chunk 82 3 = 3002074845786 :=
  join_chunk (f := 82) (a := 1) (b := 2) (u := 1004045434360) (v := 1998029411426) oneChunk82 range83To85

theorem range80To85 : chunk 80 5 = 5020255533222 :=
  join_chunk (f := 80) (a := 2) (b := 3) (u := 2018180687436) (v := 3002074845786) range80To82 range82To85

theorem range85To87 : chunk 85 2 = 1984649247658 :=
  join_chunk (f := 85) (a := 1) (b := 1) (u := 993994766800) (v := 990654480858) oneChunk85 oneChunk86

theorem range88To90 : chunk 88 2 = 1964659144544 :=
  join_chunk (f := 88) (a := 1) (b := 1) (u := 983991127780) (v := 980668016764) oneChunk88 oneChunk89

theorem range87To90 : chunk 87 3 = 2951979902716 :=
  join_chunk (f := 87) (a := 1) (b := 2) (u := 987320758172) (v := 1964659144544) oneChunk87 range88To90

theorem range85To90 : chunk 85 5 = 4936629150374 :=
  join_chunk (f := 85) (a := 2) (b := 3) (u := 1984649247658) (v := 2951979902716) range85To87 range87To90

theorem range80To90 : chunk 80 10 = 9956884683596 :=
  join_chunk (f := 80) (a := 5) (b := 5) (u := 5020255533222) (v := 4936629150374) range80To85 range85To90

theorem range90To92 : chunk 90 2 = 1951385315616 :=
  join_chunk (f := 90) (a := 1) (b := 1) (u := 977348952368) (v := 974036363248) oneChunk90 oneChunk91

theorem range93To95 : chunk 93 2 = 1931553035860 :=
  join_chunk (f := 93) (a := 1) (b := 1) (u := 967425618348) (v := 964127417512) oneChunk93 oneChunk94

theorem range92To95 : chunk 92 3 = 2902280810882 :=
  join_chunk (f := 92) (a := 1) (b := 2) (u := 970727775022) (v := 1931553035860) oneChunk92 range93To95

theorem range90To95 : chunk 90 5 = 4853666126498 :=
  join_chunk (f := 90) (a := 2) (b := 3) (u := 1951385315616) (v := 2902280810882) range90To92 range92To95

theorem range95To97 : chunk 95 2 = 1918383309878 :=
  join_chunk (f := 95) (a := 1) (b := 1) (u := 960835605284) (v := 957547704594) oneChunk95 oneChunk96

theorem range98To100 : chunk 98 2 = 1898705547016 :=
  join_chunk (f := 98) (a := 1) (b := 1) (u := 950988464100) (v := 947717082916) oneChunk98 oneChunk99

theorem range97To100 : chunk 97 3 = 2852971697366 :=
  join_chunk (f := 97) (a := 1) (b := 2) (u := 954266150350) (v := 1898705547016) oneChunk97 range98To100

theorem range95To100 : chunk 95 5 = 4771355007244 :=
  join_chunk (f := 95) (a := 2) (b := 3) (u := 1918383309878) (v := 2852971697366) range95To97 range97To100

theorem range90To100 : chunk 90 10 = 9625021133742 :=
  join_chunk (f := 90) (a := 5) (b := 5) (u := 4853666126498) (v := 4771355007244) range90To95 range95To100

theorem range80To100 : chunk 80 20 = 19581905817338 :=
  join_chunk (f := 80) (a := 10) (b := 10) (u := 9956884683596) (v := 9625021133742) range80To90 range90To100

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch080

section Pack_Z6970PlateauChunkedBatch100

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range100To102 : chunk 100 2 = 1885637762366 :=
  join_chunk (f := 100) (a := 1) (b := 1) (u := 944449526938) (v := 941188235428) oneChunk100 oneChunk101

theorem range103To105 : chunk 103 2 = 1866111345038 :=
  join_chunk (f := 103) (a := 1) (b := 1) (u := 934679443410) (v := 931431901628) oneChunk103 oneChunk104

theorem range102To105 : chunk 102 3 = 2804042072132 :=
  join_chunk (f := 102) (a := 1) (b := 2) (u := 937930727094) (v := 1866111345038) oneChunk102 range103To105

theorem range100To105 : chunk 100 5 = 4689679834498 :=
  join_chunk (f := 100) (a := 2) (b := 3) (u := 1885637762366) (v := 2804042072132) range100To102 range102To105

theorem range105To107 : chunk 105 2 = 1853143436138 :=
  join_chunk (f := 105) (a := 1) (b := 1) (u := 928190545460) (v := 924952890678) oneChunk105 oneChunk106

theorem range108To110 : chunk 108 2 = 1833765339006 :=
  join_chunk (f := 108) (a := 1) (b := 1) (u := 918493537458) (v := 915271801548) oneChunk108 oneChunk109

theorem range107To110 : chunk 107 3 = 2755486722262 :=
  join_chunk (f := 107) (a := 1) (b := 2) (u := 921721383256) (v := 1833765339006) oneChunk107 range108To110

theorem range105To110 : chunk 105 5 = 4608630158400 :=
  join_chunk (f := 105) (a := 2) (b := 3) (u := 1853143436138) (v := 2755486722262) range105To107 range107To110

theorem range100To110 : chunk 100 10 = 9298309992898 :=
  join_chunk (f := 100) (a := 5) (b := 5) (u := 4689679834498) (v := 4608630158400) range100To105 range105To110

theorem range110To112 : chunk 110 2 = 1820895336424 :=
  join_chunk (f := 110) (a := 1) (b := 1) (u := 912053688258) (v := 908841648166) oneChunk110 oneChunk111

theorem range113To115 : chunk 113 2 = 1801662676478 :=
  join_chunk (f := 113) (a := 1) (b := 1) (u := 902430774014) (v := 899231902464) oneChunk113 oneChunk114

theorem range112To115 : chunk 112 3 = 2707295868924 :=
  join_chunk (f := 112) (a := 1) (b := 2) (u := 905633192446) (v := 1801662676478) oneChunk112 range113To115

theorem range110To115 : chunk 110 5 = 4528191205348 :=
  join_chunk (f := 110) (a := 2) (b := 3) (u := 1820895336424) (v := 2707295868924) range110To112 range112To115

theorem range115To117 : chunk 115 2 = 1788888706906 :=
  join_chunk (f := 115) (a := 1) (b := 1) (u := 896039033074) (v := 892849673832) oneChunk115 oneChunk116

theorem range118To120 : chunk 118 2 = 1769798747284 :=
  join_chunk (f := 118) (a := 1) (b := 1) (u := 886486365146) (v := 883312382138) oneChunk118 oneChunk119

theorem range117To120 : chunk 117 3 = 2659465029688 :=
  join_chunk (f := 117) (a := 1) (b := 2) (u := 889666282404) (v := 1769798747284) oneChunk117 range118To120

theorem range115To120 : chunk 115 5 = 4448353736594 :=
  join_chunk (f := 115) (a := 2) (b := 3) (u := 1788888706906) (v := 2659465029688) range115To117 range117To120

theorem range110To120 : chunk 110 10 = 8976544941942 :=
  join_chunk (f := 110) (a := 5) (b := 5) (u := 4528191205348) (v := 4448353736594) range110To115 range115To120

theorem range100To120 : chunk 100 20 = 18274854934840 :=
  join_chunk (f := 100) (a := 10) (b := 10) (u := 9298309992898) (v := 8976544941942) range100To110 range110To120

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch100
