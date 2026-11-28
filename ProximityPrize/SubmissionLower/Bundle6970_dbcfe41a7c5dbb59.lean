import ProximityPrize.SubmissionLower.Bundle6970_615e81449197b637
import ProximityPrize.SubmissionLower.Bundle6970_885d50e662cbb4eb

section Pack_Z6970PlateauChunkedBatch040

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range40To42 : chunk 40 2 = 2296708748130 :=
  join_chunk (f := 40) (a := 1) (b := 1) (u := 1150155075318) (v := 1146553672812) oneChunk40 oneChunk41

theorem range43To45 : chunk 43 2 = 2275153109440 :=
  join_chunk (f := 43) (a := 1) (b := 1) (u := 1139368473090) (v := 1135784636350) oneChunk43 oneChunk44

theorem range42To45 : chunk 42 3 = 3418110448742 :=
  join_chunk (f := 42) (a := 1) (b := 2) (u := 1142957339302) (v := 2275153109440) oneChunk42 range43To45

theorem range40To45 : chunk 40 5 = 5714819196872 :=
  join_chunk (f := 40) (a := 2) (b := 3) (u := 2296708748130) (v := 3418110448742) range40To42 range42To45

theorem range45To47 : chunk 45 2 = 2260845038412 :=
  join_chunk (f := 45) (a := 1) (b := 1) (u := 1132208228360) (v := 1128636810052) oneChunk45 oneChunk46

theorem range48To50 : chunk 48 2 = 2239475678158 :=
  join_chunk (f := 48) (a := 1) (b := 1) (u := 1121513702978) (v := 1117961975180) oneChunk48 oneChunk49

theorem range47To50 : chunk 47 3 = 3364548459862 :=
  join_chunk (f := 47) (a := 1) (b := 2) (u := 1125072781704) (v := 2239475678158) oneChunk47 range48To50

theorem range45To50 : chunk 45 5 = 5625393498274 :=
  join_chunk (f := 45) (a := 2) (b := 3) (u := 2260845038412) (v := 3364548459862) range45To47 range47To50

theorem range40To50 : chunk 40 10 = 11340212695146 :=
  join_chunk (f := 40) (a := 5) (b := 5) (u := 5714819196872) (v := 5625393498274) range40To45 range45To50

theorem range50To52 : chunk 50 2 = 2225290806508 :=
  join_chunk (f := 50) (a := 1) (b := 1) (u := 1114415156678) (v := 1110875649830) oneChunk50 oneChunk51

theorem range53To55 : chunk 53 2 = 2204104753180 :=
  join_chunk (f := 53) (a := 1) (b := 1) (u := 1103813645674) (v := 1100291107506) oneChunk53 oneChunk54

theorem range52To55 : chunk 52 3 = 3311445764864 :=
  join_chunk (f := 52) (a := 1) (b := 2) (u := 1107341011684) (v := 2204104753180) oneChunk52 range53To55

theorem range50To55 : chunk 50 5 = 5536736571372 :=
  join_chunk (f := 50) (a := 2) (b := 3) (u := 2225290806508) (v := 3311445764864) range50To52 range52To55

theorem range55To57 : chunk 55 2 = 2190041084350 :=
  join_chunk (f := 55) (a := 1) (b := 1) (u := 1096775801714) (v := 1093265282636) oneChunk55 oneChunk56

theorem range58To60 : chunk 58 2 = 2169035319836 :=
  join_chunk (f := 58) (a := 1) (b := 1) (u := 1086263374546) (v := 1082771945290) oneChunk58 oneChunk59

theorem range57To60 : chunk 57 3 = 3258797275768 :=
  join_chunk (f := 57) (a := 1) (b := 2) (u := 1089761955932) (v := 2169035319836) oneChunk57 range58To60

theorem range55To60 : chunk 55 5 = 5448838360118 :=
  join_chunk (f := 55) (a := 2) (b := 3) (u := 2190041084350) (v := 3258797275768) range55To57 range57To60

theorem range50To60 : chunk 50 10 = 10985574931490 :=
  join_chunk (f := 50) (a := 5) (b := 5) (u := 5536736571372) (v := 5448838360118) range50To55 range55To60

theorem range40To60 : chunk 40 20 = 22325787626636 :=
  join_chunk (f := 40) (a := 10) (b := 10) (u := 11340212695146) (v := 10985574931490) range40To50 range50To60

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch040

section Pack_Z6970PlateauChunkedBatch060

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range60To62 : chunk 60 2 = 2155090825418 :=
  join_chunk (f := 60) (a := 1) (b := 1) (u := 1079285219688) (v := 1075805605730) oneChunk60 oneChunk61

theorem range63To65 : chunk 63 2 = 2134262282558 :=
  join_chunk (f := 63) (a := 1) (b := 1) (u := 1068862772176) (v := 1065399510382) oneChunk63 oneChunk64

theorem range62To65 : chunk 62 3 = 3206592936054 :=
  join_chunk (f := 62) (a := 1) (b := 2) (u := 1072330653496) (v := 2134262282558) oneChunk62 range63To65

theorem range60To65 : chunk 60 5 = 5361683761472 :=
  join_chunk (f := 60) (a := 2) (b := 3) (u := 2155090825418) (v := 3206592936054) range60To62 range62To65

theorem range65To67 : chunk 65 2 = 2120434902270 :=
  join_chunk (f := 65) (a := 1) (b := 1) (u := 1061943278530) (v := 1058491623740) oneChunk65 oneChunk66

theorem range68To70 : chunk 68 2 = 2099780467426 :=
  join_chunk (f := 68) (a := 1) (b := 1) (u := 1051606825944) (v := 1048173641482) oneChunk68 oneChunk69

theorem range67To70 : chunk 67 3 = 3154827425104 :=
  join_chunk (f := 67) (a := 1) (b := 2) (u := 1055046957678) (v := 2099780467426) oneChunk67 range68To70

theorem range65To70 : chunk 65 5 = 5275262327374 :=
  join_chunk (f := 65) (a := 2) (b := 3) (u := 2120434902270) (v := 3154827425104) range65To67 range67To70

theorem range60To70 : chunk 60 10 = 10636946088846 :=
  join_chunk (f := 60) (a := 5) (b := 5) (u := 5361683761472) (v := 5275262327374) range60To65 range65To70

theorem range70To72 : chunk 70 2 = 2086068109136 :=
  join_chunk (f := 70) (a := 1) (b := 1) (u := 1044744948348) (v := 1041323160788) oneChunk70 oneChunk71

theorem range73To75 : chunk 73 2 = 2065584619498 :=
  join_chunk (f := 73) (a := 1) (b := 1) (u := 1034495345420) (v := 1031089274078) oneChunk73 oneChunk74

theorem range72To75 : chunk 72 3 = 3103490440786 :=
  join_chunk (f := 72) (a := 1) (b := 2) (u := 1037905821288) (v := 2065584619498) oneChunk72 range73To75

theorem range70To75 : chunk 70 5 = 5189558549922 :=
  join_chunk (f := 70) (a := 2) (b := 3) (u := 2086068109136) (v := 3103490440786) range70To72 range72To75

theorem range75To77 : chunk 75 2 = 2051985159198 :=
  join_chunk (f := 75) (a := 1) (b := 1) (u := 1027690024184) (v := 1024295135014) oneChunk75 oneChunk76

theorem range78To80 : chunk 78 2 = 2031669405604 :=
  join_chunk (f := 78) (a := 1) (b := 1) (u := 1017523231372) (v := 1014146174232) oneChunk78 oneChunk79

theorem range77To80 : chunk 77 3 = 3052576430470 :=
  join_chunk (f := 77) (a := 1) (b := 2) (u := 1020907024866) (v := 2031669405604) oneChunk77 range78To80

theorem range75To80 : chunk 75 5 = 5104561589668 :=
  join_chunk (f := 75) (a := 2) (b := 3) (u := 2051985159198) (v := 3052576430470) range75To77 range77To80

theorem range70To80 : chunk 70 10 = 10294120139590 :=
  join_chunk (f := 70) (a := 5) (b := 5) (u := 5189558549922) (v := 5104561589668) range70To75 range75To80

theorem range60To80 : chunk 60 20 = 20931066228436 :=
  join_chunk (f := 60) (a := 10) (b := 10) (u := 10636946088846) (v := 10294120139590) range60To70 range70To80

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch060
