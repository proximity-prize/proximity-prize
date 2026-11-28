import ProximityPrize.SubmissionLower.Bundle6970_dc5ee4516d21157a
import ProximityPrize.SubmissionLower.Bundle6970_615e81449197b637

section Pack_Z6970PlateauChunkedBatch000

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range0To2 : chunk 0 2 = 2595329426944 :=
  join_chunk (f := 0) (a := 1) (b := 1) (u := 1299598582628) (v := 1295730844316) oneChunk0 oneChunk1

theorem range3To5 : chunk 3 2 = 2572182344854 :=
  join_chunk (f := 3) (a := 1) (b := 1) (u := 1288015161678) (v := 1284167183176) oneChunk3 oneChunk4

theorem range2To5 : chunk 2 3 = 3864051254178 :=
  join_chunk (f := 2) (a := 1) (b := 2) (u := 1291868909324) (v := 2572182344854) oneChunk2 range3To5

theorem range0To5 : chunk 0 5 = 6459380681122 :=
  join_chunk (f := 0) (a := 2) (b := 3) (u := 2595329426944) (v := 3864051254178) range0To2 range2To5

theorem range5To7 : chunk 5 2 = 2556820626486 :=
  join_chunk (f := 5) (a := 1) (b := 1) (u := 1280327358320) (v := 1276493268166) oneChunk5 oneChunk6

theorem range8To10 : chunk 8 2 = 2533881869572 :=
  join_chunk (f := 8) (a := 1) (b := 1) (u := 1268847027256) (v := 1265034842316) oneChunk8 oneChunk9

theorem range7To10 : chunk 7 3 = 3806549167288 :=
  join_chunk (f := 7) (a := 1) (b := 2) (u := 1272667297716) (v := 2533881869572) oneChunk7 range8To10

theorem range5To10 : chunk 5 5 = 6363369793774 :=
  join_chunk (f := 5) (a := 2) (b := 3) (u := 2556820626486) (v := 3806549167288) range5To7 range7To10

theorem range0To10 : chunk 0 10 = 12822750474896 :=
  join_chunk (f := 0) (a := 5) (b := 5) (u := 6459380681122) (v := 6363369793774) range0To5 range5To10

theorem range10To12 : chunk 10 2 = 2518658175942 :=
  join_chunk (f := 10) (a := 1) (b := 1) (u := 1261228322388) (v := 1257429853554) oneChunk10 oneChunk11

theorem range13To15 : chunk 13 2 = 2495925155294 :=
  join_chunk (f := 13) (a := 1) (b := 1) (u := 1249852191842) (v := 1246072963452) oneChunk13 oneChunk14

theorem range12To15 : chunk 12 3 = 3749562169780 :=
  join_chunk (f := 12) (a := 1) (b := 2) (u := 1253637014486) (v := 2495925155294) oneChunk12 range13To15

theorem range10To15 : chunk 10 5 = 6268220345722 :=
  join_chunk (f := 10) (a := 2) (b := 3) (u := 2518658175942) (v := 3749562169780) range10To12 range12To15

theorem range15To17 : chunk 15 2 = 2480837744744 :=
  join_chunk (f := 15) (a := 1) (b := 1) (u := 1242301716574) (v := 1238536028170) oneChunk15 oneChunk16

theorem range18To20 : chunk 18 2 = 2458307824350 :=
  join_chunk (f := 18) (a := 1) (b := 1) (u := 1231026066504) (v := 1227281757846) oneChunk18 oneChunk19

theorem range17To20 : chunk 17 3 = 3693086110474 :=
  join_chunk (f := 17) (a := 1) (b := 2) (u := 1234778286124) (v := 2458307824350) oneChunk17 range18To20

theorem range15To20 : chunk 15 5 = 6173923855218 :=
  join_chunk (f := 15) (a := 2) (b := 3) (u := 2480837744744) (v := 3693086110474) range15To17 range17To20

theorem range10To20 : chunk 10 10 = 12442144200940 :=
  join_chunk (f := 10) (a := 5) (b := 5) (u := 6268220345722) (v := 6173923855218) range10To15 range15To20

theorem range0To20 : chunk 0 20 = 25264894675836 :=
  join_chunk (f := 0) (a := 10) (b := 10) (u := 12822750474896) (v := 12442144200940) range0To10 range10To20

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch000

section Pack_Z6970PlateauChunkedBatch020

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range20To22 : chunk 20 2 = 2443354923372 :=
  join_chunk (f := 20) (a := 1) (b := 1) (u := 1223542935298) (v := 1219811988074) oneChunk20 oneChunk21

theorem range23To25 : chunk 23 2 = 2421025418672 :=
  join_chunk (f := 23) (a := 1) (b := 1) (u := 1212368832124) (v := 1208656586548) oneChunk23 oneChunk24

theorem range22To25 : chunk 22 3 = 3637111909050 :=
  join_chunk (f := 22) (a := 1) (b := 2) (u := 1216086490378) (v := 2421025418672) oneChunk22 range23To25

theorem range20To25 : chunk 20 5 = 6080466832422 :=
  join_chunk (f := 20) (a := 2) (b := 3) (u := 2443354923372) (v := 3637111909050) range20To22 range22To25

theorem range25To27 : chunk 25 2 = 2406205221884 :=
  join_chunk (f := 25) (a := 1) (b := 1) (u := 1204952144290) (v := 1201253077594) oneChunk25 oneChunk26

theorem range28To30 : chunk 28 2 = 2384073401340 :=
  join_chunk (f := 28) (a := 1) (b := 1) (u := 1193875816282) (v := 1190197585058) oneChunk28 oneChunk29

theorem range27To30 : chunk 27 3 = 3581635179190 :=
  join_chunk (f := 27) (a := 1) (b := 2) (u := 1197561777850) (v := 2384073401340) oneChunk27 range28To30

theorem range25To30 : chunk 25 5 = 5987840401074 :=
  join_chunk (f := 25) (a := 2) (b := 3) (u := 2406205221884) (v := 3581635179190) range25To27 range27To30

theorem range20To30 : chunk 20 10 = 12068307233496 :=
  join_chunk (f := 20) (a := 5) (b := 5) (u := 6080466832422) (v := 5987840401074) range20To25 range25To30

theorem range30To32 : chunk 30 2 = 2369384071510 :=
  join_chunk (f := 30) (a := 1) (b := 1) (u := 1186524654358) (v := 1182859417152) oneChunk30 oneChunk31

theorem range33To35 : chunk 33 2 = 2347447154912 :=
  join_chunk (f := 33) (a := 1) (b := 1) (u := 1175547124348) (v := 1171900030564) oneChunk33 oneChunk34

theorem range32To35 : chunk 32 3 = 3526646597462 :=
  join_chunk (f := 32) (a := 1) (b := 2) (u := 1179199442550) (v := 2347447154912) oneChunk32 range33To35

theorem range30To35 : chunk 30 5 = 5896030668972 :=
  join_chunk (f := 30) (a := 2) (b := 3) (u := 2369384071510) (v := 3526646597462) range30To32 range32To35

theorem range35To37 : chunk 35 2 = 2332886822932 :=
  join_chunk (f := 35) (a := 1) (b := 1) (u := 1168260555844) (v := 1164626267088) oneChunk35 oneChunk36

theorem range38To40 : chunk 38 2 = 2311141983218 :=
  join_chunk (f := 38) (a := 1) (b := 1) (u := 1157377999790) (v := 1153763983428) oneChunk38 oneChunk39

theorem range37To40 : chunk 37 3 = 3472141543036 :=
  join_chunk (f := 37) (a := 1) (b := 2) (u := 1160999559818) (v := 2311141983218) oneChunk37 range38To40

theorem range35To40 : chunk 35 5 = 5805028365968 :=
  join_chunk (f := 35) (a := 2) (b := 3) (u := 2332886822932) (v := 3472141543036) range35To37 range37To40

theorem range30To40 : chunk 30 10 = 11701059034940 :=
  join_chunk (f := 30) (a := 5) (b := 5) (u := 5896030668972) (v := 5805028365968) range30To35 range35To40

theorem range20To40 : chunk 20 20 = 23769366268436 :=
  join_chunk (f := 20) (a := 10) (b := 10) (u := 12068307233496) (v := 11701059034940) range20To30 range30To40

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch020
