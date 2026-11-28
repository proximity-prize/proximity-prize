import ProximityPrize.SubmissionLower.Bundle6970_f11240a2c578bb4b
import ProximityPrize.SubmissionLower.Bundle6970_6a90077dc296d543

section Pack_Z6970PlateauChunkedBatch120

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range120To122 : chunk 120 2 = 1757119033564 :=
  join_chunk (f := 120) (a := 1) (b := 1) (u := 880141838078) (v := 876977195486) oneChunk120 oneChunk121

theorem range123To125 : chunk 123 2 = 1738169179606 :=
  join_chunk (f := 123) (a := 1) (b := 1) (u := 870660588736) (v := 867508590870) oneChunk123 oneChunk124

theorem range122To125 : chunk 122 3 = 2611985136984 :=
  join_chunk (f := 122) (a := 1) (b := 2) (u := 873815957378) (v := 1738169179606) oneChunk122 range123To125

theorem range120To125 : chunk 120 5 = 4369104170548 :=
  join_chunk (f := 120) (a := 2) (b := 3) (u := 1757119033564) (v := 2611985136984) range120To122 range122To125

theorem range125To127 : chunk 125 2 = 1725582040706 :=
  join_chunk (f := 125) (a := 1) (b := 1) (u := 864362431250) (v := 861219609456) oneChunk125 oneChunk126

theorem range128To130 : chunk 128 2 = 1706769844024 :=
  join_chunk (f := 128) (a := 1) (b := 1) (u := 854948887114) (v := 851820956910) oneChunk128 oneChunk129

theorem range127To130 : chunk 127 3 = 2564852439494 :=
  join_chunk (f := 127) (a := 1) (b := 2) (u := 858082595470) (v := 1706769844024) oneChunk127 range128To130

theorem range125To130 : chunk 125 5 = 4290434480200 :=
  join_chunk (f := 125) (a := 2) (b := 3) (u := 1725582040706) (v := 2564852439494) range125To127 range127To130

theorem range120To130 : chunk 120 10 = 8659538650748 :=
  join_chunk (f := 120) (a := 5) (b := 5) (u := 4369104170548) (v := 4290434480200) range120To125 range125To130

theorem range130To132 : chunk 130 2 = 1694273695062 :=
  join_chunk (f := 130) (a := 1) (b := 1) (u := 848696300898) (v := 845577394164) oneChunk130 oneChunk131

theorem range133To135 : chunk 133 2 = 1675596849346 :=
  join_chunk (f := 133) (a := 1) (b := 1) (u := 839351788900) (v := 836245060446) oneChunk133 oneChunk134

theorem range132To135 : chunk 132 3 = 2518058580286 :=
  join_chunk (f := 132) (a := 1) (b := 2) (u := 842461730940) (v := 1675596849346) oneChunk132 range133To135

theorem range130To135 : chunk 130 5 = 4212332275348 :=
  join_chunk (f := 130) (a := 2) (b := 3) (u := 1694273695062) (v := 2518058580286) range130To132 range132To135

theorem range135To137 : chunk 135 2 = 1663190201564 :=
  join_chunk (f := 135) (a := 1) (b := 1) (u := 833144025864) (v := 830046175700) oneChunk135 oneChunk136

theorem range138To140 : chunk 138 2 = 1644646546902 :=
  join_chunk (f := 138) (a := 1) (b := 1) (u := 823864966062) (v := 820781580840) oneChunk138 oneChunk139

theorem range137To140 : chunk 137 3 = 2471600539780 :=
  join_chunk (f := 137) (a := 1) (b := 2) (u := 826953992878) (v := 1644646546902) oneChunk137 range138To140

theorem range135To140 : chunk 135 5 = 4134790741344 :=
  join_chunk (f := 135) (a := 2) (b := 3) (u := 1663190201564) (v := 2471600539780) range135To137 range137To140

theorem range130To140 : chunk 130 10 = 8347123016692 :=
  join_chunk (f := 130) (a := 5) (b := 5) (u := 4212332275348) (v := 4134790741344) range130To135 range135To140

theorem range120To140 : chunk 120 20 = 17006661667440 :=
  join_chunk (f := 120) (a := 10) (b := 10) (u := 8659538650748) (v := 8347123016692) range120To130 range130To140

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch120

section Pack_Z6970PlateauChunkedBatch140

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range140To142 : chunk 140 2 = 1632328007692 :=
  join_chunk (f := 140) (a := 1) (b := 1) (u := 817701323968) (v := 814626683724) oneChunk140 oneChunk141

theorem range143To145 : chunk 143 2 = 1613915526124 :=
  join_chunk (f := 143) (a := 1) (b := 1) (u := 808489198582) (v := 805426327542) oneChunk143 oneChunk144

theorem range142To145 : chunk 142 3 = 2425470671056 :=
  join_chunk (f := 142) (a := 1) (b := 2) (u := 811555144932) (v := 1613915526124) oneChunk142 range143To145

theorem range140To145 : chunk 140 5 = 4057798678748 :=
  join_chunk (f := 140) (a := 2) (b := 3) (u := 1632328007692) (v := 2425470671056) range140To142 range142To145

theorem range145To147 : chunk 145 2 = 1601683799004 :=
  join_chunk (f := 145) (a := 1) (b := 1) (u := 802369025540) (v := 799314773464) oneChunk145 oneChunk146

theorem range148To150 : chunk 148 2 = 1583400619092 :=
  join_chunk (f := 148) (a := 1) (b := 1) (u := 793220387440) (v := 790180231652) oneChunk148 oneChunk149

theorem range147To150 : chunk 147 3 = 2379666686896 :=
  join_chunk (f := 147) (a := 1) (b := 2) (u := 796266067804) (v := 1583400619092) oneChunk147 range148To150

theorem range145To150 : chunk 145 5 = 3981350485900 :=
  join_chunk (f := 145) (a := 2) (b := 3) (u := 1601683799004) (v := 2379666686896) range145To147 range147To150

theorem range140To150 : chunk 140 10 = 8039149164648 :=
  join_chunk (f := 140) (a := 5) (b := 5) (u := 4057798678748) (v := 3981350485900) range140To145 range145To150

theorem range150To152 : chunk 150 2 = 1571254503730 :=
  join_chunk (f := 150) (a := 1) (b := 1) (u := 787143077288) (v := 784111426442) oneChunk150 oneChunk151

theorem range153To155 : chunk 153 2 = 1553098895864 :=
  join_chunk (f := 153) (a := 1) (b := 1) (u := 778059564606) (v := 775039331258) oneChunk153 oneChunk154

theorem range152To155 : chunk 152 3 = 2334181649768 :=
  join_chunk (f := 152) (a := 1) (b := 2) (u := 781082753904) (v := 1553098895864) oneChunk152 range153To155

theorem range150To155 : chunk 150 5 = 3905436153498 :=
  join_chunk (f := 150) (a := 2) (b := 3) (u := 1571254503730) (v := 2334181649768) range150To152 range152To155

theorem range155To157 : chunk 155 2 = 1541037288052 :=
  join_chunk (f := 155) (a := 1) (b := 1) (u := 772024561654) (v := 769012726398) oneChunk155 oneChunk156

theorem range158To160 : chunk 158 2 = 1523007669270 :=
  join_chunk (f := 158) (a := 1) (b := 1) (u := 763002859448) (v := 760004809822) oneChunk158 oneChunk159

theorem range157To160 : chunk 157 3 = 2289014005442 :=
  join_chunk (f := 157) (a := 1) (b := 2) (u := 766006336172) (v := 1523007669270) oneChunk157 range158To160

theorem range155To160 : chunk 155 5 = 3830051293494 :=
  join_chunk (f := 155) (a := 2) (b := 3) (u := 1541037288052) (v := 2289014005442) range155To157 range157To160

theorem range150To160 : chunk 150 10 = 7735487446992 :=
  join_chunk (f := 150) (a := 5) (b := 5) (u := 3905436153498) (v := 3830051293494) range150To155 range155To160

theorem range140To160 : chunk 140 20 = 15774636611640 :=
  join_chunk (f := 140) (a := 10) (b := 10) (u := 8039149164648) (v := 7735487446992) range140To150 range150To160

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch140
