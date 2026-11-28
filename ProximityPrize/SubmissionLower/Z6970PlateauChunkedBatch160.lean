import ProximityPrize.SubmissionLower.Bundle6970_6a90077dc296d543
import ProximityPrize.SubmissionLower.Bundle6970_6a90077dc296d543
import ProximityPrize.SubmissionLower.Bundle6970_6a90077dc296d543
import ProximityPrize.SubmissionLower.Bundle6970_6a90077dc296d543

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range160To162 : chunk 160 2 = 1511029560950 :=
  join_chunk (f := 160) (a := 1) (b := 1) (u := 757009653608) (v := 754019907342) oneChunk160 oneChunk161

theorem range163To165 : chunk 163 2 = 1493124489992 :=
  join_chunk (f := 163) (a := 1) (b := 1) (u := 748051556548) (v := 745072933444) oneChunk163 oneChunk164

theorem range162To165 : chunk 162 3 = 2244157525148 :=
  join_chunk (f := 162) (a := 1) (b := 2) (u := 751033035156) (v := 1493124489992) oneChunk162 range163To165

theorem range160To165 : chunk 160 5 = 3755187086098 :=
  join_chunk (f := 160) (a := 2) (b := 3) (u := 1511029560950) (v := 2244157525148) range160To162 range162To165

theorem range165To167 : chunk 165 2 = 1481228969232 :=
  join_chunk (f := 165) (a := 1) (b := 1) (u := 742099688330) (v := 739129280902) oneChunk165 oneChunk166

theorem range168To170 : chunk 168 2 = 1463447151610 :=
  join_chunk (f := 168) (a := 1) (b := 1) (u := 733202013036) (v := 730245138574) oneChunk168 oneChunk169

theorem range167To170 : chunk 167 3 = 2199611388268 :=
  join_chunk (f := 167) (a := 1) (b := 2) (u := 736164236658) (v := 1463447151610) oneChunk167 range168To170

theorem range165To170 : chunk 165 5 = 3680840357500 :=
  join_chunk (f := 165) (a := 2) (b := 3) (u := 1481228969232) (v := 2199611388268) range165To167 range167To170

theorem range160To170 : chunk 160 10 = 7436027443598 :=
  join_chunk (f := 160) (a := 5) (b := 5) (u := 3755187086098) (v := 3680840357500) range160To165 range165To170

theorem range170To172 : chunk 170 2 = 1451633402628 :=
  join_chunk (f := 170) (a := 1) (b := 1) (u := 727291068428) (v := 724342334200) oneChunk170 oneChunk171

theorem range173To175 : chunk 173 2 = 1433973685432 :=
  join_chunk (f := 173) (a := 1) (b := 1) (u := 718455766732) (v := 715517918700) oneChunk173 oneChunk174

theorem range172To175 : chunk 172 3 = 2155370074170 :=
  join_chunk (f := 172) (a := 1) (b := 2) (u := 721396388738) (v := 1433973685432) oneChunk172 range173To175

theorem range170To175 : chunk 170 5 = 3607003476798 :=
  join_chunk (f := 170) (a := 2) (b := 3) (u := 1451633402628) (v := 2155370074170) range170To172 range172To175

theorem range175To177 : chunk 175 2 = 1422240988570 :=
  join_chunk (f := 175) (a := 1) (b := 1) (u := 712585382444) (v := 709655606126) oneChunk175 oneChunk176

theorem range178To180 : chunk 178 2 = 1404702365788 :=
  join_chunk (f := 178) (a := 1) (b := 1) (u := 703809401904) (v := 700892963884) oneChunk178 oneChunk179

theorem range177To180 : chunk 177 3 = 2111433496474 :=
  join_chunk (f := 177) (a := 1) (b := 2) (u := 706731130686) (v := 1404702365788) oneChunk177 range178To180

theorem range175To180 : chunk 175 5 = 3533674485044 :=
  join_chunk (f := 175) (a := 2) (b := 3) (u := 1422240988570) (v := 2111433496474) range175To177 range177To180

theorem range170To180 : chunk 170 10 = 7140677961842 :=
  join_chunk (f := 170) (a := 5) (b := 5) (u := 3607003476798) (v := 3533674485044) range170To175 range175To180

theorem range160To180 : chunk 160 20 = 14576705405440 :=
  join_chunk (f := 160) (a := 10) (b := 10) (u := 7436027443598) (v := 7140677961842) range160To170 range170To180

end ExpandedPlateauSum6970
