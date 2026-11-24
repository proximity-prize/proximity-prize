import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass0

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def priceBatch0 : P :=
  ⟨unpack [2348878853, 738267145, 402723849, 268507145, 184622093, 134291469], by decide +kernel⟩
private def priceBatch1 : P :=
  ⟨unpack [570696717, 1158227985, 1040788497, 940126225, 839463957, 772356117], by decide +kernel⟩
private def priceBatch2 : P :=
  ⟨unpack [722025493, 654917657, 621364249, 587810841, 537480221, 503926813], by decide +kernel⟩
private def priceBatch3 : P :=
  ⟨unpack [487150621, 453597217, 436821025, 1663131681, 1579246629, 1528916005], by decide +kernel⟩
private def priceBatch4 : P :=
  ⟨unpack [1461808165, 1411477545, 1361146921, 1310816297, 1260485677, 1226932269], by decide +kernel⟩
private def priceBatch5 : P :=
  ⟨unpack [1193378861, 1100568797235, 1143048241, 1126272049, 1092718641, 1059165237], by decide +kernel⟩
private def priceBatch6 : P :=
  ⟨unpack [1042389045, 1008835637, 975282233, 958506041, 941729849, 1099813690431], by decide +kernel⟩
private def priceBatch7 : P :=
  ⟨unpack [908176445, 908177469, 891401277, 857847873, 841071681, 1059766337], by decide +kernel⟩
private def priceBatch8 : P :=
  ⟨unpack [1026212933, 1026213957, 1009437765, 975884361, 975885385, 975951945], by decide +kernel⟩
private def priceBatch9 : P :=
  ⟨unpack [1099998238799, 959175757, 942399565, 1227613261, 1177282641, 1143729233], by decide +kernel⟩
private def priceBatch10 : P :=
  ⟨unpack [1711477869, 889461897, 1101291871375, 1101275093139, 1101258314903, 1728849049], by decide +kernel⟩
private def priceBatch11 : P :=
  ⟨unpack [1101241536667, 1101207981219, 1662797993, 1100837831859, 1101022380219, 18757718205], by decide +kernel⟩
private def priceBatch12 : P :=
  ⟨unpack [1101055933639, 1101005600979, 1100938491107, 1100854604023, 1242311949, 1100436913423], by decide +kernel⟩
private def priceBatch13 : P :=
  ⟨unpack [1100470466835, 1100504020247, 1100587904283, 1100537573659, 1100621457695, 1100671788323], by decide +kernel⟩
private def priceBatch14 : P :=
  ⟨unpack [1100655010087, 5419837737, 1100638231851, 1100604676403, 1100286320947, 1100587898167], by decide +kernel⟩
private def priceBatch15 : P :=
  ⟨unpack [1100319740215, 1100319806775, 1100286253367, 1100303097143, 1100571119931, 1100370136379], by decide +kernel⟩
private def priceBatch16 : P :=
  ⟨unpack [1100437243199, 1100403689791, 1100537564483, 1100470796611, 1100520786247, 1100487230799], by decide +kernel⟩
private def priceBatch17 : P :=
  ⟨unpack [1100453675351, 1100419792223, 1100386236775, 1100202437991, 1100219214191, 1100335904115], by decide +kernel⟩
private def priceBatch18 : P :=
  ⟨unpack [1100235990391, 1100285571455, 1100252016007, 673278357, 4917912993, 9145770417], by decide +kernel⟩
private def priceBatch19 : P :=
  ⟨unpack [1099816549871, 1099665564143, 1099797644787, 1099715893747, 1099665563127, 1099766151675], by decide +kernel⟩
private def priceBatch20 : P :=
  ⟨unpack [1099766223355, 1099732669947, 1099715819015, 1099699113483, 1099531415055, 1099665486355], by decide +kernel⟩
private def priceBatch21 : P :=
  ⟨unpack [1099648780823, 1099531346455, 183275993953543829437935126, 1099531414043, 184972729892983339343539738, 1099615153695], by decide +kernel⟩
private def priceBatch22 : P :=
  ⟨unpack [1099615225375, 1099548122655, 169911684115523220607394334, 186669465832422849249144350, 171435468152022749999325730, 182664930234780389039008290], by decide +kernel⟩
private def priceBatch23 : P :=
  ⟨unpack [188366201771862359154748962, 1099579540007, 1099548121639, 172959252188522279391257126, 1099548190247, 184302982991440177380846118], by decide +kernel⟩
private def priceBatch24 : P :=
  ⟨unpack [190062937711301869060353574, 1099564821035, 1099564892715, 168846772249984249331768874, 174483036225021808783188522, 185941035748099965655575082], by decide +kernel⟩
private def priceBatch25 : P :=
  ⟨unpack [191759673650741378965958186, 170314970749103241337560622, 176006820261521338175185454, 187579088504759753997412910, 193456409590180888871562798, 1099531343411], by decide +kernel⟩
private def priceBatch26 : P :=
  ⟨unpack [2939440, 171783169248222233343352370, 177530604298020867567116850, 183342444576653167928665650, 189217141261419542339250738, 195153145529620398710058546], by decide +kernel⟩
private def priceBatch27 : P :=
  ⟨unpack [167515333760161706691844662, 173251367747341225349144118, 179054388334520396959048246, 184922846698999629432612406, 190855194018079330681088566, 196849881469059908615663158], by decide +kernel⟩
private def batches : List P := [priceBatch0, priceBatch1, priceBatch2, priceBatch3, priceBatch4, priceBatch5, priceBatch6, priceBatch7, priceBatch8, priceBatch9, priceBatch10, priceBatch11, priceBatch12, priceBatch13, priceBatch14, priceBatch15, priceBatch16, priceBatch17, priceBatch18, priceBatch19, priceBatch20, priceBatch21, priceBatch22, priceBatch23, priceBatch24, priceBatch25, priceBatch26, priceBatch27]
private theorem i3 : checks (tilesOf batches) 141 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 141 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 141 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 141 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 141 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 141 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 141 51 8 = true := by
  decide +kernel
private theorem i59 : checks (tilesOf batches) 141 59 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤141) (hj : a.j≤59) :
    Covered orders a ∨ Low6960Gate.Gated ((0 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (checks_join i51 (i59)))))))) a ha ht hb hj
end Top1

end Low6960Allocation.Group0
