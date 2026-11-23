import ProximityPrize.SubmissionLower.KoalaWeightedReceipt2428
import ProximityPrize.SubmissionLower.KoalaSplitGateWords
import ProximityPrize.SubmissionLower.Final50PriceCaps

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.defProp false

namespace Final50PriceActualOrder
open Final50PriceCaps (Band start thresholds order)
open Final50Price (layerNeed)
open KoalaSplitGateWords (words)
open K1_13 (Shape remaining InBox)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.sumBelow_add
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj:0 < r.j+y.j):availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L+1650 / (r.j+y.j)):=by
  rw [P3_6_8_1.sumBelow_eq,Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]

private def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length=0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 48) = v) &&
        check f (offset+min length 48) (length - 48) vs

private theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
    (h:check f offset length values=true) :
    P3_6_8_1.sumBelow f (offset+length)=P3_6_8_1.sumBelow f offset+values.sum:=by
  induction values generalizing offset length with
  | nil =>
    have hz:length=0:=of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 48) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr:=(Bool.and_eq_true_iff.mp h).2
    have hs:min length 48+(length - 48)=length:=by omega
    calc
      _=P3_6_8_1.sumBelow f (offset+min length 48+(length - 48)):=by rw [Nat.add_assoc,hs]
      _=P3_6_8_1.sumBelow f (offset+min length 48)+vs.sum:=ih _ _ hr
      _=_:=by rw [P3_6_8_1.sumBelow_add,hv,List.sum_cons,Nat.add_assoc]

private theorem mass_of_checks (f : ℕ → ℕ) (N : ℕ) (values : List ℕ)
    (h:check f 0 N values=true) (hv:values.sum < layerNeed) :
    P3_6_8_1.sumBelow f N < layerNeed:=by
  have hs:=check_sum f 0 N values h
  have hsum : P3_6_8_1.sumBelow f N = values.sum := by
    simpa only [Nat.zero_add,P3_6_8_1.sumBelow] using hs
  rwa [hsum]

private theorem paid (r x : Shape) (l : ℕ) (code : String) (hjr : 0 < r.j := by decide)
    (h : (check (fastLayer r x l) 0 (l+1650/(r.j+x.j)) (words code) &&
      decide ((words code).sum < layerNeed))=true := by decide +kernel) :
    availableMass r x l < layerNeed:=by
  rw [mass_eq r x l (Or.inr hjr) (by omega)]
  exact mass_of_checks _ _ _ (Bool.and_eq_true_iff.mp h).1
    (of_decide_eq_true (Bool.and_eq_true_iff.mp h).2)

private def r_two6thinwide_11_95_0:=paid ⟨11,6,2⟩ ⟨124,50,0⟩ 94 "9?0ho;_ ,gr>-@B >#dS2$"
private def r_two6thinwide_11_95_1:=paid ⟨11,6,2⟩ ⟨126,49,0⟩ 94 "9?0ho;_ ,gwK8=h >N0-KK"
private def r_two6thinwide_11_94_0:=paid ⟨11,6,2⟩ ⟨124,38,0⟩ 93 "9?0ho;_ ,cqx4(J ?|I77W"
private def r_two6wider_16_126_0:=paid ⟨16,6,2⟩ ⟨104,50,0⟩ 125 "8MY8#y& +Gq3g%J $MaYK7E !"
private def r_two6wider_16_126_1:=paid ⟨16,6,2⟩ ⟨106,49,0⟩ 125 "8MY8#y& +Gq3g%J $Mlf*a/ !"
private def r_two6wider_16_126_2:=paid ⟨16,6,2⟩ ⟨108,48,0⟩ 125 "8MY8#y& +Gq3g%J $Mw`G}' !"
private def r_two6wider_16_126_3:=paid ⟨16,6,2⟩ ⟨110,47,0⟩ 125 "8MY8#y& +Gq3g%J $N%DDYX !"
private def r_two6wider_16_126_4:=paid ⟨16,6,2⟩ ⟨111,46,0⟩ 125 "8MY8#y& +Gq3g%J $N4*FXj !"
private def r_two6wider_16_126_5:=paid ⟨16,6,2⟩ ⟨113,45,0⟩ 125 "8MY8#y& +Gq3g%J $N>C*3> !"
private def r_two6wider_16_126_6:=paid ⟨16,6,2⟩ ⟨115,44,0⟩ 125 "8MY8#y& +Gq3g%J $NH;F}9 !"
private def r_two6wider_16_126_7:=paid ⟨16,6,2⟩ ⟨117,38,0⟩ 125 "8MY8#y& +Gq3g%J $OWnv?d !"
private def r_two6wider_16_126_8:=paid ⟨16,6,2⟩ ⟨120,37,0⟩ 125 "8MY8#y& +Gq3g%J $OZ=*~R !"
private def r_two6wider_16_125_0:=paid ⟨16,6,2⟩ ⟨111,38,0⟩ 124 "8MY8#y& +Gq3g%J $KX/MfH !"
private def r_two6wider_16_125_1:=paid ⟨16,6,2⟩ ⟨115,37,0⟩ 124 "8MY8#y& +Gq3g%J $KU[4r- !"
private def r_two6wider_16_125_2:=paid ⟨16,6,2⟩ ⟨119,36,0⟩ 124 "8MY8#y& +Gq3g%J $KQh*d^ !"
private def r_two6wider_16_125_3:=paid ⟨16,6,2⟩ ⟨121,35,0⟩ 124 "8MY8#y& +Gq3g%J $KYjK=S !"
private def r_two7last_11_140_0:=paid ⟨11,7,2⟩ ⟨101,49,0⟩ 139 "8D_WKt> +3U1{q! $l(zM}J V(z:o"
private def r_two7last_11_140_1:=paid ⟨11,7,2⟩ ⟨103,48,0⟩ 139 "8D_WKt> +3U1{q! $l.yE?f YRNF/"
private def r_two7last_11_140_2:=paid ⟨11,7,2⟩ ⟨104,47,0⟩ 139 "8D_WKt> +3U1{q! $l5_`ky ^HJbH"
private def r_two7last_11_140_3:=paid ⟨11,7,2⟩ ⟨105,46,0⟩ 139 "8D_WKt> +3U1{q! $l<K+|I bRv&5"
private def r_two7last_11_140_4:=paid ⟨11,7,2⟩ ⟨107,45,0⟩ 139 "8D_WKt> +3U1{q! $lBWFJW fU]~!"
private def r_two7last_11_140_5:=paid ⟨11,7,2⟩ ⟨109,44,0⟩ 139 "8D_WKt> +3U1{q! $lHh2@L jj[l_"
private def r_two7last_11_140_6:=paid ⟨11,7,2⟩ ⟨111,43,0⟩ 139 "8D_WKt> +3U1{q! $lN{D^I o3>pL"
private def r_two7last_11_140_7:=paid ⟨11,7,2⟩ ⟨113,42,0⟩ 139 "8D_WKt> +3U1{q! $lU4vy> sk}($"
private def r_two7last_11_140_8:=paid ⟨11,7,2⟩ ⟨116,41,0⟩ 139 "8D_WKt> +3U1{q! $lZd$)P x0D}4"
private def r_two7last_11_140_9:=paid ⟨11,7,2⟩ ⟨118,40,0⟩ 139 "8D_WKt> +3U1{q! $lb!WM{ },wuc"
private def r_two7last_11_140_10:=paid ⟨11,7,2⟩ ⟨121,39,0⟩ 139 "8D_WKt> +3U1{q! $lgRb@O #$hvV'"
private def r_two7last_11_140_11:=paid ⟨11,7,2⟩ ⟨126,38,0⟩ 139 "8D_WKt> +3U1{q! $lkFyf: #(E9Zq"
private def r_two7last_11_139_0:=paid ⟨11,7,2⟩ ⟨111,38,0⟩ 138 "8D_WKt> +3U1{q! $jlu9O! ht?:D"
private def r_two7last_11_139_1:=paid ⟨11,7,2⟩ ⟨115,37,0⟩ 138 "8D_WKt> +3U1{q! $js'+d+ ln8o7"
private def r_two7last_11_139_2:=paid ⟨11,7,2⟩ ⟨119,36,0⟩ 138 "8D_WKt> +3U1{q! $jy1e*) pja'5"
private def r_two7last_11_139_3:=paid ⟨11,7,2⟩ ⟨122,35,0⟩ 138 "8D_WKt> +3U1{q! $k#@~$z u>T;^"
private def r_two7last_11_139_4:=paid ⟨11,7,2⟩ ⟨126,34,0⟩ 138 "8D_WKt> +3U1{q! $k)D0'L y;Vmu"
private def r_two7last_12_187_0:=paid ⟨12,7,2⟩ ⟨15,44,0⟩ 186 "86,M,'R *{)].[B $f-tsCc M_Tx!y !"
private def r_two7last_12_187_1:=paid ⟨12,7,2⟩ ⟨59,43,0⟩ 186 "86,M,'R *{)].[B $f-tsCc M^ab9( !"
private def r_two7last_12_187_2:=paid ⟨12,7,2⟩ ⟨60,42,0⟩ 186 "86,M,'R *{)].[B $f-tsCc M_Oe]r $Ga"
private def r_two7last_12_187_3:=paid ⟨12,7,2⟩ ⟨61,41,0⟩ 186 "86,M,'R *{)].[B $f-tsCc M`AI[X 17q"
private def r_two7last_12_187_4:=paid ⟨12,7,2⟩ ⟨62,40,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Ma5tVo PR]"
private def r_two7last_12_187_5:=paid ⟨12,7,2⟩ ⟨63,39,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mb-2m` #.B@"
private def r_two7last_12_187_6:=paid ⟨12,7,2⟩ ⟨64,38,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mc'FSi $.B,"
private def r_two7last_12_187_7:=paid ⟨12,7,2⟩ ⟨66,36,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Me$tlW 'WV("
private def r_two7last_12_187_8:=paid ⟨12,7,2⟩ ⟨68,35,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mf#(O_ *90H"
private def r_two7last_12_187_9:=paid ⟨12,7,2⟩ ⟨69,34,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mg)Lg& -q|V"
private def r_two7last_12_187_10:=paid ⟨12,7,2⟩ ⟨71,33,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mh-D`+ 2KnN"
private def r_two7last_12_187_11:=paid ⟨12,7,2⟩ ⟨88,32,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mh5c_O 61$`"
private def r_two7last_12_187_12:=paid ⟨12,7,2⟩ ⟨106,31,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mh1wIm 9WH_"
private def r_two7last_12_187_13:=paid ⟨12,7,2⟩ ⟨123,30,0⟩ 186 "86,M,'R *{)].[B $f-tsCc Mh-c0) <b7-"
private def r_two7last_12_186_0:=paid ⟨12,7,2⟩ ⟨73,32,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MQ0KRe %xI1"
private def r_two7last_12_186_1:=paid ⟨12,7,2⟩ ⟨75,31,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MRGaE* (B4Y"
private def r_two7last_12_186_2:=paid ⟨12,7,2⟩ ⟨77,30,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MSccb- +gb5"
private def r_two7last_12_186_3:=paid ⟨12,7,2⟩ ⟨80,29,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MTz_V0 04vS"
private def r_two7last_12_186_4:=paid ⟨12,7,2⟩ ⟨82,28,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MV?zW_ 6*w*"
private def r_two7last_12_186_5:=paid ⟨12,7,2⟩ ⟨85,27,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MW^@-e =FNg"
private def r_two7last_12_186_6:=paid ⟨12,7,2⟩ ⟨87,26,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MY*qG_ Fiq$"
private def r_two7last_12_186_7:=paid ⟨12,7,2⟩ ⟨90,25,0⟩ 185 "86,M,'R *{)].[B $f-tsCc MZNLH7 Qr$G"
private def r_two7last_12_186_8:=paid ⟨12,7,2⟩ ⟨94,24,0⟩ 185 "86,M,'R *{)].[B $f-tsCc M[kUW4 _Qkz"
private def r_two7last_12_186_9:=paid ⟨12,7,2⟩ ⟨98,23,0⟩ 185 "86,M,'R *{)].[B $f-tsCc M^,3(s n0dS"
private def r_two7last_12_186_10:=paid ⟨12,7,2⟩ ⟨103,22,0⟩ 185 "86,M,'R *{)].[B $f-tsCc M_?drn }f`* !"
private def r_two7last_12_186_11:=paid ⟨12,7,2⟩ ⟨108,21,0⟩ 185 "86,M,'R *{)].[B $f-tsCc M`S)vd #1Wc[ !"
private def r_two7last_12_186_12:=paid ⟨12,7,2⟩ ⟨113,20,0⟩ 185 "86,M,'R *{)].[B $f-tsCc Mafz<c #C8A3 !"
private def r_two7last_12_186_13:=paid ⟨12,7,2⟩ ⟨120,19,0⟩ 185 "86,M,'R *{)].[B $f-tsCc Mb^5}M #Pgm4 !"

private theorem chart_two6thinwide_11_95 (b j t : ℕ) (h : (124 ≤ b ∧ 50 ≤ j) ∨ (126 ≤ b ∧ 49 ≤ j)) :
    availableMass ⟨11,6,2⟩ ⟨b,j,t⟩ 94 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,6,2⟩)
      (y:=⟨124,50,0⟩) (x:=⟨b,j,t⟩) (L:=94) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6thinwide_11_95_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,6,2⟩)
      (y:=⟨126,49,0⟩) (x:=⟨b,j,t⟩) (L:=94) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6thinwide_11_95_1

private theorem chart_two6thinwide_11_94 (b j t : ℕ) (h : (124 ≤ b ∧ 38 ≤ j)) :
    availableMass ⟨11,6,2⟩ ⟨b,j,t⟩ 93 < layerNeed:=by
  rcases h with ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,6,2⟩)
      (y:=⟨124,38,0⟩) (x:=⟨b,j,t⟩) (L:=93) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6thinwide_11_94_0

private theorem chart_two6wider_16_126 (b j t : ℕ) (h : (104 ≤ b ∧ 50 ≤ j) ∨ (106 ≤ b ∧ 49 ≤ j) ∨ (108 ≤ b ∧ 48 ≤ j) ∨ (110 ≤ b ∧ 47 ≤ j) ∨ (111 ≤ b ∧ 46 ≤ j) ∨ (113 ≤ b ∧ 45 ≤ j) ∨ (115 ≤ b ∧ 44 ≤ j) ∨ (117 ≤ b ∧ 38 ≤ j) ∨ (120 ≤ b ∧ 37 ≤ j)) :
    availableMass ⟨16,6,2⟩ ⟨b,j,t⟩ 125 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨104,50,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨106,49,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨108,48,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨110,47,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨111,46,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨113,45,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨115,44,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨117,38,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨120,37,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_8

private theorem chart_two6wider_16_125 (b j t : ℕ) (h : (111 ≤ b ∧ 38 ≤ j) ∨ (115 ≤ b ∧ 37 ≤ j) ∨ (119 ≤ b ∧ 36 ≤ j) ∨ (121 ≤ b ∧ 35 ≤ j)) :
    availableMass ⟨16,6,2⟩ ⟨b,j,t⟩ 124 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨111,38,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨115,37,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨119,36,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨121,35,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_3

private theorem chart_two7last_11_140 (b j t : ℕ) (h : (101 ≤ b ∧ 49 ≤ j) ∨ (103 ≤ b ∧ 48 ≤ j) ∨ (104 ≤ b ∧ 47 ≤ j) ∨ (105 ≤ b ∧ 46 ≤ j) ∨ (107 ≤ b ∧ 45 ≤ j) ∨ (109 ≤ b ∧ 44 ≤ j) ∨ (111 ≤ b ∧ 43 ≤ j) ∨ (113 ≤ b ∧ 42 ≤ j) ∨ (116 ≤ b ∧ 41 ≤ j) ∨ (118 ≤ b ∧ 40 ≤ j) ∨ (121 ≤ b ∧ 39 ≤ j) ∨ (126 ≤ b ∧ 38 ≤ j)) :
    availableMass ⟨11,7,2⟩ ⟨b,j,t⟩ 139 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨101,49,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨103,48,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨104,47,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨105,46,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨107,45,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨109,44,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨111,43,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨113,42,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨116,41,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_8
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨118,40,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_9
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨121,39,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_10
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨126,38,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_11

private theorem chart_two7last_11_139 (b j t : ℕ) (h : (111 ≤ b ∧ 38 ≤ j) ∨ (115 ≤ b ∧ 37 ≤ j) ∨ (119 ≤ b ∧ 36 ≤ j) ∨ (122 ≤ b ∧ 35 ≤ j) ∨ (126 ≤ b ∧ 34 ≤ j)) :
    availableMass ⟨11,7,2⟩ ⟨b,j,t⟩ 138 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨111,38,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨115,37,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨119,36,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨122,35,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨126,34,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_4

private theorem chart_two7last_12_187 (b j t : ℕ) (h : (15 ≤ b ∧ 44 ≤ j) ∨ (59 ≤ b ∧ 43 ≤ j) ∨ (60 ≤ b ∧ 42 ≤ j) ∨ (61 ≤ b ∧ 41 ≤ j) ∨ (62 ≤ b ∧ 40 ≤ j) ∨ (63 ≤ b ∧ 39 ≤ j) ∨ (64 ≤ b ∧ 38 ≤ j) ∨ (66 ≤ b ∧ 36 ≤ j) ∨ (68 ≤ b ∧ 35 ≤ j) ∨ (69 ≤ b ∧ 34 ≤ j) ∨ (71 ≤ b ∧ 33 ≤ j) ∨ (88 ≤ b ∧ 32 ≤ j) ∨ (106 ≤ b ∧ 31 ≤ j) ∨ (123 ≤ b ∧ 30 ≤ j)) :
    availableMass ⟨12,7,2⟩ ⟨b,j,t⟩ 186 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨15,44,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨59,43,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨60,42,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨61,41,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨62,40,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨63,39,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨64,38,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨66,36,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨68,35,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_8
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨69,34,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_9
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨71,33,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_10
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨88,32,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_11
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨106,31,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_12
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨123,30,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_13

private theorem chart_two7last_12_186 (b j t : ℕ) (h : (73 ≤ b ∧ 32 ≤ j) ∨ (75 ≤ b ∧ 31 ≤ j) ∨ (77 ≤ b ∧ 30 ≤ j) ∨ (80 ≤ b ∧ 29 ≤ j) ∨ (82 ≤ b ∧ 28 ≤ j) ∨ (85 ≤ b ∧ 27 ≤ j) ∨ (87 ≤ b ∧ 26 ≤ j) ∨ (90 ≤ b ∧ 25 ≤ j) ∨ (94 ≤ b ∧ 24 ≤ j) ∨ (98 ≤ b ∧ 23 ≤ j) ∨ (103 ≤ b ∧ 22 ≤ j) ∨ (108 ≤ b ∧ 21 ≤ j) ∨ (113 ≤ b ∧ 20 ≤ j) ∨ (120 ≤ b ∧ 19 ≤ j)) :
    availableMass ⟨12,7,2⟩ ⟨b,j,t⟩ 185 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨73,32,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨75,31,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨77,30,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨80,29,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨82,28,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨85,27,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨87,26,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨90,25,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨94,24,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_8
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨98,23,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_9
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨103,22,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_10
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨108,21,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_11
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨113,20,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_12
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨120,19,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_13

def raisedPlain (k : Band) (b j q l : ℕ) : ℕ :=
  if k = .two6thinwide ∧ q=11 ∧ ((124≤b ∧ 50≤j) ∨ (126≤b ∧ 49≤j)) then max l 95
  else if k = .two6thinwide ∧ q=11 ∧ ((124≤b ∧ 38≤j)) then max l 94
  else if k = .two6wider ∧ q=16 ∧ ((104≤b ∧ 50≤j) ∨ (106≤b ∧ 49≤j) ∨ (108≤b ∧ 48≤j) ∨ (110≤b ∧ 47≤j) ∨ (111≤b ∧ 46≤j) ∨ (113≤b ∧ 45≤j) ∨ (115≤b ∧ 44≤j) ∨ (117≤b ∧ 38≤j) ∨ (120≤b ∧ 37≤j)) then max l 126
  else if k = .two6wider ∧ q=16 ∧ ((111≤b ∧ 38≤j) ∨ (115≤b ∧ 37≤j) ∨ (119≤b ∧ 36≤j) ∨ (121≤b ∧ 35≤j)) then max l 125
  else if k = .two7last ∧ q=11 ∧ ((101≤b ∧ 49≤j) ∨ (103≤b ∧ 48≤j) ∨ (104≤b ∧ 47≤j) ∨ (105≤b ∧ 46≤j) ∨ (107≤b ∧ 45≤j) ∨ (109≤b ∧ 44≤j) ∨ (111≤b ∧ 43≤j) ∨ (113≤b ∧ 42≤j) ∨ (116≤b ∧ 41≤j) ∨ (118≤b ∧ 40≤j) ∨ (121≤b ∧ 39≤j) ∨ (126≤b ∧ 38≤j)) then max l 140
  else if k = .two7last ∧ q=11 ∧ ((111≤b ∧ 38≤j) ∨ (115≤b ∧ 37≤j) ∨ (119≤b ∧ 36≤j) ∨ (122≤b ∧ 35≤j) ∨ (126≤b ∧ 34≤j)) then max l 139
  else if k = .two7last ∧ q=12 ∧ ((15≤b ∧ 44≤j) ∨ (59≤b ∧ 43≤j) ∨ (60≤b ∧ 42≤j) ∨ (61≤b ∧ 41≤j) ∨ (62≤b ∧ 40≤j) ∨ (63≤b ∧ 39≤j) ∨ (64≤b ∧ 38≤j) ∨ (66≤b ∧ 36≤j) ∨ (68≤b ∧ 35≤j) ∨ (69≤b ∧ 34≤j) ∨ (71≤b ∧ 33≤j) ∨ (88≤b ∧ 32≤j) ∨ (106≤b ∧ 31≤j) ∨ (123≤b ∧ 30≤j)) then max l 187
  else if k = .two7last ∧ q=12 ∧ ((73≤b ∧ 32≤j) ∨ (75≤b ∧ 31≤j) ∨ (77≤b ∧ 30≤j) ∨ (80≤b ∧ 29≤j) ∨ (82≤b ∧ 28≤j) ∨ (85≤b ∧ 27≤j) ∨ (87≤b ∧ 26≤j) ∨ (90≤b ∧ 25≤j) ∨ (94≤b ∧ 24≤j) ∨ (98≤b ∧ 23≤j) ∨ (103≤b ∧ 22≤j) ∨ (108≤b ∧ 21≤j) ∨ (113≤b ∧ 20≤j) ∨ (120≤b ∧ 19≤j)) then max l 186
  else l

theorem raisedPlain_pos {k : Band} {b j q l : ℕ} (h : 0 < l) : 0 < raisedPlain k b j q l := by
  unfold raisedPlain
  repeat' split
  all_goals omega

theorem raisedPlain_valid (k : Band) (b j t q l : ℕ) :
    raisedPlain k b j q l ≤ l ∨
      availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raisedPlain k b j q l-1) < layerNeed:=by
  unfold raisedPlain
  split
  · rename_i h
    rcases h with ⟨rfl,rfl,h⟩
    by_cases hl:95≤l
    · exact Or.inl (max_le le_rfl hl)
    rw [max_eq_right (by omega:l≤95)]
    exact Or.inr (chart_two6thinwide_11_95 b j t h)
  · split
    · rename_i h
      rcases h with ⟨rfl,rfl,h⟩
      by_cases hl:94≤l
      · exact Or.inl (max_le le_rfl hl)
      rw [max_eq_right (by omega:l≤94)]
      exact Or.inr (chart_two6thinwide_11_94 b j t h)
    · split
      · rename_i h
        rcases h with ⟨rfl,rfl,h⟩
        by_cases hl:126≤l
        · exact Or.inl (max_le le_rfl hl)
        rw [max_eq_right (by omega:l≤126)]
        exact Or.inr (chart_two6wider_16_126 b j t h)
      · split
        · rename_i h
          rcases h with ⟨rfl,rfl,h⟩
          by_cases hl:125≤l
          · exact Or.inl (max_le le_rfl hl)
          rw [max_eq_right (by omega:l≤125)]
          exact Or.inr (chart_two6wider_16_125 b j t h)
        · split
          · rename_i h
            rcases h with ⟨rfl,rfl,h⟩
            by_cases hl:140≤l
            · exact Or.inl (max_le le_rfl hl)
            rw [max_eq_right (by omega:l≤140)]
            exact Or.inr (chart_two7last_11_140 b j t h)
          · split
            · rename_i h
              rcases h with ⟨rfl,rfl,h⟩
              by_cases hl:139≤l
              · exact Or.inl (max_le le_rfl hl)
              rw [max_eq_right (by omega:l≤139)]
              exact Or.inr (chart_two7last_11_139 b j t h)
            · split
              · rename_i h
                rcases h with ⟨rfl,rfl,h⟩
                by_cases hl:187≤l
                · exact Or.inl (max_le le_rfl hl)
                rw [max_eq_right (by omega:l≤187)]
                exact Or.inr (chart_two7last_12_187 b j t h)
              · split
                · rename_i h
                  rcases h with ⟨rfl,rfl,h⟩
                  by_cases hl:186≤l
                  · exact Or.inl (max_le le_rfl hl)
                  rw [max_eq_right (by omega:l≤186)]
                  exact Or.inr (chart_two7last_12_186 b j t h)
                · exact Or.inl le_rfl


open KoalaWeightedReceipt2428 (WeightedOrder)
open private KoalaWeightedReceipt2428.retained from ProximityPrize.SubmissionLower.KoalaWeightedReceipt2428

private theorem weightedRetained :
    InBox KoalaWeightedReceipt2428.retained ⟨11, (start Band.two7last).j, (start Band.two7last).t⟩ := by
  unfold InBox
  decide

private def at141:List (ℕ × ℕ × ℕ):=[(123,49,2),(124,49,2),(124,49,3),(124,49,4),(125,48,2),(125,49,4),(126,48,2),(126,48,3),(126,49,5)]
private def at142:List (ℕ × ℕ × ℕ):=[(125,49,2),(125,49,3),(126,49,2),(126,49,3),(126,49,4)]

private def weightedTarget (k : Band) (b j t q : ℕ) : ℕ :=
  if k = .two7last ∧ q=11 ∧ 125≤b ∧ 49≤j ∧ (b,j,t) ∈ at142 then 142
  else if k = .two7last ∧ q=11 ∧ 123≤b ∧ 48≤j ∧ (b,j,t) ∈ at141 then 141
  else 0

def raisedBefore (k : Band) (b j t q l : ℕ) : ℕ :=
  max (raisedPlain k b j q l) (weightedTarget k b j t q)

theorem raisedBefore_pos {k : Band} {b j t q l : ℕ} (h : 0 < l) : 0 < raisedBefore k b j t q l :=
  (raisedPlain_pos h).trans_le (le_max_left _ _)

theorem raisedBefore_valid (k : Band) (b j t q l : ℕ) :
    raisedBefore k b j t q l ≤ l ∨
      availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raisedBefore k b j t q l-1) < layerNeed ∨
        WeightedOrder ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raisedBefore k b j t q l):=by
  unfold raisedBefore
  by_cases h:weightedTarget k b j t q≤raisedPlain k b j q l
  · rw [max_eq_left h]
    exact (raisedPlain_valid k b j t q l).imp id Or.inl
  rw [max_eq_right (le_of_lt (Nat.lt_of_not_ge h))]
  right
  right
  by_cases ha:k = .two7last ∧ q=11 ∧ 125≤b ∧ 49≤j ∧ (b,j,t) ∈ at142
  · rw [weightedTarget, if_pos ha]
    rcases ha with ⟨rfl,rfl,hb,hj,_⟩
    exact ⟨weightedRetained, Or.inr ⟨le_rfl,hb,hj⟩⟩
  · by_cases hb : k = .two7last ∧ q = 11 ∧ 123 ≤ b ∧ 48 ≤ j ∧ (b,j,t) ∈ at141
    · rw [weightedTarget, if_neg ha, if_pos hb]
      rcases hb with ⟨rfl,rfl,hb,hj,_⟩
      exact ⟨weightedRetained, Or.inl ⟨le_rfl,hb,hj⟩⟩
    · simp [weightedTarget,ha,hb] at h

private def p2429_0:=paid ⟨3,4,1⟩ ⟨111,52,0⟩ 60 "<oOs;kB )74V~s!"
private def p2429_1:=paid ⟨4,4,1⟩ ⟨111,52,0⟩ 61 "<]uz1[F )M7mkQQ"
private def p2429_2:=paid ⟨5,4,1⟩ ⟨111,52,0⟩ 62 "<K>$'LJ )bN#q8f"
private def p2429_3:=paid ⟨6,4,1⟩ ⟨111,52,0⟩ 63 "<9d*z=N )tw2Lmu"
private def p2429_4:=paid ⟨7,4,1⟩ ⟨111,52,0⟩ 64 "<(,1p.R *(S?jN:"
private def p2429_5:=paid ⟨8,4,1⟩ ⟨111,52,0⟩ 65 ";sQ8e|V *7@SgC4"
private def p2429_6:=paid ⟨9,4,1⟩ ⟨111,52,0⟩ 67 ";aw?ZmZ *b?^_,Q"
private def p2429_7:=paid ⟨10,4,1⟩ ⟨111,52,0⟩ 68 ";O?FP^_ *lBC_FB !"
private def p2429_8:=paid ⟨11,4,1⟩ ⟨111,52,0⟩ 69 ";=eMFNc *tR@N+P !"
private def p2429_9:=paid ⟨12,4,1⟩ ⟨111,52,0⟩ 71 ";,-T<?g +7:*Ckg !"
private def p2429_10:=paid ⟨13,4,1⟩ ⟨111,52,0⟩ 72 ":wR[20k +:YG3+o !"
private def p2429_11:=paid ⟨14,4,1⟩ ⟨111,52,0⟩ 74 ":exc'~o +R{i;KH qsm"
private def p2429_12:=paid ⟨15,4,1⟩ ⟨111,52,0⟩ 76 ":S@izos +gvwF6B @V>k"
private def p2429_13:=paid ⟨16,4,1⟩ ⟨111,52,0⟩ 78 ":Afpp`w +wI%vDE $K<@M"
private def p2429_14:=paid ⟨17,4,1⟩ ⟨111,52,0⟩ 80 ":0.wfP{ ,%LX'/) ,$P;H"
private def p2429_15:=paid ⟨18,4,1⟩ ⟨111,52,0⟩ 83 "9{S~[B! ,<Zt}G+ YYF8/"
private def p2429_16:=paid ⟨19,4,1⟩ ⟨111,52,0⟩ 86 "9iz(Q3& ,K9XUo/ $/G@AC"
private def p2429_17:=paid ⟨20,4,1⟩ ⟨111,52,0⟩ 90 "9WB/G$* ,[2NkDG *?oMo4"
private def p2429_18:=paid ⟨21,4,1⟩ ⟨111,52,0⟩ 95 "9Eh6<r. ,Ze[3?S A:({j="
private def p2429_19:=paid ⟨22,4,1⟩ ⟨111,52,0⟩ 101 "940=2c2 ,8@Kl-. u^J;nB"
private def p2429_20:=paid ⟨23,4,1⟩ ⟨111,52,0⟩ 110 "9!UD(S6 +poiigc #O8@MUL"
private def p2429_21:=paid ⟨24,4,1⟩ ⟨111,52,0⟩ 131 "8m{J{D: +KA)gD: $+Z_b9h !"
private def p2429_22:=paid ⟨3,6,2⟩ ⟨129,47,0⟩ 75 ":`9X?[o +XI.]?C #[t;"
private def p2429_23:=paid ⟨3,6,2⟩ ⟨129,49,0⟩ 75 ":`9X?[o +U/*;'+ !"
private def p2429_24:=paid ⟨3,6,2⟩ ⟨130,46,0⟩ 75 ":`9X?[o +YyBK4: (<H}"
private def p2429_25:=paid ⟨5,6,2⟩ ⟨84,50,0⟩ 78 ":@7E4<k +tu7KhD #PAMj"
private def p2429_26:=paid ⟨6,6,2⟩ ⟨84,50,0⟩ 80 ":0e;][: ,)z5uT( .9Ag:"
private def p2429_27:=paid ⟨7,6,2⟩ ⟨84,50,0⟩ 82 "9~52(zg ,8KQSZJ Qp@{>"
private def p2429_28:=paid ⟨8,6,2⟩ ⟨84,50,0⟩ 85 "9nc(Q<6 ,RFyMA% $8C1D("
private def p2429_29:=paid ⟨9,6,2⟩ ⟨84,50,0⟩ 87 "9_2{zZc ,WH,:+T &`'Hp~"
private def p2429_30:=paid ⟨10,6,2⟩ ⟨84,50,0⟩ 90 "9N`rEz2 ,cEA`G. -c32TZ"
private def p2429_31:=paid ⟨11,6,2⟩ ⟨84,50,0⟩ 93 "9?0ho;_ ,bzN#h0 :rm12`"
private def p2429_32:=paid ⟨5,6,2⟩ ⟨87,49,0⟩ 78 ":@7E4<k +v%+}6< $Ep*="
private def p2429_33:=paid ⟨6,6,2⟩ ⟨87,49,0⟩ 80 ":0e;][: ,*{avx} 1ZmBi"
private def p2429_34:=paid ⟨7,6,2⟩ ⟨87,49,0⟩ 82 "9~52(zg ,9?}'bk YVNg#"
private def p2429_35:=paid ⟨8,6,2⟩ ⟨87,49,0⟩ 85 "9nc(Q<6 ,S'JrY| $J/F+'"
private def p2429_36:=paid ⟨9,6,2⟩ ⟨87,49,0⟩ 87 "9_2{zZc ,Wv/C~G &yC`k."
private def p2429_37:=paid ⟨10,6,2⟩ ⟨87,49,0⟩ 90 "9N`rEz2 ,c^b5*_ .+4yxo"
private def p2429_38:=paid ⟨11,6,2⟩ ⟨87,49,0⟩ 93 "9?0ho;_ ,c%D]DD ;Bn[[J"
private def p2429_39:=paid ⟨5,6,2⟩ ⟨91,46,0⟩ 78 ":@7E4<k +zHPs20 )Y8B{"
private def p2429_40:=paid ⟨6,6,2⟩ ⟨91,46,0⟩ 80 ":0e;][: ,.th0rR @w}2X"
private def p2429_41:=paid ⟨7,6,2⟩ ⟨91,46,0⟩ 82 "9~52(zg ,<fDP0a zE6Ui"
private def p2429_42:=paid ⟨8,6,2⟩ ⟨91,46,0⟩ 84 "9nc(Q<6 ,Fhdzmn $1ZSjJ"
private def p2429_43:=paid ⟨9,6,2⟩ ⟨91,46,0⟩ 87 "9_2{zZc ,YsvF@? (!]O[2"
private def p2429_44:=paid ⟨10,6,2⟩ ⟨91,46,0⟩ 90 "9N`rEz2 ,dh.t:U /a^~7$"
private def p2429_45:=paid ⟨11,6,2⟩ ⟨91,46,0⟩ 93 "9?0ho;_ ,cGb3v5 =@9>;8"
private def p2429_46:=paid ⟨5,6,2⟩ ⟨93,45,0⟩ 78 ":@7E4<k +{n$>gX ,C3v_"
private def p2429_47:=paid ⟨6,6,2⟩ ⟨93,45,0⟩ 80 ":0e;][: ,0-RLow GX46q"
private def p2429_48:=paid ⟨7,6,2⟩ ⟨93,45,0⟩ 82 "9~52(zg ,=kwj-i #)l6DR"
private def p2429_49:=paid ⟨8,6,2⟩ ⟨93,45,0⟩ 84 "9nc(Q<6 ,G[s#,D $E=w-C"
private def p2429_50:=paid ⟨9,6,2⟩ ⟨93,45,0⟩ 87 "9_2{zZc ,ZMlWTV (C|&{B"
private def p2429_51:=paid ⟨10,6,2⟩ ⟨93,45,0⟩ 90 "9N`rEz2 ,e):O7/ 03k(Pa"
private def p2429_52:=paid ⟨11,6,2⟩ ⟨93,45,0⟩ 93 "9?0ho;_ ,cQd3hw =z1kqk"
private def p2429_53:=paid ⟨5,6,2⟩ ⟨93,46,0⟩ 78 ":@7E4<k +z'5q&{ )I(Ok"
private def p2429_54:=paid ⟨6,6,2⟩ ⟨93,46,0⟩ 80 ":0e;][: ,.TXGP* @;Kk0"
private def p2429_55:=paid ⟨7,6,2⟩ ⟨93,46,0⟩ 82 "9~52(zg ,<Hm&,m xg2N:"
private def p2429_56:=paid ⟨8,6,2⟩ ⟨93,46,0⟩ 84 "9nc(Q<6 ,FND-#b $.;cdc"
private def p2429_57:=paid ⟨9,6,2⟩ ⟨93,46,0⟩ 87 "9_2{zZc ,Y`h<dY 'x<Hq2"
private def p2429_58:=paid ⟨10,6,2⟩ ⟨93,46,0⟩ 90 "9N`rEz2 ,d[Lkih /Ss$T$"
private def p2429_59:=paid ⟨11,6,2⟩ ⟨93,46,0⟩ 93 "9?0ho;_ ,cCCU4v =.%5mL"
private def p2429_60:=paid ⟨5,6,2⟩ ⟨93,47,0⟩ 78 ":@7E4<k +xAi:,C '1JX!"
private def p2429_61:=paid ⟨6,6,2⟩ ⟨93,47,0⟩ 80 ":0e;][: ,-#,w<Z :,aB("
private def p2429_62:=paid ⟨7,6,2⟩ ⟨93,47,0⟩ 82 "9~52(zg ,;)<56J l<}7T"
private def p2429_63:=paid ⟨8,6,2⟩ ⟨93,47,0⟩ 84 "9nc(Q<6 ,EBbMYB #v8HP5"
private def p2429_64:=paid ⟨9,6,2⟩ ⟨93,47,0⟩ 87 "9_2{zZc ,Xs[[<) 'Q%{R_"
private def p2429_65:=paid ⟨10,6,2⟩ ⟨93,47,0⟩ 90 "9N`rEz2 ,d1~mE] .wU)h|"
private def p2429_66:=paid ⟨11,6,2⟩ ⟨93,47,0⟩ 93 "9?0ho;_ ,c5)7J2 <AD7.A"
private def p2429_67:=paid ⟨5,6,2⟩ ⟨94,45,0⟩ 78 ":@7E4<k +{[g}y5 ,7h^7"
private def p2429_68:=paid ⟨6,6,2⟩ ⟨94,45,0⟩ 80 ":0e;][: ,/zF_$B G2f}Z"
private def p2429_69:=paid ⟨7,6,2⟩ ⟨94,45,0⟩ 82 "9~52(zg ,=]2w!l #(o,:J"
private def p2429_70:=paid ⟨8,6,2⟩ ⟨94,45,0⟩ 84 "9nc(Q<6 ,GNq%?~ $CH.'J"
private def p2429_71:=paid ⟨9,6,2⟩ ⟨94,45,0⟩ 87 "9_2{zZc ,ZD$EIZ (?{dkh"
private def p2429_72:=paid ⟨10,6,2⟩ ⟨94,45,0⟩ 90 "9N`rEz2 ,e#B.a. 0,}adm"
private def p2429_73:=paid ⟨11,6,2⟩ ⟨94,45,0⟩ 93 "9?0ho;_ ,cOR}Hs =p[x#,"
private def p2429_74:=paid ⟨5,6,2⟩ ⟨95,46,0⟩ 78 ":@7E4<k +ybwnxi )8u]Z"
private def p2429_75:=paid ⟨6,6,2⟩ ⟨95,46,0⟩ 80 ":0e;][: ,.5I_._ ?[xEe"
private def p2429_76:=paid ⟨7,6,2⟩ ⟨95,46,0⟩ 82 "9~52(zg ,<,7X(y w+.Fi"
private def p2429_77:=paid ⟨8,6,2⟩ ⟨95,46,0⟩ 84 "9nc(Q<6 ,F5$<6U $*yr^{"
private def p2429_78:=paid ⟨9,6,2⟩ ⟨95,46,0⟩ 87 "9_2{zZc ,YLY3*t 'pyB)2"
private def p2429_79:=paid ⟨10,6,2⟩ ⟨95,46,0⟩ 90 "9N`rEz2 ,dOkc:z /G*'r$"
private def p2429_80:=paid ⟨11,6,2⟩ ⟨95,46,0⟩ 93 "9?0ho;_ ,c?%wPY <xn-Aa"
private def p2429_81:=paid ⟨5,6,2⟩ ⟨99,43,0⟩ 78 ":@7E4<k +~:CpF[ 3HKnI"
private def p2429_82:=paid ⟨6,6,2⟩ ⟨99,43,0⟩ 80 ":0e;][: ,2::}Cy VOj.}"
private def p2429_83:=paid ⟨7,6,2⟩ ⟨99,43,0⟩ 82 "9~52(zg ,?XzL^& #CAM!{"
private def p2429_84:=paid ⟨8,6,2⟩ ⟨99,43,0⟩ 84 "9nc(Q<6 ,I)vysl $lJv20"
private def p2429_85:=paid ⟨9,6,2⟩ ⟨99,43,0⟩ 87 "9_2{zZc ,[KY2^s )$aJ/B"
private def p2429_86:=paid ⟨10,6,2⟩ ⟨99,43,0⟩ 90 "9N`rEz2 ,eYG1OF 1)aJmq"
private def p2429_87:=paid ⟨11,6,2⟩ ⟨99,43,0⟩ 93 "9?0ho;_ ,cb@Ajw >}?7)R"
private def p2429_88:=paid ⟨5,6,2⟩ ⟨105,46,0⟩ 78 ":@7E4<k +wtKd?k (D%@g"
private def p2429_89:=paid ⟨6,6,2⟩ ⟨105,46,0⟩ 80 ":0e;][: ,,Q[t?N <F=GT"
private def p2429_90:=paid ⟨7,6,2⟩ ⟨105,46,0⟩ 82 "9~52(zg ,:UE=rX ntv~:"
private def p2429_91:=paid ⟨8,6,2⟩ ⟨105,46,0⟩ 84 "9nc(Q<6 ,Do=,8v #w:aA:"
private def p2429_92:=paid ⟨9,6,2⟩ ⟨105,46,0⟩ 87 "9_2{zZc ,XHo`#= 'K3}62"
private def p2429_93:=paid ⟨10,6,2⟩ ⟨105,46,0⟩ 90 "9N`rEz2 ,crH7jx .d28J$"
private def p2429_94:=paid ⟨11,6,2⟩ ⟨105,46,0⟩ 93 "9?0ho;_ ,c)If#) ;ye`#i"
private def p2429_95:=paid ⟨5,6,2⟩ ⟨110,40,0⟩ 78 ":@7E4<k ,$OjRJd AKaz%"
private def p2429_96:=paid ⟨6,6,2⟩ ⟨110,40,0⟩ 80 ":0e;][: ,5%[[@0 pb+Y("
private def p2429_97:=paid ⟨7,6,2⟩ ⟨110,40,0⟩ 82 "9~52(zg ,Audu?y #k3n|Z"
private def p2429_98:=paid ⟨8,6,2⟩ ⟨110,40,0⟩ 84 "9nc(Q<6 ,Jvqx#4 %E43B9"
private def p2429_99:=paid ⟨9,6,2⟩ ⟨110,40,0⟩ 87 "9_2{zZc ,]_2f?i )uU9#a"
private def p2429_100:=paid ⟨10,6,2⟩ ⟨110,40,0⟩ 89 "9N`rEz2 ,[>6TNm .[gxC8"
private def p2429_101:=paid ⟨11,6,2⟩ ⟨110,40,0⟩ 93 "9?0ho;_ ,ct~Z|j @6jn=b"
private def p2429_102:=paid ⟨5,6,2⟩ ⟨115,38,0⟩ 77 ":@7E4<k +p{UU`I <R)[{"
private def p2429_103:=paid ⟨6,6,2⟩ ⟨115,38,0⟩ 79 ":0e;][: ,%Kwz(U cArof"
private def p2429_104:=paid ⟨7,6,2⟩ ⟨115,38,0⟩ 82 "9~52(zg ,Cnh}6s $-cDuw"
private def p2429_105:=paid ⟨8,6,2⟩ ⟨115,38,0⟩ 84 "9nc(Q<6 ,LLedQb %q2Wg."
private def p2429_106:=paid ⟨9,6,2⟩ ⟨115,38,0⟩ 86 "9_2{zZc ,Q&/juH (PocbF"
private def p2429_107:=paid ⟨10,6,2⟩ ⟨115,38,0⟩ 89 "9N`rEz2 ,]#5n9( /JxTZF"
private def p2429_108:=paid ⟨11,6,2⟩ ⟨115,38,0⟩ 93 "9?0ho;_ ,d)NY6+ A<[%vO"
private def p2429_109:=paid ⟨5,6,2⟩ ⟨118,38,0⟩ 78 ":@7E4<k ,&G^lIS KgEP."
private def p2429_110:=paid ⟨6,6,2⟩ ⟨118,38,0⟩ 79 ":0e;][: ,$h)Rl. _i9EW"
private def p2429_111:=paid ⟨7,6,2⟩ ⟨118,38,0⟩ 82 "9~52(zg ,C6iFV% $%A9Di"
private def p2429_112:=paid ⟨8,6,2⟩ ⟨118,38,0⟩ 84 "9nc(Q<6 ,KzU=b^ %d4P-c"
private def p2429_113:=paid ⟨9,6,2⟩ ⟨118,38,0⟩ 86 "9_2{zZc ,P[g!CD (>2-7|"
private def p2429_114:=paid ⟨10,6,2⟩ ⟨118,38,0⟩ 89 "9N`rEz2 ,[g~=$& /.LY]l"
private def p2429_115:=paid ⟨11,6,2⟩ ⟨118,38,0⟩ 93 "9?0ho;_ ,d!].1T @q4jan"
private def p2429_116:=paid ⟨5,6,2⟩ ⟨120,49,0⟩ 79 ":@7E4<k ,'*)L#* &du(L"
private def p2429_117:=paid ⟨6,6,2⟩ ⟨120,49,0⟩ 80 ":0e;][: ,%wf(p> ,[M_L"
private def p2429_118:=paid ⟨7,6,2⟩ ⟨120,49,0⟩ 82 "9~52(zg ,4_VAt0 IUA+w"
private def p2429_119:=paid ⟨8,6,2⟩ ⟨120,49,0⟩ 85 "9nc(Q<6 ,O0>_qf #rC^`g"
private def p2429_120:=paid ⟨9,6,2⟩ ⟨120,49,0⟩ 87 "9_2{zZc ,T`{*0) %wp-un"
private def p2429_121:=paid ⟨10,6,2⟩ ⟨120,49,0⟩ 90 "9N`rEz2 ,a]gGe3 ,3Wkif"
private def p2429_122:=paid ⟨11,6,2⟩ ⟨120,49,0⟩ 94 "9?0ho;_ ,g~FN9l ?%}Z*+"
private def p2429_123:=paid ⟨5,6,2⟩ ⟨122,40,0⟩ 78 ":@7E4<k +~j8^_| ;2{F%"
private def p2429_124:=paid ⟨6,6,2⟩ ⟨122,40,0⟩ 80 ":0e;][: ,2S2({@ c)}wu"
private def p2429_125:=paid ⟨7,6,2⟩ ⟨122,40,0⟩ 82 "9~52(zg ,?_!_k] #Q*;>{"
private def p2429_126:=paid ⟨8,6,2⟩ ⟨122,40,0⟩ 84 "9nc(Q<6 ,H|$IN< $x{0l9"
private def p2429_127:=paid ⟨9,6,2⟩ ⟨122,40,0⟩ 87 "9_2{zZc ,[8Hh2@ )*{_Mu"
private def p2429_128:=paid ⟨10,6,2⟩ ⟨122,40,0⟩ 90 "9N`rEz2 ,eGo'B6 0}Q/L!"
private def p2429_129:=paid ⟨11,6,2⟩ ⟨122,40,0⟩ 93 "9?0ho;_ ,cX{=,b >]qF1n"
private def p2429_130:=paid ⟨5,6,2⟩ ⟨123,36,0⟩ 77 ":@7E4<k +rrG7-3 Cpx9:"
private def p2429_131:=paid ⟨6,6,2⟩ ⟨123,36,0⟩ 79 ":0e;][: ,'(qkB~ ne;KX"
private def p2429_132:=paid ⟨7,6,2⟩ ⟨123,36,0⟩ 81 "9~52(zg ,4a$1Vw #]j'ZJ"
private def p2429_133:=paid ⟨8,6,2⟩ ⟨123,36,0⟩ 84 "9nc(Q<6 ,ML@R$A &-oVA]"
private def p2429_134:=paid ⟨9,6,2⟩ ⟨123,36,0⟩ 86 "9_2{zZc ,Qj|MJy (o`bxV"
private def p2429_135:=paid ⟨10,6,2⟩ ⟨123,36,0⟩ 89 "9N`rEz2 ,]JX(XT /rJ86Z"
private def p2429_136:=paid ⟨11,6,2⟩ ⟨123,36,0⟩ 93 "9?0ho;_ ,d3y:uS AmdtBz"
private def p2429_137:=paid ⟨5,6,2⟩ ⟨123,48,0⟩ 78 ":@7E4<k +q]B.S~ $;!'~"
private def p2429_138:=paid ⟨6,6,2⟩ ⟨123,48,0⟩ 80 ":0e;][: ,&i`8jg /%{7$"
private def p2429_139:=paid ⟨7,6,2⟩ ⟨123,48,0⟩ 82 "9~52(zg ,5E^C`] Ns+@X"
private def p2429_140:=paid ⟨8,6,2⟩ ⟨123,48,0⟩ 85 "9nc(Q<6 ,OdW4|Y #~^0%/"
private def p2429_141:=paid ⟨9,6,2⟩ ⟨123,48,0⟩ 87 "9_2{zZc ,U*]S@2 &,C5Qr"
private def p2429_142:=paid ⟨10,6,2⟩ ⟨123,48,0⟩ 90 "9N`rEz2 ,asIC(Z ,N(_L6"
private def p2429_143:=paid ⟨11,6,2⟩ ⟨123,48,0⟩ 93 "9?0ho;_ ,bBwL$K 8rX2yi"
private def p2429_144:=paid ⟨5,6,2⟩ ⟨123,50,0⟩ 79 ":@7E4<k ,%8I$Z6 %2]%G"
private def p2429_145:=paid ⟨6,6,2⟩ ⟨123,50,0⟩ 81 ":0e;][: ,6IGvmC 3LHKK"
private def p2429_146:=paid ⟨7,6,2⟩ ⟨123,50,0⟩ 83 "9~52(zg ,D&[p3r ]Z`(."
private def p2429_147:=paid ⟨8,6,2⟩ ⟨123,50,0⟩ 85 "9nc(Q<6 ,Mv$ei+ #]i2rN"
private def p2429_148:=paid ⟨9,6,2⟩ ⟨123,50,0⟩ 87 "9_2{zZc ,Sa&Ce` %UjJ,,"
private def p2429_149:=paid ⟨10,6,2⟩ ⟨123,50,0⟩ 90 "9N`rEz2 ,a%fy6X +VmxwJ"
private def p2429_150:=paid ⟨11,6,2⟩ ⟨123,50,0⟩ 94 "9?0ho;_ ,gsL.hR >,!i^6"
private def p2429_151:=paid ⟨5,6,2⟩ ⟨124,49,0⟩ 79 ":@7E4<k ,&L&:Y! &JA[e"
private def p2429_152:=paid ⟨6,6,2⟩ ⟨124,49,0⟩ 80 ":0e;][: ,%>O;DJ ,#lEy"
private def p2429_153:=paid ⟨7,6,2⟩ ⟨124,49,0⟩ 83 "9~52(zg ,D~..Yd ef;]~"
private def p2429_154:=paid ⟨8,6,2⟩ ⟨124,49,0⟩ 85 "9nc(Q<6 ,NajkR% #k|(iw"
private def p2429_155:=paid ⟨9,6,2⟩ ⟨124,49,0⟩ 87 "9_2{zZc ,T;x~Jz %lP05~"
private def p2429_156:=paid ⟨10,6,2⟩ ⟨124,49,0⟩ 90 "9N`rEz2 ,aF@!z+ +{=B#~"
private def p2429_157:=paid ⟨11,6,2⟩ ⟨124,49,0⟩ 94 "9?0ho;_ ,gyi?[+ >`IZ~`"
private def p2429_158:=paid ⟨5,6,2⟩ ⟨126,47,0⟩ 78 ":@7E4<k +rX6.|7 %2,d^"
private def p2429_159:=paid ⟨6,6,2⟩ ⟨126,47,0⟩ 80 ":0e;][: ,'ZD-Qv 1eUZS"
private def p2429_160:=paid ⟨7,6,2⟩ ⟨126,47,0⟩ 82 "9~52(zg ,6,@{0L TJLUh"
private def p2429_161:=paid ⟨8,6,2⟩ ⟨126,47,0⟩ 85 "9nc(Q<6 ,P:L:D[ $.&G*6"
private def p2429_162:=paid ⟨9,6,2⟩ ⟨126,47,0⟩ 87 "9_2{zZc ,UP~-): &=l]k?"
private def p2429_163:=paid ⟨10,6,2⟩ ⟨126,47,0⟩ 90 "9N`rEz2 ,b+zm%N ,i3w|J"
private def p2429_164:=paid ⟨11,6,2⟩ ⟨126,47,0⟩ 93 "9?0ho;_ ,bJ9s3h 966vR0"
private def p2429_165:=paid ⟨5,6,2⟩ ⟨126,49,0⟩ 79 ":@7E4<k ,&/$`t{ &=VGB"
private def p2429_166:=paid ⟨6,6,2⟩ ⟨126,49,0⟩ 80 ":0e;][: ,%!DD^! +d{9a"
private def p2429_167:=paid ⟨7,6,2⟩ ⟨126,49,0⟩ 83 "9~52(zg ,DeBi_C d4_vO"
private def p2429_168:=paid ⟨8,6,2⟩ ⟨126,49,0⟩ 85 "9nc(Q<6 ,NK#BBb #hik?P"
private def p2429_169:=paid ⟨9,6,2⟩ ⟨126,49,0⟩ 87 "9_2{zZc ,T)wz*E %fo`DW"
private def p2429_170:=paid ⟨10,6,2⟩ ⟨126,49,0⟩ 90 "9N`rEz2 ,a;,mUU +p_-^["
private def p2429_171:=paid ⟨11,6,2⟩ ⟨126,49,0⟩ 94 "9?0ho;_ ,gwK8=h >N0-KK"
private def p2429_172:=paid ⟨13,6,2⟩ ⟨107,48,0⟩ 102 "8}.TcyZ ,9JmG4{ #-|b2Or"
private def p2429_173:=paid ⟨13,6,2⟩ ⟨123,43,0⟩ 102 "8}.TcyZ ,9JmG4{ #/D>0(R"
private def p2429_174:=paid ⟨4,7,2⟩ ⟨105,49,0⟩ 92 "9NMCs^k ,[5%&#j 1zEhb^"
private def p2429_175:=paid ⟨5,7,2⟩ ⟨105,49,0⟩ 96 "9?x9Ro! ,XFHy3w LhW,.]"
private def p2429_176:=paid ⟨6,7,2⟩ ⟨105,49,0⟩ 99 "91E/3!6 ,Bwt+|: jnkQRk"
private def p2429_177:=paid ⟨4,7,2⟩ ⟨109,48,0⟩ 92 "9NMCs^k ,[By7]m 2EYk/1"
private def p2429_178:=paid ⟨5,7,2⟩ ⟨109,48,0⟩ 95 "9?x9Ro! ,VE&3=@ D:(zr;"
private def p2429_179:=paid ⟨6,7,2⟩ ⟨109,48,0⟩ 99 "91E/3!6 ,Bwt+|: k:=@w."
private def p2429_180:=paid ⟨4,7,2⟩ ⟨113,48,0⟩ 92 "9NMCs^k ,[9MiQ8 24?mv-"
private def p2429_181:=paid ⟨5,7,2⟩ ⟨113,48,0⟩ 96 "9?x9Ro! ,XFHy3w M!pF7:"
private def p2429_182:=paid ⟨6,7,2⟩ ⟨113,48,0⟩ 99 "91E/3!6 ,Bwt+|: k%KmM{"
private def p2429_183:=paid ⟨4,7,2⟩ ⟨116,48,0⟩ 92 "9NMCs^k ,[2Dw1V 2'C@|X"
private def p2429_184:=paid ⟨5,7,2⟩ ⟨116,48,0⟩ 96 "9?x9Ro! ,XFHy3w LnH[~L"
private def p2429_185:=paid ⟨6,7,2⟩ ⟨116,48,0⟩ 99 "91E/3!6 ,Bwt+|: jrn`/o"
private def p2429_186:=paid ⟨4,7,2⟩ ⟨117,45,0⟩ 92 "9NMCs^k ,[w,o{U 3zPZYT"
private def p2429_187:=paid ⟨5,7,2⟩ ⟨117,45,0⟩ 95 "9?x9Ro! ,VK4rM, F'jA)-"
private def p2429_188:=paid ⟨6,7,2⟩ ⟨117,45,0⟩ 99 "91E/3!6 ,Bwt+|: lqte8C"
private def p2429_189:=paid ⟨4,7,2⟩ ⟨118,45,0⟩ 92 "9NMCs^k ,[taT:} 3uLGsw"
private def p2429_190:=paid ⟨5,7,2⟩ ⟨118,45,0⟩ 95 "9?x9Ro! ,VJtUyo E~Bzh0"
private def p2429_191:=paid ⟨6,7,2⟩ ⟨118,45,0⟩ 99 "91E/3!6 ,Bwt+|: ll',kj"
private def p2429_192:=paid ⟨4,7,2⟩ ⟨121,45,0⟩ 92 "9NMCs^k ,[mCa49 3f?ld$"
private def p2429_193:=paid ⟨5,7,2⟩ ⟨121,45,0⟩ 95 "9?x9Ro! ,VIx`C} Ek+lj9"
private def p2429_194:=paid ⟨6,7,2⟩ ⟨121,45,0⟩ 99 "91E/3!6 ,Bwt+|: lYU>J#"
private def p2429_195:=paid ⟨4,7,2⟩ ⟨121,46,0⟩ 92 "9NMCs^k ,[TzRk+ 3(N=|]"
private def p2429_196:=paid ⟨5,7,2⟩ ⟨121,46,0⟩ 95 "9?x9Ro! ,VG%9GV E!L,3|"
private def p2429_197:=paid ⟨6,7,2⟩ ⟨121,46,0⟩ 99 "91E/3!6 ,Bwt+|: kvk*H6"
private def p2429_198:=paid ⟨4,7,2⟩ ⟨122,44,0⟩ 92 "9NMCs^k ,]%LQ1c 4C>d;D"
private def p2429_199:=paid ⟨5,7,2⟩ ⟨122,44,0⟩ 95 "9?x9Ro! ,VLQ48F FQB_<K"
private def p2429_200:=paid ⟨6,7,2⟩ ⟨122,44,0⟩ 99 "91E/3!6 ,Bwt+|: m96&17"
private def p2429_201:=paid ⟨4,7,2⟩ ⟨124,44,0⟩ 92 "9NMCs^k ,[}SH%$ 48a&R0"
private def p2429_202:=paid ⟨5,7,2⟩ ⟨124,44,0⟩ 95 "9?x9Ro! ,VKsGv> FC}j!l"
private def p2429_203:=paid ⟨6,7,2⟩ ⟨124,44,0⟩ 99 "91E/3!6 ,Bwt+|: m-*-}d"
private def p2429_204:=paid ⟨4,7,2⟩ ⟨129,42,0⟩ 92 "9NMCs^k ,]CDfn( 5Cf&RP"
private def p2429_205:=paid ⟨5,7,2⟩ ⟨129,42,0⟩ 95 "9?x9Ro! ,VP)?wF G^#B'w"
private def p2429_206:=paid ⟨6,7,2⟩ ⟨129,42,0⟩ 99 "91E/3!6 ,Bwt+|: n8@i.a"

private structure ExtraOrder where
  k : Band
  b : ℕ
  j : ℕ
  q : ℕ
  l : ℕ
  positiveIndex : 0 < (start k).j
  paidMass : availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,0⟩ (l-1) < layerNeed

private def newOrders : List ExtraOrder := [
  ⟨.one4,111,52,3,61,by decide,p2429_0⟩,
  ⟨.one4,111,52,4,62,by decide,p2429_1⟩,
  ⟨.one4,111,52,5,63,by decide,p2429_2⟩,
  ⟨.one4,111,52,6,64,by decide,p2429_3⟩,
  ⟨.one4,111,52,7,65,by decide,p2429_4⟩,
  ⟨.one4,111,52,8,66,by decide,p2429_5⟩,
  ⟨.one4,111,52,9,68,by decide,p2429_6⟩,
  ⟨.one4,111,52,10,69,by decide,p2429_7⟩,
  ⟨.one4,111,52,11,70,by decide,p2429_8⟩,
  ⟨.one4,111,52,12,72,by decide,p2429_9⟩,
  ⟨.one4,111,52,13,73,by decide,p2429_10⟩,
  ⟨.one4,111,52,14,75,by decide,p2429_11⟩,
  ⟨.one4,111,52,15,77,by decide,p2429_12⟩,
  ⟨.one4,111,52,16,79,by decide,p2429_13⟩,
  ⟨.one4,111,52,17,81,by decide,p2429_14⟩,
  ⟨.one4,111,52,18,84,by decide,p2429_15⟩,
  ⟨.one4,111,52,19,87,by decide,p2429_16⟩,
  ⟨.one4,111,52,20,91,by decide,p2429_17⟩,
  ⟨.one4,111,52,21,96,by decide,p2429_18⟩,
  ⟨.one4,111,52,22,102,by decide,p2429_19⟩,
  ⟨.one4,111,52,23,111,by decide,p2429_20⟩,
  ⟨.one4,111,52,24,132,by decide,p2429_21⟩,
  ⟨.two6thin,129,47,3,76,by decide,p2429_22⟩,
  ⟨.two6thin,129,49,3,76,by decide,p2429_23⟩,
  ⟨.two6thin,130,46,3,76,by decide,p2429_24⟩,
  ⟨.two6thinwide,84,50,5,79,by decide,p2429_25⟩,
  ⟨.two6thinwide,84,50,6,81,by decide,p2429_26⟩,
  ⟨.two6thinwide,84,50,7,83,by decide,p2429_27⟩,
  ⟨.two6thinwide,84,50,8,86,by decide,p2429_28⟩,
  ⟨.two6thinwide,84,50,9,88,by decide,p2429_29⟩,
  ⟨.two6thinwide,84,50,10,91,by decide,p2429_30⟩,
  ⟨.two6thinwide,84,50,11,94,by decide,p2429_31⟩,
  ⟨.two6thinwide,87,49,5,79,by decide,p2429_32⟩,
  ⟨.two6thinwide,87,49,6,81,by decide,p2429_33⟩,
  ⟨.two6thinwide,87,49,7,83,by decide,p2429_34⟩,
  ⟨.two6thinwide,87,49,8,86,by decide,p2429_35⟩,
  ⟨.two6thinwide,87,49,9,88,by decide,p2429_36⟩,
  ⟨.two6thinwide,87,49,10,91,by decide,p2429_37⟩,
  ⟨.two6thinwide,87,49,11,94,by decide,p2429_38⟩,
  ⟨.two6thinwide,91,46,5,79,by decide,p2429_39⟩,
  ⟨.two6thinwide,91,46,6,81,by decide,p2429_40⟩,
  ⟨.two6thinwide,91,46,7,83,by decide,p2429_41⟩,
  ⟨.two6thinwide,91,46,8,85,by decide,p2429_42⟩,
  ⟨.two6thinwide,91,46,9,88,by decide,p2429_43⟩,
  ⟨.two6thinwide,91,46,10,91,by decide,p2429_44⟩,
  ⟨.two6thinwide,91,46,11,94,by decide,p2429_45⟩,
  ⟨.two6thinwide,93,45,5,79,by decide,p2429_46⟩,
  ⟨.two6thinwide,93,45,6,81,by decide,p2429_47⟩,
  ⟨.two6thinwide,93,45,7,83,by decide,p2429_48⟩,
  ⟨.two6thinwide,93,45,8,85,by decide,p2429_49⟩,
  ⟨.two6thinwide,93,45,9,88,by decide,p2429_50⟩,
  ⟨.two6thinwide,93,45,10,91,by decide,p2429_51⟩,
  ⟨.two6thinwide,93,45,11,94,by decide,p2429_52⟩,
  ⟨.two6thinwide,93,46,5,79,by decide,p2429_53⟩,
  ⟨.two6thinwide,93,46,6,81,by decide,p2429_54⟩,
  ⟨.two6thinwide,93,46,7,83,by decide,p2429_55⟩,
  ⟨.two6thinwide,93,46,8,85,by decide,p2429_56⟩,
  ⟨.two6thinwide,93,46,9,88,by decide,p2429_57⟩,
  ⟨.two6thinwide,93,46,10,91,by decide,p2429_58⟩,
  ⟨.two6thinwide,93,46,11,94,by decide,p2429_59⟩,
  ⟨.two6thinwide,93,47,5,79,by decide,p2429_60⟩,
  ⟨.two6thinwide,93,47,6,81,by decide,p2429_61⟩,
  ⟨.two6thinwide,93,47,7,83,by decide,p2429_62⟩,
  ⟨.two6thinwide,93,47,8,85,by decide,p2429_63⟩,
  ⟨.two6thinwide,93,47,9,88,by decide,p2429_64⟩,
  ⟨.two6thinwide,93,47,10,91,by decide,p2429_65⟩,
  ⟨.two6thinwide,93,47,11,94,by decide,p2429_66⟩,
  ⟨.two6thinwide,94,45,5,79,by decide,p2429_67⟩,
  ⟨.two6thinwide,94,45,6,81,by decide,p2429_68⟩,
  ⟨.two6thinwide,94,45,7,83,by decide,p2429_69⟩,
  ⟨.two6thinwide,94,45,8,85,by decide,p2429_70⟩,
  ⟨.two6thinwide,94,45,9,88,by decide,p2429_71⟩,
  ⟨.two6thinwide,94,45,10,91,by decide,p2429_72⟩,
  ⟨.two6thinwide,94,45,11,94,by decide,p2429_73⟩,
  ⟨.two6thinwide,95,46,5,79,by decide,p2429_74⟩,
  ⟨.two6thinwide,95,46,6,81,by decide,p2429_75⟩,
  ⟨.two6thinwide,95,46,7,83,by decide,p2429_76⟩,
  ⟨.two6thinwide,95,46,8,85,by decide,p2429_77⟩,
  ⟨.two6thinwide,95,46,9,88,by decide,p2429_78⟩,
  ⟨.two6thinwide,95,46,10,91,by decide,p2429_79⟩,
  ⟨.two6thinwide,95,46,11,94,by decide,p2429_80⟩,
  ⟨.two6thinwide,99,43,5,79,by decide,p2429_81⟩,
  ⟨.two6thinwide,99,43,6,81,by decide,p2429_82⟩,
  ⟨.two6thinwide,99,43,7,83,by decide,p2429_83⟩,
  ⟨.two6thinwide,99,43,8,85,by decide,p2429_84⟩,
  ⟨.two6thinwide,99,43,9,88,by decide,p2429_85⟩,
  ⟨.two6thinwide,99,43,10,91,by decide,p2429_86⟩,
  ⟨.two6thinwide,99,43,11,94,by decide,p2429_87⟩,
  ⟨.two6thinwide,105,46,5,79,by decide,p2429_88⟩,
  ⟨.two6thinwide,105,46,6,81,by decide,p2429_89⟩,
  ⟨.two6thinwide,105,46,7,83,by decide,p2429_90⟩,
  ⟨.two6thinwide,105,46,8,85,by decide,p2429_91⟩,
  ⟨.two6thinwide,105,46,9,88,by decide,p2429_92⟩,
  ⟨.two6thinwide,105,46,10,91,by decide,p2429_93⟩,
  ⟨.two6thinwide,105,46,11,94,by decide,p2429_94⟩,
  ⟨.two6thinwide,110,40,5,79,by decide,p2429_95⟩,
  ⟨.two6thinwide,110,40,6,81,by decide,p2429_96⟩,
  ⟨.two6thinwide,110,40,7,83,by decide,p2429_97⟩,
  ⟨.two6thinwide,110,40,8,85,by decide,p2429_98⟩,
  ⟨.two6thinwide,110,40,9,88,by decide,p2429_99⟩,
  ⟨.two6thinwide,110,40,10,90,by decide,p2429_100⟩,
  ⟨.two6thinwide,110,40,11,94,by decide,p2429_101⟩,
  ⟨.two6thinwide,115,38,5,78,by decide,p2429_102⟩,
  ⟨.two6thinwide,115,38,6,80,by decide,p2429_103⟩,
  ⟨.two6thinwide,115,38,7,83,by decide,p2429_104⟩,
  ⟨.two6thinwide,115,38,8,85,by decide,p2429_105⟩,
  ⟨.two6thinwide,115,38,9,87,by decide,p2429_106⟩,
  ⟨.two6thinwide,115,38,10,90,by decide,p2429_107⟩,
  ⟨.two6thinwide,115,38,11,94,by decide,p2429_108⟩,
  ⟨.two6thinwide,118,38,5,79,by decide,p2429_109⟩,
  ⟨.two6thinwide,118,38,6,80,by decide,p2429_110⟩,
  ⟨.two6thinwide,118,38,7,83,by decide,p2429_111⟩,
  ⟨.two6thinwide,118,38,8,85,by decide,p2429_112⟩,
  ⟨.two6thinwide,118,38,9,87,by decide,p2429_113⟩,
  ⟨.two6thinwide,118,38,10,90,by decide,p2429_114⟩,
  ⟨.two6thinwide,118,38,11,94,by decide,p2429_115⟩,
  ⟨.two6thinwide,120,49,5,80,by decide,p2429_116⟩,
  ⟨.two6thinwide,120,49,6,81,by decide,p2429_117⟩,
  ⟨.two6thinwide,120,49,7,83,by decide,p2429_118⟩,
  ⟨.two6thinwide,120,49,8,86,by decide,p2429_119⟩,
  ⟨.two6thinwide,120,49,9,88,by decide,p2429_120⟩,
  ⟨.two6thinwide,120,49,10,91,by decide,p2429_121⟩,
  ⟨.two6thinwide,120,49,11,95,by decide,p2429_122⟩,
  ⟨.two6thinwide,122,40,5,79,by decide,p2429_123⟩,
  ⟨.two6thinwide,122,40,6,81,by decide,p2429_124⟩,
  ⟨.two6thinwide,122,40,7,83,by decide,p2429_125⟩,
  ⟨.two6thinwide,122,40,8,85,by decide,p2429_126⟩,
  ⟨.two6thinwide,122,40,9,88,by decide,p2429_127⟩,
  ⟨.two6thinwide,122,40,10,91,by decide,p2429_128⟩,
  ⟨.two6thinwide,122,40,11,94,by decide,p2429_129⟩,
  ⟨.two6thinwide,123,36,5,78,by decide,p2429_130⟩,
  ⟨.two6thinwide,123,36,6,80,by decide,p2429_131⟩,
  ⟨.two6thinwide,123,36,7,82,by decide,p2429_132⟩,
  ⟨.two6thinwide,123,36,8,85,by decide,p2429_133⟩,
  ⟨.two6thinwide,123,36,9,87,by decide,p2429_134⟩,
  ⟨.two6thinwide,123,36,10,90,by decide,p2429_135⟩,
  ⟨.two6thinwide,123,36,11,94,by decide,p2429_136⟩,
  ⟨.two6thinwide,123,48,5,79,by decide,p2429_137⟩,
  ⟨.two6thinwide,123,48,6,81,by decide,p2429_138⟩,
  ⟨.two6thinwide,123,48,7,83,by decide,p2429_139⟩,
  ⟨.two6thinwide,123,48,8,86,by decide,p2429_140⟩,
  ⟨.two6thinwide,123,48,9,88,by decide,p2429_141⟩,
  ⟨.two6thinwide,123,48,10,91,by decide,p2429_142⟩,
  ⟨.two6thinwide,123,48,11,94,by decide,p2429_143⟩,
  ⟨.two6thinwide,123,50,5,80,by decide,p2429_144⟩,
  ⟨.two6thinwide,123,50,6,82,by decide,p2429_145⟩,
  ⟨.two6thinwide,123,50,7,84,by decide,p2429_146⟩,
  ⟨.two6thinwide,123,50,8,86,by decide,p2429_147⟩,
  ⟨.two6thinwide,123,50,9,88,by decide,p2429_148⟩,
  ⟨.two6thinwide,123,50,10,91,by decide,p2429_149⟩,
  ⟨.two6thinwide,123,50,11,95,by decide,p2429_150⟩,
  ⟨.two6thinwide,124,49,5,80,by decide,p2429_151⟩,
  ⟨.two6thinwide,124,49,6,81,by decide,p2429_152⟩,
  ⟨.two6thinwide,124,49,7,84,by decide,p2429_153⟩,
  ⟨.two6thinwide,124,49,8,86,by decide,p2429_154⟩,
  ⟨.two6thinwide,124,49,9,88,by decide,p2429_155⟩,
  ⟨.two6thinwide,124,49,10,91,by decide,p2429_156⟩,
  ⟨.two6thinwide,124,49,11,95,by decide,p2429_157⟩,
  ⟨.two6thinwide,126,47,5,79,by decide,p2429_158⟩,
  ⟨.two6thinwide,126,47,6,81,by decide,p2429_159⟩,
  ⟨.two6thinwide,126,47,7,83,by decide,p2429_160⟩,
  ⟨.two6thinwide,126,47,8,86,by decide,p2429_161⟩,
  ⟨.two6thinwide,126,47,9,88,by decide,p2429_162⟩,
  ⟨.two6thinwide,126,47,10,91,by decide,p2429_163⟩,
  ⟨.two6thinwide,126,47,11,94,by decide,p2429_164⟩,
  ⟨.two6thinwide,126,49,5,80,by decide,p2429_165⟩,
  ⟨.two6thinwide,126,49,6,81,by decide,p2429_166⟩,
  ⟨.two6thinwide,126,49,7,84,by decide,p2429_167⟩,
  ⟨.two6thinwide,126,49,8,86,by decide,p2429_168⟩,
  ⟨.two6thinwide,126,49,9,88,by decide,p2429_169⟩,
  ⟨.two6thinwide,126,49,10,91,by decide,p2429_170⟩,
  ⟨.two6thinwide,126,49,11,95,by decide,p2429_171⟩,
  ⟨.two6wide,107,48,13,103,by decide,p2429_172⟩,
  ⟨.two6wide,123,43,13,103,by decide,p2429_173⟩,
  ⟨.two7,105,49,4,93,by decide,p2429_174⟩,
  ⟨.two7,105,49,5,97,by decide,p2429_175⟩,
  ⟨.two7,105,49,6,100,by decide,p2429_176⟩,
  ⟨.two7,109,48,4,93,by decide,p2429_177⟩,
  ⟨.two7,109,48,5,96,by decide,p2429_178⟩,
  ⟨.two7,109,48,6,100,by decide,p2429_179⟩,
  ⟨.two7,113,48,4,93,by decide,p2429_180⟩,
  ⟨.two7,113,48,5,97,by decide,p2429_181⟩,
  ⟨.two7,113,48,6,100,by decide,p2429_182⟩,
  ⟨.two7,116,48,4,93,by decide,p2429_183⟩,
  ⟨.two7,116,48,5,97,by decide,p2429_184⟩,
  ⟨.two7,116,48,6,100,by decide,p2429_185⟩,
  ⟨.two7,117,45,4,93,by decide,p2429_186⟩,
  ⟨.two7,117,45,5,96,by decide,p2429_187⟩,
  ⟨.two7,117,45,6,100,by decide,p2429_188⟩,
  ⟨.two7,118,45,4,93,by decide,p2429_189⟩,
  ⟨.two7,118,45,5,96,by decide,p2429_190⟩,
  ⟨.two7,118,45,6,100,by decide,p2429_191⟩,
  ⟨.two7,121,45,4,93,by decide,p2429_192⟩,
  ⟨.two7,121,45,5,96,by decide,p2429_193⟩,
  ⟨.two7,121,45,6,100,by decide,p2429_194⟩,
  ⟨.two7,121,46,4,93,by decide,p2429_195⟩,
  ⟨.two7,121,46,5,96,by decide,p2429_196⟩,
  ⟨.two7,121,46,6,100,by decide,p2429_197⟩,
  ⟨.two7,122,44,4,93,by decide,p2429_198⟩,
  ⟨.two7,122,44,5,96,by decide,p2429_199⟩,
  ⟨.two7,122,44,6,100,by decide,p2429_200⟩,
  ⟨.two7,124,44,4,93,by decide,p2429_201⟩,
  ⟨.two7,124,44,5,96,by decide,p2429_202⟩,
  ⟨.two7,124,44,6,100,by decide,p2429_203⟩,
  ⟨.two7,129,42,4,93,by decide,p2429_204⟩,
  ⟨.two7,129,42,5,96,by decide,p2429_205⟩,
  ⟨.two7,129,42,6,100,by decide,p2429_206⟩
]

private def findOrder (k : Band) (b j q : ℕ) : List ExtraOrder → ℕ
  | [] => 0
  | entry :: more =>
      if k = entry.k ∧ b = entry.b ∧ j = entry.j ∧ q = entry.q then entry.l
      else findOrder k b j q more

private theorem findOrder_valid (k : Band) (b j t q : ℕ) (entries : List ExtraOrder)
    (h : 0 < findOrder k b j q entries) :
    availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩
      (findOrder k b j q entries - 1) < layerNeed := by
  induction entries with
  | nil => simp [findOrder] at h
  | cons entry more ih =>
    by_cases he : k = entry.k ∧ b = entry.b ∧ j = entry.j ∧ q = entry.q
    · rw [findOrder, if_pos he]
      rcases he with ⟨hk,hb,hj,hq⟩
      rw [hk,hb,hj,hq]
      have hanti := Final50PriceLayer.availableMass_anti_prefix
        (r := ⟨entry.q,(start entry.k).j,(start entry.k).t⟩)
        (y := ⟨entry.b,entry.j,0⟩) (x := ⟨entry.b,entry.j,t⟩)
        (L := entry.l-1) (Or.inr entry.positiveIndex)
        (entry.positiveIndex.trans_le (Nat.le_add_right _ _)) le_rfl le_rfl
      exact hanti.trans_lt entry.paidMass
    · rw [findOrder, if_neg he] at h ⊢
      exact ih h

def raised (k : Band) (b j t q l : ℕ) : ℕ :=
  max (raisedBefore k b j t q l) (findOrder k b j q newOrders)

theorem raised_pos {k : Band} {b j t q l : ℕ} (h : 0 < l) : 0 < raised k b j t q l :=
  (raisedBefore_pos h).trans_le (le_max_left _ _)

theorem raised_valid (k : Band) (b j t q l : ℕ) :
    raised k b j t q l ≤ l ∨
      availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raised k b j t q l-1) < layerNeed ∨
        WeightedOrder ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raised k b j t q l) := by
  unfold raised
  by_cases h : findOrder k b j q newOrders ≤ raisedBefore k b j t q l
  · rw [max_eq_left h]
    exact raisedBefore_valid k b j t q l
  · rw [max_eq_right (by omega : raisedBefore k b j t q l ≤ findOrder k b j q newOrders)]
    exact Or.inr (Or.inl (findOrder_valid k b j t q newOrders (by omega)))

#print axioms raised_valid
end Final50PriceActualOrder
