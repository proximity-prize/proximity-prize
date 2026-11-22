import ProximityPrize.SubmissionLower.KoalaRectCutoff
import ProximityPrize.SubmissionLower.KoalaRectRank
import ProximityPrize.SubmissionLower.KoalaRectPoleBridge
import ProximityPrize.SubmissionLower.GoldBranch7N1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section
open Finset Polynomial
open K1 (I)
open K1_14 (L FX Jet Equation Shape shapeSum seedHasse)
open K1_14_1
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open P1_7_1 (poleRows nodeRows groupedPoleMoment)
open scoped BigOperators

theorem rectRankFloor {h : ℕ} (hpos : 0 < h) (hraw : h ≤ 131070) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (U : Fin 2 → ℕ) (hbox : U 0 + U 1 ≤ s.U) (hs : s.B < K1.p) (hw : rawWidthCond h s W)
    {nodes moment : ℕ} (hnodes : nodeRows s ≤ nodes) (hmoment : groupedPoleMoment s.B s.J ≤ moment) :
    area U * shapeSum s (fun q j => W+1+j-q*(131071-h)) ≤
      rectDebit h nodes moment U + ∑ t ∈ range (W+1), Module.finrank FX (rectEvaluated Crt word s t U) := by
  have hvol := rectAmbient_volume h s W U (hraw.trans (by decide)) hbox hw
  have hphys := rectPhysical_bound h word s W U
  have hpole := rectPole_bound hpos hchar Crt word s hs W U
  have hsum := rectTelescope hraw Crt word s W U
  have hm := Nat.mul_le_mul_left (h*(U 0+U 1+2)) hmoment
  have hn := Nat.mul_le_mul_left (area U) hnodes
  rw [show 2*h*poleRows s*area U = 2*h*area U*poleRows s by ring] at hpole
  unfold rectDebit
  omega

theorem rectDivides {h : ℕ} (hpos : 0 < h) {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (A : ℕ) (s : Shape) (U : Fin 2 → ℕ) (hsmall : s.m*A < K1.p)
    {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt word s (s.m*A-1), P ∈ q.asIdeal)
    {f : Equation} (hprod : ProjectedProduct qs f) {W : ℕ} (hW : W < s.m*A)
    {P : Jet} (hP : P ∈ rectEvaluated Crt word s W U) (hn : P ≠ 0) :
    f ^ (rectPower A h s W-P.natDegree) ∣ P.leadingCoeff := by
  have htri := rectEvaluated_le Crt word s W U hP
  apply hprod.divides_leading P _ hn
  intro q hq
  apply K1_14_3R_1.proof _ _ _ (hgeo q hq)
  · have hd := Nat.div_le_self (s.m*A-1-W) (2*h)
    unfold rectPower
    omega
  intro a c hac
  change a+c < 1+(s.m*A-1-W)/(2*h) at hac
  have hc := (Nat.le_div_iff_mul_le (by omega : 0 < 2*h)).mp
    (show a+c ≤ (s.m*A-1-W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c), Nat.mul_add] at hc
  have hX : W+2*h*a+2*h*c ≤ s.m*A-1 := by omega
  have ha := P0_10_1.evaluated_shift Crt word htri 0 a
  have hb := P0_10_1.evaluated_shift Crt word ha 1 c
  exact hpass q hq _ (evaluated_mono Crt word rfl rfl rfl le_rfl hX hb)

theorem rectLoss {h : ℕ} (hpos : 0 < h) (hraw : h ≤ 131070) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (A : ℕ) (s : Shape)
    (U d : Fin 2 → ℕ) (hA : 0 < s.m*A) (hsmall : s.m*A < K1.p) (hbox : U 0 + U 1 ≤ s.U)
    (hs : s.B < K1.p) (hwidth : s.B*(131071-h) ≤ s.m*A)
    {nodes moment E : ℕ} (hnodes : nodeRows s ≤ nodes) (hmoment : groupedPoleMoment s.B s.J ≤ moment)
    (he : 0 < E) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt word s (s.m*A-1), P ∈ q.asIdeal)
    {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree) (hprod : ProjectedProduct qs f)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    rectGain A h s E U d ≤ rectDebit h nodes moment U := by
  let top := s.m*A
  have htop : top-1+1 = top := by dsimp [top]; omega
  have hrawWidth : rawWidthCond h s (top-1) := by
    intro q hq j _
    rw [htop]
    exact (Nat.mul_le_mul_right _ hq).trans (hwidth.trans (by omega : top ≤ top+j))
  have hfloor := rectRankFloor hpos hraw hchar Crt word s (top-1) U hbox hs hrawWidth hnodes hmoment
  rw [htop] at hfloor
  have hcap (W : ℕ) (hW : W ∈ range top) :
      Module.finrank FX (rectEvaluated Crt word s W U) ≤ rectCapacity A h s E U d W := by
    apply rectCutoff_finrank_le _ _ _ _ _ _ _ _ hf hE (by omega) he
    · intro P hP j i hn
      exact evaluated_shape Crt word (rectEvaluated_le Crt word s W U hP) j i hn
    · intro P hP
      exact rectEvaluated_axis Crt word hP
    · intro P hP hn
      exact P0_10_1.leading_bound hpos hraw Crt word s W P (rectEvaluated_le Crt word s W U hP) hn
    · intro P hP hn
      exact rectDivides hpos Crt word A s U hsmall hgeo hpass hprod (mem_range.mp hW) hP hn
    · exact hslots
  have hsum := sum_le_sum (s := range top) hcap
  have htotal := rectCapacity_total A h s E U d (by omega) (by omega)
  change (∑ W ∈ range top, rectCapacity A h s E U d W) + rectGain A h s E U d =
    area U * shapeSum s (fun q j => top+j-q*(131071-h)) at htotal
  omega

#print axioms rectLoss
end
end KoalaRect
