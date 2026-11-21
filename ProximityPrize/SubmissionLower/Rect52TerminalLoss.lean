import ProximityPrize.SubmissionLower.Rect52TerminalArithmetic
import ProximityPrize.SubmissionLower.RectAsymmetricBank
import ProximityPrize.SubmissionLower.Rect51Bank

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
namespace Rect52Terminal
noncomputable section

open K1 (I)
open K1_14 K1_14_1 Polynomial Finset
open scoped BigOperators
open K1_14_3 (RowCaps)
open P1_7_1 (nodeRows groupedPoleMoment)
open RectAsymmetric (rectangle rectAmbientVolume rectPhysicalDebit)
open private centerCoeff centerCoeff_eval from ProximityPrize.SubmissionLower.Fast065
open private flatten from ProximityPrize.SubmissionLower.Fast069

/-- Evaluation and linear span preserve each separate bound on seed degree. -/
theorem leading_seed_of_rectangle {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (u v W : ℕ) {P : Jet}
    (hP : P ∈ Rect51Bank.evaluated Crt word s (rectangle u v) W) (i : Fin 2) :
    Rect51Rank.coordDegree P.leadingCoeff (some i) ≤ (![u,v] : Fin 2 → ℕ) i := by
  unfold Rect51Rank.coordDegree
  rw [MvPolynomial.weightedTotalDegree_piSingle, MvPolynomial.degreeOf_le_iff]
  intro e he
  by_contra! hn
  have hsub : Rect51Bank.evaluated Crt word s (rectangle u v) W ≤
      LinearMap.ker (centerCoeff P.natDegree (e none) e.some) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q, hQ, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply centerCoeff_eval
    intro a
    exact hQ.2 P.natDegree (e none) a e.some i hn
  have hz := LinearMap.mem_ker.mp (hsub hP)
  change ((P.coeff P.natDegree).coeff (e none)).coeff e.some = 0 at hz
  rw [coeff_natDegree] at hz
  have hc := MvPolynomial.optionEquivLeft_coeff_coeff FX (flatten P.leadingCoeff) (e none) e.some
  rw [Finsupp.optionElim_some] at hc
  have hflat : MvPolynomial.optionEquivLeft FX (Fin 2) (flatten P.leadingCoeff) =
      P.leadingCoeff := AlgEquiv.apply_symm_apply _ _
  rw [hflat, hz] at hc
  exact (MvPolynomial.mem_support_iff.mp he) hc.symm

private theorem caps_shape {P : Jet} {s : Shape} (hP : RowCaps P s) (hn : P ≠ 0) :
    P.leadingCoeff.natDegree + P.natDegree ≤ s.B ∧ P.natDegree ≤ s.J := by
  have hc : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
  have h := hP _ _ hc
  exact ⟨h.1,h.2.1⟩


private theorem oriented_loss {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {e u v : ℕ} {f : Equation} (c : ℕ → ℕ) (hl : 2391 ≤ h) (hu : h ≤ 2451) (he : 0<e)
    (huv : u+v ≤ bank.shape.U) (hf : f ≠ 0) (hE : e ≤ f.natDegree)
    (hc : Antitone c) (hc0 : c 0 = (u+1)*(v+1))
    (hslots : ∀ r, Rect51Rank.slots u v (r*Rect51Rank.coordDegree f (some 0))
        (r*Rect51Rank.coordDegree f (some 1)) ≤ c r)
    (hnodes : nodeRows bank.shape = bank.nodeRows)
    (hmoment : groupedPoleMoment bank.shape.B bank.shape.J ≤ bank.poleMoment)
    (hcap : ∀ W, ∀ P ∈ evaluated Crt word bank.shape W, RowCaps P bank.shape)
    (hlead : ∀ W, ∀ P ∈ evaluated Crt word bank.shape W, P ≠ 0 →
        (P.leadingCoeff.natDegree+P.natDegree)*(131071-h) ≤ W+P.natDegree)
    (hdvd : ∀ W < bank.shape.m*High52.agreement, ∀ P ∈ evaluated Crt word bank.shape W, P ≠ 0 →
        f^(High52.contactPower h bank.shape W-P.natDegree) ∣ P.leadingCoeff) :
    jointGain h bank.shape e c ≤ rectangleDebit h u v := by
  let T := bank.shape.m*High52.agreement
  let s := bank.shape
  let C := Rect51Bank.evaluated Crt word s (rectangle u v)
  have hT : T-1+1 = T := by decide
  have hk : 0<131071-h := by omega
  have hw : rawWidthCond h s (T-1) := by
    intro q hq j _
    rw [hT]
    have hm := Nat.mul_le_mul hq (Nat.sub_le_sub_left hl _ : 131071-h≤131071-2391)
    exact hm.trans ((show s.B*(131071-2391)≤T by decide).trans (Nat.le_add_right _ _))
  have hfloor := RectAsymmetricBank.rank_floor Crt word s (by omega) (by omega)
    (hu.trans_lt (by decide : 2451 < K1.p)) (T-1) u v huv hw
  have hpole := Nat.mul_le_mul_left (h*(u+v+2)) hmoment
  have hd : rectPhysicalDebit s u v = (u+1)*(v+1)*bank.nodeRows := by
    rw [← hnodes]
    simp only [rectPhysicalDebit, nodeRows]
    exact Nat.mul_assoc _ _ _
  rw [hd,hT] at hfloor
  have hfloor' := hfloor.trans (Nat.add_le_add_right (Nat.add_le_add_left hpole _) _)
  change _ ≤ rectangleDebit h u v + ∑ W ∈ range T, Module.finrank FX (C W) at hfloor'
  have hcut : (∑ W ∈ range T, Module.finrank FX (C W)) ≤
      ∑ W ∈ range T, cutoffCapacity h s e c W := by
    apply sum_le_sum
    intro W hW
    have hle := Rect51Bank.evaluated_le Crt word s (rectangle u v) W
    rw [← cutoffCapacity_eq h s e c W hk he]
    exact cutoff_finrank_le h s u v e W c (C W) hf hE hslots hk
      (fun P hP hn => caps_shape (hcap W P (hle hP)) hn)
      (fun P hP => ⟨leading_seed_of_rectangle Crt word s u v W hP 0,
        leading_seed_of_rectangle Crt word s u v W hP 1⟩)
      (fun P hP hn => hlead W P (hle hP) hn)
      (fun P hP hn => hdvd W (mem_range.mp hW) P (hle hP) hn)
  have htotal := cutoff_total h s e c hc (by omega) hk
  rw [hc0] at htotal
  unfold rectAmbientVolume at hfloor'
  rw [hT] at hfloor'
  have hbound := hfloor'.trans (Nat.add_le_add_left hcut (rectangleDebit h u v))
  rw [← htotal] at hbound
  exact Nat.add_le_add_iff_left.mp (hbound.trans_eq (Nat.add_comm _ _))

/-- Compare the two possible CRT bank orientations with the balanced loss. -/
theorem rectangle_loss_of_bank {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {e u v V : ℕ} {f : Equation} (hl : 2391 ≤ h) (hu : h ≤ 2451) (he : 0<e)
    (hsides : u+v ≤ bank.shape.U) (horder : v ≤ u) (hf : f ≠ 0) (hE : e ≤ f.natDegree)
    (hV : V ≤ Rect51Rank.coordDegree f (some 0) + Rect51Rank.coordDegree f (some 1))
    (hnodes : nodeRows bank.shape = bank.nodeRows)
    (hmoment : groupedPoleMoment bank.shape.B bank.shape.J ≤ bank.poleMoment)
    (hcap : ∀ W, ∀ P ∈ evaluated Crt word bank.shape W, RowCaps P bank.shape)
    (hlead : ∀ W, ∀ P ∈ evaluated Crt word bank.shape W, P ≠ 0 →
        (P.leadingCoeff.natDegree+P.natDegree)*(131071-h) ≤ W+P.natDegree)
    (hdvd : ∀ W < bank.shape.m*High52.agreement, ∀ P ∈ evaluated Crt word bank.shape W, P ≠ 0 →
        f^(High52.contactPower h bank.shape W-P.natDegree) ∣ P.leadingCoeff) :
    jointGain h bank.shape e (slots u v (V/2) ((V+1)/2)) ≤ rectangleDebit h u v := by
  let x := Rect51Rank.coordDegree f (some 0)
  let y := Rect51Rank.coordDegree f (some 1)
  let c := slots u v (V/2) ((V+1)/2)
  have hc := slots_antitone u v (V/2) ((V+1)/2)
  by_cases hxy : x ≤ y
  · refine oriented_loss Crt word c hl hu he hsides hf hE hc (by simp [c,slots]) ?_
      hnodes hmoment hcap hlead hdvd
    intro r
    rw [box_slots_eq]
    simpa [slots,c] using RectAsymmetric.slots_le_balanced horder hxy hV r
  · have hs' : v+u ≤ bank.shape.U := by omega
    have horder' : y ≤ x := by omega
    have hV' : V ≤ y+x := by omega
    have h0 : c 0 = (v+1)*(u+1) := by simp [c,slots,Nat.mul_comm]
    have hm := oriented_loss Crt word c hl hu he hs' hf hE hc h0 ?_
      hnodes hmoment hcap hlead hdvd
    · simpa only [rectangleDebit, Nat.mul_comm (v+1) (u+1), Nat.add_comm v u] using hm
    · intro r
      rw [box_slots_eq]
      simp only [slots, one_mul]
      rw [Nat.mul_comm (v+1-r*x) (u+1-r*y)]
      exact RectAsymmetric.slots_le_balanced horder horder' hV' r

theorem stock_loss {h e v : ℕ} {C : ℕ → Submodule FX Jet}
    {f : Equation} (hl : 2391 ≤ h) (hu : h ≤ 2451) (he : 0 < e)
    (hf : f ≠ 0) (hE : e ≤ f.natDegree) (hV : v ≤ K1_14_4.seedDegree f)
    (hfloor : triangle bank.shape.U *
      shapeSum bank.shape (fun q j => bank.shape.m*High52.agreement+j-q*(131071-h)) ≤
      High52.debit h bank + ∑ W ∈ range (bank.shape.m*High52.agreement), Module.finrank FX (C W))
    (hcaps : ∀ W, ∀ P ∈ C W, RowCaps P bank.shape)
    (hlead : ∀ W, ∀ P ∈ C W, P ≠ 0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h) ≤ W+P.natDegree)
    (hdvd : ∀ W < bank.shape.m*High52.agreement, ∀ P ∈ C W, P ≠ 0 →
      f^(High52.contactPower h bank.shape W-P.natDegree) ∣ P.leadingCoeff) :
    High52.jointGain h bank.shape e v ≤ High52.debit h bank := by
  have hk : 0 < 131071-h := by omega
  have hc : (∑ W ∈ range (bank.shape.m*High52.agreement), Module.finrank FX (C W)) ≤
      ∑ W ∈ range (bank.shape.m*High52.agreement), High52.cutoffCapacity h bank.shape e v W :=
    sum_le_sum fun W hW => High52.cutoff_finrank_le h bank.shape e v W (C W)
      hf hE hV hk he (hcaps W) (hlead W) (hdvd W (mem_range.mp hW))
  have htot := High52.cutoff_total h bank.shape e v (by omega) hk
  omega


#print axioms rectangle_loss_of_bank
#print axioms stock_loss
end
end Rect52Terminal
