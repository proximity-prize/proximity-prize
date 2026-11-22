import ProximityPrize.SubmissionLower.UpperBranch6
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_7_2
noncomputable section
open K1_14 (Shape Jet Seeds Equation FX Banks triangle shapeSum)
open K1_14_3 (RowCaps LeadingFilter)
open Polynomial Finset
open private seed_finrank from ProximityPrize.SubmissionLower.Fast073
private def eligible (h N W q j : ℕ) : Prop :=
  q * (131071 - h) ≤ W + j ∧ N ≤ W + 2 * h * j
private instance (h N W q j : ℕ) : Decidable (eligible h N W q j) := by
  unfold eligible
  infer_instance
private def positions (s : Shape) (h N W : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((range (s.B + 1)).sigma (fun q => range (min q s.J + 1))).filter
    (fun a => eligible h N W a.1 a.2)
theorem positions_card (s : Shape) (h N W : ℕ) :
    (positions s h N W).card =
      shapeSum s (fun q j => if eligible h N W q j then 1 else 0) := by
  unfold positions shapeSum
  rw [card_filter, sum_sigma]
private theorem cutoff_finrank_le (s : Shape) (h N W : ℕ) (V : Submodule FX Jet)
    (hcaps : ∀ P ∈ V, RowCaps P s)
    (hlead : ∀ P ∈ V, P ≠ 0 →
      (P.leadingCoeff.natDegree + P.natDegree) * (131071 - h) ≤ W + P.natDegree)
    (horder : ∀ P ∈ V, P ≠ 0 → N ≤ W + 2 * h * P.natDegree) :
    Module.finrank FX V ≤
      triangle s.U * shapeSum s (fun q j => if eligible h N W q j then 1 else 0) := by
  let S := positions s h N W
  let T := MvPolynomial.restrictTotalDegree (Fin 2) FX s.U
  let coord (a : S) : V →ₗ[FX] Seeds :=
    (((lcoeff Seeds (a.1.1 - a.1.2)).restrictScalars FX).comp
      ((lcoeff Equation a.1.2).restrictScalars FX)).comp V.subtype
  let proj : V →ₗ[FX] (S → T) := LinearMap.pi fun a => (coord a).codRestrict T (by
    intro P
    change (P.1.coeff a.1.2).coeff (a.1.1 - a.1.2) ∈ T
    apply (MvPolynomial.mem_restrictTotalDegree _ _ _).2
    by_cases hz : (P.1.coeff a.1.2).coeff (a.1.1 - a.1.2) = 0
    · simp [hz]
    · exact (hcaps P.1 P.2 _ _ hz).2.2)
  have hzero : ∀ P : V, proj P = 0 → P = 0 := by
    intro P hp
    apply Subtype.ext
    by_contra hn
    let j := P.val.natDegree
    let i := P.val.leadingCoeff.natDegree
    have hcoef : (P.val.coeff j).coeff i ≠ 0 := by
      change (P.val.coeff P.val.natDegree).coeff P.val.leadingCoeff.natDegree ≠ 0
      rw [coeff_natDegree, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB, hJ, _⟩ := hcaps P.val P.property j i hcoef
    have hpos : (⟨i + j, j⟩ : Σ _ : ℕ, ℕ) ∈ S := by
      have hj := le_min (Nat.le_add_left j i) hJ
      have hel : eligible h N W (i+j) j :=
        ⟨hlead P.val P.property hn, horder P.val P.property hn⟩
      simp [S, positions, hB, hj, hel]
    let a : S := ⟨⟨i + j, j⟩, hpos⟩
    have hz := congrArg (fun v : S → T => (v a : Seeds)) hp
    change (P.val.coeff j).coeff (i+j-j) = 0 at hz
    rw [Nat.add_sub_cancel] at hz
    exact hcoef hz
  have hinj : Function.Injective proj := by
    intro P Q heq
    let D : V := P + (-1 : FX) • Q
    have hD : proj D = 0 := calc
      _ = proj P + (-1 : FX) • proj Q := by
        change proj (P + (-1 : FX) • Q) = _
        rw [map_add, map_smul]
      _ = ((1 : FX) + -1) • proj Q := by rw [add_smul, one_smul, heq]
      _ = 0 := by rw [add_neg_cancel, zero_smul]
    have h := congrArg Subtype.val (hzero D hD)
    change P.val + (-1 : FX) • Q.val = (0 : Jet) at h
    have hneg : Q.val + (-1 : FX) • Q.val = 0 := calc
      _ = ((1 : FX) + -1) • Q.val := by rw [add_smul, one_smul]
      _ = 0 := by rw [add_neg_cancel, zero_smul]
    have he := congrArg (fun r : Jet => r + Q.val) h
    rw [add_assoc, add_comm ((-1 : FX) • Q.val), hneg, add_zero, zero_add] at he
    exact Subtype.ext he
  calc
    _ ≤ Module.finrank FX (S → T) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = _ := by
      let : Module.Free FX T := Module.Free.of_basis (MvPolynomial.basisRestrictSupport FX _)
      rw [Module.finrank_pi_fintype FX (M := fun _ : S => T)]
      simp [T, S, seed_finrank, positions_card, Nat.mul_comm]
private theorem cutoff_interval_card (N j t d : ℕ) (hj : j ≤ t) :
    (∑ W ∈ range N, if t ≤ W+j ∧ W+d < N then 1 else 0) = N+j-t-d := by
  rw [← card_filter]
  have hr : (range N).filter (fun W => t ≤ W+j ∧ W+d < N) =
      Ico (t-j) (N-d) := by
    ext W
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hr, Nat.card_Ico]
  omega
private theorem position_sum (h N q j : ℕ) (hj : j ≤ q * (131071-h)) :
    (∑ W ∈ range N, if eligible h N W q j then 1 else 0) +
      (N+j-q*(131071-h)-2*h*j) = N+j-q*(131071-h) := by
  let t := q * (131071-h)
  let d := 2*h*j
  change (∑ W ∈ range N, if eligible h N W q j then 1 else 0) +
    (N+j-t-d) = N+j-t
  rw [← cutoff_interval_card N j t d hj, ← sum_add_distrib]
  have hraw := cutoff_interval_card N j t 0 hj
  rw [Nat.sub_zero] at hraw
  rw [← hraw]
  apply sum_congr rfl
  intro W hW
  have hw := mem_range.mp hW
  by_cases ht : t ≤ W+j
  · by_cases hd : W+d < N
    · have he : ¬ eligible h N W q j := fun he => (Nat.not_le_of_lt hd) he.2
      simp [he, ht, hd, hw]
    · have he : eligible h N W q j := ⟨ht, Nat.le_of_not_gt hd⟩
      simp [he, ht, hd, hw]
  · have he : ¬ eligible h N W q j := fun he => ht he.1
    simp [he, ht]
private theorem cutoff_total (s : Shape) (h N : ℕ) (hk : 1 ≤ 131071-h) :
    (∑ W ∈ range N, shapeSum s (fun q j => if eligible h N W q j then 1 else 0)) +
      shapeSum s (fun q j => N+j-q*(131071-h)-2*h*j) =
      shapeSum s (fun q j => N+j-q*(131071-h)) := by
  have hswap :
      (∑ W ∈ range N, shapeSum s (fun q j => if eligible h N W q j then 1 else 0)) =
      shapeSum s (fun q j => ∑ W ∈ range N, if eligible h N W q j then 1 else 0) := by
    unfold shapeSum
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  rw [hswap]
  simp only [shapeSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq : j ≤ q := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_left _ _)
  have hq : q ≤ q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
  exact position_sum h N q j (hjq.trans hq)
end
end P1_7_2
end
