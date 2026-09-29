import ProximityPrize.SubmissionLower.UniqueCurvatureOwner6814

/-! Exact multiplicity split used by the cofactor audit. The factorization
is finite and nonzero, and the cofactor is explicitly nonvanishing at the
chosen root. The conclusion is not a desired geometric counting bound. -/
namespace ProximityPrize.SubmissionLower.CofactorOwnership6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial UniqueCurvatureOwner6814

variable {ι E : Type*} [Field E]
local instance : DecidableEq ι := Classical.decEq ι

def owningCopies (s : Finset ι) (e m : ι → ℕ) : ℕ :=
  ∑ i ∈ s, if 0 < m i then e i else 0

theorem owner_copy_split (s : Finset ι) (e m : ι → ℕ)
    (hpos : 0 < ∑ i ∈ s, e i*m i) :
    2 ≤ owningCopies s e m ∨
      ∃ i ∈ s, e i = 1 ∧ 0 < m i ∧ (∑ j ∈ s, e j*m j) = m i ∧
        ∀ j ∈ s, j ≠ i → e j = 0 ∨ m j = 0 := by
  classical
  by_cases htwo : 2 ≤ owningCopies s e m
  · exact Or.inl htwo
  right
  obtain ⟨i,hi,hprod⟩ := Finset.sum_pos_iff.mp hpos
  have he : 0 < e i := by nlinarith
  have hm : 0 < m i := by nlinarith
  let copies : ι → ℕ := fun j => if 0 < m j then e j else 0
  have htotal : (∑ j ∈ s, copies j) ≤ 1 := by
    change owningCopies s e m ≤ 1
    omega
  have hei : copies i = e i := if_pos hm
  have hile := Finset.single_le_sum (f := copies) (fun _ _ => Nat.zero_le _) hi
  have heone : e i = 1 := by omega
  have hsplit := Finset.sum_erase_add s copies hi
  have herase : ∑ j ∈ s.erase i, copies j = 0 := by omega
  have hothers : ∀ j ∈ s, j ≠ i → e j = 0 ∨ m j = 0 := by
    intro j hj hji
    have hjle := Finset.single_le_sum (f := copies) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hji,hj⟩)
    rw [herase] at hjle
    by_cases hmj : 0 < m j
    · left
      simpa only [copies,if_pos hmj,Nat.le_zero] using hjle
    · exact Or.inr (by omega)
  refine ⟨i,hi,heone,hm,?_,hothers⟩
  rw [Finset.sum_eq_single i]
  · rw [heone,one_mul]
  · intro j hj hji
    exact mul_eq_zero.mpr (hothers j hj hji)
  · exact fun hn => False.elim (hn hi)

theorem rootMultiplicity_prod_powers (s : Finset ι) (p : ι → Polynomial E)
    (e : ι → ℕ) (t : E) (hp : ∀ i ∈ s, p i ≠ 0) :
    (∏ i ∈ s, p i ^ e i).rootMultiplicity t =
      ∑ i ∈ s, e i*(p i).rootMultiplicity t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hpa := hp a (Finset.mem_insert_self _ _)
    have hps : ∀ i ∈ s, p i ≠ 0 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hn : (∏ i ∈ s, p i ^ e i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hps i hi))
    rw [Finset.prod_insert ha,Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hpa) hn),
      rootMultiplicity_power _ _ _ hpa,ih hps,Finset.sum_insert ha]

/-- Either at least two owning factor copies are available for an
intersection count, or one factor occurs once and carries all required
root order. No irreducibility is needed for this bookkeeping theorem. -/
theorem cofactor_root_split (s : Finset ι) (p : ι → Polynomial E)
    (e : ι → ℕ) (q : Polynomial E) (t : E) (d : ℕ)
    (hp : ∀ i ∈ s, p i ≠ 0) (hq : q.eval t ≠ 0) (hd : 0 < d)
    (hdiv : (Polynomial.X-Polynomial.C t)^d ∣ q*(∏ i ∈ s, p i^e i)) :
    2 ≤ owningCopies s e (fun i => (p i).rootMultiplicity t) ∨
      ∃ i ∈ s, e i=1 ∧ d ≤ (p i).rootMultiplicity t := by
  classical
  have hq0 : q ≠ 0 := by
    intro hzero
    exact hq (by rw [hzero]; simp)
  have hn : (∏ i ∈ s, p i ^ e i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp i hi))
  have hle := (Polynomial.le_rootMultiplicity_iff (mul_ne_zero hq0 hn)).mpr hdiv
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hq0 hn),
    Polynomial.rootMultiplicity_eq_zero hq,zero_add,rootMultiplicity_prod_powers s p e t hp] at hle
  have hpos : 0 < ∑ i ∈ s, e i*(p i).rootMultiplicity t := lt_of_lt_of_le hd hle
  rcases owner_copy_split s e (fun i => (p i).rootMultiplicity t) hpos with htwo | hsingle
  · exact Or.inl htwo
  · obtain ⟨i,hi,he,_,hsum,_⟩ := hsingle
    exact Or.inr ⟨i,hi,he,hsum ▸ hle⟩

/-- Arithmetic of the multiple-copy proper-intersection branch only. -/
theorem multiple_copy_main_fits :
    checkedMain (4491/7) (34551/2) 61022 = 10199274802274101633/42 ∧
    checkedMain (4491/7) (34551/2) 61022 < 272069082261391681 := by
  norm_num [checkedMain]

/-- The surviving price is genuinely too large; this is not a geometric
counterexample, only exact arithmetic for the recorded relaxation. -/
theorem recorded_price_excess :
    checkedMain (4491/7) 28815 101496 - 272069082261391681 = 8630754917097280/7 ∧
    272069082261391681 < checkedMain (4491/7) 28815 101496 := by
  norm_num [checkedMain]

#print axioms owner_copy_split
#print axioms rootMultiplicity_prod_powers
#print axioms cofactor_root_split
#print axioms multiple_copy_main_fits
#print axioms recorded_price_excess
end
end ProximityPrize.SubmissionLower.CofactorOwnership6814
