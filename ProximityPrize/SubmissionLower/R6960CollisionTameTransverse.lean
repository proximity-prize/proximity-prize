import ProximityPrize.SubmissionLower.R6960CollisionTameWeights
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial UniqueFactorizationMonoid Finset
open scoped Polynomial BigOperators
open Lower6960.BranchIndex (mult_product)

variable {k : Type} [Field k] [DecidableEq k]

private theorem unique_sum_one {I : Type*} [Fintype I] [DecidableEq I]
    (f : I→ℕ) (sum : ∑ i,f i=1) :
    ∃ i, f i=1 ∧ ∀ j≠i,f j=0 := by
  classical
  have pos : ∃ i,0<f i := by
    by_contra! all
    have gone (i : I) : f i=0 := by have q := all i; omega
    simp only [gone,Finset.sum_const_zero,zero_ne_one] at sum
  obtain ⟨i,hi⟩ := pos
  have le : f i≤1 := sum ▸ Finset.single_le_sum (f:=f) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have eq : f i=1 := by omega
  have rem := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [sum,eq] at rem
  refine ⟨i,eq,fun j ji=>?_⟩
  have mem : j∈(Finset.univ : Finset I).erase i := Finset.mem_erase.mpr ⟨ji,Finset.mem_univ _⟩
  have jel := Finset.single_le_sum (f:=f) (fun _ _=>Nat.zero_le _) mem
  omega

/-- At a simple zero of the reduced, nonzero branch product, exactly one
irreducible branch factor crosses the fibre and the specialized
weighted discriminant has precisely that factor's original weight. -/
theorem simple_branch_weight (δ : (Polynomial (Polynomial k))) (nz : δ≠0) (z x : k)
    (good : (branchProduct δ).map (evalRingHom z)≠0)
    (simple : ((branchProduct δ).map (evalRingHom z)).rootMultiplicity x=1) :
    ∃ i : branchFactors δ, (((i:(Polynomial (Polynomial k))).map (evalRingHom z)).rootMultiplicity x=1) ∧
      (δ.map (evalRingHom z)).rootMultiplicity x=branchWeight δ i ∧
      emultiplicity (i:(Polynomial (Polynomial k))) δ=(branchWeight δ i:ℕ∞) := by
  classical
  let f (i : branchFactors δ) := (i:(Polynomial (Polynomial k))).map (evalRingHom z)
  let m (i : branchFactors δ) := (f i).rootMultiplicity x
  have gn : (∏ i,f i)≠0 := by
    simpa only [branchProduct,Polynomial.map_prod,f] using good
  have fn (i : branchFactors δ) : f i≠0 := prod_ne_zero_iff.mp gn _ (Finset.mem_univ _)
  have eq : (∑ i,m i)=1 := by
    have h := Lower6960.BranchIndex.mult_product f (fun _=>1) Finset.univ (fun i _=>fn i) x
    simp only [pow_one,one_mul] at h
    exact h.symm.trans (by simpa only [branchProduct,Polynomial.map_prod,f] using simple)
  obtain ⟨i,hi,other⟩ := unique_sum_one m eq
  let W := ∏ j : branchFactors δ,(f j)^branchWeight δ j
  have wn : W≠0 := prod_ne_zero_iff.mpr fun i _=>pow_ne_zero _ (fn i)
  have assoc : Associated W (δ.map (evalRingHom z)) := by
    have h := (branch_weighted_product δ nz).map (mapRingHom (evalRingHom z))
    simpa only [coe_mapRingHom,Polynomial.map_prod,Polynomial.map_pow,f,W] using h
  have δn : δ.map (evalRingHom z)≠0 := by
    intro zero
    exact wn (zero_dvd_iff.mp (zero ▸ assoc.dvd'))
  have mult_eq : (δ.map (evalRingHom z)).rootMultiplicity x=W.rootMultiplicity x := by
    apply le_antisymm
    · exact (le_rootMultiplicity_iff wn).mpr (((δ.map (evalRingHom z)).pow_rootMultiplicity_dvd x).trans assoc.dvd')
    · exact (le_rootMultiplicity_iff δn).mpr ((W.pow_rootMultiplicity_dvd x).trans assoc.dvd)
  refine ⟨i,hi,?_,?_⟩
  · rw [mult_eq,show W=∏ j,(f j)^branchWeight δ j from rfl,
      Lower6960.BranchIndex.mult_product _ _ _ (fun j _=>fn j)]
    change (∑ j,branchWeight δ j*m j)=branchWeight δ i
    rw [Finset.sum_eq_single i,hi,mul_one]
    · intro j _ ji
      rw [other j ji,mul_zero]
    · simp
  · have norm : normalize (i:(Polynomial (Polynomial k)))=(i:(Polynomial (Polynomial k))) :=
      normalize_normalized_factor _ (Multiset.mem_toFinset.mp i.property)
    rw [emultiplicity_eq_count_normalizedFactors (branchFactor_prime δ i).irreducible nz,norm]
    rfl

#print axioms simple_branch_weight
end
end Lower6960.CollisionTame
