import ProximityPrize.SubmissionLower.R6960CollisionTameWeights
import ProximityPrize.SubmissionLower.R6960NormalizedFiber
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Squarefree.Basic

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Algebra Polynomial NormalizedFiber Module CollisionTame UniqueFactorizationMonoid
open scoped Polynomial TensorProduct

variable {k : Type} [Field k] [DecidableEq k]

theorem branch_squarefree (P:k[X][X]) : Squarefree (branchProduct P) := by
  let S := branchFactors P
  have eq : branchProduct P=S.val.prod := by
    calc branchProduct P = ∏ i∈S,i := Finset.prod_coe_sort S id
         _ = S.val.prod := by simp only [Finset.prod,Multiset.map_id']
  have nz : branchProduct P≠0 := Finset.prod_ne_zero_iff.mpr fun i _=>(branchFactor_prime P i).ne_zero
  apply (squarefree_iff_nodup_normalizedFactors nz).mpr
  rw [eq,normalizedFactors_prod_eq _ (fun x hx=>irreducible_of_normalized_factor x
    (Multiset.mem_toFinset.mp (show x∈S from hx)))]
  have norm : S.val.map normalize=S.val := by
    calc S.val.map normalize = S.val.map id :=
           Multiset.map_congr rfl fun x hx=>normalize_normalized_factor x
             (Multiset.mem_toFinset.mp (show x∈S from hx))
         _ = S.val := Multiset.map_id' _
  rw [norm]
  exact S.nodup

theorem branch_dvd (P:k[X][X]) (nz:P≠0) : branchProduct P∣P := by
  apply Dvd.dvd.trans _ (branch_weighted_product P nz).dvd
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  exact dvd_pow_self _ (branch_weight_pos P i).ne'

private theorem map_trailing {A B:Type*} [Semiring A] [Semiring B] [Nontrivial B]
    (j:A→+*B) (p:A[X]) (keep:j p.trailingCoeff≠0) :
    p.map j≠0 ∧ (p.map j).natTrailingDegree=p.natTrailingDegree := by
  have c : (p.map j).coeff p.natTrailingDegree≠0 := by
    rw [coeff_map]
    exact keep
  have n : p.map j≠0 := by intro h; rw [h,coeff_zero] at c; exact c rfl
  refine ⟨n,le_antisymm (natTrailingDegree_le_of_ne_zero c) ?_⟩
  by_contra! lt
  have h : p.coeff (p.map j).natTrailingDegree=0 := coeff_eq_zero_of_lt_natTrailingDegree lt
  exact (coeff_natTrailingDegree_ne_zero.mpr n) (by rw [coeff_map,h,map_zero])

/-- Excluding the roots of the actual first nonzero coefficient of the
reciprocal-chart discriminant makes the abscissa boundary either
unbranched or a simple reduced crossing. Its seed degree is at most the
seed degree of the original discriminant. -/
theorem boundary_seed_polynomial (δ : Plane k) (nz : δ≠0) :
    let avoid := (Bivariate.swap δ).trailingCoeff
    avoid≠0 ∧ avoid.natDegree≤δ.natDegree ∧
      ∀ z:k, avoid.eval z≠0 →
        ((branchProduct (Bivariate.swap δ)).map (evalRingHom z))≠0 ∧
        ((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity 0≤1 := by
  let P := Bivariate.swap δ
  have np : P≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nz
  have degree : P.trailingCoeff.natDegree≤δ.natDegree := by
    have h := CurvatureSquares.coeff_height P P.natTrailingDegree
    change P.trailingCoeff.natDegree≤(Bivariate.swap (Bivariate.swap δ)).natDegree at h
    rwa [Bivariate.swap_swap_apply] at h
  refine ⟨coeff_natTrailingDegree_ne_zero.mpr np,degree,?_⟩
  intro z keep
  let B := branchProduct P
  let j := evalRingHom z
  obtain ⟨Q,eq⟩ := branch_dvd P np
  have keepB : j B.trailingCoeff≠0 := by
    intro zero
    change j P.trailingCoeff≠0 at keep
    apply keep
    rw [eq,trailingCoeff_mul,map_mul,zero,zero_mul]
  obtain ⟨good,tr⟩ := map_trailing j B keepB
  refine ⟨good,?_⟩
  rw [rootMultiplicity_eq_natTrailingDegree',tr]
  by_contra! large
  have div : (Polynomial.X:k[X][X])^2∣B :=
    X_pow_dvd_iff.mpr fun i hi=>coeff_eq_zero_of_lt_natTrailingDegree (hi.trans_le large)
  exact (irreducible_X.not_isUnit) ((branch_squarefree P) _ (by simpa only [pow_two] using div))

#print axioms boundary_seed_polynomial
end
end Lower6960.CollisionMarked
