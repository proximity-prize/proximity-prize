import ProximityPrize.SubmissionLower.R6960BranchIndex
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators

variable {k : Type} [Field k] [DecidableEq k]

/-- The distinct normalized branch factors of the actual discriminant. -/
def branchFactors (δ : k[X][X]) : Finset (k[X][X]) := (normalizedFactors δ).toFinset

def branchWeight (δ : k[X][X]) (i : branchFactors δ) : ℕ := (normalizedFactors δ).count (i:k[X][X])

def branchProduct (δ : k[X][X]) : k[X][X] := ∏ i : branchFactors δ,(i:k[X][X])

theorem branch_weight_pos (δ : k[X][X]) (i : branchFactors δ) : 0<branchWeight δ i :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp i.property)

theorem branchFactor_prime (δ : k[X][X]) (i : branchFactors δ) : Prime (i:k[X][X]) :=
  prime_of_normalized_factor _ (Multiset.mem_toFinset.mp i.property)

theorem branch_weighted_product (δ : k[X][X]) (nz : δ≠0) :
    Associated (∏ i : branchFactors δ,(i:k[X][X])^branchWeight δ i) δ := by
  unfold branchWeight
  rw [Finset.prod_coe_sort (branchFactors δ) (fun p : k[X][X]=>p^(normalizedFactors δ).count p)]
  change Associated (∏ p∈(normalizedFactors δ).toFinset,p^(normalizedFactors δ).count p) δ
  rw [←Finset.prod_multiset_count]
  exact prod_normalizedFactors nz

/-- Both weighted sums used by the collision bound are exactly the
corresponding affine degrees of the original discriminant generator. -/
theorem branch_weighted_degrees (δ : k[X][X]) (nz : δ≠0) :
    (∑ i : branchFactors δ,branchWeight δ i*(i:k[X][X]).natDegree)=δ.natDegree ∧
    (∑ i : branchFactors δ,branchWeight δ i*CurvatureSquares.height (i:k[X][X]))=
      CurvatureSquares.height δ := by
  have factor := branch_weighted_product δ nz
  constructor
  · have eq := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated factor)
    rw [natDegree_prod _ _ (fun i _=>pow_ne_zero _ (branchFactor_prime δ i).ne_zero)] at eq
    simpa only [natDegree_pow] using eq
  · have eq := factor.map Bivariate.swap.toRingHom
    have swap : Bivariate.swap (∏ i : branchFactors δ,(i:k[X][X])^branchWeight δ i)=
        ∏ i : branchFactors δ,(Bivariate.swap (i:k[X][X]))^branchWeight δ i := by
      rw [map_prod]
      simp only [map_pow]
    change Associated (Bivariate.swap (∏ i : branchFactors δ,(i:k[X][X])^branchWeight δ i))
      (Bivariate.swap δ) at eq
    rw [swap] at eq
    have deg := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated eq)
    rw [natDegree_prod _ _ (fun i _=>pow_ne_zero _
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (branchFactor_prime δ i).ne_zero))] at deg
    simpa only [natDegree_pow,CurvatureSquares.height] using deg

/-- Apply the collision accountant with weights taken from the actual
discriminant. It suffices to bound its ordinary bidegrees and supply the
support and separability receipts for its reduced branch product. -/
theorem branch_index_of_discriminant [IsAlgClosed k]
    (δ : k[X][X]) (nz : δ≠0)
    (sep : ((branchProduct δ).map (algebraMap k[X] (FractionRing k[X]))).Separable)
    (T : Finset k) (good : ∀ z∈T,(branchProduct δ).map (evalRingHom z)≠0)
    (idx : k→k[X]) (supported : ∀ z∈T,∀ x∈(idx z).roots,
      2≤((branchProduct δ).map (evalRingHom z)).rootMultiplicity x)
    (disc : ∀ z∈T,idx z^2∣δ.map (evalRingHom z))
    {s t : ℕ} (xcap : δ.natDegree≤2*s) (zcap : CurvatureSquares.height δ≤2*t) :
    (∑ z∈T,(idx z).natDegree)≤8*s*t := by
  let f : branchFactors δ→k[X][X] := Subtype.val
  have weights := branch_weighted_degrees δ nz
  refine BranchIndex.index_degree f (branchWeight δ) (branch_weight_pos δ) (branchProduct δ) rfl
    sep T good idx supported ?_ (weights.1 ▸ xcap) (weights.2 ▸ zcap)
  intro z hz
  have factor := (branch_weighted_product δ nz).map (Polynomial.mapRingHom (evalRingHom z))
  change Associated ((∏ i : branchFactors δ,f i^branchWeight δ i).map (evalRingHom z))
    (δ.map (evalRingHom z)) at factor
  have dp : idx z^2∣(∏ i : branchFactors δ,f i^branchWeight δ i).map (evalRingHom z) :=
    (disc z hz).trans factor.dvd'
  simpa only [Polynomial.map_prod,Polynomial.map_pow] using dp

#print axioms branch_weighted_degrees
#print axioms branch_index_of_discriminant
end
end Lower6960.CollisionTame
