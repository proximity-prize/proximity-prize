/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# The almost-cyclotomic interface at the first surviving fold degree

The collision-curve audit excludes full-fibre folds through degree five.  At
degree six the extremal configuration has 85 disjoint full fibres on 510 of
the 512 points of the inner multiplicative subgroup.  This file records two
exact consequences of that configuration.

First, normalize the fibre pencil as `A - t B`, with every full fibre monic of
degree six.  Its constant coefficient is the product of its six roots.  Hence,
when those roots lie in `mu_512`, the affine label

`A(0) - t * B(0)`

also lies in `mu_512`.  If `B(0) != 0`, this relabeling is injective, so the
85 fibre labels themselves can be normalized into the same subgroup.

Second, multiplying the 85 fibre polynomials and the two missing linear
factors gives a monic degree-512 divisor of `X^512 - 1`.  It must therefore be
exactly `X^512 - 1`:

`(X-a)(X-b) * product_t (A-tB) = X^512 - 1`.

This is the concrete rigidity target for the degree-six route.  A useful
upper-bound improvement can now come from classifying these almost
decompositions, or from proving that their normalized rational map cannot
send 510 of 512 subgroup points back into the subgroup.  No lower-challenge
module is imported.
-/

namespace ProximityPrize.SubmissionUpper.SexticAlmostDecomposition

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

def productLabel (a0 b0 t : F) : F := a0 - t * b0

/-- The constant coefficient of a monic split sextic is the product of its
six roots (the sign is positive because six is even). -/
theorem product_label_eq_of_split_sextic
    (A B : Polynomial F) (a0 b0 t : F) (roots : Fin 6 → F)
    (hA0 : A.eval 0 = a0) (hB0 : B.eval 0 = b0)
    (hsplit : A - Polynomial.C t * B =
      ∏ i, (Polynomial.X - Polynomial.C (roots i))) :
    productLabel a0 b0 t = ∏ i, roots i := by
  have hzero := congrArg (fun P : Polynomial F => P.eval 0) hsplit
  have hsign : (-1 : F) ^ 6 = 1 := by ring
  simpa [productLabel, hA0, hB0, Polynomial.eval_prod, Finset.prod_neg, hsign]
    using hzero

/-- Products preserve membership in the order-512 subgroup. -/
theorem product_label_mem_subgroup
    (a0 b0 t : F) (roots : Fin 6 → F)
    (hroots : ∀ i, roots i ^ 512 = 1)
    (hconstant : productLabel a0 b0 t = ∏ i, roots i) :
    productLabel a0 b0 t ^ 512 = 1 := by
  rw [hconstant, ← Finset.prod_pow]
  simp [hroots]

/-- When the pencil denominator has nonzero constant coefficient, product
labels retain all distinctions between fibre parameters. -/
theorem productLabel_injective (a0 : F) {b0 : F} (hb0 : b0 ≠ 0) :
    Function.Injective (productLabel a0 b0) := by
  intro s t hst
  apply mul_right_cancel₀ hb0
  exact sub_right_inj.mp hst

theorem normalized_label_card [DecidableEq F]
    (a0 : F) {b0 : F} (hb0 : b0 ≠ 0)
    (labels : Finset F) :
    (labels.image (productLabel a0 b0)).card = labels.card := by
  classical
  exact Finset.card_image_of_injective labels (productLabel_injective a0 hb0)

noncomputable def fibreProduct (A B : Polynomial F) (labels : Finset F) : Polynomial F :=
  ∏ t ∈ labels, (A - Polynomial.C t * B)

theorem fibreProduct_monic (A B : Polynomial F) (labels : Finset F)
    (hfibre : ∀ t ∈ labels, (A - Polynomial.C t * B).Monic) :
    (fibreProduct A B labels).Monic := by
  classical
  exact monic_prod_of_monic labels (fun t => A - Polynomial.C t * B) hfibre

theorem fibreProduct_natDegree (A B : Polynomial F) (labels : Finset F)
    (hfibre : ∀ t ∈ labels, (A - Polynomial.C t * B).Monic)
    (hdegree : ∀ t ∈ labels, (A - Polynomial.C t * B).natDegree = 6) :
    (fibreProduct A B labels).natDegree = labels.card * 6 := by
  classical
  rw [fibreProduct, natDegree_prod_of_monic labels
    (fun t => A - Polynomial.C t * B) hfibre]
  calc
    (∑ t ∈ labels, (A - Polynomial.C t * B).natDegree) = ∑ _t ∈ labels, 6 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hdegree t ht
    _ = labels.card * 6 := by simp

noncomputable def missingPairProduct (a b : F) (R : Polynomial F) : Polynomial F :=
  (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) * R

theorem missingPairProduct_monic (a b : F) {R : Polynomial F} (hR : R.Monic) :
    (missingPairProduct a b R).Monic := by
  simpa [missingPairProduct] using
    ((monic_X_sub_C a).mul (monic_X_sub_C b)).mul hR

theorem missingPairProduct_natDegree (a b : F) {R : Polynomial F}
    (hR : R.Monic) (hdegree : R.natDegree = 510) :
    (missingPairProduct a b R).natDegree = 512 := by
  simp only [missingPairProduct]
  rw [
    ((monic_X_sub_C a).mul (monic_X_sub_C b)).natDegree_mul hR,
    (monic_X_sub_C a).natDegree_mul (monic_X_sub_C b),
    natDegree_X_sub_C, natDegree_X_sub_C, hdegree]

set_option maxRecDepth 10000 in
/-- A monic degree-512 product supported on the 512th roots of unity is the
cyclotomic binomial itself. -/
theorem almost_decomposition_eq_cyclotomic
    (a b : F) {R : Polynomial F} (hR : R.Monic) (hdegree : R.natDegree = 510)
    (hdiv : missingPairProduct a b R ∣
      (Polynomial.X : Polynomial F) ^ 512 - Polynomial.C 1) :
    missingPairProduct a b R =
      (Polynomial.X : Polynomial F) ^ 512 - Polynomial.C 1 := by
  have hleft : (missingPairProduct a b R).Monic :=
    missingPairProduct_monic a b hR
  have hright : ((Polynomial.X : Polynomial F) ^ 512 - Polynomial.C (1 : F)).Monic := by
    exact monic_X_pow_sub_C (R := F) 1 (by norm_num : (512 : Nat) ≠ 0)
  have hleftDegree : (missingPairProduct a b R).natDegree = 512 :=
    missingPairProduct_natDegree a b hR hdegree
  have hrightDegree :
      ((Polynomial.X : Polynomial F) ^ 512 - Polynomial.C (1 : F)).natDegree = 512 := by
    rw [natDegree_X_pow_sub_C]
  have hdegreeLe :
      ((Polynomial.X : Polynomial F) ^ 512 - Polynomial.C (1 : F)).natDegree ≤
        (missingPairProduct a b R).natDegree := by
    rw [hrightDegree, hleftDegree]
  exact (eq_of_monic_of_dvd_of_natDegree_le hleft hright hdiv
    hdegreeLe).symm

/-- The exact 85-by-6 ledger feeding the almost-decomposition identity. -/
theorem sextic_fibre_degree_receipt : 85 * 6 = 510 := by norm_num

theorem two_missing_points_receipt : 2 + 85 * 6 = 512 := by norm_num

def subgroupOrder : ℕ := 512
def collisionBidegree : ℕ := 5
def boundaryEulerCap : ℕ := 46
def requiredOrderedCollisions : ℕ := 2550
def baseCharacteristic : ℕ := 2130706433

/-- An Euler-characteristic improvement from 50 to 46 is exactly enough to
cross the degree-six collision threshold in the first Corvaja--Zannier
branch. -/
theorem chi46_first_branch_below_required :
    54 * subgroupOrder ^ 2 * collisionBidegree ^ 2 * boundaryEulerCap <
      requiredOrderedCollisions ^ 3 := by
  norm_num [subgroupOrder, collisionBidegree, boundaryEulerCap,
    requiredOrderedCollisions]

theorem chi46_second_branch_below_required :
    12 * subgroupOrder ^ 2 * collisionBidegree ^ 2 <
      requiredOrderedCollisions * baseCharacteristic := by
  norm_num [subgroupOrder, collisionBidegree, requiredOrderedCollisions,
    baseCharacteristic]

/-- Numerical consumer for any geometric argument that lowers the relevant
Euler characteristic to at most 46. -/
theorem no_85_full_sextic_fibres_of_strict_collision_cap
    (collisionPoints : ℕ)
    (hfull : requiredOrderedCollisions ≤ collisionPoints)
    (hcurve : collisionPoints < requiredOrderedCollisions) : False := by
  omega

/-- If zero and infinity are poles whose multiplicities sum to at least
three, the pole-fibre branch count gives at most 15 boundary punctures; with
the generic genus cap 16 this yields Euler characteristic 45.  The geometric
branch-count premise remains external to this numerical receipt. -/
theorem ramified_boundary_receipt : 24 - 3 * 3 = 15 ∧ 2 * 16 - 2 + 15 = 45 := by
  norm_num

end ProximityPrize.SubmissionUpper.SexticAlmostDecomposition

#print axioms ProximityPrize.SubmissionUpper.SexticAlmostDecomposition.product_label_mem_subgroup
#print axioms ProximityPrize.SubmissionUpper.SexticAlmostDecomposition.almost_decomposition_eq_cyclotomic
