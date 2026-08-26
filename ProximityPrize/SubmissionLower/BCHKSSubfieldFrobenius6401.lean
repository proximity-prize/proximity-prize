import ProximityPrize.SubmissionLower.BCHKSParameters6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSSubfieldFrobenius6401
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
theorem eval_map_eq_map_eval_of_fixed
    {K : Type*} [Field K] (sigma : K →+* K)
    (P : Polynomial K) (x : K) (hx : sigma x = x) :
    Polynomial.eval x (P.map sigma) = sigma (Polynomial.eval x P) := by
  calc
    Polynomial.eval x (P.map sigma) =
        Polynomial.eval (sigma x) (P.map sigma) := by rw [hx]
    _ = sigma (Polynomial.eval x P) :=
      Polynomial.eval_map_apply (p := P) sigma x
theorem eval_map_eq_of_eval_eq_of_fixed
    {K : Type*} [Field K] (sigma : K →+* K)
    (P : Polynomial K) (x y : K) (hx : sigma x = x)
    (hxy : Polynomial.eval x P = y) :
    Polynomial.eval x (P.map sigma) = sigma y := by
  rw [eval_map_eq_map_eval_of_fixed sigma P x hx, hxy]
theorem map_affine_challenge
    {K : Type*} [Field K] (sigma : K →+* K) (u0 u1 z : K) :
    sigma (u0 + z * u1) = sigma u0 + sigma z * sigma u1 := by
  simp
noncomputable def qAffinePolynomial
    {L : Type*} [Field L] (q : Nat) (a b c : L) : Polynomial L :=
  Polynomial.C a * Polynomial.X ^ q +
    Polynomial.C b * Polynomial.X + Polynomial.C c
theorem qAffinePolynomial_natDegree_le
    {L : Type*} [Field L] (q : Nat) (a b c : L) (hq : 0 < q) :
    (qAffinePolynomial q a b c).natDegree ≤ q := by
  unfold qAffinePolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · calc
        (Polynomial.C a * Polynomial.X ^ q).natDegree ≤
            (Polynomial.X ^ q : Polynomial L).natDegree :=
          Polynomial.natDegree_C_mul_le a _
        _ = q := by simp
    · calc
        (Polynomial.C b * Polynomial.X).natDegree ≤
            (Polynomial.X : Polynomial L).natDegree :=
          Polynomial.natDegree_C_mul_le b _
        _ = 1 := by simp
        _ ≤ q := hq
  · simp
theorem qAffinePolynomial_rootSet_card_le
    {L : Type*} [Field L] [DecidableEq L]
    (q : Nat) (a b c : L) (T : Finset L) (hq : 0 < q)
    (hnonzero : qAffinePolynomial q a b c ≠ 0)
    (hroot : ∀ x ∈ T, a * x ^ q + b * x + c = 0) :
    T.card ≤ q := by
  apply (Polynomial.card_le_degree_of_subset_roots
    (p := qAffinePolynomial q a b c) ?_).trans
    (qAffinePolynomial_natDegree_le q a b c hq)
  intro x hx
  rw [Polynomial.mem_roots hnonzero, Polynomial.IsRoot]
  simpa [qAffinePolynomial] using hroot x hx
def domainSize6401 : Nat := 262144
def messageDimension6401 : Nat := 131072
def maxMessageDegree6401 : Nat := messageDimension6401 - 1
def extensionDegree6401 : Nat := 6
def koalaBearCard6401 : Nat := 2130706433
def twoFrobeniusD6401 : Nat :=
  (domainSize6401 - messageDimension6401 + 1) / 3
def sixFrobeniusD6401 : Nat :=
  (domainSize6401 - messageDimension6401 + 1) / 7
lemma twoFrobenius_rectangle_exact6401 :
    twoFrobeniusD6401 = 43691 ∧
      (twoFrobeniusD6401 + messageDimension6401) +
          2 * (twoFrobeniusD6401 + 1) = 262147 ∧
      domainSize6401 <
        (twoFrobeniusD6401 + messageDimension6401) +
          2 * (twoFrobeniusD6401 + 1) ∧
      twoFrobeniusD6401 + maxMessageDegree6401 = 174762 ∧
      bchksAgreements6401 -
          (twoFrobeniusD6401 + maxMessageDegree6401) = 10592 ∧
      3 * bchksErrors6401 ≤
        2 * (domainSize6401 - messageDimension6401) := by
  norm_num [twoFrobeniusD6401, domainSize6401,
    messageDimension6401, maxMessageDegree6401,
    bchksAgreements6401, bchksErrors6401]
lemma sixFrobenius_rectangle_exact6401 :
    sixFrobeniusD6401 = 18724 ∧
      (sixFrobeniusD6401 + messageDimension6401) +
          6 * (sixFrobeniusD6401 + 1) = 262146 ∧
      domainSize6401 <
        (sixFrobeniusD6401 + messageDimension6401) +
          6 * (sixFrobeniusD6401 + 1) ∧
      sixFrobeniusD6401 + maxMessageDegree6401 = 149795 ∧
      bchksAgreements6401 -
          (sixFrobeniusD6401 + maxMessageDegree6401) = 35559 ∧
      7 * bchksErrors6401 ≤
        6 * (domainSize6401 - messageDimension6401) := by
  norm_num [sixFrobeniusD6401, domainSize6401,
    messageDimension6401, maxMessageDegree6401,
    bchksAgreements6401, bchksErrors6401]
lemma oneFrobeniusBranch_fits_ownerBudget6401 :
    koalaBearCard6401 * (bchksErrors6401 + 1) <
      274980700000000000 := by
  norm_num [koalaBearCard6401, bchksErrors6401]
end BCHKSSubfieldFrobenius6401
end ProximityPrize.SubmissionLower
