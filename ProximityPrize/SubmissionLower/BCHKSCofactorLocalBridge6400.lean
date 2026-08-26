import ProximityPrize.SubmissionLower.BCHKSCofactorOwnerLedger6400
import ProximityPrize.SubmissionLower.BCHKSWeightedFactorCaps
import ProximityPrize.SubmissionLower.BCHKSTailoredRepeatedRepair6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSCofactorLocalBridge6400

open BCHKSSubstitutionVanish
open BCHKSWeightedSubstitution
open BCHKSLocalValuation6400
open BCHKSTailoredRepeatedRepair6400
open WeightedFactorCaps

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-!
The algebraic bridge behind the full cofactor owner ledger.

If `Q = C * R^e` has interpolation order `m` at a received point and
`R` has exact local order `nu` there, additivity of local order gives

`m <= localOrder C + e * nu`.

After specializing `Z=z`, a matching degree-`k` polynomial turns the local
order of `C` into ordinary `X`-root multiplicity of `triEval C z P`.  If
that polynomial is nonzero, root counting over all agreement coordinates
therefore retains the full `m * card A` term.  The final theorem combines
this with exact additivity of the `(1,k)` support weight.
-/

/-- Local order remaining in a cofactor of a repeated owner. -/
theorem localOrder_cofactor_add_mul_ge
    {A : Type*} [CommSemiring A] [IsDomain A]
    (C R : Polynomial (Polynomial A)) (e m nu : Nat)
    (hC : C ≠ 0) (hR : R ≠ 0)
    (hvan : LocalVanish (C * R ^ e) m)
    (hRorder : localOrder R = nu) :
    m <= localOrder C + e * nu := by
  have hRpow : R ^ e ≠ 0 := pow_ne_zero e hR
  have hprod : C * R ^ e ≠ 0 := mul_ne_zero hC hRpow
  have h := (localVanish_iff_le_localOrder hprod m).mp hvan
  rw [localOrder_mul hC hRpow,
    localOrder_pow R e nu hR hRorder] at h
  exact h

/-- A local order over `F[Z]` survives specialization and a matching
polynomial substitution as ordinary root multiplicity in `X`. -/
theorem localOrder_shift_le_rootMultiplicity_triEval
    {F : Type} [Field F]
    (C : Polynomial (Polynomial (Polynomial F)))
    (omega z : F) (yZ P : Polynomial F)
    (hC : C ≠ 0)
    (hmatch : Polynomial.eval omega P = Polynomial.eval z yZ)
    (htri : triEval C z P ≠ 0) :
    localOrder (Polynomial.Bivariate.shift C (Polynomial.C omega) yZ) <=
      (triEval C z P).rootMultiplicity omega := by
  let mu := localOrder
    (Polynomial.Bivariate.shift C (Polynomial.C omega) yZ)
  have hshift :
      Polynomial.Bivariate.shift C (Polynomial.C omega) yZ ≠ 0 :=
    Polynomial.Bivariate.shift_ne_zero C (Polynomial.C omega) yZ hC
  have hvan : LocalVanish
      (Polynomial.Bivariate.shift C (Polynomial.C omega) yZ) mu :=
    (localVanish_iff_le_localOrder hshift mu).mpr (by simp [mu])
  apply rootMultiplicity_triEval_ge_of_shift_coeff_zero
    C omega z yZ P mu
  · intro s t h hst
    have hcoeff := hvan s t hst
    simp [hcoeff]
  · exact hmatch
  · exact htri

/-- Summed local product order plus root counting for the specialized
cofactor.  This theorem does not clip `e * nu i`; retaining the original
untruncated inequality is what preserves the decisive extra-cardinality
term. -/
theorem cofactor_root_count_of_local_orders
    {F : Type} {iota : Type*} [Field F] [DecidableEq F] [DecidableEq iota]
    (Q C R : Polynomial (Polynomial (Polynomial F)))
    (e m : Nat) (z : F) (P : Polynomial F)
    (omega : iota ↪ F) (A : Finset iota)
    (yZ : iota -> Polynomial F) (nu : iota -> Nat)
    (hQ : Q = C * R ^ e)
    (hC : C ≠ 0) (hR : R ≠ 0)
    (htri : triEval C z P ≠ 0)
    (hvan : ∀ i ∈ A,
      LocalVanish
        (Polynomial.Bivariate.shift Q (Polynomial.C (omega i)) (yZ i)) m)
    (hRorder : ∀ i ∈ A,
      localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C (omega i)) (yZ i)) =
          nu i)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i)) :
    m * A.card <= (triEval C z P).natDegree + e * (∑ i ∈ A, nu i) := by
  let cOrder : iota -> Nat := fun i =>
    localOrder
      (Polynomial.Bivariate.shift C (Polynomial.C (omega i)) (yZ i))
  have hCroot : ∀ i ∈ A,
      cOrder i <= (triEval C z P).rootMultiplicity (omega i) := by
    intro i hi
    exact localOrder_shift_le_rootMultiplicity_triEval
      C (omega i) z (yZ i) P hC (hmatch i hi) htri
  have hCsum : (∑ i ∈ A, cOrder i) <= (triEval C z P).natDegree :=
    sum_le_natDegree_of_rootMultiplicity
      (triEval C z P) omega A cOrder hCroot
  have hpoint : ∀ i ∈ A, m <= cOrder i + e * nu i := by
    intro i hi
    let Ci := Polynomial.Bivariate.shift C
      (Polynomial.C (omega i)) (yZ i)
    let Ri := Polynomial.Bivariate.shift R
      (Polynomial.C (omega i)) (yZ i)
    have hCi : Ci ≠ 0 :=
      Polynomial.Bivariate.shift_ne_zero C
        (Polynomial.C (omega i)) (yZ i) hC
    have hRi : Ri ≠ 0 :=
      Polynomial.Bivariate.shift_ne_zero R
        (Polynomial.C (omega i)) (yZ i) hR
    have hshift :
        Polynomial.Bivariate.shift Q (Polynomial.C (omega i)) (yZ i) =
          Ci * Ri ^ e := by
      rw [hQ]
      simp [Ci, Ri, Polynomial.Bivariate.shift]
    have hlocal : LocalVanish (Ci * Ri ^ e) m := by
      rw [← hshift]
      exact hvan i hi
    exact localOrder_cofactor_add_mul_ge Ci Ri e m (nu i)
      hCi hRi hlocal (by simpa [Ri] using hRorder i hi)
  calc
    m * A.card = ∑ i ∈ A, m := by simp [Nat.mul_comm]
    _ <= ∑ i ∈ A, (cOrder i + e * nu i) :=
      Finset.sum_le_sum fun i hi => hpoint i hi
    _ = (∑ i ∈ A, cOrder i) + e * (∑ i ∈ A, nu i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ <= (triEval C z P).natDegree + e * (∑ i ∈ A, nu i) :=
      Nat.add_le_add_right hCsum _

/-- Clipped version of `cofactor_root_count_of_local_orders`.  Clipping is
pointwise, before summation, so surplus order at one coordinate cannot pay
for a deficit at another coordinate. -/
theorem cofactor_clipped_root_count_of_local_orders
    {F : Type} {iota : Type*} [Field F] [DecidableEq F] [DecidableEq iota]
    (Q C R : Polynomial (Polynomial (Polynomial F)))
    (e m : Nat) (z : F) (P : Polynomial F)
    (omega : iota ↪ F) (A : Finset iota)
    (yZ : iota -> Polynomial F) (nu : iota -> Nat)
    (hQ : Q = C * R ^ e)
    (hC : C ≠ 0) (hR : R ≠ 0)
    (htri : triEval C z P ≠ 0)
    (hvan : ∀ i ∈ A,
      LocalVanish
        (Polynomial.Bivariate.shift Q (Polynomial.C (omega i)) (yZ i)) m)
    (hRorder : ∀ i ∈ A,
      localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C (omega i)) (yZ i)) =
          nu i)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i)) :
    m * A.card <= (triEval C z P).natDegree +
      (∑ i ∈ A, min m (e * nu i)) := by
  let cOrder : iota -> Nat := fun i =>
    localOrder
      (Polynomial.Bivariate.shift C (Polynomial.C (omega i)) (yZ i))
  have hCroot : ∀ i ∈ A,
      cOrder i <= (triEval C z P).rootMultiplicity (omega i) := by
    intro i hi
    exact localOrder_shift_le_rootMultiplicity_triEval
      C (omega i) z (yZ i) P hC (hmatch i hi) htri
  have hCsum : (∑ i ∈ A, cOrder i) <= (triEval C z P).natDegree :=
    sum_le_natDegree_of_rootMultiplicity
      (triEval C z P) omega A cOrder hCroot
  have hpoint : ∀ i ∈ A, m <= cOrder i + min m (e * nu i) := by
    intro i hi
    let Ci := Polynomial.Bivariate.shift C
      (Polynomial.C (omega i)) (yZ i)
    let Ri := Polynomial.Bivariate.shift R
      (Polynomial.C (omega i)) (yZ i)
    have hCi : Ci ≠ 0 :=
      Polynomial.Bivariate.shift_ne_zero C
        (Polynomial.C (omega i)) (yZ i) hC
    have hRi : Ri ≠ 0 :=
      Polynomial.Bivariate.shift_ne_zero R
        (Polynomial.C (omega i)) (yZ i) hR
    have hshift :
        Polynomial.Bivariate.shift Q (Polynomial.C (omega i)) (yZ i) =
          Ci * Ri ^ e := by
      rw [hQ]
      simp [Ci, Ri, Polynomial.Bivariate.shift]
    have hlocal : LocalVanish (Ci * Ri ^ e) m := by
      rw [← hshift]
      exact hvan i hi
    have hproduct : m <= cOrder i + e * nu i := by
      simpa [cOrder, Ci, Ri] using
        (localOrder_cofactor_add_mul_ge Ci Ri e m (nu i)
          hCi hRi hlocal (by simpa [Ri] using hRorder i hi))
    have hclip := BCHKSCofactorOwnerLedger6400.clipped_cofactor_order_le
      m e (nu i) (cOrder i) hproduct
    omega
  calc
    m * A.card = ∑ i ∈ A, m := by simp [Nat.mul_comm]
    _ <= ∑ i ∈ A, (cOrder i + min m (e * nu i)) :=
      Finset.sum_le_sum fun i hi => hpoint i hi
    _ = (∑ i ∈ A, cOrder i) +
        (∑ i ∈ A, min m (e * nu i)) := by
      rw [Finset.sum_add_distrib]
    _ <= (triEval C z P).natDegree +
        (∑ i ∈ A, min m (e * nu i)) :=
      Nat.add_le_add_right hCsum _

/-- Exact support weight of a nonzero power. -/
theorem weightedSupportDegree_pow
    {A : Type*} [CommSemiring A] [IsDomain A]
    (R : Polynomial (Polynomial A)) (e k : Nat) (hR : R ≠ 0) :
    weightedSupportDegree (R ^ e) k =
      e * weightedSupportDegree R k := by
  induction e with
  | zero =>
      simp only [pow_zero, Nat.zero_mul]
      apply Nat.eq_zero_of_le_zero
      unfold weightedSupportDegree
      apply Finset.sup_le
      intro i hi
      have hcoeff :
          (1 : Polynomial (Polynomial A)).coeff i ≠ 0 :=
        Polynomial.mem_support_iff.mp hi
      have hi0 : i = 0 := by
        by_contra hne
        rw [Polynomial.coeff_one] at hcoeff
        simp [hne] at hcoeff
      subst i
      simp
  | succ e ih =>
      rw [pow_succ,
        weightedSupportDegree_mul (R ^ e) R k (pow_ne_zero e hR) hR,
        ih]
      simp [Nat.succ_mul]

/-- Specialization in `Z` and substitution of a degree-`k` polynomial do
not exceed the weighted support degree. -/
theorem triEval_natDegree_le_weightedSupportDegree
    {F : Type} [Field F]
    (C : Polynomial (Polynomial (Polynomial F)))
    (z : F) (P : Polynomial F) (k : Nat)
    (hP : P.natDegree <= k) :
    (triEval C z P).natDegree <= weightedSupportDegree C k := by
  apply triEval_natDegree_le_of_weighted_X_cap
    C z P k (weightedSupportDegree C k) hP
  intro j a hcoeff
  have houter : C.coeff j ≠ 0 := by
    intro hz
    exact hcoeff (by simp [hz])
  have ha : a <= (C.coeff j).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff
  have hw := coeffWeight_le_of_ne C k j houter
  omega

/-- Quotient root-degree budget from exact additivity of weighted support.
The conclusion is deliberately weak (`<= D`) because the interpolation cap
is strict; this matches the benchmark identity `D + M = m*a`. -/
theorem cofactor_triEval_degree_add_owner_weight_le
    {F : Type} [Field F]
    (Q C R : Polynomial (Polynomial (Polynomial F)))
    (e k D : Nat) (z : F) (P : Polynomial F)
    (hQ : Q = C * R ^ e)
    (hC : C ≠ 0) (hR : R ≠ 0)
    (hP : P.natDegree <= k)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + k * j < D) :
    (triEval C z P).natDegree +
        e * weightedSupportDegree R k <= D := by
  have hRpow : R ^ e ≠ 0 := pow_ne_zero e hR
  have hQne : Q ≠ 0 := by
    rw [hQ]
    exact mul_ne_zero hC hRpow
  have hQweight : weightedSupportDegree Q k < D :=
    weightedSupportDegree_lt_of_coeff_cap Q k D hQne hcap
  have hmul : weightedSupportDegree Q k =
      weightedSupportDegree C k + e * weightedSupportDegree R k := by
    rw [hQ, weightedSupportDegree_mul C (R ^ e) k hC hRpow,
      weightedSupportDegree_pow R e k hR]
  have hCdegree := triEval_natDegree_le_weightedSupportDegree C z P k hP
  omega

/-- End-to-end full cofactor excess ledger for an explicit repeated-factor
decomposition.  Apart from the normalized-factor construction, the only
specialization hypothesis is the necessary one: `C_z(P)` is nonzero.
The global-radical resultant supplies exactly this unique-owner property. -/
theorem full_cofactor_owner_excess_ledger_of_factorization
    {F : Type} {iota : Type*} [Field F] [DecidableEq F] [DecidableEq iota]
    (Q C R : Polynomial (Polynomial (Polynomial F)))
    (e m k D M a : Nat) (z : F) (P : Polynomial F)
    (omega : iota ↪ F) (A : Finset iota)
    (yZ : iota -> Polynomial F) (nu : iota -> Nat)
    (hQ : Q = C * R ^ e)
    (hC : C ≠ 0) (hR : R ≠ 0)
    (htri : triEval C z P ≠ 0)
    (hvan : ∀ i ∈ A,
      LocalVanish
        (Polynomial.Bivariate.shift Q (Polynomial.C (omega i)) (yZ i)) m)
    (hRorder : ∀ i ∈ A,
      localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C (omega i)) (yZ i)) =
          nu i)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree <= k)
    (hcap : ∀ j x, ((Q.coeff j).coeff x) ≠ 0 →
      x + k * j < D)
    (hDM : D + M = m * a)
    (ha : a <= A.card)
    (hw : weightedSupportDegree R k <= ∑ i ∈ A, nu i) :
    m * (A.card - a) + M <=
      e * ((∑ i ∈ A, nu i) - weightedSupportDegree R k) := by
  have hroot := cofactor_root_count_of_local_orders
    Q C R e m z P omega A yZ nu hQ hC hR htri hvan hRorder hmatch
  have hdegree := cofactor_triEval_degree_add_owner_weight_le
    Q C R e k D z P hQ hC hR hP hcap
  exact BCHKSCofactorOwnerLedger6400.full_cofactor_owner_excess_ledger
    m e (weightedSupportDegree R k) D M a A.card
      (∑ i ∈ A, nu i) (triEval C z P).natDegree
      hDM hroot hdegree ha hw

/-- End-to-end clipped cofactor ledger.  The credit on the right is the
actual sum over the same agreement set `A`; no global profile mass is
silently substituted for it. -/
theorem full_clipped_cofactor_owner_ledger_of_factorization
    {F : Type} {iota : Type*} [Field F] [DecidableEq F] [DecidableEq iota]
    (Q C R : Polynomial (Polynomial (Polynomial F)))
    (e m k D M a : Nat) (z : F) (P : Polynomial F)
    (omega : iota ↪ F) (A : Finset iota)
    (yZ : iota -> Polynomial F) (nu : iota -> Nat)
    (hQ : Q = C * R ^ e)
    (hC : C ≠ 0) (hR : R ≠ 0)
    (htri : triEval C z P ≠ 0)
    (hvan : ∀ i ∈ A,
      LocalVanish
        (Polynomial.Bivariate.shift Q (Polynomial.C (omega i)) (yZ i)) m)
    (hRorder : ∀ i ∈ A,
      localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C (omega i)) (yZ i)) =
          nu i)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree <= k)
    (hcap : ∀ j x, ((Q.coeff j).coeff x) ≠ 0 ->
      x + k * j < D)
    (hDM : D + M = m * a) :
    m * A.card + e * weightedSupportDegree R k + M <=
      m * a + (∑ i ∈ A, min m (e * nu i)) := by
  have hroot := cofactor_clipped_root_count_of_local_orders
    Q C R e m z P omega A yZ nu hQ hC hR htri hvan hRorder hmatch
  have hdegree := cofactor_triEval_degree_add_owner_weight_le
    Q C R e k D z P hQ hC hR hP hcap
  exact BCHKSCofactorOwnerLedger6400.full_clipped_cofactor_owner_ledger
    m e (weightedSupportDegree R k) D M a A.card
      (∑ i ∈ A, min m (e * nu i)) (triEval C z P).natDegree
      hDM hroot hdegree

/-- At exactly the interpolation baseline number of agreements, the factor
weight and margin must be paid by pointwise clipped owner order. -/
theorem clipped_credit_ge_factor_cost_of_factorization
    {F : Type} {iota : Type*} [Field F] [DecidableEq F] [DecidableEq iota]
    (Q C R : Polynomial (Polynomial (Polynomial F)))
    (e m k D M a : Nat) (z : F) (P : Polynomial F)
    (omega : iota ↪ F) (A : Finset iota)
    (yZ : iota -> Polynomial F) (nu : iota -> Nat)
    (hQ : Q = C * R ^ e)
    (hC : C ≠ 0) (hR : R ≠ 0)
    (htri : triEval C z P ≠ 0)
    (hvan : ∀ i ∈ A,
      LocalVanish
        (Polynomial.Bivariate.shift Q (Polynomial.C (omega i)) (yZ i)) m)
    (hRorder : ∀ i ∈ A,
      localOrder
        (Polynomial.Bivariate.shift R (Polynomial.C (omega i)) (yZ i)) =
          nu i)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree <= k)
    (hcap : ∀ j x, ((Q.coeff j).coeff x) ≠ 0 ->
      x + k * j < D)
    (hDM : D + M = m * a)
    (hcard : A.card = a) :
    e * weightedSupportDegree R k + M <=
      ∑ i ∈ A, min m (e * nu i) := by
  have hmain := full_clipped_cofactor_owner_ledger_of_factorization
    Q C R e m k D M a z P omega A yZ nu hQ hC hR htri hvan
      hRorder hmatch hP hcap hDM
  rw [hcard] at hmain
  omega

end BCHKSCofactorLocalBridge6400
end ProximityPrize.SubmissionLower
