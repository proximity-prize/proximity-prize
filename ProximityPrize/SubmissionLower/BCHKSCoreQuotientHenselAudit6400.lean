import ProximityPrize.SubmissionLower.BCHKSTripleCoreMomentAudit6400
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteObstruction

namespace ProximityPrize.SubmissionLower
namespace BCHKSCoreQuotientHenselAudit6400

open Polynomial Polynomial.Bivariate
open BCHKSHybridHighDegreeAudit6400

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
Audit of the common-core quotient followed by universal Hensel lifting.

If a fixed full-order core has codimension `s`, the already compiled core
quotient bridge writes every owner as

`P_z = B0 + z*B1 + G*Q_z`,  with `deg Q_z <= s`.

Substituting `Y = B0 + Z*B1 + G*V` in the owning factor turns `Q_z` into an
exact polynomial root of degree at most `s`.  Thus the universal denominator
exponent is `2*s-1`, rather than `2*131071-1`.  The definitions and elementary
root/degree identities are recorded below.  The exact arithmetic says that
the degree-129 ledger fits through `s=130229`, equivalently as soon as the
fixed core has at least 842 coordinates.  The next value misses.

This is an audit/helper, not a completed selector.  In particular the
64.00 simultaneous center-selection and simple-slope adapters for the
transformed factor remain to be wired.
-/

/-- Embed an `X`-polynomial into the middle-variable polynomial ring, with
no dependence on the coefficient variable `Z`. -/
noncomputable def liftMiddle
    {F : Type*} [Field F] (P : F[X]) : F[X][X] :=
  P.map Polynomial.C

/-- The affine change of the outer root variable
`Y = B0(X) + Z*B1(X) + G(X)*V`. -/
noncomputable def coreRootSubstitution
    {F : Type*} [Field F] (B0 B1 G : F[X]) : F[X][X][Y] :=
  Polynomial.C
      (liftMiddle B0 + Polynomial.C Polynomial.X * liftMiddle B1) +
    Polynomial.C (liftMiddle G) * Polynomial.X

/-- Apply the common-core affine root change to a trivariate factor. -/
noncomputable def coreRootTransform
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) : F[X][X][Y] :=
  R.comp (coreRootSubstitution B0 B1 G)

@[simp]
theorem eval_liftMiddle
    {F : Type*} [Field F] (P : F[X]) (z : F) :
    (liftMiddle P).map (Polynomial.evalRingHom z) = P := by
  simp [liftMiddle]

/-- Specializing the challenge variable turns the symbolic affine change
into the expected change of polynomial root. -/
theorem triSpecializeZ_coreRootSubstitution
    {F : Type*} [Field F] (B0 B1 G : F[X]) (z : F) :
    triSpecializeZ (coreRootSubstitution B0 B1 G) z =
      Polynomial.C (B0 + Polynomial.C z * B1) +
        Polynomial.C G * Polynomial.X := by
  simp [coreRootSubstitution, triSpecializeZ, liftMiddle]

/-- Exact roots survive the common-core change of variables. -/
theorem triEval_coreRootTransform
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G Q : F[X]) (z : F) :
    triEval (coreRootTransform R B0 B1 G) z Q =
      triEval R z
        (B0 + Polynomial.C z * B1 + G * Q) := by
  rw [triEval_eq_eval_triSpecializeZ, triEval_eq_eval_triSpecializeZ]
  rw [coreRootTransform, triSpecializeZ, Polynomial.map_comp,
    Polynomial.eval_comp]
  rw [show Polynomial.map
      (Polynomial.mapRingHom (Polynomial.evalRingHom z))
        (coreRootSubstitution B0 B1 G) =
      Polynomial.C (B0 + Polynomial.C z * B1) +
        Polynomial.C G * Polynomial.X by
      simpa [triSpecializeZ] using
        triSpecializeZ_coreRootSubstitution B0 B1 G z]
  simp
  rfl

/-- The affine substitution has outer degree one whenever the core locator
is nonzero. -/
theorem coreRootSubstitution_natDegree
    {F : Type*} [Field F] (B0 B1 G : F[X]) (hG : G ≠ 0) :
    (coreRootSubstitution B0 B1 G).natDegree = 1 := by
  have hGlift : liftMiddle G ≠ 0 :=
    by simpa [liftMiddle] using
      (Polynomial.map_injective Polynomial.C Polynomial.C_injective).ne hG
  unfold coreRootSubstitution
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · exact Polynomial.natDegree_C_mul_X (liftMiddle G) hGlift
  · rw [Polynomial.natDegree_C,
      Polynomial.natDegree_C_mul_X (liftMiddle G) hGlift]
    omega

/-- Consequently the transformed factor keeps its outer `Y`-degree. -/
theorem coreRootTransform_natDegree
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) (hG : G ≠ 0) :
    (coreRootTransform R B0 B1 G).natDegree = R.natDegree := by
  rw [coreRootTransform, Polynomial.natDegree_comp,
    coreRootSubstitution_natDegree B0 B1 G hG, Nat.mul_one]

/-! ## Preservation of the `Y+Z` support cap -/

private theorem degreeX_add_le
    {F : Type*} [Field F] (P Q : F[X][X]) :
    Polynomial.Bivariate.degreeX (P + Q) ≤
      max (Polynomial.Bivariate.degreeX P)
        (Polynomial.Bivariate.degreeX Q) := by
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  calc
    ((P + Q).coeff i).natDegree =
        (P.coeff i + Q.coeff i).natDegree := by rw [Polynomial.coeff_add]
    _ ≤ max (P.coeff i).natDegree (Q.coeff i).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ max (P.support.sup fun j ↦ (P.coeff j).natDegree)
        (Q.support.sup fun j ↦ (Q.coeff j).natDegree) := by
      exact max_le_max
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX P i)
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX Q i)

private theorem degreeX_liftMiddle_eq_zero
    {F : Type*} [Field F] (P : F[X]) :
    Polynomial.Bivariate.degreeX (liftMiddle P) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  simp [liftMiddle]

private theorem degreeX_one
    {F : Type*} [Field F] :
    Polynomial.Bivariate.degreeX (1 : F[X][X]) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  have hi0 : i = 0 := by
    by_contra hine
    exact (Polynomial.mem_support_iff.mp hi)
      (by simp [Polynomial.coeff_one, hine])
  subst i
  simp

private theorem yzSupportDegree_one
    {F : Type*} [Field F] :
    YZFactorCap.yzSupportDegree
      (1 : Polynomial (Polynomial (Polynomial F))) 1 = 0 := by
  unfold YZFactorCap.yzSupportDegree
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro i hi
  have hi0 : i = 0 := by
    by_contra hine
    exact (Polynomial.mem_support_iff.mp hi)
      (by simp [Polynomial.coeff_one, hine])
  subst i
  simpa using degreeX_one (F := F)

private theorem yzSupportDegree_zero
    {F : Type*} [Field F] :
    YZFactorCap.yzSupportDegree
      (0 : Polynomial (Polynomial (Polynomial F))) 1 = 0 := by
  rfl

private theorem yzSupportDegree_X
    {F : Type*} [Field F] :
    YZFactorCap.yzSupportDegree
      (Polynomial.X : Polynomial (Polynomial (Polynomial F))) 1 = 1 := by
  unfold YZFactorCap.yzSupportDegree
  rw [Polynomial.support_X]
  simp [degreeX_one (F := F)]

private theorem yzSupportDegree_C_le_degreeX
    {F : Type*} [Field F] (P : F[X][X]) :
    YZFactorCap.yzSupportDegree
      (Polynomial.C P : F[X][X][Y]) 1 ≤
        Polynomial.Bivariate.degreeX P := by
  unfold YZFactorCap.yzSupportDegree
  simp only [one_mul]
  apply Finset.sup_le
  intro i hi
  have hi0 : i = 0 := by
    by_contra hine
    exact (Polynomial.mem_support_iff.mp hi)
      (by simp [Polynomial.coeff_C, hine])
  subst i
  simp

private theorem yzSupportDegree_add_le
    {F : Type*} [Field F] (P Q : F[X][X][Y]) :
    YZFactorCap.yzSupportDegree (P + Q) 1 ≤
      max (YZFactorCap.yzSupportDegree P 1)
        (YZFactorCap.yzSupportDegree Q 1) := by
  unfold YZFactorCap.yzSupportDegree
  simp only [one_mul]
  apply Finset.sup_le
  intro i hi
  by_cases hPi : P.coeff i = 0
  · have hQi : Q.coeff i ≠ 0 := by
      intro hQi
      exact (Polynomial.mem_support_iff.mp hi) (by simp [hPi, hQi])
    have hQw := YZFactorCap.coeffWeight_le_of_ne Q 1 i hQi
    simp only [one_mul, YZFactorCap.yzSupportDegree] at hQw
    rw [Polynomial.coeff_add, hPi, zero_add]
    exact hQw.trans (le_max_right _ _)
  · by_cases hQi : Q.coeff i = 0
    · have hPw := YZFactorCap.coeffWeight_le_of_ne P 1 i hPi
      simp only [one_mul, YZFactorCap.yzSupportDegree] at hPw
      rw [Polynomial.coeff_add, hQi, add_zero]
      exact hPw.trans (le_max_left _ _)
    · have hdeg := degreeX_add_le (P.coeff i) (Q.coeff i)
      have hPw := YZFactorCap.coeffWeight_le_of_ne P 1 i hPi
      have hQw := YZFactorCap.coeffWeight_le_of_ne Q 1 i hQi
      simp only [one_mul, YZFactorCap.yzSupportDegree] at hPw hQw
      rw [Polynomial.coeff_add]
      apply le_trans (b := max
        (Polynomial.Bivariate.degreeX (P.coeff i) + i)
        (Polynomial.Bivariate.degreeX (Q.coeff i) + i))
      · omega
      · exact max_le_max hPw hQw

private theorem yzSupportDegree_finset_sum_le
    {F I : Type*} [Field F] [DecidableEq I]
    (S : Finset I) (P : I → F[X][X][Y]) (D : Nat)
    (hP : ∀ i ∈ S, YZFactorCap.yzSupportDegree (P i) 1 ≤ D) :
    YZFactorCap.yzSupportDegree (∑ i ∈ S, P i) 1 ≤ D := by
  induction S using Finset.induction_on with
  | empty => simp [yzSupportDegree_zero]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (yzSupportDegree_add_le (P i) (∑ j ∈ S, P j)).trans
        (max_le (hP i (by simp))
          (ih (fun j hj ↦ hP j (by simp [hj]))))

private theorem yzSupportDegree_pow_le
    {F : Type*} [Field F] (P : F[X][X][Y]) (hP0 : P ≠ 0) :
    ∀ n, YZFactorCap.yzSupportDegree (P ^ n) 1 ≤
      n * YZFactorCap.yzSupportDegree P 1 := by
  intro n
  induction n with
  | zero => simp [yzSupportDegree_one]
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact (YZFactorCap.yzSupportDegree_mul_le (P ^ n) P 1
        (pow_ne_zero n hP0) hP0).trans (Nat.add_le_add_right ih _)

/-- Composing in the outer variable with a nonzero affine polynomial of
`Y+Z` weight at most one cannot increase `Y+Z` support. -/
theorem yzSupportDegree_comp_affine_le
    {F : Type*} [Field F] (R A : F[X][X][Y])
    (hA0 : A ≠ 0) (hA : YZFactorCap.yzSupportDegree A 1 ≤ 1) :
    YZFactorCap.yzSupportDegree (R.comp A) 1 ≤
      YZFactorCap.yzSupportDegree R 1 := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
  apply yzSupportDegree_finset_sum_le
  intro i hi
  have hRi : R.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hC : (Polynomial.C (R.coeff i) : F[X][X][Y]) ≠ 0 :=
    by simpa using Polynomial.C_injective.ne hRi
  have hpow : A ^ i ≠ 0 := pow_ne_zero i hA0
  calc
    YZFactorCap.yzSupportDegree
        (Polynomial.C (R.coeff i) * A ^ i) 1 ≤
        YZFactorCap.yzSupportDegree
            (Polynomial.C (R.coeff i) : F[X][X][Y]) 1 +
          YZFactorCap.yzSupportDegree (A ^ i) 1 :=
      YZFactorCap.yzSupportDegree_mul_le _ _ 1 hC hpow
    _ ≤ Polynomial.Bivariate.degreeX (R.coeff i) +
          i * YZFactorCap.yzSupportDegree A 1 :=
      Nat.add_le_add (yzSupportDegree_C_le_degreeX (R.coeff i))
        (yzSupportDegree_pow_le A hA0 i)
    _ ≤ Polynomial.Bivariate.degreeX (R.coeff i) + i := by
      exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left i hA) _
    _ ≤ YZFactorCap.yzSupportDegree R 1 := by
      simpa using YZFactorCap.coeffWeight_le_of_ne R 1 i hRi

/-- The common-core affine substitution has `Y+Z` support at most one. -/
theorem coreRootSubstitution_yzSupportDegree_le_one
    {F : Type*} [Field F] (B0 B1 G : F[X]) :
    YZFactorCap.yzSupportDegree
      (coreRootSubstitution B0 B1 G) 1 ≤ 1 := by
  have hB0 : Polynomial.Bivariate.degreeX (liftMiddle B0) = 0 :=
    degreeX_liftMiddle_eq_zero B0
  have hB1 : Polynomial.Bivariate.degreeX (liftMiddle B1) = 0 :=
    degreeX_liftMiddle_eq_zero B1
  have hG : Polynomial.Bivariate.degreeX (liftMiddle G) = 0 :=
    degreeX_liftMiddle_eq_zero G
  have hZ : Polynomial.Bivariate.degreeX
      (Polynomial.C (Polynomial.X : F[X]) : F[X][X]) = 1 := by
    unfold Polynomial.Bivariate.degreeX
    rw [Polynomial.support_C (by simp : (Polynomial.X : F[X]) ≠ 0)]
    simp
  have hbase : Polynomial.Bivariate.degreeX
      (liftMiddle B0 +
        Polynomial.C (Polynomial.X : F[X]) * liftMiddle B1) ≤ 1 := by
    exact (degreeX_add_le _ _).trans (max_le (by omega)
      ((Polynomial.Bivariate.degreeX_mul_le _ _).trans (by omega)))
  have hsecond : YZFactorCap.yzSupportDegree
      (Polynomial.C (liftMiddle G) *
        (Polynomial.X : F[X][X][Y])) 1 ≤ 1 := by
    by_cases hz : G = 0
    · simp [hz, liftMiddle, yzSupportDegree_zero]
    · have hGlift : liftMiddle G ≠ 0 := by
        simpa [liftMiddle] using
          (Polynomial.map_injective Polynomial.C Polynomial.C_injective).ne hz
      have hC : (Polynomial.C (liftMiddle G) : F[X][X][Y]) ≠ 0 := by
        simpa using Polynomial.C_injective.ne hGlift
      exact (YZFactorCap.yzSupportDegree_mul_le
        (Polynomial.C (liftMiddle G)) Polynomial.X 1 hC (by simp)).trans (by
          rw [yzSupportDegree_X]
          have hCG := yzSupportDegree_C_le_degreeX (liftMiddle G)
          omega)
  unfold coreRootSubstitution
  exact (yzSupportDegree_add_le _ _).trans (max_le
    ((yzSupportDegree_C_le_degreeX _).trans hbase)
    hsecond)

/-- The transformed factor inherits the original actual `Y+Z` support cap. -/
theorem coreRootTransform_yzSupportDegree_le
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) (hG : G ≠ 0) :
    YZFactorCap.yzSupportDegree (coreRootTransform R B0 B1 G) 1 ≤
      YZFactorCap.yzSupportDegree R 1 := by
  apply yzSupportDegree_comp_affine_le
  · intro hzero
    have hdeg := coreRootSubstitution_natDegree B0 B1 G hG
    rw [hzero] at hdeg
    simp at hdeg
  · exact coreRootSubstitution_yzSupportDegree_le_one B0 B1 G

/-! ## The correct transformed `X` weight -/

private theorem weightedSupportDegree_zero
    {A : Type*} [CommSemiring A] (k : Nat) :
    WeightedFactorCaps.weightedSupportDegree
      (0 : Polynomial (Polynomial A)) k = 0 := by
  rfl

private theorem weightedSupportDegree_one
    {A : Type*} [CommSemiring A] (k : Nat) :
    WeightedFactorCaps.weightedSupportDegree
      (1 : Polynomial (Polynomial A)) k = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold WeightedFactorCaps.weightedSupportDegree
  apply Finset.sup_le
  intro i hi
  have hi0 : i = 0 := by
    by_contra hine
    exact (Polynomial.mem_support_iff.mp hi)
      (by simp [Polynomial.coeff_one, hine])
  subst i
  simp

private theorem weightedSupportDegree_X
    {A : Type*} [CommSemiring A] [Nontrivial A] (k : Nat) :
    WeightedFactorCaps.weightedSupportDegree
      (Polynomial.X : Polynomial (Polynomial A)) k = k := by
  unfold WeightedFactorCaps.weightedSupportDegree
  rw [Polynomial.support_X]
  simp

private theorem weightedSupportDegree_C_le_natDegree
    {A : Type*} [CommSemiring A] (P : Polynomial A) (k : Nat) :
    WeightedFactorCaps.weightedSupportDegree
      (Polynomial.C P : Polynomial (Polynomial A)) k ≤ P.natDegree := by
  unfold WeightedFactorCaps.weightedSupportDegree
  apply Finset.sup_le
  intro i hi
  have hi0 : i = 0 := by
    by_contra hine
    exact (Polynomial.mem_support_iff.mp hi)
      (by simp [Polynomial.coeff_C, hine])
  subst i
  simp

private theorem weightedSupportDegree_add_le
    {A : Type*} [CommSemiring A]
    (P Q : Polynomial (Polynomial A)) (k : Nat) :
    WeightedFactorCaps.weightedSupportDegree (P + Q) k ≤
      max (WeightedFactorCaps.weightedSupportDegree P k)
        (WeightedFactorCaps.weightedSupportDegree Q k) := by
  unfold WeightedFactorCaps.weightedSupportDegree
  apply Finset.sup_le
  intro i hi
  by_cases hPi : P.coeff i = 0
  · have hQi : Q.coeff i ≠ 0 := by
      intro hQi
      exact (Polynomial.mem_support_iff.mp hi) (by simp [hPi, hQi])
    rw [Polynomial.coeff_add, hPi, zero_add]
    exact (WeightedFactorCaps.coeffWeight_le_of_ne Q k i hQi).trans
      (le_max_right _ _)
  · by_cases hQi : Q.coeff i = 0
    · rw [Polynomial.coeff_add, hQi, add_zero]
      exact (WeightedFactorCaps.coeffWeight_le_of_ne P k i hPi).trans
        (le_max_left _ _)
    · have hdeg := Polynomial.natDegree_add_le (P.coeff i) (Q.coeff i)
      have hPw := WeightedFactorCaps.coeffWeight_le_of_ne P k i hPi
      have hQw := WeightedFactorCaps.coeffWeight_le_of_ne Q k i hQi
      rw [Polynomial.coeff_add]
      apply le_trans (b := max
        ((P.coeff i).natDegree + k * i)
        ((Q.coeff i).natDegree + k * i))
      · omega
      · exact max_le_max hPw hQw

private theorem weightedSupportDegree_finset_sum_le
    {A I : Type*} [CommSemiring A] [DecidableEq I]
    (S : Finset I) (P : I → Polynomial (Polynomial A)) (k D : Nat)
    (hP : ∀ i ∈ S,
      WeightedFactorCaps.weightedSupportDegree (P i) k ≤ D) :
    WeightedFactorCaps.weightedSupportDegree (∑ i ∈ S, P i) k ≤ D := by
  induction S using Finset.induction_on with
  | empty => simp [weightedSupportDegree_zero]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (weightedSupportDegree_add_le (P i) (∑ j ∈ S, P j) k).trans
        (max_le (hP i (by simp))
          (ih (fun j hj ↦ hP j (by simp [hj]))))

private theorem weightedSupportDegree_pow_le
    {A : Type*} [CommSemiring A] [IsDomain A]
    (P : Polynomial (Polynomial A)) (hP0 : P ≠ 0) (k : Nat) :
    ∀ n, WeightedFactorCaps.weightedSupportDegree (P ^ n) k ≤
      n * WeightedFactorCaps.weightedSupportDegree P k := by
  intro n
  induction n with
  | zero => simp [weightedSupportDegree_one]
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact (WeightedFactorCaps.weightedSupportDegree_mul_le (P ^ n) P k
        (pow_ne_zero n hP0) hP0).trans (Nat.add_le_add_right ih _)

/-- If an affine root substitution has transformed `X+sY` weight at most
the original root cap `k`, composition sends an original `X+kY` cap to the
transformed `X+sY` cap. -/
theorem weightedSupportDegree_comp_affine_le
    {A : Type*} [CommSemiring A] [IsDomain A]
    (R T : Polynomial (Polynomial A)) (s k : Nat)
    (hT0 : T ≠ 0)
    (hT : WeightedFactorCaps.weightedSupportDegree T s ≤ k) :
    WeightedFactorCaps.weightedSupportDegree (R.comp T) s ≤
      WeightedFactorCaps.weightedSupportDegree R k := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
  apply weightedSupportDegree_finset_sum_le
  intro i hi
  have hRi : R.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hC : (Polynomial.C (R.coeff i) : Polynomial (Polynomial A)) ≠ 0 :=
    by simpa using Polynomial.C_injective.ne hRi
  have hpow : T ^ i ≠ 0 := pow_ne_zero i hT0
  calc
    WeightedFactorCaps.weightedSupportDegree
        (Polynomial.C (R.coeff i) * T ^ i) s ≤
        WeightedFactorCaps.weightedSupportDegree
            (Polynomial.C (R.coeff i) : Polynomial (Polynomial A)) s +
          WeightedFactorCaps.weightedSupportDegree (T ^ i) s :=
      WeightedFactorCaps.weightedSupportDegree_mul_le _ _ s hC hpow
    _ ≤ (R.coeff i).natDegree +
          i * WeightedFactorCaps.weightedSupportDegree T s :=
      Nat.add_le_add (weightedSupportDegree_C_le_natDegree (R.coeff i) s)
        (weightedSupportDegree_pow_le T hT0 s i)
    _ ≤ (R.coeff i).natDegree + k * i := by
      exact Nat.add_le_add_left (by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right i hT) _
    _ ≤ WeightedFactorCaps.weightedSupportDegree R k :=
      WeightedFactorCaps.coeffWeight_le_of_ne R k i hRi

private theorem liftMiddle_natDegree
    {F : Type*} [Field F] (P : F[X]) :
    (liftMiddle P).natDegree = P.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective P

/-- The exact degree hypotheses needed on the common-core base and locator.
The locator condition is `deg G + s ≤ k`, not merely `deg G ≤ k`. -/
theorem coreRootSubstitution_weightedSupportDegree_le
    {F : Type*} [Field F] (B0 B1 G : F[X]) (s k : Nat)
    (hB0 : B0.natDegree ≤ k) (hB1 : B1.natDegree ≤ k)
    (hG : G.natDegree + s ≤ k) (hG0 : G ≠ 0) :
    WeightedFactorCaps.weightedSupportDegree
      (coreRootSubstitution B0 B1 G) s ≤ k := by
  have hbase :
      (liftMiddle B0 +
        Polynomial.C (Polynomial.X : F[X]) * liftMiddle B1).natDegree ≤ k := by
    calc
      _ ≤ max (liftMiddle B0).natDegree
          (Polynomial.C (Polynomial.X : F[X]) *
            liftMiddle B1).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ max B0.natDegree B1.natDegree := by
        apply max_le_max
        · rw [liftMiddle_natDegree]
        · calc
            (Polynomial.C (Polynomial.X : F[X]) *
                liftMiddle B1).natDegree ≤
                (Polynomial.C (Polynomial.X : F[X]) : F[X][X]).natDegree +
                  (liftMiddle B1).natDegree := Polynomial.natDegree_mul_le
            _ = B1.natDegree := by
              rw [Polynomial.natDegree_C, zero_add, liftMiddle_natDegree]
      _ ≤ k := max_le hB0 hB1
  have hGlift : liftMiddle G ≠ 0 := by
    simpa [liftMiddle] using
      (Polynomial.map_injective Polynomial.C Polynomial.C_injective).ne hG0
  unfold coreRootSubstitution
  exact (weightedSupportDegree_add_le _ _ s).trans (max_le
    ((weightedSupportDegree_C_le_natDegree _ s).trans hbase)
    ((WeightedFactorCaps.weightedSupportDegree_mul_le
      (Polynomial.C (liftMiddle G)) Polynomial.X s
      (by simpa using Polynomial.C_injective.ne hGlift) (by simp)).trans (by
        rw [weightedSupportDegree_X]
        have hCG := weightedSupportDegree_C_le_natDegree (liftMiddle G) s
        rw [liftMiddle_natDegree] at hCG
        omega)))

/-- With the sharp core degrees, the transformed factor does not exceed the
original factor's weighted `X` support. -/
theorem coreRootTransform_weightedSupportDegree_le
    {F : Type*} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) (s k : Nat)
    (hB0 : B0.natDegree ≤ k) (hB1 : B1.natDegree ≤ k)
    (hG : G.natDegree + s ≤ k) (hG0 : G ≠ 0) :
    WeightedFactorCaps.weightedSupportDegree
        (coreRootTransform R B0 B1 G) s ≤
      WeightedFactorCaps.weightedSupportDegree R k := by
  apply weightedSupportDegree_comp_affine_le
  · intro hzero
    have hdeg := coreRootSubstitution_natDegree B0 B1 G hG0
    rw [hzero] at hdeg
    simp at hdeg
  · exact coreRootSubstitution_weightedSupportDegree_le
      B0 B1 G s k hB0 hB1 hG hG0

def bchksCoreQuotientDegree129Cap6400 : Nat := 129
def bchksCoreQuotientMaxCodim6400 : Nat := 130229
def bchksCoreQuotientMinCoreCard6400 : Nat := 842
def bchksCoreQuotientExponent6400 : Nat := 260457
def bchksCoreQuotientFusedCoefficient6400 : Nat := 162228007
def bchksCoreQuotientTotal6400 : Nat := 274978189239607384

def bchksCoreQuotientFirstMissCodim6400 : Nat := 130230
def bchksCoreQuotientFirstMissExponent6400 : Nat := 260459
def bchksCoreQuotientFirstMissCoefficient6400 : Nat := 162229252
def bchksCoreQuotientFirstMissTotal6400 : Nat := 274980292014015244

/-- Exact endpoint of the transformed-root universal-resultant ledger. -/
lemma bchksCoreQuotient_degree129_endpoint6400 :
    bchksCoreQuotientMaxCodim6400 +
        bchksCoreQuotientMinCoreCard6400 = 131071 /\
      bchksCoreQuotientExponent6400 =
        2 * bchksCoreQuotientMaxCodim6400 - 1 /\
      bchksCoreQuotientFusedCoefficient6400 =
        ((262144 - 131071) *
              (bchksCoreQuotientExponent6400 *
                (2 * bchksCoreQuotientDegree129Cap6400)) +
            (262144 - bchksErrors6400 - 131071) - 1) /
            (262144 - bchksErrors6400 - 131071) +
          2 * bchksCoreQuotientDegree129Cap6400 /\
      bchksCoreQuotientTotal6400 =
        bchksCoreQuotientFusedCoefficient6400 * bchksHybridZMass6400 +
          bchksHybridCheapCover6400 + bchksHybridRadicalCover6400 +
          bchksHybridFullCoreCover6400 +
          bchksHybridOrderStabilityCover6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 /\
      bchksCoreQuotientTotal6400 < bchksWeightedNumerator6400 /\
      bchksWeightedNumerator6400 - bchksCoreQuotientTotal6400 =
        810760392616 := by
  norm_num [bchksCoreQuotientMaxCodim6400,
    bchksCoreQuotientMinCoreCard6400, bchksCoreQuotientExponent6400,
    bchksCoreQuotientFusedCoefficient6400,
    bchksCoreQuotientDegree129Cap6400, bchksCoreQuotientTotal6400,
    bchksErrors6400, bchksHybridZMass6400,
    bchksHybridCheapCover6400, bchksHybridRadicalCover6400,
    bchksHybridFullCoreCover6400, bchksHybridOrderStabilityCover6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksWeightedNumerator6400]

/-- Increasing the quotient degree by one is the first miss. -/
lemma bchksCoreQuotient_degree129_firstMiss6400 :
    bchksCoreQuotientFirstMissExponent6400 =
        2 * bchksCoreQuotientFirstMissCodim6400 - 1 /\
      bchksCoreQuotientFirstMissCoefficient6400 =
        ((262144 - 131071) *
              (bchksCoreQuotientFirstMissExponent6400 *
                (2 * bchksCoreQuotientDegree129Cap6400)) +
            (262144 - bchksErrors6400 - 131071) - 1) /
            (262144 - bchksErrors6400 - 131071) +
          2 * bchksCoreQuotientDegree129Cap6400 /\
      bchksCoreQuotientFirstMissTotal6400 =
        bchksCoreQuotientFirstMissCoefficient6400 *
            bchksHybridZMass6400 +
          bchksHybridCheapCover6400 + bchksHybridRadicalCover6400 +
          bchksHybridFullCoreCover6400 +
          bchksHybridOrderStabilityCover6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 /\
      bchksWeightedNumerator6400 <
        bchksCoreQuotientFirstMissTotal6400 /\
      bchksCoreQuotientFirstMissTotal6400 -
          bchksWeightedNumerator6400 = 1292014015244 := by
  norm_num [bchksCoreQuotientFirstMissExponent6400,
    bchksCoreQuotientFirstMissCodim6400,
    bchksCoreQuotientFirstMissCoefficient6400,
    bchksCoreQuotientDegree129Cap6400,
    bchksCoreQuotientFirstMissTotal6400, bchksErrors6400,
    bchksHybridZMass6400, bchksHybridCheapCover6400,
    bchksHybridRadicalCover6400, bchksHybridFullCoreCover6400,
    bchksHybridOrderStabilityCover6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksWeightedNumerator6400]

end BCHKSCoreQuotientHenselAudit6400
end ProximityPrize.SubmissionLower
