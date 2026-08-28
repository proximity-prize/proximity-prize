import ProximityPrize.SubmissionLower.BCHKSUniversalNumerator
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap
import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

open Polynomial Polynomial.Bivariate

namespace ProximityPrize.SubmissionLower.UniversalNumerator

open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

noncomputable section

set_option maxHeartbeats 4000000

variable {F : Type} [Field F]

def zToUniversalU : F[X] →+* F[X][X][X] :=
  (Polynomial.C : F[X][X] →+* F[X][X][X]).comp
    (Polynomial.C : F[X] →+* F[X][X])

def shiftXToUniversal (x₀ : F) : F[X][X] →+* F[X][X][X] :=
  Polynomial.eval₂RingHom zToUniversalU
    (Polynomial.C (Polynomial.C (Polynomial.C x₀)) + Polynomial.X)

def universalShift (x₀ : F) (R : F[X][X][Y]) : F[X][X][X][X] :=
  (R.map (shiftXToUniversal x₀)).comp
    (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X)

def universalSlope (x₀ : F) (R : F[X][X][Y]) : F[X][Y] :=
  triSpecializeX R.derivative x₀

def evalZY (z y : F) : F[X][Y] →+* F :=
  (Polynomial.evalRingHom y).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom z))

theorem evalZY_apply (z y : F) (p : F[X][Y]) :
    evalZY z y p = biEval p y z := rfl

theorem map_shiftXToUniversal_evalZY (x₀ z y : F) (A : F[X][X]) :
    (shiftXToUniversal x₀ A).map (evalZY z y) =
      ProximityPrize.SubmissionLower.FiniteHensel.shiftMap x₀
        (A.map (Polynomial.evalRingHom z)) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [hA, hB]
  | monomial n c =>
      simp [shiftXToUniversal, zToUniversalU, evalZY,
        ProximityPrize.SubmissionLower.FiniteHensel.shiftMap,
        Polynomial.map_monomial, Polynomial.eval_monomial]

theorem universalShift_map_evalZY (x₀ z y : F) (R : F[X][X][Y]) :
    (universalShift x₀ R).map (Polynomial.mapRingHom (evalZY z y)) =
      ((triSpecializeZ R z).map
        (ProximityPrize.SubmissionLower.FiniteHensel.shiftMap x₀)).comp
          (Polynomial.C (Polynomial.C y) + Polynomial.X) := by
  induction R using Polynomial.induction_on' with
  | add A B hA hB =>
      rw [show universalShift x₀ (A + B) =
          universalShift x₀ A + universalShift x₀ B by
        simp [universalShift]]
      rw [Polynomial.map_add, hA, hB]
      simp [triSpecializeZ]
  | monomial n A =>
      have hcoeff :
          Polynomial.map ((Polynomial.evalRingHom y).comp
              (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
              (shiftXToUniversal x₀ A) =
            ProximityPrize.SubmissionLower.FiniteHensel.shiftMap x₀
              (A.map (Polynomial.evalRingHom z)) := by
        simpa [evalZY] using map_shiftXToUniversal_evalZY x₀ z y A
      simp [universalShift, triSpecializeZ, Polynomial.map_monomial,
        evalZY, hcoeff]

theorem universalSlope_eval (x₀ z y : F) (R : F[X][X][Y]) :
    evalZY z y (universalSlope x₀ R) =
      ProximityPrize.SubmissionLower.FiniteHensel.ySlope
        (triSpecializeZ R z) x₀ y := by
  unfold universalSlope evalZY triSpecializeX triSpecializeZ
    ProximityPrize.SubmissionLower.FiniteHensel.ySlope
  rw [Polynomial.derivative_map]
  change Polynomial.eval y
      (Polynomial.map (Polynomial.evalRingHom z)
        (Polynomial.map (Polynomial.evalRingHom (Polynomial.C x₀)) R.derivative)) =
    Polynomial.eval₂ (Polynomial.evalRingHom x₀) y
      (Polynomial.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) R.derivative)
  induction R.derivative using Polynomial.induction_on' with
  | add A B hA hB => simp [hA, hB]
  | monomial n A =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial,
        eval_map_eval_eq_eval_eval_C]

private theorem degreeX_C_eq_natDegree (p : F[X]) :
    Bivariate.degreeX (Polynomial.C p : F[X][X]) = p.natDegree := by
  unfold Bivariate.degreeX
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Polynomial.support_C hp]
    simp

theorem shiftXToUniversal_coeff_natDegree_le
    (x₀ : F) (A : F[X][X]) (a : ℕ) :
    ((shiftXToUniversal x₀ A).coeff a).natDegree ≤ 0 := by
  classical
  rw [A.as_sum_support]
  simp only [map_sum]
  rw [show (∑ x ∈ A.support,
      shiftXToUniversal x₀ (Polynomial.monomial x (A.coeff x))).coeff a =
      ∑ x ∈ A.support,
        (shiftXToUniversal x₀ (Polynomial.monomial x (A.coeff x))).coeff a by
    simp]
  apply YZFactorCap.natDegree_sum_le_of_forall
  intro n hn
  rw [show shiftXToUniversal x₀ (Polynomial.monomial n (A.coeff n)) =
      Polynomial.C (Polynomial.C (A.coeff n)) *
        (Polynomial.C (Polynomial.C (Polynomial.C x₀)) + Polynomial.X) ^ n by
    simp [shiftXToUniversal, zToUniversalU]]
  rw [Polynomial.coeff_C_mul]
  rw [show Polynomial.C (Polynomial.C (Polynomial.C x₀)) + Polynomial.X =
      Polynomial.X + Polynomial.C (Polynomial.C (Polynomial.C x₀)) by ring,
    Polynomial.coeff_X_add_C_pow]
  rw [show Polynomial.C (A.coeff n) *
      (Polynomial.C (Polynomial.C x₀) ^ (n - a) * (n.choose a : F[X][X])) =
      Polynomial.C (A.coeff n * (Polynomial.C x₀) ^ (n - a) *
        Polynomial.C (n.choose a : F)) by
          simp only [Polynomial.C_mul, Polynomial.C_pow, map_natCast, mul_assoc]]
  exact (Polynomial.natDegree_C _).le

theorem shiftXToUniversal_coeff_degreeX_le
    (x₀ : F) (A : F[X][X]) (a : ℕ) :
    Bivariate.degreeX ((shiftXToUniversal x₀ A).coeff a) ≤
      Bivariate.degreeX A := by
  classical
  conv_lhs => rw [A.as_sum_support]
  simp only [map_sum]
  rw [show (∑ x ∈ A.support,
      shiftXToUniversal x₀ (Polynomial.monomial x (A.coeff x))).coeff a =
      ∑ x ∈ A.support,
        (shiftXToUniversal x₀ (Polynomial.monomial x (A.coeff x))).coeff a by
    simp]
  apply YZFactorCap.degreeX_sum_le_of_forall
  intro n hn
  rw [show shiftXToUniversal x₀ (Polynomial.monomial n (A.coeff n)) =
      Polynomial.C (Polynomial.C (A.coeff n)) *
        (Polynomial.C (Polynomial.C (Polynomial.C x₀)) + Polynomial.X) ^ n by
    simp [shiftXToUniversal, zToUniversalU]]
  rw [Polynomial.coeff_C_mul]
  rw [show Polynomial.C (Polynomial.C (Polynomial.C x₀)) + Polynomial.X =
      Polynomial.X + Polynomial.C (Polynomial.C (Polynomial.C x₀)) by ring,
    Polynomial.coeff_X_add_C_pow]
  rw [show Polynomial.C (A.coeff n) *
      (Polynomial.C (Polynomial.C x₀) ^ (n - a) * (n.choose a : F[X][X])) =
      Polynomial.C (A.coeff n * (Polynomial.C x₀) ^ (n - a) *
        Polynomial.C (n.choose a : F)) by
          simp only [Polynomial.C_mul, Polynomial.C_pow, map_natCast, mul_assoc]]
  rw [degreeX_C_eq_natDegree]
  calc
    (A.coeff n * (Polynomial.C x₀) ^ (n - a) *
        Polynomial.C (n.choose a : F)).natDegree ≤
        (A.coeff n).natDegree +
          ((Polynomial.C x₀) ^ (n - a) *
            Polynomial.C (n.choose a : F)).natDegree :=
      by simpa only [mul_assoc] using
        (Polynomial.natDegree_mul_le (p := A.coeff n)
          (q := (Polynomial.C x₀) ^ (n-a) * Polynomial.C (n.choose a : F)))
    _ ≤ Bivariate.degreeX A + 0 := Nat.add_le_add
      (Polynomial.Bivariate.coeff_natDegree_le_degreeX A n) (by
        rw [show ((Polynomial.C x₀) ^ (n - a) *
            Polynomial.C (n.choose a : F)) =
            Polynomial.C (x₀ ^ (n-a) * (n.choose a : F)) by simp]
        exact (Polynomial.natDegree_C _).le)
    _ = Bivariate.degreeX A := Nat.add_zero _

theorem universalShift_coeff_natDegree_le
    (x₀ : F) (R : F[X][X][Y]) (d b a : ℕ)
    (hRdeg : R.natDegree ≤ d) :
    (((universalShift x₀ R).coeff b).coeff a).natDegree ≤ d := by
  classical
  have hsum : universalShift x₀ R =
      ∑ j ∈ R.support,
        Polynomial.C (shiftXToUniversal x₀ (R.coeff j)) *
          (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) ^ j := by
    conv_lhs => rw [R.as_sum_support]
    unfold universalShift
    let q : Polynomial (Polynomial (Polynomial (Polynomial F))) :=
      Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X
    change (@Polynomial.compRingHom (Polynomial (Polynomial (Polynomial F))) _ q)
      ((Polynomial.mapRingHom (shiftXToUniversal x₀))
        (∑ j ∈ R.support, Polynomial.monomial j (R.coeff j))) = _
    dsimp [q]
    rw [show (Polynomial.map (shiftXToUniversal x₀)
        (∑ j ∈ R.support, Polynomial.monomial j (R.coeff j))).comp
          (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) =
        ∑ j ∈ R.support,
          (Polynomial.map (shiftXToUniversal x₀)
            (Polynomial.monomial j (R.coeff j))).comp
              (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) by
      rw [Polynomial.map_sum]
      exact map_sum
        (@Polynomial.compRingHom (Polynomial (Polynomial (Polynomial F))) _ q) _ _]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  rw [hsum]
  have hcoeffsum : ((∑ j ∈ R.support,
      Polynomial.C (shiftXToUniversal x₀ (R.coeff j)) *
        (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) ^ j :
          F[X][X][X][X]).coeff b).coeff a =
      ∑ j ∈ R.support,
        ((Polynomial.C (shiftXToUniversal x₀ (R.coeff j)) *
          (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) ^ j).coeff b).coeff a := by
    simp
  rw [hcoeffsum]
  apply YZFactorCap.natDegree_sum_le_of_forall
  intro j hj
  rw [Polynomial.coeff_C_mul]
  rw [show Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X =
      Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) by
        exact add_comm _ _,
    Polynomial.coeff_X_add_C_pow]
  rw [show (Polynomial.C Polynomial.X) ^ (j-b) *
      (j.choose b : F[X][X][X]) =
      Polynomial.C (Polynomial.X ^ (j-b) * (j.choose b : F[X][X])) by
    simp only [Polynomial.C_pow, Polynomial.C_mul, map_natCast]]
  rw [Polynomial.coeff_mul_C]
  calc
    (((shiftXToUniversal x₀ (R.coeff j)).coeff a) *
        (Polynomial.X ^ (j-b) * (j.choose b : F[X][X]))).natDegree ≤
        ((shiftXToUniversal x₀ (R.coeff j)).coeff a).natDegree +
          (Polynomial.X ^ (j-b) * (j.choose b : F[X][X])).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + j := Nat.add_le_add
      (shiftXToUniversal_coeff_natDegree_le x₀ (R.coeff j) a) (by
        have hp := Polynomial.natDegree_mul_le
          (p := Polynomial.X ^ (j-b)) (q := (j.choose b : F[X][X]))
        exact hp.trans (by
          rw [Polynomial.natDegree_pow]
          simp))
    _ ≤ d := by
      simpa using (Polynomial.le_natDegree_of_mem_supp j hj).trans hRdeg

private theorem degreeX_coeff_le_of_YZCap
    (R : F[X][X][Y]) (D j : ℕ) (hYZ : YZCap R D) :
    Bivariate.degreeX (R.coeff j) ≤ D := by
  unfold Bivariate.degreeX
  apply Finset.sup_le
  intro r hr
  have hc : (R.coeff j).coeff r ≠ 0 := Polynomial.mem_support_iff.mp hr
  exact (Nat.le_add_right _ j).trans (hYZ j r hc)

private theorem degreeX_X_pow_natCast_le_zero (n c : ℕ) :
    Bivariate.degreeX (Polynomial.X ^ n * (c : F[X][X])) ≤ 0 := by
  unfold Bivariate.degreeX
  apply Finset.sup_le
  intro r hr
  rw [show (c : F[X][X]) = Polynomial.C (Polynomial.C (c : F)) by simp,
    Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
  split <;> simp

theorem universalShift_coeff_degreeX_le
    (x₀ : F) (R : F[X][X][Y]) (D b a : ℕ)
    (hYZ : YZCap R D) :
    Bivariate.degreeX (((universalShift x₀ R).coeff b).coeff a) ≤ D := by
  classical
  have hsum : universalShift x₀ R =
      ∑ j ∈ R.support,
        Polynomial.C (shiftXToUniversal x₀ (R.coeff j)) *
          (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) ^ j := by
    conv_lhs => rw [R.as_sum_support]
    unfold universalShift
    let q : Polynomial (Polynomial (Polynomial (Polynomial F))) :=
      Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X
    change (@Polynomial.compRingHom (Polynomial (Polynomial (Polynomial F))) _ q)
      ((Polynomial.mapRingHom (shiftXToUniversal x₀))
        (∑ j ∈ R.support, Polynomial.monomial j (R.coeff j))) = _
    dsimp [q]
    rw [show (Polynomial.map (shiftXToUniversal x₀)
        (∑ j ∈ R.support, Polynomial.monomial j (R.coeff j))).comp
          (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) =
        ∑ j ∈ R.support,
          (Polynomial.map (shiftXToUniversal x₀)
            (Polynomial.monomial j (R.coeff j))).comp
              (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) by
      rw [Polynomial.map_sum]
      exact map_sum
        (@Polynomial.compRingHom (Polynomial (Polynomial (Polynomial F))) _ q) _ _]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  rw [hsum]
  have hcoeffsum : ((∑ j ∈ R.support,
      Polynomial.C (shiftXToUniversal x₀ (R.coeff j)) *
        (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) ^ j :
          F[X][X][X][X]).coeff b).coeff a =
      ∑ j ∈ R.support,
        ((Polynomial.C (shiftXToUniversal x₀ (R.coeff j)) *
          (Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X) ^ j).coeff b).coeff a := by
    simp
  rw [hcoeffsum]
  apply YZFactorCap.degreeX_sum_le_of_forall
  intro j hj
  rw [Polynomial.coeff_C_mul]
  rw [show Polynomial.C (Polynomial.C Polynomial.X) + Polynomial.X =
      Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) by
        exact add_comm _ _,
    Polynomial.coeff_X_add_C_pow]
  rw [show (Polynomial.C Polynomial.X) ^ (j-b) *
      (j.choose b : F[X][X][X]) =
      Polynomial.C (Polynomial.X ^ (j-b) * (j.choose b : F[X][X])) by
    simp only [Polynomial.C_pow, Polynomial.C_mul, map_natCast]]
  rw [Polynomial.coeff_mul_C]
  calc
    Bivariate.degreeX (((shiftXToUniversal x₀ (R.coeff j)).coeff a) *
        (Polynomial.X ^ (j-b) * (j.choose b : F[X][X]))) ≤
        Bivariate.degreeX ((shiftXToUniversal x₀ (R.coeff j)).coeff a) +
          Bivariate.degreeX
            (Polynomial.X ^ (j-b) * (j.choose b : F[X][X])) :=
      Bivariate.degreeX_mul_le _ _
    _ ≤ Bivariate.degreeX (R.coeff j) + 0 := Nat.add_le_add
      (shiftXToUniversal_coeff_degreeX_le x₀ (R.coeff j) a)
      (degreeX_X_pow_natCast_le_zero (F := F) (j-b) (j.choose b))
    _ ≤ D := by simpa using degreeX_coeff_le_of_YZCap R D j hYZ

theorem universalShift_concrete_caps
    (x₀ : F) (R : F[X][X][Y]) (d D : ℕ)
    (hRdeg : R.natDegree ≤ d) (hYZ : YZCap R D) :
    (∀ n b a, b ≤ d → a ≤ n →
      (((universalShift x₀ R).coeff b).coeff a).natDegree ≤ d) ∧
    (∀ n b a, b ≤ d → a ≤ n →
      Bivariate.degreeX (((universalShift x₀ R).coeff b).coeff a) ≤ D) := by
  constructor
  · intro n b a hb ha
    exact universalShift_coeff_natDegree_le x₀ R d b a hRdeg
  · intro n b a hb ha
    exact universalShift_coeff_degreeX_le x₀ R D b a hYZ

theorem natDegree_eval_C_le_degreeX (p : F[X][X]) (x : F) :
    (Polynomial.eval (Polynomial.C x) p).natDegree ≤ Bivariate.degreeX p := by
  have heq : (Polynomial.Bivariate.swap p).map
      (Polynomial.evalRingHom x) = Polynomial.eval (Polynomial.C x) p := by
    rw [← Polynomial.Bivariate.evalX_eq_map]
    exact (Polynomial.Bivariate.evalY_eq_evalX_swap x p).symm
  rw [← heq]
  exact Polynomial.natDegree_map_le.trans (by
    rw [show (Polynomial.Bivariate.swap p).natDegree =
      Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap p) from rfl,
      Polynomial.Bivariate.natDegreeY_swap])

theorem universalSlope_degreeX_le_sub_one
    (x₀ : F) (R : F[X][X][Y]) (D : ℕ) (hD : 0 < D)
    (hYZ : YZCap R D) :
    Bivariate.degreeX (universalSlope x₀ R) ≤ D - 1 := by
  classical
  unfold Bivariate.degreeX
  apply Finset.sup_le
  intro b hb
  have hraw : Bivariate.degreeX (R.coeff (b + 1)) ≤ D - (b + 1) := by
    unfold Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have hc : ((R.coeff (b+1)).coeff a) ≠ 0 := Polynomial.mem_support_iff.mp ha
    have hh := hYZ (b+1) a hc
    omega
  have hderraw : Bivariate.degreeX (R.derivative.coeff b) ≤ D - (b+1) := by
    rw [Polynomial.coeff_derivative]
    have hcast : Bivariate.degreeX (b+1 : F[X][X]) ≤ 0 := by
      have houter : (b+1 : F[X][X]) =
          Polynomial.C (b+1 : F[X]) := by
        ext i
        by_cases hi : i = 0
        · subst i
          simp
        · simp [Polynomial.coeff_C, hi]
      rw [houter, degreeX_C_eq_natDegree]
      have hinner : (b+1 : F[X]) = Polynomial.C (b+1 : F) := by
        ext i
        by_cases hi : i = 0
        · subst i
          simp
        · simp [Polynomial.coeff_C, hi]
      rw [hinner]
      exact (Polynomial.natDegree_C _).le
    calc
      Bivariate.degreeX (R.coeff (b+1) * (b+1 : F[X][X])) ≤
          Bivariate.degreeX (R.coeff (b+1)) +
            Bivariate.degreeX (b+1 : F[X][X]) := Bivariate.degreeX_mul_le _ _
      _ ≤ (D-(b+1)) + 0 := Nat.add_le_add hraw hcast
      _ = D-(b+1) := by omega
  have heval :
      (universalSlope x₀ R).coeff b =
        Polynomial.eval (Polynomial.C x₀) (R.derivative.coeff b) := by
    simp [universalSlope, triSpecializeX]
  rw [heval]
  exact (natDegree_eval_C_le_degreeX _ _).trans
    (hderraw.trans (by omega))

theorem universalSlope_natDegree_le_sub_one
    (x₀ : F) (R : F[X][X][Y]) (d : ℕ)
    (hRdeg : R.natDegree ≤ d) :
    (universalSlope x₀ R).natDegree ≤ d - 1 := by
  unfold universalSlope triSpecializeX
  exact Polynomial.natDegree_map_le.trans
    ((Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right hRdeg 1))

theorem affine_slope_degree_absorbed (E D : ℕ)
    (hE : 1 ≤ E) (hD : 1 ≤ D) :
    1 + E * (D - 1) ≤ E * D := by
  have hsplit : D = (D - 1) + 1 := by omega
  calc
    1 + E * (D - 1) = E * (D - 1) + 1 := Nat.add_comm _ _
    _ ≤ E * (D - 1) + E := Nat.add_le_add_left hE _
    _ = E * ((D - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ = E * D := by rw [← hsplit]

end

end ProximityPrize.SubmissionLower.UniversalNumerator
