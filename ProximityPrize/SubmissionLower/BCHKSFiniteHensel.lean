import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.FiniteHensel
open Finset Polynomial
universe u
variable {L : Type u} [Field L]
noncomputable section
noncomputable def dividedDifference {A : Type*} [CommRing A]
    (P : A[X]) (u v : A) : A :=
  P.sum fun k c => c * ∑ j ∈ Finset.range k, u ^ j * v ^ (k - 1 - j)
lemma pow_sub_pow_eq_mul_divided (A : Type*) [CommRing A] (u v : A) (k : ℕ) :
    u ^ k - v ^ k =
      (u - v) * ∑ j ∈ Finset.range k, u ^ j * v ^ (k - 1 - j) := by
  symm
  exact (Commute.all u v).mul_geom_sum₂ k
lemma eval_sub_eval_eq_mul_dividedDifference {A : Type*} [CommRing A]
    (P : A[X]) (u v : A) :
    P.eval u - P.eval v = (u - v) * dividedDifference P u v := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [dividedDifference, Polynomial.sum_def]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_sub]
  rw [pow_sub_pow_eq_mul_divided A u v k]
  ring
lemma dividedDifference_self {A : Type*} [CommRing A]
    (P : A[X]) (y : A) :
    dividedDifference P y y = P.derivative.eval y := by
  rw [Polynomial.derivative_eval]
  simp only [dividedDifference, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k hk
  have hinner : (∑ j ∈ Finset.range k, y ^ j * y ^ (k - 1 - j)) =
      (k : A) * y ^ (k - 1) := by
    calc
      _ = ∑ _j ∈ Finset.range k, y ^ (k - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← pow_add]
        congr 1
        have hj' : j < k := Finset.mem_range.mp hj
        omega
      _ = (k : A) * y ^ (k - 1) := by simp
  rw [hinner]
  ring
lemma dividedDifference_add {A : Type*} [CommRing A]
    (P Q : A[X]) (u v : A) :
    dividedDifference (P + Q) u v = dividedDifference P u v + dividedDifference Q u v := by
  unfold dividedDifference
  apply Polynomial.sum_add_index
  · intro i
    simp
  · intro i a b
    rw [add_mul]
lemma dividedDifference_monomial {A : Type*} [CommRing A]
    (n : ℕ) (a u v : A) :
    dividedDifference (Polynomial.monomial n a) u v =
      a * ∑ j ∈ range n, u ^ j * v ^ (n - 1 - j) := by
  simp [dividedDifference, Polynomial.sum_monomial_index]
lemma map_dividedDifference {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (P : A[X]) (u v : A) :
    f (dividedDifference P u v) =
      dividedDifference (P.map f) (f u) (f v) := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
      rw [dividedDifference_add, map_add, ihP, ihQ,
        Polynomial.map_add, dividedDifference_add]
  | monomial n a => simp [dividedDifference_monomial]
lemma coeff_mul_of_left_vanishes_below {A : Type*} [CommRing A]
    (D Q : A[X]) (n : ℕ) (hD : ∀ i, i < n → D.coeff i = 0) :
    (D * Q).coeff n = D.coeff n * Q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  classical
  apply Finset.sum_eq_single (n, 0)
  · intro p hp hne
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_antidiagonal] at hp
    have hab : a + b = n := hp
    by_cases ha : a = n
    · have hb : b = 0 := by omega
      exact (hne (Prod.ext ha hb)).elim
    · rw [hD a (by omega), zero_mul]
  · intro hnot
    exfalso
    exact hnot (by simp)
noncomputable def shiftMap {L : Type*} [Field L] (x₀ : L) : L[X] →+* L[X] :=
  Polynomial.eval₂RingHom (Polynomial.C : L →+* L[X])
    (Polynomial.C x₀ + Polynomial.X)
lemma eval_zero_shiftMap {L : Type*} [Field L] (x₀ : L) (p : L[X]) :
    Polynomial.eval 0 (shiftMap x₀ p) = Polynomial.eval x₀ p := by
  change Polynomial.eval 0
      (Polynomial.eval₂ (Polynomial.C : L →+* L[X])
        (Polynomial.C x₀ + Polynomial.X) p) = Polynomial.eval x₀ p
  rw [Polynomial.eval₂_eq_sum]
  conv_rhs => rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def]
  change (Polynomial.evalRingHom 0) (∑ n ∈ p.support,
    Polynomial.C (p.coeff n) * (Polynomial.C x₀ + Polynomial.X) ^ n) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp
lemma map_shiftMap_zero {L : Type*} [Field L]
    (R : L[X][X]) (x₀ : L) :
    (R.map (shiftMap x₀)).map (Polynomial.evalRingHom 0) =
      R.map (Polynomial.evalRingHom x₀) := by
  ext n
  simp [eval_zero_shiftMap]
def truncSeries (c : ℕ → L) (N : ℕ) : L[X] :=
  ∑ i ∈ range (N + 1), Polynomial.C (c i) * Polynomial.X ^ i
@[simp]
theorem coeff_truncSeries (c : ℕ → L) (N n : ℕ) (hn : n ≤ N) :
    (truncSeries c N).coeff n = c n := by
  simp [truncSeries, coeff_C_mul, coeff_X_pow, hn]
@[simp]
theorem eval_zero_truncSeries (c : ℕ → L) (N : ℕ) :
    (truncSeries c N).eval 0 = c 0 := by
  rw [← coeff_zero_eq_eval_zero]
  exact coeff_truncSeries c N 0 (Nat.zero_le N)
def residual (R : Polynomial (Polynomial L)) (x₀ : L)
    (c : ℕ → L) (N : ℕ) : L[X] :=
  R.eval₂ (shiftMap x₀) (truncSeries c N)
def VanishesThrough (p : L[X]) (N : ℕ) : Prop :=
  ∀ n, n ≤ N → p.coeff n = 0
def ySlope (R : Polynomial (Polynomial L)) (x₀ y₀ : L) : L :=
  R.derivative.eval₂ (Polynomial.evalRingHom x₀) y₀
def IsSimpleRootAt (R : Polynomial (Polynomial L)) (x₀ y₀ : L) : Prop :=
  R.eval₂ (Polynomial.evalRingHom x₀) y₀ = 0 ∧ ySlope R x₀ y₀ ≠ 0
theorem coefficientRecurrence
    (R : Polynomial (Polynomial L)) (x₀ y₀ : L)
    (a b : ℕ → L) (N n : ℕ) (hn : n ≤ N)
    (ha0 : a 0 = y₀) (hb0 : b 0 = y₀)
    (hprev : ∀ i, i < n → a i = b i) :
    (residual R x₀ a N).coeff n - (residual R x₀ b N).coeff n =
      ySlope R x₀ y₀ * (a n - b n) := by
  let A := truncSeries a N
  let B := truncSeries b N
  let P := R.map (shiftMap x₀)
  let D := A - B
  let Q := dividedDifference P A B
  have hres : residual R x₀ a N - residual R x₀ b N = D * Q := by
    dsimp [residual, D, Q, P, A, B]
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map]
    exact eval_sub_eval_eq_mul_dividedDifference
      (R.map (shiftMap x₀)) (truncSeries a N) (truncSeries b N)
  have hDlow : ∀ i, i < n → D.coeff i = 0 := by
    intro i hi
    simp only [D, Polynomial.coeff_sub]
    rw [coeff_truncSeries a N i (by omega), coeff_truncSeries b N i (by omega),
      hprev i hi, sub_self]
  have hDn : D.coeff n = a n - b n := by
    simp [D, A, B, coeff_truncSeries a N n hn, coeff_truncSeries b N n hn]
  have hA0 : Polynomial.eval 0 A = y₀ := by simp [A, ha0]
  have hB0 : Polynomial.eval 0 B = y₀ := by simp [B, hb0]
  have hQ0 : Q.coeff 0 = ySlope R x₀ y₀ := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    change (Polynomial.evalRingHom 0) (dividedDifference P A B) = _
    rw [map_dividedDifference]
    change dividedDifference (P.map (Polynomial.evalRingHom 0))
      (Polynomial.eval 0 A) (Polynomial.eval 0 B) = _
    rw [hA0, hB0, dividedDifference_self]
    simp only [P, ySlope]
    rw [map_shiftMap_zero, Polynomial.derivative_map,
      Polynomial.eval_map]
  calc
    _ = (residual R x₀ a N - residual R x₀ b N).coeff n := by
      rw [Polynomial.coeff_sub]
    _ = (D * Q).coeff n := by rw [hres]
    _ = D.coeff n * Q.coeff 0 := coeff_mul_of_left_vanishes_below D Q n hDlow
    _ = ySlope R x₀ y₀ * (a n - b n) := by rw [hDn, hQ0, mul_comm]
theorem simpleRoot_unique_of_vanishesThrough
    (R : Polynomial (Polynomial L)) (x₀ y₀ : L)
    (a b : ℕ → L) (N : ℕ)
    (hsimple : IsSimpleRootAt R x₀ y₀)
    (ha0 : a 0 = y₀) (hb0 : b 0 = y₀)
    (ha : VanishesThrough (residual R x₀ a N) N)
    (hb : VanishesThrough (residual R x₀ b N) N) :
    ∀ n, n ≤ N → a n = b n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact ha0.trans hb0.symm
      · have hprev : ∀ i, i < n → a i = b i := by
          intro i hi
          exact ih i hi (Nat.le_trans (Nat.le_of_lt hi) hn)
        have hz : ySlope R x₀ y₀ * (a n - b n) = 0 := by
          rw [← coefficientRecurrence R x₀ y₀ a b N n hn ha0 hb0 hprev,
            ha n hn, hb n hn, sub_self]
        have hab : a n - b n = 0 :=
          (mul_eq_zero.mp hz).resolve_left hsimple.2
        exact sub_eq_zero.mp hab
lemma residual_coeff_zero (R : Polynomial (Polynomial L)) (x₀ : L)
    (c : ℕ → L) (N : ℕ) :
    (residual R x₀ c N).coeff 0 =
      R.eval₂ (Polynomial.evalRingHom x₀) (c 0) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold residual
  rw [Polynomial.eval₂_eq_eval_map]
  change (Polynomial.evalRingHom 0)
      ((R.map (shiftMap x₀)).eval (truncSeries c N)) = _
  rw [← Polynomial.eval₂_at_apply (Polynomial.evalRingHom 0) (truncSeries c N)]
  rw [Polynomial.eval₂_eq_eval_map, map_shiftMap_zero, Polynomial.eval_map]
  simp
noncomputable def liftPoly (R : Polynomial (Polynomial L)) (x₀ y₀ : L)
    (N : ℕ) : ℕ → L[X]
  | 0 => Polynomial.C y₀
  | m + 1 =>
      let p := liftPoly R x₀ y₀ N m
      let e := (residual R x₀ (fun i => p.coeff i) N).coeff (m + 1)
      p + Polynomial.C (-e / ySlope R x₀ y₀) * Polynomial.X ^ (m + 1)
noncomputable def liftCoeff (R : Polynomial (Polynomial L)) (x₀ y₀ : L)
    (N i : ℕ) : L :=
  (liftPoly R x₀ y₀ N N).coeff i
@[simp] lemma liftPoly_coeff_zero (R : Polynomial (Polynomial L))
    (x₀ y₀ : L) (N m : ℕ) :
    (liftPoly R x₀ y₀ N m).coeff 0 = y₀ := by
  induction m with
  | zero => simp [liftPoly]
  | succ m ih =>
      simp [liftPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, ih]
@[simp] lemma liftCoeff_zero (R : Polynomial (Polynomial L))
    (x₀ y₀ : L) (N : ℕ) :
    liftCoeff R x₀ y₀ N 0 = y₀ := by
  exact liftPoly_coeff_zero R x₀ y₀ N N
lemma liftPoly_succ_coeff_lt (R : Polynomial (Polynomial L))
    (x₀ y₀ : L) (N m i : ℕ) (hi : i < m + 1) :
    (liftPoly R x₀ y₀ N (m + 1)).coeff i =
      (liftPoly R x₀ y₀ N m).coeff i := by
  simp [liftPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, ne_of_lt hi]
lemma liftPoly_succ_coeff_sub (R : Polynomial (Polynomial L))
    (x₀ y₀ : L) (N m : ℕ) :
    (liftPoly R x₀ y₀ N (m + 1)).coeff (m + 1) -
        (liftPoly R x₀ y₀ N m).coeff (m + 1) =
      -((residual R x₀ (fun i => (liftPoly R x₀ y₀ N m).coeff i) N).coeff
          (m + 1)) / ySlope R x₀ y₀ := by
  simp [liftPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
theorem liftPoly_vanishesThrough_stage
    (R : Polynomial (Polynomial L)) (x₀ y₀ : L) (N m : ℕ)
    (hsimple : IsSimpleRootAt R x₀ y₀) (hm : m ≤ N) :
    VanishesThrough
      (residual R x₀ (fun i => (liftPoly R x₀ y₀ N m).coeff i) N) m := by
  induction m with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      rw [residual_coeff_zero, liftPoly_coeff_zero]
      exact hsimple.1
  | succ m ih =>
      have hmN : m ≤ N := by omega
      have hold := ih hmN
      intro i hi
      by_cases hitop : i = m + 1
      · subst i
        let old : ℕ → L := fun j => (liftPoly R x₀ y₀ N m).coeff j
        let new : ℕ → L := fun j => (liftPoly R x₀ y₀ N (m + 1)).coeff j
        have hprev : ∀ j, j < m + 1 → new j = old j := by
          intro j hj
          exact liftPoly_succ_coeff_lt R x₀ y₀ N m j hj
        have hnew0 : new 0 = y₀ := liftPoly_coeff_zero R x₀ y₀ N (m + 1)
        have hold0 : old 0 = y₀ := liftPoly_coeff_zero R x₀ y₀ N m
        have hrec := coefficientRecurrence R x₀ y₀ new old N (m + 1)
          (by omega) hnew0 hold0 hprev
        have hsub : new (m + 1) - old (m + 1) =
            -((residual R x₀ old N).coeff (m + 1)) / ySlope R x₀ y₀ := by
          exact liftPoly_succ_coeff_sub R x₀ y₀ N m
        rw [hsub] at hrec
        have hslope : ySlope R x₀ y₀ ≠ 0 := hsimple.2
        field_simp [hslope] at hrec
        change (residual R x₀ new N).coeff (m + 1) = 0
        linear_combination hrec
      · have hiold : i ≤ m := by omega
        let old : ℕ → L := fun j => (liftPoly R x₀ y₀ N m).coeff j
        let new : ℕ → L := fun j => (liftPoly R x₀ y₀ N (m + 1)).coeff j
        have hprev : ∀ j, j < i → new j = old j := by
          intro j hj
          exact liftPoly_succ_coeff_lt R x₀ y₀ N m j (by omega)
        have hnew0 : new 0 = y₀ := liftPoly_coeff_zero R x₀ y₀ N (m + 1)
        have hold0 : old 0 = y₀ := liftPoly_coeff_zero R x₀ y₀ N m
        have hsame : new i = old i :=
          liftPoly_succ_coeff_lt R x₀ y₀ N m i (by omega)
        have hrec := coefficientRecurrence R x₀ y₀ new old N i
          (by omega) hnew0 hold0 hprev
        rw [hsame, sub_self, mul_zero] at hrec
        exact (sub_eq_zero.mp hrec).trans (hold i hiold)
theorem liftCoeff_vanishesThrough
    (R : Polynomial (Polynomial L)) (x₀ y₀ : L) (N : ℕ)
    (hsimple : IsSimpleRootAt R x₀ y₀) :
    VanishesThrough (residual R x₀ (liftCoeff R x₀ y₀ N) N) N := by
  exact liftPoly_vanishesThrough_stage R x₀ y₀ N N hsimple (Nat.le_refl N)
theorem exists_finiteHenselLift
    (R : Polynomial (Polynomial L)) (x₀ y₀ : L) (N : ℕ)
    (hsimple : IsSimpleRootAt R x₀ y₀) :
    ∃ c : ℕ → L, c 0 = y₀ ∧
      VanishesThrough (residual R x₀ c N) N := by
  exact ⟨liftCoeff R x₀ y₀ N, liftCoeff_zero R x₀ y₀ N,
    liftCoeff_vanishesThrough R x₀ y₀ N hsimple⟩
def TaylorCoeff (P : L[X]) (x₀ : L) (n : ℕ) : L :=
  (P.comp (Polynomial.C x₀ + Polynomial.X)).coeff n
@[simp] lemma TaylorCoeff_zero (P : L[X]) (x₀ : L) :
    TaylorCoeff P x₀ 0 = P.eval x₀ := by
  simp [TaylorCoeff, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
lemma shiftMap_apply (P : L[X]) (x₀ : L) :
    shiftMap x₀ P = P.comp (Polynomial.C x₀ + Polynomial.X) := by
  rfl
theorem truncSeries_TaylorCoeff_eq_shift
    (P : L[X]) (x₀ : L) (k : ℕ) (hdeg : P.natDegree ≤ k) :
    truncSeries (TaylorCoeff P x₀) k =
      P.comp (Polynomial.C x₀ + Polynomial.X) := by
  let S := P.comp (Polynomial.C x₀ + Polynomial.X)
  have hinner : (Polynomial.C x₀ + Polynomial.X : L[X]).natDegree = 1 := by
    simp [add_comm]
  have hS : S.natDegree < k + 1 := by
    dsimp [S]
    rw [Polynomial.natDegree_comp, hinner, mul_one]
    omega
  calc
    truncSeries (TaylorCoeff P x₀) k =
        ∑ i ∈ range (k + 1), Polynomial.monomial i (S.coeff i) := by
      simp only [truncSeries, TaylorCoeff, S, Polynomial.C_mul_X_pow_eq_monomial]
    _ = S := (Polynomial.as_sum_range' S (k + 1) hS).symm
    _ = P.comp (Polynomial.C x₀ + Polynomial.X) := rfl
theorem TaylorCoeff_vanishesThrough
    (R : Polynomial (Polynomial L)) (P : L[X]) (x₀ : L) (k : ℕ)
    (hdeg : P.natDegree ≤ k) (hExact : R.eval P = 0) :
    VanishesThrough (residual R x₀ (TaylorCoeff P x₀) k) k := by
  have htr := truncSeries_TaylorCoeff_eq_shift P x₀ k hdeg
  have hzero : residual R x₀ (TaylorCoeff P x₀) k = 0 := by
    unfold residual
    rw [htr, ← shiftMap_apply P x₀]
    rw [Polynomial.eval₂_at_apply]
    rw [hExact, map_zero]
  intro n hn
  rw [hzero]
  simp
theorem lift_eq_TaylorCoeff
    (R : Polynomial (Polynomial L)) (P : L[X]) (x₀ y₀ : L)
    (a : ℕ → L) (k : ℕ)
    (hdeg : P.natDegree ≤ k) (hExact : R.eval P = 0)
    (hsimple : IsSimpleRootAt R x₀ y₀)
    (ha0 : a 0 = y₀) (hP0 : P.eval x₀ = y₀)
    (ha : VanishesThrough (residual R x₀ a k) k) :
    ∀ n, n ≤ k → a n = TaylorCoeff P x₀ n := by
  apply simpleRoot_unique_of_vanishesThrough R x₀ y₀ a
    (TaylorCoeff P x₀) k hsimple ha0
  · simpa using hP0
  · exact ha
  · exact TaylorCoeff_vanishesThrough R P x₀ k hdeg hExact
end
end ProximityPrize.SubmissionLower.FiniteHensel
