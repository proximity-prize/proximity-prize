import ProximityPrize.SubmissionLower.BCHKSParameters6401

/-!
# A rational degree-three spherical bound at score 64.01

This file records the degree-three Levenshtein/Delsarte certificate needed for
constant-cardinality agreement sets at the score-64.01 parameters.  The
geometry is performed over `ℚ`: it concerns centered incidence vectors and
is independent of the benchmark coefficient field.

The eventual combinatorial endpoint is that a family of `185354`-subsets of a
`262144`-set with pairwise intersections at most `131071` has cardinality at
most `17045844`.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSSphericalL3Bound6401

open scoped BigOperators
open Finset

def sphereN : Nat := 262144
def sphereDim : Nat := sphereN - 1
def sphereA : Nat := bchksAgreements6401
def sphereE : Nat := sphereN - sphereA
def sphereK : Nat := 131071

/-- The normalized maximum inner product of two centered incidence vectors. -/
def maxInner : ℚ :=
  (sphereN * sphereK - sphereA ^ 2 : ℕ) / (sphereA * sphereE : ℕ)

/-- The double root of the optimized degree-three LP polynomial. -/
def levenRoot : ℚ :=
  -(1 + maxInner) / (1 + sphereDim * maxInner)

theorem concrete_parameters :
    sphereDim = 262143 ∧ sphereA = 185354 ∧ sphereE = 76790 ∧
      maxInner = 842727 / 3558333415 ∧
      levenRoot = -1779588071 / 112236658688 := by
  norm_num [sphereDim, sphereN, sphereA, sphereE, bchksAgreements6401,
    maxInner, sphereK, levenRoot]

theorem leven_interval_signs :
    0 < maxInner ∧ maxInner < 1 ∧
      0 < 1 - sphereDim * maxInner ^ 2 ∧
      levenRoot < -(maxInner / 2) := by
  norm_num [sphereDim, sphereN, maxInner, sphereA, sphereE,
    bchksAgreements6401, sphereK, levenRoot]

/-- Coefficients of `(T-s)(T-r)^2` in the normalized degree-`0,1,2,3`
Gegenbauer basis for sphere dimension `m`. -/
def gegen0 (m : ℚ) (s r : ℚ) : ℚ := -(s + 2 * r) / m - s * r ^ 2
def gegen1 (m : ℚ) (s r : ℚ) : ℚ := 3 / (m + 2) + 2 * s * r + r ^ 2
def gegen2 (m : ℚ) (s r : ℚ) : ℚ := -(s + 2 * r) * (m - 1) / m
def gegen3 (m : ℚ) : ℚ := (m - 1) / (m + 2)

theorem concrete_gegenbauer_coefficients_positive :
    0 < gegen0 sphereDim maxInner levenRoot ∧
      0 < gegen1 sphereDim maxInner levenRoot ∧
      0 < gegen2 sphereDim maxInner levenRoot ∧
      0 < gegen3 sphereDim := by
  norm_num [gegen0, gegen1, gegen2, gegen3, sphereDim, sphereN,
    maxInner, sphereA, sphereE, bchksAgreements6401, sphereK, levenRoot]

/-- Exact optimized `L_3` ratio. -/
def levenRatio : ℚ :=
  sphereDim * (1 - maxInner) * (2 + (sphereDim + 1) * maxInner) /
    (1 - sphereDim * maxInner ^ 2)

theorem levenRatio_exact :
    levenRatio =
      15189753906177057020510208 / 891111833615504327 ∧
      levenRatio < 17045845 := by
  norm_num [levenRatio, sphereDim, sphereN, maxInner, sphereA, sphereE,
    bchksAgreements6401, sphereK]

def gegenQ1 (t : ℚ) : ℚ := t
def gegenQ2 (t : ℚ) : ℚ :=
  (sphereDim * t ^ 2 - 1) / (sphereDim - 1)
def gegenQ3 (t : ℚ) : ℚ :=
  ((sphereDim + 2) * t ^ 3 - 3 * t) / (sphereDim - 1)
def levenPoly (t : ℚ) : ℚ :=
  (t - maxInner) * (t - levenRoot) ^ 2

theorem levenPoly_gegenbauer_expansion (t : ℚ) :
    levenPoly t = gegen0 sphereDim maxInner levenRoot +
      gegen1 sphereDim maxInner levenRoot * gegenQ1 t +
      gegen2 sphereDim maxInner levenRoot * gegenQ2 t +
      gegen3 sphereDim * gegenQ3 t := by
  norm_num [levenPoly, gegen0, gegen1, gegen2, gegen3, gegenQ1, gegenQ2,
    gegenQ3, sphereDim, sphereN]
  ring

theorem levenPoly_nonpos {t : ℚ} (ht : t ≤ maxInner) :
    levenPoly t ≤ 0 := by
  unfold levenPoly
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sq_nonneg _)

theorem levenPoly_one_positive : 0 < levenPoly 1 := by
  norm_num [levenPoly, maxInner, levenRoot, sphereDim, sphereN, sphereA,
    sphereE, sphereK, bchksAgreements6401]

theorem levenPoly_one_div_gegen0 :
    levenPoly 1 / gegen0 sphereDim maxInner levenRoot = levenRatio := by
  norm_num [levenPoly, gegen0, levenRatio, maxInner, levenRoot, sphereDim,
    sphereN, sphereA, sphereE, sphereK, bchksAgreements6401]

/-! ## A finite rational Gram interface -/

section LP

variable {owners : Type*} [Fintype owners]

/-- An abstract normalized Gram kernel.  The three moment hypotheses below
are exactly the rational sums-of-squares supplied by the first three
Gegenbauer kernels. -/
structure RationalSphereGram where
  gram : owners → owners → ℚ
  symm : ∀ i j, gram i j = gram j i
  diagonal : ∀ i, gram i i = 1
  offDiagonal : ∀ i j, i ≠ j → gram i j ≤ maxInner
  moment1 : 0 ≤ ∑ i, ∑ j, gram i j
  moment2 : 0 ≤ ∑ i, ∑ j,
    (sphereDim * gram i j ^ 2 - 1) / (sphereDim - 1)
  moment3 : 0 ≤ ∑ i, ∑ j,
    ((sphereDim + 2) * gram i j ^ 3 - 3 * gram i j) /
      (sphereDim - 1)

theorem RationalSphereGram.sum_le_diagonal
    (G : RationalSphereGram (owners := owners)) :
    ∑ i, ∑ j, levenPoly (G.gram i j) ≤
      Fintype.card owners * levenPoly 1 := by
  classical
  letI : DecidableEq owners := Classical.decEq owners
  calc
    ∑ i, ∑ j, levenPoly (G.gram i j) ≤
        ∑ i, ∑ j, if i = j then levenPoly 1 else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        simp [G.diagonal]
      · simp only [hij, ↓reduceIte]
        exact levenPoly_nonpos (G.offDiagonal i j hij)
    _ = Fintype.card owners * levenPoly 1 := by simp

theorem RationalSphereGram.sum_ge_constant
    (G : RationalSphereGram (owners := owners)) :
    (Fintype.card owners : ℚ) ^ 2 *
        gegen0 sphereDim maxInner levenRoot ≤
      ∑ i, ∑ j, levenPoly (G.gram i j) := by
  classical
  letI : DecidableEq owners := Classical.decEq owners
  let c0 := gegen0 sphereDim maxInner levenRoot
  let c1 := gegen1 sphereDim maxInner levenRoot
  let c2 := gegen2 sphereDim maxInner levenRoot
  let c3 := gegen3 sphereDim
  have hc : 0 ≤ c1 ∧ 0 ≤ c2 ∧ 0 ≤ c3 := by
    have h := concrete_gegenbauer_coefficients_positive
    exact ⟨h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩
  have h1 : 0 ≤ c1 * (∑ i, ∑ j, gegenQ1 (G.gram i j)) :=
    mul_nonneg hc.1 G.moment1
  have h2 : 0 ≤ c2 * (∑ i, ∑ j, gegenQ2 (G.gram i j)) :=
    mul_nonneg hc.2.1 G.moment2
  have h3 : 0 ≤ c3 * (∑ i, ∑ j, gegenQ3 (G.gram i j)) :=
    mul_nonneg hc.2.2 G.moment3
  have hexpand :
      (∑ i, ∑ j, levenPoly (G.gram i j)) =
        (Fintype.card owners : ℚ) ^ 2 * c0 +
          c1 * (∑ i, ∑ j, gegenQ1 (G.gram i j)) +
          c2 * (∑ i, ∑ j, gegenQ2 (G.gram i j)) +
          c3 * (∑ i, ∑ j, gegenQ3 (G.gram i j)) := by
    simp_rw [levenPoly_gegenbauer_expansion]
    simp only [Finset.sum_add_distrib]
    simp [c0, c1, c2, c3, Finset.mul_sum, Finset.sum_mul]
    ring
  rw [hexpand]
  dsimp [c0] at ⊢
  nlinarith

theorem RationalSphereGram.card_le_17045844
    (G : RationalSphereGram (owners := owners)) :
    Fintype.card owners ≤ 17045844 := by
  classical
  letI : DecidableEq owners := Classical.decEq owners
  have hlow := G.sum_ge_constant
  have hupp := G.sum_le_diagonal
  have hc0 : 0 < gegen0 sphereDim maxInner levenRoot :=
    concrete_gegenbauer_coefficients_positive.1
  have hcard_nonneg : (0 : ℚ) ≤ Fintype.card owners := by positivity
  by_contra hnot
  have hlarge : (17045845 : ℚ) ≤ Fintype.card owners := by
    exact_mod_cast (show 17045845 ≤ Fintype.card owners by omega)
  have hratio := levenRatio_exact.2
  have hpoly_ratio := levenPoly_one_div_gegen0
  have hdiv : levenPoly 1 < (17045845 : ℚ) *
      gegen0 sphereDim maxInner levenRoot := by
    rw [← div_lt_iff₀ hc0, hpoly_ratio]
    exact hratio
  have hposcard : (0 : ℚ) < Fintype.card owners := lt_of_lt_of_le (by norm_num) hlarge
  have hchain :
      (Fintype.card owners : ℚ) ^ 2 *
          gegen0 sphereDim maxInner levenRoot ≤
        (Fintype.card owners : ℚ) * levenPoly 1 :=
    le_trans hlow hupp
  have : (Fintype.card owners : ℚ) * levenPoly 1 <
      (Fintype.card owners : ℚ) ^ 2 *
        gegen0 sphereDim maxInner levenRoot := by
    have hm := mul_lt_mul_of_pos_left
      (lt_of_lt_of_le hdiv (mul_le_mul_of_nonneg_right hlarge hc0.le)) hposcard
    nlinarith
  exact (not_lt_of_ge hchain) this

end LP

/-! ## Rational sums of squares for centered coordinate vectors -/

section RationalMoments

variable {coords owners : Type*} [Fintype coords] [Fintype owners]

def rationalDot (u v : coords → ℚ) : ℚ := ∑ x, u x * v x

theorem rationalDot_comm (u v : coords → ℚ) :
    rationalDot u v = rationalDot v u := by
  unfold rationalDot
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem sum_rationalDot_eq_sum_sq (v : owners → coords → ℚ) :
    (∑ i, ∑ j, rationalDot (v i) (v j)) =
      ∑ x, (∑ i, v i x) ^ 2 := by
  calc
    (∑ i, ∑ j, rationalDot (v i) (v j)) =
        ∑ i, ∑ j, ∑ x, v i x * v j x := rfl
    _ = ∑ i, ∑ x, ∑ j, v i x * v j x := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ j, v i x * v j x := Finset.sum_comm
    _ = ∑ x, (∑ i, v i x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_two, Finset.sum_mul_sum]

def aggregateTensor2 (v : owners → coords → ℚ) (x y : coords) : ℚ :=
  ∑ i, v i x * v i y

theorem sum_rationalDot_sq_eq_sum_aggregateTensor2_sq
    (v : owners → coords → ℚ) :
    (∑ i, ∑ j, rationalDot (v i) (v j) ^ 2) =
      ∑ x, ∑ y, aggregateTensor2 v x y ^ 2 := by
  have hdot (i j : owners) :
      rationalDot (v i) (v j) ^ 2 =
        ∑ x, ∑ y, (v i x * v i y) * (v j x * v j y) := by
    unfold rationalDot
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hdot]
  calc
    (∑ i, ∑ j, ∑ x, ∑ y,
        (v i x * v i y) * (v j x * v j y)) =
        ∑ i, ∑ x, ∑ j, ∑ y,
          (v i x * v i y) * (v j x * v j y) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ j, ∑ y,
          (v i x * v i y) * (v j x * v j y) := Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ j,
          (v i x * v i y) * (v j x * v j y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i, ∑ j,
          (v i x * v i y) * (v j x * v j y) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, aggregateTensor2 v x y ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [aggregateTensor2, pow_two, Finset.sum_mul_sum]

def aggregateTensor3 (v : owners → coords → ℚ) (x y z : coords) : ℚ :=
  ∑ i, v i x * v i y * v i z

theorem sum_rationalDot_cube_eq_sum_aggregateTensor3_sq
    (v : owners → coords → ℚ) :
    (∑ i, ∑ j, rationalDot (v i) (v j) ^ 3) =
      ∑ x, ∑ y, ∑ z, aggregateTensor3 v x y z ^ 2 := by
  have hdot (i j : owners) :
      rationalDot (v i) (v j) ^ 3 =
        ∑ x, ∑ y, ∑ z,
          (v i x * v i y * v i z) * (v j x * v j y * v j z) := by
    unfold rationalDot
    rw [pow_succ, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  simp_rw [hdot]
  calc
    (∑ i, ∑ j, ∑ x, ∑ y, ∑ z,
        (v i x * v i y * v i z) * (v j x * v j y * v j z)) =
        ∑ i, ∑ x, ∑ j, ∑ y, ∑ z,
          (v i x * v i y * v i z) * (v j x * v j y * v j z) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ j, ∑ y, ∑ z,
          (v i x * v i y * v i z) * (v j x * v j y * v j z) :=
      Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ j, ∑ z,
          (v i x * v i y * v i z) * (v j x * v j y * v j z) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i, ∑ j, ∑ z,
          (v i x * v i y * v i z) * (v j x * v j y * v j z) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i, ∑ z, ∑ j,
          (v i x * v i y * v i z) * (v j x * v j y * v j z) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ z, ∑ i, ∑ j,
          (v i x * v i y * v i z) * (v j x * v j y * v j z) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ z, aggregateTensor3 v x y z ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      rw [aggregateTensor3, pow_two, Finset.sum_mul_sum]

end RationalMoments

/-! ## Centered incidence vectors -/

abbrev SphereCoord := Fin sphereN

def incidenceIndicator (A : Finset SphereCoord) (x : SphereCoord) : ℚ :=
  if x ∈ A then 1 else 0

def centeredIncidence (A : Finset SphereCoord) (x : SphereCoord) : ℚ :=
  sphereN * incidenceIndicator A x - sphereA

def centeredNormSq : ℚ := sphereN * sphereA * sphereE

theorem sum_incidenceIndicator (A : Finset SphereCoord) :
    ∑ x, incidenceIndicator A x = A.card := by
  classical
  simp [incidenceIndicator, Finset.sum_boole]

theorem sum_incidenceIndicator_mul (A B : Finset SphereCoord) :
    ∑ x, incidenceIndicator A x * incidenceIndicator B x = (A ∩ B).card := by
  classical
  simp only [incidenceIndicator]
  calc
    (∑ x : SphereCoord,
        (if x ∈ A then (1 : ℚ) else 0) * (if x ∈ B then 1 else 0)) =
        ∑ x : SphereCoord, if x ∈ A ∩ B then (1 : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
        simp [hxA, hxB]
    _ = (A ∩ B).card := sum_incidenceIndicator (A ∩ B)

theorem centeredIncidence_sum_zero (A : Finset SphereCoord)
    (hA : A.card = sphereA) :
    ∑ x, centeredIncidence A x = 0 := by
  rw [show (∑ x, centeredIncidence A x) =
      sphereN * (∑ x, incidenceIndicator A x) -
        (Fintype.card SphereCoord : ℚ) * sphereA by
    simp [centeredIncidence, Finset.sum_sub_distrib, Finset.mul_sum]]
  rw [sum_incidenceIndicator, hA]
  norm_num [sphereN]

theorem centeredIncidence_dot (A B : Finset SphereCoord)
    (hA : A.card = sphereA) (hB : B.card = sphereA) :
    rationalDot (centeredIncidence A) (centeredIncidence B) =
      sphereN * (sphereN * (A ∩ B).card - sphereA ^ 2) := by
  rw [show rationalDot (centeredIncidence A) (centeredIncidence B) =
      sphereN ^ 2 * (∑ x, incidenceIndicator A x * incidenceIndicator B x) -
        sphereN * sphereA * (∑ x, incidenceIndicator A x) -
        sphereN * sphereA * (∑ x, incidenceIndicator B x) +
        (Fintype.card SphereCoord : ℚ) * sphereA ^ 2 by
    unfold rationalDot
    calc
      (∑ x, centeredIncidence A x * centeredIncidence B x) =
          ∑ x, (sphereN ^ 2 *
              (incidenceIndicator A x * incidenceIndicator B x) -
            (sphereN * sphereA) * incidenceIndicator A x -
            (sphereN * sphereA) * incidenceIndicator B x + sphereA ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [centeredIncidence]
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        simp [sphereN]]
  rw [sum_incidenceIndicator_mul, sum_incidenceIndicator,
    sum_incidenceIndicator, hA, hB]
  norm_num [sphereN]
  ring

theorem centeredIncidence_norm (A : Finset SphereCoord)
    (hA : A.card = sphereA) :
    rationalDot (centeredIncidence A) (centeredIncidence A) = centeredNormSq := by
  rw [centeredIncidence_dot A A hA hA, Finset.inter_self, hA]
  norm_num [centeredNormSq, sphereN, sphereA, sphereE, bchksAgreements6401]

/-! The rational orthogonal projector onto the zero-coordinate-sum
hyperplane. -/
def centeredProjector (x y : SphereCoord) : ℚ :=
  (if x = y then 1 else 0) - 1 / sphereN

theorem centeredProjector_symm (x y : SphereCoord) :
    centeredProjector x y = centeredProjector y x := by
  simp only [centeredProjector]
  by_cases h : x = y
  · subst y
    rfl
  · have h' : y ≠ x := Ne.symm h
    simp only [h, h', ↓reduceIte]

theorem centeredProjector_row_sum (x : SphereCoord) :
    ∑ y, centeredProjector x y = 0 := by
  classical
  unfold centeredProjector
  rw [Finset.sum_sub_distrib]
  simp
  norm_num [sphereN]

theorem centeredProjector_apply (u : SphereCoord → ℚ)
    (hu : ∑ x, u x = 0) (x : SphereCoord) :
    ∑ y, centeredProjector x y * u y = u x := by
  classical
  calc
    (∑ y, centeredProjector x y * u y) =
        (∑ y, (if x = y then (1 : ℚ) else 0) * u y) -
          (1 / sphereN) * (∑ y, u y) := by
      unfold centeredProjector
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = u x := by simp [hu]

theorem centeredProjector_row_sq (x : SphereCoord) :
    ∑ y, centeredProjector x y ^ 2 = centeredProjector x x := by
  classical
  calc
    (∑ y, centeredProjector x y ^ 2) =
        ∑ y, (centeredProjector x y *
          (if x = y then (1 : ℚ) else 0) -
            (1 / sphereN) * centeredProjector x y) := by
      apply Finset.sum_congr rfl
      intro y _
      unfold centeredProjector
      ring
    _ = centeredProjector x x -
        (1 / sphereN) * (∑ y, centeredProjector x y) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      simp
    _ = centeredProjector x x := by rw [centeredProjector_row_sum]; simp

theorem centeredProjector_sq_sum :
    ∑ x, ∑ y, centeredProjector x y ^ 2 = sphereDim := by
  classical
  simp_rw [centeredProjector_row_sq]
  norm_num [centeredProjector, sphereDim, sphereN]

theorem centeredProjector_bilinear (u v : SphereCoord → ℚ)
    (hv : ∑ x, v x = 0) :
    ∑ x, ∑ y, u x * centeredProjector x y * v y = rationalDot u v := by
  calc
    (∑ x, ∑ y, u x * centeredProjector x y * v y) =
        ∑ x, u x * (∑ y, centeredProjector x y * v y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ x, u x * v x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [centeredProjector_apply v hv x]
    _ = rationalDot u v := by
      unfold rationalDot
      apply Finset.sum_congr rfl
      intro x _
      ring

section CenteredFamily

variable {owners : Type*} [Fintype owners]

structure CenteredVectorFamily where
  vec : owners → SphereCoord → ℚ
  sum_zero : ∀ i, ∑ x, vec i x = 0
  norm : ∀ i, rationalDot (vec i) (vec i) = centeredNormSq

def CenteredVectorFamily.gram (V : CenteredVectorFamily (owners := owners))
    (i j : owners) : ℚ := rationalDot (V.vec i) (V.vec j) / centeredNormSq

theorem centeredNormSq_pos : 0 < centeredNormSq := by
  norm_num [centeredNormSq, sphereN, sphereA, sphereE, bchksAgreements6401]

theorem CenteredVectorFamily.gram_diagonal
    (V : CenteredVectorFamily (owners := owners)) (i : owners) :
    V.gram i i = 1 := by
  rw [CenteredVectorFamily.gram, V.norm]
  exact div_self centeredNormSq_pos.ne'

theorem CenteredVectorFamily.gram_symm
    (V : CenteredVectorFamily (owners := owners)) (i j : owners) :
    V.gram i j = V.gram j i := by
  unfold CenteredVectorFamily.gram
  rw [rationalDot_comm]

theorem aggregateTensor2_projector_inner
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, aggregateTensor2 V.vec x y * centeredProjector x y) =
      Fintype.card owners * centeredNormSq := by
  classical
  calc
    (∑ x, ∑ y, aggregateTensor2 V.vec x y * centeredProjector x y) =
        ∑ x, ∑ y, ∑ i,
          V.vec i x * centeredProjector x y * V.vec i y := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [aggregateTensor2, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ x, ∑ i, ∑ y,
          V.vec i x * centeredProjector x y * V.vec i y := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y,
          V.vec i x * centeredProjector x y * V.vec i y := Finset.sum_comm
    _ = ∑ i, rationalDot (V.vec i) (V.vec i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact centeredProjector_bilinear (V.vec i) (V.vec i) (V.sum_zero i)
    _ = Fintype.card owners * centeredNormSq := by simp [V.norm]

def CenteredVectorFamily.residualTensor2
    (V : CenteredVectorFamily (owners := owners)) (x y : SphereCoord) : ℚ :=
  aggregateTensor2 V.vec x y -
    ((Fintype.card owners : ℚ) * centeredNormSq / sphereDim) *
      centeredProjector x y

theorem CenteredVectorFamily.raw_moment2_nonneg
    (V : CenteredVectorFamily (owners := owners)) :
    0 ≤ sphereDim *
        (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 2) -
      (Fintype.card owners : ℚ) ^ 2 * centeredNormSq ^ 2 := by
  have hsos : 0 ≤ ∑ x, ∑ y, V.residualTensor2 x y ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hid :
      (∑ x, ∑ y, V.residualTensor2 x y ^ 2) =
        (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 2) -
          (Fintype.card owners : ℚ) ^ 2 * centeredNormSq ^ 2 / sphereDim := by
    rw [sum_rationalDot_sq_eq_sum_aggregateTensor2_sq]
    let c : ℚ := (Fintype.card owners : ℚ) * centeredNormSq / sphereDim
    have hcross :
        (∑ x, ∑ y, 2 * aggregateTensor2 V.vec x y *
          (c * centeredProjector x y)) =
          2 * c * (∑ x, ∑ y,
            aggregateTensor2 V.vec x y * centeredProjector x y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    have hsquare :
        (∑ x, ∑ y, (c * centeredProjector x y) ^ 2) =
          c ^ 2 * (∑ x, ∑ y, centeredProjector x y ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    unfold CenteredVectorFamily.residualTensor2
    change (∑ x, ∑ y,
      (aggregateTensor2 V.vec x y - c * centeredProjector x y) ^ 2) = _
    simp_rw [sub_sq]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hcross, hsquare, aggregateTensor2_projector_inner V,
      centeredProjector_sq_sum]
    dsimp [c]
    norm_num [sphereDim, sphereN]
    ring
  rw [hid] at hsos
  norm_num [sphereDim, sphereN] at hsos ⊢
  linarith

def CenteredVectorFamily.ownerSum
    (V : CenteredVectorFamily (owners := owners)) (x : SphereCoord) : ℚ :=
  ∑ i, V.vec i x

theorem CenteredVectorFamily.ownerSum_sum_zero
    (V : CenteredVectorFamily (owners := owners)) :
    ∑ x, V.ownerSum x = 0 := by
  calc
    (∑ x, V.ownerSum x) = ∑ x, ∑ i, V.vec i x := rfl
    _ = ∑ i, ∑ x, V.vec i x := Finset.sum_comm
    _ = 0 := by simp [V.sum_zero]

theorem centeredProjector_composition (y z : SphereCoord) :
    ∑ x, centeredProjector x y * centeredProjector x z =
      centeredProjector y z := by
  have hcol : ∑ x, centeredProjector x z = 0 := by
    calc
      (∑ x, centeredProjector x z) =
          ∑ x, centeredProjector z x := by
        apply Finset.sum_congr rfl
        intro x _
        exact centeredProjector_symm x z
      _ = 0 := centeredProjector_row_sum z
  calc
    (∑ x, centeredProjector x y * centeredProjector x z) =
        ∑ x, centeredProjector y x * centeredProjector x z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [centeredProjector_symm x y]
    _ = centeredProjector y z := centeredProjector_apply _ hcol y

theorem aggregateTensor3_contract
    (V : CenteredVectorFamily (owners := owners)) (z : SphereCoord) :
    (∑ x, ∑ y,
      aggregateTensor3 V.vec x y z * centeredProjector x y) =
      centeredNormSq * V.ownerSum z := by
  calc
    (∑ x, ∑ y,
      aggregateTensor3 V.vec x y z * centeredProjector x y) =
        ∑ x, ∑ y, ∑ i,
          (V.vec i x * centeredProjector x y * V.vec i y) * V.vec i z := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [aggregateTensor3, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ x, ∑ i, ∑ y,
          (V.vec i x * centeredProjector x y * V.vec i y) * V.vec i z := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y,
          (V.vec i x * centeredProjector x y * V.vec i y) * V.vec i z :=
      Finset.sum_comm
    _ = ∑ i, rationalDot (V.vec i) (V.vec i) * V.vec i z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← centeredProjector_bilinear (V.vec i) (V.vec i) (V.sum_zero i)]
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = centeredNormSq * V.ownerSum z := by
      simp_rw [V.norm]
      unfold CenteredVectorFamily.ownerSum
      rw [Finset.mul_sum]

def CenteredVectorFamily.traceTensor
    (V : CenteredVectorFamily (owners := owners))
    (x y z : SphereCoord) : ℚ :=
  centeredProjector x y * V.ownerSum z +
    centeredProjector x z * V.ownerSum y +
    centeredProjector y z * V.ownerSum x

def CenteredVectorFamily.residualTensor3
    (V : CenteredVectorFamily (owners := owners))
    (x y z : SphereCoord) : ℚ :=
  aggregateTensor3 V.vec x y z -
    centeredNormSq / (sphereDim + 2) * V.traceTensor x y z

theorem aggregateTensor3_swap23 (v : owners → SphereCoord → ℚ)
    (x y z : SphereCoord) :
    aggregateTensor3 v x y z = aggregateTensor3 v x z y := by
  unfold aggregateTensor3
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem aggregateTensor3_cycle (v : owners → SphereCoord → ℚ)
    (x y z : SphereCoord) :
    aggregateTensor3 v x y z = aggregateTensor3 v y z x := by
  unfold aggregateTensor3
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem CenteredVectorFamily.tensor_trace_xy
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec x y z *
      (centeredProjector x y * V.ownerSum z)) =
      centeredNormSq * (∑ z, V.ownerSum z ^ 2) := by
  calc
    (∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec x y z *
      (centeredProjector x y * V.ownerSum z)) =
        ∑ x, ∑ z, ∑ y, aggregateTensor3 V.vec x y z *
          (centeredProjector x y * V.ownerSum z) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, aggregateTensor3 V.vec x y z *
          (centeredProjector x y * V.ownerSum z) := Finset.sum_comm
    _ = ∑ z, (∑ x, ∑ y,
          aggregateTensor3 V.vec x y z * centeredProjector x y) *
            V.ownerSum z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ z, (centeredNormSq * V.ownerSum z) * V.ownerSum z := by
      simp_rw [aggregateTensor3_contract V]
    _ = centeredNormSq * (∑ z, V.ownerSum z ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

theorem CenteredVectorFamily.tensor_trace_xz
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec x y z *
      (centeredProjector x z * V.ownerSum y)) =
      centeredNormSq * (∑ y, V.ownerSum y ^ 2) := by
  calc
    (∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec x y z *
      (centeredProjector x z * V.ownerSum y)) =
        ∑ y, ∑ x, ∑ z, aggregateTensor3 V.vec x z y *
          (centeredProjector x z * V.ownerSum y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      rw [aggregateTensor3_swap23]
    _ = ∑ y, (∑ x, ∑ z,
          aggregateTensor3 V.vec x z y * centeredProjector x z) *
            V.ownerSum y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑ y, (centeredNormSq * V.ownerSum y) * V.ownerSum y := by
      simp_rw [aggregateTensor3_contract V]
    _ = centeredNormSq * (∑ y, V.ownerSum y ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

theorem CenteredVectorFamily.tensor_trace_yz
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec x y z *
      (centeredProjector y z * V.ownerSum x)) =
      centeredNormSq * (∑ x, V.ownerSum x ^ 2) := by
  calc
    (∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec x y z *
      (centeredProjector y z * V.ownerSum x)) =
        ∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec y z x *
          (centeredProjector y z * V.ownerSum x) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      rw [aggregateTensor3_cycle]
    _ = ∑ x, (∑ y, ∑ z,
          aggregateTensor3 V.vec y z x * centeredProjector y z) *
            V.ownerSum x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑ x, (centeredNormSq * V.ownerSum x) * V.ownerSum x := by
      simp_rw [aggregateTensor3_contract V]
    _ = centeredNormSq * (∑ x, V.ownerSum x ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem CenteredVectorFamily.tensor_trace_inner
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z, aggregateTensor3 V.vec x y z *
      V.traceTensor x y z) =
      3 * centeredNormSq * (∑ x, V.ownerSum x ^ 2) := by
  unfold CenteredVectorFamily.traceTensor
  simp_rw [mul_add]
  simp only [Finset.sum_add_distrib]
  rw [V.tensor_trace_xy, V.tensor_trace_xz, V.tensor_trace_yz]
  ring

theorem CenteredVectorFamily.traceTerm_xy_sq
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x y * V.ownerSum z) ^ 2) =
      sphereDim * (∑ z, V.ownerSum z ^ 2) := by
  calc
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x y * V.ownerSum z) ^ 2) =
        ∑ x, ∑ y, centeredProjector x y ^ 2 *
          (∑ z, V.ownerSum z ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = (∑ x, ∑ y, centeredProjector x y ^ 2) *
        (∑ z, V.ownerSum z ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = sphereDim * (∑ z, V.ownerSum z ^ 2) := by
      rw [centeredProjector_sq_sum]

theorem CenteredVectorFamily.traceTerm_xz_sq
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x z * V.ownerSum y) ^ 2) =
      sphereDim * (∑ y, V.ownerSum y ^ 2) := by
  calc
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x z * V.ownerSum y) ^ 2) =
        ∑ x, ∑ z, ∑ y,
          (centeredProjector x z * V.ownerSum y) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = sphereDim * (∑ y, V.ownerSum y ^ 2) := V.traceTerm_xy_sq

theorem CenteredVectorFamily.traceTerm_yz_sq
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z,
      (centeredProjector y z * V.ownerSum x) ^ 2) =
      sphereDim * (∑ x, V.ownerSum x ^ 2) := by
  calc
    (∑ x, ∑ y, ∑ z,
      (centeredProjector y z * V.ownerSum x) ^ 2) =
        ∑ y, ∑ x, ∑ z,
          (centeredProjector y z * V.ownerSum x) ^ 2 := Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ x,
          (centeredProjector y z * V.ownerSum x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm
    _ = sphereDim * (∑ x, V.ownerSum x ^ 2) := V.traceTerm_xy_sq

theorem CenteredVectorFamily.traceTerm_xy_xz
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x y * V.ownerSum z) *
        (centeredProjector x z * V.ownerSum y)) =
      ∑ x, V.ownerSum x ^ 2 := by
  calc
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x y * V.ownerSum z) *
        (centeredProjector x z * V.ownerSum y)) =
        ∑ y, ∑ z, ∑ x,
          (centeredProjector x y * centeredProjector x z) *
            (V.ownerSum y * V.ownerSum z) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ y, ∑ z, centeredProjector y z *
          (V.ownerSum y * V.ownerSum z) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_mul, centeredProjector_composition]
    _ = rationalDot V.ownerSum V.ownerSum := by
      rw [← centeredProjector_bilinear V.ownerSum V.ownerSum
        V.ownerSum_sum_zero]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑ x, V.ownerSum x ^ 2 := by
      unfold rationalDot
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem CenteredVectorFamily.traceTerm_xy_yz
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x y * V.ownerSum z) *
        (centeredProjector y z * V.ownerSum x)) =
      ∑ x, V.ownerSum x ^ 2 := by
  calc
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x y * V.ownerSum z) *
        (centeredProjector y z * V.ownerSum x)) =
        ∑ y, ∑ x, ∑ z,
          (centeredProjector y x * V.ownerSum z) *
            (centeredProjector y z * V.ownerSum x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      rw [centeredProjector_symm y x]
    _ = ∑ x, V.ownerSum x ^ 2 := V.traceTerm_xy_xz

theorem CenteredVectorFamily.traceTerm_xz_yz
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x z * V.ownerSum y) *
        (centeredProjector y z * V.ownerSum x)) =
      ∑ x, V.ownerSum x ^ 2 := by
  calc
    (∑ x, ∑ y, ∑ z,
      (centeredProjector x z * V.ownerSum y) *
        (centeredProjector y z * V.ownerSum x)) =
        ∑ z, ∑ x, ∑ y,
          (centeredProjector z x * V.ownerSum y) *
            (centeredProjector z y * V.ownerSum x) := by
      rw [show (∑ x, ∑ y, ∑ z,
        (centeredProjector x z * V.ownerSum y) *
          (centeredProjector y z * V.ownerSum x)) =
          ∑ x, ∑ z, ∑ y,
            (centeredProjector x z * V.ownerSum y) *
              (centeredProjector y z * V.ownerSum x) by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [centeredProjector_symm z x, centeredProjector_symm z y]
    _ = ∑ x, V.ownerSum x ^ 2 := V.traceTerm_xy_xz

theorem CenteredVectorFamily.traceTensor_sq
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ x, ∑ y, ∑ z, V.traceTensor x y z ^ 2) =
      3 * (sphereDim + 2) * (∑ x, V.ownerSum x ^ 2) := by
  have hsquare (a b c : ℚ) :
      (a + b + c) ^ 2 =
        a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b) + 2 * (a * c) + 2 * (b * c) := by
    ring
  have hsum_two (f : SphereCoord → SphereCoord → SphereCoord → ℚ) :
      (∑ x, ∑ y, ∑ z, 2 * f x y z) =
        2 * (∑ x, ∑ y, ∑ z, f x y z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
  unfold CenteredVectorFamily.traceTensor
  simp_rw [hsquare]
  simp only [Finset.sum_add_distrib]
  rw [V.traceTerm_xy_sq, V.traceTerm_xz_sq, V.traceTerm_yz_sq,
    hsum_two, hsum_two, hsum_two,
    V.traceTerm_xy_xz, V.traceTerm_xy_yz, V.traceTerm_xz_yz]
  ring

theorem CenteredVectorFamily.raw_moment3_nonneg
    (V : CenteredVectorFamily (owners := owners)) :
    0 ≤ (sphereDim + 2) *
        (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 3) -
      3 * centeredNormSq ^ 2 *
        (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j)) := by
  have hsos : 0 ≤ ∑ x, ∑ y, ∑ z, V.residualTensor3 x y z ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      Finset.sum_nonneg fun z _ => sq_nonneg _
  have hid :
      (∑ x, ∑ y, ∑ z, V.residualTensor3 x y z ^ 2) =
        (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 3) -
          3 * centeredNormSq ^ 2 / (sphereDim + 2) *
            (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j)) := by
    rw [sum_rationalDot_cube_eq_sum_aggregateTensor3_sq,
      sum_rationalDot_eq_sum_sq]
    let c : ℚ := centeredNormSq / (sphereDim + 2)
    have hcross :
        (∑ x, ∑ y, ∑ z, 2 * aggregateTensor3 V.vec x y z *
          (c * V.traceTensor x y z)) =
          2 * c * (∑ x, ∑ y, ∑ z,
            aggregateTensor3 V.vec x y z * V.traceTensor x y z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    have hsquare :
        (∑ x, ∑ y, ∑ z, (c * V.traceTensor x y z) ^ 2) =
          c ^ 2 * (∑ x, ∑ y, ∑ z, V.traceTensor x y z ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    unfold CenteredVectorFamily.residualTensor3
    change (∑ x, ∑ y, ∑ z,
      (aggregateTensor3 V.vec x y z - c * V.traceTensor x y z) ^ 2) = _
    simp_rw [sub_sq]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hcross, hsquare, V.tensor_trace_inner, V.traceTensor_sq]
    dsimp [c]
    norm_num [sphereDim, sphereN]
    simp only [CenteredVectorFamily.ownerSum]
    ring
  rw [hid] at hsos
  norm_num [sphereDim, sphereN] at hsos ⊢
  linarith

theorem CenteredVectorFamily.gram_moment1
    (V : CenteredVectorFamily (owners := owners)) :
    0 ≤ ∑ i, ∑ j, V.gram i j := by
  have hraw : 0 ≤ ∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) := by
    rw [sum_rationalDot_eq_sum_sq]
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  have hid :
      (∑ i, ∑ j, V.gram i j) =
        (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j)) / centeredNormSq := by
    unfold CenteredVectorFamily.gram
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  rw [hid]
  exact div_nonneg hraw centeredNormSq_pos.le

theorem CenteredVectorFamily.sum_gram_sq
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ i, ∑ j, V.gram i j ^ 2) =
      (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 2) /
        centeredNormSq ^ 2 := by
  calc
    (∑ i, ∑ j, V.gram i j ^ 2) =
        ∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 2 /
          centeredNormSq ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold CenteredVectorFamily.gram
      field_simp
    _ = (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 2) /
        centeredNormSq ^ 2 := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

theorem CenteredVectorFamily.sum_gram_cube
    (V : CenteredVectorFamily (owners := owners)) :
    (∑ i, ∑ j, V.gram i j ^ 3) =
      (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 3) /
        centeredNormSq ^ 3 := by
  calc
    (∑ i, ∑ j, V.gram i j ^ 3) =
        ∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 3 /
          centeredNormSq ^ 3 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold CenteredVectorFamily.gram
      field_simp
    _ = (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 3) /
        centeredNormSq ^ 3 := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

theorem double_sum_mul_right (f : owners → owners → ℚ) (c : ℚ) :
    (∑ i, ∑ j, f i j * c) = (∑ i, ∑ j, f i j) * c := by
  calc
    (∑ i, ∑ j, f i j * c) = ∑ i, (∑ j, f i j) * c := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_mul Finset.univ (fun j => f i j) c).symm
    _ = (∑ i, ∑ j, f i j) * c :=
      (Finset.sum_mul Finset.univ (fun i => ∑ j, f i j) c).symm

theorem sum_gegenQ2_eq (g : owners → owners → ℚ) :
    (∑ i, ∑ j, gegenQ2 (g i j)) =
      (sphereDim * (∑ i, ∑ j, g i j ^ 2) -
        (Fintype.card owners : ℚ) ^ 2) / (sphereDim - 1) := by
  calc
    (∑ i, ∑ j, gegenQ2 (g i j)) =
        ∑ i, ∑ j, (sphereDim * g i j ^ 2 - 1) *
          ((sphereDim : ℚ) - 1)⁻¹ := rfl
    _ = (∑ i, ∑ j, (sphereDim * g i j ^ 2 - 1)) *
        ((sphereDim : ℚ) - 1)⁻¹ := by
      exact double_sum_mul_right (owners := owners)
        (fun i j => (sphereDim : ℚ) * g i j ^ 2 - 1)
        (((sphereDim : ℚ) - 1)⁻¹)
    _ = _ := by
      simp only [Finset.sum_sub_distrib]
      simp [Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv]
      norm_num [sphereDim, sphereN]
      ring

theorem sum_gegenQ3_eq (g : owners → owners → ℚ) :
    (∑ i, ∑ j, gegenQ3 (g i j)) =
      ((sphereDim + 2) * (∑ i, ∑ j, g i j ^ 3) -
        3 * (∑ i, ∑ j, g i j)) / (sphereDim - 1) := by
  calc
    (∑ i, ∑ j, gegenQ3 (g i j)) =
        ∑ i, ∑ j, ((sphereDim + 2) * g i j ^ 3 - 3 * g i j) *
          ((sphereDim : ℚ) - 1)⁻¹ := rfl
    _ = (∑ i, ∑ j, ((sphereDim + 2) * g i j ^ 3 - 3 * g i j)) *
        ((sphereDim : ℚ) - 1)⁻¹ := by
      exact double_sum_mul_right (owners := owners)
        (fun i j => ((sphereDim : ℚ) + 2) * g i j ^ 3 - 3 * g i j)
        (((sphereDim : ℚ) - 1)⁻¹)
    _ = _ := by
      simp only [Finset.sum_sub_distrib]
      simp [Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv]

theorem CenteredVectorFamily.gram_moment2
    (V : CenteredVectorFamily (owners := owners)) :
    0 ≤ ∑ i, ∑ j, gegenQ2 (V.gram i j) := by
  have hraw := V.raw_moment2_nonneg
  have hid :
      (∑ i, ∑ j, gegenQ2 (V.gram i j)) =
        (sphereDim *
            (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 2) -
          (Fintype.card owners : ℚ) ^ 2 * centeredNormSq ^ 2) /
            ((sphereDim - 1) * centeredNormSq ^ 2) := by
    rw [sum_gegenQ2_eq, V.sum_gram_sq]
    field_simp [centeredNormSq_pos.ne']
  rw [hid]
  exact div_nonneg hraw (by
    have hm : (0 : ℚ) < sphereDim - 1 := by norm_num [sphereDim, sphereN]
    exact (mul_pos hm (pow_pos centeredNormSq_pos 2)).le)

theorem CenteredVectorFamily.gram_moment3
    (V : CenteredVectorFamily (owners := owners)) :
    0 ≤ ∑ i, ∑ j, gegenQ3 (V.gram i j) := by
  have hraw := V.raw_moment3_nonneg
  have hid :
      (∑ i, ∑ j, gegenQ3 (V.gram i j)) =
        ((sphereDim + 2) *
            (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j) ^ 3) -
          3 * centeredNormSq ^ 2 *
            (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j))) /
              ((sphereDim - 1) * centeredNormSq ^ 3) := by
    rw [sum_gegenQ3_eq, V.sum_gram_cube]
    have hsum :
        (∑ i, ∑ j, V.gram i j) =
          (∑ i, ∑ j, rationalDot (V.vec i) (V.vec j)) /
            centeredNormSq := by
      unfold CenteredVectorFamily.gram
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    rw [hsum]
    field_simp [centeredNormSq_pos.ne']
  rw [hid]
  exact div_nonneg hraw (by
    have hm : (0 : ℚ) < sphereDim - 1 := by norm_num [sphereDim, sphereN]
    exact (mul_pos hm (pow_pos centeredNormSq_pos 3)).le)

def incidenceCenteredFamily (A : owners → Finset SphereCoord)
    (hcard : ∀ i, (A i).card = sphereA) :
    CenteredVectorFamily (owners := owners) where
  vec i := centeredIncidence (A i)
  sum_zero i := centeredIncidence_sum_zero (A i) (hcard i)
  norm i := centeredIncidence_norm (A i) (hcard i)

theorem incidenceGram_offDiagonal (A : owners → Finset SphereCoord)
    (hcard : ∀ i, (A i).card = sphereA)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ sphereK)
    (i j : owners) (hij : i ≠ j) :
    (incidenceCenteredFamily A hcard).gram i j ≤ maxInner := by
  have ht : ((A i ∩ A j).card : ℚ) ≤ sphereK := by
    exact_mod_cast hinter i j hij
  change rationalDot (centeredIncidence (A i)) (centeredIncidence (A j)) /
    centeredNormSq ≤ maxInner
  rw [
    centeredIncidence_dot (A i) (A j) (hcard i) (hcard j)]
  rw [show (sphereN : ℚ) *
      ((sphereN : ℚ) * (A i ∩ A j).card - (sphereA : ℚ) ^ 2) /
        centeredNormSq =
      ((sphereN : ℚ) * (A i ∩ A j).card - (sphereA : ℚ) ^ 2) /
        ((sphereA : ℚ) * sphereE) by
    norm_num [centeredNormSq, sphereN, sphereA, sphereE,
      bchksAgreements6401]
    ring]
  rw [show maxInner =
      ((sphereN : ℚ) * sphereK - (sphereA : ℚ) ^ 2) /
        ((sphereA : ℚ) * sphereE) by
    norm_num [maxInner, sphereN, sphereA, sphereE, sphereK,
      bchksAgreements6401]]
  apply (div_le_div_iff_of_pos_right (by
    norm_num [sphereN, sphereA, sphereE, bchksAgreements6401] :
      (0 : ℚ) < (sphereA : ℚ) * sphereE)).2
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left ht (by norm_num [sphereN])) _

def incidenceRationalSphereGram (A : owners → Finset SphereCoord)
    (hcard : ∀ i, (A i).card = sphereA)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ sphereK) :
    RationalSphereGram (owners := owners) where
  gram := (incidenceCenteredFamily A hcard).gram
  symm := (incidenceCenteredFamily A hcard).gram_symm
  diagonal := (incidenceCenteredFamily A hcard).gram_diagonal
  offDiagonal := incidenceGram_offDiagonal A hcard hinter
  moment1 := (incidenceCenteredFamily A hcard).gram_moment1
  moment2 := by
    simpa only [gegenQ2] using (incidenceCenteredFamily A hcard).gram_moment2
  moment3 := by
    simpa only [gegenQ3] using (incidenceCenteredFamily A hcard).gram_moment3

/-- Exact constant-weight family endpoint used by the score-64.01 list
adapter.  No benchmark field appears: this is a theorem about rational
centered incidence vectors. -/
theorem exactAgreementFamily_card_le_17045844
    (A : owners → Finset SphereCoord)
    (hcard : ∀ i, (A i).card = 185354)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 131071) :
    Fintype.card owners ≤ 17045844 := by
  apply (incidenceRationalSphereGram A ?_ ?_).card_le_17045844
  · intro i
    simpa [sphereA, bchksAgreements6401] using hcard i
  · intro i j hij
    simpa [sphereK] using hinter i j hij

/-- Coordinate-type invariant form of `exactAgreementFamily_card_le_17045844`. -/
theorem exactAgreementFamily_card_le_17045844_of_card
    {coords : Type*} [Fintype coords] [DecidableEq coords]
    (hcoords : Fintype.card coords = 262144)
    (A : owners → Finset coords)
    (hcard : ∀ i, (A i).card = 185354)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 131071) :
    Fintype.card owners ≤ 17045844 := by
  classical
  let e : coords ≃ SphereCoord := Fintype.equivFinOfCardEq hcoords
  let B : owners → Finset SphereCoord := fun i => (A i).map e.toEmbedding
  apply exactAgreementFamily_card_le_17045844 B
  · intro i
    simp [B, hcard]
  · intro i j hij
    rw [show B i ∩ B j = (A i ∩ A j).map e.toEmbedding by
      simp [B, Finset.map_inter]]
    simpa using hinter i j hij

end CenteredFamily

end BCHKSSphericalL3Bound6401
end ProximityPrize.SubmissionLower
