import ProximityPrize.SubmissionBinaryLower.P64SubstitutionVanish

/-!
# Orders along lines (PROOF.md Lemma V)

A trivariate polynomial `G : F[Z][X][Y]` (outer `Y`, middle `X`, inner `Z`) is shifted to the
line `X = x, Y = y(Z)` with `Polynomial.Bivariate.shift` over the base ring `K = F[Z]`. The order
along the line is the least total degree `a + b` of a nonzero coefficient of `U^a V^b` in the
shifted polynomial. It is computed as the trailing degree in `T` of the homogenisation
`S(T·U, T·V)`, which makes it additive over products.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64LineOrder

open Polynomial

section Homog

variable {K : Type*} [CommRing K]

/-- Inner part of the homogenisation: `f(X) ↦ f(T·X)`, with `T` the outer variable. -/
noncomputable def homogX : K[X] →+* Polynomial (Polynomial (Polynomial K)) :=
  Polynomial.eval₂RingHom (R := K) (S := Polynomial (Polynomial (Polynomial K)))
    ((Polynomial.C : Polynomial (Polynomial K) →+* Polynomial (Polynomial (Polynomial K))).comp
      ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp Polynomial.C))
    (Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X)

/-- Homogenisation `S(X, Y) ↦ S(T·X, T·Y)` of `S : K[X][Y]`, with `T` the outer variable. -/
noncomputable def homog : Polynomial (Polynomial K) →+* Polynomial (Polynomial (Polynomial K)) :=
  Polynomial.eval₂RingHom (R := Polynomial K) (S := Polynomial (Polynomial (Polynomial K)))
    homogX (Polynomial.C Polynomial.X * Polynomial.X)

lemma homogX_monomial (a : ℕ) (c : K) :
    homogX (monomial a c) = monomial a (Polynomial.C (monomial a c)) := by
  simp only [homogX, coe_eval₂RingHom, eval₂_monomial, RingHom.coe_comp, Function.comp_apply]
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow]
  ring

lemma homog_monomial (a b : ℕ) (c : K) :
    homog (monomial b (monomial a c)) = monomial (a + b) (monomial b (monomial a c)) := by
  simp only [homog, coe_eval₂RingHom, eval₂_monomial, homogX_monomial]
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial (n := a + b),
    ← C_mul_X_pow_eq_monomial (n := b)]
  simp only [map_mul, map_pow]
  ring

lemma coeff_homog (S : Polynomial (Polynomial K)) (k b a : ℕ) :
    (((homog S).coeff k).coeff b).coeff a = if a + b = k then (S.coeff b).coeff a else 0 := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, coeff_add, coeff_add, coeff_add, hp, hq, coeff_add, coeff_add]
      split_ifs <;> simp
  | monomial b' f =>
      induction f using Polynomial.induction_on' with
      | add f g hf hg =>
          rw [map_add, map_add, coeff_add, coeff_add, coeff_add, hf, hg, coeff_add, coeff_add]
          split_ifs <;> simp
      | monomial a' c =>
          rw [homog_monomial]
          simp only [coeff_monomial]
          by_cases h2 : b' = b
          · subst h2
            by_cases h3 : a' = a
            · subst h3
              split_ifs <;> simp_all
            · have : ((monomial a') c).coeff a = 0 := by simp [coeff_monomial, h3]
              split_ifs <;> simp [this]
          · split_ifs <;> simp [coeff_monomial, h2]

lemma homog_eq_zero_iff (S : Polynomial (Polynomial K)) : homog S = 0 ↔ S = 0 := by
  constructor
  · intro h
    ext b a
    have := coeff_homog S (a + b) b a
    simp only [h, coeff_zero, ite_true] at this
    simpa using this.symm
  · rintro rfl
    simp

/-- Least total degree `a + b` of a nonzero coefficient of `X^a Y^b` (zero for `S = 0`). -/
noncomputable def tord (S : Polynomial (Polynomial K)) : ℕ := (homog S).natTrailingDegree

lemma le_tord_iff {S : Polynomial (Polynomial K)} (hS : S ≠ 0) {r : ℕ} :
    r ≤ tord S ↔ ∀ a b, a + b < r → (S.coeff b).coeff a = 0 := by
  constructor
  · intro h a b hab
    have h0 := coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hab h)
    have := coeff_homog S (a + b) b a
    rw [h0] at this
    simpa using this.symm
  · intro h
    apply le_natTrailingDegree ((homog_eq_zero_iff S).not.mpr hS)
    intro k hk
    ext b a
    rw [coeff_homog]
    split_ifs with hab
    · simpa using h a b (by omega)
    · simp

lemma tord_mul [IsDomain K] {S S' : Polynomial (Polynomial K)} (hS : S ≠ 0) (hS' : S' ≠ 0) :
    tord (S * S') = tord S + tord S' := by
  unfold tord
  rw [map_mul]
  exact natTrailingDegree_mul ((homog_eq_zero_iff S).not.mpr hS)
    ((homog_eq_zero_iff S').not.mpr hS')

end Homog

section Line

variable {F : Type*} [Field F]

/-- `G(X + x, Y + y(Z), Z)`, the polynomial in line coordinates `(U, V)` over `F[Z]`. -/
noncomputable def lineShift (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) :
    Polynomial (Polynomial (Polynomial F)) :=
  Polynomial.Bivariate.shift G (Polynomial.C x) y

lemma lineShift_mul (G H : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) :
    lineShift (G * H) x y = lineShift G x y * lineShift H x y := by
  simp [lineShift, Polynomial.Bivariate.shift, mul_comp, Polynomial.map_mul]

lemma lineShift_eq_zero_iff (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) :
    lineShift G x y = 0 ↔ G = 0 := by
  unfold lineShift Polynomial.Bivariate.shift
  have hinj : Function.Injective
      (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C x)) :
        Polynomial (Polynomial F) →+* Polynomial (Polynomial F)) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    rw [Polynomial.coe_compRingHom_apply] at hq
    exact comp_X_add_C_eq_zero_iff.mp hq
  rw [Polynomial.map_eq_zero_iff hinj, comp_X_add_C_eq_zero_iff]

lemma lineShift_derivative (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) :
    lineShift (derivative G) x y = derivative (lineShift G x y) := by
  simp [lineShift, Polynomial.Bivariate.shift, derivative_map, derivative_comp]

/-- `OrdGE G x y r`: the order of `G` along the line `X = x, Y = y(Z)` is at least `r`. This is
the vanishing condition of the interpolation space (PROOF.md 2.1). -/
def OrdGE (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) (r : ℕ) : Prop :=
  ∀ a b, a + b < r → ((lineShift G x y).coeff b).coeff a = 0

/-- The order `ord_i G` of `G` along the line `X = x, Y = y(Z)` (PROOF.md 2.1). -/
noncomputable def lineOrd (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) : ℕ :=
  tord (lineShift G x y)

lemma ordGE_iff {G : Polynomial (Polynomial (Polynomial F))} (hG : G ≠ 0) (x : F) (y : F[X])
    (r : ℕ) : OrdGE G x y r ↔ r ≤ lineOrd G x y :=
  (le_tord_iff ((lineShift_eq_zero_iff G x y).not.mpr hG)).symm

lemma ordGE_lineOrd (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X]) :
    OrdGE G x y (lineOrd G x y) := by
  by_cases hG : G = 0
  · subst hG
    intro a b _
    simp [lineShift, Polynomial.Bivariate.shift]
  · exact (ordGE_iff hG x y _).mpr le_rfl

/-- Lemma V(a): the order along a line is additive over products. -/
theorem lineOrd_mul {G H : Polynomial (Polynomial (Polynomial F))} (hG : G ≠ 0) (hH : H ≠ 0)
    (x : F) (y : F[X]) : lineOrd (G * H) x y = lineOrd G x y + lineOrd H x y := by
  unfold lineOrd
  rw [lineShift_mul]
  exact tord_mul ((lineShift_eq_zero_iff G x y).not.mpr hG)
    ((lineShift_eq_zero_iff H x y).not.mpr hH)

theorem lineOrd_pow {G : Polynomial (Polynomial (Polynomial F))} (hG : G ≠ 0) (x : F)
    (y : F[X]) (a : ℕ) : lineOrd (G ^ a) x y = a * lineOrd G x y := by
  induction a with
  | zero =>
      have h1 : lineOrd (1 : Polynomial (Polynomial (Polynomial F))) x y = 0 := by
        apply Nat.eq_zero_of_le_zero
        by_contra hpos
        have h := (ordGE_iff one_ne_zero x y 1).mpr (by omega) 0 0 (by omega)
        simp [lineShift, Polynomial.Bivariate.shift] at h
      simpa using h1
  | succ a ih =>
      rw [pow_succ, lineOrd_mul (pow_ne_zero a hG) hG, ih]
      ring

/-- Lemma V(a), cofactor form: an order bound on `G * H` passes to `H` after subtracting the
order of `G`. -/
theorem ordGE_cofactor {G H : Polynomial (Polynomial (Polynomial F))} (hG : G ≠ 0) (hH : H ≠ 0)
    (x : F) (y : F[X]) (r : ℕ) (h : OrdGE (G * H) x y r) :
    OrdGE H x y (r - lineOrd G x y) := by
  rw [ordGE_iff (mul_ne_zero hG hH), lineOrd_mul hG hH] at h
  rw [ordGE_iff hH]
  omega

/-- Lemma V(b): order `s` along the line through `(x, P(x))` at `Z = z` gives a root of
multiplicity at least `s` of `G(X, P(X), z)`. -/
theorem le_rootMultiplicity_triEval (G : Polynomial (Polynomial (Polynomial F))) (x z : F)
    (y P : F[X]) (s : ℕ) (hord : OrdGE G x y s) (hmatch : P.eval x = y.eval z)
    (hne : BCHKSSubstitutionVanish.triEval G z P ≠ 0) :
    s ≤ (BCHKSSubstitutionVanish.triEval G z P).rootMultiplicity x := by
  apply BCHKSSubstitutionVanish.rootMultiplicity_triEval_ge_of_shift_coeff_zero G x z y P s
    _ hmatch hne
  intro a b k hab
  have := hord a b hab
  simp only [lineShift] at this
  rw [this, coeff_zero]

/-- Lemma V(c): differentiating in `Y` lowers the order by at most one. -/
theorem ordGE_derivative (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X])
    (r : ℕ) (h : OrdGE G x y r) : OrdGE (derivative G) x y (r - 1) := by
  intro a b hab
  rw [lineShift_derivative, coeff_derivative]
  have hc : ((b : Polynomial (Polynomial F)) + 1) = Polynomial.C ((b : Polynomial F) + 1) := by
    simp
  rw [hc, coeff_mul_C, h a (b + 1) (by omega), zero_mul]

/-- `G(x, Y, Z)` as a polynomial in `Y` over `F[Z]`. -/
noncomputable def evalXAt (G : Polynomial (Polynomial (Polynomial F))) (x : F) :
    Polynomial (Polynomial F) :=
  G.map (Polynomial.evalRingHom (Polynomial.C x))

lemma lineShift_coeff_zero (G : Polynomial (Polynomial (Polynomial F))) (x : F) (y : F[X])
    (b : ℕ) : ((lineShift G x y).coeff b).coeff 0 = ((evalXAt G x).comp ((Polynomial.X : Polynomial (Polynomial F)) + C y)).coeff b := by
  have hcomp : (evalXAt G x).comp ((Polynomial.X : Polynomial (Polynomial F)) + C y) =
      (G.comp ((Polynomial.X : Polynomial (Polynomial (Polynomial F))) + C (C y))).map
        (Polynomial.evalRingHom (Polynomial.C x)) := by
    rw [Polynomial.map_comp]
    simp [evalXAt]
  rw [hcomp, coeff_map]
  simp [lineShift, Polynomial.Bivariate.shift, coeff_map, Polynomial.coe_compRingHom_apply,
    coeff_zero_eq_eval_zero, eval_comp]

/-- Lemma V(d), first half: the order is at most the `Y`-degree when `X - x` does not divide `G`,
in the form `G(x, Y, Z) ≠ 0`. -/
theorem lineOrd_le_natDegree {G : Polynomial (Polynomial (Polynomial F))} (x : F) (y : F[X])
    (hx : evalXAt G x ≠ 0) : lineOrd G x y ≤ G.natDegree := by
  have hG : G ≠ 0 := by
    rintro rfl
    simp [evalXAt] at hx
  have hc : (evalXAt G x).comp ((Polynomial.X : Polynomial (Polynomial F)) + C y) ≠ 0 := comp_X_add_C_ne_zero_iff.mpr hx
  obtain ⟨b, hbdef⟩ : ∃ b, b = ((evalXAt G x).comp ((Polynomial.X : Polynomial (Polynomial F)) + C y)).natDegree := ⟨_, rfl⟩
  have hb : ((evalXAt G x).comp ((Polynomial.X : Polynomial (Polynomial F)) + C y)).coeff b ≠ 0 := by
    rw [hbdef, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hc
  have hbG : b ≤ G.natDegree := by
    have h1 : b = (evalXAt G x).natDegree := by
      rw [hbdef, natDegree_comp, natDegree_X_add_C, mul_one]
    rw [h1]
    exact natDegree_map_le
  by_contra hlt
  push Not at hlt
  have := (ordGE_iff hG x y (b + 1)).mpr (by omega) 0 b (by omega)
  rw [lineShift_coeff_zero] at this
  exact hb this

/-- Lemma V(d), second half: an irreducible `G` of positive `Y`-degree is not divisible by
`X - x`, so `G(x, Y, Z) ≠ 0`. -/
theorem evalXAt_ne_zero_of_irreducible {G : Polynomial (Polynomial (Polynomial F))}
    (hirr : Irreducible G) (hdeg : 1 ≤ G.natDegree) (x : F) : evalXAt G x ≠ 0 := by
  intro h0
  have hdvd : Polynomial.C (Polynomial.X - Polynomial.C (Polynomial.C x)) ∣ G := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro j
    rw [Polynomial.dvd_iff_isRoot]
    have := congrArg (fun p => p.coeff j) h0
    simpa [evalXAt, coeff_map] using this
  rcases hdvd with ⟨c, hc⟩
  have hunit := hirr.isUnit_or_isUnit hc
  rcases hunit with hu | hu
  · have : IsUnit (Polynomial.X - Polynomial.C (Polynomial.C x) : Polynomial (Polynomial F)) :=
      Polynomial.isUnit_C.mp hu
    exact (Polynomial.not_isUnit_X_sub_C _) this
  · have h1 : G.natDegree = 0 := by
      rw [hc, natDegree_mul (by
          rw [Ne, Polynomial.C_eq_zero]; exact Polynomial.X_sub_C_ne_zero _)
        (by rintro rfl; simp at hu), natDegree_C, natDegree_eq_zero_of_isUnit hu]
    omega

/-- Lemma V(d): an irreducible factor of `Y`-degree `h ≥ 1` has order at most `h` on every line. -/
theorem lineOrd_le_natDegree_of_irreducible {G : Polynomial (Polynomial (Polynomial F))}
    (hirr : Irreducible G) (hdeg : 1 ≤ G.natDegree) (x : F) (y : F[X]) :
    lineOrd G x y ≤ G.natDegree :=
  lineOrd_le_natDegree x y (evalXAt_ne_zero_of_irreducible hirr hdeg x)

end Line

end P64LineOrder
end ProximityPrize.SubmissionBinaryLower
