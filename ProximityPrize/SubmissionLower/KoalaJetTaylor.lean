import ProximityPrize.SubmissionLower.HighCore82229UpperGeometry

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace SplitCut.JetTaylor
noncomputable section

open Polynomial Finset HighCore82229Upper HighCore82229Upper_4
open HighCore82229Upper_4_2 (divided divided_mul divided_sub divided_const_mul)
open K1_14 (L FX Seeds Equation)
open K1_14_6 (Biform)
open K1_14_6_1 (Dx flatten separant partialX cleared tangent)
open private K1_14_6_1.partialX_C K1_14_6_1.partialX_mul_X from ProximityPrize.SubmissionLower.Fast055
open private HighCore82229Upper_4.taylor_constant HighCore82229Upper_4_1.coeffDx_C
  HighCore82229Upper_4_1.Dx_center HighCore82229Upper_4_1.coeffDx_liftSeeds
  from ProximityPrize.SubmissionLower.HighCore82229UpperGeometry

variable {E : Type} [Field E]

structure Data (E : Type) [Field E] where
  ι : Seeds →+* E
  δ : Derivation ℤ E E
  compatible : ∀ s : Seeds, δ (ι s) = ι (coeffDx s)

namespace Data

abbrev embed (T : Data E) : FX →+* E := T.ι.comp MvPolynomial.C

theorem embed_derivative (T : Data E) (a : FX) : T.δ (T.embed a) = T.embed (Dx a) := by
  change T.δ (T.ι (MvPolynomial.C a)) = T.ι (MvPolynomial.C (Dx a))
  rw [T.compatible, HighCore82229Upper_4_1.coeffDx_C]

theorem center_one (T : Data E) : T.δ (origin T.ι) = 1 := by
  change T.δ (T.embed center) = 1
  rw [T.embed_derivative, HighCore82229Upper_4_1.Dx_center, map_one]

theorem frozen (T : Data E) (s : SeedConstants) : T.δ (T.ι (liftSeeds s)) = 0 := by
  rw [T.compatible, HighCore82229Upper_4_1.coeffDx_liftSeeds, map_zero]

end Data

theorem point_C (T : Data E) (y : E) (a : FX) :
    point (T.ι) y (MvPolynomial.C a) = T.embed a := by
  change eval₂ (T.ι) y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.C a)) = _
  rw [MvPolynomial.optionEquivLeft_C, eval₂_C]
  rfl
private theorem point_Y (T : Data E) (y : E) :
    point (T.ι) y (MvPolynomial.X (R := FX) (none : Option (Fin 2))) = y := by
  change eval₂ (T.ι) y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.X none)) = _
  rw [MvPolynomial.optionEquivLeft_X_none, eval₂_X]
private theorem point_seedVar (T : Data E) (y : E) (i : Fin 2) :
    point (T.ι) y (MvPolynomial.X (R := FX) (some i)) =
      T.ι (liftSeeds (MvPolynomial.X i)) := by
  change eval₂ (T.ι) y (MvPolynomial.optionEquivLeft FX (Fin 2) (MvPolynomial.X (some i))) = _
  rw [MvPolynomial.optionEquivLeft_X_some, eval₂_C, liftSeeds, MvPolynomial.map_X]
theorem point_seed (T : Data E) (y : E) :
    (point (T.ι) y).comp seedBiform = (T.ι).comp liftSeeds := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change point (T.ι) y (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.C a))) = T.ι (MvPolynomial.map constantAbscissa (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.rename_C, point_C]
    rfl
  · intro i
    change point (T.ι) y (MvPolynomial.rename some (MvPolynomial.map constantAbscissa
      (MvPolynomial.X i))) = _
    rw [MvPolynomial.map_X, MvPolynomial.rename_X, point_seedVar]
    rfl
private theorem split_mul (T : Data E) (a b : E) :
    T.δ (a * b) = a * T.δ b + T.δ a * b := by
  rw [T.δ.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]
private theorem split_point (T : Data E) (y : E)
    (P : Biform) :
    T.δ (point (T.ι) y P) =
      point (T.ι) y (partialX P) +
        T.δ y * point (T.ι) y (MvPolynomial.pderiv none P) := by
  let ev := point (T.ι) y
  change T.δ (ev P) = ev (partialX P) + T.δ y * ev (MvPolynomial.pderiv none P)
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [ev, K1_14_6_1.partialX_C, point_C, MvPolynomial.pderiv_C, map_zero, mul_zero, add_zero]
    exact T.embed_derivative a
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, mul_add]
    ring
  | mul_X P i hP =>
    have hi : T.δ (ev (MvPolynomial.X i)) =
        T.δ y * ev (MvPolynomial.pderiv none (MvPolynomial.X i)) := by
      cases i with
      | none => simp [ev, point_Y]
      | some j =>
        rw [show ev (MvPolynomial.X (some j)) = _ from point_seedVar T y j,
          MvPolynomial.pderiv_X_of_ne (Option.some_ne_none j), map_zero, mul_zero]
        exact T.frozen _
    simp only [map_mul, split_mul T, hP, K1_14_6_1.partialX_mul_X, MvPolynomial.pderiv_mul, map_add, hi]
    ring
private theorem eval_tangent (T : Data E) (y : E)
    (f P : Biform) (hf : point (T.ι) y f = 0) :
    point (T.ι) y (tangent f P) =
      point (T.ι) y (separant f) * T.δ (point (T.ι) y P) := by
  have h := split_point T y f
  rw [hf, map_zero] at h
  rw [split_point T, tangent, map_sub, map_mul, map_mul]
  linear_combination -point (T.ι) y (MvPolynomial.pderiv none P) * (Eq.symm h)
private theorem cleared_product_rule (T : Data E)
    (m : ℕ) (a v : E) :
    a * (a * T.δ (a^m * v)) - (m : E) * (a * T.δ a) * (a^m * v) =
      a^(m+2) * T.δ v := by
  cases m with
  | zero => simp [pow_two, mul_assoc]
  | succ m =>
    rw [split_mul T, T.δ.leibniz_pow, Nat.succ_sub_one, pow_add a (m+1) 2, pow_succ' a m]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
private theorem eval_cleared (T : Data E) (y : E)
    (f : Biform) (hf : point (T.ι) y f = 0) (n : ℕ) :
    point (T.ι) y (cleared f n) =
      point (T.ι) y (separant f) ^ (2*n+1) * (T.δ^[n+1]) y := by
  induction n with
  | zero =>
    have h := split_point T y f
    rw [hf, map_zero] at h
    simp only [cleared, map_neg, Nat.mul_zero, Nat.zero_add, pow_one, Function.iterate_one]
    linear_combination -(Eq.symm h)
  | succ n ih =>
    rw [cleared, map_sub, map_mul, map_mul, map_mul, point_C, eval_tangent T _ _ _ hf,
      eval_tangent T _ _ _ hf, ih, map_natCast, cleared_product_rule T,
      show 2*(n+1)+1 = 2*n+1+2 by omega, Function.iterate_succ_apply' T.δ (n+1) y]
theorem ordinate (T : Data E) (y : E)
    (f : Equation) (hf : point (T.ι) y (flatten f) = 0) {r i : ℕ} (hi : i ≤ r) :
    point (T.ι) y (ordinateTaylorNum f r i) =
      point (T.ι) y (separant (flatten f))^(2*r-1) *
        ((T.δ^[i]) y / (i.factorial : E)) := by
  cases i with
  | zero => simp [ordinateTaylorNum, point_Y]
  | succ i =>
    rw [ordinateTaylorNum, map_mul, map_mul, map_pow, point_C,
      eval_cleared T y _ hf, map_inv₀, map_natCast]
    let a := point (T.ι) y (separant (flatten f))
    have hp : a ^ (2*r-1-(2*i+1)) * a ^ (2*i+1) = a ^ (2*r-1) := by
      rw [← pow_add, show (2*r-1-(2*i+1))+(2*i+1) = 2*r-1 by omega]
    change _ * (a^_ * (a^_ * (T.δ^[i+1]) y)) = a^_ * _
    rw [← mul_assoc (a^_) (a^_), hp]
    ring
private theorem iterate_eval (T : Data E)
    (N : SeedConstants[X]) (i : ℕ) :
    (T.δ^[i]) ((N.map ((T.ι).comp liftSeeds)).eval (origin (T.ι))) =
      ((Polynomial.derivative^[i]) (N.map ((T.ι).comp liftSeeds))).eval
        (origin (T.ι)) := by
  let κ := (T.ι).comp liftSeeds
  let x := origin (T.ι)
  have hone (P : SeedConstants[X]) : T.δ ((P.map κ).eval x) =
      (P.derivative.map κ).eval x := by
    rw [← Polynomial.derivative_map, T.δ.apply_eval_eq]
    have hcoeff : T.δ.mapCoeffs (P.map κ) = 0 := by
      apply PolynomialModule.coeff_injective
      apply Finsupp.ext
      intro k
      rw [Derivation.mapCoeffs_apply, coeff_map, PolynomialModule.coeff_zero]
      exact T.frozen _
    simp [hcoeff, x, T.center_one, smul_eq_mul]
  rw [Polynomial.iterate_derivative_map]
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, hone, Function.iterate_succ_apply']
theorem numerator_taylor (T : Data E) (y : E)
    (N : SeedConstants[X]) (i : ℕ) (hi : (i.factorial : E) ≠ 0) :
    point (T.ι) y (liftTaylor N i) =
      divided T.δ ((N.map ((T.ι).comp liftSeeds)).eval (origin (T.ι))) i := by
  rw [liftTaylor, ← Polynomial.coeff_map, Polynomial.map_taylor, Polynomial.map_map,
    point_seed, point_C, Polynomial.taylor_coeff, divided, iterate_eval]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := E) i)
    (N.map ((T.ι).comp liftSeeds))
  rw [← h, LinearMap.smul_apply, eval_smul, nsmul_eq_mul, inv_mul_cancel_left₀ hi]
  rfl
theorem eval_blocks (T : Data E) (J : Input) :
    (blocks (T.ι) J).eval (origin (T.ι)) =
      T.embed (algebraMap L[X] FX J.blockProduct) := by
  have hc : ((T.ι).comp liftSeeds).comp MvPolynomial.C =
      (T.embed).comp constantAbscissa := by
    apply RingHom.ext
    intro a
    change T.ι (MvPolynomial.map constantAbscissa (MvPolynomial.C a)) =
      T.ι (MvPolynomial.C (constantAbscissa a))
    rw [MvPolynomial.map_C]
  rw [blocks, eval_map, hc, show origin (T.ι) = T.embed center from rfl, ← hom_eval₂]
  congr 1
  unfold constantAbscissa center
  rw [← hom_eval₂, eval₂_C_X]
theorem inverse_block_taylor (T : Data E) (J : Input) (i : ℕ) :
    T.embed (inverseBlockCoeff J i) =
      divided T.δ ((blocks (T.ι) J).eval (origin (T.ι)))⁻¹ i := by
  have hiter (a : FX) (n : ℕ) : T.embed ((Dx^[n]) a) = (T.δ^[n]) (T.embed a) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ← T.embed_derivative, ih,
        Function.iterate_succ_apply']
  rw [inverseBlockCoeff, divided, eval_blocks T, map_mul, map_inv₀, map_natCast, hiter, map_inv₀]
/-- Cleared Taylor numerator on an arbitrary differential root branch. -/
theorem numerator (T : Data E) (J : Input) (B : ResidueLift J) (y : E) (r : ℕ)
    (hf : point T.ι y (flatten J.f) = 0)
    (ha : T.ι (liftSeeds B.denominator) ≠ 0)
    (hfac : ∀ i ≤ r, (i.factorial : E) ≠ 0) :
    point T.ι y (quotientNumerator J B r) =
      (T.ι (liftSeeds B.denominator) *
        point T.ι y (separant (flatten J.f))^(2*r-1)) *
          divided T.δ (quotientValue T.ι B y) r := by
  let ι := T.ι
  let ev := point ι y
  let a := ι (liftSeeds B.denominator)
  let s := ev (separant (flatten J.f)) ^ (2*r-1)
  let t := (B.numerator.map (ι.comp liftSeeds)).eval (origin ι)
  let g := (blocks ι J).eval (origin ι)
  have hseed : ev (seedBiform B.denominator) = a :=
    RingHom.congr_fun (point_seed T y) B.denominator
  have hcrt : (crt ι B).eval (origin ι) = a⁻¹ * t := by
    rw [crt, eval_mul, eval_C] <;> rfl
  have hconst : T.δ a⁻¹ = 0 := by
    rw [T.δ.leibniz_inv, show T.δ a = 0 from T.frozen _, smul_zero]
  have hnum : ev (quotientNumerator J B r) =
      (a*s) * divided T.δ (quotientValue ι B y) r := by
    rw [quotientValue, hcrt, div_eq_inv_mul, ← show g = (blocks ι J).eval (origin ι) from rfl,
      divided_mul _ _ _ hfac, quotientNumerator, map_sum, Finset.mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hir : i ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [map_mul, map_sub, map_pow]
    rw [point_C, inverse_block_taylor T, hseed, ordinate T y J.f hf hir,
      numerator_taylor T y _ i (hfac i hir), divided_sub, divided_const_mul _ _ _ hconst]
    change divided T.δ g⁻¹ (r-i) *
        (a * (s * ((T.δ^[i]) y / (i.factorial : E))) -
          s * divided T.δ t i) =
      a * s * (divided T.δ g⁻¹ (r-i) *
        (divided T.δ y i - a⁻¹ * divided T.δ t i))
    rw [show (T.δ^[i]) y / (i.factorial : E) = divided T.δ y i by
      rw [divided, div_eq_inv_mul]]
    have hcancel (z : E) : a * (a⁻¹ * z) = z :=
      mul_inv_cancel_left₀ ha z
    calc
      _ = s * (divided T.δ g⁻¹ (r-i) *
          (a * divided T.δ y i - divided T.δ t i)) := by ring
      _ = _ := by
        conv_lhs => rw [← hcancel (divided T.δ t i)]
        ring
  exact hnum

theorem jet_eq_divided (T : Data E) (J : Input) (B : ResidueLift J) (y : E) (r : ℕ)
    (hf : point T.ι y (flatten J.f) = 0)
    (ha : T.ι (liftSeeds B.denominator) ≠ 0)
    (hs : point T.ι y (separant (flatten J.f)) ≠ 0)
    (hfac : ∀ i ≤ r, (i.factorial : E) ≠ 0) :
    jet T.ι B y r = divided T.δ (quotientValue T.ι B y) r := by
  unfold jet
  rw [numerator T J B y r hf ha hfac]
  have hden : point T.ι y (quotientDenominator J B r) =
      T.ι (liftSeeds B.denominator) * point T.ι y (separant (flatten J.f))^(2*r-1) := by
    rw [quotientDenominator, map_mul, map_pow]
    exact congrArg (· * _) (RingHom.congr_fun (point_seed T y) B.denominator)
  rw [hden, mul_comm, mul_div_cancel_right₀ _ (mul_ne_zero ha (pow_ne_zero _ hs))]

/-- The cleared derivation of a positive Taylor numerator reduces to its successor
    modulo the numerator itself. -/
theorem derivative_step (T : Data E) (J : Input) (B : ResidueLift J) (y : E) (r : ℕ)
    (hr : 0 < r) (hf : point T.ι y (flatten J.f) = 0)
    (ha : T.ι (liftSeeds B.denominator) ≠ 0)
    (hfac : ∀ i ≤ r+1, (i.factorial : E) ≠ 0) :
    let s := point T.ι y (separant (flatten J.f))
    let u := point T.ι y (quotientNumerator J B r)
    s^2 * T.δ u = (r+1 : ℕ) * point T.ι y (quotientNumerator J B (r+1)) +
      (2*r-1 : ℕ) * s * T.δ s * u := by
  let s := point T.ι y (separant (flatten J.f))
  let a := T.ι (liftSeeds B.denominator)
  let q := quotientValue T.ι B y
  have hn := numerator T J B y r hf ha (fun i hi => hfac i (by omega))
  have hn' := numerator T J B y (r+1) hf ha hfac
  change _ = a * s^(2*r-1) * divided T.δ q r at hn
  change _ = a * s^(2*(r+1)-1) * divided T.δ q (r+1) at hn'
  have hd (n : ℕ) : T.δ ((n.factorial : E)⁻¹) = 0 := by
    rw [T.δ.leibniz_inv, T.δ.map_natCast, smul_zero]
  have hnext : T.δ (divided T.δ q r) = (r+1 : ℕ) * divided T.δ q (r+1) := by
    unfold divided
    rw [split_mul, hd, zero_mul, add_zero, Function.iterate_succ_apply', Nat.factorial_succ,
      Nat.cast_mul]
    have h₁ : ((r+1 : ℕ) : E) ≠ 0 := by
      have h := hfac (r+1) le_rfl
      rw [Nat.factorial_succ, Nat.cast_mul, mul_ne_zero_iff] at h
      exact h.1
    simp only [mul_inv, ← mul_assoc, mul_inv_cancel₀ h₁, one_mul]
  change s^2 * T.δ (point T.ι y (quotientNumerator J B r)) = _
  rw [hn, hn', split_mul, split_mul, T.frozen, zero_mul, add_zero,
    T.δ.leibniz_pow, hnext, smul_eq_mul, nsmul_eq_mul,
    show 2*(r+1)-1 = (2*r-1)+2 by omega, pow_add,
    show s^(2*r-1) = s^(2*r-1-1)*s by rw [← pow_succ, show 2*r-1-1+1 = 2*r-1 by omega]]
  push_cast
  ring

theorem model_constant (T : Data E) (J : Input) (B : ResidueLift J) (y : E)
    (hf : point T.ι y (flatten J.f) = 0)
    (ha : T.ι (liftSeeds B.denominator) ≠ 0)
    (hs : point T.ι y (separant (flatten J.f)) ≠ 0)
    (hfac : ∀ i ≤ J.ell+1, (i.factorial : E) ≠ 0)
    (hcut : point T.ι y (quotientNumerator J B (J.ell+1)) = 0) :
    coeffDeriv T.δ (modelValue T.ι B y) = 0 := by
  have hcrt : coeffDeriv T.δ (crt T.ι B) = 0 := by
    have hnum : coeffDeriv T.δ (B.numerator.map (T.ι.comp liftSeeds)) = 0 := by
      apply Polynomial.ext
      intro k
      rw [coeff_coeffDeriv, coeff_map, coeff_zero]
      exact T.frozen _
    unfold crt
    rw [Derivation.leibniz, hnum, coeffDeriv_C, T.δ.leibniz_inv, T.frozen]
    simp
  have hblock : coeffDeriv T.δ (blocks T.ι J) = 0 := by
    apply Polynomial.ext
    intro k
    rw [coeff_coeffDeriv, blocks, coeff_map, coeff_zero]
    exact T.frozen _
  have hflat : (T.δ^[J.ell+1]) (quotientValue T.ι B y) = 0 := by
    have hn := numerator T J B y (J.ell+1) hf ha hfac
    rw [hcut] at hn
    have h := (mul_eq_zero.mp hn.symm).resolve_left (mul_ne_zero ha (pow_ne_zero _ hs))
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (hfac _ le_rfl))
  have hTaylor := HighCore82229Upper_4.taylor_constant T.δ (origin T.ι)
    (quotientValue T.ι B y) J.ell T.center_one hflat (fun i hi => hfac i (by omega))
  have ht : (∑ r ∈ range (J.ell+1), C (jet T.ι B y r) *
        ((Polynomial.X : E[X]) - C (origin T.ι)) ^ r) =
      ∑ r ∈ range (J.ell+1), C ((T.δ^[r]) (quotientValue T.ι B y) / (r.factorial : E)) *
        ((Polynomial.X : E[X]) - C (origin T.ι)) ^ r := by
    apply sum_congr rfl
    intro r hr
    rw [jet_eq_divided T J B y r hf ha hs (fun i hi => hfac i (by have := mem_range.mp hr; omega))]
    simp [divided, div_eq_inv_mul]
  unfold modelValue
  rw [ht, map_add, Derivation.leibniz, hcrt, hblock, hTaylor]
  simp

theorem model_center (T : Data E) (J : Input) (B : ResidueLift J) (y : E)
    (hf : point T.ι y (flatten J.f) = 0)
    (ha : T.ι (liftSeeds B.denominator) ≠ 0)
    (hs : point T.ι y (separant (flatten J.f)) ≠ 0)
    (hb : (blocks T.ι J).eval (origin T.ι) ≠ 0) :
    (modelValue T.ι B y).eval (origin T.ι) = y := by
  have hjet := jet_eq_divided T J B y 0 hf ha hs (fun i hi => by
    have : i = 0 := by omega
    simp [this])
  have hz : jet T.ι B y 0 = quotientValue T.ι B y := by simpa [divided] using hjet
  unfold modelValue
  simp only [eval_add, eval_mul, eval_finsetSum, eval_C, eval_pow, eval_X, eval_sub, sub_self]
  rw [Finset.sum_eq_single 0, hz]
  · simp only [pow_zero, mul_one, quotientValue]
    field_simp
    ring
  · intro i _ hi
    rw [zero_pow hi, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim
end
end SplitCut.JetTaylor

#print axioms SplitCut.JetTaylor.numerator
#print axioms SplitCut.JetTaylor.derivative_step
#print axioms SplitCut.JetTaylor.model_constant
#print axioms SplitCut.JetTaylor.model_center
