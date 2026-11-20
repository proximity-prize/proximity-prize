import ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.RingTheory.Polynomial.UniqueFactorization
set_option Elab.async false

section PackSource_K1_13_5_5_2_3Specialization
set_option autoImplicit true
namespace K1_13_5_5_2_3

noncomputable section

open scoped BigOperators Polynomial

set_option linter.style.haveILetI false

section

variable {R A B : Type} [CommRing R] [CommRing A] [IsDomain A] [CommRing B]
variable (ρ : R[X] →+* A) (τ : R →+* B) (s : A →+* B)

/-- Lifts of a tuple independent at zero are independent over the polynomial ring. -/
private theorem independent_of_specialization (hw : ρ Polynomial.X ≠ 0)
    (hs : s.comp ρ = τ.comp (Polynomial.evalRingHom 0)) {n : ℕ} (v : Fin n → A) :
    letI : Module R[X] A := Module.compHom A ρ
    letI : Module R B := Module.compHom B τ
    LinearIndependent R (s ∘ v) → LinearIndependent R[X] v := by
  classical
  letI : Module R[X] A := Module.compHom A ρ
  letI : Module R B := Module.compHom B τ
  change LinearIndependent R (s ∘ v) → LinearIndependent R[X] v
  intro hv
  have specialize (f : Fin n → R[X]) (hf : ∑ i, ρ (f i) * v i = 0) :
      ∀ i, (f i).coeff 0 = 0 := by
    have hcompat (p : R[X]) : s (ρ p) = τ (p.coeff 0) := by
      simpa only [RingHom.comp_apply, Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coe_evalRingHom] using
        DFunLike.congr_fun hs p
    have h := congrArg s hf
    rw [map_sum, map_zero] at h
    simp only [map_mul, hcompat] at h
    exact Fintype.linearIndependent_iff.mp hv (fun i => (f i).coeff 0) h
  have allCoeffs (k : ℕ) (f : Fin n → R[X]) (hf : ∑ i, ρ (f i) * v i = 0) :
      ∀ i, (f i).coeff k = 0 := by
    induction k generalizing f with
    | zero => exact specialize f hf
    | succ k ih =>
      have hdiv (i : Fin n) : Polynomial.X * (f i).divX = f i := by
        simpa [specialize f hf i] using Polynomial.X_mul_divX_add (f i)
      have hprod : ρ Polynomial.X * ∑ i, ρ ((f i).divX) * v i = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, ← map_mul, hdiv]
        exact hf
      have hrel := (mul_eq_zero.mp hprod).resolve_left hw
      intro i
      simpa only [Polynomial.coeff_divX] using ih (fun i => (f i).divX) hrel i
  refine Fintype.linearIndependent_iff.mpr fun f hf i => ?_
  ext k
  rw [Polynomial.coeff_zero]
  exact allCoeffs k f hf i

/-- Torsion-free specialization at the polynomial variable, with no finiteness
assumption on the module being specialized. -/
theorem rank_le_of_specialization [Nontrivial R] (hw : ρ Polynomial.X ≠ 0)
    (hs : s.comp ρ = τ.comp (Polynomial.evalRingHom 0))
    (hsurj : Function.Surjective s) (n : ℕ) :
    letI : Module R[X] A := Module.compHom A ρ
    letI : Module R B := Module.compHom B τ
    Module.rank R[X] A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal) := by
  classical
  letI : Module R[X] A := Module.compHom A ρ
  letI : Module R B := Module.compHom B τ
  change Module.rank R[X] A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal)
  intro hrank
  by_contra! h
  have hlarge : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank R B := by
    rwa [Nat.cast_add_one, Cardinal.natCast_add_one_le_iff]
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hlarge
  choose u hu using fun i => hsurj (v i)
  have hu' : s ∘ u = v := funext hu
  have hind := independent_of_specialization ρ τ s hw hs u (hu' ▸ hv)
  have hsmall : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank R[X] A :=
    Module.le_rank_iff.mpr ⟨u, hind⟩
  exact (Nat.not_succ_le_self n) (by exact_mod_cast hsmall.trans hrank)

end

/-- A fixed nonzero denominator giving recovery up to powers transfers a
rank bound along a compatible map of algebras. -/
theorem rank_le_of_recovery {R A B : Type} [CommRing R] [IsDomain R]
    [CommRing A] [CommRing B] [IsDomain B] (ρ : R →+* A) (τ : R →+* B) (s : A →+* B)
    (hs : s.comp ρ = τ) (b : A) (hb : s b ≠ 0)
    (hrec : ∀ a : B, ∃ q : A, ∃ m : ℕ, s q = s b ^ m * a) (n : ℕ) :
    letI : Module R A := Module.compHom A ρ
    letI : Module R B := Module.compHom B τ
    Module.rank R A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal) := by
  classical
  letI : Module R A := Module.compHom A ρ
  letI : Module R B := Module.compHom B τ
  change Module.rank R A ≤ (n : Cardinal) → Module.rank R B ≤ (n : Cardinal)
  intro hrank
  by_contra! h
  have hlarge : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank R B := by
    rwa [Nat.cast_add_one, Cardinal.natCast_add_one_le_iff]
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hlarge
  choose q m hm using fun i => hrec (v i)
  let k := Finset.univ.sup m
  let u (i : Fin (n + 1)) := b ^ (k - m i) * q i
  have hu (i : Fin (n + 1)) : s (u i) = s b ^ k * v i := by
    have hi : m i ≤ k := Finset.le_sup (Finset.mem_univ i)
    change s (b ^ (k - m i) * q i) = s b ^ k * v i
    rw [map_mul, map_pow, hm, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  have hind : LinearIndependent R u := by
    refine Fintype.linearIndependent_iff.mpr fun f hf => ?_
    have hf' : ∑ i, ρ (f i) * u i = 0 := hf
    have h := congrArg s hf'
    have hcomp (r : R) : s (ρ r) = τ r := DFunLike.congr_fun hs r
    rw [map_sum, map_zero] at h
    simp only [map_mul, hu, hcomp] at h
    have hprod : s b ^ k * ∑ i, τ (f i) * v i = 0 := by
      simpa only [Finset.mul_sum, mul_left_comm] using h
    exact Fintype.linearIndependent_iff.mp hv f
      ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ hb))
  have hsmall : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank R A :=
    Module.le_rank_iff.mpr ⟨u, hind⟩
  exact (Nat.not_succ_le_self n) (by exact_mod_cast hsmall.trans hrank)

end

end K1_13_5_5_2_3
end PackSource_K1_13_5_5_2_3Specialization

section PackSource_K1_13_5_5_2_3_1Equation
set_option autoImplicit true
namespace K1_13_5_5_2_3_1

noncomputable section

open scoped BigOperators Polynomial

variable {F R S σ : Type} [Field F] [CommRing R] [CommRing S]

/-- Homogenize to the total degree while evaluating coordinates and coefficients. -/
def homogeneousEval (f : F →+* R) (g : MvPolynomial σ F) (x : σ → R) (w : R) : R :=
  ∑ d ∈ g.support, f (g.coeff d) * (∏ i ∈ d.support, x i ^ d i) *
    w ^ (g.totalDegree - d.degree)

theorem map_homogeneousEval (k : R →+* S) (f : F →+* R) (g : MvPolynomial σ F)
    (x : σ → R) (w : R) :
    k (homogeneousEval f g x w) = homogeneousEval (k.comp f) g (k ∘ x) (k w) := by
  simp [homogeneousEval, map_sum, map_prod]

theorem homogeneousEval_zero (f : F →+* R) (g : MvPolynomial σ F) (x : σ → R) :
    homogeneousEval f g x 0 = (MvPolynomial.homogeneousComponent g.totalDegree g).eval₂ f x := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply, MvPolynomial.eval₂_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d.degree ≤ g.totalDegree := MvPolynomial.le_totalDegree hd
  by_cases he : d.degree = g.totalDegree
  · simp [he, MvPolynomial.eval₂_monomial, Finsupp.prod]
  · simp [he, zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hle he))]

theorem homogeneousEval_scaled (f : F →+* R) (g : MvPolynomial σ F) (x : σ → R) (w : R) :
    homogeneousEval f g (fun i => x i * w) w = g.eval₂ f x * w ^ g.totalDegree := by
  rw [homogeneousEval, MvPolynomial.eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d.degree ≤ g.totalDegree := MvPolynomial.le_totalDegree hd
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_apply]
  rw [← mul_assoc (f _), mul_assoc (f _ * ∏ i ∈ d.support, x i ^ d i),
    ← pow_add, Nat.add_sub_of_le hle]

open Polynomial in
private theorem coeff_prod_at_sum {ι : Type} (s : Finset ι) (p : ι → R[X]) (n : ι → ℕ)
    (h : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (p i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, (p j).natDegree ≤ n j := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self i s))
        ((natDegree_prod_le s p).trans (Finset.sum_le_sum hs)), ih hs]

/-- The equation after inserting a line in direction v with offset a. -/
def lineEquation (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R) : R[X] :=
  homogeneousEval (Polynomial.C.comp f) g
    (fun i => Polynomial.C (a i) + Polynomial.C (f (v i)) * Polynomial.X) (Polynomial.C w)

open Polynomial in
theorem lineEquation_degree (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R) :
    (lineEquation f g v a w).natDegree ≤ g.totalDegree ∧
    (lineEquation f g v a w).coeff g.totalDegree =
      f (MvPolynomial.eval v (MvPolynomial.homogeneousComponent g.totalDegree g)) := by
  classical
  let q : σ → R[X] := fun i => C (a i) + C (f (v i)) * X
  have hq (i : σ) : (q i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · simpa only [pow_one] using natDegree_C_mul_X_pow_le (f (v i)) 1
  have hqcoeff (i : σ) : (q i).coeff 1 = f (v i) := by
    simp [q, coeff_add]
  let term (d : σ →₀ ℕ) : R[X] :=
    C (f (g.coeff d) * w ^ (g.totalDegree - d.degree)) * ∏ i ∈ d.support, q i ^ d i
  have hterm (d : σ →₀ ℕ) : (term d).natDegree ≤ d.degree := by
    apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => by
      simpa using natDegree_pow_le_of_le (d i) (hq i))
  have hsum : lineEquation f g v a w = ∑ d ∈ g.support, term d := by
    unfold lineEquation homogeneousEval
    apply Finset.sum_congr rfl
    intro d _
    simp only [term, RingHom.comp_apply, map_mul, map_pow]
    ring
  rw [hsum]
  refine ⟨natDegree_sum_le_of_forall_le _ _ (fun d hd => (hterm d).trans
    (MvPolynomial.le_totalDegree hd)), ?_⟩
  rw [finsetSum_coeff, MvPolynomial.homogeneousComponent_apply, map_sum, map_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d.degree ≤ g.totalDegree := MvPolynomial.le_totalDegree hd
  by_cases he : d.degree = g.totalDegree
  · have hprod :
        (∏ i ∈ d.support, q i ^ d i).coeff d.degree =
          ∏ i ∈ d.support, f (v i ^ d i) := by
      rw [Finsupp.degree_apply, coeff_prod_at_sum d.support (fun i => q i ^ d i) d
        (fun i _ => by simpa using natDegree_pow_le_of_le (d i) (hq i))]
      apply Finset.prod_congr rfl
      intro i _
      simpa [hqcoeff, Nat.mul_one] using
        (coeff_pow_of_natDegree_le (m := d i) (hq i))
    simp only [he, ↓reduceIte, Nat.sub_self, pow_zero, mul_one, term, coeff_C_mul]
    rw [← he, hprod]
    simp [MvPolynomial.eval_monomial, Finsupp.prod, map_mul, map_prod]
  · simp [he, coeff_eq_zero_of_natDegree_lt ((hterm d).trans_lt (lt_of_le_of_ne hle he))]

/-- Multiply by the inverse of the scalar leading coefficient. -/
def monicEquation (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R) : R[X] :=
  Polynomial.C (f (MvPolynomial.eval v (MvPolynomial.homogeneousComponent g.totalDegree g))⁻¹) *
    lineEquation f g v a w

open Polynomial in
theorem monicEquation_spec [Nontrivial R] (f : F →+* R) (g : MvPolynomial σ F)
    (v : σ → F) (a : σ → R) (w : R)
    (hv : MvPolynomial.eval v (MvPolynomial.homogeneousComponent g.totalDegree g) ≠ 0) :
    (monicEquation f g v a w).Monic ∧ (monicEquation f g v a w).natDegree = g.totalDegree := by
  obtain ⟨hd, hc⟩ := lineEquation_degree f g v a w
  have hcoeff : (monicEquation f g v a w).coeff g.totalDegree = 1 := by
    rw [monicEquation, coeff_C_mul, hc, ← map_mul, inv_mul_cancel₀ hv, map_one]
  have hdeg : (monicEquation f g v a w).natDegree = g.totalDegree :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_C_mul_le _ _).trans hd)
      (by rw [hcoeff]; exact one_ne_zero)
  exact ⟨by rwa [Monic, leadingCoeff, hdeg], hdeg⟩

open Polynomial in
theorem monicEquation_root (f : F →+* R) (g : MvPolynomial σ F) (v : σ → F)
    (a : σ → R) (w : R) (ρ : R →+* S) (z : S)
    (h : homogeneousEval (ρ.comp f) g (fun i => ρ (a i) + ρ (f (v i)) * z) (ρ w) = 0) :
    (monicEquation f g v a w).eval₂ ρ z = 0 := by
  have hf : (eval₂RingHom ρ z).comp (C.comp f) = ρ.comp f := by
    ext r
    simp [eval₂_C]
  have hline : (eval₂RingHom ρ z) (lineEquation f g v a w) = 0 := by
    rw [lineEquation, map_homogeneousEval, hf]
    simpa [Function.comp_def, map_add, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X] using h
  change (eval₂RingHom ρ z) (monicEquation f g v a w) = 0
  rw [monicEquation, map_mul, hline, mul_zero]

end

end K1_13_5_5_2_3_1
end PackSource_K1_13_5_5_2_3_1Equation

section PackSource_K1_13_6_1_4_1_1Elimination
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace K1_13_6_1_4_1_1

noncomputable section

open MvPolynomial

/-- Eliminate the parameter at `c` when its coefficient is `1`. The
remaining polynomial ring still contains the original coefficient ring. -/
theorem eliminateConstantParameter {A τ : Type*} [CommRing A] [Nontrivial A]
    (s : Finset τ) (c : τ) (hc : c ∈ s) (v : τ → A) (hv : v c = 1) :
    let g : MvPolynomial τ A := ∑ m ∈ s, MvPolynomial.X m * MvPolynomial.C (v m)
    g ≠ 0 ∧
      ∃ f : MvPolynomial τ A →+* MvPolynomial {m // m ≠ c} A,
        RingHom.ker f = Ideal.span {g} ∧ f.comp MvPolynomial.C = MvPolynomial.C := by
  classical
  let B := MvPolynomial {m // m ≠ c} A
  let e : MvPolynomial τ A ≃ₐ[A] Polynomial B :=
    (renameEquiv A (Equiv.optionSubtypeNe c).symm).trans (optionEquivLeft A _)
  let g : MvPolynomial τ A := ∑ m ∈ s, MvPolynomial.X m * MvPolynomial.C (v m)
  let y : B := ∑ m ∈ s.erase c, if hm : m ≠ c then MvPolynomial.X ⟨m, hm⟩ * MvPolynomial.C (v m) else 0
  have eC (a : A) : e (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
    change optionEquivLeft A _ (rename (Equiv.optionSubtypeNe c).symm (MvPolynomial.C a)) = _
    rw [rename_C, optionEquivLeft_C]
  have eX (m : τ) : e (MvPolynomial.X m) = match (Equiv.optionSubtypeNe c).symm m with
      | none => Polynomial.X
      | some n => Polynomial.C (MvPolynomial.X n) := by
    change optionEquivLeft A _ (rename (Equiv.optionSubtypeNe c).symm (MvPolynomial.X m)) = _
    rw [rename_X]
    cases (Equiv.optionSubtypeNe c).symm m with
    | none => exact optionEquivLeft_X_none A _
    | some n => exact optionEquivLeft_X_some A _ n
  have eg : e g = Polynomial.X + Polynomial.C y := by
    dsimp only [g, y]
    rw [← Finset.sum_erase_add _ _ hc, map_add, map_sum, map_sum, add_comm]
    congr 1
    · rw [hv, map_one, mul_one, eX, Equiv.optionSubtypeNe_symm_self]
    · apply Finset.sum_congr rfl
      intro m hm
      have hmc := Finset.ne_of_mem_erase hm
      rw [dite_eq_left hmc, map_mul, eX, Equiv.optionSubtypeNe_symm_of_ne hmc, eC, map_mul]
  change g ≠ 0 ∧ _
  refine ⟨?_, (Polynomial.evalRingHom (-y)).comp e.toRingHom, ?_, ?_⟩
  · intro hg
    have h := congrArg (fun p : Polynomial B => p.coeff 1) (eg.symm.trans (hg ▸ e.map_zero))
    simp at h
  · rw [← RingHom.comap_ker, Polynomial.ker_evalRingHom]
    have hh : Polynomial.X - Polynomial.C (-y) = e.toRingHom g := by
      change Polynomial.X - Polynomial.C (-y) = e g
      rw [eg, map_neg, sub_neg_eq_add]
    rw [hh, ← Set.image_singleton (f := e.toRingHom) (a := g), ← Ideal.map_span]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  · apply RingHom.ext
    intro a
    change Polynomial.eval (-y) (e (MvPolynomial.C a)) = MvPolynomial.C a
    rw [eC, Polynomial.eval_C]

end

end K1_13_6_1_4_1_1
end PackSource_K1_13_6_1_4_1_1Elimination

section PackSource_K1_13_5_4_2_3Aux1
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_5_4_2_3

noncomputable section

/-- A strict inclusion of contracted ideals remains strict after adjoining a
parameter. The parameter is a unit in the localization and lies in the
maximal ideal downstairs. -/
private theorem contract_sup_span_strictMono {R S : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (algebraMap R S a)) :
    StrictMono (fun J : Ideal S => J.under R ⊔ Ideal.span {a}) := by
  intro J K hJK
  have hle := (IsLocalization.orderEmbedding M S).monotone hJK.le
  refine lt_of_le_of_ne (sup_le_sup_right hle _) ?_
  intro heq
  change J.under R ⊔ Ideal.span {a} = K.under R ⊔ Ideal.span {a} at heq
  have hcontain : K.under R ≤ J.under R ⊔ Ideal.span {a} * K.under R := by
    intro b hb
    have hb' : b ∈ J.under R ⊔ Ideal.span {a} := by
      rw [heq]
      exact Ideal.mem_sup_left hb
    obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb'
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
    have had : a * d ∈ K.under R := by
      rw [← add_sub_cancel_left j (a * d)]
      exact (K.under R).sub_mem hb (hle hj)
    have hd : d ∈ K.under R := by
      change algebraMap R S d ∈ K
      have hh : algebraMap R S a * algebraMap R S d ∈ K := by
        rw [← map_mul]
        exact had
      obtain ⟨u, hu⟩ := hu
      rw [← hu] at hh
      simpa [← mul_assoc] using K.mul_mem_left (↑u⁻¹ : S) hh
    exact Submodule.mem_sup.mpr ⟨j, hj, a * d,
      Ideal.mem_span_singleton_mul.mpr ⟨d, hd, rfl⟩, rfl⟩
  have hback : K.under R ≤ J.under R :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      ((Ideal.span_singleton_le_iff_mem _).mpr
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R) ha)) hcontain
  exact hJK.not_ge ((IsLocalization.under_le_under_iff M S).mp hback)

/-- Localizing away from a parameter and then taking colength gives a lower
bound for the colength of the parameter quotient at the closed point. -/
private theorem length_localization_le_length_cut {R S : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R) {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (algebraMap R S a)) :
    Module.length S (S ⧸ I.map (algebraMap R S)) ≤ Module.length R (R ⧸ (I ⊔ Ideal.span {a})) := by
  let F : Set.Ici (I.map (algebraMap R S)) → Set.Ici (I ⊔ Ideal.span {a}) := fun J =>
    ⟨J.1.under R ⊔ Ideal.span {a}, sup_le_sup_right (Ideal.map_le_iff_le_comap.mp J.2) _⟩
  have hF : StrictMono F := fun _ _ h => contract_sup_span_strictMono M ha hu h
  rw [← WithBot.coe_le_coe, Module.length_quotient, Module.length_quotient,
    Order.coheight_eq_krullDim_Ici, Order.coheight_eq_krullDim_Ici]
  exact Order.krullDim_le_of_strictMono F hF

/-- The generic colength on a component bounds the closed-point colength
after a cut that passes through the point and misses the component. -/
theorem length_atPrime_le_length_principalCut {R : Type*}
    [CommRing R] [IsNoetherianRing R] {P Q I : Ideal R} [P.IsPrime] [Q.IsPrime]
    (hPQ : P ≤ Q) {a : R} (haQ : a ∈ Q) (haP : a ∉ P) :
    let A := Localization.AtPrime P
    let B := Localization.AtPrime Q
    Module.length A (A ⧸ I.map (algebraMap R A)) ≤
      Module.length B (B ⧸ (I ⊔ Ideal.span {a}).map (algebraMap R B)) := by
  let A := Localization.AtPrime P
  let B := Localization.AtPrime Q
  have hsub : Q.primeCompl ≤ P.primeCompl := fun _ h => fun hp => h (hPQ hp)
  change Module.length A (A ⧸ I.map (algebraMap R A)) ≤
    Module.length B (B ⧸ (I ⊔ Ideal.span {a}).map (algebraMap R B))
  let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe B A _ _ hsub
  let : IsScalarTower R B A := IsLocalization.localization_isScalarTower_of_submonoid_le B A _ _ hsub
  let : IsLocalization (P.primeCompl.map (algebraMap R B)) A :=
    IsLocalization.isLocalization_of_submonoid_le B A _ _ hsub
  have ha : algebraMap R B a ∈ IsLocalRing.maximalIdeal B := by
    change a ∈ (IsLocalRing.maximalIdeal B).under R
    rwa [IsLocalization.AtPrime.under_maximalIdeal B Q]
  have hu : IsUnit (algebraMap B A (algebraMap R B a)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact IsLocalization.map_units A (⟨a, haP⟩ : P.primeCompl)
  have he := length_localization_le_length_cut (P.primeCompl.map (algebraMap R B))
    (I.map (algebraMap R B)) ha hu
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R B A] at he
  rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

end

end K1_13_5_4_2_3
end PackSource_K1_13_5_4_2_3Aux1

section PackSource_K1_13_7_6_2_2Euler
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6_2_2

open LinearMap

section Euler

variable {R : Type*} [CommRing R]
variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

/-- The finite-length criterion for the Euler characteristic of multiplication by a scalar. -/
def CutFinite (t : R) (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  Module.length R (ker (lsmul R M t)) < ⊤ ∧
    Module.length R (M ⧸ range (lsmul R M t)) < ⊤

/-- Cokernel length minus kernel length, used only under the finite-length criterion. -/
noncomputable def cutEuler (t : R) (M : Type*) [AddCommGroup M] [Module R M] : ℤ :=
  ((Module.length R (M ⧸ range (lsmul R M t))).toNat : ℤ) -
    (Module.length R (ker (lsmul R M t))).toNat

theorem length_kernel_add_range (v : M →ₗ[R] N) :
    Module.length R M = Module.length R (ker v) + Module.length R (range v) := by
  refine Module.length_eq_add_of_exact (ker v).subtype v.rangeRestrict
    (Submodule.subtype_injective _) v.surjective_rangeRestrict ?_
  rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]

theorem length_range_add_cokernel (v : M →ₗ[R] N) :
    Module.length R N = Module.length R (range v) + Module.length R (N ⧸ range v) :=
  Module.length_eq_add_of_exact (range v).subtype (range v).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

theorem cut_add (t : R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM : CutFinite t M) (hP : CutFinite t P) :
    CutFinite t N ∧ cutEuler t N = cutEuler t M + cutEuler t P := by
  let a := lsmul R M t
  let b := lsmul R N t
  let c := lsmul R P t
  have hab : g.comp b = c.comp g := by ext x; simp [b, c]
  have hbc : f.comp a = b.comp f := by ext x; simp [a, b]
  let fK : ker a →ₗ[R] ker b := (f.comp (ker a).subtype).codRestrict _ (by
    intro x
    change t • f x.val = 0
    rw [← map_smul]
    exact (congrArg f x.property).trans (map_zero f))
  let gK : ker b →ₗ[R] ker c := (g.comp (ker b).subtype).codRestrict _ (by
    intro x
    change t • g x.val = 0
    rw [← map_smul]
    exact (congrArg g x.property).trans (map_zero g))
  let fC := Submodule.mapQ (range a) (range b) f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, (DFunLike.congr_fun hbc x).symm⟩)
  let gC := Submodule.mapQ (range b) (range c) g (by
    rintro _ ⟨x, rfl⟩
    exact ⟨g x, (DFunLike.congr_fun hab x).symm⟩)
  let δ := SnakeLemma.δ' a b c f g hfg f g hfg hbc hab
    (ker c).subtype (LinearMap.exact_subtype_ker_map c) (range a).mkQ
    (LinearMap.exact_map_mkQ_range a) hg hf
  have hfK : Function.Injective fK := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
  have hgC : Function.Surjective gC := by
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨y, rfl⟩ := hg x
    exact ⟨(range b).mkQ y, rfl⟩
  have hk : Function.Exact fK gK := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (hfg x.val).mp (congrArg Subtype.val hx)
      have hay : a y = 0 := hf (by
        simpa [hy, x.property] using DFunLike.congr_fun hbc y)
      exact ⟨⟨y, hay⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (hfg.apply_apply_eq_zero y.val)
  have hkδ : Function.Exact gK δ :=
    SnakeLemma.exact_δ'_right a b c f g hfg f g hfg hbc hab
      (ker b).subtype (LinearMap.exact_subtype_ker_map b)
      (ker c).subtype (LinearMap.exact_subtype_ker_map c)
      (range a).mkQ (LinearMap.exact_map_mkQ_range a) hg hf gK rfl
      (Submodule.subtype_injective _)
  have hδc : Function.Exact δ fC :=
    SnakeLemma.exact_δ'_left a b c f g hfg f g hfg hbc hab
      (ker c).subtype (LinearMap.exact_subtype_ker_map c)
      (range a).mkQ (LinearMap.exact_map_mkQ_range a)
      (range b).mkQ (LinearMap.exact_map_mkQ_range b) hg hf fC rfl
      (Submodule.mkQ_surjective _)
  have hc : Function.Exact fC gC := by
    apply (hfg.exact_mapQ_iff _ _).2
    rw [show range g = ⊤ from LinearMap.range_eq_top.mpr hg, top_inf_eq]
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hg x
    exact ⟨b y, ⟨y, rfl⟩, DFunLike.congr_fun hab y⟩
  change Module.length R (ker a) < ⊤ ∧ Module.length R (M ⧸ range a) < ⊤ at hM
  change Module.length R (ker c) < ⊤ ∧ Module.length R (P ⧸ range c) < ⊤ at hP
  have l1 := length_kernel_add_range gK
  rw [hk.linearMap_ker_eq, ← (LinearEquiv.ofInjective fK hfK).length_eq] at l1
  have l2 := length_kernel_add_range δ
  rw [hkδ.linearMap_ker_eq] at l2
  have l3 := length_kernel_add_range fC
  rw [hδc.linearMap_ker_eq] at l3
  have l4 := length_kernel_add_range gC
  rw [hc.linearMap_ker_eq, LinearMap.range_eq_top.mpr hgC, Module.length_top] at l4
  have h2 := ENat.add_lt_top.mp (l2 ▸ hP.1)
  have h3 := ENat.add_lt_top.mp (l3 ▸ hM.2)
  refine ⟨⟨l1.symm ▸ ENat.add_lt_top.mpr ⟨hM.1, h2.1⟩,
      l4.symm ▸ ENat.add_lt_top.mpr ⟨h3.2, hP.2⟩⟩, ?_⟩
  have n1 := congrArg ENat.toNat l1
  have n2 := congrArg ENat.toNat l2
  have n3 := congrArg ENat.toNat l3
  have n4 := congrArg ENat.toNat l4
  rw [ENat.toNat_add hM.1.ne h2.1.ne] at n1
  rw [ENat.toNat_add h2.1.ne h2.2.ne] at n2
  rw [ENat.toNat_add h3.1.ne h3.2.ne] at n3
  rw [ENat.toNat_add h3.2.ne hP.2.ne] at n4
  unfold cutEuler
  change ((Module.length R (N ⧸ range b)).toNat : ℤ) - (Module.length R (ker b)).toNat =
    ((Module.length R (M ⧸ range a)).toNat : ℤ) - (Module.length R (ker a)).toNat +
      (((Module.length R (P ⧸ range c)).toNat : ℤ) - (Module.length R (ker c)).toNat)
  omega

theorem cut_congr (t : R) (e : M ≃ₗ[R] N) :
    (CutFinite t M ↔ CutFinite t N) ∧ cutEuler t M = cutEuler t N := by
  let a := lsmul R M t
  let b := lsmul R N t
  have hker : (ker a).map e.toLinearMap = ker b := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    constructor
    · rintro ⟨z, hz, ezy⟩
      have hx : a x = 0 := e.injective ezy ▸ hz
      show t • e x = 0
      rw [← map_smul, show t • x = 0 from hx, map_zero]
    · intro hx
      exact ⟨x, e.injective (by simpa [a, b] using hx), rfl⟩
  have hrange : (range a).map e.toLinearMap = range b := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp [a, b]⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := e.surjective x
      exact ⟨a z, ⟨z, rfl⟩, by simp [a, b]⟩
  have lk := (e.ofSubmodules (ker a) (ker b) hker).length_eq
  have lc := (Submodule.Quotient.equiv (range a) (range b) e hrange).length_eq
  unfold CutFinite cutEuler
  rw [lk, lc]
  exact ⟨Iff.rfl, rfl⟩

theorem cut_of_finite_length (t : R) (h : Module.length R M < ⊤) :
    CutFinite t M ∧ cutEuler t M = 0 := by
  let a := lsmul R M t
  have lk := length_kernel_add_range a
  have lc := length_range_add_cokernel a
  have hk := ENat.add_lt_top.mp (lk ▸ h)
  have hc := ENat.add_lt_top.mp (lc ▸ h)
  refine ⟨⟨hk.1, hc.2⟩, ?_⟩
  have h₁ := congrArg ENat.toNat lk
  have h₂ := congrArg ENat.toNat lc
  rw [ENat.toNat_add hk.1.ne hk.2.ne] at h₁
  rw [ENat.toNat_add hc.1.ne hc.2.ne] at h₂
  unfold cutEuler
  change ((Module.length R (M ⧸ range a)).toNat : ℤ) - (Module.length R (ker a)).toNat = 0
  omega

end Euler
end K1_13_7_6_2_2
end PackSource_K1_13_7_6_2_2Euler

section PackSource_K1_13_7_4_2_2Defs
set_option autoImplicit true
namespace K1_13_7_4_2_2

noncomputable section

open MvPolynomial

abbrev Vars (K : Type*) [CommRing K] (n : ℕ) := idealOfVars (Fin n) K

abbrev Jets (K : Type*) [CommRing K] (n t : ℕ) :=
  MvPolynomial (Fin n) K ⧸ Vars K n ^ t

abbrev jet (K : Type*) [CommRing K] (n t : ℕ) :
    MvPolynomial (Fin n) K →+* Jets K n t := Ideal.Quotient.mk _

abbrev aug (K : Type*) [CommRing K] (n t : ℕ) : Ideal (Jets K n t) :=
  (Vars K n).map (jet K n t)

theorem aug_pow_self (K : Type*) [CommRing K] (n t : ℕ) :
    aug K n t ^ t = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

theorem aug_eq_span (K : Type*) [CommRing K] (n t : ℕ) :
    aug K n t = Ideal.span (Set.range fun i => jet K n t (X i)) := by
  change (Ideal.span (Set.range X)).map (jet K n t) = _
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem X_mem_aug (K : Type*) [CommRing K] (n t : ℕ) (i : Fin n) :
    jet K n t (X i) ∈ aug K n t :=
  Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

theorem ker_constantCoeff (K : Type*) [CommRing K] (n : ℕ) :
    RingHom.ker (constantCoeff : MvPolynomial (Fin n) K →+* K) = Vars K n := by
  ext p
  rw [RingHom.mem_ker, ← pow_one (Vars K n), mem_pow_idealOfVars_iff']
  change p.coeff 0 = 0 ↔ _
  constructor
  · intro h d hd
    obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (Nat.lt_one_iff.mp hd)
    exact h
  · intro h
    exact h 0 (by simp)

abbrev constant (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t) :
    Jets K n t →+* K :=
  Ideal.Quotient.lift _ constantCoeff <| by
    change Vars K n ^ t ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin n) K →+* K)
    rw [ker_constantCoeff]
    exact Ideal.pow_le_self ht.ne'

@[simp] theorem constant_jet (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t)
    (p : MvPolynomial (Fin n) K) : constant K n t ht (jet K n t p) = constantCoeff p := rfl

theorem ker_constant (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t) :
    RingHom.ker (constant K n t ht) = aug K n t := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, constant_jet, ← RingHom.mem_ker, ker_constantCoeff]
  change p ∈ Vars K n ↔ p ∈ (aug K n t).comap (jet K n t)
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change p ∈ Vars K n ↔ p ∈ Vars K n ⊔ RingHom.ker (jet K n t)
  rw [Ideal.mk_ker, sup_eq_left.mpr (Ideal.pow_le_self ht.ne')]

@[simp] theorem constant_algebraMap (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t)
    (c : K) : constant K n t ht (algebraMap K (Jets K n t) c) = c := by
  change constant K n t ht (jet K n t (C c)) = c
  simp

theorem constant_surjective (K : Type*) [CommRing K] (n t : ℕ) (ht : 0 < t) :
    Function.Surjective (constant K n t ht) := fun c =>
  ⟨algebraMap K (Jets K n t) c, constant_algebraMap K n t ht c⟩

end

end K1_13_7_4_2_2
end PackSource_K1_13_7_4_2_2Defs

section PackSource_K1_13_6_2_3_3_1Lift
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_2_3_3_1

noncomputable section

open MvPolynomial
open scoped MonomialOrder BigOperators

variable {k σ : Type*} [Field k] [Finite σ]

/-- A cyclic submodule of an affine quotient inherits the ordinary degree
filtration up to a bounded shift in the degree of a cyclic representative. -/
theorem exists_degree_shift (I : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k) :
    ∃ C : ℕ, ∀ f ∈ I ⊔ Ideal.span {g}, ∃ q : MvPolynomial σ k,
      f - q * g ∈ I ∧ q.totalDegree ≤ f.totalDegree + C := by
  classical
  let := Fintype.ofFinite σ
  let : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  let : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  let J := I ⊔ Ideal.span {g}
  obtain ⟨E, hE⟩ := m.exists_finset_standardExponents_iff J
  have hex (e : E) : ∃ b ∈ J, b ≠ 0 ∧ m.degree b ≤ (e : σ →₀ ℕ) := by
    by_contra! h
    have hs : (e : σ →₀ ℕ) ∈ m.standardExponents J := fun b hb hn => h b hb hn
    exact (hE _).mp hs _ e.property le_rfl
  choose b hb hn he using hex
  let B : Set (MvPolynomial σ k) := Set.range b
  let : Fintype B := (Set.finite_range b).fintype
  have hB (x : B) : (x : MvPolynomial σ k) ∈ J ∧ (x : MvPolynomial σ k) ≠ 0 := by
    obtain ⟨e, h⟩ := x.property
    rw [← h]
    exact ⟨hb e, hn e⟩
  have hrep (x : B) : ∃ q : MvPolynomial σ k, (x : MvPolynomial σ k) - q * g ∈ I := by
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (hB x).1
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hj
    refine ⟨q, ?_⟩
    rw [← hij, mul_comm g q, add_sub_cancel_right]
    exact hi
  choose a ha using hrep
  refine ⟨Finset.univ.sup fun x : B => (a x).totalDegree, ?_⟩
  intro f hf
  obtain ⟨c, r, hfr, hc, hr⟩ :=
    m.div_set (B := B) (fun x hx => m.isUnit_leadingCoeff.mpr (hB ⟨x, hx⟩).2) f
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hfr
  have hsum : ∑ x ∈ c.support, c x • (x : MvPolynomial σ k) ∈ J :=
    J.sum_mem fun x _ => J.smul_mem (c x) (hB x).1
  have hrJ : r ∈ J := by
    convert J.sub_mem hf hsum using 1
    rw [hfr, add_comm, add_sub_cancel_right]
  have hr0 : r = 0 := by
    by_contra hr0
    have hstd : m.degree r ∈ m.standardExponents J := by
      apply (hE _).mpr
      intro e heE hle
      exact hr _ (m.degree_mem_support hr0) (b ⟨e, heE⟩) ⟨⟨e, heE⟩, rfl⟩
        ((he ⟨e, heE⟩).trans hle)
    exact hstd r hrJ hr0 le_rfl
  refine ⟨∑ x ∈ c.support, c x * a x, ?_, ?_⟩
  · rw [Finset.sum_mul, hfr, hr0, add_zero, ← Finset.sum_sub_distrib]
    exact I.sum_mem fun x _ => by
      simpa only [smul_eq_mul, mul_sub, mul_assoc] using I.mul_mem_left (c x) (ha x)
  · apply totalDegree_finsetSum_le
    intro x _
    have hcx : (c x).totalDegree ≤ f.totalDegree := by
      by_cases hx : c x = 0
      · simp [hx]
      have hx' := m.totalDegree_le_of_degree_le
        (fun _ _ h => degree_le_degree_of_degLex_le h) (hc x)
      rw [totalDegree_mul_of_isDomain (hB x).2 hx] at hx'
      omega
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add hcx (Finset.le_sup (f := fun y : B => (a y).totalDegree) (Finset.mem_univ x)))

end

end K1_13_6_2_3_3_1
end PackSource_K1_13_6_2_3_3_1Lift

section PackSource_K1_13_6_1_4_3_3_1Length
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_3_3_1

open Ideal

private theorem mul_mem_square_iff {R : Type*} [CommRing R] (I : Ideal R) (a x : R)
    (hreg : ∀ y, a * y ∈ I → y ∈ I) :
    a * x ∈ I ⊔ span {a ^ 2} ↔ x ∈ I ⊔ span {a} := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
    have he : a * (x - a * r) = u := by
      calc
        a * (x - a * r) = a * x - a ^ 2 * r := by ring
        _ = u := by rw [← huv, add_sub_cancel_right]
    exact Submodule.mem_sup.mpr
      ⟨x - a * r, hreg _ (he ▸ hu), a * r, mem_span_singleton.mpr ⟨r, rfl⟩,
        sub_add_cancel _ _⟩
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
    exact Submodule.mem_sup.mpr
      ⟨a * u, I.mul_mem_left _ hu, a ^ 2 * r, mem_span_singleton.mpr ⟨r, rfl⟩,
        by rw [mul_add, pow_two, mul_assoc]⟩

/-- Multiplication by a regular element gives the kernel of the projection from the
quotient by its square to the quotient by the element itself. -/
theorem square_length {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    (I : Ideal R) (a : R) (hreg : ∀ y, a * y ∈ I → y ∈ I)
    [Module.Finite k (R ⧸ (I ⊔ span {a}))] :
    Module.Finite k (R ⧸ (I ⊔ span {a ^ 2})) ∧
      Module.finrank k (R ⧸ (I ⊔ span {a ^ 2})) =
        2 * Module.finrank k (R ⧸ (I ⊔ span {a})) := by
  let J : Ideal R := I ⊔ span {a}
  let J₂ : Ideal R := I ⊔ span {a ^ 2}
  change Module.Finite k (R ⧸ J₂) ∧ Module.finrank k (R ⧸ J₂) = 2 * Module.finrank k (R ⧸ J)
  have hle : J₂ ≤ J := sup_le_sup_left
    (span_singleton_le_span_singleton.mpr (dvd_pow_self a (by decide))) I
  let π : (R ⧸ J₂) →ₗ[k] (R ⧸ J) := (Ideal.Quotient.factorₐ k hle).toLinearMap
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hle
  let m : R →ₗ[k] (R ⧸ J₂) :=
    (Ideal.Quotient.mkₐ k J₂).toLinearMap.comp (LinearMap.mulLeft k a)
  let Jk : Submodule k R := J.restrictScalars k
  have hm (x : R) : m x = 0 ↔ x ∈ J := by
    change Ideal.Quotient.mk J₂ (a * x) = 0 ↔ x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact mul_mem_square_iff I a x hreg
  let ι : (R ⧸ J) →ₗ[k] (R ⧸ J₂) :=
    Jk.liftQ m (fun x hx => LinearMap.mem_ker.mpr ((hm x).mpr hx))
  have hι (x : R) : ι (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J₂ (a * x) := rfl
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hm x).mp (LinearMap.mem_ker.mp hz))
  have hexact : Function.Exact ι π := by
    rw [LinearMap.exact_iff]
    ext z
    constructor
    · intro hz
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hz)
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp hv
      refine ⟨Ideal.Quotient.mk J r, ?_⟩
      rw [hι, ← huv, map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ J₂ from le_sup_left) hu),
        zero_add]
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [hι]
      apply LinearMap.mem_ker.mpr
      change Ideal.Quotient.mk J (a * x) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show span {a} ≤ J from le_sup_right) (mem_span_singleton.mpr ⟨x, rfl⟩))
  have hfin : Module.Finite k (R ⧸ J₂) := Module.Finite.of_exact hexact hπ
  refine ⟨hfin, ?_⟩
  have hlen := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, LinearMap.exact_iff.mp hexact,
    LinearMap.finrank_range_of_inj hinj] at hlen
  simpa only [two_mul] using hlen.symm

end K1_13_6_1_4_3_3_1
end PackSource_K1_13_6_1_4_3_3_1Length

section PackSource_K1_13_7_3Geometry
set_option autoImplicit true
namespace K1_13_7_3
noncomputable section

open MvPolynomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

private def project (φ : L →ₗ[F] F) (P : MvPolynomial (Fin 3) L) :
    MvPolynomial (Fin 3) F :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange φ (map_zero φ) P.coeff)

private theorem coeff_project (φ : L →ₗ[F] F) (P : MvPolynomial (Fin 3) L)
    (m : Fin 3 →₀ ℕ) : (project φ P).coeff m = φ (P.coeff m) :=
  Finsupp.mapRange_apply (hf := map_zero φ)

private theorem project_mul (φ : L →ₗ[F] F) (P : MvPolynomial (Fin 3) F)
    (V : MvPolynomial (Fin 3) L) :
    project φ (MvPolynomial.map (algebraMap F L) P * V) = P * project φ V := by
  ext m
  simp only [coeff_project, coeff_mul, coeff_map, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem project_total_le (φ : L →ₗ[F] F) (V : MvPolynomial (Fin 3) L) :
    (project φ V).totalDegree ≤ V.totalDegree := by
  refine Finset.sup_le fun m hm => le_totalDegree ?_
  rw [MvPolynomial.mem_support_iff, coeff_project] at hm
  exact MvPolynomial.mem_support_iff.mpr fun h => hm (by rw [h, map_zero])

/-- A common geometric divisor of positive degree would yield a relation
with a smaller cofactor. Project a nonzero coefficient of that relation
back to the base field and contradict Euclid's lemma there. -/
theorem relPrime_map_field (P Q : MvPolynomial (Fin 3) F)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hrel : IsRelPrime P Q) :
    IsRelPrime (MvPolynomial.map (algebraMap F L) P)
      (MvPolynomial.map (algebraMap F L) Q) := by
  let i := algebraMap F L
  have hi : Function.Injective i := i.injective
  have hmap : Function.Injective (MvPolynomial.map (σ := Fin 3) i) := MvPolynomial.map_injective _ hi
  rintro D ⟨U, hU⟩ ⟨V, hV⟩
  by_contra hD
  have hv : V ≠ 0 := by
    intro hz
    exact hQ (hmap (by rw [hV, hz, mul_zero, map_zero]))
  have hd : D ≠ 0 := by
    intro hz
    exact hP (hmap (by rw [hU, hz, zero_mul, map_zero]))
  have hdeg : 0 < D.totalDegree := by
    by_contra! h
    have hc : D = C (D.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have hn : D.coeff 0 ≠ 0 := by
      intro hz
      exact hd (by rw [hc, hz, map_zero])
    exact hD (hc ▸ (isUnit_iff_ne_zero.mpr hn).map C)
  obtain ⟨m, hm⟩ := support_nonempty.mpr hv
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F (MvPolynomial.mem_support_iff.mp hm)
  have hpv : project φ V ≠ 0 := fun h => hφ (by
    simpa [coeff_project] using congrArg (fun G : MvPolynomial (Fin 3) F => G.coeff m) h)
  have hsyzygy : P * project φ V = Q * project φ U := by
    rw [← project_mul, ← project_mul]
    change project φ (MvPolynomial.map i P * V) = project φ (MvPolynomial.map i Q * U)
    rw [hU, hV, mul_assoc, mul_assoc, mul_comm U V]
  have hdiv : Q ∣ project φ V :=
    hrel.symm.dvd_of_dvd_mul_left ⟨project φ U, hsyzygy⟩
  have hle := (totalDegree_le_of_dvd_of_isDomain hdiv hpv).trans (project_total_le φ V)
  have heq : Q.totalDegree = D.totalDegree + V.totalDegree := by
    change (Finset.sup Q.support _) = _
    rw [← support_map_of_injective Q hi]
    change (MvPolynomial.map i Q).totalDegree = _
    rw [hV, totalDegree_mul_of_isDomain hd hv]
  omega

end
end K1_13_7_3
end PackSource_K1_13_7_3Geometry

section PackSource_K1_13_6_1_4_3_2Aux1
set_option autoImplicit true
namespace K1_13_6_1_4_3_2

noncomputable section

open scoped BigOperators
open LinearMap Submodule

section Length

variable {R : Type*} [CommRing R]

private theorem length_step (S K : Type*) [CommRing S] [CommRing K]
    [Algebra R S] [Algebra K S] [Module.Flat R S]
    (I Q : Ideal R) (x : R)
    (hQ : (⊥ : Submodule R (R ⧸ I)).colon {I.mkQ x} = Q) :
    Module.length K (S ⧸ I.map (algebraMap R S)) =
      Module.length K (S ⧸ Q.map (algebraMap R S)) +
        Module.length K (S ⧸ (I ⊔ Ideal.span {x}).map (algebraMap R S)) := by
  let N := I ⊔ Ideal.span {x}
  let f₀ := toSpanSingleton R (R ⧸ I) (I.mkQ x)
  have hf₀ : ker f₀ = Q := by
    rw [← hQ]
    ext a
    simp [f₀, mem_colon_singleton]
  let f : (R ⧸ Q) →ₗ[R] (R ⧸ I) := Q.liftQ f₀ hf₀.ge
  let hIN : I ≤ N := le_sup_left
  let g : (R ⧸ I) →ₗ[R] (R ⧸ N) := I.mapQ N LinearMap.id (by simpa using hIN)
  have hf : Function.Injective f :=
    ker_eq_bot.mp (Q.ker_liftQ_eq_bot f₀ hf₀.ge hf₀.le)
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨z, rfl⟩ := N.mkQ_surjective z
    exact ⟨I.mkQ z, rfl⟩
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    have hrange : range f = Submodule.map I.mkQ (Ideal.span {x}) := by
      dsimp only [f, f₀]
      rw [range_liftQ, LinearMap.range_toSpanSingleton,
        Ideal.span, Submodule.map_span, Set.image_singleton]
    dsimp only [g]
    rw [ker_mapQ, comap_id, hrange]
    change Submodule.map I.mkQ ((I : Submodule R R) ⊔ Ideal.span {x}) = _
    rw [Submodule.map_sup, mkQ_map_self, bot_sup_eq]
  let e (L : Ideal R) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S L).toLinearEquiv.restrictScalars K
  rw [(e I).length_eq, (e Q).length_eq, (e N).length_eq]
  exact Module.length_eq_add_of_exact ((f.baseChange S).restrictScalars K)
    ((g.baseChange S).restrictScalars K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (LinearMap.baseChange_surjective S hg) (Module.Flat.lTensor_exact S hfg)

/-- The length of a cyclic quotient at a prime of the original ring. -/
def localWeight (I P : Ideal R) : ℕ∞ :=
  haveI := Classical.dec P.IsPrime
  if hP : P.IsPrime then
    letI := hP
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))
  else 0

theorem localWeight_of_prime (I P : Ideal R) [hp : P.IsPrime] :
    localWeight I P =
      Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  exact dite_eq_left hp

private theorem localWeight_step {J I Q P : Ideal R} {x : R}
    (hJI : J ≤ I) (hP : J.IsMinimalPrime P) (hQ : Q.IsPrime)
    (hcolon : (⊥ : Submodule R (R ⧸ I)).colon {I.mkQ x} = Q) :
    localWeight I P = (if P = Q then 1 else 0) + localWeight (I ⊔ Ideal.span {x}) P := by
  classical
  let hp := hP.isPrime
  let L := Localization.AtPrime P
  have hIQ : I ≤ Q := by
    intro y hy
    rw [← hcolon, mem_colon_singleton, Submodule.mem_bot]
    change y • Ideal.Quotient.mk I x = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hy,
      zero_mul]
  have hlen := length_step L L I Q x hcolon
  rw [localWeight_of_prime, localWeight_of_prime, hlen]
  congr 1
  by_cases h : P = Q
  · rw [← h, ite_eq_left rfl, IsLocalization.AtPrime.map_eq_maximalIdeal P L]
    apply Module.length_eq_one_iff.mpr
    exact isSimpleModule_iff_quot_maximal.mpr
      ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  · have hn : ¬ Q ≤ P := fun hQP => h (hP.eq_of_le ⟨hQ, hJI.trans hIQ⟩ hQP).symm
    rw [ite_eq_right h, IsLocalization.AtPrime.map_eq_top_of_not_le (S := L) hn]
    exact Module.length_eq_zero

/-- Add the prime factors along a Noetherian induction on cyclic quotients.
At a minimal prime of the starting ideal, a factor contributes one exactly
when its prime is that minimal prime. -/
theorem weighted_length_le (S K : Type*) [CommRing S] [CommRing K]
    [Algebra R S] [Algebra K S] [Module.Flat R S] [IsNoetherianRing R]
    (J : Ideal R) (surfaces : Finset (Ideal R))
    (hmin : ∀ P ∈ surfaces, J.IsMinimalPrime P) :
    (∑ P ∈ surfaces, localWeight J P *
      Module.length K (S ⧸ P.map (algebraMap R S))) ≤
      Module.length K (S ⧸ J.map (algebraMap R S)) := by
  classical
  let d (I : Ideal R) := Module.length K (S ⧸ I.map (algebraMap R S))
  suffices H : ∀ I : Ideal R, J ≤ I → (∑ P ∈ surfaces, localWeight I P * d P) ≤ d I by
    exact H J le_rfl
  intro I
  induction I using WellFoundedGT.induction with
  | ind I ih =>
    intro hJI
    by_cases hI : I = ⊤
    · subst I
      have hw (P : Ideal R) (hP : P ∈ surfaces) : localWeight (⊤ : Ideal R) P = 0 := by
        let hp := (hmin P hP).isPrime
        rw [localWeight_of_prime, Ideal.map_top]
        exact Module.length_eq_zero
      simp [Finset.sum_congr rfl fun P hP => show localWeight (⊤ : Ideal R) P * d P = 0 by
        rw [hw P hP, zero_mul]]
    · have : Nontrivial (R ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hI
      obtain ⟨Q, hQ⟩ := associatedPrimes.nonempty R (R ⧸ I)
      rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hQ
      obtain ⟨hQ, z, hcolon⟩ := hQ
      obtain ⟨x, rfl⟩ := I.mkQ_surjective z
      have hx : x ∉ I := by
        intro hx
        have hzero : I.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero I).mpr hx
        rw [hzero, Submodule.colon_singleton_zero] at hcolon
        exact hQ.ne_top hcolon
      let N := I ⊔ Ideal.span {x}
      have hxN : x ∈ N :=
        (show Ideal.span {x} ≤ N from le_sup_right) (Ideal.mem_span_singleton_self x)
      have hIN : I < N := lt_of_le_of_ne le_sup_left (fun he => hx (he.symm ▸ hxN))
      have hnext := ih N hIN (hJI.trans hIN.le)
      have hstep : d I = d Q + d N := length_step S K I Q x hcolon.symm
      have hfirst :
          (∑ P ∈ surfaces, (if P = Q then (1 : ℕ∞) else 0) * d P) ≤ d Q := by
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']
        split <;> simp
      rw [hstep]
      calc
        _ = (∑ P ∈ surfaces, (if P = Q then (1 : ℕ∞) else 0) * d P) +
              ∑ P ∈ surfaces, localWeight N P * d P := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro P hP
          rw [localWeight_step hJI (hmin P hP) hQ hcolon.symm, add_mul]
        _ ≤ d Q + d N := add_le_add hfirst hnext

end Length

end

end K1_13_6_1_4_3_2
end PackSource_K1_13_6_1_4_3_2Aux1

section PackSource_K1_13_7_2_1_2Aux1
set_option autoImplicit true
namespace K1_13_7_2_1_2

noncomputable section

open Polynomial UniqueFactorizationMonoid
open scoped Polynomial

/-- Over a reduced coefficient ring, the separant annihilates every nilpotent
of a monic polynomial quotient. Check the monic remainder in each prime's
fraction field, where the derivative contains all but one copy of each factor. -/
private theorem monic_dvd_derivative_mul_of_dvd_pow {A : Type*} [CommRing A] [IsReduced A]
    {F g : A[X]} (hF : F.Monic) {n : ℕ} (h : F ∣ g ^ n) :
    F ∣ F.derivative * g := by
  classical
  apply (modByMonic_eq_zero_iff_dvd hF).mp
  ext i
  rw [coeff_zero]
  apply (nilpotent_iff_mem_prime.mpr ?_).eq_zero
  intro P hP
  let : P.IsPrime := hP
  let L := FractionRing (A ⧸ P)
  let ρ : A →+* L := (algebraMap (A ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hFL : (F.map ρ).Monic := hF.map ρ
  have hd : F.map ρ ∣ (g.map ρ) ^ n := by
    simpa only [map_pow, coe_mapRingHom] using map_dvd (Polynomial.mapRingHom ρ) h
  have hr : radical (F.map ρ) ∣ g.map ρ :=
    (exists_dvd_pow_iff_radical_dvd hFL.ne_zero).mp ⟨n, hd⟩
  have hL : F.map ρ ∣ (F.map ρ).derivative * g.map ρ := by
    calc
      F.map ρ = EuclideanDomain.divRadical (F.map ρ) * radical (F.map ρ) :=
        EuclideanDomain.divRadical_mul_radical.symm
      _ ∣ (F.map ρ).derivative * g.map ρ := mul_dvd_mul (divRadical_dvd_derivative _) hr
  have hm : ((F.derivative * g) %ₘ F).map ρ = 0 := by
    rw [map_modByMonic ρ hF, Polynomial.map_mul, ← derivative_map]
    exact (modByMonic_eq_zero_iff_dvd hFL).mpr hL
  have hc := congrArg (fun p : L[X] => p.coeff i) hm
  rw [coeff_map, coeff_zero] at hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (IsFractionRing.injective (A ⧸ P) L (by simpa [ρ] using hc))

attribute [local instance] Polynomial.algebra

/-- In the cut by a reduced lower equation, a power vanishing modulo the two
equations forces its base to vanish after inverting the leading coefficient
and separant. The displayed identity clears the leading-coefficient denominator. -/
theorem clear_monic_cut {A : Type*} [CommRing A] (F g : A[X]) {q : A}
    (hq : (Ideal.span ({q} : Set A)).IsRadical) {n : ℕ}
    (hn : g ^ n ∈ Ideal.span {F, Polynomial.C q}) :
    ∃ k : ℕ, Polynomial.C F.leadingCoeff ^ k * (F.derivative * g) ∈
      Ideal.span {F, Polynomial.C q} := by
  let I : Ideal A := Ideal.span {q}
  let J : Ideal A[X] := Ideal.span {F, Polynomial.C q}
  let B := A ⧸ I
  let a : B := Ideal.Quotient.mk I F.leadingCoeff
  let D := Localization.Away a
  let π : A[X] →+* B[X] := Polynomial.mapRingHom (Ideal.Quotient.mk I)
  let j : B[X] →+* D[X] := algebraMap B[X] D[X]
  let φ : A →+* D := (algebraMap B D).comp (Ideal.Quotient.mk I)
  let : IsLocalization ((Submonoid.powers a).map (Polynomial.C : B →+* B[X])) D[X] :=
    Polynomial.isLocalization (Submonoid.powers a) D
  have : IsReduced D := by
    have hB : (⊥ : Ideal B).radical = ⊥ :=
      nilradical_eq_bot_iff.mpr ((Ideal.isRadical_iff_quotient_reduced I).mp hq)
    have hD := IsLocalization.map_radical (Submonoid.powers a) D (⊥ : Ideal B)
    rw [hB, Ideal.map_bot] at hD
    exact nilradical_eq_bot_iff.mp hD.symm
  have hπ : Function.Surjective π :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = Ideal.span {Polynomial.C q} := by
    change RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk I)) = _
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
    simp [I, Ideal.map_span]
  have hπq : π (Polynomial.C q) = 0 := by
    change (Polynomial.C q).map (Ideal.Quotient.mk I) = 0
    rw [Polynomial.map_C, Ideal.Quotient.mk_singleton_self, Polynomial.C_0]
  have hJπ : J.map π = Ideal.span {π F} := by
    change (Ideal.span {F, Polynomial.C q}).map π = _
    rw [Ideal.span_insert, Ideal.map_sup, Ideal.map_span, Ideal.map_span,
      Set.image_singleton, Set.image_singleton, hπq, Ideal.span_singleton_zero, sup_bot_eq]
  have hj (x : A[X]) : j (π x) = x.map φ := by
    change (x.map (Ideal.Quotient.mk I)).map (algebraMap B D) = _
    rw [Polynomial.map_map]
  have hu : IsUnit (φ F.leadingCoeff) :=
    IsLocalization.Away.algebraMap_isUnit a
  have hlead : (F.map φ).leadingCoeff = φ F.leadingCoeff := by
    rcases subsingleton_or_nontrivial D with hD | hD
    · exact Subsingleton.elim _ _
    · exact leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero
  have hinv : φ F.leadingCoeff * (↑(hu.unit⁻¹) : D) = 1 := by
    calc
      _ = (↑hu.unit : D) * (↑(hu.unit⁻¹) : D) :=
        congrArg (fun c : D => c * (↑(hu.unit⁻¹) : D)) hu.unit_spec.symm
      _ = 1 := Units.mul_inv _
  let G : D[X] := F.map φ * Polynomial.C (↑(hu.unit⁻¹) : D)
  have hG : G.Monic := by
    apply monic_mul_C_of_leadingCoeff_mul_eq_one
    exact hlead.symm ▸ hinv
  have hscale : G * Polynomial.C (φ F.leadingCoeff) = F.map φ := by
    dsimp only [G]
    rw [mul_assoc, ← map_mul, mul_comm (↑(hu.unit⁻¹) : D), hinv, map_one, mul_one]
  have hnπ : π F ∣ (π g) ^ n := by
    have h := Ideal.mem_map_of_mem π (show g ^ n ∈ J from hn)
    rwa [hJπ, Ideal.mem_span_singleton, map_pow] at h
  have hnD : F.map φ ∣ (g.map φ) ^ n := by
    have h := map_dvd j hnπ
    rwa [map_pow, hj, hj] at h
  have hd := monic_dvd_derivative_mul_of_dvd_pow hG
    ((show G ∣ F.map φ from ⟨_, hscale.symm⟩).trans hnD)
  have hderiv : G.derivative * Polynomial.C (φ F.leadingCoeff) =
      (F.map φ).derivative := by
    simpa only [derivative_mul, derivative_C, mul_zero, add_zero]
      using congrArg derivative hscale
  have hdD : F.map φ ∣ (F.derivative * g).map φ := by
    obtain ⟨d, hd⟩ := hd
    refine ⟨d, ?_⟩
    rw [Polynomial.map_mul, ← derivative_map, ← hderiv, mul_right_comm, hd, mul_right_comm, hscale]
  have hmem : j (π (F.derivative * g)) ∈ (Ideal.span {π F}).map j := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, hj, hj]
    exact hdD
  obtain ⟨m, hm, hmJ⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((Submonoid.powers a).map (Polynomial.C : B →+* B[X])) D[X] _ _).mp hmem
  obtain ⟨b, hb, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  have hkerle : RingHom.ker π ≤ J := by
    rw [hker, Ideal.span_singleton_le_iff_mem]
    apply Ideal.subset_span
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hcomap : (J.map π).comap π = J := by
    rw [Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerle]
  rw [← show J = Ideal.span {F, Polynomial.C q} from rfl, ← hcomap, Ideal.mem_comap, hJπ]
  simpa only [map_mul, map_pow, π, coe_mapRingHom, Polynomial.map_C, a] using hmJ

end

end K1_13_7_2_1_2
end PackSource_K1_13_7_2_1_2Aux1

section PackSource_K1_13_6_1_4_2_1_1_2Cancel
set_option autoImplicit true
namespace K1_13_6_1_4_2_1_1_2

noncomputable section

open MvPolynomial
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem linear_cancel {R β : Type*} [CommRing R] (s : Finset β)
    (w : β → R) (b : β) (hb : b ∈ s) (hu : IsUnit (w b)) (p : MvPolynomial β R)
    (hp : p * (∑ j ∈ s, C (w j) * X j) = 0) : p = 0 := by
  classical
  let e := (renameEquiv R (Equiv.optionSubtypeNe b).symm).trans
    (optionEquivLeft R {j // j ≠ b})
  have hc (r : R) : e (C r) = Polynomial.C (C r) := by
    simp [e, renameEquiv_apply, optionEquivLeft_C]
  have hx (j : β) : (e (X j)).coeff 1 = if j = b then 1 else 0 := by
    by_cases hj : j = b
    · subst j
      simp [e, renameEquiv_apply, optionEquivLeft_X_none]
    · simp [e, renameEquiv_apply, Equiv.optionSubtypeNe_symm_of_ne hj,
        optionEquivLeft_X_some, hj]
  have hcoef : (e (∑ j ∈ s, C (w j) * X j)).coeff 1 = C (w b) := by
    simp only [map_sum, map_mul, Polynomial.finsetSum_coeff, hc, Polynomial.coeff_C_mul, hx]
    rw [Finset.sum_eq_single_of_mem b hb]
    · simp
    · intro j _ hj
      simp [hj]
  have hregular : e (∑ j ∈ s, C (w j) * X j) ∈
      (Polynomial (MvPolynomial {j // j ≠ b} R))⁰ :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
      (hcoef ▸ (hu.map (C (σ := {j // j ≠ b}))).mem_nonZeroDivisors)
  apply e.injective
  rw [map_zero, ← mul_right_mem_nonZeroDivisors_eq_zero_iff hregular, ← map_mul, hp, map_zero]

private theorem cancel_over_unit {R α β : Type*} [CommRing R] (l : MvPolynomial α R)
    (s : Finset β) (w : β → R) (b : β) (hb : b ∈ s) (hu : IsUnit (w b))
    (p : MvPolynomial β (MvPolynomial α R))
    (hp : p * (∑ j ∈ s, C (C (w j)) * X j) ∈ Ideal.span {C l}) :
    p ∈ Ideal.span {C l} := by
  let I : Ideal (MvPolynomial α R) := Ideal.span {l}
  let q := Ideal.Quotient.mk I
  have hk : RingHom.ker (MvPolynomial.map (σ := β) q) = Ideal.span {C l} := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
  have hmul := RingHom.mem_ker.mp (hk.symm ▸ hp)
  rw [map_mul, map_sum] at hmul
  simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X] at hmul
  rw [← hk, RingHom.mem_ker]
  exact linear_cancel s (fun j => q (C (w j))) b hb ((hu.map C).map q) _ hmul

/-- A right coefficient with invertible multiplier gives cancellation after imposing
a left equation. Before inverting the chart, cancellation clears a chart power. -/
theorem cancel_chart {R α β : Type*} [CommRing R] (l : MvPolynomial α R)
    (s : Finset β) (w : β → R) (b : β) (hb : b ∈ s) (a : R)
    (p : MvPolynomial β (MvPolynomial α R))
    (hp : p * (∑ j ∈ s, C (C (w j)) * X j) ∈ Ideal.span {C l}) :
    ∃ n : ℕ, (C (C (a * w b))) ^ n * p ∈ Ideal.span {C l} := by
  let z := a * w b
  let T := Localization.Away z
  let q := algebraMap R T
  let B := MvPolynomial β (MvPolynomial α T)
  let M := ((Submonoid.powers z).map (C (σ := α))).map (C (σ := β))
  let g := algebraMap (MvPolynomial β (MvPolynomial α R)) B
  have hloc : IsLocalization M B := MvPolynomial.isLocalization _ _
  have hu : IsUnit (q (w b)) := by
    have hz : IsUnit (q z) := IsLocalization.map_units T ⟨z, Submonoid.mem_powers _⟩
    change IsUnit (q (a * w b)) at hz
    rw [map_mul] at hz
    exact isUnit_of_mul_isUnit_right hz
  have hmap : (Ideal.span {C l}).map g = Ideal.span {C (MvPolynomial.map q l)} := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {MvPolynomial.map (MvPolynomial.map q) (C l)} = _
    rw [MvPolynomial.map_C]
  have hmem := Ideal.mem_map_of_mem g hp
  rw [hmap, map_mul] at hmem
  change g p * MvPolynomial.map (MvPolynomial.map q) (∑ j ∈ s, C (C (w j)) * X j) ∈ _ at hmem
  simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X] at hmem
  have h := cancel_over_unit (MvPolynomial.map q l) s (q ∘ w) b hb hu (g p) hmem
  rw [← hmap] at h
  obtain ⟨d, hd, hdp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M B
    (Ideal.span {C l}) p).mp h
  obtain ⟨e, he, rfl⟩ := Submonoid.mem_map.mp hd
  obtain ⟨f, hf, rfl⟩ := Submonoid.mem_map.mp he
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hf
  exact ⟨n, by simpa only [map_pow] using hdp⟩

/-- Cancellation up to a power of one element survives a separate localization. -/
theorem cancel_localization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I : Ideal A) (z r : A)
    (h : ∀ p : A, p * r ∈ I → ∃ n : ℕ, z ^ n * p ∈ I)
    (q : B) (hq : q * algebraMap A B r ∈ I.map (algebraMap A B)) :
    ∃ n : ℕ, (algebraMap A B z) ^ n * q ∈ I.map (algebraMap A B) := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj M q
  have hp : algebraMap A B (p * r) ∈ I.map (algebraMap A B) := by
    rw [map_mul, ← hs]
    have hmul : algebraMap A B s * (q * algebraMap A B r) ∈ I.map (algebraMap A B) :=
      Ideal.mul_mem_left _ _ hq
    convert hmul using 1
    ac_rfl
  obtain ⟨d, hd, hdp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M B I _).mp hp
  rw [← mul_assoc] at hdp
  obtain ⟨n, hn⟩ := h (d * p) hdp
  refine ⟨n, ?_⟩
  have he := Ideal.mem_map_of_mem (algebraMap A B) hn
  rw [map_mul, map_pow, map_mul, ← hs] at he
  have hu := (IsLocalization.map_units B ⟨d, hd⟩).mul (IsLocalization.map_units B s)
  have he' : (algebraMap A B d * algebraMap A B s) * ((algebraMap A B z) ^ n * q) ∈
      I.map (algebraMap A B) := by
    convert he using 1
    ac_rfl
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp he'

end

end K1_13_6_1_4_2_1_1_2
end PackSource_K1_13_6_1_4_2_1_1_2Cancel
