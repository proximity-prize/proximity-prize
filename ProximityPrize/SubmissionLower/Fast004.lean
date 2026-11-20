import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Field
import ProximityPrize.SubmissionLower.Fast000
set_option Elab.async false

section PackSource_K1_13_6_3_5_3_3_3Bounds
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_5_3_3_3

noncomputable section

open MvPolynomial Filter
open scoped BigOperators

variable {k σ τ F E : Type} [Field k] [Finite σ] [Finite τ]
variable [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E]
variable {P : Ideal (MvPolynomial σ k)} {Q : Ideal (MvPolynomial τ k)}

local notation "A" => MvPolynomial τ k ⧸ Q
local notation "B" => MvPolynomial σ k ⧸ P

/-- A basis lifted to the coordinate ring gives the lower Hilbert-function bound. -/
theorem lower_bound (g : A →ₐ[k] B) (i : A →ₐ[k] F) (j : B →ₐ[k] E)
    (hi : Function.Injective i) (hcomm : ∀ a, j (g a) = algebraMap F E (i a))
    (hg : ∀ t, g (Ideal.Quotient.mk Q (MvPolynomial.X t)) ∈ quotientDegreeLE P 1)
    {ι : Type} [Fintype ι] (e : Module.Basis ι F E)
    (u : ι → B) (hu : ∀ l, j (u l) = e l) :
    ∃ C : ℕ, ∀ n : ℕ, Fintype.card ι * affineHilbertFunction Q n ≤
      affineHilbertFunction P (n + C) := by
  classical
  choose d hd using fun l => exists_mem_quotientDegreeLE P (u l)
  obtain ⟨C, hC⟩ := Finite.exists_le d
  refine ⟨C, fun n => ?_⟩
  let T : (ι → quotientDegreeLE Q n) →ₗ[k] B :=
    ∑ l, (LinearMap.mulRight k (u l)).comp
      (g.toLinearMap.comp ((quotientDegreeLE Q n).subtype.comp (LinearMap.proj l)))
  have hT (x : ι → quotientDegreeLE Q n) : T x = ∑ l, g (x l) * u l := by
    simp [T]
  let S := T.codRestrict (quotientDegreeLE P (n + C)) fun x => by
    rw [hT]
    refine Submodule.sum_mem _ fun l _ => mul_mem_quotientDegreeLE ?_ ?_
    · simpa only [one_mul] using map_mem_quotientDegreeLE g hg (x l).property
    · exact quotientDegreeLE_mono P (hC l) (hd l)
  have hcoords (x : ι → quotientDegreeLE Q n) :
      j (T x) = e.equivFun.symm (fun l => i (x l)) := by
    simp only [hT, map_sum, map_mul, hcomm, hu, Module.Basis.equivFun_symm_apply, Algebra.smul_def]
  have hinj : Function.Injective S := by
    intro x y h
    have h' : T x = T y := congrArg Subtype.val h
    have h'' := e.equivFun.symm.injective ((hcoords x).symm.trans ((congrArg j h').trans (hcoords y)))
    exact funext fun l => Subtype.ext (hi (congrFun h'' l))
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h

variable [IsScalarTower k F E]

omit [Finite σ] in
/-- A common denominator for the coordinates of finitely many filtered
generators gives the upper Hilbert-function bound. -/
theorem upper_bound (g : A →ₐ[k] B) (i : A →ₐ[k] F) (j : B →ₐ[k] E)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hcomm : ∀ a, j (g a) = algebraMap F E (i a))
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Module.Basis ι F E)
    (v : κ → B)
    (hgen : ∀ n (x : B), x ∈ quotientDegreeLE P n → ∃ a : κ → A,
      (∀ l, a l ∈ quotientDegreeLE Q n) ∧ ∑ l, g (a l) * v l = x)
    {d : F} (hd : d ≠ 0) (b : κ → ι → A)
    (hb : ∀ l r, i (b l r) = d * e.equivFun (j (v l)) r) :
    ∃ C : ℕ, ∀ n : ℕ, affineHilbertFunction P n ≤
      Fintype.card ι * affineHilbertFunction Q (n + C) := by
  classical
  choose levels hlevels using fun s : κ × ι => exists_mem_quotientDegreeLE Q (b s.1 s.2)
  obtain ⟨C, hC⟩ := Finite.exists_le levels
  refine ⟨C, fun n => ?_⟩
  let W := (quotientDegreeLE Q (n + C)).map i.toLinearMap
  let T (r : ι) : B →ₗ[k] F :=
    (LinearMap.mulLeft k d).comp (((LinearMap.proj r).comp
      e.equivFun.toLinearMap).restrictScalars k |>.comp j.toLinearMap)
  have hT (r : ι) (x : B) : T r x = d * e.equivFun (j x) r := rfl
  have hmem (r : ι) (x : quotientDegreeLE P n) : T r x ∈ W := by
    obtain ⟨a, ha, hax⟩ := hgen n x x.property
    refine Submodule.mem_map.mpr ⟨∑ l, a l * b l r, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun l _ =>
        mul_mem_quotientDegreeLE (ha l) (quotientDegreeLE_mono Q (hC (l, r)) (hlevels (l, r)))
    · change i (∑ l, a l * b l r) = T r x
      have hm (l : κ) : j (g (a l) * v l) = (i (a l)) • j (v l) := by
        rw [map_mul, hcomm, Algebra.smul_def]
      rw [hT, ← hax, map_sum, map_sum, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, hb, hm, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  let S : quotientDegreeLE P n →ₗ[k] (ι → W) :=
    LinearMap.pi fun r => ((T r).domRestrict _).codRestrict W (hmem r)
  have hinj : Function.Injective S := by
    intro x y h
    apply Subtype.ext
    apply hj
    apply e.equivFun.injective
    funext r
    apply mul_left_cancel₀ hd
    exact congrArg (fun f : ι → W => (f r : F)) h
  have hrw : Module.finrank k W = affineHilbertFunction Q (n + C) :=
    (Submodule.equivMapOfInjective i.toLinearMap hi (quotientDegreeLE Q (n + C))).finrank_eq.symm
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hrw] at h

/-- Additive shifts preserve the leading coefficient of the affine Hilbert polynomial. -/
theorem degree_of_bounds {d C₁ C₂ : ℕ} (hd : d ≠ 0)
    (hdeg : (affineHilbertPolynomial P).natDegree = (affineHilbertPolynomial Q).natDegree)
    (hl : ∀ n, d * affineHilbertFunction Q n ≤ affineHilbertFunction P (n + C₁))
    (hu : ∀ n, affineHilbertFunction P n ≤ d * affineHilbertFunction Q (n + C₂)) :
    affineDegree P = (d : ℚ) * affineDegree Q := by
  open Polynomial in
  let HS := affineHilbertPolynomial P
  let HT := Polynomial.C (d : ℚ) * affineHilbertPolynomial Q
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hdeg' : HS.natDegree = HT.natDegree := by
    rw [show HT.natDegree = (affineHilbertPolynomial Q).natDegree from natDegree_C_mul hd']
    exact hdeg
  have hshift (c : ℕ) : Tendsto (fun n : ℕ => n + c) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n c) tendsto_id
  have hS : ∀ᶠ n : ℕ in atTop, HS.eval (n : ℚ) = affineHilbertFunction P n :=
    eventually_eval_affineHilbertPolynomial _
  have hT : ∀ᶠ n : ℕ in atTop, HT.eval (n : ℚ) = (d * affineHilbertFunction Q n : ℕ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial Q] with n hn
    simp [HT, hn]
  have hlo : ∀ᶠ n : ℕ in atTop, HT.eval (n : ℚ) ≤ (taylor (C₁ : ℚ) HS).eval (n : ℚ) := by
    filter_upwards [hT, (hshift C₁).eventually hS] with n hn hn'
    rw [taylor_eval, ← Nat.cast_add, hn, hn']
    exact_mod_cast hl n
  have hup : ∀ᶠ n : ℕ in atTop, HS.eval (n : ℚ) ≤ (taylor (C₂ : ℚ) HT).eval (n : ℚ) := by
    filter_upwards [hS, (hshift C₂).eventually hT] with n hn hn'
    rw [taylor_eval, ← Nat.cast_add, hn, hn']
    exact_mod_cast hu n
  have hTpos : ∀ᶠ n : ℕ in atTop, 0 ≤ HT.eval (n : ℚ) :=
    hT.mono fun n h => h.symm ▸ Nat.cast_nonneg (α := ℚ) (d * affineHilbertFunction Q n)
  have lc₁ := (natDegree_le_of_eventually_eval_natCast_le hTpos hlo).2
    (hdeg'.symm.trans (natDegree_taylor _ _).symm)
  have lc₂ := (natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg P) hup).2
    (hdeg'.trans (natDegree_taylor _ _).symm)
  rw [leadingCoeff_taylor] at lc₁ lc₂
  have he := lc₂.antisymm lc₁
  change (HS.natDegree.factorial : ℚ) * HS.leadingCoeff =
    (d : ℚ) * ((((affineHilbertPolynomial Q).natDegree.factorial : ℕ) : ℚ) *
      (affineHilbertPolynomial Q).leadingCoeff)
  rw [show HS.natDegree = (affineHilbertPolynomial Q).natDegree from hdeg, he,
    show HT.leadingCoeff = _ from leadingCoeff_C_mul_of_isUnit hd'.isUnit _]
  ring

end

end K1_13_6_3_5_3_3_3
end PackSource_K1_13_6_3_5_3_3_3Bounds

section PackSource_K1_13_6_3_1_1Geometry
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_1_1

noncomputable section

open scoped TensorProduct

private theorem quotient_reduced_of_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (q : Ideal R) [q.IsPrime]
    (h : IsReduced (S ⊗[R] q.ResidueField)) :
    IsReduced (S ⧸ q.map (algebraMap R S)) := by
  let f : (R ⧸ q) →ₐ[R] q.ResidueField := IsScalarTower.toAlgHom R _ _
  have hf : Function.Injective f := Ideal.injective_algebraMap_quotient_residueField q
  let e := Algebra.TensorProduct.map (AlgHom.id R S) f
  have he : Function.Injective e :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) f.toLinearMap hf
  have : IsReduced (S ⊗[R] (R ⧸ q)) := isReduced_of_injective e he
  let baseChange := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S q
  exact isReduced_of_injective baseChange baseChange.injective

variable {k E R S : Type*} [Field k] [Field E] [CommRing R] [CommRing S]
  [Algebra k E] [Algebra k R] [Algebra k S] [Algebra R S] [Algebra E S]
  [IsScalarTower k R S] [IsScalarTower k E S] [Algebra.IsPushout k R E S]
  [IsPurelyInseparable k E]

include k E in
private theorem algebraMap_power (x : S) :
    ∃ n > 0, ∃ y : R, algebraMap R S y = x ^ n := by
  let e := Algebra.IsPushout.equiv k R E S
  obtain ⟨n, hn, y, hy⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct (e.symm x)
  refine ⟨n, hn, y, ?_⟩
  simpa [Algebra.TensorProduct.algebraMap_apply, Algebra.IsPushout.equiv_tmul, e] using
    congrArg e hy

include k E in
private theorem localization_at_contraction (P : Ideal S) [P.IsPrime]
    (q : Ideal R) [q.IsPrime] (hq : q = P.comap (algebraMap R S)) :
    IsLocalization (Algebra.algebraMapSubmonoid S q.primeCompl) (Localization.AtPrime P) := by
  let M := Algebra.algebraMapSubmonoid S q.primeCompl
  have hle : M ≤ P.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    apply Ideal.mem_primeCompl_iff.mpr
    intro hp
    apply Ideal.mem_primeCompl_iff.mp hx
    rw [hq]
    exact hp
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := Localization.AtPrime P) M
    P.primeCompl hle ?_).mpr inferInstance
  intro x hx
  obtain ⟨n, hn, y, hy⟩ := algebraMap_power (k := k) (E := E) (R := R) x
  refine ⟨x ^ n, ⟨y, ?_, hy⟩, dvd_pow_self x hn.ne'⟩
  change y ∉ q
  rw [hq, Ideal.mem_comap, hy]
  exact P.primeCompl.pow_mem hx _

include k E in
private def localFiberEquiv (P : Ideal S) [P.IsPrime]
    (q : Ideal R) [q.IsPrime] (hq : q = P.comap (algebraMap R S)) :
    let L := Localization.AtPrime P
    S ⊗[R] q.ResidueField ≃+* L ⧸ (q.map (algebraMap R S)).map (algebraMap S L) := by
  let L := Localization.AtPrime P
  let M := Algebra.algebraMapSubmonoid S q.primeCompl
  let B := Localization M
  letI : IsLocalization M L := localization_at_contraction (k := k) (E := E) P q hq
  let e := IsLocalization.algEquiv M B L
  letI : Algebra S (q.Fiber S) := Algebra.TensorProduct.rightAlgebra
  refine (Algebra.TensorProduct.comm R S q.ResidueField).toRingEquiv.trans ?_
  refine (Ideal.Fiber.algEquivAux₁ (S := S) q).toRingEquiv.trans ?_
  refine Ideal.quotientEquiv _ _ e.toRingEquiv ?_
  have hcomp : e.toRingEquiv.toRingHom.comp (algebraMap S B) = algebraMap S L :=
    RingHom.ext e.commutes
  exact ((Ideal.map_map (algebraMap S B) e.toRingEquiv.toRingHom).trans
    (congrArg (q.map (algebraMap R S)).map hcomp)).symm

include k E in
/-- Purely inseparable coefficient extension reflects equality of a prime
and its extended contraction from the localization at that prime. -/
theorem descent_of_local_equality (P : Ideal S) [P.IsPrime]
    (h : let L := Localization.AtPrime P
      ((P.comap (algebraMap R S)).map (algebraMap R S)).map (algebraMap S L) =
        IsLocalRing.maximalIdeal L) :
    (P.comap (algebraMap R S)).map (algebraMap R S) = P := by
  let q := P.comap (algebraMap R S)
  have : q.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime P
  let e : S ⊗[R] q.ResidueField ≃+* IsLocalRing.ResidueField L :=
    (localFiberEquiv (k := k) (E := E) P q rfl).trans (Ideal.quotEquivOfEq h)
  have hred : IsReduced (S ⊗[R] q.ResidueField) :=
    isReduced_of_injective e e.injective
  have hpush : Algebra.IsPushout k R E S := inferInstance
  have : Module.Flat R S := Module.Flat.isBaseChange k R E S hpush.out
  let J := q.map (algebraMap R S)
  have hrad : J.IsRadical := (Ideal.isRadical_iff_quotient_reduced J).mpr
    (quotient_reduced_of_fiber q hred)
  refine le_antisymm Ideal.map_comap_le ?_
  intro x hx
  obtain ⟨n, hn, y, hy⟩ := algebraMap_power (k := k) (E := E) (R := R) x
  have hyq : y ∈ q := by
    change algebraMap R S y ∈ P
    rw [hy]
    exact P.pow_mem_of_mem hx n hn
  exact hrad ⟨n, hy ▸ Ideal.mem_map_of_mem (algebraMap R S) hyq⟩

end
end K1_13_6_3_1_1
end PackSource_K1_13_6_3_1_1Geometry

section PackSource_K1_14_2_2_7_4_1Aux
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_14_2_2_7_4_1

open scoped Polynomial
open MvPolynomial

/-- Over an infinite field at most one constant slope can make a varying jet pair algebraic. -/
private theorem infinite_good_slopes {k A : Type} [Field k] [Infinite k]
    [CommRing A] [Algebra k A] (y v : A)
    (hvar : ¬ IsAlgebraic k y ∨ ¬ IsAlgebraic k v) :
    {t : k | ¬ IsAlgebraic k (y + algebraMap k A t * v)}.Infinite := by
  apply Set.infinite_of_finite_compl
  apply Set.Subsingleton.finite
  intro t ht u hu
  change ¬ ¬ IsAlgebraic k (y + algebraMap k A t * v) at ht
  change ¬ ¬ IsAlgebraic k (y + algebraMap k A u * v) at hu
  by_contra htu
  have ht' := isAlgebraic_iff_isIntegral.mp (not_not.mp ht)
  have hu' := isAlgebraic_iff_isIntegral.mp (not_not.mp hu)
  have hdiff : IsIntegral k (algebraMap k A (t - u) * v) := by
    convert ht'.sub hu' using 1
    rw [map_sub]
    ring
  have hv : IsIntegral k v := by
    have h := (isIntegral_algebraMap (R := k) (A := A) (x := (t - u)⁻¹)).mul hdiff
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr htu), map_one, one_mul] at h
    exact h
  have hy : IsIntegral k y := by
    have h := ht'.sub ((isIntegral_algebraMap (R := k) (A := A) (x := t)).mul hv)
    rwa [add_sub_cancel_right] at h
  exact hvar.elim (fun h => h hy.isAlgebraic) (fun h => h hv.isAlgebraic)

/-- The free slope and the resulting intercept are algebraically independent.
Specialize the free slope across an infinite set of transcendental intercepts. -/
theorem parameter_injective_of_varying {k A : Type} [Field k] [Infinite k]
    [CommRing A] [Algebra k A] (y v : A)
    (hvar : ¬ IsAlgebraic k y ∨ ¬ IsAlgebraic k v) :
    Function.Injective (MvPolynomial.eval₂Hom (σ := Fin 2)
      (Polynomial.C.comp (algebraMap k A))
      ![Polynomial.X, Polynomial.C y + Polynomial.X * Polynomial.C v]) := by
  let f : MvPolynomial (Fin 2) k →+* A[X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k A))
      ![Polynomial.X, Polynomial.C y + Polynomial.X * Polynomial.C v]
  apply (injective_iff_map_eq_zero f).mpr
  intro P hP
  let good : Set k := {t | ¬ IsAlgebraic k (y + algebraMap k A t * v)}
  let box : Fin 2 → Set k := ![good, Set.univ]
  have hbox (i : Fin 2) : (box i).Infinite := by
    fin_cases i
    · exact infinite_good_slopes y v hvar
    · exact Set.infinite_univ
  apply MvPolynomial.funext_set box hbox
  intro a ha
  have ht : a 0 ∈ good := ha 0 (Set.mem_univ _)
  let intercept := y + algebraMap k A (a 0) * v
  let fixSlope : MvPolynomial (Fin 2) k →+* k[X] :=
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.C (a 0), Polynomial.X]
  have hfix : (Polynomial.aeval intercept).toRingHom.comp fixSlope =
      (Polynomial.evalRingHom (algebraMap k A (a 0))).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fixSlope, f]
    · intro i
      fin_cases i
      · simp [fixSlope, f, intercept]
      · simp [fixSlope, f, intercept]
        exact mul_comm _ _
  have hfixP : fixSlope P = 0 := by
    apply (transcendental_iff_injective.mp ht)
    change ((Polynomial.aeval intercept).toRingHom.comp fixSlope) P = _
    rw [hfix]
    simp [hP]
  have heval : (Polynomial.evalRingHom (a 1)).comp fixSlope = MvPolynomial.eval a := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [fixSlope]
    · intro i
      fin_cases i <;> simp [fixSlope]
  rw [← heval]
  simp [hfixP]

/-- Noether normalization gives the same finite rank for Krull dimension and transcendence degree. -/
theorem affine_dimension {k A : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) ∧ Algebra.trdeg k A = (n : Cardinal) := by
  obtain ⟨n, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  let : Algebra B A := g.toRingHom.toAlgebra
  let : IsScalarTower k B A := IsScalarTower.of_algHom g
  have : Module.Finite B A := hg_fin
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg_inj
  have hdim : ringKrullDim B = (n : WithBot ℕ∞) := by
    simp [B, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  refine ⟨n, ?_, ?_⟩
  · apply le_antisymm
    · rw [← hdim]
      apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B A))
      intro a b hab
      exact Ideal.IsIntegral.under_lt_under (R := B) (show a.asIdeal < b.asIdeal from hab)
    · obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hdim.ge
      have := l.head.isPrime
      have hle : (⊥ : Ideal A).under B ≤ l.head.asIdeal := by
        change Ideal.comap (algebraMap B A) ⊥ ≤ l.head.asIdeal
        rw [← RingHom.ker_eq_comap_bot,
          (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
        exact bot_le
      obtain ⟨P, _, hP, hPhead⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
        (⊥ : Ideal A) hle
      let : P.IsPrime := hP
      let : P.LiesOver l.head.asIdeal := ⟨hPhead.symm⟩
      obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
      exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hlen⟩
  · have h := trdeg_add_eq k B (A := A)
    rw [trdeg_eq_zero (R := B) (A := A), add_zero] at h
    simpa [B, MvPolynomial.trdeg_of_isDomain] using h.symm

/-- The slope and intercept contribute two to the transcendence degree of the coefficient field. -/
theorem parameter_field_trdeg (k : Type) [Field k] :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin 2) k)) = 2 := by
  let P := MvPolynomial (Fin 2) k
  let F := FractionRing P
  have : Algebra.IsAlgebraic P F := IsLocalization.isAlgebraic _ (nonZeroDivisors P)
  have : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective P F).mpr
    (IsFractionRing.injective P F)
  rw [← trdeg_add_eq k P (A := F), trdeg_eq_zero (R := P) (A := F), add_zero]
  simp [P]

/-- Adjoining a free slope adds one to the transcendence degree. Making both
line parameters scalars subtracts two, and localization adds nothing. -/
theorem affine_slice_dimension {k E A B : Type}
    [Field k] [Field E] [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra k E] [Algebra k A] [Algebra k B] [Algebra E B] [IsScalarTower k E B]
    [Algebra.FiniteType k A] [Algebra.FiniteType E B]
    (f : A[X] →ₐ[k] B) (hf : Function.Injective f)
    (hAlg : let : Algebra A[X] B := f.toRingHom.toAlgebra; Algebra.IsAlgebraic A[X] B)
    (hE : Algebra.trdeg k E = 2) (d : ℕ)
    (hdim : ringKrullDim A = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim B = (d : WithBot ℕ∞) := by
  let : Algebra A[X] B := f.toRingHom.toAlgebra
  let : IsScalarTower k A[X] B := IsScalarTower.of_algHom f
  have : FaithfulSMul A[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  have : Algebra.IsAlgebraic A[X] B := hAlg
  obtain ⟨n, hdimA, htrdegA⟩ := affine_dimension (k := k) (A := A)
  obtain ⟨m, hdimB, htrdegB⟩ := affine_dimension (k := E) (A := B)
  have hn : n = d + 1 := by exact_mod_cast hdimA.symm.trans hdim
  have hSlope := trdeg_add_eq k A (A := A[X])
  rw [htrdegA, Polynomial.trdeg_of_isDomain] at hSlope
  have hSlice := trdeg_add_eq k A[X] (A := B)
  rw [trdeg_eq_zero (R := A[X]) (A := B), add_zero, ← hSlope] at hSlice
  have h := trdeg_add_eq k E (A := B)
  rw [hE, htrdegB, ← hSlice] at h
  have hm : (2 + m : ℕ) = n + 1 := by exact_mod_cast h
  rw [hdimB, show m = d by omega]

end K1_14_2_2_7_4_1
end PackSource_K1_14_2_2_7_4_1Aux

section PackSource_K1_14_2_2_5_1Aux1
set_option autoImplicit true
namespace K1_14_2_2_5_1

noncomputable section

open Polynomial

variable {M E : Type*} [Field M] [Field E] [Algebra M E]

/-- Keep the two slopes free and substitute the generic intercept in the third coordinate. -/
def genericLine (x y : E) : MvPolynomial (Fin 3) M →+* MvPolynomial (Fin 2) E :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap M E))
    ![MvPolynomial.X 0, MvPolynomial.X 1,
      MvPolynomial.C x + MvPolynomial.X 0 * MvPolynomial.C y]

private theorem algebraic_of_specialization (x y : E) (P : MvPolynomial (Fin 3) M)
    (hP : genericLine x y P = 0) (b : Fin 3 → M) (hb : MvPolynomial.eval b P ≠ 0) :
    IsAlgebraic M (x + algebraMap M E (b 0) * y) := by
  let f : MvPolynomial (Fin 3) M →+* M[X] :=
    MvPolynomial.eval₂Hom C ![C (b 0), C (b 1), X]
  let v : E := x + algebraMap M E (b 0) * y
  have he : (evalRingHom (b 2)).comp f = MvPolynomial.eval b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f]
    · intro i
      fin_cases i <;> simp [f]
  have hf : f P ≠ 0 := by
    intro hz
    apply hb
    rw [← he, RingHom.comp_apply, hz, map_zero]
  let s : MvPolynomial (Fin 2) E →+* E :=
    MvPolynomial.eval ![algebraMap M E (b 0), algebraMap M E (b 1)]
  have hs : (aeval v).toRingHom.comp f = s.comp (genericLine x y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f, s, genericLine]
    · intro i
      fin_cases i <;> simp [f, s, genericLine, v]
  refine ⟨f P, hf, ?_⟩
  change ((aeval v).toRingHom.comp f) P = 0
  rw [hs, RingHom.comp_apply, hP, map_zero]

/-- Over an infinite coefficient field, a relation on the generic intercept would
give algebraic intercepts at two distinct slopes. Their difference and either
intercept then make both seed coordinates algebraic. -/
theorem genericLine_injective [Infinite M] (x y : E)
    (ht : ¬ (IsAlgebraic M x ∧ IsAlgebraic M y)) :
    Function.Injective (genericLine (M := M) x y) := by
  classical
  apply (injective_iff_map_eq_zero (genericLine (M := M) x y)).mpr
  intro P hP
  by_contra hp
  have hex (Q : MvPolynomial (Fin 3) M) (hQ : Q ≠ 0) :
      ∃ b : Fin 3 → M, MvPolynomial.eval b Q ≠ 0 := by
    by_contra! h
    apply hQ
    exact MvPolynomial.funext (fun b => by rw [h b, map_zero])
  obtain ⟨b, hb⟩ := hex P hp
  have hlin : (MvPolynomial.X 0 - MvPolynomial.C (b 0) : MvPolynomial (Fin 3) M) ≠ 0 :=
    fun h => by
      have he := congrArg (MvPolynomial.eval ![b 0 + 1, (0 : M), 0]) h
      simp at he
  obtain ⟨d, hd⟩ := hex (P * (MvPolynomial.X 0 - MvPolynomial.C (b 0))) (mul_ne_zero hp hlin)
  have hd' : MvPolynomial.eval d P * (d 0 - b 0) ≠ 0 := by simpa using hd
  have hdb := right_ne_zero_of_mul hd'
  have hb_alg := algebraic_of_specialization x y P hP b hb
  have hd_alg := algebraic_of_specialization x y P hP d (left_ne_zero_of_mul hd')
  have hdiff : IsAlgebraic M (algebraMap M E (d 0 - b 0) * y) := by
    have h := hd_alg.sub hb_alg
    convert h using 1
    rw [map_sub]
    ring
  have hy : IsAlgebraic M y := by
    have h := (isAlgebraic_algebraMap (A := E) ((d 0 - b 0)⁻¹)).mul hdiff
    have hn : algebraMap M E (d 0 - b 0) ≠ 0 :=
      (map_ne_zero_iff (algebraMap M E) (algebraMap M E).injective).mpr hdb
    rw [map_inv₀, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] at h
    exact h
  have hx : IsAlgebraic M x := by
    simpa using hb_alg.sub ((isAlgebraic_algebraMap (A := E) (b 0)).mul hy)
  exact ht ⟨hx, hy⟩

end
end K1_14_2_2_5_1
end PackSource_K1_14_2_2_5_1Aux1

section PackSource_K1_13_7_5_1Chart
set_option autoImplicit true
namespace K1_13_7_5_1

open Polynomial Algebra TensorProduct

noncomputable section

variable {A : Type*} [CommRing A]

/-- The hypersurface ring on the leading-coefficient open. -/
abbrev LeadingChart (F : A[X]) := Localization.Away (AdjoinRoot.of F F.leadingCoeff)

/-- Base change to the leading-coefficient open makes the defining polynomial monic up to a unit. -/
theorem leadingChart_flat [IsDomain A] (F : A[X]) (hF : F.leadingCoeff ≠ 0) :
    Module.Flat A (LeadingChart F) := by
  let a := F.leadingCoeff
  let R := Localization.Away a
  let : IsDomain R := Localization.Away.isDomain hF
  let p := F.map (algebraMap A R)
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := R) a
  let g := C (↑u⁻¹ : R) * p
  have hg : g.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    change (↑u⁻¹ : R) * (F.map (algebraMap A R)).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (hu ▸ Units.ne_zero u),
      ← hu, Units.inv_mul]
  let q := F.map (Algebra.TensorProduct.includeRight : A →ₐ[A] R ⊗[A] A).toRingHom
  let e := Algebra.TensorProduct.rid A R R
  have hq : q.map e = p := by
    rw [show q = F.map (Algebra.TensorProduct.includeRight : A →ₐ[A] R ⊗[A] A).toRingHom from rfl,
      Polynomial.map_map]
    congr 1
    apply RingHom.ext
    intro x
    change e (1 ⊗ₜ[A] x) = algebraMap A R x
    simp [e, Algebra.smul_def]
  have hassoc : Associated (q.map e) g := by
    rw [hq]
    exact associated_unit_mul_right _ _ (IsUnit.map Polynomial.C (u⁻¹).isUnit)
  let e₀ : R ⊗[A] AdjoinRoot F ≃ₐ[A] LeadingChart F := by
    let : Algebra (AdjoinRoot F) (R ⊗[A] AdjoinRoot F) := Algebra.TensorProduct.rightAlgebra
    exact (IsLocalization.Away.tensorRightEquiv (R := A) (A := R) (r := a)
      (AdjoinRoot F)).restrictScalars A
  let e₁ : R ⊗[A] AdjoinRoot F ≃ₐ[R] AdjoinRoot q := AdjoinRoot.tensorAlgEquiv F q rfl
  let e₂ : AdjoinRoot q ≃ₐ[R] AdjoinRoot g := AdjoinRoot.mapAlgEquiv e q g hassoc
  let : Module.Free R (AdjoinRoot g) := hg.free_adjoinRoot
  let : Module.Flat R (AdjoinRoot g) := Module.Flat.of_free
  let : Module.Flat A (AdjoinRoot g) := Module.Flat.trans A R (AdjoinRoot g)
  exact Module.Flat.of_linearEquiv (e₀.symm.trans ((e₁.trans e₂).restrictScalars A)).toLinearEquiv

end

end K1_13_7_5_1
end PackSource_K1_13_7_5_1Chart

section PackSource_K1_14_3R_3_1_3_1Lattice
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 750000

namespace K1_14_3R_3_1_3_1

open scoped BigOperators nonZeroDivisors
open Module

/-- The image subring of an iterate of Frobenius. -/
abbrev FrobeniusRing (A : Type) [CommRing A] (p n : ℕ) [ExpChar A p] :=
  (iterateFrobenius A p n).range

/-- Every finite set lies in a finitely generated submodule saturated under
nonzero scalars from the image of an iterate of Frobenius. -/
def FrobeniusLattices (A : Type) [CommRing A] : Prop :=
  ∀ (p n : ℕ) [ExpChar A p] (w : Finset A),
    ∃ T : Submodule (FrobeniusRing A p n) A, T.FG ∧ (w : Set A) ⊆ T ∧
      ∀ (s : FrobeniusRing A p n) (a : A), s ≠ 0 → s • a ∈ T → a ∈ T

/-- Frobenius sends a finite integral basis of the whole extension into the
finite normalization of its separable part. Finite saturated scalar lattices
then bound all the coordinates of the image of the integral closure. -/
theorem finite_normalization (A K L : Type) [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hA : FrobeniusLattices A) : Module.Finite A (integralClosure A L) := by
  classical
  let E := separableClosure K L
  let B := integralClosure A L
  let C := integralClosure A E
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite A C := IsIntegralClosure.finite A K E C
  have : IsTorsionFree A E := .trans_faithfulSMul A K E
  have : Module.Free A C := IsIntegralClosure.module_free A K E C
  let p := ringExpChar L
  have : ExpChar L p := ringExpChar.expChar L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : ExpChar A p := (algebraMap A L).expChar hAL p
  have : ExpChar E p := (algebraMap E L).expChar (algebraMap E L).injective p
  let n := IsPurelyInseparable.exponent E L
  let S := FrobeniusRing A p n
  let σ : A →+* S := (iterateFrobenius A p n).rangeRestrict
  let e : A ≃+* S := RingEquiv.ofBijective σ
    ⟨fun _ _ h => iterateFrobenius_inj A p n (congrArg Subtype.val h),
      (iterateFrobenius A p n).rangeRestrict_surjective⟩
  have : RingHomInvPair (e : A →+* S) (e.symm : S →+* A) := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair (e.symm : S →+* A) (e : A →+* S) := RingHomInvPair.of_ringEquiv e.symm
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv A e
  let φ : L →+* E := IsPurelyInseparable.iterateFrobenius E L p (n := n) le_rfl
  have hφ (b : L) : algebraMap E L (φ b) = b ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius E p le_rfl b
  have hmem (b : B) : φ b.val ∈ integralClosure A E := by
    change IsIntegral A (φ b.val)
    apply (IntermediateField.coe_isIntegral_iff (R := A)).mp
    change IsIntegral A (algebraMap E L (φ b.val))
    rw [hφ]
    exact (show IsIntegral A b.val from b.property).pow _
  let g : B →+* C :=
    (φ.comp (integralClosure A L).val.toRingHom).codRestrict (integralClosure A E).toSubring hmem
  let f : B →ₛₗ[(e : A →+* S)] C :=
    { g with
      map_smul' a b := by
        apply Subtype.ext
        apply (algebraMap E L).injective
        change algebraMap E L (φ (a • b.val)) =
          algebraMap E L ((a ^ p ^ n) • φ b.val)
        simp only [Algebra.smul_def]
        rw [hφ, mul_pow, map_mul, ← IsScalarTower.algebraMap_apply A E L, map_pow, hφ] }
  have hf : Function.Injective f := by
    intro b b' hb
    apply Subtype.ext
    apply iterateFrobenius_inj L p n
    change b.val ^ p ^ n = b'.val ^ p ^ n
    rw [← hφ, ← hφ]
    exact congrArg (fun c : C => algebraMap E L c.val) hb
  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let J := Module.Free.ChooseBasisIndex A C
  let v : Basis J A C := Module.Free.chooseBasis A C
  let w (i : ι) : B := ⟨b i, hb i⟩
  let r : B →ₛₗ[(e : A →+* S)] (J → A) :=
    (v.equivFun.toLinearMap.restrictScalars S).comp f
  have hr : Function.Injective r := v.equivFun.injective.comp hf
  let coeffs := (Finset.univ : Finset (ι × J)).image (fun ij => r (w ij.1) ij.2)
  obtain ⟨T, hT, hcoeffs, hsat⟩ := hA p n coeffs
  have hw (i : ι) (j : J) : r (w i) j ∈ T :=
    hcoeffs (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hr_mem (z : B) (j : J) : r z j ∈ T := by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite A⁰ (b.repr z.val)
    choose a ha using hd
    have hdenom : (d : A) • z = ∑ i, a i • w i := by
      apply Subtype.ext
      change (d : A) • z.val = (integralClosure A L).val (∑ i, a i • w i)
      rw [map_sum]
      calc
        _ = ∑ i, (b.repr ((d : A) • z.val) i) • b i := (b.sum_repr _).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          have hrepr : b.repr ((d : A) • z.val) i = algebraMap A K (a i) := by
            rw [← IsScalarTower.algebraMap_smul K (d : A) z.val,
              LinearEquiv.map_smul, Finsupp.smul_apply]
            exact (IsScalarTower.algebraMap_smul K (d : A) _).trans (ha i).symm
          rw [hrepr]
          exact IsScalarTower.algebraMap_smul K (a i) (b i)
    have hd0 : (e : A →+* S) d ≠ 0 :=
      e.map_ne_zero_iff.mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
    apply hsat ((e : A →+* S) d) _ hd0
    have h := congrFun (congrArg r hdenom) j
    simp only [map_smulₛₗ, map_sum, Pi.smul_apply, Finset.sum_apply] at h
    rw [h]
    exact Submodule.sum_mem T (fun i _ => T.smul_mem _ (hw i j))
  have : Module.Finite S T := Module.Finite.of_fg hT
  let q : B →ₛₗ[(e : A →+* S)] (J → T) :=
    { toFun := fun z j => ⟨r z j, hr_mem z j⟩
      map_add' := fun a b => by
        ext j
        exact congrFun (map_add r a b) j
      map_smul' := fun a b => by
        ext j
        exact congrFun (map_smulₛₗ r a b) j }
  apply Module.Finite.of_injective q
  intro a b hab
  exact hr (funext fun j => congrArg (fun u : J → T => (u j : A)) hab)

end K1_14_3R_3_1_3_1
end PackSource_K1_14_3R_3_1_3_1Lattice

section PackSource_K1_14_3R_3_1_3_1Polynomial
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 750000

namespace K1_14_3R_3_1_3_1

open Polynomial
open scoped Polynomial

/-- For a finite set of polynomials, adjoin their coefficients to the image
of Frobenius on the constant field. The polynomial subring over these
constants is finite over the Frobenius image and contains all the inputs.
Divisibility of polynomials descends along an extension of coefficient fields,
which makes this subring saturated. -/
theorem polynomial_frobenius_lattices (k : Type) [Field k] : FrobeniusLattices k[X] := by
  classical
  intro p n _ w
  have : ExpChar k p := Polynomial.C.expChar Polynomial.C_injective p
  let R := (iterateFrobenius k p n).fieldRange
  let S := FrobeniusRing k[X] p n
  let D := w.biUnion fun a => a.coeffs
  let K := IntermediateField.adjoin R (D : Set k)
  let f : K →+* k := K.subtype
  have hr (a : k) : IsIntegral R a := by
    apply IsIntegral.of_pow (expChar_pow_pos k p n)
    exact isIntegral_algebraMap (x := (iterateFrobenius k p n).rangeRestrictField a)
  let V : Subalgebra S k[X] :=
    { (mapRingHom f).range.toSubsemiring with
      algebraMap_mem' := fun s => by
        obtain ⟨a, ha⟩ := s.property
        let g : k →+* K := (algebraMap R K).comp (iterateFrobenius k p n).rangeRestrictField
        change ∃ b : K[X], b.map f = (s : k[X])
        refine ⟨(expand k (p ^ n) a).map g, ?_⟩
        rw [Polynomial.map_map]
        change (expand k (p ^ n) a).map (iterateFrobenius k p n) = (s : k[X])
        rw [map_iterateFrobenius_expand, ← iterateFrobenius_def, ha] }
  let U : Subalgebra S k[X] := Algebra.adjoin S (insert X (C '' (D : Set k)))
  have huX : X ∈ U := Algebra.subset_adjoin (Set.mem_insert _ _)
  have huC (a : k) (ha : a ∈ K) : C a ∈ U := by
    change a ∈ K.toSubalgebra at ha
    change a ∈ (IntermediateField.adjoin R (D : Set k)).toSubalgebra at ha
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun a _ => (hr a).isAlgebraic)] at ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
    | algebraMap r =>
      obtain ⟨c, hc⟩ := r.property
      have hs : C (r : k) ∈ (iterateFrobenius k[X] p n).range := by
        refine ⟨C c, ?_⟩
        rw [iterateFrobenius_def, ← map_pow]
        exact congrArg C hc
      exact U.algebraMap_mem ⟨_, hs⟩
    | add a b _ _ ha hb => simpa only [map_add] using U.add_mem ha hb
    | mul a b _ _ ha hb => simpa only [map_mul] using U.mul_mem ha hb
  have hVU : V = U := by
    apply le_antisymm
    · intro a ha
      obtain ⟨b, rfl⟩ : ∃ b : K[X], b.map f = a := ha
      induction b using Polynomial.induction_on' with
      | add a b ha hb => simpa only [Polynomial.map_add] using U.add_mem ha hb
      | monomial i c =>
        rw [Polynomial.map_monomial, ← C_mul_X_pow_eq_monomial]
        exact U.mul_mem (huC c c.property) (U.pow_mem huX i)
    · apply Algebra.adjoin_le
      rintro _ (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨X, Polynomial.map_X f⟩
      · exact ⟨C ⟨c, IntermediateField.subset_adjoin R _ hc⟩, Polynomial.map_C f⟩
  refine ⟨V.toSubmodule, ?_, ?_, ?_⟩
  · rw [hVU]
    apply fg_adjoin_of_finite ((D.finite_toSet.image C).insert X)
    intro a _
    apply IsIntegral.of_pow (expChar_pow_pos k[X] p n)
    exact isIntegral_algebraMap (x := (iterateFrobenius k[X] p n).rangeRestrict a)
  · intro a ha
    change a ∈ Polynomial.lifts f
    apply (Polynomial.lifts_iff_coeffs_subset_range a).mpr
    intro c hc
    have hD : c ∈ D := Finset.mem_biUnion.mpr ⟨a, ha, hc⟩
    exact ⟨⟨c, IntermediateField.subset_adjoin R _ hD⟩, rfl⟩
  · intro s a hs0 hs
    change (s : k[X]) * a ∈ V at hs
    obtain ⟨s', hs'⟩ : ∃ s' : K[X], s'.map f = (s : k[X]) := V.algebraMap_mem s
    obtain ⟨b, hb⟩ : ∃ b : K[X], b.map f = (s : k[X]) * a := hs
    have hd : s'.map f ∣ b.map f := ⟨a, by rw [hb, hs']⟩
    obtain ⟨a', ha'⟩ := (Polynomial.map_dvd_map' f).mp hd
    refine ⟨a', ?_⟩
    change a'.map f = a
    apply mul_left_cancel₀ (show (s : k[X]) ≠ 0 from fun h => hs0 (Subtype.ext h))
    rw [← hs', ← Polynomial.map_mul, ← ha', hb, hs']

end K1_14_3R_3_1_3_1
end PackSource_K1_14_3R_3_1_3_1Polynomial

section PackSource_K1_13_6_1_3_2Local
set_option autoImplicit true
namespace K1_13_6_1_3_2

noncomputable section

open IsLocalRing

private theorem dim_le_two {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {f q : A} (hf : f ∈ maximalIdeal A) (hq : q ∈ maximalIdeal A)
    (hlen : Order.coheight (Ideal.span ({f, q} : Set A)) ≠ ⊤) :
    ringKrullDim A ≤ 2 := by
  let J : Ideal A := Ideal.span {f, q}
  have hJ : J ≤ maximalIdeal A :=
    Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨hf, Set.singleton_subset_iff.mpr hq⟩)
  have hfin : IsFiniteLength A (A ⧸ J) :=
    Module.length_ne_top_iff.mp (by simpa only [Module.length_quotient] using hlen)
  have : IsArtinianRing (A ⧸ J) :=
    isArtinian_of_tower A (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  have hmin : J.IsMinimalPrime (maximalIdeal A) := by
    refine ⟨⟨inferInstance, hJ⟩, ?_⟩
    intro p hp hp'
    have := hp.1
    exact Ideal.IsPrime.le_of_pow_le (hn.trans hp.2)
  have hcard : ({f, q} : Set A).ncard ≤ 2 := by
    classical
    simpa using (Set.ncard_insert_le f ({q} : Set A))
  have hh := (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hmin).trans
    (show (({f, q} : Set A).ncard : ℕ∞) ≤ 2 by exact_mod_cast hcard)
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr hh

private theorem span_with {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {x : V} (hx : x ≠ 0) (hdim : Module.finrank k V ≤ 2) :
    ∃ y : V, Submodule.span k ({x, y} : Set V) = ⊤ := by
  let U := Submodule.span k ({x} : Set V)
  have hU : Module.finrank k U = 1 := finrank_span_singleton hx
  have hd := U.finrank_quotient_add_finrank
  rw [hU] at hd
  obtain ⟨y', hy'⟩ := finrank_le_one_iff.mp (show Module.finrank k (V ⧸ U) ≤ 1 by omega)
  obtain ⟨y, rfl⟩ := U.mkQ_surjective y'
  refine ⟨y, eq_top_iff.mpr fun z _ => ?_⟩
  obtain ⟨c, hc⟩ := hy' (U.mkQ z)
  have hz : z - c • y ∈ U := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, hc, sub_self]
  have hy : c • y ∈ Submodule.span k ({x, y} : Set V) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact (Submodule.sub_mem_iff_left _ hy).mp
    ((Submodule.span_mono (by simp : ({x} : Set V) ⊆ {x, y})) hz)

private theorem maximalIdeal_span_pair {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {f : A} (hf : f ∈ maximalIdeal A) (hf2 : f ∉ maximalIdeal A ^ 2)
    (hdim : ringKrullDim A ≤ 2) :
    ∃ t : A, maximalIdeal A = Ideal.span {f, t} := by
  let m := maximalIdeal A
  let f' : m := ⟨f, hf⟩
  have hf' : m.toCotangent f' ≠ 0 := by
    rwa [ne_eq, Ideal.toCotangent_eq_zero]
  have hd := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›
  have hd' : Module.finrank (ResidueField A) (CotangentSpace A) ≤ 2 := by
    exact_mod_cast hd ▸ hdim
  obtain ⟨y, hy⟩ := span_with hf' hd'
  obtain ⟨t, rfl⟩ := m.toCotangent_surjective y
  have hs : Submodule.span A ({f', t} : Set m) = ⊤ :=
    CotangentSpace.span_image_eq_top_iff.mp (by simpa only [Set.image_insert_eq, Set.image_singleton] using hy)
  have hm := congrArg (Submodule.map m.subtype) hs
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    Set.image_insert_eq, Set.image_singleton] at hm
  exact ⟨t, hm.symm⟩

/-- In the regular local chart, the separant test gives a parameter transverse
to the smooth hypersurface. The remaining parameter measures the cutter order. -/
theorem local_order {A : Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [UniqueFactorizationMonoid A] {f q : A} {v : ℕ}
    (hf : f ∈ maximalIdeal A) (hq : q ∈ maximalIdeal A)
    (hf2 : f ∉ maximalIdeal A ^ 2) (hqf : q ∉ Ideal.span {f})
    (hlen : Order.coheight (Ideal.span ({f, q} : Set A)) = (v : ℕ∞)) :
    ∃ t u : A, maximalIdeal A = Ideal.span {f, t} ∧ IsUnit u ∧
      q - u * t ^ v ∈ Ideal.span {f} := by
  let I : Ideal A := Ideal.span {f}
  let B := A ⧸ I
  let π : A →+* B := Ideal.Quotient.mk I
  have hf0 : f ≠ 0 := by
    intro e
    exact hf2 (e.symm ▸ (maximalIdeal A ^ 2).zero_mem)
  have hirr : Irreducible f := by
    refine ⟨hf, fun a b e => ?_⟩
    by_contra! h
    apply hf2
    rw [e, pow_two]
    exact Ideal.mul_mem_mul h.1 h.2
  have : I.IsPrime := (Ideal.span_singleton_prime hf0).mpr (irreducible_iff_prime.mp hirr)
  have hdim := dim_le_two hf hq (hlen.trans_ne (by simp))
  obtain ⟨t, ht⟩ := maximalIdeal_span_pair hf hf2 hdim
  have : IsLocalRing B := .of_surjective' π Ideal.Quotient.mk_surjective
  have : IsLocalHom π := .of_surjective π Ideal.Quotient.mk_surjective
  have hmax : maximalIdeal B = Ideal.span {π t} := by
    rw [← map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective, ht,
      Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    have hf' : π f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    simp [hf']
  have hq0 : π q ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hqf
  have hqB : π q ∈ maximalIdeal B := map_nonunit π q hq
  have hB : ¬ IsField B := by
    rw [isField_iff_maximalIdeal_eq]
    exact fun H => hq0 (Ideal.mem_bot.mp (H ▸ hqB))
  have hprincipal : (maximalIdeal B).IsPrincipal := ⟨⟨π t, hmax⟩⟩
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hB).out 5 1).mp hprincipal
  have hti := (IsDiscreteValuationRing.irreducible_iff_uniformizer (π t)).mpr hmax
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hti
  have hI : I ≤ Ideal.span ({f, q} : Set A) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.subset_span (Set.mem_insert _ _)))
  have hcomap : (Ideal.span ({π q} : Set B)).comap π = Ideal.span ({f, q} : Set A) := by
    have h := Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective
      (Ideal.span ({f, q} : Set A))
    rwa [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      show π f = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f),
      Ideal.span_pair_comm (x := (0 : B)), Ideal.span_pair_zero,
      ← RingHom.ker_eq_comap_bot, show RingHom.ker π = I from Ideal.mk_ker, sup_of_le_left hI] at h
  have hn : Order.coheight (Ideal.span ({π q} : Set B)) = (n : ℕ∞) := by
    rw [hw, Ideal.span_singleton_mul_left_unit w.isUnit, ← Ideal.span_singleton_pow, ← hmax]
    exact IsDiscreteValuationRing.coheight_pow_maximalIdeal B n
  have hvn : v = n := by
    have h := Ideal.coheight_comap_of_surjective π Ideal.Quotient.mk_surjective
      (Ideal.span ({π q} : Set B))
    rw [hcomap, hlen, hn] at h
    exact_mod_cast h
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (w : B)
  have hu' : π u = (w : B) := hu
  refine ⟨t, u, ht, isUnit_of_map_unit π u (hu'.symm ▸ w.isUnit), ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (q - u * t ^ v) = 0
  rw [map_sub, map_mul, map_pow, hu', hvn, ← hw, sub_self]

end
end K1_13_6_1_3_2
end PackSource_K1_13_6_1_3_2Local

section PackSource_K1_13_7_4_2_2Aux1
set_option autoImplicit true
namespace K1_13_7_4_2_2

noncomputable section

open IsLocalRing KaehlerDifferential MvPolynomial
open scoped TensorProduct

variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- A split conormal map gives a first-order coordinate map whose values on
lifts of the cotangent basis are the coordinate variables. -/
private theorem firstOrder [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (ResidueField R)] {n : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R)) :
    ∃ (f : R →ₐ[k] Jets (ResidueField R) n 2),
      (∀ r, constant (ResidueField R) n 2 (by decide) (f r) = residue R r) ∧
      ∀ i, ∃ x ∈ maximalIdeal R, f x = jet (ResidueField R) n 2 (X i) := by
  let K := ResidueField R
  let S := Jets K n 2
  let J := aug K n 2
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := k)
    (P := R) (A := K) residue_surjective).mp inferInstance
  have hk : RingHom.ker (algebraMap R K) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  let e : (RingHom.ker (algebraMap R K)).Cotangent ≃ₗ[R] CotangentSpace R :=
    Ideal.Cotangent.equivOfEq _ _ hk
  let τ : Ω[R⁄k] →ₗ[R] K ⊗[R] Ω[R⁄k] := TensorProduct.mk R K _ 1
  let D₀ : Derivation k R (CotangentSpace R) :=
    (e.toLinearMap.comp (l.comp τ)).compDer (D k R)
  let v (i : Fin n) : J := ⟨jet K n 2 (X i), X_mem_aug K n 2 i⟩
  let L : CotangentSpace R →ₗ[K] J := b.constr K v
  let δ : Derivation k R J := (L.restrictScalars R).compDer D₀
  let f := liftOfDerivationToSquareZero J (aug_pow_self K n 2) δ
  refine ⟨f, ?_, ?_⟩
  · intro r
    rw [liftOfDerivationToSquareZero_apply, map_add]
    have hδ : (δ r : S) ∈ RingHom.ker (constant K n 2 (by decide)) := by
      rw [ker_constant]
      exact (δ r).2
    rw [RingHom.mem_ker.mp hδ, zero_add]
    exact constant_algebraMap K n 2 (by decide) (residue R r)
  · intro i
    obtain ⟨x, hx⟩ := (maximalIdeal R).toCotangent_surjective (b i)
    let x' : RingHom.ker (algebraMap R K) := ⟨x, by
      rw [ResidueField.algebraMap_eq, ker_residue]
      exact x.2⟩
    have hD : D₀ (x : R) = b i := by
      change e (l (1 ⊗ₜ[R] D k R (x : R))) = b i
      rw [← kerCotangentToTensor_toCotangent k R K x']
      have h := DFunLike.congr_fun hl ((RingHom.ker (algebraMap R K)).toCotangent x')
      change l (kerCotangentToTensor k R K _) = _ at h
      rw [h, LinearMap.id_apply]
      dsimp only [e]
      rw [Ideal.Cotangent.equivOfEq_toCotangent]
      exact hx
    refine ⟨x, x.2, ?_⟩
    rw [liftOfDerivationToSquareZero_apply]
    change (L (D₀ (x : R)) : S) + algebraMap K S (residue R x) = _
    dsimp only [L]
    rw [hD, Module.Basis.constr_basis, (residue_eq_zero_iff _).mpr x.2, map_zero, add_zero]

/-- A nilpotent ideal contained in its square modulo another ideal
is contained in that other ideal. -/
private theorem le_of_le_sup_sq {S : Type*} [CommRing S] (J I : Ideal S) (t : ℕ)
    (hJ : J ^ t = ⊥) (h : J ≤ I ⊔ J ^ 2) : J ≤ I := by
  have step (s : ℕ) : J ^ (s + 1) ≤ I ⊔ J ^ (s + 1 + 1) := by
    calc
      J ^ (s + 1) = J * J ^ s := pow_succ' _ _
      _ ≤ (I ⊔ J ^ 2) * J ^ s := Ideal.mul_mono_left h
      _ ≤ I ⊔ J ^ (s + 1 + 1) := by
        rw [Ideal.sup_mul, ← pow_add, show 2 + s = s + 1 + 1 by omega]
        exact sup_le_sup (Ideal.mul_le_left) le_rfl
  have all (s : ℕ) : J ≤ I ⊔ J ^ s := by
    induction s with
    | zero => simp
    | succ s ih =>
      cases s with
      | zero => simpa only [Nat.zero_add, pow_one] using (le_sup_right : J ≤ I ⊔ J)
      | succ s => exact ih.trans (sup_le le_sup_left (step s))
  simpa [hJ] using all t

omit [IsLocalRing R] in
/-- Surjectivity follows from surjectivity modulo a nilpotent ideal,
provided the ideal is generated by the images of its inverse image. -/
private theorem surj_of_augmentation {S K : Type*} [CommRing S] [CommRing K]
    (f : R →+* S) (a : S →+* K) (I : Ideal R) (J : Ideal S) (t : ℕ)
    (hJ : J ^ t = ⊥) (hmap : I.map f = J)
    (ha : RingHom.ker a = J) (hs : Function.Surjective (a.comp f)) :
    Function.Surjective f := by
  let : Algebra R S := f.toAlgebra
  let A : Submodule R S := LinearMap.range (Algebra.linearMap R S)
  have htop : A ⊔ I • (⊤ : Submodule R S) = ⊤ := by
    rw [Ideal.smul_top_eq_map, show algebraMap R S = f from rfl, hmap]
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨x, hx⟩ := hs (a y)
    refine Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, y - f x, ?_, by ring⟩
    rw [Submodule.restrictScalars_mem, ← ha, RingHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr hx.symm
  have hs' (s : ℕ) : A ⊔ I ^ s • (⊤ : Submodule R S) = ⊤ := by
    induction s with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
    | succ s ih =>
      calc
        A ⊔ I ^ (s + 1) • (⊤ : Submodule R S)
            = A ⊔ I • (I ^ s • (⊤ : Submodule R S)) := by rw [pow_succ', mul_smul]
        _ = A ⊔ I • (A ⊔ I ^ s • (⊤ : Submodule R S)) := by
          rw [Submodule.smul_sup, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • A ≤ A)]
        _ = ⊤ := by rw [ih, htop]
  have hzero : I ^ t • (⊤ : Submodule R S) = ⊥ := by
    rw [Ideal.smul_top_eq_map, show algebraMap R S = f from rfl, Ideal.map_pow, hmap, hJ]
    rfl
  have hA := hs' t
  rw [hzero, sup_bot_eq] at hA
  exact LinearMap.range_eq_top.mp hA

/-- Lift the first-order chart through the nilpotent polynomial truncations. -/
theorem exists_jet_surjection [Algebra.FormallySmooth k R]
    [Algebra.FormallySmooth k (ResidueField R)] {n t : ℕ} (ht : 2 ≤ t)
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R)) :
    ∃ f : (R ⧸ maximalIdeal R ^ t) →+* Jets (ResidueField R) n t,
      Function.Surjective f := by
  let K := ResidueField R
  let S := Jets K n t
  let J := aug K n t
  let a : S →+* K := constant K n t (by omega)
  let π : S →ₐ[k] Jets K n 2 :=
    Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right ht)
  have hπ : RingHom.ker π = J ^ 2 := by
    change RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right ht :
      Vars K n ^ t ≤ Vars K n ^ 2)) = J ^ 2
    rw [Ideal.Quotient.factor_ker, Ideal.map_pow]
  have hnil : IsNilpotent (RingHom.ker π) := by
    rw [hπ]
    refine ⟨t, ?_⟩
    change (J ^ 2) ^ t = (⊥ : Ideal S)
    rw [← pow_mul, mul_comm 2 t, pow_mul, show J ^ t = ⊥ from aug_pow_self K n t]
    exact Ideal.bot_pow (by decide)
  have hs : Function.Surjective π :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right ht)
  obtain ⟨f₂, hconst, hx⟩ := firstOrder (k := k) b
  let f := Algebra.FormallySmooth.liftOfSurjective f₂ π hs hnil
  have hf (r : R) : π (f r) = f₂ r :=
    Algebra.FormallySmooth.liftOfSurjective_apply f₂ π hs hnil r
  have hconst' (r : R) : a (f r) = residue R r := by
    have ha (y : S) : a y = constant K n 2 (by decide) (π y) := by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    rw [ha, hf, hconst]
  have hker : RingHom.ker a = J := ker_constant K n t _
  have hm : (maximalIdeal R).map f.toRingHom ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    rw [Ideal.mem_comap, ← hker, RingHom.mem_ker]
    change a (f r) = 0
    rw [hconst']
    exact (residue_eq_zero_iff _).mpr hr
  have hmap : (maximalIdeal R).map f.toRingHom = J := by
    refine le_antisymm hm (le_of_le_sup_sq J _ t (aug_pow_self K n t) ?_)
    refine ((aug_eq_span K n t).le).trans (Ideal.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hx₁, hx₂⟩ := hx i
    refine Submodule.mem_sup.mpr ⟨f x, Ideal.mem_map_of_mem _ hx₁, jet K n t (X i) - f x, ?_,
      by ring⟩
    change _ ∈ J ^ 2
    rw [← hπ, RingHom.mem_ker, map_sub, sub_eq_zero, hf, hx₂]
    rfl
  have hsurj := surj_of_augmentation f.toRingHom a _ J t (aug_pow_self K n t)
    hmap hker (fun c => by
      obtain ⟨r, hr⟩ := residue_surjective (R := R) c
      exact ⟨r, (hconst' r).trans hr⟩)
  have hkill : maximalIdeal R ^ t ≤ RingHom.ker f.toRingHom := by
    rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, hmap]
    exact aug_pow_self K n t
  exact ⟨Ideal.Quotient.lift _ f.toRingHom hkill,
    hsurj.of_comp (g := Ideal.Quotient.mk _)⟩

end

end K1_13_7_4_2_2
end PackSource_K1_13_7_4_2_2Aux1

section PackSource_K1_13_7_4_2_2Aux2
set_option autoImplicit true
namespace K1_13_7_4_2_2

noncomputable section

open MvPolynomial IsLocalRing
open scoped BigOperators

private abbrev Mono (n t : ℕ) := Σ j : Fin t, Sym (Fin n) j.val

private def exponent {n t : ℕ} (a : Mono n t) : Fin n →₀ ℕ := a.2.val.toFinsupp

private theorem exponent_degree {n t : ℕ} (a : Mono n t) :
    (exponent a).degree = a.1.val := by
  change (a.2.val.toFinsupp).sum (fun _ j => j) = a.1.val
  exact (Multiset.toFinsupp_sum_eq _).trans a.2.property

private theorem exponent_injective (n t : ℕ) : Function.Injective (@exponent n t) := by
  rintro ⟨d, a⟩ ⟨e, b⟩ h
  have hde : d = e := Fin.ext ((exponent_degree ⟨d, a⟩).symm.trans
    ((congrArg Finsupp.degree h).trans (exponent_degree ⟨e, b⟩)))
  subst e
  exact congrArg (Sigma.mk d) (Subtype.ext (Multiset.toFinsupp.injective h))

private theorem card_mono (n t : ℕ) (ht : 0 < t) :
    Fintype.card (Mono n t) = (t + n - 1).choose n := by
  classical
  rw [Fintype.card_sigma]
  simp only [Sym.card_sym_eq_multichoose, Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  rw [Nat.sum_range_multichoose]
  congr 1
  omega

/-- Distinct monomials below the cutoff survive in the truncated polynomial ring. -/
private theorem length_over_field (K : Type*) [Field K] (n t : ℕ) (ht : 0 < t) :
    ((t + n - 1).choose n : ℕ∞) ≤ Module.length K (Jets K n t) := by
  classical
  let coeff (a : Mono n t) : Jets K n t →ₗ[K] K :=
    ((Vars K n ^ t).restrictScalars K).liftQ (lcoeff K (exponent a)) (by
      intro p hp
      exact (mem_pow_idealOfVars_iff' t p).mp hp _ (by
        rw [exponent_degree]
        exact a.1.isLt))
  let f : Jets K n t →ₗ[K] (Mono n t → K) := LinearMap.pi coeff
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨jet K n t (∑ a, monomial (exponent a) (c a)), ?_⟩
    funext a
    change (∑ b, monomial (exponent b) (c b)).coeff (exponent a) = c a
    rw [coeff_sum, Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [coeff_monomial, (exponent_injective n t).ne hba]
    · simp
  have h := Module.length_le_of_surjective f hsurj
  rw [Module.length_pi_of_fintype] at h
  simpa [card_mono n t ht] using h

/-- The length over the truncated ring equals its length over the residue field. -/
theorem length_jets (K : Type*) [Field K] (n t : ℕ) (ht : 0 < t) :
    ((t + n - 1).choose n : ℕ∞) ≤ Module.length (Jets K n t) (Jets K n t) := by
  let S := Jets K n t
  let J := aug K n t
  let f := constant K n t ht
  have hf : Function.Surjective f := constant_surjective K n t ht
  have hker : RingHom.ker f = J := ker_constant K n t ht
  have hmax : J.IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective f hf
  have hnil : nilradical S = J := by
    let : J.IsPrime := hmax.isPrime
    refine le_antisymm (nilradical_le_prime J) (fun x hx => ?_)
    apply mem_nilradical.mpr
    refine ⟨t, ?_⟩
    exact Ideal.mem_bot.mp ((show J ^ t = ⊥ from aug_pow_self K n t) ▸ Ideal.pow_mem_pow hx t)
  let : (nilradical S).IsMaximal := hnil.symm ▸ hmax
  let : IsLocalRing S := IsLocalRing.of_isMaximal_nilradical S
  have hm : maximalIdeal S = J := (IsLocalRing.eq_maximalIdeal hmax).symm
  let : IsLocalHom (algebraMap K S) := ⟨fun x hx => by
    apply isUnit_iff_ne_zero.mpr
    rintro rfl
    simp at hx⟩
  have hres : Function.Surjective (algebraMap K (ResidueField S)) := by
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    refine ⟨f x, ?_⟩
    change residue S (algebraMap K S (f x)) = residue S x
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, hm, ← hker,
      RingHom.mem_ker, map_sub, constant_algebraMap, sub_self]
  have hlen : Module.length (ResidueField K) (ResidueField S) = 1 := by
    rw [← Module.length_eq_of_surjective (M := ResidueField S) (residue_surjective (R := K)),
      Module.length_eq_of_surjective hres, Module.length_eq_one]
  have h := length_over_field K n t ht
  rwa [IsLocalRing.length_restrictScalars K S S, hlen, mul_one] at h

end

end K1_13_7_4_2_2
end PackSource_K1_13_7_4_2_2Aux2
