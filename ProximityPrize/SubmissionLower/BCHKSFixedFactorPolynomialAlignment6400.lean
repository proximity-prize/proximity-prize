import ProximityPrize.SubmissionLower.BCHKSFixedFactorConcreteSelection6400
import ProximityPrize.SubmissionLower.BCHKSUniversalNumeratorFunctionField
import ProximityPrize.SubmissionLower.BCHKSUniversalSelectedPairCore

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace FixedFactorPolynomialAlignment6400

open FixedFactorCover6400
open FixedFactorConcreteSelection6400
open UniversalPairFiberBridge6399
open UniversalNumerator

/-- A selected score-64 factor of degree 3 through 114 forces polynomial
alignment on more than `errors+1` challenge rows. -/
theorem fixed_factor_polynomial_alignment_6400
    (U : Fin 2 → IRSProfile.Index → F)
    (S : Finset F)
    (A : F → Finset IRSProfile.Index)
    (P : ↑S → Polynomial F)
    (R : TriPoly)
    (hR : Irreducible R) (hpos : 0 < R.natDegree)
    (hd : R.natDegree ≤ 114) (D : ℕ) (hD : D ≤ 1898945373)
    (hYZ : YZCap R D)
    (hweighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 8325809424)
    (hPdeg : ∀ z : ↑S, (P z).natDegree ≤ 131071)
    (hAcard : ∀ z : ↑S, 185364 ≤ (A z.1).card)
    (hagree : ∀ z : ↑S, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + z.1 * U 1 i)
    (hRroot : ∀ z : ↑S, triEval R z.1 (P z) = 0)
    (hS : 144802557 * D < S.card) :
    ∃ p₀ p₁ : F[X], ∃ T : Finset F,
      ∃ hTsub : T ⊆ S, bchksErrors6400 + 1 < T.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z, ∀ hz : z ∈ T,
        P ⟨z, hTsub hz⟩ = p₀ + Polynomial.C z * p₁ := by
  classical
  let PE : F → Polynomial F := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  obtain ⟨x₀, Bad, H, Coord, hBad, hBdeg, hB0, hprim, hseed,
      hH, hTcard, hCoord, hrelRaw, hdiv, hsimple⟩ :=
    exists_concrete_fixed_factor_pair_6400 U S A P R hR hpos hd D hD
      hYZ hweighted hPdeg hAcard hagree hRroot hS
  let T := innerFiber S Bad PE x₀ H
  have hTsub : T ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hrel : ∀ z ∈ T, innerRel PE x₀ z H := by
    simpa [T, PE] using hrelRaw
  have hHnorm : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX R x₀) :=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp hH).1
  have hHpos : 0 < H.natDegree := (Finset.mem_filter.mp hH).2
  have hHirr : Irreducible H :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H hHnorm).irreducible
  have hHd : H ∣ triSpecializeX R x₀ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHnorm
  have hHyp : HenselNumerators.Hypotheses x₀ R H := by
    have hRXeq : triSpecializeX R x₀ =
        Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
      simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
    refine ⟨?_, ?_, ?_⟩
    · simpa [hRXeq] using hHd
    · simpa [← hRXeq] using hprim.ne_zero
    · intro Q hfac hQdeg
      let q₀ : Polynomial F := Q.coeff 0
      have hQC : Q = Polynomial.C q₀ :=
        Polynomial.eq_C_of_natDegree_le_zero hQdeg.le
      have hCdvd : Polynomial.C q₀ ∣
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
        refine ⟨H, ?_⟩
        calc
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R = H * Q := hfac
          _ = H * Polynomial.C q₀ := by rw [hQC]
          _ = Polynomial.C q₀ * H := mul_comm _ _
      have hprimEval :
          (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive := by
        simpa [← hRXeq] using hprim
      exact (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprimEval) q₀ hCdvd
  letI : Fact (Irreducible H) := ⟨hHirr⟩
  letI : Fact (0 < H.natDegree) := ⟨hHpos⟩
  let PT : T → Polynomial F := fun z => PE z
  have hPTdeg : ∀ z : T, (PT z).natDegree ≤ 131071 := by
    intro z
    simpa [PT, PE, hTsub z.property] using hPdeg ⟨z, hTsub z.property⟩
  have hExact : ∀ z : T,
      (triSpecializeZ R (z : F)).eval (PT z) = 0 := by
    intro z
    change triEval R (z : F) (PT z) = 0
    simpa [PT, PE, hTsub z.property] using hRroot ⟨z, hTsub z.property⟩
  have hfactor : ∀ z : T,
      Polynomial.evalEval (z : F) ((PT z).eval x₀) H = 0 := by
    intro z
    exact (eval_map_eval_eq_eval_eval_C H ((PT z).eval x₀) (z : F)).symm.trans
      (by
        change biEval H ((PT z).eval x₀) (z : F) = 0
        simpa only [PT, innerRel] using hrel z z.property)
  have hsimpleSlope : ∀ z : T, FiniteHensel.ySlope
      (triSpecializeZ R (z : F)) x₀ ((PT z).eval x₀) ≠ 0 := by
    intro z
    rw [ySlope_eq_derivative_specialization]
    have hzBad : (z : F) ∉ Bad :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp z.property).1).2
    apply hsimple (z : F) hzBad ((PT z).eval x₀)
    have hz := congrArg (Polynomial.eval x₀) (hExact z)
    calc
      Polynomial.eval ((PT z).eval x₀)
          (biSpecializeZ (triSpecializeX R x₀) (z : F)) =
        (Polynomial.evalRingHom x₀)
          ((triSpecializeZ R (z : F)).eval (PT z)) := by
            exact (eval_triEval_eq_biEval_triSpecializeX R (PT z) x₀
              (z : F)).symm.trans (by rfl)
      _ = 0 := by simpa using hz
  have hW : ∀ z : T, H.leadingCoeff.eval (z : F) ≠ 0 := by
    intro z
    have hzBad : (z : F) ∉ Bad :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp z.property).1).2
    have hparts := obstruction_seed_parts x₀ (z : F) R (hseed (z : F) hzBad)
    exact inner_leadingCoeff_eval_ne_zero x₀ (z : F) R H hBdeg hHd hparts.1
  let root : ∀ z : T, rationalRoot (monicize H) (z : F) :=
    fun z => rationalRootOfPair H hHpos (z : F) ((PT z).eval x₀) (hfactor z)
  have hx : ∀ z : T, GoodAt (z : F) (root z)
      (fieldTo𝕃 (H := H) x₀) x₀ := fun z =>
    GoodAt.fieldTo𝕃 (H := H) (z : F) (root z) x₀
  have hy : ∀ z : T, GoodAt (z : F) (root z)
      (initialValue (H := H)) ((PT z).eval x₀) := by
    intro z
    have hTval : GoodAt (z : F) (root z)
        (functionFieldT (H := H))
        (H.leadingCoeff.eval (z : F) * (PT z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X,
        1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using
          (piZ_mk_X_rationalRootOfPair H hHpos (z : F)
            ((PT z).eval x₀) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H := H)
      (z : F) (root z) H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ (hW z)] using
      GoodAt.div hTval hWgood (hW z)
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by
    have : bchksErrors6400 + 1 < T.card := by simpa [T, PE] using hTcard
    omega)
  let z₀ : T := ⟨Classical.choose hTnonempty, Classical.choose_spec hTnonempty⟩
  have hzeta : zeta R x₀ H ≠ 0 :=
    zeta_ne_zero_of_selected_slope x₀ R (z₀ : F) (root z₀) x₀
      ((PT z₀).eval x₀) (hx z₀) (hy z₀) (hsimpleSlope z₀)
  have hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp
      (z : F) (root z) x₀ ((PT z).eval x₀) := by
    intro z
    exact selectedNonpoleData x₀ R hHyp hzeta (z : F) (root z) x₀
      ((PT z).eval x₀) (hx z) (hy z) (hW z) (hsimpleSlope z)
  have hsimpleAt : ∀ z : T, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R (z : F)) x₀ ((PT z).eval x₀) := by
    intro z
    refine ⟨?_, hsimpleSlope z⟩
    have hz := congrArg (Polynomial.eval x₀) (hExact z)
    calc
      (triSpecializeZ R (z : F)).eval₂ (Polynomial.evalRingHom x₀)
          ((PT z).eval x₀) =
        (Polynomial.evalRingHom x₀)
          ((triSpecializeZ R (z : F)).eval (PT z)) := by
            exact (Polynomial.hom_eval₂ (triSpecializeZ R (z : F))
              (RingHom.id _) (Polynomial.evalRingHom x₀) (PT z)).symm
      _ = 0 := by simpa using hz
  let Sel : UniversalSelectedHenselData x₀ R H hHyp hzeta
      D R.natDegree 131071 131072 T PT := {
    root := root
    hx := hx
    hy := hy
    hsL := (hNP z₀).hsL
    hsimple := hsimpleAt
    hExact := hExact
    hslope := fun z => (hNP z).hslope
    hW := hW
    hxi := fun z => (hNP z).hxi }
  let Afield : Finset F := Coord.image IRSProfile.domain
  have hAfield : 131072 ≤ Afield.card := by
    have hc : Afield.card = Coord.card :=
      Finset.card_image_iff.mpr fun a _ b _ hab => IRSProfile.domain.injective hab
    rw [hc]
    exact hCoord
  let idx : Afield → IRSProfile.Index := fun x =>
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : Afield) : idx x ∈ Coord ∧ IRSProfile.domain (idx x) = (x : F) :=
    Classical.choose_spec (Finset.mem_image.mp x.property)
  let U₀ : F → F := fun x =>
    if hxA : x ∈ Afield then U 0 (idx ⟨x, hxA⟩) else 0
  let U₁ : F → F := fun x =>
    if hxA : x ∈ Afield then U 1 (idx ⟨x, hxA⟩) else 0
  have hs : Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H)) (universalSlope x₀ R) = zeta R x₀ H := by
    change evalUniversal (liftToFunctionField (H := H))
      (initialValue (H := H)) (universalSlope x₀ R) = _
    rw [universalSlope_evalUniversal]
    simpa [liftedR, fieldTo𝕃] using
      (ySlope_liftedR_eq_zeta (R := R) (H := H) x₀)
  have hnum : ∀ i, i ≤ 131071 →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (universalRootedNumerators x₀ R i) =
        finiteAlpha (R := R) (H := H) x₀ 131072 i *
          zeta R x₀ H ^ FiniteHenselWeight.denominatorExponent i := by
    intro i hi
    exact eval₂_universalRootedNumerators_eq_finiteAlpha_mul_zeta_pow
      x₀ R hHyp hzeta 131072 i (by omega)
  have hzero : ∀ x ∈ Afield,
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H))
          (universalAffineObstruction (universalRootedNumerators x₀ R)
            (universalSlope x₀ R) bchksUniversalExponent6399 131071
            (x - x₀) (U₀ x) (U₁ x)) = 0 := by
    intro x hxA
    let xx : Afield := ⟨x, hxA⟩
    have hdvd := hdiv (idx xx) (hidx xx).1
    have heval := eval₂_lift_initialValue_eq_zero_of_dvd _ H hdvd
    have hxeq : IRSProfile.domain (idx xx) = x := (hidx xx).2
    simpa [concreteUniversalAffineObstruction, U₀, U₁, hxA, xx, hxeq]
      using heval
  obtain ⟨p₀, p₁, hp₀, hp₁, halign⟩ :=
    universal_selected_pair_alignment_core_light x₀ R hHyp hzeta
      D R.natDegree 131071 131072 (by norm_num) T PT Sel hNP hPTdeg
      (by norm_num [F, IRSProfile.Field]) Afield hAfield U₀ U₁
      (universalRootedNumerators x₀ R) (universalSlope x₀ R)
      bchksUniversalExponent6399
      (by norm_num [bchksUniversalExponent6399,
        FiniteHenselWeight.denominatorExponent]) hs hnum hzero
  refine ⟨p₀, p₁, T, hTsub, ?_, hp₀, hp₁, ?_⟩
  · simpa [T, PE] using hTcard
  · intro z hz
    have hzS := hTsub hz
    simpa [PT, PE, hzS] using halign ⟨z, hz⟩

end FixedFactorPolynomialAlignment6400

end ProximityPrize.SubmissionLower
