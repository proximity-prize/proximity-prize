import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface6399
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteSelection6399
import ProximityPrize.SubmissionLower.BCHKSUniversalNumeratorFunctionField
import ProximityPrize.SubmissionLower.BCHKSUniversalSelectedPairCore
import ProximityPrize.SubmissionLower.BCHKSUniversalPairFiberBridge6399
import ProximityPrize.SubmissionLower.BCHKSPairSetup6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open UniversalOuterCover6399
open UniversalConcreteSelection6399
open UniversalPairFiberBridge6399
open UniversalNumerator

/-- Unconditional polynomial alignment at the 63.99 parameters, obtained from
the universal unreduced numerator and aggregate all-factor resultant ledger. -/
theorem bchksPolynomialAlignment6399 : BCHKSPolynomialAlignment6399 := by
  classical
  intro U S A P Q hScard hQ hPdeg hAcard hagree hQeval hcaps
  let PE : IRSProfile.Field → Polynomial IRSProfile.Field := fun z =>
    if hz : z ∈ S then P ⟨z, hz⟩ else 0
  obtain ⟨x₀, RH, T, Coord, hRH, hxSelected, hTS, hTcard, hCoord,
      hrelRaw, hdiv⟩ :=
    exists_concrete_selected_pair6399 U S A P Q hScard hQ hPdeg hAcard
      hagree hQeval hcaps
  have hrel : ∀ z ∈ T, pairRel PE x₀ z RH := by
    simpa [PE] using hrelRaw
  have hm := pair_mem_facts Q x₀ RH hRH
  have hQY : Q.natDegree ≤ 5279 := by
    simpa [bchksFactorMass6399] using natDegree_le_factorMass Q hQ hcaps
  have hprimEvalX :
      (Polynomial.Bivariate.evalX (Polynomial.C x₀) RH.1).IsPrimitive := by
    simpa [triSpecializeX, Polynomial.Bivariate.evalX_eq_map] using hxSelected.1
  obtain ⟨hRirr, hHirr, hHpos, hHd, hRdeg, hHdeg, hHtotal,
      hBtotal, hRweighted, hHyp⟩ :=
    bchks_pair_setup6399_of_selected_factors Q RH.1 RH.2 x₀ hQ hm.1
      hm.2.2.1 hm.2.2.2.1 hQY
      (fun j a ha => (hcaps j a ha).2.2)
      (fun j a ha => (hcaps j a ha).2.1) hprimEvalX
  letI : Fact (Irreducible RH.2) := ⟨hHirr⟩
  letI : Fact (0 < RH.2.natDegree) := ⟨hHpos⟩
  let PT : T → Polynomial IRSProfile.Field := fun z => PE z
  have hPTdeg : ∀ z : T, (PT z).natDegree ≤ 131071 := by
    intro z
    simpa [PT, PE, hTS z.property] using hPdeg ⟨z, hTS z.property⟩
  have hExact : ∀ z : T,
      (triSpecializeZ RH.1 (z : IRSProfile.Field)).eval (PT z) = 0 := by
    intro z
    exact (hrel z z.property).1
  have hfactor : ∀ z : T,
      Polynomial.evalEval (z : IRSProfile.Field) ((PT z).eval x₀) RH.2 = 0 := by
    intro z
    exact (eval_map_eval_eq_eval_eval_C RH.2 ((PT z).eval x₀)
      (z : IRSProfile.Field)).symm.trans (hrel z z.property).2.1
  have hsimpleSlope : ∀ z : T, FiniteHensel.ySlope
      (triSpecializeZ RH.1 (z : IRSProfile.Field)) x₀ ((PT z).eval x₀) ≠ 0 := by
    intro z
    exact simple_slope_of_pairRel PE x₀ (z : IRSProfile.Field) RH.1 RH.2
      (hrel z z.property) hxSelected.2.2.2.1 hm.2.1
  have hW : ∀ z : T, RH.2.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0 := by
    intro z
    have hparts := obstruction_seed_parts x₀ (z : IRSProfile.Field) RH.1
      (hrel z z.property).2.2.1
    exact inner_leadingCoeff_eval_ne_zero x₀ (z : IRSProfile.Field)
      RH.1 RH.2 hxSelected.2.2.2.1 hHd hparts.1
  let root : ∀ z : T, rationalRoot (monicize RH.2) (z : IRSProfile.Field) :=
    fun z => rationalRootOfPair RH.2 hHpos (z : IRSProfile.Field)
      ((PT z).eval x₀) (hfactor z)
  have hx : ∀ z : T, GoodAt (z : IRSProfile.Field) (root z)
      (fieldTo𝕃 (H := RH.2) x₀) x₀ := fun z =>
    GoodAt.fieldTo𝕃 (H := RH.2) (z : IRSProfile.Field) (root z) x₀
  have hy : ∀ z : T, GoodAt (z : IRSProfile.Field) (root z)
      (initialValue (H := RH.2)) ((PT z).eval x₀) := by
    intro z
    have hTval : GoodAt (z : IRSProfile.Field) (root z)
        (functionFieldT (H := RH.2))
        (RH.2.leadingCoeff.eval (z : IRSProfile.Field) * (PT z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize RH.2}) Polynomial.X,
        1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using
          (piZ_mk_X_rationalRootOfPair RH.2 hHpos (z : IRSProfile.Field)
            ((PT z).eval x₀) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H := RH.2)
      (z : IRSProfile.Field) (root z) RH.2.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ (hW z)] using
      GoodAt.div hTval hWgood (hW z)
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  let z₀ : T := ⟨Classical.choose hTnonempty, Classical.choose_spec hTnonempty⟩
  have hzeta : zeta RH.1 x₀ RH.2 ≠ 0 :=
    zeta_ne_zero_of_selected_slope x₀ RH.1 (z₀ : IRSProfile.Field)
      (root z₀) x₀ ((PT z₀).eval x₀) (hx z₀) (hy z₀)
      (hsimpleSlope z₀)
  have hNP : ∀ z : T, SelectedNonpoleData x₀ RH.1 RH.2 hHyp
      (z : IRSProfile.Field) (root z) x₀ ((PT z).eval x₀) := by
    intro z
    exact selectedNonpoleData x₀ RH.1 hHyp hzeta (z : IRSProfile.Field)
      (root z) x₀ ((PT z).eval x₀) (hx z) (hy z) (hW z)
      (hsimpleSlope z)
  have hsimpleAt : ∀ z : T, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ RH.1 (z : IRSProfile.Field)) x₀ ((PT z).eval x₀) := by
    intro z
    refine ⟨?_, hsimpleSlope z⟩
    have hz := congrArg (Polynomial.eval x₀) (hExact z)
    calc
      (triSpecializeZ RH.1 (z : IRSProfile.Field)).eval₂
          (Polynomial.evalRingHom x₀) ((PT z).eval x₀) =
          (Polynomial.evalRingHom x₀)
            ((triSpecializeZ RH.1 (z : IRSProfile.Field)).eval (PT z)) := by
        exact (Polynomial.hom_eval₂
          (triSpecializeZ RH.1 (z : IRSProfile.Field)) (RingHom.id _)
          (Polynomial.evalRingHom x₀) (PT z)).symm
      _ = 0 := by simpa using hz
  let Sel : UniversalSelectedHenselData x₀ RH.1 RH.2 hHyp hzeta
      bchksFactorZMass6399 RH.1.natDegree 131071 131072 T PT := {
    root := root
    hx := hx
    hy := hy
    hsL := (hNP z₀).hsL
    hsimple := hsimpleAt
    hExact := hExact
    hslope := fun z => (hNP z).hslope
    hW := hW
    hxi := fun z => (hNP z).hxi }
  let Afield : Finset IRSProfile.Field := Coord.image IRSProfile.domain
  have hAfield : 131072 ≤ Afield.card := by
    have hc : Afield.card = Coord.card :=
      Finset.card_image_iff.mpr fun a _ b _ hab => IRSProfile.domain.injective hab
    rw [hc]
    exact hCoord
  let idx : Afield → IRSProfile.Index := fun x =>
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : Afield) : idx x ∈ Coord ∧
      IRSProfile.domain (idx x) = (x : IRSProfile.Field) := by
    exact Classical.choose_spec (Finset.mem_image.mp x.property)
  let U₀ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hxA : x ∈ Afield then U 0 (idx ⟨x, hxA⟩) else 0
  let U₁ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hxA : x ∈ Afield then U 1 (idx ⟨x, hxA⟩) else 0
  have hs : Polynomial.eval₂ (liftToFunctionField (H := RH.2))
      (initialValue (H := RH.2)) (universalSlope x₀ RH.1) =
        zeta RH.1 x₀ RH.2 := by
    change evalUniversal (liftToFunctionField (H := RH.2))
      (initialValue (H := RH.2)) (universalSlope x₀ RH.1) = _
    rw [universalSlope_evalUniversal]
    simpa [liftedR, fieldTo𝕃] using
      (ySlope_liftedR_eq_zeta (R := RH.1) (H := RH.2) x₀)
  have hnum : ∀ i, i ≤ 131071 →
      Polynomial.eval₂ (liftToFunctionField (H := RH.2))
          (initialValue (H := RH.2)) (universalRootedNumerators x₀ RH.1 i) =
        finiteAlpha (R := RH.1) (H := RH.2) x₀ 131072 i *
          zeta RH.1 x₀ RH.2 ^ FiniteHenselWeight.denominatorExponent i := by
    intro i hi
    exact eval₂_universalRootedNumerators_eq_finiteAlpha_mul_zeta_pow
      x₀ RH.1 hHyp hzeta 131072 i (by omega)
  have hzero : ∀ x ∈ Afield,
      Polynomial.eval₂ (liftToFunctionField (H := RH.2))
        (initialValue (H := RH.2))
          (universalAffineObstruction (universalRootedNumerators x₀ RH.1)
            (universalSlope x₀ RH.1) bchksUniversalExponent6399 131071
            (x - x₀) (U₀ x) (U₁ x)) = 0 := by
    intro x hxA
    let xx : Afield := ⟨x, hxA⟩
    have hdvd := hdiv (idx xx) (hidx xx).1
    have heval := eval₂_lift_initialValue_eq_zero_of_dvd _ RH.2 hdvd
    have hxeq : IRSProfile.domain (idx xx) = x := (hidx xx).2
    simpa [concreteUniversalAffineObstruction, U₀, U₁, hxA, xx, hxeq]
      using heval
  obtain ⟨p₀, p₁, hp₀, hp₁, halign⟩ :=
    universal_selected_pair_alignment_core_light x₀ RH.1 hHyp hzeta
      bchksFactorZMass6399 RH.1.natDegree 131071 131072 (by norm_num)
      T PT Sel hNP hPTdeg (by norm_num [IRSProfile.Field]) Afield hAfield
      U₀ U₁ (universalRootedNumerators x₀ RH.1)
      (universalSlope x₀ RH.1) bchksUniversalExponent6399
      (by norm_num [bchksUniversalExponent6399,
        FiniteHenselWeight.denominatorExponent]) hs hnum hzero
  refine ⟨p₀, p₁, T, hTS, hTcard, hp₀, hp₁, ?_⟩
  intro z hz
  have hzS := hTS hz
  simpa [PT, PE, hzS] using halign ⟨z, hz⟩

end ProximityPrize.SubmissionLower
