import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.HW
import ProximityPrize.SubmissionLower.S7
import ProximityPrize.SubmissionLower.AP
section ProximityFlatProofPort
noncomputable section
open scoped nonZeroDivisors Polynomial WithZero RatFunc
variable (F K:Type*) [Field F] [Field K]
abbrev FunctionField [Algebra F⟮X⟯ K]:Prop:=
 FiniteDimensional F⟮X⟯ K
theorem functionField_iff (Ft:Type*) [Field Ft] [Algebra F[X] Ft]
   [IsFractionRing F[X] Ft] [Algebra F⟮X⟯ K] [Algebra Ft K] [Algebra F[X] K]
   [IsScalarTower F[X] Ft K] [IsScalarTower F[X] F⟮X⟯ K]:
   FunctionField F K ↔ FiniteDimensional Ft K:=by
 let e:=IsLocalization.algEquiv F[X]⁰ F⟮X⟯ Ft
 have:∀ (c) (x:K),e c • x=c • x:=by
   intro c x
   rw [Algebra.smul_def,Algebra.smul_def]
   congr
   refine congr_fun (f:=fun c => algebraMap Ft K (e c)) ?_ c
   refine IsLocalization.ext (nonZeroDivisors F[X]) _ _ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
     simp only [map_one,map_mul,AlgEquiv.commutes, ←IsScalarTower.algebraMap_apply]
 constructor <;> intro h
 · let b:=Module.finBasis F⟮X⟯ K
   exact (b.mapCoeffs e this).finiteDimensional_of_finite
 · let b:=Module.finBasis Ft K
   refine (b.mapCoeffs e.symm ?_).finiteDimensional_of_finite
   intro c x;convert! (this (e.symm c) x).symm;simp only [e.apply_symm_apply]
namespace FunctionField
theorem algebraMap_injective [Algebra F[X] K] [Algebra F⟮X⟯ K]
   [IsScalarTower F[X] F⟮X⟯ K]:Function.Injective (algebraMap F[X] K):=by
 rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
 exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
def ringOfIntegers [Algebra F[X] K]:=
 integralClosure F[X] K
namespace ringOfIntegers
variable [Algebra F[X] K]
instance:IsDomain (ringOfIntegers F K):=
 (ringOfIntegers F K).isDomain
instance:IsIntegralClosure (ringOfIntegers F K) F[X] K:=
 integralClosure.isIntegralClosure _ _
variable [Algebra F⟮X⟯ K] [IsScalarTower F[X] F⟮X⟯ K]
theorem algebraMap_injective:Function.Injective (algebraMap F[X] (ringOfIntegers F K)):=by
 have hinj:Function.Injective (algebraMap F[X] K):=by
   rw [IsScalarTower.algebraMap_eq F[X] F⟮X⟯ K]
   exact (algebraMap F⟮X⟯ K).injective.comp (IsFractionRing.injective F[X] F⟮X⟯)
 rw [injective_iff_map_eq_zero (algebraMap F[X] (↥(ringOfIntegers F K)))]
 intro p hp
 rw [←Subtype.coe_inj,Subalgebra.coe_zero] at hp
 rw [injective_iff_map_eq_zero (algebraMap F[X] K)] at hinj
 exact hinj p hp
theorem not_isField:¬IsField (ringOfIntegers F K):=by
 simpa [←(IsIntegralClosure.isIntegral_algebra F[X] K).isField_iff_isField
     (algebraMap_injective F K)] using
   Polynomial.not_isField F
variable [FunctionField F K]
instance:IsFractionRing (ringOfIntegers F K) K:=
 integralClosure.isFractionRing_of_finite_extension F⟮X⟯ K
instance:IsIntegrallyClosed (ringOfIntegers F K):=
 integralClosure.isIntegrallyClosedOfFiniteExtension F⟮X⟯
instance [Algebra.IsSeparable F⟮X⟯ K]:IsNoetherian F[X] (ringOfIntegers F K):=
 IsIntegralClosure.isNoetherian _ F⟮X⟯ K _
instance [Algebra.IsSeparable F⟮X⟯ K]:IsDedekindDomain (ringOfIntegers F K):=
 IsIntegralClosure.isDedekindDomain F[X] F⟮X⟯ K _
end ringOfIntegers
section deprecated
@[deprecated RatFunc.inftyValuationDef (since:="2026-04-14")]
alias inftyValuationDef:=RatFunc.inftyValuationDef
@[deprecated RatFunc.InftyValuation.map_zero' (since:="2026-04-14")]
alias InftyValuation.map_zero':=RatFunc.InftyValuation.map_zero'
@[deprecated RatFunc.InftyValuation.map_one' (since:="2026-04-14")]
alias InftyValuation.map_one':=RatFunc.InftyValuation.map_one'
@[deprecated RatFunc.InftyValuation.map_mul' (since:="2026-04-14")]
alias InftyValuation.map_mul':=RatFunc.InftyValuation.map_mul'
@[deprecated RatFunc.InftyValuation.map_add_le_max' (since:="2026-04-14")]
alias InftyValuation.map_add_le_max':=RatFunc.InftyValuation.map_add_le_max'
@[deprecated RatFunc.inftyValuation_of_nonzero (since:="2026-04-14")]
alias inftyValuation_of_nonzero:=RatFunc.inftyValuation_of_nonzero
@[deprecated RatFunc.inftyValuation (since:="2026-04-14")]
alias inftyValuation:=RatFunc.inftyValuation
@[deprecated RatFunc.inftyValuation_apply (since:="2026-04-14")]
alias inftyValuation_apply:=RatFunc.inftyValuation_apply
@[deprecated RatFunc.inftyValuation.C (since:="2026-04-14")]
alias inftyValuation.C:=RatFunc.inftyValuation.C
@[deprecated RatFunc.inftyValuation.X (since:="2026-04-14")]
alias inftyValuation.X:=RatFunc.inftyValuation.X
@[deprecated RatFunc.inftyValuation.X_zpow (since:="2026-04-14")]
alias inftyValuation.X_zpow:=RatFunc.inftyValuation.X_zpow
@[deprecated RatFunc.inftyValuation.X_inv (since:="2026-04-14")]
alias inftyValuation.X_inv:=RatFunc.inftyValuation.X_inv
@[deprecated RatFunc.inftyValuation.polynomial (since:="2026-04-14")]
alias inftyValuation.polynomial:=RatFunc.inftyValuation.polynomial
@[deprecated RatFunc.inftyValued (since:="2026-04-14")]
alias inftyValuedFqt:=RatFunc.inftyValued
@[deprecated RatFunc.inftyValued.def (since:="2026-04-14")]
alias inftyValuedFqt.def:=RatFunc.inftyValued.def
@[deprecated RatFunc.CompletionAtInfty (since:="2026-04-14")]
alias FqtInfty:=RatFunc.CompletionAtInfty
@[deprecated "Use the anonymous `Valued` instance on `RatFunc.CompletionAtInfty`"
(since:="2026-04-14")]
instance valuedFqtInfty [DecidableEq F⟮X⟯]:
   Valued (RatFunc.CompletionAtInfty F) ℤᵐ⁰:=
 inferInstance
@[deprecated RatFunc.valuedCompletionAtInfty.def (since:="2026-04-14")]
alias valuedFqtInfty.def:=RatFunc.valuedCompletionAtInfty.def
end deprecated
section AdjoinTranscendental
open IntermediateField RatFunc
variable {F K:Type*} [Field F] [Field K] [Algebra F⟮X⟯ K] [FunctionField F K]
instance FiniteDimensional.adjoin_X:FiniteDimensional F⟮(RatFunc.X:F⟮X⟯)⟯ K:=
 have:Module.Finite (⊤:IntermediateField F F⟮X⟯) F⟮X⟯:=
   .top_left F⟮X⟯ F⟮X⟯
 RatFunc.adjoin_X (K:=F) ▸ Module.Finite.trans F⟮X⟯ _
variable [Algebra F K] [IsScalarTower F F⟮X⟯ K]
theorem FiniteDimensional.adjoin_algebraMap_X:
   FiniteDimensional F⟮algebraMap _ K (RatFunc.X:F⟮X⟯)⟯ K:=
 .of_restrictScalars_finite F⟮(RatFunc.X:F⟮X⟯)⟯ _ _
theorem Algebra.IsAlgebraic.adjoin_algebraMap_X:
   Algebra.IsAlgebraic F⟮algebraMap _ K (RatFunc.X:F⟮X⟯)⟯ K:=by
 exact .tower_top (K:=F⟮(RatFunc.X:F⟮X⟯)⟯) _
variable {y:K}
theorem isAlgebraic_X_over_adjoin_transcendental (hy:Transcendental F y):
   IsAlgebraic F⟮y⟯ (algebraMap _ K (RatFunc.X:F⟮X⟯)):=
 isAlgebraic_adjoin_iff.mpr (.adjoin_singleton transcendental_X hy
   (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic y)))
lemma finiteDimensional_of_adjoin_transcendental (hy:Transcendental F y):
   FiniteDimensional F⟮y⟯ K:=
 let x:=algebraMap _ K (RatFunc.X:F⟮X⟯)
 let Fyx:=restrictScalars F F⟮y⟯⟮x⟯
 let Fxy:=restrictScalars F F⟮x⟯⟮y⟯
 let:Algebra F⟮y⟯ Fyx:=F⟮y⟯⟮x⟯.algebra
 let:Module F⟮y⟯ Fyx:=Algebra.toModule
 let:SMul F⟮y⟯ Fyx:=Algebra.toSMul
 let:Algebra F⟮x⟯ Fxy:=F⟮x⟯⟮y⟯.algebra
 let:Module F⟮x⟯ Fxy:=Algebra.toModule
 let:SMul F⟮x⟯ Fxy:=Algebra.toSMul
 have:FiniteDimensional F⟮y⟯ Fyx:=
   adjoin.finiteDimensional
     (isAlgebraic_iff_isIntegral.mp (isAlgebraic_X_over_adjoin_transcendental hy))
 have:FiniteDimensional Fyx K:=by
   have:=FiniteDimensional.adjoin_algebraMap_X (F:=F) (K:=K)
   unfold Fyx
   rw [adjoin_simple_comm]
   have:IsScalarTower F⟮x⟯ Fxy K:=isScalarTower_mid' F⟮x⟯⟮y⟯
   exact .right F⟮x⟯ Fxy K
 have:IsScalarTower F⟮y⟯ Fyx K:=isScalarTower_mid' F⟮y⟯⟮x⟯
 .trans F⟮y⟯ Fyx K
end AdjoinTranscendental
section constantExtension
open RatFunc
variable {F}
variable [Algebra F[X] K] [FaithfulSMul F[X] K] [FunctionField F K]
attribute [local instance] Polynomial.algebra
section Unbundled
open Polynomial
variable {E:Type*} [Field E] [Algebra F E] [Algebra E[X] K] [FaithfulSMul E[X] K]
theorem finiteDimensional_ratFunc_of_constantExtension [IsScalarTower F[X] E[X] K]:
   FiniteDimensional F⟮X⟯ E⟮X⟯:=
 .equiv (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F⟮X⟯ E⟮X⟯ K)).toLinearEquiv.symm
theorem finiteDimensional_of_constantExtension [IsScalarTower F[X] E[X] K]
   [Algebra.IsAlgebraic F E]:FiniteDimensional F E:=
 have:=finiteDimensional_ratFunc_of_constantExtension (F:=F) (E:=E) K
 Module.finite_of_finrank_pos ((finrank_ratFunc_ratFunc F E) ▸ Module.finrank_pos)
end Unbundled
section IntermediateField
variable [Algebra F K] (E:IntermediateField F K) [Algebra E[X] K] [FaithfulSMul E[X] K]
 [IsScalarTower F[X] E[X] K]
instance:FiniteDimensional F⟮X⟯ E⟮X⟯:=
 finiteDimensional_ratFunc_of_constantExtension K
instance [Algebra.IsAlgebraic F E]:FiniteDimensional F E:=
 finiteDimensional_of_constantExtension K
end IntermediateField
end constantExtension
end FunctionField
