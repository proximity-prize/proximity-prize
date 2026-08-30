import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.B4
namespace ProximityPrize.SubmissionLower.ContactAdaptiveComponentSeparatorResearch
open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ActualCurveCoordinateField ActualCurveRationalProjection
 ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactLocalPoleBound ContactLeadingCancellationResearch
 ContactGenericCoefficientAvoidanceResearch ContactSparsePoleSupportResearch
open ContactTropicalBKKSeamResearch ContactResidualSparseComponentAdapterResearch
open ContactSparsePoleZeroCountResearch
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
noncomputable def componentSeparator
   (C:RegularComponent Omega G T H):Fin 3:=
 Classical.choose
   (exists_transcendental_coordinate_of_ne_point_kernel Omega C.1
     (regularComponent_ne_point Omega G T H C))
theorem componentSeparator_transcendental
   (C:RegularComponent Omega G T H):
   Transcendental Omega
     (coordinate Omega C.1 (componentSeparator C)):=
 Classical.choose_spec
   (exists_transcendental_coordinate_of_ne_point_kernel Omega C.1
     (regularComponent_ne_point Omega G T H C))
def componentRelevantPlacesAdaptive
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (C:RegularComponent Omega G T H):
   Finset (Place Omega (CoordinateField Omega C.1)):=by
 classical
 let i0:=componentSeparator C
 let htr:=componentSeparator_transcendental C
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
   quotientPolynomialAlgebra Omega C.1 i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
   polynomialBaseAlgebra Omega C.1 i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
   rationalBaseAlgebra Omega C.1 i0 htr
 letI:=quotientBaseScalarTower Omega C.1 i0
 letI:=polynomialBaseScalarTower Omega C.1 i0
 letI:=quotientFractionScalarTower Omega C.1 i0
 letI:=polynomialRationalScalarTower Omega C.1 i0 htr
 letI:=rationalBaseScalarTower Omega C.1 i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).1
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).2
 exact Finset.univ.biUnion (fun i:Fin 3 =>
   if hi:coordinate Omega C.1 i≠0 then
     CommonPlaceBalance.placesFor Omega (CoordinateField Omega C.1)
       (coordinate Omega C.1 i) hi
   else ∅)
theorem coordinate_poleOrder_eq_zero_of_not_mem_adaptive
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1))
   (hv:v∉componentRelevantPlacesAdaptive hproj C) (i:Fin 3):
   poleOrder v.val (coordinate Omega C.1 i)=0:=by
 classical
 let i0:=componentSeparator C
 let htr:=componentSeparator_transcendental C
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
   quotientPolynomialAlgebra Omega C.1 i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
   polynomialBaseAlgebra Omega C.1 i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
   rationalBaseAlgebra Omega C.1 i0 htr
 letI:=quotientBaseScalarTower Omega C.1 i0
 letI:=polynomialBaseScalarTower Omega C.1 i0
 letI:=quotientFractionScalarTower Omega C.1 i0
 letI:=polynomialRationalScalarTower Omega C.1 i0 htr
 letI:=rationalBaseScalarTower Omega C.1 i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).1
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).2
 by_cases hi:coordinate Omega C.1 i=0
 · simp [hi,poleOrder]
 · have hnot:v∉CommonPlaceBalance.placesFor Omega
       (CoordinateField Omega C.1) (coordinate Omega C.1 i) hi:=by
     intro hmem
     apply hv
     unfold componentRelevantPlacesAdaptive
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:CommonPlaceBalance.order Omega (CoordinateField Omega C.1) v
       (coordinate Omega C.1 i)=0:=by
     by_contra hne
     exact hnot (CommonPlaceBalance.placesFor_covers Omega
       (CoordinateField Omega C.1) (coordinate Omega C.1 i) hi v hne)
   unfold CommonPlaceBalance.order at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Omega C.1 i)).log=0:=by omega
   rw [hlog]
   simp
theorem exponentSetPoleWeight_eq_zero_of_not_mem_adaptive
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1))
   (hv:v∉componentRelevantPlacesAdaptive hproj C):
   exponentSetPoleWeight v.val (coordinate Omega C.1) E=0:=by
 classical
 have hcoord:forall i:Fin 3,
     poleOrder v.val (coordinate Omega C.1 i)=0:=
   coordinate_poleOrder_eq_zero_of_not_mem_adaptive hproj C v hv
 unfold exponentSetPoleWeight exponentPoleWeight
 apply le_antisymm
 · apply Finset.max'_le
   intro z hz
   obtain rfl | hz:=Finset.mem_insert.mp hz
   · exact le_rfl
   · obtain ⟨d,_,rfl⟩:=Finset.mem_image.mp hz
     simp [hcoord]
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:Int) _)
abbrev AdaptiveRelevantPlaceIndex
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1):=
 Sigma fun C:RegularComponent Omega G T H =>
   {v:Place Omega (CoordinateField Omega C.1)//
     v∈componentRelevantPlacesAdaptive hproj C}
abbrev AdaptiveGenericityIndex
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1):=
 RegularComponent Omega G T H ⊕ AdaptiveRelevantPlaceIndex hproj
def adaptiveBadSubmodule
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ)):
   AdaptiveGenericityIndex hproj → Submodule Omega (E → Omega)
 | Sum.inl C => LinearMap.ker (coefficientEvaluation (coordinate Omega C.1) E)
 | Sum.inr ⟨C,v⟩ => cancellationSubmodule v.1.val
     (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v.1 a)
     (coordinate Omega C.1) E
theorem adaptiveBadSubmodule_ne_top
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   forall j:AdaptiveGenericityIndex hproj,
     adaptiveBadSubmodule hproj E j≠⊤:=by
 classical
 intro j
 rcases j with C | ⟨C,v⟩
 · intro htop
   let e0:E:=⟨0,hzero⟩
   let c0:E → Omega:=deltaCoefficient E e0
   have hc0:c0∈adaptiveBadSubmodule hproj E (Sum.inl C):=by
     rw [htop]
     trivial
   have hzeroeval:coefficientEvaluation (coordinate Omega C.1) E c0=0:=
     LinearMap.mem_ker.mp hc0
   have honeeval:coefficientEvaluation (coordinate Omega C.1) E c0=1:=by
     rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
       polynomialOfSupport_deltaCoefficient]
     simp [e0]
   rw [honeeval] at hzeroeval
   exact one_ne_zero hzeroeval
 · obtain ⟨c,hc⟩:=
     exists_exact_support_evaluation_of_downwardClosed
       (K:=Omega) (L:=CoordinateField Omega C.1) (σ:=Fin 3)
       v.1.val (coordinate Omega C.1) E hdown hzero
   exact cancellationSubmodule_ne_top_of_exact v.1.val
     (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v.1 a)
     (coordinate Omega C.1) E c hc
structure AdaptiveGenericExactPolePolynomial
   (G T H:MvPolynomial (Fin 3) Omega)
   (E:Finset (Fin 3 →₀ ℕ))
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1) where
 polynomial:MvPolynomial (Fin 3) Omega
 support_subset:polynomial.support ⊆ E
 proper:forall C:RegularComponent Omega G T H,polynomial∉C.1
 exact_pole:forall C:RegularComponent Omega G T H,
   let i0:=componentSeparator C
   let htr:=componentSeparator_transcendental C
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 i0 htr
   letI:=quotientBaseScalarTower Omega C.1 i0
   letI:=polynomialBaseScalarTower Omega C.1 i0
   letI:=quotientFractionScalarTower Omega C.1 i0
   letI:=polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).1
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).2
   forall v:Place Omega (CoordinateField Omega C.1),
     poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Omega (CoordinateField Omega C.1))
           (coordinate Omega C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1) E
theorem exists_adaptiveGenericExactPolePolynomial
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   Nonempty (AdaptiveGenericExactPolePolynomial G T H E hproj):=by
 classical
 let bad:=adaptiveBadSubmodule hproj E
 obtain ⟨c,hc⟩:=exists_avoiding_finite_proper_submodules bad
   (adaptiveBadSubmodule_ne_top hproj E hdown hzero)
 let B:=polynomialOfSupport E c
 have hsupport:B.support ⊆ E:=support_polynomialOfSupport_subset E c
 have hproper:forall C:RegularComponent Omega G T H,B∉C.1:=by
   intro C hmem
   apply hc (Sum.inl C)
   change c∈LinearMap.ker (coefficientEvaluation (coordinate Omega C.1) E)
   rw [LinearMap.mem_ker]
   have hker:B∈RingHom.ker
       (MvPolynomial.aeval (coordinate Omega C.1)).toRingHom:=by
     rw [aeval_coordinate_ker]
     exact hmem
   have hz:=RingHom.mem_ker.mp hker
   change MvPolynomial.aeval (coordinate Omega C.1) B=0 at hz
   rw [MvPolynomial.aeval_eq_eval₂Hom] at hz
   exact hz
 refine ⟨⟨B,hsupport,hproper,?_⟩⟩
 intro C
 dsimp only
 let i0:=componentSeparator C
 let htr:=componentSeparator_transcendental C
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
   quotientPolynomialAlgebra Omega C.1 i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
   polynomialBaseAlgebra Omega C.1 i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
   rationalBaseAlgebra Omega C.1 i0 htr
 letI:=quotientBaseScalarTower Omega C.1 i0
 letI:=polynomialBaseScalarTower Omega C.1 i0
 letI:=quotientFractionScalarTower Omega C.1 i0
 letI:=polynomialRationalScalarTower Omega C.1 i0 htr
 letI:=rationalBaseScalarTower Omega C.1 i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).1
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).2
 intro v
 by_cases hv:v∈componentRelevantPlacesAdaptive hproj C
 · have havoid:=hc (Sum.inr ⟨C,⟨v,hv⟩⟩)
   change ¬(v.val (coefficientEvaluation (coordinate Omega C.1) E c) <
     WithZero.exp (exponentSetPoleWeight v.val (coordinate Omega C.1) E)) at havoid
   have hlower:WithZero.exp
       (exponentSetPoleWeight v.val (coordinate Omega C.1) E) ≤
       v.val (coefficientEvaluation (coordinate Omega C.1) E c):=
     le_of_not_gt havoid
   have hupper:v.val (coefficientEvaluation (coordinate Omega C.1) E c) ≤
       WithZero.exp (exponentSetPoleWeight v.val (coordinate Omega C.1) E):=
     valuation_eval_le_exp_exponentSet v.val (algebraMap Omega _)
       (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v a)
       (coordinate Omega C.1) E B hsupport
   exact poleOrder_eq_of_valuation_eq_exp v.val _ _
     (ContactLeadingCancellationResearch.exponentSetPoleWeight_nonneg
       v.val (coordinate Omega C.1) E)
     (le_antisymm hupper hlower)
 · have hweight:exponentSetPoleWeight v.val (coordinate Omega C.1) E=0:=
     exponentSetPoleWeight_eq_zero_of_not_mem_adaptive hproj E C v hv
   have hle:poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B) ≤
       exponentSetPoleWeight v.val (coordinate Omega C.1) E:=
     (poleOrder_eval_le_support v.val (algebraMap Omega _)
       (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v a)
       (coordinate Omega C.1) B).trans
     (supportPoleWeight_le_exponentSetPoleWeight v.val
       (coordinate Omega C.1) B E hsupport)
   rw [hweight] at hle ⊢
   exact le_antisymm hle (by unfold poleOrder;exact le_max_left _ _)
def AdaptiveGenericExactPolePolynomial.toResidualComponentBudget
   {E:Finset (Fin 3 →₀ ℕ)} {wholeCost:ℕ}
   {hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   (B:AdaptiveGenericExactPolePolynomial G T H E hproj)
   (cost:RegularComponent Omega G T H → ℕ)
   (cycle_le:forall C:RegularComponent Omega G T H,
     let i0:=componentSeparator C
     let htr:=componentSeparator_transcendental C
     letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
       quotientPolynomialAlgebra Omega C.1 i0
     letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
       polynomialBaseAlgebra Omega C.1 i0
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       rationalBaseAlgebra Omega C.1 i0 htr
     letI:=quotientBaseScalarTower Omega C.1 i0
     letI:=polynomialBaseScalarTower Omega C.1 i0
     letI:=quotientFractionScalarTower Omega C.1 i0
     letI:=polynomialRationalScalarTower Omega C.1 i0 htr
     letI:=rationalBaseScalarTower Omega C.1 i0 htr
     letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
       (hproj C i0 htr).1
     letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
       (hproj C i0 htr).2
     let b:=MvPolynomial.eval₂Hom
       (algebraMap Omega (CoordinateField Omega C.1))
       (coordinate Omega C.1) B.polynomial
     let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
       C.1 B.polynomial (B.proper C)
     (∑ v∈CommonPlaceBalance.placesFor Omega
         (CoordinateField Omega C.1) b hb,
       CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v b) ≤
         (cost C:ℤ))
   (sum_cost_le:(∑ C:RegularComponent Omega G T H,cost C) ≤ wholeCost):
   ResidualComponentBudget G T H (fun A => A.support ⊆ E) wholeCost where
 cost:=cost
 sum_cost_le:=sum_cost_le
 zero_le:=by
   intro C A hAE hproper points hpointsP hpointsA
   let i0:=componentSeparator C
   let htr:=componentSeparator_transcendental C
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 i0 htr
   letI:=quotientBaseScalarTower Omega C.1 i0
   letI:=polynomialBaseScalarTower Omega C.1 i0
   letI:=quotientFractionScalarTower Omega C.1 i0
   letI:=polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).1
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   have hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   have hpole:forall W:Finset (Place Omega (CoordinateField Omega C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1) E) ≤
         (cost C:ℤ):=fun W =>
     (support_sum_le_principal_poleMass_of_exact
       (K:=Omega) (L:=CoordinateField Omega C.1)
       (coordinate Omega C.1) E b hb (B.exact_pole C) W).trans
         (cycle_le C)
   exact finite_zero_points_le_exponentSet_of_separator C.1 (hproj C)
     i0 htr E (cost C) hpole A hAE hproper points hpointsP hpointsA
end
end ProximityPrize.SubmissionLower.ContactAdaptiveComponentSeparatorResearch
