import ProximityPrize.SubmissionLower.Part.F006_07
section Compact_PackedLegacy
section PackedLegacy_A0
namespace ProximityPrize.SubmissionLower.RCN029
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN125 RCN031 RCN106 RCN111 RCN112
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (multiplicity:RegularComponent Omega G T H → ℕ)

def ActiveNestedZFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (a₀:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q),
   q^(∑ a:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q,
     multiplicity a.1.1*indexedPlaneResidueWeight
       (activeNestedZComponent (G:=G) (T:=T) (H:=H))
       D.lam D.mu (D.mu*D.lam) zOrder
       (activeNestedZTranscendental base hactive hSderiv D)
       (activeNestedZFinite base hactive hZ hSderiv D) a.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T
def ActiveNestedUFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) uOrder
       (activeNestedUTranscendental base hactive hSderiv D)
       (activeNestedUFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T
def ActiveNestedVFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) vOrder
       (activeNestedVTranscendental base hactive hSderiv D)
       (activeNestedVFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T
structure ActiveNestedFixedPowers:Prop where
 z:ActiveNestedZFixedPowers base hactive hZ hSderiv D multiplicity
 u:ActiveNestedUFixedPowers base hactive hSderiv D multiplicity
 v:ActiveNestedVFixedPowers base hactive hSderiv D multiplicity
end
end ProximityPrize.SubmissionLower.RCN029
end PackedLegacy_A0

/-! Packed from ProximityPrize.SubmissionLower.P8. -/
section PackedLegacy_P8
namespace ProximityPrize.SubmissionLower.RCN331
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN243 RCN264 RCN095 RCN066 RCN336 RCN333 RCN029 RCN031 RCN037 RCN038 RCN341 RCN117 RCN125 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem reducedStage_activeFixedPowers
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1) - Tred)
   (base:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 0) ≠ 0 ∨
       KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 2) ≠ 0)
   (hZ:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) S.G ≠ 0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv) :
   ActiveNestedFixedPowers base hactive hZ hSderiv D
     (transportedMultiplicity hd
       (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))):=by
 refine { z:=?_, u:=?_, v:=?_ }
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (activeNestedZComponent (G:=S.G) (T:=Tred)
       (H:=regularitySurface (polynomialEmbedding K) S.F))
     activeNestedZComponent_injective D.lam D.mu (D.mu * D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D)
     (activeNestedZFinite base hactive hZ hSderiv D)
     (activeNestedZGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).2
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D)
     (activeNestedUFinite base hactive hSderiv D)
     (activeNestedUGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).1
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D)
     (activeNestedVFinite base hactive hSderiv D)
     (activeNestedVGenerates base hactive hSderiv D)
     (flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional)
     q hq hqMonic a0
end
end ProximityPrize.SubmissionLower.RCN331
end PackedLegacy_P8

/-! Packed from ProximityPrize.SubmissionLower.DJ. -/
section PackedLegacy_DJ
namespace ProximityPrize.SubmissionLower.RCN030
open RCN002 RCN264 RCN341 RCN042 RCN344 RCN037 RCN038 RCN040 RCN046 RCN237 RCN095 RCN093 RCN125 RCN116 RCN022 RCN031
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
noncomputable def activeNestedUnitFamily:
   AdaptiveUnitProjectionFamily base surfaceFlag tailFlag:=
 adaptiveUnitProjectionFamily_of_active_nested surfaceFlag tailFlag base hactive
   hZ hSderiv D hG hproper hGsupport hTsupport
theorem activeNestedUnitFamily_zCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=rfl
theorem activeNestedUnitFamily_uCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)):=rfl
theorem activeNestedUnitFamily_allCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (Sum.inr {
         embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
           (affineV Omega C.1 D.mu (D.mu*D.lam))
             (D.allAffineTranscendental C)
         finite:=D.allFinite C
         separable:=D.allSeparable C}):=rfl
theorem activeNestedUnitFamily_zCost_eq_flagCost
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost a.1=
     coordinateDegree Omega (CoordinateField Omega a.1.1)
       (coordinateOfGate
         (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (zOrder 0)))
         (activeNestedZGate base hactive hZ hSderiv D a)):=by
 rw [activeNestedUnitFamily_zCost]
 rw [coordinateOfGate_degree_of_transcendental _ _ a.2]
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedZTranscendental base hactive hSderiv D a)]
 rw [elementEmbedding_congr
   (activeNestedZTranscendental base hactive hSderiv D a) a.2
   (by simp [zOrder,flagEvaluation_X_two])]
theorem activeNestedUnitFamily_uCost_eq_flagCost
   (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate
         (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (uOrder 0)))
         (activeNestedUGate base hactive hSderiv D C)):=by
 rw [activeNestedUnitFamily_uCost]
 rw [coordinateOfGate_degree_of_transcendental _ _ (D.uTranscendental C)]
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedUTranscendental base hactive hSderiv D C)]
 rw [elementEmbedding_congr
   (activeNestedUTranscendental base hactive hSderiv D C)
   (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])]
theorem activeNestedUnitFamily_allCost_eq_flagCost
   (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate
         (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (vOrder 0)))
         (activeNestedVGate base hactive hSderiv D C)):=by
 rw [activeNestedUnitFamily_allCost]
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
         (D.allAffineTranscendental C)).toRingHom.toAlgebra;
   Module.finrank (RatFunc Omega) (CoordinateField Omega C.1))=_
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedVTranscendental base hactive hSderiv D C)]
 rw [elementEmbedding_congr
   (activeNestedVTranscendental base hactive hSderiv D C)
   (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])]
end
end ProximityPrize.SubmissionLower.RCN030
end PackedLegacy_DJ

/-! Packed from ProximityPrize.SubmissionLower.K2. -/
section PackedLegacy_K2
namespace ProximityPrize.SubmissionLower.RCN105
open RCN002 RCN011 RCN264 RCN093 RCN120 RCN042 RCN344 RCN106 RCN111 RCN226 RCN113 RCN021 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type}
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
theorem indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (a:A):
   coordinateDegree Omega (CoordinateField Omega (component a).1)
     (coordinateOfGate
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0)))
       (hgate a))=
     (indexedComponentFactor component lam mu nu order ht a).natDegree*
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
 rw [coordinateOfGate_degree_of_transcendental _ (hgate a) (ht a)]
 let F:=RatFunc Omega
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Algebra F L:=flagBaseAlgebra Omega (component a).1
   lam mu nu order (ht a)
 letI:FiniteDimensional F L:=hfinite a
 letI:J.IsMaximal:=relationKernel_isMaximal Omega L order e (ht a)
   (hfinite a) (hgen a)
 let aResidue:=residueAlgebra q J
   (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 have hq:Irreducible q:=projectedFactor_irreducible Omega L order e
   (ht a) (hfinite a)
 let phi:PlaneRing Omega →ₐ[F] L:={
   toRingHom:=planeEvaluation Omega L order e (ht a)
   commutes':=fun c => by
     change planeEvaluation Omega L order e (ht a)
       (Polynomial.C (Polynomial.C c))=algebraMap F L c
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) (hgen a)
 let eqv:(PlaneRing Omega ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing Omega ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 have hquot:Module.finrank F (PlaneRing Omega ⧸ J)=
     Module.finrank F L:=eqv.toLinearEquiv.finrank_eq
 change Module.finrank F L=q.natDegree*
   indexedPlaneResidueWeight component lam mu nu order ht hfinite a
 rw [show indexedPlaneResidueWeight component lam mu nu order ht hfinite a=
     Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J) by rfl]
 calc
   Module.finrank F L=Module.finrank F (PlaneRing Omega ⧸ J):=hquot.symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J):=
     quotient_finrank_eq_natDegree_mul_residue_finrank q hq J
       (relationKernel_comap_C Omega L order e (ht a))
end
end ProximityPrize.SubmissionLower.RCN105
end PackedLegacy_K2

/-! Packed from ProximityPrize.SubmissionLower.AN. -/
section PackedLegacy_AN
namespace ProximityPrize.SubmissionLower.RCN343
open scoped Classical BigOperators
open RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Base:Type} [Field Base] [DecidableEq Base]
structure WeightedGroupedResultantChannel
   {I:Type*} [Fintype I]
   (multiplicity cost:I → ℕ) (budget:ℕ) where
 resultant:Polynomial Base
 factor:I → Polynomial Base
 residueWeight:I → ℕ
 resultant_ne:resultant≠0
 factor_irreducible:∀ i,Irreducible (factor i)
 factor_monic:∀ i,(factor i).Monic
 groupedPowerDvd:∀ f∈Finset.univ.image factor,
   f^(∑ i with factor i=f,multiplicity i*residueWeight i)∣resultant
 cost_le_residue_mul_degree:∀ i,
   cost i ≤ residueWeight i*(factor i).natDegree
 resultant_degree_le:resultant.natDegree ≤ budget
theorem WeightedGroupedResultantChannel.sum_mul_cost_le
   {I:Type*} [Fintype I]
   {multiplicity cost:I → ℕ} {budget:ℕ}
   (C:WeightedGroupedResultantChannel
     (Base:=Base) multiplicity cost budget):
   (∑ i,multiplicity i*cost i) ≤ budget:=by
 let weightedMultiplicity:I → ℕ:=fun i↦
   multiplicity i*C.residueWeight i
 have hfactor:=sum_grouped_power_factor_degrees_le
   C.resultant C.factor weightedMultiplicity C.resultant_ne
     C.factor_irreducible C.factor_monic C.groupedPowerDvd
 calc
   (∑ i,multiplicity i*cost i) ≤
       ∑ i,multiplicity i*
         (C.residueWeight i*(C.factor i).natDegree):=
     Finset.sum_le_sum (fun i _↦
       Nat.mul_le_mul_left (multiplicity i)
         (C.cost_le_residue_mul_degree i))
   _=∑ i,weightedMultiplicity i*(C.factor i).natDegree:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [weightedMultiplicity,Nat.mul_assoc]
   _ ≤ C.resultant.natDegree:=hfactor
   _ ≤ budget:=C.resultant_degree_le
end
end ProximityPrize.SubmissionLower.RCN343
end PackedLegacy_AN

/-! Packed from ProximityPrize.SubmissionLower.K1. -/
section PackedLegacy_K1
namespace ProximityPrize.SubmissionLower.RCN104
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN106 RCN111 RCN105 RCN120 RCN226 RCN042 RCN344 RCN343
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
noncomputable def indexedWeightedFlagPlaneChannel_of_fixedFactors
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (multiplicity:A → ℕ)
   (resultant:Polynomial (RatFunc Omega)) (budget:ℕ)
   (hresultant:resultant≠0)
   (hdegree:resultant.natDegree ≤ budget)
   (hfixed:∀ (q:Polynomial (RatFunc Omega))
     (hq:Irreducible q) (hqMonic:q.Monic)
     (a₀:IndexedFactorFiber component lam mu nu order ht q),
     q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
       multiplicity a.1*indexedPlaneResidueWeight component
         lam mu nu order ht hfinite a.1)∣resultant):
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     (fun a↦coordinateDegree Omega (CoordinateField Omega (component a).1)
       (coordinateOfGate
         (flagEvaluation Omega (component a).1 lam mu nu
           (MvPolynomial.X (order 0))) (hgate a))) budget:=by
 let factor:=indexedComponentFactor component lam mu nu order ht
 let weight:=indexedPlaneResidueWeight component lam mu nu order ht hfinite
 refine {
   resultant:=resultant
   factor:=factor
   residueWeight:=weight
   resultant_ne:=hresultant
   factor_irreducible:=?_
   factor_monic:=?_
   groupedPowerDvd:=?_
   cost_le_residue_mul_degree:=?_
   resultant_degree_le:=hdegree}
 · intro a
   exact projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro a
   exact projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro q hqmem
   obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hqmem
   subst q
   have hqirr:Irreducible (factor a):=projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hqmonic:(factor a).Monic:=projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   let a₀:IndexedFactorFiber component lam mu nu order ht (factor a):=⟨a,rfl⟩
   have hpow:=hfixed (factor a) hqirr hqmonic a₀
   have hsum:
       (∑ b with factor b=factor a,multiplicity b*weight b)=
         ∑ b:IndexedFactorFiber component lam mu nu order ht (factor a),
           multiplicity b.1*weight b.1:=by
     simpa only [Finset.subtype_univ,eq_comm] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset A))
         (fun b↦multiplicity b*weight b)
         (p:=fun b↦factor a=factor b)).symm
   rw [hsum]
   exact hpow
 · intro a
   have hcost:=indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
     component lam mu nu order ht hfinite hgen hgate a
   simpa only [factor,weight,Nat.mul_comm] using hcost.le
end
end ProximityPrize.SubmissionLower.RCN104
end PackedLegacy_K1

/-! Packed from ProximityPrize.SubmissionLower.Q9. -/
section PackedLegacy_Q9
namespace ProximityPrize.SubmissionLower.RCN342
open scoped Classical BigOperators
open RCN343
noncomputable section
set_option autoImplicit false
variable {Base:Type} [Field Base] [DecidableEq Base]
noncomputable def recost
   {I:Type*} [Fintype I] {multiplicity oldCost newCost:I → ℕ}
   {budget:ℕ}
   (C:WeightedGroupedResultantChannel (Base:=Base)
     multiplicity oldCost budget)
   (hcost:∀ i,newCost i ≤ oldCost i):
   WeightedGroupedResultantChannel (Base:=Base)
     multiplicity newCost budget where
 resultant:=C.resultant
 factor:=C.factor
 residueWeight:=C.residueWeight
 resultant_ne:=C.resultant_ne
 factor_irreducible:=C.factor_irreducible
 factor_monic:=C.factor_monic
 groupedPowerDvd:=C.groupedPowerDvd
 cost_le_residue_mul_degree i:=(hcost i).trans (C.cost_le_residue_mul_degree i)
 resultant_degree_le:=C.resultant_degree_le
noncomputable def emptyChannel
   {I:Type*} [Fintype I] [IsEmpty I]
   (multiplicity cost:I → ℕ) (budget:ℕ):
   WeightedGroupedResultantChannel (Base:=Base) multiplicity cost budget where
 resultant:=1
 factor i:=isEmptyElim i
 residueWeight i:=isEmptyElim i
 resultant_ne:=one_ne_zero
 factor_irreducible i:=isEmptyElim i
 factor_monic i:=isEmptyElim i
 groupedPowerDvd f hf:=by simp at hf
 cost_le_residue_mul_degree i:=isEmptyElim i
 resultant_degree_le:=by simp
end
end ProximityPrize.SubmissionLower.RCN342
end PackedLegacy_Q9

/-! Packed from ProximityPrize.SubmissionLower.DI. -/
section PackedLegacy_DI
namespace ProximityPrize.SubmissionLower.RCN028
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN095 RCN125 RCN117 RCN031 RCN030 RCN029 RCN112 RCN104 RCN343 RCN342
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
 (multiplicity:RegularComponent Omega G T H → ℕ)
 (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedZChannel
   [Nonempty (ActiveNestedZIndex (G:=G) (T:=T) (H:=H))]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)↦multiplicity a.1)
     (fun a↦U.toPrimeFlagBudgetFamily.zCost a.1)
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let a₀:ActiveNestedZIndex (G:=G) (T:=T) (H:=H):=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) zOrder
   hG hproper a₀.1 (activeNestedZTranscendental base hactive hSderiv D a₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
 have hdeg:=flagPlaneResultant_z_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (activeNestedZComponent (G:=G) (T:=T) (H:=H))
   D.lam D.mu (D.mu*D.lam) zOrder
   (activeNestedZTranscendental base hactive hSderiv D)
   (activeNestedZFinite base hactive hZ hSderiv D)
   (activeNestedZGenerates base hactive hSderiv D)
   (activeNestedZGate base hactive hZ hSderiv D)
   (fun a↦multiplicity a.1)
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T)
   (flagMixed surfaceFlag tailFlag unitZFlag) hres hdeg powers.z
 exact recost raw fun a↦
   (activeNestedUnitFamily_zCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport a).le
noncomputable def activeNestedUChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.yzCost
     (flagMixed surfaceFlag tailFlag unitYZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) uOrder
   hG hproper C₀ (activeNestedUTranscendental base hactive hSderiv D C₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
 have hdeg:=flagPlaneResultant_u_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) uOrder
   (activeNestedUTranscendental base hactive hSderiv D)
   (activeNestedUFinite base hactive hSderiv D)
   (activeNestedUGenerates base hactive hSderiv D)
   (activeNestedUGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T)
   (flagMixed surfaceFlag tailFlag unitYZFlag) hres hdeg powers.u
 exact recost raw fun C↦
   (activeNestedUnitFamily_uCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
noncomputable def activeNestedVChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.allCost
     (flagMixed surfaceFlag tailFlag unitAllFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) vOrder
   hG hproper C₀ (activeNestedVTranscendental base hactive hSderiv D C₀)
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
 have hdeg:=flagPlaneResultant_v_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) vOrder
   (activeNestedVTranscendental base hactive hSderiv D)
   (activeNestedVFinite base hactive hSderiv D)
   (activeNestedVGenerates base hactive hSderiv D)
   (activeNestedVGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T)
   (flagMixed surfaceFlag tailFlag unitAllFlag) hres hdeg powers.v
 exact recost raw fun C↦
   (activeNestedUnitFamily_allCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
end
end ProximityPrize.SubmissionLower.RCN028
end PackedLegacy_DI

/-! Packed from ProximityPrize.SubmissionLower.DK. -/
section PackedLegacy_DK
namespace ProximityPrize.SubmissionLower.RCN032
open scoped Classical BigOperators
open RCN042 RCN344 RCN022
noncomputable section
set_option autoImplicit false
theorem sum_mul_eq_active_subtype
   {I:Type*} [Fintype I]
   (active:I → Prop) [DecidablePred active]
   (multiplicity cost:I → ℕ)
   (hzero:∀ i,¬ active i → cost i=0):
   (∑ i,multiplicity i*cost i)=
     ∑ i:{i//active i},multiplicity i.1*cost i.1:=by
 let f:I → ℕ:=fun i↦multiplicity i*cost i
 calc
   (∑ i,multiplicity i*cost i)=
       ∑ i∈(Finset.univ.filter active),f i:=by
     symm
     apply Finset.sum_subset (Finset.filter_subset active Finset.univ)
     intro i _ hi
     have hnot:¬ active i:=by simpa using hi
     simp [f,hzero i hnot]
   _=∑ i:{i//active i},multiplicity i.1*cost i.1:=by
     simpa only [f,Finset.subtype_univ] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset I)) f (p:=active)).symm
theorem sum_mul_coordinateOfGate_eq_active
   {K:Type} [Field K] [IsAlgClosed K]
   {I:Type*} [Fintype I]
   (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   (x:∀ i,E i)
   (hgate:∀ i,∀ hx:Transcendental K (x i),
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) (E i))∧
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) (E i)))
   (multiplicity:I → ℕ):
   (∑ i,multiplicity i*coordinateDegree K (E i)
     (coordinateOfGate (K:=K) (L:=E i) (x i) (hgate i)))=
   ∑ i:{i//Transcendental K (x i)},
     multiplicity i.1*coordinateDegree K (E i.1)
       (coordinateOfGate (K:=K) (L:=E i.1) (x i.1) (hgate i.1)):=by
 classical
 apply sum_mul_eq_active_subtype
 intro i hi
 change ¬¬ IsAlgebraic K (x i) at hi
 exact coordinateOfGate_degree_of_isAlgebraic
   (K:=K) (L:=E i) (x i) (hgate i) (not_not.mp hi)
end
end ProximityPrize.SubmissionLower.RCN032
end PackedLegacy_DK

/-! Packed from ProximityPrize.SubmissionLower.DL. -/
section PackedLegacy_DL
namespace ProximityPrize.SubmissionLower.RCN033
open scoped Classical BigOperators
open RCN264 RCN095 RCN237 RCN343 RCN338
noncomputable section
set_option autoImplicit false
variable {Base Omega:Type} [Field Base] [Field Omega]
local instance:DecidableEq Base:=Classical.decEq Base
variable {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag:FlagDegree}
theorem regularComponentWeightedInertiaCertificate_of_active_channels
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   {zIndex uIndex:Type*} [Fintype zIndex] [Fintype uIndex]
   (zComponent:zIndex → RegularComponent Omega G T H)
   (uComponent:uIndex → RegularComponent Omega G T H)
   (zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a))
   (uRewrite:(∑ C,multiplicity C*B.yzCost C)=
     ∑ a:uIndex,multiplicity (uComponent a)*B.yzCost (uComponent a))
   (zChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag firstTailFlag unitZFlag))
   (uChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (uComponent a))
     (fun a↦B.yzCost (uComponent a))
     (flagMixed surfaceFlag firstTailFlag unitYZFlag))
   (allChannel:WeightedGroupedResultantChannel (Base:=Base) multiplicity
     B.allCost (flagMixed surfaceFlag firstTailFlag unitAllFlag)):
   RegularComponentWeightedInertiaResultantCertificate B multiplicity where
 z:=by
   rw [zRewrite]
   exact zChannel.sum_mul_cost_le
 yz:=by
   rw [uRewrite]
   exact uChannel.sum_mul_cost_le
 all:=allChannel.sum_mul_cost_le
end
end ProximityPrize.SubmissionLower.RCN033
end PackedLegacy_DL

/-! Packed from ProximityPrize.SubmissionLower.DH. -/
section PackedLegacy_DH
namespace ProximityPrize.SubmissionLower.RCN027
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN042 RCN344 RCN037 RCN038 RCN095 RCN031 RCN030 RCN029 RCN028 RCN032 RCN033 RCN343 RCN342 RCN338
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
 (multiplicity:RegularComponent Omega G T H → ℕ)
 (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedWeightedCertificate:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   RegularComponentWeightedInertiaResultantCertificate
     U.toPrimeFlagBudgetFamily multiplicity:=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let B:=U.toPrimeFlagBudgetFamily
 let zIndex:=ActiveNestedZIndex (G:=G) (T:=T) (H:=H)
 let zComponent:=activeNestedZComponent (G:=G) (T:=T) (H:=H)
 let zChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:zIndex↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
   by_cases hz:Nonempty zIndex
   · letI:Nonempty zIndex:=hz
     exact activeNestedZChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty zIndex:=⟨fun a↦hz ⟨a⟩⟩
     exact emptyChannel _ _ _
 let uChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.yzCost (flagMixed surfaceFlag tailFlag unitYZFlag):=by
   by_cases hu:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hu
     exact activeNestedUChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hu ⟨C⟩⟩
     exact emptyChannel _ _ _
 let allChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.allCost (flagMixed surfaceFlag tailFlag unitAllFlag):=by
   by_cases hv:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hv
     exact activeNestedVChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hv ⟨C⟩⟩
     exact emptyChannel _ _ _
 have zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a):=by
   calc
     _=∑ C,multiplicity C*coordinateDegree Omega
         (CoordinateField Omega C.1)
         (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
     _=∑ a:zIndex,multiplicity a.1*coordinateDegree Omega
         (CoordinateField Omega a.1.1)
         (coordinateOfGate (coordinate Omega a.1.1 2) (hZ a.1)):=
       sum_mul_coordinateOfGate_eq_active
         (fun C:RegularComponent Omega G T H↦CoordinateField Omega C.1)
         (fun C↦coordinate Omega C.1 2) hZ multiplicity
     _=_:=by
       apply Finset.sum_congr rfl
       intro a _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
       rfl
 exact regularComponentWeightedInertiaCertificate_of_active_channels B
   multiplicity zComponent (fun C:RegularComponent Omega G T H↦C)
   zRewrite rfl zChannel uChannel allChannel
end
end ProximityPrize.SubmissionLower.RCN027
end PackedLegacy_DH

/-! Packed from ProximityPrize.SubmissionLower.Q1. -/
section PackedLegacy_Q1
namespace ProximityPrize.SubmissionLower.RCN334
open scoped Classical BigOperators
open RCN135 RCN136 RCN319 RCN174 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN090 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN037 RCN038 RCN042 RCN341 RCN312 RCN339 RCN330 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
 {tightSupport:ResidualSupportParameters}
def loosenStageGeneral
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport) :
   Stage K I Gamma x p flag stageErrorCap tightSupport:=S
theorem loosenStageGeneral_one_le_localMultiplicity
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ∀ C, 1 ≤ localMultiplicity (loosenStageGeneral S)
     (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C:=by
 exact one_le_localMultiplicity (loosenStageGeneral S) hfirstProper
def loosenStage
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hs:tightSupport.s ≤ fixedSupport.s)
   (hys:tightSupport.ys ≤ fixedSupport.ys)
   (htotal:tightSupport.total ≤ fixedSupport.total) :
   Stage K I Gamma x p flag stageErrorCap fixedSupport :=
 { S with
   surface_s_weight:=S.surface_s_weight.trans hs
   surface_ys_weight:=S.surface_ys_weight.trans hys
   surface_total_weight:=S.surface_total_weight.trans htotal }
theorem laterTail_in_reduced_delay_secondFlag
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (C:FirstTailComponent S) (delay:ℕ) (hdelay:1 ≤ delay) :
   PolynomialInFlagMod C.1
     (delay • reducedResidualAgreementFlag tightSupport (w + 2))
     (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)):=by
 let d:=w + 1 + delay
 let Tred:=reducedGlobalTailCut (polynomialEmbedding K) tightSupport S.F d
 let Hsupport:ResidualSupportData tightSupport S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hred:PolynomialInFlag (reducedResidualAgreementFlag tightSupport d) Tred :=
   reducedGlobalTailCut_in_flag (polynomialEmbedding K) tightSupport Hsupport d
 have hflag:PolynomialInFlag
     (delay • reducedResidualAgreementFlag tightSupport (w + 2)) Tred:=by
   have hscale:d ≤ delay * (w + 2):=by
     dsimp only [d]
     norm_num [w]
     omega
   have hallFlag:(reducedResidualAgreementFlag tightSupport d).all ≤
       (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     simp only [reducedResidualAgreementFlag, reducedAgreementDirection, nsmul_all]
     calc
       (2 * tightSupport.s - 2) * d ≤
           (2 * tightSupport.s - 2) * (delay * (w + 2)) :=
         Nat.mul_le_mul_left _ hscale
       _ = delay * ((2 * tightSupport.s - 2) * (w + 2)):=by ring
   have hysFlag :
       (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_ys]
     simp only [nsmul_yz, nsmul_all]
     rw [← Nat.mul_add]
     rw [reducedResidualAgreementFlag_ys]
     calc
       1 + d * (2 * tightSupport.ys - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.ys - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.ys - 2)):=by ring
   have htotalFlag :
       (reducedResidualAgreementFlag tightSupport d).zOnly +
           (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).zOnly +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_total]
     simp only [nsmul_zOnly, nsmul_yz, nsmul_all]
     rw [← Nat.mul_add, ← Nat.mul_add]
     rw [reducedResidualAgreementFlag_total]
     calc
       1 + d * (2 * tightSupport.total - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.total - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.total - 2)):=by ring
   intro exponent hexponent
   have h:=hred exponent hexponent
   exact ⟨h.1.trans hallFlag, h.2.1.trans hysFlag, h.2.2.trans htotalFlag⟩
 refine ⟨Tred, hflag, ?_⟩
 have hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F d - Tred :=
   S.G_dvd_surface.trans
     (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) tightSupport S.F d)
 exact C.1.mem_of_dvd hd
   (regularComponent_G_mem (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F) C)
structure ReducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) where
 base:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   SeparableLiteralCoordinate C.1
 hactive:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 0) ≠ 0 ∨
     KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 2) ≠ 0
 hZ:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F), LiteralProjectionGate C 2
 data:AdaptiveNestedProjectionDataActive base hactive
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
theorem exists_reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   Nonempty (ReducedActiveGeometry S):=by
 obtain ⟨base, hactive, hZ, ⟨D⟩⟩ :=
   exists_reduced_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
 exact ⟨⟨base, hactive, hZ, D⟩⟩
noncomputable def reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   ReducedActiveGeometry S :=
 Classical.choice (exists_reducedActiveGeometry S hfirstProper hflagChar hmixed)
theorem loosenStageGeneral_dichotomy_with_tangent
   {tailFlag1:FlagDegree}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent:∀ C:FirstTailComponent S,
     (∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) →
     (componentSeeds (GenericField K) S.G
       (globalTailCut (polynomialEmbedding K) S.F (w + 1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C) :
   ∀ C:FirstTailComponent S,
     (∃ delay, 1 ≤ delay ∧
       delay ≤ localMultiplicity (loosenStageGeneral S)
         (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C ∧
       globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1) ∨
     ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1) ∧
       (componentSeeds (GenericField K) S.G
         (globalTailCut (polynomialEmbedding K) S.F (w + 1))
         (regularitySurface (polynomialEmbedding K) S.F) Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
           (stageErrorCap + 1) * B.yzCost C):=by
 intro C
 have dichotomy:=local_order_tail_dichotomy (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall, htangent C hall⟩
end
end ProximityPrize.SubmissionLower.RCN334
end PackedLegacy_Q1

/-! Packed from ProximityPrize.SubmissionLower.P9. -/
section PackedLegacy_P9
namespace ProximityPrize.SubmissionLower.RCN332
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
def reducedFirstCut
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)):MvPolynomial (Fin 3) (GenericField K) :=
 reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1)
theorem ordinary_sub_reducedFirstCut_dvd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) -
     reducedFirstCut S :=
 S.G_dvd_surface.trans
   (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) (support a b s)
     S.F (w + 1))
theorem reducedFirstCut_proper
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ¬ S.G ∣ reducedFirstCut S:=by
 intro hr
 apply hfirstProper
 have h:=(ordinary_sub_reducedFirstCut_dvd S).add hr
 simpa only [reducedFirstCut, sub_add_cancel] using h
theorem reducedFirstCut_in_flag
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   PolynomialInFlag (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S):=by
 exact reducedGlobalTailCut_in_flag (polynomialEmbedding K) (support a b s)
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩ (w + 1)
noncomputable def reducedUnitFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 activeNestedUnitFamily A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
noncomputable def reducedMultiplicity
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStage S hs hys htotal)
   (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
noncomputable def reducedBudgetFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
noncomputable def reducedBaseOrd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S):SeparableLiteralCoordinate C.1:=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 exact (reducedActiveGeometry S hfirstProper hflagChar hmixed).base C'
theorem reducedBudgetFamily_yzPositive
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S) :
   1 ≤ (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C:=by
 let hd:=ordinary_sub_reducedFirstCut_dvd S
 let C':=regularComponentEquiv hd C
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 let U:=reducedUnitFamily S hfirstProper hflagChar hmixed
 change 1 ≤ U.toPrimeFlagBudgetFamily.yzCost C'
 change 1 ≤ coordinateDegree (GenericField K)
   (CoordinateField (GenericField K) C'.1) (U.yzProjection C')
 apply one_le_coordinateDegree_of_transcendental_value
 have hproj:U.yzProjection C' = coordinateOfGate
     (RCN093.affineU
       (GenericField K) C'.1 A.data.lam) (A.data.uGate C'):=rfl
 rw [hproj, coordinateOfGate_value]
 exact A.data.uTranscendental C'
theorem reducedBudgetFamily_yzPole
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S) :
   LiteralSupportPoleBound
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     (flagSupport unitYZFlag)
     ((reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C):=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 have heq:regularComponentEquiv (ordinary_sub_reducedFirstCut_dvd S) C = C':=by
   apply Subtype.ext
   rfl
 rw [show (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C =
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C' by
   simp only [reducedBudgetFamily, PrimeFlagBudgetFamily.ofCongruentCut, heq]]
 change LiteralSupportPoleBound
   ((reducedActiveGeometry S hfirstProper hflagChar hmixed).base C')
   (flagSupport unitYZFlag)
   ((reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C')
 exact (reducedUnitFamily S hfirstProper hflagChar hmixed).toAdaptiveUnitPoleBudget.yzPole C'
noncomputable def reducedMultiplicityGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
theorem reducedFixedPowersGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStageGeneral S)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicityGeneral S hfirstProper))
   (reducedFixedPowersGeneral S hfirstProper hflagChar hmixed)
theorem transportedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicityGeneral S hfirstProper)
   (reducedWeightedResultantsGeneral S hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.RCN332
end PackedLegacy_P9

/-! Packed from ProximityPrize.SubmissionLower.Q2. -/
section PackedLegacy_Q2
namespace ProximityPrize.SubmissionLower.RCN335
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
theorem exists_delayedTailMultiplicityProvider_of_reducedGeneral
   {a b s:ℕ}
   (agreementCap:ℕ)
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card = agreementCap + stageErrorCap)
   (hagreement:∀ gamma ∈ Gamma, agreementCap ≤ (S.agreementFiber gamma).card)
   (hwa:w < agreementCap)
   (hshort:w + 1 ≤ bound) (hchar:bound < p)
   (hbox:S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate:stageErrorCap + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2:=reducedResidualAgreementFlag (support a b s) (w + 2)) S):=by
 classical
 let supp:=support a b s
 let S0:=loosenStageGeneral S
 let T:=globalTailCut (polynomialEmbedding K) S.F (w + 1)
 let H:=regularitySurface (polynomialEmbedding K) S.F
 let secondFlag:=reducedResidualAgreementFlag supp (w + 2)
 let B:=reducedBudgetFamily S hfirstProper hflagChar hmixed
 let multiplicity:=reducedMultiplicityGeneral S hfirstProper
 have hone:∀ C, 1 ≤ multiplicity C:=by
   exact loosenStageGeneral_one_le_localMultiplicity S hfirstProper
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) :
     (componentSeeds (GenericField K) S.G T H Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     agreementCap bound seedCap slopeCap hnodes hagreement
     hwa (by norm_num [w])
     hshort hchar hbox B
     (reducedBudgetFamily_yzPositive S hfirstProper hflagChar hmixed C)
     hall (reducedBudgetFamily_yzPole S hfirstProper hflagChar hmixed C)
 have branchBound (C:FirstTailComponent S) :
     ((∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
         globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1 ∧
         (componentSeeds (GenericField K) S.G T H Gamma
           (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
             multiplicity C * B.weightedCost secondFlag C) ∨
       (∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1)):=by
   have dichotomy:=local_order_tail_dichotomy S0
     (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
   rcases dichotomy.2 with hproper | htangent
   · left
     obtain ⟨delay, hdelay, hdelayMu, htail⟩:=hproper
     have hzero:∀ gamma ∈ componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C,
         MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)
           (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0:=by
       intro gamma hgamma
       have hGamma:=componentSeeds_subset (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
       exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected
         gamma w (w + 1 + delay) (S.degree_le gamma hGamma)
         (S.solution gamma hGamma) (by omega)
     have hcount:=component_secondTail_card_le_mod B C Gamma
       (selectedPoint (polynomialEmbedding K) S.selected)
       (selectedPoint_injective (polynomialEmbedding K) S.selected)
       (laterTail_in_reduced_delay_secondFlag S C delay hdelay) htail hzero
     have hscale:B.weightedCost (delay • secondFlag) C =
         delay * B.weightedCost secondFlag C:=by
       simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
         nsmul_all]
       ring
     rw [hscale] at hcount
     exact ⟨delay, hdelay, hdelayMu, htail,
       hcount.trans (Nat.mul_le_mul_right (B.weightedCost secondFlag C) hdelayMu)⟩
   · exact Or.inr htangent
 have providerDichotomy :=
   loosenStageGeneral_dichotomy_with_tangent S hfirstProper B tangentCount
 refine ⟨{
   budgetFamily:=B
   multiplicity:=multiplicity
   cost:=fun C => multiplicity C * B.weightedCost secondFlag C
   one_le_multiplicity:=hone
   tangentYZGate:=htangentGate
   cost_le:=fun _ => le_rfl
   divisor_le :=
     (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixed).divisor_le
       B multiplicity
   componentBound:=?_
   dichotomy:=providerDichotomy }⟩
 intro C
 rcases branchBound C with hproper | htangent
 · obtain ⟨_delay, _hdelay, _hdelayMu, _htail, hcount⟩:=hproper
   exact hcount
 · calc
     (componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=tangentCount C htangent
     _ ≤ B.weightedCost secondFlag C :=
       yzCost_mul_le_weightedCost B secondFlag C (stageErrorCap + 1) htangentGate
     _ = 1 * B.weightedCost secondFlag C:=by simp
     _ ≤ multiplicity C * B.weightedCost secondFlag C :=
       Nat.mul_le_mul_right (B.weightedCost secondFlag C) (hone C)
end
end ProximityPrize.SubmissionLower.RCN335
end PackedLegacy_Q2

/-! Packed from ProximityPrize.SubmissionLower.J4. -/
section PackedLegacy_J4
namespace ProximityPrize.SubmissionLower.RCN087
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 25000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e:ℕ} [CharP Ω p]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
local instance:DecidableEq I:=Classical.decEq I
def IdentityCurveCountProvider
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support) (identityDegree:ℕ):Prop:=
 ∀ i∈S.nodes,
   let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
   (hproper:¬S.G∣T) →
   let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
   ∃ cost:RegularComponent Ω S.G T (regularitySurface φ S.F)→ℕ,
     (∀ C,(componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
       (selectedPoint φ S.selected) C).card≤(e+1)*cost C)∧
     (∑ C,cost C) ≤ identityDegree
private theorem proper_node_fiber_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (identityDegree:ℕ) (hprovider:IdentityCurveCountProvider S identityDegree)
   (i:I) (hi:i∈S.nodes)
   (hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)):
   (Γ.filter (fun γ=>S.Agrees γ i)).card≤(e+1)*identityDegree:=by
 let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨cost,hcomponent,hsum⟩:=hprovider i hi hproper
 have hsub:Gi⊆Γ:=Finset.filter_subset _ _
 have hGpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) S.G=0:=by
   intro γ hγ;exact S.on_component γ (hsub hγ)
 have hTpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) T=0:=by
   intro γ hγ
   exact (selected_agreement_zero_iff φ S.F S.selected p w S.characteristic_bound γ
     (S.degree_le γ (hsub hγ)) (S.solution γ (hsub hγ))
     (S.regular γ (hsub hγ)) (x i) (S.u0 i) (S.u1 i)).mpr
     (Finset.mem_filter.mp hγ).2
 have hHp:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ)
     (regularitySurface φ S.F)≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ S.selected γ)
     (surfaceMap φ (MvPolynomial.pderiv 2 S.F))≠0
   rw [selectedPoint_evaluation]
   exact S.regular γ (hsub hγ)
 calc
   Gi.card≤∑ C:RegularComponent Ω S.G T (regularitySurface φ S.F),
       (componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
         (selectedPoint φ S.selected) C).card:=
     card_le_sum_componentSeeds Ω _ _ _ Gi _ hGpoint hTpoint hHp
   _≤∑ C,(e+1)*cost C:=Finset.sum_le_sum fun C _=>hcomponent C
   _=(e+1)*(∑ C,cost C):=by rw [Finset.mul_sum]
   _≤(e+1)*identityDegree:=Nat.mul_le_mul_left _ hsum
theorem identity_surface_seed_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (a identityDegree:ℕ)
   (hprovider:IdentityCurveCountProvider S identityDegree)
   (hagreement:∀ γ∈Γ,a≤(S.agreementFiber γ).card)
   (hwa:w < a) (han:a ≤ S.nodes.card) (hdegreePos:1 ≤ identityDegree):
   Γ.card*(a-w)≤(S.nodes.card-w)*(e+1)*identityDegree:=by
 classical
 letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
 let relation:K→I→Prop:=fun γ i=>S.Agrees γ i
 let identities:=S.identities
 by_cases hI:identities.card ≤ w
 · have hfiber:∀ i∈S.nodes\identities,
       (Γ.filter (fun γ=>relation γ i)).card≤(e+1)*identityDegree:=by
     intro i hi
     obtain ⟨hiNode,hiNot⟩:=Finset.mem_sdiff.mp hi
     have hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i):=by
       intro hd
       exact hiNot (Finset.mem_filter.mpr ⟨hiNode,Ideal.mem_span_singleton.mpr hd⟩)
     exact proper_node_fiber_bound S identityDegree hprovider i hiNode hproper
   simpa only [mul_assoc] using RCN173.sharp_incidence_bound relation Γ S.nodes
     identities a w ((e+1)*identityDegree)
     (identityNodes_subset φ S.componentIdeal S.F S.nodes x S.u0 S.u1 w)
     hI hwa han hagreement hfiber
 · have hi:w < identities.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈identities→
       (S.selected t.1).eval (x i)=S.u0 i+t.1*S.u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ S.componentIdeal S.F S.nodes x S.u0 S.u1
       p w S.characteristic_bound (S.selected t.1) t.1 (S.degree_le t.1 t.2)
       (S.solution t.1 t.2) (S.regular t.1 t.2) (S.selected_point_ideal t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=exists_common_pencil_of_many_identities
     φ S.componentIdeal S.F S.surface_mem_componentIdeal S.regularity_not_mem_componentIdeal
     S.nodes x S.u0 S.u1 w S.x_injective hi
     (fun t:{γ:K//γ∈Γ}=>t.1) (fun t=>S.selected t.1)
     (fun t=>S.degree_le t.1 t.2) hvalues
   have hsmall:Γ.card ≤ e+1:=by
     have hf:Γ.filter (fun γ=>S.selected γ=P0+Polynomial.C γ*P1)=Γ:=
       Finset.filter_eq_self.mpr (fun γ hγ=>hpencil ⟨γ,hγ⟩)
     simpa only [hf] using S.no_large_pencil P0 P1 h0 h1
   calc
     Γ.card*(a-w)≤(e+1)*(a-w):=Nat.mul_le_mul_right _ hsmall
     _≤(e+1)*(S.nodes.card-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _≤(S.nodes.card-w)*(e+1)*identityDegree:=by
       have h:=Nat.mul_le_mul_left ((S.nodes.card-w)*(e+1)) hdegreePos
       simpa [mul_assoc,mul_comm,mul_left_comm] using h
end
end ProximityPrize.SubmissionLower.RCN087
end PackedLegacy_J4

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DU. -/
section PackedLegacy_DU
namespace ProximityPrize.SubmissionLower.RCN049
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN274 RCN198
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem exists_agreement_projection_of_caps
   (S:ResidualStage φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣agreementPolynomial φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   ∃ base:∀ C:RegularComponent Ω S.G
       (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (support a b s) w)):=by
 classical
 let T:=agreementPolynomial φ S.F w x0 u0 u1
 let H:=regularitySurface φ S.F
 have hsy:s+2 < b+s+3:=by omega
 have hTflag:PolynomialInFlag (sharpResidualAgreementFlag (support a b s) w) T:=
   surfaceMap_agreement_in_sharp_flag hsy (phi:=φ)
     ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
     w (fun j:ℕ => (j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag S.flag_support
 obtain ⟨hTY,hTS,_⟩:=
   RCN314.degree_bounds_of_polynomialInFlag hTflag
 have hTY':T.degreeOf 0 ≤ 1+w*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact sharpResidualAgreementFlag_ys (support a b s) hsy w
 have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*w:=by
   apply hTS.trans_eq
   simp only [sharpResidualAgreementFlag,sharpAgreementDirection,
     RCN198.support]
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixZ:coordinateMixedDegree Ω S.G T 2<p:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Ω S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C => regularComponent_exists_separableLiteralCoordinate6630
     φ S.F S.G T p S.G_dvd_surface S.irreducible_G hproper
     S.y_dependent hGdegree hmixZ C
 let base:∀ C:RegularComponent Ω S.G T H,
     SeparableLiteralCoordinate C.1:=fun C => (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Ω S.G T H,
     D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Ω S.G T H,LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Ω C.1 2 htr
     p S.G T S.irreducible_G
     (regularComponent_G_mem Ω S.G T H C)
     (regularComponent_T_mem Ω S.G T H C)
     hproper hGdegree hmixZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end ProximityPrize.SubmissionLower.RCN049
end PackedLegacy_DU

/-! Packed from ProximityPrize.SubmissionLower.EQ. -/
section PackedLegacy_EQ
namespace ProximityPrize.SubmissionLower.RCN146
open scoped Classical BigOperators
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
end
end ProximityPrize.SubmissionLower.RCN146
end PackedLegacy_EQ
end Compact_PackedLegacy
