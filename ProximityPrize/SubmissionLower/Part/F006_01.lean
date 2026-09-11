import ProximityPrize.SubmissionLower.Part.F006_00
section Compact_PackedLegacy
section PackedLegacy_GJ
namespace ProximityPrize.SubmissionLower.RCN305
open scoped Classical BigOperators
open RCN002 RCN007 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN272 RCN216
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
 {Iota:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota

end
end ProximityPrize.SubmissionLower.RCN305
end PackedLegacy_GJ

/-! Packed from ProximityPrize.SubmissionLower.ER. -/
section PackedLegacy_ER
namespace ProximityPrize.SubmissionLower.RCN148
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN151 RCN152 RCN156 RCN165 RCN237 RCN305 RCN234 RCN215 RCN275
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def regularComponentCurveStageOfSupport
   (support:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ support.s)
   (hFys:wt residualYSWeights F ≤ support.ys)
   (hFtotal:wt residualTotalWeights F ≤ support.total)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d support:=by
 classical
 let GammaC:=componentSeeds Omega G T (regularitySurface phi F) Gamma
   (selectedPoint phi selected) C
 have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T
   (regularitySurface phi F) Gamma (selectedPoint phi selected) C
 exact {
   nodes:=nodes
   u0:=u0
   u1:=u1
   selected:=selected
   F:=F
   G:=G
   T:=T
   primeData:={
     ideal:=C.1
     isPrime:=inferInstance
     G_mem:=regularComponent_G_mem Omega G T (regularitySurface phi F) C
     T_mem:=regularComponent_T_mem Omega G T (regularitySurface phi F) C
     H_not_mem:=regularComponent_H_not_mem Omega G T
       (regularitySurface phi F) C
     ne_point:=regularComponent_ne_point Omega G T
       (regularitySurface phi F) C
   }
   G_dvd_surface:=hdiv
   G_flag_support:=hGflag
   T_flag_support:=hTflag
   surface_s_weight:=hFs
   surface_ys_weight:=hFys
   surface_total_weight:=hFtotal
   x_injective:=hinj
   degree_le:=fun gamma hgamma↦hdegree gamma (hsub hgamma)
   solution:=fun gamma hgamma↦hsolution gamma (hsub hgamma)
   regular:=fun gamma hgamma↦hregular gamma (hsub hgamma)
   on_prime:=fun gamma hgamma↦componentSeeds_on_prime Omega G T
     (regularitySurface phi F) Gamma (selectedPoint phi selected) C gamma hgamma
   no_large_pencil:=noLargeSelectedPencil_mono selected Gamma GammaC d e
     hsub hnoPencil
   characteristic_bound:=hchar
 }
def activeDifferentialSupport:ResidualSupportParameters where
 s:=6
 ys:=33
 total:=582
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
def regularComponentCurveStageActive
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 6)
   (hFys:wt residualYSWeights F ≤ 33)
   (hFtotal:wt residualTotalWeights F ≤ 582)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d activeDifferentialSupport:=
 regularComponentCurveStageOfSupport activeDifferentialSupport
   F G T selected Gamma nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag
   hTflag hFs hFys hFtotal hinj hdegree hsolution hregular hnoPencil hchar C
def regularComponentCurveStage
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 8)
   (hFys:wt residualYSWeights F ≤ 43)
   (hFtotal:wt residualTotalWeights F ≤ 503)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d:=
 regularComponentCurveStageOfSupport ResidualSupportParameters.acceptedSupport
   F G T selected Gamma nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag
   hTflag hFs hFys hFtotal hinj hdegree hsolution hregular hnoPencil hchar C
end
end ProximityPrize.SubmissionLower.RCN148
end PackedLegacy_ER

/-! Packed from ProximityPrize.SubmissionLower.BN. -/
section PackedLegacy_BN
namespace ProximityPrize.SubmissionLower.RCN149
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN151 RCN152 RCN156 RCN165 RCN237 RCN305 RCN234 RCN215 RCN148 RCN275
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN149
end PackedLegacy_BN

/-! Packed from ProximityPrize.SubmissionLower.ES. -/

/-! Packed from ProximityPrize.SubmissionLower.DP. -/
section PackedLegacy_DP
namespace ProximityPrize.SubmissionLower.RCN038
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044 RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370
 RCN351
open RCN037
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveNestedProjectionDataActive
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0) where
 lam:Omega
 lam_ne:lam≠0
 mu:Omega
 mu_ne:mu≠0
 uProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 allProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 uGate:∀ C:RegularComponent Omega G T H,
   ∀ htr:Transcendental Omega (affineU Omega C.1 lam),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 uTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega (affineU Omega C.1 lam)
 allAffineTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega (affineV Omega C.1 mu (mu*lam))
 allFinite:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)
 allSeparable:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)
 uValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=
     affineU Omega C.1 lam
 allValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (allProjection C)=
     affineV Omega C.1 mu (mu*lam)
 allTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega
     (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 uPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (uProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
       (RCN187.poleOrder v.val (coordinate Omega C.1 2))
 allPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
       (max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)))
 directional:MvPolynomial.pderiv (0:Fin 3) G-
   MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0
theorem exists_adaptiveNestedProjectionDataActive
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   Nonempty (AdaptiveNestedProjectionDataActive base hactive hSderiv):=by
 classical
 let E:RegularComponent Omega G T H → Type:=
   fun C => CoordinateField Omega C.1
 let rY:∀ C,E C:=fun C => coordinate Omega C.1 0
 let z:∀ C,E C:=fun C => coordinate Omega C.1 2
 let W:∀ C,Finset (Place Omega (E C)):=
   fun C => literalRelevantPlaces (base C)
 let baseC:∀ C,SeparableCoordinate Omega (E C):=
   fun C => literalToSeparableCoordinate (base C)
 obtain ⟨lam,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_affine_adaptive E rY z W
     baseC hactive
 let U:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=fun C => affineU Omega C.1 lam
 have hUgate:∀ C:RegularComponent Omega G T H,
     ∀ htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
   intro C htr
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   have hp:htr=hs:=Subsingleton.elim _ _
   cases hp
   exact ⟨hfinite,hsep⟩
 let uProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=
   fun C => coordinateOfGate (U C) (hUgate C)
 have huValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=U C:=
   fun C => coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rY,z,U,affineU] using
         (hlam C).choose_spec.2.2 v hv)
   · have h0:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 0
     have h2:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 2
     have h0le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h0
     have h2le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h2
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (lam • coordinate Omega C.1 2)=
         v.val (coordinate Omega C.1 2):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
     have hUle:v.val (U C) ≤ 1:=by
       exact (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le h0le h2le)
     have hU0:RCN187.poleOrder v.val (U C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.1) v _ hUle
     rw [hU0,h0,h2]
     simp
 have hactiveV:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 1)≠0∨
       D Omega (CoordinateField Omega C.1) (U C)≠0:=by
   intro C
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   exact Or.inr (differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
 let rS:∀ C,E C:=fun C => coordinate Omega C.1 1
 let Extra:Omega → Prop:=fun mu =>
   MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G=0
 have hextra:∀ {a b},Extra a → Extra b → a=b:=by
   exact directional_bad_coefficient_subsingleton G hSderiv
 obtain ⟨mu,hmu0,hmudir,hmu⟩:=
   exists_common_exact_finite_separable_affine_adaptive_avoiding_one
     E rS U W Extra hextra baseC hactiveV
 let V:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=
   fun C => coordinate Omega C.1 1+mu • U C
 let hV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (V C):=fun C => (hmu C).choose
 let vProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (vProjection C)=V C:=by
   intro C
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1) (V C) (hV C)
 have hvPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 1
     have hY:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 0
     have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C) ≤ 1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (affineV Omega C.1 mu (mu*lam)):=fun C => by
   rw [show affineV Omega C.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 mu (mu*lam)) (hVAff C)=
       elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C):=
   elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])
 refine ⟨{
   lam:=lam
   lam_ne:=hlam0
   mu:=mu
   mu_ne:=hmu0
   uProjection:=uProjection
   allProjection:=vProjection
   uGate:=hUgate
   uTranscendental:=fun C => (hlam C).choose
   allAffineTranscendental:=hVAff
   allFinite:=?_
   allSeparable:=?_
   uValue:=huValue
   allValue:=?_
   allTranscendental:=?_
   uPole:=?_
   allPole:=?_
   directional:=hmudir}⟩
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.1
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.2.1
 · intro C
   rw [hvValue C]
   simp only [V,U,affineU,affineV]
   simp only [smul_add,smul_smul,add_assoc]
 · intro C
   rw [hvValue C]
   exact hV C
 · intro C v
   rw [huValue C]
   exact huPole C v
 · intro C v
   rw [hvValue C,hvPole C v,huPole C v]
end
end ProximityPrize.SubmissionLower.RCN038
end PackedLegacy_DP

/-! Packed from ProximityPrize.SubmissionLower.A2. -/
section PackedLegacy_A2
namespace ProximityPrize.SubmissionLower.RCN040
open scoped Classical BigOperators WithZero
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN046 RCN037 RCN038 RCN095 RCN114 RCN093 RCN123 RCN121 RCN117 RCN116 RCN125 RCN022
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamily_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamily base p q:=by
 classical
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let zProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (coordinate Omega C.1 2) (hZ C)
 let uProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
 let vProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
   finite:=D.allFinite C
   separable:=D.allSeparable C}
 let gCaps:=flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let sZ:={C:RegularComponent Omega G T H//
   Transcendental Omega (coordinate Omega C.1 2)}
 have hinjZ:Function.Injective (fun C:sZ => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htZ:∀ C:sZ,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (zOrder 0))):=by
   intro C
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using C.2
 have hembZ (C:sZ):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (coordinate Omega C.1.1 2) C.2:=
   elementEmbedding_congr (htZ C) C.2
     (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenZ:∀ C:sZ,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembZ C]
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_z Omega C.1.1 lam mu nu C.2
 have hfamilyZ:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sZ => C.1.1) hinjZ lam mu nu zOrder
   htZ hgenZ G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
   p.all q.all (p.yz+p.all) (q.yz+q.all)
   (flagMixed p q unitZFlag) hTne
   (by simpa only [gCaps] using gCaps.zOuter)
   (by simpa only [tCaps] using tCaps.zOuter)
   (by simpa only [gCaps] using gCaps.zTotal)
   (by simpa only [tCaps] using tCaps.zTotal)
   (z_flag_trapezoid_budget p q)
 have hsumZ:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (zProj C)) ≤
       flagMixed p q unitZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => coordinate Omega C.1 2) hZ
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sZ,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sZ,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembZ C]
     _ ≤ _:=hfamilyZ.2
 let sU:={C:RegularComponent Omega G T H//
   Transcendental Omega (affineU Omega C.1 D.lam)}
 have hinjU:Function.Injective (fun C:sU => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htU:∀ C:sU,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (uOrder 0))):=by
   intro C
   simpa [uOrder,lam,mu,nu] using C.2
 have hembU (C:sU):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (affineU Omega C.1.1 D.lam) C.2:=
   elementEmbedding_congr (htU C) C.2
     (by simp [uOrder,lam,mu,nu])
 have hgenU:∀ C:sU,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembU C]
   simpa [uOrder,lam,mu,nu] using
     flag_generators_u Omega C.1.1 lam mu nu C.2
 have hfamilyU:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sU => C.1.1) hinjU lam mu nu uOrder
   htU hgenU G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
   p.all q.all (p.zOnly+p.yz+p.all)
   (q.zOnly+q.yz+q.all) (flagMixed p q unitYZFlag) hTne
   (by simpa only [gCaps] using gCaps.uOuter)
   (by simpa only [tCaps] using tCaps.uOuter)
   (by simpa only [gCaps] using gCaps.uTotal)
   (by simpa only [tCaps] using tCaps.uTotal)
   (u_flag_trapezoid_budget p q)
 have hsumU:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (uProj C)) ≤
       flagMixed p q unitYZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => affineU Omega C.1 D.lam) D.uGate
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sU,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sU,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembU C]
     _ ≤ _:=hfamilyU.2
 let htV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu
         (MvPolynomial.X (vOrder 0))):=by
   intro C
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     D.allAffineTranscendental C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam))
           (D.allAffineTranscendental C):=
   elementEmbedding_congr (htV C) (D.allAffineTranscendental C)
     (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenV:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 2)),
         flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 1))}:
         Set (CoordinateField Omega C.1))=⊤:=by
   intro C
   rw [hembV C]
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_v Omega C.1 lam mu nu (D.allAffineTranscendental C)
 have hinjV:Function.Injective
     (fun C:RegularComponent Omega G T H => C.1):=by
   intro C E hCE
   exact Subtype.ext hCE
 have hfamilyV:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:RegularComponent Omega G T H => C.1)
   hinjV lam mu nu vOrder htV hgenV G T hG
   (fun C => regularComponent_G_mem Omega G T H C)
   (fun C => regularComponent_T_mem Omega G T H C)
   hproper
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
   (p.yz+p.all) (q.yz+q.all)
   (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
   (flagMixed p q unitAllFlag) hTne
   (by simpa only [gCaps] using gCaps.vOuter)
   (by simpa only [tCaps] using tCaps.vOuter)
   (by simpa only [gCaps] using gCaps.vTotal)
   (by simpa only [tCaps] using tCaps.vTotal)
   (v_flag_trapezoid_budget p q)
 have hsumV:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (vProj C)) ≤
       flagMixed p q unitAllFlag:=by
   calc
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (affineV Omega C.1 D.mu (D.mu*D.lam))
               (D.allAffineTranscendental C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rfl
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (flagEvaluation Omega C.1 lam mu nu
               (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembV C]
     _ ≤ _:=hfamilyV.2
 have hvValue (C:RegularComponent Omega G T H):
     coordinateValue Omega (CoordinateField Omega C.1) (vProj C)=
       affineV Omega C.1 D.mu (D.mu*D.lam):=by
   dsimp only [vProj,coordinateValue,SeparableCoordinate.value,Sum.elim_inr]
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
 refine {
   zProjection:=zProj
   yzProjection:=uProj
   allProjection:=vProj
   zValue:=?_
   allTranscendental:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   sum_zDegree_le:=hsumZ
   sum_yzDegree_le:=hsumU
   sum_allDegree_le:=hsumV}
 · intro C
   exact coordinateOfGate_value _ _
 · intro C
   rw [hvValue C]
   exact D.allAffineTranscendental C
 · intro C v
   rw [exponentSetPoleWeight_unitZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
 · intro C v
   rw [exponentSetPoleWeight_unitYZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
   rw [←D.uValue C]
   exact (D.uPole C v).symm
 · intro C v
   rw [exponentSetPoleWeight_unitAll]
   change _=RCN187.poleOrder v.val _
   rw [hvValue C, ←D.allValue C]
   exact (D.allPole C v).symm
end
end ProximityPrize.SubmissionLower.RCN040
end PackedLegacy_A2

/-! Packed from ProximityPrize.SubmissionLower.E7. -/
section PackedLegacy_E7
namespace ProximityPrize.SubmissionLower.RCN265
open scoped Classical
open RCN002 RCN136 RCN243 RCN264 RCN267 RCN344 RCN341 RCN042 RCN037 RCN039 RCN046 RCN142 RCN093 RCN095
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
def verticalPoint (y z:Omega):Fin 3 → Polynomial Omega:=
 ![Polynomial.C y,Polynomial.X,Polynomial.C z]
def verticalPolynomial (y z:Omega):
   MvPolynomial (Fin 3) Omega →ₐ[Omega] Polynomial Omega:=
 MvPolynomial.aeval (verticalPoint y z)
theorem verticalPolynomial_derivative (y z:Omega)
   (F:MvPolynomial (Fin 3) Omega):
   (verticalPolynomial y z F).derivative=
     verticalPolynomial y z (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp [verticalPolynomial]
 | add P Q hP hQ => simp only [map_add,Polynomial.derivative_add,hP,hQ]
 | mul_X P i hP =>
     fin_cases i <;>
       simp [verticalPolynomial,verticalPoint,Polynomial.derivative_mul] at hP ⊢ <;>
       rw [hP] <;> ring
theorem aeval_verticalPolynomial_eq_coordinateEvaluation
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (y z:Omega)
   (hy:algebraMap Omega (CoordinateField Omega P) y=coordinate Omega P 0)
   (hz:algebraMap Omega (CoordinateField Omega P) z=coordinate Omega P 2)
   (F:MvPolynomial (Fin 3) Omega):
   Polynomial.aeval (coordinate Omega P 1) (verticalPolynomial y z F)=
     coordinateEvaluation Omega P F:=by
 let lhs:MvPolynomial (Fin 3) Omega →ₐ[Omega] CoordinateField Omega P:=
   (Polynomial.aeval (coordinate Omega P 1)).comp (verticalPolynomial y z)
 have hlhs:lhs=coordinateEvaluation Omega P:=by
   apply MvPolynomial.algHom_ext
   intro i
   fin_cases i <;>
     simp [lhs,verticalPolynomial,verticalPoint,coordinate,hy,hz]
 exact AlgHom.congr_fun hlhs F
theorem y_or_z_transcendental_of_regular_polynomial
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Omega)
   (hF:F∈P)
   (hFR:MvPolynomial.pderiv (1:Fin 3) F∉P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2):=by
 by_contra hYZ
 push_neg at hYZ
 have hYalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hYZ.1
 have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hYZ.2
 obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hYalg
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZalg
 obtain ⟨i,hi⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
 have hiR:i=(1:Fin 3):=by
   fin_cases i <;> simp_all
 subst i
 let Q:=verticalPolynomial y z F
 have hQeval:Polynomial.aeval (coordinate Omega P 1) Q=0:=by
   rw [aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz F]
   change coordinateEvaluation Omega P F=0
   have hm:F∈RingHom.ker (coordinateEvaluation Omega P).toRingHom:=by
     rwa [coordinateEvaluation_ker Omega P]
   exact hm
 have hQ:Q=0:=by
   apply transcendental_iff_injective.mp hi
   simpa using hQeval
 have hQderiv:Q.derivative=0:=by rw [hQ,Polynomial.derivative_zero]
 have hFReval:coordinateEvaluation Omega P
     (MvPolynomial.pderiv (1:Fin 3) F)=0:=by
   rw [←aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz]
   rw [←verticalPolynomial_derivative]
   simpa [Q] using congrArg
     (Polynomial.aeval (coordinate Omega P 1)) hQderiv
 apply hFR
 rw [←coordinateEvaluation_ker Omega P,RingHom.mem_ker]
 exact hFReval
variable {K:Type} [Field K]
theorem regularComponent_y_or_z_transcendental
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Omega)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   Transcendental Omega (coordinate Omega C.1 0)∨
     Transcendental Omega (coordinate Omega C.1 2):=by
 let H:=regularitySurface phi F
 have hGmem:G∈C.1:=regularComponent_G_mem Omega G T H C
 have hFmem:surfaceMap phi F∈C.1:=by
   obtain ⟨Q,hQ⟩:=hdiv
   rw [hQ]
   exact C.1.mul_mem_right Q hGmem
 have hFRnot:MvPolynomial.pderiv (1:Fin 3) (surfaceMap phi F)∉C.1:=by
   rw [surfaceMap_pderiv_R]
   exact regularComponent_H_not_mem Omega G T H C
 exact y_or_z_transcendental_of_regular_polynomial C.1 (surfaceMap phi F)
   hFmem hFRnot (regularComponent_ne_point Omega G T H C)
section RefinedAdaptiveFamily
variable {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveUnitProjectionFamilyYZ
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 family:AdaptiveUnitProjectionFamily base p q
 lam:Omega
 yzValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1)
       (family.yzProjection C)=affineU Omega C.1 lam
def adaptiveUnitProjectionFamilyYZ_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionData base hY hZ hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamilyYZ base p q where
 family:=adaptiveUnitProjectionFamily_of_nested p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport
 lam:=D.lam
 yzValue:=by
   intro C
   exact coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)
theorem AdaptiveUnitProjectionFamilyYZ.one_le_zCost_add_yzCost
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree}
   (P:AdaptiveUnitProjectionFamilyYZ base p q)
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (hH:H=regularitySurface phi F)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T H):
   1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C+
     P.family.toPrimeFlagBudgetFamily.yzCost C:=by
 subst H
 have hYZ:=regularComponent_y_or_z_transcendental phi F G T hdiv C
 by_cases hZ:Transcendental Omega (coordinate Omega C.1 2)
 · have hzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C:=
     P.family.one_le_toPrimeFlagBudgetFamily_zCost C hZ
   omega
 · have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=
     not_not.mp hZ
   have hY:Transcendental Omega (coordinate Omega C.1 0):=by
     rcases hYZ with hY | hZ'
     · exact hY
     · exact (hZ hZ').elim
   have hU:Transcendental Omega (affineU Omega C.1 P.lam):=by
     exact transcendental_add_smul_of_transcendental_isAlgebraic
       Omega C.1 (coordinate Omega C.1 0) (coordinate Omega C.1 2)
         P.lam hY hZalg
   have hyzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.yzCost C:=by
     apply one_le_coordinateDegree_of_transcendental_value
     rw [P.yzValue C]
     exact hU
   omega
end RefinedAdaptiveFamily
end
end ProximityPrize.SubmissionLower.RCN265
end PackedLegacy_E7

/-! Packed from ProximityPrize.SubmissionLower.DQ. -/
section PackedLegacy_DQ
namespace ProximityPrize.SubmissionLower.RCN041
open scoped Classical
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN093 RCN037 RCN038 RCN040 RCN046 RCN265 RCN095
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamilyYZ_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamilyYZ base p q where
 family:=adaptiveUnitProjectionFamily_of_active_nested p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport
 lam:=D.lam
 yzValue:=by
   intro C
   exact coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)
theorem exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamilyYZ base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionDataActive base hactive hSderiv
 exact ⟨adaptiveUnitProjectionFamilyYZ_of_active_nested p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport⟩
end
end ProximityPrize.SubmissionLower.RCN041
end PackedLegacy_DQ

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.O6. -/
section PackedLegacy_O6
namespace ProximityPrize.SubmissionLower.RCN277
open scoped Classical
open RCN002 RCN005 RCN003 RCN009 RCN001 RCN072 RCN264 RCN136 RCN243 RCN341 RCN265
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
abbrev Poly3:=MvPolynomial (Fin 3) Omega
theorem exists_coordinate_difference_mem_of_isAlgebraic
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime] (i:Fin 3)
   (hi:IsAlgebraic Omega (coordinate Omega P i)):
   ∃ c:Omega,MvPolynomial.X i-MvPolynomial.C c∈P:=by
 obtain ⟨c,hc⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P i hi
 refine ⟨c,?_⟩
 rw [←aeval_coordinate_ker Omega P]
 change MvPolynomial.aeval (coordinate Omega P)
     (MvPolynomial.X i-MvPolynomial.C c)=0
 simp only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
 rw [←hc,sub_self]
theorem not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos
   (G:Poly3 (Omega:=Omega)) (hG:G≠0)
   (hdep:0 < G.degreeOf (1:Fin 3)) (c:Omega):
   ¬ G∣(MvPolynomial.X (2:Fin 3)-MvPolynomial.C c):=by
 let H:Poly3 (Omega:=Omega):=
   MvPolynomial.X (2:Fin 3)-MvPolynomial.C c
 have hHne:H≠0:=coordinate_difference_ne_zero Omega 2 c
 have hHdegree:H.degreeOf (1:Fin 3) ≤ 0:=by
   calc
     H.degreeOf (1:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 1)
           ((MvPolynomial.C c:Poly3).degreeOf 1):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (1:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=0:=by
       rw [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2),
         MvPolynomial.degreeOf_C]
       rfl
 intro hdiv
 obtain ⟨A,hA⟩:=hdiv
 have hHA:H=G*A:=by simpa only [H] using hA
 have hAne:A≠0:=by
   intro hzero
   apply hHne
   rw [hHA,hzero,mul_zero]
 have hle:G.degreeOf (1:Fin 3) ≤ H.degreeOf (1:Fin 3):=by
   calc
     G.degreeOf (1:Fin 3) ≤
         G.degreeOf (1:Fin 3)+A.degreeOf (1:Fin 3):=
       Nat.le_add_right _ _
     _=(G*A).degreeOf (1:Fin 3):=by
       rw [MvPolynomial.degreeOf_mul_eq hG hAne]
     _=H.degreeOf (1:Fin 3):=by rw [hHA]
 omega
theorem finite_separable_at_y_of_z_algebraic
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hY:Transcendental Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P 0 hY
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=by
 obtain ⟨c,hHmem⟩:=
   exists_coordinate_difference_mem_of_isAlgebraic P 2 hZ
 let H:Poly3 (Omega:=Omega):=
   MvPolynomial.X (2:Fin 3)-MvPolynomial.C c
 have hproper:¬ G∣H:=
   not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos G hG.ne_zero hdep c
 have hHone:H.degreeOf (1:Fin 3) ≤ 0:=by
   calc
     H.degreeOf (1:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 1)
           ((MvPolynomial.C c:Poly3).degreeOf 1):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (1:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=0:=by
       rw [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2),
         MvPolynomial.degreeOf_C]
       rfl
 have hHtwo:H.degreeOf (2:Fin 3) ≤ 1:=by
   calc
     H.degreeOf (2:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 2)
           ((MvPolynomial.C c:Poly3).degreeOf 2):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (2:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=1:=by simp
 have hmixed:coordinateMixedDegree Omega G H 0 < p:=by
   rw [coordinateMixedDegree_zero]
   calc
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2 ≤
         0*G.degreeOf 2+G.degreeOf 1*1:=
       Nat.add_le_add (Nat.mul_le_mul hHone (Nat.le_refl _))
         (Nat.mul_le_mul (Nat.le_refl _) hHtwo)
     _=G.degreeOf 1:=by simp
     _ < p:=hdegree 1
 exact finite_separable_at_of_original_coordinate_gate Omega P 0 hY p G H
   hG hGmem hHmem hproper hdegree hmixed
theorem exists_separableLiteralCoordinate_y_or_z
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G T:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P) (hTmem:T∈P)
   (hproper:¬ G∣T)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedZ:coordinateMixedDegree Omega G T 2 < p)
   (hYZ:Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2)):
   ∃ D:SeparableLiteralCoordinate P,
     D.index=0∨D.index=2:=by
 by_cases hZ:Transcendental Omega (coordinate Omega P 2)
 · have hz:=finite_separable_at_of_original_coordinate_gate
     Omega P 2 hZ p G T hG hGmem hTmem hproper hdegree hmixedZ
   exact ⟨⟨2,hZ,hz.1,hz.2⟩,Or.inr rfl⟩
 · have hY:Transcendental Omega (coordinate Omega P 0):=
     hYZ.resolve_right hZ
   have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hZ
   have hy:=finite_separable_at_y_of_z_algebraic P p G hG hGmem hdep
     hdegree hY hZalg
   exact ⟨⟨0,hY,hy.1,hy.2⟩,Or.inl rfl⟩
theorem regularComponent_exists_separableLiteralCoordinate6630
   {K:Type} [Field K]
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:Poly3 (Omega:=Omega))
   (p:ℕ) [CharP Omega p]
   (hdiv:G∣surfaceMap phi F)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedZ:coordinateMixedDegree Omega G T 2 < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   ∃ D:SeparableLiteralCoordinate C.1,
     D.index=0∨D.index=2:=by
 apply exists_separableLiteralCoordinate_y_or_z C.1 p G T hG
   (regularComponent_G_mem Omega G T (regularitySurface phi F) C)
   (regularComponent_T_mem Omega G T (regularitySurface phi F) C)
   hproper hdep hdegree hmixedZ
 exact regularComponent_y_or_z_transcendental phi F G T hdiv C
end
end ProximityPrize.SubmissionLower.RCN277
end PackedLegacy_O6

/-! Packed from ProximityPrize.SubmissionLower.EV. -/
section PackedLegacy_EV
namespace ProximityPrize.SubmissionLower.RCN153
open scoped Classical
open RCN159 RCN164 RCN213 RCN215 RCN214 RCN238 RCN095 RCN275
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
def factorRegularLedgerFor (p direction:FlagDegree):ℕ:=
 degreeIncidence*
     ((flagMixed p direction direction*degreeIncidence+
         flagMixed p direction unitYZFlag*unitIncidence)+
       (errors+1)*gap*
         (flagMixed p direction unitZFlag+
           flagMixed p direction unitAllFlag))+
   unitIncidence*
     ((flagMixed p direction unitYZFlag*degreeIncidence+
         flagMixed p unitYZFlag unitYZFlag*unitIncidence)+
       (errors+1)*gap*
         (flagMixed p unitYZFlag unitZFlag+
           flagMixed p unitYZFlag unitAllFlag))
end
end ProximityPrize.SubmissionLower.RCN153
end PackedLegacy_EV

/-! Packed from ProximityPrize.SubmissionLower.EW. -/
section PackedLegacy_EW
namespace ProximityPrize.SubmissionLower.RCN154
open scoped Classical
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN159 RCN159.ResidualStage RCN151 RCN148 RCN149 RCN153 RCN156 RCN158 RCN275 RCN237 RCN213 RCN215 RCN214 RCN234 RCN276 RCN091
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 40000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def TerminalLargeZChargeOfSupport
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (D:S.TerminalDescendant) (i:Iota)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (support.residualAgreementFlag D.degree)):Prop:=
 let GammaI:=Gamma.filter (fun gamma↦D.stage.Agrees gamma i)
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let aD:=agreements-(w-D.degree)
 ∀ C:RegularComponent Omega D.stage.G T
     (regularitySurface phi D.stage.F),
   let GammaC:=componentSeeds Omega D.stage.G T
     (regularitySurface phi D.stage.F) GammaI
     (selectedPoint phi D.stage.selected) C
   let SC:=regularComponentCurveStageOfSupport support D.stage.F D.stage.G T
     D.stage.selected GammaI D.stage.nodes x D.stage.u0 D.stage.u1
     pchar errors D.degree flag (support.residualAgreementFlag D.degree)
     D.stage.G_dvd_surface D.stage.flag_support
     (surfaceMap_agreement_in_flag_of_support support
       D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
       D.stage.surface_total_weight D.degree
       (fun j↦(j.factorial:K)⁻¹)
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     D.stage.surface_s_weight D.stage.surface_ys_weight
     D.stage.surface_total_weight D.stage.x_injective
     (fun gamma hgamma↦D.stage.degree_le gamma
       (Finset.mem_filter.mp hgamma).1)
     (fun gamma hgamma↦D.stage.solution gamma
       (Finset.mem_filter.mp hgamma).1)
     (fun gamma hgamma↦D.stage.regular gamma
       (Finset.mem_filter.mp hgamma).1)
     (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
       D.degree errors (Finset.filter_subset _ _) D.stage.no_large_pencil)
     D.stage.characteristic_bound C
   ∀ E:SC.TerminalDescendant,
     E.degree < E.stage.identities.card →
       GammaC.card*(aD-D.degree) ≤
         (errors+1)*(aD-D.degree)*B.zCost C
abbrev TerminalLargeZCharge
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w)
   (D:S.TerminalDescendant) (i:Iota)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (residualAgreementFlag D.degree)):Prop:=
 TerminalLargeZChargeOfSupport S D i B
end
end ProximityPrize.SubmissionLower.RCN154
end PackedLegacy_EW

/-! Packed from ProximityPrize.SubmissionLower.DR. -/
section PackedLegacy_DR
namespace ProximityPrize.SubmissionLower.RCN043
open scoped Classical
open RCN213 RCN231 RCN238 RCN264 RCN243 RCN095 RCN159 RCN151 RCN156 RCN154 RCN237 RCN215 RCN214 RCN341 RCN046
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def TerminalAdaptiveProjectionFamilies
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (residualAgreementFlag D.degree))
end
end ProximityPrize.SubmissionLower.RCN043
end PackedLegacy_DR

/-! Packed from ProximityPrize.SubmissionLower.O5. -/
section PackedLegacy_O5
namespace ProximityPrize.SubmissionLower.RCN274
open RCN136 RCN267 RCN159 RCN095
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
end
end ProximityPrize.SubmissionLower.RCN274
end PackedLegacy_O5

/-! Packed from ProximityPrize.SubmissionLower.GN. -/
section PackedLegacy_GN
namespace ProximityPrize.SubmissionLower.RCN314
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN095 RCN159 RCN158 RCN156 RCN037 RCN039 RCN043 RCN341 RCN274
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem degree_bounds_of_polynomialInFlag
   {p:FlagDegree} {F:MvPolynomial (Fin 3) Omega}
   (hF:PolynomialInFlag p F):
   F.degreeOf 0 ≤ p.yz+p.all∧
     F.degreeOf 1 ≤ p.all∧
     F.degreeOf 2 ≤ p.zOnly+p.yz+p.all:=by
 refine ⟨?_,?_,?_⟩
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (hF e he).1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_left (e 2) (e 0+e 1)).trans (by
     simpa only [Nat.add_assoc] using (hF e he).2.2)
end
end ProximityPrize.SubmissionLower.RCN314
end PackedLegacy_GN

/-! Packed from ProximityPrize.SubmissionLower.GO. -/
section PackedLegacy_GO
namespace ProximityPrize.SubmissionLower.RCN315
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN267 RCN095 RCN159 RCN158 RCN037 RCN039 RCN046 RCN341 RCN274 RCN275 RCN276
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem residualStage_pderiv_one_ne_zero_of_support
   {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
   {support:ResidualSupportParameters}
   (S:ResidualStage phi Gamma x p e flag d support):
   MvPolynomial.pderiv (1:Fin 3) S.G≠0:=by
 intro hzero
 apply S.regular_proper
 rw [←surfaceMap_pderiv_R]
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 refine ⟨MvPolynomial.pderiv (1:Fin 3) Q,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul,hzero,zero_mul,zero_add]
def FixedMeetTerminalAdaptiveProjectionFamilies
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree))
end
end ProximityPrize.SubmissionLower.RCN315
end PackedLegacy_GO

/-! Packed from ProximityPrize.SubmissionLower.GP. -/

/-! Packed from ProximityPrize.SubmissionLower.FR. -/

/-! Packed from ProximityPrize.SubmissionLower.P3. -/

/-! Packed from ProximityPrize.SubmissionLower.B6. -/

/-! Packed from ProximityPrize.SubmissionLower.B7. -/
section PackedLegacy_B7
namespace ProximityPrize.SubmissionLower.RCN089
open RCN136 RCN313 RCN238 RCN275 RCN095 RCN198 RCN086 RCN262 RCN263
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
def reducedGlobalTailCut (phi:Polynomial K →+* Omega)
   (support:ResidualSupportParameters) (F:MvPolynomial (Fin 4) K)
   (d:ℕ):MvPolynomial (Fin 3) Omega :=
 surfaceMap phi
   (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
theorem globalTailCut_sub_reduced_dvd
   (phi:Polynomial K →+* Omega) (support:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K) (d:ℕ) :
   surfaceMap phi F ∣ globalTailCut phi F d -
     reducedGlobalTailCut phi support F d:=by
 change surfaceMap phi F ∣
   surfaceMap phi (agreementNumerator F d (tailSelector d) 0 0 0) -
     surfaceMap phi
       (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
 rw [← map_sub]
 exact map_dvd (surfaceMap phi)
   (agreementNumerator_sub_reduced_dvd F support.s d
     (tailSelector d) 0 0 0)
theorem reducedGlobalTailCut_in_flag
   (phi:Polynomial K →+* Omega) (support:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData support F)
   (d:ℕ) :
   PolynomialInFlag (reducedResidualAgreementFlag support d)
     (reducedGlobalTailCut phi support F d):=by
 exact surfaceMap_reducedAgreement_in_flag phi support H d
   (tailSelector d) 0 0 0
end
end ProximityPrize.SubmissionLower.RCN089
end PackedLegacy_B7

/-! Packed from ProximityPrize.SubmissionLower.J5. -/
section PackedLegacy_J5
namespace ProximityPrize.SubmissionLower.RCN090
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN198 RCN086 RCN263 RCN089
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+* Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem exists_reduced_firstTail_activeNestedData_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
   ∃ (base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F), SeparableLiteralCoordinate C.1),
     ∃ (hactive:∀ C:RegularComponent Omega S.G
         (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
         (regularitySurface phi S.F),
         KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 0) ≠ 0 ∨
           KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃ (hZ:∀ C:RegularComponent Omega S.G
           (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
           (regularitySurface phi S.F), LiteralProjectionGate C 2),
         Nonempty (AdaptiveNestedProjectionDataActive base hactive
           (RCN315.residualStage_pderiv_one_ne_zero_of_support S)):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T, Tred, sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY, hGS, hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY, hTS, _hTZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hTY':Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2):=by
   apply hTY.trans_eq
   exact reducedResidualAgreementFlag_ys supp (w + 1)
 have hTS':Tred.degreeOf 1 ≤ (2 * (s + 2) - 2) * (w + 1):=by
   apply hTS.trans_eq
   rfl
 have hGdegree:∀ j:Fin 3, S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixedZ:coordinateMixedDegree Omega S.G Tred 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
   fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G Tred pchar S.G_dvd_surface S.irreducible_G hproperRed
     S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 have hZ:∀ C:RegularComponent Omega S.G Tred H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G Tred S.irreducible_G
     (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C)
     hproperRed hGdegree hmixedZ
 exact ⟨base, hactive, hZ,
   exists_adaptiveNestedProjectionDataActive base hactive
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.RCN090
end PackedLegacy_J5

/-! Packed from ProximityPrize.SubmissionLower.CK. -/
section PackedLegacy_CK
namespace ProximityPrize.SubmissionLower.RCN337
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
variable {K:Type} [Field K] [DecidableEq K]
end
end ProximityPrize.SubmissionLower.RCN337
end PackedLegacy_CK
end Compact_PackedLegacy
