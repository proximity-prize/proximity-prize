import ProximityPrize.SubmissionLower.MergedInfra6815_37
import ProximityPrize.SubmissionLower.MergedInfra6815_31
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
noncomputable section
set_option autoImplicit false
open RCN135 RCN136 RCN159 RCN174 RCN243 RCN275
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p errorCap d : ℕ} [CharP (GenericField K) p]
  {flag : RCN095.FlagDegree} {support : ResidualSupportParameters}

end
end ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical
open RCN086 RCN095 RCN135 RCN136 RCN156 RCN159 RCN174 RCN234 RCN243 RCN244 RCN260 RCN264 RCN275
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourcePairStageSupplier6814 MovingSourceCoupledClearing6814
open LocatorHybridCells

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN084 RCN095

def CumulativeLe (p q : FlagDegree) : Prop :=
  p.all≤q.all ∧ p.yz+p.all≤q.yz+q.all ∧ p.zOnly+p.yz+p.all≤q.zOnly+q.yz+q.all

theorem mixed_mono_left (p p' q r : FlagDegree) (h : CumulativeLe p p') :
    flagMixed p q r≤flagMixed p' q r := by
  have hh := sum_flagMixed_le_of_cumulative (fun _ : Fin 1 => p) p' q r
    (by simpa using h.1) (by simpa using h.2.1) (by simpa using h.2.2)
  simpa using hh

theorem mixed_swap_left (p q r : FlagDegree) : flagMixed p q r=flagMixed q p r := by
  simp only [flagMixed]
  ring

theorem mixed_mono_pair (p q p' q' r : FlagDegree)
    (hp : CumulativeLe p p') (hq : CumulativeLe q q') :
    flagMixed p q r≤flagMixed p' q' r := by
  apply (mixed_mono_left p p' q r hp).trans
  rw [mixed_swap_left p' q r,mixed_swap_left p' q' r]
  exact mixed_mono_left q q' p' r hq

end
end ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingSourceCheckedPairStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN086 RCN095 RCN135 RCN136 RCN156 RCN159 RCN174 RCN234 RCN243 RCN244 RCN260 RCN264
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCoupledClearing6814
open MovingSourcePairRetainedStage6814 MovingSourcePairStageSupplier6814
open MovingSourcePairEnvelope6814 LocatorHybridCells

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.MovingSourceCheckedPairStage6814
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.MovingSourceOuterCommonFrame6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044
open RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370 RCN351 RCN037 RCN038
variable {Omega J : Type} [Field Omega] [IsAlgClosed Omega] [Fintype J]
local notation "Poly" => MvPolynomial (Fin 3) Omega

theorem exists_common_outer_frames
    (G T H : J → Poly)
    (base : ∀ i, ∀ C : RegularComponent Omega (G i) (T i) (H i), SeparableLiteralCoordinate C.1)
    (hactive : ∀ i, ∀ C : RegularComponent Omega (G i) (T i) (H i),
      D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0 ∨
        D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
    (hSderiv : ∀ i, MvPolynomial.pderiv (1 : Fin 3) (G i)≠0)
    (S : Set Omega) (hS : S.Infinite) :
    ∃ lam mu : Omega, lam∈S ∧ mu∈S ∧
      ∃ data : ∀ i, AdaptiveNestedProjectionDataActive (base i) (hactive i) (hSderiv i),
        ∀ i, (data i).lam=lam ∧ (data i).mu=mu := by
 let Family := (i : J) × RegularComponent Omega (G i) (T i) (H i)
 classical
 let E:Family → Type:=
   fun C => CoordinateField Omega C.2.1
 let rY:∀ C,E C:=fun C => coordinate Omega C.2.1 0
 let z:∀ C,E C:=fun C => coordinate Omega C.2.1 2
 let W:∀ C,Finset (Place Omega (E C)):=
   fun C => literalRelevantPlaces (base C.1 C.2)
 let baseC:∀ C,SeparableCoordinate Omega (E C):=
   fun C => literalToSeparableCoordinate (base C.1 C.2)
 obtain ⟨lam,hlamS,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_affine_adaptive_in E rY z W
     S hS baseC (fun C => hactive C.1 C.2)
 let U:∀ C:Family,
     CoordinateField Omega C.2.1:=fun C => affineU Omega C.2.1 lam
 have hUgate:∀ C:Family,
     ∀ htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.2.1):=
           (elementEmbedding Omega (CoordinateField Omega C.2.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.2.1))∧
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.2.1):=
           (elementEmbedding Omega (CoordinateField Omega C.2.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.2.1)):=by
   intro C htr
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   have hp:htr=hs:=Subsingleton.elim _ _
   cases hp
   exact ⟨hfinite,hsep⟩
 let uProjection:∀ C:Family,
     Coordinate Omega (CoordinateField Omega C.2.1):=
   fun C => coordinateOfGate (U C) (hUgate C)
 have huValue:∀ C:Family,
     coordinateValue Omega (CoordinateField Omega C.2.1) (uProjection C)=U C:=
   fun C => coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀ (C:Family)
     (v:Place Omega (CoordinateField Omega C.2.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.2.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.2.1 2)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C.1 C.2)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rY,z,U,affineU] using
         (hlam C).choose_spec.2.2 v hv)
   · have h0:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 0
     have h2:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 2
     have h0le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h0
     have h2le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h2
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (lam • coordinate Omega C.2.1 2)=
         v.val (coordinate Omega C.2.1 2):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
     have hUle:v.val (U C) ≤ 1:=by
       exact (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le h0le h2le)
     have hU0:RCN187.poleOrder v.val (U C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.2.1) v _ hUle
     rw [hU0,h0,h2]
     simp
 have hactiveV:∀ C:Family,
     D Omega (CoordinateField Omega C.2.1) (coordinate Omega C.2.1 1)≠0∨
       D Omega (CoordinateField Omega C.2.1) (U C)≠0:=by
   intro C
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   exact Or.inr (differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
 let rS:∀ C,E C:=fun C => coordinate Omega C.2.1 1
 let bad (i : J) : Set Omega := {mu | MvPolynomial.pderiv (0 : Fin 3) (G i)-
   MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) (G i)=0}
 have hbad : (⋃ i, bad i).Finite := by
   apply Set.finite_iUnion
   intro i
   have hs : (bad i).Subsingleton := by
     intro a ha b hb
     exact directional_bad_coefficient_subsingleton (G i) (hSderiv i) ha hb
   exact hs.finite
 obtain ⟨mu,hmuS,hmu0,hmu⟩ :=
   exists_common_exact_finite_separable_affine_adaptive_in
     E rS U W (S \ ⋃ i, bad i) (hS.sdiff hbad) baseC hactiveV
 have hmudir (i : J) : MvPolynomial.pderiv (0 : Fin 3) (G i)-
     MvPolynomial.C mu*MvPolynomial.pderiv (1 : Fin 3) (G i)≠0 := by
   intro hh
   exact hmuS.2 (Set.mem_iUnion.mpr ⟨i,hh⟩)
 let V:∀ C:Family,
     CoordinateField Omega C.2.1:=
   fun C => coordinate Omega C.2.1 1+mu • U C
 let hV:∀ C:Family,
     Transcendental Omega (V C):=fun C => (hmu C).choose
 let vProjection:∀ C:Family,
     Coordinate Omega (CoordinateField Omega C.2.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.2.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀ C:Family,
     coordinateValue Omega (CoordinateField Omega C.2.1) (vProjection C)=V C:=by
   intro C
   exact elementEmbedding_variable Omega (CoordinateField Omega C.2.1) (V C) (hV C)
 have hvPole:∀ (C:Family)
     (v:Place Omega (CoordinateField Omega C.2.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.2.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C.1 C.2)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 1
     have hY:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 0
     have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C.1 C.2) v hv 2
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
         (CoordinateField Omega C.2.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀ C:Family,
     Transcendental Omega (affineV Omega C.2.1 mu (mu*lam)):=fun C => by
   rw [show affineV Omega C.2.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:Family):
     elementEmbedding Omega (CoordinateField Omega C.2.1)
         (affineV Omega C.2.1 mu (mu*lam)) (hVAff C)=
       elementEmbedding Omega (CoordinateField Omega C.2.1) (V C) (hV C):=
   elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])

 let data (i : J) : AdaptiveNestedProjectionDataActive (base i) (hactive i) (hSderiv i) := {
   lam := lam
   lam_ne := hlam0
   mu := mu
   mu_ne := hmu0
   uProjection := fun C => uProjection ⟨i,C⟩
   allProjection := fun C => vProjection ⟨i,C⟩
   uGate := fun C => hUgate ⟨i,C⟩
   uTranscendental := fun C => (hlam ⟨i,C⟩).choose
   allAffineTranscendental := fun C => hVAff ⟨i,C⟩
   allFinite := by
     intro C
     rw [hembV ⟨i,C⟩]
     exact (hmu ⟨i,C⟩).choose_spec.1
   allSeparable := by
     intro C
     rw [hembV ⟨i,C⟩]
     exact (hmu ⟨i,C⟩).choose_spec.2.1
   uValue := fun C => huValue ⟨i,C⟩
   allValue := by
     intro C
     rw [hvValue ⟨i,C⟩]
     simp only [V,U,affineU,affineV,smul_add,smul_smul,add_assoc]
   allTranscendental := by
     intro C
     rw [hvValue ⟨i,C⟩]
     exact hV ⟨i,C⟩
   uPole := by
     intro C nu
     rw [huValue ⟨i,C⟩]
     exact huPole ⟨i,C⟩ nu
   allPole := by
     intro C nu
     rw [hvValue ⟨i,C⟩,hvPole ⟨i,C⟩ nu,huPole ⟨i,C⟩ nu]
   directional := hmudir i }
 exact ⟨lam,mu,hlamS,hmuS.1,data,fun _ => ⟨rfl,rfl⟩⟩

end
end ProximityPrize.SubmissionLower.MovingSourceOuterCommonFrame6814
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingSourceOuterStageFrames6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical
open RCN030 RCN086 RCN095 RCN135 RCN136 RCN159 RCN198 RCN243 RCN263 RCN264 RCN275 RCN327 RCN332 RCN341
open RCN334 RCN089
open MovingSourceOuterCommonFrame6814

variable {K I J : Type} [Field K] [Fintype J]
variable {p errorCap a b s : ℕ} [CharP (GenericField K) p]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem exists_common_stage_geometry
    (Gamma : J → Finset K) (x : I → K) (flag : J → FlagDegree)
    (stage : ∀ j, ResidualStage (polynomialEmbedding K) (Gamma j) x p errorCap (flag j) w (support a b s))
    (hproper : ∀ j, ¬(stage j).G∣globalTailCut (polynomialEmbedding K) (stage j).F (w+1))
    (hflag : ∀ j, (flag j).yz+(flag j).all<p ∧ (flag j).all<p ∧
      (flag j).zOnly+(flag j).yz+(flag j).all<p)
    (hmixed : ∀ j, flagMixed (flag j) (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag<p) :
    ∃ lam mu : GenericField K,
      lam∈Set.range (polynomialEmbedding K) ∧ mu∈Set.range (polynomialEmbedding K) ∧
      ∃ geometry : ∀ j, ReducedActiveGeometry (stage j),
        ∀ j, (geometry j).data.lam=lam ∧ (geometry j).data.mu=mu := by
  classical
  choose base hactive hZ hdata using fun j =>
    BoundaryTailProjection.exists_reduced_firstTail_activeNestedData_of_caps
      (stage j) (hproper j) (hflag j) (hmixed j)
  obtain ⟨lam,mu,hlam,hmu,data,heq⟩ := exists_common_outer_frames
    (fun j => (stage j).G)
    (fun j => reducedGlobalTailCut (polynomialEmbedding K) (support a b s) (stage j).F (w+1))
    (fun j => regularitySurface (polynomialEmbedding K) (stage j).F)
    base hactive (fun j => RCN315.residualStage_pderiv_one_ne_zero_of_support (stage j))
    (Set.range (polynomialEmbedding K))
    (Set.infinite_range_of_injective (polynomialEmbedding_injective K))
  let geometry (j : J) : ReducedActiveGeometry (stage j) := {
    base := base j
    hactive := hactive j
    hZ := hZ j
    data := data j
    lam_poly := by rw [(heq j).1]; exact hlam
    mu_poly := by rw [(heq j).2]; exact hmu }
  exact ⟨lam,mu,hlam,hmu,geometry,heq⟩

end
end ProximityPrize.SubmissionLower.MovingSourceOuterStageFrames6814
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider MovingFiberThreeSources6811
open MovingSourcePairEnvelope6814 MovingSourceTwoProfiles6814
open MovingSourceCoupledClearing6814
local notation "w" => RCN326.w

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

end
end ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN095

theorem mixed_linear_first (p q r : FlagDegree) :
    flagMixed p q r=p.zOnly*flagMixed unitZFlag q r+
      p.yz*flagMixed unitYZFlag q r+p.all*flagMixed unitAllFlag q r := by
  unfold flagMixed unitZFlag unitYZFlag unitAllFlag
  ring

theorem mixed_sum_linear (p q r s : FlagDegree) :
    flagMixed p q r+flagMixed p q s=
      p.zOnly*(flagMixed unitZFlag q r+flagMixed unitZFlag q s)+
      p.yz*(flagMixed unitYZFlag q r+flagMixed unitYZFlag q s)+
      p.all*(flagMixed unitAllFlag q r+flagMixed unitAllFlag q s) := by
  rw [mixed_linear_first p q r,mixed_linear_first p q s]
  ring

end ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.MovingSourceIdentityFirstCharge6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 25000
open scoped BigOperators
open RCN095 RCN198 RCN327 LocatorHybridCells MovingSourcePairRetainedStage6814
open MovingSourceFirstChargeAlgebra6814

def identityDegree (p : FlagDegree) : ℕ :=
  RCN146.identityCurveDegree p (cellA 3561 57) (cellB 57 12) (cellS 12) RCN326.w

theorem identityDegree_linear (p : FlagDegree) :
    identityDegree p=p.zOnly*identityDegree unitZFlag+p.yz*identityDegree unitYZFlag+p.all*identityDegree unitAllFlag := by
  exact mixed_sum_linear p (RCN203.paddedCut (cellA 3561 57) (cellB 57 12) (cellS 12) (RCN326.w+1))
    unitZFlag unitYZFlag

end
end ProximityPrize.SubmissionLower.MovingSourceIdentityFirstCharge6814
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.MovingSourceUniformTail6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 20000
open RCN074 RCN086 RCN095 RCN135 RCN136 RCN244 RCN313
open MovingSourceDenominatorSeeds6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p errorCap : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {stageSupport : RCN275.ResidualSupportParameters}

theorem geometric_tail_dvd_iff_original
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hF : Irreducible S.F) (n : ℕ) :
    S.G∣globalTailCut (polynomialEmbedding K) S.F n ↔ S.F∣numerator K S.F n := by
  rw [globalTailCut_dvd_iff (polynomialEmbedding K) (polynomialEmbedding_injective K)]
  constructor
  · intro hG
    by_contra hnot
    have hrel := surfaceMap_relPrime S.F (numerator K S.F n) hF.ne_zero
      (hF.isRelPrime_iff_not_dvd.mpr hnot)
    exact S.irreducible_G.not_isUnit (hrel S.G_dvd_surface hG)
  · intro hdiv
    exact S.G_dvd_surface.trans (map_dvd (surfaceMap (polynomialEmbedding K)) hdiv)

end
end ProximityPrize.SubmissionLower.MovingSourceUniformTail6814
end MergedPart9
