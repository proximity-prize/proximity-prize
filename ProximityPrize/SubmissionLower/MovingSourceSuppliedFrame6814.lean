import ProximityPrize.SubmissionLower.MovingSourceOuterChannel6814
namespace ProximityPrize.SubmissionLower.MovingSourceSuppliedFrame6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 30000
open scoped Classical
open RCN030 RCN066 RCN086 RCN095 RCN135 RCN136 RCN159 RCN198 RCN199 RCN207 RCN237 RCN243 RCN244 RCN263 RCN264 RCN275
open RCN327 RCN332 RCN334 RCN336 RCN338 RCN340 RCN341 RCN344
open RCN002 RCN037 RCN038 RCN042 RCN074 RCN134 RCN156 RCN248
open LocatorHybridTransportC2 CommonLinearChannels6807

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p errorCap a b s : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p]
local notation "Ω" => GenericField K
variable (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (support a b s))
variable (hp : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1)) (geometry : ReducedActiveGeometry S)

def suppliedReducedUnit :=
  activeNestedUnitFamily geometry.base geometry.hactive geometry.hZ
    (RCN315.residualStage_pderiv_one_ne_zero_of_support S) geometry.data
    S.irreducible_G (reducedFirstCut_proper S hp)
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag (support a b s) (w+1)) (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))

def suppliedBase (C : FirstTailComponent S) : SeparableLiteralCoordinate C.1 := by
  let C' : RegularComponent Ω S.G (reducedFirstCut S)
      (regularitySurface (polynomialEmbedding K) S.F) :=
    ⟨C.1,by
      rw [←regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
      exact C.2⟩
  exact geometry.base C'

def suppliedUnit := unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
  (suppliedReducedUnit S hp geometry) (suppliedBase S geometry)

def suppliedCommon : CommonLinearValues (suppliedUnit S hp geometry) :=
  of_congruent_cut (ordinary_sub_reducedFirstCut_dvd S) (suppliedReducedUnit S hp geometry)
    (suppliedBase S geometry)
    (of_active_nested geometry.base geometry.hactive geometry.hZ
      (RCN315.residualStage_pderiv_one_ne_zero_of_support S) geometry.data
      S.irreducible_G (reducedFirstCut_proper S hp)
      ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
      ((support_subset_flagSupport_iff
        (reducedResidualAgreementFlag (support a b s) (w+1)) (reducedFirstCut S)).2 (reducedFirstCut_in_flag S)))

theorem suppliedCommon_lam : (suppliedCommon S hp geometry).lam=geometry.data.lam := rfl
theorem suppliedCommon_mu : (suppliedCommon S hp geometry).mu=geometry.data.mu := rfl

def suppliedBudget := (suppliedUnit S hp geometry).toPrimeFlagBudgetFamily

theorem suppliedBudget_yzPositive (C : FirstTailComponent S) :
    1≤(suppliedBudget S hp geometry).yzCost C := by
  let C' : RegularComponent Ω S.G (reducedFirstCut S)
      (regularitySurface (polynomialEmbedding K) S.F) :=
    ⟨C.1,by
      rw [←regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
      exact C.2⟩
  change 1≤coordinateDegree Ω (CoordinateField Ω C.1) ((suppliedUnit S hp geometry).yzProjection C)
  apply one_le_coordinateDegree_of_transcendental_value
  rw [common_u_value (suppliedUnit S hp geometry) (suppliedCommon S hp geometry) C,
    suppliedCommon_lam,eval_linearU]
  exact geometry.data.uTranscendental C'

theorem suppliedBudget_yzPole (C : FirstTailComponent S) :
    LiteralSupportPoleBound (suppliedBase S geometry C) (flagSupport unitYZFlag)
      ((suppliedBudget S hp geometry).yzCost C) := by
  exact (suppliedUnit S hp geometry).toAdaptiveUnitPoleBudget.yzPole C

theorem supplied_u_value (lam : Ω) (hlam : geometry.data.lam=lam) (C : FirstTailComponent S) :
    coordinateValue Ω (CoordinateField Ω C.1) ((suppliedUnit S hp geometry).yzProjection C)=
      coordinateEvaluation Ω C.1 (linearU lam) := by
  have hh := common_u_value (suppliedUnit S hp geometry) (suppliedCommon S hp geometry) C
  simpa only [suppliedCommon_lam,hlam] using hh

theorem supplied_a_value (lam mu : Ω) (hlam : geometry.data.lam=lam) (hmu : geometry.data.mu=mu)
    (C : FirstTailComponent S) :
    coordinateValue Ω (CoordinateField Ω C.1) ((suppliedUnit S hp geometry).allProjection C)=
      coordinateEvaluation Ω C.1 (linearA mu lam) := by
  have hh := common_a_value (suppliedUnit S hp geometry) (suppliedCommon S hp geometry) C
  simpa only [suppliedCommon_lam,suppliedCommon_mu,hlam,hmu] using hh

end
end ProximityPrize.SubmissionLower.MovingSourceSuppliedFrame6814
