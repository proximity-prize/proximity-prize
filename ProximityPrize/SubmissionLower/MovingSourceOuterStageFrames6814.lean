import ProximityPrize.SubmissionLower.MovingSourceOuterSliceLabels6814

/-! Actual proper-first-tail Stages supply one common reduced geometry.
The frame construction does not assume its bases or active-coordinate
conditions: they come from each Stage's existing projection theorem. -/
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

#print axioms exists_common_stage_geometry
end
end ProximityPrize.SubmissionLower.MovingSourceOuterStageFrames6814
