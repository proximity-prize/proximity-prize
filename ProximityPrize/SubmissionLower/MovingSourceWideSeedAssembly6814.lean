import ProximityPrize.SubmissionLower.MovingSourceWideExceptions6814

/-! Full checked-cell seed count for the small-source-only linear owner.
Reuse the original exhaustive four-way seed cover, with every widened
geometric and exceptional count proved before adding the costs. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWideSeedAssembly6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN002 RCN074 RCN086 RCN095 RCN135 RCN136 RCN174 RCN238 RCN243 RCN244 RCN264 RCN330
open MovingSourceLinearFlow6814 MovingSourceReducedGamma6814
open MovingSourceProperSeedCount6814 MovingSourceConstantSeeds6814 MovingSourcePersistentSeeds6814
open MovingSourceDenominatorSeeds6814 MovingSourceLinearSeedAssembly6814
open MovingSourceWideLinearFlow6814 MovingSourceWideProperSeeds6814 MovingSourceWideExceptions6814

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

/-- Complete checked-cell linear-owner count. No cardinality inequality
or exceptional-component classification is an input. The remaining
profile hypotheses are the ordinary stage geometry and received-word
agreement bounds required by the pre-existing tangent consumer. -/
theorem checked_wide_linear_owner_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hp : p=2130706433) (he : errorCap=80889)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : WideLinearRoute S.F J)
    (hS : PolynomialInFlag ⟨3504,45,12⟩ S.G)
    (hFY : S.F.degreeOf 1≤57) (hFR : S.F.degreeOf 2≤12) (hFZ : S.F.degreeOf 3≤3561)
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card)
    (bound seedCap slopeCap : ℕ) (hshort : RCN326.w+1≤bound) (hchar : bound<p)
    (hbox : S.F∈globalCoefficientBox K bound RCN326.w seedCap slopeCap) :
    Gamma.card≤143434076546795600 := by
  have hH := wide_denominator_proper S J hroute
  have hsmall : flagMixed ⟨3504,45,12⟩ wideFirstFlag unitZFlag<p := by
    rw [hp]
    exact wide_gamma_budget.2
  have hd := wide_checked_denominator_seed_count S hp he J hroute hS hFY hFR hFZ hnodes hagreement
  have hpr := checked_wide_proper_seed_count S hp hfirst J hroute hS
  have hc := (wide_constant_seed_sum_le S hfirst J hroute hH ⟨3504,45,12⟩ hS).trans_eq wide_constant_checked_budget
  have ht := wide_persistent_seed_sum_le S hfirst J hroute hH ⟨3504,45,12⟩ hS hsmall
    181255 bound seedCap slopeCap (by omega) hagreement (by decide)
    hshort hchar hbox
  have htCost : (errorCap+1)*flagMixed ⟨3504,45,12⟩ wideFirstFlag unitYZFlag=723646569172920 := by
    rw [he]
    exact wide_persistent_checked_budget
  have ht' := ht.trans_eq htCost
  calc
    Gamma.card≤_ := linear_seed_cover S hfirst J
    _≤4302466850810+(142706085158652585+(42352119285+723646569172920)) :=
      Nat.add_le_add hd (Nat.add_le_add hpr (Nat.add_le_add hc ht'))
    _=143434076546795600 := by decide +kernel

theorem checked_wide_linear_owner_seed_count_fits :
    143434076546795600<272069082261391681 := by decide +kernel


#print axioms checked_wide_linear_owner_seed_count
#print axioms checked_wide_linear_owner_seed_count_fits
end
end ProximityPrize.SubmissionLower.MovingSourceWideSeedAssembly6814
