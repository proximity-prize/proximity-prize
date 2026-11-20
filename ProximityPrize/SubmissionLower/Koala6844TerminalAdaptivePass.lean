import ProximityPrize.SubmissionLower.Koala6844TerminalAdaptiveResidue
import ProximityPrize.SubmissionLower.Koala6844VirtualShortAdaptiveExhaustion


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open RCN081 RCN095 RCN140 RCN266
open LocatorFactorAggregate
open Koala6831MovingAdaptive (aggregateFlag aggregateFlag_mono)
open Koala6844Receipts Koala6844Normalization Koala6844VirtualShort

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000

variable {K I : Type} [Field K] [CharP K 2130706433] [DecidableEq K] [DecidableEq I] [Fintype I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {excess : Nat}

theorem short_pass_residue_card_le_terminal
    (data : CenteredVirtualData x domain σ 131071 180958 81186 excess)
    (full : Finset I) (hfull : domain ⊆ full) (hcount : full.card = 262144)
    (hSize : Fintype.card I ≤ 262144)
    (hPole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (A : Finset (RegularIndex H)) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1)
    (hFit : Below (aggregateFlag H A) afterRooms.toFlagDegree)
    {first second : CenteredAdaptiveSource data prime} {δ : Nat}
    (pass₁ : CenteredAdaptivePass first δ H A)
    (pass₂ : CenteredAdaptivePass second δ H pass₁.residue)
    (hStop : pass₂.residue = ∅ ∨
      ¬ geometricGate flowWidth (bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap)
        (aggregateFlag H pass₂.residue) ∧
      ¬ geometricGate flowWidth (bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap)
        (aggregateFlag H pass₂.residue))
    (table : List CertifiedEndpoint) (hTable : AdaptiveEndpointCover table)
    (hTerm : ∀ e ∈ table, terminalMetadata e = true)
    (hRaw : ∀ e ∈ table, intrinsicRawMetadata e = true)
    (margins : ∀ i : Fin contactProfiles.size, sourceMargin contactProfiles[i])
    (seeds : Finset K) (hsub : seeds ⊆ data.seeds)
    (hcover : seeds ⊆ pass₂.residue.biUnion (regularSeeds H data.selected seeds)) :
    seeds.card ≤ terminalBudget := by
  have h := aggregateFlag_mono H (pass₂.subset_incoming.trans pass₁.subset_incoming)
  have fit : Below (aggregateFlag H pass₂.residue) afterRooms.toFlagDegree :=
    ⟨h.1.trans hFit.1,h.2.1.trans hFit.2.1,h.2.2.trans hFit.2.2⟩
  exact adaptive_residue_card_le_terminal data full hfull hcount hSize hPole hLead H hH pass₂.residue
    D hD hDchar hcontact fit hStop table hTable hTerm hRaw margins seeds hsub hcover

end
end ProximityPrize.SubmissionLower.Koala6844Terminal
