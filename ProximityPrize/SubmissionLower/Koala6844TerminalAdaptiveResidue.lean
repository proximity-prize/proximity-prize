import ProximityPrize.SubmissionLower.Koala6844TerminalEndpointApply
import ProximityPrize.SubmissionLower.Koala6844TerminalIntrinsic
import ProximityPrize.SubmissionLower.Koala6844ReceiptsExactBand
import ProximityPrize.SubmissionLower.Koala6831MovingSchedule


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical
open RCN081 RCN095 RCN130 RCN140 RCN266
open LocatorBatchProductRoute LocatorFactorAggregate
open Koala6831MovingAdaptive (aggregateFlag aggregateFlag_pos)
open Koala6844Receipts Koala6844Normalization

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4200
set_option maxHeartbeats 1500000

def AdaptiveEndpointCover (table : List CertifiedEndpoint) : Prop :=
  ∀ f : Flag, 0 < f.r → f.ordered → f.cumulativeLE afterRooms →
    ¬ geometricGate flowWidth (bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap) f.toFlagDegree →
    ¬ geometricGate flowWidth (bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap) f.toFlagDegree →
    ∃ e ∈ table, f.cumulativeLE e.flag

variable {K I : Type} [Field K] [CharP K 2130706433] [DecidableEq K] [DecidableEq I] [Fintype I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {excess : Nat}

omit [CharP K 2130706433] [DecidableEq K] in
private theorem physical_toFlagDegree (F : MvPolynomial (Fin 4) K) :
    (physicalFlag F).toFlagDegree = originalCumulativeFlag F := by
  change geometryFlag (physicalFlag F).increments = _
  rw [physicalFlag_increments, geometryFlag_increments]

private theorem flag_fit_of_below {f g : Flag} (hf : f.ordered) (hg : g.ordered)
    (h : Below f.toFlagDegree g.toFlagDegree) : f.cumulativeLE g := by
  obtain ⟨hr,hy,ht⟩ := h
  change middle f.toFlagDegree ≤ middle g.toFlagDegree at hy
  change total f.toFlagDegree ≤ total g.toFlagDegree at ht
  rw [Flag.toFlagDegree_middle f hf,Flag.toFlagDegree_middle g hg] at hy
  rw [Flag.toFlagDegree_total f hf,Flag.toFlagDegree_total g hg] at ht
  exact ⟨hr,hy,ht⟩

private theorem seeds_at_endpoint_le
    (data : CenteredVirtualData x domain σ 131071 180958 81186 excess)
    (full : Finset I) (hfull : domain ⊆ full) (hcount : full.card = 262144)
    (hSize : Fintype.card I ≤ 262144)
    (hPole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (remaining : Finset (RegularIndex H)) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1)
    (e : CertifiedEndpoint) (hfit : (physicalFlag (regularProduct H remaining)).cumulativeLE e.flag)
    (hTerm : terminalMetadata e = true) (hRaw : intrinsicRawMetadata e = true)
    (margins : ∀ i : Fin contactProfiles.size, sourceMargin contactProfiles[i])
    (seeds : Finset K) (hsub : seeds ⊆ data.seeds)
    (hcover : seeds ⊆ remaining.biUnion (regularSeeds H data.selected seeds)) :
    seeds.card ≤ terminalBudget := by
  rcases e with ⟨f,price,receipt⟩
  cases receipt with
  | intrinsic _ _ =>
    have hguard : intrinsicRawGuard f = true := hRaw
    have hdata := (centered_terminalSeedData data full hfull hcount).subset hsub
    have hcov : seeds ⊆ @Finset.biUnion _ K (Classical.decEq K) remaining (regularSeeds H data.selected seeds) := by
      simpa only [Finset.subset_iff,Finset.mem_biUnion] using hcover
    exact intrinsic_regular_family H hH remaining D hD hDchar hcontact
      f hguard hfit full x (data.received 0) (data.received 1) data.selected seeds hdata hcov
  | terminal src hprice hfits =>
    have hmeta := terminalMetadata_of_check f price src hprice hfits hTerm
    exact (centered_terminal_bound_of_metadata data full hfull hcount hSize hPole hLead
      H hH remaining D hD hDchar hcontact f src price hprice hfit hmeta margins seeds hsub hcover).trans hfits

theorem adaptive_residue_card_le_terminal
    (data : CenteredVirtualData x domain σ 131071 180958 81186 excess)
    (full : Finset I) (hfull : domain ⊆ full) (hcount : full.card = 262144)
    (hSize : Fintype.card I ≤ 262144)
    (hPole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (remaining : Finset (RegularIndex H)) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1)
    (hFit : Below (aggregateFlag H remaining) afterRooms.toFlagDegree)
    (hStop : remaining = ∅ ∨
      ¬ geometricGate flowWidth (bandSourceNumbers firstAdaptiveFlag firstAdaptiveGap)
        (aggregateFlag H remaining) ∧
      ¬ geometricGate flowWidth (bandSourceNumbers secondAdaptiveFlag secondAdaptiveGap)
        (aggregateFlag H remaining))
    (table : List CertifiedEndpoint) (hTable : AdaptiveEndpointCover table)
    (hTerm : ∀ e ∈ table, terminalMetadata e = true)
    (hRaw : ∀ e ∈ table, intrinsicRawMetadata e = true)
    (margins : ∀ i : Fin contactProfiles.size, sourceMargin contactProfiles[i])
    (seeds : Finset K) (hsub : seeds ⊆ data.seeds)
    (hcover : seeds ⊆ remaining.biUnion (regularSeeds H data.selected seeds)) :
    seeds.card ≤ terminalBudget := by
  by_cases hempty : remaining = ∅
  · have h : seeds.card ≤ 0 := by simpa [hempty] using Finset.card_le_card hcover
    exact h.trans (Nat.zero_le _)
  · let f := physicalFlag (regularProduct H remaining)
    have hflag : f.toFlagDegree = aggregateFlag H remaining := physical_toFlagDegree _
    have hord : f.ordered := physicalFlag_ordered _
    have hRoom : afterRooms.ordered := by
      rw [afterRooms_eq]
      change 50 ≤ 230 ∧ 230 ≤ 21999
      decide
    have hpos : 0 < f.r := by
      have h := aggregateFlag_pos H (Finset.nonempty_iff_ne_empty.mpr hempty)
      change 0 < f.toFlagDegree.all
      rw [hflag]
      exact h
    have hf : f.cumulativeLE afterRooms := flag_fit_of_below hord hRoom (hflag.symm ▸ hFit)
    obtain ⟨fail₁,fail₂⟩ := hStop.resolve_left hempty
    obtain ⟨e,he,hfite⟩ := hTable f hpos hord hf (hflag.symm ▸ fail₁) (hflag.symm ▸ fail₂)
    exact seeds_at_endpoint_le data full hfull hcount hSize hPole hLead H hH remaining D
      hD hDchar hcontact e hfite (hTerm e he) (hRaw e he) margins seeds hsub hcover

end
end ProximityPrize.SubmissionLower.Koala6844Terminal
