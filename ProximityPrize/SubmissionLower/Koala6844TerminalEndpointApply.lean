import ProximityPrize.SubmissionLower.Koala6844TerminalCentered
import ProximityPrize.SubmissionLower.Koala6844TerminalEndpointMeta
import ProximityPrize.SubmissionLower.Koala6844TerminalProfile
import ProximityPrize.SubmissionLower.Koala6844ReceiptsWellFormed


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical
open RCN081 RCN140 RCN266
open LocatorBatchProductRoute Koala6844Receipts Koala6844Normalization

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

private theorem terminalMetadata_profile (f : Flag) (src : Sources)
    (h : TerminalMetadata f src) (j : Fin 3) :
    ∃ i : Fin contactProfiles.size, contactProfiles[i] = shapeAt src j := by
  fin_cases j
  · exact h.z
  · exact h.yz
  · exact h.all

private theorem terminalMetadata_cap (f : Flag) (src : Sources) (h : TerminalMetadata f src) :
    src.totalCap ≤ 3873 := by
  obtain ⟨i,hi⟩ := h.z
  obtain ⟨j,hj⟩ := h.yz
  obtain ⟨k,hk⟩ := h.all
  unfold Sources.totalCap
  exact max_le (hi ▸ terminal_profile_total i)
    (max_le (hj ▸ terminal_profile_total j) (hk ▸ terminal_profile_total k))

private theorem terminalMetadata_valid (f : Flag) (src : Sources)
    (h : TerminalMetadata f src) (margins : ∀ i : Fin contactProfiles.size, sourceMargin contactProfiles[i])
    (j : Fin 3) :
    sourceWellFormed (shapeAt src j) = true ∧ sourceMargin (shapeAt src j) := by
  obtain ⟨i,hi⟩ := terminalMetadata_profile f src h j
  rw [← hi]
  exact ⟨terminal_profile_wellFormed i,margins i⟩

private theorem terminalMetadata_scale (f : Flag) (src : Sources) (h : TerminalMetadata f src)
    (j : Fin 3) :
    3*(shapeAt src j).k+3 ∣ graphScale := by
  obtain ⟨i,hi⟩ := terminalMetadata_profile f src h j
  rw [← hi]
  exact terminal_profile_graphScale i

variable {K I : Type} [Field K] [CharP K 2130706433] [DecidableEq K] [DecidableEq I] [Fintype I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {excess : Nat}

theorem centered_terminal_bound_of_metadata
    (data : CenteredVirtualData x domain σ 131071 180960 81184 excess)
    (full : Finset I) (hfull : domain ⊆ full) (hcount : full.card = 262144)
    (hSize : Fintype.card I ≤ 262144)
    (hPole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (remaining : Finset (RegularIndex H)) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1)
    (f : Flag) (src : Sources) (price : Nat) (hprice : terminalPrice f src = some price)
    (hfit : (physicalFlag (regularProduct H remaining)).cumulativeLE f)
    (hmeta : TerminalMetadata f src) (margins : ∀ i : Fin contactProfiles.size, sourceMargin contactProfiles[i])
    (seeds : Finset K) (hsub : seeds ⊆ data.seeds)
    (hcover : seeds ⊆ remaining.biUnion (regularSeeds H data.selected seeds)) :
    seeds.card ≤ price := by
  obtain ⟨hry,hyt,hyL,hLt⟩ := terminalPrice_order hprice
  exact centered_terminal_bound data full hfull hcount hSize hPole hLead
    H hH remaining D hD hDchar hcontact f src price hprice ⟨hry,hyt⟩ hyL hLt
    hmeta.slope hmeta.middle (terminalMetadata_cap f src hmeta) hfit
    (terminalMetadata_valid f src hmeta margins) (terminalMetadata_scale f src hmeta) seeds hsub hcover

end
end ProximityPrize.SubmissionLower.Koala6844Terminal
