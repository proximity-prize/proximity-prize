import ProximityPrize.SubmissionLower.Koala6844VirtualShortFeeInputs
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPrimary


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical
open RCN095 RCN140 RCN266 RCN286
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open Koala6831MovingAdaptive (aggregateFlag)
open Koala6844Receipts Koala6844Normalization Koala6844Terminal

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4200
set_option maxHeartbeats 2500000

variable {K I : Type} [Field K] [CharP K prime] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {excess : Nat}

omit [CharP K prime] in
private theorem primary_phase_cover (H : MvPolynomial (Fin 4) K)
    (D : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hcover : seeds ⊆ shortPrimaryExcluded seeds selected H D ∪
      (transverseFactors H D).biUnion (shortRegularSeeds seeds selected)) :
    seeds ⊆ shortPrimaryExcluded seeds selected H D ∪
      phaseSeeds H selected seeds (transverseRegularFactors H D) := by
  intro g hg
  have h := hcover hg
  simp only [phaseSeeds,Finset.mem_union,Finset.mem_biUnion] at h ⊢
  rcases h with he | ⟨F,hF,hgF⟩
  · exact Or.inl he
  · simp only [transverseFactors,Finset.mem_filter] at hF
    simp only [shortRegularSeeds,shortFactorSeeds,Finset.mem_filter] at hgF
    let P : RegularIndex H := ⟨F,hF.1⟩
    have hP : P ∈ transverseRegularFactors H D := by
      simpa only [transverseRegularFactors,Finset.mem_filter,Finset.mem_univ,true_and] using hF.2
    have hsol : RegularSolution P.1 (selected g) g := ⟨hgF.1.2,hgF.2⟩
    have hreg : g ∈ regularSeeds H selected seeds P :=
      (@Finset.mem_filter _ _ _ _ _).mpr ⟨hg,hsol⟩
    exact Or.inr ⟨P,hP,hreg⟩

private theorem pay_short_phases (n initial a b c d e room₁ room₂ adaptive₁ adaptive₂ : Nat)
    (hn : n ≤ initial+a) (ha : a ≤ room₁+b) (hb : b ≤ room₂+c)
    (hc : c ≤ adaptive₁+d) (hd : d ≤ adaptive₂+e)
    (h₀ : initial ≤ shortSymbolicBudget) (h₁ : room₁ ≤ 1911244048176055)
    (h₂ : room₂ ≤ 524153822751450) (h₃ : adaptive₁ ≤ 524260342023650)
    (h₄ : adaptive₂ ≤ 5723913147137156) (h₅ : e ≤ terminalBudget) :
    n ≤ 274566834571012320 := by
  unfold shortSymbolicBudget at h₀
  unfold terminalBudget at h₅
  omega

omit [CharP K prime] [DecidableEq K] in
private theorem short_adaptive_field_cap
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hfit : Below (aggregateFlag H A) afterRooms.toFlagDegree)
    (hField : (185 : ENat) < ENat.card K) : A.card < ENat.card K := by
  have hs : (aggregateFlag H A).all ≤ 185 :=
    hfit.1.trans (show afterRooms.toFlagDegree.all ≤ 185 by decide)
  have h := (short_regular_card_le_slope H A).trans hs
  exact (by exact_mod_cast h : (A.card : ENat) ≤ 185).trans_lt hField

variable [Fintype I]

theorem short_centered_support_bound
    (data : CenteredVirtualData x domain σ degree agreements 81187 excess)
    (hσ : ∀ g ∈ data.seeds, σ g = g^2130706433)
    (full : Finset I) (hfull : domain ⊆ full) (hcount : full.card = 262144)
    (hSize : Fintype.card I ≤ 262144) (hField : (185 : ENat) < ENat.card K)
    (hpole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (hFees : ShortPhaseFees data ((Finset.card_le_univ domain).trans hSize) hpole)
    (table : List CertifiedEndpoint) (hTable : AdaptiveEndpointCover table)
    (hTerm : ∀ e ∈ table, terminalMetadata e = true)
    (hRaw : ∀ e ∈ table, intrinsicRawMetadata e = true)
    (margins : ∀ j : Fin contactProfiles.size, sourceMargin contactProfiles[j]) :
    data.seeds.card ≤ 274566834571012320 := by
  have hsize : domain.card ≤ nodes := (Finset.card_le_univ domain).trans hSize
  have hgap : 0 < firstJetGap primaryShape 0 := by rw [primary_firstJetGap_eq]; decide
  obtain ⟨H,hH,hbox,_,_,hzero⟩ := exists_checked_primary data hsize hpole hLead hgap
  have hbox' : H ∈ nestedCoefficientBox K primaryWeight 131071 47571 829 185 := hbox
  obtain ⟨hr,hy,ht,hcontact⟩ := short_primary_box_caps H primaryWeight hbox'
  let D := (centeredFlow data).flow
  let A := transverseRegularFactors H D
  let bill := phaseSeeds H data.selected data.seeds
  let excluded := shortPrimaryExcluded data.seeds data.selected H D
  obtain ⟨hcover0,hinitial⟩ :=
    centered_short_primary_cover_and_budget data hσ hpole H hH hr hy ht hsize hzero
  have hcover : data.seeds ⊆ excluded ∪ bill A :=
    primary_phase_cover H D data.seeds data.selected hcover0
  have hcount0 : data.seeds.card ≤ excluded.card + (bill A).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have htrans := transverseRegularFactors_transverse H D
  have hfit := short_primary_fit H hH A primaryWeight hbox'
  have hgap₁ : 0 < firstJetGap firstRoomShape firstRoomCut := by
    rw [firstRoom_firstJetGap_eq]
    decide
  have hgap₂ : 0 < firstJetGap secondRoomShape secondRoomCut := by
    rw [secondRoom_firstJetGap_eq]
    decide
  obtain ⟨R₁,hR₁,R₂,hR₂,hfit₁,hfit₂,hpart₁,hpart₂⟩ :=
    exists_two_checked_room_passes data hsize hpole hLead hgap₁ hgap₂ H A hfit htrans
  have hfield₂ := short_adaptive_field_cap H R₂ hfit₂ hField
  have htrans₂ : ∀ F ∈ R₂, ¬ F.val ∣ ((centeredFlow data).flow) F.val :=
    fun F hF => htrans F (hR₁ (hR₂ hF))
  obtain ⟨pass₁,pass₂,hStop⟩ :=
    exists_two_short_receipt_passes data hsize hpole hLead H R₂ hfield₂ hfit₂ htrans₂
  let residue := bill pass₂.residue
  have hresidue : residue.card ≤ terminalBudget :=
    short_pass_residue_card_le_terminal data full hfull hcount hSize hpole hLead H hH R₂
      primaryWeight (by decide) (by decide) hcontact hfit₂ pass₁ pass₂ hStop table hTable hTerm hRaw margins
      residue (phaseSeeds_subset H data.selected data.seeds pass₂.residue)
      (phaseSeeds_regular_cover H data.selected data.seeds pass₂.residue)
  exact pay_short_phases _ _ _ _ _ _ _ _ _ _ _ hcount0
    (phaseSeeds_card_split H data.selected data.seeds A R₁)
    (phaseSeeds_card_split H data.selected data.seeds R₁ R₂)
    (phaseSeeds_card_split H data.selected data.seeds R₂ pass₁.residue)
    (phaseSeeds_card_split H data.selected data.seeds pass₁.residue pass₂.residue)
    hinitial (hFees.firstRoom H A R₁ hH hR₁ hfit hpart₁)
    (hFees.secondRoom H R₁ R₂ hH hR₂ hfit₁ hpart₂)
    (hFees.firstAdaptive H R₂ hH hfit₂ pass₁)
    (hFees.secondAdaptive H R₂ hH hfit₂ pass₁ pass₂) hresidue

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
