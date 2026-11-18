import ProximityPrize.SubmissionLower.Koala6831MovingPaidStageCounts

namespace ProximityPrize.SubmissionLower.Koala6831MovingPaid

open scoped Classical BigOperators
open RCN095 RCN238 RCN266 RCN313 RCN319
open Koala6831Moving Koala6831MovingAdaptive Koala6831MovingSources Koala6831MovingStages
open LocatorBatchProductRoute (regularProduct regularProduct_dvd_carrier)
open LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag_all)

noncomputable section

variable {K I : Type} [Field K] [Fintype I]

structure AdaptivePrices : Prop where
  first : ∀ f (hpos : 0 < f.all), Below f postRoomCap →
    adaptiveGate Stage.adaptive1.numbers f → stagePrice f hpos Stage.adaptive1 600 ≤ 2243281056745829
  second : ∀ f (hpos : 0 < f.all), Below f postRoomCap →
    ¬ adaptiveGate Stage.adaptive1.numbers f → adaptiveGate Stage.adaptive2.numbers f →
    stagePrice f hpos Stage.adaptive2 1200 ≤ 824314952017431
  third : ∀ f (hpos : 0 < f.all), Below f postRoomCap →
    ¬ adaptiveGate Stage.adaptive1.numbers f → ¬ adaptiveGate Stage.adaptive2.numbers f →
    adaptiveGate Stage.adaptive3.numbers f → stagePrice f hpos Stage.adaptive3 6776 ≤ 2334906151847889

structure PaidRoute (H : P4 K) (Γ : Finset K) (selected : K → Polynomial K) where
  residue : Finset (RegularIndex H)
  below_room : Below (aggregateFlag H residue) postRoomCap
  stopped : residue = ∅ ∨
    ¬ adaptiveGate Stage.adaptive1.numbers (aggregateFlag H residue) ∧
    ¬ adaptiveGate Stage.adaptive2.numbers (aggregateFlag H residue) ∧
    ¬ adaptiveGate Stage.adaptive3.numbers (aggregateFlag H residue)
  paid : Γ.card + fixedRoomCredit₁ (aggregateFlag H residue) + fixedRoomCredit₂ (aggregateFlag H residue) ≤
    (residue.biUnion (regularFiber H Γ selected)).card + 24584613663490380

def PaidRoute.seeds {H : P4 K} {Γ : Finset K} {selected : K → Polynomial K} (route : PaidRoute H Γ selected) :
    Finset K := route.residue.biUnion (regularFiber H Γ selected)

private theorem below_trans {a b c : FlagDegree} (hab : Below a b) (hbc : Below b c) :
    Below a c := ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩

private theorem card_factor_union_split {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A B : Finset α) (fibers : α → Finset β) :
    (A.biUnion fibers).card ≤ ((A \ B).biUnion fibers).card + (B.biUnion fibers).card := by
  have hsub : A.biUnion fibers ⊆ (A \ B).biUnion fibers ∪ B.biUnion fibers := by
    intro g hg
    obtain ⟨F, hF, hfiber⟩ := Finset.mem_biUnion.mp hg
    by_cases hB : F ∈ B
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨F, hB, hfiber⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨F, Finset.mem_sdiff.mpr ⟨hF, hB⟩, hfiber⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private theorem factor_card_le_slope (H : P4 K) (A : Finset (RegularIndex H)) :
    A.card ≤ (aggregateFlag H A).all := by
  calc
    _ = ∑ F ∈ A, 1 := by simp
    _ ≤ ∑ F ∈ A, (contactFlag F.1).all := Finset.sum_le_sum fun F _ => RCN130.regularCumulativeFlag_positive H F
    _ = _ := by
      change _ = (contactFlag (regularProduct H A)).all
      rw [contactFlag_regularProduct, sumFlag_all]

private theorem adaptive_failure_in_subset (s : Stage) (H : P4 K)
    {R A : Finset (RegularIndex H)} (hsub : R ⊆ A) (hne : R.Nonempty)
    (hstop : A = ∅ ∨ ¬ adaptiveGate s.numbers (aggregateFlag H A)) :
    ¬ adaptiveGate s.numbers (aggregateFlag H R) := by
  intro hgate
  rcases hstop with hA | hA
  · simpa only [hA, Finset.not_nonempty_empty] using hne.mono hsub
  · exact hA (adaptiveGate_mono s.numbers (aggregateFlag_mono H hsub)
      (aggregateFlag_pos H hne) hgate)

theorem exists_paid_route [CharP K 2130706433]
    (prices : AdaptivePrices)
    (B : FlowData K) (x : I ↪ K) (u₀ u₁ word : I → K) (good : Finset I)
    (hcard : Fintype.card I = 262144)
    (hfixed : ∀ i ∈ good,
      B.d0.eval (x i) * u₀ i + B.c0.eval (x i) = B.a0.eval (x i) * word i ∧
      B.d0.eval (x i) * u₁ i + B.c1.eval (x i) = B.a1.eval (x i) * word i)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ 9554)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ weight + 9554)
    (H : P4 K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 53188 360 80)
    (Γ : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (Finset.univ.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hgood : ∀ γ ∈ Γ, ∀ i, (selected γ).eval (x i) = u₀ i + γ * u₁ i → i ∈ good)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81060)
    (hregular : ∀ γ ∈ Γ, ∃ F : RegularIndex H,
      specialization K (selected γ) γ F.1 = 0 ∧
      specialization K (selected γ) γ (polyH K F.1) ≠ 0 ∧ ¬ F.1 ∣ B.flow F.1) :
    Nonempty (PaidRoute H Γ selected) := by
  classical
  let xg : ↥good ↪ K := ⟨fun i => x i.1, fun _ _ h => Subtype.ext (x.injective h)⟩
  let ug₀ (i : ↥good) := u₀ i.1
  let ug₁ (i : ↥good) := u₁ i.1
  let wg (i : ↥good) := word i.1
  let support (γ : K) : Finset ↥good :=
    Finset.univ.filter (fun i => (selected γ).eval (xg i) = ug₀ i + γ * ug₁ i)
  have hnodes : (Finset.univ : Finset I).card = 262144 := Finset.card_univ.trans hcard
  have hcardg : Fintype.card (↥good) ≤ 262144 := by
    rw [Fintype.card_coe, ← hnodes]
    exact Finset.card_le_card (Finset.subset_univ _)
  have h₀ (i : ↥good) := (hfixed i.1 i.2).1
  have h₁ (i : ↥good) := (hfixed i.1 i.2).2
  have hvalues (γ : K) (i : ↥good) (hi : i ∈ support γ) :
      (selected γ).eval (xg i) = ug₀ i + γ * ug₁ i := (Finset.mem_filter.mp hi).2
  have hsupport (γ : K) (hγ : γ ∈ Γ) : agreement ≤ (support γ).card := by
    have hsub : Finset.univ.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i) ⊆
        (support γ).image Subtype.val := by
      intro i hi
      have hv := (Finset.mem_filter.mp hi).2
      exact Finset.mem_image.mpr ⟨⟨i, hgood γ hγ i hv⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    exact (hagreement γ hγ).trans ((Finset.card_le_card hsub).trans Finset.card_image_le)
  let A₀ := transverseRoomFactors B H
  let A₁ := stageRoomResidual Stage.room1 xg ug₀ ug₁ H A₀
  let A₂ := stageRoomResidual Stage.room2 xg ug₀ ug₁ H A₁
  let fibers := regularFiber H Γ selected
  have hcover : Γ ⊆ A₀.biUnion fibers := by
    intro γ hγ
    obtain ⟨F, hF, hreg, htrans⟩ := hregular γ hγ
    exact Finset.mem_biUnion.mpr ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrans⟩,
      mem_regularFiber.mpr ⟨hγ, hF, hreg⟩⟩
  have hA₀ (F : RegularIndex H) (hF : F ∈ A₀) : ¬ F.1 ∣ B.flow F.1 := (Finset.mem_filter.mp hF).2
  have hA₁ : A₁ ⊆ A₀ := stageRoomResidual_subset Stage.room1 xg ug₀ ug₁ H A₀
  have hA₂ : A₂ ⊆ A₁ := stageRoomResidual_subset Stage.room2 xg ug₀ ug₁ H A₁
  have hfit₀ : Below (aggregateFlag H A₀) primaryIncoming := by
    obtain ⟨hT, hY, hR, _⟩ := nested_mem_weights hbox hH
    apply below_trans (contactFlag_below_of_dvd hH (regularProduct_dvd_carrier H A₀))
    simp only [Below, contactFlag_all, contactFlag_middle, contactFlag_total]
    exact ⟨hR, hY, hT⟩
  have ⟨hfit₁, hfit₂⟩ := two_room_residue_caps xg ug₀ ug₁ hcardg H hH A₀ hbox
  have hsmall : (A₂.card : ENat) < ENat.card K := by
    have hA : A₂.card ≤ 30 := (factor_card_le_slope H A₂).trans hfit₂.1
    have hb := ENat.card_le_card_of_injective x.injective
    rw [ENat.card_eq_coe_fintype_card, hcard] at hb
    exact (show (A₂.card : ENat) < 262144 by exact_mod_cast hA.trans_lt (by decide : 30 < 262144)).trans_le hb
  have hpass (s : Stage) (R : Finset (RegularIndex H)) (hR : R ⊆ A₂) :
      ∃ pass : ExhaustedPass s xg ug₀ ug₁ H R,
        pass.residue ≠ R → adaptiveGate s.numbers (aggregateFlag H R) := by
    by_cases hgate : adaptiveGate s.numbers (aggregateFlag H R)
    · have hfield := show (R.card : ENat) < ENat.card K from
        (show (R.card : ENat) ≤ A₂.card by exact_mod_cast Finset.card_le_card hR).trans_lt hsmall
      obtain ⟨pass⟩ := exists_exhausted_adaptive_pass s B xg ug₀ ug₁ wg hcardg h₀ h₁ hden hminor
        H R hfield (below_trans (aggregateFlag_mono H hR) hfit₂)
        (fun F hF => hA₀ F (hA₁ (hA₂ (hR hF))))
      exact ⟨pass, fun _ => hgate⟩
    · refine ⟨⟨R, Finset.Subset.rfl, Or.inr hgate, ?_⟩, fun h => (h rfl).elim⟩
      intro F hF
      exact ((Finset.mem_sdiff.mp hF).2 (Finset.mem_sdiff.mp hF).1).elim
  obtain ⟨p₁, ha₁⟩ := hpass Stage.adaptive1 A₂ Finset.Subset.rfl
  obtain ⟨p₂, ha₂⟩ := hpass Stage.adaptive2 p₁.residue p₁.subset_incoming
  obtain ⟨p₃, ha₃⟩ := hpass Stage.adaptive3 p₂.residue (p₂.subset_incoming.trans p₁.subset_incoming)
  let final := p₃.residue
  have hfinal₁ : final ⊆ p₁.residue := p₃.subset_incoming.trans p₂.subset_incoming
  have hfinal₂ : final ⊆ A₂ := hfinal₁.trans p₁.subset_incoming
  have hfitFinal : Below (aggregateFlag H final) postRoomCap :=
    below_trans (aggregateFlag_mono H hfinal₂) hfit₂
  have hstopFinal :
      final = ∅ ∨ ¬ adaptiveGate Stage.adaptive1.numbers (aggregateFlag H final) ∧
        ¬ adaptiveGate Stage.adaptive2.numbers (aggregateFlag H final) ∧
        ¬ adaptiveGate Stage.adaptive3.numbers (aggregateFlag H final) := by
    rcases Finset.eq_empty_or_nonempty final with h | h
    · exact Or.inl h
    · exact Or.inr ⟨adaptive_failure_in_subset _ H hfinal₁ h p₁.stopped,
        adaptive_failure_in_subset _ H p₃.subset_incoming h p₂.stopped,
        adaptive_failure_in_subset _ H Finset.Subset.rfl h p₃.stopped⟩
  have roomCount (s : Stage) (A : Finset (RegularIndex H)) (hA : A ⊆ A₀)
      (hfin : final ⊆ stageRoomResidual s xg ug₀ ug₁ H A)
      (incoming : FlagDegree) (hpos : 0 < incoming.all)
      (hfit : Below (aggregateFlag H A) incoming) (hcap : Below incoming primaryIncoming) :
      ((A \ stageRoomResidual s xg ug₀ ug₁ H A).biUnion fibers).card +
        flagMixed (Koala6831MovingLedger.creditFlag (aggregateFlag H final))
          (stagePartnerFlag s s.roomOrder) (stageScaledCut incoming hpos) / agreementScale ≤
        stagePrice incoming hpos s s.roomOrder := by
    apply stageRoom_card_add_credit_of_subset s xg ug₀ ug₁ H A final hfin fibers incoming
      (stagePartnerFlag s s.roomOrder) (stageScaledCut incoming hpos) agreementScale_pos hfit
    intro F hF
    obtain ⟨hin, hout⟩ := Finset.mem_sdiff.mp hF
    obtain ⟨Q, hrel, hQbox, hsolution⟩ := B.exists_vanishing_stage_room_partner xg ug₀ ug₁ wg
      h₀ h₁ hden hminor s H A hin (hA₀ F (hA hin)) hout Γ selected support
      hdegree hsupport (fun γ _ i hi => hvalues γ i hi)
    exact regularFiber_le_paid_factor H A F hin incoming hpos hfit hcap s s.roomOrder Γ selected
      Finset.univ x u₀ u₁ x.injective.injOn hnodes hdegree hagreement hnoPencil Q hrel hQbox hsolution
  have hroom₁ := roomCount Stage.room1 A₀ Finset.Subset.rfl (hfinal₂.trans hA₂) primaryIncoming
    (by decide +kernel) hfit₀ ⟨le_rfl, le_rfl, le_rfl⟩
  have hroom₂ := roomCount Stage.room2 A₁ hA₁ hfinal₂ secondRoomIncoming
    (by decide +kernel) hfit₁ (by change 54 ≤ 80 ∧ 245 ≤ 360 ∧ 15351 ≤ 53188; decide +kernel)
  have adaptiveCount (s : Stage) (A : Finset (RegularIndex H)) (hA : A ⊆ A₂)
      (pass : ExhaustedPass s xg ug₀ ug₁ H A)
      (hacts : pass.residue ≠ A → adaptiveGate s.numbers (aggregateFlag H A)) (limit : ℕ)
      (hprice : ∀ hne : A.Nonempty, adaptiveGate s.numbers (aggregateFlag H A) →
        stagePrice (aggregateFlag H A) (aggregateFlag_pos H hne) s s.numbers.slopeCap ≤ limit) :
      ((A \ pass.residue).biUnion fibers).card ≤ limit := by
    by_cases hsame : pass.residue = A
    · simp [hsame]
    have hne : A.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      apply hsame
      apply Finset.Subset.antisymm pass.subset_incoming
      intro F hF
      have hf : F ∈ (∅ : Finset (RegularIndex H)) := hempty ▸ hF
      simp at hf
    have hfit : Below (aggregateFlag H A) (aggregateFlag H A) := ⟨le_rfl, le_rfl, le_rfl⟩
    have hcap : Below (aggregateFlag H A) primaryIncoming :=
      below_trans (below_trans (aggregateFlag_mono H hA) hfit₂)
        (by change 30 ≤ 80 ∧ 138 ≤ 360 ∧ 15351 ≤ 53188; decide +kernel)
    refine (paid_union_le_stagePrice H A (A \ pass.residue) Finset.sdiff_subset Γ selected
      (aggregateFlag H A) (aggregateFlag_pos H hne) hfit s s.numbers.slopeCap ?_).trans
      (hprice hne (hacts hsame))
    intro F hF
    have hin := (Finset.mem_sdiff.mp hF).1
    obtain ⟨Q, hrel, hQbox, hcontact⟩ := pass.partners F hF
    have hsolution (γ : K) (hγ : γ ∈ Γ) : specialization K (selected γ) γ Q = 0 :=
      specialization_zero_of_box_and_agreement xg ug₀ ug₁ s Q (selected γ) γ (support γ)
        hQbox (fun i _ => hcontact i) (hdegree γ hγ) (hsupport γ hγ) (hvalues γ)
    exact regularFiber_le_paid_factor H A F hin (aggregateFlag H A) (aggregateFlag_pos H hne)
      hfit hcap s s.numbers.slopeCap Γ selected Finset.univ x u₀ u₁ x.injective.injOn hnodes
      hdegree hagreement hnoPencil Q hrel hQbox hsolution
  have had₁ := adaptiveCount Stage.adaptive1 A₂ Finset.Subset.rfl p₁ ha₁ 2243281056745829
    (fun hne hgate => prices.first _ (aggregateFlag_pos H hne) hfit₂ hgate)
  have had₂ := adaptiveCount Stage.adaptive2 p₁.residue p₁.subset_incoming p₂ ha₂ 824314952017431
    (fun hne hgate => prices.second _ (aggregateFlag_pos H hne)
      (below_trans (aggregateFlag_mono H p₁.subset_incoming) hfit₂)
      (adaptive_failure_in_subset _ H Finset.Subset.rfl hne p₁.stopped) hgate)
  have had₃ := adaptiveCount Stage.adaptive3 p₂.residue (p₂.subset_incoming.trans p₁.subset_incoming)
    p₃ ha₃ 2334906151847889 (fun hne hgate => prices.third _ (aggregateFlag_pos H hne)
      (below_trans (aggregateFlag_mono H (p₂.subset_incoming.trans p₁.subset_incoming)) hfit₂)
      (adaptive_failure_in_subset _ H p₂.subset_incoming hne p₁.stopped)
      (adaptive_failure_in_subset _ H Finset.Subset.rfl hne p₂.stopped) hgate)
  have hh₁ := card_factor_union_split A₀ A₁ fibers
  have hh₂ := card_factor_union_split A₁ A₂ fibers
  have hh₃ := card_factor_union_split A₂ p₁.residue fibers
  have hh₄ := card_factor_union_split p₁.residue p₂.residue fibers
  have hh₅ := card_factor_union_split p₂.residue final fibers
  have hcount := Finset.card_le_card hcover
  change ((A₀ \ A₁).biUnion fibers).card + fixedRoomCredit₁ (aggregateFlag H final) ≤ fixedRoomPrice₁ at hroom₁
  change ((A₁ \ A₂).biUnion fibers).card + fixedRoomCredit₂ (aggregateFlag H final) ≤ fixedRoomPrice₂ at hroom₂
  rw [fixedRoomPrice₁_value] at hroom₁
  rw [fixedRoomPrice₂_value] at hroom₂
  change ((p₂.residue \ final).biUnion fibers).card ≤ 2334906151847889 at had₃
  refine ⟨⟨final, hfitFinal, hstopFinal, ?_⟩⟩
  change Γ.card + fixedRoomCredit₁ (aggregateFlag H final) + fixedRoomCredit₂ (aggregateFlag H final) ≤
    (final.biUnion fibers).card + 24584613663490380
  omega

end

end ProximityPrize.SubmissionLower.Koala6831MovingPaid
