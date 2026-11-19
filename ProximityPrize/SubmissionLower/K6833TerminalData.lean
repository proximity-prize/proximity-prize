/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from Lucieno, BitWonka, and Bome2017's terminal proofs. -/
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentRetainedGraph
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentRaw
import ProximityPrize.SubmissionLower.K6833TerminalNumeric
import ProximityPrize.SubmissionLower.Koala6831MovingPaidStageCounts

namespace ProximityPrize.SubmissionLower.K6833Residual
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open LocatorHybridCells LocatorFactorAggregate LocatorBatchProductRoute LocatorLowQuotient
open Koala6831Moving Koala6831MovingAdaptive Koala6831MovingPaid
open K6833TerminalIncumbentGraph (axisPrice)
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

structure TerminalData (x : I ↪ K) where
  primary : MvPolynomial (Fin 4) K
  primary_ne : primary ≠ 0
  primary_box : primary ∈ nestedCoefficientBox K 57757821 131071 53215 440 98
  seeds : Finset K
  u₀ : I → K
  u₁ : I → K
  selected : K → Polynomial K
  nodes_card : Fintype.card I = 262144
  degree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071
  agreement : ∀ g ∈ seeds, 181059 ≤
    (Finset.univ.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card
  pencil : NoLargeSelectedPencil selected seeds 131071 81085

theorem TerminalData.factor_global_box {x : I ↪ K} (T : TerminalData x) (F : RegularIndex T.primary)
    {support : ResidualSupportParameters} (hData : ResidualSupportData support F.1) :
    F.1 ∈ RCN174.globalCoefficientBox K 57757821 131071 support.total support.s := by
  have hdiv := (positiveRFactors_spec T.primary F.1 F.2).2.1
  have hcut := (nested_mem_weights T.primary_box T.primary_ne).2.2.2
  have hF := (weightedTotalDegree_le_of_dvd (contactWeights 131071) F.1 T.primary hdiv
    T.primary_ne).trans_lt hcut
  intro d hd
  have hT := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans hData.total_weight
  have hS := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hData.s_weight
  have hX := (MvPolynomial.le_weightedTotalDegree (contactWeights 131071) hd).trans_lt hF
  exact ⟨by
      have htotal : d 1 + d 2 + d 3 ≤ support.total := by simpa [weight_fin4, residualTotalWeights] using hT
      change d 1 + d 3 ≤ support.total
      omega,
    by simpa [weight_fin4, residualSWeights] using hS,
    by simpa only [contact_weight] using hX⟩

private theorem small_padded_bounds (f : Envelope)
    (hf : f.slope ≤ 16 ∧ f.middle ≤ 67 ∧ f.total ≤ 8870)
    (k : ℕ) (hk : k ≤ 2) :
    let a := f.pad k
    3 ≤ a.slope ∧ a.slope+2 ≤ a.middle ∧ a.middle+k ≤ a.total ∧
      a.slope ≤ 31 ∧ a.middle ≤ 142 ∧ a.total ≤ 8870 := by
  simp only [Envelope.pad]
  omega

private theorem paddedSupport_eq_cellSupport (f : Envelope) (k : ℕ) :
    f.paddedSupport k =
      cellSupport (f.pad k).total (f.pad k).middle (f.pad k).slope := by
  have hr : 3 ≤ (f.pad k).slope := by simp [Envelope.pad]
  have hy : (f.pad k).slope+2 ≤ (f.pad k).middle := by simp [Envelope.pad]
  have ht : (f.pad k).middle ≤ (f.pad k).total := by
    change max f.middle (max 3 f.slope + 2) ≤ max f.total (max f.middle (max 3 f.slope + 2) + k)
    exact (Nat.le_add_right _ _).trans (le_max_right _ _)
  have hs : (f.pad k).slope-2+2 = (f.pad k).slope := by omega
  have hm : (f.pad k).middle-(f.pad k).slope-1+((f.pad k).slope-2)+3 =
      (f.pad k).middle := by omega
  have htotal : (f.pad k).total-(f.pad k).middle+
      ((f.pad k).middle-(f.pad k).slope-1)+((f.pad k).slope-2)+3 =
      (f.pad k).total := by omega
  unfold Envelope.paddedSupport cellSupport RCN198.support cellA cellB cellS
  congr <;> omega

omit [CharP K 2130706433] in
theorem factor_below_endpoint
    (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (f : Envelope) (hfit : Below (aggregateFlag H remaining) f.flag)
    (F : RegularIndex H) (hF : F ∈ remaining) :
    Below (originalCumulativeFlag F.1) f.flag := by
  have hdiv : F.1 ∣ regularProduct H remaining :=
    ⟨regularCofactor H remaining F, (regularFactor_mul_cofactor H remaining F hF).symm⟩
  have hle := contactFlag_below_of_dvd (regularProduct_ne_zero H remaining) hdiv
  exact ⟨hle.1.trans hfit.1, hle.2.1.trans hfit.2.1, hle.2.2.trans hfit.2.2⟩

omit [CharP K 2130706433] in
theorem residual_support_of_endpoint (F : MvPolynomial (Fin 4) K)
    (f : Envelope) (hf : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hfit : Below (originalCumulativeFlag F) f.flag) : ResidualSupportData (f.paddedSupport 0) F := by
  obtain ⟨h0, h1, h2⟩ := hfit
  change (contactFlag F).all ≤ f.flag.all at h0
  change middle (contactFlag F) ≤ middle f.flag at h1
  change total (contactFlag F) ≤ total f.flag at h2
  rw [contactFlag_all] at h0
  rw [contactFlag_middle] at h1
  rw [contactFlag_total] at h2
  simp only [Envelope.flag, middle, total] at h0 h1 h2
  exact ⟨by simp only [Envelope.paddedSupport, Envelope.pad]; omega,
    by simp only [Envelope.paddedSupport, Envelope.pad]; omega,
    by simp only [Envelope.paddedSupport, Envelope.pad]; omega⟩

theorem incumbent_raw_fiber
    {x : I ↪ K} (T : TerminalData x)
    (F : RegularIndex T.primary) (f : Envelope)
    (hf : f.slope ≤ 16 ∧ f.middle ≤ 67 ∧ f.total ≤ 8870)
    (hgate : rawGatesWithCorrections TailCorrections.original (f.pad 0) = true)
    (hdata : ResidualSupportData (f.paddedSupport 0) F.1) :
    (regularFiber T.primary T.seeds T.selected F).card ≤
      rawChargeWithCorrections TailCorrections.original (f.pad 0) (originalCumulativeFlag F.1) := by
  let a := f.pad 0
  have hg := small_padded_bounds f hf 0 (by decide)
  change 3 ≤ a.slope ∧ a.slope+2 ≤ a.middle ∧ a.middle+0 ≤ a.total ∧
    a.slope ≤ 31 ∧ a.middle ≤ 142 ∧ a.total ≤ 8870 at hg
  obtain ⟨h3, hy, ht, hs, hm, hT⟩ := hg
  have hbox := T.factor_global_box F hdata
  change F.1 ∈ globalCoefficientBox K 57757821 131071 a.total a.slope at hbox
  have hsupport : ResidualSupportData (cellSupport a.total a.middle a.slope) F.1 :=
    paddedSupport_eq_cellSupport f 0 ▸ hdata
  obtain ⟨hF, _, hR⟩ := positiveRFactors_spec T.primary F.1 F.2
  let seeds := regularFiber T.primary T.seeds T.selected F
  have hsub : seeds ⊆ T.seeds := fun _ hg => (mem_regularFiber.mp hg).1
  have hn : (Finset.univ : Finset I).card = 262144 := Finset.card_univ.trans T.nodes_card
  have hraw := K6833TerminalIncumbentRaw.regular_raw_seed_card_le
    57757821 a.total a.middle a.slope (by decide +kernel) (by decide +kernel)
    hT hm hs h3 hy (by omega) F.1 hF hR hbox hsupport T.selected seeds Finset.univ x T.u₀ T.u₁
    x.injective.injOn hn
    (fun g hg => T.degree g (hsub hg)) (fun g hg => T.agreement g (hsub hg))
    (fun _ hg => (mem_regularFiber.mp hg).2.1) (fun _ hg => (mem_regularFiber.mp hg).2.2)
    (RCN243.noLargeSelectedPencil_mono T.selected T.seeds seeds 131071 81085 hsub T.pencil)
    (fun left => incumbent_raw_identity_absorbed a left h3 hy hgate)
  rw [rawChargeWithCorrections_original_eq_incumbent a _ h3 hy]
  exact hraw

theorem upperGraphAxis_eq (f : Envelope) (cfg : Fin 3 → JetProfile) :
    upperGraphAxis f cfg = graphAxis f cfg := by funext i; rfl

theorem single_flag_eq {x : I ↪ K} (T : TerminalData x) (F : RegularIndex T.primary) :
    aggregateFlag T.primary {F} = originalCumulativeFlag F.1 := by
  simp [aggregateFlag,regularProduct]

theorem individual_alternatives {x : I ↪ K} (T : TerminalData x) (F : RegularIndex T.primary)
    (f : Envelope) (ids : Profiles)
    (hmin : 1 ≤ f.slope ∧ 2 ≤ f.middle) (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hcaps : f.slope ≤ 16 ∧ f.middle ≤ 67 ∧ f.total ≤ 8870)
    (hbelow : Below (originalCumulativeFlag F.1) f.flag)
    (hg : jetGatesWithCorrections TailCorrections.original f (cellConfig ids) = true) :
    let cfg := cellConfig ids
    let bag := regularFiber T.primary T.seeds T.selected F
    let left := originalCumulativeFlag F.1
    (wt residualTotalWeights F.1 ≤ jetSourceCap cfg ∧ bag.card ≤ rawCost (clip f cfg) left) ∨
      (∃ j, bag.card * residualPriceScale ≤ helperCost f (cfg j) left) ∨
        bag.card * residualPriceScale ≤ graphCost f cfg left := by
  let cfg := cellConfig ids
  let bag := regularFiber T.primary T.seeds T.selected F
  have hsub : bag ⊆ T.seeds := fun _ hg => (mem_regularFiber.mp hg).1
  have hsing : Below (aggregateFlag T.primary {F}) f.flag := (single_flag_eq T F) ▸ hbelow
  have hcard : 181059 ≤ Fintype.card I := by rw [T.nodes_card]; decide
  have ht : f.total < 2130706433 := by omega
  obtain ⟨hirr, _, hpos⟩ := positiveRFactors_spec T.primary F.1 F.2
  have hreg : ∀ g ∈ bag, RegularSolution F.1 (T.selected g) g := fun _ hg => (mem_regularFiber.mp hg).2
  have hdeg := fun g (hg : g ∈ bag) => T.degree g (hsub hg)
  have hag := fun g (hg : g ∈ bag) => T.agreement g (hsub hg)
  have hpencil := RCN243.noLargeSelectedPencil_mono T.selected T.seeds bag 131071 81085 hsub T.pencil
  rcases route_regular_factor T.primary {F} f ids hshape hsing T.nodes_card.le x T.u₀ T.u₁ F
    (Finset.mem_singleton_self _) with ⟨hsmall, hdata⟩ | ⟨hlarge, hdata, ⟨j,Q,hQ⟩ | sources⟩
  · left
    have hlt : jetSourceCap cfg < f.total := by
      have h := hg
      simp only [jetGatesWithCorrections, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.2
    exact ⟨hsmall, incumbent_raw_fiber T F (clip f cfg) ⟨hcaps.1,hcaps.2.1,hlt.le.trans hcaps.2.2⟩
      (rawGates_of_jetGates_small _ _ _ hg) hdata⟩
  · exact Or.inr (Or.inl ⟨j,individual_profile_helper_count f cfg j hmin hshape ht hg F.1 Q hirr hpos
      hbelow x T.u₀ T.u₁ T.nodes_card.le hcard hQ T.selected bag hdeg hreg hag hpencil⟩)
  · right; right
    have ⟨_,_,_,hpR,hpY,hpT⟩ := small_padded_bounds f hcaps 2 le_rfl
    have h := individual_retained_profile_seed_card_mul_le f ids hmin hshape ht hg 57757821
      (by decide) (by decide) hpT hpY hpR F.1 hirr hpos hbelow (T.factor_global_box F hdata)
      hdata hlarge x T.u₀ T.u₁ T.nodes_card sources T.selected bag hdeg hreg hag hpencil
    change bag.card * terminalScale ≤ graphCost f cfg (originalCumulativeFlag F.1)
    rw [graphCost,upperGraphAxis_eq]
    rw [jetLeadingNumerator_eq_list] at h
    exact h

end
end ProximityPrize.SubmissionLower.K6833Residual
