import ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual
import ProximityPrize.SubmissionLower.Koala6831MovingShortStages
import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentLedger
import ProximityPrize.SubmissionLower.Koala6831ResidualCoverage
import ProximityPrize.SubmissionLower.Koala6831ResidualFactorRouting
import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentPrices
import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentRaw
import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentHelpers
import ProximityPrize.SubmissionLower.Koala6831ResidualIncumbentRetainedGraph

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkShortCount

open scoped Classical BigOperators
open RCN095 RCN130 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open LocatorHybridCells
open LocatorPhase6800Oracle (sumFlag_all sumFlag_middle sumFlag_total)
open LocatorFactorAggregate LocatorBatchProductRoute
open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkRetention (retainedSeedBudget)
open Koala6831Moving Koala6831MovingAdaptive Koala6831MovingPaid Koala6831MovingShortRetained
open Koala6831MovingSources (Stage)
open Koala6831MovingStages (adaptiveGate)
open Koala6831Residual

noncomputable section

variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

private theorem flag_below_endpoint (f : FlagDegree) (e : Envelope)
    (hs : e.slope = f.all) (hy : e.middle = middle f) (ht : total f ≤ e.total) :
    Below f e.flag := by
  simp only [Below, Envelope.flag, total, middle] at *
  omega

omit [CharP K 2130706433] in

theorem reachedTerminal_count
    {x : I ↪ K} {original : Finset K} {R : Ready x original} (T : ReachedTerminal R)
    (hterminal : ∀ cell ∈ terminalCells, cell.envelope.slope ≤ cell.envelope.middle →
      cell.envelope.middle ≤ cell.envelope.total →
      Below (aggregateFlag T.primary T.route.residue) cell.envelope.flag →
      T.route.seeds.card ≤ incumbentCellPrice cell) :
    original.card ≤ retainedSeedBudget := by
  by_cases hempty : T.route.residue = ∅
  · have hzero : T.route.seeds.card = 0 := by
      simp [PaidRoute.seeds, hempty]
    have h := T.paid
    rw [hzero, zero_add] at h
    have hb : 31621569077767686 ≤ retainedSeedBudget := by decide +kernel
    omega
  let f := aggregateFlag T.primary T.route.residue
  have hf : 0 < f.all := aggregateFlag_pos T.primary (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hcaps : f.all ≤ 30 ∧ middle f ≤ 138 ∧ total f ≤ 15351 := by
    simpa only [Below, postRoomCap, middle, total, Nat.reduceAdd] using T.route.below_room
  obtain ⟨h₁, h₂, h₃⟩ := T.route.stopped.resolve_left hempty
  obtain ⟨cell, hc, hs, hy, ht⟩ := exists_terminalCell_of_failed_gates f hf
    hcaps.1 hcaps.2.1 hcaps.2.2 h₁ h₂ h₃
  have hshape : cell.envelope.slope ≤ cell.envelope.middle ∧
      cell.envelope.middle ≤ cell.envelope.total := by
    rw [hs, hy]
    unfold middle total at *
    omega
  have hcount := hterminal cell hc hshape.1 hshape.2 (flag_below_endpoint f cell.envelope hs hy ht)
  have hpaid := T.paid_with_certificate_credit cell.envelope hs hy
  have hp : 31621569077767686 ≤ paid := by decide +kernel
  have htotal := incumbentCellTotal_le_of_mem hc
  unfold incumbentCellTotal at htotal
  have hretained := incumbentCeiling_with_retained_fees
  omega

theorem shortSeparatedRetainedCount_of_terminal
    (x : I ↪ K) (σ : K ≃+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpower : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144)
    (hterminal : ∀ {original : Finset K} {R : Ready x original} (T : ReachedTerminal R),
      ∀ cell ∈ terminalCells, cell.envelope.slope ≤ cell.envelope.middle →
        cell.envelope.middle ≤ cell.envelope.total →
        Below (aggregateFlag T.primary T.route.residue) cell.envelope.flag →
        T.route.seeds.card ≤ incumbentCellPrice cell) :
    Koala6831BenchmarkResidual.ShortSeparatedRetainedCount x σ.toRingHom := by
  intro received retained selected q hret hdelta hnormal
  obtain ⟨R, ⟨T⟩⟩ := reaches_terminal_checked x σ hfixed hpower hcard
    received retained selected q hret _ hdelta hnormal
  exact reachedTerminal_count T (hterminal T)

private theorem small_padded_bounds (f : Envelope)
    (hf : f.slope ≤ 15 ∧ f.middle ≤ 63 ∧ f.total ≤ 6473)
    (k : ℕ) (hk : k ≤ 2) :
    let a := f.pad k
    3 ≤ a.slope ∧ a.slope+2 ≤ a.middle ∧ a.middle+k ≤ a.total ∧
      a.slope ≤ 31 ∧ a.middle ≤ 142 ∧ a.total ≤ 7501 := by
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
private theorem factor_below_endpoint
    (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (f : Envelope) (hfit : Below (aggregateFlag H remaining) f.flag)
    (F : RegularIndex H) (hF : F ∈ remaining) :
    Below (originalCumulativeFlag F.1) f.flag := by
  have hdiv : F.1 ∣ regularProduct H remaining :=
    ⟨regularCofactor H remaining F, (regularFactor_mul_cofactor H remaining F hF).symm⟩
  have hle := contactFlag_below_of_dvd (regularProduct_ne_zero H remaining) hdiv
  exact ⟨hle.1.trans hfit.1, hle.2.1.trans hfit.2.1, hle.2.2.trans hfit.2.2⟩

omit [CharP K 2130706433] in
private theorem residual_support_of_endpoint (F : MvPolynomial (Fin 4) K)
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

private theorem incumbent_raw_fiber
    {x : I ↪ K} {original : Finset K} {R : Ready x original} (T : ReachedTerminal R)
    (F : RegularIndex T.primary) (f : Envelope)
    (hf : f.slope ≤ 15 ∧ f.middle ≤ 63 ∧ f.total ≤ 6473)
    (hgate : rawGatesWithCorrections TailCorrections.original (f.pad 0) = true)
    (hdata : ResidualSupportData (f.paddedSupport 0) F.1) :
    (regularFiber T.primary T.regular R.selected F).card ≤
      rawChargeWithCorrections TailCorrections.original (f.pad 0) (originalCumulativeFlag F.1) := by
  let a := f.pad 0
  have hg := small_padded_bounds f hf 0 (by decide)
  change 3 ≤ a.slope ∧ a.slope+2 ≤ a.middle ∧ a.middle+0 ≤ a.total ∧
    a.slope ≤ 31 ∧ a.middle ≤ 142 ∧ a.total ≤ 7501 at hg
  obtain ⟨h3, hy, ht, hs, hm, hT⟩ := hg
  have hbox := T.factor_global_box F hdata
  change F.1 ∈ globalCoefficientBox K Stage.primary.cutoff 131071 a.total a.slope at hbox
  have hsupport : ResidualSupportData (cellSupport a.total a.middle a.slope) F.1 :=
    paddedSupport_eq_cellSupport f 0 ▸ hdata
  obtain ⟨hF, _, hR⟩ := positiveRFactors_spec T.primary F.1 F.2
  let seeds := regularFiber T.primary T.regular R.selected F
  have hsub : seeds ⊆ R.seeds := fun _ hg => T.regular_subset (mem_regularFiber.mp hg).1
  have hn : (Finset.univ : Finset I).card = 262144 := Finset.card_univ.trans R.nodes_card
  have hraw := Koala6831ResidualIncumbentRaw.regular_raw_seed_card_le
    Stage.primary.cutoff a.total a.middle a.slope (by decide +kernel) (by decide +kernel)
    hT hm hs h3 hy (by omega) F.1 hF hR hbox hsupport R.selected seeds Finset.univ x R.u₀ R.u₁
    x.injective.injOn hn
    (fun g hg => R.degree g (hsub hg)) (fun g hg => R.agreement g (hsub hg))
    (fun _ hg => (mem_regularFiber.mp hg).2.1) (fun _ hg => (mem_regularFiber.mp hg).2.2)
    (RCN243.noLargeSelectedPencil_mono R.selected R.seeds seeds 131071 81060 hsub R.pencil)
    (fun left => incumbent_raw_identity_absorbed a left h3 hy hgate)
  rw [rawChargeWithCorrections_original_eq_incumbent a _ h3 hy]
  exact hraw

private theorem incumbent_raw_residue
    {x : I ↪ K} {original : Finset K} {R : Ready x original} (T : ReachedTerminal R)
    (f : Envelope) (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hfit : Below (aggregateFlag T.primary T.route.residue) f.flag)
    (hcaps : f.slope ≤ 15 ∧ f.middle ≤ 63 ∧ f.total ≤ 6473)
    (hgate : rawGatesWithCorrections TailCorrections.original (f.pad 0) = true) :
    T.route.seeds.card ≤ rawChargeWithCorrections TailCorrections.original (f.pad 0) f.flag := by
  let active := T.route.residue
  let fiber := regularFiber T.primary T.regular R.selected
  let support := f.pad 0
  let price := rawChargeWithCorrections TailCorrections.original support
  let agg := aggregateFlag T.primary active
  have hcounts (F : RegularIndex T.primary) (hF : F ∈ active) :
      (fiber F).card ≤ price (originalCumulativeFlag F.1) :=
    incumbent_raw_fiber T F f hcaps hgate
      (residual_support_of_endpoint F.1 f hshape (factor_below_endpoint _ _ f hfit F hF))
  have hsummixed (b c : FlagDegree) :
      (∑ F ∈ active, flagMixed (originalCumulativeFlag F.1) b c) = flagMixed agg b c := by
    change _ = flagMixed (contactFlag (regularProduct T.primary active)) b c
    rw [contactFlag_regularProduct]
    simp only [mixed_expansion, sumFlag_all, sumFlag_middle, sumFlag_total,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hsum : (∑ F ∈ active, price (originalCumulativeFlag F.1)) = price agg := by
    unfold price rawChargeWithCorrections
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsummixed, hsummixed]
  have hmono : price agg ≤ price f.flag :=
    Nat.add_le_add (mixed_mono_first hfit _ _)
      (Nat.mul_le_mul_left _ (mixed_mono_first hfit _ _))
  calc
    _ ≤ ∑ F ∈ active, (fiber F).card := Finset.card_biUnion_le
    _ ≤ ∑ F ∈ active, price (originalCumulativeFlag F.1) := Finset.sum_le_sum hcounts
    _ = price agg := hsum
    _ ≤ _ := hmono

private theorem incumbent_cell_count_of_graph
    {x : I ↪ K} {original : Finset K} {R : Ready x original} (T : ReachedTerminal R)
    (cell : Cell) (hc : cell ∈ terminalCells)
    (hshape : cell.envelope.slope ≤ cell.envelope.middle ∧ cell.envelope.middle ≤ cell.envelope.total)
    (hfit : Below (aggregateFlag T.primary T.route.residue) cell.envelope.flag)
    (hgraph : ∀ ids, incumbentProfileIds cell = some ids →
      ∀ F ∈ T.route.residue, jetSourceCap (cellConfig ids) < wt residualTotalWeights F.1 →
        ResidualSupportData (cell.envelope.paddedSupport 2) F.1 →
        RetainedProfileSources ids F.1 x R.u₀ R.u₁ →
        (regularFiber T.primary T.regular R.selected F).card * terminalScale ≤
          jetFlagCharge TailCorrections.original cell.envelope (cellConfig ids)
            (originalCumulativeFlag F.1)) :
    T.route.seeds.card ≤ incumbentCellPrice cell := by
  have hcaps := terminalCell_caps_of_mem hc
  cases hids : incumbentProfileIds cell with
  | none =>
    simp only [incumbentCellPrice, hids]
    exact incumbent_raw_residue T cell.envelope hshape hfit hcaps (incumbentRawGate_of_mem hc hids)
  | some ids =>
    simp only [incumbentCellPrice, hids]
    let f := cell.envelope
    let cfg := cellConfig ids
    let fiber := regularFiber T.primary T.regular R.selected
    have hj := incumbentJetGates_of_mem hc hids
    have hn := incumbent_jet_endpoint_size hc hids
    have hN : Fintype.card I ≤ 262144 := R.nodes_card.le
    have hA : 181084 ≤ Fintype.card I := by rw [R.nodes_card]; decide
    have hsub (F : RegularIndex T.primary) : fiber F ⊆ R.seeds :=
      fun _ hg => T.regular_subset (mem_regularFiber.mp hg).1
    refine routed_jet_residue_card_le T.primary T.route.residue f ids TailCorrections.original
      hshape hfit hj.2 hN x R.u₀ R.u₁ T.route.seeds fiber (by rfl) ?_ ?_ (hgraph ids hids)
    · intro F _ _ hdata
      let small : Envelope := ⟨f.slope, f.middle, jetSourceCap cfg⟩
      have hgate := rawGates_of_jetGates_small TailCorrections.original f cfg hj.1
      have hlt : jetSourceCap cfg < f.total := by
        have h := hj.1
        simp only [jetGatesWithCorrections, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1.2
      have hs : small.slope ≤ 15 ∧ small.middle ≤ 63 ∧ small.total ≤ 6473 :=
        ⟨hcaps.1, hcaps.2.1, hlt.le.trans hcaps.2.2⟩
      exact incumbent_raw_fiber T F small hs hgate hdata
    · intro F hF _ _ j Q hQ
      obtain ⟨hirr, _, hpos⟩ := positiveRFactors_spec T.primary F.1 F.2
      exact incumbent_profile_helper_count f cfg j ⟨hn.1,hn.2.1⟩ hshape hn.2.2 hj.1 F.1 Q
        hirr hpos (factor_below_endpoint T.primary T.route.residue f hfit F hF)
        x R.u₀ R.u₁ hN hA hQ R.selected (fiber F)
        (fun g hg => R.degree g (hsub F hg))
        (fun _ hg => (mem_regularFiber.mp hg).2)
        (fun g hg => R.agreement g (hsub F hg))
        (RCN243.noLargeSelectedPencil_mono R.selected R.seeds _ 131071 81060 (hsub F) R.pencil)

private theorem incumbent_cell_count
    {x : I ↪ K} {original : Finset K} {R : Ready x original} (T : ReachedTerminal R)
    (cell : Cell) (hc : cell ∈ terminalCells)
    (hs : cell.envelope.slope ≤ cell.envelope.middle)
    (ht : cell.envelope.middle ≤ cell.envelope.total)
    (hfit : Below (aggregateFlag T.primary T.route.residue) cell.envelope.flag) :
    T.route.seeds.card ≤ incumbentCellPrice cell := by
  refine incumbent_cell_count_of_graph T cell hc ⟨hs,ht⟩ hfit ?_
  intro ids hids F hF hlarge hdata hsources
  let f := cell.envelope
  have hcaps := terminalCell_caps_of_mem hc
  have hpad := small_padded_bounds f hcaps 2 le_rfl
  change 3 ≤ (f.pad 2).slope ∧ (f.pad 2).slope+2 ≤ (f.pad 2).middle ∧
    (f.pad 2).middle+2 ≤ (f.pad 2).total ∧ (f.pad 2).slope ≤ 31 ∧
    (f.pad 2).middle ≤ 142 ∧ (f.pad 2).total ≤ 7501 at hpad
  obtain ⟨_, _, _, hpR, hpY, hpT⟩ := hpad
  have hsize := incumbent_jet_endpoint_size hc hids
  have hgate := (incumbentJetGates_of_mem hc hids).1
  have hbox := T.factor_global_box F hdata
  obtain ⟨hirr, _, hpos⟩ := positiveRFactors_spec T.primary F.1 F.2
  let seeds := regularFiber T.primary T.regular R.selected F
  have hsub : seeds ⊆ R.seeds := fun _ hg => T.regular_subset (mem_regularFiber.mp hg).1
  exact incumbent_retained_profile_seed_card_mul_le f ids ⟨hsize.1,hsize.2.1⟩ ⟨hs,ht⟩
    hsize.2.2 hgate Stage.primary.cutoff (by decide +kernel) (by decide +kernel)
    hpT hpY hpR F.1 hirr hpos (factor_below_endpoint T.primary T.route.residue f hfit F hF)
    hbox hdata hlarge x R.u₀ R.u₁ R.nodes_card hsources R.selected seeds
    (fun g hg => R.degree g (hsub hg)) (fun _ hg => (mem_regularFiber.mp hg).2)
    (fun g hg => R.agreement g (hsub hg))
    (RCN243.noLargeSelectedPencil_mono R.selected R.seeds _ 131071 81060 hsub R.pencil)

theorem shortSeparatedRetainedCount
    (x : I ↪ K) (σ : K ≃+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpower : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144) :
    Koala6831BenchmarkResidual.ShortSeparatedRetainedCount x σ.toRingHom :=
  shortSeparatedRetainedCount_of_terminal x σ hfixed hpower hcard
    (fun T => incumbent_cell_count T)

open ProximityPrize.Benchmark

theorem benchmark_short_separated_count :
    Koala6831BenchmarkResidual.ShortSeparatedRetainedCount IRSProfile.domain
      Koala6831BenchmarkField.frobenius.toRingHom := by
  let _ : CharP IRSProfile.Field 2130706433 := Koala6831BenchmarkField.characteristic
  exact shortSeparatedRetainedCount IRSProfile.domain Koala6831BenchmarkField.frobenius
    Koala6831BenchmarkField.domain_fixed Koala6831BenchmarkField.frobenius_apply
    (by norm_num [IRSProfile.Index])

end

end ProximityPrize.SubmissionLower.Koala6831BenchmarkShortCount
