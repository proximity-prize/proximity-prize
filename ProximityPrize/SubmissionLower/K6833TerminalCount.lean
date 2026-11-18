/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Count each irreducible by its actual branch and subtract a positive
slope from individual supports in the case of at least two residual factors. -/
import ProximityPrize.SubmissionLower.K6833TerminalData

namespace ProximityPrize.SubmissionLower.K6833Residual
open scoped Classical BigOperators
open RCN095 RCN130 RCN156 RCN167 RCN234 RCN266 RCN275 RCN313
open LocatorFactorAggregate LocatorBatchProductRoute
open LocatorPhase6800Oracle (sumFlag_all sumFlag_middle sumFlag_total)
open Koala6831Moving Koala6831MovingAdaptive Koala6831MovingPaid
open K6833TerminalIncumbentGraph (axisPrice)
noncomputable section
set_option maxHeartbeats 5500000
set_option maxRecDepth 8000
variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

private theorem raw_mono (f : Envelope) {p q : FlagDegree} (h : Below p q) :
    rawCost f p ≤ rawCost f q :=
  Nat.add_le_add (mixed_mono_first h _ _) (Nat.mul_le_mul_left _ (mixed_mono_first h _ _))

private theorem graph_mono_left (f : Envelope) (cfg : Fin 3 → JetProfile)
    {p q : FlagDegree} (h : Below p q) : graphCost f cfg p ≤ graphCost f cfg q := by
  have hd (l : FlagDegree) : leadCost f cfg l = jetLeadingNumerator f cfg l :=
    (jetLeadingNumerator_eq_list f cfg l).symm
  have ha : leadCost f cfg p ≤ leadCost f cfg q := by
    rw [hd,hd]
    exact Finset.sum_le_sum fun j _ => mixed_mono_first h _ _
  let a := graphAxis f cfg
  have ham := graphAxis_mono f cfg
  have hb : axisPrice a p ≤ axisPrice a q := by
    rw [axisPrice,axisPrice,RCN131.linear_cost_cumulative _ _ _ _ ham.1 ham.2,
      RCN131.linear_cost_cumulative _ _ _ _ ham.1 ham.2]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2)
      (Nat.mul_le_mul_left _ h.2.1)) (Nat.mul_le_mul_left _ h.1)
  exact Nat.add_le_add ha hb

private theorem flag_below_clip (f : Envelope) (cfg : Fin 3 → JetProfile) {p : FlagDegree}
    (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total) (hs : f.middle ≤ jetSourceCap cfg)
    (hfit : Below p f.flag) (ht : total p ≤ jetSourceCap cfg) : Below p (clip f cfg).flag := by
  simp only [Below,Envelope.flag,total,middle,clip] at hfit ht ⊢
  omega

private theorem helper_absorbed (f : Envelope) (cfg : Fin 3 → JetProfile) (j : Fin 3) (p : FlagDegree) :
    helperCost f (cfg j) p ≤ jetFlagCharge TailCorrections.original f cfg p := by
  unfold helperCost sharpDirection
  rw [flagMixed_left_increments, jetFlagCharge_eq]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (helper_axis_le _ f cfg j 0))
    (Nat.mul_le_mul_left _ (helper_axis_le _ f cfg j 1)))
    (Nat.mul_le_mul_left _ (helper_axis_le _ f cfg j 2))

private theorem graph_absorbed (f : Envelope) (cfg : Fin 3 → JetProfile) (p : FlagDegree) :
    graphCost f cfg p ≤ jetFlagCharge TailCorrections.original f cfg p := by
  have h := leading_add_axis_le f cfg p
  rw [jetLeadingNumerator_eq_list] at h
  exact h

private theorem single_count {x : I ↪ K} (T : TerminalData x) (F : RegularIndex T.primary)
    (f : Envelope) (limit : ℕ) (choice : Option Profiles)
    (shape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (caps : f.slope ≤ 16 ∧ f.middle ≤ 66 ∧ f.total ≤ 8870)
    (below : Below (originalCumulativeFlag F.1) f.flag) (ok : simpleMode f limit choice = true) :
    (regularFiber T.primary T.seeds T.selected F).card ≤ limit := by
  cases choice with
  | none =>
    simp only [simpleMode,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact (incumbent_raw_fiber T F f caps ok.1 (residual_support_of_endpoint F.1 f shape below)).trans
      ((raw_mono f below).trans ok.2)
  | some ids =>
    simp only [simpleMode,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
    obtain ⟨⟨gate,hr,hy,hclip,hraw,hgraph⟩,hh⟩ := ok
    rcases individual_alternatives T F f ids ⟨hr,hy⟩ shape caps below gate with
      ⟨ht,ct⟩ | ⟨j,hj⟩ | hg
    · exact ct.trans ((raw_mono _ (flag_below_clip f _ shape hclip below (by rwa [contactFlag_total]))).trans hraw)
    · have hj' := hj.trans (mixed_mono_first below _ _)
      exact ((Nat.le_div_iff_mul_le (show 0 < residualPriceScale by decide)).2 hj').trans (hh j (by simp))
    · exact ((Nat.le_div_iff_mul_le (show 0 < residualPriceScale by decide)).2
        (hg.trans (graph_mono_left _ _ below))).trans hgraph

private theorem positive_split {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (F : RegularIndex T.primary) (hF : F ∈ A) (hcard : 1 < A.card) :
    let p := originalCumulativeFlag F.1
    let agg := aggregateFlag T.primary A
    p.all < agg.all ∧ middle p < middle agg ∧ total p < total agg := by
  let deg (F : RegularIndex T.primary) := originalCumulativeFlag F.1
  have ne : (A.erase F).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hF]; omega)
  have hpos := aggregateFlag_pos T.primary ne
  have split (g : RegularIndex T.primary → ℕ) :
      g F + ∑ i ∈ A.erase F, g i = ∑ i ∈ A, g i := Finset.add_sum_erase A g hF
  have whole := contactFlag_regularProduct T.primary A
  have rest := contactFlag_regularProduct T.primary (A.erase F)
  change 0 < (contactFlag (regularProduct T.primary (A.erase F))).all at hpos
  rw [rest, sumFlag_all] at hpos
  have hypos : 0 < ∑ i ∈ A.erase F, middle (deg i) :=
    hpos.trans_le (Finset.sum_le_sum fun i _ => show (deg i).all ≤ middle (deg i) by unfold middle; omega)
  have htpos : 0 < ∑ i ∈ A.erase F, total (deg i) :=
    hypos.trans_le (Finset.sum_le_sum fun i _ => show middle (deg i) ≤ total (deg i) by unfold middle total; omega)
  change (deg F).all < (contactFlag (regularProduct T.primary A)).all ∧
    middle (deg F) < middle (contactFlag (regularProduct T.primary A)) ∧
    total (deg F) < total (contactFlag (regularProduct T.primary A))
  rw [whole,sumFlag_all,sumFlag_middle,sumFlag_total]
  change 0 < ∑ i ∈ A.erase F, (deg i).all at hpos
  have a := split (fun i => (deg i).all)
  have b := split (fun i => middle (deg i))
  have c := split (fun i => total (deg i))
  change (deg F).all < ∑ i ∈ A, (deg i).all ∧ middle (deg F) < ∑ i ∈ A, middle (deg i) ∧
    total (deg F) < ∑ i ∈ A, total (deg i)
  omega

private theorem below_pred {p agg : FlagDegree} (f : Envelope)
    (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (ha : p.all < agg.all ∧ middle p < middle agg ∧ total p < total agg)
    (hb : Below agg f.flag) : Below p (predEnvelope f).flag := by
  simp only [Below, Envelope.flag, predEnvelope,middle,total] at *
  omega

private theorem multiple_count {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (f : Envelope) (limit : ℕ) (choice : Option Profiles)
    (hcard : 1 < A.card) (shape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (caps : f.slope ≤ 16 ∧ f.middle ≤ 66 ∧ f.total ≤ 8870)
    (overall : Below (aggregateFlag T.primary A) f.flag)
    (ok : multipleMode f (predEnvelope f) limit choice = true) :
    (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ limit := by
  let sm := predEnvelope f
  let deg (F : RegularIndex T.primary) := originalCumulativeFlag F.1
  let bag := regularFiber T.primary T.seeds T.selected
  have localBelow (F) (hF : F ∈ A) : Below (deg F) sm.flag := below_pred f shape
    (positive_split T A F hF hcard) overall
  have sh : sm.slope ≤ sm.middle ∧ sm.middle ≤ sm.total := by simp only [sm,predEnvelope]; omega
  have cp : sm.slope ≤ 16 ∧ sm.middle ≤ 66 ∧ sm.total ≤ 8870 := by simp only [sm,predEnvelope]; omega
  have agg : originalCumulativeFlag (regularProduct T.primary A) = LocatorPhase6800Oracle.sumFlag A deg :=
    contactFlag_regularProduct T.primary A
  cases choice with
  | none =>
    simp only [multipleMode, Bool.and_eq_true, decide_eq_true_eq] at ok
    have hcount (F) (hF : F ∈ A) : (bag F).card ≤ rawCost sm (deg F) :=
      incumbent_raw_fiber T F sm cp ok.1 (residual_support_of_endpoint F.1 sm sh (localBelow F hF))
    have hsum (a b : FlagDegree) : (∑ F ∈ A, flagMixed (deg F) a b) =
        flagMixed (aggregateFlag T.primary A) a b := by
      change _ = flagMixed (originalCumulativeFlag (regularProduct T.primary A)) a b
      rw [agg]
      simp only [mixed_expansion,sumFlag_all,sumFlag_middle,sumFlag_total,Finset.sum_add_distrib,Finset.mul_sum]
    have hraw : (∑ F ∈ A, rawCost sm (deg F)) = rawCost sm (aggregateFlag T.primary A) := by
      unfold rawCost rawChargeWithCorrections
      rw [Finset.sum_add_distrib,← Finset.mul_sum,hsum,hsum]
    exact Finset.card_biUnion_le.trans ((Finset.sum_le_sum hcount).trans
      (hraw.le.trans ((raw_mono _ overall).trans ok.2)))
  | some ids =>
    simp only [multipleMode,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨⟨gate,mono⟩,hr,hy,hlim⟩ := ok
    let cfg := cellConfig ids
    have hcount (F) (hF : F ∈ A) : (bag F).card * terminalScale ≤
        jetFlagCharge TailCorrections.original sm cfg (deg F) := by
      rcases individual_alternatives T F sm ids ⟨hr,hy⟩ sh cp (localBelow F hF) gate with
        ⟨_,hc⟩ | ⟨j,hj⟩ | hg
      · exact (Nat.mul_le_mul_right _ hc).trans (rawCharge_mul_le_jetFlagCharge _ _ _ _)
      · exact hj.trans (helper_absorbed _ _ _ _)
      · exact hg.trans (graph_absorbed _ _ _)
    apply Nat.le_trans _ hlim
    apply (Nat.le_div_iff_mul_le (show 0 < residualPriceScale by decide)).2
    calc
      _ ≤ (∑ F ∈ A, (bag F).card)*terminalScale := Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ F ∈ A, (bag F).card*terminalScale := Finset.sum_mul _ _ _
      _ ≤ ∑ F ∈ A, jetFlagCharge TailCorrections.original sm cfg (deg F) := Finset.sum_le_sum hcount
      _ = jetFlagCharge TailCorrections.original sm cfg (originalCumulativeFlag (regularProduct T.primary A)) := by
        rw [agg,sum_jetFlagCharge]
      _ ≤ jetFlagCharge TailCorrections.original sm cfg f.flag := jetFlagCharge_mono _ sm cfg mono overall
      _ = _ := jetFlagCharge_eq _ _ _ _

theorem terminal_count {x : I ↪ K} (T : TerminalData x) (A : Finset (RegularIndex T.primary))
    (row : TerminalRow) (valid : validRow row = true)
    (hs : row.envelope.slope = (aggregateFlag T.primary A).all)
    (hy : row.envelope.middle = middle (aggregateFlag T.primary A))
    (ht : total (aggregateFlag T.primary A) ≤ row.envelope.total) :
    (A.biUnion (regularFiber T.primary T.seeds T.selected)).card ≤ row.terminalLimit := by
  simp only [validRow,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true] at valid
  obtain ⟨⟨⟨hr,hy0,ht0,cp⟩,sok⟩,mok⟩ := valid
  have below : Below (aggregateFlag T.primary A) row.envelope.flag := by
    simp only [Below,Envelope.flag,total,middle] at hs hy ht ⊢
    omega
  rcases A.eq_empty_or_nonempty with he|hne
  · simp [he]
  by_cases one : A.card = 1
  · obtain ⟨F,hF⟩ := Finset.card_eq_one.mp one
    subst A
    simpa using single_count T F row.envelope row.terminalLimit row.single ⟨hy0,ht0⟩ cp
      ((single_flag_eq T F) ▸ below) sok
  have many : 1 < A.card := by have hp := Finset.card_pos.mpr hne; omega
  have rgt : 1 < row.envelope.slope := by
    obtain ⟨F,hF⟩ := hne
    have hp : 0 < (originalCumulativeFlag F.1).all := regularCumulativeFlag_positive T.primary F
    have ha := (positive_split T A F hF many).1
    omega
  have mok' := mok.resolve_left (show row.envelope.slope ≠ 1 by omega)
  exact multiple_count T A row.envelope row.terminalLimit row.multiple many ⟨hy0,ht0⟩ cp below mok'

#print axioms terminal_count
end
end ProximityPrize.SubmissionLower.K6833Residual
