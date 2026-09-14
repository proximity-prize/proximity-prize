import ProximityPrize.SubmissionLower.HigherAffineSingleData6810
import ProximityPrize.SubmissionLower.HigherPhaseSemantics6810

namespace ProximityPrize.SubmissionLower.HigherAffineRateBridge6810
open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open HigherAffineSingleton6810 Lower80850.PhaseRows Lower80850.PhaseData
open Lower80850.PhaseSemantics Lower80850.PhaseChecks Lower80850.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def RateAt (r v : ℕ) : Prop :=
  (r+1≤34 → r+1+v≤156 → HigherAffineRateData6810.rate r v ≤ HigherAffineRateData6810.rate (r+1) v) ∧
  (r+(v+1)≤156 → HigherAffineRateData6810.rate r v ≤ HigherAffineRateData6810.rate r (v+1))
instance (r v : ℕ) : Decidable (RateAt r v) := by unfold RateAt; infer_instance

def RateReceipt : Prop := ∀ r v, 1≤r → r≤34 → r+v≤156 → RateAt r v

theorem rate_zero (v : ℕ) : HigherAffineRateData6810.rate 0 v = 0 := by
  simp [HigherAffineRateData6810.rate]

theorem rate_r_mono (hc : RateReceipt) (r R v : ℕ)
    (hr : r≤R) (hR : R≤34) (hY : R+v≤156) :
    HigherAffineRateData6810.rate r v ≤ HigherAffineRateData6810.rate R v := by
  by_cases h0 : r=0
  · subst r; rw [rate_zero]; exact Nat.zero_le _
  induction R,hr using Nat.le_induction with
  | base => exact le_rfl
  | succ R hr ih =>
    exact (ih (by omega) (by omega)).trans ((hc R v (by omega) (by omega) (by omega)).1 (by omega) (by omega))

theorem rate_v_mono (hc : RateReceipt) (r v V : ℕ)
    (hv : v≤V) (hR : r≤34) (hY : r+V≤156) :
    HigherAffineRateData6810.rate r v ≤ HigherAffineRateData6810.rate r V := by
  by_cases h0 : r=0
  · subst r; simp [rate_zero]
  induction V,hv using Nat.le_induction with
  | base => exact le_rfl
  | succ V hv ih =>
    exact (ih (by omega)).trans ((hc r V (by omega) hR (by omega)).2 (by omega))

theorem rate_mono (hc : RateReceipt) (r v R V : ℕ)
    (hr : r≤R) (hv : v≤V) (hR : R≤34) (hY : R+V≤156) :
    HigherAffineRateData6810.rate r v ≤ HigherAffineRateData6810.rate R V :=
  (rate_r_mono hc r R v hr hR (by omega)).trans (rate_v_mono hc R v V hv hR hY)

theorem count_le_affine
    (r v z count : ℕ) (hr : 1≤r) (hR : r≤34) (hY : r+v≤156) (hT : r+v+z≤8865)
    (hvalid : HigherAffineSingleData6810.Valid r v)
    (hthreshold : ThresholdAt r v)
    (hraw : HigherAffineSingleton6810.Active (lookup r v).threshold 0 r v z z →
      count ≤ HigherShape6810.cost r v z)
    (hroot : ∀ w, 1≤w → w≤4 → HigherAffineSingleton6810.Active (lookup r v).threshold w r v z z →
      count ≤ HigherAffineSingleton6810.rootUpper w r v z)
    (hsource : ∀ j, j<10 → (phaseSource j).Routeable (rawFlag r v z) →
      count ≤ (phasePotential j).eval (rawFlag r v z)) :
    count ≤ HigherAffineSingleton6810.cap (HigherAffineRateData6810.rate r v) r z := by
  rcases hvalid with ⟨hc,hcover⟩
  obtain ⟨w,hw,hbound⟩ := cover_sound (HigherAffineSingleData6810.carrier r v)
    (HigherAffineRateData6810.rate r v) r v (lookup r v).threshold
    (8866-r-v) 0 (HigherAffineSingleData6810.cover r v) hcover z (Nat.zero_le _) (by omega)
  apply le_trans (b := choice (HigherAffineSingleData6810.carrier r v) w r v z) ?_ hbound
  by_cases h0 : w=0
  · subst w
    simp only [choice,if_pos,HigherAffineSingleton6810.Active] at hw ⊢
    rw [Carrier.eval_correct _ r v z hr hc]
    exact hraw hw
  by_cases h1 : w≤4
  · simpa only [choice,if_neg h0,if_pos h1] using hroot w (by omega) h1 hw
  · have hw' : w-5<10 ∧ thresholdAt (lookup r v).threshold (w-5) ≤ z := by
      simpa only [HigherAffineSingleton6810.Active,if_neg h0,if_neg h1] using hw
    have ht := hthreshold (w-5) (List.mem_range.mpr hw'.1)
    have route := sufficient_route (phaseSource (w-5)) r v
      (thresholdAt (rowContext r v).threshold (w-5)) z
      (source_total (w-5) hw'.1) hT hw'.2 ht
    simpa only [choice,if_neg h0,if_neg h1] using hsource (w-5) hw'.1 route


theorem base_value (r v z : ℕ) (hr : 1≤r) (hR : r≤34) (hY : r+v≤156) :
    (HigherBaseData6810.lookup r v).evalAt z =
      HigherAffineSingleton6810.cap (HigherAffineRateData6810.rate r v) r z := by
  have hbox : 1≤r ∧ r≤34 ∧ r+v≤156 := ⟨hr,hR,hY⟩
  rw [HigherBaseData6810.lookup,if_pos hbox]
  dsimp [BaseRow.evalAt,evalBaseSegments,BaseSegment.evalAt,HigherAffineSingleton6810.cap,HigherAffineSingleton6810.slope]
  split_ifs <;> omega


structure Receipt : Prop where
  single : ∀ r v, 1≤r → r≤34 → r+v≤156 → HigherAffineSingleData6810.Valid r v
  rate : RateReceipt

theorem sum_count_le_base {ι : Type} [DecidableEq ι]
    (hRate : RateReceipt) (s : Finset ι) (p : ι → FlagDegree) (count : ι → ℕ)
    (hr : ∀ i ∈ s, 1≤(p i).all)
    (hR : (∑ i ∈ s, (p i).all)≤34)
    (hY : (∑ i ∈ s, (p i).all)+(∑ i ∈ s, (p i).yz)≤156)
    (hcount : ∀ i ∈ s, count i ≤ HigherAffineSingleton6810.cap
      (HigherAffineRateData6810.rate (p i).all (p i).yz) (p i).all (p i).zOnly) :
    (∑ i ∈ s, count i) ≤ HigherBaseData6810.cap (sumFlag s p) := by
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi⟩ := hs
    have hpos := (hr i hi).trans (Finset.single_le_sum (f := fun i => (p i).all)
      (fun _ _ => Nat.zero_le _) hi)
    have hrows := AffineFactorAggregate6808.rate_bellman 34 156 HigherAffineRateData6810.rate
      (rate_mono hRate)
    have hb := AffineFactorAggregate6808.sum_count_le 34 156 HigherAffineSingleton6810.slope
      (fun r v => r*HigherAffineRateData6810.rate r v) (fun r v => r*HigherAffineRateData6810.rate r v)
      hrows s (fun i => (p i).all) (fun i => (p i).yz) (fun i => (p i).zOnly) count
      hr hR hY hcount
    unfold HigherBaseData6810.cap
    rw [base_value _ _ _ (by simpa [sumFlag] using hpos)
      (by simpa [sumFlag] using hR) (by simpa [sumFlag] using hY)]
    simpa [HigherAffineSingleton6810.cap,sumFlag] using hb
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

end ProximityPrize.SubmissionLower.HigherAffineRateBridge6810
