import ProximityPrize.SubmissionLower.AffineSingleData6808
import ProximityPrize.SubmissionLower.AffineSingletonGeometry6808
import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics6808

namespace ProximityPrize.SubmissionLower.AffineSingleBridge6808
open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open AffineSingleton6808 Lower80830.PhaseRows Lower80830.PhaseData
open Lower80830.PhaseSemantics Lower80830.PhaseChecks Lower80830.ThresholdFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def RateAt (r v : ℕ) : Prop :=
  (r+1≤32 → r+1+v≤149 → AffineRateData6808.rate r v ≤ AffineRateData6808.rate (r+1) v) ∧
  (r+(v+1)≤149 → AffineRateData6808.rate r v ≤ AffineRateData6808.rate r (v+1))
instance (r v : ℕ) : Decidable (RateAt r v) := by unfold RateAt; infer_instance

def RateReceipt : Prop := ∀ r v, 1≤r → r≤32 → r+v≤149 → RateAt r v

theorem rate_zero (v : ℕ) : AffineRateData6808.rate 0 v = 0 := by
  simp [AffineRateData6808.rate]

theorem rate_r_mono (hc : RateReceipt) (r R v : ℕ)
    (hr : r≤R) (hR : R≤32) (hY : R+v≤149) :
    AffineRateData6808.rate r v ≤ AffineRateData6808.rate R v := by
  by_cases h0 : r=0
  · subst r; rw [rate_zero]; exact Nat.zero_le _
  induction R,hr using Nat.le_induction with
  | base => exact le_rfl
  | succ R hr ih =>
    exact (ih (by omega) (by omega)).trans ((hc R v (by omega) (by omega) (by omega)).1 (by omega) (by omega))

theorem rate_v_mono (hc : RateReceipt) (r v V : ℕ)
    (hv : v≤V) (hR : r≤32) (hY : r+V≤149) :
    AffineRateData6808.rate r v ≤ AffineRateData6808.rate r V := by
  by_cases h0 : r=0
  · subst r; simp [rate_zero]
  induction V,hv using Nat.le_induction with
  | base => exact le_rfl
  | succ V hv ih =>
    exact (ih (by omega)).trans ((hc r V (by omega) hR (by omega)).2 (by omega))

theorem rate_mono (hc : RateReceipt) (r v R V : ℕ)
    (hr : r≤R) (hv : v≤V) (hR : R≤32) (hY : R+V≤149) :
    AffineRateData6808.rate r v ≤ AffineRateData6808.rate R V :=
  (rate_r_mono hc r R v hr hR (by omega)).trans (rate_v_mono hc R v V hv hR hY)

theorem count_le_affine
    (r v z count : ℕ) (hr : 1≤r) (hR : r≤32) (hY : r+v≤149) (hT : r+v+z≤8121)
    (hvalid : AffineSingleData6808.Valid r v)
    (hthreshold : ThresholdAt r v)
    (hraw : BoundaryTailGates6808.Safe r (r+v) → count ≤ BoundaryTailShape6808.cost r v z)
    (hroot : AffineSingleton6808.Active (lookup r v).threshold 1 r v z z →
      count ≤ BoundaryTailAffineRounding6808.rootUpper r v z)
    (hsource : ∀ j, j<10 → (phaseSource j).Routeable (rawFlag r v z) →
      count ≤ (phasePotential j).eval (rawFlag r v z)) :
    count ≤ AffineSingleton6808.cap (AffineRateData6808.rate r v) r z := by
  rcases hvalid with ⟨hc,hcover⟩
  obtain ⟨w,hw,hbound⟩ := cover_sound (AffineSingleData6808.carrier r v)
    (AffineRateData6808.rate r v) r v (lookup r v).threshold
    (8122-r-v) 0 (AffineSingleData6808.cover r v) hcover z (Nat.zero_le _) (by omega)
  apply le_trans (b := choice (AffineSingleData6808.carrier r v) w r v z) ?_ hbound
  by_cases h0 : w=0
  · subst w
    simp only [choice,if_pos,AffineSingleton6808.Active] at hw ⊢
    rw [Carrier.eval_correct _ r v z hr hc]
    exact hraw hw
  by_cases h1 : w=1
  · subst w
    simpa only [choice,if_neg (by decide : ¬(1:ℕ)=0),if_pos] using hroot hw
  · have hw' : w-2<10 ∧ thresholdAt (lookup r v).threshold (w-2) ≤ z := by
      simpa only [AffineSingleton6808.Active,if_neg h0,if_neg h1] using hw
    have ht := hthreshold (w-2) (List.mem_range.mpr hw'.1)
    have route := sufficient_route (phaseSource (w-2)) r v
      (thresholdAt (rowContext r v).threshold (w-2)) z
      (source_total (w-2) hw'.1) hT hw'.2 ht
    simpa only [choice,if_neg h0,if_neg h1] using hsource (w-2) hw'.1 route

theorem base_value (r v z : ℕ) (hr : 1≤r) (hR : r≤32) (hY : r+v≤149) :
    (BoundaryTailBaseData6808.lookup r v).evalAt z =
      AffineSingleton6808.cap (AffineRateData6808.rate r v) r z := by
  have hbox : 1≤r ∧ r≤32 ∧ r+v≤149 := ⟨hr,hR,hY⟩
  rw [BoundaryTailBaseData6808.lookup,if_pos hbox]
  dsimp [BaseRow.evalAt,evalBaseSegments,BaseSegment.evalAt,AffineSingleton6808.cap,AffineSingleton6808.slope]
  split_ifs <;> omega


structure Receipt : Prop where
  single : ∀ r v, 1≤r → r≤32 → r+v≤149 → AffineSingleData6808.Valid r v
  rate : RateReceipt

theorem sum_count_le_base {ι : Type} [DecidableEq ι]
    (hRate : RateReceipt) (s : Finset ι) (p : ι → FlagDegree) (count : ι → ℕ)
    (hr : ∀ i ∈ s, 1≤(p i).all)
    (hR : (∑ i ∈ s, (p i).all)≤32)
    (hY : (∑ i ∈ s, (p i).all)+(∑ i ∈ s, (p i).yz)≤149)
    (hcount : ∀ i ∈ s, count i ≤ AffineSingleton6808.cap
      (AffineRateData6808.rate (p i).all (p i).yz) (p i).all (p i).zOnly) :
    (∑ i ∈ s, count i) ≤ BoundaryTailBaseData6808.cap (sumFlag s p) := by
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi⟩ := hs
    have hpos := (hr i hi).trans (Finset.single_le_sum (f := fun i => (p i).all)
      (fun _ _ => Nat.zero_le _) hi)
    have hrows := AffineFactorAggregate6808.rate_bellman 32 149 AffineRateData6808.rate
      (rate_mono hRate)
    have hb := AffineFactorAggregate6808.sum_count_le 32 149 AffineSingleton6808.slope
      (fun r v => r*AffineRateData6808.rate r v) (fun r v => r*AffineRateData6808.rate r v)
      hrows s (fun i => (p i).all) (fun i => (p i).yz) (fun i => (p i).zOnly) count
      hr hR hY hcount
    unfold BoundaryTailBaseData6808.cap
    rw [base_value _ _ _ (by simpa [sumFlag] using hpos)
      (by simpa [sumFlag] using hR) (by simpa [sumFlag] using hY)]
    simpa [AffineSingleton6808.cap,sumFlag] using hb
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

end ProximityPrize.SubmissionLower.AffineSingleBridge6808
