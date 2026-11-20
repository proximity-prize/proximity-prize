import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open RCN081 RCN095 RCN130 RCN156 RCN180 RCN234 RCN266
open LocatorFactorAggregate LocatorLowQuotient LocatorTwoFactorAvoidance
open LocatorBatchProductRoute LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open LocatorPhase6800Audit (powerBandBudget_mono_fuel)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
local instance stageDecidableEq : DecidableEq K := Classical.decEq K

private theorem div_remainder_lt (a b : ℕ) (hb : 0 < b) : a - (a / b) * b < b := by
  have hm := Nat.mod_lt a hb
  have heq := Nat.mod_add_div' a b
  omega

private theorem fuel_terminal (s : SourceNumbers) (f : FlagDegree) (hr : 0 < f.all) :
    s.totalCap - s.fuel f * total f < total f ∨
    s.middleCap - s.fuel f * middle f < middle f ∨
    s.slopeCap - s.fuel f * f.all < f.all := by
  have hy : 0 < middle f := by unfold middle; omega
  have ht : 0 < total f := by unfold total; omega
  unfold LocatorPhase6800Oracle.SourceNumbers.fuel
  by_cases hT : s.totalCap / total f ≤ min (s.middleCap / middle f) (s.slopeCap / f.all)
  · left
    rw [min_eq_left hT]
    exact div_remainder_lt s.totalCap (total f) ht
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY : s.middleCap / middle f ≤ s.slopeCap / f.all
    · right; left
      rw [min_eq_left hY]
      exact div_remainder_lt s.middleCap (middle f) hy
    · right; right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact div_remainder_lt s.slopeCap f.all hr

def geometricBand (gain : ℕ) (source : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget gain (total p) (middle p) p.all
    (source.totalCap - total p) (source.middleCap - middle p)
    (source.slopeCap - p.all) (source.fuel p)

theorem geometricBand_antitone (gain : ℕ) (source : SourceNumbers) {p q : FlagDegree}
    (h : Below p q) (hs : 0 < p.all) : geometricBand gain source q ≤ geometricBand gain source p := by
  have hy : 0 < middle p := by unfold middle; omega
  have ht : 0 < total p := by unfold total; omega
  have hfuel : source.fuel q ≤ source.fuel p := by
    unfold LocatorPhase6800Oracle.SourceNumbers.fuel
    exact min_le_min (Nat.div_le_div_left h.2.2 ht)
      (min_le_min (Nat.div_le_div_left h.2.1 hy) (Nat.div_le_div_left h.1 hs))
  unfold geometricBand
  have hsameFuel := powerBandBudget_mono gain
    (total q) (middle q) q.all (source.totalCap - total q) (source.middleCap - middle q)
    (source.slopeCap - q.all)
    (total p) (middle p) p.all (source.totalCap - total p) (source.middleCap - middle p)
    (source.slopeCap - p.all) (source.fuel q)
    (Nat.sub_le_sub_left h.2.2 _) (Nat.sub_le_sub_left h.2.1 _)
    (Nat.sub_le_sub_left h.1 _) h.2.2 h.2.1 h.1
  exact hsameFuel.trans (powerBandBudget_mono_fuel _ _ _ _ _ _ _ hfuel)

def geometricGate (gain : ℕ) (source : SourceNumbers) (p : FlagDegree) : Prop :=
  geometricBand gain source p < source.gap

theorem geometricGate_mono (gain : ℕ) (source : SourceNumbers) {p q : FlagDegree}
    (h : Below p q) (hs : 0 < p.all) (hactive : geometricGate gain source p) :
    geometricGate gain source q :=
  (geometricBand_antitone gain source h hs).trans_lt hactive

theorem exists_adaptive_source_exit (s : SourceNumbers) (cutoff weight gain : ℕ)
    (hw : 1 ≤ weight) (r : V →ₗ[K] MvPolynomial (Fin 4) K) (hrInjective : Function.Injective r)
    (hBox : ∀ v, r v ∈ nestedCoefficientBox K cutoff weight s.totalCap s.middleCap s.slopeCap)
    (hdim : s.gap ≤ Module.finrank K V)
    (H : MvPolynomial (Fin 4) K)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty) (hfield : A.card < ENat.card K)
    (hr : 0 < (originalCumulativeFlag (regularProduct H A)).all)
    (hfuel : 0 < s.fuel (originalCumulativeFlag (regularProduct H A)))
    (hgate : geometricGate gain s (originalCumulativeFlag (regularProduct H A))) :
    ∃ U ⊂ A, ∃ v : V, ∃ j : ℕ,
      j ≤ s.fuel (originalCumulativeFlag (regularProduct H A)) ∧
      r v ≠ 0 ∧
      r v ∈ nestedCoefficientBox K (cutoff-j*gain) weight s.totalCap s.middleCap s.slopeCap ∧
      ∀ F ∈ A \ U, ∃ J : MvPolynomial (Fin 4) K,
        r v = F.1^j * J ∧ ¬ F.1 ∣ J := by
  classical
  let P := regularProduct H A
  let f := originalCumulativeFlag P
  let U₀ := universalFactors H A r
  have box_of_weight (v : V) (D : ℕ)
      (hweight : wt (contactWeights weight) (r v) < D) :
      r v ∈ nestedCoefficientBox K D weight s.totalCap s.middleCap s.slopeCap := by
    intro d hd
    have hbox := hBox v hd
    have hweighted := (MvPolynomial.le_weightedTotalDegree (contactWeights weight) hd).trans_lt hweight
    exact ⟨hbox.1, hbox.2.1, hbox.2.2.1, by simpa only [contact_weight] using hweighted⟩
  have hP : P ≠ 0 := regularProduct_ne_zero H A
  have ⟨hR, hY, hT⟩ := originalCumulativeFlag_cumulative P
  change middle (originalCumulativeFlag P) = wt residualYSWeights P at hY
  change total (originalCumulativeFlag P) = wt residualTotalWeights P at hT
  by_cases hU₀ : U₀ = A
  · have hd : ∀ v : V, P ∣ r v := by
      intro v
      have hv : regularProduct H U₀ ∣ r v := universalProduct_dvd H A r v
      rwa [hU₀] at hv
    obtain ⟨hq, hproduct, hqbox⟩ := quotientLinear_nested_data cutoff weight
      s.totalCap s.middleCap s.slopeCap r hrInjective
      (hBox) P hP hd
    let q := quotientLinear r P hP hd
    let fuel := s.fuel f
    let steps := fuel - 1
    have hsteps : steps + 1 = fuel := by
      change fuel - 1 + 1 = fuel
      have hp : 0 < fuel := hfuel
      omega
    let dw := wt (contactWeights weight) P
    let dt := wt residualTotalWeights P
    let dy := wt residualYSWeights P
    let dr := wt residualSWeights P
    let hi := cutoff - dw
    let low := hi - gain
    let availT := s.totalCap - dt
    let availY := s.middleCap - dy
    let availR := s.slopeCap - dr
    have hband : powerBandBudgetThin weight hi gain dw dt dy dr availT availY availR (steps + 1) <
        Module.finrank K (V) := by
      apply (powerBandBudgetThin_le weight gain dw dt dy dr (steps + 1) hi availT availY availR).trans_lt
      rw [hsteps]
      have hg : powerBandBudget gain dt dy dr availT availY availR fuel < s.gap := by
        change geometricGate gain s f at hgate
        simpa only [geometricGate, geometricBand, f, hR, hY, hT, dt, dy, dr, fuel, availT, availY, availR]
          using hgate
      exact hg.trans_le hdim
    have hterm : availT - steps * dt < dt ∨ availY - steps * dy < dy ∨
        availR - steps * dr < dr := by
      have hf := fuel_terminal s f hr
      change s.totalCap - fuel * total f < total f ∨
        s.middleCap - fuel * middle f < middle f ∨
        s.slopeCap - fuel * f.all < f.all at hf
      have ht : dt = total f := hT.symm
      have hy : dy = middle f := hY.symm
      have hs : dr = f.all := hR.symm
      rw [← hsteps, ← ht, ← hy, ← hs] at hf
      simpa only [availT, availY, availR, Nat.add_mul, Nat.one_mul, Nat.sub_sub, Nat.add_comm] using hf
    obtain ⟨j, U, v, J, hU, hv, hJ, heq, hJbox, hJavoid⟩ :=
      exists_batchExitStage_of_bandBudgetThin_succ steps hi low weight gain availT availY availR
        hw rfl q hq hqbox H A hA hband hterm hfield
    have hsourceEq : r v = P ^ (j.val + 1) * J := by
      rw [hproduct v, ← heq, pow_succ', mul_assoc]
    have hnz : r v ≠ 0 := hsourceEq ▸ mul_ne_zero (pow_ne_zero _ hP) hJ
    have hJweight := (nested_mem_weights hJbox hJ).2.2.2
    have hweight : wt (contactWeights weight) (r v) < cutoff - (j.val + 1) * gain := by
      have hmul := weightedTotalDegree_mul (contactWeights weight) (P ^ (j.val + 1)) J
        (pow_ne_zero _ hP) hJ
      change wt (contactWeights weight) (P ^ (j.val + 1) * J) = _ at hmul
      rw [hsourceEq, hmul]
      change wt (contactWeights weight) (P ^ (j.val + 1)) + wt (contactWeights weight) J < _
      rw [wt_pow_eq _ P hP]
      change wt (contactWeights weight) J < cutoff - dw - gain -
        j.val * gain - j.val * dw at hJweight
      change (j.val + 1) * dw + wt (contactWeights weight) J < _
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    have hpow : j.val + 1 ≤ fuel := by have hp := j.isLt; omega
    refine ⟨U, hU, v, j.val + 1, hpow, hnz,
      box_of_weight v _ hweight, ?_⟩
    intro F hF
    have hFA := (Finset.mem_sdiff.mp hF).1
    refine ⟨regularCofactor H A F ^ (j.val + 1) * J,
      hsourceEq.trans (regularProduct_power_split H A F hFA _ J), ?_⟩
    exact ((RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd).mp
      (regularFactor_isRelPrime_liftedHelper H A F hFA _ J (hJavoid F hF))
  · have hU₀sub := universalFactors_subset H A r
    have hstrict : U₀ ⊂ A := (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hU₀⟩
    have hremoved : (A \ U₀).Nonempty := Finset.sdiff_nonempty.mpr hstrict.not_ge
    have hc : (A \ U₀).card < ENat.card K := by
      have h := Finset.card_le_card (Finset.sdiff_subset (s := A) (t := U₀))
      exact (by exact_mod_cast h : ((A \ U₀).card : ENat) ≤ A.card).trans_lt hfield
    obtain ⟨v, hv, hav⟩ := exists_avoiding_nonuniversal_factors (A \ U₀) hremoved r
      (fun F => F.1) (fun F hF hdiv => (Finset.mem_sdiff.mp hF).2
        ((mem_universalFactors H A r F).mpr ⟨(Finset.mem_sdiff.mp hF).1, hdiv⟩)) hc
    have hnz : r v ≠ 0 := fun h => hv (hrInjective (h.trans (map_zero r).symm))
    refine ⟨U₀, hstrict, v, 0, Nat.zero_le _, hnz, ?_, fun F hF => ?_⟩
    · simpa only [Nat.zero_mul, Nat.sub_zero] using hBox v
    · exact ⟨r v, by rw [pow_zero, one_mul], hav F hF⟩


end

end ProximityPrize.SubmissionLower.Koala6844Receipts
