/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the 68.32 work of Bome2017, after Lucieno and BitWonka. New 68.33 source and variable input caps. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/
import ProximityPrize.SubmissionLower.Mid6833K6833FlowSources
import ProximityPrize.SubmissionLower.Koala6831MovingPartner

namespace ProximityPrize.SubmissionLower.K6833FlowAdaptive

open RCN081 RCN095 RCN130 RCN156 RCN180 RCN234 RCN266
open LocatorFactorAggregate LocatorLowQuotient LocatorTwoFactorAvoidance
open LocatorBatchProductRoute LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open K6833FlowSources K6833FlowStages Koala6831Moving

noncomputable section

variable {K : Type} [Field K]
variable {I : Type*} [Fintype I]
local instance movingAdaptiveDecidableEq : DecidableEq K := Classical.decEq K

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

private theorem stage_box_of_weight_lt (s : Stage) (nodes u₀ u₁ : I → K)
    (v : s.Kernel K nodes u₀ u₁) (newCutoff : ℕ)
    (hweight : wt (contactWeights weight) (s.reconstruct K nodes u₀ u₁ v) < newCutoff) :
    s.reconstruct K nodes u₀ u₁ v ∈ nestedCoefficientBox K newCutoff weight
      s.numbers.totalCap s.numbers.middleCap s.numbers.slopeCap := by
  intro d hd
  have hbox := s.reconstruct_mem_box K nodes u₀ u₁ v hd
  have hweighted := (MvPolynomial.le_weightedTotalDegree (contactWeights weight) hd).trans_lt hweight
  exact ⟨hbox.1, hbox.2.1, hbox.2.2.1, by simpa only [contact_weight] using hweighted⟩

theorem exists_adaptive_exit_source (s : Stage) (nodes u₀ u₁ : I → K)
    (hcard : Fintype.card I ≤ 262144) (H : MvPolynomial (Fin 4) K)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty) (hfield : A.card < ENat.card K)
    (hr : 0 < (originalCumulativeFlag (regularProduct H A)).all)
    (hfuel : 0 < s.numbers.fuel (originalCumulativeFlag (regularProduct H A)))
    (hgate : adaptiveGate s.numbers (originalCumulativeFlag (regularProduct H A))) :
    ∃ U ⊂ A, ∃ v : s.Kernel K nodes u₀ u₁, ∃ j : ℕ,
      j ≤ s.numbers.fuel (originalCumulativeFlag (regularProduct H A)) ∧
      s.reconstruct K nodes u₀ u₁ v ≠ 0 ∧
      s.reconstruct K nodes u₀ u₁ v ∈ nestedCoefficientBox K
        (s.cutoff - j * weightGain) weight s.numbers.totalCap s.numbers.middleCap
        s.numbers.slopeCap ∧
      ∀ F ∈ A \ U, ∃ J : MvPolynomial (Fin 4) K,
        s.reconstruct K nodes u₀ u₁ v = F.1 ^ j * J ∧ ¬ F.1 ∣ J := by
  classical
  let P := regularProduct H A
  let f := originalCumulativeFlag P
  let r := s.reconstruct K nodes u₀ u₁
  let U₀ := universalFactors H A r
  have hP : P ≠ 0 := regularProduct_ne_zero H A
  have hrInjective := s.reconstruct_injective K nodes u₀ u₁
  have ⟨hR, hY, hT⟩ := originalCumulativeFlag_cumulative P
  change middle (originalCumulativeFlag P) = wt residualYSWeights P at hY
  change total (originalCumulativeFlag P) = wt residualTotalWeights P at hT
  by_cases hU₀ : U₀ = A
  · have hd : ∀ v : s.Kernel K nodes u₀ u₁, P ∣ r v := by
      intro v
      have hv : regularProduct H U₀ ∣ r v := universalProduct_dvd H A r v
      rwa [hU₀] at hv
    obtain ⟨hq, hproduct, hqbox⟩ := quotientLinear_nested_data s.cutoff weight
      s.numbers.totalCap s.numbers.middleCap s.numbers.slopeCap r hrInjective
      (s.reconstruct_mem_box K nodes u₀ u₁) P hP hd
    let q := quotientLinear r P hP hd
    let fuel := s.numbers.fuel f
    let steps := fuel - 1
    have hsteps : steps + 1 = fuel := by
      change fuel - 1 + 1 = fuel
      have hp : 0 < fuel := hfuel
      omega
    let dw := wt (contactWeights weight) P
    let dt := wt residualTotalWeights P
    let dy := wt residualYSWeights P
    let dr := wt residualSWeights P
    let hi := s.cutoff - dw
    let low := hi - weightGain
    let availT := s.numbers.totalCap - dt
    let availY := s.numbers.middleCap - dy
    let availR := s.numbers.slopeCap - dr
    have hband : powerBandBudgetThin weight hi weightGain dw dt dy dr availT availY availR (steps + 1) <
        Module.finrank K (s.Kernel K nodes u₀ u₁) := by
      apply (powerBandBudgetThin_le weight weightGain dw dt dy dr (steps + 1) hi availT availY availR).trans_lt
      rw [hsteps]
      have hg : powerBandBudget weightGain dt dy dr availT availY availR fuel < s.numbers.gap := by
        change adaptiveGate s.numbers f at hgate
        simpa only [adaptiveGate, adaptiveBand, f, hR, hY, hT, dt, dy, dr, fuel, availT, availY, availR]
          using hgate
      exact hg.trans_le (s.finrank_lower_bound K nodes u₀ u₁ hcard)
    have hterm : availT - steps * dt < dt ∨ availY - steps * dy < dy ∨
        availR - steps * dr < dr := by
      have hf := fuel_terminal s.numbers f hr
      change s.numbers.totalCap - fuel * total f < total f ∨
        s.numbers.middleCap - fuel * middle f < middle f ∨
        s.numbers.slopeCap - fuel * f.all < f.all at hf
      have ht : dt = total f := hT.symm
      have hy : dy = middle f := hY.symm
      have hs : dr = f.all := hR.symm
      rw [← hsteps, ← ht, ← hy, ← hs] at hf
      simpa only [availT, availY, availR, Nat.add_mul, Nat.one_mul, Nat.sub_sub, Nat.add_comm] using hf
    obtain ⟨j, U, v, J, hU, hv, hJ, heq, hJbox, hJavoid⟩ :=
      exists_batchExitStage_of_bandBudgetThin_succ steps hi low weight weightGain availT availY availR
        (by decide +kernel) rfl q hq hqbox H A hA hband hterm hfield
    have hsourceEq : r v = P ^ (j.val + 1) * J := by
      rw [hproduct v, ← heq, pow_succ', mul_assoc]
    have hnz : r v ≠ 0 := hsourceEq ▸ mul_ne_zero (pow_ne_zero _ hP) hJ
    have hJweight := (nested_mem_weights hJbox hJ).2.2.2
    have hweight : wt (contactWeights weight) (r v) < s.cutoff - (j.val + 1) * weightGain := by
      have hmul := weightedTotalDegree_mul (contactWeights weight) (P ^ (j.val + 1)) J
        (pow_ne_zero _ hP) hJ
      change wt (contactWeights weight) (P ^ (j.val + 1) * J) = _ at hmul
      rw [hsourceEq, hmul]
      change wt (contactWeights weight) (P ^ (j.val + 1)) + wt (contactWeights weight) J < _
      rw [wt_pow_eq _ P hP]
      change wt (contactWeights weight) J < s.cutoff - dw - weightGain -
        j.val * weightGain - j.val * dw at hJweight
      change (j.val + 1) * dw + wt (contactWeights weight) J < _
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    have hpow : j.val + 1 ≤ fuel := by have hp := j.isLt; omega
    refine ⟨U, hU, v, j.val + 1, hpow, hnz,
      stage_box_of_weight_lt s nodes u₀ u₁ v _ hweight, ?_⟩
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
    · simpa only [Nat.zero_mul, Nat.sub_zero] using s.reconstruct_mem_box K nodes u₀ u₁ v
    · exact ⟨r v, by rw [pow_zero, one_mul], hav F hF⟩

theorem exists_adaptive_exit_partners {p : ℕ} [CharP K p]
    (s : Stage) (B : FlowData K) (nodes u₀ u₁ normalized : I → K)
    (hcard : Fintype.card I ≤ 262144) (hchar : s.numbers.slopeCap < p)
    (h₀ : ∀ i, B.d0.eval (nodes i) * u₀ i + B.c0.eval (nodes i) =
      B.a0.eval (nodes i) * normalized i)
    (h₁ : ∀ i, B.d0.eval (nodes i) * u₁ i + B.c1.eval (nodes i) =
      B.a1.eval (nodes i) * normalized i)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ 9568)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ weight + 9568)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hA : A.Nonempty) (hfield : A.card < ENat.card K)
    (hr : 0 < (originalCumulativeFlag (regularProduct H A)).all)
    (hfuel : 0 < s.numbers.fuel (originalCumulativeFlag (regularProduct H A)))
    (hgate : adaptiveGate s.numbers (originalCumulativeFlag (regularProduct H A)))
    (htrans : ∀ F ∈ A, ¬ F.1 ∣ B.flow F.1) :
    ∃ U ⊂ A, ∀ F ∈ A \ U, ∃ Q : MvPolynomial (Fin 4) K,
      IsRelPrime F.1 Q ∧ Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
        (s.numbers.totalCap + s.numbers.slopeCap) s.numbers.middleCap s.numbers.slopeCap ∧
      ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q := by
  obtain ⟨U, hU, v, j, hj, hv, hb, hexact⟩ :=
    exists_adaptive_exit_source s nodes u₀ u₁ hcard H A hA hfield hr hfuel hgate
  have hjSlope : j ≤ s.numbers.slopeCap := by
    let f := originalCumulativeFlag (regularProduct H A)
    change j ≤ s.numbers.fuel f at hj
    have hf : s.numbers.fuel f ≤ s.numbers.slopeCap / f.all :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact hj.trans (hf.trans (Nat.div_le_self _ _))
  have hroom : (s.cutoff - j * weightGain) + j * (2 * 9568) ≤ s.multiplicity * agreement := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hv
    have hpositive := (hb hd).2.2.2
    have hle : j * weightGain ≤ s.cutoff := by omega
    change s.cutoff - j * weightGain + j * weightGain ≤ s.multiplicity * agreement
    rw [Nat.sub_add_cancel hle]
    exact Nat.sub_le _ _
  refine ⟨U, hU, fun F hF => ?_⟩
  have hFA := (Finset.mem_sdiff.mp hF).1
  obtain ⟨J, heq, hJ⟩ := hexact F hF
  have hb' := heq ▸ hb
  have hc : ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i)
      s.multiplicity (F.1 ^ j * J) := by
    intro i
    rw [← heq]
    exact s.reconstruct_contact K nodes u₀ u₁ v i
  obtain ⟨Q, hrel, hbox, hcontact⟩ := B.exists_contact_partner_of_room nodes u₀ u₁ normalized
    h₀ h₁ (RCN167.positiveRFactors_spec H F.1 F.2).1 hJ (htrans F hFA)
    (hjSlope.trans_lt hchar) (by decide +kernel) (by decide +kernel) hden hminor hroom hb' hc
  refine ⟨Q, hrel, ?_, hcontact⟩
  intro d hd
  have h := hbox hd
  exact ⟨h.1.trans (Nat.add_le_add_left hjSlope _), h.2⟩

theorem exhaust_finset_stage {α : Type*} [DecidableEq α] (initial : Finset α)
    (active : Finset α → Prop) (covered : α → Prop)
    (step : ∀ S ⊆ initial, S.Nonempty → active S →
      ∃ U ⊂ S, ∀ a ∈ S \ U, covered a) :
    ∃ U ⊆ initial, (U = ∅ ∨ ¬ active U) ∧ ∀ a ∈ initial \ U, covered a := by
  classical
  have hfinish (S : Finset α) (hsub : S ⊆ initial) :
      ∃ U ⊆ S, (U = ∅ ∨ ¬ active U) ∧ ∀ a ∈ S \ U, covered a := by
    induction S using Finset.strongInductionOn
    rename_i S ih
    by_cases hact : S.Nonempty ∧ active S
    · obtain ⟨V, hV, hcovered⟩ := step S hsub hact.1 hact.2
      obtain ⟨U, hUV, hstop, hrec⟩ := ih V hV (hV.subset.trans hsub)
      refine ⟨U, hUV.trans hV.subset, hstop, fun a ha => ?_⟩
      obtain ⟨haS, haU⟩ := Finset.mem_sdiff.mp ha
      by_cases haV : a ∈ V
      · exact hrec a (Finset.mem_sdiff.mpr ⟨haV, haU⟩)
      · exact hcovered a (Finset.mem_sdiff.mpr ⟨haS, haV⟩)
    · refine ⟨S, fun _ h => h, ?_, fun a ha => ?_⟩
      · by_cases hz : S.Nonempty
        · exact Or.inr (fun hf => hact ⟨hz, hf⟩)
        · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hz)
      · exact ((Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp ha).1).elim
  exact hfinish initial (fun _ h => h)

end

end ProximityPrize.SubmissionLower.K6833FlowAdaptive
