import ProximityPrize.SubmissionLower.Koala6831MovingPaidNumericData
import ProximityPrize.SubmissionLower.Koala6831ResidualPrices

namespace ProximityPrize.SubmissionLower.Koala6831MovingPaid

open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open Koala6831MovingSources Koala6831MovingStages Koala6831MovingAdaptive
open Koala6831MovingPairIncidence Koala6831MovingLedger

set_option Elab.async false
set_option maxRecDepth 20000
set_option autoImplicit false

private theorem direction_cumulative (P : ResidualSupportParameters) :
    (reducedAgreementDirection P).all = 2 * P.s - 2 ∧
      middle (reducedAgreementDirection P) = 2 * P.ys - 2 ∧
      total (reducedAgreementDirection P) = 2 * P.total - 2 := by
  have hs := P.one_le_s
  have hy := P.s_le_ys
  have ht := P.ys_le_total
  simp only [reducedAgreementDirection, middle, total, true_and]
  omega

private theorem direction_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) :
    Below (reducedAgreementDirection (stageSupport f hf))
      (reducedAgreementDirection (stageSupport g hg)) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  obtain ⟨hrf, hyf, htf⟩ := direction_cumulative (stageSupport f hf)
  obtain ⟨hrg, hyg, htg⟩ := direction_cumulative (stageSupport g hg)
  unfold Below
  rw [hrf, hrg, hyf, hyg, htf, htg]
  have hy' := max_le_max_left 2 hy
  have ht' := max_le_max_left 2 ht
  change _ ∧ (2 * max 2 (middle f) - 2 ≤ 2 * max 2 (middle g) - 2) ∧
    (2 * max 2 (total f) - 2 ≤ 2 * max 2 (total g) - 2)
  exact ⟨by simpa only [stageSupport] using Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hy') 2,
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 ht') 2⟩

private theorem below_scaled_add {f g : FlagDegree} (hfg : Below f g)
    (k : ℕ) (p q : FlagDegree) : Below (k • f + p + q) (k • g + p + q) := by
  obtain ⟨hr, hy, ht⟩ := hfg
  simp only [Below, middle, total, add_all, add_yz, add_zOnly, nsmul_all, nsmul_yz, nsmul_zOnly]
  have hS := Nat.mul_le_mul_left k hr
  have hY := Nat.mul_le_mul_left k hy
  have hT := Nat.mul_le_mul_left k ht
  simp only [middle, total, Nat.mul_add] at hY hT
  omega

theorem stagePrice_mono {f g : FlagDegree} (hf : 0 < f.all) (hg : 0 < g.all)
    (hfg : Below f g) (s : Stage) (gain : ℕ) :
    stagePrice f hf s gain ≤ stagePrice g hg s gain := by
  unfold stagePrice
  apply Nat.div_le_div_right
  apply (mixed_mono_first hfg _ _).trans
  apply mixed_mono_third
  unfold stageScaledCut scaledPairFlag
  exact below_scaled_add (direction_mono hf hg hfg) _ _ _

theorem adaptive1_stagePrice_le (f : FlagDegree) (hpos : 0 < f.all)
    (hcap : Below f postRoomCap) :
    stagePrice f hpos Stage.adaptive1 Stage.adaptive1.numbers.slopeCap ≤ adaptivePrice₁ :=
  (stagePrice_mono hpos (by decide +kernel) hcap _ _).trans (by decide +kernel)

private theorem cellChecks_of_flag (f : FlagDegree) (hpos : 0 < f.all)
    (hcap : Below f postRoomCap) : cellChecks f.all (middle f) hpos := by
  have hR : f.all ≤ 30 := hcap.1
  have hY : middle f ≤ 138 := hcap.2.1
  have hRY : f.all ≤ middle f := Nat.le_add_left _ _
  let r : Fin 30 := ⟨f.all - 1, by omega⟩
  have hr : r.val + 1 = f.all := by dsimp [r]; omega
  have hy : middle f - 1 + 1 = middle f := by omega
  have hmem : middle f - 1 ∈ List.range 138 := List.mem_range.mpr (by omega)
  have hcheck := List.all_eq_true.mp (checkedSlope_all r) (middle f - 1) hmem
  change checkAt (r.val + 1) (middle f - 1 + 1) (Nat.succ_pos r.val) = true at hcheck
  have hc : checkAt f.all (middle f) hpos = true := by
    simpa only [hr, hy] using hcheck
  rw [checkAt, if_pos hRY] at hc
  exact of_decide_eq_true hc

private theorem flagAt_le (f : FlagDegree) (t : ℕ) (hy : middle f ≤ t) (ht : t ≤ total f) :
    Below (flagAt f.all (middle f) t) f := by
  obtain ⟨hR, hY, hT⟩ := flagFromCaps_cumulative t (middle f) f.all (Nat.le_add_left _ _) hy
  change Below (flagFromCaps t (middle f) f.all) f
  change middle (flagFromCaps t (middle f) f.all) = middle f at hY
  change total (flagFromCaps t (middle f) f.all) = t at hT
  unfold Below
  rw [hT, hY, hR]
  exact ⟨le_rfl, le_rfl, ht⟩

private theorem le_flagAt (f : FlagDegree) (t : ℕ) (ht : total f ≤ t) :
    Below f (flagAt f.all (middle f) t) := by
  have hy : middle f ≤ total f := by unfold middle total; omega
  obtain ⟨hR, hY, hT⟩ := flagFromCaps_cumulative t (middle f) f.all (Nat.le_add_left _ _) (hy.trans ht)
  change Below f (flagFromCaps t (middle f) f.all)
  change middle (flagFromCaps t (middle f) f.all) = middle f at hY
  change total (flagFromCaps t (middle f) f.all) = t at hT
  unfold Below
  rw [hT, hY, hR]
  exact ⟨le_rfl, le_rfl, ht⟩

private theorem total_le_cutoff₁ (f : FlagDegree) (hpos : 0 < f.all)
    (hcap : Below f postRoomCap) (hfail : ¬ adaptiveGate Stage.adaptive1.numbers f) :
    total f ≤ (cutoffs f.all (middle f)).1 := by
  obtain ⟨hy, _, _, _, hcheck, _, _, _⟩ := cellChecks_of_flag f hpos hcap
  rcases hcheck with heq | hg
  · rw [heq]
    exact hcap.2.2
  · by_contra! hcontra
    exact hfail (adaptiveGate_mono _ (flagAt_le f _ hy hcontra) hpos ((evalGate_true _ _).mp hg))

private theorem total_le_cutoff₂ (f : FlagDegree) (hpos : 0 < f.all)
    (hcap : Below f postRoomCap) (hfail₁ : ¬ adaptiveGate Stage.adaptive1.numbers f)
    (hfail₂ : ¬ adaptiveGate Stage.adaptive2.numbers f) :
    total f ≤ (cutoffs f.all (middle f)).2 := by
  obtain ⟨_, hy, _, _, _, hcheck, _, _⟩ := cellChecks_of_flag f hpos hcap
  rcases hcheck with heq | hg
  · rw [heq]
    exact total_le_cutoff₁ f hpos hcap hfail₁
  · by_contra! hcontra
    exact hfail₂ (adaptiveGate_mono _ (flagAt_le f _ hy hcontra) hpos ((evalGate_true _ _).mp hg))

set_option maxHeartbeats 800000 in
theorem adaptive2_stagePrice_le (f : FlagDegree) (hpos : 0 < f.all)
    (hcap : Below f postRoomCap) (hfail₁ : ¬ adaptiveGate Stage.adaptive1.numbers f)
    (hgate : adaptiveGate Stage.adaptive2.numbers f) :
    stagePrice f hpos Stage.adaptive2 Stage.adaptive2.numbers.slopeCap ≤ adaptivePrice₂ := by
  let t := (cutoffs f.all (middle f)).1
  have ht : total f ≤ t := total_le_cutoff₁ f hpos hcap hfail₁
  have hy : middle f ≤ t := (show middle f ≤ total f by unfold middle total; omega).trans ht
  obtain ⟨_, _, _, _, _, _, hprice, _⟩ := cellChecks_of_flag f hpos hcap
  have hb := le_flagAt f t ht
  have hg := (evalGate_true Stage.adaptive2 (flagAt f.all (middle f) t)).mpr
    (adaptiveGate_mono _ hb hpos hgate)
  rcases hprice hy with hp | hf
  · exact (stagePrice_mono (g := flagAt f.all (middle f) t) hpos hpos hb _ _).trans hp
  · change evalGate _ (flagAt f.all (middle f) t) = false at hf
    exact Bool.noConfusion (hf.symm.trans hg)

set_option maxHeartbeats 800000 in
theorem adaptive3_stagePrice_le (f : FlagDegree) (hpos : 0 < f.all)
    (hcap : Below f postRoomCap) (hfail₁ : ¬ adaptiveGate Stage.adaptive1.numbers f)
    (hfail₂ : ¬ adaptiveGate Stage.adaptive2.numbers f)
    (hgate : adaptiveGate Stage.adaptive3.numbers f) :
    stagePrice f hpos Stage.adaptive3 Stage.adaptive3.numbers.slopeCap ≤ adaptivePrice₃ := by
  let t := (cutoffs f.all (middle f)).2
  have ht : total f ≤ t := total_le_cutoff₂ f hpos hcap hfail₁ hfail₂
  have hy : middle f ≤ t := (show middle f ≤ total f by unfold middle total; omega).trans ht
  obtain ⟨_, _, _, _, _, _, _, hprice⟩ := cellChecks_of_flag f hpos hcap
  have hb := le_flagAt f t ht
  have hg := (evalGate_true Stage.adaptive3 (flagAt f.all (middle f) t)).mpr
    (adaptiveGate_mono _ hb hpos hgate)
  rcases hprice hy with hp | hf
  · exact (stagePrice_mono (g := flagAt f.all (middle f) t) hpos hpos hb _ _).trans hp
  · change evalGate _ (flagAt f.all (middle f) t) = false at hf
    exact Bool.noConfusion (hf.symm.trans hg)

private theorem fixed_credit_scale (left right cut : FlagDegree) :
    flagMixed left right (30030 • cut) / (agreementScale * 30030) =
      flagMixed left right cut / agreementScale := by
  have h : flagMixed left right (30030 • cut) = flagMixed left right cut * 30030 := by
    simp only [flagMixed, nsmul_all, nsmul_yz, nsmul_zOnly]
    ring
  rw [h, Nat.mul_div_mul_right _ _ (by decide : 0 < 30030)]

theorem fixedRoomCredits_eq_certificate (f : Koala6831Residual.Envelope) :
    fixedRoomCredit₁ f.flag + fixedRoomCredit₂ f.flag = Koala6831Residual.roomCredit f := by
  let c : Koala6831Residual.Envelope := ⟨f.slope, f.middle, f.middle⟩
  have hc : c.flag = creditFlag f.flag := by
    simp [c, creditFlag, Koala6831Residual.Envelope.flag]
  have h₁ : Koala6831Residual.pairPrice c ⟨384, 1717, 107468⟩ ⟨80, 360, 53188⟩ =
      fixedRoomCredit₁ f.flag := by
    unfold Koala6831Residual.pairPrice
    rw [hc]
    change flagMixed (creditFlag f.flag) (stagePartnerFlag Stage.room1 Stage.room1.roomOrder)
      (30030 • stageScaledCut primaryIncoming (by decide +kernel)) /
      (agreementScale * 30030) = _
    exact fixed_credit_scale _ _ _
  have h₂ : Koala6831Residual.pairPrice c ⟨402, 1805, 601718⟩ ⟨54, 245, 15351⟩ =
      fixedRoomCredit₂ f.flag := by
    unfold Koala6831Residual.pairPrice
    rw [hc]
    change flagMixed (creditFlag f.flag) (stagePartnerFlag Stage.room2 Stage.room2.roomOrder)
      (30030 • stageScaledCut secondRoomIncoming (by decide +kernel)) /
      (agreementScale * 30030) = _
    exact fixed_credit_scale _ _ _
  rw [← h₁, ← h₂]
  rfl

end ProximityPrize.SubmissionLower.Koala6831MovingPaid
