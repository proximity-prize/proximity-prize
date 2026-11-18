import ProximityPrize.SubmissionLower.Koala6831ResidualFactorRouting
import ProximityPrize.SubmissionLower.Koala6831ResidualHelperCount

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open scoped Classical BigOperators
open RCN095 RCN263 RCN275 RCN277 LocatorFactorAggregate
open Koala6831MovingPairIncidence (scaledPairFlag)

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000

private def terminalPairCut (f : Envelope) : FlagDegree :=
  let slopeScale := (terminalScale / 181078) * 262144 * 131071
  let nodeScale := (terminalScale / (181078 - 131071)) * (262144 - 131071)
  ⟨2 * slopeScale * (f.total - f.middle) + 81067 * terminalScale,
    2 * slopeScale * (f.middle - f.slope) + nodeScale,
    2 * slopeScale * (f.slope - 1)⟩

private theorem scaledPairFlag_mono_nodes (support : ResidualSupportParameters) {n m : ℕ}
    (h : n ≤ m) :
    let a := scaledPairFlag support n 131071 181078 81066
    let b := scaledPairFlag support m 131071 181078 81066
    a.zOnly ≤ b.zOnly ∧ a.yz ≤ b.yz ∧ a.all ≤ b.all := by
  have hlen : n * 131071 * (181078 - 131071) ≤ m * 131071 * (181078 - 131071) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
  have hnode : (n - 131071) * 181078 ≤ (m - 131071) * 181078 :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_right h _)
  simp only [scaledPairFlag, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all,
    unitYZFlag, unitZFlag, mul_zero, mul_one, add_zero]
  exact ⟨Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _,
    Nat.add_le_add (Nat.mul_le_mul_right _ hlen) hnode, Nat.mul_le_mul_right _ hlen⟩

private theorem scaledPairFlag_full_eq (f : Envelope) (support : ResidualSupportParameters)
    (hS : support.s = f.slope) (hY : support.ys = f.middle) (hT : support.total = f.total) :
    30030 • scaledPairFlag support 262144 131071 181078 81066 = terminalPairCut f := by
  unfold scaledPairFlag terminalPairCut
  have hlast : 2 * f.slope - 2 = 2 * (f.slope - 1) := by omega
  apply LocatorHybridCells.flag_ext <;>
    simp only [reducedAgreementDirection, add_zOnly, add_yz, add_all,
      nsmul_zOnly, nsmul_yz, nsmul_all, unitYZFlag, unitZFlag, hS, hY, hT, hlast,
      mul_zero, mul_one, add_zero] <;> norm_num [terminalScale] <;> ring

private theorem terminalPairCut_ge (f : Envelope) (support : ResidualSupportParameters)
    (hS : support.s = f.slope) (hY : support.ys = f.middle) (hT : support.total = f.total)
    {n : ℕ} (hn : n ≤ 262144) :
    Below (30030 • scaledPairFlag support n 131071 181078 81066) (terminalPairCut f) := by
  rw [← scaledPairFlag_full_eq f support hS hY hT]
  obtain ⟨hz, hy, hr⟩ := scaledPairFlag_mono_nodes support hn
  unfold Below middle total
  simp only [nsmul_zOnly, nsmul_yz, nsmul_all]
  exact ⟨Nat.mul_le_mul_left _ hr,
    Nat.add_le_add (Nat.mul_le_mul_left _ hy) (Nat.mul_le_mul_left _ hr),
    Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hz) (Nat.mul_le_mul_left _ hy))
      (Nat.mul_le_mul_left _ hr)⟩

private theorem flagMixed_scale_last (left right cut : FlagDegree) (a : ℕ) :
    flagMixed left right (a • cut) = flagMixed left right cut * a := by
  simp only [flagMixed, nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

private theorem flagMixed_left_increments (left right cut : FlagDegree) :
    flagMixed left right cut =
      left.zOnly * flagMixed unitZFlag right cut +
      left.yz * flagMixed unitYZFlag right cut +
      left.all * flagMixed unitAllFlag right cut := by
  simp only [flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
  ring

private theorem terminalPairCut_eq (f : Envelope) :
    terminalPairCut f = shortenedDirection f (pencilBudget * residualPriceScale) := rfl

private theorem fin_three_le_foldl_max (a : Fin 3 → ℕ) (j : Fin 3) :
    a j ≤ ((List.finRange 3).map a).foldl max 0 := by
  change a j ≤ max (max (max 0 (a 0)) (a 1)) (a 2)
  fin_cases j
  · exact ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem helper_axis_le (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile)
    (j i : Fin 3) :
    flagMixed (unit i) ((cfg j).helper (f.pad 2)).flag
      (shortenedDirection f (pencilBudget * residualPriceScale)) ≤
        jetChargeAxisWithCorrections cuts f cfg i := by
  let a (j : Fin 3) := flagMixed (unit i) ((cfg j).helper (f.pad 2)).flag
    (shortenedDirection f (pencilBudget * residualPriceScale))
  have ha : a j ≤ ((List.finRange 3).map a).foldl max 0 := fin_three_le_foldl_max a j
  apply ha.trans
  unfold jetChargeAxisWithCorrections
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem terminal_pair_count_scaled_le (n count : ℕ) (f : Envelope)
    (left right : FlagDegree) (support : ResidualSupportParameters)
    (hS : support.s = f.slope) (hY : support.ys = f.middle) (hT : support.total = f.total)
    (hn : n ≤ 262144)
    (hcount : count * (181078 * (181078 - 131071)) ≤
      flagMixed left right (scaledPairFlag support n 131071 181078 81066)) :
    count * terminalScale ≤ flagMixed left right
      (shortenedDirection f (pencilBudget * residualPriceScale)) := by
  rw [← terminalPairCut_eq]
  calc
    count * terminalScale = (count * (181078 * (181078 - 131071))) * 30030 := by
      rw [Nat.mul_assoc]
      rfl
    _ ≤ flagMixed left right (scaledPairFlag support n 131071 181078 81066) * 30030 :=
      Nat.mul_le_mul_right _ hcount
    _ = flagMixed left right (30030 • scaledPairFlag support n 131071 181078 81066) :=
      (flagMixed_scale_last _ _ _ _).symm
    _ ≤ flagMixed left right (terminalPairCut f) :=
      mixed_mono_third left right (terminalPairCut_ge f support hS hY hT hn)

theorem helper_count_mul_le_jetFlagCharge (cuts : TailCorrections) (n count : ℕ) (f : Envelope)
    (cfg : Fin 3 → JetProfile) (j : Fin 3) (left : FlagDegree)
    (support : ResidualSupportParameters)
    (hS : support.s = f.slope) (hY : support.ys = f.middle) (hT : support.total = f.total)
    (hn : n ≤ 262144)
    (hcount : count * (181078 * (181078 - 131071)) ≤
      flagMixed left (helperEnvelope (cfg j) (f.paddedSupport 2)).flag
        (scaledPairFlag support n 131071 181078 81066)) :
    count * terminalScale ≤ jetFlagCharge cuts f cfg left := by
  let right := (helperEnvelope (cfg j) (f.paddedSupport 2)).flag
  have hright : right = ((cfg j).helper (f.pad 2)).flag := rfl
  have hpriced := terminal_pair_count_scaled_le n count f left right support hS hY hT hn hcount
  rw [hright] at hpriced
  apply hpriced.trans
  rw [flagMixed_left_increments, jetFlagCharge_eq]
  apply Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ ?_) (Nat.mul_le_mul_left _ ?_))
    (Nat.mul_le_mul_left _ ?_)
  · exact helper_axis_le cuts f cfg j 0
  · exact helper_axis_le cuts f cfg j 1
  · exact helper_axis_le cuts f cfg j 2

def jetLeadingNumerator (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree) : ℕ :=
  ∑ j : Fin 3, flagMixed left (cfg j).leading.flag
    (shortenedDirection f (pencilBudget * residualPriceScale))

private theorem fin_three_sum_eq_list (a : Fin 3 → ℕ) :
    (∑ j : Fin 3, a j) = ((List.finRange 3).map a).sum := by
  rw [Fin.sum_univ_three]
  change a 0 + a 1 + a 2 = a 0 + (a 1 + (a 2 + 0))
  rw [Nat.add_zero, Nat.add_assoc]

theorem jetLeadingNumerator_eq_list (f : Envelope) (cfg : Fin 3 → JetProfile)
    (left : FlagDegree) :
    jetLeadingNumerator f cfg left = ((List.finRange 3).map
      (fun j => flagMixed left (cfg j).leading.flag
        (shortenedDirection f (pencilBudget * residualPriceScale)))).sum :=
  fin_three_sum_eq_list _

theorem leading_counts_mul_le_jetLeadingNumerator (n : ℕ) (count : Fin 3 → ℕ)
    (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree)
    (support : ResidualSupportParameters)
    (hS : support.s = f.slope) (hY : support.ys = f.middle) (hT : support.total = f.total)
    (hn : n ≤ 262144)
    (hcount : ∀ j, count j * (181078 * (181078 - 131071)) ≤
      flagMixed left (cfg j).leading.flag (scaledPairFlag support n 131071 181078 81066)) :
    (∑ j : Fin 3, count j) * terminalScale ≤ jetLeadingNumerator f cfg left := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ =>
    terminal_pair_count_scaled_le n (count j) f left (cfg j).leading.flag support
      hS hY hT hn (hcount j)

end ProximityPrize.SubmissionLower.Koala6831Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
