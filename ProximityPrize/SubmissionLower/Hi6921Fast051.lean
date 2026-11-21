import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921P21Arithmetic
import ProximityPrize.SubmissionLower.Hi6921P21Split
import ProximityPrize.SubmissionLower.Hi6921P32Split
import ProximityPrize.SubmissionLower.Hi6921P34Cutter
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/






section High_K1_14_3RDefs
set_option autoImplicit true
namespace H21_3R

noncomputable section

open K21 H21 H21_3 Polynomial

export _root_.K1_14_3R (chainCutter)

export _root_.K1_14_3R (compatible)

export _root_.K1_14_3R (OrdinaryGraphs)

def stagePass {h : ℕ} (rows : Banks) (pairs : ∀ i : Fin 4, BufferedPair h rows i)
    (i : Fin 5) (q : Surface) : Prop :=
  if hi : i.val < 4 then
    let j : Fin 4 := ⟨i.val, hi⟩
    BankVanishes rows (cheapShape j) q ∧ BankVanishes rows (layeredShape j) q ∧
      compatible (pairs j).cheap (pairs j).layered q
  else BankVanishes rows fullShape q

end
end H21_3R
end High_K1_14_3RDefs

section High_K1_14_3RBuffered
set_option autoImplicit true
set_option maxSynthPendingDepth 8

namespace H21_3R

noncomputable section

open K21 H21 H21_3 Polynomial
open H21_2_1 (cutoffCount rawVolume movingCeiling)
open private worstBase from ProximityPrize.SubmissionLower.Hi6921P21Arithmetic
open private worstSlope from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private surplusBase from ProximityPrize.SubmissionLower.Hi6921P21Arithmetic
open private surplusSlope from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private volume_eq from ProximityPrize.SubmissionLower.Hi6921P21Arithmetic
open private debit_eq from ProximityPrize.SubmissionLower.Pack_K1_14_2_1Arithmetic
open private bank_nonzero from ProximityPrize.SubmissionLower.Hi6921P21Split
open private avoids_one from ProximityPrize.SubmissionLower.Hi6921P21Split
open private pair_membership from ProximityPrize.SubmissionLower.Hi6921P3Split

private def Certificate (s : Shape) (r mode : ℕ) : Prop :=
  0 < worstBase s + 3555 * worstSlope s r ∧
  0 < worstBase s + 32950 * worstSlope s r ∧
  0 < surplusBase s + 3555 * surplusSlope s r mode ∧
  0 < surplusBase s + 32950 * surplusSlope s r mode

private def stageCheck (i : Fin 4) : Prop :=
  Certificate (cheapShape i) (reserve i) 0 ∧
  Certificate (layeredShape i) (reserve i) 1

private instance (i : Fin 4) : Decidable (stageCheck i) := by
  unfold stageCheck Certificate
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem certificates : ∀ i : Fin 4, stageCheck i := by decide +kernel

private theorem affine_positive {a b h : ℤ} (hlo : 3555 ≤ h) (hhi : h ≤ 32950)
    (ha : 0 < a + 3555 * b) (hb : 0 < a + 32950 * b) : 0 < a + h * b := by
  by_cases hb0 : 0 ≤ b
  · nlinarith only [ha, mul_nonneg (sub_nonneg.mpr hlo) hb0]
  · nlinarith only [hb, mul_nonneg (sub_nonneg.mpr hhi) (neg_nonneg.mpr (le_of_not_ge hb0))]

private theorem test (h r mode : ℕ) (s : Shape) (hlo : 3555 ≤ h) (hhi : h ≤ 32950)
    (hc : Certificate s r mode) :
    s.B * (131071 - h) < cutoffCount h r s ∧
      sourceDebit h s + mode * movingCeiling h s < rawVolume h r s := by
  have hh : h ≤ 131071 := by omega
  have hloI : (3555 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hlo
  have hhiI : (h : ℤ) ≤ 32950 := by exact_mod_cast hhi
  obtain ⟨ha, hb, hc, hd⟩ := hc
  have hw := affine_positive hloI hhiI ha hb
  unfold worstBase worstSlope at hw
  have hpos : (s.B : ℤ) * (131071 - (h : ℤ)) <
      (s.m : ℤ) * 180130 - 2 * (h : ℤ) * r := by nlinarith only [hw]
  have hbuf : 2 * h * r ≤ s.m * 180130 := by
    have hn : 0 ≤ (s.B : ℤ) * (131071 - (h : ℤ)) := by
      exact mul_nonneg (Int.natCast_nonneg _) (by omega)
    have ht : 2 * (h : ℤ) * r ≤ (s.m : ℤ) * 180130 := by linarith only [hpos, hn]
    exact_mod_cast ht
  have hwidth : s.B * (131071 - h) < cutoffCount h r s := by
    unfold cutoffCount
    have ht : ((s.B * (131071 - h) : ℕ) : ℤ) <
        ((s.m * 180130 - 2 * h * r : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hh, Nat.cast_sub hbuf]
      exact hpos
    exact_mod_cast ht
  have hs := affine_positive hloI hhiI hc hd
  have heq := volume_eq h r mode s hh hwidth
  unfold surplusBase surplusSlope at hs
  refine ⟨hwidth, ?_⟩
  have ht : ((sourceDebit h s + mode * movingCeiling h s : ℕ) : ℤ) <
      (rawVolume h r s : ℤ) := by
    rw [debit_eq]
    push_cast
    nlinarith only [hs, heq]
  exact_mod_cast ht

open private fixed_of_no_seed from ProximityPrize.SubmissionLower.Fast051

theorem bufferedPairs (power : H21_2_1.c1) (rankBound : H21_2_1.c2)
    {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : JetSource M F rows) (hl : 3555 ≤ M.overhead)
    (hu : M.overhead ≤ 32950) (i : Fin 4) :
    Nonempty (BufferedPair M.overhead.toNat rows i) := by
  let h := M.overhead.toNat
  have hlo : 3555 ≤ h := by dsimp [h]; omega
  have hhi : h ≤ 32950 := by dsimp [h]; omega
  obtain ⟨hc, hd⟩ := certificates i
  obtain ⟨cw, cv⟩ := test h (reserve i) 0 _ hlo hhi hc
  obtain ⟨lw, lv⟩ := test h (reserve i) 1 _ hlo hhi hd
  simp only [zero_mul, add_zero] at cv
  simp only [one_mul] at lv
  have hcs := pair_membership hl i (s := cheapShape i) (by simp)
  have hls := pair_membership hl i (s := layeredShape i) (by simp)
  have hp : (cheapShape i).U < p := by fin_cases i <;> decide
  obtain ⟨P, hPm, hP⟩ := bank_nonzero src hcs (reserve i) cw cv
  have hLn := bank_nonzero src hls (reserve i) lw (lt_of_le_of_lt (Nat.le_add_right _ _) lv)
  have hseed (j y : ℕ) : ((P.coeff j).coeff y).totalDegree ≤ (cheapShape i).U := by
    by_cases hz : (P.coeff j).coeff y = 0
    · simp [hz]
    · exact (src.shape _ hcs _ P hPm j y hz).2.2
  obtain ⟨Q, hQm, hQ, havoid⟩ := H21_2_1.exists_layered P hP _ hLn
    (fun G hi hdiv hv hm => avoids_one src power rankBound (by dsimp [h] at hlo; omega)
      hls (reserve i) lw lv hi hv hm hP hdiv hp hseed)
  have hcut (s : Shape) : reserveCutoff h s i = cutoffCount h (reserve i) s - 1 := by
    unfold reserveCutoff cutoffCount
    omega
  exact ⟨⟨P, Q, hP, hQ, (hcut _).symm ▸ hPm, (hcut _).symm ▸ hQm,
    src.shape _ hcs _ _ hPm, src.shape _ hls _ _ hQm,
    fun G hi hdiv hdiv' hv => fixed_of_no_seed G (fun hm => havoid G hi hdiv hv hm hdiv')⟩⟩

end
end H21_3R
end High_K1_14_3RBuffered

section High_K1_14_3RCutter
set_option autoImplicit true
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

namespace H21_3R

noncomputable section

open K21 H21 H21_3 Polynomial
open scoped BigOperators

open private seedValues from ProximityPrize.SubmissionLower.Fast051

open private specializeSeeds from ProximityPrize.SubmissionLower.Fast051

open private specialize_monomial from ProximityPrize.SubmissionLower.Fast051

open private specialize_dxSeed from ProximityPrize.SubmissionLower.Fast051

open private specialize_chain from ProximityPrize.SubmissionLower.Fast051

open private specialize_lift from ProximityPrize.SubmissionLower.Fast051

export _root_.K1_14_3R (chainCutter_zero)

end
end H21_3R
end High_K1_14_3RCutter

section High_K1_14_3RFactor
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000

namespace H21_3R

noncomputable section

open K21 H21 H21_3 Polynomial
open scoped BigOperators

open private asSeedPoly from ProximityPrize.SubmissionLower.Fast051

open private asSeedPoly_coeff from ProximityPrize.SubmissionLower.Fast051

open private total_asSeedPoly_le from ProximityPrize.SubmissionLower.Fast051

open private seed_cap_of_dvd from ProximityPrize.SubmissionLower.Fast051

open private liftSeed from ProximityPrize.SubmissionLower.Fast051

open private liftSeed_injective from ProximityPrize.SubmissionLower.Fast051

open private liftSeed_degree from ProximityPrize.SubmissionLower.Fast051

open private lift_coeff from ProximityPrize.SubmissionLower.Fast051

open private clearing_coeff from ProximityPrize.SubmissionLower.Fast051

open private dxSeed from ProximityPrize.SubmissionLower.Fast051

open private dxSeed_degree from ProximityPrize.SubmissionLower.Fast051

open private dx_coeff from ProximityPrize.SubmissionLower.Fast051

open private lift_derivative from ProximityPrize.SubmissionLower.Fast051

open private degree_scalar from ProximityPrize.SubmissionLower.Fast051

export _root_.K1_14_3R (chainCutter_caps_of_dvd)

attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
  Polynomial.isLocalization in
open private exists_clearing from ProximityPrize.SubmissionLower.Fast051

open private derivative_nonzero from ProximityPrize.SubmissionLower.Fast051

export _root_.K1_14_3R (chainCutter_proper)

export _root_.K1_14_3R (ordinary_graph)

end
end H21_3R
end High_K1_14_3RFactor
