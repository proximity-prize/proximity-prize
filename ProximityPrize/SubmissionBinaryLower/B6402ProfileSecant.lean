import ProximityPrize.SubmissionBinaryLower.B6401FarkasVerifier

/-! The secant bound with the actual missed-site spatial weight W. Adapted
from the quotient concavity argument in the promoted 6401 proof. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ProfileSecant
open B6401Params B6401ContactKerD
open scoped BigOperators
def vquotLbQ (W d m s : ℕ) (c : ℚ) : ℚ :=
  ((varsKerDExact wY W s : ℚ) - varsKerDUpperQ wY ((W : ℚ) - c * (wY : ℚ)) (s - d)) /
    ((N : ℚ) * (m : ℚ) * (m : ℚ))

theorem vquotLbQ_ge_secant (W d m s : ℕ) (hm : 0 < m) {cLo cHi c : ℚ}
    (hlo : cLo ≤ c) (hhi : c ≤ cHi) (hlt : cLo < cHi) :
    let t := (c - cLo) / (cHi - cLo)
    (1 - t) * vquotLbQ W d m s cLo + t * vquotLbQ W d m s cHi ≤ vquotLbQ W d m s c := by
  intro t
  have hden : (0 : ℚ) < cHi - cLo := sub_pos.mpr hlt
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hden.le
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (sub_le_sub_right hhi cLo)
  have hW_eq : ((W : ℕ) : ℚ) - c * (wY : ℚ) =
      (1 - t) * (((W : ℕ) : ℚ) - cLo * (wY : ℚ)) +
      t * (((W : ℕ) : ℚ) - cHi * (wY : ℚ)) := by
    have hc : c = (1 - t) * cLo + t * cHi := by
      dsimp [t]; field_simp [hden.ne']; ring
    conv_lhs => rw [hc]
    ring
  have hconv := varsKerDUpperQ_convex wY (s - d) (by norm_num [wY, D])
    (((W : ℕ) : ℚ) - cLo * (wY : ℚ))
    (((W : ℕ) : ℚ) - cHi * (wY : ℚ)) t ht0 ht1
  rw [← hW_eq] at hconv
  have hNm2 : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
    have hN : (0 : ℚ) < N := by norm_num [N]
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  unfold vquotLbQ
  rw [show (1 - t) * (((varsKerDExact wY (W) s : ℚ) -
        varsKerDUpperQ wY (((W : ℕ) : ℚ) - cLo * (wY : ℚ)) (s - d)) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ))) +
      t * (((varsKerDExact wY (W) s : ℚ) -
        varsKerDUpperQ wY (((W : ℕ) : ℚ) - cHi * (wY : ℚ)) (s - d)) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ))) =
      ((varsKerDExact wY (W) s : ℚ) -
        ((1 - t) * varsKerDUpperQ wY (((W : ℕ) : ℚ) - cLo * (wY : ℚ)) (s - d) +
         t * varsKerDUpperQ wY (((W : ℕ) : ℚ) - cHi * (wY : ℚ)) (s - d))) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ)) by ring]
  exact div_le_div_of_nonneg_right (by linarith) hNm2.le

theorem vquotLbQ_le_exact (W d m s W_F : ℕ) (hm : 0 < m) (hW : W_F ≤ W)
    {c : ℚ} (hc : c * (wY : ℚ) ≤ (W_F : ℚ)) :
    vquotLbQ W d m s c ≤
      ((varsKerDExact wY W s : ℚ) - varsKerDExact wY (W-W_F) (s-d)) /
      ((N : ℚ) * (m : ℚ) * (m : ℚ)) := by
  have hNm2 : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
    have hN : (0 : ℚ) < N := by norm_num [N]
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hwYpos : 0 < wY := by norm_num [wY, D]
  have hsub_le : ((W - W_F : ℕ) : ℚ) ≤ ((W : ℕ) : ℚ) - c * (wY : ℚ) := by
    rw [Nat.cast_sub hW]; linarith
  have hup : (varsKerDExact wY (W - W_F) (s - d) : ℚ) ≤
      varsKerDUpperQ wY (((W : ℕ) : ℚ) - c * (wY : ℚ)) (s - d) :=
    varsKerDExact_le_upperQ wY (W - W_F) (s - d)
      (((W : ℕ) : ℚ) - c * (wY : ℚ)) hwYpos hsub_le
  unfold vquotLbQ
  exact div_le_div_of_nonneg_right (sub_le_sub_left hup _) hNm2.le

#print axioms vquotLbQ_ge_secant
#print axioms vquotLbQ_le_exact
end ProximityPrize.SubmissionBinaryLower.B6402ProfileSecant
