import ProximityPrize.SubmissionBinaryLower.B6402DimensionBudget
import ProximityPrize.SubmissionBinaryLower.B6402ProfileCosts
import ProximityPrize.SubmissionBinaryLower.B6402ProfileSecant

/-! Lower bound the graded dimension after removing genuine multiples using
the spatial secant and monotonicity of the cofactor moment. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ProfileBudget
open B6401ContactKerD B6401QuotInterp B6402DimensionBudget B6402ProfileCosts B6401Params
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem vars_mono (w a b s : ℕ) (hw : 0<w) (h : a≤b) : varsKerDExact w a s≤varsKerDExact w b s := by
  rw [←card_kerDIdxFinset _ _ _ hw,←card_kerDIdxFinset _ _ _ hw]
  apply Finset.card_le_card
  rintro ⟨k,r,n,j⟩ ha
  have he := (mem_kerDIdxFinset_iff w a s hw k r n j).mp ha
  exact (mem_kerDIdxFinset_iff w b s hw k r n j).mpr ⟨he.1,he.2.1,he.2.2.trans h⟩

theorem source_budget (w W WF WFhi s q T H : ℕ) (hw : 0<w) (hH : H≤T) (hh : WF≤WFhi)
    (gap : ℚ) (hgap : gap≤(varsKerDExact w W s : ℚ) - varsKerDExact w (W-WF) (s-1)) :
    gap*(T+1)+(H:ℚ)*varsKerDExact w (W-WFhi) (s-1) -
       (q:ℚ)*((gMoment w W s:ℚ)-gMoment w (W-WFhi) (s-1)) ≤
      (sourceSize w W s q T:ℚ) - (sourceSize w (W-WF) (s-1) q (T-H):ℚ) := by
  have leW : W-WFhi≤W-WF := by omega
  have hV : (varsKerDExact w (W-WFhi) (s-1):ℚ)≤varsKerDExact w (W-WF) (s-1) := by
    exact_mod_cast vars_mono w _ _ _ hw leW
  have hM : (gMoment w (W-WFhi) (s-1):ℚ)≤gMoment w (W-WF) (s-1) := by
    exact_mod_cast global_moment_mono w _ _ _ hw leW
  unfold sourceSize
  push_cast [Nat.cast_sub hH]
  have ht : (0:ℚ)≤T+1 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hgap ht,
    mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg H),mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg q)]

def secant (W m s : ℕ) (lo hi c : ℚ) : ℚ :=
  let vl := B6402ProfileSecant.vquotLbQ W 1 m s lo
  let vh := B6402ProfileSecant.vquotLbQ W 1 m s hi
  vl+((vh-vl)/(hi-lo))*(c-lo)

theorem gap_from_endpoints (W WF m s : ℕ) (hm : 0<m) (hF : WF≤W)
    (lo hi c : ℚ) (cl : lo≤c) (ch : c≤hi) (proper : lo<hi) (hc : c*wY≤WF) :
    secant W m s lo hi c *((N:ℚ)*m*m)≤(varsKerDExact wY W s : ℚ)-varsKerDExact wY (W-WF) (s-1) := by
  have h1 := B6402ProfileSecant.vquotLbQ_ge_secant W 1 m s hm cl ch proper
  have h2 := B6402ProfileSecant.vquotLbQ_le_exact W 1 m s WF hm hF hc
  have den : (0:ℚ)<(N:ℚ)*m*m := by
    have hn : (0:ℚ)<N := by decide
    have hmq : (0:ℚ)<m := by exact_mod_cast hm
    exact mul_pos (mul_pos hn hmq) hmq
  apply (le_div_iff₀ den).mp
  apply le_trans _ (h1.trans h2)
  unfold secant; dsimp only
  apply le_of_eq; ring

/-- Check the two endpoint heights of a factor. Strict positivity is preserved
at the actual height because the full price difference is affine. -/
theorem positive_between (a t lo hi : ℚ) (hspan : lo<hi) (l : lo≤t) (r : t≤hi) (b : ℚ)
    (posL : 0<a*lo+b) (posH : 0<a*hi+b) : 0<a*t+b := by
  rcases le_total 0 a with ha|ha
  · exact posL.trans_le (by linarith only [mul_le_mul_of_nonneg_left l ha])
  · exact posH.trans_le (by linarith only [mul_le_mul_of_nonpos_left r ha])

#print axioms source_budget
#print axioms gap_from_endpoints
end ProximityPrize.SubmissionBinaryLower.B6402ProfileBudget
