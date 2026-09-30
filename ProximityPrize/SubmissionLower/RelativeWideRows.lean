import ProximityPrize.SubmissionLower.RelativeAffineMargins6814
import ProximityPrize.SubmissionLower.RelativeConvexCount
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open RCN100 ClosedRank RelativeBounded6814
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem countSlopeAt_eq (D w L s : ℕ) :
    countSlopeAt D w L s = coefficientCount (D+1) w L s-coefficientCount D w L s := by
  rw [coefficientCount_eq_hinges, coefficientCount_eq_hinges, countSlopeAt]
  rw [← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_tsub_distrib]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Nat.mul_sub]
    · intro j _
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.le_succ D) _)
  · intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.le_succ D) _)

def tanMarginA (Dh k E s R m mu : ℕ) : ℤ :=
  12*(countSlope Dh s+k*(countSlope (Dh+1) s-countSlope Dh s)-countSlope E (s-R))-
    262144*(rankSlope m s-rankSlope (m-mu) (s-R))
def tanMarginB (E s R m mu : ℕ) : ℤ :=
  12*countSlope E (s-R)-262144*rankSlope (m-mu) (s-R)
def tanMarginC (Dh k E s R m mu : ℕ) : ℤ :=
  12*(countIntercept Dh s+k*(countIntercept (Dh+1) s-countIntercept Dh s)-
      countIntercept E (s-R))-
    262144*(rankIntercept m s-rankIntercept (m-mu) (s-R))

theorem tan_margin_identity (Dh k E L s T R m mu : ℕ)
    (hs : s<131071) (hR : R≤s) (hT : T≤L)
    (hsq : s≤Dh/131071) (hsq1 : s≤(Dh+1)/131071) (hsq' : s-R≤E/131071)
    (hL : (Dh+1)/131071+1≤L) (hL' : E/131071+1≤L-T)
    (hm : m+s≤L+1) (hm' : (m-mu)+(s-R)≤L-T+1) :
    tanMarginA Dh k E s R m mu*L+tanMarginB E s R m mu*T+tanMarginC Dh k E s R m mu =
      12*((coefficientCount Dh 131071 L s : ℤ)+
          k*((coefficientCount (Dh+1) 131071 L s : ℤ)-coefficientCount Dh 131071 L s)-
          coefficientCount E 131071 (L-T) (s-R))-
        262144*(12*(RCN119.localRankBound m L s : ℤ)-
          12*RCN119.localRankBound (m-mu) (L-T) (s-R)) := by
  have hL0 : Dh/131071+1≤L := le_trans (Nat.add_le_add_right (Nat.div_le_div_right (Nat.le_succ Dh)) 1) hL
  rw [coefficient_formula Dh L s hs hsq hL0, coefficient_formula (Dh+1) L s hs hsq1 hL,
    coefficient_formula E (L-T) (s-R) (by omega) hsq' hL',
    rank_formula m L s hm, rank_formula (m-mu) (L-T) (s-R) hm', Nat.cast_sub hT]
  unfold tanMarginA tanMarginB tanMarginC
  ring

theorem tan_row_test_of_margin (Dh k E L s T R m mu : ℕ)
    (hs : s<131071) (hR : R≤s) (hT : T≤L)
    (hsq : s≤Dh/131071) (hsq1 : s≤(Dh+1)/131071) (hsq' : s-R≤E/131071)
    (hL : (Dh+1)/131071+1≤L) (hL' : E/131071+1≤L-T)
    (hm : m+s≤L+1) (hm' : (m-mu)+(s-R)≤L-T+1)
    (hmargin : 0<tanMarginA Dh k E s R m mu*L+tanMarginB E s R m mu*T+tanMarginC Dh k E s R m mu)
    (hr : RCN119.localRankBound (m-mu) (L-T) (s-R) ≤ RCN119.localRankBound m L s) :
    coefficientCount E 131071 (L-T) (s-R)+
      262144*(RCN119.localRankBound m L s-RCN119.localRankBound (m-mu) (L-T) (s-R)) <
      coefficientCount Dh 131071 L s+countSlopeAt Dh 131071 L s*k := by
  have hh := tan_margin_identity Dh k E L s T R m mu hs hR hT hsq hsq1 hsq' hL hL' hm hm'
  have hmono : coefficientCount Dh 131071 L s ≤ coefficientCount (Dh+1) 131071 L s :=
    coefficientCount_mono_cutoff 131071 L s (Nat.le_succ Dh)
  rw [countSlopeAt_eq]
  have hslope : ((coefficientCount (Dh+1) 131071 L s-coefficientCount Dh 131071 L s : ℕ) : ℤ) =
      (coefficientCount (Dh+1) 131071 L s : ℤ)-coefficientCount Dh 131071 L s := Nat.cast_sub hmono

  have hi : (coefficientCount E 131071 (L-T) (s-R) : ℤ)+262144*RCN119.localRankBound m L s <
      (coefficientCount Dh 131071 L s : ℤ)+
        ((coefficientCount (Dh+1) 131071 L s : ℤ)-coefficientCount Dh 131071 L s)*k+
        262144*RCN119.localRankBound (m-mu) (L-T) (s-R) := by
    nlinarith only [hh, hmargin]
  have hle : 262144*RCN119.localRankBound (m-mu) (L-T) (s-R) ≤ 262144*RCN119.localRankBound m L s :=
    Nat.mul_le_mul_left _ hr
  have hfin : ((coefficientCount E 131071 (L-T) (s-R)+
      262144*(RCN119.localRankBound m L s-RCN119.localRankBound (m-mu) (L-T) (s-R)) : ℕ) : ℤ) <
      ((coefficientCount Dh 131071 L s+
        (coefficientCount (Dh+1) 131071 L s-coefficientCount Dh 131071 L s)*k : ℕ) : ℤ) := by
    rw [Nat.mul_sub]
    push_cast
    rw [hslope, Nat.cast_sub hle]
    push_cast
    linarith
  exact Nat.cast_lt.mp hfin

end ProximityPrize.SubmissionLower.RelativeCertificate6814
