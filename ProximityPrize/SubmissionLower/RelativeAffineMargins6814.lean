import ProximityPrize.SubmissionLower.RelativeGeneralRank6814
import ProximityPrize.SubmissionLower.RelativeCoefficientAffine6814
import ProximityPrize.SubmissionLower.RelativeRoundedAffine6814

/-! Exact signed affine margins for the original coefficient and rank
counts. Rearranging the row test avoids assuming that a Nat subtraction
can be treated as signed subtraction. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open RCN100 ClosedRank
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def rankAffine (m s : ℕ) (L : ℤ) : ℤ :=
  sourceTwelve m L s-removedPartialTwelve m L s (min s (m/2) : ℕ)
def rankSlope (m s : ℕ) : ℤ := rankAffine m s 1-rankAffine m s 0
def rankIntercept (m s : ℕ) : ℤ := rankAffine m s 0

theorem rankAffine_eq (m s : ℕ) (L : ℤ) :
    rankAffine m s L=rankSlope m s*L+rankIntercept m s := by
  unfold rankSlope rankIntercept rankAffine sourceTwelve removedPartialTwelve
  ring

theorem rank_formula (m L s : ℕ) (hshape : m+s≤L+1) :
    12*(RCN119.localRankBound m L s : ℤ)=rankSlope m s*L+rankIntercept m s := by
  rw [localRankBound_twelve m L s hshape]
  exact rankAffine_eq m s L

def countSlope (D s : ℕ) : ℤ := coefficientSlope (D/131071) (D%131071) 131071 s
def countIntercept (D s : ℕ) : ℤ := coefficientIntercept (D/131071) (D%131071) 131071 s

theorem coefficient_formula (D L s : ℕ) (hs : s<131071) (hsq : s≤D/131071) (hL : D/131071+1≤L) :
    (coefficientCount D 131071 L s : ℤ)=countSlope D s*L+countIntercept D s := by
  have he : (D/131071)*131071+D%131071=D := by have := Nat.div_add_mod D 131071; omega
  simpa only [he,countSlope,countIntercept] using coefficientCount_affine (D/131071) (D%131071)
    131071 L s (by decide) (Nat.mod_lt _ (by decide)) hs hsq hL

def marginA (D nu s R m mu : ℕ) : ℤ :=
  12*(countSlope D s-countSlope (D-nu) (s-R))-
    262144*(rankSlope m s-rankSlope (m-mu) (s-R))
def marginB (D nu s R m mu : ℕ) : ℤ :=
  12*countSlope (D-nu) (s-R)-262144*rankSlope (m-mu) (s-R)
def marginC (D nu s R m mu : ℕ) : ℤ :=
  12*(countIntercept D s-countIntercept (D-nu) (s-R))-
    262144*(rankIntercept m s-rankIntercept (m-mu) (s-R))

theorem margin_identity (D nu L s T R m mu : ℕ)
    (hs : s<131071) (hR : R≤s) (hT : T≤L)
    (hsq : s≤D/131071) (hsq' : s-R≤(D-nu)/131071)
    (hL : D/131071+1≤L) (hL' : (D-nu)/131071+1≤L-T)
    (hm : m+s≤L+1) (hm' : (m-mu)+(s-R)≤L-T+1) :
    marginA D nu s R m mu*L+marginB D nu s R m mu*T+marginC D nu s R m mu=
      12*((coefficientCount D 131071 L s : ℤ)-coefficientCount (D-nu) 131071 (L-T) (s-R))-
        262144*(12*(RCN119.localRankBound m L s : ℤ)-12*RCN119.localRankBound (m-mu) (L-T) (s-R)) := by
  rw [coefficient_formula D L s hs hsq hL,
    coefficient_formula (D-nu) (L-T) (s-R) (by omega) hsq' hL',
    rank_formula m L s hm,rank_formula (m-mu) (L-T) (s-R) hm',Nat.cast_sub hT]
  unfold marginA marginB marginC
  ring

theorem row_test_of_margin (D nu L s T R m mu : ℕ)
    (hD : 0<D) (hnu : 0<nu) (hs : s<131071) (hR : R≤s) (hT : T≤L)
    (hsq : s≤D/131071) (hsq' : s-R≤(D-nu)/131071)
    (hL : D/131071+1≤L) (hL' : (D-nu)/131071+1≤L-T)
    (hm : m+s≤L+1) (hm' : (m-mu)+(s-R)≤L-T+1)
    (hmargin : 0<marginA D nu s R m mu*L+marginB D nu s R m mu*T+marginC D nu s R m mu) :
    coefficientCount (D-nu) 131071 (L-T) (s-R)+
      262144*(RCN119.localRankBound m L s-RCN119.localRankBound (m-mu) (L-T) (s-R))<
      coefficientCount D 131071 L s := by
  have hh := margin_identity D nu L s T R m mu hs hR hT hsq hsq' hL hL' hm hm'
  have hi : (coefficientCount (D-nu) 131071 (L-T) (s-R) : ℤ)+
      262144*RCN119.localRankBound m L s <
      (coefficientCount D 131071 L s : ℤ)+262144*RCN119.localRankBound (m-mu) (L-T) (s-R) := by
    nlinarith only [hh,hmargin]
  apply row_test_of_rearranged _ _ _ _ 262144 (multiple_count_lt_source _ _ _ _ _ _ _ hD hnu)
  exact_mod_cast hi

#print axioms row_test_of_margin
end ProximityPrize.SubmissionLower.RelativeCertificate6814
