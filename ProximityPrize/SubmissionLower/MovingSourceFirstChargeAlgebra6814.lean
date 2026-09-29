import ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814

/-! Keep finite-sum linearity symbolic, so checking it never expands
the large concrete degree coefficients inside the ring normalizer. -/
namespace ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN095

theorem mixed_linear_first (p q r : FlagDegree) :
    flagMixed p q r=p.zOnly*flagMixed unitZFlag q r+
      p.yz*flagMixed unitYZFlag q r+p.all*flagMixed unitAllFlag q r := by
  unfold flagMixed unitZFlag unitYZFlag unitAllFlag
  ring

theorem sum_mixed_linear {I : Type} [Fintype I]
    (weight : I → ℕ) (q r : I → FlagDegree) (p : FlagDegree) :
    (∑ i, weight i*flagMixed p (q i) (r i))=
      p.zOnly*(∑ i, weight i*flagMixed unitZFlag (q i) (r i))+
      p.yz*(∑ i, weight i*flagMixed unitYZFlag (q i) (r i))+
      p.all*(∑ i, weight i*flagMixed unitAllFlag (q i) (r i)) := by
  have he (i : I) : weight i*flagMixed p (q i) (r i)=
      p.zOnly*(weight i*flagMixed unitZFlag (q i) (r i))+
      p.yz*(weight i*flagMixed unitYZFlag (q i) (r i))+
      p.all*(weight i*flagMixed unitAllFlag (q i) (r i)) := by
    rw [mixed_linear_first p]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]

theorem mixed_sum_linear (p q r s : FlagDegree) :
    flagMixed p q r+flagMixed p q s=
      p.zOnly*(flagMixed unitZFlag q r+flagMixed unitZFlag q s)+
      p.yz*(flagMixed unitYZFlag q r+flagMixed unitYZFlag q s)+
      p.all*(flagMixed unitAllFlag q r+flagMixed unitAllFlag q s) := by
  rw [mixed_linear_first p q r,mixed_linear_first p q s]
  ring

theorem weighted_three_le (z u v a b c d e f g h : ℕ)
    (hz : g*a≤h*d) (hu : g*b≤h*e) (hv : g*c≤h*f) :
    g*(z*a+u*b+v*c)≤h*(z*d+u*e+v*f) := by
  have hh := Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left z hz) (Nat.mul_le_mul_left u hu))
    (Nat.mul_le_mul_left v hv)
  convert hh using 1 <;> ring

end ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814
