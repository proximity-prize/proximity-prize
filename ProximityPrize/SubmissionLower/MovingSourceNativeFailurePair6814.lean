import ProximityPrize.SubmissionLower.MovingSourceUniformPairBudget6814
import ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814
import ProximityPrize.SubmissionLower.MovingSourceJointPairBudget6814

/-! At the tight (12,57,3561) endpoint, native failure itself lowers
the owner order to ten. Keep that fact when pricing its avoidance
cofactor; the old unconditional pair cap discarded it. -/
namespace ProximityPrize.SubmissionLower.MovingSourceNativeFailurePair6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open RCN095 WholeSpacePowerCover6814 MovingSourceCoupledClearing6814
open MovingSourcePairEnvelope6814 MovingSourceNativeEnvelope6814

theorem native_failure_order_le_ten (m s b u t : ℕ)
    (hm : 3≤m) (hms : m≤s) (hsb : 2*s≤b) (hbu : b≤u) (hut : u≤t)
    (hb : b≤31) (hu : u≤98) (ht : t≤995)
    (hfail : 3*269880000000000000*m≤native m s b u t) : s≤10 := by
  have h := native_linear m s b u t hms hsb hbu hut
  omega

theorem bounded_order_pair_prices {K : Type} [Field K]
    (J Q : WholeSpaceCube6814.Poly (K:=K))
    (hb : slope J≤31) (hu : middle J≤98) (ht : total J≤995) (hs : order J≤10)
    (hqb : slope Q≤31) (hqu : middle Q≤98) (hqt : total Q≤1700) (hqs : order Q≤14) :
    flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤83328 ∧
      flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤285576 := by
  have hj := ordinaryFlag_cumulative J
  have hq := ordinaryFlag_cumulative Q
  have capJ : CumulativeLe (ordinaryFlag J) ⟨897,77,31⟩ := by
    change (ordinaryFlag J).all≤31 ∧ (ordinaryFlag J).yz+(ordinaryFlag J).all≤108 ∧
      (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all≤1005
    omega
  have capQ : CumulativeLe (ordinaryFlag Q) ⟨1602,81,31⟩ := by
    change (ordinaryFlag Q).all≤31 ∧ (ordinaryFlag Q).yz+(ordinaryFlag Q).all≤112 ∧
      (ordinaryFlag Q).zOnly+(ordinaryFlag Q).yz+(ordinaryFlag Q).all≤1714
    omega
  exact ⟨(mixed_mono_pair _ _ _ _ unitYZFlag capJ capQ).trans_eq (by decide +kernel),
    (mixed_mono_pair _ _ _ _ unitAllFlag capJ capQ).trans_eq (by decide +kernel)⟩

theorem checked_cofactor_price_fits :
    63*126275387074424400+3*coefficientZ3*4491+
      7*(coefficientU3*83328+coefficientA3*285576)+63*23104862107476<
      63*270000000000000000 := by decide +kernel

theorem checked_joint_price_fits :
    coefficientU3≤5*coefficientA3 ∧
    21*126275387074424400+coefficientZ3*4491+
      7*(coefficientU3*26233+coefficientA3*98890)+21*23104862107476<
      21*270000000000000000 := by decide +kernel

#print axioms native_failure_order_le_ten
#print axioms bounded_order_pair_prices
#print axioms checked_cofactor_price_fits
#print axioms checked_joint_price_fits
end
end ProximityPrize.SubmissionLower.MovingSourceNativeFailurePair6814
