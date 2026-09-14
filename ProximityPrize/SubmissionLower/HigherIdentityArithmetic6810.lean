import ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic

namespace ProximityPrize.SubmissionLower.HigherIdentityArithmetic6810
open RCN095 RCN146 Lower80788.HybridIdentityC2
open BoundaryTailIdentityArithmetic (newCost newNormal)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem generic_absorption (f : FlagDegree) (a b s : ℕ) (_ha : 0 ≤ a)
    (hb : 1 ≤ b) (hs : 1 ≤ s) :
    131073 * 80851 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a b s 131071 ≤
      50223 * newCost f a b s := by
  obtain ⟨b',rfl⟩ : ∃ b', b = b'+1 := ⟨b-1,by omega⟩
  obtain ⟨s',rfl⟩ : ∃ s', s = s'+1 := ⟨s-1,by omega⟩
  change 131073 * 80851 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a (b'+1) (s'+1)
    Lower80788.HybridIdentityC2.w ≤ _
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  simp [newCost, newNormal, reducedABS, rationalABS, mfibABS, mcutABS,
    flagMixed, unitAllFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring_nf
  omega

end ProximityPrize.SubmissionLower.HigherIdentityArithmetic6810
