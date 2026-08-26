import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveLaneFactorDescent6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveOwnerMassAmplification6401
open scoped BigOperators
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSExtremePrimitiveLaneResultantFork6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
theorem sum_powersetCard_sum_weights6401
    {Owner : Type*} [DecidableEq Owner]
    (U : Finset Owner) (weight : Owner → Nat) (k : Nat)
    (hk : 0 < k) :
    (∑ T ∈ U.powersetCard k, ∑ z ∈ T, weight z) =
      Nat.choose (U.card - 1) (k - 1) * ∑ z ∈ U, weight z := by
  classical
  have hinner (T : Finset Owner) (hT : T ∈ U.powersetCard k) :
      (∑ z ∈ T, weight z) =
        ∑ z ∈ U, if z ∈ T then weight z else 0 := by
    have hsub : T ⊆ U := (Finset.mem_powersetCard.mp hT).1
    symm
    calc
      (∑ z ∈ U, if z ∈ T then weight z else 0) =
          ∑ z ∈ U.filter (fun z => z ∈ T), weight z := by
        rw [Finset.sum_filter]
      _ = ∑ z ∈ T, weight z := by
        congr 1
        ext z
        simp only [Finset.mem_filter]
        constructor
        · exact fun hz => hz.2
        · exact fun hz => ⟨hsub hz, hz⟩
  have hcount (z : Owner) (hz : z ∈ U) :
      ((U.powersetCard k).filter fun T => z ∈ T).card =
        Nat.choose (U.card - 1) (k - 1) := by
    have hraw := Finset.card_filter_powersetCard_subset
      ({z} : Finset Owner) U k (by simpa using hz) (by simp; omega)
    simpa using hraw
  calc
    (∑ T ∈ U.powersetCard k, ∑ z ∈ T, weight z) =
        ∑ T ∈ U.powersetCard k,
          ∑ z ∈ U, if z ∈ T then weight z else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      exact hinner T hT
    _ = ∑ z ∈ U, ∑ T ∈ U.powersetCard k,
          if z ∈ T then weight z else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ U,
        Nat.choose (U.card - 1) (k - 1) * weight z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [← hcount z hz]
      simp
    _ = Nat.choose (U.card - 1) (k - 1) *
        ∑ z ∈ U, weight z := by
      rw [Finset.mul_sum]
theorem card_mul_minSubsetWeight_le6401
    {Owner : Type*} [DecidableEq Owner]
    (U : Finset Owner) (weight : Owner → Nat) (k L : Nat)
    (hkPos : 0 < k) (hkU : k ≤ U.card)
    (hlower : ∀ T ∈ U.powersetCard k,
      L ≤ ∑ z ∈ T, weight z) :
    U.card * L ≤ k * ∑ z ∈ U, weight z := by
  classical
  let C := Nat.choose U.card k
  let D := Nat.choose (U.card - 1) (k - 1)
  have hfamilies :
      C * L ≤ ∑ T ∈ U.powersetCard k, ∑ z ∈ T, weight z := by
    calc
      C * L = ∑ _T ∈ U.powersetCard k, L := by
        simp [C]
      _ ≤ ∑ T ∈ U.powersetCard k, ∑ z ∈ T, weight z := by
        exact Finset.sum_le_sum hlower
  have hmass : C * L ≤ D * ∑ z ∈ U, weight z := by
    rw [← sum_powersetCard_sum_weights6401 U weight k hkPos]
    exact hfamilies
  have hnPos : 0 < U.card := hkPos.trans_le hkU
  have hchooseIdentity : U.card * D = C * k := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hnPos.ne'
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hkPos.ne'
    rw [hn, hr]
    simpa [C, D, hn, hr] using Nat.add_one_mul_choose_eq n r
  have hscaled := Nat.mul_le_mul_left U.card hmass
  have hcancel : C * (U.card * L) ≤
      C * (k * ∑ z ∈ U, weight z) := by
    calc
      C * (U.card * L) = U.card * (C * L) := by ring
      _ ≤ U.card * (D * ∑ z ∈ U, weight z) := hscaled
      _ = (U.card * D) * ∑ z ∈ U, weight z := by ring
      _ = (C * k) * ∑ z ∈ U, weight z := by rw [hchooseIdentity]
      _ = C * (k * ∑ z ∈ U, weight z) := by ring
  exact Nat.le_of_mul_le_mul_left hcancel (Nat.choose_pos hkU)
theorem laneResultantMassAmplification_exact6401 :
    primitiveLaneFactorDescentGoodFloor6401 * 108566 >
      weakCurveOutput6401 * primitiveLaneResultantChallengeCap6401 := by
  native_decide
theorem no_largeOwnerFamily_of_subsetMass_and_resultantCap6401
    {Owner : Type*} [DecidableEq Owner]
    (U : Finset Owner) (weight : Owner → Nat)
    (hU : primitiveLaneFactorDescentGoodFloor6401 ≤ U.card)
    (hlower : ∀ T ∈ U.powersetCard weakCurveOutput6401,
      108566 ≤ ∑ z ∈ T, weight z)
    (hmass : ∑ z ∈ U, weight z ≤
      primitiveLaneResultantChallengeCap6401) : False := by
  have hkPos : 0 < weakCurveOutput6401 := by native_decide
  have hkU : weakCurveOutput6401 ≤ U.card := by
    exact (by native_decide : weakCurveOutput6401 ≤
      primitiveLaneFactorDescentGoodFloor6401).trans hU
  have hamp := card_mul_minSubsetWeight_le6401
    U weight weakCurveOutput6401 108566 hkPos hkU hlower
  have hleft := Nat.mul_le_mul_right 108566 hU
  have hright := Nat.mul_le_mul_left weakCurveOutput6401 hmass
  have hfalse := hleft.trans (hamp.trans hright)
  rw [primitiveLaneFactorDescentLedger_exact6401.2,
    primitiveLaneResultantChallengeCap_exact6401] at hfalse
  have houtput : weakCurveOutput6401 = 1183 := by native_decide
  rw [houtput] at hfalse
  norm_num at hfalse
end BCHKSExtremePrimitiveOwnerMassAmplification6401
end ProximityPrize.SubmissionLower
