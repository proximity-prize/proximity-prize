import ProximityPrize.SubmissionLower.BCHKSFrobeniusDeltaOneCofactor6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusOffsetProductDegreeAudit6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 1000000
def hOneGenericRank6401 : Nat := keyFirstLaneRows6401 + 1
def hOneCofactorDegreeCap6401 : Nat :=
  genericRankMinorDegreeCap6401 hOneGenericRank6401
def naiveFiveOffsetDegreeCap6401 : Nat :=
  5 * hOneCofactorDegreeCap6401
def firstClearedOffsetDegreeCap6401 : Nat :=
  (q6401 + 1) * hOneCofactorDegreeCap6401
noncomputable def challengeFrobenius
    {F : Type*} [Field F] (sigma : F →+* F) (q : Nat)
    (P : Polynomial F) : Polynomial F :=
  (P.map sigma).comp (Polynomial.X ^ q)
theorem challengeFrobenius_eval
    {F : Type*} [Field F] (sigma : F →+* F) (q : Nat)
    (P : Polynomial F) (z : F) (hz : sigma z = z ^ q) :
    Polynomial.eval z (challengeFrobenius sigma q P) =
      sigma (Polynomial.eval z P) := by
  rw [challengeFrobenius, Polynomial.eval_comp]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [← hz]
  exact Polynomial.eval_map_apply sigma z
theorem challengeFrobenius_natDegree
    {F : Type*} [Field F] (sigma : F →+* F) (q : Nat)
    (P : Polynomial F) :
    (challengeFrobenius sigma q P).natDegree = P.natDegree * q := by
  rw [challengeFrobenius, Polynomial.natDegree_comp,
    Polynomial.natDegree_map_eq_of_injective sigma.injective]
  simp
theorem firstClearedOffset_natDegree_le
    {F : Type*} [Field F] (sigma : F →+* F) (q D : Nat)
    (NA DA NB DB : Polynomial F)
    (hNA : NA.natDegree ≤ D) (hDA : DA.natDegree ≤ D)
    (hNB : NB.natDegree ≤ D) (hDB : DB.natDegree ≤ D) :
    (NB * challengeFrobenius sigma q DA -
        challengeFrobenius sigma q NA * DB).natDegree ≤ (q + 1) * D := by
  have hFDA : (challengeFrobenius sigma q DA).natDegree ≤ D * q := by
    rw [challengeFrobenius_natDegree]
    exact Nat.mul_le_mul_right q hDA
  have hFNA : (challengeFrobenius sigma q NA).natDegree ≤ D * q := by
    rw [challengeFrobenius_natDegree]
    exact Nat.mul_le_mul_right q hNA
  have hleft : (NB * challengeFrobenius sigma q DA).natDegree ≤
      D + D * q :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hNB hFDA)
  have hright : (challengeFrobenius sigma q NA * DB).natDegree ≤
      D * q + D :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hFNA hDB)
  have hcap : D + D * q = (q + 1) * D := by ring
  have hcap' : D * q + D = (q + 1) * D := by ring
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (hleft.trans_eq hcap) (hright.trans_eq hcap'))
theorem hOne_offset_degree_ledger_exact6401 :
    hOneGenericRank6401 = 54283 ∧
      hOneCofactorDegreeCap6401 = 2130760715 ∧
      naiveFiveOffsetDegreeCap6401 = 10653803575 ∧
      naiveFiveOffsetDegreeCap6401 < weakCurveSeedInput6401 ∧
      firstClearedOffsetDegreeCap6401 = 4540025564764940310 ∧
      weakCurveSeedInput6401 < firstClearedOffsetDegreeCap6401 := by
  native_decide
theorem firstFrobeniusDegree_exceeds_pool6401 :
    weakCurveSeedInput6401 <
      q6401 * hOneCofactorDegreeCap6401 := by
  native_decide
end BCHKSFrobeniusOffsetProductDegreeAudit6401
end ProximityPrize.SubmissionLower
