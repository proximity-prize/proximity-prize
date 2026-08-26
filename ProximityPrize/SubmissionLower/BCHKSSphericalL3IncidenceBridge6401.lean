import ProximityPrize.SubmissionLower.BCHKSList6401
import ProximityPrize.SubmissionLower.BCHKSSphericalL3Bound6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSSphericalL3IncidenceBridge6401
open ProximityPrize.Benchmark
open BCHKSList6401
open BCHKSSphericalL3Bound6401
open scoped NNReal
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
def ExactAgreementFamilyBound6401 : Prop :=
  ∀ (owners : Type) [Fintype owners]
    (A : owners → Finset IRSProfile.Index),
    (∀ z, (A z).card = bchksAgreements6401) →
    (∀ z w, z ≠ w → ((A z) ∩ (A w)).card ≤ 131071) →
    Fintype.card owners ≤ listBound6401
theorem close_finset_card_le_of_exactAgreementFamilyBound6401
    (hbound : ExactAgreementFamilyBound6401)
    (y : SquaredWord6401) (T : Finset SquaredWord6401)
    (hT : ∀ c ∈ T,
      c ∈ Code.closeCodewordsRel SquaredCode6401 y
        (bchksRadius6401 : ℝ)) :
    T.card ≤ listBound6401 := by
  classical
  obtain ⟨F⟩ := exists_exactAgreementFamily6401 y T hT
  have hcard := hbound {c // c ∈ T} F.coords F.card_eq
    F.pair_intersection_le
  simpa using hcard
theorem lambda_le_of_exactAgreementFamilyBound6401
    (hbound : ExactAgreementFamilyBound6401) :
    Code.Lambda SquaredCode6401 (bchksRadius6401 : ℝ) ≤
      (listBound6401 : ℕ∞) := by
  rw [Code.Lambda_le_iff_forall_encard_le]
  intro y
  let S := Code.closeCodewordsRel SquaredCode6401 y
    (bchksRadius6401 : ℝ)
  have hSfin : S.Finite := Set.toFinite _
  rw [← hSfin.cast_ncard_eq, Set.ncard_eq_toFinset_card S hSfin]
  exact_mod_cast close_finset_card_le_of_exactAgreementFamilyBound6401
    hbound y hSfin.toFinset (by
      intro c hc
      exact hSfin.mem_toFinset.mp hc)
theorem exactAgreementFamilyBound6401 : ExactAgreementFamilyBound6401 := by
  intro owners _ A hcard hinter
  simpa [BCHKSSphericalL3Bound6401.SphereCoord,
    BCHKSSphericalL3Bound6401.sphereN, IRSProfile.Index,
    BCHKSList6401.listBound6401] using
      (BCHKSSphericalL3Bound6401.exactAgreementFamily_card_le_17045844
        A hcard hinter)
theorem bchks6401_lambda_le :
    Code.Lambda SquaredCode6401 (bchksRadius6401 : ℝ) ≤
      (listBound6401 : ℕ∞) :=
  lambda_le_of_exactAgreementFamilyBound6401
    exactAgreementFamilyBound6401
end BCHKSSphericalL3IncidenceBridge6401
end ProximityPrize.SubmissionLower
