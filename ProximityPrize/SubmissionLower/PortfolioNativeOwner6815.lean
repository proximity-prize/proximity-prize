import ProximityPrize.SubmissionLower.PortfolioCost6815
import ProximityPrize.SubmissionLower.PortfolioOwners6815
namespace ProximityPrize.SubmissionLower.PortfolioNativeOwner6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open PortfolioCost6815

def ownerDegrees (m s b u hi : ℕ) : Degrees := ⟨b,max b u,max b hi,m-1,s⟩

variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

theorem packet_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (m s b u hi cap : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hFT : max b hi<wt residualTotalWeights P.F) (hk : m-1<2130706433)
    (hg : Gates t y r (b-2*s) (max b u-s) (max b hi-s))
    (hfit : nativeScalar (ownerDegrees m s b u hi) t y r/(3*(ownerDegrees m s b u hi).d)+
      leading (ownerDegrees m s b u hi) t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hn := source_nested J
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤max b u ∧
      e 1+e 2+e 3+e 4≤max b hi := by
    intro e he
    have hb' := le_weightedTotalDegree slopeWeights he
    have hu' := le_weightedTotalDegree middleWeights he
    have ht' := (le_weightedTotalDegree totalWeights he).trans ht
    change Finsupp.weight slopeWeights e≤slope J at hb'
    change Finsupp.weight middleWeights e≤middle J at hu'
    rw [hb] at hb'
    rw [hu] at hu'
    simp [weight_coords,slopeWeights,middleWeights,totalWeights] at hb' hu' ht'
    exact ⟨by omega,hu'.trans (le_max_right _ _),ht'.trans (le_max_right _ _)⟩
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,hSJ,hprofile⟩ := PortfolioOwners6815.exact_owner_source P.F P.rdegree hchar
    J m s b (max b u) (max b hi) hm hms hs (by rw [hs,hb] at hn; omega)
    (le_max_left _ _) (max_le_max le_rfl (by rw [hu] at hn; omega)) hshape hroot
  have hS : Fits S (ownerDegrees m s b u hi) :=
    ⟨hprofile.1,hprofile.2.1,hprofile.2.2.1,hprofile.2.2.2.2.1,hprofile.2.2.2.2.2⟩
  have hc := native_count_of_degrees P S _ hS hFT hk hg
  exact hc.trans (max_le_max le_rfl hfit)

theorem exists_owner_source (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (m s b u hi : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 : ∃ S : MovingFiberThreeSources6811.Source P.F, S.P=J ∧ Fits S (ownerDegrees m s b u hi) := by
  have hn := source_nested J
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤max b u ∧
      e 1+e 2+e 3+e 4≤max b hi := by
    intro e he
    have hb' := le_weightedTotalDegree slopeWeights he
    have hu' := le_weightedTotalDegree middleWeights he
    have ht' := (le_weightedTotalDegree totalWeights he).trans ht
    change Finsupp.weight slopeWeights e≤slope J at hb'
    change Finsupp.weight middleWeights e≤middle J at hu'
    rw [hb] at hb'
    rw [hu] at hu'
    simp [weight_coords,slopeWeights,middleWeights,totalWeights] at hb' hu' ht'
    exact ⟨by omega,hu'.trans (le_max_right _ _),ht'.trans (le_max_right _ _)⟩
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,hSJ,hprofile⟩ := PortfolioOwners6815.exact_owner_source P.F P.rdegree hchar
    J m s b (max b u) (max b hi) hm hms hs (by rw [hs,hb] at hn; omega)
    (le_max_left _ _) (max_le_max le_rfl (by rw [hu] at hn; omega)) hshape hroot
  have hS : Fits S (ownerDegrees m s b u hi) :=
    ⟨hprofile.1,hprofile.2.1,hprofile.2.2.1,hprofile.2.2.2.2.1,hprofile.2.2.2.2.2⟩
  exact ⟨S,hSJ,hS⟩

end
end ProximityPrize.SubmissionLower.PortfolioNativeOwner6815
