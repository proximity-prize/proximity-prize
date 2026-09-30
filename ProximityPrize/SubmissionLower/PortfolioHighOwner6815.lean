import ProximityPrize.SubmissionLower.PortfolioNativeOwner6815
namespace ProximityPrize.SubmissionLower.PortfolioHighOwner6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open PortfolioCost6815
variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

def degrees (B U L : ℕ) : Degrees := ⟨B,U,L,6,7⟩

theorem packet_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (m B U L s cap : ℕ)
    (hm : 7≤m) (hord : m≤order J) (hs : order J≤s)
    (hb : slope J≤B) (hu : middle J≤U) (ht : total J≤L)
    (hB : 14≤B) (hBU : B≤U) (hUL : U≤L) (hFT : L<wt residualTotalWeights P.F)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hg : Gates t y r (B-14) (U-7) (L-7))
    (hfit : nativeScalar (degrees B U L) t y r/21+leading (degrees B U L) t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤L := by
    intro e he
    have h1 := (le_weightedTotalDegree slopeWeights he).trans hb
    have h2 := (le_weightedTotalDegree middleWeights he).trans hu
    have h3 := (le_weightedTotalDegree totalWeights he).trans ht
    constructor
    · simpa [weight_coords,slopeWeights,Nat.mul_comm] using h1
    constructor
    · simpa [weight_coords,middleWeights] using h2
    · simpa [weight_coords,totalWeights] using h3
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨S,hSJ,hprofile⟩ := PortfolioOwners6815.root_source_profile P.F P.rdegree hchar J
    m s B U L 6 7 hm (by decide) (by change 7≤order J; omega) hs hB hBU hUL hshape hroot
  have hS : Fits S (degrees B U L) :=
    ⟨hprofile.1,hprofile.2.1,hprofile.2.2.1,hprofile.2.2.2.2.1,hprofile.2.2.2.2.2⟩
  have hc := native_count_of_degrees P S _ hS hFT (by change 6<2130706433; decide) hg
  exact hc.trans (max_le_max le_rfl hfit)

end
end ProximityPrize.SubmissionLower.PortfolioHighOwner6815
