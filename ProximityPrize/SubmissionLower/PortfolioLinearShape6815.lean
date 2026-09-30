import ProximityPrize.SubmissionLower.PortfolioLinearPacket6815
namespace ProximityPrize.SubmissionLower.PortfolioLinearShape6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
open MovingSourceReducedTailWeights6814 PortfolioLinearRoute6815 PortfolioLinearPacket6815
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy
variable {K : Type} [Field K]

theorem tail_weights (J : Poly (K:=K)) (B U L : ℕ) (hB : 2≤B) (hBU : B≤U) (hUL : U≤L)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤L)
    (n : ℕ) :
    wt residualSWeights (numerators (linearH J) (linearG J) n)≤(2*B-3)*n ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+(2*U-2)*n ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+(2*L-2)*n := by
  have hh := linear_coefficient_weights J B U L hshape
  have hR := numerator_weight residualSWeights (linearH J) (linearG J) (B-2) (B-1)
    hh.1.1 (by change _≤B-1+1; omega) (by change B-2≤B-1+0; omega)
    (by change 1+(B-2)≤B-1+0; omega) n
  have hY := numerator_weight residualYSWeights (linearH J) (linearG J) (U-1) (U-1)
    hh.1.2.1 (by change _≤U-1+1; omega) (by change U-1≤U-1+0; omega)
    (by change 1+(U-1)≤U-1+1; omega) n
  have hT := numerator_weight residualTotalWeights (linearH J) (linearG J) (L-1) (L-1)
    hh.1.2.2 (by change _≤L-1+1; omega) (by change L-1≤L-1+0; omega)
    (by change 1+(L-1)≤L-1+1; omega) n
  have hr : (B-2)+(B-1)=2*B-3 := by omega
  have hy : (U-1)+(U-1)=2*U-2 := by omega
  have ht : (L-1)+(L-1)=2*L-2 := by omega
  exact ⟨by simpa only [show residualSWeights 1=0 from rfl,zero_add,hr,Nat.mul_comm] using hR,
    by simpa only [show residualYSWeights 1=1 from rfl,hy,Nat.mul_comm] using hY,
    by simpa only [show residualTotalWeights 1=1 from rfl,ht,Nat.mul_comm] using hT⟩

variable [CharP K 2130706433] {I : Type} {x : I → K} {t y r : ℕ}

theorem packet_count_of_shape
    (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : Poly (K:=K)) (hJ : J≠0) (hs : J.degreeOf 1=1)
    (B U L : ℕ) (hB : 2≤B) (hBU : B≤U) (hUL : U≤L)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤B ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤L)
    (hFT : L<wt residualTotalWeights P.F)
    (hroot : ((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
    (hgates : Gates t y r (B-2) (U-1) (L-1))
    (hsmall : flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433) :
    P.seeds.card≤max (identityPrice t y r)
      (linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
        (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)) := by
  have hchar := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega : r<2130706433)
  have route := route_of_weights P.F J hJ hs P.rdegree hchar L
    (fun e he => (hshape e he).2.2) hFT hroot (2*B-3) (2*U-2) (2*L-2)
    (by omega) (by omega) (tail_weights J B U L hB hBU hUL hshape)
  exact packet_count P J _ _ route (B-2) (U-1) (L-1)
    (linear_coefficient_weights J B U L hshape).1 hgates hsmall

end
end ProximityPrize.SubmissionLower.PortfolioLinearShape6815
