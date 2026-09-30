import ProximityPrize.SubmissionLower.PortfolioCofactorEnvelope6815
import ProximityPrize.SubmissionLower.RamifiedOwnerDerivative6815
namespace ProximityPrize.SubmissionLower.PortfolioDerivativeOwner6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourcePairEnvelope6814
open PortfolioCost6815 PortfolioPriceIntervals6815 PortfolioCofactorEnvelope6815
variable {K I : Type} [Field K] [CharP K 2130706433] {x : I → K} {t y r : ℕ}

def derivativeFlag (s b u hi : ℕ) : FlagDegree := ⟨hi-u,u+s-b,b-2⟩

theorem derivative_envelope (J : Poly (K:=K)) (s b u hi : ℕ) (hs : order J=s)
    (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi) (hs2 : 2≤s) :
    CumulativeLe (ordinaryFlag (pderiv 1 J)) (derivativeFlag s b u hi) := by
  have hdB := RamifiedOwnerDerivative6815.pderiv_weight J slopeWeights
  have hdU := RamifiedOwnerDerivative6815.pderiv_weight J middleWeights
  have hdT := RamifiedOwnerDerivative6815.pderiv_weight J totalWeights
  have hdS := RamifiedOwnerDerivative6815.pderiv_order J
  change slope (pderiv 1 J)≤slope J-2 at hdB
  change middle (pderiv 1 J)≤middle J-1 at hdU
  change total (pderiv 1 J)≤total J-1 at hdT
  change order (pderiv 1 J)≤order J-1 at hdS
  have hn := source_nested J
  have hd := ordinaryFlag_cumulative (pderiv 1 J)
  change _≤b-2 ∧ _≤u+s-b+(b-2) ∧ _≤hi-u+(u+s-b)+(b-2)
  omega

theorem packet_count (P : Packet x t y r) [Fact (Irreducible P.F)]
    (SZ : Source P.F) (z : Degrees) (hZ : Fits SZ z)
    (hZFT : z.T<wt residualTotalWeights P.F) (hk : z.k<2130706433)
    (hg : Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hFT : 1700<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (m s b u hi cap : ℕ)
    (hm : 2≤m) (hms : m≤s) (hs : order J=s) (hb : slope J=b) (hu : middle J=u)
    (ht : total J≤hi) (hh : hi≤1700) (hsChar : s<2130706433) (hsize : hi+s≤8192)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hfit : pairCost z (m-1) (ownerFlag s b u hi) (derivativeFlag s b u hi) t y r+
      leading z t y r≤cap) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨SJ,SQ,hSJ,hSQ,hcop,hJd,hQd,_⟩ := RamifiedOwnerDerivative6815.source_pair_of_ramified_owner
    P.F hFT P.rdegree hchar J hJ (ht.trans hh)
    (by rw [asS_natDegree]; change 0<order J; omega)
    (by rw [asS_natDegree]; change order J<2130706433; omega) m hm hroot
  have hn := source_nested J
  have hp : CumulativeLe (ordinaryFlag SJ.P) (ownerFlag s b u hi) := by
    rw [hSJ]
    have h := ordinaryFlag_cumulative J
    change _≤b ∧ _≤u+s-b+b ∧ _≤hi-u+(u+s-b)+b
    omega
  have hq : CumulativeLe (ordinaryFlag SQ.P) (derivativeFlag s b u hi) := by
    rw [hSQ]
    exact derivative_envelope J s b u hi hs hb hu ht (by omega)
  have hpT : (ownerFlag s b u hi).zOnly+(ownerFlag s b u hi).yz+(ownerFlag s b u hi).all≤8192 := by
    dsimp only [ownerFlag]
    omega
  have hqT : (derivativeFlag s b u hi).zOnly+(derivativeFlag s b u hi).yz+
      (derivativeFlag s b u hi).all≤8192 := by
    dsimp only [derivativeFlag]
    omega
  have hcg := PortfolioPacketHelpers6815.pair_characteristic_gates _ _ hpT hqT
  have hc := pair_count_of_bounds P SZ SJ SQ z hZ hZFT hk hg hcop (m-1) (by omega)
    (by omega) (by omega) hQd _ _ hp hq hcg.1 hcg.2
  exact hc.trans (max_le_max le_rfl hfit)

end
end ProximityPrize.SubmissionLower.PortfolioDerivativeOwner6815
