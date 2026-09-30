import ProximityPrize.SubmissionLower.PortfolioBoxCheck6815
namespace ProximityPrize.SubmissionLower.PortfolioBoxCover6815
noncomputable section
set_option autoImplicit false
open PortfolioBoxes6815 PortfolioBoxCount6815 PortfolioCost6815
open RCN095 RCN135 RCN136 RCN156 RCN234 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 SecondJetCoefficients SecondJetCarrierDichotomy

def Valid (fixed : Degrees) (m low t y r cap : ℕ) (a : Box) : Prop :=
  ∃ c, PortfolioBoxCheck6815.check c fixed a m low t y r cap=true

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r : ℕ}
theorem count_of_covered (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (a : Box) (m low cap : ℕ)
    (hloF : low≤wt residualTotalWeights P.F) (hlo : 1700<low) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (ha : Admissible m (point J)) (h : Contains a (point J))
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hc : Covered m (Valid fixed m low t y r cap) a) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  obtain ⟨b,⟨c,hc⟩,hb⟩ := hc (point J) ha h
  exact PortfolioBoxCheck6815.count_of_check nodes hI P fixedS fixed hFixed c b m low cap
    hloF hlo hcap J hJ hb hroot hJne hc

end
end ProximityPrize.SubmissionLower.PortfolioBoxCover6815
