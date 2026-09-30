import ProximityPrize.SubmissionLower.PortfolioReceiptChecks6815
import ProximityPrize.SubmissionLower.PortfolioNativeOwner6815
import ProximityPrize.SubmissionLower.PortfolioDerivativeOwner6815
namespace ProximityPrize.SubmissionLower.PortfolioChoice6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 SecondJetCoefficients SecondJetCarrierDichotomy MovingFiberThreeSources6811
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open PortfolioSource6815 PortfolioCost6815 PortfolioNativeOwner6815
open PortfolioPriceIntervals6815 PortfolioReceiptChecks6815

inductive Choice where
  | native
  | derivative (ownerZ : Bool)
  | auxiliary (ownerZ : Bool) (source : Fin 75)
  deriving DecidableEq

def chosenZ (useOwner : Bool) (fixed : Degrees) (m s b u hi : ℕ) : Degrees :=
  if useOwner then ownerDegrees m s b u hi else fixed

def Common (z : Degrees) (low t y r : ℕ) : Prop :=
  z.T<low ∧ z.k<2130706433 ∧ Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0)
instance (z : Degrees) (low t y r : ℕ) : Decidable (Common z low t y r) := by
  unfold Common Gates
  infer_instance

def check (c : Choice) (fixed : Degrees) (low t y r cap m s b u lo hi : ℕ) : Bool :=
  match c with
  | .native => decide (Common (ownerDegrees m s b u hi) low t y r ∧
      nativeScalar (ownerDegrees m s b u hi) t y r/(3*(ownerDegrees m s b u hi).d)+
        leading (ownerDegrees m s b u hi) t y r≤cap)
  | .derivative useOwner =>
      let z := chosenZ useOwner fixed m s b u hi
      decide (2≤m ∧ Common z low t y r ∧
        pairCost z (m-1) (ownerFlag s b u hi) (PortfolioDerivativeOwner6815.derivativeFlag s b u hi) t y r+
          leading z t y r≤cap)
  | .auxiliary useOwner i =>
      let z := chosenZ useOwner fixed m s b u hi
      decide (Common z low t y r ∧ (PortfolioSourceCatalogue6815.profile i).L<low) &&
        checkAux i z m s b u lo hi t y r cap

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x : I → K} {t y r : ℕ}

theorem chosen_source (P : Packet x t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (J : Poly (K:=K)) (m s b u hi : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J≤hi)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (useOwner : Bool) : ∃ S : Source P.F, Fits S (chosenZ useOwner fixed m s b u hi) := by
  cases useOwner
  · exact ⟨fixedS,hFixed⟩
  · obtain ⟨S,_,hS⟩ := exists_owner_source P J m s b u hi hm hms hs hb hu ht hroot
    exact ⟨S,hS⟩

theorem count_of_check (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (c : Choice) (low cap m s b u lo hi tau : ℕ)
    (hloF : low≤wt residualTotalWeights P.F) (hlo : 2985<low) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hm : 0<m) (hms : m≤s)
    (hs : order J=s) (hb : slope J=b) (hu : middle J=u) (ht : total J=tau)
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hsmall : hi≤995) (hsChar : s<2130706433) (hsize : hi+s≤8192)
    (hx : lo≤tau) (hx' : tau≤hi)
    (hc : check c fixed low t y r cap m s b u lo hi=true) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hT : total J≤hi := by omega
  cases c with
  | native =>
    have hh := of_decide_eq_true hc
    exact PortfolioNativeOwner6815.packet_count P J m s b u hi cap hm hms hs hb hu hT hroot
      (hh.1.1.trans_le hloF) hh.1.2.1 hh.1.2.2 hh.2
  | derivative useOwner =>
    have hh := of_decide_eq_true hc
    obtain ⟨SZ,hZ⟩ := chosen_source P fixedS fixed hFixed J m s b u hi hm hms hs hb hu hT hroot useOwner
    exact PortfolioDerivativeOwner6815.packet_count P SZ _ hZ (hh.2.1.1.trans_le hloF)
      hh.2.1.2.1 hh.2.1.2.2 (by omega) J hJ m s b u hi cap hh.1 hms hs hb hu hT
      (by omega) hsChar hsize hroot hh.2.2
  | auxiliary useOwner i =>
    have hh := hc
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨SZ,hZ⟩ := chosen_source P fixedS fixed hFixed J m s b u hi hm hms hs hb hu hT hroot useOwner
    have hs' := aux_spec i _ m s b u lo hi t y r cap hh.2
    exact PortfolioAuxiliaryCount6815.packet_count nodes hI P SZ _ hZ (hh.1.1.1.trans_le hloF)
      hh.1.1.2.1 hh.1.1.2.2 i (hh.1.2.trans_le hloF) J hJ m s b u tau lo hi cap hm
      hs hb hu ht hroot hJne hx hx' (by omega) hsize hcap hs'.1 hs'.2

end
end ProximityPrize.SubmissionLower.PortfolioChoice6815
