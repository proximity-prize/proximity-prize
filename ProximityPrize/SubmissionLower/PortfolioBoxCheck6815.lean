import ProximityPrize.SubmissionLower.PortfolioBoxCount6815
import ProximityPrize.SubmissionLower.PortfolioChoice6815
namespace ProximityPrize.SubmissionLower.PortfolioBoxCheck6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open PortfolioBoxes6815 PortfolioBoxCount6815 PortfolioCost6815 PortfolioSource6815
open PortfolioChoice6815 (Choice Common)
open RCN095 RCN135 RCN136 RCN156 RCN234 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 SecondJetCoefficients SecondJetCarrierDichotomy

def chosenZ (useOwner : Bool) (fixed : Degrees) (a : Box) (m : ℕ) :=
  if useOwner then ownerZ a m else fixed

instance (p : Parameters) (a : Box) (m e : ℕ) : Decidable (active p a m e) := by
  unfold active; infer_instance
instance (i : Fin 75) (a : Box) (m : ℕ) : Decidable (GoodPower i a m) := by
  unfold GoodPower PacketPortfolioAvoidance6815.Impossible; infer_instance

def PairChecks (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r cap : ℕ) : Prop :=
  flagMixed p q unitZFlag<2130706433 ∧ flagMixed p q unitYZFlag<2130706433 ∧
    pairCost z delta p q t y r+leading z t y r≤cap
instance (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r cap : ℕ) :
    Decidable (PairChecks z delta p q t y r cap) := by unfold PairChecks; infer_instance

def checkExit (p : Parameters) (a : Box) (z : Degrees) (m t y r cap e : ℕ) : Bool :=
  if active p a m e then decide (PairChecks z (min m (p.k+1-e*m))
    (ownerFlag a) (cofactorFlag p a e) t y r cap) else true
def checkExits (p : Parameters) (a : Box) (z : Degrees) (m t y r cap : ℕ) : Bool :=
  (List.range (powerBox p a m).q).all (checkExit p a z m t y r cap)

def checkChoice (c : Choice) (fixed : Degrees) (a : Box) (m low t y r cap : ℕ) : Bool :=
  match c with
  | .native => decide (Common (ownerZ a m) low t y r ∧
      nativeScalar (ownerZ a m) t y r/(3*(ownerZ a m).d)+leading (ownerZ a m) t y r≤cap)
  | .derivative useOwner =>
      let z := chosenZ useOwner fixed a m
      decide (2≤m ∧ Common z low t y r ∧ PairChecks z (m-1) (ownerFlag a) (derivativeFlag a) t y r cap)
  | .auxiliary useOwner i =>
      let z := chosenZ useOwner fixed a m
      decide (Common z low t y r ∧ (PortfolioSourceCatalogue6815.profile i).L<low) &&
        decide (GoodPower i a m) && checkExits (PortfolioSourceCatalogue6815.profile i) a z m t y r cap

def check (c : Choice) (fixed : Degrees) (a : Box) (m low t y r cap : ℕ) : Bool :=
  decide (0<m ∧ m≤a.slo ∧ 2*a.slo≤a.bhi ∧ a.thi≤1700 ∧ a.thi<low ∧ a.shi<2130706433) &&
    checkChoice c fixed a m low t y r cap

theorem exits_spec (p : Parameters) (a : Box) (z : Degrees) (m t y r cap : ℕ)
    (hc : checkExits p a z m t y r cap=true) :
    ∀ e, e<(powerBox p a m).q → active p a m e →
      PairChecks z (min m (p.k+1-e*m)) (ownerFlag a) (cofactorFlag p a e) t y r cap := by
  intro e he ha
  have hh := List.all_eq_true.mp hc e (List.mem_range.mpr he)
  simpa only [checkExit,if_pos ha,decide_eq_true_eq] using hh

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r : ℕ}

theorem count_of_check (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (fixedS : Source P.F) (fixed : Degrees) (hFixed : Fits fixedS fixed)
    (c : Choice) (a : Box) (m low cap : ℕ)
    (hloF : low≤wt residualTotalWeights P.F) (hlo : 1700<low) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (h : Contains a (point J))
    (hroot : ((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne : (asS J).map (carrierMap P.F)≠0)
    (hc : check c fixed a m low t y r cap=true) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hm,hms,h2,hsmall,hJF,hsChar⟩ := hc.1
  have hsrc (useOwner : Bool) : ∃ S : Source P.F, Fits S (chosenZ useOwner fixed a m) := by
    cases useOwner
    · exact ⟨fixedS,hFixed⟩
    · exact owner_source P J a m hm h hms h2 hroot
  cases c with
  | native =>
    have hh := of_decide_eq_true hc.2
    obtain ⟨S,hS⟩ := owner_source P J a m hm h hms h2 hroot
    exact (native_count_of_degrees P S _ hS (hh.1.1.trans_le hloF) hh.1.2.1 hh.1.2.2).trans
      (max_le_max le_rfl hh.2)
  | derivative useOwner =>
    have hh := of_decide_eq_true hc.2
    obtain ⟨S,hS⟩ := hsrc useOwner
    exact derivative_count P S _ hS (hh.2.1.1.trans_le hloF) hh.2.1.2.1 hh.2.1.2.2
      (hlo.trans_le hloF) J hJ a m cap h hh.1 (hms.trans h.1) hsmall hsChar hroot
      ⟨hh.2.2.1,hh.2.2.2.1⟩ hh.2.2.2.2
  | auxiliary useOwner i =>
    have hh := hc.2
    simp only [checkChoice,Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨S,hS⟩ := hsrc useOwner
    exact auxiliary_count nodes hI P S _ hS (hh.1.1.1.1.trans_le hloF)
      hh.1.1.1.2.1 hh.1.1.1.2.2 i (hh.1.1.2.trans_le hloF) J hJ a m cap h hm hroot hJne
      (hJF.trans_le hloF) hcap hh.1.2 (exits_spec _ _ _ _ _ _ _ _ hh.2)

end
end ProximityPrize.SubmissionLower.PortfolioBoxCheck6815
