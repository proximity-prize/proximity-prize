import ProximityPrize.SubmissionLower.PortfolioAuxiliaryCount6815
namespace ProximityPrize.SubmissionLower.PortfolioReceiptChecks6815
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 50000
open PortfolioSource6815 PortfolioCost6815 PortfolioPriceIntervals6815 PortfolioAuxiliaryCount6815

instance (p : Parameters) (m s b u e : ℕ) : Decidable (active p m s b u e) := by
  unfold active
  infer_instance

def GoodPower (i : Fin 75) (m s b u lo : ℕ) : Prop :=
  let p := PortfolioSourceCatalogue6815.profile i
  (PacketPortfolioAvoidance6815.Impossible (PortfolioAvoidanceSource6815.caps p) (box p m s b u lo) ∧
    0<PortfolioSourceCatalogue6815.kernel i) ∨
  PacketPortfolioAvoidance6815.count (PortfolioAvoidanceSource6815.caps p) (box p m s b u lo)<
    PortfolioSourceCatalogue6815.kernel i

instance (i : Fin 75) (m s b u lo : ℕ) : Decidable (GoodPower i m s b u lo) := by
  unfold GoodPower PacketPortfolioAvoidance6815.Impossible
  infer_instance

def checkExit (p : Parameters) (z : Degrees) (m s b u lo hi t y r cap e : ℕ) : Bool :=
  if active p m s b u e ∧ lo≤upper p.L e hi then
    decide (totalNumerator z (min m (p.k+1-e*m)) (ownerFlag s b u lo)
        (cofactorFlag p.B p.U p.L p.s e s b u lo) t y r≤
          50174*(3*(z.d*min m (p.k+1-e*m)))*cap ∧
      totalNumerator z (min m (p.k+1-e*m)) (ownerFlag s b u (upper p.L e hi))
        (cofactorFlag p.B p.U p.L p.s e s b u (upper p.L e hi)) t y r≤
          50174*(3*(z.d*min m (p.k+1-e*m)))*cap)
  else true

def checkEndpoints (p : Parameters) (z : Degrees) (m s b u lo hi t y r cap : ℕ) : Bool :=
  (List.range (box p m s b u lo).q).all (checkExit p z m s b u lo hi t y r cap)

def checkAux (i : Fin 75) (z : Degrees) (m s b u lo hi t y r cap : ℕ) : Bool :=
  decide (GoodPower i m s b u lo) &&
    checkEndpoints (PortfolioSourceCatalogue6815.profile i) z m s b u lo hi t y r cap

theorem endpoints_spec (p : Parameters) (z : Degrees) (m s b u lo hi t y r cap : ℕ)
    (h : checkEndpoints p z m s b u lo hi t y r cap=true) :
    EndpointChecks p z m s b u lo hi t y r cap := by
  intro e he ha hl
  have hh := List.all_eq_true.mp h e (List.mem_range.mpr he)
  have hcond : active p m s b u e ∧ lo≤upper p.L e hi := ⟨ha,hl⟩
  simpa only [checkExit,if_pos hcond,decide_eq_true_eq] using hh

theorem aux_spec (i : Fin 75) (z : Degrees) (m s b u lo hi t y r cap : ℕ)
    (h : checkAux i z m s b u lo hi t y r cap=true) :
    GoodPower i m s b u lo ∧
      EndpointChecks (PortfolioSourceCatalogue6815.profile i) z m s b u lo hi t y r cap := by
  have hh := h
  simp only [checkAux,Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨hh.1,endpoints_spec _ _ _ _ _ _ _ _ _ _ _ _ hh.2⟩

end ProximityPrize.SubmissionLower.PortfolioReceiptChecks6815
