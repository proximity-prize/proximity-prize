import ProximityPrize.SubmissionLower.MovingSourceBandOwnerEndpoints6814

/-! Transport actual packets to their eligibility interval's upper
endpoint. This preserves the carrier, selected polynomials and seeds;
only support bounds become weaker. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814.Packet
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
open RCN095 RCN135 RCN136 RCN156 RCN234 RCN275 LocatorHybridCells
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}

def widen (P : Packet x t y r) (t' y' r' : ℕ)
    (ht : t≤t') (hy : y≤y') (hr : r≤r')
    (hrlo : 4≤r') (hrhi : r'≤13) (hylo : r'+2≤y')
    (hyhi : y'≤57) (hyt : y'≤t') (hthi : t'≤3578) : Packet x t' y' r' :=
  {P with rlow := hrlo, rhigh := hrhi, ylow := hylo, yhigh := hyhi, yt := hyt, thigh := hthi
          box := by
            intro e he
            have hh := P.box he
            exact ⟨hh.1.trans ht,hh.2.1.trans hr,hh.2.2⟩
          support := by
            have hhR := P.r_weight.trans hr
            have hhY := P.y_weight.trans hy
            have hhT := P.total_weight.trans ht
            constructor <;> dsimp [cellSupport,RCN198.support,cellA,cellB,cellS] <;> omega}

theorem widen_seeds (P : Packet x t y r) (t' y' r' : ℕ)
    (ht : t≤t') (hy : y≤y') (hr : r≤r')
    (hrlo : 4≤r') (hrhi : r'≤13) (hylo : r'+2≤y')
    (hyhi : y'≤57) (hyt : y'≤t') (hthi : t'≤3578) :
    (P.widen t' y' r' ht hy hr hrlo hrhi hylo hyhi hyt hthi).seeds=P.seeds := rfl

#print axioms widen
end
end ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814.Packet
