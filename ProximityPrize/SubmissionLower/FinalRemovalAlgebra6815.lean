import ProximityPrize.SubmissionLower.FinalPrefixCheck6815
import ProximityPrize.SubmissionLower.ActualExactPhase6815
namespace ProximityPrize.SubmissionLower.FinalRemovalAlgebra6815
open FinalCurves6815 FinalPrefixCheck6815
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open Lower80899.Oracle Lower80899.PowerRoute Lower80899.FactorSwitch
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def phaseSound (j : ℕ) : PhaseSourceSound :=
  if j<7 then Lower80899.TenPhase.sound j else Lower80899.SourceSound.PhaseFinal.sound

theorem phase_source (j : ℕ) : (phaseSound j).source=(Lower80899.TenPhase.sound (sourceIndex j)).source := by
  unfold phaseSound sourceIndex
  split_ifs <;> rfl

theorem cost_phase_le (j r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    ExactInitialCharge6815.cost (phaseSound j).source.totalCap (phaseSound j).source.middleCap
      (phaseSound j).source.slopeCap r (r+v) (r+v+z)≤affine (phase j) r v z := by
  have h := (phaseSound j).stageCost_le (rawFlag r v z) 0 hr hR
    (by simpa only [rawFlag,middle,Nat.add_comm] using hy)
    (by simpa only [rawFlag,total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht) (Nat.zero_le _)
  have hp : (phaseSound j).potential=phase j := by unfold phaseSound phase; split_ifs <;> rfl
  simpa only [hp,stageCost,stagePair,exactRouteBox,helperPair,ExactInitialCharge6815.cost,
    PhasePotential6815.pair,rawFlag,Potential.eval,affine,middle,total,Nat.zero_mul,Nat.sub_zero,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem cost_terminal_le (k r y t : ℕ) (hk : k<5) (hr : 1≤r)
    (hR : r≤39-floorR k) (hy : y≤182-floorY k) (ht : t≤11192-floorT k) :
    ExactInitialCharge6815.cost 88902 1382 308 r y t≤
      (terminal k).totalCoeff*t+(terminal k).middleCoeff*y+(terminal k).slopeCoeff*r := by
  interval_cases k
  · exact TerminalPotentials6815.count0 r y t hr hR hy ht
  · exact TerminalPotentials6815.count1 r y t hr hR hy ht
  · exact TerminalPotentials6815.count2 r y t hr hR hy ht
  · exact TerminalPotentials6815.count3 r y t hr hR hy ht
  · exact TerminalPotentials6815.count4 r y t hr hR hy ht

def exactPieceCheck (L U S r y plo phi pstart : ℕ) (p : Piece) (cut cstart : ℕ) (c : Piece) : Bool :=
  if cstart<min c.stop cut then TriangularAffine6815.check
    (50174*c.base+ExactInitialCharge6815.num L U S r y y+1) (50174*c.slope)
    cstart (min c.stop cut-1) 0 (ExactRemovalPhase6815.tSlope L U S r y)
    (50174*(value p pstart plo+1)) (50174*p.slope) plo phi else true

def exactChildCheck (L U S r y plo phi pstart : ℕ) (p : Piece) (cut : ℕ) (child : List Piece) : Bool :=
  allCells (exactPieceCheck L U S r y plo phi pstart p cut) 0 child

theorem exactPieceCheck_sound (L U S r y plo phi pstart : ℕ) (p : Piece) (cut cstart : ℕ) (c : Piece)
    (h : exactPieceCheck L U S r y plo phi pstart p cut cstart c=true)
    (x z : ℕ) (hx0 : cstart≤x) (hxc : x<c.stop) (hxcut : x<cut) (hxz : x≤z)
    (hz0 : plo≤z) (hz1 : z≤phi) (hstart : pstart≤plo) :
    value c cstart x+ExactInitialCharge6815.cost L U S r y (y+(z-x))≤value p pstart z := by
  have hn : cstart<min c.stop cut := by omega
  simp only [exactPieceCheck,if_pos hn] at h
  have htri := TriangularAffine6815.check_sound _ _ _ _ _ _ _ _ _ _ x z h hx0 (by omega) hxz hz0 hz1
  have hp : value p pstart plo+p.slope*(z-plo)=value p pstart z := by
    unfold value
    rw [show z-pstart=(plo-pstart)+(z-plo) by omega,Nat.mul_add]
    omega
  have hn := ExactRemovalPhase6815.num_shift L U S r y (z-x)
  have ha : ExactInitialCharge6815.num L U S r y (y+(z-x))+50174*value c cstart x<
      50174*(value p pstart z+1) := by
    unfold TriangularAffine6815.left TriangularAffine6815.right at htri
    rw [hn,←hp]
    dsimp only [value] at *
    nlinarith only [htri]
  have hd : (ExactInitialCharge6815.num L U S r y (y+(z-x))+50174*value c cstart x)/50174<value p pstart z+1 := by
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa only [Nat.mul_comm] using ha)
  rw [Nat.add_mul_div_left _ _ (by decide),←ExactInitialCharge6815.cost_eq] at hd
  omega

theorem exactChildCheck_sound (L U S r y plo phi pstart : ℕ) (p : Piece)
    (cut finish : ℕ) (child : List Piece)
    (hv : validFrom finish 0 child=true)
    (hc : exactChildCheck L U S r y plo phi pstart p cut child=true)
    (x z : ℕ) (hxf : x<finish) (hxc : x<cut) (hxz : x≤z)
    (hz0 : plo≤z) (hz1 : z≤phi) (hstart : pstart≤plo) :
    eval child x+ExactInitialCharge6815.cost L U S r y (y+(z-x))≤value p pstart z := by
  obtain ⟨lo,c,hlo,hhi,he,hc⟩ := cell_at _ 0 finish child hv (allCells_sound _ 0 child hc) x (Nat.zero_le _) hxf
  simpa only [eval,he] using exactPieceCheck_sound L U S r y plo phi pstart p cut lo c hc x z hlo hhi hxc hxz hz0 hz1 hstart

end ProximityPrize.SubmissionLower.FinalRemovalAlgebra6815
