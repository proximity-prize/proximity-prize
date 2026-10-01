import ProximityPrize.SubmissionLower.MergedPackingFull6815_1
import ProximityPrize.SubmissionLower.MergedPackingLight6815_1
import ProximityPrize.SubmissionLower.SingletonData6815
import ProximityPrize.SubmissionLower.MergedInfra6815_52
import ProximityPrize.SubmissionLower.MergedInfra6815_51
import ProximityPrize.SubmissionLower.MergedInfra6815_20
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.PackingData6815
open PackingSemantics6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
def full_slope (j : ℕ) : ℕ := match j with
  | 0 => PackingFull6815_S00.slope
  | 1 => PackingFull6815_S01.slope
  | 2 => PackingFull6815_S02.slope
  | 3 => PackingFull6815_S03.slope
  | 4 => PackingFull6815_S04.slope
  | 5 => PackingFull6815_S05.slope
  | 6 => PackingFull6815_S06.slope
  | 7 => PackingFull6815_S07.slope
  | _ => 0
def full_own (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingFull6815_S00.own
  | 1 => PackingFull6815_S01.own
  | 2 => PackingFull6815_S02.own
  | 3 => PackingFull6815_S03.own
  | 4 => PackingFull6815_S04.own
  | 5 => PackingFull6815_S05.own
  | 6 => PackingFull6815_S06.own
  | 7 => PackingFull6815_S07.own
  | _ => fun _ => #[]
def full_packed (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingFull6815_S00.packed
  | 1 => PackingFull6815_S01.packed
  | 2 => PackingFull6815_S02.packed
  | 3 => PackingFull6815_S03.packed
  | 4 => PackingFull6815_S04.packed
  | 5 => PackingFull6815_S05.packed
  | 6 => PackingFull6815_S06.packed
  | 7 => PackingFull6815_S07.packed
  | _ => fun _ => #[]
theorem full_bellman (j : ℕ) (hj : j<8) : AffineFactorAggregate6808.BellmanRows 39 182 (lookup (full_own j)) (lookup (full_packed j)) := by
  interval_cases j
  · exact PackingFull6815_S00.bellman
  · exact PackingFull6815_S01.bellman
  · exact PackingFull6815_S02.bellman
  · exact PackingFull6815_S03.bellman
  · exact PackingFull6815_S04.bellman
  · exact PackingFull6815_S05.bellman
  · exact PackingFull6815_S06.bellman
  · exact PackingFull6815_S07.bellman
def light_slope (j : ℕ) : ℕ := match j with
  | 0 => PackingLight6815_S00.slope
  | 1 => PackingLight6815_S01.slope
  | 2 => PackingLight6815_S02.slope
  | 3 => PackingLight6815_S03.slope
  | 4 => PackingLight6815_S04.slope
  | 5 => PackingLight6815_S05.slope
  | 6 => PackingLight6815_S06.slope
  | 7 => PackingLight6815_S07.slope
  | 8 => PackingLight6815_S08.slope
  | 9 => PackingLight6815_S09.slope
  | 10 => PackingLight6815_S10.slope
  | 11 => PackingLight6815_S11.slope
  | 12 => PackingLight6815_S12.slope
  | 13 => PackingLight6815_S13.slope
  | _ => 0
def light_own (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingLight6815_S00.own
  | 1 => PackingLight6815_S01.own
  | 2 => PackingLight6815_S02.own
  | 3 => PackingLight6815_S03.own
  | 4 => PackingLight6815_S04.own
  | 5 => PackingLight6815_S05.own
  | 6 => PackingLight6815_S06.own
  | 7 => PackingLight6815_S07.own
  | 8 => PackingLight6815_S08.own
  | 9 => PackingLight6815_S09.own
  | 10 => PackingLight6815_S10.own
  | 11 => PackingLight6815_S11.own
  | 12 => PackingLight6815_S12.own
  | 13 => PackingLight6815_S13.own
  | _ => fun _ => #[]
def light_packed (j : ℕ) : ℕ → Array ℕ := match j with
  | 0 => PackingLight6815_S00.packed
  | 1 => PackingLight6815_S01.packed
  | 2 => PackingLight6815_S02.packed
  | 3 => PackingLight6815_S03.packed
  | 4 => PackingLight6815_S04.packed
  | 5 => PackingLight6815_S05.packed
  | 6 => PackingLight6815_S06.packed
  | 7 => PackingLight6815_S07.packed
  | 8 => PackingLight6815_S08.packed
  | 9 => PackingLight6815_S09.packed
  | 10 => PackingLight6815_S10.packed
  | 11 => PackingLight6815_S11.packed
  | 12 => PackingLight6815_S12.packed
  | 13 => PackingLight6815_S13.packed
  | _ => fun _ => #[]
theorem light_bellman (j : ℕ) (hj : j<14) : RectangularPacking6815.Bellman 19 70 (lookup (light_own j)) (lookup (light_packed j)) := by
  interval_cases j
  · exact PackingLight6815_S00.bellman
  · exact PackingLight6815_S01.bellman
  · exact PackingLight6815_S02.bellman
  · exact PackingLight6815_S03.bellman
  · exact PackingLight6815_S04.bellman
  · exact PackingLight6815_S05.bellman
  · exact PackingLight6815_S06.bellman
  · exact PackingLight6815_S07.bellman
  · exact PackingLight6815_S08.bellman
  · exact PackingLight6815_S09.bellman
  · exact PackingLight6815_S10.bellman
  · exact PackingLight6815_S11.bellman
  · exact PackingLight6815_S12.bellman
  · exact PackingLight6815_S13.bellman
end ProximityPrize.SubmissionLower.PackingData6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.PackingOwnCheck6815
open PackingSemantics6815 PackingData6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def fullCheck (r v : ℕ) (curve : List FinalCurves6815.Piece) : Bool := allN (fun j =>
  affineCheck (full_slope j) (lookup (full_own j) r v) curve) 8
def lightCheck (r v : ℕ) (curve : List FinalCurves6815.Piece) : Bool := allN (fun j =>
  affineCheck (light_slope j) (lookup (light_own j) r v) curve) 14
def localCheck (r v : ℕ) (curve : List FinalCurves6815.Piece) : Bool := fullCheck r v curve &&
  (if r<10 ∧ v≤70 then lightCheck r v curve else true)
def rowCheck (r v : ℕ) : Bool := localCheck r v (SingletonData6815.curve r v)

theorem curve_valid (r v : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) :
    FinalCurves6815.validFrom (11193-r-v) 0 (SingletonData6815.curve r v)=true := by
  have h := check_curve r v _ (SingletonData6815.checked r v hr hR hy)
  simp only [SingletonCurveChecks6815.check,Bool.and_eq_true] at h
  exact h.1.1

theorem full_sound (r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (hz : r+v+z≤11192)
    (h : rowCheck r v=true) (j : ℕ) (hj : j<8) :
    SingletonData6815.cap r v z≤full_slope j*z+lookup (full_own j) r v := by
  simp only [rowCheck,localCheck,Bool.and_eq_true] at h
  exact affineCheck_sound _ _ (11193-r-v) _ (curve_valid r v hr hR hy)
    (allN_sound _ 8 h.1 j hj) z (by omega)

theorem light_sound (r v z : ℕ) (hr : 1≤r) (hR : r<10) (hv : v≤70) (hz : r+v+z≤11192)
    (h : rowCheck r v=true) (j : ℕ) (hj : j<14) :
    SingletonData6815.cap r v z≤light_slope j*z+lookup (light_own j) r v := by
  simp only [rowCheck,localCheck,Bool.and_eq_true,if_pos (show r<10 ∧ v≤70 from ⟨hR,hv⟩)] at h
  exact affineCheck_sound _ _ (11193-r-v) _ (curve_valid r v hr (by omega) (by omega))
    (allN_sound _ 14 h.2 j hj) z (by omega)

end ProximityPrize.SubmissionLower.PackingOwnCheck6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.FinalBaseCheck6815
open FinalCurves6815 PackingData6815 PackingSemantics6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def fullNum (j r v : ℕ) := lookup (full_packed j) r v
def lightNum (j r v : ℕ) := lookup (light_packed j) r v

def BaseBound (r v z cap : ℕ) : Prop :=
  (∃ j, j<8 ∧ full_slope j*z+fullNum j r v≤cap) ∨
  (10≤r ∧ r≤19 ∧ v≤70 ∧
    (∃ j, j<14 ∧ light_slope j*z+lightNum j r v≤cap) ∧
    ∀ q u, 10≤q → q≤r → u≤v → ∃ j, j<14 ∧ ∀ x, x≤z →
      SingletonData6815.cap q u x+light_slope j*(z-x)+lightNum j (r-q) (v-u)≤cap)

def lineCheck (slope base lo hi start : ℕ) (p : Piece) : Bool :=
  if lo≤hi then Nat.ble (slope*lo+base) (value p start lo) &&
    Nat.ble (slope*hi+base) (value p start hi) else true

theorem lineCheck_sound (slope base lo hi start : ℕ) (p : Piece)
    (h : lineCheck slope base lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo) : slope*z+base≤value p start z := by
  simp only [lineCheck,if_pos (hz.trans hh),Bool.and_eq_true,Nat.ble_eq] at h
  have hm := TriangularAffine6815.shifted_between lo hi z 0 start base p.base slope p.slope
    (Nat.zero_le _) hs hz hh
    (by simpa only [value,Nat.sub_zero,Nat.add_comm] using h.1)
    (by simpa only [value,Nat.sub_zero,Nat.add_comm] using h.2)
  simpa only [value,Nat.sub_zero,Nat.add_comm] using hm

def childPiece (slope charge lo hi start : ℕ) (p : Piece) (cstart : ℕ) (c : Piece) : Bool :=
  TriangularAffine6815.check c.base c.slope cstart (c.stop-1) charge slope
    (value p start lo) p.slope lo hi
def childCheck (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) : Bool :=
  allCells (childPiece slope charge lo hi start p) 0 child

theorem childCheck_sound (slope charge lo hi start : ℕ) (p : Piece) (finish : ℕ) (child : List Piece)
    (hv : validFrom finish 0 child=true) (hc : childCheck slope charge lo hi start p child=true)
    (x z : ℕ) (hxf : x<finish) (hxz : x≤z) (hz : lo≤z) (hh : z≤hi) (hs : start≤lo) :
    eval child x+slope*(z-x)+charge≤value p start z := by
  obtain ⟨clo,c,hclo,hchi,he,hc⟩ := cell_at _ 0 finish child hv (allCells_sound _ 0 child hc) x (Nat.zero_le _) hxf
  have h := TriangularAffine6815.check_sound _ _ _ _ _ _ _ _ _ _ x z hc hclo (by omega) hxz hz hh
  have hp : value p start lo+p.slope*(z-lo)=value p start z := by
    unfold value
    rw [show z-start=(lo-start)+(z-lo) by omega,Nat.mul_add]
    omega
  change value c clo x+charge+slope*(z-x)≤value p start lo+p.slope*(z-lo) at h
  rw [hp] at h
  simpa only [eval,he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def digit (code i : ℕ) := code/(16^i)%16
def heavyChoice (code v q u : ℕ) := digit code (1+(q-10)*(v+1)+u)
def heavyCheck (r v code lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt (digit code 0) 14 && lineCheck (light_slope (digit code 0)) (lightNum (digit code 0) r v) lo hi start p &&
  allN (fun i => allN (fun u =>
    let q := i+10
    let j := heavyChoice code v q u
    Nat.blt j 14 && childCheck (light_slope j) (lightNum j (r-q) (v-u)) lo hi start p
      (FinalLookup6815.single q u).curve) (v+1)) (r-9)

def check (r v aux lo hi start : ℕ) (p : Piece) : Bool :=
  if aux<8 then lineCheck (full_slope aux) (fullNum aux r v) lo hi start p
  else decide (aux%16=15 ∧ 10≤r ∧ r≤19 ∧ v≤70 ∧ hi≤4500) &&
    heavyCheck r v (aux/16) lo hi start p

theorem check_sound (r v aux lo hi start : ℕ) (p : Piece)
    (h : check r v aux lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo) (ht : r+v+z≤11192) :
    BaseBound r v z (value p start z) := by
  by_cases ha : aux<8
  · left
    simp only [check,if_pos ha] at h
    exact ⟨aux,ha,lineCheck_sound _ _ _ _ _ p h z hz hh hs⟩
  · right
    simp only [check,if_neg ha,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨hg,hc⟩ := h
    simp only [heavyCheck,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨hg.2.1,hg.2.2.1,hg.2.2.2.1,?_,?_⟩
    · exact ⟨digit (aux/16) 0,hc.1.1,lineCheck_sound _ _ _ _ _ p hc.1.2 z hz hh hs⟩
    · intro q u hq hqr hu
      have hhq := allN_sound _ (r-9) hc.2 (q-10) (by omega)
      have hhu := allN_sound _ (v+1) hhq u (by omega)
      simp only [show q-10+10=q by omega,Bool.and_eq_true,Nat.blt_eq] at hhu
      refine ⟨heavyChoice (aux/16) v q u,hhu.1,?_⟩
      intro x hx
      have hq39 : q≤39 := by omega
      have hqu : q+u≤182 := by omega
      have he : (FinalLookup6815.single q u).curve=SingletonData6815.curve q u :=
        congrArg SingletonCertificate6815.Row.curve (FinalLookup6815.single_eq q u (by omega) hq39)
      have hv : validFrom (11193-q-u) 0 (FinalLookup6815.single q u).curve=true := by
        rw [he]
        exact PackingOwnCheck6815.curve_valid q u (by omega) hq39 hqu
      have hb := childCheck_sound _ _ lo hi start p (11193-q-u) _ hv hhu.2 x z (by omega) hx hz hh hs
      simpa only [he,SingletonData6815.cap] using hb

end ProximityPrize.SubmissionLower.FinalBaseCheck6815
end MergedPart2
section MergedPart3
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
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.FinalPayment6815
open FinalCurves6815 FinalPrefixCheck6815 FinalPrefixSound6815 FinalRemovalAlgebra6815
open FinalPrefixRowsCheck6815 FinalBaseCheck6815
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def src (j : ℕ) := (Lower80899.TenPhase.sound j).source
def cost (j r v z : ℕ) := ExactInitialCharge6815.cost (src j).totalCap (src j).middleCap
  (src j).slopeCap r (r+v) (r+v+z)
def Payment (j r v z cap : ℕ) : Prop :=
  ∀ q u x, q<r → u≤v → x≤z → (q=0 → u=0 ∧ x=0) →
    (1≤q → x<cut q u j) →
    FinalLedgerData6815.cap q u x+cost j (r-q) (v-u) (z-x)≤cap

def fastCut (r v j : ℕ) := threshold (SingletonCertificate6815.thresholds (FinalLookup6815.single r v)) j
def fastPrefix (r v j : ℕ) := coeff (FinalLookup6815.pref r v) j
def fastSeen (r v k : ℕ) := present (FinalLookup6815.pref r v) k

theorem fastCut_eq (r v j : ℕ) (hr : 1≤r) (hR : r≤39) : fastCut r v j=cut r v j := by
  unfold fastCut cut
  rw [FinalLookup6815.single_eq r v hr hR]

theorem fastPrefix_eq (r v j : ℕ) (hR : r≤39) : fastPrefix r v j=prefixCap r v j := by
  unfold fastPrefix prefixCap
  by_cases h : r=0
  · subst r; rfl
  · rw [FinalLookup6815.pref_eq r v (by omega) hR]

theorem fastSeen_eq (r v k : ℕ) (hR : r≤39) : fastSeen r v k=seen r v k := by
  unfold fastSeen seen
  by_cases h : r=0
  · subst r; rfl
  · rw [FinalLookup6815.pref_eq r v (by omega) hR]

theorem affine_add_removed (p : Potential) (r v z q u x : ℕ) (hq : q≤r) (hu : u≤v) (hx : x≤z) :
    affine p q u x+affine p (r-q) (v-u) (z-x)=affine p r v z := by
  unfold affine
  calc
    _=p.totalCoeff*(q+u+x+((r-q)+(v-u)+(z-x)))+
      p.middleCoeff*(q+u+((r-q)+(v-u)))+p.slopeCoeff*(q+(r-q)) := by ring
    _=_ := by
      rw [show q+u+x+((r-q)+(v-u)+(z-x))=r+v+z by omega,
        show q+u+((r-q)+(v-u))=r+v by omega,show q+(r-q)=r by omega]

theorem cost_phase (j r v z : ℕ) (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    cost (sourceIndex j) r v z≤affine (phase j) r v z := by
  have h := cost_phase_le j r v z hr hR hy ht
  simpa only [cost,src,phase_source] using h

theorem phase_payment (j r v z cap : ℕ) (hj : j<8) (hr : 1≤r) (hR : r≤39)
    (hy : r+v≤182) (ht : r+v+z≤11192)
    (hbudget : affine (phase j) r v z+prefixCap (r-1) v j≤cap) :
    Payment (sourceIndex j) r v z cap := by
  intro q u x hq hu hx hzero hcut
  by_cases hq0 : q=0
  · obtain ⟨rfl,rfl⟩ := hzero hq0
    subst q
    have h := cost_phase j r v z hr hR hy ht
    simpa only [FinalLedgerData6815.cap,FinalLedgerData6815.row,FinalCurves6815.eval,
      FinalCurves6815.evalFrom,Nat.sub_zero,Nat.zero_add] using h.trans (Nat.le_add_right _ _ |>.trans hbudget)
  · have hq1 : 1≤q := by omega
    have hc := phase_prefix q u x j hq1 (by omega) (by omega) (by omega) hj (hcut hq1)
    have hp := prefix_mono j q u (r-1) v (by omega) (by omega) hu (by omega) (by omega)
    have hm := cost_phase j (r-q) (v-u) (z-x) (by omega) (by omega) (by omega) (by omega)
    have he := affine_add_removed (phase j) r v z q u x (by omega) hu hx
    omega

theorem terminal_payment (r v z cap : ℕ) (hr : 1≤r) (hR : r≤39)
    (hy : r+v≤182) (ht : r+v+z≤11192)
    (hbudget : ∀ k, k<5 → (k=0 ∨ (seen (r-1) v k=true ∧ floorR k<r ∧ floorY k<r+v ∧ floorT k<r+v+z)) →
      affine (terminal k) r v z+prefixCap (r-1) v (k+8)≤cap) :
    Payment 5 r v z cap := by
  intro q u x hq hu hx hzero hcut
  by_cases hq0 : q=0
  · obtain ⟨rfl,rfl⟩ := hzero hq0
    subst q
    have hc := cost_terminal_le 0 r (r+v) (r+v+z) (by decide) hr hR hy ht
    have hb := hbudget 0 (by decide) (Or.inl rfl)
    change cost 5 r v z≤affine (terminal 0) r v z at hc
    simpa only [FinalLedgerData6815.cap,FinalLedgerData6815.row,FinalCurves6815.eval,
      FinalCurves6815.evalFrom,Nat.sub_zero,Nat.zero_add] using hc.trans (Nat.le_add_right _ _ |>.trans hb)
  · have hq1 : 1≤q := by omega
    let k := classify q u x
    have hk : k<5 := class_lt_five _ _ _
    have hc := terminal_prefix q u x hq1 (by omega) (by omega) (by omega) (hcut hq1)
    have hs := seen_mono k q u (r-1) v hk (by omega) hu (by omega) (by omega) hc.2
    have hp := prefix_mono (k+8) q u (r-1) v (by omega) (by omega) hu (by omega) (by omega)
    have hf := class_interval q u x (by omega)
    change (floorR k≤q ∧ floorY k≤q+u) ∧ lower k q u≤x ∧ _ at hf
    have htFloor : floorT k≤q+u+x := by have h := hf.2.1; unfold lower at h; omega
    have hm := cost_terminal_le k (r-q) ((r-q)+(v-u)) ((r-q)+(v-u)+(z-x)) hk
      (by omega) (by omega) (by omega) (by omega)
    change cost 5 (r-q) (v-u) (z-x)≤affine (terminal k) (r-q) (v-u) (z-x) at hm
    have he := affine_add_removed (terminal k) r v z q u x (by omega) hu hx
    have hb := hbudget k hk (Or.inr ⟨hs,by omega,by omega,by omega⟩)
    dsimp only [k] at hp hm he hb
    omega

end ProximityPrize.SubmissionLower.FinalPayment6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.FinalRuleCheck6815
open FinalCurves6815 FinalPrefixCheck6815 FinalPrefixSound6815 FinalRemovalAlgebra6815
open FinalPrefixRowsCheck6815 FinalBaseCheck6815 FinalPayment6815 SingletonCertificate6815
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def RuleBound (r v z cap : ℕ) : Prop := BaseBound r v z cap ∨
  ∃ j, j<7 ∧ cut r v j≤z ∧ Payment j r v z cap

def phaseCheck (r v j lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt j 8 && Nat.ble (fastCut r v (sourceIndex j)) lo &&
    lineCheck (phase j).totalCoeff (affine (phase j) r v 0+fastPrefix (r-1) v j) lo hi start p

theorem phaseCheck_sound (r v j lo hi start : ℕ) (p : Piece)
    (h : phaseCheck r v j lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo)
    (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    RuleBound r v z (value p start z) := by
  simp only [phaseCheck,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq,fastCut_eq r v _ hr hR] at h
  have hj : sourceIndex j<7 := by unfold sourceIndex; split_ifs <;> omega
  have hb := lineCheck_sound _ _ lo hi start p h.2 z hz hh hs
  rw [fastPrefix_eq (r-1) v j (by omega)] at hb
  have hb' : affine (phase j) r v z+prefixCap (r-1) v j≤value p start z := by
    rw [affine_shift (phase j) r v 0 z (Nat.zero_le _)]
    simpa only [Nat.sub_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
  exact Or.inr ⟨sourceIndex j,hj,h.1.2.trans hz,phase_payment j r v z _ h.1.1 hr hR hy ht hb'⟩

def terminalGuard (r v k : ℕ) : Prop :=
  k=0 ∨ (fastSeen (r-1) v k=true ∧ floorR k<r ∧ floorY k<r+v)
instance (r v k : ℕ) : Decidable (terminalGuard r v k) := by unfold terminalGuard; infer_instance
def terminalLow (r v k lo : ℕ) := if k=0 then lo else max lo (floorT k+1-(r+v))
def terminalPiece (r v k lo hi start : ℕ) (p : Piece) : Bool :=
  if terminalGuard r v k then
    lineCheck (terminal k).totalCoeff (affine (terminal k) r v 0+fastPrefix (r-1) v (k+8))
      (terminalLow r v k lo) hi start p
  else true
def terminalCheck (r v lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.ble (fastCut r v 5) lo && allN (fun k => terminalPiece r v k lo hi start p) 5

theorem terminalCheck_sound (r v lo hi start : ℕ) (p : Piece)
    (h : terminalCheck r v lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo)
    (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    RuleBound r v z (value p start z) := by
  simp only [terminalCheck,Bool.and_eq_true,Nat.ble_eq,fastCut_eq r v 5 hr hR] at h
  refine Or.inr ⟨5,by decide,h.1.trans hz,?_⟩
  apply terminal_payment r v z _ hr hR hy ht
  intro k hk hg
  have hguard : terminalGuard r v k := by
    unfold terminalGuard
    rw [fastSeen_eq (r-1) v k (by omega)]
    rcases hg with he | he
    · exact Or.inl he
    · exact Or.inr ⟨he.1,he.2.1,he.2.2.1⟩
  have hl : terminalLow r v k lo≤z := by
    unfold terminalLow
    split_ifs with he
    · exact hz
    · rcases hg with hg | hg
      · exact (he hg).elim
      · exact max_le hz (by omega)
  have hstart : start≤terminalLow r v k lo := by
    unfold terminalLow
    split_ifs
    · exact hs
    · exact hs.trans (le_max_left _ _)
  have hc := allN_sound _ 5 h.2 k hk
  simp only [terminalPiece,if_pos hguard] at hc
  have hb := lineCheck_sound _ _ _ hi start p hc z hl hh hstart
  rw [fastPrefix_eq (r-1) v (k+8) (by omega)] at hb
  rw [affine_shift (terminal k) r v 0 z (Nat.zero_le _)]
  simpa only [Nat.sub_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb

def emptyCurve : List Piece := [⟨1,0,0⟩]
def exactEmpty (r v j lo hi start : ℕ) (p : Piece) : Bool :=
  exactChildCheck (src j).totalCap (src j).middleCap (src j).slopeCap r (r+v)
    lo hi start p 1 emptyCurve
def exactChild (r v j lo hi start : ℕ) (p : Piece) (q u : ℕ) : Bool :=
  exactChildCheck (src j).totalCap (src j).middleCap (src j).slopeCap (r-q) ((r-q)+(v-u))
    lo hi start p (fastCut q u j) (FinalLookup6815.final q u)
def exactCheck (r v j lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt j 7 && Nat.ble (fastCut r v j) lo && exactEmpty r v j lo hi start p &&
    allN (fun i => allN (fun u => exactChild r v j lo hi start p (i+1) u) (v+1)) (r-1)

theorem exactCheck_sound (r v j lo hi start : ℕ) (p : Piece)
    (h : exactCheck r v j lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo)
    (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    RuleBound r v z (value p start z) := by
  simp only [exactCheck,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq,fastCut_eq r v j hr hR] at h
  refine Or.inr ⟨j,h.1.1.1,h.1.1.2.trans hz,?_⟩
  intro q u x hq hu hx hzero hcut
  by_cases hq0 : q=0
  · obtain ⟨rfl,rfl⟩ := hzero hq0
    subst q
    have hb := exactChildCheck_sound (src j).totalCap (src j).middleCap (src j).slopeCap r (r+v)
      lo hi start p 1 1 emptyCurve (by decide) h.1.2 0 z (by decide) (by decide) (Nat.zero_le _) hz hh hs
    simpa only [emptyCurve,eval,evalFrom,value,show 0<1 by decide,if_pos,Nat.zero_mul,Nat.add_zero,
      Nat.zero_add,Nat.sub_zero,FinalLedgerData6815.cap,FinalLedgerData6815.row,cost] using hb
  · have hq1 : 1≤q := by omega
    have hc := allN_sound _ (r-1) h.2 (q-1) (by omega)
    have hc := allN_sound _ (v+1) hc u (by omega)
    simp only [show q-1+1=q by omega] at hc
    have he := FinalLookup6815.final_eq q u hq1 (by omega)
    have hv : validFrom (11193-q-u) 0 (FinalLookup6815.final q u)=true := by
      rw [he]
      exact FinalPrefixSound6815.curve_valid q u hq1 (by omega) (by omega)
    have hxcut : x<fastCut q u j := by rw [fastCut_eq q u j hq1 (by omega)]; exact hcut hq1
    have hb := exactChildCheck_sound (src j).totalCap (src j).middleCap (src j).slopeCap (r-q) ((r-q)+(v-u))
      lo hi start p (fastCut q u j) (11193-q-u) (FinalLookup6815.final q u) hv hc x z (by omega) hxcut hx hz hh hs
    simpa only [he,FinalLedgerData6815.cap,cost] using hb

def check (r v code aux lo hi start : ℕ) (p : Piece) : Bool :=
  if code=0 then FinalBaseCheck6815.check r v aux lo hi start p
  else if code≤8 then phaseCheck r v (code-1) lo hi start p
  else if code=9 then terminalCheck r v lo hi start p
  else if code≤13 then exactCheck r v (code-7) lo hi start p else false

theorem check_sound (r v code aux lo hi start : ℕ) (p : Piece)
    (h : check r v code aux lo hi start p=true) (z : ℕ)
    (hz : lo≤z) (hh : z≤hi) (hs : start≤lo)
    (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (ht : r+v+z≤11192) :
    RuleBound r v z (value p start z) := by
  unfold check at h
  split_ifs at h with h0 h8 h9 h13
  · exact Or.inl (FinalBaseCheck6815.check_sound _ _ _ _ _ _ p h z hz hh hs ht)
  · exact phaseCheck_sound _ _ _ _ _ _ p h z hz hh hs hr hR hy ht
  · exact terminalCheck_sound _ _ _ _ _ p h z hz hh hs hr hR hy ht
  · exact exactCheck_sound _ _ _ _ _ _ p h z hz hh hs hr hR hy ht

end ProximityPrize.SubmissionLower.FinalRuleCheck6815
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.FinalRulesRowCheck6815
open FinalCurves6815 FinalRuleCheck6815
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def decodeAux : ℕ → ℕ → List Piece
  | 0,_ => []
  | n+1,code =>
    let digits := code/262144%1024
    let payload := code/268435456
    ⟨code%16384,code/16384%16,payload%(16^digits)⟩ :: decodeAux n (payload/(16^digits))
def decode (code : ℕ) := decodeAux (code%65536) (code/65536)

def pair (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) : Bool :=
  let lo := max rlo start
  let stop := min rule.stop p.stop
  if lo<stop then check r v rule.base rule.slope lo (stop-1) start p else true

def checkRow (r v : ℕ) (curve rules : List Piece) : Bool :=
  validFrom (11193-r-v) 0 rules && allCells (fun lo rule => allCells (pair r v lo rule) 0 curve) 0 rules

def get (ps : List Piece) (i : ℕ) : Piece := (ps[i]?).getD ⟨0,0,0⟩
def startAt (start : ℕ) (ps : List Piece) (i : ℕ) : ℕ :=
  if i=0 then start else (get ps (i-1)).stop

theorem allCells_of_indices (test : ℕ → Piece → Bool) (start : ℕ) (ps : List Piece)
    (h : ∀ i, i<ps.length → test (startAt start ps i) (get ps i)=true) :
    allCells test start ps=true := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    simp only [allCells,Bool.and_eq_true]
    constructor
    · simpa [startAt,get] using h 0 (by simp)
    · apply ih
      intro i hi
      have hh := h (i+1) (by simpa using hi)
      cases i with
      | zero => simpa [startAt,get] using hh
      | succ i => simpa [startAt,get,Nat.add_assoc] using hh

def indexCheck (r v : ℕ) (curve rules : List Piece) (i : ℕ) : Bool :=
  if i<rules.length then allCells (pair r v (startAt 0 rules i) (get rules i)) 0 curve else true
def blockCheck (r v : ℕ) (curve rules : List Piece) (b : ℕ) : Bool :=
  SingletonCertificate6815.allN (fun j => indexCheck r v curve rules (8*b+j)) 8

theorem allN_complete (test : ℕ → Bool) (n : ℕ) (h : ∀ i, i<n → test i=true) :
    SingletonCertificate6815.allN test n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [SingletonCertificate6815.allN,Bool.and_eq_true]
    exact ⟨ih (fun i hi => h i (by omega)),h n (by omega)⟩

theorem block_of_indices (r v : ℕ) (curve rules : List Piece) (b : ℕ)
    (h : ∀ i, i<8 → indexCheck r v curve rules (8*b+i)=true) :
    blockCheck r v curve rules b=true := allN_complete _ 8 h

theorem of_blocks (r v : ℕ) (curve rules : List Piece) (n : ℕ)
    (hv : validFrom (11193-r-v) 0 rules=true) (hn : rules.length≤8*n)
    (hc : ∀ b, b<n → blockCheck r v curve rules b=true) :
    checkRow r v curve rules=true := by
  simp only [checkRow,Bool.and_eq_true]
  refine ⟨hv,allCells_of_indices _ 0 rules ?_⟩
  intro i hi
  have hb : i/8<n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have h := SingletonCertificate6815.allN_sound _ 8 (hc (i/8) hb) (i%8) (Nat.mod_lt _ (by decide))
  rw [Nat.div_add_mod] at h
  simpa only [indexCheck,if_pos hi] using h

theorem row_sound (r v : ℕ) (curve rules : List Piece)
    (hv : validFrom (11193-r-v) 0 curve=true) (hc : checkRow r v curve rules=true)
    (hr : 1≤r) (hR : r≤39) (hy : r+v≤182) (z : ℕ) (ht : r+v+z≤11192) :
    RuleBound r v z (eval curve z) := by
  simp only [checkRow,Bool.and_eq_true] at hc
  obtain ⟨rlo,rule,hrlo,hrhi,_,hrule⟩ := cell_at _ 0 (11193-r-v) rules hc.1
    (allCells_sound _ 0 rules hc.2) z (Nat.zero_le _) (by omega)
  obtain ⟨start,p,hstart,hpstop,he,hp⟩ := cell_at _ 0 (11193-r-v) curve hv
    (allCells_sound _ 0 curve hrule) z (Nat.zero_le _) (by omega)
  have hn : max rlo start<min rule.stop p.stop := by omega
  simp only [pair,if_pos hn] at hp
  have h := check_sound r v rule.base rule.slope (max rlo start) (min rule.stop p.stop-1) start p hp z
    (by omega) (by omega) (le_max_right _ _) hr hR hy ht
  simpa only [eval,he] using h

end ProximityPrize.SubmissionLower.FinalRulesRowCheck6815
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.FinalRulesFast6815
open FinalCurves6815 FinalRulesRowCheck6815 FinalRuleCheck6815 FinalRemovalAlgebra6815
open FinalPayment6815 FinalBaseCheck6815 PackingData6815
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def allK (test : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec true (fun i ih => Bool.rec false (test i) ih) n
theorem allK_eq (test : ℕ → Bool) (n : ℕ) : allK test n=SingletonCertificate6815.allN test n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec false (test n) (allK test n)=(SingletonCertificate6815.allN test n && test n)
    rw [ih]
    cases SingletonCertificate6815.allN test n <;> rfl

def cellsK (test : ℕ → Piece → Bool) (ps : List Piece) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun p _ ih start => Bool.rec false (ih p.stop) (test start p)) ps
theorem cellsK_eq (test : ℕ → Piece → Bool) (ps : List Piece) (start : ℕ) :
    cellsK test ps start=allCells test start ps := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    change Bool.rec false (cellsK test ps p.stop) (test start p)=(test start p && allCells test p.stop ps)
    rw [ih]
    cases test start p <;> rfl

def exactChildK (r v j lo hi start : ℕ) (p : Piece) (q u : ℕ) : Bool :=
  cellsK (exactPieceCheck (src j).totalCap (src j).middleCap (src j).slopeCap (r-q) ((r-q)+(v-u))
    lo hi start p (fastCut q u j)) (FinalLookup6815.final q u) 0
theorem exactChildK_eq (r v j lo hi start : ℕ) (p : Piece) (q u : ℕ) :
    exactChildK r v j lo hi start p q u=exactChild r v j lo hi start p q u := by
  simp only [exactChildK,exactChild,exactChildCheck,cellsK_eq]

def exactK (r v j lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt j 7 && Nat.ble (fastCut r v j) lo && exactEmpty r v j lo hi start p &&
    allK (fun i => allK (fun u => exactChildK r v j lo hi start p (i+1) u) (v+1)) (r-1)
theorem exactK_eq (r v j lo hi start : ℕ) (p : Piece) : exactK r v j lo hi start p=exactCheck r v j lo hi start p := by
  simp only [exactK,exactCheck,allK_eq,exactChildK_eq]

def childK (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) : Bool :=
  cellsK (childPiece slope charge lo hi start p) child 0
theorem childK_eq (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) :
    childK slope charge lo hi start p child=childCheck slope charge lo hi start p child := by
  simp only [childK,childCheck,cellsK_eq]

def heavyK (r v code lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt (digit code 0) 14 && lineCheck (light_slope (digit code 0)) (lightNum (digit code 0) r v) lo hi start p &&
  allK (fun i => allK (fun u =>
    let q := i+10
    let j := heavyChoice code v q u
    Nat.blt j 14 && childK (light_slope j) (lightNum j (r-q) (v-u)) lo hi start p
      (FinalLookup6815.single q u).curve) (v+1)) (r-9)
theorem heavyK_eq (r v code lo hi start : ℕ) (p : Piece) : heavyK r v code lo hi start p=heavyCheck r v code lo hi start p := by
  simp only [heavyK,heavyCheck,allK_eq,childK_eq]

def baseK (r v aux lo hi start : ℕ) (p : Piece) : Bool :=
  if aux<8 then lineCheck (full_slope aux) (fullNum aux r v) lo hi start p
  else decide (aux%16=15 ∧ 10≤r ∧ r≤19 ∧ v≤70 ∧ hi≤4500) && heavyK r v (aux/16) lo hi start p
theorem baseK_eq (r v aux lo hi start : ℕ) (p : Piece) : baseK r v aux lo hi start p=FinalBaseCheck6815.check r v aux lo hi start p := by
  simp only [baseK,FinalBaseCheck6815.check,heavyK_eq]

def ruleK (r v code aux lo hi start : ℕ) (p : Piece) : Bool :=
  if code=0 then baseK r v aux lo hi start p
  else if code≤8 then phaseCheck r v (code-1) lo hi start p
  else if code=9 then terminalCheck r v lo hi start p
  else if code≤13 then exactK r v (code-7) lo hi start p else false
theorem ruleK_eq (r v code aux lo hi start : ℕ) (p : Piece) : ruleK r v code aux lo hi start p=FinalRuleCheck6815.check r v code aux lo hi start p := by
  simp only [ruleK,FinalRuleCheck6815.check,baseK_eq,exactK_eq]

def pairK (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) : Bool :=
  let lo := max rlo start
  let stop := min rule.stop p.stop
  if lo<stop then ruleK r v rule.base rule.slope lo (stop-1) start p else true
theorem pairK_eq (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) : pairK r v rlo rule start p=pair r v rlo rule start p := by
  simp only [pairK,pair,ruleK_eq]

def indexK (r v : ℕ) (curve rules : List Piece) (i : ℕ) : Bool :=
  if i<rules.length then cellsK (pairK r v (startAt 0 rules i) (get rules i)) curve 0 else true
theorem indexK_eq (r v : ℕ) (curve rules : List Piece) (i : ℕ) : indexK r v curve rules i=indexCheck r v curve rules i := by
  have he := funext (fun start => funext (fun p => pairK_eq r v (startAt 0 rules i) (get rules i) start p))
  simp only [indexK,indexCheck,cellsK_eq,he]

end ProximityPrize.SubmissionLower.FinalRulesFast6815
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.FinalRulesCapped6815
open FinalCurves6815 FinalRulesRowCheck6815 FinalRuleCheck6815 FinalRemovalAlgebra6815
open FinalPayment6815 FinalBaseCheck6815 PackingData6815 FinalRulesFast6815
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def cellsAux (limit : ℕ) (test : ℕ → Piece → Bool) (ps : List Piece) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun p _ ih start => if limit≤start then true else Bool.rec false (ih p.stop) (test start p)) ps
def cells (limit : ℕ) (test : ℕ → Piece → Bool) (ps : List Piece) (start : ℕ) : Bool :=
  if limit≤start then true else cellsAux limit test ps start

theorem after_limit (limit : ℕ) (test : ℕ → Piece → Bool) (ps : List Piece) (start finish : ℕ)
    (hv : validFrom finish start ps=true) (hstart : limit≤start)
    (htrue : ∀ lo p, limit≤lo → test lo p=true) : cellsK test ps start=true := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    simp only [validFrom,Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq] at hv
    change Bool.rec false (cellsK test ps p.stop) (test start p)=true
    rw [htrue start p hstart,ih p.stop hv.2 (by omega)]

theorem cellsAux_eq (limit : ℕ) (test : ℕ → Piece → Bool) (ps : List Piece) (start finish : ℕ)
    (hv : validFrom finish start ps=true)
    (htrue : ∀ lo p, limit≤lo → test lo p=true) : cellsAux limit test ps start=cellsK test ps start := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih =>
    by_cases hs : limit≤start
    · change (if limit≤start then true else _)=cellsK test (p::ps) start
      rw [if_pos hs,after_limit limit test (p::ps) start finish hv hs htrue]
    · simp only [validFrom,Bool.and_eq_true] at hv
      change (if limit≤start then true else Bool.rec false (cellsAux limit test ps p.stop) (test start p))=_
      rw [if_neg hs,ih p.stop hv.2]
      rfl

theorem cells_eq (limit : ℕ) (test : ℕ → Piece → Bool) (ps : List Piece) (start finish : ℕ)
    (hv : validFrom finish start ps=true)
    (htrue : ∀ lo p, limit≤lo → test lo p=true) : cells limit test ps start=cellsK test ps start := by
  unfold cells
  split_ifs with h
  · rw [after_limit limit test ps start finish hv h htrue]
  · exact cellsAux_eq limit test ps start finish hv htrue

theorem allK_congr (a b : ℕ → Bool) (n : ℕ) (h : ∀ i, i<n → a i=b i) : allK a n=allK b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (a n) (allK a n)=Bool.rec false (b n) (allK b n)
    rw [h n (by omega),ih (fun i hi => h i (by omega))]

def exactChildC (r v j lo hi start : ℕ) (p : Piece) (q u : ℕ) : Bool :=
  cells (min (fastCut q u j) (hi+1))
    (exactPieceCheck (src j).totalCap (src j).middleCap (src j).slopeCap (r-q) ((r-q)+(v-u))
      lo hi start p (fastCut q u j)) (FinalLookup6815.final q u) 0

theorem exactChildC_eq (r v j lo hi start : ℕ) (p : Piece) (q u : ℕ)
    (hq : 1≤q) (hQ : q≤39) (hy : q+u≤182) :
    exactChildC r v j lo hi start p q u=exactChildK r v j lo hi start p q u := by
  unfold exactChildC exactChildK
  apply cells_eq _ _ _ 0 (11193-q-u)
  · rw [FinalLookup6815.final_eq q u hq hQ]
    exact FinalPrefixSound6815.curve_valid q u hq hQ hy
  · intro clo c hc
    unfold exactPieceCheck
    split_ifs with hvalid
    · unfold TriangularAffine6815.check
      have hn : ¬(clo≤min c.stop (fastCut q u j)-1 ∧ max lo clo≤hi) := by omega
      rw [if_neg hn]
    · rfl

def exactC (r v j lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt j 7 && Nat.ble (fastCut r v j) lo && exactEmpty r v j lo hi start p &&
    allK (fun i => allK (fun u => exactChildC r v j lo hi start p (i+1) u) (v+1)) (r-1)
theorem exactC_eq (r v j lo hi start : ℕ) (p : Piece) (hR : r≤39) (hy : r+v≤182) :
    exactC r v j lo hi start p=exactK r v j lo hi start p := by
  unfold exactC exactK
  congr 1
  apply allK_congr
  intro i hindex
  apply allK_congr
  intro u hu
  exact exactChildC_eq r v j lo hi start p (i+1) u (by omega) (by omega) (by omega)

def childC (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) : Bool :=
  cells (hi+1) (childPiece slope charge lo hi start p) child 0
theorem childC_eq (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) (finish : ℕ)
    (hv : validFrom finish 0 child=true) : childC slope charge lo hi start p child=childK slope charge lo hi start p child := by
  unfold childC childK
  apply cells_eq _ _ _ 0 finish hv
  intro clo c hc
  unfold childPiece TriangularAffine6815.check
  have hn : ¬(clo≤c.stop-1 ∧ max lo clo≤hi) := by omega
  rw [if_neg hn]

def heavyC (r v code lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt (digit code 0) 14 && lineCheck (light_slope (digit code 0)) (lightNum (digit code 0) r v) lo hi start p &&
  allK (fun i => allK (fun u =>
    let q := i+10
    let j := heavyChoice code v q u
    Nat.blt j 14 && childC (light_slope j) (lightNum j (r-q) (v-u)) lo hi start p
      (FinalLookup6815.single q u).curve) (v+1)) (r-9)
theorem heavyC_eq (r v code lo hi start : ℕ) (p : Piece) (hR : r≤39) (hy : r+v≤182) :
    heavyC r v code lo hi start p=heavyK r v code lo hi start p := by
  unfold heavyC heavyK
  congr 1
  apply allK_congr
  intro i hindex
  apply allK_congr
  intro u hu
  dsimp only
  congr 1
  apply childC_eq _ _ lo hi start p _ (11193-(i+10)-u)
  have he := congrArg SingletonCertificate6815.Row.curve (FinalLookup6815.single_eq (i+10) u (by omega) (by omega))
  rw [he]
  exact PackingOwnCheck6815.curve_valid _ _ (by omega) (by omega) (by omega)

def baseC (r v aux lo hi start : ℕ) (p : Piece) : Bool :=
  if aux<8 then lineCheck (full_slope aux) (fullNum aux r v) lo hi start p
  else decide (aux%16=15 ∧ 10≤r ∧ r≤19 ∧ v≤70 ∧ hi≤4500) && heavyC r v (aux/16) lo hi start p
theorem baseC_eq (r v aux lo hi start : ℕ) (p : Piece) (hR : r≤39) (hy : r+v≤182) : baseC r v aux lo hi start p=baseK r v aux lo hi start p := by
  simp only [baseC,baseK,heavyC_eq r v _ lo hi start p hR hy]

def ruleC (r v code aux lo hi start : ℕ) (p : Piece) : Bool :=
  if code=0 then baseC r v aux lo hi start p
  else if code≤8 then phaseCheck r v (code-1) lo hi start p
  else if code=9 then terminalCheck r v lo hi start p
  else if code≤13 then exactC r v (code-7) lo hi start p else false
theorem ruleC_eq (r v code aux lo hi start : ℕ) (p : Piece) (hR : r≤39) (hy : r+v≤182) : ruleC r v code aux lo hi start p=ruleK r v code aux lo hi start p := by
  simp only [ruleC,ruleK,baseC_eq r v aux lo hi start p hR hy,exactC_eq r v _ lo hi start p hR hy]

def pairC (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) : Bool :=
  let lo := max rlo start
  let stop := min rule.stop p.stop
  if lo<stop then ruleC r v rule.base rule.slope lo (stop-1) start p else true
theorem pairC_eq (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) (hR : r≤39) (hy : r+v≤182) : pairC r v rlo rule start p=pairK r v rlo rule start p := by
  simp only [pairC,pairK,ruleC_eq r v _ _ _ _ start p hR hy]

def indexC (r v : ℕ) (curve rules : List Piece) (i : ℕ) : Bool :=
  if i<rules.length then cellsK (pairC r v (startAt 0 rules i) (get rules i)) curve 0 else true
theorem indexC_eq (r v : ℕ) (curve rules : List Piece) (i : ℕ) (hR : r≤39) (hy : r+v≤182) : indexC r v curve rules i=indexCheck r v curve rules i := by
  rw [←indexK_eq]
  have he := funext (fun start => funext (fun p => pairC_eq r v (startAt 0 rules i) (get rules i) start p hR hy))
  simp only [indexC,indexK,he]

def blockC (r v : ℕ) (curve rules : List Piece) (b : ℕ) : Bool :=
  allK (fun j => indexC r v curve rules (8*b+j)) 8
theorem blockC_eq (r v : ℕ) (curve rules : List Piece) (b : ℕ) (hR : r≤39) (hy : r+v≤182) : blockC r v curve rules b=blockCheck r v curve rules b := by
  simp only [blockC,blockCheck,allK_eq,indexC_eq r v curve rules _ hR hy]

end ProximityPrize.SubmissionLower.FinalRulesCapped6815
end MergedPart8
