import ProximityPrize.SubmissionLower.FinalPayment6815
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
