import ProximityPrize.SubmissionLower.FinalRulesRowCheck6815
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
