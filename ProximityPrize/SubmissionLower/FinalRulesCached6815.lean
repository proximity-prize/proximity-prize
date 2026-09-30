import ProximityPrize.SubmissionLower.FinalRulesCapped6815
import ProximityPrize.SubmissionLower.LiteralThresholds6815
import ProximityPrize.SubmissionLower.LiteralFinalCurves6815
import ProximityPrize.SubmissionLower.TriangularKernel6815
namespace ProximityPrize.SubmissionLower.FinalRulesCached6815
open FinalCurves6815 FinalRulesRowCheck6815 FinalRuleCheck6815 FinalRemovalAlgebra6815
open FinalPayment6815 FinalBaseCheck6815 PackingData6815 FinalRulesFast6815 FinalRulesCapped6815
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def sourceNums : ℕ → Lower80899.Oracle.SourceNumbers
  | 0 => Lower80899.SourceSound.Phase00.source
  | 1 => Lower80899.SourceSound.Phase01.source
  | 2 => Lower80899.SourceSound.Phase02.source
  | 3 => Lower80899.SourceSound.Phase03.source
  | 4 => Lower80899.SourceSound.Phase04.source
  | 5 => Lower80899.SourceSound.Phase05.source
  | 6 => Lower80899.SourceSound.Phase06.source
  | n+7 => src (n+7)
theorem sourceNums_eq (j : ℕ) : sourceNums j=src j := by
  by_cases h : j<7
  · interval_cases j <;> rfl
  · obtain ⟨k,hk⟩ : ∃ k, j=k+7 := ⟨j-7,by omega⟩
    rw [hk]
    rfl

def exactPieceL (capL capU capS r y lo hi start : ℕ) (p : Piece) (cut cstart : ℕ) (c : Piece) : Bool :=
  Bool.rec true
    (TriangularKernel6815.triangle
      (50174*c.base+ExactInitialCharge6815.num capL capU capS r y y+1) (50174*c.slope)
      cstart (min c.stop cut-1) 0 (ExactRemovalPhase6815.tSlope capL capU capS r y)
      (50174*(value p start lo+1)) (50174*p.slope) lo hi)
    (Nat.blt cstart (min c.stop cut))
theorem exactPieceL_eq (capL capU capS r y lo hi start : ℕ) (p : Piece) (cut cstart : ℕ) (c : Piece) :
    exactPieceL capL capU capS r y lo hi start p cut cstart c=exactPieceCheck capL capU capS r y lo hi start p cut cstart c := by
  by_cases h : cstart<min c.stop cut
  · have hb : Nat.blt cstart (min c.stop cut)=true := by simpa only [Nat.blt_eq] using h
    simp only [exactPieceL,hb,exactPieceCheck,if_pos h,TriangularKernel6815.triangle_eq]
  · have hb : Nat.blt cstart (min c.stop cut)=false := by
      apply Bool.eq_false_iff.mpr
      intro he
      apply h
      simpa only [Nat.blt_eq] using he
    simp only [exactPieceL,hb,exactPieceCheck,if_neg h]

def childL (r v j lo hi start : ℕ) (p : Piece) (q u : ℕ) : Bool :=
  cells (min (LiteralThresholds6815.cut q u j) (hi+1))
    (fun cstart c => exactPieceL (sourceNums j).totalCap (sourceNums j).middleCap (sourceNums j).slopeCap (r-q) ((r-q)+(v-u))
      lo hi start p (LiteralThresholds6815.cut q u j) cstart c) (LiteralFinalCurves6815.curve q u) 0
theorem childL_eq (r v j lo hi start : ℕ) (p : Piece) (q u : ℕ) : childL r v j lo hi start p q u=exactChildC r v j lo hi start p q u := by
  simp only [childL,exactChildC,exactPieceL_eq,LiteralThresholds6815.cut_eq,LiteralFinalCurves6815.curve_eq,sourceNums_eq]

def exactL (r v j lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt j 7 && Nat.ble (fastCut r v j) lo && exactEmpty r v j lo hi start p &&
    allK (fun i => allK (fun u => childL r v j lo hi start p (i+1) u) (v+1)) (r-1)
theorem exactL_eq (r v j lo hi start : ℕ) (p : Piece) : exactL r v j lo hi start p=exactC r v j lo hi start p := by
  simp only [exactL,exactC,childL_eq]

def childP (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) : Bool :=
  cells (hi+1) (fun clo c => TriangularKernel6815.triangle c.base c.slope clo (c.stop-1) charge slope
    (value p start lo) p.slope lo hi) child 0
theorem childP_eq (slope charge lo hi start : ℕ) (p : Piece) (child : List Piece) :
    childP slope charge lo hi start p child=childC slope charge lo hi start p child := by
  simp only [childP,childC,childPiece,TriangularKernel6815.triangle_eq]
  rfl

def heavyP (r v code lo hi start : ℕ) (p : Piece) : Bool :=
  Nat.blt (digit code 0) 14 && lineCheck (light_slope (digit code 0)) (lightNum (digit code 0) r v) lo hi start p &&
  allK (fun i => allK (fun u =>
    let q := i+10
    let j := heavyChoice code v q u
    Nat.blt j 14 && childP (light_slope j) (lightNum j (r-q) (v-u)) lo hi start p
      (FinalLookup6815.single q u).curve) (v+1)) (r-9)
theorem heavyP_eq (r v code lo hi start : ℕ) (p : Piece) : heavyP r v code lo hi start p=heavyC r v code lo hi start p := by
  simp only [heavyP,heavyC,childP_eq]
def baseP (r v aux lo hi start : ℕ) (p : Piece) : Bool :=
  if aux<8 then lineCheck (full_slope aux) (fullNum aux r v) lo hi start p
  else decide (aux%16=15 ∧ 10≤r ∧ r≤19 ∧ v≤70 ∧ hi≤4500) && heavyP r v (aux/16) lo hi start p
theorem baseP_eq (r v aux lo hi start : ℕ) (p : Piece) : baseP r v aux lo hi start p=baseC r v aux lo hi start p := by
  simp only [baseP,baseC,heavyP_eq]

def ruleL (r v code aux lo hi start : ℕ) (p : Piece) : Bool :=
  if code=0 then baseP r v aux lo hi start p
  else if code≤8 then phaseCheck r v (code-1) lo hi start p
  else if code=9 then terminalCheck r v lo hi start p
  else if code≤13 then exactL r v (code-7) lo hi start p else false
theorem ruleL_eq (r v code aux lo hi start : ℕ) (p : Piece) : ruleL r v code aux lo hi start p=ruleC r v code aux lo hi start p := by
  simp only [ruleL,ruleC,exactL_eq,baseP_eq]

def pairL (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) : Bool :=
  let lo := max rlo start
  let stop := min rule.stop p.stop
  if lo<stop then ruleL r v rule.base rule.slope lo (stop-1) start p else true
theorem pairL_eq (r v rlo : ℕ) (rule : Piece) (start : ℕ) (p : Piece) : pairL r v rlo rule start p=pairC r v rlo rule start p := by
  simp only [pairL,pairC,ruleL_eq]

def indexL (r v : ℕ) (curve rules : List Piece) (i : ℕ) : Bool :=
  if i<rules.length then cellsK (pairL r v (startAt 0 rules i) (get rules i)) curve 0 else true
theorem indexL_eq (r v : ℕ) (curve rules : List Piece) (i : ℕ) (hR : r≤39) (hy : r+v≤182) : indexL r v curve rules i=indexCheck r v curve rules i := by
  rw [←indexC_eq r v curve rules i hR hy]
  have he := funext (fun start => funext (fun p => pairL_eq r v (startAt 0 rules i) (get rules i) start p))
  simp only [indexL,indexC,he]

def blockL (r v : ℕ) (curve rules : List Piece) (b : ℕ) : Bool :=
  allK (fun j => indexL r v curve rules (8*b+j)) 8
theorem blockL_eq (r v : ℕ) (curve rules : List Piece) (b : ℕ) (hR : r≤39) (hy : r+v≤182) : blockL r v curve rules b=blockCheck r v curve rules b := by
  simp only [blockL,blockCheck,allK_eq,indexL_eq r v curve rules _ hR hy]

end ProximityPrize.SubmissionLower.FinalRulesCached6815
