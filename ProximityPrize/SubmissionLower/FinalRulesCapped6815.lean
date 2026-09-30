import ProximityPrize.SubmissionLower.FinalRulesFast6815
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
