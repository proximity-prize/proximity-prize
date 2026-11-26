import ProximityPrize.SubmissionBinaryLower.B6402CellBounds
import ProximityPrize.SubmissionBinaryLower.B6402PriceTarget
import ProximityPrize.SubmissionBinaryLower.B6402PriceCells

/-! A cell stores closed numerical endpoints. Its soundness theorem extends
both endpoint inequalities to the actual mixed degree of the fixed factor. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402PricedCell
open B6401Params hiding A
open B6402RectCover B6402LinearCertificate B6402PriceRows B6402PriceCells
open B6402EndpointBudget B6402PriceTarget B6402CellBounds B6402IntFarkas
set_option autoImplicit false
set_option maxHeartbeats 1600000

structure Prepared where
  plan : Plan
  side : Side
  low : ℚ
  high : ℚ
  w : CapWitness
  lowValue : Values
  highValue : Values

def numerical (p : Prepared) (box : Box) (q price : ℕ) (gapHi : ℚ) : Bool :=
  valid p.plan p.side && Binary6402NativeCaps.allowance (p.plan.m-p.plan.b) p.side.ordinate p.side.spatial p.side.delta
    q p.plan.cap price p.w &&
  decide (p.plan.q=q ∧ p.plan.lo=box.c.lo ∧ p.plan.hi=box.c.hi ∧ p.plan.lo<p.plan.hi ∧
     (p.side.least:ℚ)-1<p.low*N ∧ p.high*N<(p.side.mostBad:ℚ)+1 ∧ p.plan.hi*wY≤p.plan.WFhi ∧
     (p.plan.s:ℚ)*gapHi*N<(p.side.gap0:ℚ)+1 ∧ p.plan.WFhi≤p.plan.W ∧ gapHi<1)

structure Correct (p : Prepared) : Prop where
  atLow : values p.plan (5*p.plan.q)=p.lowValue
  atHigh : values p.plan (1811+p.plan.q)=p.highValue

def targetLo (p : Prepared) := one 2 (-1) (-p.low)
def targetHi (p : Prepared) (n : ℕ) := one n 1 p.high

structure Weights4 where
  lowSites : Weights
  highBad : Weights
  lowHeight : Weights
  highHeight : Weights

def paid (n : ℕ) (src : Array Row) (p : Prepared) (w : Weights4) : Bool :=
  certifies (n+1) src w.lowSites (targetLo p) false &&
  certifies (n+1) src w.highBad (targetHi p n) false &&
  certifies (n+1) src w.lowHeight (p.lowValue.row n) true &&
  certifies (n+1) src w.highHeight (p.highValue.row n) true

def Funds {n : ℕ} (hn : 5≤n) (x : Fin n → ℚ) (v : ℚ) (p : Prepared) : Prop :=
  p.low≤x ⟨2,by omega⟩ ∧ v≤p.high ∧
    ∀ h : ℚ, (5*p.plan.q:ℚ)≤h → h≤(1811+p.plan.q:ℚ) →
    B6402EndpointBudget.lhs p.plan h (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨2,by omega⟩)
      (x ⟨3,by omega⟩) (x ⟨4,by omega⟩) (x ⟨n-1,by omega⟩) v<rhs p.plan h

theorem sound {n : ℕ} (hn : 5≤n) (p : Prepared) (c : Correct p) (w : Weights4) (src : Array Row)
    (hcheck : paid n src p w=true) (x : Fin n → ℚ) (v : ℚ) (hx : ∀ i,0≤x i) (hv : 0≤v)
    (inputs : ∀ r∈src.toList,B6402LinearCertificate.lhs r (extend x v)≤r.bound) :
    Funds hn x v p := by
  have hnon (i : Fin (n+1)) : 0≤extend x v i := by unfold extend; split; exact hx _; exact hv
  simp only [paid,Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨a,b⟩,l⟩,h⟩ := hcheck
  have aa := B6402LinearCertificate.sound src _ _ false a (extend x v) hnon inputs
  have bb := B6402LinearCertificate.sound src _ _ false b (extend x v) hnon inputs
  change B6402LinearCertificate.lhs (targetLo p) (extend x v) ≤ -p.low at aa
  change B6402LinearCertificate.lhs (targetHi p n) (extend x v) ≤ p.high at bb
  rw [row_lhs] at aa bb
  simp only [targetLo,targetHi,one,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    dite_eq_left (by omega : 2<n+1),dite_eq_left (Nat.lt_succ_self n),extend,
    dite_eq_left (by omega : 2<n),dite_eq_right (lt_irrefl n),neg_one_mul,one_mul] at aa bb
  refine ⟨by linarith,bb,?_⟩
  intro t lo hi
  apply between _ _ _ _ _ _ _ _ _ _ _ lo hi
  · have z := B6402LinearCertificate.sound src _ _ true l (extend x v) hnon inputs
    change B6402LinearCertificate.lhs (p.lowValue.row n) (extend x v)<p.lowValue.bound at z
    rw [←c.atLow,objective hn] at z
    exact z
  · have z := B6402LinearCertificate.sound src _ _ true h (extend x v) hnon inputs
    change B6402LinearCertificate.lhs (p.highValue.row n) (extend x v)<p.highValue.bound at z
    rw [←c.atHigh,objective hn] at z
    exact z

theorem impossible {n : ℕ} (src : Array Row) (w : Weights)
    (check : certifies n src w ⟨[],0⟩ true=true) (x : Fin n → ℚ) (nonneg : ∀ i,0≤x i)
    (inputs : ∀ r∈src.toList,B6402LinearCertificate.lhs r x≤r.bound) : False := by
  have h := B6402LinearCertificate.sound src w _ true check x nonneg inputs
  simpa [row_lhs] using h

theorem repack {n : ℕ} (src : Array Row) (ws : Weights) (a : Values) (r : Row)
    (same : represents n r a=true) (checked : certifies (n+1) src ws r true=true) :
    certifies (n+1) src ws (a.row n) true=true := by
  simp only [represents,decide_eq_true_eq] at same
  simp only [certifies,Bool.and_eq_true,decide_eq_true_eq,ite_true] at checked ⊢
  have cols : (∀ i : Fin (n+1), coeff r i.val≤dualCoeff src ws i.val) ↔
      ∀ i : Fin (n+1), coeff (a.row n) i.val≤dualCoeff src ws i.val := by
    constructor <;> intro h i
    · rw [←same.2 i]; exact h i
    · rw [same.2 i]; exact h i
  refine ⟨⟨checked.1.1,cols.mp checked.1.2⟩,?_⟩
  change B6402LinearCertificate.rhs src ws<a.bound
  exact lt_of_lt_of_eq checked.2 same.1

def Receipt (n : ℕ) (src : Array Row) (box : Box) (q budget : ℕ) (gapHi : ℚ) : Prop :=
  (∃ w : Weights,certifies (n+1) src w ⟨[],0⟩ true=true) ∨
  ∃ (p : Prepared) (w : Weights4), numerical p box q budget gapHi=true ∧ Correct p ∧ paid n src p w=true

theorem choose {n : ℕ} (hn : 5≤n) (x : Fin n → ℚ) (v : ℚ)
    (ub eq : Array SparseRow) (box : Box) (q budget : ℕ) (gapHi : ℚ)
    (rc : Receipt n (cell ub eq n box) box q budget gapHi)
    (hx : ∀ i,0≤x i) (hv : 0≤v)
    (hu : ∀ r∈ub.toList,B6402Table4Common.RowValid n r ∧ B6402Table4Common.RowSatLe x r)
    (he : ∀ r∈eq.toList,B6402Table4Common.RowValid n r ∧ B6402Table4Common.RowSatEq x r)
    (inside : Contains box (x ⟨2,by omega⟩) (x ⟨n-1,by omega⟩) v)
    (sub : v≤x ⟨2,by omega⟩) (deg : 2097152*v≤(x ⟨n-1,by omega⟩-5)*1048575+1) :
    ∃ p : Prepared,numerical p box q budget gapHi=true ∧ Funds hn x v p := by
  have all := cell_sound (by omega : 2<n) x v box ub eq hu he inside sub deg
  rcases rc with ⟨w,emp⟩|⟨p,w,ok,correct,checks⟩
  · exfalso
    exact impossible _ w emp (extend x v) (fun i => by unfold extend; split; exact hx _; exact hv) all
  · exact ⟨p,ok,sound hn p correct w _ checks x v hx hv all⟩

theorem from_cover {n : ℕ} (hn : 5≤n) (x : Fin n → ℚ) (v : ℚ) (ub eq : Array SparseRow)
    (domain : Box) (boxes : Array Box) (q budget : ℕ) (gapHi : ℚ)
    (cover : ∀ p c z,Contains domain p c z → ∃ i : Fin boxes.size,Contains boxes[i] p c z)
    (bank : ∀ i : Fin boxes.size, Receipt n (cell ub eq n boxes[i]) boxes[i] q budget gapHi)
    (hx : ∀ i,0≤x i) (hv : 0≤v)
    (hu : ∀ r∈ub.toList,B6402Table4Common.RowValid n r ∧ B6402Table4Common.RowSatLe x r)
    (he : ∀ r∈eq.toList,B6402Table4Common.RowValid n r ∧ B6402Table4Common.RowSatEq x r)
    (inside : Contains domain (x ⟨2,by omega⟩) (x ⟨n-1,by omega⟩) v)
    (sub : v≤x ⟨2,by omega⟩) (deg : 2097152*v≤(x ⟨n-1,by omega⟩-5)*1048575+1) :
    ∃ (p : Prepared) (box : Box), Contains box (x ⟨2,by omega⟩) (x ⟨n-1,by omega⟩) v ∧
      numerical p box q budget gapHi=true ∧ Funds hn x v p := by
  obtain ⟨i,loc⟩ := cover _ _ _ inside
  obtain ⟨p,hnum,hfund⟩ := choose hn x v ub eq boxes[i] q budget gapHi (bank i) hx hv hu he loc sub deg
  exact ⟨p,boxes[i],loc,hnum,hfund⟩

#print axioms sound
#print axioms choose
end ProximityPrize.SubmissionBinaryLower.B6402PricedCell
