import ProximityPrize.SubmissionBinaryLower.B6402GridRouting
import ProximityPrize.SubmissionBinaryLower.B6402PricedCell

namespace ProximityPrize.SubmissionBinaryLower.B6402BucketBudget
open B6401Params hiding A
open B6402GridProfile B6402GridRouting B6402PricedCell B6402RectCover
open B6402Table4Common B6402IntFarkas
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

def singleBudget (q : ℕ) : ℕ := if q=1 then 1515102683476236048 else 1536625616049505072
def groupBudget (r : Fin 5) (q : ℕ) : ℕ :=
  match r.val with
  | 0 => 3200000000000000000*q
  | 1 => 2100000000000000000*q
  | 2 => 1250000000000000000*q
  | 3 => if q=1 then 65682344667889283 else 66615564190764881
  | _ => if q=1 then 36831301134248129 else 37339926120107219

def budget (k : Key) (q : ℕ) : ℕ :=
  if k.gap=single then singleBudget q else
  if k.gap=B6401T4Grid.std5Bounds 0 then groupBudget 0 q else
  if k.gap=B6401T4Grid.std5Bounds 1 then groupBudget 1 q else
  if k.gap=B6401T4Grid.std5Bounds 2 then groupBudget 2 q else
  if k.gap=B6401T4Grid.std5Bounds 3 then groupBudget 3 q else groupBudget 4 q

def gapHi (k : Key) : ℚ := (k.gap.2.2.1:ℚ)/k.gap.2.2.2

theorem standard (k : Key) (r : Fin 5) (q : ℕ) (e : k.gap=B6401T4Grid.std5Bounds r) :
    budget k q=groupBudget r q := by
  unfold budget; rw [e]; fin_cases r <;> rfl

theorem totals : singleBudget 1+(∑ r : Fin 5,groupBudget r 1)=8167616329278373460 ∧
    singleBudget 2+(∑ r : Fin 5,groupBudget r 2)=14740581106360377172 := by decide +kernel

def Ordinary (k : Key) (q : ℕ) : Prop :=
  ∃ b : T4BucketCert,checkT4Bucket (arity k.branch) (rows k).1 (rows k).2 k.cLoNum k.cLoDen k.cHiNum k.cHiDen b=true ∧
    (b.loGNum,b.loGDen,b.hiGNum,b.hiGDen)=k.gap ∧
    (b.m=0 ∨ (b.m≤3000 ∧ b.s≤300 ∧
      (let w:=if q=1 then b.cap1 else b.cap2
       w.c1Bkt*1811+w.c0Bkt≤budget k q ∧ (b.hiGNum=b.hiGDen → w.useP64=false))))

def Replacement (k : Key) (q : ℕ) : Prop :=
  ∀ (hn : 5≤arity k.branch) (x : Fin (arity k.branch) → ℚ) (v : ℚ),
    (∀ i,0≤x i) → 0≤v → x ⟨2,by omega⟩≤1 → lo k≤x ⟨arity k.branch-1,by omega⟩ →
    x ⟨arity k.branch-1,by omega⟩≤hi k → hi k≤28/5 →
    v≤x ⟨2,by omega⟩ → 2097152*v≤(x ⟨arity k.branch-1,by omega⟩-5)*1048575+1 →
    (∀ r∈(rows k).1.toList,RowValid (arity k.branch) r ∧ RowSatLe x r) →
    (∀ r∈(rows k).2.toList,RowValid (arity k.branch) r ∧ RowSatEq x r) →
    ∃ (p : Prepared) (box : Box), Contains box (x ⟨2,by omega⟩) (x ⟨arity k.branch-1,by omega⟩) v ∧
       numerical p box q (budget k q) (gapHi k)=true ∧ Funds hn x v p

theorem replaced (k : Key) (q : ℕ) (boxes : Array Box)
    (cover : ∀ a c v, Contains ⟨⟨0,1⟩,⟨lo k,hi k⟩,⟨0,1/3⟩⟩ a c v → ∃ i : Fin boxes.size,Contains boxes[i] a c v)
    (bank : ∀ i : Fin boxes.size,Receipt (arity k.branch) (B6402PriceCells.cell (rows k).1 (rows k).2 (arity k.branch) boxes[i])
        boxes[i] q (budget k q) (gapHi k)) : Replacement k q := by
  intro hn x v hx hv hp cl ch global sub deg hu he
  have vh : v≤1/3 := by linarith only [deg,ch,global]
  exact from_cover hn x v _ _ _ boxes q _ _ cover bank hx hv hu he
    ⟨⟨hx _,hp⟩,⟨cl,ch⟩,hv,vh⟩ sub deg

#print axioms totals
#print axioms replaced
end ProximityPrize.SubmissionBinaryLower.B6402BucketBudget
