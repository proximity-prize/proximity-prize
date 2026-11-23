import ProximityPrize.SubmissionLower.KoalaGateCheck

set_option autoImplicit false
set_option Elab.async false

namespace KoalaGateCheck
open FadicGate Finset
open KoalaWeightedRate (Envelope)
open scoped BigOperators

private abbrev S : ℕ := 406807694511
private abbrev Plain := ℕ → ℕ × ℕ × ℕ
private abbrev Boxes := ℕ → List Entry

private def level (h : ℕ) (p : Envelope) (plain : Plain) (boxes : Boxes) (i : ℕ) : ℤ :=
  varLevelLoss (S : ℤ) h p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow
    p.taperHigh (plain (i+1)) (boxes (i+1))

def lossChunk (h : ℕ) (p : Envelope) (plain : Plain) (boxes : Boxes) (i n : ℕ) : ℕ :=
  rPrefix (fun j =>
    let r := i+j+1
    rVarLevelLoss S h p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow
      p.taperHigh (plain r).1 (plain r).2.1 (plain r).2.2 (boxes r)) n

private theorem lossChunk_cast (h : ℕ) (p : Envelope) (plain : Plain) (boxes : Boxes) (i n : ℕ) :
    (lossChunk h p plain boxes i n : ℤ) = ∑ j ∈ range n, level h p plain boxes (i+j) := by
  rw [lossChunk, rPrefix_cast]
  apply sum_congr rfl
  intro j _
  exact rVarLevelLoss_cast S h p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow
    p.taperHigh (plain (i+j+1)).1 (plain (i+j+1)).2.1 (plain (i+j+1)).2.2 (boxes (i+j+1))

def LossSum (h : ℕ) (p : Envelope) (plain : Plain) (boxes : Boxes) (n v : ℕ) : Prop :=
  ∑ i ∈ range n, level h p plain boxes i = (v : ℤ)

theorem LossSum.empty (h : ℕ) (p : Envelope) (plain : Plain) (boxes : Boxes) :
    LossSum h p plain boxes 0 0 := by simp [LossSum]

theorem LossSum.append {h : ℕ} {p : Envelope} {plain : Plain} {boxes : Boxes} {i v : ℕ}
    (last : LossSum h p plain boxes i v) (n w : ℕ)
    (next : lossChunk h p plain boxes i n = w) : LossSum h p plain boxes (i+n) (v+w) := by
  unfold LossSum at *
  rw [sum_range_add, last, ← lossChunk_cast, next, Nat.cast_add]

theorem loss_of_chunks (h : ℕ) (p : Envelope) (t : ℕ) (plain : Plain) (boxes : Boxes)
    (v N : ℕ) (ht : 0 < t) (hh : 0 < h) (checked : LossSum h p plain boxes (t-1) v) :
    Bound p t plain boxes v N := by
  let f := varCertLoss (S : ℤ) h p.widthLow p.widthHigh p.indexLow p.indexHigh
    p.topLow p.taperLow p.taperHigh t plain boxes
  have last : f (t-1) = 0 := by
    unfold f varCertLoss
    exact if_pos (by omega)
  have total : ∑ i ∈ range t, f i = (v : ℤ) := by
    conv_lhs => rw [show t = (t-1)+1 by omega, sum_range_succ]
    rw [last, add_zero]
    refine (sum_congr rfl fun i hi => ?_).trans checked
    unfold f varCertLoss
    rw [if_neg (by have := mem_range.mp hi; omega)]
    rfl
  exact loss_of_varCert (S : ℤ) h p.widthLow p.widthHigh p.indexLow p.indexHigh
    p.topLow p.taperLow p.taperHigh t plain boxes (v : ℤ) hh total N

end KoalaGateCheck
#print axioms KoalaGateCheck.loss_of_chunks
