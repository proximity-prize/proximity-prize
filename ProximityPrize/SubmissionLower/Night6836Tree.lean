/- Apache-2.0. The certified owner partition follows BitWonka's tree checker.
   A shared leaf retains its multiplicity and the window-independent band proof. -/
import ProximityPrize.SubmissionLower.P33Base
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Night6836Tree
open DR PA P33
set_option autoImplicit false
set_option maxHeartbeats 3000000
structure Receipt where
  m : ℕ
  code : ℕ
  key : ℕ
  band : P33.bandTest m code = true
inductive Partition where
  | empty : Partition
  | leaf (receipt : Receipt) : Partition
  | node (axis : Fin 4) (pivot : ℕ) (left right : Partition) : Partition

structure Height (W:P33.Window) where
  b : ℕ
  c : ℕ
  cert : FormalR.H2.Certificate W.r W.y W.low b c W.qd W.nh

def reheight (W : P33.Window) (h : Height W) : P33.Window :=
  {W with Bh := h.b, Ch := h.c}

def check (W : P33.Window) (pick : ℕ → Height W) (m : ℕ) : Partition → Box → Bool
  | .empty,a => decide (Empty (normalize m 1 a))
  | .leaf q,a => decide (q.m = m ∧ CP.subset (normalize m 1 a) (P33.receiptBox q.code)) &&
      P33.priceTest (reheight W (pick q.key)) m q.code
  | .node axis pivot left right,a =>
      let b := normalize m 1 a
      check W pick m left (lower b axis pivot) && check W pick m right (upper b axis pivot)

theorem glue (W : P33.Window) (pick : ℕ → Height W) (m : ℕ) (a : Box)
    (axis : Fin 4) (pivot : ℕ) (left right : Partition)
    (hl : check W pick m left (lower (normalize m 1 a) axis pivot) = true)
    (hr : check W pick m right (upper (normalize m 1 a) axis pivot) = true) :
    check W pick m (.node axis pivot left right) a = true :=
  by simp only [check, hl, hr, Bool.and_true]

theorem sound (W : P33.Window) (pick : ℕ → Height W)
    (m : ℕ) (tree : Partition) (a : Box) (ok : check W pick m tree a = true) :
    Covered m (OZ.Valid m W.low W.t W.y W.r W.cap) a := by
  induction tree generalizing a with
  | empty =>
    simp only [check, decide_eq_true_eq] at ok
    intro p hp ha
    have hb := ATG m 1 a p hp ha
    unfold DR.Empty DR.Contains at *
    omega
  | leaf q =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at ok
    intro p hp ha
    have hb := ATG m 1 a p hp ha
    have hband : P33.bandTest m q.code = true := ok.1.1 ▸ q.band
    refine ⟨P33.receiptBox q.code, P33.receipt_sound (reheight W (pick q.key)) (pick q.key).cert m q.code hband ok.2, ?_⟩
    have hs := ok.1.2
    unfold CP.subset DR.Contains at *
    omega
  | node axis pivot left right ihl ihr =>
    simp only [check, Bool.and_eq_true] at ok
    intro p hp ha
    exact BJ m _ _ axis pivot (ihl _ ok.1) (ihr _ ok.2) p hp (ATG m 1 a p hp ha)
#print axioms sound
end ProximityPrize.SubmissionLower.Night6836Tree
