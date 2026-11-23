import ProximityPrize.SubmissionLower.KoalaSplitProof
import ProximityPrize.SubmissionLower.FadicVarCert

set_option autoImplicit false
set_option Elab.async false

namespace KoalaGateCheck

open FadicGate
open KoalaWeightedRate (Envelope)
open scoped BigOperators

private abbrev S : ℕ := 406807694511
private abbrev Plain := ℕ → ℕ × ℕ × ℕ
private abbrev Boxes := ℕ → List Entry

abbrev Bound (p : Envelope) (t : ℕ) (plain : Plain) (boxes : Boxes) (v N : ℕ) : Prop :=
  ∑ i ∈ Finset.range N, max 0 ((S : ℤ) - varGateDim S p.widthLow p.widthHigh
    p.indexLow p.indexHigh p.topLow p.taperLow p.taperHigh t plain
    (fun r => (boxes r).length) (fun r a => (boxes r).getD a none) (i+1)) ≤ (v : ℤ)

private def raw (h : ℕ) (p : Envelope) (plain : Plain) (boxes : Boxes) (i : ℕ) : ℕ :=
  rVarLevelLoss S h p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow p.taperLow p.taperHigh
    (plain (i+1)).1 (plain (i+1)).2.1 (plain (i+1)).2.2 (boxes (i+1))

def valid (h : ℕ) (p : Envelope) (plain : Plain) (boxes : Boxes) (values : List ℕ) (i : ℕ) : Bool :=
  decide (raw h p plain boxes i = values.getD i 0)

inductive Prefix (ok : ℕ → Bool) : ℕ → Prop
  | nil : Prefix ok 0
  | step {lo : ℕ} (n : ℕ) (before : Prefix ok lo)
      (here : (List.range' lo n).all ok = true) : Prefix ok (lo+n)

theorem Prefix.six {ok : ℕ → Bool} {lo : ℕ} (h : Prefix ok lo)
    (hs : (List.range' lo 6).all ok = true) : Prefix ok (lo+6) := .step 6 h hs

theorem Prefix.last {ok : ℕ → Bool} {lo : ℕ} (h : Prefix ok lo) (n : ℕ)
    (hs : (List.range' lo n).all ok = true) : Prefix ok (lo+n) := .step n h hs

private theorem Prefix.at {ok : ℕ → Bool} {n : ℕ} (h : Prefix ok n) :
    ∀ i, i < n → ok i = true := by
  induction h with
  | nil => intro i hi; omega
  | @step lo n before here ih =>
    intro i hi
    by_cases hl : i < lo
    · exact ih i hl
    · exact List.all_eq_true.mp here i (List.mem_range'_1.mpr ⟨by omega,hi⟩)

theorem price {priced : ℕ → Bool} {t r : ℕ} (hr : 0 < r) (ht : r < t)
    (checked : (List.range (t-1)).all (fun i => priced (i+1)) = true) : priced r = true := by
  have hi : r-1 ∈ List.range (t-1) := List.mem_range.mpr (by omega)
  simpa only [Nat.sub_add_cancel hr] using List.all_eq_true.mp checked (r-1) hi

theorem loss (h : ℕ) (p : Envelope) (t : ℕ) (plain : Plain) (boxes : Boxes) (values : List ℕ)
    (v N : ℕ) (ht : 0 < t) (hh : 0 < h) (checks : Prefix (valid h p plain boxes values) (t-1))
    (total : ∑ i ∈ Finset.range (t-1), ((values.getD i 0 : ℕ) : ℤ) = (v : ℤ)) :
    Bound p t plain boxes v N := by
  let f := varCertLoss (S : ℤ) h p.widthLow p.widthHigh p.indexLow p.indexHigh
    p.topLow p.taperLow p.taperHigh t plain boxes
  have row (i : ℕ) (hi : i < t-1) : f i = ((values.getD i 0 : ℕ) : ℤ) :=
    varCertLoss_row S h p.widthLow p.widthHigh p.indexLow p.indexHigh p.topLow
      p.taperLow p.taperHigh t plain boxes i (plain (i+1)).1 (plain (i+1)).2.1
      (plain (i+1)).2.2 (boxes (i+1)) _ (by omega)
      (by rcases plain (i+1) with ⟨a,b,c⟩; rfl) rfl
      (of_decide_eq_true (checks.at i hi))
  have tail : f (t-1) = ((0 : ℕ) : ℤ) :=
    varCertLoss_terminal (S : ℤ) h p.widthLow p.widthHigh p.indexLow p.indexHigh
      p.topLow p.taperLow p.taperHigh t plain boxes (t-1) (by omega)
  have full : ∑ i ∈ Finset.range t, f i = (v : ℤ) := by
    conv_lhs => rw [show t = (t-1)+1 by omega, Finset.sum_range_succ]
    rw [tail, Nat.cast_zero, add_zero]
    exact (Finset.sum_congr rfl fun i hi => row i (Finset.mem_range.mp hi)).trans total
  exact loss_of_varCert (S : ℤ) h p.widthLow p.widthHigh p.indexLow p.indexHigh
    p.topLow p.taperLow p.taperHigh t plain boxes (v : ℤ) hh full N

end KoalaGateCheck
