import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.UpperBranch1

-- merged module GoldBranch7N1
section Merged_GoldBranch7N1
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_7_1
open P1_7 (Bank)
open P1_7_1 (nodeRows groupedPoleMoment)
open P1_7_1_2 (six_nodeRows sixPerNode)
open P1_7_1_3 (momentEstimate grouped_bound)
open P1_7_1_3_2 (ExactMoment)
structure BankOK (t : Bank) : Prop where
  nodes : nodeRows t.shape = t.nodeRows
  moment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment ∧ t.shape.B < K1.p
theorem checked (t : Bank) {m B J N M : ℕ}
    (hm : t.shape.m = m) (hB : t.shape.B = B) (hJ : t.shape.J = J)
    (hN : t.nodeRows = N) (hM : t.poleMoment = M)
    (hmJ : 2*J ≤ m) (hJB : m+J ≤ B+1)
    (hnode : 262144 * sixPerNode (m-2*J) J = 6*N)
    (hchar : B < K1.p) (hbound : momentEstimate B J = M) : BankOK t := by
  have h := six_nodeRows t.shape (by rw [hm, hJ]; exact hmJ) (by rw [hm, hJ, hB]; exact hJB)
  rw [hm, hJ, hnode, ← hN] at h
  refine ⟨by omega, ?_⟩
  rw [hB, hJ, hM]
  exact ⟨(grouped_bound _ _).trans hbound.le, hchar⟩
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
end P3_7_1
end
section
namespace P3_7_1
open P3 (HighBand)
open P3_7 (Bank Stage terminal stages  )
open scoped P1_7_1_3_2
local notation "b!" depth "," grade "," deriv "," nodes "," moment ";" h =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) h
end P3_7_1
end

end Merged_GoldBranch7N1

-- merged module HighCore82258Source
section Merged_HighCore82258Source

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace HighCore82258
noncomputable section

open Polynomial
open P1 (K I p node twist)
open FrontCore82258 (AnchorModel AnchoredFamily AdjacentChart)
open K1_14 (L FX Seeds Equation Shape Jet Banks SeedBound liftPoly graphEval atX atMark
  jetAt triangle slots shapeSum)
open K1_14_1
open P1_7_1 (groupedPoleMoment nodeRows telescope)
open scoped BigOperators Polynomial
open P1_7_1 (pole_bound)



def fullCutoff (s : Shape) := s.m * agreement - 1
def buffered (h r : ℕ) (s : Shape) := fullCutoff s - 2*h*r
def RankFloor (h : ℕ) (t : Bank) (rows : Banks) : Prop :=
  ∀ W < t.shape.m * agreement,
    (∀ q ≤ t.shape.B, ∀ j ≤ min q t.shape.J, q * (131071-h) ≤ W+1+j) →
    triangle t.shape.U * shapeSum t.shape (fun q j => W+1+j - q*(131071-h)) ≤
      debit h t + ∑ w ∈ Finset.range (W+1), Module.finrank FX (rows t.shape w)
structure Source (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) (rows : Banks) : Prop where
  nested : ∀ t, Listed b t → ∀ t', Listed b t' →
    t.shape.m = t'.shape.m → t.shape.B = t'.shape.B → t.shape.J = t'.shape.J →
    t.shape.U ≤ t'.shape.U → ∀ W W', W ≤ W' → rows t.shape W ≤ rows t'.shape W'
  necessary : ∀ t, Listed b t → ∀ W < t.shape.m * agreement, ∀ P ∈ rows t.shape W,
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ t, Listed b t → ∀ W, ∀ P ∈ rows t.shape W, K1_14_3.RowCaps P t.shape
  leading : ∀ t, Listed b t → K1_14_3.LeadingFilter M.overhead.toNat rows t.shape
  shift : ∀ t, Listed b t → K1_14_3.SeedShift M.overhead.toNat rows t.shape
  floor_bound : ∀ t, Listed b t → RankFloor M.overhead.toNat t rows
structure BufferedPair (h : ℕ) (rows : Banks) (s : Stage) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows s.free.shape (buffered h s.reserve s.free.shape)
  moving_mem : moving ∈ rows s.moving.shape (buffered h s.reserve s.moving.shape)
  no_moving : K1_14_3.NoMovingCommon free moving
abbrev Pairs (b : Band) (h : ℕ) (rows : Banks) :=
  ∀ s ∈ stages b, BufferedPair h rows s


def crtWord {u del} (M : AnchorModel u del) : I → L :=
  fun i => algebraMap K L (M.word i)

structure ChartSource (b : Band) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) where
  poles : PoleData M.overhead.toNat
  crt : CRTLift poles
  node_avoids : ∀ i k, (poles.block i).eval (nodeL k) ≠ 0
  residues : ∀ γ ∈ Γ, MarkResidues poles (M.label γ) (F.scalar γ)
  source : Source b M F (evaluated crt (crtWord M))





end
end HighCore82258

end Merged_HighCore82258Source
