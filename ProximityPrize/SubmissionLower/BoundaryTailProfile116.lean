import ProximityPrize.SubmissionLower.BoundaryTailInterpolation

namespace ProximityPrize.SubmissionLower.BoundaryTailProfile116

open RCN135 SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation SecondJetRelaxedGlobalMap
open SecondJetRelaxedCoefficientsReceipt

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def m : ℕ := 116
def B : ℕ := 47
def s : ℕ := 21
def U : ℕ := 157
def L : ℕ := 2286
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (BoundaryTailInterpolation.cutoff m k n0) 131071 L B s U =
      1606478760777756 := by decide

theorem local_rank :
    SecondJetRelaxedCounts.rankBound m L B s U = 6128217722 := by decide

theorem cutoff_caps : ∀ h : Fin (s + 1),
    U ≤ (BoundaryTailInterpolation.cutoff m k n0 h.val + B - 1) / 131071 := by
  decide

theorem source_card :
    Fintype.card (Index (BoundaryTailInterpolation.cutoff m k n0)
      131071 L B s U) = 1606478760777756 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide), coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (BoundaryTailInterpolation.cutoff m k n0 h + B - 1) / 131071) =
        6128217722 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide) (by decide) (by decide)
    (by decide) (fun h hh => cutoff_caps ⟨h, by omega⟩), local_rank]

theorem dimension_gap :
    262144 * 6128217722 < 1606478760777756 := by decide

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 :=
  genericField_charP K 2130706433

theorem exists_interpolant (hI : Fintype.card I = 262144) :
    ∃ P, BoundaryTailInterpolation.Interpolant m B s U L k n0
      nodes u0 u1 P := by
  apply BoundaryTailInterpolation.exists_of_dimension m B s U L k n0
    (by decide) (by decide) hI nodes u0 u1
  rw [exact_rank, source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.BoundaryTailProfile116
