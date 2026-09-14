import ProximityPrize.SubmissionLower.HigherRootInterpolation6810

namespace ProximityPrize.SubmissionLower.HigherRootSources6810.P0

open RCN135 SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation SecondJetRelaxedGlobalMap
open SecondJetRelaxedCoefficientsReceipt

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def m : ℕ := 132
def B : ℕ := 54
def s : ℕ := 24
def U : ℕ := 180
def L : ℕ := 1800
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (HigherRootInterpolation6810.cutoff m k n0) 131071 L B s U =
      2102627697450660 := by decide +kernel

theorem local_rank :
    SecondJetRelaxedCounts.rankBound m L B s U = 8019382406 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s + 1),
    U ≤ (HigherRootInterpolation6810.cutoff m k n0 h.val + B - 1) / 131071 := by
  decide

theorem source_card :
    Fintype.card (Index (HigherRootInterpolation6810.cutoff m k n0)
      131071 L B s U) = 2102627697450660 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel), coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (HigherRootInterpolation6810.cutoff m k n0 h + B - 1) / 131071) =
        8019382406 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun h hh => cutoff_caps ⟨h, by omega⟩), local_rank]

theorem dimension_gap :
    262144 * 8019382406 < 2102627697450660 := by decide +kernel

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 :=
  genericField_charP K 2130706433

theorem exists_interpolant (hI : Fintype.card I = 262144) :
    ∃ P, HigherRootInterpolation6810.Interpolant m B s U L k n0
      nodes u0 u1 P := by
  apply HigherRootInterpolation6810.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank, source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.HigherRootSources6810.P0

namespace ProximityPrize.SubmissionLower.HigherRootSources6810.P1

open RCN135 SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation SecondJetRelaxedGlobalMap
open SecondJetRelaxedCoefficientsReceipt

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def m : ℕ := 134
def B : ℕ := 56
def s : ℕ := 25
def U : ℕ := 180
def L : ℕ := 2749
def k : ℕ := 6
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (HigherRootInterpolation6810.cutoff m k n0) 131071 L B s U =
      3566543683158980 := by decide +kernel

theorem local_rank :
    SecondJetRelaxedCounts.rankBound m L B s U = 13605267182 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s + 1),
    U ≤ (HigherRootInterpolation6810.cutoff m k n0 h.val + B - 1) / 131071 := by
  decide

theorem source_card :
    Fintype.card (Index (HigherRootInterpolation6810.cutoff m k n0)
      131071 L B s U) = 3566543683158980 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel), coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (HigherRootInterpolation6810.cutoff m k n0 h + B - 1) / 131071) =
        13605267182 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun h hh => cutoff_caps ⟨h, by omega⟩), local_rank]

theorem dimension_gap :
    262144 * 13605267182 < 3566543683158980 := by decide +kernel

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 :=
  genericField_charP K 2130706433

theorem exists_interpolant (hI : Fintype.card I = 262144) :
    ∃ P, HigherRootInterpolation6810.Interpolant m B s U L k n0
      nodes u0 u1 P := by
  apply HigherRootInterpolation6810.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank, source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.HigherRootSources6810.P1

namespace ProximityPrize.SubmissionLower.HigherRootSources6810.P2

open RCN135 SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation SecondJetRelaxedGlobalMap
open SecondJetRelaxedCoefficientsReceipt

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def m : ℕ := 136
def B : ℕ := 56
def s : ℕ := 25
def U : ℕ := 185
def L : ℕ := 2526
def k : ℕ := 6
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (HigherRootInterpolation6810.cutoff m k n0) 131071 L B s U =
      3384947870141283 := by decide +kernel

theorem local_rank :
    SecondJetRelaxedCounts.rankBound m L B s U = 12912535762 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s + 1),
    U ≤ (HigherRootInterpolation6810.cutoff m k n0 h.val + B - 1) / 131071 := by
  decide

theorem source_card :
    Fintype.card (Index (HigherRootInterpolation6810.cutoff m k n0)
      131071 L B s U) = 3384947870141283 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel), coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (HigherRootInterpolation6810.cutoff m k n0 h + B - 1) / 131071) =
        12912535762 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun h hh => cutoff_caps ⟨h, by omega⟩), local_rank]

theorem dimension_gap :
    262144 * 12912535762 < 3384947870141283 := by decide +kernel

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 :=
  genericField_charP K 2130706433

theorem exists_interpolant (hI : Fintype.card I = 262144) :
    ∃ P, HigherRootInterpolation6810.Interpolant m B s U L k n0
      nodes u0 u1 P := by
  apply HigherRootInterpolation6810.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank, source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.HigherRootSources6810.P2

namespace ProximityPrize.SubmissionLower.HigherRootSources6810.P3

open RCN135 SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation SecondJetRelaxedGlobalMap
open SecondJetRelaxedCoefficientsReceipt

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def m : ℕ := 116
def B : ℕ := 46
def s : ℕ := 21
def U : ℕ := 158
def L : ℕ := 2695
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (HigherRootInterpolation6810.cutoff m k n0) 131071 L B s U =
      1844470489720046 := by decide +kernel

theorem local_rank :
    SecondJetRelaxedCounts.rankBound m L B s U = 7036093956 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s + 1),
    U ≤ (HigherRootInterpolation6810.cutoff m k n0 h.val + B - 1) / 131071 := by
  decide

theorem source_card :
    Fintype.card (Index (HigherRootInterpolation6810.cutoff m k n0)
      131071 L B s U) = 1844470489720046 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel), coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (HigherRootInterpolation6810.cutoff m k n0 h + B - 1) / 131071) =
        7036093956 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun h hh => cutoff_caps ⟨h, by omega⟩), local_rank]

theorem dimension_gap :
    262144 * 7036093956 < 1844470489720046 := by decide +kernel

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 :=
  genericField_charP K 2130706433

theorem exists_interpolant (hI : Fintype.card I = 262144) :
    ∃ P, HigherRootInterpolation6810.Interpolant m B s U L k n0
      nodes u0 u1 P := by
  apply HigherRootInterpolation6810.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank, source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.HigherRootSources6810.P3


#print axioms ProximityPrize.SubmissionLower.HigherRootSources6810.P0.exists_interpolant
#print axioms ProximityPrize.SubmissionLower.HigherRootSources6810.P1.exists_interpolant
#print axioms ProximityPrize.SubmissionLower.HigherRootSources6810.P2.exists_interpolant
#print axioms ProximityPrize.SubmissionLower.HigherRootSources6810.P3.exists_interpolant
