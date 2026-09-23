import ProximityPrize.SubmissionLower.MovingFiberSources6811D

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P27
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 72
def B : ℕ := 31
def s : ℕ := 14
def U : ℕ := 98
def L : ℕ := 979
def k : ℕ := 2
def n0 : ℕ := 3

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      117665944823972 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 448857969 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 117665944823972 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 448857969 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*448857969 < 117665944823972 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P27

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P28
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 104
def B : ℕ := 45
def s : ℕ := 21
def U : ℕ := 142
def L : ℕ := 1697
def k : ℕ := 4
def n0 : ℕ := 5

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      863558012119170 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3294204681 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 863558012119170 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 3294204681 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3294204681 < 863558012119170 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P28

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P29
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 104
def B : ℕ := 45
def s : ℕ := 21
def U : ℕ := 141
def L : ℕ := 1835
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      935912335440764 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3570221829 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 935912335440764 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 3570221829 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3570221829 < 935912335440764 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P29

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P30
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 136
def B : ℕ := 59
def s : ℕ := 27
def U : ℕ := 185
def L : ℕ := 2423
def k : ℕ := 6
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      3532940686794351 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 13477083409 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 3532940686794351 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 13477083409 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*13477083409 < 3532940686794351 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P30
