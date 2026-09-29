import ProximityPrize.SubmissionLower.MovingFiberInterpolation6814

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P0
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 132
def B : ℕ := 54
def s : ℕ := 24
def U : ℕ := 180
def L : ℕ := 1871
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      2188161019514560 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 8347167112 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 2188161019514560 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 8347167112 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*8347167112 < 2188161019514560 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P0

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P1
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 134
def B : ℕ := 56
def s : ℕ := 25
def U : ℕ := 180
def L : ℕ := 3044
def k : ℕ := 6
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      3958457074967863 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 15100308302 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 3958457074967863 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 15100308302 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*15100308302 < 3958457074967863 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P1

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P2
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 136
def B : ℕ := 56
def s : ℕ := 25
def U : ℕ := 185
def L : ℕ := 2768
def k : ℕ := 6
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      3717812868511537 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 14182305164 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 3717812868511537 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 14182305164 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*14182305164 < 3717812868511537 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P2

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P3
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 116
def B : ℕ := 46
def s : ℕ := 21
def U : ℕ := 158
def L : ℕ := 3023
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      2073596964862477 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7910135892 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 2073596964862477 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 7910135892 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7910135892 < 2073596964862477 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P3

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P4
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 45
def s : ℕ := 21
def U : ℕ := 155
def L : ℕ := 3396
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      2172257008113656 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 8286502522 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 2172257008113656 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 8286502522 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*8286502522 < 2172257008113656 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P4

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P5
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 158
def B : ℕ := 63
def s : ℕ := 29
def U : ℕ := 215
def L : ℕ := 3223
def k : ℕ := 7
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      7445296861861548 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 28401542899 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 7445296861861548 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 28401542899 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*28401542899 < 7445296861861548 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P5
