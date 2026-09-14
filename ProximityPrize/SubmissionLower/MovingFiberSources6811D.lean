import ProximityPrize.SubmissionLower.MovingFiberSources6811C

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P21
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 111
def B : ℕ := 46
def s : ℕ := 22
def U : ℕ := 151
def L : ℕ := 3089
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      1923596440947592 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7337935450 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 1923596440947592 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 7337935450 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7337935450 < 1923596440947592 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P21

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P22
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 189
def B : ℕ := 83
def s : ℕ := 39
def U : ℕ := 256
def L : ℕ := 3112
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      16886177860853516 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 64415619986 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 16886177860853516 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 64415619986 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*64415619986 < 16886177860853516 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P22

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P23
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 45
def s : ℕ := 20
def U : ℕ := 155
def L : ℕ := 3066
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      1943690857433990 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7414588980 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 1943690857433990 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 7414588980 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7414588980 < 1943690857433990 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P23

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P24
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 190
def B : ℕ := 84
def s : ℕ := 40
def U : ℕ := 258
def L : ℕ := 3048
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      17073478385944741 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 65130073176 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 17073478385944741 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 65130073176 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*65130073176 < 17073478385944741 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P24

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P25
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 111
def B : ℕ := 46
def s : ℕ := 21
def U : ℕ := 151
def L : ℕ := 3071
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      1902298102281753 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7256688379 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 1902298102281753 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 7256688379 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7256688379 < 1902298102281753 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P25

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P26
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 189
def B : ℕ := 83
def s : ℕ := 39
def U : ℕ := 257
def L : ℕ := 3084
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      16729782789508276 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 63818941246 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 16729782789508276 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 63818941246 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*63818941246 < 16729782789508276 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P26
