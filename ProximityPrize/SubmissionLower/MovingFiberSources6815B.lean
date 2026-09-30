import ProximityPrize.SubmissionLower.MovingFiberSources6815A
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P6
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 166
def B : ℕ := 73
def s : ℕ := 34
def U : ℕ := 226
def L : ℕ := 3437
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      11270386540659834 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 42993075061 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 11270386540659834 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 42993075061 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*42993075061 < 11270386540659834 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P6

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P7
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 47
def s : ℕ := 21
def U : ℕ := 154
def L : ℕ := 3146
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      2137585483518867 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 8154240246 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 2137585483518867 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 8154240246 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*8154240246 < 2137585483518867 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P7

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P8
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 142
def B : ℕ := 56
def s : ℕ := 26
def U : ℕ := 193
def L : ℕ := 3010
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      4504178231975820 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 17182051854 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 4504178231975820 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 17182051854 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*17182051854 < 4504178231975820 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P8

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P9
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 174
def B : ℕ := 76
def s : ℕ := 36
def U : ℕ := 236
def L : ℕ := 2961
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      11521876425873722 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 43952428136 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 11521876425873722 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 43952428136 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*43952428136 < 11521876425873722 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P9

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P10
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 170
def B : ℕ := 71
def s : ℕ := 32
def U : ℕ := 231
def L : ℕ := 3399
def k : ℕ := 8
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      11223491763992462 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 42814186017 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 11223491763992462 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 42814186017 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*42814186017 < 11223491763992462 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P10

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P11
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 98
def B : ℕ := 41
def s : ℕ := 19
def U : ℕ := 132
def L : ℕ := 2704
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      1048554600024207 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3999915433 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 1048554600024207 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 3999915433 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3999915433 < 1048554600024207 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P11
