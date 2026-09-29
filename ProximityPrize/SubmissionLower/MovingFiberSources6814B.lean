import ProximityPrize.SubmissionLower.MovingFiberSources6814A

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P6
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 166
def B : ℕ := 73
def s : ℕ := 34
def U : ℕ := 226
def L : ℕ := 3349
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      10974806343356610 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 41865508621 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 10974806343356610 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 41865508621 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*41865508621 < 10974806343356610 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P6

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P7
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 47
def s : ℕ := 21
def U : ℕ := 154
def L : ℕ := 3043
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      2066370262589177 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7882576304 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 2066370262589177 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 7882576304 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7882576304 < 2066370262589177 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P7

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P8
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 142
def B : ℕ := 56
def s : ℕ := 26
def U : ℕ := 193
def L : ℕ := 2936
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      4390918900144896 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 16750025868 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 4390918900144896 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 16750025868 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*16750025868 < 4390918900144896 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P8

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P9
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 174
def B : ℕ := 76
def s : ℕ := 36
def U : ℕ := 236
def L : ℕ := 2900
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      11277468667084986 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 43020061619 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 11277468667084986 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 43020061619 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*43020061619 < 11277468667084986 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P9

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P10
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 170
def B : ℕ := 71
def s : ℕ := 32
def U : ℕ := 231
def L : ℕ := 3318
def k : ℕ := 8
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      10949410519932218 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 41768666124 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 10949410519932218 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 41768666124 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*41768666124 < 10949410519932218 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P10

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P11
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 98
def B : ℕ := 41
def s : ℕ := 19
def U : ℕ := 132
def L : ℕ := 2615
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      1013434585419617 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3865941597 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 1013434585419617 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 3865941597 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3865941597 < 1013434585419617 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P11
