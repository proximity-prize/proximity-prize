import ProximityPrize.SubmissionLower.MovingFiberSources6811B

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P14
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 146
def B : ℕ := 58
def s : ℕ := 27
def U : ℕ := 198
def L : ℕ := 2498
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      4194771043943235 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 16001770476 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 4194771043943235 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 16001770476 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*16001770476 < 4194771043943235 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P14

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P15
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 98
def B : ℕ := 41
def s : ℕ := 19
def U : ℕ := 133
def L : ℕ := 2289
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      884806673741073 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3375264212 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 884806673741073 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 3375264212 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3375264212 < 884806673741073 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P15

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P16
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 150
def B : ℕ := 60
def s : ℕ := 28
def U : ℕ := 204
def L : ℕ := 2288
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      4304640567595772 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 16420856314 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 4304640567595772 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 16420856314 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*16420856314 < 4304640567595772 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P16

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P17
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 162
def B : ℕ := 71
def s : ℕ := 33
def U : ℕ := 218
def L : ℕ := 2338
def k : ℕ := 7
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      6853094634711026 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 26142431686 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 6853094634711026 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 26142431686 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*26142431686 < 6853094634711026 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P17

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P18
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 47
def s : ℕ := 22
def U : ℕ := 155
def L : ℕ := 2711
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      1849082264981388 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7053684309 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 1849082264981388 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 7053684309 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7053684309 < 1849082264981388 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P18

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P19
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 166
def B : ℕ := 66
def s : ℕ := 31
def U : ℕ := 226
def L : ℕ := 2667
def k : ℕ := 7
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      7416680657483088 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 28292381157 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 7416680657483088 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 28292381157 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*28292381157 < 7416680657483088 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P19

namespace ProximityPrize.SubmissionLower.MovingFiberSources6811.P20
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 174
def B : ℕ := 76
def s : ℕ := 36
def U : ℕ := 237
def L : ℕ := 2716
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U =
      10540329886663022 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 40208136171 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6811.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6811.cutoff m k n0) 131071 L B s U) = 10540329886663022 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6811.cutoff m k n0 h+B-1)/131071) = 40208136171 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*40208136171 < 10540329886663022 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6811.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6811.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6811.P20
