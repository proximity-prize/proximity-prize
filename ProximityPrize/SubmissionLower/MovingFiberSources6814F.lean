import ProximityPrize.SubmissionLower.MovingFiberSources6814E

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P30
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 136
def B : ℕ := 59
def s : ℕ := 27
def U : ℕ := 185
def L : ℕ := 2478
def k : ℕ := 6
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      3615391649982091 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 13791611084 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 3615391649982091 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 13791611084 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*13791611084 < 3615391649982091 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P30

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P31
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 130
def B : ℕ := 53
def s : ℕ := 24
def U : ℕ := 177
def L : ℕ := 3429
def k : ℕ := 6
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      3830167918600970 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 14610919708 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 3830167918600970 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 14610919708 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*14610919708 < 3830167918600970 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P31

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P32
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 158
def B : ℕ := 62
def s : ℕ := 29
def U : ℕ := 215
def L : ℕ := 3401
def k : ℕ := 7
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      7684612401342838 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 29314446294 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 7684612401342838 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 29314446294 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*29314446294 < 7684612401342838 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P32

namespace ProximityPrize.SubmissionLower.MovingFiberSources6814.P33
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 186
def B : ℕ := 82
def s : ℕ := 39
def U : ℕ := 253
def L : ℕ := 3449
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U =
      17760503501691442 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 67750844921 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6814.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6814.cutoff m k n0) 131071 L B s U) = 17760503501691442 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6814.cutoff m k n0 h+B-1)/131071) = 67750844921 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*67750844921 < 17760503501691442 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6814.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6814.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

#print axioms exists_interpolant
end
end ProximityPrize.SubmissionLower.MovingFiberSources6814.P33
