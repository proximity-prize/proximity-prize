import ProximityPrize.SubmissionLower.MovingFiberSources6815C
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P18
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 47
def s : ℕ := 22
def U : ℕ := 155
def L : ℕ := 3060
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      2091995942683606 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 7980323632 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 2091995942683606 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 7980323632 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*7980323632 < 2091995942683606 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P18

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P19
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 166
def B : ℕ := 66
def s : ℕ := 31
def U : ℕ := 226
def L : ℕ := 2877
def k : ℕ := 7
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      8018437105906152 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 30587864487 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 8018437105906152 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 30587864487 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*30587864487 < 8018437105906152 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P19

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P20
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 174
def B : ℕ := 76
def s : ℕ := 36
def U : ℕ := 237
def L : ℕ := 2938
def k : ℕ := 8
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      11429840791222364 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 43601379975 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 11429840791222364 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 43601379975 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*43601379975 < 11429840791222364 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P20

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P21
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 111
def B : ℕ := 46
def s : ℕ := 22
def U : ℕ := 151
def L : ℕ := 3572
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      2229624545787382 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 8505339205 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 2229624545787382 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 8505339205 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*8505339205 < 2229624545787382 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P21

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P22
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 189
def B : ℕ := 83
def s : ℕ := 39
def U : ℕ := 256
def L : ℕ := 3383
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      18402001784104522 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 70198007961 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 18402001784104522 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 70198007961 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*70198007961 < 18402001784104522 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P22

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P23
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 114
def B : ℕ := 45
def s : ℕ := 20
def U : ℕ := 155
def L : ℕ := 3507
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      2228229439108064 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 8500020075 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 2228229439108064 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 8500020075 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*8500020075 < 2228229439108064 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P23
