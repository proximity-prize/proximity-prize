import ProximityPrize.SubmissionLower.MovingFiberSources6815D
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P24
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 190
def B : ℕ := 84
def s : ℕ := 40
def U : ℕ := 258
def L : ℕ := 3307
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      18570330419650472 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 70840163296 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 18570330419650472 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 70840163296 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*70840163296 < 18570330419650472 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P24

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P25
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 111
def B : ℕ := 46
def s : ℕ := 21
def U : ℕ := 151
def L : ℕ := 3548
def k : ℕ := 5
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      2202960866996373 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 8403622000 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 2202960866996373 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 8403622000 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*8403622000 < 2202960866996373 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P25

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P26
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 189
def B : ℕ := 83
def s : ℕ := 39
def U : ℕ := 257
def L : ℕ := 3350
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      18217633845117522 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 69494714916 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 18217633845117522 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 69494714916 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*69494714916 < 18217633845117522 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P26

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P27
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 72
def B : ℕ := 31
def s : ℕ := 14
def U : ℕ := 98
def L : ℕ := 1012
def k : ℕ := 2
def n0 : ℕ := 3

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      121776386811934 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 464539866 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 121776386811934 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 464539866 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*464539866 < 121776386811934 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P27

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P28
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 104
def B : ℕ := 45
def s : ℕ := 21
def U : ℕ := 142
def L : ℕ := 1769
def k : ℕ := 4
def n0 : ℕ := 5

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      901318580867354 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3438248097 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 901318580867354 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 3438248097 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3438248097 < 901318580867354 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P28

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P29
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 104
def B : ℕ := 45
def s : ℕ := 21
def U : ℕ := 141
def L : ℕ := 1920
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      980491422231259 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3740269769 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 980491422231259 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 3740269769 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3740269769 < 980491422231259 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P29
