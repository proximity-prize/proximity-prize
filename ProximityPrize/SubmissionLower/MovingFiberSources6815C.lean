import ProximityPrize.SubmissionLower.MovingFiberSources6815B
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P12
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 142
def B : ℕ := 59
def s : ℕ := 27
def U : ℕ := 193
def L : ℕ := 2625
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      4241775770038611 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 16181057831 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 4241775770038611 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 16181057831 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*16181057831 < 4241775770038611 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P12

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P13
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 158
def B : ℕ := 69
def s : ℕ := 32
def U : ℕ := 214
def L : ℕ := 2607
def k : ℕ := 7
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      6916144975504702 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 26382993893 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 6916144975504702 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 26382993893 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*26382993893 < 6916144975504702 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P13

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P14
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 146
def B : ℕ := 58
def s : ℕ := 27
def U : ℕ := 198
def L : ℕ := 2709
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      4559171741970797 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 17391826027 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 4559171741970797 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 17391826027 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*17391826027 < 4559171741970797 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P14

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P15
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 98
def B : ℕ := 41
def s : ℕ := 19
def U : ℕ := 133
def L : ℕ := 2580
def k : ℕ := 4
def n0 : ℕ := 6

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      999640065772791 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 3813321353 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 999640065772791 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 3813321353 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*3813321353 < 999640065772791 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P15

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P16
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 150
def B : ℕ := 60
def s : ℕ := 28
def U : ℕ := 204
def L : ℕ := 2457
def k : ℕ := 6
def n0 : ℕ := 9

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      4632792950272956 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 17672687648 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 4632792950272956 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 17672687648 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*17672687648 < 4632792950272956 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P16

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P17
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 162
def B : ℕ := 71
def s : ℕ := 33
def U : ℕ := 218
def L : ℕ := 2511
def k : ℕ := 7
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      7378050356205804 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 28144961181 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 7378050356205804 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 28144961181 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*28144961181 < 7378050356205804 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P17
