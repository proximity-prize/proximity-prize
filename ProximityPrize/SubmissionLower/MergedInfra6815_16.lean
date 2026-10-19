import ProximityPrize.SubmissionLower.MergedInfra6815_15
import ProximityPrize.SubmissionLower.MergedInfra6815_10
set_option Elab.async false
section MergedPart0
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
end MergedPart0
section MergedPart1
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P30
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 136
def B : ℕ := 59
def s : ℕ := 27
def U : ℕ := 185
def L : ℕ := 2536
def k : ℕ := 6
def n0 : ℕ := 7

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      3702342481581303 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 14123294814 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 3702342481581303 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 14123294814 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*14123294814 < 3702342481581303 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P30

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P31
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 130
def B : ℕ := 53
def s : ℕ := 24
def U : ℕ := 177
def L : ℕ := 3543
def k : ℕ := 6
def n0 : ℕ := 8

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      3959844937245224 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 15105604012 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 3959844937245224 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 15105604012 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*15105604012 < 3959844937245224 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P31

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P32
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 158
def B : ℕ := 62
def s : ℕ := 29
def U : ℕ := 215
def L : ℕ := 3489
def k : ℕ := 7
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      7887900152649018 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 30089939166 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 7887900152649018 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 30089939166 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*30089939166 < 7887900152649018 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P32

namespace ProximityPrize.SubmissionLower.MovingFiberSources6815.P33
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
noncomputable section
set_option autoImplicit false
def m : ℕ := 186
def B : ℕ := 82
def s : ℕ := 39
def U : ℕ := 253
def L : ℕ := 3531
def k : ℕ := 9
def n0 : ℕ := 10

theorem coefficient_count :
    coefficientCount (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U =
      18194269939623242 := by decide +kernel

theorem local_rank : SecondJetRelaxedCounts.rankBound m L B s U = 69405624191 := by decide +kernel

theorem cutoff_caps : ∀ h : Fin (s+1),
    U ≤ (MovingFiberInterpolation6815.cutoff m k n0 h.val+B-1)/131071 := by decide +kernel

theorem source_card :
    Fintype.card (Index (MovingFiberInterpolation6815.cutoff m k n0) 131071 L B s U) = 18194269939623242 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide +kernel),coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (MovingFiberInterpolation6815.cutoff m k n0 h+B-1)/131071) = 69405624191 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun h hh => cutoff_caps ⟨h,by omega⟩),local_rank]

theorem dimension_gap : 262144*69405624191 < 18194269939623242 := by decide +kernel

theorem exists_interpolant {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) :
    ∃ P, MovingFiberInterpolation6815.Interpolant m B s U L k n0 nodes u0 u1 P := by
  apply MovingFiberInterpolation6815.exists_of_dimension m B s U L k n0
    (by decide +kernel) (by decide +kernel) hI nodes u0 u1
  rw [exact_rank,source_card]
  exact dimension_gap

end
end ProximityPrize.SubmissionLower.MovingFiberSources6815.P33
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6811
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetDifferentiation
open SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]

theorem coefficient_monomial_degree (f : Polynomial K) (z : K) (w : ℕ)
    (hf : f.natDegree ≤ w) (e : Fin 4 →₀ ℕ) (c : K) :
    (coefficientSpecialize f z (MvPolynomial.monomial e c)).natDegree ≤
      e 0+w*e 1+(w-1)*e 2 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
    have hc : (coefficientSpecialize f z (MvPolynomial.C c)).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have h0 : (coefficientSpecialize f z (MvPolynomial.X 0)^e 0).natDegree ≤ e 0 := by
      simp [coefficientSpecialize]
    have h1 : (coefficientSpecialize f z (MvPolynomial.X 1)^e 1).natDegree ≤ e 1*w := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 1) hf
    have h2 : (coefficientSpecialize f z (MvPolynomial.X 2)^e 2).natDegree ≤ e 2*(w-1) := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 2)
        ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1))
    have h3 : (coefficientSpecialize f z (MvPolynomial.X 3)^e 3).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have hh := Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2 h3)))
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm] using hh
  · intro i
    simp

theorem coefficient_degree (P : MvPolynomial (Fin 4) K) (f : Polynomial K)
    (z : K) (w D : ℕ) (hf : f.natDegree ≤ w) (hD : 0 < D)
    (hP : ∀ e ∈ P.support, e 0+w*e 1+(w-1)*e 2 < D) :
    (coefficientSpecialize f z P).natDegree < D := by
  classical
  have ht : ∀ e ∈ P.support,
      (coefficientSpecialize f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))).natDegree ≤ D-1 := by
    intro e he
    have hh := coefficient_monomial_degree f z w hf e (AddMonoidAlgebra.coeff P e)
    have hb := hP e he
    omega
  rw [MvPolynomial.as_sum P, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun e => coefficientSpecialize f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))) ht
  omega

theorem iterate_derivative_top {R : Type*} [CommRing R] (P : Polynomial R) (d : ℕ)
    (hh : ∀ j, d < j → P.coeff j = 0) :
    (Polynomial.derivative)^[d] P = Polynomial.C (d.factorial • P.coeff d) := by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj : j = 0
  · subst j
    simp [Nat.descFactorial_self]
  · rw [hh (j+d) (by omega)]
    simp [hj]

theorem specialize_top (P : Poly (K := K)) (f : Polynomial K) (z : K) (d : ℕ)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    specialize f z ((pderiv 1)^[d] P) =
      d.factorial • coefficientSpecialize f z ((asS P).coeff d) := by
  rw [specialize_eq, asS_iterate, ← Polynomial.eval_map, ← Polynomial.iterate_derivative_map]
  rw [iterate_derivative_top _ d (by intro j hj; simpa using hh j hj)]
  simp

theorem low_coefficient_vanish (P : Poly (K := K)) (m k n0 d : ℕ)
    (hdm : d < m) (hdn : d < n0) (hfact : (d.factorial : K) ≠ 0)
    (hP : ∀ e ∈ P.support,
      e 0+131071*e 2+131070*e 3+131069*e 1+
        reserve k n0 (e 1)*50196 < m*181265)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcontact : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f : Polynomial K) (hf : f.natDegree ≤ 131071) (z : K) (S : Finset N)
    (hS : 181265 ≤ S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    coefficientSpecialize f z ((asS P).coeff d) = 0 := by
  have hweight : ∀ e ∈ ((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2 < (m-d)*181265 := by
    intro e he
    have hb := hP _ (coefficient_support P d e he)
    obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [reserve,if_pos hdn] at hb
    omega
  have hdeg := coefficient_degree ((asS P).coeff d) f z 131071 ((m-d)*181265)
    hf (by omega) hweight
  have htop := specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P) = 0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
    · rw [htop]
      have hs := Polynomial.natDegree_smul_le d.factorial
        (coefficientSpecialize f z ((asS P).coeff d))
      exact (hs.trans_lt hdeg).trans_le (Nat.mul_le_mul_left (m-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  apply (mul_eq_zero.mp hv).resolve_left
  simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr hfact)

end
end ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6811
end MergedPart2
