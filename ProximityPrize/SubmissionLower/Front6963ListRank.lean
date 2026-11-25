import ProximityPrize.SubmissionLower.Front6963ListCells0
import ProximityPrize.SubmissionLower.Front6963ListCells1
import ProximityPrize.SubmissionLower.Front6963ListCells2
import ProximityPrize.SubmissionLower.Front6963ListCells3
import ProximityPrize.SubmissionLower.Front6963ListCells4
import ProximityPrize.SubmissionLower.Front6963ListCells5
import ProximityPrize.SubmissionLower.Front6963ListCells6
import ProximityPrize.SubmissionLower.Front6963ListCells7

set_option Elab.async false

namespace Front6963ListBank
open scoped BigOperators

private def rankTable : List ℕ := [59, 174, 342, 560, 825, 1134, 1484, 1872, 2295, 2750, 3234, 3696, 4136, 4554, 4950, 5280, 5547, 5754, 5904, 6000, 6045, 6042, 5994, 5904, 5775, 5610, 5445, 5280, 5115, 4950, 4785, 4620, 4455, 4290, 4125, 3960, 3796, 3633, 3471, 3311, 3153, 2997, 2844, 2694, 2547, 2404, 2265, 2129, 1998, 1870, 1747, 1627, 1513, 1401, 1296, 1193, 1096, 1002, 914, 828, 749, 672, 601, 533, 471, 411, 358, 307, 262, 220, 183, 149, 120, 94, 72, 54, 39, 27, 18, 11, 6]

private theorem grades (q : Fin 81) :
    (∑ u ∈ Finset.range (83-q.val), (CJ0.blockMatrix source q.val ((u : ℤ)-24)).rank) ≤
      rankTable[q.val]'(by simpa [rankTable] using q.isLt) := by
  fin_cases q
  · exact grade_0
  · exact grade_1
  · exact grade_2
  · exact grade_3
  · exact grade_4
  · exact grade_5
  · exact grade_6
  · exact grade_7
  · exact grade_8
  · exact grade_9
  · exact grade_10
  · exact grade_11
  · exact grade_12
  · exact grade_13
  · exact grade_14
  · exact grade_15
  · exact grade_16
  · exact grade_17
  · exact grade_18
  · exact grade_19
  · exact grade_20
  · exact grade_21
  · exact grade_22
  · exact grade_23
  · exact grade_24
  · exact grade_25
  · exact grade_26
  · exact grade_27
  · exact grade_28
  · exact grade_29
  · exact grade_30
  · exact grade_31
  · exact grade_32
  · exact grade_33
  · exact grade_34
  · exact grade_35
  · exact grade_36
  · exact grade_37
  · exact grade_38
  · exact grade_39
  · exact grade_40
  · exact grade_41
  · exact grade_42
  · exact grade_43
  · exact grade_44
  · exact grade_45
  · exact grade_46
  · exact grade_47
  · exact grade_48
  · exact grade_49
  · exact grade_50
  · exact grade_51
  · exact grade_52
  · exact grade_53
  · exact grade_54
  · exact grade_55
  · exact grade_56
  · exact grade_57
  · exact grade_58
  · exact grade_59
  · exact grade_60
  · exact grade_61
  · exact grade_62
  · exact grade_63
  · exact grade_64
  · exact grade_65
  · exact grade_66
  · exact grade_67
  · exact grade_68
  · exact grade_69
  · exact grade_70
  · exact grade_71
  · exact grade_72
  · exact grade_73
  · exact grade_74
  · exact grade_75
  · exact grade_76
  · exact grade_77
  · exact grade_78
  · exact grade_79
  · exact grade_80

theorem prefix_bound : CJ0.prefixRank source 81 ≤ 200031 := by
  unfold CJ0.prefixRank
  change (∑ q ∈ Finset.range 81, ∑ u ∈ Finset.range (83-q),
    (CJ0.blockMatrix source q ((u : ℤ)-24)).rank) ≤ _
  rw [← Fin.sum_univ_eq_sum_range]
  apply (Finset.sum_le_sum fun q _ => grades q).trans_eq
  decide +kernel

#print axioms prefix_bound

theorem native_shape : CJ0.ShapeOK source := by
  have hmem := CJ0.mem_fullBox (B := 80) (J := 24) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 80
  unfold CJ0.Jet.q at hq
  omega

end Front6963ListBank
