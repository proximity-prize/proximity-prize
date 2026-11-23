import ProximityPrize.SubmissionLower.R6960Front6960ListCells0
import ProximityPrize.SubmissionLower.R6960Front6960ListCells1
import ProximityPrize.SubmissionLower.R6960Front6960ListCells2
import ProximityPrize.SubmissionLower.R6960Front6960ListCells3
import ProximityPrize.SubmissionLower.R6960Front6960ListCells4
import ProximityPrize.SubmissionLower.R6960Front6960ListCells5
import ProximityPrize.SubmissionLower.R6960Front6960ListCells6
import ProximityPrize.SubmissionLower.R6960Front6960ListCells7

set_option Elab.async false

namespace Front6960ListBank
open scoped BigOperators

private def rankTable : List ℕ := [58, 171, 336, 550, 810, 1113, 1456, 1836, 2250, 2695, 3168, 3619, 4048, 4455, 4796, 5074, 5292, 5453, 5560, 5616, 5624, 5587, 5508, 5390, 5236, 5082, 4928, 4774, 4620, 4466, 4312, 4158, 4004, 3850, 3696, 3542, 3389, 3237, 3086, 2937, 2790, 2645, 2503, 2364, 2228, 2096, 1968, 1843, 1723, 1606, 1494, 1385, 1282, 1181, 1086, 994, 907, 823, 745, 669, 599, 532, 470, 411, 358, 307, 262, 220, 183, 149, 120, 94, 72, 54, 39, 27, 18, 11, 6, 3]

private theorem grades (q : Fin 80) :
    (∑ u ∈ Finset.range (81-q.val), (CJ0.blockMatrix source q.val ((u : ℤ)-23)).rank) ≤
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

theorem prefix_bound : CJ0.prefixRank source 80 ≤ 182049 := by
  unfold CJ0.prefixRank
  change (∑ q ∈ Finset.range 80, ∑ u ∈ Finset.range (81-q),
    (CJ0.blockMatrix source q ((u : ℤ)-23)).rank) ≤ _
  rw [← Fin.sum_univ_eq_sum_range]
  apply (Finset.sum_le_sum fun q _ => grades q).trans_eq
  decide +kernel

#print axioms prefix_bound
end Front6960ListBank
