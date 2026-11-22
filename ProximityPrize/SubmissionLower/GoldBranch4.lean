import ProximityPrize.SubmissionLower.SilverBase
import ProximityPrize.SubmissionLower.HighCore82258ScheduleData
set_option autoImplicit true
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace P3_4
noncomputable section
open P3 MvPolynomial
open P2_4 (Bank Puncture ContactInput)
open K1_11 (sourceWeights sourceBounds filtered mem_filtered)
open K1_11_2 (OmitsMessages sWeight tWeight graph PlaneOutput equation equation_degrees
  nodeWordMap decoder_bounds decoderNumerator decoderDenominator decoderDenominator_ne equation_linear
  equation_primitive linear_relation_contact_order_one)
open K1_11_2_2 (interpolant parameterNode nodeValue parameterNode_interpolant
  parameterNode_nodeValue degreeOf_interpolant_le degreeOf_nodeValue_le seedEval
  seedEval_nodeValue eval_graph nodeWord_combination nodeWord_omits)
open private degreeOf_le_of_dvd from ProximityPrize.SubmissionLower.Fast072
open private no_pair_one_one_of_graph native_column_rank from ProximityPrize.SubmissionLower.Fast070
open private transfer_at from ProximityPrize.SubmissionLower.Fast068
private theorem degree_lt_of_product (s d m b : ℕ) (hd : s * d ≤ b) (hm : b < s * m) :
    d < m := by
  by_contra! h
  exact (not_lt_of_ge ((Nat.mul_le_mul_left s h).trans hd)) hm
end
end P3_4
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P3_4
open P3 Finset
open P2_4 (Bank)
open K1_11 (V J)
open private countRow gradeRow count grade contactRow V_affine rational_fee from ProximityPrize.SubmissionLower.PortFrontA
open private
  dims_5_16_10 dims_4_15_8 jets_4_16_10 jets_3_15_8
  dims_5_8_7 dims_4_7_4 jets_4_8_7 jets_3_7_4
  dims_5_10_16 dims_4_8_15 jets_4_10_16 jets_3_8_15
  dims_5_11_10 dims_4_9_8 jets_4_11_10 jets_3_9_8
  dims_5_8_6 dims_4_6_3 jets_4_8_6 jets_3_6_3
  dims_5_7_8 dims_4_4_7 jets_4_7_8 jets_3_4_7
  dims_5_6_8 dims_4_3_6 jets_4_6_8 jets_3_3_6
  dims_4_3_5 jets_3_3_5 from ProximityPrize.SubmissionLower.FrontBranch4
open private dims_5_10_11 jets_4_10_11 dims_4_8_9 jets_3_8_9 dims_4_5_3 jets_3_5_3 from ProximityPrize.SubmissionLower.SilverBase
abbrev tariff : ℕ := 0x1eda8e86f984d83
private theorem priced (E M zeroFee cap : ℕ)
    (h : zeroFee * 16304^2 + 5 * E * (43691*M)^2 ≤ cap * 16304^2)
    (hc : cap ≤ tariff) :
    (zeroFee : ℚ) + 5 * ((E : ℚ) * ((43691 / 16304 : ℚ) * M)^2) ≤ tariff :=
  (rational_fee E M zeroFee cap 43691 16304 (by decide) h).trans (by exact_mod_cast hc)
local notation "fee!" e "," m "," z "," c => priced e m z c (by decide) (by decide)
end P3_4
end
