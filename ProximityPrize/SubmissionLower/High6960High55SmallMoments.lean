import ProximityPrize.SubmissionLower.UpperBranch1

/-! Selected bank receipts from the 69.55 donor's GoldBranch7N1. -/
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

private theorem r1A:momentEstimate 15 3=2194:=rfl

private theorem r2A:momentEstimate 28 4=17031:=rfl

private theorem r3A:momentEstimate 29 6=24733:=rfl

private theorem r4A:momentEstimate 47 10=156979:=rfl

private theorem r5A:momentEstimate 53 9=211909:=rfl

private theorem r6A:momentEstimate 75 16=957077:=rfl

private theorem r7A:momentEstimate 89 15=1564938:=rfl

private theorem r8A:momentEstimate 101 22=3108650:=rfl

private theorem r10A:momentEstimate 108 24=4103823:=rfl

private theorem r12A:momentEstimate 119 26=5931589:=rfl

private theorem r14A:momentEstimate 130 29=8531244:=rfl

private theorem r16A:momentEstimate 141 24=9562298:=rfl

private theorem r17A:momentEstimate 141 31=11621252:=rfl

private theorem r19A:momentEstimate 149 33=14526868:=rfl

private theorem r20A:momentEstimate 150 33=14840297:=rfl

private theorem r23A_block_0:P1_7_1_3.blockEstimate 173 32 32 192=22790651:=rfl

private theorem r23A_block_1:P1_7_1_3.blockEstimate 173 32 224 13=42218:=rfl

private theorem r23A : momentEstimate 173 32 = 22832869 := moment_from_blocks
  [(192,22790651),(13,42218)]
  ⟨r23A_block_0,r23A_block_1,True.intro⟩ rfl rfl

private theorem r24A_block_0:P1_7_1_3.blockEstimate 197 43 43 192=41550683:=rfl

private theorem r24A_block_1:P1_7_1_3.blockEstimate 197 43 235 48=1768299:=rfl

private theorem r24A : momentEstimate 197 43 = 43318982 := moment_from_blocks
  [(192,41550683),(48,1768299)]
  ⟨r24A_block_0,r24A_block_1,True.intro⟩ rfl rfl

private theorem r25A_block_0:P1_7_1_3.blockEstimate 226 50 50 192=65796440:=rfl

private theorem r25A_block_1:P1_7_1_3.blockEstimate 226 50 242 84=9604957:=rfl

private theorem r25A : momentEstimate 226 50 = 75401397 := moment_from_blocks
  [(192,65796440),(84,9604957)]
  ⟨r25A_block_0,r25A_block_1,True.intro⟩ rfl rfl

end P3_7_1
