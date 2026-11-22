import ProximityPrize.SubmissionLower.GoldBranch7
import ProximityPrize.SubmissionLower.UpperBranch1
set_option autoImplicit true
section
namespace P3_7_1
open P1_7 (Bank)
open P1_7_1 (nodeRows groupedPoleMoment)
open P1_7_1_2 (six_nodeRows sixPerNode)
open P1_7_1_3 (momentEstimate grouped_bound)
open P1_7_1_3_2 (ExactMoment)
structure BankOK (t : Bank) : Prop where
  nodes : nodeRows t.shape = t.nodeRows
  moment : groupedPoleMoment t.shape.B t.shape.J ≤ t.poleMoment ∧ t.shape.B < K1.p
theorem checked (t : Bank) {m B J N M : ℕ}
    (hm : t.shape.m = m) (hB : t.shape.B = B) (hJ : t.shape.J = J)
    (hN : t.nodeRows = N) (hM : t.poleMoment = M)
    (hmJ : 2*J ≤ m) (hJB : m+J ≤ B+1)
    (hnode : 262144 * sixPerNode (m-2*J) J = 6*N)
    (hchar : B < K1.p) (hbound : momentEstimate B J = M) : BankOK t := by
  have h := six_nodeRows t.shape (by rw [hm, hJ]; exact hmJ) (by rw [hm, hJ, hB]; exact hJB)
  rw [hm, hJ, hnode, ← hN] at h
  refine ⟨by omega, ?_⟩
  rw [hB, hJ, hM]
  exact ⟨(grouped_bound _ _).trans hbound.le, hchar⟩
theorem moment_instance {B J M : ℕ} [h : ExactMoment B J M] : momentEstimate B J = M :=
  h.eq_moment
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
private theorem r1A : momentEstimate 15 3 = 2194 := rfl
private theorem r2A : momentEstimate 28 4 = 17031 := rfl
private theorem r3A : momentEstimate 29 6 = 24733 := rfl
private theorem r4A : momentEstimate 47 10 = 156979 := rfl
private theorem r5A : momentEstimate 53 9 = 211909 := rfl
private theorem r6A : momentEstimate 75 16 = 957077 := rfl
private theorem r7A : momentEstimate 89 15 = 1564938 := rfl
private theorem r8A : momentEstimate 101 22 = 3108650 := rfl
private theorem r9A : momentEstimate 105 23 = 3635193 := rfl
private theorem r10A : momentEstimate 108 24 = 4103823 := rfl
private theorem r11A : momentEstimate 111 24 = 4477423 := rfl
private theorem r12A : momentEstimate 119 26 = 5931589 := rfl
private theorem r13A : momentEstimate 125 27 = 7136131 := rfl
private theorem r14A : momentEstimate 130 29 = 8531244 := rfl
private theorem r15A : momentEstimate 137 30 = 10343855 := rfl
private theorem r16A : momentEstimate 141 24 = 9562298 := rfl
private theorem r17A : momentEstimate 141 31 = 11621252 := rfl
private theorem r18A : momentEstimate 147 32 = 13594640 := rfl
private theorem r19A : momentEstimate 149 33 = 14526868 := rfl
private theorem r20A : momentEstimate 150 33 = 14840297 := rfl
private theorem r21A : momentEstimate 158 34 = 17916156 := rfl
private theorem r22A_block_0 : P1_7_1_3.blockEstimate 159 35 35 192 = 18685378 := rfl

private theorem r22A_block_1 : P1_7_1_3.blockEstimate 159 35 227 2 = 476 := rfl

private theorem r22A : momentEstimate 159 35 = 18685854 := moment_from_blocks
  [(192,18685378),(2,476)]
  ⟨r22A_block_0, r22A_block_1, True.intro⟩ rfl rfl
private theorem r23A_block_0 : P1_7_1_3.blockEstimate 173 32 32 192 = 22790651 := rfl

private theorem r23A_block_1 : P1_7_1_3.blockEstimate 173 32 224 13 = 42218 := rfl

private theorem r23A : momentEstimate 173 32 = 22832869 := moment_from_blocks
  [(192,22790651),(13,42218)]
  ⟨r23A_block_0, r23A_block_1, True.intro⟩ rfl rfl
private theorem r24A_block_0 : P1_7_1_3.blockEstimate 197 43 43 192 = 41550683 := rfl

private theorem r24A_block_1 : P1_7_1_3.blockEstimate 197 43 235 48 = 1768299 := rfl

private theorem r24A : momentEstimate 197 43 = 43318982 := moment_from_blocks
  [(192,41550683),(48,1768299)]
  ⟨r24A_block_0, r24A_block_1, True.intro⟩ rfl rfl
private theorem r25A_block_0 : P1_7_1_3.blockEstimate 226 50 50 192 = 65796440 := rfl

private theorem r25A_block_1 : P1_7_1_3.blockEstimate 226 50 242 84 = 9604957 := rfl

private theorem r25A : momentEstimate 226 50 = 75401397 := moment_from_blocks
  [(192,65796440),(84,9604957)]
  ⟨r25A_block_0, r25A_block_1, True.intro⟩ rfl rfl
private theorem r26A_block_0 : P1_7_1_3.blockEstimate 270 60 60 192 = 0x68121f5 := rfl

private theorem r26A_block_1 : P1_7_1_3.blockEstimate 270 60 252 138 = 44087081 := rfl

private theorem r26A : momentEstimate 270 60 = 0x921d91e := moment_from_blocks
  [(192,0x68121f5),(138,44087081)]
  ⟨r26A_block_0, r26A_block_1, True.intro⟩ rfl rfl
private theorem r27A_block_0 : P1_7_1_3.blockEstimate 294 65 65 192 = 0x808bd50 := rfl

private theorem r27A_block_1 : P1_7_1_3.blockEstimate 294 65 257 167 = 79226879 := rfl

private theorem r27A : momentEstimate 294 65 = 0xcc1a54f := moment_from_blocks
  [(192,0x808bd50),(167,79226879)]
  ⟨r27A_block_0, r27A_block_1, True.intro⟩ rfl rfl
private theorem r28A_block_0 : P1_7_1_3.blockEstimate 306 68 68 192 = 0x8ddfa7f := rfl

private theorem r28A_block_1 : P1_7_1_3.blockEstimate 306 68 260 182 = 0x625310d := rfl

private theorem r28A : momentEstimate 306 68 = 0xf032b8c := moment_from_blocks
  [(192,0x8ddfa7f),(182,0x625310d)]
  ⟨r28A_block_0, r28A_block_1, True.intro⟩ rfl rfl
private theorem r29A_block_0 : P1_7_1_3.blockEstimate 324 73 73 192 = 0xa3139de := rfl

private theorem r29A_block_1 : P1_7_1_3.blockEstimate 324 73 265 192 = 0x8d7fbbb := rfl

private theorem r29A_block_2 : P1_7_1_3.blockEstimate 324 73 457 13 = 80270 := rfl

private theorem r29A : momentEstimate 324 73 = 0x130a6f27 := moment_from_blocks
  [(192,0xa3139de),(192,0x8d7fbbb),(13,80270)]
  ⟨r29A_block_0, r29A_block_1, r29A_block_2, True.intro⟩ rfl rfl
private theorem r30A_block_0 : P1_7_1_3.blockEstimate 327 73 73 192 = 0xa5b3786 := rfl

private theorem r30A_block_1 : P1_7_1_3.blockEstimate 327 73 265 192 = 0x93f5af2 := rfl

private theorem r30A_block_2 : P1_7_1_3.blockEstimate 327 73 457 16 = 142140 := rfl

private theorem r30A : momentEstimate 327 73 = 0x139cbdb4 := moment_from_blocks
  [(192,0xa5b3786),(192,0x93f5af2),(16,142140)]
  ⟨r30A_block_0, r30A_block_1, r30A_block_2, True.intro⟩ rfl rfl
private theorem r31A_block_0 : P1_7_1_3.blockEstimate 341 75 75 192 = 0xb474b6d := rfl

private theorem r31A_block_1 : P1_7_1_3.blockEstimate 341 75 267 192 = 0xb90f0fd := rfl

private theorem r31A_block_2 : P1_7_1_3.blockEstimate 341 75 459 32 = 1021768 := rfl

private theorem r31A : momentEstimate 341 75 = 0x16e7d3b2 := moment_from_blocks
  [(192,0xb474b6d),(192,0xb90f0fd),(32,1021768)]
  ⟨r31A_block_0, r31A_block_1, r31A_block_2, True.intro⟩ rfl rfl
private theorem r32A_block_0 : P1_7_1_3.blockEstimate 347 75 75 192 = 0xb9c8d15 := rfl

private theorem r32A_block_1 : P1_7_1_3.blockEstimate 347 75 267 192 = 0xc82cc78 := rfl

private theorem r32A_block_2 : P1_7_1_3.blockEstimate 347 75 459 38 = 1692095 := rfl

private theorem r32A : momentEstimate 347 75 = 0x18392b4c := moment_from_blocks
  [(192,0xb9c8d15),(192,0xc82cc78),(38,1692095)]
  ⟨r32A_block_0, r32A_block_1, r32A_block_2, True.intro⟩ rfl rfl
private theorem r33A_block_0 : P1_7_1_3.blockEstimate 362 81 81 192 = 0xcedc43c := rfl

private theorem r33A_block_1 : P1_7_1_3.blockEstimate 362 81 273 192 = 0x1023a26f := rfl

private theorem r33A_block_2 : P1_7_1_3.blockEstimate 362 81 465 59 = 6179160 := rfl

private theorem r33A : momentEstimate 362 81 = 0x1d6fb003 := moment_from_blocks
  [(192,0xcedc43c),(192,0x1023a26f),(59,6179160)]
  ⟨r33A_block_0, r33A_block_1, r33A_block_2, True.intro⟩ rfl rfl
private theorem r34A_block_0 : P1_7_1_3.blockEstimate 362 82 82 192 = 0xd0114a6 := rfl

private theorem r34A_block_1 : P1_7_1_3.blockEstimate 362 82 274 192 = 0x1052f371 := rfl

private theorem r34A_block_2 : P1_7_1_3.blockEstimate 362 82 466 60 = 6481635 := rfl

private theorem r34A : momentEstimate 362 82 = 0x1db6eefa := moment_from_blocks
  [(192,0xd0114a6),(192,0x1052f371),(60,6481635)]
  ⟨r34A_block_0, r34A_block_1, r34A_block_2, True.intro⟩ rfl rfl
private theorem r35A_block_0 : P1_7_1_3.blockEstimate 386 85 85 192 = 0xea4c745 := rfl

private theorem r35A_block_1 : P1_7_1_3.blockEstimate 386 85 277 192 = 0x15b39ae5 := rfl

private theorem r35A_block_2 : P1_7_1_3.blockEstimate 386 85 469 87 = 19974493 := rfl

private theorem r35A : momentEstimate 386 85 = 0x25892b87 := moment_from_blocks
  [(192,0xea4c745),(192,0x15b39ae5),(87,19974493)]
  ⟨r35A_block_0, r35A_block_1, r35A_block_2, True.intro⟩ rfl rfl
private theorem r36A_block_0 : P1_7_1_3.blockEstimate 480 101 101 192 = 0x15b81f79 := rfl

private theorem r36A_block_1 : P1_7_1_3.blockEstimate 480 101 293 192 = 0x31e4e442 := rfl

private theorem r36A_block_2 : P1_7_1_3.blockEstimate 480 101 485 192 = 0xead24ec := rfl

private theorem r36A_block_3 : P1_7_1_3.blockEstimate 480 101 677 5 = 10521 := rfl

private theorem r36A : momentEstimate 480 101 = 0x564a51c0 := moment_from_blocks
  [(192,0x15b81f79),(192,0x31e4e442),(192,0xead24ec),(5,10521)]
  ⟨r36A_block_0, r36A_block_1, r36A_block_2, r36A_block_3, True.intro⟩ rfl rfl
private theorem r37A_block_0 : P1_7_1_3.blockEstimate 489 103 103 192 = 0x1673e52a := rfl

private theorem r37A_block_1 : P1_7_1_3.blockEstimate 489 103 295 192 = 0x352e8780 := rfl

private theorem r37A_block_2 : P1_7_1_3.blockEstimate 489 103 487 192 = 0x1157e3c7 := rfl

private theorem r37A_block_3 : P1_7_1_3.blockEstimate 489 103 679 16 = 214068 := rfl

private theorem r37A : momentEstimate 489 103 = 0x5cfd94a5 := moment_from_blocks
  [(192,0x1673e52a),(192,0x352e8780),(192,0x1157e3c7),(16,214068)]
  ⟨r37A_block_0, r37A_block_1, r37A_block_2, r37A_block_3, True.intro⟩ rfl rfl
private theorem r38A_block_0 : P1_7_1_3.blockEstimate 495 104 104 192 = 0x16eabb16 := rfl

private theorem r38A_block_1 : P1_7_1_3.blockEstimate 495 104 296 192 = 0x3746f460 := rfl

private theorem r38A_block_2 : P1_7_1_3.blockEstimate 495 104 488 192 = 0x13329b79 := rfl

private theorem r38A_block_3 : P1_7_1_3.blockEstimate 495 104 680 23 = 592504 := rfl

private theorem r38A : momentEstimate 495 104 = 0x616d5567 := moment_from_blocks
  [(192,0x16eabb16),(192,0x3746f460),(192,0x13329b79),(23,592504)]
  ⟨r38A_block_0, r38A_block_1, r38A_block_2, r38A_block_3, True.intro⟩ rfl rfl
private theorem r39A_block_0 : P1_7_1_3.blockEstimate 499 105 105 192 = 0x174097de := rfl

private theorem r39A_block_1 : P1_7_1_3.blockEstimate 499 105 297 192 = 0x38d2a9a0 := rfl

private theorem r39A_block_2 : P1_7_1_3.blockEstimate 499 105 489 192 = 0x14951936 := rfl

private theorem r39A_block_3 : P1_7_1_3.blockEstimate 499 105 681 28 = 1038730 := rfl

private theorem r39A : momentEstimate 499 105 = 0x64b8343e := moment_from_blocks
  [(192,0x174097de),(192,0x38d2a9a0),(192,0x14951936),(28,1038730)]
  ⟨r39A_block_0, r39A_block_1, r39A_block_2, r39A_block_3, True.intro⟩ rfl rfl
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
private theorem r1B_block_0 : P1_7_1_3.blockEstimate 543 114 114 192 = 0x1acca72b := rfl

private theorem r1B_block_1 : P1_7_1_3.blockEstimate 543 114 306 192 = 0x49cce7c0 := rfl

private theorem r1B_block_2 : P1_7_1_3.blockEstimate 543 114 498 192 = 0x26c5cd69 := rfl

private theorem r1B_block_3 : P1_7_1_3.blockEstimate 543 114 690 81 = 23656913 := rfl

private theorem r1B : momentEstimate 543 114 = 0x8cc85625 := moment_from_blocks
  [(192,0x1acca72b),(192,0x49cce7c0),(192,0x26c5cd69),(81,23656913)]
  ⟨r1B_block_0, r1B_block_1, r1B_block_2, r1B_block_3, True.intro⟩ rfl rfl
private theorem r2B_block_0 : P1_7_1_3.blockEstimate 596 126 126 192 = 0x1f2189eb := rfl

private theorem r2B_block_1 : P1_7_1_3.blockEstimate 596 126 318 192 = 0x60a4c0e0 := rfl

private theorem r2B_block_2 : P1_7_1_3.blockEstimate 596 126 510 192 = 0x44f74cde := rfl

private theorem r2B_block_3 : P1_7_1_3.blockEstimate 596 126 702 146 = 0x869414c := rfl

private theorem r2B : momentEstimate 596 126 = 0xcd26d8f5 := moment_from_blocks
  [(192,0x1f2189eb),(192,0x60a4c0e0),(192,0x44f74cde),(146,0x869414c)]
  ⟨r2B_block_0, r2B_block_1, r2B_block_2, r2B_block_3, True.intro⟩ rfl rfl
private theorem r3B_block_0 : P1_7_1_3.blockEstimate 615 137 137 192 = 0x20f7b1f6 := rfl

private theorem r3B_block_1 : P1_7_1_3.blockEstimate 615 137 329 192 = 0x6cef9fa0 := rfl

private theorem r3B_block_2 : P1_7_1_3.blockEstimate 615 137 521 192 = 0x556e3a6f := rfl

private theorem r3B_block_3 : P1_7_1_3.blockEstimate 615 137 713 176 = 0xec39232 := rfl

private theorem r3B : momentEstimate 615 137 = 0xf2191e37 := moment_from_blocks
  [(192,0x20f7b1f6),(192,0x6cef9fa0),(192,0x556e3a6f),(176,0xec39232)]
  ⟨r3B_block_0, r3B_block_1, r3B_block_2, r3B_block_3, True.intro⟩ rfl rfl
private theorem r4B_block_0 : P1_7_1_3.blockEstimate 671 142 142 192 = 0x25141ae4 := rfl

private theorem r4B_block_1 : P1_7_1_3.blockEstimate 671 142 334 192 = 0x8379c980 := rfl

private theorem r4B_block_2 : P1_7_1_3.blockEstimate 671 142 526 192 = 0x7b8a266a := rfl

private theorem r4B_block_3 : P1_7_1_3.blockEstimate 671 142 718 192 = 0x24e9a86a := rfl

private theorem r4B_block_4 : P1_7_1_3.blockEstimate 671 142 910 45 = 5446518 := rfl

private theorem r4B : momentEstimate 671 142 = 0x14954ceae := moment_from_blocks
  [(192,0x25141ae4),(192,0x8379c980),(192,0x7b8a266a),(192,0x24e9a86a),(45,5446518)]
  ⟨r4B_block_0, r4B_block_1, r4B_block_2, r4B_block_3, r4B_block_4, True.intro⟩ rfl rfl
private theorem r5B_block_0 : P1_7_1_3.blockEstimate 724 153 153 192 = 0x2927a7ba := rfl

private theorem r5B_block_1 : P1_7_1_3.blockEstimate 724 153 345 192 = 0x9dac94a0 := rfl

private theorem r5B_block_2 : P1_7_1_3.blockEstimate 724 153 537 192 = 0xa8abfa1e := rfl

private theorem r5B_block_3 : P1_7_1_3.blockEstimate 724 153 729 192 = 0x4974c902 := rfl

private theorem r5B_block_4 : P1_7_1_3.blockEstimate 724 153 921 109 = 75722962 := rfl

private theorem r5B : momentEstimate 724 153 = 0x1bd78704c := moment_from_blocks
  [(192,0x2927a7ba),(192,0x9dac94a0),(192,0xa8abfa1e),(192,0x4974c902),(109,75722962)]
  ⟨r5B_block_0, r5B_block_1, r5B_block_2, r5B_block_3, r5B_block_4, True.intro⟩ rfl rfl
private theorem r6B_block_0 : P1_7_1_3.blockEstimate 813 172 172 192 = 0x2fc7ce93 := rfl

private theorem r6B_block_1 : P1_7_1_3.blockEstimate 813 172 364 192 = 0xcc995ae0 := rfl

private theorem r6B_block_2 : P1_7_1_3.blockEstimate 813 172 556 192 = 0xfe654ae0 := rfl

private theorem r6B_block_3 : P1_7_1_3.blockEstimate 813 172 748 192 = 0xa4733f8f := rfl

private theorem r6B_block_4 : P1_7_1_3.blockEstimate 813 172 940 192 = 0x24b91683 := rfl

private theorem r6B_block_5 : P1_7_1_3.blockEstimate 813 172 1132 25 = 1240582 := rfl

private theorem r6B : momentEstimate 813 172 = 0x2c405b86b := moment_from_blocks
  [(192,0x2fc7ce93),(192,0xcc995ae0),(192,0xfe654ae0),(192,0xa4733f8f),(192,0x24b91683),
    (25,1240582)]
  ⟨r6B_block_0, r6B_block_1, r6B_block_2, r6B_block_3, r6B_block_4, r6B_block_5, True.intro⟩ rfl rfl
private theorem r7B_block_0 : P1_7_1_3.blockEstimate 942 212 212 192 = 0x390aedb0 := rfl

private theorem r7B_block_1 : P1_7_1_3.blockEstimate 942 212 404 192 = 0x11bbb70db := rfl

private theorem r7B_block_2 : P1_7_1_3.blockEstimate 942 212 596 192 = 0x19eb7cfc0 := rfl

private theorem r7B_block_3 : P1_7_1_3.blockEstimate 942 212 788 192 = 0x16e33e996 := rfl

private theorem r7B_block_4 : P1_7_1_3.blockEstimate 942 212 980 192 = 0xb7980703 := rfl

private theorem r7B_block_5 : P1_7_1_3.blockEstimate 942 212 1172 192 = 0x1f9c1048 := rfl

private theorem r7B_block_6 : P1_7_1_3.blockEstimate 942 212 1364 2 = 2825 := rfl

private theorem r7B : momentEstimate 942 212 = 0x538e63a35 := moment_from_blocks
  [(192,0x390aedb0),(192,0x11bbb70db),(192,0x19eb7cfc0),(192,0x16e33e996),(192,0xb7980703),
    (192,0x1f9c1048),(2,2825)]
  ⟨r7B_block_0, r7B_block_1, r7B_block_2, r7B_block_3, r7B_block_4, r7B_block_5, r7B_block_6, True.intro⟩ rfl rfl
private theorem r8B_block_0 : P1_7_1_3.blockEstimate 1208 255 255 192 = 0x4c0a0030 := rfl

private theorem r8B_block_1 : P1_7_1_3.blockEstimate 1208 255 447 192 = 0x1abaaa810 := rfl

private theorem r8B_block_2 : P1_7_1_3.blockEstimate 1208 255 639 192 = 0x2e8667000 := rfl

private theorem r8B_block_3 : P1_7_1_3.blockEstimate 1208 255 831 192 = 0x34f9e7000 := rfl

private theorem r8B_block_4 : P1_7_1_3.blockEstimate 1208 255 1023 192 = 0x2ded6cdb2 := rfl

private theorem r8B_block_5 : P1_7_1_3.blockEstimate 1208 255 1215 192 = 0x1b9f42a13 := rfl

private theorem r8B_block_6 : P1_7_1_3.blockEstimate 1208 255 1407 192 = 0x96ce821d := rfl

private theorem r8B_block_7 : P1_7_1_3.blockEstimate 1208 255 1599 119 = 0xa04af06 := rfl

private theorem r8B : momentEstimate 1208 255 = 0xd6957b128 := moment_from_blocks
  [(192,0x4c0a0030),(192,0x1abaaa810),(192,0x2e8667000),(192,0x34f9e7000),(192,0x2ded6cdb2),
    (192,0x1b9f42a13),(192,0x96ce821d),(119,0xa04af06)]
  ⟨r8B_block_0, r8B_block_1, r8B_block_2, r8B_block_3, r8B_block_4, r8B_block_5, r8B_block_6, r8B_block_7, True.intro⟩ rfl rfl
private theorem r9B_block_0 : P1_7_1_3.blockEstimate 1383 310 310 192 = 0x588963f0 := rfl

private theorem r9B_block_1 : P1_7_1_3.blockEstimate 1383 310 502 192 = 0x2108c928e := rfl

private theorem r9B_block_2 : P1_7_1_3.blockEstimate 1383 310 694 192 = 0x40bc37100 := rfl

private theorem r9B_block_3 : P1_7_1_3.blockEstimate 1383 310 886 192 = 0x513895100 := rfl

private theorem r9B_block_4 : P1_7_1_3.blockEstimate 1383 310 1078 192 = 0x514e73100 := rfl

private theorem r9B_block_5 : P1_7_1_3.blockEstimate 1383 310 1270 192 = 0x411fc3a35 := rfl

private theorem r9B_block_6 : P1_7_1_3.blockEstimate 1383 310 1462 192 = 0x26aaf3efb := rfl

private theorem r9B_block_7 : P1_7_1_3.blockEstimate 1383 310 1654 192 = 0xeadc69d9 := rfl

private theorem r9B_block_8 : P1_7_1_3.blockEstimate 1383 310 1846 157 = 0x19e8ba84 := rfl

private theorem r9B : momentEstimate 1383 310 = 0x181eba870b := moment_from_blocks
  [(192,0x588963f0),(192,0x2108c928e),(192,0x40bc37100),(192,0x513895100),(192,0x514e73100),
    (192,0x411fc3a35),(192,0x26aaf3efb),(192,0xeadc69d9),(157,0x19e8ba84)]
  ⟨r9B_block_0, r9B_block_1, r9B_block_2, r9B_block_3, r9B_block_4, r9B_block_5, r9B_block_6, r9B_block_7, r9B_block_8, True.intro⟩ rfl rfl
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
private theorem r1C_block_0 : P1_7_1_3.blockEstimate 1429 302 302 192 = 0x5bd25f70 := rfl

private theorem r1C_block_1 : P1_7_1_3.blockEstimate 1429 302 494 192 = 0x22599cd36 := rfl

private theorem r1C_block_2 : P1_7_1_3.blockEstimate 1429 302 686 192 = 0x43235a6c0 := rfl

private theorem r1C_block_3 : P1_7_1_3.blockEstimate 1429 302 878 192 = 0x54f28e6c0 := rfl

private theorem r1C_block_4 : P1_7_1_3.blockEstimate 1429 302 1070 192 = 0x56c7426c0 := rfl

private theorem r1C_block_5 : P1_7_1_3.blockEstimate 1429 302 1262 192 = 0x48a2954aa := rfl

private theorem r1C_block_6 : P1_7_1_3.blockEstimate 1429 302 1454 192 = 0x2de0b6d85 := rfl

private theorem r1C_block_7 : P1_7_1_3.blockEstimate 1429 302 1646 192 = 0x138162636 := rfl

private theorem r1C_block_8 : P1_7_1_3.blockEstimate 1429 302 1838 192 = 0x326e7ef0 := rfl

private theorem r1C_block_9 : P1_7_1_3.blockEstimate 1429 302 2030 3 = 9997 := rfl

private theorem r1C : momentEstimate 1429 302 = 0x1a41f86f48 := moment_from_blocks
  [(192,0x5bd25f70),(192,0x22599cd36),(192,0x43235a6c0),(192,0x54f28e6c0),(192,0x56c7426c0),
    (192,0x48a2954aa),(192,0x2de0b6d85),(192,0x138162636),(192,0x326e7ef0),(3,9997)]
  ⟨r1C_block_0, r1C_block_1, r1C_block_2, r1C_block_3, r1C_block_4, r1C_block_5, r1C_block_6, r1C_block_7, r1C_block_8, r1C_block_9, True.intro⟩ rfl rfl
private theorem r2C_block_0 : P1_7_1_3.blockEstimate 1689 356 356 192 = 0x6e63c070 := rfl

private theorem r2C_block_1 : P1_7_1_3.blockEstimate 1689 356 548 192 = 0x2abfac68d := rfl

private theorem r2C_block_2 : P1_7_1_3.blockEstimate 1689 356 740 192 = 0x5ca3ddee0 := rfl

private theorem r2C_block_3 : P1_7_1_3.blockEstimate 1689 356 932 192 = 0x7fb1acee0 := rfl

private theorem r2C_block_4 : P1_7_1_3.blockEstimate 1689 356 1124 192 = 0x8febfbee0 := rfl

private theorem r2C_block_5 : P1_7_1_3.blockEstimate 1689 356 1316 192 = 0x8d52caee0 := rfl

private theorem r2C_block_6 : P1_7_1_3.blockEstimate 1689 356 1508 192 = 0x77e6381c4 := rfl

private theorem r2C_block_7 : P1_7_1_3.blockEstimate 1689 356 1700 192 = 0x52c7446a1 := rfl

private theorem r2C_block_8 : P1_7_1_3.blockEstimate 1689 356 1892 192 = 0x2c193ddcc := rfl

private theorem r2C_block_9 : P1_7_1_3.blockEstimate 1689 356 2084 192 = 0xe6e9b818 := rfl

private theorem r2C_block_10 : P1_7_1_3.blockEstimate 1689 356 2276 125 = 0x1065f110 := rfl

private theorem r2C : momentEstimate 1689 356 = 0x33175ef1d6 := moment_from_blocks
  [(192,0x6e63c070),(192,0x2abfac68d),(192,0x5ca3ddee0),(192,0x7fb1acee0),(192,0x8febfbee0),
    (192,0x8d52caee0),(192,0x77e6381c4),(192,0x52c7446a1),(192,0x2c193ddcc),(192,0xe6e9b818),
    (125,0x1065f110)]
  ⟨r2C_block_0, r2C_block_1, r2C_block_2, r2C_block_3, r2C_block_4, r2C_block_5, r2C_block_6, r2C_block_7, r2C_block_8, r2C_block_9, r2C_block_10, True.intro⟩ rfl rfl
private theorem r3C_block_0 : P1_7_1_3.blockEstimate 1761 373 373 192 = 0x73881270 := rfl

private theorem r3C_block_1 : P1_7_1_3.blockEstimate 1761 373 565 192 = 0x2cfec2449 := rfl

private theorem r3C_block_2 : P1_7_1_3.blockEstimate 1761 373 757 192 = 0x63f6c4be0 := rfl

private theorem r3C_block_3 : P1_7_1_3.blockEstimate 1761 373 949 192 = 0x8cd259be0 := rfl

private theorem r3C_block_4 : P1_7_1_3.blockEstimate 1761 373 1141 192 = 0xa1f4eebe0 := rfl

private theorem r3C_block_5 : P1_7_1_3.blockEstimate 1761 373 1333 192 = 0xa35e83be0 := rfl

private theorem r3C_block_6 : P1_7_1_3.blockEstimate 1761 373 1525 192 = 0x910f18be0 := rfl

private theorem r3C_block_7 : P1_7_1_3.blockEstimate 1761 373 1717 192 = 0x6c3901bd5 := rfl

private theorem r3C_block_8 : P1_7_1_3.blockEstimate 1761 373 1909 192 = 0x40eaa1aed := rfl

private theorem r3C_block_9 : P1_7_1_3.blockEstimate 1761 373 2101 192 = 0x1bd6591c8 := rfl

private theorem r3C_block_10 : P1_7_1_3.blockEstimate 1761 373 2293 192 = 0x527843d8 := rfl

private theorem r3C_block_11 : P1_7_1_3.blockEstimate 1761 373 2485 22 = 1887937 := rfl

private theorem r3C : momentEstimate 1761 373 = 0x3c9863ad3c := moment_from_blocks
  [(192,0x73881270),(192,0x2cfec2449),(192,0x63f6c4be0),(192,0x8cd259be0),(192,0xa1f4eebe0),
    (192,0xa35e83be0),(192,0x910f18be0),(192,0x6c3901bd5),(192,0x40eaa1aed),(192,0x1bd6591c8),
    (192,0x527843d8),(22,1887937)]
  ⟨r3C_block_0, r3C_block_1, r3C_block_2, r3C_block_3, r3C_block_4, r3C_block_5, r3C_block_6, r3C_block_7, r3C_block_8, r3C_block_9, r3C_block_10, r3C_block_11, True.intro⟩ rfl rfl
private theorem r4C_block_0 : P1_7_1_3.blockEstimate 2034 430 430 192 = 0x87071eb0 := rfl

private theorem r4C_block_1 : P1_7_1_3.blockEstimate 2034 430 622 192 = 0x3573562b0 := rfl

private theorem r4C_block_2 : P1_7_1_3.blockEstimate 2034 430 814 192 = 0x7e621ec21 := rfl

private theorem r4C_block_3 : P1_7_1_3.blockEstimate 2034 430 1006 192 = 0xbf36e5620 := rfl

private theorem r4C_block_4 : P1_7_1_3.blockEstimate 2034 430 1198 192 = 0xe96a84620 := rfl

private theorem r4C_block_5 : P1_7_1_3.blockEstimate 2034 430 1390 192 = 0xfce3a3620 := rfl

private theorem r4C_block_6 : P1_7_1_3.blockEstimate 2034 430 1582 192 = 0xf9a242620 := rfl

private theorem r4C_block_7 : P1_7_1_3.blockEstimate 2034 430 1774 192 = 0xdfa661620 := rfl

private theorem r4C_block_8 : P1_7_1_3.blockEstimate 2034 430 1966 192 = 0xafb904338 := rfl

private theorem r4C_block_9 : P1_7_1_3.blockEstimate 2034 430 2158 192 = 0x75981284b := rfl

private theorem r4C_block_10 : P1_7_1_3.blockEstimate 2034 430 2350 192 = 0x3fcfcc59c := rfl

private theorem r4C_block_11 : P1_7_1_3.blockEstimate 2034 430 2542 192 = 0x1713adfc0 := rfl

private theorem r4C_block_12 : P1_7_1_3.blockEstimate 2034 430 2734 160 = 0x28ffa820 := rfl

private theorem r4C : momentEstimate 2034 430 = 0x6b9d823520 := moment_from_blocks
  [(192,0x87071eb0),(192,0x3573562b0),(192,0x7e621ec21),(192,0xbf36e5620),(192,0xe96a84620),
    (192,0xfce3a3620),(192,0xf9a242620),(192,0xdfa661620),(192,0xafb904338),(192,0x75981284b),
    (192,0x3fcfcc59c),(192,0x1713adfc0),(160,0x28ffa820)]
  ⟨r4C_block_0, r4C_block_1, r4C_block_2, r4C_block_3, r4C_block_4, r4C_block_5, r4C_block_6, r4C_block_7, r4C_block_8, r4C_block_9, r4C_block_10, r4C_block_11, r4C_block_12, True.intro⟩ rfl rfl
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
private theorem r1D_block_0 : P1_7_1_3.blockEstimate 2038 431 431 192 = 0x87503fb0 := rfl

private theorem r1D_block_1 : P1_7_1_3.blockEstimate 2038 431 623 192 = 0x35930c3b0 := rfl

private theorem r1D_block_2 : P1_7_1_3.blockEstimate 2038 431 815 192 = 0x7ec53f14c := rfl

private theorem r1D_block_3 : P1_7_1_3.blockEstimate 2038 431 1007 192 = 0xc0032e500 := rfl

private theorem r1D_block_4 : P1_7_1_3.blockEstimate 2038 431 1199 192 = 0xea9436500 := rfl

private theorem r1D_block_5 : P1_7_1_3.blockEstimate 2038 431 1391 192 = 0xfe5d3e500 := rfl

private theorem r1D_block_6 : P1_7_1_3.blockEstimate 2038 431 1583 192 = 0xfb5e46500 := rfl

private theorem r1D_block_7 : P1_7_1_3.blockEstimate 2038 431 1775 192 = 0xe1974e500 := rfl

private theorem r1D_block_8 : P1_7_1_3.blockEstimate 2038 431 1967 192 = 0xb1c2fd710 := rfl

private theorem r1D_block_9 : P1_7_1_3.blockEstimate 2038 431 2159 192 = 0x776ae5c50 := rfl

private theorem r1D_block_10 : P1_7_1_3.blockEstimate 2038 431 2351 192 = 0x413cd8ccd := rfl

private theorem r1D_block_11 : P1_7_1_3.blockEstimate 2038 431 2543 192 = 0x17f4c6c88 := rfl

private theorem r1D_block_12 : P1_7_1_3.blockEstimate 2038 431 2735 165 = 0x2cf6bf79 := rfl

private theorem r1D : momentEstimate 2038 431 = 0x6c7e6759da := moment_from_blocks
  [(192,0x87503fb0),(192,0x35930c3b0),(192,0x7ec53f14c),(192,0xc0032e500),(192,0xea9436500),
    (192,0xfe5d3e500),(192,0xfb5e46500),(192,0xe1974e500),(192,0xb1c2fd710),(192,0x776ae5c50),
    (192,0x413cd8ccd),(192,0x17f4c6c88),(165,0x2cf6bf79)]
  ⟨r1D_block_0, r1D_block_1, r1D_block_2, r1D_block_3, r1D_block_4, r1D_block_5, r1D_block_6, r1D_block_7, r1D_block_8, r1D_block_9, r1D_block_10, r1D_block_11, r1D_block_12, True.intro⟩ rfl rfl
private theorem r2D_block_0 : P1_7_1_3.blockEstimate 3050 645 645 192 = 0xcf95dcb0 := rfl

private theorem r2D_block_1 : P1_7_1_3.blockEstimate 3050 645 837 192 = 0x54e9fa0b0 := rfl

private theorem r2D_block_2 : P1_7_1_3.blockEstimate 3050 645 1029 192 = 0xd673f64b0 := rfl

private theorem r2D_block_3 : P1_7_1_3.blockEstimate 3050 645 1221 192 = 0x17fbb29709 := rfl

private theorem r2D_block_4 : P1_7_1_3.blockEstimate 3050 645 1413 192 = 0x22227851e0 := rfl

private theorem r2D_block_5 : P1_7_1_3.blockEstimate 3050 645 1605 192 = 0x2a303281e0 := rfl

private theorem r2D_block_6 : P1_7_1_3.blockEstimate 3050 645 1797 192 = 0x301cdcb1e0 := rfl

private theorem r2D_block_7 : P1_7_1_3.blockEstimate 3050 645 1989 192 = 0x33e876e1e0 := rfl

private theorem r2D_block_8 : P1_7_1_3.blockEstimate 3050 645 2181 192 = 0x35930111e0 := rfl

private theorem r2D_block_9 : P1_7_1_3.blockEstimate 3050 645 2373 192 = 0x351c7b41e0 := rfl

private theorem r2D_block_10 : P1_7_1_3.blockEstimate 3050 645 2565 192 = 0x3284e571e0 := rfl

private theorem r2D_block_11 : P1_7_1_3.blockEstimate 3050 645 2757 192 = 0x2dcc3fa1e0 := rfl

private theorem r2D_block_12 : P1_7_1_3.blockEstimate 3050 645 2949 192 = 0x26f99e9fc9 := rfl

private theorem r2D_block_13 : P1_7_1_3.blockEstimate 3050 645 3141 192 = 0x1edada8c8c := rfl

private theorem r2D_block_14 : P1_7_1_3.blockEstimate 3050 645 3333 192 = 0x16acfd0034 := rfl

private theorem r2D_block_15 : P1_7_1_3.blockEstimate 3050 645 3525 192 = 0xf13b8d3b9 := rfl

private theorem r2D_block_16 : P1_7_1_3.blockEstimate 3050 645 3717 192 = 0x8908e7350 := rfl

private theorem r2D_block_17 : P1_7_1_3.blockEstimate 3050 645 3909 192 = 0x3ada8bf50 := rfl

private theorem r2D_block_18 : P1_7_1_3.blockEstimate 3050 645 4101 192 = 0xc952ab50 := rfl

private theorem r2D_block_19 : P1_7_1_3.blockEstimate 3050 645 4293 47 = 28771956 := rfl

private theorem r2D : momentEstimate 3050 645 = 0x21f78372cbf := moment_from_blocks
  [(192,0xcf95dcb0),(192,0x54e9fa0b0),(192,0xd673f64b0),(192,0x17fbb29709),(192,0x22227851e0),
    (192,0x2a303281e0),(192,0x301cdcb1e0),(192,0x33e876e1e0),(192,0x35930111e0),
    (192,0x351c7b41e0),(192,0x3284e571e0),(192,0x2dcc3fa1e0),(192,0x26f99e9fc9),
    (192,0x1edada8c8c),(192,0x16acfd0034),(192,0xf13b8d3b9),(192,0x8908e7350),(192,0x3ada8bf50),
    (192,0xc952ab50),(47,28771956)]
  ⟨r2D_block_0, r2D_block_1, r2D_block_2, r2D_block_3, r2D_block_4, r2D_block_5, r2D_block_6, r2D_block_7, r2D_block_8, r2D_block_9, r2D_block_10, r2D_block_11, r2D_block_12, r2D_block_13, r2D_block_14, r2D_block_15, r2D_block_16, r2D_block_17, r2D_block_18, r2D_block_19, True.intro⟩ rfl rfl
private theorem r3D_block_0 : P1_7_1_3.blockEstimate 3131 661 661 192 = 0xd55eb8f0 := rfl

private theorem r3D_block_1 : P1_7_1_3.blockEstimate 3131 661 853 192 = 0x576c20cf0 := rfl

private theorem r3D_block_2 : P1_7_1_3.blockEstimate 3131 661 1045 192 = 0xdd3e760f0 := rfl

private theorem r3D_block_3 : P1_7_1_3.blockEstimate 3131 661 1237 192 = 0x18dcb8a9e9 := rfl

private theorem r3D_block_4 : P1_7_1_3.blockEstimate 3131 661 1429 192 = 0x23be1347e0 := rfl

private theorem r3D_block_5 : P1_7_1_3.blockEstimate 3131 661 1621 192 = 0x2c805357e0 := rfl

private theorem r3D_block_6 : P1_7_1_3.blockEstimate 3131 661 1813 192 = 0x33140367e0 := rfl

private theorem r3D_block_7 : P1_7_1_3.blockEstimate 3131 661 2005 192 = 0x37792377e0 := rfl

private theorem r3D_block_8 : P1_7_1_3.blockEstimate 3131 661 2197 192 = 0x39afb387e0 := rfl

private theorem r3D_block_9 : P1_7_1_3.blockEstimate 3131 661 2389 192 = 0x39b7b397e0 := rfl

private theorem r3D_block_10 : P1_7_1_3.blockEstimate 3131 661 2581 192 = 0x379123a7e0 := rfl

private theorem r3D_block_11 : P1_7_1_3.blockEstimate 3131 661 2773 192 = 0x333c03b7e0 := rfl

private theorem r3D_block_12 : P1_7_1_3.blockEstimate 3131 661 2965 192 = 0x2cb87f29c9 := rfl

private theorem r3D_block_13 : P1_7_1_3.blockEstimate 3131 661 3157 192 = 0x2470112237 := rfl

private theorem r3D_block_14 : P1_7_1_3.blockEstimate 3131 661 3349 192 = 0x1bc0973255 := rfl

private theorem r3D_block_15 : P1_7_1_3.blockEstimate 3131 661 3541 192 = 0x1370b8cc3f := rfl

private theorem r3D_block_16 : P1_7_1_3.blockEstimate 3131 661 3733 192 = 0xc0c3f41ec := rfl

private theorem r3D_block_17 : P1_7_1_3.blockEstimate 3131 661 3925 192 = 0x616d54a90 := rfl

private theorem r3D_block_18 : P1_7_1_3.blockEstimate 3131 661 4117 192 = 0x209083e90 := rfl

private theorem r3D_block_19 : P1_7_1_3.blockEstimate 3131 661 4309 144 = 0x2ee0a2cc := rfl

private theorem r3D : momentEstimate 3131 661 = 0x25ab1ba8825 := moment_from_blocks
  [(192,0xd55eb8f0),(192,0x576c20cf0),(192,0xdd3e760f0),(192,0x18dcb8a9e9),(192,0x23be1347e0),
    (192,0x2c805357e0),(192,0x33140367e0),(192,0x37792377e0),(192,0x39afb387e0),
    (192,0x39b7b397e0),(192,0x379123a7e0),(192,0x333c03b7e0),(192,0x2cb87f29c9),
    (192,0x2470112237),(192,0x1bc0973255),(192,0x1370b8cc3f),(192,0xc0c3f41ec),
    (192,0x616d54a90),(192,0x209083e90),(144,0x2ee0a2cc)]
  ⟨r3D_block_0, r3D_block_1, r3D_block_2, r3D_block_3, r3D_block_4, r3D_block_5, r3D_block_6, r3D_block_7, r3D_block_8, r3D_block_9, r3D_block_10, r3D_block_11, r3D_block_12, r3D_block_13, r3D_block_14, r3D_block_15, r3D_block_16, r3D_block_17, r3D_block_18, r3D_block_19, True.intro⟩ rfl rfl
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
private theorem r1E_block_0 : P1_7_1_3.blockEstimate 4705 995 995 192 = 0x145c6f270 := rfl

private theorem r1E_block_1 : P1_7_1_3.blockEstimate 4705 995 1187 192 = 0x882a7a670 := rfl

private theorem r1E_block_2 : P1_7_1_3.blockEstimate 4705 995 1379 192 = 0x1613525a70 := rfl

private theorem r1E_block_3 : P1_7_1_3.blockEstimate 4705 995 1571 192 = 0x2904c70e70 := rfl

private theorem r1E_block_4 : P1_7_1_3.blockEstimate 4705 995 1763 192 = 0x406405c270 := rfl

private theorem r1E_block_5 : P1_7_1_3.blockEstimate 4705 995 1955 192 = 0x5ab3f1520b := rfl

private theorem r1E_block_6 : P1_7_1_3.blockEstimate 4705 995 2147 192 = 0x7379a6d5c0 := rfl

private theorem r1E_block_7 : P1_7_1_3.blockEstimate 4705 995 2339 192 = 0x88f89375c0 := rfl

private theorem r1E_block_8 : P1_7_1_3.blockEstimate 4705 995 2531 192 = 0x9b2f2015c0 := rfl

private theorem r1E_block_9 : P1_7_1_3.blockEstimate 4705 995 2723 192 = 0xaa1d4cb5c0 := rfl

private theorem r1E_block_10 : P1_7_1_3.blockEstimate 4705 995 2915 192 = 0xb5c31955c0 := rfl

private theorem r1E_block_11 : P1_7_1_3.blockEstimate 4705 995 3107 192 = 0xbe2085f5c0 := rfl

private theorem r1E_block_12 : P1_7_1_3.blockEstimate 4705 995 3299 192 = 0xc3359295c0 := rfl

private theorem r1E_block_13 : P1_7_1_3.blockEstimate 4705 995 3491 192 = 0xc5023f35c0 := rfl

private theorem r1E_block_14 : P1_7_1_3.blockEstimate 4705 995 3683 192 = 0xc3868bd5c0 := rfl

private theorem r1E_block_15 : P1_7_1_3.blockEstimate 4705 995 3875 192 = 0xbec27875c0 := rfl

private theorem r1E_block_16 : P1_7_1_3.blockEstimate 4705 995 4067 192 = 0xb6b60515c0 := rfl

private theorem r1E_block_17 : P1_7_1_3.blockEstimate 4705 995 4259 192 = 0xab6131b5c0 := rfl

private theorem r1E_block_18 : P1_7_1_3.blockEstimate 4705 995 4451 192 = 0x9cc3fe55c0 := rfl

private theorem r1E_block_19 : P1_7_1_3.blockEstimate 4705 995 4643 192 = 0x8afdfc671e := rfl

private theorem r1E_block_20 : P1_7_1_3.blockEstimate 4705 995 4835 192 = 0x779047a371 := rfl

private theorem r1E_block_21 : P1_7_1_3.blockEstimate 4705 995 5027 192 = 0x63e11eae1b := rfl

private theorem r1E_block_22 : P1_7_1_3.blockEstimate 4705 995 5219 192 = 0x509623bc19 := rfl

private theorem r1E_block_23 : P1_7_1_3.blockEstimate 4705 995 5411 192 = 0x3e4635293e := rfl

private theorem r1E_block_24 : P1_7_1_3.blockEstimate 4705 995 5603 192 = 0x2d7587686e := rfl

private theorem r1E_block_25 : P1_7_1_3.blockEstimate 4705 995 5795 192 = 0x1e961280e0 := rfl

private theorem r1E_block_26 : P1_7_1_3.blockEstimate 4705 995 5987 192 = 0x124e59eae0 := rfl

private theorem r1E_block_27 : P1_7_1_3.blockEstimate 4705 995 6179 192 = 0x8f4bcb4e0 := rfl

private theorem r1E_block_28 : P1_7_1_3.blockEstimate 4705 995 6371 192 = 0x2d52adee0 := rfl

private theorem r1E_block_29 : P1_7_1_3.blockEstimate 4705 995 6563 132 = 0x36dff01c := rfl

private theorem r1E : momentEstimate 4705 995 = 0xc029d47a706 := moment_from_blocks
  [(192,0x145c6f270),(192,0x882a7a670),(192,0x1613525a70),(192,0x2904c70e70),
    (192,0x406405c270),(192,0x5ab3f1520b),(192,0x7379a6d5c0),(192,0x88f89375c0),
    (192,0x9b2f2015c0),(192,0xaa1d4cb5c0),(192,0xb5c31955c0),(192,0xbe2085f5c0),
    (192,0xc3359295c0),(192,0xc5023f35c0),(192,0xc3868bd5c0),(192,0xbec27875c0),
    (192,0xb6b60515c0),(192,0xab6131b5c0),(192,0x9cc3fe55c0),(192,0x8afdfc671e),
    (192,0x779047a371),(192,0x63e11eae1b),(192,0x509623bc19),(192,0x3e4635293e),
    (192,0x2d7587686e),(192,0x1e961280e0),(192,0x124e59eae0),(192,0x8f4bcb4e0),
    (192,0x2d52adee0),(132,0x36dff01c)]
  ⟨r1E_block_0, r1E_block_1, r1E_block_2, r1E_block_3, r1E_block_4, r1E_block_5, r1E_block_6, r1E_block_7, r1E_block_8, r1E_block_9, r1E_block_10, r1E_block_11, r1E_block_12, r1E_block_13, r1E_block_14, r1E_block_15, r1E_block_16, r1E_block_17, r1E_block_18, r1E_block_19, r1E_block_20, r1E_block_21, r1E_block_22, r1E_block_23, r1E_block_24, r1E_block_25, r1E_block_26, r1E_block_27, r1E_block_28, r1E_block_29, True.intro⟩ rfl rfl
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
private theorem r1F_block_0 : P1_7_1_3.blockEstimate 7341 1556 1556 192 = 0x20206e570 := rfl

private theorem r1F_block_1 : P1_7_1_3.blockEstimate 7341 1556 1748 192 = 0xd9cc25970 := rfl

private theorem r1F_block_2 : P1_7_1_3.blockEstimate 7341 1556 1940 192 = 0x23e357cd70 := rfl

private theorem r1F_block_3 : P1_7_1_3.blockEstimate 7341 1556 2132 192 = 0x43e2c74170 := rfl

private theorem r1F_block_4 : P1_7_1_3.blockEstimate 7341 1556 2324 192 = 0x6ca810b570 := rfl

private theorem r1F_block_5 : P1_7_1_3.blockEstimate 7341 1556 2516 192 = 0x9d40342970 := rfl

private theorem r1F_block_6 : P1_7_1_3.blockEstimate 7341 1556 2708 192 = 0xd4b8319d70 := rfl

private theorem r1F_block_7 : P1_7_1_3.blockEstimate 7341 1556 2900 192 = 0x1121d091170 := rfl

private theorem r1F_block_8 : P1_7_1_3.blockEstimate 7341 1556 3092 192 = 0x1535dce88c9 := rfl

private theorem r1F_block_9 : P1_7_1_3.blockEstimate 7341 1556 3284 192 = 0x191ae228160 := rfl

private theorem r1F_block_10 : P1_7_1_3.blockEstimate 7341 1556 3476 192 = 0x1cadd343160 := rfl

private theorem r1F_block_11 : P1_7_1_3.blockEstimate 7341 1556 3668 192 = 0x1feea8de160 := rfl

private theorem r1F_block_12 : P1_7_1_3.blockEstimate 7341 1556 3860 192 = 0x22dd62f9160 := rfl

private theorem r1F_block_13 : P1_7_1_3.blockEstimate 7341 1556 4052 192 = 0x257a0194160 := rfl

private theorem r1F_block_14 : P1_7_1_3.blockEstimate 7341 1556 4244 192 = 0x27c484af160 := rfl

private theorem r1F_block_15 : P1_7_1_3.blockEstimate 7341 1556 4436 192 = 0x29bcec4a160 := rfl

private theorem r1F_block_16 : P1_7_1_3.blockEstimate 7341 1556 4628 192 = 0x2b633865160 := rfl

private theorem r1F_block_17 : P1_7_1_3.blockEstimate 7341 1556 4820 192 = 0x2cb76900160 := rfl

private theorem r1F_block_18 : P1_7_1_3.blockEstimate 7341 1556 5012 192 = 0x2db97e1b160 := rfl

private theorem r1F_block_19 : P1_7_1_3.blockEstimate 7341 1556 5204 192 = 0x2e6977b6160 := rfl

private theorem r1F_block_20 : P1_7_1_3.blockEstimate 7341 1556 5396 192 = 0x2ec755d1160 := rfl

private theorem r1F_block_21 : P1_7_1_3.blockEstimate 7341 1556 5588 192 = 0x2ed3186c160 := rfl

private theorem r1F_block_22 : P1_7_1_3.blockEstimate 7341 1556 5780 192 = 0x2e8cbf87160 := rfl

private theorem r1F_block_23 : P1_7_1_3.blockEstimate 7341 1556 5972 192 = 0x2df44b22160 := rfl

private theorem r1F_block_24 : P1_7_1_3.blockEstimate 7341 1556 6164 192 = 0x2d09bb3d160 := rfl

private theorem r1F_block_25 : P1_7_1_3.blockEstimate 7341 1556 6356 192 = 0x2bcd0fd8160 := rfl

private theorem r1F_block_26 : P1_7_1_3.blockEstimate 7341 1556 6548 192 = 0x2a3e48f3160 := rfl

private theorem r1F_block_27 : P1_7_1_3.blockEstimate 7341 1556 6740 192 = 0x285d668e160 := rfl

private theorem r1F_block_28 : P1_7_1_3.blockEstimate 7341 1556 6932 192 = 0x262a68a9160 := rfl

private theorem r1F_block_29 : P1_7_1_3.blockEstimate 7341 1556 7124 192 = 0x23a54f44160 := rfl

private theorem r1F_block_30 : P1_7_1_3.blockEstimate 7341 1556 7316 192 = 0x20d48b5e287 := rfl

private theorem r1F_block_31 : P1_7_1_3.blockEstimate 7341 1556 7508 192 = 0x1de114a5d0d := rfl

private theorem r1F_block_32 : P1_7_1_3.blockEstimate 7341 1556 7700 192 = 0x1ae25ec5676 := rfl

private theorem r1F_block_33 : P1_7_1_3.blockEstimate 7341 1556 7892 192 = 0x17e2f2335c9 := rfl

private theorem r1F_block_34 : P1_7_1_3.blockEstimate 7341 1556 8084 192 = 0x14ecdaa5b58 := rfl

private theorem r1F_block_35 : P1_7_1_3.blockEstimate 7341 1556 8276 192 = 0x1209abf605c := rfl

private theorem r1F_block_36 : P1_7_1_3.blockEstimate 7341 1556 8468 192 = 0xf428221210 := rfl

private theorem r1F_block_37 : P1_7_1_3.blockEstimate 7341 1556 8660 192 = 0xca00147dc6 := rfl

private theorem r1F_block_38 : P1_7_1_3.blockEstimate 7341 1556 8852 192 = 0xa27cc95897 := rfl

private theorem r1F_block_39 : P1_7_1_3.blockEstimate 7341 1556 9044 192 = 0x7e17166cf8 := rfl

private theorem r1F_block_40 : P1_7_1_3.blockEstimate 7341 1556 9236 192 = 0x5db18853f8 := rfl

private theorem r1F_block_41 : P1_7_1_3.blockEstimate 7341 1556 9428 192 = 0x419ccd5af8 := rfl

private theorem r1F_block_42 : P1_7_1_3.blockEstimate 7341 1556 9620 192 = 0x2a24d581f8 := rfl

private theorem r1F_block_43 : P1_7_1_3.blockEstimate 7341 1556 9812 192 = 0x179590c8f8 := rfl

private theorem r1F_block_44 : P1_7_1_3.blockEstimate 7341 1556 10004 192 = 0xa3aef2ff8 := rfl

private theorem r1F_block_45 : P1_7_1_3.blockEstimate 7341 1556 10196 192 = 0x260e0b6f8 := rfl

private theorem r1F_block_46 : P1_7_1_3.blockEstimate 7341 1556 10388 65 = 0xaace255 := rfl

private theorem r1F : momentEstimate 7341 1556 = 0x4741ba66013a := moment_from_blocks
  [(192,0x20206e570),(192,0xd9cc25970),(192,0x23e357cd70),(192,0x43e2c74170),
    (192,0x6ca810b570),(192,0x9d40342970),(192,0xd4b8319d70),(192,0x1121d091170),
    (192,0x1535dce88c9),(192,0x191ae228160),(192,0x1cadd343160),(192,0x1feea8de160),
    (192,0x22dd62f9160),(192,0x257a0194160),(192,0x27c484af160),(192,0x29bcec4a160),
    (192,0x2b633865160),(192,0x2cb76900160),(192,0x2db97e1b160),(192,0x2e6977b6160),
    (192,0x2ec755d1160),(192,0x2ed3186c160),(192,0x2e8cbf87160),(192,0x2df44b22160),
    (192,0x2d09bb3d160),(192,0x2bcd0fd8160),(192,0x2a3e48f3160),(192,0x285d668e160),
    (192,0x262a68a9160),(192,0x23a54f44160),(192,0x20d48b5e287),(192,0x1de114a5d0d),
    (192,0x1ae25ec5676),(192,0x17e2f2335c9),(192,0x14ecdaa5b58),(192,0x1209abf605c),
    (192,0xf428221210),(192,0xca00147dc6),(192,0xa27cc95897),(192,0x7e17166cf8),
    (192,0x5db18853f8),(192,0x419ccd5af8),(192,0x2a24d581f8),(192,0x179590c8f8),
    (192,0xa3aef2ff8),(192,0x260e0b6f8),(65,0xaace255)]
  ⟨r1F_block_0, r1F_block_1, r1F_block_2, r1F_block_3, r1F_block_4, r1F_block_5, r1F_block_6, r1F_block_7, r1F_block_8, r1F_block_9, r1F_block_10, r1F_block_11, r1F_block_12, r1F_block_13, r1F_block_14, r1F_block_15, r1F_block_16, r1F_block_17, r1F_block_18, r1F_block_19, r1F_block_20, r1F_block_21, r1F_block_22, r1F_block_23, r1F_block_24, r1F_block_25, r1F_block_26, r1F_block_27, r1F_block_28, r1F_block_29, r1F_block_30, r1F_block_31, r1F_block_32, r1F_block_33, r1F_block_34, r1F_block_35, r1F_block_36, r1F_block_37, r1F_block_38, r1F_block_39, r1F_block_40, r1F_block_41, r1F_block_42, r1F_block_43, r1F_block_44, r1F_block_45, r1F_block_46, True.intro⟩ rfl rfl
end P3_7_1
end
section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
private theorem r1G_block_0 : P1_7_1_3.blockEstimate 9172 1952 1952 192 = 0x284c9a730 := rfl

private theorem r1G_block_1 : P1_7_1_3.blockEstimate 9172 1952 2144 192 = 0x1127ff0b30 := rfl

private theorem r1G_block_2 : P1_7_1_3.blockEstimate 9172 1952 2336 192 = 0x2d7b826f30 := rfl

private theorem r1G_block_3 : P1_7_1_3.blockEstimate 9172 1952 2528 192 = 0x568c53d330 := rfl

private theorem r1G_block_4 : P1_7_1_3.blockEstimate 9172 1952 2720 192 = 0x8b67733730 := rfl

private theorem r1G_block_5 : P1_7_1_3.blockEstimate 9172 1952 2912 192 = 0xcb19e09b30 := rfl

private theorem r1G_block_6 : P1_7_1_3.blockEstimate 9172 1952 3104 192 = 0x114b09bff30 := rfl

private theorem r1G_block_7 : P1_7_1_3.blockEstimate 9172 1952 3296 192 = 0x16738a56330 := rfl

private theorem r1G_block_8 : P1_7_1_3.blockEstimate 9172 1952 3488 192 = 0x1c1befcc730 := rfl

private theorem r1G_block_9 : P1_7_1_3.blockEstimate 9172 1952 3680 192 = 0x22350a22b30 := rfl

private theorem r1G_block_10 : P1_7_1_3.blockEstimate 9172 1952 3872 192 = 0x289d9ace828 := rfl

private theorem r1G_block_11 : P1_7_1_3.blockEstimate 9172 1952 4064 192 = 0x2ed24be09c0 := rfl

private theorem r1G_block_12 : P1_7_1_3.blockEstimate 9172 1952 4256 192 = 0x34a025249c0 := rfl

private theorem r1G_block_13 : P1_7_1_3.blockEstimate 9172 1952 4448 192 = 0x3a0700e89c0 := rfl

private theorem r1G_block_14 : P1_7_1_3.blockEstimate 9172 1952 4640 192 = 0x3f06df2c9c0 := rfl

private theorem r1G_block_15 : P1_7_1_3.blockEstimate 9172 1952 4832 192 = 0x439fbff09c0 := rfl

private theorem r1G_block_16 : P1_7_1_3.blockEstimate 9172 1952 5024 192 = 0x47d1a3349c0 := rfl

private theorem r1G_block_17 : P1_7_1_3.blockEstimate 9172 1952 5216 192 = 0x4b9c88f89c0 := rfl

private theorem r1G_block_18 : P1_7_1_3.blockEstimate 9172 1952 5408 192 = 0x4f00713c9c0 := rfl

private theorem r1G_block_19 : P1_7_1_3.blockEstimate 9172 1952 5600 192 = 0x51fd5c009c0 := rfl

private theorem r1G_block_20 : P1_7_1_3.blockEstimate 9172 1952 5792 192 = 0x549349449c0 := rfl

private theorem r1G_block_21 : P1_7_1_3.blockEstimate 9172 1952 5984 192 = 0x56c239089c0 := rfl

private theorem r1G_block_22 : P1_7_1_3.blockEstimate 9172 1952 6176 192 = 0x588a2b4c9c0 := rfl

private theorem r1G_block_23 : P1_7_1_3.blockEstimate 9172 1952 6368 192 = 0x59eb20109c0 := rfl

private theorem r1G_block_24 : P1_7_1_3.blockEstimate 9172 1952 6560 192 = 0x5ae517549c0 := rfl

private theorem r1G_block_25 : P1_7_1_3.blockEstimate 9172 1952 6752 192 = 0x5b7811189c0 := rfl

private theorem r1G_block_26 : P1_7_1_3.blockEstimate 9172 1952 6944 192 = 0x5ba40d5c9c0 := rfl

private theorem r1G_block_27 : P1_7_1_3.blockEstimate 9172 1952 7136 192 = 0x5b690c209c0 := rfl

private theorem r1G_block_28 : P1_7_1_3.blockEstimate 9172 1952 7328 192 = 0x5ac70d649c0 := rfl

private theorem r1G_block_29 : P1_7_1_3.blockEstimate 9172 1952 7520 192 = 0x59be11289c0 := rfl

private theorem r1G_block_30 : P1_7_1_3.blockEstimate 9172 1952 7712 192 = 0x584e176c9c0 := rfl

private theorem r1G_block_31 : P1_7_1_3.blockEstimate 9172 1952 7904 192 = 0x567720309c0 := rfl

private theorem r1G_block_32 : P1_7_1_3.blockEstimate 9172 1952 8096 192 = 0x54392b749c0 := rfl

private theorem r1G_block_33 : P1_7_1_3.blockEstimate 9172 1952 8288 192 = 0x519439389c0 := rfl

private theorem r1G_block_34 : P1_7_1_3.blockEstimate 9172 1952 8480 192 = 0x4e88497c9c0 := rfl

private theorem r1G_block_35 : P1_7_1_3.blockEstimate 9172 1952 8672 192 = 0x4b155c409c0 := rfl

private theorem r1G_block_36 : P1_7_1_3.blockEstimate 9172 1952 8864 192 = 0x473b71849c0 := rfl

private theorem r1G_block_37 : P1_7_1_3.blockEstimate 9172 1952 9056 192 = 0x42fb47b017f := rfl

private theorem r1G_block_38 : P1_7_1_3.blockEstimate 9172 1952 9248 192 = 0x3e735882949 := rfl

private theorem r1G_block_39 : P1_7_1_3.blockEstimate 9172 1952 9440 192 = 0x39d17209cae := rfl

private theorem r1G_block_40 : P1_7_1_3.blockEstimate 9172 1952 9632 192 = 0x3522e794da2 := rfl

private theorem r1G_block_41 : P1_7_1_3.blockEstimate 9172 1952 9824 192 = 0x307237f31da := rfl

private theorem r1G_block_42 : P1_7_1_3.blockEstimate 9172 1952 10016 192 = 0x2bc982657e9 := rfl

private theorem r1G_block_43 : P1_7_1_3.blockEstimate 9172 1952 10208 192 = 0x2732869e152 := rfl

private theorem r1G_block_44 : P1_7_1_3.blockEstimate 9172 1952 10400 192 = 0x22b6a4c05a0 := rfl

private theorem r1G_block_45 : P1_7_1_3.blockEstimate 9172 1952 10592 192 = 0x1e5edd60b5a := rfl

private theorem r1G_block_46 : P1_7_1_3.blockEstimate 9172 1952 10784 192 = 0x1a33d185610 := rfl

private theorem r1G_block_47 : P1_7_1_3.blockEstimate 9172 1952 10976 192 = 0x163d56ed976 := rfl

private theorem r1G_block_48 : P1_7_1_3.blockEstimate 9172 1952 11168 192 = 0x127b4c29610 := rfl

private theorem r1G_block_49 : P1_7_1_3.blockEstimate 9172 1952 11360 192 = 0xeffc096410 := rfl

private theorem r1G_block_50 : P1_7_1_3.blockEstimate 9172 1952 11552 192 = 0xbd51019210 := rfl

private theorem r1G_block_51 : P1_7_1_3.blockEstimate 9172 1952 11744 192 = 0x8fff9b2010 := rfl

private theorem r1G_block_52 : P1_7_1_3.blockEstimate 9172 1952 11936 192 = 0x6853c60e10 := rfl

private theorem r1G_block_53 : P1_7_1_3.blockEstimate 9172 1952 12128 192 = 0x4699725c10 := rfl

private theorem r1G_block_54 : P1_7_1_3.blockEstimate 9172 1952 12320 192 = 0x2b1c900a10 := rfl

private theorem r1G_block_55 : P1_7_1_3.blockEstimate 9172 1952 12512 192 = 0x16290f1810 := rfl

private theorem r1G_block_56 : P1_7_1_3.blockEstimate 9172 1952 12704 192 = 0x80adf8610 := rfl

private theorem r1G_block_57 : P1_7_1_3.blockEstimate 9172 1952 12896 180 = 0x10de40607 := rfl

private theorem r1G : momentEstimate 9172 1952 = 0xae27f29bc6cc := moment_from_blocks
  [(192,0x284c9a730),(192,0x1127ff0b30),(192,0x2d7b826f30),(192,0x568c53d330),
    (192,0x8b67733730),(192,0xcb19e09b30),(192,0x114b09bff30),(192,0x16738a56330),
    (192,0x1c1befcc730),(192,0x22350a22b30),(192,0x289d9ace828),(192,0x2ed24be09c0),
    (192,0x34a025249c0),(192,0x3a0700e89c0),(192,0x3f06df2c9c0),(192,0x439fbff09c0),
    (192,0x47d1a3349c0),(192,0x4b9c88f89c0),(192,0x4f00713c9c0),(192,0x51fd5c009c0),
    (192,0x549349449c0),(192,0x56c239089c0),(192,0x588a2b4c9c0),(192,0x59eb20109c0),
    (192,0x5ae517549c0),(192,0x5b7811189c0),(192,0x5ba40d5c9c0),(192,0x5b690c209c0),
    (192,0x5ac70d649c0),(192,0x59be11289c0),(192,0x584e176c9c0),(192,0x567720309c0),
    (192,0x54392b749c0),(192,0x519439389c0),(192,0x4e88497c9c0),(192,0x4b155c409c0),
    (192,0x473b71849c0),(192,0x42fb47b017f),(192,0x3e735882949),(192,0x39d17209cae),
    (192,0x3522e794da2),(192,0x307237f31da),(192,0x2bc982657e9),(192,0x2732869e152),
    (192,0x22b6a4c05a0),(192,0x1e5edd60b5a),(192,0x1a33d185610),(192,0x163d56ed976),
    (192,0x127b4c29610),(192,0xeffc096410),(192,0xbd51019210),(192,0x8fff9b2010),
    (192,0x6853c60e10),(192,0x4699725c10),(192,0x2b1c900a10),(192,0x16290f1810),
    (192,0x80adf8610),(180,0x10de40607)]
  ⟨r1G_block_0, r1G_block_1, r1G_block_2, r1G_block_3, r1G_block_4, r1G_block_5, r1G_block_6, r1G_block_7, r1G_block_8, r1G_block_9, r1G_block_10, r1G_block_11, r1G_block_12, r1G_block_13, r1G_block_14, r1G_block_15, r1G_block_16, r1G_block_17, r1G_block_18, r1G_block_19, r1G_block_20, r1G_block_21, r1G_block_22, r1G_block_23, r1G_block_24, r1G_block_25, r1G_block_26, r1G_block_27, r1G_block_28, r1G_block_29, r1G_block_30, r1G_block_31, r1G_block_32, r1G_block_33, r1G_block_34, r1G_block_35, r1G_block_36, r1G_block_37, r1G_block_38, r1G_block_39, r1G_block_40, r1G_block_41, r1G_block_42, r1G_block_43, r1G_block_44, r1G_block_45, r1G_block_46, r1G_block_47, r1G_block_48, r1G_block_49, r1G_block_50, r1G_block_51, r1G_block_52, r1G_block_53, r1G_block_54, r1G_block_55, r1G_block_56, r1G_block_57, True.intro⟩ rfl rfl
end P3_7_1
end
section
namespace P3_7_1
open P3 (HighBand)
open P3_7 (Bank Stage terminal stages subbank Listed)
open scoped P1_7_1_3_2
open P3_7_1 (r1A r2A r3A r4A r5A r6A r7A r8A r9A r10A r11A r12A r13A r14A r15A r16A r17A r18A r19A r20A r21A r22A r23A r24A r25A r26A r27A r28A r29A r30A r31A r32A r33A r34A r35A r36A r37A r38A r39A)
open P3_7_1 (r1B r2B r3B r4B r5B r6B r7B r8B r9B)
open P3_7_1 (r1C r2C r3C r4C)
open P3_7_1 (r1D r2D r3D)
open P3_7_1 (r1E)
open P3_7_1 (r1F)
open P3_7_1 (r1G)
local notation "b!" depth "," grade "," deriv "," nodes "," moment ";" h =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) h
private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankOK s.free ∧ BankOK s.moving
private theorem stages_nil : StageOK [] := by
  intro s hs
  simp at hs
private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf : BankOK s.free) (hm : BankOK s.moving) (ht : StageOK ss) : StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option maxHeartbeats 2000000 in
private theorem stages_ok (b : HighBand) : StageOK (stages b) := by
  cases b with
  | h2274 =>
      rw [stages]
      refine stages_cons (b! 76,105,23,0x345100000,3635193; r9A)
        (b! 359,499,105,0x14006680000,0x64b8343e; r39A) ?_
      refine stages_cons (b! 80,111,24,0x3c7300000,4477423; r11A)
        (b! 356,495,104,0x137d3580000,0x616d5567; r38A) ?_
      refine stages_cons (b! 90,125,27,0x558480000,7136131; r13A)
        (b! 391,543,114,0x19c04900000,0x8cc85625; r1B) ?_
      refine stages_cons (b! 99,137,30,0x722180000,10343855; r15A)
        (b! 429,596,126,0x222a41c0000,0xcd26d8f5; r2B) ?_
      refine stages_cons (b! 106,147,32,0x8b45c0000,13594640; r18A)
        (b! 483,671,142,0x30bbe980000,0x14954ceae; r4B) ?_
      refine stages_cons (b! 115,159,35,0xb24d00000,18685854; r22A)
        (b! 521,724,153,0x3d118e80000,0x1bd78704c; r5B) ?_
      refine stages_cons (b! 114,158,34,0xab2c00000,17916156; r21A)
        (b! 585,813,172,0x56714d40000,0x2c405b86b; r6B) ?_
      refine stages_cons (b! 142,197,43,0x14bde80000,43318982; r24A)
        (b! 666,926,195,0x7f04c380000,0x4a1c95ad2; moment_instance) ?_
      refine stages_cons (b! 195,270,60,0x35dfb80000,0x921d91e; r26A)
        (b! 869,1208,255,0x11a29c000000,0xd6957b128; r8B) ?_
      refine stages_cons (b! 236,327,73,0x5f7bb40000,0x139cbdb4; r30A)
        (b! 1028,1429,302,0x1d31d5640000,0x1a41f86f48; r1C) ?_
      refine stages_cons (b! 234,324,73,0x5daf840000,0x130a6f27; r29A)
        (b! 1267,1761,373,0x36b2a6f80000,0x3c9863ad3c; r3C) ?_
      refine stages_cons (b! 261,362,81,0x813b280000,0x1d6fb003; r33A)
        (b! 1466,2038,431,0x54997c200000,0x6c7e6759da; r1D) ?_
      refine stages_cons (b! 250,347,75,0x6ece680000,0x18392b4c; r32A)
        (b! 1215,1689,356,0x3011c0200000,0x33175ef1d6; r2C) ?_
      refine stages_cons (b! 444,615,137,0x274cf340000,0xf2191e37; r3B)
        (b! 2194,3050,645,0x11b429fac0000,0x21f78372cbf; r2D) ?_
      refine stages_cons (b! 680,942,212,0x8dc48280000,0x538e63a35; r7B)
        (b! 3385,4705,995,0x40f5ebab00000,0xc029d47a706; r1E) ?_
      refine stages_cons (b! 998,1383,310,0x1bdf3ba00000,0x181eba870b; r9B)
        (b! 5282,7341,1556,0xf7195a1840000,0x4741ba66013a; r1F) ?_
      exact stages_nil
  | h2294 =>
      rw [stages]
      refine stages_cons (b! 73,101,22,0x2e5640000,3108650; r8A)
        (b! 352,489,103,0x12dda700000,0x5cfd94a5; r37A) ?_
      refine stages_cons (b! 78,108,24,0x392740000,4103823; r10A)
        (b! 345,480,101,0x11c61f80000,0x564a51c0; r36A) ?_
      refine stages_cons (b! 86,119,26,0x4b3780000,5931589; r12A)
        (b! 385,535,112,0x188bf840000,0x84679137; moment_instance) ?_
      refine stages_cons (b! 94,130,29,0x633bc0000,8531244; r14A)
        (b! 411,572,120,0x1dec1a80000,0xad1e0c80; moment_instance) ?_
      refine stages_cons (b! 102,141,31,0x7cec00000,11621252; r17A)
        (b! 438,609,128,0x2436d340000,0xde912dc3; moment_instance) ?_
      refine stages_cons (b! 108,150,33,0x948040000,14840297; r20A)
        (b! 522,726,153,0x3d548e40000,0x1c16ef1c7; moment_instance) ?_
      refine stages_cons (b! 108,149,33,0x948040000,14526868; r19A)
        (b! 570,792,167,0x4fc3e700000,0x27c2e15db; moment_instance) ?_
      refine stages_cons (b! 142,197,43,0x14bde80000,43318982; r24A)
        (b! 696,968,204,0x910a3980000,0x5884788a7; moment_instance) ?_
      refine stages_cons (b! 163,226,50,0x1f8a780000,75401397; r25A)
        (b! 851,1183,249,0x108708880000,0xc4f2a7606; P1_7_1_3_3.moment1183_249) ?_
      refine stages_cons (b! 221,306,68,0x4e346c0000,0xf032b8c; r28A)
        (b! 952,1324,279,0x17270e900000,0x1350bb1fb5; P1_7_1_3_3.moment1324_279) ?_
      refine stages_cons (b! 212,294,65,0x44e9c40000,0xcc1a54f; r27A)
        (b! 1115,1550,329,0x255cff880000,0x2473d5ffe4; P1_7_1_3_3.moment1550_329) ?_
      refine stages_cons (b! 261,362,82,0x826c0c0000,0x1db6eefa; r34A)
        (b! 1463,2034,430,0x54106e900000,0x6b9d823520; r4C) ?_
      refine stages_cons (b! 246,341,75,0x6ae4280000,0x16e7d3b2; r31A)
        (b! 1220,1696,357,0x309db61c0000,0x33e3754396; P1_7_1_3_3.moment1696_357) ?_
      refine stages_cons (b! 279,386,85,0x9b80980000,0x25892b87; r35A)
        (b! 1240,1725,359,0x32a0cb700000,0x370899d961; P1_7_1_3_3.moment1725_359) ?_
      refine stages_cons (b! 534,740,167,0x44f1df00000,0x1ff6e1863; moment_instance)
        (b! 2252,3131,661,0x131ef423c0000,0x25ab1ba8825; r3D) ?_
      refine stages_cons (b! 637,883,197,0x73e2ad80000,0x401d0f0c6; moment_instance)
        (b! 3474,4830,1019,0x461aa92080000,0xd5013df2ef9; P1_7_1_3_5.moment4830) ?_
      refine stages_cons (b! 774,1072,239,0xcf60ca00000,0x8af950b98; P1_7_1_3_3.moment1072_239)
        (b! 4170,5798,1223,0x7934721300000,0x1ba1a89b2ba1; P1_7_1_3_5.moment5798) ?_
      refine stages_cons (b! 1042,1443,329,0x201c60040000,0x1cf53a5560; P1_7_1_3_3.moment1443_329)
        (b! 5487,7630,1607,0x113c22e7a00000,0x52bdbe618ec3; P1_7_1_3_5.moment7630) ?_
      exact stages_nil
  | h7773 =>
      rw [stages]
      refine stages_cons (b! 11,15,3,55574528,2194; r1A)
        (b! 20,28,4,0xdc00000,17031; r2A) ?_
      refine stages_cons (b! 21,29,6,0x13cc0000,24733; r3A)
        (b! 38,53,9,0x5d840000,211909; r5A) ?_
      refine stages_cons (b! 34,47,10,0x4f100000,156979; r4A)
        (b! 64,89,15,0x1a3600000,1564938; r7A) ?_
      refine stages_cons (b! 54,75,16,0x12f140000,957077; r6A)
        (b! 101,141,24,0x64f3c0000,9562298; r16A) ?_
      exact stages_nil
end P3_7_1
end
