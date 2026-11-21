import ProximityPrize.SubmissionLower.HighBankCore

set_option Elab.async false
set_option autoImplicit true

-- Only the e-independent moment witnesses reused by the retargeted banks.
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
theorem r22A_block_0 : P1_7_1_3.blockEstimate 159 35 35 192 = 18685378 := rfl

theorem r22A_block_1 : P1_7_1_3.blockEstimate 159 35 227 2 = 476 := rfl

private theorem r22A : momentEstimate 159 35 = 18685854 := moment_from_blocks
  [(192,18685378),(2,476)]
  ⟨r22A_block_0, r22A_block_1, True.intro⟩ rfl rfl
theorem r23A_block_0 : P1_7_1_3.blockEstimate 173 32 32 192 = 22790651 := rfl

theorem r23A_block_1 : P1_7_1_3.blockEstimate 173 32 224 13 = 42218 := rfl

private theorem r23A : momentEstimate 173 32 = 22832869 := moment_from_blocks
  [(192,22790651),(13,42218)]
  ⟨r23A_block_0, r23A_block_1, True.intro⟩ rfl rfl
theorem r24A_block_0 : P1_7_1_3.blockEstimate 197 43 43 192 = 41550683 := rfl

theorem r24A_block_1 : P1_7_1_3.blockEstimate 197 43 235 48 = 1768299 := rfl

private theorem r24A : momentEstimate 197 43 = 43318982 := moment_from_blocks
  [(192,41550683),(48,1768299)]
  ⟨r24A_block_0, r24A_block_1, True.intro⟩ rfl rfl
theorem r25A_block_0 : P1_7_1_3.blockEstimate 226 50 50 192 = 65796440 := rfl

theorem r25A_block_1 : P1_7_1_3.blockEstimate 226 50 242 84 = 9604957 := rfl

private theorem r25A : momentEstimate 226 50 = 75401397 := moment_from_blocks
  [(192,65796440),(84,9604957)]
  ⟨r25A_block_0, r25A_block_1, True.intro⟩ rfl rfl
end P3_7_1
end

section
namespace P3_7_1
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
theorem r1E_block_0 : P1_7_1_3.blockEstimate 4705 995 995 192 = 0x145c6f270 := rfl

theorem r1E_block_1 : P1_7_1_3.blockEstimate 4705 995 1187 192 = 0x882a7a670 := rfl

theorem r1E_block_2 : P1_7_1_3.blockEstimate 4705 995 1379 192 = 0x1613525a70 := rfl

theorem r1E_block_3 : P1_7_1_3.blockEstimate 4705 995 1571 192 = 0x2904c70e70 := rfl

theorem r1E_block_4 : P1_7_1_3.blockEstimate 4705 995 1763 192 = 0x406405c270 := rfl

theorem r1E_block_5 : P1_7_1_3.blockEstimate 4705 995 1955 192 = 0x5ab3f1520b := rfl

theorem r1E_block_6 : P1_7_1_3.blockEstimate 4705 995 2147 192 = 0x7379a6d5c0 := rfl

theorem r1E_block_7 : P1_7_1_3.blockEstimate 4705 995 2339 192 = 0x88f89375c0 := rfl

theorem r1E_block_8 : P1_7_1_3.blockEstimate 4705 995 2531 192 = 0x9b2f2015c0 := rfl

theorem r1E_block_9 : P1_7_1_3.blockEstimate 4705 995 2723 192 = 0xaa1d4cb5c0 := rfl

theorem r1E_block_10 : P1_7_1_3.blockEstimate 4705 995 2915 192 = 0xb5c31955c0 := rfl

theorem r1E_block_11 : P1_7_1_3.blockEstimate 4705 995 3107 192 = 0xbe2085f5c0 := rfl

theorem r1E_block_12 : P1_7_1_3.blockEstimate 4705 995 3299 192 = 0xc3359295c0 := rfl

theorem r1E_block_13 : P1_7_1_3.blockEstimate 4705 995 3491 192 = 0xc5023f35c0 := rfl

theorem r1E_block_14 : P1_7_1_3.blockEstimate 4705 995 3683 192 = 0xc3868bd5c0 := rfl

theorem r1E_block_15 : P1_7_1_3.blockEstimate 4705 995 3875 192 = 0xbec27875c0 := rfl

theorem r1E_block_16 : P1_7_1_3.blockEstimate 4705 995 4067 192 = 0xb6b60515c0 := rfl

theorem r1E_block_17 : P1_7_1_3.blockEstimate 4705 995 4259 192 = 0xab6131b5c0 := rfl

theorem r1E_block_18 : P1_7_1_3.blockEstimate 4705 995 4451 192 = 0x9cc3fe55c0 := rfl

theorem r1E_block_19 : P1_7_1_3.blockEstimate 4705 995 4643 192 = 0x8afdfc671e := rfl

theorem r1E_block_20 : P1_7_1_3.blockEstimate 4705 995 4835 192 = 0x779047a371 := rfl

theorem r1E_block_21 : P1_7_1_3.blockEstimate 4705 995 5027 192 = 0x63e11eae1b := rfl

theorem r1E_block_22 : P1_7_1_3.blockEstimate 4705 995 5219 192 = 0x509623bc19 := rfl

theorem r1E_block_23 : P1_7_1_3.blockEstimate 4705 995 5411 192 = 0x3e4635293e := rfl

theorem r1E_block_24 : P1_7_1_3.blockEstimate 4705 995 5603 192 = 0x2d7587686e := rfl

theorem r1E_block_25 : P1_7_1_3.blockEstimate 4705 995 5795 192 = 0x1e961280e0 := rfl

theorem r1E_block_26 : P1_7_1_3.blockEstimate 4705 995 5987 192 = 0x124e59eae0 := rfl

theorem r1E_block_27 : P1_7_1_3.blockEstimate 4705 995 6179 192 = 0x8f4bcb4e0 := rfl

theorem r1E_block_28 : P1_7_1_3.blockEstimate 4705 995 6371 192 = 0x2d52adee0 := rfl

theorem r1E_block_29 : P1_7_1_3.blockEstimate 4705 995 6563 132 = 0x36dff01c := rfl

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
theorem r1F_block_0 : P1_7_1_3.blockEstimate 7341 1556 1556 192 = 0x20206e570 := rfl

theorem r1F_block_1 : P1_7_1_3.blockEstimate 7341 1556 1748 192 = 0xd9cc25970 := rfl

theorem r1F_block_2 : P1_7_1_3.blockEstimate 7341 1556 1940 192 = 0x23e357cd70 := rfl

theorem r1F_block_3 : P1_7_1_3.blockEstimate 7341 1556 2132 192 = 0x43e2c74170 := rfl

theorem r1F_block_4 : P1_7_1_3.blockEstimate 7341 1556 2324 192 = 0x6ca810b570 := rfl

theorem r1F_block_5 : P1_7_1_3.blockEstimate 7341 1556 2516 192 = 0x9d40342970 := rfl

theorem r1F_block_6 : P1_7_1_3.blockEstimate 7341 1556 2708 192 = 0xd4b8319d70 := rfl

theorem r1F_block_7 : P1_7_1_3.blockEstimate 7341 1556 2900 192 = 0x1121d091170 := rfl

theorem r1F_block_8 : P1_7_1_3.blockEstimate 7341 1556 3092 192 = 0x1535dce88c9 := rfl

theorem r1F_block_9 : P1_7_1_3.blockEstimate 7341 1556 3284 192 = 0x191ae228160 := rfl

theorem r1F_block_10 : P1_7_1_3.blockEstimate 7341 1556 3476 192 = 0x1cadd343160 := rfl

theorem r1F_block_11 : P1_7_1_3.blockEstimate 7341 1556 3668 192 = 0x1feea8de160 := rfl

theorem r1F_block_12 : P1_7_1_3.blockEstimate 7341 1556 3860 192 = 0x22dd62f9160 := rfl

theorem r1F_block_13 : P1_7_1_3.blockEstimate 7341 1556 4052 192 = 0x257a0194160 := rfl

theorem r1F_block_14 : P1_7_1_3.blockEstimate 7341 1556 4244 192 = 0x27c484af160 := rfl

theorem r1F_block_15 : P1_7_1_3.blockEstimate 7341 1556 4436 192 = 0x29bcec4a160 := rfl

theorem r1F_block_16 : P1_7_1_3.blockEstimate 7341 1556 4628 192 = 0x2b633865160 := rfl

theorem r1F_block_17 : P1_7_1_3.blockEstimate 7341 1556 4820 192 = 0x2cb76900160 := rfl

theorem r1F_block_18 : P1_7_1_3.blockEstimate 7341 1556 5012 192 = 0x2db97e1b160 := rfl

theorem r1F_block_19 : P1_7_1_3.blockEstimate 7341 1556 5204 192 = 0x2e6977b6160 := rfl

theorem r1F_block_20 : P1_7_1_3.blockEstimate 7341 1556 5396 192 = 0x2ec755d1160 := rfl

theorem r1F_block_21 : P1_7_1_3.blockEstimate 7341 1556 5588 192 = 0x2ed3186c160 := rfl

theorem r1F_block_22 : P1_7_1_3.blockEstimate 7341 1556 5780 192 = 0x2e8cbf87160 := rfl

theorem r1F_block_23 : P1_7_1_3.blockEstimate 7341 1556 5972 192 = 0x2df44b22160 := rfl

theorem r1F_block_24 : P1_7_1_3.blockEstimate 7341 1556 6164 192 = 0x2d09bb3d160 := rfl

theorem r1F_block_25 : P1_7_1_3.blockEstimate 7341 1556 6356 192 = 0x2bcd0fd8160 := rfl

theorem r1F_block_26 : P1_7_1_3.blockEstimate 7341 1556 6548 192 = 0x2a3e48f3160 := rfl

theorem r1F_block_27 : P1_7_1_3.blockEstimate 7341 1556 6740 192 = 0x285d668e160 := rfl

theorem r1F_block_28 : P1_7_1_3.blockEstimate 7341 1556 6932 192 = 0x262a68a9160 := rfl

theorem r1F_block_29 : P1_7_1_3.blockEstimate 7341 1556 7124 192 = 0x23a54f44160 := rfl

theorem r1F_block_30 : P1_7_1_3.blockEstimate 7341 1556 7316 192 = 0x20d48b5e287 := rfl

theorem r1F_block_31 : P1_7_1_3.blockEstimate 7341 1556 7508 192 = 0x1de114a5d0d := rfl

theorem r1F_block_32 : P1_7_1_3.blockEstimate 7341 1556 7700 192 = 0x1ae25ec5676 := rfl

theorem r1F_block_33 : P1_7_1_3.blockEstimate 7341 1556 7892 192 = 0x17e2f2335c9 := rfl

theorem r1F_block_34 : P1_7_1_3.blockEstimate 7341 1556 8084 192 = 0x14ecdaa5b58 := rfl

theorem r1F_block_35 : P1_7_1_3.blockEstimate 7341 1556 8276 192 = 0x1209abf605c := rfl

theorem r1F_block_36 : P1_7_1_3.blockEstimate 7341 1556 8468 192 = 0xf428221210 := rfl

theorem r1F_block_37 : P1_7_1_3.blockEstimate 7341 1556 8660 192 = 0xca00147dc6 := rfl

theorem r1F_block_38 : P1_7_1_3.blockEstimate 7341 1556 8852 192 = 0xa27cc95897 := rfl

theorem r1F_block_39 : P1_7_1_3.blockEstimate 7341 1556 9044 192 = 0x7e17166cf8 := rfl

theorem r1F_block_40 : P1_7_1_3.blockEstimate 7341 1556 9236 192 = 0x5db18853f8 := rfl

theorem r1F_block_41 : P1_7_1_3.blockEstimate 7341 1556 9428 192 = 0x419ccd5af8 := rfl

theorem r1F_block_42 : P1_7_1_3.blockEstimate 7341 1556 9620 192 = 0x2a24d581f8 := rfl

theorem r1F_block_43 : P1_7_1_3.blockEstimate 7341 1556 9812 192 = 0x179590c8f8 := rfl

theorem r1F_block_44 : P1_7_1_3.blockEstimate 7341 1556 10004 192 = 0xa3aef2ff8 := rfl

theorem r1F_block_45 : P1_7_1_3.blockEstimate 7341 1556 10196 192 = 0x260e0b6f8 := rfl

theorem r1F_block_46 : P1_7_1_3.blockEstimate 7341 1556 10388 65 = 0xaace255 := rfl

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
