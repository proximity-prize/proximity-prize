import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000

namespace HighCore82219BankProof
open P1_7_1_3 (blockEstimate)

theorem w6010_1275_4 : blockEstimate 6010 1275 2075 200 = 0x60d9f5192a := by decide +kernel
theorem w6010_1275_16 : blockEstimate 6010 1275 4475 200 = 0x1acaffdd038 := by decide +kernel
theorem w6010_1275_28 : blockEstimate 6010 1275 6875 200 = 0x91c2e4fc33 := by decide +kernel
theorem w4863_1027_4 : blockEstimate 4863 1027 1827 200 = 0x4b152b57c2 := by decide +kernel
theorem w4863_1027_16 : blockEstimate 4863 1027 4227 200 = 0xd06ec28b68 := by decide +kernel
theorem w4863_1027_28 : blockEstimate 4863 1027 6627 200 = 0x2334dab77 := by decide +kernel
theorem w3850_812_18 : blockEstimate 3850 812 4412 200 = 0x22ef654174 := by decide +kernel
theorem w3142_664_7 : blockEstimate 3142 664 2064 200 = 0x3b545c94c0 := by decide +kernel
theorem w6010_1275_36 : blockEstimate 6010 1275 8475 85 = 0x1330b2ab := by decide +kernel
theorem w2235_472_3 : blockEstimate 2235 472 1072 200 = 0xfa2e0dc54 := by decide +kernel
theorem w2035_429_1 : blockEstimate 2035 429 629 200 = 0x3bfbaacb2 := by decide +kernel
theorem w1815_383_1 : blockEstimate 1815 383 583 200 = 0x3447bfa1e := by decide +kernel
theorem w1412_298_2 : blockEstimate 1412 298 698 200 = 0x46b5d54fc := by decide +kernel
theorem w1202_254_5 : blockEstimate 1202 254 1254 200 = 0x17151e27a := by decide +kernel
theorem w952_201_2 : blockEstimate 952 201 601 200 = 0x1abd391fc := by decide +kernel
theorem w831_188_4 : blockEstimate 831 188 988 200 = 0x26bdacb7 := by decide +kernel
theorem w692_155_0 : blockEstimate 692 155 155 200 = 0x2b53c7cd := by decide +kernel
theorem w606_128_0 : blockEstimate 606 128 128 200 = 0x23459730 := by decide +kernel
theorem w692_155_4 : blockEstimate 692 155 955 47 = 0x61368c := by decide +kernel
theorem w686_144_4 : blockEstimate 686 144 944 30 = 0x1aaefc := by decide +kernel

end HighCore82219BankProof
