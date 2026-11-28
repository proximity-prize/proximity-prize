import ProximityPrize.SubmissionLower.Z6970GateLeadingSteps

set_option Elab.async false
set_option maxRecDepth 3500
set_option maxHeartbeats 0

namespace Gate6970Leading

private theorem block0 : check 0 48 = true := by decide +kernel
private theorem block48 : check 48 48 = true := by decide +kernel
private theorem block96 : check 96 48 = true := by decide +kernel
private theorem block144 : check 144 48 = true := by decide +kernel
private theorem block192 : check 192 48 = true := by decide +kernel
private theorem block240 : check 240 48 = true := by decide +kernel
private theorem block288 : check 288 48 = true := by decide +kernel
private theorem block336 : check 336 48 = true := by decide +kernel
private theorem block384 : check 384 48 = true := by decide +kernel
private theorem block432 : check 432 48 = true := by decide +kernel
private theorem block480 : check 480 48 = true := by decide +kernel
private theorem block528 : check 528 48 = true := by decide +kernel
private theorem block576 : check 576 48 = true := by decide +kernel
private theorem block624 : check 624 48 = true := by decide +kernel
private theorem block672 : check 672 48 = true := by decide +kernel
private theorem block720 : check 720 48 = true := by decide +kernel
private theorem block768 : check 768 48 = true := by decide +kernel
private theorem block816 : check 816 48 = true := by decide +kernel
private theorem block864 : check 864 48 = true := by decide +kernel
private theorem block912 : check 912 48 = true := by decide +kernel
private theorem block960 : check 960 48 = true := by decide +kernel
private theorem block1008 : check 1008 48 = true := by decide +kernel
private theorem block1056 : check 1056 48 = true := by decide +kernel
private theorem block1104 : check 1104 48 = true := by decide +kernel
private theorem block1152 : check 1152 48 = true := by decide +kernel
private theorem block1200 : check 1200 48 = true := by decide +kernel
private theorem block1248 : check 1248 48 = true := by decide +kernel
private theorem block1296 : check 1296 48 = true := by decide +kernel
private theorem block1344 : check 1344 48 = true := by decide +kernel
private theorem block1392 : check 1392 48 = true := by decide +kernel
private theorem block1440 : check 1440 48 = true := by decide +kernel
private theorem block1488 : check 1488 48 = true := by decide +kernel
private theorem block1536 : check 1536 48 = true := by decide +kernel
private theorem block1584 : check 1584 48 = true := by decide +kernel
private theorem block1632 : check 1632 48 = true := by decide +kernel
private theorem join0_96 : check 0 96 = true := check_join (n := 48) (m := 48) block0 block48
private theorem join96_192 : check 96 96 = true := check_join (n := 48) (m := 48) block96 block144
private theorem join0_192 : check 0 192 = true := check_join (n := 96) (m := 96) join0_96 join96_192
private theorem join192_288 : check 192 96 = true := check_join (n := 48) (m := 48) block192 block240
private theorem join288_384 : check 288 96 = true := check_join (n := 48) (m := 48) block288 block336
private theorem join192_384 : check 192 192 = true := check_join (n := 96) (m := 96) join192_288 join288_384
private theorem join0_384 : check 0 384 = true := check_join (n := 192) (m := 192) join0_192 join192_384
private theorem join384_480 : check 384 96 = true := check_join (n := 48) (m := 48) block384 block432
private theorem join480_576 : check 480 96 = true := check_join (n := 48) (m := 48) block480 block528
private theorem join384_576 : check 384 192 = true := check_join (n := 96) (m := 96) join384_480 join480_576
private theorem join576_672 : check 576 96 = true := check_join (n := 48) (m := 48) block576 block624
private theorem join720_816 : check 720 96 = true := check_join (n := 48) (m := 48) block720 block768
private theorem join672_816 : check 672 144 = true := check_join (n := 48) (m := 96) block672 join720_816
private theorem join576_816 : check 576 240 = true := check_join (n := 96) (m := 144) join576_672 join672_816
private theorem join384_816 : check 384 432 = true := check_join (n := 192) (m := 240) join384_576 join576_816
private theorem join0_816 : check 0 816 = true := check_join (n := 384) (m := 432) join0_384 join384_816
private theorem join816_912 : check 816 96 = true := check_join (n := 48) (m := 48) block816 block864
private theorem join912_1008 : check 912 96 = true := check_join (n := 48) (m := 48) block912 block960
private theorem join816_1008 : check 816 192 = true := check_join (n := 96) (m := 96) join816_912 join912_1008
private theorem join1008_1104 : check 1008 96 = true := check_join (n := 48) (m := 48) block1008 block1056
private theorem join1152_1248 : check 1152 96 = true := check_join (n := 48) (m := 48) block1152 block1200
private theorem join1104_1248 : check 1104 144 = true := check_join (n := 48) (m := 96) block1104 join1152_1248
private theorem join1008_1248 : check 1008 240 = true := check_join (n := 96) (m := 144) join1008_1104 join1104_1248
private theorem join816_1248 : check 816 432 = true := check_join (n := 192) (m := 240) join816_1008 join1008_1248
private theorem join1248_1344 : check 1248 96 = true := check_join (n := 48) (m := 48) block1248 block1296
private theorem join1344_1440 : check 1344 96 = true := check_join (n := 48) (m := 48) block1344 block1392
private theorem join1248_1440 : check 1248 192 = true := check_join (n := 96) (m := 96) join1248_1344 join1344_1440
private theorem join1440_1536 : check 1440 96 = true := check_join (n := 48) (m := 48) block1440 block1488
private theorem join1584_1680 : check 1584 96 = true := check_join (n := 48) (m := 48) block1584 block1632
private theorem join1536_1680 : check 1536 144 = true := check_join (n := 48) (m := 96) block1536 join1584_1680
private theorem join1440_1680 : check 1440 240 = true := check_join (n := 96) (m := 144) join1440_1536 join1536_1680
private theorem join1248_1680 : check 1248 432 = true := check_join (n := 192) (m := 240) join1248_1440 join1440_1680
private theorem join816_1680 : check 816 864 = true := check_join (n := 432) (m := 432) join816_1248 join1248_1680
private theorem join0_1680 : check 0 1680 = true := check_join (n := 816) (m := 864) join0_816 join816_1680

theorem stairs_checked : StepRule stairs := steps_of_check join0_1680

end Gate6970Leading
