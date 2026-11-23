import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2430Banks
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem p982 : blockEstimate 4658 982 982 128 = 0x614bfb20 := by decide +kernel
private theorem p1110 : blockEstimate 4658 982 1110 128 = 0x28fe88b20 := by decide +kernel
private theorem p1238 : blockEstimate 4658 982 1238 128 = 0x6bc951b20 := by decide +kernel
private theorem p1366 : blockEstimate 4658 982 1366 128 = 0xcb751ab20 := by decide +kernel
private theorem p1494 : blockEstimate 4658 982 1494 128 = 0x14501e3b20 := by decide +kernel
private theorem p1622 : blockEstimate 4658 982 1622 128 = 0x1d56facb20 := by decide +kernel
private theorem p1750 : blockEstimate 4658 982 1750 128 = 0x279be75b20 := by decide +kernel
private theorem p1878 : blockEstimate 4658 982 1878 128 = 0x32ec35887f := by decide +kernel
private theorem p2006 : blockEstimate 4658 982 2006 128 = 0x3e7569c1c0 := by decide +kernel
private theorem p2134 : blockEstimate 4658 982 2134 128 = 0x49208081c0 := by decide +kernel
private theorem p2262 : blockEstimate 4658 982 2262 128 = 0x52d5d741c0 := by decide +kernel
private theorem p2390 : blockEstimate 4658 982 2390 128 = 0x5b956e01c0 := by decide +kernel
private theorem p2518 : blockEstimate 4658 982 2518 128 = 0x635f44c1c0 := by decide +kernel
private theorem p2646 : blockEstimate 4658 982 2646 128 = 0x6a335b81c0 := by decide +kernel
private theorem p2774 : blockEstimate 4658 982 2774 128 = 0x7011b241c0 := by decide +kernel
private theorem p2902 : blockEstimate 4658 982 2902 128 = 0x74fa4901c0 := by decide +kernel
private theorem p3030 : blockEstimate 4658 982 3030 128 = 0x78ed1fc1c0 := by decide +kernel
private theorem p3158 : blockEstimate 4658 982 3158 128 = 0x7bea3681c0 := by decide +kernel
private theorem p3286 : blockEstimate 4658 982 3286 128 = 0x7df18d41c0 := by decide +kernel
private theorem p3414 : blockEstimate 4658 982 3414 128 = 0x7f032401c0 := by decide +kernel
private theorem p3542 : blockEstimate 4658 982 3542 128 = 0x7f1efac1c0 := by decide +kernel
private theorem p3670 : blockEstimate 4658 982 3670 128 = 0x7e451181c0 := by decide +kernel
private theorem p3798 : blockEstimate 4658 982 3798 128 = 0x7c756841c0 := by decide +kernel
private theorem p3926 : blockEstimate 4658 982 3926 128 = 0x79afff01c0 := by decide +kernel
private theorem p4054 : blockEstimate 4658 982 4054 128 = 0x75f4d5c1c0 := by decide +kernel
private theorem p4182 : blockEstimate 4658 982 4182 128 = 0x7143ec81c0 := by decide +kernel
private theorem p4310 : blockEstimate 4658 982 4310 128 = 0x6b9d4341c0 := by decide +kernel
private theorem p4438 : blockEstimate 4658 982 4438 128 = 0x6500da01c0 := by decide +kernel
private theorem p4566 : blockEstimate 4658 982 4566 128 = 0x5d6f59978f := by decide +kernel
private theorem p4694 : blockEstimate 4658 982 4694 128 = 0x5525b72c0b := by decide +kernel
private theorem p4822 : blockEstimate 4658 982 4822 128 = 0x4ca0694c87 := by decide +kernel
private theorem p4950 : blockEstimate 4658 982 4950 128 = 0x440b48097d := by decide +kernel
private theorem p5078 : blockEstimate 4658 982 5078 128 = 0x3b86c14b30 := by decide +kernel
private theorem p5206 : blockEstimate 4658 982 5206 128 = 0x3331b2f3cf := by decide +kernel
private theorem p5334 : blockEstimate 4658 982 5334 128 = 0x2b296ae2ae := by decide +kernel
private theorem p5462 : blockEstimate 4658 982 5462 128 = 0x2389a6f07e := by decide +kernel
private theorem p5590 : blockEstimate 4658 982 5590 128 = 0x1c67d99a86 := by decide +kernel
private theorem p5718 : blockEstimate 4658 982 5718 128 = 0x15d6ca1500 := by decide +kernel
private theorem p5846 : blockEstimate 4658 982 5846 128 = 0x1003e1a500 := by decide +kernel
private theorem p5974 : blockEstimate 4658 982 5974 128 = 0xb00923500 := by decide +kernel
private theorem p6102 : blockEstimate 4658 982 6102 128 = 0x6dbdbc500 := by decide +kernel
private theorem p6230 : blockEstimate 4658 982 6230 128 = 0x3a4be5500 := by decide +kernel
private theorem p6358 : blockEstimate 4658 982 6358 128 = 0x16a39e500 := by decide +kernel
private theorem p6486 : blockEstimate 4658 982 6486 128 = 0x3b4e7500 := by decide +kernel
private theorem p6614 : blockEstimate 4658 982 6614 8 = 0x4f8d0 := by decide +kernel

private theorem sum_982_256 : blockEstimate 4658 982 982 256 = 0x2f1348640 :=
  append (B := 4658) (J := 982) (start := 982) (a := 128) (x := 0x614bfb20)
    p982 1110 128 0x28fe88b20 256 0x2f1348640 rfl rfl rfl p1110

private theorem sum_1238_256 : blockEstimate 4658 982 1238 256 = 0x1373e6c640 :=
  append (B := 4658) (J := 982) (start := 1238) (a := 128) (x := 0x6bc951b20)
    p1238 1366 128 0xcb751ab20 256 0x1373e6c640 rfl rfl rfl p1366

private theorem sum_1494_256 : blockEstimate 4658 982 1494 256 = 0x31a7190640 :=
  append (B := 4658) (J := 982) (start := 1494) (a := 128) (x := 0x14501e3b20)
    p1494 1622 128 0x1d56facb20 256 0x31a7190640 rfl rfl rfl p1622

private theorem sum_1750_256 : blockEstimate 4658 982 1750 256 = 0x5a881ce39f :=
  append (B := 4658) (J := 982) (start := 1750) (a := 128) (x := 0x279be75b20)
    p1750 1878 128 0x32ec35887f 256 0x5a881ce39f rfl rfl rfl p1878

private theorem sum_2006_256 : blockEstimate 4658 982 2006 256 = 0x8795ea4380 :=
  append (B := 4658) (J := 982) (start := 2006) (a := 128) (x := 0x3e7569c1c0)
    p2006 2134 128 0x49208081c0 256 0x8795ea4380 rfl rfl rfl p2134

private theorem sum_2262_256 : blockEstimate 4658 982 2262 256 = 0xae6b454380 :=
  append (B := 4658) (J := 982) (start := 2262) (a := 128) (x := 0x52d5d741c0)
    p2262 2390 128 0x5b956e01c0 256 0xae6b454380 rfl rfl rfl p2390

private theorem sum_2518_256 : blockEstimate 4658 982 2518 256 = 0xcd92a04380 :=
  append (B := 4658) (J := 982) (start := 2518) (a := 128) (x := 0x635f44c1c0)
    p2518 2646 128 0x6a335b81c0 256 0xcd92a04380 rfl rfl rfl p2646

private theorem sum_2774_256 : blockEstimate 4658 982 2774 256 = 0xe50bfb4380 :=
  append (B := 4658) (J := 982) (start := 2774) (a := 128) (x := 0x7011b241c0)
    p2774 2902 128 0x74fa4901c0 256 0xe50bfb4380 rfl rfl rfl p2902

private theorem sum_3030_256 : blockEstimate 4658 982 3030 256 = 0xf4d7564380 :=
  append (B := 4658) (J := 982) (start := 3030) (a := 128) (x := 0x78ed1fc1c0)
    p3030 3158 128 0x7bea3681c0 256 0xf4d7564380 rfl rfl rfl p3158

private theorem sum_3286_256 : blockEstimate 4658 982 3286 256 = 0xfcf4b14380 :=
  append (B := 4658) (J := 982) (start := 3286) (a := 128) (x := 0x7df18d41c0)
    p3286 3414 128 0x7f032401c0 256 0xfcf4b14380 rfl rfl rfl p3414

private theorem sum_3542_256 : blockEstimate 4658 982 3542 256 = 0xfd640c4380 :=
  append (B := 4658) (J := 982) (start := 3542) (a := 128) (x := 0x7f1efac1c0)
    p3542 3670 128 0x7e451181c0 256 0xfd640c4380 rfl rfl rfl p3670

private theorem sum_3798_256 : blockEstimate 4658 982 3798 256 = 0xf625674380 :=
  append (B := 4658) (J := 982) (start := 3798) (a := 128) (x := 0x7c756841c0)
    p3798 3926 128 0x79afff01c0 256 0xf625674380 rfl rfl rfl p3926

private theorem sum_4054_256 : blockEstimate 4658 982 4054 256 = 0xe738c24380 :=
  append (B := 4658) (J := 982) (start := 4054) (a := 128) (x := 0x75f4d5c1c0)
    p4054 4182 128 0x7143ec81c0 256 0xe738c24380 rfl rfl rfl p4182

private theorem sum_4310_256 : blockEstimate 4658 982 4310 256 = 0xd09e1d4380 :=
  append (B := 4658) (J := 982) (start := 4310) (a := 128) (x := 0x6b9d4341c0)
    p4310 4438 128 0x6500da01c0 256 0xd09e1d4380 rfl rfl rfl p4438

private theorem sum_4566_256 : blockEstimate 4658 982 4566 256 = 0xb29510c39a :=
  append (B := 4658) (J := 982) (start := 4566) (a := 128) (x := 0x5d6f59978f)
    p4566 4694 128 0x5525b72c0b 256 0xb29510c39a rfl rfl rfl p4694

private theorem sum_4822_256 : blockEstimate 4658 982 4822 256 = 0x90abb15604 :=
  append (B := 4658) (J := 982) (start := 4822) (a := 128) (x := 0x4ca0694c87)
    p4822 4950 128 0x440b48097d 256 0x90abb15604 rfl rfl rfl p4950

private theorem sum_5078_256 : blockEstimate 4658 982 5078 256 = 0x6eb8743eff :=
  append (B := 4658) (J := 982) (start := 5078) (a := 128) (x := 0x3b86c14b30)
    p5078 5206 128 0x3331b2f3cf 256 0x6eb8743eff rfl rfl rfl p5206

private theorem sum_5334_256 : blockEstimate 4658 982 5334 256 = 0x4eb311d32c :=
  append (B := 4658) (J := 982) (start := 5334) (a := 128) (x := 0x2b296ae2ae)
    p5334 5462 128 0x2389a6f07e 256 0x4eb311d32c rfl rfl rfl p5462

private theorem sum_5590_256 : blockEstimate 4658 982 5590 256 = 0x323ea3af86 :=
  append (B := 4658) (J := 982) (start := 5590) (a := 128) (x := 0x1c67d99a86)
    p5590 5718 128 0x15d6ca1500 256 0x323ea3af86 rfl rfl rfl p5718

private theorem sum_5846_256 : blockEstimate 4658 982 5846 256 = 0x1b0473da00 :=
  append (B := 4658) (J := 982) (start := 5846) (a := 128) (x := 0x1003e1a500)
    p5846 5974 128 0xb00923500 256 0x1b0473da00 rfl rfl rfl p5974

private theorem sum_6102_256 : blockEstimate 4658 982 6102 256 = 0xa809a1a00 :=
  append (B := 4658) (J := 982) (start := 6102) (a := 128) (x := 0x6dbdbc500)
    p6102 6230 128 0x3a4be5500 256 0xa809a1a00 rfl rfl rfl p6230

private theorem sum_6358_256 : blockEstimate 4658 982 6358 256 = 0x1a5885a00 :=
  append (B := 4658) (J := 982) (start := 6358) (a := 128) (x := 0x16a39e500)
    p6358 6486 128 0x3b4e7500 256 0x1a5885a00 rfl rfl rfl p6486

private theorem sum_982_512 : blockEstimate 4658 982 982 512 = 0x16651b4c80 :=
  append (B := 4658) (J := 982) (start := 982) (a := 256) (x := 0x2f1348640)
    sum_982_256 1238 256 0x1373e6c640 512 0x16651b4c80 rfl rfl rfl sum_1238_256

private theorem sum_1494_512 : blockEstimate 4658 982 1494 512 = 0x8c2f35e9df :=
  append (B := 4658) (J := 982) (start := 1494) (a := 256) (x := 0x31a7190640)
    sum_1494_256 1750 256 0x5a881ce39f 512 0x8c2f35e9df rfl rfl rfl sum_1750_256

private theorem sum_2006_512 : blockEstimate 4658 982 2006 512 = 0x136012f8700 :=
  append (B := 4658) (J := 982) (start := 2006) (a := 256) (x := 0x8795ea4380)
    sum_2006_256 2262 256 0xae6b454380 512 0x136012f8700 rfl rfl rfl sum_2262_256

private theorem sum_2518_512 : blockEstimate 4658 982 2518 512 = 0x1b29e9b8700 :=
  append (B := 4658) (J := 982) (start := 2518) (a := 256) (x := 0xcd92a04380)
    sum_2518_256 2774 256 0xe50bfb4380 512 0x1b29e9b8700 rfl rfl rfl sum_2774_256

private theorem sum_3030_512 : blockEstimate 4658 982 3030 512 = 0x1f1cc078700 :=
  append (B := 4658) (J := 982) (start := 3030) (a := 256) (x := 0xf4d7564380)
    sum_3030_256 3286 256 0xfcf4b14380 512 0x1f1cc078700 rfl rfl rfl sum_3286_256

private theorem sum_3542_512 : blockEstimate 4658 982 3542 512 = 0x1f389738700 :=
  append (B := 4658) (J := 982) (start := 3542) (a := 256) (x := 0xfd640c4380)
    sum_3542_256 3798 256 0xf625674380 512 0x1f389738700 rfl rfl rfl sum_3798_256

private theorem sum_4054_512 : blockEstimate 4658 982 4054 512 = 0x1b7d6df8700 :=
  append (B := 4658) (J := 982) (start := 4054) (a := 256) (x := 0xe738c24380)
    sum_4054_256 4310 256 0xd09e1d4380 512 0x1b7d6df8700 rfl rfl rfl sum_4310_256

private theorem sum_4566_512 : blockEstimate 4658 982 4566 512 = 0x14340c2199e :=
  append (B := 4658) (J := 982) (start := 4566) (a := 256) (x := 0xb29510c39a)
    sum_4566_256 4822 256 0x90abb15604 512 0x14340c2199e rfl rfl rfl sum_4822_256

private theorem sum_5078_512 : blockEstimate 4658 982 5078 512 = 0xbd6b86122b :=
  append (B := 4658) (J := 982) (start := 5078) (a := 256) (x := 0x6eb8743eff)
    sum_5078_256 5334 256 0x4eb311d32c 512 0xbd6b86122b rfl rfl rfl sum_5334_256

private theorem sum_5590_512 : blockEstimate 4658 982 5590 512 = 0x4d43178986 :=
  append (B := 4658) (J := 982) (start := 5590) (a := 256) (x := 0x323ea3af86)
    sum_5590_256 5846 256 0x1b0473da00 512 0x4d43178986 rfl rfl rfl sum_5846_256

private theorem sum_6102_512 : blockEstimate 4658 982 6102 512 = 0xc26227400 :=
  append (B := 4658) (J := 982) (start := 6102) (a := 256) (x := 0xa809a1a00)
    sum_6102_256 6358 256 0x1a5885a00 512 0xc26227400 rfl rfl rfl sum_6358_256

private theorem sum_982_1024 : blockEstimate 4658 982 982 1024 = 0xa29451365f :=
  append (B := 4658) (J := 982) (start := 982) (a := 512) (x := 0x16651b4c80)
    sum_982_512 1494 512 0x8c2f35e9df 1024 0xa29451365f rfl rfl rfl sum_1494_512

private theorem sum_2006_1024 : blockEstimate 4658 982 2006 1024 = 0x2e89fcb0e00 :=
  append (B := 4658) (J := 982) (start := 2006) (a := 512) (x := 0x136012f8700)
    sum_2006_512 2518 512 0x1b29e9b8700 1024 0x2e89fcb0e00 rfl rfl rfl sum_2518_512

private theorem sum_3030_1024 : blockEstimate 4658 982 3030 1024 = 0x3e5557b0e00 :=
  append (B := 4658) (J := 982) (start := 3030) (a := 512) (x := 0x1f1cc078700)
    sum_3030_512 3542 512 0x1f389738700 1024 0x3e5557b0e00 rfl rfl rfl sum_3542_512

private theorem sum_4054_1024 : blockEstimate 4658 982 4054 1024 = 0x2fb17a1a09e :=
  append (B := 4658) (J := 982) (start := 4054) (a := 512) (x := 0x1b7d6df8700)
    sum_4054_512 4566 512 0x14340c2199e 1024 0x2fb17a1a09e rfl rfl rfl sum_4566_512

private theorem sum_5078_1024 : blockEstimate 4658 982 5078 1024 = 0x10aae9d9bb1 :=
  append (B := 4658) (J := 982) (start := 5078) (a := 512) (x := 0xbd6b86122b)
    sum_5078_512 5590 512 0x4d43178986 1024 0x10aae9d9bb1 rfl rfl rfl sum_5590_512

private theorem sum_6102_520 : blockEstimate 4658 982 6102 520 = 0xc26276cd0 :=
  append (B := 4658) (J := 982) (start := 6102) (a := 512) (x := 0xc26227400)
    sum_6102_512 6614 8 0x4f8d0 520 0xc26276cd0 rfl rfl rfl p6614

private theorem sum_982_2048 : blockEstimate 4658 982 982 2048 = 0x38b341c445f :=
  append (B := 4658) (J := 982) (start := 982) (a := 1024) (x := 0xa29451365f)
    sum_982_1024 2006 1024 0x2e89fcb0e00 2048 0x38b341c445f rfl rfl rfl sum_2006_1024

private theorem sum_3030_2048 : blockEstimate 4658 982 3030 2048 = 0x6e06d1cae9e :=
  append (B := 4658) (J := 982) (start := 3030) (a := 1024) (x := 0x3e5557b0e00)
    sum_3030_1024 4054 1024 0x2fb17a1a09e 2048 0x6e06d1cae9e rfl rfl rfl sum_4054_1024

private theorem sum_5078_1544 : blockEstimate 4658 982 5078 1544 = 0x116d4c50881 :=
  append (B := 4658) (J := 982) (start := 5078) (a := 1024) (x := 0x10aae9d9bb1)
    sum_5078_1024 6102 520 0xc26276cd0 1544 0x116d4c50881 rfl rfl rfl sum_6102_520

private theorem sum_982_4096 : blockEstimate 4658 982 982 4096 = 0xa6ba138f2fd :=
  append (B := 4658) (J := 982) (start := 982) (a := 2048) (x := 0x38b341c445f)
    sum_982_2048 3030 2048 0x6e06d1cae9e 4096 0xa6ba138f2fd rfl rfl rfl sum_3030_2048

private theorem sum_982_5640 : blockEstimate 4658 982 982 5640 = 0xb8275fdfb7e :=
  append (B := 4658) (J := 982) (start := 982) (a := 4096) (x := 0xa6ba138f2fd)
    sum_982_4096 5078 1544 0x116d4c50881 5640 0xb8275fdfb7e rfl rfl rfl sum_5078_1544

theorem moment4658_982 : momentEstimate 4658 982 = 0xb8275fdfb7e := by
  change blockEstimate 4658 982 982 5640 = 0xb8275fdfb7e
  exact sum_982_5640

end KoalaH2430Banks
