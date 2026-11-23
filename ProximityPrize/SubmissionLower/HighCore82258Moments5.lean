import ProximityPrize.SubmissionLower.HighCore82258Moments4
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
set_option quotPrecheck false

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem b3784_799_799 : blockEstimate 3784 799 799 660 = 0x24de545887 := by decide +kernel
private theorem b3784_799_1459 : blockEstimate 3784 799 1459 660 = 0xc6e45af301 := by decide +kernel
private theorem b3784_799_2119 : blockEstimate 3784 799 2119 660 = 0x143ce01c8a0 := by decide +kernel
private theorem b3784_799_2779 : blockEstimate 3784 799 2779 660 = 0x155f054d7a0 := by decide +kernel
private theorem b3784_799_3439 : blockEstimate 3784 799 3439 660 = 0xfe83b8564d := by decide +kernel
private theorem b3784_799_4099 : blockEstimate 3784 799 4099 660 = 0x70d6ec8113 := by decide +kernel
private theorem b3784_799_4759 : blockEstimate 3784 799 4759 623 = 0x108135070c := by decide +kernel
private theorem s3784_799_799_1320 : blockEstimate 3784 799 799 1320 = 0xebc2af4b88 :=
  append (B := 3784) (J := 799) (start := 799) (a := 660) (x := 0x24de545887)
    b3784_799_799 1459 660 0xc6e45af301 1320 0xebc2af4b88 rfl rfl rfl b3784_799_1459
private theorem s3784_799_2119_1320 : blockEstimate 3784 799 2119 1320 = 0x299be56a040 :=
  append (B := 3784) (J := 799) (start := 2119) (a := 660) (x := 0x143ce01c8a0)
    b3784_799_2119 2779 660 0x155f054d7a0 1320 0x299be56a040 rfl rfl rfl b3784_799_2779
private theorem s3784_799_3439_1320 : blockEstimate 3784 799 3439 1320 = 0x16f5aa4d760 :=
  append (B := 3784) (J := 799) (start := 3439) (a := 660) (x := 0xfe83b8564d)
    b3784_799_3439 4099 660 0x70d6ec8113 1320 0x16f5aa4d760 rfl rfl rfl b3784_799_4099
private theorem s3784_799_799_2640 : blockEstimate 3784 799 799 2640 = 0x3858105ebc8 :=
  append (B := 3784) (J := 799) (start := 799) (a := 1320) (x := 0xebc2af4b88)
    s3784_799_799_1320 2119 1320 0x299be56a040 2640 0x3858105ebc8 rfl rfl rfl s3784_799_2119_1320
private theorem s3784_799_3439_1943 : blockEstimate 3784 799 3439 1943 = 0x17fdbd9de6c :=
  append (B := 3784) (J := 799) (start := 3439) (a := 1320) (x := 0x16f5aa4d760)
    s3784_799_3439_1320 4759 623 0x108135070c 1943 0x17fdbd9de6c rfl rfl rfl b3784_799_4759
private theorem s3784_799_799_4583 : blockEstimate 3784 799 799 4583 = 0x5055cdfca34 :=
  append (B := 3784) (J := 799) (start := 799) (a := 2640) (x := 0x3858105ebc8)
    s3784_799_799_2640 3439 1943 0x17fdbd9de6c 4583 0x5055cdfca34 rfl rfl rfl s3784_799_3439_1943
theorem moment3784_799 : momentEstimate 3784 799 = 0x5055cdfca34 := by
  change blockEstimate 3784 799 799 4583 = 0x5055cdfca34
  exact s3784_799_799_4583

private theorem b3012_632_632 : blockEstimate 3012 632 632 660 = 0x1c36f0604a := by decide +kernel
private theorem b3012_632_1292 : blockEstimate 3012 632 1292 660 = 0x812a487bcc := by decide +kernel
private theorem b3012_632_1952 : blockEstimate 3012 632 1952 660 = 0xad559d56cc := by decide +kernel
private theorem b3012_632_2612 : blockEstimate 3012 632 2612 660 = 0x85751bdaad := by decide +kernel
private theorem b3012_632_3272 : blockEstimate 3012 632 3272 660 = 0x2f4c76f105 := by decide +kernel
private theorem b3012_632_3932 : blockEstimate 3012 632 3932 344 = 0x2481d40d4 := by decide +kernel
private theorem s3012_632_632_1320 : blockEstimate 3012 632 632 1320 = 0x9d6138dc16 :=
  append (B := 3012) (J := 632) (start := 632) (a := 660) (x := 0x1c36f0604a)
    b3012_632_632 1292 660 0x812a487bcc 1320 0x9d6138dc16 rfl rfl rfl b3012_632_1292
private theorem s3012_632_1952_1320 : blockEstimate 3012 632 1952 1320 = 0x132cab93179 :=
  append (B := 3012) (J := 632) (start := 1952) (a := 660) (x := 0xad559d56cc)
    b3012_632_1952 2612 660 0x85751bdaad 1320 0x132cab93179 rfl rfl rfl b3012_632_2612
private theorem s3012_632_3272_1004 : blockEstimate 3012 632 3272 1004 = 0x31949431d9 :=
  append (B := 3012) (J := 632) (start := 3272) (a := 660) (x := 0x2f4c76f105)
    b3012_632_3272 3932 344 0x2481d40d4 1004 0x31949431d9 rfl rfl rfl b3012_632_3932
private theorem s3012_632_632_2640 : blockEstimate 3012 632 632 2640 = 0x1d02bf20d8f :=
  append (B := 3012) (J := 632) (start := 632) (a := 1320) (x := 0x9d6138dc16)
    s3012_632_632_1320 1952 1320 0x132cab93179 2640 0x1d02bf20d8f rfl rfl rfl s3012_632_1952_1320
private theorem s3012_632_632_3644 : blockEstimate 3012 632 632 3644 = 0x201c0863f68 :=
  append (B := 3012) (J := 632) (start := 632) (a := 2640) (x := 0x1d02bf20d8f)
    s3012_632_632_2640 3272 1004 0x31949431d9 3644 0x201c0863f68 rfl rfl rfl s3012_632_3272_1004
theorem moment3012_632 : momentEstimate 3012 632 = 0x201c0863f68 := by
  change blockEstimate 3012 632 632 3644 = 0x201c0863f68
  exact s3012_632_632_3644

private theorem b1473_310_310 : blockEstimate 1473 310 310 660 = 0x9784a1d80 := by decide +kernel
private theorem b1473_310_970 : blockEstimate 1473 310 970 660 = 0x11a60909fa := by decide +kernel
private theorem b1473_310_1630 : blockEstimate 1473 310 1630 463 = 0x26c7ffd69 := by decide +kernel
private theorem s1473_310_310_1320 : blockEstimate 1473 310 310 1320 = 0x1b1e53277a :=
  append (B := 1473) (J := 310) (start := 310) (a := 660) (x := 0x9784a1d80)
    b1473_310_310 970 660 0x11a60909fa 1320 0x1b1e53277a rfl rfl rfl b1473_310_970
private theorem s1473_310_310_1783 : blockEstimate 1473 310 310 1783 = 0x1d8ad324e3 :=
  append (B := 1473) (J := 310) (start := 310) (a := 1320) (x := 0x1b1e53277a)
    s1473_310_310_1320 1630 463 0x26c7ffd69 1783 0x1d8ad324e3 rfl rfl rfl b1473_310_1630
theorem moment1473_310 : momentEstimate 1473 310 = 0x1d8ad324e3 := by
  change blockEstimate 1473 310 310 1783 = 0x1d8ad324e3
  exact s1473_310_310_1783

private theorem b1096_237_237 : blockEstimate 1096 237 237 660 = 0x526b8b2f1 := by decide +kernel
private theorem b1096_237_897 : blockEstimate 1096 237 897 660 = 0x41d74913f := by decide +kernel
private theorem b1096_237_1557 : blockEstimate 1096 237 1557 13 = 0x4317e := by decide +kernel
private theorem s1096_237_237_1320 : blockEstimate 1096 237 237 1320 = 0x9442d4430 :=
  append (B := 1096) (J := 237) (start := 237) (a := 660) (x := 0x526b8b2f1)
    b1096_237_237 897 660 0x41d74913f 1320 0x9442d4430 rfl rfl rfl b1096_237_897
private theorem s1096_237_237_1333 : blockEstimate 1096 237 237 1333 = 0x9443175ae :=
  append (B := 1096) (J := 237) (start := 237) (a := 1320) (x := 0x9442d4430)
    s1096_237_237_1320 1557 13 0x4317e 1333 0x9443175ae rfl rfl rfl b1096_237_1557
theorem moment1096_237 : momentEstimate 1096 237 = 0x9443175ae := by
  change blockEstimate 1096 237 237 1333 = 0x9443175ae
  exact s1096_237_237_1333

private theorem b727_154_154 : blockEstimate 727 154 154 660 = 0x1a3caa735 := by decide +kernel
private theorem b727_154_814 : blockEstimate 727 154 814 221 = 0x21ecd5ab := by decide +kernel
private theorem s727_154_154_881 : blockEstimate 727 154 154 881 = 0x1c5b77ce0 :=
  append (B := 727) (J := 154) (start := 154) (a := 660) (x := 0x1a3caa735)
    b727_154_154 814 221 0x21ecd5ab 881 0x1c5b77ce0 rfl rfl rfl b727_154_814
theorem moment727_154 : momentEstimate 727 154 = 0x1c5b77ce0 := by
  change blockEstimate 727 154 154 881 = 0x1c5b77ce0
  exact s727_154_154_881

private theorem b347_77_77 : blockEstimate 347 77 77 424 = 0x18b7e486 := by decide +kernel
theorem moment347_77 : momentEstimate 347 77 = 0x18b7e486 := by
  change blockEstimate 347 77 77 424 = 0x18b7e486
  exact b347_77_77

private theorem b247_55_55 : blockEstimate 247 55 55 302 = 0x66c8fdf := by decide +kernel
theorem moment247_55 : momentEstimate 247 55 = 0x66c8fdf := by
  change blockEstimate 247 55 55 302 = 0x66c8fdf
  exact b247_55_55

private theorem b143_31_31 : blockEstimate 143 31 31 174 = 0xb978d4 := by decide +kernel
theorem moment143_31 : momentEstimate 143 31 = 0xb978d4 := by
  change blockEstimate 143 31 31 174 = 0xb978d4
  exact b143_31_31

end HighCore82258BankProof
