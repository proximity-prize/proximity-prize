import ProximityPrize.SubmissionLower.HighCore82258Source

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
set_option quotPrecheck false

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem b6631_1396_1396 : blockEstimate 6631 1396 1396 660 = 0x44c6677d83 := by decide +kernel
private theorem b6631_1396_2056 : blockEstimate 6631 1396 2056 660 = 0x1b3e623adf7 := by decide +kernel
private theorem b6631_1396_2716 : blockEstimate 6631 1396 2716 660 = 0x3f2e6e90ead := by decide +kernel
private theorem b6631_1396_3376 : blockEstimate 6631 1396 3376 660 = 0x5d02632e776 := by decide +kernel
private theorem b6631_1396_4036 : blockEstimate 6631 1396 4036 660 = 0x6f2764ee246 := by decide +kernel
private theorem b6631_1396_4696 : blockEstimate 6631 1396 4696 660 = 0x759c0299c96 := by decide +kernel
private theorem b6631_1396_5356 : blockEstimate 6631 1396 5356 660 = 0x70603c31666 := by decide +kernel
private theorem b6631_1396_6016 : blockEstimate 6631 1396 6016 660 = 0x5f742ecbfd7 := by decide +kernel
private theorem b6631_1396_6676 : blockEstimate 6631 1396 6676 660 = 0x44cd7150b4b := by decide +kernel
private theorem b6631_1396_7336 : blockEstimate 6631 1396 7336 660 = 0x28dd9d82b94 := by decide +kernel
private theorem b6631_1396_7996 : blockEstimate 6631 1396 7996 660 = 0x11a0161d574 := by decide +kernel
private theorem b6631_1396_8656 : blockEstimate 6631 1396 8656 660 = 0x37121ab36b := by decide +kernel
private theorem b6631_1396_9316 : blockEstimate 6631 1396 9316 107 = 0x29bfd295 := by decide +kernel
private theorem s6631_1396_1396_1320 : blockEstimate 6631 1396 1396 1320 = 0x1f8ac8b2b7a :=
  append (B := 6631) (J := 1396) (start := 1396) (a := 660) (x := 0x44c6677d83)
    b6631_1396_1396 2056 660 0x1b3e623adf7 1320 0x1f8ac8b2b7a rfl rfl rfl b6631_1396_2056
private theorem s6631_1396_2716_1320 : blockEstimate 6631 1396 2716 1320 = 0x9c30d1bf623 :=
  append (B := 6631) (J := 1396) (start := 2716) (a := 660) (x := 0x3f2e6e90ead)
    b6631_1396_2716 3376 660 0x5d02632e776 1320 0x9c30d1bf623 rfl rfl rfl b6631_1396_3376
private theorem s6631_1396_4036_1320 : blockEstimate 6631 1396 4036 1320 = 0xe4c36787edc :=
  append (B := 6631) (J := 1396) (start := 4036) (a := 660) (x := 0x6f2764ee246)
    b6631_1396_4036 4696 660 0x759c0299c96 1320 0xe4c36787edc rfl rfl rfl b6631_1396_4696
private theorem s6631_1396_5356_1320 : blockEstimate 6631 1396 5356 1320 = 0xcfd46afd63d :=
  append (B := 6631) (J := 1396) (start := 5356) (a := 660) (x := 0x70603c31666)
    b6631_1396_5356 6016 660 0x5f742ecbfd7 1320 0xcfd46afd63d rfl rfl rfl b6631_1396_6016
private theorem s6631_1396_6676_1320 : blockEstimate 6631 1396 6676 1320 = 0x6dab0ed36df :=
  append (B := 6631) (J := 1396) (start := 6676) (a := 660) (x := 0x44cd7150b4b)
    b6631_1396_6676 7336 660 0x28dd9d82b94 1320 0x6dab0ed36df rfl rfl rfl b6631_1396_7336
private theorem s6631_1396_7996_1320 : blockEstimate 6631 1396 7996 1320 = 0x151137c88df :=
  append (B := 6631) (J := 1396) (start := 7996) (a := 660) (x := 0x11a0161d574)
    b6631_1396_7996 8656 660 0x37121ab36b 1320 0x151137c88df rfl rfl rfl b6631_1396_8656
private theorem s6631_1396_1396_2640 : blockEstimate 6631 1396 1396 2640 = 0xbbbb9a7219d :=
  append (B := 6631) (J := 1396) (start := 1396) (a := 1320) (x := 0x1f8ac8b2b7a)
    s6631_1396_1396_1320 2716 1320 0x9c30d1bf623 2640 0xbbbb9a7219d rfl rfl rfl s6631_1396_2716_1320
private theorem s6631_1396_4036_2640 : blockEstimate 6631 1396 4036 2640 = 0x1b497d285519 :=
  append (B := 6631) (J := 1396) (start := 4036) (a := 1320) (x := 0xe4c36787edc)
    s6631_1396_4036_1320 5356 1320 0xcfd46afd63d 2640 0x1b497d285519 rfl rfl rfl s6631_1396_5356_1320
private theorem s6631_1396_6676_2640 : blockEstimate 6631 1396 6676 2640 = 0x82bc469bfbe :=
  append (B := 6631) (J := 1396) (start := 6676) (a := 1320) (x := 0x6dab0ed36df)
    s6631_1396_6676_1320 7996 1320 0x151137c88df 2640 0x82bc469bfbe rfl rfl rfl s6631_1396_7996_1320
private theorem s6631_1396_1396_5280 : blockEstimate 6631 1396 1396 5280 = 0x270536cf76b6 :=
  append (B := 6631) (J := 1396) (start := 1396) (a := 2640) (x := 0xbbbb9a7219d)
    s6631_1396_1396_2640 4036 2640 0x1b497d285519 5280 0x270536cf76b6 rfl rfl rfl s6631_1396_4036_2640
private theorem s6631_1396_6676_2747 : blockEstimate 6631 1396 6676 2747 = 0x82bee299253 :=
  append (B := 6631) (J := 1396) (start := 6676) (a := 2640) (x := 0x82bc469bfbe)
    s6631_1396_6676_2640 9316 107 0x29bfd295 2747 0x82bee299253 rfl rfl rfl b6631_1396_9316
private theorem s6631_1396_1396_8027 : blockEstimate 6631 1396 1396 8027 = 0x2f3124f90909 :=
  append (B := 6631) (J := 1396) (start := 1396) (a := 5280) (x := 0x270536cf76b6)
    s6631_1396_1396_5280 6676 2747 0x82bee299253 8027 0x2f3124f90909 rfl rfl rfl s6631_1396_6676_2747
theorem moment6631_1396 : momentEstimate 6631 1396 = 0x2f3124f90909 := by
  change blockEstimate 6631 1396 1396 8027 = 0x2f3124f90909
  exact s6631_1396_1396_8027

private theorem b1893_399_399 : blockEstimate 1893 399 399 660 = 0xec7a457c4 := by decide +kernel
private theorem b1893_399_1059 : blockEstimate 1893 399 1059 660 = 0x29b28df190 := by decide +kernel
private theorem b1893_399_1719 : blockEstimate 1893 399 1719 660 = 0x170d61b8a8 := by decide +kernel
private theorem b1893_399_2379 : blockEstimate 1893 399 2379 312 = 0x10b6ca37e := by decide +kernel
private theorem s1893_399_399_1320 : blockEstimate 1893 399 399 1320 = 0x387a324954 :=
  append (B := 1893) (J := 399) (start := 399) (a := 660) (x := 0xec7a457c4)
    b1893_399_399 1059 660 0x29b28df190 1320 0x387a324954 rfl rfl rfl b1893_399_1059
private theorem s1893_399_1719_972 : blockEstimate 1893 399 1719 972 = 0x1818ce5c26 :=
  append (B := 1893) (J := 399) (start := 1719) (a := 660) (x := 0x170d61b8a8)
    b1893_399_1719 2379 312 0x10b6ca37e 972 0x1818ce5c26 rfl rfl rfl b1893_399_2379
private theorem s1893_399_399_2292 : blockEstimate 1893 399 399 2292 = 0x509300a57a :=
  append (B := 1893) (J := 399) (start := 399) (a := 1320) (x := 0x387a324954)
    s1893_399_399_1320 1719 972 0x1818ce5c26 2292 0x509300a57a rfl rfl rfl s1893_399_1719_972
theorem moment1893_399 : momentEstimate 1893 399 = 0x509300a57a := by
  change blockEstimate 1893 399 399 2292 = 0x509300a57a
  exact s1893_399_399_2292

private theorem b904_200_200 : blockEstimate 904 200 200 660 = 0x33bf63716 := by decide +kernel
private theorem b904_200_860 : blockEstimate 904 200 860 444 = 0x1236ff49d := by decide +kernel
private theorem s904_200_200_1104 : blockEstimate 904 200 200 1104 = 0x45f662bb3 :=
  append (B := 904) (J := 200) (start := 200) (a := 660) (x := 0x33bf63716)
    b904_200_200 860 444 0x1236ff49d 1104 0x45f662bb3 rfl rfl rfl b904_200_860
theorem moment904_200 : momentEstimate 904 200 = 0x45f662bb3 := by
  change blockEstimate 904 200 200 1104 = 0x45f662bb3
  exact s904_200_200_1104

private theorem b626_134_134 : blockEstimate 626 134 134 660 = 0xf8ec6c5c := by decide +kernel
private theorem b626_134_794 : blockEstimate 626 134 794 100 = 0x302c931 := by decide +kernel
private theorem s626_134_134_760 : blockEstimate 626 134 134 760 = 0xfbef358d :=
  append (B := 626) (J := 134) (start := 134) (a := 660) (x := 0xf8ec6c5c)
    b626_134_134 794 100 0x302c931 760 0xfbef358d rfl rfl rfl b626_134_794
theorem moment626_134 : momentEstimate 626 134 = 0xfbef358d := by
  change blockEstimate 626 134 134 760 = 0xfbef358d
  exact s626_134_134_760

private theorem b471_106_106 : blockEstimate 471 106 106 577 = 0x544a4209 := by decide +kernel
theorem moment471_106 : momentEstimate 471 106 = 0x544a4209 := by
  change blockEstimate 471 106 106 577 = 0x544a4209
  exact b471_106_106

private theorem b237_50_50 : blockEstimate 237 50 50 287 = 0x53b7f45 := by decide +kernel
theorem moment237_50 : momentEstimate 237 50 = 0x53b7f45 := by
  change blockEstimate 237 50 50 287 = 0x53b7f45
  exact b237_50_50

private theorem b107_23_23 : blockEstimate 107 23 23 130 = 0x3ae575 := by decide +kernel
theorem moment107_23 : momentEstimate 107 23 = 0x3ae575 := by
  change blockEstimate 107 23 23 130 = 0x3ae575
  exact b107_23_23

end HighCore82258BankProof
