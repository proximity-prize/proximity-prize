import ProximityPrize.SubmissionLower.HighCore82258Moments1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
set_option quotPrecheck false

namespace HighCore82258BankProof
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

private theorem b5843_1234_1234 : blockEstimate 5843 1234 1234 660 = 0x3bf19f9b33 := by decide +kernel
private theorem b5843_1234_1894 : blockEstimate 5843 1234 1894 660 = 0x17620f0ba1c := by decide +kernel
private theorem b5843_1234_2554 : blockEstimate 5843 1234 2554 660 = 0x32f9d81b60c := by decide +kernel
private theorem b5843_1234_3214 : blockEstimate 5843 1234 3214 660 = 0x468c0b000cc := by decide +kernel
private theorem b5843_1234_3874 : blockEstimate 5843 1234 3874 660 = 0x4fc8db5780c := by decide +kernel
private theorem b5843_1234_4534 : blockEstimate 5843 1234 4534 660 = 0x4eb04921bcc := by decide +kernel
private theorem b5843_1234_5194 : blockEstimate 5843 1234 5194 660 = 0x434254c61d6 := by decide +kernel
private theorem b5843_1234_5854 : blockEstimate 5843 1234 5854 660 = 0x2f009d98898 := by decide +kernel
private theorem b5843_1234_6514 : blockEstimate 5843 1234 6514 660 = 0x1987ab8f3d5 := by decide +kernel
private theorem b5843_1234_7174 : blockEstimate 5843 1234 7174 660 = 0x8c1c8886ed := by decide +kernel
private theorem b5843_1234_7834 : blockEstimate 5843 1234 7834 477 = 0xbf253282c := by decide +kernel
private theorem s5843_1234_1234_1320 : blockEstimate 5843 1234 1234 1320 = 0x1b21290554f :=
  append (B := 5843) (J := 1234) (start := 1234) (a := 660) (x := 0x3bf19f9b33)
    b5843_1234_1234 1894 660 0x17620f0ba1c 1320 0x1b21290554f rfl rfl rfl b5843_1234_1894
private theorem s5843_1234_2554_1320 : blockEstimate 5843 1234 2554 1320 = 0x7985e31b6d8 :=
  append (B := 5843) (J := 1234) (start := 2554) (a := 660) (x := 0x32f9d81b60c)
    b5843_1234_2554 3214 660 0x468c0b000cc 1320 0x7985e31b6d8 rfl rfl rfl b5843_1234_3214
private theorem s5843_1234_3874_1320 : blockEstimate 5843 1234 3874 1320 = 0x9e7924793d8 :=
  append (B := 5843) (J := 1234) (start := 3874) (a := 660) (x := 0x4fc8db5780c)
    b5843_1234_3874 4534 660 0x4eb04921bcc 1320 0x9e7924793d8 rfl rfl rfl b5843_1234_4534
private theorem s5843_1234_5194_1320 : blockEstimate 5843 1234 5194 1320 = 0x7242f25ea6e :=
  append (B := 5843) (J := 1234) (start := 5194) (a := 660) (x := 0x434254c61d6)
    b5843_1234_5194 5854 660 0x2f009d98898 1320 0x7242f25ea6e rfl rfl rfl b5843_1234_5854
private theorem s5843_1234_6514_1320 : blockEstimate 5843 1234 6514 1320 = 0x22497417ac2 :=
  append (B := 5843) (J := 1234) (start := 6514) (a := 660) (x := 0x1987ab8f3d5)
    b5843_1234_6514 7174 660 0x8c1c8886ed 1320 0x22497417ac2 rfl rfl rfl b5843_1234_7174
private theorem s5843_1234_1234_2640 : blockEstimate 5843 1234 1234 2640 = 0x94a70c20c27 :=
  append (B := 5843) (J := 1234) (start := 1234) (a := 1320) (x := 0x1b21290554f)
    s5843_1234_1234_1320 2554 1320 0x7985e31b6d8 2640 0x94a70c20c27 rfl rfl rfl s5843_1234_2554_1320
private theorem s5843_1234_3874_2640 : blockEstimate 5843 1234 3874 2640 = 0x110bc16d7e46 :=
  append (B := 5843) (J := 1234) (start := 3874) (a := 1320) (x := 0x9e7924793d8)
    s5843_1234_3874_1320 5194 1320 0x7242f25ea6e 2640 0x110bc16d7e46 rfl rfl rfl s5843_1234_5194_1320
private theorem s5843_1234_6514_1797 : blockEstimate 5843 1234 6514 1797 = 0x2308994a2ee :=
  append (B := 5843) (J := 1234) (start := 6514) (a := 1320) (x := 0x22497417ac2)
    s5843_1234_6514_1320 7834 477 0xbf253282c 1797 0x2308994a2ee rfl rfl rfl b5843_1234_7834
private theorem s5843_1234_1234_5280 : blockEstimate 5843 1234 1234 5280 = 0x1a56322f8a6d :=
  append (B := 5843) (J := 1234) (start := 1234) (a := 2640) (x := 0x94a70c20c27)
    s5843_1234_1234_2640 3874 2640 0x110bc16d7e46 5280 0x1a56322f8a6d rfl rfl rfl s5843_1234_3874_2640
private theorem s5843_1234_1234_7077 : blockEstimate 5843 1234 1234 7077 = 0x1c86bbc42d5b :=
  append (B := 5843) (J := 1234) (start := 1234) (a := 5280) (x := 0x1a56322f8a6d)
    s5843_1234_1234_5280 6514 1797 0x2308994a2ee 7077 0x1c86bbc42d5b rfl rfl rfl s5843_1234_6514_1797
theorem moment5843_1234 : momentEstimate 5843 1234 = 0x1c86bbc42d5b := by
  change blockEstimate 5843 1234 1234 7077 = 0x1c86bbc42d5b
  exact s5843_1234_1234_7077

private theorem b2041_430_430 : blockEstimate 2041 430 430 660 = 0x10a7b782fe := by decide +kernel
private theorem b2041_430_1090 : blockEstimate 2041 430 1090 660 = 0x339a65babc := by decide +kernel
private theorem b2041_430_1750 : blockEstimate 2041 430 1750 660 = 0x245b4c1c01 := by decide +kernel
private theorem b2041_430_2410 : blockEstimate 2041 430 2410 491 = 0x432087e73 := by decide +kernel
private theorem s2041_430_430_1320 : blockEstimate 2041 430 430 1320 = 0x44421d3dba :=
  append (B := 2041) (J := 430) (start := 430) (a := 660) (x := 0x10a7b782fe)
    b2041_430_430 1090 660 0x339a65babc 1320 0x44421d3dba rfl rfl rfl b2041_430_1090
private theorem s2041_430_1750_1151 : blockEstimate 2041 430 1750 1151 = 0x288d549a74 :=
  append (B := 2041) (J := 430) (start := 1750) (a := 660) (x := 0x245b4c1c01)
    b2041_430_1750 2410 491 0x432087e73 1151 0x288d549a74 rfl rfl rfl b2041_430_2410
private theorem s2041_430_430_2471 : blockEstimate 2041 430 430 2471 = 0x6ccf71d82e :=
  append (B := 2041) (J := 430) (start := 430) (a := 1320) (x := 0x44421d3dba)
    s2041_430_430_1320 1750 1151 0x288d549a74 2471 0x6ccf71d82e rfl rfl rfl s2041_430_1750_1151
theorem moment2041_430 : momentEstimate 2041 430 = 0x6ccf71d82e := by
  change blockEstimate 2041 430 430 2471 = 0x6ccf71d82e
  exact s2041_430_430_2471

private theorem b1150_242_242 : blockEstimate 1150 242 242 660 = 0x5a9a9f41c := by decide +kernel
private theorem b1150_242_902 : blockEstimate 1150 242 902 660 = 0x55238c7df := by decide +kernel
private theorem b1150_242_1562 : blockEstimate 1150 242 1562 72 = 0x233bd58 := by decide +kernel
private theorem s1150_242_242_1320 : blockEstimate 1150 242 242 1320 = 0xafbe2bbfb :=
  append (B := 1150) (J := 242) (start := 242) (a := 660) (x := 0x5a9a9f41c)
    b1150_242_242 902 660 0x55238c7df 1320 0xafbe2bbfb rfl rfl rfl b1150_242_902
private theorem s1150_242_242_1392 : blockEstimate 1150 242 242 1392 = 0xafe167953 :=
  append (B := 1150) (J := 242) (start := 242) (a := 1320) (x := 0xafbe2bbfb)
    s1150_242_242_1320 1562 72 0x233bd58 1392 0xafe167953 rfl rfl rfl b1150_242_1562
theorem moment1150_242 : momentEstimate 1150 242 = 0xafe167953 := by
  change blockEstimate 1150 242 242 1392 = 0xafe167953
  exact s1150_242_242_1392

private theorem b731_154_154 : blockEstimate 731 154 154 660 = 0x1a9e540b8 := by decide +kernel
private theorem b731_154_814 : blockEstimate 731 154 814 225 = 0x23e29980 := by decide +kernel
private theorem s731_154_154_885 : blockEstimate 731 154 154 885 = 0x1cdc7da38 :=
  append (B := 731) (J := 154) (start := 154) (a := 660) (x := 0x1a9e540b8)
    b731_154_154 814 225 0x23e29980 885 0x1cdc7da38 rfl rfl rfl b731_154_814
theorem moment731_154 : momentEstimate 731 154 = 0x1cdc7da38 := by
  change blockEstimate 731 154 154 885 = 0x1cdc7da38
  exact s731_154_154_885

private theorem b580_122_122 : blockEstimate 580 122 122 660 = 0xb71dc787 := by decide +kernel
private theorem b580_122_782 : blockEstimate 580 122 782 42 = 0x3aa8e4 := by decide +kernel
private theorem s580_122_122_702 : blockEstimate 580 122 122 702 = 0xb758706b :=
  append (B := 580) (J := 122) (start := 122) (a := 660) (x := 0xb71dc787)
    b580_122_122 782 42 0x3aa8e4 702 0xb758706b rfl rfl rfl b580_122_782
theorem moment580_122 : momentEstimate 580 122 = 0xb758706b := by
  change blockEstimate 580 122 122 702 = 0xb758706b
  exact s580_122_122_702

private theorem b318_70_70 : blockEstimate 318 70 70 388 = 0x115d6f33 := by decide +kernel
theorem moment318_70 : momentEstimate 318 70 = 0x115d6f33 := by
  change blockEstimate 318 70 70 388 = 0x115d6f33
  exact b318_70_70

private theorem b154_33_33 : blockEstimate 154 33 33 187 = 0xf64733 := by decide +kernel
theorem moment154_33 : momentEstimate 154 33 = 0xf64733 := by
  change blockEstimate 154 33 33 187 = 0xf64733
  exact b154_33_33

end HighCore82258BankProof
