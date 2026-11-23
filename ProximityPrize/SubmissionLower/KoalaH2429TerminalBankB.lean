import ProximityPrize.SubmissionLower.HighBankCore

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaH2429TerminalB

open P1_7 (Bank)
open P1_7_1_3 (momentEstimate blockEstimate)
open P1_7_1_3_6 (append)

def terminal : Bank := ⟨⟨5010,6967,1473,524314⟩,0xd28dc69940000,0x39b28d52e38d⟩

private theorem b1473 : blockEstimate 6967 1473 1473 660 = 0x488a645ac3 := by decide +kernel
private theorem b2133 : blockEstimate 6967 1473 2133 660 = 0x1ce30945c37 := by decide +kernel
private theorem b2793 : blockEstimate 6967 1473 2793 660 = 0x4456ce62518 := by decide +kernel
private theorem b3453 : blockEstimate 6967 1473 3453 660 = 0x67447627ab6 := by decide +kernel
private theorem b4113 : blockEstimate 6967 1473 4113 660 = 0x7de94394e26 := by decide +kernel
private theorem b4773 : blockEstimate 6967 1473 4773 660 = 0x8838bd96496 := by decide +kernel
private theorem b5433 : blockEstimate 6967 1473 5433 660 = 0x8632e42be06 := by decide +kernel
private theorem b6093 : blockEstimate 6967 1473 6093 660 = 0x77d7b755a76 := by decide +kernel
private theorem b6753 : blockEstimate 6967 1473 6753 660 = 0x5da3eab446d := by decide +kernel
private theorem b7413 : blockEstimate 6967 1473 7413 660 = 0x3e30e3acf64 := by decide +kernel
private theorem b8073 : blockEstimate 6967 1473 8073 660 = 0x214c2425596 := by decide +kernel
private theorem b8733 : blockEstimate 6967 1473 8733 660 = 0xbac45b3e78 := by decide +kernel
private theorem b9393 : blockEstimate 6967 1473 9393 520 = 0x1280c319ae := by decide +kernel

private theorem s1473_1320 : blockEstimate 6967 1473 1473 1320 = 0x216baf8b6fa :=
  append (B := 6967) (J := 1473) (start := 1473) (a := 660) (x := 0x488a645ac3)
    b1473 2133 660 0x1ce30945c37 1320 0x216baf8b6fa rfl rfl rfl b2133
private theorem s2793_1320 : blockEstimate 6967 1473 2793 1320 = 0xab9b4489fce :=
  append (B := 6967) (J := 1473) (start := 2793) (a := 660) (x := 0x4456ce62518)
    b2793 3453 660 0x67447627ab6 1320 0xab9b4489fce rfl rfl rfl b3453
private theorem s4113_1320 : blockEstimate 6967 1473 4113 1320 = 0x10622012b2bc :=
  append (B := 6967) (J := 1473) (start := 4113) (a := 660) (x := 0x7de94394e26)
    b4113 4773 660 0x8838bd96496 1320 0x10622012b2bc rfl rfl rfl b4773
private theorem s5433_1320 : blockEstimate 6967 1473 5433 1320 = 0xfe0a9b8187c :=
  append (B := 6967) (J := 1473) (start := 5433) (a := 660) (x := 0x8632e42be06)
    b5433 6093 660 0x77d7b755a76 1320 0xfe0a9b8187c rfl rfl rfl b6093
private theorem s6753_1320 : blockEstimate 6967 1473 6753 1320 = 0x9bd4ce613d1 :=
  append (B := 6967) (J := 1473) (start := 6753) (a := 660) (x := 0x5da3eab446d)
    b6753 7413 660 0x3e30e3acf64 1320 0x9bd4ce613d1 rfl rfl rfl b7413
private theorem s8073_1320 : blockEstimate 6967 1473 8073 1320 = 0x2cf869d940e :=
  append (B := 6967) (J := 1473) (start := 8073) (a := 660) (x := 0x214c2425596)
    b8073 8733 660 0xbac45b3e78 1320 0x2cf869d940e rfl rfl rfl b8733
private theorem s1473_2640 : blockEstimate 6967 1473 1473 2640 = 0xcd06f4156c8 :=
  append (B := 6967) (J := 1473) (start := 1473) (a := 1320) (x := 0x216baf8b6fa)
    s1473_1320 2793 1320 0xab9b4489fce 2640 0xcd06f4156c8 rfl rfl rfl s2793_1320
private theorem s4113_2640 : blockEstimate 6967 1473 4113 2640 = 0x2042c9cacb38 :=
  append (B := 6967) (J := 1473) (start := 4113) (a := 1320) (x := 0x10622012b2bc)
    s4113_1320 5433 1320 0xfe0a9b8187c 2640 0x2042c9cacb38 rfl rfl rfl s5433_1320
private theorem s6753_2640 : blockEstimate 6967 1473 6753 2640 = 0xc8cd383a7df :=
  append (B := 6967) (J := 1473) (start := 6753) (a := 1320) (x := 0x9bd4ce613d1)
    s6753_1320 8073 1320 0x2cf869d940e 2640 0xc8cd383a7df rfl rfl rfl s8073_1320
private theorem s1473_5280 : blockEstimate 6967 1473 1473 5280 = 0x2d13390c2200 :=
  append (B := 6967) (J := 1473) (start := 1473) (a := 2640) (x := 0xcd06f4156c8)
    s1473_2640 4113 2640 0x2042c9cacb38 5280 0x2d13390c2200 rfl rfl rfl s4113_2640
private theorem s6753_3160 : blockEstimate 6967 1473 6753 3160 = 0xc9f5446c18d :=
  append (B := 6967) (J := 1473) (start := 6753) (a := 2640) (x := 0xc8cd383a7df)
    s6753_2640 9393 520 0x1280c319ae 3160 0xc9f5446c18d rfl rfl rfl b9393
private theorem s1473_8440 : blockEstimate 6967 1473 1473 8440 = 0x39b28d52e38d :=
  append (B := 6967) (J := 1473) (start := 1473) (a := 5280) (x := 0x2d13390c2200)
    s1473_5280 6753 3160 0xc9f5446c18d 8440 0x39b28d52e38d rfl rfl rfl s6753_3160

theorem moment : momentEstimate 6967 1473 = 0x39b28d52e38d := by
  change blockEstimate 6967 1473 1473 8440 = 0x39b28d52e38d
  exact s1473_8440

theorem terminal_ok : P3_7_1.BankOK terminal :=
  P3_7_1.checked terminal (m := 5010) (B := 6967) (J := 1473) (N := 0xd28dc69940000) (M := 0x39b28d52e38d)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) moment

end KoalaH2429TerminalB

#print axioms KoalaH2429TerminalB.terminal_ok
