import ProximityPrize.SubmissionLower.KoalaH2429TerminalBankB
import ProximityPrize.SubmissionLower.KoalaH2429TerminalOnce

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2429TerminalB

open KoalaRectArithmetic (RectArgs)
open KoalaRect (rectGain rectDebit)
open Pr657Rect2435Arithmetic (blockSurplus blockSurplus_eq)
open Pr657RectStockTerminalArithmetic (Parts)

def rectWitness : ℕ → RectArgs
  | 1 => ⟨![409989,42363], ![237,238]⟩
  | 2 => ⟨![409873,42479], ![235,236]⟩
  | 3 => ⟨![409531,42821], ![233,234]⟩
  | 4 => ⟨![409387,42965], ![230,231]⟩
  | 5 => ⟨![408843,43509], ![228,229]⟩
  | 6 => ⟨![408735,43617], ![225,226]⟩
  | 7 => ⟨![408225,44127], ![223,224]⟩
  | 8 => ⟨![407932,44420], ![220,221]⟩
  | 9 => ⟨![407445,44907], ![217,218]⟩
  | 10 => ⟨![406988,45364], ![214,215]⟩
  | 11 => ⟨![406349,46003], ![211,212]⟩
  | 12 => ⟨![405746,46606], ![208,209]⟩
  | 13 => ⟨![404998,47354], ![204,205]⟩
  | 14 => ⟨![404113,48239], ![200,201]⟩
  | 15 => ⟨![402906,49446], ![196,197]⟩
  | 16 => ⟨![473509,50805], ![190,191]⟩
  | 17 => ⟨![470665,53649], ![185,185]⟩
  | 18 => ⟨![226176,226176], ![175,175]⟩
  | 19 => ⟨![227037,225315], ![131,132]⟩
  | 20 => ⟨![226176,226176], ![84,84]⟩
  | 21 => ⟨![226459,225893], ![33,34]⟩
  | 22 => ⟨![226381,225971], ![0,1]⟩
  | 23 => ⟨![226176,226176], ![0,0]⟩
  | _ => ⟨![0,0], ![0,0]⟩

def paidCap (E : ℕ) : ℕ := (rectWitness E).order 0 + (rectWitness E).order 1 - 1

theorem paidCap16 : paidCap 16 = 380 := by decide
theorem paidCap17 : paidCap 17 = 369 := by decide

theorem paidCap_le {E : ℕ} (he : 0 < E) (hE : E < 23) : paidCap E ≤ 474 := by
  interval_cases E <;> decide

theorem witness_guards {E : ℕ} (he : 0 < E) (hE : E ≤ 23) :
    (rectWitness E).U 1 ≤ (rectWitness E).U 0 ∧
    (rectWitness E).U 0 + (rectWitness E).U 1 ≤ terminal.shape.U := by
  interval_cases E <;> decide

theorem witness_order {E : ℕ} (he : 0 < E) (hE : E < 23) :
    (rectWitness E).order 0 ≤ (rectWitness E).order 1 ∧
    (rectWitness E).order 1 ≤ (rectWitness E).order 0 + 1 ∧
    (rectWitness E).order 0 + (rectWitness E).order 1 = paidCap E + 1 := by
  interval_cases E <;> decide

theorem reject_order : (rectWitness 23).order = ![0,0] := rfl

open KoalaH2429TerminalOnce (positive)

local notation "last!" x =>
  Parts.final (gain := x) (next := 0) (P0_10_5.Row.eq_of_check (by decide +kernel))

local notation "more!" x ";" rest =>
  Parts.more (gain := x) (next := 0) (P0_10_5.Row.eq_of_check (by decide +kernel)) rest

local notation "cert!" nn "," mm "," cc ";" parts =>
  positive (n := nn) (last := mm) (cost := cc) parts
    (by decide +kernel) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide)

private theorem r1 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 1 (rectWitness 1) :=
  cert! 1651,9,0x12bac0e11b9d043f00529e940; (more! 0x114717a7cdd915be9a9a7fb80; (last! 0x173a96390a6fdf86f3a4e580))

private theorem r2 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 2 (rectWitness 2) :=
  cert! 1653,10,0x12c6825e8506e7aa10129e940; (more! 0x1154303a89a73ddccce0d7500; (last! 0x17253d9945a8a76edaf18500))

private theorem r3 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 3 (rectWitness 3) :=
  cert! 1656,10,0x12e9201e3c3fe3d1b4529e940; (more! 0x117571517eeade25d77861100; (last! 0x173b2673c459f8cf4bc1b600))

private theorem r4 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 4 (rectWitness 4) :=
  cert! 1659,10,0x12f7ae70bc169c267f529e940; (more! 0x11845cf947664c9d7a8b73a80; (last! 0x17351fb5ac848008d579a080))

private theorem r5 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 5 (rectWitness 5) :=
  cert! 1663,10,0x132e913c903ccb0195529e940; (more! 0x11b7d4e73c95565ca27a01500; (last! 0x176bf8053a137480e73d0900))

private theorem r6 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 6 (rectWitness 6) :=
  cert! 1666,10,0x133971c30fab7ae023129e940; (more! 0x11c3e184f79d29119b5329a00; (last! 0x1759113a08c647b2f321cf00))

private theorem r7 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 7 (rectWitness 7) :=
  cert! 1670,10,0x136cb8a8ee19763c1f129e940; (more! 0x11f4a7ed7bb19c4c38e456800; (last! 0x1781533285c6e1467ea28800))

private theorem r8 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 8 (rectWitness 8) :=
  cert! 1674,10,0x138a1d950cf5a33eee9a9e940; (more! 0x12117c74ac66cff73f648ce00; (last! 0x178a43e350211c7e81a95fa0))

private theorem r9 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 9 (rectWitness 9) :=
  cert! 1679,11,0x13bade0f8735ec8553529e940; (more! 0x123fbf0cfab6bb372520be580; (last! 0x17b215bbe55a74dc44c9e6c0))

private theorem r10 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 10 (rectWitness 10) :=
  cert! 1684,11,0x13e87f44355eee103a9a9e940; (more! 0x126b8e653160712f388e8f060; (last! 0x17cf3263ef77c9c757c6f120))

private theorem r11 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 11 (rectWitness 11) :=
  cert! 1690,11,0x14281b10f16c3d6d2fd29e940; (more! 0x12a7bc3369ed1e57dcfe1ca00; (last! 0x18061e79090bd255c6dec200))

private theorem r12 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 12 (rectWitness 12) :=
  cert! 1696,11,0x1463ec996d83e29420fa9e940; (more! 0x12e0f2af19592753dcbfb3960; (last! 0x182febf76636d45ce9655ee0))

private theorem r13 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 13 (rectWitness 13) :=
  cert! 1704,11,0x14add927245a948b25fa9e940; (more! 0x13267ff6e9c35e62b0f522460; (last! 0x1875b0f78e5493b14397de60))

private theorem r14 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 14 (rectWitness 14) :=
  cert! 1713,12,0x1504e9cff1664911f8129e940; (more! 0x13786e6eb9645e6f14d269880; (last! 0x18c7bbd7d482b6d2517254c0))

private theorem r15 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 15 (rectWitness 15) :=
  cert! 1724,12,0x157af5c402b49f1bd9fa9e940; (more! 0x13e6f56970822a1456bde18e0; (last! 0x19401329bedf5cb887171da0))

private theorem r16 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 16 (rectWitness 16) :=
  cert! 1739,13,0x19efee24386a764c7e2dd8180; (more! 0x18075c54911e0f4caa9340100; (last! 0x1e8971321db1ba2b8a409680))

private theorem r17 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 17 (rectWitness 17) :=
  cert! 1763,14,0x1b3934c1b1f5ac680fadd8180; (more! 0x19371401b0b97f1c3e0a96c40; (last! 0x20220c009029a879f0dbfea0))

private theorem r18 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 18 (rectWitness 18) :=
  cert! 1861,1,0x371fcc8bb64731df4f1a9e940; (more! 0x32919126e4fdfc083cd603680; (more! 0x48e3c049ae445429a54852a0; (last! 0x0)))

private theorem r19 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 19 (rectWitness 19) :=
  cert! 1840,1,0x371f98369323e40642d29e940; (more! 0x329f7b77a7685e26855abbb00; (more! 0x4801fd06a5b4f7dc71b7c300; (last! 0x0)))

private theorem r20 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 20 (rectWitness 20) :=
  cert! 1822,16,0x371fcc8bb64731df4f1a9e940; (more! 0x32ac5ffdc7332102a17887040; (last! 0x4736d7ffbf5b749b30419140))

private theorem r21 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 21 (rectWitness 21) :=
  cert! 1805,15,0x371fc6e4586776371a529e940; (more! 0x32b8422a41e09185f574a8200; (last! 0x46784ff29488fe1af3f05480))

private theorem r22 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 22 (rectWitness 22) :=
  cert! 1790,15,0x371fc9943cb411985fd29e940; (more! 0x32cbba88b10c19bbc8c63b700; (last! 0x4547ad92032f274cefd52d40))

private theorem r23 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 23 (rectWitness 23) :=
  cert! 1776,14,0x371fcc8bb64731df4f1a9e940; (more! 0x32ea7f3aa433122f393e700a0; (last! 0x436c31a1a56a78aefc212da0))

theorem rect_bounds {E : ℕ} (he : 0 < E) (hE : E ≤ 23) :
    rectDebit 2429 terminal.nodeRows terminal.poleMoment (rectWitness E).U <
      rectGain 179876 2429 terminal.shape E (rectWitness E).U (rectWitness E).order := by
  have h : 0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 E (rectWitness E) := by
    interval_cases E
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    · exact r7
    · exact r8
    · exact r9
    · exact r10
    · exact r11
    · exact r12
    · exact r13
    · exact r14
    · exact r15
    · exact r16
    · exact r17
    · exact r18
    · exact r19
    · exact r20
    · exact r21
    · exact r22
    · exact r23
  rw [blockSurplus_eq terminal 2429 E (rectWitness E) (by decide) (by decide) he] at h
  unfold Pr657Rect2435Arithmetic.surplus Pr657Rect2435Width.stockAgreement at h
  omega

end KoalaH2429TerminalB
