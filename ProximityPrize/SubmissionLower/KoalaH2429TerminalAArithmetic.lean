import ProximityPrize.SubmissionLower.KoalaH2429Banks
import ProximityPrize.SubmissionLower.KoalaH2429TerminalOnce

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2429TerminalA

open KoalaH2429Banks (terminal)
open KoalaRectArithmetic (RectArgs)
open KoalaRect (rectGain rectDebit)
open Pr657Rect2435Arithmetic (blockSurplus blockSurplus_eq)
open Pr657RectStockTerminalArithmetic (Parts)

def rectWitness : ℕ → RectArgs
  | 1 => ⟨![397815,40629], ![238,239]⟩
  | 2 => ⟨![397681,40763], ![236,237]⟩
  | 3 => ⟨![397320,41124], ![234,235]⟩
  | 4 => ⟨![397149,41295], ![231,232]⟩
  | 5 => ⟨![396815,41629], ![229,230]⟩
  | 6 => ⟨![396677,41767], ![226,227]⟩
  | 7 => ⟨![396145,42299], ![224,225]⟩
  | 8 => ⟨![395821,42623], ![221,222]⟩
  | 9 => ⟨![395302,43142], ![218,219]⟩
  | 10 => ⟨![395029,43415], ![215,216]⟩
  | 11 => ⟨![394354,44090], ![212,213]⟩
  | 12 => ⟨![393715,44729], ![209,210]⟩
  | 13 => ⟨![393125,45319], ![205,206]⟩
  | 14 => ⟨![392187,46257], ![201,202]⟩
  | 15 => ⟨![391123,47321], ![197,198]⟩
  | 16 => ⟨![389169,49275], ![193,194]⟩
  | 17 => ⟨![386557,51887], ![188,188]⟩
  | 18 => ⟨![229035,209409], ![177,178]⟩
  | 19 => ⟨![220081,218363], ![133,134]⟩
  | 20 => ⟨![219650,218794], ![85,86]⟩
  | 21 => ⟨![219498,218946], ![34,35]⟩
  | 22 => ⟨![219421,219023], ![0,1]⟩
  | 23 => ⟨![219222,219222], ![0,0]⟩
  | _ => ⟨![0,0], ![0,0]⟩

def paidCap (E : ℕ) : ℕ := (rectWitness E).order 0 + (rectWitness E).order 1 - 1

theorem paidCap16 : paidCap 16 = 386 := by decide
theorem paidCap17 : paidCap 17 = 375 := by decide

theorem paidCap_le {E : ℕ} (he : 0 < E) (hE : E < 23) : paidCap E ≤ 476 := by
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
  cert! 1581,8,0xf53ab48d4277c224b9aa3580; (more! 0xe469e03490f989242d05c080; (last! 0x10d0d704a2cff3d2548b0c00))

private theorem r2 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 2 (rectWitness 2) :=
  cert! 1583,9,0xf5f4560f76bba83bb1aa3580; (more! 0xe532a21c02e71e481625bec0; (last! 0x10c1cafaab3e31ccb48fca80))

private theorem r3 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 3 (rectWitness 3) :=
  cert! 1586,9,0xf7e7bcefad06014528aa3580; (more! 0xe7130796295703dbd1f69ae0; (last! 0x10d4e55d953b070e12f437e0))

private theorem r4 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 4 (rectWitness 4) :=
  cert! 1589,9,0xf8d3f1a02dfd4b5169aa3580; (more! 0xe800b8c3e944e1c6bc529600; (last! 0x10d340faeed3195680f40c00))

private theorem r5 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 5 (rectWitness 5) :=
  cert! 1592,9,0xfaa0a687c8bd2054e9aa3580; (more! 0xe9c3c65c7e697b1ed0f00280; (last! 0x10dd0b2e1b936e152a1ca380))

private theorem r6 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 6 (rectWitness 6) :=
  cert! 1595,9,0xfb5ebfe8bee04b4599aa3580; (more! 0xea8cf98d21241b8bb24d5880; (last! 0x10d1d31be25591aa3a716900))

private theorem r7 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 7 (rectWitness 7) :=
  cert! 1599,9,0xfe3a3670c3619f67b1aa3580; (more! 0xed4712a6f44fa201250df340; (last! 0x10f3603c3a3acc8a11748d80))

private theorem r8 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 8 (rectWitness 8) :=
  cert! 1603,9,0xfff69d3470bae90f49aa3580; (more! 0xeef930c16c83a9baaebb87c0; (last! 0x10fd97990b1431123df94500))

private theorem r9 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 9 (rectWitness 9) :=
  cert! 1608,9,0x102bcc825dbdca2d0d4aa3580; (more! 0xf19d1af76fd04752b31cdb60; (last! 0x111fce8e72ad2a0ca74a0840))

private theorem r10 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 10 (rectWitness 10) :=
  cert! 1612,10,0x104317fd7eb8966b4f9aa3580; (more! 0xf3161d6db72187e1f4a0de00; (last! 0x111b8328e42294d8a8e91200))

private theorem r11 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 11 (rectWitness 11) :=
  cert! 1618,10,0x107c89232b609235d24aa3580; (more! 0xf67eef4de61481268a5d5ae0; (last! 0x1149cdd8192cd0b884b1dce0))

private theorem r12 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 12 (rectWitness 12) :=
  cert! 1624,10,0x10b2b5e30e437c408e1aa3580; (more! 0xf9be5bc422e6b08d2b18d080; (last! 0x116d44d7a565c70283bedc80))

private theorem r13 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 13 (rectWitness 13) :=
  cert! 1631,10,0x10e48e22bae852cf859aa3580; (more! 0xfcbb6f1c4b1bfcdc20426040; (last! 0x118d8f0b840e61e564355300))

private theorem r14 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 14 (rectWitness 14) :=
  cert! 1640,11,0x113373cb84b12df6931aa3580; (more! 0x101652da67333261fc41a1f80; (last! 0x11d217519adef74371a7dd80))

private theorem r15 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 15 (rectWitness 15) :=
  cert! 1650,11,0x118c6e56fcd03d1bca1aa3580; (more! 0x106ab077a2ff6a0183eb7c180; (last! 0x121bec24a3b934f5bd259a80))

private theorem r16 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 16 (rectWitness 16) :=
  cert! 1665,12,0x122e6848febd59e4a31aa3580; (more! 0x11026399ce54af958bd8f4100; (last! 0x12c0850bb32d6ce5fb9e0740))

private theorem r17 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 17 (rectWitness 17) :=
  cert! 1687,12,0x1304095367a6cc2ad29aa3580; (more! 0x11c998df9e365a5320eaf2e00; (last! 0x13a7073ccbafd60a44996d00))

private theorem r18 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 18 (rectWitness 18) :=
  cert! 1782,16,0x2d72a6ca9dc6ee1e491aa3580; (more! 0x2a19f91aa8942cb20a9641c80; (last! 0x358ae5e2b03c9f3a1925f180))

private theorem r19 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 19 (rectWitness 19) :=
  cert! 1763,15,0x2d89d2bbb1a30a64b31aa3580; (more! 0x2a3adf6740ae0813529731980; (last! 0x34ef5d4b91f8d11b12531a00))

private theorem r20 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 20 (rectWitness 20) :=
  cert! 1745,15,0x2d89f52ad843ae077a4aa3580; (more! 0x2a4578d67c9129a83046fc660; (last! 0x3447d307e8234ec47ef1b3c0))

private theorem r21 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 21 (rectWitness 21) :=
  cert! 1729,14,0x2d89fbcf65d750b0da4aa3580; (more! 0x2a4f51acec8c72ce616a80720; (last! 0x33aaaaf5f6c7caf765051d00))

private theorem r22 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 22 (rectWitness 22) :=
  cert! 1715,14,0x2d89fe14a43b46c9be9aa3580; (more! 0x2a5f15d43716f2ba69dcb8b00; (last! 0x32b3ed476950688360df7340))

private theorem r23 :
    0 < blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2429 23 (rectWitness 23) :=
  cert! 1702,13,0x2d8a0089f952fa303d4aa3580; (more! 0x2a784c189383b31f612347700; (last! 0x312e6c7b6023d8da450ef4c0))

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

end KoalaH2429TerminalA
