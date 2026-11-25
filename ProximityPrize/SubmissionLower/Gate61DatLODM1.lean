import ProximityPrize.SubmissionLower.Gate61DatLODDefs
import ProximityPrize.SubmissionLower.Gate63Split
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatLOD
open Gate61Cell
open Gate61CertCF (cvOf)
def P63_10 : Pr := mkPr G 64 10 (cvOf 1 ws 64 10).1 (cvOf 1 ws 64 10).2 175230087 4012 1650 550
theorem K63_10_2 : cell P63_10 79 0 0 0 1316 1230 410 = true := by decide +kernel  -- 9633 cells
theorem K63_10_4 : cell P63_10 78 1317 0 0 1974 1230 410 = true := by decide +kernel  -- 857 cells
theorem K63_10_7 : cell P63_10 76 1975 0 0 2303 615 410 = true := by decide +kernel  -- 4131 cells
theorem K63_10_12 : cell P63_10 72 2304 0 0 2468 153 205 = true := by decide +kernel  -- 6031 cells
theorem K63_10_18 : cell P63_10 67 2304 154 0 2345 230 51 = true := by decide +kernel  -- 1423 cells
theorem K63_10_20 : cell P63_10 66 2346 154 0 2386 192 51 = true := by decide +kernel  -- 9423 cells
theorem K63_10_21 : cell P63_10 66 2346 193 0 2386 230 51 = true := by decide +kernel  -- 13779 cells
theorem K63_10_19 : cell P63_10 67 2346 154 0 2386 230 51 = true :=
  cell_node1 P63_10 66 2346 154 0 2386 230 51 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_20 K63_10_21
theorem K63_10_17 : cell P63_10 68 2304 154 0 2386 230 51 = true :=
  cell_node0 P63_10 67 2304 154 0 2386 230 51 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_18 K63_10_19
theorem K63_10_22 : cell P63_10 68 2304 154 52 2386 230 102 = true := by decide +kernel  -- 8531 cells
theorem K63_10_16 : cell P63_10 69 2304 154 0 2386 230 102 = true :=
  cell_node2 P63_10 68 2304 154 0 2386 230 102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_17 K63_10_22
theorem K63_10_24 : cell P63_10 68 2304 231 0 2386 307 51 = true := by decide +kernel  -- 14847 cells
theorem K63_10_25 : cell P63_10 68 2304 231 52 2386 307 102 = true := by decide +kernel  -- 11781 cells
theorem K63_10_23 : cell P63_10 69 2304 231 0 2386 307 102 = true :=
  cell_node2 P63_10 68 2304 231 0 2386 307 102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_24 K63_10_25
theorem K63_10_15 : cell P63_10 70 2304 154 0 2386 307 102 = true :=
  cell_node1 P63_10 69 2304 154 0 2386 307 102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_16 K63_10_23
theorem K63_10_26 : cell P63_10 70 2387 154 0 2468 307 102 = true := by decide +kernel  -- 1 cells
theorem K63_10_14 : cell P63_10 71 2304 154 0 2468 307 102 = true :=
  cell_node0 P63_10 70 2304 154 0 2468 307 102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_15 K63_10_26
theorem K63_10_27 : cell P63_10 71 2304 154 103 2468 307 205 = true := by decide +kernel  -- 1 cells
theorem K63_10_13 : cell P63_10 72 2304 154 0 2468 307 205 = true :=
  cell_node2 P63_10 71 2304 154 0 2468 307 205 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_14 K63_10_27
theorem K63_10_11 : cell P63_10 73 2304 0 0 2468 307 205 = true :=
  cell_node1 P63_10 72 2304 0 0 2468 307 205 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_12 K63_10_13
theorem K63_10_28 : cell P63_10 73 2469 0 0 2632 307 205 = true := by decide +kernel  -- 1 cells
theorem K63_10_10 : cell P63_10 74 2304 0 0 2632 307 205 = true :=
  cell_node0 P63_10 73 2304 0 0 2632 307 205 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_11 K63_10_28
theorem K63_10_29 : cell P63_10 74 2304 0 206 2632 307 410 = true := by decide +kernel  -- 1 cells
theorem K63_10_9 : cell P63_10 75 2304 0 0 2632 307 410 = true :=
  cell_node2 P63_10 74 2304 0 0 2632 307 410 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_10 K63_10_29
theorem K63_10_30 : cell P63_10 75 2304 308 0 2632 615 410 = true := by decide +kernel  -- 9105 cells
theorem K63_10_8 : cell P63_10 76 2304 0 0 2632 615 410 = true :=
  cell_node1 P63_10 75 2304 0 0 2632 615 410 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_9 K63_10_30
theorem K63_10_6 : cell P63_10 77 1975 0 0 2632 615 410 = true :=
  cell_node0 P63_10 76 1975 0 0 2632 615 410 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_7 K63_10_8
theorem K63_10_31 : cell P63_10 77 1975 616 0 2632 1230 410 = true := by decide +kernel  -- 417 cells
theorem K63_10_5 : cell P63_10 78 1975 0 0 2632 1230 410 = true :=
  cell_node1 P63_10 77 1975 0 0 2632 1230 410 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_6 K63_10_31
theorem K63_10_3 : cell P63_10 79 1317 0 0 2632 1230 410 = true :=
  cell_node0 P63_10 78 1317 0 0 2632 1230 410 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_4 K63_10_5
theorem K63_10_1 : cell P63_10 80 0 0 0 2632 1230 410 = true :=
  cell_node0 P63_10 79 0 0 0 2632 1230 410 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) true true K63_10_2 K63_10_3

abbrev F63 : ℕ → Bool := lvBody G (63 + 1) (lv.getD 63 dflt).2.2.2 (lv.getD 63 dflt).1 (lv.getD 63 dflt).2.1
  (lv.getD 63 dflt).2.2.1 80 (fun a => some (cvOf 1 ws (63 + 1) a))

theorem body10 : F63 10 = true := by
  have h := lvBody_cell G 64 10 175230087 4012 1650 550 80 (fun a => some (cvOf 1 ws 64 a)) (cvOf 1 ws 64 10) (by decide) rfl
  exact h.trans K63_10_1

theorem ok63 : okAt G 1 ws lv 63 = true := by
  have p1 : allR F63 0 10 = true := by decide +kernel
  have p2 : allR F63 10 1 = true := allR_one F63 10 body10
  have p3 : allR F63 11 19 = true := by decide +kernel
  have h : allR F63 0 30 = true := allR_add F63 0 11 19 (allR_add F63 0 10 1 p1 p2) p3
  rw [allR_zero] at h
  exact h

theorem C7 : allOK G 1 ws lv 63 1 = true := by
  unfold allOK
  simpa using ok63

end Gate61DatLOD
