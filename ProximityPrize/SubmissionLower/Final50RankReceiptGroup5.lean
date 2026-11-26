import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Final50RankBlocks
set_option Elab.async false


set_option Elab.async false

-- merged module Final50RankReceiptGroup0
section Merged_Final50RankReceiptGroup0

-- merged module Final50RankReceiptBase
section Merged_Final50RankReceiptBase
set_option Elab.async false
namespace Final50RankReceipt
open K1_13_1_1 (bandCount)
open AnchorPivot82180 (monoData)
abbrev Row := RankRows82190.Row
def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 57 ∧ x.top ≤ 14 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)
private def pivot (i : Fin 9) : AnchorPivot82180.E :=
  ![⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,1,0,0⟩, ⟨1,1,0,0⟩,
    ⟨1,0,1,0⟩, ⟨2,0,1,0⟩, ⟨1,3,0,0⟩, ⟨2,3,0,0⟩] i
private abbrev E := AnchorPivot82180.E
private abbrev Factor := RankRows82190.Factor
private def readFactors : ℕ → ℕ → List Factor × ℕ
  | 0, bits => ([], bits)
  | n+1, bits =>
    let i : Fin 9 := ⟨(bits % 16) % 9, Nat.mod_lt _ (by decide)⟩
    let k := bits / 16 % 16
    let rest := bits / 256
    let (fs, tail) := readFactors n (if k = 0 then rest / 64 else rest)
    ((i, if k = 0 then rest % 64 else k) :: fs, tail)
private def readSchedules : ℕ → ℕ → List (List Factor)
  | 0, _ => []
  | n+1, bits =>
    let (fs, rest) := readFactors (bits % 8) (bits / 8)
    fs :: readSchedules n rest
private def pivots (d i : ℕ) : List E :=
  (List.range (min (min d 14) (i / 3) + 1)).flatMap fun f =>
    let lo := i - (d + 2*f)
    let hi := min (d-f) ((i-3*f)/2)
    (List.range (hi+1-lo)).map fun k =>
      let c := lo+k
      let b := i-2*c-3*f
      ⟨d-b-c-f, b, c, f⟩
private def subtractPivot (e : E) (f : Factor) : E :=
  let p := pivot f.1
  ⟨e.a-f.2*p.a, e.b-f.2*p.b, e.c-f.2*p.c, e.f-f.2*p.f⟩
private def decodeRow (e : E) (fs : List Factor) : Row :=
  let r := fs.foldl subtractPivot e
  let x := (monoData r).plus (RankRows82190.measure fs)
  ⟨x.tag, x.lo, x.ord, r, fs⟩
def decode (d i start n data : ℕ) : List Row :=
  ((pivots d i).drop start).zipWith decodeRow (readSchedules n data)
def fee (s : ℕ) (r : Row) : ℕ := 101 + r.index - (s + r.ord)
def triangle (n : ℕ) : ℕ := n * (n+1) / 2
def stageRange : ℕ → ℕ × ℕ
  | 33 => (136, 137)
  | 34 => (135, 136)
  | 35 => (134, 135)
  | 36 => (133, 134)
  | 37 => (132, 133)
  | 38 => (131, 132)
  | 39 => (130, 131)
  | 40 => (129, 130)
  | 41 => (128, 129)
  | 42 => (127, 128)
  | 43 => (126, 127)
  | 44 => (125, 126)
  | 45 => (124, 125)
  | 46 => (123, 124)
  | 47 => (122, 123)
  | 48 => (121, 122)
  | 49 => (120, 121)
  | 50 => (119, 120)
  | 51 => (118, 119)
  | 52 => (117, 118)
  | 53 => (116, 117)
  | 54 => (115, 116)
  | 55 => (114, 115)
  | 56 => (113, 114)
  | 57 => (58, 113)
  | _ => (137, 137)
def lateLo (d : ℕ) : ℕ := (stageRange d).1
def lateHi (d : ℕ) : ℕ := (stageRange d).2
def price (d : ℕ) (r : Row) : ℕ :=
  fee d r + (triangle (fee (lateLo d) r) - triangle (fee (lateHi d) r))
def checkRows (d i upper lower : ℕ) : List Row → Bool
  | [] => true
  | r :: rs => decide (lower ≤ r.tag ∧ r.tag ≤ upper ∧ r.index = i) &&
      good d r && checkRows d i upper (r.tag + 1) rs
theorem checkRows_sound {d i u l : ℕ} {rs : List Row} (h : checkRows d i u l rs = true) :
    (∀ r ∈ rs, l ≤ r.tag ∧ r.tag ≤ u ∧ r.index = i ∧ good d r = true) ∧
      rs.Pairwise (fun a b => a.tag < b.tag) := by
  induction rs generalizing l with
  | nil => simp
  | cons r rs ih =>
    simp only [checkRows, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hl, hu, hi⟩, hg⟩, hr⟩ := h
    obtain ⟨ha, hs⟩ := ih hr
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_, hs⟩⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hl, hu, hi, hg⟩
      · obtain ⟨hb, hc, hd, he⟩ := ha q hq
        exact ⟨by omega, hc, hd, he⟩
    · intro q hq
      exact (ha q hq).1
structure Chunk (d : ℕ) where
  index : ℕ
  lower : ℕ
  upper : ℕ
  size : ℕ
  total : ℕ
  rows : List Row
  checked : checkRows d index upper lower rows = true
  length_eq : rows.length = size
  total_eq : (rows.map (price d)).sum = total
def witnessFinal50 (d i start lo hi n total bits : ℕ)
    (checked : checkRows d i hi lo (decode d i start n bits) = true ∧
      (decode d i start n bits).length = n ∧
      ((decode d i start n bits).map (price d)).sum = total) : Chunk d :=
  ⟨i, lo, hi, n, total, decode d i start n bits, checked.1, checked.2.1, checked.2.2⟩
def rowsFrom {d : ℕ} (cs : List (Chunk d)) : List Row :=
  cs.flatMap Chunk.rows
theorem rowsFrom_good {d : ℕ} (cs : List (Chunk d)) :
    ∀ r ∈ rowsFrom cs, good d r = true := by
  intro r hr
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hr
  exact ((checkRows_sound c.checked).1 r hc).2.2.2
def chunksOrdered {d : ℕ} (limit : ℕ) : List (Chunk d) → Bool
  | [] => true
  | a :: cs => decide (limit ≤ a.lower ∧ a.lower ≤ a.upper) && chunksOrdered (a.upper + 1) cs
theorem rowsFrom_sorted_aux {d : ℕ} (cs : List (Chunk d)) (limit : ℕ)
    (h : chunksOrdered limit cs = true) :
    (rowsFrom cs).Pairwise (fun a b => a.tag < b.tag) ∧
      ∀ r ∈ rowsFrom cs, limit ≤ r.tag := by
  induction cs generalizing limit with
  | nil => simp [rowsFrom]
  | cons a cs ih =>
    simp only [chunksOrdered, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs, hl⟩ := ih _ h.2
    have ha := checkRows_sound a.checked
    change (a.rows ++ rowsFrom cs).Pairwise _ ∧ _
    refine ⟨List.pairwise_append.mpr ⟨ha.2, hs, ?_⟩, ?_⟩
    · intro r hr q hq
      exact (ha.1 r hr).2.1.trans_lt (hl q hq)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact h.1.1.trans (ha.1 r hr).1
      · exact (h.1.1.trans h.1.2).trans ((Nat.le_succ _).trans (hl r hr))
def mass {d : ℕ} (i : ℕ) (cs : List (Chunk d)) : ℕ :=
  (cs.map fun c => if i ≤ c.index then c.size else 0).sum
theorem mass_eq {d : ℕ} (i : ℕ) (cs : List (Chunk d)) :
    ((rowsFrom cs).filter fun r => decide (i ≤ r.index)).length = mass i cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change ((c.rows ++ rowsFrom cs).filter fun r => decide (i ≤ r.index)).length = _
    rw [List.filter_append, List.length_append, ih]
    have heq : c.rows.filter (fun r => decide (i ≤ r.index)) =
        c.rows.filter (fun _ => decide (i ≤ c.index)) := by
      apply List.filter_congr
      intro r hr
      rw [((checkRows_sound c.checked).1 r hr).2.2.1]
    rw [heq]
    by_cases h : i ≤ c.index <;> simp [mass, h, c.length_eq]
def total {d : ℕ} (cs : List (Chunk d)) : ℕ :=
  (cs.map Chunk.total).sum
theorem total_eq {d : ℕ} (cs : List (Chunk d)) :
    ((rowsFrom cs).map (price d)).sum = total cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change ((c.rows ++ rowsFrom cs).map (price d)).sum = _
    rw [List.map_append, List.sum_append, c.total_eq, ih]
    rfl
end Final50RankReceipt

end Merged_Final50RankReceiptBase

-- merged module Final50RankReceiptGroup0
section Merged_Final50RankReceiptGroup0

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)

private def cert0_0 := witnessFinal50 0 0 0 0 0 1 101
  0x0 (by decide +kernel)
private def chunks0 : List (Chunk 0) := [
  cert0_0]
def rows0 := rowsFrom chunks0

theorem good0 : ∀ r ∈ rows0, good 0 r = true := rowsFrom_good chunks0

theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks0 0 (by decide +kernel)).1

theorem mass0 (i : Fin 58) :
    bandCount 0 (i.val : ℤ) 57 14 ≤ (rows0.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks0).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 0 (j : ℤ) 57 14 ≤ mass j chunks0)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total0 : (rows0.map (price 0)).sum = 101 :=
  (total_eq chunks0).trans (by decide +kernel)

private def cert1_0 := witnessFinal50 1 3 0 64 64 1 101
  0x0 (by decide +kernel)
private def cert1_1 := witnessFinal50 1 2 0 10001 10001 1 101
  0x0 (by decide +kernel)
private def cert1_2 := witnessFinal50 1 1 0 20000 20000 1 101
  0x0 (by decide +kernel)
private def cert1_3 := witnessFinal50 1 0 0 30000 30000 1 97
  0x91 (by decide +kernel)
private def chunks1 : List (Chunk 1) := [
  cert1_0,
  cert1_1,
  cert1_2,
  cert1_3]
def rows1 := rowsFrom chunks1

theorem good1 : ∀ r ∈ rows1, good 1 r = true := rowsFrom_good chunks1

theorem sorted1 : rows1.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks1 0 (by decide +kernel)).1

theorem mass1 (i : Fin 58) :
    bandCount 1 (i.val : ℤ) 57 14 ≤ (rows1.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks1).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 1 (j : ℤ) 57 14 ≤ mass j chunks1)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total1 : (rows1.map (price 1)).sum = 400 :=
  (total_eq chunks1).trans (by decide +kernel)

private def cert2_0 := witnessFinal50 2 6 0 128 128 1 101
  0x0 (by decide +kernel)
private def cert2_1 := witnessFinal50 2 5 0 10065 10065 1 101
  0x0 (by decide +kernel)
private def cert2_2 := witnessFinal50 2 4 0 20002 20064 2 202
  0x0 (by decide +kernel)
private def cert2_3 := witnessFinal50 2 3 0 30001 30064 2 198
  0x488 (by decide +kernel)
private def cert2_4 := witnessFinal50 2 2 0 40000 40001 2 198
  0x488 (by decide +kernel)
private def cert2_5 := witnessFinal50 2 1 0 50000 50000 1 97
  0x91 (by decide +kernel)
private def cert2_6 := witnessFinal50 2 0 0 60000 60000 1 93
  0x111 (by decide +kernel)
private def chunks2 : List (Chunk 2) := [
  cert2_0,
  cert2_1,
  cert2_2,
  cert2_3,
  cert2_4,
  cert2_5,
  cert2_6]
def rows2 := rowsFrom chunks2

theorem good2 : ∀ r ∈ rows2, good 2 r = true := rowsFrom_good chunks2

theorem sorted2 : rows2.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks2 0 (by decide +kernel)).1

theorem mass2 (i : Fin 58) :
    bandCount 2 (i.val : ℤ) 57 14 ≤ (rows2.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks2).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 2 (j : ℤ) 57 14 ≤ mass j chunks2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total2 : (rows2.map (price 2)).sum = 990 :=
  (total_eq chunks2).trans (by decide +kernel)

private def cert3_0 := witnessFinal50 3 9 0 192 192 1 101
  0x0 (by decide +kernel)
private def cert3_1 := witnessFinal50 3 8 0 10129 10129 1 101
  0x0 (by decide +kernel)
private def cert3_2 := witnessFinal50 3 7 0 20066 20128 2 202
  0x0 (by decide +kernel)
private def cert3_3 := witnessFinal50 3 6 0 30003 30128 3 299
  0x2440 (by decide +kernel)
private def cert3_4 := witnessFinal50 3 5 0 40002 40065 3 299
  0x2440 (by decide +kernel)
private def cert3_5 := witnessFinal50 3 4 0 50001 50064 3 295
  0x244488 (by decide +kernel)
private def cert3_6 := witnessFinal50 3 3 0 60000 60064 3 291
  0x444488 (by decide +kernel)
private def cert3_7 := witnessFinal50 3 2 0 70000 70001 2 190
  0x88891 (by decide +kernel)
private def cert3_8 := witnessFinal50 3 1 0 80000 80000 1 93
  0x111 (by decide +kernel)
private def cert3_9 := witnessFinal50 3 0 0 90000 90000 1 89
  0x191 (by decide +kernel)
private def chunks3 : List (Chunk 3) := [
  cert3_0,
  cert3_1,
  cert3_2,
  cert3_3,
  cert3_4,
  cert3_5,
  cert3_6,
  cert3_7,
  cert3_8,
  cert3_9]
def rows3 := rowsFrom chunks3

theorem good3 : ∀ r ∈ rows3, good 3 r = true := rowsFrom_good chunks3

theorem sorted3 : rows3.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks3 0 (by decide +kernel)).1

theorem mass3 (i : Fin 58) :
    bandCount 3 (i.val : ℤ) 57 14 ≤ (rows3.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks3).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 3 (j : ℤ) 57 14 ≤ mass j chunks3)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total3 : (rows3.map (price 3)).sum = 1960 :=
  (total_eq chunks3).trans (by decide +kernel)

private def cert4_0 := witnessFinal50 4 12 0 256 256 1 101
  0x0 (by decide +kernel)
private def cert4_1 := witnessFinal50 4 11 0 10193 10193 1 101
  0x0 (by decide +kernel)
private def cert4_2 := witnessFinal50 4 10 0 20130 20192 2 202
  0x0 (by decide +kernel)
private def cert4_3 := witnessFinal50 4 9 0 30067 30192 3 299
  0x2440 (by decide +kernel)
private def cert4_4 := witnessFinal50 4 8 0 40004 40129 4 400
  0x12200 (by decide +kernel)
private def cert4_5 := witnessFinal50 4 7 0 50003 50128 4 396
  0x1222440 (by decide +kernel)
private def cert4_6 := witnessFinal50 4 6 0 60002 60128 5 489
  0x1111220488 (by decide +kernel)
private def cert4_7 := witnessFinal50 4 5 0 70001 70065 4 388
  0x222244488 (by decide +kernel)
private def cert4_8 := witnessFinal50 4 4 0 80000 80064 4 384
  0x222444488 (by decide +kernel)
private def cert4_9 := witnessFinal50 4 3 0 90000 90064 3 279
  0x64488891 (by decide +kernel)
private def cert4_10 := witnessFinal50 4 2 0 100000 100001 2 182
  0xc8911 (by decide +kernel)
private def cert4_11 := witnessFinal50 4 1 0 110000 110000 1 89
  0x191 (by decide +kernel)
private def cert4_12 := witnessFinal50 4 0 0 120000 120000 1 85
  0x211 (by decide +kernel)
private def chunks4 : List (Chunk 4) := [
  cert4_0,
  cert4_1,
  cert4_2,
  cert4_3,
  cert4_4,
  cert4_5,
  cert4_6,
  cert4_7,
  cert4_8,
  cert4_9,
  cert4_10,
  cert4_11,
  cert4_12]
def rows4 := rowsFrom chunks4

theorem good4 : ∀ r ∈ rows4, good 4 r = true := rowsFrom_good chunks4

theorem sorted4 : rows4.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks4 0 (by decide +kernel)).1

theorem mass4 (i : Fin 58) :
    bandCount 4 (i.val : ℤ) 57 14 ≤ (rows4.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks4).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 4 (j : ℤ) 57 14 ≤ mass j chunks4)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total4 : (rows4.map (price 4)).sum = 3395 :=
  (total_eq chunks4).trans (by decide +kernel)


end Final50RankReceipt

end Merged_Final50RankReceiptGroup0

end Merged_Final50RankReceiptGroup0

-- merged module Final50RankReceiptGroup5
section Merged_Final50RankReceiptGroup5

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)

private def cert5_0 := witnessFinal50 5 15 0 320 320 1 101
  0x0 (by decide +kernel)
private def cert5_1 := witnessFinal50 5 14 0 10257 10257 1 101
  0x0 (by decide +kernel)
private def cert5_2 := witnessFinal50 5 13 0 20194 20256 2 202
  0x0 (by decide +kernel)
private def cert5_3 := witnessFinal50 5 12 0 30131 30256 3 299
  0x2440 (by decide +kernel)
private def cert5_4 := witnessFinal50 5 11 0 40068 40193 4 400
  0x12200 (by decide +kernel)
private def cert5_5 := witnessFinal50 5 10 0 50005 50192 5 497
  0x9112200 (by decide +kernel)
private def cert5_6 := witnessFinal50 5 9 0 60004 60192 6 590
  0x8889102440 (by decide +kernel)
private def cert5_7 := witnessFinal50 5 8 0 70003 70129 6 586
  0x888911220488 (by decide +kernel)
private def cert5_8 := witnessFinal50 5 7 0 80002 80128 6 582
  0x889111220488 (by decide +kernel)
private def cert5_9 := witnessFinal50 5 6 0 90001 90128 6 570
  0xc8911122444488 (by decide +kernel)
private def cert5_10 := witnessFinal50 5 5 0 100000 100065 5 473
  0x191222444488 (by decide +kernel)
private def cert5_11 := witnessFinal50 5 4 0 110000 110064 4 368
  0x32264488891 (by decide +kernel)
private def cert5_12 := witnessFinal50 5 3 0 120000 120064 3 267
  0x844c8911 (by decide +kernel)
private def cert5_13 := witnessFinal50 5 2 0 130000 130001 2 174
  0x108991 (by decide +kernel)
private def cert5_14 := witnessFinal50 5 1 0 140000 140000 1 85
  0x211 (by decide +kernel)
private def cert5_15 := witnessFinal50 5 0 0 150000 150000 1 81
  0x291 (by decide +kernel)
private def chunks5 : List (Chunk 5) := [
  cert5_0,
  cert5_1,
  cert5_2,
  cert5_3,
  cert5_4,
  cert5_5,
  cert5_6,
  cert5_7,
  cert5_8,
  cert5_9,
  cert5_10,
  cert5_11,
  cert5_12,
  cert5_13,
  cert5_14,
  cert5_15]
def rows5 := rowsFrom chunks5

theorem good5 : ∀ r ∈ rows5, good 5 r = true := rowsFrom_good chunks5

theorem sorted5 : rows5.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks5 0 (by decide +kernel)).1

theorem mass5 (i : Fin 58) :
    bandCount 5 (i.val : ℤ) 57 14 ≤ (rows5.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks5).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 5 (j : ℤ) 57 14 ≤ mass j chunks5)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total5 : (rows5.map (price 5)).sum = 5376 :=
  (total_eq chunks5).trans (by decide +kernel)

private def cert6_0 := witnessFinal50 6 18 0 384 384 1 101
  0x0 (by decide +kernel)
private def cert6_1 := witnessFinal50 6 17 0 10321 10321 1 101
  0x0 (by decide +kernel)
private def cert6_2 := witnessFinal50 6 16 0 20258 20320 2 202
  0x0 (by decide +kernel)
private def cert6_3 := witnessFinal50 6 15 0 30195 30320 3 299
  0x2440 (by decide +kernel)
private def cert6_4 := witnessFinal50 6 14 0 40132 40257 4 400
  0x12200 (by decide +kernel)
private def cert6_5 := witnessFinal50 6 13 0 50069 50256 5 497
  0x9112200 (by decide +kernel)
private def cert6_6 := witnessFinal50 6 12 0 60006 60256 7 691
  0x44448812200 (by decide +kernel)
private def cert6_7 := witnessFinal50 6 11 0 70005 70193 7 687
  0x4444889102440 (by decide +kernel)
private def cert6_8 := witnessFinal50 6 10 0 80004 80192 8 780
  0x2224444881220488 (by decide +kernel)
private def cert6_9 := witnessFinal50 6 9 0 90003 90192 8 768
  0x322444489111220488 (by decide +kernel)
private def cert6_10 := witnessFinal50 6 8 0 100002 100129 8 764
  0x322444888910444488 (by decide +kernel)
private def cert6_11 := witnessFinal50 6 7 0 110001 110128 7 659
  0x644c8911122444488 (by decide +kernel)
private def cert6_12 := witnessFinal50 6 6 0 120000 120128 7 647
  0x844c8911322444488 (by decide +kernel)
private def cert6_13 := witnessFinal50 6 5 0 130000 130065 5 453
  0x21132264488891 (by decide +kernel)
private def cert6_14 := witnessFinal50 6 4 0 140000 140064 4 352
  0x422844c8911 (by decide +kernel)
private def cert6_15 := witnessFinal50 6 3 0 150000 150064 3 255
  0xa4508991 (by decide +kernel)
private def cert6_16 := witnessFinal50 6 2 0 160000 160001 2 166
  0x148a11 (by decide +kernel)
private def cert6_17 := witnessFinal50 6 1 0 170000 170000 1 81
  0x291 (by decide +kernel)
private def cert6_18 := witnessFinal50 6 0 0 180000 180000 1 77
  0x311 (by decide +kernel)
private def chunks6 : List (Chunk 6) := [
  cert6_0,
  cert6_1,
  cert6_2,
  cert6_3,
  cert6_4,
  cert6_5,
  cert6_6,
  cert6_7,
  cert6_8,
  cert6_9,
  cert6_10,
  cert6_11,
  cert6_12,
  cert6_13,
  cert6_14,
  cert6_15,
  cert6_16,
  cert6_17,
  cert6_18]
def rows6 := rowsFrom chunks6

theorem good6 : ∀ r ∈ rows6, good 6 r = true := rowsFrom_good chunks6

theorem sorted6 : rows6.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks6 0 (by decide +kernel)).1

theorem mass6 (i : Fin 58) :
    bandCount 6 (i.val : ℤ) 57 14 ≤ (rows6.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks6).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 6 (j : ℤ) 57 14 ≤ mass j chunks6)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total6 : (rows6.map (price 6)).sum = 7980 :=
  (total_eq chunks6).trans (by decide +kernel)

private def cert7_0 := witnessFinal50 7 21 0 448 448 1 101
  0x0 (by decide +kernel)
private def cert7_1 := witnessFinal50 7 20 0 10385 10385 1 101
  0x0 (by decide +kernel)
private def cert7_2 := witnessFinal50 7 19 0 20322 20384 2 202
  0x0 (by decide +kernel)
private def cert7_3 := witnessFinal50 7 18 0 30259 30384 3 299
  0x2440 (by decide +kernel)
private def cert7_4 := witnessFinal50 7 17 0 40196 40321 4 400
  0x12200 (by decide +kernel)
private def cert7_5 := witnessFinal50 7 16 0 50133 50320 5 497
  0x9112200 (by decide +kernel)
private def cert7_6 := witnessFinal50 7 15 0 60070 60320 7 691
  0x44448812200 (by decide +kernel)
private def cert7_7 := witnessFinal50 7 14 0 70007 70257 8 788
  0x22224448812200 (by decide +kernel)
private def cert7_8 := witnessFinal50 7 13 0 80006 80256 9 881
  0x11122224409102440 (by decide +kernel)
private def cert7_9 := witnessFinal50 7 12 0 90005 90256 10 966
  0xc89111224444881220488 (by decide +kernel)
private def cert7_10 := witnessFinal50 7 11 0 100004 100193 10 962
  0xc89112222441111220488 (by decide +kernel)
private def cert7_11 := witnessFinal50 7 10 0 110003 110192 10 950
  0xc8991222244888910444488 (by decide +kernel)
private def cert7_12 := witnessFinal50 7 9 0 120002 120192 10 938
  0x108991222644888910444488 (by decide +kernel)
private def cert7_13 := witnessFinal50 7 8 0 130001 130129 9 833
  0x21132264488891322444488 (by decide +kernel)
private def cert7_14 := witnessFinal50 7 7 0 140000 140128 8 732
  0x422844c8911322444488 (by decide +kernel)
private def cert7_15 := witnessFinal50 7 6 0 150000 150128 7 619
  0xa450899142264488891 (by decide +kernel)
private def cert7_16 := witnessFinal50 7 5 0 160000 160065 5 433
  0x291422844c8911 (by decide +kernel)
private def cert7_17 := witnessFinal50 7 4 0 170000 170064 4 336
  0x522a4508991 (by decide +kernel)
private def cert7_18 := witnessFinal50 7 3 0 180000 180064 3 243
  0xc4548a11 (by decide +kernel)
private def cert7_19 := witnessFinal50 7 2 0 190000 190001 2 158
  0x188a91 (by decide +kernel)
private def cert7_20 := witnessFinal50 7 1 0 200000 200000 1 77
  0x311 (by decide +kernel)
private def cert7_21 := witnessFinal50 7 0 0 210000 210000 1 73
  0x391 (by decide +kernel)
private def chunks7 : List (Chunk 7) := [
  cert7_0,
  cert7_1,
  cert7_2,
  cert7_3,
  cert7_4,
  cert7_5,
  cert7_6,
  cert7_7,
  cert7_8,
  cert7_9,
  cert7_10,
  cert7_11,
  cert7_12,
  cert7_13,
  cert7_14,
  cert7_15,
  cert7_16,
  cert7_17,
  cert7_18,
  cert7_19,
  cert7_20,
  cert7_21]
def rows7 := rowsFrom chunks7

theorem good7 : ∀ r ∈ rows7, good 7 r = true := rowsFrom_good chunks7

theorem sorted7 : rows7.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks7 0 (by decide +kernel)).1

theorem mass7 (i : Fin 58) :
    bandCount 7 (i.val : ℤ) 57 14 ≤ (rows7.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks7).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 7 (j : ℤ) 57 14 ≤ mass j chunks7)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total7 : (rows7.map (price 7)).sum = 11280 :=
  (total_eq chunks7).trans (by decide +kernel)

private def cert8_0 := witnessFinal50 8 24 0 512 512 1 101
  0x0 (by decide +kernel)
private def cert8_1 := witnessFinal50 8 23 0 10449 10449 1 101
  0x0 (by decide +kernel)
private def cert8_2 := witnessFinal50 8 22 0 20386 20448 2 202
  0x0 (by decide +kernel)
private def cert8_3 := witnessFinal50 8 21 0 30323 30448 3 299
  0x2440 (by decide +kernel)
private def cert8_4 := witnessFinal50 8 20 0 40260 40385 4 400
  0x12200 (by decide +kernel)
private def cert8_5 := witnessFinal50 8 19 0 50197 50384 5 497
  0x9112200 (by decide +kernel)
private def cert8_6 := witnessFinal50 8 18 0 60134 60384 7 691
  0x44448812200 (by decide +kernel)
private def cert8_7 := witnessFinal50 8 17 0 70071 70321 8 788
  0x22224448812200 (by decide +kernel)
private def cert8_8 := witnessFinal50 8 16 0 80008 80320 10 982
  0x88911122048812200 (by decide +kernel)
private def cert8_9 := witnessFinal50 8 15 0 90007 90320 11 1067
  0x6448889122224409102440 (by decide +kernel)
private def cert8_10 := witnessFinal50 8 14 0 100006 100257 12 1160
  0x3224448889104444881220488 (by decide +kernel)
private def cert8_11 := witnessFinal50 8 13 0 110005 110256 12 1148
  0x322644888912222441111220488 (by decide +kernel)
private def cert8_12 := witnessFinal50 8 12 0 120004 120256 13 1229
  0x211322444c89111220888910444488 (by decide +kernel)
private def cert8_13 := witnessFinal50 8 11 0 130003 130193 12 1124
  0x422644c8911122644888910444488 (by decide +kernel)
private def cert8_14 := witnessFinal50 8 10 0 140002 140192 12 1112
  0x422844c8911322444488322444488 (by decide +kernel)
private def cert8_15 := witnessFinal50 8 9 0 150001 150192 11 999
  0xa450899142264488891322444488 (by decide +kernel)
private def cert8_16 := witnessFinal50 8 8 0 160000 160129 10 898
  0x148a1142264488a11322444488 (by decide +kernel)
private def cert8_17 := witnessFinal50 8 7 0 170000 170128 8 700
  0x522a450899142264488891 (by decide +kernel)
private def cert8_18 := witnessFinal50 8 6 0 180000 180128 7 591
  0xc4548a11522844c8911 (by decide +kernel)
private def cert8_19 := witnessFinal50 8 5 0 190000 190065 5 413
  0x311522a4508991 (by decide +kernel)
private def cert8_20 := witnessFinal50 8 4 0 200000 200064 4 320
  0x622c4548a11 (by decide +kernel)
private def cert8_21 := witnessFinal50 8 3 0 210000 210064 3 231
  0xe4588a91 (by decide +kernel)
private def cert8_22 := witnessFinal50 8 2 0 220000 220001 2 150
  0x1c8b11 (by decide +kernel)
private def cert8_23 := witnessFinal50 8 1 0 230000 230000 1 73
  0x391 (by decide +kernel)
private def cert8_24 := witnessFinal50 8 0 0 240000 240000 1 69
  0x411 (by decide +kernel)
private def chunks8 : List (Chunk 8) := [
  cert8_0,
  cert8_1,
  cert8_2,
  cert8_3,
  cert8_4,
  cert8_5,
  cert8_6,
  cert8_7,
  cert8_8,
  cert8_9,
  cert8_10,
  cert8_11,
  cert8_12,
  cert8_13,
  cert8_14,
  cert8_15,
  cert8_16,
  cert8_17,
  cert8_18,
  cert8_19,
  cert8_20,
  cert8_21,
  cert8_22,
  cert8_23,
  cert8_24]
def rows8 := rowsFrom chunks8

theorem good8 : ∀ r ∈ rows8, good 8 r = true := rowsFrom_good chunks8

theorem sorted8 : rows8.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks8 0 (by decide +kernel)).1

theorem mass8 (i : Fin 58) :
    bandCount 8 (i.val : ℤ) 57 14 ≤ (rows8.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks8).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 8 (j : ℤ) 57 14 ≤ mass j chunks8)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total8 : (rows8.map (price 8)).sum = 15345 :=
  (total_eq chunks8).trans (by decide +kernel)

private def cert9_0 := witnessFinal50 9 27 0 576 576 1 101
  0x0 (by decide +kernel)
private def cert9_1 := witnessFinal50 9 26 0 10513 10513 1 101
  0x0 (by decide +kernel)
private def cert9_2 := witnessFinal50 9 25 0 20450 20512 2 202
  0x0 (by decide +kernel)
private def cert9_3 := witnessFinal50 9 24 0 30387 30512 3 299
  0x2440 (by decide +kernel)
private def cert9_4 := witnessFinal50 9 23 0 40324 40449 4 400
  0x12200 (by decide +kernel)
private def cert9_5 := witnessFinal50 9 22 0 50261 50448 5 497
  0x9112200 (by decide +kernel)
private def cert9_6 := witnessFinal50 9 21 0 60198 60448 7 691
  0x44448812200 (by decide +kernel)
private def cert9_7 := witnessFinal50 9 20 0 70135 70385 8 788
  0x22224448812200 (by decide +kernel)
private def cert9_8 := witnessFinal50 9 19 0 80072 80384 10 982
  0x88911122048812200 (by decide +kernel)
private def cert9_9 := witnessFinal50 9 18 0 90009 90384 12 1168
  0x32244448911122048812200 (by decide +kernel)
private def cert9_10 := witnessFinal50 9 17 0 100008 100321 13 1261
  0x19122244448822224409102440 (by decide +kernel)
private def cert9_11 := witnessFinal50 9 16 0 110007 110320 14 1346
  0xc89912222448889104444881220488 (by decide +kernel)
private def cert9_12 := witnessFinal50 9 15 0 120006 120320 15 1427
  0x844c89113224444882222441111220488 (by decide +kernel)
private def cert9_13 := witnessFinal50 9 14 0 130005 130257 15 1415
  0x844c8991222244c89111220888910444488 (by decide +kernel)
private def cert9_14 := witnessFinal50 9 13 0 140004 140256 15 1403
  0x84508991222644888910644888910444488 (by decide +kernel)
private def cert9_15 := witnessFinal50 9 12 0 150003 150256 15 1379
  0xa450899142264488891322444488322444488 (by decide +kernel)
private def cert9_16 := witnessFinal50 9 11 0 160002 160193 14 1278
  0x148a1142264488a11322444488322444488 (by decide +kernel)
private def cert9_17 := witnessFinal50 9 10 0 170001 170192 13 1165
  0x291522844c8a1132244448a11322444488 (by decide +kernel)
private def cert9_18 := witnessFinal50 9 9 0 180000 180192 12 1056
  0x622a4508a9142264488a11322444488 (by decide +kernel)
private def cert9_19 := witnessFinal50 9 8 0 190000 190129 10 858
  0x188a91522844c8a9142264488891 (by decide +kernel)
private def cert9_20 := witnessFinal50 9 7 0 200000 200128 8 668
  0x622c4548a11522844c8911 (by decide +kernel)
private def cert9_21 := witnessFinal50 9 6 0 210000 210128 7 563
  0xe4588a91622a4508991 (by decide +kernel)
private def cert9_22 := witnessFinal50 9 5 0 220000 220065 5 393
  0x391622c4548a11 (by decide +kernel)
private def cert9_23 := witnessFinal50 9 4 0 230000 230064 4 304
  0x722e4588a91 (by decide +kernel)
private def cert9_24 := witnessFinal50 9 3 0 240000 240064 3 219
  0x1045c8b11 (by decide +kernel)
private def cert9_25 := witnessFinal50 9 2 0 250000 250001 2 142
  0x208b91 (by decide +kernel)
private def cert9_26 := witnessFinal50 9 1 0 260000 260000 1 69
  0x411 (by decide +kernel)
private def cert9_27 := witnessFinal50 9 0 0 270000 270000 1 65
  0x491 (by decide +kernel)
private def chunks9 : List (Chunk 9) := [
  cert9_0,
  cert9_1,
  cert9_2,
  cert9_3,
  cert9_4,
  cert9_5,
  cert9_6,
  cert9_7,
  cert9_8,
  cert9_9,
  cert9_10,
  cert9_11,
  cert9_12,
  cert9_13,
  cert9_14,
  cert9_15,
  cert9_16,
  cert9_17,
  cert9_18,
  cert9_19,
  cert9_20,
  cert9_21,
  cert9_22,
  cert9_23,
  cert9_24,
  cert9_25,
  cert9_26,
  cert9_27]
def rows9 := rowsFrom chunks9

theorem good9 : ∀ r ∈ rows9, good 9 r = true := rowsFrom_good chunks9

theorem sorted9 : rows9.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks9 0 (by decide +kernel)).1

theorem mass9 (i : Fin 58) :
    bandCount 9 (i.val : ℤ) 57 14 ≤ (rows9.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks9).filter _).length
  rw [mass_eq]
  have h : (List.range 58).all
      (fun j => decide (bandCount 9 (j : ℤ) 57 14 ≤ mass j chunks9)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total9 : (rows9.map (price 9)).sum = 20240 :=
  (total_eq chunks9).trans (by decide +kernel)


end Final50RankReceipt

end Merged_Final50RankReceiptGroup5
