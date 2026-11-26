import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalRankBlocks
import ProximityPrize.SubmissionLower.DdZZ6ou4c

section Merged6967_A6966FinalRankReceiptGroup58
set_option Elab.async false


set_option Elab.async false

-- merged module A6966FinalRankReceiptGroup0
section Merged_A6966FinalRankReceiptGroup0

-- merged module A6966FinalRankReceiptBase
section Merged_A6966FinalRankReceiptBase
set_option Elab.async false
namespace A6966FinalRankReceipt
open K1_13_1_1 (bandCount)
open AnchorPivot82180 (monoData)
abbrev Row := A6966Rows.Row
def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 58 ∧ x.top ≤ 15 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)
private def pivot (i : Fin 9) : AnchorPivot82180.E :=
  ![⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,1,0,0⟩, ⟨1,1,0,0⟩,
    ⟨1,0,1,0⟩, ⟨2,0,1,0⟩, ⟨1,3,0,0⟩, ⟨2,3,0,0⟩] i
private abbrev E := AnchorPivot82180.E
private abbrev Factor := A6966Rows.Factor
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
  (List.range (min (min d 15) (i / 3) + 1)).flatMap fun f =>
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
  let x := (monoData r).plus (A6966Rows.measure fs)
  ⟨x.tag, x.lo, x.ord, r, fs⟩
def decode (d i start n data : ℕ) : List Row :=
  ((pivots d i).drop start).zipWith decodeRow (readSchedules n data)
def fee (s : ℕ) (r : Row) : ℕ := 106 + r.index - (s + r.ord)
def triangle (n : ℕ) : ℕ := n * (n+1) / 2
def stageRange : ℕ → ℕ × ℕ
  | 36 => (142, 143)
  | 37 => (141, 142)
  | 38 => (140, 141)
  | 39 => (139, 140)
  | 40 => (138, 139)
  | 41 => (137, 138)
  | 42 => (136, 137)
  | 43 => (135, 136)
  | 44 => (134, 135)
  | 45 => (133, 134)
  | 46 => (132, 133)
  | 47 => (131, 132)
  | 48 => (130, 131)
  | 49 => (129, 130)
  | 50 => (128, 129)
  | 51 => (127, 128)
  | 52 => (126, 127)
  | 53 => (125, 126)
  | 54 => (124, 125)
  | 55 => (123, 124)
  | 56 => (122, 123)
  | 57 => (121, 122)
  | 58 => (59, 121)
  | _ => (143, 143)

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
def witnessA6966Final (d i start lo hi n total bits : ℕ)
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
end A6966FinalRankReceipt

end Merged_A6966FinalRankReceiptBase

-- merged module A6966FinalRankReceiptGroup0
section Merged_A6966FinalRankReceiptGroup0
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace A6966FinalRankReceipt
open K1_13_1_1 (bandCount)

private def cert0_0 := witnessA6966Final 0 0 0 0 0 1 106
  0x0 (by decide +kernel)
private def chunks0 : List (Chunk 0) := [
  cert0_0]
def rows0 := rowsFrom chunks0

theorem good0 : ∀ r ∈ rows0, good 0 r = true := rowsFrom_good chunks0

theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks0 0 (by decide +kernel)).1

theorem mass0 (i : Fin 59) :
    bandCount 0 (i.val : ℤ) 58 15 ≤ (rows0.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks0).filter _).length
  rw [mass_eq]
  have h : (List.range 59).all
      (fun j => decide (bandCount 0 (j : ℤ) 58 15 ≤ mass j chunks0)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total0 : (rows0.map (price 0)).sum = 106 :=
  (total_eq chunks0).trans (by decide +kernel)

private def cert1_0 := witnessA6966Final 1 3 0 64 64 1 106
  0x0 (by decide +kernel)
private def cert1_1 := witnessA6966Final 1 2 0 10001 10001 1 106
  0x0 (by decide +kernel)
private def cert1_2 := witnessA6966Final 1 1 0 20000 20000 1 106
  0x0 (by decide +kernel)
private def cert1_3 := witnessA6966Final 1 0 0 30000 30000 1 102
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

theorem mass1 (i : Fin 59) :
    bandCount 1 (i.val : ℤ) 58 15 ≤ (rows1.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks1).filter _).length
  rw [mass_eq]
  have h : (List.range 59).all
      (fun j => decide (bandCount 1 (j : ℤ) 58 15 ≤ mass j chunks1)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total1 : (rows1.map (price 1)).sum = 420 :=
  (total_eq chunks1).trans (by decide +kernel)

private def cert2_0 := witnessA6966Final 2 6 0 128 128 1 106
  0x0 (by decide +kernel)
private def cert2_1 := witnessA6966Final 2 5 0 10065 10065 1 106
  0x0 (by decide +kernel)
private def cert2_2 := witnessA6966Final 2 4 0 20002 20064 2 212
  0x0 (by decide +kernel)
private def cert2_3 := witnessA6966Final 2 3 0 30001 30064 2 208
  0x488 (by decide +kernel)
private def cert2_4 := witnessA6966Final 2 2 0 40000 40001 2 208
  0x488 (by decide +kernel)
private def cert2_5 := witnessA6966Final 2 1 0 50000 50000 1 102
  0x91 (by decide +kernel)
private def cert2_6 := witnessA6966Final 2 0 0 60000 60000 1 98
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

theorem mass2 (i : Fin 59) :
    bandCount 2 (i.val : ℤ) 58 15 ≤ (rows2.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks2).filter _).length
  rw [mass_eq]
  have h : (List.range 59).all
      (fun j => decide (bandCount 2 (j : ℤ) 58 15 ≤ mass j chunks2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total2 : (rows2.map (price 2)).sum = 1040 :=
  (total_eq chunks2).trans (by decide +kernel)

private def cert3_0 := witnessA6966Final 3 9 0 192 192 1 106
  0x0 (by decide +kernel)
private def cert3_1 := witnessA6966Final 3 8 0 10129 10129 1 106
  0x0 (by decide +kernel)
private def cert3_2 := witnessA6966Final 3 7 0 20066 20128 2 212
  0x0 (by decide +kernel)
private def cert3_3 := witnessA6966Final 3 6 0 30003 30128 3 314
  0x2440 (by decide +kernel)
private def cert3_4 := witnessA6966Final 3 5 0 40002 40065 3 314
  0x2440 (by decide +kernel)
private def cert3_5 := witnessA6966Final 3 4 0 50001 50064 3 310
  0x244488 (by decide +kernel)
private def cert3_6 := witnessA6966Final 3 3 0 60000 60064 3 306
  0x444488 (by decide +kernel)
private def cert3_7 := witnessA6966Final 3 2 0 70000 70001 2 200
  0x88891 (by decide +kernel)
private def cert3_8 := witnessA6966Final 3 1 0 80000 80000 1 98
  0x111 (by decide +kernel)
private def cert3_9 := witnessA6966Final 3 0 0 90000 90000 1 94
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

theorem mass3 (i : Fin 59) :
    bandCount 3 (i.val : ℤ) 58 15 ≤ (rows3.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks3).filter _).length
  rw [mass_eq]
  have h : (List.range 59).all
      (fun j => decide (bandCount 3 (j : ℤ) 58 15 ≤ mass j chunks3)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total3 : (rows3.map (price 3)).sum = 2060 :=
  (total_eq chunks3).trans (by decide +kernel)

private def cert4_0 := witnessA6966Final 4 12 0 256 256 1 106
  0x0 (by decide +kernel)
private def cert4_1 := witnessA6966Final 4 11 0 10193 10193 1 106
  0x0 (by decide +kernel)
private def cert4_2 := witnessA6966Final 4 10 0 20130 20192 2 212
  0x0 (by decide +kernel)
private def cert4_3 := witnessA6966Final 4 9 0 30067 30192 3 314
  0x2440 (by decide +kernel)
private def cert4_4 := witnessA6966Final 4 8 0 40004 40129 4 420
  0x12200 (by decide +kernel)
private def cert4_5 := witnessA6966Final 4 7 0 50003 50128 4 416
  0x1222440 (by decide +kernel)
private def cert4_6 := witnessA6966Final 4 6 0 60002 60128 5 514
  0x1111220488 (by decide +kernel)
private def cert4_7 := witnessA6966Final 4 5 0 70001 70065 4 408
  0x222244488 (by decide +kernel)
private def cert4_8 := witnessA6966Final 4 4 0 80000 80064 4 404
  0x222444488 (by decide +kernel)
private def cert4_9 := witnessA6966Final 4 3 0 90000 90064 3 294
  0x64488891 (by decide +kernel)
private def cert4_10 := witnessA6966Final 4 2 0 100000 100001 2 192
  0xc8911 (by decide +kernel)
private def cert4_11 := witnessA6966Final 4 1 0 110000 110000 1 94
  0x191 (by decide +kernel)
private def cert4_12 := witnessA6966Final 4 0 0 120000 120000 1 90
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

theorem mass4 (i : Fin 59) :
    bandCount 4 (i.val : ℤ) 58 15 ≤ (rows4.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks4).filter _).length
  rw [mass_eq]
  have h : (List.range 59).all
      (fun j => decide (bandCount 4 (j : ℤ) 58 15 ≤ mass j chunks4)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total4 : (rows4.map (price 4)).sum = 3570 :=
  (total_eq chunks4).trans (by decide +kernel)


end A6966FinalRankReceipt
end Merged_A6966FinalRankReceiptGroup0

end Merged_A6966FinalRankReceiptGroup0

-- merged module A6966FinalRankReceiptGroup58
section Merged_A6966FinalRankReceiptGroup58
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace A6966FinalRankReceipt
open K1_13_1_1 (bandCount)

private def cert58_0 := witnessA6966Final 58 58 0 1160000 1160206 100 376551
  0x0 (by decide +kernel)
private def cert58_1 := witnessA6966Final 58 58 100 1160207 1160515 100 337491
  0x0 (by decide +kernel)
private def cert58_2 := witnessA6966Final 58 58 200 1160516 1160966 96 281862
  0x0 (by decide +kernel)
private def cert58_3 := witnessA6966Final 58 57 0 1170000 1170208 100 352611
  0x1722e45c8b91722e45c8b91722e45c8b91722e45c8b91722645c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b11322e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8991722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b9 (by decide +kernel)
private def cert58_4 := witnessA6966Final 58 57 100 1170209 1170519 100 314055
  0x1722e45c8b91722e45c8b91622645c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8991722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b11322e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722645c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91722e45c8b91622645c8b91722e45c8b9 (by decide +kernel)
private def cert58_5 := witnessA6966Final 58 57 200 1170520 1170966 88 237132
  0x1022644c8991322644c8991722e45c8b91722e45c8b11322e45c8b91722e45c8b91722645c8b91722e45c8b91722e45c8b91622645c8b91722e45c8b91722e45c8b91722645c8b91722e45c8b91722e45c8b91722e45c8b11322e45c8b91722e45c8b91722e45c8b91722e45c8991722e45c8b91722e45c8b9 (by decide +kernel)
private def cert58_6 := witnessA6966Final 58 56 0 1180000 1180209 100 328419
  0x2724e49c9392724e49c9392724e49c9392724e49c9392724e498919171344e49c9392724e49c9392724e49c9392724e49c9392724e49c9392724e49c939161342e2c85c4d1392724e49c9392724e49c9392724e49c9392724e49c9392724e49c9392724e49c9312322e2689c9392724e49c9392724e49c9392724e49c9392724e49c9392724e49c9392724e49c939 (by decide +kernel)
private def cert58_7 := witnessA6966Final 58 56 100 1180210 1180523 100 290619
  0x2724e49c9392724e49c9392724e49c939161342e2c85c4d1392724e49c9392724e49c9392724e49c9392724e498919171344e49c9392724e49c9392724e49c9392724e49c9392724e4584d0b8b2171344e49c9392724e49c9392724e49c9392724e49c9392724e49c9312322e2689c9392724e49c9392724e49c9392724e49c9392724e49c9392724e4584d0b8b2171344e49c939 (by decide +kernel)
private def cert58_8 := witnessA6966Final 58 56 200 1180524 1180965 80 198387
  0x131044648c9192324645841119171342e2685c4d0b89a171342e268584d0b8b2171344e49c9392724e49c9312322e2689c9392724e49c9392724e4584d0b8b2171344e49c9392724e49c9392724e498919171344e49c9392724e49c9392724e49c939161342e2c85c4d1392724e49c9392724e49c9392724e49c9312322e2689c939 (by decide +kernel)
private def cert58_9 := witnessA6966Final 58 55 0 1190000 1190211 100 304542
  0x271346e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b9261342e4c85c8d1389a3726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726c4588d0b8b09b271644e268dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b9261342e4c85c8d1389a3726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b9 (by decide +kernel)
private def cert58_10 := witnessA6966Final 58 55 100 1190212 1190527 100 266868
  0x261342e4c85c8d1389a3726e4dc9b93726e4dc9b93726e4dc9b93622c4685c584d938b2271346e4dc9b93726e4dc9b93726e4dc9b93726e4984d0b932172344e268dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726c4588d0b8b09b271644e268dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4984d0b932172344e268dc9b93726e4dc9b93726e4dc9b93726e4dc9b93726e4dc9b93622c4685c584d938b2 (by decide +kernel)
private def cert58_11 := witnessA6966Final 58 55 200 1190576 1190965 72 164871
  0x30246208cc999332664584c41999172342e4685c8d0b91a172344c208588d0b8b09b271044e2689c4d1389a271344e268984d0b932172344e268dc9b93726e4dc9b93622c4685c584d938b2271346e4dc9b93726e4dc9b9261342e4c85c8d1389a3726e4dc9b93726e4dc9b93726c4588d0b8b09b271644e268dc9b93726e4dc9b93726e4dc9b9 (by decide +kernel)
private def cert58_12 := witnessA6966Final 58 54 0 1200000 1200212 100 281106
  0x17162364e2c26cdc591b89a4728e51ca394728e51ca394728e51ca394728e51ca394728c4988d0b9309b272644e468dc4d2394728e51ca394728e51ca394728e51ca394728e51ca394728e4d84d0b9b217162364e2c26cdc591b89a4728e51ca394728e51ca394728e51ca394728e51ca394728e51ca394624c4685c984d93932272346e2691ca394728e51ca394728e51ca394728e51ca394728e51ca394728e51ca39 (by decide +kernel)
private def cert58_13 := witnessA6966Final 58 54 100 1200213 1200579 100 245952
  0x4728e51ca394624c4685c984d93932272346e2691ca394728e51ca394728e51ca39361342e6c85c588d938b09b371646e2691ca394728e51ca394728e51ca394728c4988d0b9309b272644e468dc4d2394728e51ca394728e51ca394728e51ca39361342e6c85c588d938b09b371646e2691ca394728e51ca394728e51ca394728e51ca394624c4685c984d93932272346e2691ca394728e51ca394728e51ca394728e51ca394728e4d84d0b9b2 (by decide +kernel)
private def cert58_14 := witnessA6966Final 58 54 200 1200580 1200964 64 133497
  0x13304662090ca194322c608588c41a19173342e6685ccd0b99a26131062c6685c588d9389883272344e4689c8d1391a361044c4685c984d938b083272346e268dc4d1b89a371346e268d84d0b9b217162364e2c26cdc591b89a4728e51ca394728c4988d0b9309b272644e468dc4d2394728e51ca394728e4d84d0b9b217162364e2c26cdc591b89a4728e51ca39 (by decide +kernel)
private def cert58_15 := witnessA6966Final 58 53 0 1210000 1210214 100 258237
  0x5626c4685cd84d939b227162366e2c26d1c592389a572ae55cab9572ae55cab9572ae55cab9572ae55ca309a174642e4c46c9c984d9b932372348e2695cab9572ae55cab9572ae55cab9572ae55cab9572ae55cab1362342e6c26c9cd9138b11b37161368e2c91c4d2b9572ae55cab9572ae55cab9572ae55cab9572ae55cab95728c2685d190b9311b27261366e4c8dc8d2389a572ae55cab9572ae55cab9572ae55cab9572ae55cab9572ae55cab9 (by decide +kernel)
private def cert58_16 := witnessA6966Final 58 53 100 1210256 1210584 100 224346
  0x37161368e2c91c4d2b9572ae55cab95728c2685d190b9311b27261366e4c8dc8d2389a572ae55cab9572ae55cab95626c4685cd84d939b227162366e2c26d1c592389a572ae55cab9572ae55cab95728c2685d190b9311b27261366e4c8dc8d2389a572ae55cab9572ae55cab9572ae55cab1362342e6c26c9cd9138b11b37161368e2c91c4d2b9572ae55cab9572ae55cab9572ae55ca309a174642e4c46c9c984d9b932372348e2695cab9572ae55cab9572ae55cab9572ae55cab9 (by decide +kernel)
private def cert58_17 := witnessA6966Final 58 53 200 1210585 1210964 56 107359
  0x502466090c412995322c2660c58cc41a99174342e8685d0d1318226231062c8685c58cd9391883273344e6689ccd1b09883263342e4c46c9c584c421399a372346e468dc8d1b91a461046c4685cd84d939308327162366e2c26d1c412389a471348e2691c4d2309a174642e4c46c9c984d9b932372348e2695cab9572ae55cab1362342e6c26c9cd9138b11b (by decide +kernel)
private def cert58_18 := witnessA6966Final 58 52 0 1220000 1220257 100 237702
  0x672ce5584d0bab217362364e6c26cdcd91b8b11b4716136ae2c95c4d339672ce59cb39672ce59cb39672ce59cb396628c4685d184d93a3227262366e4c26d1c992391a57134ce59cb39672ce59cb39672ce59cb39672ce59cb39561342eac85cd88d939b09b373646e2c46d1c584dab8b257134ce59cb39672ce59cb39672ce59cb39672ce59cb39672cc5188d0ba309b274644e4c46cdc984da393247234ae2699cb39672ce59cb39672ce59cb39672ce59cb39672ce59cb39 (by decide +kernel)
private def cert58_19 := witnessA6966Final 58 52 100 1220258 1220588 100 201557
  0x561342eac85cd88d939b09b373646e2c46d1c584dab8b257134ce59cb39672cc5188d0ba309b274644e4c46cdc984da393247234ae2699cb39672ce59cb39561342eac85cd88d939b09b373646e2c46d1c584dab8b257134ce59cb39672ce59cb396628c4685d184d93a3227262366e4c26d1c992391a57134ce59cb39672ce59cb39672ce5584d0bab217362364e6c26cdcd91b8b11b4716136ae2c95c4d339672ce59cb39672ce59cb39672cc5188d0ba309b274644e4c46cdc984da393247234ae2699cb39672ce59cb39672ce59cb39 (by decide +kernel)
private def cert58_20 := witnessA6966Final 58 52 200 1220640 1220963 48 85472
  0x13504666094c41319165042c4660c590c41b19175342ea68984cc19319883165342e2c86c9ccc4193a1a274346c608d88c419321a17263364e2c462109d0d1b99a373346e669184c419b19a17362364e4c262109c58cd9b8b11b47131068e4691c8d2391a561048c4685d184d939b08327262366e4c26d1c5841a391a57134ae2695c4d2b89a (by decide +kernel)
private def cert58_21 := witnessA6966Final 58 51 0 1230000 1230259 100 217252
  0x772ee5dcbb9762ac4685d584d93ab227362366e6c26d1cd9238b11b5716136ce2c99c4d3b9772ee5dcbb9772ee5dcbb9772ee5984d0bb3217462364e8c26cdd191b9311b4726136ae4c95c8d3389a772ee5dcbb9772ee5dcbb9772ee5dcbb9772ec5588d0bab09b275644e6c46cdcd84da39b24716236ae2c26d9c593389a772ee5dcbb9772ee5dcbb9772ee5dcbb9772ee5984d0bb3217462364e8c26cdd191b9311b4726136ae4c95c8d3389a772ee5dcbb9772ee5dcbb9772ee5dcbb9772ee5dcbb9 (by decide +kernel)
private def cert58_22 := witnessA6966Final 58 51 100 1230260 1230644 100 181916
  0x4716131088e6695c8d2b91a57234cc209588d0bab09b27461064e6c46cdcd84da3930834716236ae2c26d9c413389a67134ce269984d0bb3217462364e8c26cdd191b9311b4726136ae4c95c8d3389a772ee5dcbb9762ac4685d584d93ab227362366e6c26d1cd9238b11b5716136ce2c99c4d3b9772ee5dcbb9661342ecc85d188d93a309b374646e4c46d1c984dab93257234ce269dcbb9772ee5dcbb9772ec5588d0bab09b275644e6c46cdcd84da39b24716236ae2c26d9c593389a772ee5dcbb9772ee5dcbb9661342ecc85d188d93a309b374646e4c46d1c984dab93257234ce269dcbb9772ee5dcbb9 (by decide +kernel)
private def cert58_23 := witnessA6966Final 58 51 200 1230645 1230963 40 65790
  0x70246a090cc13188216135062c6660c594c41b99176344ca08988cc19321883166342e2ca6c9d0c4193a9a36133066c6620c994d0b9321b2716331084ea68dd0d1ba1a463048c4620cd90d0b9b19b2726231084e2c86cdc58cda391883473348e669584c41a319a17462364e6c262109c98cd9b9311b (by decide +kernel)
private def cert58_24 := witnessA6966Final 58 50 0 1240000 1240261 100 197180
  0x8730e61cc398730e5d84d0bbb217562364eac26cdd591b9b11b4736136ae6c95c588db38b09b77164ee26a1cc398730e61cc398730e61cc31662342ecc26c9d9913a311b37461368e8c91c988dab9309b67264ce469dc4d4398730e61cc398730e61cc398730e5d84d0bbb217562364eac26cdd591b9b11b4736136ae6c95c588db38b09b77164ee26a1cc398730e61cc398730e61cc398730e618b311a17661364ecc89d188d9ba309b474648e4c46d5c984db393267234ee26a1cc398730e61cc398730e61cc398730e61cc39 (by decide +kernel)
private def cert58_25 := witnessA6966Final 58 50 100 1240262 1240649 100 164316
  0x56231068c8685d18cd939b1188427264366e4c66d1c588c4223a1a57334ae669984c41ab19a17562364e8c262109cd8cd9b9b11b4726131088e2c66d5c588db38988367234ce469d8413311a17661364eac20c9d188d9ba309b47361068e4c46d5c984db38b08367234ee269dc4d3b89a761342eec85d588d93ab09b375646e6c46d1cd84dab9b25716236ce2c26ddc593b89a8730e61cc31662342ecc26c9d9913a311b37461368e8c91c988dab9309b67264ce469dc4d4398730e61cc39761342eec85d588d93ab09b375646e6c46d1cd84dab9b25716236ce2c26ddc593b89a8730e61cc398730e618b311a17661364ecc89d188d9ba309b474648e4c46d5c984db393267234ee26a1cc39 (by decide +kernel)
private def cert58_26 := witnessA6966Final 58 50 200 1240650 1240962 32 49237
  0x1370466a094cc10b38216235062c8660c598c41c1926135064c6660c994c418b39a17166364ea620cd9411b1198336431064cc685c994d938b21884276346ea69184cc1a319883365342e6c86c9c98cc42138b29b37164368e6620d1d0d2b182 (by decide +kernel)
private def cert58_27 := witnessA6966Final 58 49 0 1250000 1250263 100 177760
  0x772350e26a5ccb99732e65ccb9962ec4685dd84d93bb227562366eac26d1d59239b11b5736136ce6c99c588dbb8b09b871650e26a5ccb99732e65ccb99730c2685e190bb311b27661366ecc8dd188da3a309b57464ae4c46d9c984dbb932772350e26a5ccb99732e65ccb99732e65ccb1762342eec26c9dd913ab11b37561368eac91cd88dab9b09b67364ce2c46ddc584dc38b2871352e65ccb99732e65ccb99732e65cc309a178642ecc46c9d984d9bb3237462368e8c26d5d192b9311b6726136ee4c9dc8d4389a9732e65ccb99732e65ccb99732e65ccb9 (by decide +kernel)
private def cert58_28 := witnessA6966Final 58 49 100 1250264 1250708 100 149459
  0x17365364e4c862109c598d9b8b29b4743106ac2660d58cc41a329a17464364e6c662109c994d9b9321b4716331088ea695d0d331826623106ac8685d58cd93a31188427364366e6c66d1c988c42238b21b5716336ce4620d9ccd3b09883663342ecc46c9d584c4213a319b37462368e6c262111c98cdab9311b671613108ce669dc8d3b91a86104ec4685dd84d93b308327562366eac26d1d1841a39b11b5736136ce4c20d9c588dbb8b09b871050e26a1c4d4309a178642ecc46c9d984d9bb3237462368e8c26d5d192b9311b6726136ee4c9dc8d4389a9732e65ccb1762342eec26c9dd913ab11b37561368eac91cd88dab9b09b67364ce2c46ddc584dc38b2871352e65ccb99730c2685e190bb311b27661366ecc8dd188da3a309b57464ae4c46d9c984dbb932 (by decide +kernel)
private def cert58_29 := witnessA6966Final 58 49 200 1250709 1250962 24 34735
  0x90246e090d410b09b8316335062ca660dcc811338226235064c8660c998c418b41a17731066c26a0cd8ccc19b29883267342e4cc6c9c594c4213b9a465048c4660d190c419b31a (by decide +kernel)
private def cert58_30 := witnessA6966Final 58 48 0 1260000 1260265 100 159758
  0x67464ce4c46ddc984dc3932872352e26a9cd39a734e6584d0bcb217762364eec26cddd91bab11b4756136aeac95cd88db39b09b77364ee2c46e1c584dcb8b2971354e69cd39a734e698c311a17861364f0c89d988d9bb309b476648e8c46d5d184db3a326726236ee4c26e1c994391a971354e69cd39a734e69cd39961342f2c85dd88d93bb09b377646eac46d1d584dabab25736236ce6c26ddcd93b8b11b87161372e2ca5c4d539a734e69cd39a734e69cd31862342f0c26c9e1913b311b37661368ecc91d188daba309b67464ce4c46ddc984dc3932872352e26a9cd39a734e69cd39a734e69cd39 (by decide +kernel)
private def cert58_31 := witnessA6966Final 58 48 100 1260266 1260769 100 136484
  0x1716731082f269184d41a31998346531066ce685cd98d93932988427167366ec620d59412b1198356431068cc685d194d939b2188427266366e4ca6d1c590c4223b1a6613306cc6620d594d0bab21b2746331084e6ca6cdcd90da393198844716536ae2c86d9ccc41bb1827623106cc8685d98cd93ab1188427464366e8c66d1cd88c42239321b5726336ce2c462119d0d3b99a8613106ec6685dd88d93b30988427563366eac46d1d184c42239b19b5736236ce4c262119c58cdbb8b11b87131070e46a58414311a17861364eec20c9d988d9bb309b47561068e8c46d5d184db39b0836726236ee4c26e1c5841c391a971352e26a584d0bcb217762364eec26cddd91bab11b4756136aeac95cd88db39b09b77364ee2c46e1c584dcb8b2971354e69cd31862342f0c26c9e1913b311b37661368ecc91d188daba309b (by decide +kernel)
private def cert58_32 := witnessA6966Final 58 48 200 1260770 1260961 16 22060
  0x1390466e085a410b11b831643506c6808984dc19319a8326533062ce640e4c411b38236235066c8660cd98c419341a (by decide +kernel)
private def cert58_33 := witnessA6966Final 58 47 0 1270000 1270267 100 143246
  0x4766136aecc95d188db3a309b77464ee4c46e1c984dcb932972354e26adcdb9b632c4685e584d93cb227762366eec26d1dd923ab11b5756136ceac99cd88dbb9b09b873650e2c46e5c584dd38b2a71356e6dcdb9a61342f4c85e188d93c309b378646ecc46d1d984dabb325746236ce8c26ddd193b9311b87261372e4ca5c8d5389ab736e6dcdb9b736c6588d0bcb09b279644eec46cddd84da3bb24756236aeac26d9d59339b11b77361370e6ca1c588dcb8b09ba71654e26adcdb9b736e6dcdb9a61342f4c85e188d93c309b378646ecc46d1d984dabb325746236ce8c26ddd193b9311b87261372e4ca5c8d5389ab736e6dcdb9b736e6dcdb9 (by decide +kernel)
private def cert58_34 := witnessA6966Final 58 47 100 1270268 1270833 100 125519
  0x166340706608d84dc19b19a8336533064ce640c5a4c41d99467048c46a0d190cc1a331883368342e4ce62105c5a4d93c18835613506ac6660d594c41a339a17466364e6ca62109c99cd9b8b3188437834cca09988cc1b321883566342eaca6c9d190c42139b31b37365368e4c862111c598daba98837613306ec6620d994d0bb321b2756331084e8ca6cdd190da39b198844726536ae4c86d9c58cc4233a9a863050c4620dd90d0bbb19b2766231084eac86cdd58cda3a3118844736436ae6c66d9c988c42338b21b77163370e4620e584c41c319a17862364eec262109d98cd9bb311b4756131088e8c66d5d188db39b098846726336ee4c46e1c584c424399a972354c20a588d0bcb09b27861064eec46cddd84da3b30834756236aeac26d9d1841b39b11b77361370e4c20e1c588dcb8b09ba71054e26a984d0bd3217862364f0c26cde191bb311b (by decide +kernel)
private def cert58_35 := witnessA6966Final 58 47 200 1270834 1270961 8 10818
  0xb0247208584e418b19b83536044d208988dc19321a83 (by decide +kernel)
private def cert58_36 := witnessA6966Final 58 46 0 1280000 1280269 100 128516
  0x27862366f0c26d1dd841a3b311b5766136ceac20d9d188dbba309b87361070e4c46e5c984dd38b083a72356e26ad84d0bdb217962364f2c26cde591bbb11b4776136aeec95d588db3ab09b77564ee6c46e1cd84dcb9b297162374e2c26edc595b89ac738c6988d0bd309b27a644f0c46cde184da3c324766236aecc26d9d9933a311b77461370e8ca1c988dcb9309ba72654e46adc4d639c738e6d84d0bdb217962364f2c26cde591bbb11b4776136aeec95d588db3ab09b77564ee6c46e1cd84dcb9b297162374e2c26edc595b89ac738e71ce39c634c4685e984d93d3227862366f0c26d1e1923b311b5766136cecc99d188dbba309b874650e4c46e5c984dd3932a72356e26b1ce39c738e71ce39 (by decide +kernel)
private def cert58_37 := witnessA6966Final 58 46 100 1280270 1280960 100 116725
  0x13b042d608588e41a1c0226139064c66e0c594d81b9a82369046c46e0cd90d419331a03168330746409184dc1a319a8346533066ce640c9a4c418b59a17a3106ace09588d41ab2198356631068d0685cd9cc420b9349b2716831084f469984d41b3199836653106ace685d598d93a32988427367366e4cc6210dc5a0da3b988376504ec4660dd90c41b331a17665364eac862109d198d9ba329b4736431088e4cc6d5c594c422bb9a86133070c6620dd94d0bbb21b2766331084eaca6cdd590da3a3198844736536ae6c86d9c98cc42338b29b77431072c60a588c41c321a17863364eec462109d990d9bb319b4756231088e8c86d5d18cdb39b118846726436ee4c66e1c588c4243a1aa6131072c6685e588d93c30988427763366eec46d1d984c4223ab19b5756236ce8c262119cd8cdbb9b11b8726131090e2c66e5c588dd389883b61054c4685e984d93cb083 (by decide +kernel)
private def cert58_38 := witnessA6966Final 58 45 0 1290000 1290271 100 115387
  0xa63342f4c46c9e584c4213c319b37862368eec262111d98cdabb311b675613108ce8c66ddd188dc39b0988487263372e4c46e9c584c425399ac61056c4685ed84d93d308327962366f2c26d1e1841a3bb11b5776136cecc20d9d588dbbab09b87461070e6c46e5cd84dd393083a7162376e2c26f1c416309a17c642f4c46c9e984d9bd3237862368f0c26d5e192bb311b6766136eecc9dd188dc3a309b974652e4c46e9c984ddb932b72358e26b5ceb1b62342f6c26c9ed913cb11b37961368f2c91dd88dabbb09b67764ceac46ddd584dc3ab287362372e6c26e9cd9538b11bb7161378e2cb1c4d6b9d738c2685f190bd311b27a61366f4c8de188da3c309b57864aecc46d9d984dbbb3277462370e8c26e5d194b9311ba7261376e4cadc8d6389ad73ae75ceb9 (by decide +kernel)
private def cert58_39 := witnessA6966Final 58 45 100 1290272 1290960 92 99594
  0xd022c2760cce811358226239062c8700d8dc11b09c8336337064ca6c0c59cd41c9a02469048c46e0d190d419b31a0326833062d4640f0c412b09b835633506aca660d19cc819b4988326b342e2d462105f0d333826623506cc8660d998c41ab41a1746731082e6d26c9c9a0c42138b51b3793106ec26a0dd8ccc1bb29883667342eccc6c9d594c4213a339b3736631086e4d06d1c59cc4223c9a865050c4660e190c41bb31a17765364ecc862109d598d9bab29b4746431088e6cc6d5c994c422b8b39b67631072c2660e58cc41c329a17864364eec662109d994d9bb321b4756331088e8ca6d5d190db39b198846726536ee2c86211dd8d53182a6231072c8685e58cd93c31188427764366eec66d1d988c4223ab21b5756336ce8c462119cd90dbb9b19b8726231090e2c86e5ccc41db09883 (by decide +kernel)
private def cert58_40 := witnessA6966Final 58 44 0 1300000 1300320 100 104032
  0x87531076c60ad88c41d321a17a63364f2c462109e190d9bc319b4776231088ecc86d5d98cdb3ab118846746436ee8c66e1cd88c42439321b9716331092ea6b184c41db19a17b62364f4c262109e58cd9bcb11b4786131088eec66d5dd88db3b3098846756336eeac46e1d184c42439b19b97362374e4c262129c58cddb91883d61058c4685f184d93db08327a62366f4c26d1e5841a3c311b5786136ceec20d9d988dbbb309b87561070e8c46e5d184dd39b083a7262376e4c26f1c5841e391ad61342fac85ed88d93db09b37b646f2c46d1e584dabcb25776236ceec26dddd93bab11b87561372eaca5cd88dd39b09bb73656e2c46f1c584deb8b2d7135cc7188d0be309b27c644f4c46cde984da3d324786236af0c26d9e1933b311b77661370ecca1d188dcba309ba74654e4c46edc984de3932c7235ae26b9cf39 (by decide +kernel)
private def cert58_41 := witnessA6966Final 58 44 100 1300321 1300897 84 84101
  0x16d0447808984ec18b19d03539046d608d88e419321c03166370706c09184e41a319b8336536064ce6a0c5a4d01d998256904ac46e0d590d41a331a0336833064d4640c5b0c41f196613706cc66a0d994cc1ab3990346931066d6685c9a8c420b8b61b27b3106ece09d88d41bb219837663106cd0685d59cc420ba349b2736831084e4d46cdc5a4c421bd9a86135070c6660e194c41bb39a17766364ecca62109d59cd9ba33188437368368e4ce62111c5a4dabc1883965052c4660e590c41c331a17865364eec862109d998d9bb329b4756431088e8cc6d5cd94c422b9339b671663108cf06a984cc1d319883965342f2c86c9e18cc4213bb29b37764368ecc662111d594dabab21b674633108ce6ca6ddc990c423b8b31b (by decide +kernel)
private def cert58_42 := witnessA6966Final 58 43 0 1310000 1310323 100 94189
  0x5736736ce4cc62119c5a0dbbb9883b6133076c6620e994d0bd321b2796331084f0ca6cde190da3bb198844766536aecc86d9d58cc4233a329b773643108ee4cc6e1c594c4243b9ac63058c4620ed90d0bdb19b27a6231084f2c86cde58cda3c3118844776436aeec66d9d988c4233ab21b77563370e8c462121cd90dcb931988497165374e8620f584c41e319a17c62364f6c262109e98cd9bd311b4796131088f0c66d5e188db3bb098846766336eecc46e1d584c4243a319b97462374e6c262129c98cddb8b11884b7435cc20b588d0beb09b27c61064f6c46cded84da3d30834796236af2c26d9e1841b3bb11b77761370ecc20e1d588dcbab09ba7461074e6c46edcd84de393083c716237ae2620f984d0bf3217c62364f8c26cdf191bd311b47a6136af4c95e188db3c309b77864eecc46e1d984dcbb3297462374e8c26edd195b9311bc726137ae4cb5c8d7389a (by decide +kernel)
private def cert58_43 := witnessA6966Final 58 43 100 1310324 1310896 76 70396
  0x13e044da08588f01a1d823613b064c6740c594e41b9c0246b048c4720cd90e019331b83168360746a09584e41ab19b8346536066ce6a0c9a4d018b59983d3204cd209988dc1b321a8356634068d0660cda8c81936188316e342fa620dd84dc1bb19a837653306cce640d5a4c41a359a1736a31082e4d86c9c5acc4213e9a867050c46a0e190cc1c331883768342ecce62105d5a4d93a3418842736a366e4d26210dc5acda3d188396135072c6660e594c41c339a17866364eeca62109d99cd9bab3188437468368e6ce62111c9a4dab8b4188457a354ca0a988cc1d321883966342f2ca6c9e190c4213bb31b37765368ecc862111d598daba329884 (by decide +kernel)
private def cert58_44 := witnessA6966Final 58 42 0 1320000 1320325 100 85219
  0x37568368e8ce62111cda4dab93418845716a36cf2620ed9415b11983b6431074cc685e994d93cb2188427866366f0ca6d1dd90c4223b331b575653108ae8ce6d9cd98c42339341b771673108ef26b184cc1e319883b65342f6c86c9e98cc4213cb29b37964368f0c662111dd94dabbb21b676633108ceaca6ddd190c423b9b31b8726531090e2ce6e5d8c41eb182d6231078c8685f18cd93db1188427a64366f4c66d1e588c4223c321b5786336ceec462119d990dbbb319b8756231090e8c86e5cd8cc424b9329ba716431094ec6b984c41eb19a17d62364f8c262109ed8cd9bdb11b47a6131088f2c66d5e588db3c3098846776336eeec46e1d984c4243ab19b97562374e8c262129cd8cddb9311884b7164378e6620fd8417311a17e61364fac20c9f188d9be309b47b61068f4c46d5e984db3cb0836786236ef0c26e1dd841c3b311b97661374eac20e9d188ddba309bc7361078e4c46f5c584c426b99a (by decide +kernel)
private def cert58_45 := witnessA6966Final 58 42 100 1320326 1320896 69 59481
  0x80011613e0667a08db411311e031643b06c7409184ec19b19d0326539062ce700e4dc12b58256239068c8700cd98dc19341b0316a350786809984e41b319b8356536068ce6a0cda4d01935998316d3207e6209da413b11b837643506ccc680d5a0cc1a35190336c31064dc685c5b4c420bf9a86137070c66a0e194cc1bb399036693106ad6685d1a8c420b9b61b2726b31084e2da6cdf0c41cb38296235072c8660e598c41c341a1776731082ecd26c9d5a0c4213a351b3736931086e4d66d1c5a8c4223e1aa6135074c6660e994c41cb39a17966364f0ca62109dd9cd9bb331884 (by decide +kernel)
private def cert58_46 := witnessA6966Final 58 41 0 1330000 1330328 100 76857
  0x1786731082eed26c9d9a0c4213ab51b3746931086e6d66d1c9a8c42238b61b57b31076c26a0ed8ccc1db29883a67342f4cc6c9e594c4213c339b3776631086ecd06d1d59cc4223a349b573683108ae4d46d9c5a4c4233d9ac65058c4660f190c41db31a17b65364f4c862109e598d9bcb29b4786431088eecc6d5d994c422bab39b674663108ce6d06ddc99cc423b8b49b8783107ac2660f58cc41e329a17c64364f6c662109e994d9bd321b4796331088f0ca6d5e190db3bb198846766536eeac86211dd198dc39b2988487267372e2cc62125e0d73182e623107ac8685f58cd93e31188427b64366f6c66d1e988c4223cb21b5796336cf0c462119dd90dbbbb19b8766231090eac86e5d18cc424b9b29ba726431094e2cc6edd4c41fb09883e63342fcc46c9f584c4213e319b37c62368f6c262111e98cdabd311b679613108cf0c66dde188dc3bb0988487663372ecc46e9d584c4253a319bb736231096e4c86f1c58cc4263a9a (by decide +kernel)
private def cert58_47 := witnessA6966Final 58 41 100 1330329 1330833 61 49157
  0xb200088fc11309f031633d06a78091b411b11e032643b062cc740e0e412b09d834633a066ca720c99ce018b49b83b3604cd609988e41ab21c0346637066d06c0c9a8d418b61a03e3304ec2720dd8cdc1b329b0356735068d2680cdaccc1936990316f31068819869050c46e0e190d41bb31a036683306ad4640d1b0c419b71a1726d31082e2de6c9f8c41cb09b8396335072ca660e19cc81bb4988366b342ead462105d1b0d939b598842726d366e2d86210df8d53382a6235074c8660e998c41cb41a (by decide +kernel)
private def cert58_48 := witnessA6966Final 58 40 0 1340000 1340330 100 69149
  0xa6533072ce640e1a4c41bb59a1766a31082ead86c9d1acc42139b69b3726c31086e2dc6d1f4c41db382b6235076c8660ed98c41d341a1796731082f0d26c9dda0c4213b351b3756931086e8d66d1cda8c42239361b5716b3108afa6b184d41e319983c6531076ce685ed98d93d32988427967366f0cc6210ddda0da3b3398844756936ae8d062115cda8db393498846716b36ef4620f59416b11983d6431078cc685f194d93db2188427a66366f4ca6d1e590c4223c331b577653108aecce6d9d598c4233a341b773673108ee4d26e1c5a0c4243d1ae613307cc6620f594d0beb21b27c6331084f6ca6cded90da3d3198844796536af2c86d9e18cc4233bb29b776643108eeacc6e1d194c42439b39b9726631092e2d06e9dcc41fb182f623107cc8685f98cd93eb1188427c64366f8c66d1ed88c4223d321b57a6336cf2c462119e190dbbc319b8776231090ecc86e5d58cc424ba329ba736431094e4cc6edc594c425bb9a (by decide +kernel)
private def cert58_49 := witnessA6966Final 58 40 100 1340331 1340832 54 40990
  0x4d10044c80021623f0687c08d84f819319e831653c06e76095b412311e033643b064cc740c5a0e41d1c026613b06ac6740d194e419b39c0326937062d66c0f4d413b5827623906cc8700d598dc1a341b0336a35064d8680c5b8cc1a00640a184e41c319b837653606cce6a0d5a4d01a35998336d32064de620c5910342e801883969052c46e0e590d41c331a037683306cd4640d5b0c41a371a1736d31082e4de6c9c5b8c4213a006a984dc1d319a83 (by decide +kernel)
private def cert58_50 := witnessA6966Final 58 39 0 1350000 1350384 100 62435
  0x17480d53482a6237074c86a0e598d01c34198376a3206cd8620d5b8d0ba3698841736f364e4dc62109c5900366fe620ed84dc1db19a83b6533074ce640e5a4c41c359a1776a31082ecd86c9d5acc4213a369b3736c31086e4dc6d1c5b4c4223f9ac67058c46a0f190cc1e331883b68342f4ce62105e5a4d93c3418842776a366ecd26210dd5acda3a3518844736c36ae4d662115c5b4db3e1883d613507ac6660f594c41e339a17c66364f6ca62109e99cd9bcb3188437868368eece62111d9a4dabab418845746a36ce6d262119c9acdbb8b5188477c35cca0b988cc1f321883d66342faca6c9f190c4213db31b37b65368f4c862111e598dabc3298845776736ceccc62119d5a0dbba33988477369370e4d062121c5a8dcbc9883f613307ec6620f994d0bf321b27d6331084f8ca6cdf190da3db1988447a6536af4c86d9e58cc4233c329b777643108eeccc6e1d594c4243a339b9736631092e4d06e9c59cc4253c9a (by decide +kernel)
private def cert58_51 := witnessA6966Final 58 39 100 1350385 1350832 47 33685
  0x98011613440199a0008d900044c47e0c590f81b1e824613e066c67a0c994f018b39d8393a04cda09588f01a321d833663a064d0720c5a8e01e1b827613b06cc6740d594e41a339c0336937064d66c0c5b4d41f9a0286b050c4720dd90e01b331b8356836068d46a0cdb0d01937198316400c81a40620a584e41cb19b838653606ece6a0d9a4d01ab5998346d32066de620c9910342e2c801884 (by decide +kernel)
private def cert58_52 := witnessA6966Final 58 38 0 1360000 1360387 100 56360
  0xdb8cc193200640c59203106a019a6139074c66e0e594d81c339a837693406cd6660d5b4c81a37988336440d0b9320062105c5920364e881883b69056c46e0ed90d41d331a0396833070d4640ddb0c41b371a1756d31082e8de6c9cdb8c4213932006cdc5bcc421ba206b184dc1e319a83c6533076ce640e9a4c41cb59a1786a31082eed86c9d9acc4213ab69b3746c31086e6dc6d1c9b4c42238b79b57e3107ace0b588d41eb21983d6631078d0685ed9cc420bd349b2796831084f0d46cddda4c421bb359b4756a31088e8d86d5cdacc422b9369b6716c3108cfc6b984d41f319983e653107ace685f598d93e32988427b67366f4cc6210de5a0da3c3398844776936aecd062115d5a8db3a3498846736b36ee4d46211dc5b0dc3d9883f6505ec4660fd90c41f331a17e65364fac862109f198d9be329b47b6431088f4cc6d5e594c422bc339b677663108cecd06ddd59cc423ba349b8736831090e4d46e5c5a4c424bd9a (by decide +kernel)
private def cert58_53 := witnessA6966Final 58 38 100 1360388 1360769 40 27101
  0x164c0111a4008984d10062c66800353f048c80023623f064c87c0c598f41c1e025613e068c67a0cd94f019339d831693a0767209db413311e035643b068cc740cda0e419351c0316c3707c6c0a184ec1bb19d036653906ace700d1a4dc19b59b0326d35062de680d1033052d60a588e41c321c037663706cd06c0d5a8d41a361a03 (by decide +kernel)
private def cert58_54 := witnessA6966Final 58 37 0 1370000 1370390 100 51109
  0x199ce01ab49b8346b36066da6a0c9bcd018b220660d3032054d60a988e41cb21c038663706ed06c0d9a8d41ab61a0346e33066c80190326480c418b280685d3031076c2720ed8cdc1d329b0396735070d2680ddaccc1b36990356f31068c881a1736400c420b932406c9c591031084e981ac69058c46e0f190d41db31a03a6833072d4640e1b0c41bb71a1766d31082eade6c9d1b8c42139b2006cdc9bcc421b8b2206d1d003107ac26e0f58cd41eb29983c6732076d2620e9acd0bcb518841786c364eed662109d9b4d9bab618843746e368e6da62111c9bcdab8b7188457400d73382e623507cc8660f998c41eb41a17c6731082f6d26c9e9a0c4213cb51b3786931086eed66d1d9a8c4223ab61b5746b3108ae6da6d9c9b0c42338b71b77d3107ec26a0fd8ccc1fb29883e67342fccc6c9f594c4213e339b37b6631086f4d06d1e59cc4223c349b577683108aecd46d9d5a4c4233a359b7736a3108ee4d86e1c5acc4243e9a (by decide +kernel)
private def cert58_55 := witnessA6966Final 58 37 100 1370391 1370768 33 21259
  0x9a80089930042c4690034344011b09a200c98cd00062ca7e0dcf812b20009188fc19b21f032663d062d0780e8ec13309f035633d068ca780cd9cec19349d0316b3907a700a1b413b11e036643b06acc740d1a0e419b51c0326c37062dc6c0d0035052c2760e18ce81bb29c83 (by decide +kernel)
private def cert58_56 := witnessA6966Final 58 36 0 1380000 1380393 100 46486
  0x25b414311e037643b06ccc740d5a0e41a351c0336c37064dc6c0c59003506901a02a613b072c6740e194e41bb39c036693706ad66c0d1b4d419b79a0326440cc18b260640d5031056d60ad88e41d321c0396637070d06c0dda8d41b361a0356e33068c80190336480c4193280685c593031082ea81ac6139078c66e0ed94d81d339a8396934070d6660ddb4c81b37988356440d0ba320062105cd920364e4c88188427164c0d9ba40620f5a416b11b83d6435078cc680eda0cc1d35190396c31070dc685ddb4c420bb379b2756e31084e8c801b3736f31086e4c881b4716400c4223a406b984dc1f319a83e653307ace640f1a4c41db59a17a6a31082f2d86c9e1acc4213bb69b3766c31086eadc6d1d1b4c42239b79b5726e3108ae2c801b67f3107ece0bd88d41fb21983f663107cd0685f59cc420be349b27b6831084f4d46cde5a4c421bc359b4776a31088ecd86d5d5acc422ba369b6736c3108ce4dc6ddc5b4c423bf9a (by decide +kernel)
private def cert58_57 := witnessA6966Final 58 36 100 1380448 1380768 27 16614
  0xb0011613500199a6008d930044c46900316434401b1a0009184d10066c6680032653f062ce7c0e4f413320009588fc1a321f033663d064d0780c5a8ec1e1d027613e06cc67a0d594f01a339d833693a064d6720c5b4e01f9b82 (by decide +kernel)
private def cert58_58 := witnessA6966Final 58 35 0 1390000 1390451 100 42628
  0x3683c064d4760c5b0e81f1c828613e06ec67a0d994f01ab39d834693a066d6720c9b4e018b79b83440d81536829623c070c8760dd98e81b341c8356a38068d86e0cdb8d81932006a0c59203406a01982b613b074c6740e594e41c339c037693706cd66c0d5b4d41a379a0336440cc193260640c59503106b819c6b058c4720ed90e01d331b8396836070d46a0ddb0d01b37198356400c81a3240620cd940342e4c9818841716540d93a80620f584e41eb19b83c6536076ce6a0e9a4d01cb5998386d3206ede620d9910342eac8018841746480d939b22062109c9930366e2c90188437500d73482e623707cc86a0f598d01e341983b6a32074d8620e5b8d0bc3698841776f364ecdc62109d5900366e8de6210dcd910368e4c8018844716480daba20620fd84dc1fb19a83f653307cce640f5a4c41e359a17b6a31082f4d86c9e5acc4213c369b3776c31086ecdc6d1d5b4c4223a379b5736e3108ae4c801b6716f3108ce881a (by decide +kernel)
private def cert58_59 := witnessA6966Final 58 35 100 1390452 1390705 20 11675
  0x16580111aa008984d40062c6698035348012326008d88d20064c86880316634001c1f8256134401a319a000cd94fc19339f031693d0767809d90004cc47e0d590f81a331e83 (by decide +kernel)
private def cert58_60 := witnessA6966Final 58 34 0 1400000 1400454 100 39199
  0x66134401ab19a000d194fc19b39f032693d062d6780f4ec14320009d88fc1b321f035663d068d0780cda8ec19361d0316e3906801c029613e070c67a0dd94f01b339d835693a068d6720cdb4e019379b8316440d81a606a0adb415311e039643b070cc740dda0e41b351c0356c37068dc6c0cd90035064c901a0316500cc1ac0640b184ec1db19d03a6539072ce700e1a4dc1bb59b0366d3506ade680d191033066c98190326540c418b2e0685d603107ad60b588e41e321c03b6637074d06c0e5a8d41c361a0376e3306cc80190356480c41a3280685cd93031082e4ca81b2716500c4213ac06b984e41f319b83d6536078ce6a0eda4d01d35998396d32070de620dd910342ecc8018841756480d93a322062109cd930366e4c9018843716500da3a60620fda417b11b83f643507ccc680f5a0cc1e351903b6c31074dc685e5b4c420bc379b2776e31084ecc801b3756f31086e8c881b4736400c4223932406d5c59103108ae981a (by decide +kernel)
private def cert58_61 := witnessA6966Final 58 34 100 1400512 1400704 14 7827
  0x4d70044cb00216235401a1a8008d84d40064c66980316534801b9a20095930048c469003364344019331a000c5a0fc1d1f02 (by decide +kernel)
private def cert58_62 := witnessA6966Final 58 33 0 1410000 1410515 100 36373
  0x36334c019329a400c59cd1007268002664c012b11a400d190d10066cc680032683f062d47c0f0f413b09a200d98cd0006aca7e0d19cf819b49e8326b3c062da760fce814b2000a188fc1bb21f036663d06ad0780d1a8ec19b61d0326e39062c801c03480dc15309f039633d070ca780dd9cec1b349d0356b39068da700cdbcdc1932206c0c59303506a81a02c6d056c4780e990ec1cb31d038683906ed4700d9b0dc1ab71b0346400d419b240680c994033062cb01903600c416b09d83c633a076ca720e99ce01cb49b8386b3606eda6a0d9bcd01ab220660d193032066ca81883265c0d0b8b2c062105d8035cd60b988e41eb21c03c6637076d06c0e9a8d41cb61a0386e3306ec80190366480c41ab280685d193031082e6ca81b2726500c42138b2c06cdd503107ec2720fd8cdc1f329b03d6735078d2680edaccc1d36990396f31070c881a1776400c420bb32406c9d591031084e8c981b3736480c421b932806d1c593031088ea81a (by decide +kernel)
private def cert58_63 := witnessA6966Final 58 33 100 1410516 1410704 8 4325
  0x64008b09ae00ccd60046cb002262354018b21a800d8d30048c26a003 (by decide +kernel)
private def cert58_64 := witnessA6966Final 58 32 0 1420000 1420578 100 33879
  0x26135c018b19ac00d4d50048cb002362354019321a800c598d300706900256135001a319a600cd94d20064ce6880316934001d9f82764c013311a400d590d10068cc680033683f064d47c0c5b0f41f1e0286134401bb19a000d994fc1ab39f034693d066d6780c9b4ec18b79d03440e41532000a588fc1c321f037663d06cd0780d5a8ec1a361d0336e39064c801c0316480dc1a806c0ad84f81d319e839653c070ce760dda4e81b359c8356d38068de6e0cd91036064c981a8316540d01ae0660b5b416311e03b643b074cc740e5a0e41c351c0376c3706cdc6c0d590035068c901a0336500cc1932c0640c59803106d019e613b07ac6740f194e41db39c03a6937072d66c0e1b4d41bb79a0366440cc1ab260640d195031066cb81a1726580c420b8b3006c9d703107ed60bd88e41f321c03d6637078d06c0eda8d41d361a0396e33070c80190376480c41b3280685d593031082e8ca81b2736500c4213932c06cdc595031086eb81a (by decide +kernel)
private def cert58_65 := witnessA6966Final 58 32 100 1420640 1420641 2 1056
  0x59900446c002 (by decide +kernel)
private def cert58_66 := witnessA6966Final 58 31 0 1430000 1430640 96 29958
  0x4da0044cc80216236001a1ae008d84d70064c66b00316535401b9a80095960048c46a803364350019331a600c5a0d200746880266135001ab19a600d194d20066ce68803269340018b59f83d3e050c980276234801b321a200d598d00068d07e0cda8f819361e8316e3c06801d8296134401c319a000dd94fc1b339f035693d068d6780cdb4ec19379d0316440e41a60700ad900054c47e0e590f81c331e837683c06cd4760d5b0e81a371c8336400e01932406e0c59403606b01a82c613e076c67a0e994f01cb39d838693a06ed6720d9b4e01ab79b8346440d819b2606a0c995034062cb81983640c8173682d623c078c8760ed98e81d341c8396a38070d86e0ddb8d81b32006a0d592034068ca0198336580c8193300620c59a0342ec81883f613b07cc6740f594e41e339c03b6937074d66c0e5b4d41c379a0376440cc1b3260640d595031068cb81a1736580c420b933006c9c597031084ec81a (by decide +kernel)
private def cert58_67 := witnessA6966Final 58 30 0 1440000 1440640 91 25867
  0x38004584da00666c8023664011311b000c590d7006c6b00246135c019b19ac00c994d50062ce6a003934c01332c009588d50068c86a00336634c019341a400c5a8d100786800276135001b319a600d594d20068ce68803369340019359f8316d3e07e7a0a5930050c46900376434401b331a000d5a0fc1a351f0336c3d064dc780c59003b06901d02a6134401cb19a000e194fc1bb39f036693d06ad6780d1b4ec19b79d0326440e418b260700d5037058c8002b623f074c87c0e598f41c341e0376a3b06cd8740d5b8e41a3200700cd92037064ca01b0316580d41b00680b584f81e319e83b653c074ce760e5a4e81c359c8376d3806cde6e0d591036068c981a8336540d01932e0660c59903206d81882f6d05cc4780f590ec1e331d03b6839074d4700e5b0dc1c371b0376400d41b3240680d594033068cb0190336600c4193340685c599031082ed81a (by decide +kernel)
private def cert58_68 := witnessA6966Final 58 29 0 1450000 1450577 85 21880
  0xb380088db0044c26d00316336401a9b00091990046c46c00326435c018b31ac00e0d5004ac26b803463358019b29aa00c99cd40062d269803b348013b2c009988d5006ac86a00346634c019b41a400c9a8d10062d868003e3f050c26a00376334c01b329a400d59cd10068d26800336b3f064da7c0c5bcf41a20780a9930052c46900386434401bb31a000d9a0fc1ab51f0346c3d066dc780c99003b062c901d03500e415b09a200e98cd00072ca7e0e19cf81bb49e8366b3c06ada760d1bce819b220720c993038062ca81b835c0d816b2000b188fc1db21f03a663d072d0780e1a8ec1bb61d0366e3906ac801c0346480dc19b2806c0c996035062cc01a03680cc17309f03d633d078ca780ed9cec1d349d0396b39070da700ddbcdc1b32206c0d593035068ca81a03365c0cc193320640c59b03106e819 (by decide +kernel)
private def cert58_69 := witnessA6966Final 58 28 0 1460000 1460576 80 18605
  0x4dd0044ce00216236c01a1b4008d84da0064c66c80316536001b9ae0095990048c46c00336435c019331ac00c5a0d500746a00266135c01ab19ac00d194d50066ce6a00326934c018b59a400f4d10050cb00276235401b321a800d598d30068d06900336a344019361a000c5b8fc1a007c0a584d40070c66980376534801b339a200d5a4d00068d67e0cdb4f819379e8316440f01a60760ad930054c46900396434401c331a000dda0fc1b351f0356c3d068dc780cd9003b064c901d0316500e41ac0700b184d10076c668003a653f072ce7c0e1a4f41bb59e0366d3b06ade740d191039066c981c0326540dc18b2e06c0d903505cc8002d623f078c87c0ed98f41d341e0396a3b070d8740ddb8e41b3200700d592037068ca01b0336580d4193300680c59a03306e01902 (by decide +kernel)
private def cert58_70 := witnessA6966Final 58 27 0 1470000 1470576 75 15755
  0x3e004584dd00666e0023670011311b600c590da006c6c802461368019b19b200c994d80062ce6b8039358013332009588d80068c86b803366358019341aa00c5a8d400786980276135c01b319ac00d594d50068ce6a00336934c019359a400c5b4d1007e680029658014311aa00dd90d4006ccc6980356834801a351a200cdb0d00064dc7e0c59003e06901e82a6135001cb19a600e194d2006ece6880366934001ab59f8346d3e066de7a0c99103c062c981d83540e81632600ad88d20074c86880396634001c341f8376a3e06cd87a0d5b8f01a3200760cd9203a064ca01c8316580e01b006e0b584d10078c668003b653f074ce7c0e5a4f41c359e0376d3b06cde740d591039068c981c0336540dc1932e06c0c59903506d81a02 (by decide +kernel)
private def cert58_71 := witnessA6966Final 58 26 0 1480000 1480513 70 13090
  0x59f00446f002261374018b19b800d4db0048ce00236236c019321b400c598d900706c00256136801a319b200cd94d80064ce6b80316935801d9aa009d99004cc46c00356435c01a331ac00cda0d50064d46a00316c34c01f1a400a184d7006ec66b00366535401ab39a800d1a4d30066d66900326d344018b79a000d103f054cb00296235401c321a800dd98d3006cd06900356a34401a361a000cdb8fc1932007c0c59203d06a01e02b6135001d319a600e594d20070ce6880376934001b359f8356d3e068de7a0cd9103c064c981d8316540e81ae0720b5930058c469003b6434401d331a000e5a0fc1c351f0376c3d06cdc780d59003b068c901d0336500e41932c0700c59803706d01b02 (by decide +kernel)
private def cert58_72 := witnessA6966Final 58 25 0 1490000 1490512 65 10810
  0x9c000899f0042c46f0034374011b09ba00c98cdc0062ca6d8037368012b38009188db0066c86d003266364018b41b000e8d7004cc26d00356336401a329b000cd9cd70064d26b00316b35401e9a800a199004ec46c00366435c01ab31ac00d1a0d50066d46a00326c34c018b71a400d00344014b09ae00e18cd6006eca6a80366735001ab49a600d1acd20066da6880326f340018b2207e0d303e056cb002a6235401cb21a800e198d3006ed06900366a34401ab61a000d1b8fc19b2007c0c99203d062ca01e03580ec16309a800ed8cd30074ca6900396734401c349a000ddacfc1b369f0356f3d068c881e03364c0ec1932a0740c59703906c81c02 (by decide +kernel)
private def cert58_73 := witnessA6966Final 58 24 0 1500000 1500512 61 8971
  0x44004584e000666f802367c011311bc00c590dd006c6e002461374019b19b800c994db0062ce6d0039364013338009588db0068c86d003366364019341b000c5a8d700786b00276136801b319b200d594d80068ce6b803369358019359aa00c5b4d4007e698029664014311b000dd90d7006ccc6b00356835401a351a800cdb0d30064dc6900316400d1006901a000a984d70072c66b00386535401bb39a800d9a4d3006ad66900346d344019b79a000c99103f062c981f03540f41632c00ad88d50074c86a00396634c01c341a400dda8d1006cd86800356e3f068c801f0336480f4193280780c59603b06c01d02 (by decide +kernel)
private def cert58_74 := witnessA6966Final 58 23 0 1510000 1510449 56 7178
  0x5a2004470802261380018b19be00d4de0048cf802362378019321ba00c598dc00706d80256137401a319b800cd94db0064ce6d00316936401d9b0009d9c004cc46d80356436801a331b200cda0d80064d46b80316c35801f1aa00a184da006ec66c80366536001ab39ae00d1a4d60066d66a80326d350018b79a600d1034801533200a588d80070c86b80376635801b341aa00d5a8d40068d86980336e34801932006880316480d0006a01f82b6135c01d319ac00e594d50070ce6a00376934c01b359a400d5b4d10068de6800336440fc1932607c0c59503d06b81e02 (by decide +kernel)
private def cert58_75 := witnessA6966Final 58 22 0 1520000 1520448 52 5762
  0x4e30044d100216238401a1c0008d84e00064c66f80316537801b9ba00959f0048c46f003364374019331b800c5a0db00746d00266137401ab19b800d194db0066ce6d003269364018b59b000f4d70050ce00276236c01b321b400d598d90068d06c00336a35c019361ac00c5b8d5006801a800a584da0070c66c80376536001b339ae00d5a4d60068d66a80336d350019379a600c591034801a6068802b664015311b000e590d70070cc6b00376835401b351a800d5b0d30068dc6900336400d10064c901a000c59403f06b01f02 (by decide +kernel)
private def cert58_76 := witnessA6966Final 58 21 0 1530000 1530448 48 4590
  0x250022c2718033388011b44008988e10062c870003637c012309c000cd8cdf0064ca6f00316737401c9b800999f004ac46f003464374019b31b800c9a0db0062d46d003c364013b09ba00d98cdc006aca6d803467368019b49b200c9acd80062da6b803f358014b3800a188db006ec86d00366636401ab41b000d1a8d70066d86b00326e354018b2006a003480d30054c26d00396336401c329b000dd9cd7006cd26b00356b35401a369a800cdbcd30064c881a400c593034401aa068002 (by decide +kernel)
private def cert58_77 := witnessA6966Final 58 20 0 1540000 1540385 44 3526
  0x16940111c8008984e30062c6710035384012344008d88e10064c87000316637c01c1bc009584e00068c66f803365378019339ba00c5a4dc00766d802767c013311bc00d590dd0068cc6e00336836c019351b400c5b0d9007c6c00286137401bb19b800d994db006ace6d003469364019b59b000c9b4d70062de6b003440d50054ce00296236c01c321b400dd98d9006cd06c00356a35c01a361ac00cdb8d50064c801a800c592034c01a8069002 (by decide +kernel)
private def cert58_78 := witnessA6966Final 58 19 0 1550000 1550384 40 2674
  0x4e60044d280216239001a1c6008d84e30064c67100316538401b9c00095a20048c470803364380019331be00c5a0de00746e80266138001ab19be00d194de0066ce6e803269370018b59b600f4da0050cf80276237801b321ba00d598dc0068d06d80336a368019361b200c5b8d8006801ae00a584dd0070c66e00376536c01b339b400d5a4d90068d66c00336d35c019379ac00c591035401a606a002 (by decide +kernel)
private def cert58_79 := witnessA6966Final 58 18 0 1560000 1560384 37 2034
  0x140011613980199ca008da50044c47200316438c01b1c4009184e30066c671003265384018b39c000e4df004cd100256238401a321c000cd98df0064d06f00316a37401e1b8009d84e0006cc66f80356537801a339ba00cda4dc0064d66d80316d36801f9b200a59f0050c46f00376437401b331b800d5a0db0068d46d00336c364019371b000c590035c01a406b002 (by decide +kernel)
private def cert58_80 := witnessA6966Final 58 17 0 1570000 1570321 33 1439
  0xb500088e70044c27300316339401a9c80091a50046c47200326438c018b31c400e0e1004ac271803463388019b29c200c99ce00062d26f803b378013b44009988e1006ac87000346637c019b41bc00c9a8dd0062d86e003e36c014309c000dd8cdf006cca6f00356737401a349b800cdacdb0064da6d00316f36401a206c002 (by decide +kernel)
private def cert58_81 := witnessA6966Final 58 16 0 1580000 1580320 30 1012
  0x13a4011350008588e7006873002361398019319ca00c594e4006e718025694012311c800cd90e30064cc7100316838401d1c0009984e3006ac671003465384019b39c000c9a4df0062d66f003d374014344009d88e1006cc87000356637c01a341bc00cda8dd0064d86e00316e36c01a006d002 (by decide +kernel)
private def cert58_82 := witnessA6966Final 58 15 0 1590000 1590320 27 696
  0x56004584e900667400236a0011311ce00c590e6006c72802461398019b19ca00c994e40062ce71803938801334a009588e40068c871803366388019341c200c5a8e000786f80276138c01b319c400d594e10068ce7000336937c019359bc00c5b4dd007e6e002 (by decide +kernel)
private def cert58_83 := witnessA6966Final 58 14 0 1600000 1600257 24 431
  0x16ac0111d4008984e90062c674003539c012350008d88e70064c87300316639401c1c8009584e60068c672803365390019339c600c5a4e20076708027694013311c800d590e30068cc71003368384019351c000c5b0df007c6f002 (by decide +kernel)
private def cert58_84 := witnessA6966Final 58 13 0 1610000 1610256 21 253
  0x27600226ac010b11d400d0e90046c2748032633a0018b29ce00dce6004ad400246239c019b21cc00c998e50062d072003a38c013309cc00d58ce50068ca7200336738c019349c400c5ace1007a70002 (by decide +kernel)
private def cert58_85 := witnessA6966Final 58 12 0 1620000 1620256 19 142
  0x5c004584ec00667580236ac011311d400c590e9006c740024613a4019b19d000c994e70062ce730039394013350009588e70068c873003366394019341c800c5a8e3007871002 (by decide +kernel)
private def cert58_86 := witnessA6966Final 58 11 0 1630000 1630193 16 59
  0x16b80111da008984ec0062c67580353a8012356008d88ea0064c8748031663a001c1ce009584e90068c67400336539c019339cc00c5a4e5007672002 (by decide +kernel)
private def cert58_87 := witnessA6966Final 58 10 0 1640000 1640192 14 19
  0x4ef0044d70021623b401a1d8008d84ec0064c6758031653a801b9d20095ab0048c4750033643a4019331d000c5a0e7007473002 (by decide +kernel)
private def cert58_88 := witnessA6966Final 58 9 0 1650000 1650192 12 5
  0xc4008b09de00ccee0046d70022623b4018b21d800d8eb0048c2760033633ac019329d400c59ce9007274002 (by decide +kernel)
private def cert58_89 := witnessA6966Final 58 8 0 1660000 1660129 10 0
  0x5b10044780022613bc018b19dc00d4ed0048d70023623b4019321d800c598eb007075002 (by decide +kernel)
private def cert58_90 := witnessA6966Final 58 7 0 1670000 1670128 8 0
  0x13c8011362008588f00068778023613bc019319dc00c594ed006e76002 (by decide +kernel)
private def cert58_91 := witnessA6966Final 58 6 0 1680000 1680128 7 0
  0x68004584f200667880236c4011311e000c590ef006c77002 (by decide +kernel)
private def cert58_92 := witnessA6966Final 58 5 0 1690000 1690065 5 0
  0x2da00223cc011309e400c58cf1006a78002 (by decide +kernel)
private def cert58_93 := witnessA6966Final 58 4 0 1700000 1700064 4 0
  0x13d4011368008588f3006879002 (by decide +kernel)
private def cert58_94 := witnessA6966Final 58 3 0 1710000 1710064 3 0
  0x6e004584f500667a002 (by decide +kernel)
private def cert58_95 := witnessA6966Final 58 2 0 1720000 1720001 2 0
  0x5b700447b002 (by decide +kernel)
private def cert58_96 := witnessA6966Final 58 1 0 1730000 1730000 1 0
  0x27c002 (by decide +kernel)
private def cert58_97 := witnessA6966Final 58 0 0 1740000 1740000 1 0
  0x1d001 (by decide +kernel)
private def chunks58 : List (Chunk 58) := [
  cert58_0,
  cert58_1,
  cert58_2,
  cert58_3,
  cert58_4,
  cert58_5,
  cert58_6,
  cert58_7,
  cert58_8,
  cert58_9,
  cert58_10,
  cert58_11,
  cert58_12,
  cert58_13,
  cert58_14,
  cert58_15,
  cert58_16,
  cert58_17,
  cert58_18,
  cert58_19,
  cert58_20,
  cert58_21,
  cert58_22,
  cert58_23,
  cert58_24,
  cert58_25,
  cert58_26,
  cert58_27,
  cert58_28,
  cert58_29,
  cert58_30,
  cert58_31,
  cert58_32,
  cert58_33,
  cert58_34,
  cert58_35,
  cert58_36,
  cert58_37,
  cert58_38,
  cert58_39,
  cert58_40,
  cert58_41,
  cert58_42,
  cert58_43,
  cert58_44,
  cert58_45,
  cert58_46,
  cert58_47,
  cert58_48,
  cert58_49,
  cert58_50,
  cert58_51,
  cert58_52,
  cert58_53,
  cert58_54,
  cert58_55,
  cert58_56,
  cert58_57,
  cert58_58,
  cert58_59,
  cert58_60,
  cert58_61,
  cert58_62,
  cert58_63,
  cert58_64,
  cert58_65,
  cert58_66,
  cert58_67,
  cert58_68,
  cert58_69,
  cert58_70,
  cert58_71,
  cert58_72,
  cert58_73,
  cert58_74,
  cert58_75,
  cert58_76,
  cert58_77,
  cert58_78,
  cert58_79,
  cert58_80,
  cert58_81,
  cert58_82,
  cert58_83,
  cert58_84,
  cert58_85,
  cert58_86,
  cert58_87,
  cert58_88,
  cert58_89,
  cert58_90,
  cert58_91,
  cert58_92,
  cert58_93,
  cert58_94,
  cert58_95,
  cert58_96,
  cert58_97]
def rows58 := rowsFrom chunks58

theorem good58 : ∀ r ∈ rows58, good 58 r = true := rowsFrom_good chunks58

theorem sorted58 : rows58.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks58 0 (by decide +kernel)).1

theorem mass58 (i : Fin 59) :
    bandCount 58 (i.val : ℤ) 58 15 ≤ (rows58.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks58).filter _).length
  rw [mass_eq]
  have h : (List.range 59).all
      (fun j => decide (bandCount 58 (j : ℤ) 58 15 ≤ mass j chunks58)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total58 : (rows58.map (price 58)).sum = 8924726 :=
  (total_eq chunks58).trans (by decide +kernel)


end A6966FinalRankReceipt

end Merged_A6966FinalRankReceiptGroup58

end Merged6967_A6966FinalRankReceiptGroup58

section Merged6967_Low48BentCycle
set_option Elab.async false


set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace Low48BentCycle

noncomputable section

open K1_13_6 K1_13_6_2 MvPolynomial
open K1_13_6_2_4 (Exponent OfDim DimLE Component LengthAt sectionIdeal dim_le_after_section)
open K1_13_6_2_4_1 (Grade Form unitGrade squarefree slotWeight piece gradedHilbert
  Represents TopNonnegative line positiveDiagonal component_mul_of_grade homogeneous_cut_exact
  forms_of_counts eq_sub_previous backwardDiff previous backwardDiff_degree_le previous_degree_le
  squarefree_degree backwardDiff_coeff_squarefree previous_coeff line_eval totalDegree_le_of_lines
  cube_extract positiveDiagonal_apply)
open scoped BigOperators Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra

abbrev Family := Fin 5 → Set Exponent

def diagonalExponents (B : Family) (t : Grade) : Set Exponent :=
  {m | ∃ u : (i : Fin 5) → Fin (t i) → Exponent,
    (∀ i j, u i j ∈ B i) ∧ m = ∑ i, ∑ j, u i j}

instance diagonalExponentsFinite (B : Family) [∀ i, Finite (B i)] (t : Grade) :
    Finite (diagonalExponents B t) := by
  let addExponents (u : (i : Fin 5) → Fin (t i) → B i) : Exponent :=
    ∑ i, ∑ j, (u i j).val
  have heq : diagonalExponents B t = Set.range addExponents := by
    ext m
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i j => ⟨u i j, hu i j⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨fun i j => (u i j).val, fun i j => (u i j).property, rfl⟩
  rw [heq]
  exact (Set.finite_range _).to_subtype
def mixedDegree (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (I : Finset (Fin 5)) : ℚ :=
  (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
    (MvPolynomial.affineHilbertPolynomial (Ideal.comap
      (MvPolynomial.monomialMap GeoField (diagonalExponents B (positiveDiagonal J)))
      P)).coeff I.card) / (2 : ℚ) ^ I.card
abbrev Generator (B : Family) := (i : Fin 5) × B i
abbrev SlotRing (B : Family) := MvPolynomial (Generator B) GeoField
instance (B : Family) [∀ i, Finite (B i)] : Finite (Generator B) := by
  infer_instance

def slot (B : Family) : Generator B → Fin 5 := Sigma.fst
def taggedMap (B : Family) : SlotRing B →ₐ[GeoField] GeoJets5 :=
  aeval fun v => monomial v.2.val 1
def gradedIdeal (B : Family) (P : Ideal GeoJets5) : Ideal (SlotRing B) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).toIdeal
def diagonalIdeal (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (t : Grade) :=
  P.comap (monomialMap GeoField (diagonalExponents B t))
theorem gradedIdeal_homogeneous (B : Family) (P : Ideal GeoJets5) :
    (gradedIdeal B P).IsHomogeneous (piece (slot B)) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).isHomogeneous
theorem gradedIdeal_mono (B : Family) {P Q : Ideal GeoJets5} (h : P ≤ Q) :
    gradedIdeal B P ≤ gradedIdeal B Q :=
  Ideal.homogeneousCore_mono _ (Ideal.comap_mono h)
theorem mem_gradedIdeal_of_grade {B : Family} {P : Ideal GeoJets5} {a : SlotRing B}
    {t : Grade} (ha : a ∈ piece (slot B) t) :
    a ∈ gradedIdeal B P ↔ taggedMap B a ∈ P := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (piece (slot B)) (P.comap (taggedMap B)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t, ha⟩ h
open K1_13_6_2_4_1 (homogeneous_colon regular_colon square_colon)

private theorem gradedIdeal_colon {B : Family} {P Q : Ideal GeoJets5} {g : SlotRing B}
    {e : Grade} (hg : g ∈ piece (slot B) e)
    (h : ∀ a : GeoJets5, a * taggedMap B g ∈ P ↔ a ∈ Q) :
    (gradedIdeal B P).colon {g} = gradedIdeal B Q := by
  ext a
  rw [mem_iff_weightedHomogeneousComponent_mem _ _
      (homogeneous_colon (slot B) (gradedIdeal_homogeneous B P) hg),
    mem_iff_weightedHomogeneousComponent_mem _ _ (gradedIdeal_homogeneous B Q)]
  apply forall_congr'
  intro t
  let z := weightedHomogeneousComponent (slotWeight (slot B)) t a
  have hz : z ∈ piece (slot B) t := weightedHomogeneousComponent_mem _ _ _
  have hg' : g.IsWeightedHomogeneous (slotWeight (slot B)) e := hg
  have hzg : z * g ∈ piece (slot B) (t + e) :=
    (weightedHomogeneousComponent_isWeightedHomogeneous t a).mul hg'
  change z ∈ (gradedIdeal B P).colon {g} ↔ z ∈ gradedIdeal B Q
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_gradedIdeal_of_grade hzg,
    mem_gradedIdeal_of_grade hz, map_mul, h]
private theorem exists_slot_lift (B : Family) (i : Fin 5) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ B i) :
    ∃ g : SlotRing B, g ∈ piece (slot B) (unitGrade i) ∧ taggedMap B g = D := by
  classical
  let gen (m : D.support) : Generator B := ⟨i, ⟨m, hD m m.property⟩⟩
  refine ⟨∑ m : D.support, C (D.coeff m) * MvPolynomial.X (gen m), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro m _
    have hc : (C (D.coeff m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) 0 :=
      isWeightedHomogeneous_C _ _
    have hx : (MvPolynomial.X (gen m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) (unitGrade i) :=
      isWeightedHomogeneous_X GeoField (slotWeight (slot B)) (gen m)
    rw [mem_weightedHomogeneousSubmodule]
    simpa only [zero_add] using hc.mul hx
  · simp only [map_sum, map_mul, taggedMap, aeval_C, algebraMap_eq, aeval_X,
      C_mul_monomial, mul_one, gen]
    rw [Finset.sum_coe_sort D.support (fun m => monomial m (D.coeff m))]
    exact D.support_sum_monomial_coeff
theorem exists_regular_lifts (B : Family) (P : Ideal GeoJets5) (i : Fin 5) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ B i)
    (hD₂ : ∀ m ∈ (D ^ 2).support, m ∈ B i) (hr : IsLeftRegular (Ideal.Quotient.mk P D)) :
    ∃ f g : SlotRing B,
      f ∈ piece (slot B) (unitGrade i) ∧ g ∈ piece (slot B) (unitGrade i) ∧
      (gradedIdeal B P).colon {f} = gradedIdeal B P ∧
      gradedIdeal B P ⊔ Ideal.span {f} ≤ gradedIdeal B (sectionIdeal P (D ^ 2)) ∧
      (gradedIdeal B (sectionIdeal P (D ^ 2))).colon {g} = gradedIdeal B (sectionIdeal P D) ∧
      gradedIdeal B (sectionIdeal P (D ^ 2)) ⊔ Ideal.span {g} ≤ gradedIdeal B (sectionIdeal P D) := by
  classical
  obtain ⟨f, hf, hfmap⟩ := exists_slot_lift B i (D ^ 2) hD₂
  obtain ⟨g, hg, hgmap⟩ := exists_slot_lift B i D hD
  refine ⟨f, g, hf, hg, ?_, ?_, ?_, ?_⟩
  · apply gradedIdeal_colon hf
    intro a
    rw [hfmap]
    have h : IsLeftRegular (Ideal.Quotient.mk P (D ^ 2)) := by
      rw [map_pow]
      exact IsLeftRegular.pow 2 hr
    exact regular_colon h a
  · refine sup_le (gradedIdeal_mono B le_sup_left) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    rw [mem_gradedIdeal_of_grade hf, hfmap]
    exact (le_sup_right : Ideal.span {D ^ 2} ≤ sectionIdeal P (D ^ 2))
      (Ideal.mem_span_singleton_self _)
  · apply gradedIdeal_colon hg
    intro a
    rw [hgmap]
    exact square_colon hr a
  · refine sup_le (gradedIdeal_mono B (sup_le le_sup_left ?_))
      ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mem_span_singleton'.mpr ⟨D, (pow_two D).symm⟩)).trans le_sup_right
    · rw [mem_gradedIdeal_of_grade hg, hgmap]
      exact (le_sup_right : Ideal.span {D} ≤ sectionIdeal P D) (Ideal.mem_span_singleton_self _)
theorem diagonal_add (B : Family) (s t : Grade) :
    diagonalExponents B (s + t : Grade) = diagonalExponents B s + diagonalExponents B t := by
  ext m
  constructor
  · rintro ⟨u, hu, rfl⟩
    let v (i : Fin 5) (j : Fin (s i)) := u i (Fin.castAdd (t i) j)
    let w (i : Fin 5) (j : Fin (t i)) := u i (Fin.natAdd (s i) j)
    refine ⟨∑ i, ∑ j, v i j, ⟨v, fun i j => hu i _, rfl⟩,
      ∑ i, ∑ j, w i j, ⟨w, fun i j => hu i _, rfl⟩, ?_⟩
    simp only [v, w, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (Fin.sum_univ_add (u i)).symm)
  · rintro ⟨a, ⟨v, hv, rfl⟩, b, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i => Fin.append (v i) (w i), ?_, ?_⟩
    · intro i
      exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hv i j)
        (fun j => by simpa only [Fin.append_right] using hw i j)
    · change (∑ i, ∑ j, v i j) + (∑ i, ∑ j, w i j) =
          ∑ i, ∑ j : Fin (s i + t i), Fin.append (v i) (w i) j
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa only [Fin.append_left, Fin.append_right] using
        (Fin.sum_univ_add (Fin.append (v i) (w i))).symm
private theorem diagonal_zero (B : Family) : diagonalExponents B (0 : Grade) = 0 := by
  ext m
  rw [Set.mem_zero]
  constructor
  · rintro ⟨u, _, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun _ j => j.elim0, fun _ j => j.elim0, by simp⟩
theorem diagonal_nsmul (B : Family) (t : Grade) (n : ℕ) :
    diagonalExponents B (n • t : Grade) = n • diagonalExponents B t := by
  induction n with
  | zero => simpa only [zero_smul] using diagonal_zero B
  | succ n ih => simp only [succ_nsmul, diagonal_add, ih]
private theorem zero_mem_diagonal (B : Family) (h0 : ∀ i, 0 ∈ B i) (t : Grade) : 0 ∈ diagonalExponents B t :=
  ⟨fun _ _ => 0, fun i _ => h0 i, by simp⟩
theorem generator_mem_diagonal {B : Family} (h0 : ∀ i, 0 ∈ B i) (v : Generator B) :
    v.2.val ∈ diagonalExponents B (slotWeight (slot B) v) := by
  classical
  let a (i : Fin 5) : Exponent := if i = v.1 then v.2.val else 0
  refine ⟨fun i _ => a i, ?_, ?_⟩
  · intro i _
    by_cases h : i = v.1
    · subst i
      simpa only [a, ite_eq_left rfl] using v.2.property
    · simpa only [a, ite_eq_right h] using h0 i
  · symm
    calc
      (∑ i, ∑ _j : Fin (slotWeight (slot B) v i), a i) =
          ∑ i, (slotWeight (slot B) v i) • a i :=
        Finset.sum_congr rfl fun i _ => Fin.sum_const _ _
      _ = v.2.val := by
        change (∑ i, (Finsupp.single v.1 (1 : ℕ) i) • a i) = _
        refine (Finset.sum_eq_single v.1 ?_ ?_).trans ?_
        · intro i _ h
          simp [a, h]
        · simp
        · simp [a]
private theorem tagged_monomial (B : Family) (d : Generator B →₀ ℕ) (c : GeoField) :
    taggedMap B (monomial d c) =
      monomial (Finsupp.weight (fun v : Generator B => v.2.val) d) c := by
  rw [taggedMap, aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, algebraMap_eq, C_mul_monomial, mul_one]
private theorem tagged_exponent_mem (B : Family) (h0 : ∀ i, 0 ∈ B i) (d : Generator B →₀ ℕ) :
    Finsupp.weight (fun v : Generator B => v.2.val) d ∈
      diagonalExponents B (Finsupp.weight (slotWeight (slot B)) d) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using zero_mem_diagonal B h0 (0 : Grade)
  | add a b ha hb => simpa only [map_add, diagonal_add] using Set.add_mem_add ha hb
  | single v n =>
      have hmem : n • v.2.val ∈ n • diagonalExponents B (slotWeight (slot B) v) := by
        induction n with
        | zero => simp
        | succ n ih =>
            simpa only [succ_nsmul] using Set.add_mem_add ih (generator_mem_diagonal h0 v)
      simpa only [Finsupp.weight_single, diagonal_nsmul] using hmem
private theorem tagged_lift {B : Family} {g : Grade} {m : Exponent}
    (hm : m ∈ diagonalExponents B g) :
    ∃ a : SlotRing B, a ∈ piece (slot B) g ∧ taggedMap B a = monomial m 1 := by
  classical
  obtain ⟨u, hu, rfl⟩ := hm
  let v (i : Fin 5) (j : Fin (g i)) : Generator B := ⟨i, ⟨u i j, hu i j⟩⟩
  let d : Generator B →₀ ℕ := ∑ i, ∑ j, Finsupp.single (v i j) 1
  have hg : Finsupp.weight (slotWeight (slot B)) d = g := by
    simp only [d, map_sum, Finsupp.weight_single, one_smul, slotWeight, slot, v, Fin.sum_const]
    ext i
    rw [Finsupp.finsetSum_apply]
    simp [unitGrade, Finsupp.single_apply]
  refine ⟨monomial d 1, isWeightedHomogeneous_monomial _ _ _ hg, ?_⟩
  simp only [tagged_monomial, d, map_sum, Finsupp.weight_single, one_smul, v]
private theorem tagged_image (B : Family) (h0 : ∀ i, 0 ∈ B i) (g : Grade) :
    (piece (slot B) g).map (taggedMap B).toLinearMap =
      restrictSupport GeoField (diagonalExponents B g) := by
  apply le_antisymm
  · have hpiece : piece (slot B) g =
        restrictSupport GeoField {d | Finsupp.weight (slotWeight (slot B)) d = g} :=
      weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
    rw [Submodule.map_le_iff_le_comap, hpiece, restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨d, hd, rfl⟩
    change taggedMap B (monomial d 1) ∈ restrictSupport GeoField (diagonalExponents B g)
    rw [tagged_monomial, monomial_mem_restrictSupport]
    exact Or.inl ((show Finsupp.weight (slotWeight (slot B)) d = g from hd) ▸
      tagged_exponent_mem B h0 d)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, heq⟩ := tagged_lift hm
    exact ⟨a, ha, heq⟩
open K1_13_6_2_4_1_2 (affine_image quotient_image_finrank)

theorem diagonal_hilbert (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (P : Ideal GeoJets5) (t : Grade) (n : ℕ) :
    gradedHilbert (slot B) (gradedIdeal B P) (n • t) =
      affineHilbertFunction (diagonalIdeal B P t) n := by
  let S := diagonalExponents B t
  change Module.finrank GeoField
      ((piece (slot B) (n • t)).map (Ideal.Quotient.mkₐ GeoField (gradedIdeal B P)).toLinearMap) =
    Module.finrank GeoField
      ((restrictTotalDegree S GeoField n).map
        (Ideal.Quotient.mkₐ GeoField (diagonalIdeal B P t)).toLinearMap)
  have hle : gradedIdeal B P ≤ P.comap (taggedMap B) :=
    Ideal.toIdeal_homogeneousCore_le (piece (slot B)) _
  have hgraded := quotient_image_finrank (piece (slot B) (n • t)) (gradedIdeal B P) P
    (taggedMap B) hle (fun _ ha => (mem_gradedIdeal_of_grade ha).mpr)
  have haffine := quotient_image_finrank (restrictTotalDegree S GeoField n) (diagonalIdeal B P t) P
    (monomialMap GeoField S) le_rfl (fun _ _ h => h)
  rw [hgraded, haffine, tagged_image B h0 (n • t), affine_image S (zero_mem_diagonal B h0 t) n,
    diagonal_nsmul]
theorem line_of_diagonal_agreement (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (t : Grade) (ht : ∀ j, 0 < t j)
    (hdiag : ∀ N, gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
      affineHilbertFunction (diagonalIdeal B P t) N) :
    line t p = affineHilbertPolynomial (diagonalIdeal B P t) := by
  obtain ⟨N₀, hN₀⟩ := hp
  refine eq_affineHilbertPolynomial_of_eval_eq (N₀ := N₀) fun N hN => ?_
  rw [line_eval, hN₀ _ (fun j => hN.trans (Nat.le_mul_of_pos_right N (ht j)))]
  exact congrArg (fun n : ℕ => (n : ℚ)) (hdiag N)
theorem diagonal_degree_le (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (t : Grade) {d : ℕ}
    (hd : DimLE P d) : (affineHilbertPolynomial (diagonalIdeal B P t)).natDegree ≤ d := by
  let f := monomialMap GeoField (diagonalExponents B t)
  let φ := Ideal.quotientMapₐ P f le_rfl
  exact (natDegree_affineHilbertPolynomial_le_of_injective φ Ideal.quotientMap_injective).trans
    (K1_13_6_2_4_2.hilbert_degree_le hd)
theorem gradedIdeal_degree_le (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) {d : ℕ} (hd : DimLE P d)
    {p : Form} (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    p.totalDegree ≤ d := by
  apply totalDegree_le_of_lines
  intro t ht
  rw [line_of_diagonal_agreement B P hp t ht (hdiag t ht)]
  exact diagonal_degree_le B P t hd
theorem mixedDegree_eq (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (I : Finset (Fin 5)) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    mixedDegree B P I = p.coeff (squarefree I) / (2 : ℚ) ^ I.card := by
  unfold mixedDegree
  rw [← cube_extract I p]
  congr 1
  refine Finset.sum_congr rfl fun J _ => ?_
  have ht (j : Fin 5) : 0 < positiveDiagonal J j := by
    rw [positiveDiagonal_apply]
    split <;> decide
  have he := line_of_diagonal_agreement B P hp (positiveDiagonal J) ht
    (hdiag (positiveDiagonal J) ht)
  rw [he]
  rfl
private theorem top_coeff_mono {p q : Form} {a : Grade}
    (hp : p.totalDegree ≤ a.degree) (hq : q.totalDegree ≤ a.degree)
    (h : TopNonnegative (p - q)) : q.coeff a ≤ p.coeff a := by
  have hd : (p - q).totalDegree ≤ a.degree :=
    (totalDegree_sub p q).trans (max_le hp hq)
  exact sub_nonneg.mp (by simpa only [coeff_sub] using h a hd)
theorem properCut (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5)
    (hi : i ∉ I) (hdim : DimLE P (I.card + 1)) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ B i) (hD₂ : ∀ m ∈ (D ^ 2).support, m ∈ B i)
    (hreg : IsLeftRegular (Ideal.Quotient.mk P D)) :
    mixedDegree B (sectionIdeal P D) I ≤ mixedDegree B P (insert i I) := by
  let hcounts := K1_13_6_2_4_1_1.proof
  have hdiag (Q : Ideal GeoJets5) (t : Grade) (_ : ∀ j, 0 < t j) (n : ℕ) :=
    diagonal_hilbert B h0 Q t n
  let P₁ := sectionIdeal P D
  let P₂ := sectionIdeal P (D ^ 2)
  obtain ⟨f, g, hf, hg, hcf, hle₁, hcg, hle₂⟩ := exists_regular_lifts B P i D hD hD₂ hreg
  obtain ⟨hhom₁, hex₁⟩ := homogeneous_cut_exact (slot B) (gradedIdeal B P)
    (gradedIdeal_homogeneous B P) i f hf
  obtain ⟨hhom₂, hex₂⟩ := homogeneous_cut_exact (slot B) (gradedIdeal B P₂)
    (gradedIdeal_homogeneous B P₂) i g hg
  rw [hcf] at hex₁
  rw [hcg] at hex₂
  obtain ⟨p, _, hp, _, _⟩ := forms_of_counts hcounts (Generator B) (slot B) (gradedIdeal B P) (gradedIdeal B P)
    (gradedIdeal_homogeneous B P) (gradedIdeal_homogeneous B P) le_rfl
  obtain ⟨q, p₂, hq, hp₂, hpos₂⟩ := forms_of_counts hcounts (Generator B) (slot B)
    (gradedIdeal B P ⊔ Ideal.span {f}) (gradedIdeal B P₂) hhom₁
    (gradedIdeal_homogeneous B P₂) hle₁
  obtain ⟨r, p₁, hr, hp₁, hpos₁⟩ := forms_of_counts hcounts (Generator B) (slot B)
    (gradedIdeal B P₂ ⊔ Ideal.span {g}) (gradedIdeal B P₁) hhom₂
    (gradedIdeal_homogeneous B P₁) hle₂
  have hqeq : q = backwardDiff i p := eq_sub_previous i hq hp hp hex₁
  have hreq : r = p₂ - previous i p₁ := eq_sub_previous i hr hp₂ hp₁ hex₂
  have hreg₂ : IsLeftRegular (Ideal.Quotient.mk P (D ^ 2)) := by
    rw [map_pow]
    exact IsLeftRegular.pow 2 hreg
  have hdp := gradedIdeal_degree_le B P hdim hp (hdiag P)
  have hdp₁ := gradedIdeal_degree_le B P₁ (dim_le_after_section hreg hdim) hp₁ (hdiag P₁)
  have hdp₂ := gradedIdeal_degree_le B P₂ (dim_le_after_section hreg₂ hdim) hp₂ (hdiag P₂)
  have hdq : q.totalDegree ≤ I.card := by
    rw [hqeq]
    exact backwardDiff_degree_le i hdp
  have hdr : r.totalDegree ≤ I.card := by
    rw [hreq]
    exact (totalDegree_sub _ _).trans (max_le hdp₂ (previous_degree_le i hdp₁))
  have hdeg := squarefree_degree I
  have hm₂ := top_coeff_mono (hdq.trans_eq hdeg.symm) (hdp₂.trans_eq hdeg.symm) hpos₂
  have hm₁ := top_coeff_mono (hdr.trans_eq hdeg.symm) (hdp₁.trans_eq hdeg.symm) hpos₁
  rw [hqeq, backwardDiff_coeff_squarefree i hi hdp] at hm₂
  rw [hreq, coeff_sub, previous_coeff i (squarefree I) (hdp₁.trans_eq hdeg.symm)] at hm₁
  have hscaled : 2 * p₁.coeff (squarefree I) ≤ p.coeff (squarefree (insert i I)) := by
    linarith only [hm₁, hm₂]
  rw [mixedDegree_eq B P₁ I hp₁ (hdiag P₁), mixedDegree_eq B P (insert i I) hp (hdiag P)]
  rw [Finset.card_insert_of_notMem hi, pow_succ]
  refine (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) I.card)
    (mul_pos (pow_pos (by norm_num : (0 : ℚ) < 2) I.card) (by norm_num))).mpr ?_
  convert mul_le_mul_of_nonneg_right hscaled
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) I.card) using 1; ring
theorem diagonal_surjective {B : Family} (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i) {t : Grade}
    (ht : ∀ i, 0 < t i) : Function.Surjective (monomialMap GeoField (diagonalExponents B t)) := by
  classical
  apply monomialMap_surjective
  intro v
  obtain ⟨i, hi⟩ := hcoords v
  let j₀ : Fin (t i) := ⟨0, ht i⟩
  let u (k : Fin 5) (j : Fin (t k)) : Exponent :=
    if h : k = i then if h ▸ j = j₀ then Finsupp.single v 1 else 0 else 0
  refine ⟨u, ?_, ?_⟩
  · intro k j
    by_cases hk : k = i
    · subst k
      by_cases hj : j = j₀
      · simpa [u, hj] using hi
      · simpa [u, hj] using h0 i
    · simpa [u, hk] using h0 k
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j₀]
      · simp [u]
      · intro j _ hj
        simp [u, hj]
      · simp
    · intro k _ hk
      simp [u, hk]
    · simp


theorem mixedDegree_nonneg (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (P : Ideal GeoJets5) (I : Finset (Fin 5)) (hdim : DimLE P I.card) :
    0 ≤ mixedDegree B P I := by
  have htop : (⊤ : Ideal (SlotRing B)).IsHomogeneous (piece (slot B)) := by
    intro _ _ _
    trivial
  obtain ⟨p, q, hp, hq, hpos⟩ := forms_of_counts K1_13_6_2_4_1_1.proof
    (Generator B) (slot B) (gradedIdeal B P) ⊤ (gradedIdeal_homogeneous B P) htop le_top
  have hq0 : q = 0 := by
    obtain ⟨N, hN⟩ := hq
    apply K1_13_6_2_4_1.eq_of_grid (N := N)
    intro t ht
    rw [hN t ht]
    have hmap : (piece (slot B) t).map
        (Ideal.Quotient.mkₐ GeoField (⊤ : Ideal (SlotRing B))).toLinearMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨a, _, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (by trivial)
    simp [gradedHilbert, hmap]
  have hdiag (t : Grade) (_ : ∀ j, 0 < t j) (n : ℕ) := diagonal_hilbert B h0 P t n
  have hd := gradedIdeal_degree_le B P hdim hp hdiag
  rw [hq0, sub_zero] at hpos
  rw [mixedDegree_eq B P I hp hdiag]
  exact div_nonneg (hpos _ (hd.trans_eq (squarefree_degree I).symm)) (by positivity)

open K1_13_6_2_4_2 (dim_mono local_step weight weight_eq length_top)

private theorem mixed_step {B : Family} [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i) {I : Finset (Fin 5)}
    {J Q : Ideal GeoJets5} (hJ : DimLE J I.card) {a : GeoJets5}
    (ha : ∀ x, x * a ∈ J ↔ x ∈ Q) :
    mixedDegree B J I = mixedDegree B (sectionIdeal J a) I + mixedDegree B Q I := by
  classical
  have hdiag (U : Finset (Fin 5)) :
      let f := monomialMap GeoField (diagonalExponents B (positiveDiagonal U))
      (affineHilbertPolynomial (J.comap f)).coeff I.card =
        (affineHilbertPolynomial ((sectionIdeal J a).comap f)).coeff I.card +
          (affineHilbertPolynomial (Q.comap f)).coeff I.card := by
    let t := positiveDiagonal U
    have ht : ∀ i, 0 < t i := fun i => by rw [positiveDiagonal_apply]; split <;> decide
    let f := monomialMap GeoField (diagonalExponents B t)
    have hf : Function.Surjective f := diagonal_surjective h0 hcoords ht
    obtain ⟨A, hA⟩ := hf a
    change (affineHilbertPolynomial (J.comap f)).coeff I.card =
      (affineHilbertPolynomial ((sectionIdeal J a).comap f)).coeff I.card +
        (affineHilbertPolynomial (Q.comap f)).coeff I.card
    have hsection : (sectionIdeal J a).comap f = J.comap f ⊔ Ideal.span {A} := by
      have hk : J.comap f ⊔ Ideal.span {A} =
          (J.comap f ⊔ Ideal.span {A}) ⊔ Ideal.comap f ⊥ :=
        (sup_eq_left.mpr ((Ideal.comap_mono bot_le).trans le_sup_left)).symm
      calc
        (sectionIdeal J a).comap f = ((J.comap f ⊔ Ideal.span {A}).map f).comap f := by
          rw [Ideal.map_sup, Ideal.map_comap_of_surjective f hf, Ideal.map_span,
            Set.image_singleton, hA, sectionIdeal]
        _ = J.comap f ⊔ Ideal.span {A} :=
          (Ideal.comap_map_of_surjective f hf _).trans hk.symm
    have hAann (x : MvPolynomial (diagonalExponents B t) GeoField) :
        x * A ∈ J.comap f ↔ x ∈ Q.comap f := by
      simp only [Ideal.mem_comap, map_mul, hA, ha]
    have hd := diagonal_degree_le B J t hJ
    have hlow := K1_13_7_6_1.hilbertCoeff_step
      (J := J.comap f) (K := J.comap f ⊔ Ideal.span {A})
      le_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self A)) hAann hd
    rw [hsection]
    exact le_antisymm (K1_13_6_2_4_2_1.proof _ _ A hAann _ hd) hlow
  unfold mixedDegree
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  rw [hdiag U, mul_add]
private theorem cycleBudget {B : Family} [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i)
    {H : Ideal GeoJets5} {I : Finset (Fin 5)} (hH : DimLE H I.card)
    {ι : Type} (S : Finset ι) {C : ι → Ideal GeoJets5}
    (hinj : Set.InjOn C (S : Set ι)) (hp : ∀ a ∈ S, H.IsMinimalPrime (C a))
    (J : Ideal GeoJets5) (hHJ : H ≤ J) :
    (∀ a (ha : a ∈ S), LengthAt J (C a) (hp a ha).isPrime ≠ ⊤) ∧
      (∑ a ∈ S, (weight J (C a) : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B J I := by
  classical
  let D (P : Ideal GeoJets5) := mixedDegree B P I
  change _ ∧ (∑ a ∈ S, (weight J (C a) : ℚ) * D (C a)) ≤ D J
  revert hHJ
  induction J using WellFounded.induction (wellFounded_gt (α := Ideal GeoJets5)) with
  | h J ih =>
    intro hHJ
    by_cases hJ : J = ⊤
    · subst J
      have hz (a : ι) (ha : a ∈ S) : LengthAt ⊤ (C a) (hp a ha).isPrime = 0 :=
        length_top _ (hp a ha).isPrime
      constructor
      · intro a ha
        simp [hz a ha]
      · have hs : (∑ a ∈ S, (weight ⊤ (C a) : ℚ) * D (C a)) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          simp [weight_eq (hp a ha).isPrime, hz a ha]
        rw [hs]
        simp [D, mixedDegree, affineHilbertPolynomial_top]
    obtain ⟨a, Q, haJ, hQ, hann⟩ := K1_13_7_6_1.exists_prime_factor hJ
    let K := sectionIdeal J a
    have hJK : J ≤ K := le_sup_left
    have haK : a ∈ K := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < K := lt_of_le_of_ne hJK fun he => haJ (he ▸ haK)
    have hHQ : H ≤ Q := fun x hx => (hann x).mp (J.mul_mem_right _ (hHJ hx))
    obtain ⟨hfinK, hboundK⟩ := ih K hlt (hHJ.trans hJK)
    have hstep (i : ι) (hi : i ∈ S) :
        LengthAt J (C i) (hp i hi).isPrime =
          (if Q = C i then 1 else 0) + LengthAt K (C i) (hp i hi).isPrime :=
      local_step hHJ hQ hann (hp i hi)
    have hDQ : 0 ≤ D Q := mixedDegree_nonneg B h0 Q I (dim_mono hHQ hH)
    have hweight (i : ι) (hi : i ∈ S) :
        (weight J (C i) : ℚ) = (weight K (C i) : ℚ) + (if Q = C i then 1 else 0) := by
      rw [weight_eq (hp i hi).isPrime, weight_eq (J := K) (hp i hi).isPrime, hstep i hi]
      split_ifs with hEq
      · rw [ENat.toNat_add (by simp) (hfinK i hi)]
        simp [add_comm]
      · simp
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hstep i hi]
      have hfinite : (if Q = C i then 1 else 0 : ℕ∞) ≠ ⊤ := by
        split_ifs <;> simp
      exact WithTop.add_ne_top.mpr ⟨hfinite, hfinK i hi⟩
    · have hindicator : (∑ i ∈ S, if Q = C i then D Q else 0) ≤ D Q := by
        by_cases hex : ∃ i ∈ S, Q = C i
        · obtain ⟨i, hi, he⟩ := hex
          rw [Finset.sum_eq_single_of_mem i hi, ite_eq_left he]
          intro j hj hji
          exact ite_eq_right fun hjQ => hji (hinj hj hi (hjQ.symm.trans he))
        · rw [Finset.sum_eq_zero (fun i hi => ite_eq_right (fun h => hex ⟨i, hi, h⟩))]
          exact hDQ
      calc
        _ = (∑ i ∈ S, (weight K (C i) : ℚ) * D (C i)) +
            (∑ i ∈ S, if Q = C i then D Q else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hweight i hi, add_mul]
          split_ifs with he
          · rw [← he, one_mul]
          · rw [zero_mul]
        _ ≤ D K + D Q := add_le_add hboundK hindicator
        _ = D J := (mixed_step h0 hcoords (dim_mono hHJ hH) hann).symm
theorem cycleComparison (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i)
    (J : Ideal GeoJets5) (I : Finset (Fin 5)) (hJ : DimLE J I.card)
    {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ)
    (hinj : Set.InjOn C (S : Set ι))
    (h : ∀ a ∈ S, ∃ h : J.IsMinimalPrime (C a), (w a : ℕ∞) ≤ LengthAt J (C a) h.isPrime) :
    (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B J I := by
  have hp (a : ι) (ha : a ∈ S) : J.IsMinimalPrime (C a) := Exists.choose (h a ha)
  obtain ⟨hfin, hbudget⟩ := cycleBudget h0 hcoords hJ S hinj hp J le_rfl
  refine le_trans (Finset.sum_le_sum fun a ha => ?_) hbudget
  have hlen : (w a : ℕ∞) ≤ LengthAt J (C a) (hp a ha).isPrime := Exists.choose_spec (h a ha)
  have hw : w a ≤ weight J (C a) := by
    rw [weight_eq (hp a ha).isPrime]
    exact ENat.toNat_le_toNat hlen (hfin a ha)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hw)
    (mixedDegree_nonneg B h0 (C a) I (dim_mono (hp a ha).le hJ))

theorem divisorBound (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i)
    (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5)
    (hP : P.IsPrime) (hi : i ∉ I) (hd : OfDim P (I.card + 1))
    (D : GeoJets5) (hD : ∀ m ∈ D.support, m ∈ B i)
    (hD₂ : ∀ m ∈ (D ^ 2).support, m ∈ B i) (hprop : D ∉ P)
    {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ)
    (hinj : Set.InjOn C (S : Set ι)) (hcomp : ∀ a ∈ S, Component P D (C a) (w a)) :
    (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B P (insert i I) := by
  let := hP
  have hr : IsLeftRegular (Ideal.Quotient.mk P D) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hprop)
  have hdle : DimLE P (I.card + 1) := le_of_eq hd
  exact (cycleComparison B h0 hcoords (sectionIdeal P D) I (dim_le_after_section hr hdle)
    S C w hinj (fun a ha => ⟨(hcomp a ha).minimal, (hcomp a ha).length_le⟩)).trans
    (properCut B h0 P I i hi hdle D hD hD₂ hr)

end

end Low48BentCycle

end Merged6967_Low48BentCycle

section Merged6967_Low48PrimaryPivotBinParity
set_option Elab.async false







set_option Elab.async false

-- merged module Low48PrimaryPivotAggregate
section Merged_Low48PrimaryPivotAggregate

-- merged module KoalaAffineTriangle
section Merged_KoalaAffineTriangle

set_option autoImplicit false

namespace KoalaAffineTriangle

open scoped BigOperators

def twiceTriangle (x : ℤ) : ℤ :=
  let q := max 0 x
  q * (q + 1)

private def polynomial (a d : ℤ) (n : ℕ) : ℤ :=
  let m : ℤ := n
  6 * m * a * (a + 1) + 3 * d * (2 * a + 1) * m * (m - 1) +
    d * d * m * (m - 1) * (2 * m - 1)

private def closed (a d : ℤ) (n : ℕ) : ℤ := polynomial a d n / 6

















private def firstPositive (a d : ℤ) : ℕ := ((-a)/d+1).toNat





private def fast (a d : ℤ) (n : ℕ) : ℤ :=
  if 0 < d then
    let j := min n (firstPositive a d)
    if j = n then 0 else closed (a+d*(j : ℤ)) d (n-j)
  else if d < 0 then
    closed a d (min n (firstPositive (-a) (-d)))
  else
    (n : ℤ) * twiceTriangle a


/-- Sum a positive triangular term using the unique sign crossing of the affine argument. -/
def sumFast (a d lo : ℤ) (n : ℕ) : ℤ := fast (a+d*lo) d n



end KoalaAffineTriangle

end Merged_KoalaAffineTriangle

-- merged module KoalaPiecewiseTriangle
section Merged_KoalaPiecewiseTriangle

set_option autoImplicit false
set_option Elab.async false

namespace KoalaPiecewiseTriangle
open Finset
open scoped BigOperators

structure Line where
  a : ℤ
  d : ℤ

def Line.at (f : Line) (x : ℤ) : ℤ := f.a + f.d*x

def Line.sub (f g : Line) : Line := ⟨f.a-g.a,f.d-g.d⟩

inductive Expr
  | affine (f : Line)
  | lower (f g : Expr)
  | upper (f g : Expr)
  | sub (f g : Expr)

def Expr.at : Expr → ℤ → ℤ
  | .affine f, x => f.at x
  | .lower f g, x => min (f.at x) (g.at x)
  | .upper f g, x => max (f.at x) (g.at x)
  | .sub f g, x => f.at x - g.at x

def Expr.const (a : ℤ) : Expr := .affine ⟨a,0⟩

private def ordered (f g : Line) (lo hi : ℤ) : Prop :=
  f.at lo ≤ g.at lo ∧ f.at hi ≤ g.at hi

private instance (f g : Line) (lo hi : ℤ) : Decidable (ordered f g lo hi) := by
  unfold ordered
  infer_instance









structure BandCuts where
  l0 : ℤ
  q1 : ℤ
  first : ℤ
  last : ℤ



private def lineCutSum (b : BandCuts) (l q : Line) (k lo : ℤ) (n : ℕ) : ℤ :=
  let sum := KoalaAffineTriangle.sumFast
  sum (l.a-k-q.a) (l.d-q.d) lo n -
    sum (b.l0-k-q.a) (-q.d) lo n -
    (sum (l.a-k-b.q1) l.d lo n -
      (n : ℤ) * KoalaAffineTriangle.twiceTriangle (b.l0-k-b.q1))


def lineBandSum (b : BandCuts) (l q : Line) (lo : ℤ) (n : ℕ) : ℤ :=
  lineCutSum b l q b.first lo n - lineCutSum b l q b.last lo n









end KoalaPiecewiseTriangle

end Merged_KoalaPiecewiseTriangle

-- merged module Low48PrimaryPivotAggregate
section Merged_Low48PrimaryPivotAggregate

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Low48PrimaryPivot
open K1_13_2_3 Finset KoalaPiecewiseTriangle
open scoped BigOperators

def contactExpr (c f r : ℕ) : Expr :=
  .lower (.const (1650-(f : ℤ)))
    (.lower (.affine ⟨3300-2*(r : ℤ)-3*(c : ℤ)-4*(f : ℤ),-5⟩)
      (.lower (.affine ⟨4950-3*(r : ℤ)-5*(c : ℤ)-7*(f : ℤ),-9⟩)
        (.affine ⟨1650-(r : ℤ)-(c : ℤ)-(f : ℤ)+(1650-(c : ℤ)-3*(f : ℤ))/2,-3⟩)))

theorem contactExpr_eq (c f r t : ℕ) (hr : r < 3)
    (h : (Triple.mk (3*t+r) c f).index ≤ 1650) :
    (contactExpr c f r).at t = ((Triple.mk (3*t+r) c f).contact : ℤ) := by
  rw [contact_eq]
  simp only [contactExpr, Expr.at, Expr.const, Line.at, zero_mul, add_zero, Triple.room, Triple.index] at *
  omega












end Low48PrimaryPivot

end Merged_Low48PrimaryPivotAggregate

end Merged_Low48PrimaryPivotAggregate

-- merged module Low48PrimaryPivotBinParity
section Merged_Low48PrimaryPivotBinParity

-- merged module KoalaLinearWindow
section Merged_KoalaLinearWindow

set_option autoImplicit false

namespace KoalaLinearWindow
open Finset KoalaPiecewiseTriangle

structure Span where
  lo : ℤ
  hi : ℤ

def Span.finset (s : Span) : Finset ℤ := Ico s.lo s.hi

def Span.keep (s : Span) (f : Line) : Span :=
  if 0 < f.d then
    ⟨max s.lo (-(f.a/f.d)), s.hi⟩
  else if f.d < 0 then
    ⟨s.lo, min s.hi (f.a/(-f.d)+1)⟩
  else if 0 ≤ f.a then s
  else ⟨0,0⟩

theorem mem_keep (s : Span) (f : Line) (x : ℤ) :
    x ∈ (s.keep f).finset ↔ x ∈ s.finset ∧ 0 ≤ f.at x := by
  unfold Span.keep
  by_cases hpos : 0 < f.d
  · rw [ite_eq_left hpos]
    simp only [Span.finset, mem_Ico, max_le_iff]
    have h : -(f.a/f.d) ≤ x ↔ 0 ≤ f.at x := by
      rw [neg_le, Int.le_ediv_iff_mul_le hpos, Line.at]
      rw [neg_mul, mul_comm x f.d]
      omega
    tauto
  rw [ite_eq_right hpos]
  by_cases hneg : f.d < 0
  · rw [ite_eq_left hneg]
    simp only [Span.finset, mem_Ico, lt_min_iff]
    have h : x < f.a/(-f.d)+1 ↔ 0 ≤ f.at x := by
      rw [Int.lt_add_one_iff, Int.le_ediv_iff_mul_le (by omega : 0 < -f.d), Line.at]
      rw [mul_neg, mul_comm x f.d]
      omega
    tauto
  rw [ite_eq_right hneg]
  have hz : f.d = 0 := by omega
  simp [Line.at,hz]
  split <;> simp_all [Span.finset]

def Span.split (s : Span) (f : Line) : Span × Span :=
  (s.keep f, s.keep ⟨-f.a-1,-f.d⟩)

theorem split_sum (s : Span) (f : Line) (g : ℤ → ℤ) :
    (∑ x ∈ s.finset, g x) =
      (∑ x ∈ (s.split f).1.finset, g x) + ∑ x ∈ (s.split f).2.finset, g x := by
  unfold Span.split
  have hneg (x : ℤ) : 0 ≤ (Line.mk (-f.a-1) (-f.d)).at x ↔ f.at x < 0 := by
    simp only [Line.at, neg_mul]
    omega
  have hu : (s.keep f).finset ∪ (s.keep ⟨-f.a-1,-f.d⟩).finset = s.finset := by
    ext x
    simp only [mem_union, mem_keep, hneg]
    by_cases hx : x ∈ s.finset <;> simp [hx, le_or_gt 0 (f.at x)]
  have hd : Disjoint (s.keep f).finset (s.keep ⟨-f.a-1,-f.d⟩).finset := by
    refine disjoint_left.mpr fun x h₁ h₂ => ?_
    have ha := ((mem_keep s f x).mp h₁).2
    have hb := (hneg x).mp ((mem_keep s ⟨-f.a-1,-f.d⟩ x).mp h₂).2
    omega
  rw [← hu, sum_union hd]

def Span.size (s : Span) : ℕ := (s.hi-s.lo).toNat

theorem Span.sum_eq_range (s : Span) (g : ℤ → ℤ) :
    (∑ x ∈ s.finset, g x) = ∑ i ∈ range s.size, g (s.lo + (i : ℤ)) := by
  rw [Span.finset, Int.Ico_eq_finset_map, sum_map]
  rfl

open KoalaPiecewiseTriangle (lineBandSum)

def Span.charge (s : Span) (b : BandCuts) (l q : Line) : ℤ :=
  if s.hi ≤ s.lo ∨ (l.d = 0 ∧ l.a = b.l0) ∨ (q.d = 0 ∧ q.a = b.q1) then 0
  else lineBandSum b l q s.lo s.size


inductive ReceiptTree (α : Type)
  | leaf (a : α)
  | fork (cond : Line) (yes no : ReceiptTree α)

def ReceiptTree.eval {α : Type} : ReceiptTree α → ℤ → α
  | .leaf a, _ => a
  | .fork cond yes no, x => if 0 ≤ cond.at x then yes.eval x else no.eval x

def ReceiptTree.bind {α β : Type} (k : α → ReceiptTree β) : ReceiptTree α → ReceiptTree β
  | .leaf a => k a
  | .fork cond yes no => .fork cond (yes.bind k) (no.bind k)

theorem ReceiptTree.eval_bind {α β : Type} (k : α → ReceiptTree β) (t : ReceiptTree α) (x : ℤ) :
    (t.bind k).eval x = (k (t.eval x)).eval x := by
  induction t with
  | leaf a => rfl
  | fork cond yes no ihy ihn =>
    by_cases h : 0 ≤ cond.at x <;> simp [ReceiptTree.bind, ReceiptTree.eval, h, ihy, ihn]

def chooseMin (f g : Line) : ReceiptTree Line := .fork (g.sub f) (.leaf f) (.leaf g)


theorem chooseMin_at (f g : Line) (x : ℤ) :
    ((chooseMin f g).eval x).at x = min (f.at x) (g.at x) := by
  have h : (g.sub f).at x = g.at x - f.at x := by simp [Line.sub,Line.at]; ring
  simp only [chooseMin, ReceiptTree.eval, h, sub_nonneg]
  split <;> simp [min_def, *]


def ReceiptTree.receipt (b : BandCuts) : ReceiptTree (Line × Line) → Span → ℤ
  | .leaf pair, s => s.charge b pair.1 pair.2
  | .fork cond yes no, s =>
    if s.hi ≤ s.lo then 0 else
      let parts := s.split cond
      yes.receipt b parts.1 + no.receipt b parts.2


end KoalaLinearWindow

end Merged_KoalaLinearWindow

-- merged module Low48PrimaryPivotThreshold
section Merged_Low48PrimaryPivotThreshold
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Low48PrimaryPivot
open K1_13_2_3 KoalaLinearWindow KoalaPiecewiseTriangle Finset
open scoped BigOperators
open Low48PrimaryPivot (contactExpr contactExpr_eq)
theorem contact_ge_iff (p : Triple) (q : ℤ) (h : p.index ≤ 1650) :
    q ≤ (p.contact : ℤ) ↔
      (p.f : ℤ) ≤ 1650-q ∧
      (p.c : ℤ)+3*(p.f : ℤ) ≥ 3*q-9900+5*(p.index : ℤ) ∧
      (p.c : ℤ)+2*(p.f : ℤ) ≥ q-4950+3*(p.index : ℤ) ∧
      (p.c : ℤ)+(p.f : ℤ) ≥ 2*q-4950+2*(p.index : ℤ) := by
  rcases p with ⟨b,c,f⟩
  let r := b%3
  let t := b/3
  have hr : r < 3 := Nat.mod_lt _ (by decide)
  have hbt : 3*t+r = b := by dsimp [r,t]; omega
  have he := contactExpr_eq c f r t hr (by rwa [hbt])
  rw [hbt] at he
  rw [← he]
  simp only [contactExpr, Expr.at, Expr.const, Line.at, zero_mul, add_zero, le_min_iff]
  simp only [Triple.index, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  have hbt' : (b : ℤ) = 3*(t : ℤ)+(r : ℤ) := by omega
  omega
def sectionWidth (j f : ℕ) : ℤ := ((j : ℤ)-3*(f : ℤ))/2+1
def sectionFloor (j f : ℕ) (q : ℤ) : ℤ :=
  max 0 (max
    (3*q-9900+5*(j : ℤ)-3*(f : ℤ))
    (max (q-4950+3*(j : ℤ)-2*(f : ℤ)) (2*q-4950+2*(j : ℤ)-(f : ℤ))))
theorem section_count (j f : ℕ) (q : ℤ) (hf : (f : ℤ) ≤ 1650-q) (hj : j ≤ 1650)
    (h : 3*f ≤ j) :
    (((Ico (0 : ℤ) (sectionWidth j f)).filter fun c =>
        q ≤ (((Triple.mk (j-2*c.toNat-3*f) c.toNat f).contact) : ℤ)).card : ℤ) =
      max 0 (sectionWidth j f-sectionFloor j f q) := by
  have hset : ((Ico (0 : ℤ) (sectionWidth j f)).filter fun c =>
        q ≤ (((Triple.mk (j-2*c.toNat-3*f) c.toNat f).contact) : ℤ)) =
      Ico (sectionFloor j f q) (sectionWidth j f) := by
    ext c
    simp only [mem_filter,mem_Ico,sectionFloor,max_le_iff]
    constructor
    · rintro ⟨⟨hc,hu⟩,hq⟩
      have hidx : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index = j := by
        simp only [Triple.index]
        dsimp [sectionWidth] at hu
        omega
      have hh : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index ≤ 1650 := by rw [hidx]; exact hj
      rw [contact_ge_iff _ _ hh,hidx] at hq
      dsimp only at hq
      simp only [Int.toNat_of_nonneg hc] at hq
      omega
    · rintro ⟨⟨hc,h₁,h₂,h₃⟩,hu⟩
      refine ⟨⟨hc,hu⟩,?_⟩
      have hidx : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index = j := by
        simp only [Triple.index]
        dsimp [sectionWidth] at hu
        omega
      have hh : (Triple.mk (j-2*c.toNat-3*f) c.toNat f).index ≤ 1650 := by rw [hidx]; exact hj
      rw [contact_ge_iff _ _ hh,hidx]
      dsimp only
      simp only [Int.toNat_of_nonneg hc]
      omega
  rw [hset,Int.card_Ico]
  omega
#print axioms contact_ge_iff
#print axioms section_count
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotThreshold

-- merged module Low48PrimaryPivotSectionSum
section Merged_Low48PrimaryPivotSectionSum

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace KoalaLinearWindow
open Finset KoalaPiecewiseTriangle
open scoped BigOperators

def Span.sumLine (s : Span) (f : Line) : ℤ :=
  if s.lo < s.hi then (s.hi-s.lo)*(2*f.a+f.d*(s.lo+s.hi-1))/2 else 0

private theorem twice_sum_line (a d : ℤ) (n : ℕ) :
    2*(∑ i ∈ range n, (a+d*(i : ℤ))) =
      (n : ℤ)*(2*a+d*((n : ℤ)-1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [Nat.cast_succ]
    ring

theorem Span.sumLine_eq (s : Span) (f : Line) :
    s.sumLine f = ∑ x ∈ s.finset, f.at x := by
  unfold sumLine
  rw [s.sum_eq_range]
  by_cases hs : s.lo < s.hi
  · rw [ite_eq_left hs]
    have h (i : ℕ) : f.at (s.lo+(i : ℤ)) = (f.a+f.d*s.lo)+f.d*(i : ℤ) := by
      simp [Line.at]
      ring
    simp_rw [h]
    have he := twice_sum_line (f.a+f.d*s.lo) f.d s.size
    have hn : (s.size : ℤ) = s.hi-s.lo := by unfold size; omega
    rw [hn] at he
    rw [← Int.mul_ediv_cancel_left (∑ i ∈ range s.size, (f.a+f.d*s.lo+f.d*(i : ℤ)))
      (by decide : (2 : ℤ) ≠ 0),he]
    congr 1
    ring
  · rw [ite_eq_right hs]
    have h : s.size = 0 := by unfold size; omega
    simp [h]

def ReceiptTree.sumPositive : ReceiptTree Line → Span → ℤ
  | .leaf f, s => (s.keep f).sumLine f
  | .fork cond yes no, s =>
    if s.hi ≤ s.lo then 0 else
      let pair := s.split cond
      yes.sumPositive pair.1 + no.sumPositive pair.2

theorem ReceiptTree.sumPositive_eq (t : ReceiptTree Line) (s : Span) :
    t.sumPositive s = ∑ x ∈ s.finset, max 0 ((t.eval x).at x) := by
  induction t generalizing s with
  | leaf f =>
    rw [ReceiptTree.sumPositive,Span.sumLine_eq,split_sum s f]
    have eq (x : ℤ) : (ReceiptTree.leaf f).eval x = f := rfl
    simp only [eq]
    have hpos : (∑ x ∈ (s.split f).1.finset, max 0 (f.at x)) =
          ∑ x ∈ (s.keep f).finset, f.at x := by
      apply sum_congr rfl
      intro x hx
      rw [max_eq_right (((mem_keep s f x).mp hx).2)]
    have hneg : (∑ x ∈ (s.split f).2.finset, max 0 (f.at x)) = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [Span.split,mem_keep] at hx
      simp only [Line.at,neg_mul] at hx
      change max 0 (f.a+f.d*x) = 0
      rw [max_eq_left (by omega)]
    rw [hpos,hneg,add_zero]
  | fork cond yes no ihy ihn =>
    rw [ReceiptTree.sumPositive]
    split
    · rename_i h
      have hz : s.finset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := mem_Ico.mp hx
        omega
      simp [hz]
    dsimp only
    rw [ihy,ihn,split_sum s cond]
    congr 1
    · apply sum_congr rfl
      intro x hx
      rw [Span.split,mem_keep] at hx
      simp [ReceiptTree.eval,hx.2]
    · apply sum_congr rfl
      intro x hx
      rw [Span.split,mem_keep] at hx
      have hh : ¬0 ≤ cond.at x := by
        simp only [Line.at,neg_mul] at hx ⊢
        omega
      simp [ReceiptTree.eval,hh]

#print axioms Span.sumLine_eq
#print axioms ReceiptTree.sumPositive_eq
end KoalaLinearWindow

namespace Low48PrimaryPivot
open KoalaLinearWindow KoalaPiecewiseTriangle Finset K1_13_2_3
open scoped BigOperators

def paritySpan (fmax r : ℤ) : Span := ⟨0,(fmax-r)/2+1⟩

def widthLine (j r : ℤ) : Line := ⟨(j-3*r)/2+1,-3⟩

def countTree (j q r : ℤ) : ReceiptTree Line :=
  let k := (widthLine j r).a
  let a := widthLine j r
  let b : Line := ⟨k-(3*q-9900+5*j)+3*r,3⟩
  let c : Line := ⟨k-(q-4950+3*j)+2*r,1⟩
  let d : Line := ⟨k-(2*q-4950+2*j)+r,-1⟩
  ((chooseMin c d).bind (chooseMin b)).bind (chooseMin a)

theorem countTree_at (j q r x : ℤ) :
    ((countTree j q r).eval x).at x =
      (j-3*(2*x+r))/2+1 -
        max 0 (max (3*q-9900+5*j-3*(2*x+r))
          (max (q-4950+3*j-2*(2*x+r)) (2*q-4950+2*j-(2*x+r)))) := by
  simp only [countTree,ReceiptTree.eval_bind,chooseMin_at]
  simp only [widthLine,Line.at]
  omega

def uncharged (j q : ℤ) : ℤ :=
  let fmax := min (j/3) (1650-q)
  let c0 := (countTree j q 0).sumPositive (paritySpan fmax 0)
  let c1 := (countTree j q 1).sumPositive (paritySpan fmax 1)
  c0+c1

def totalAtIndex (j : ℤ) : ℤ :=
  let s0 := paritySpan (j/3) 0
  let s1 := paritySpan (j/3) 1
  s0.sumLine (widthLine j 0) + s1.sumLine (widthLine j 1)

def binWeight (w : Window) (j q : ℤ) : ℤ :=
  max 0 (min (min (j+1) (1651-(w.offsetLo : ℤ))) (q+(w.gradeHi : ℤ)-3000) -
    max (1650-(w.offsetHi : ℤ)) (q+(w.gradeLo : ℤ)-3000))

def binAt (w : Window) (j : ℕ) : ℤ :=
  let total := totalAtIndex j
  let q0 := w.diagonalHi
  ((List.range (w.diagonalHi+1-w.diagonalLo)).map fun i : ℕ =>
    let q : ℤ := 4650-(q0 : ℤ)+(i : ℤ)
    let volume := binWeight w j q
    if volume = 0 then 0 else volume*(total-uncharged j q)).sum

#print axioms countTree_at
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotSectionSum

-- merged module Low48PrimaryPivotBinParity
section Merged_Low48PrimaryPivotBinParity

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Low48PrimaryPivot
open Finset KoalaLinearWindow KoalaPiecewiseTriangle
open scoped BigOperators
open Low48PrimaryPivot (paritySpan widthLine countTree countTree_at)

private theorem sum_by_parity (m : ℤ) (f : ℤ → ℤ) :
    (∑ a ∈ Ico (0:ℤ) (m+1), f a) =
      (∑ u ∈ (paritySpan m 0).finset, f (2*u)) +
        ∑ u ∈ (paritySpan m 1).finset, f (2*u+1) := by
  let idx (r : ℤ) := (paritySpan m r).finset
  have htwo : Ico (0:ℤ) 2 = {0,1} := by decide
  have hsum : (∑ r ∈ Ico (0:ℤ) 2, ∑ u ∈ idx r, f (2*u+r)) =
      (∑ u ∈ idx 0, f (2*u)) + (∑ u ∈ idx 1, f (2*u+1)) := by
    rw [htwo]
    simp
  rw [← hsum, Finset.sum_sigma']
  refine sum_bij (fun a _ => (⟨a%2,a/2⟩ : Sigma (fun _ : ℤ => ℤ))) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_sigma,mem_Ico,idx,Span.finset,paritySpan] at ha ⊢
    omega
  · intro a _ b _ he
    have hmod := congrArg Sigma.fst he
    have hdiv := congrArg (fun p : Sigma (fun _ : ℤ => ℤ) => p.snd) he
    change a%2 = b%2 at hmod
    change a/2 = b/2 at hdiv
    omega
  · rintro ⟨r,u⟩ hx
    simp only [mem_sigma,mem_Ico,idx,Span.finset,paritySpan] at hx
    refine ⟨2*u+r,mem_Ico.mpr (by omega),?_⟩
    have hm : (2*u+r)%2 = r := by omega
    have hd : (2*u+r)/2 = u := by omega
    simp [hm,hd]
  · intro a _
    change f a = f (2*(a/2)+a%2)
    congr 1
    omega

theorem totalAtIndex_eq (j : ℤ) :
    totalAtIndex j = ∑ f ∈ Ico (0:ℤ) (j/3+1), ((j-3*f)/2+1) := by
  rw [sum_by_parity]
  unfold totalAtIndex
  simp only [Span.sumLine_eq,widthLine,Line.at]
  congr 1 <;> apply sum_congr rfl <;> intro u _ <;> omega

theorem uncharged_eq (j q : ℤ) :
    uncharged j q = ∑ f ∈ Ico (0:ℤ) (min (j/3) (1650-q)+1),
      max 0 ((j-3*f)/2+1 -
        max 0 (max (3*q-9900+5*j-3*f)
          (max (q-4950+3*j-2*f) (2*q-4950+2*j-f)))) := by
  rw [sum_by_parity]
  simp only [uncharged,ReceiptTree.sumPositive_eq,countTree_at,add_zero]

#print axioms totalAtIndex_eq
#print axioms uncharged_eq
end Low48PrimaryPivot

end Merged_Low48PrimaryPivotBinParity

end Merged_Low48PrimaryPivotBinParity

end Merged6967_Low48PrimaryPivotBinParity

section Merged6967_PortHighFinish
set_option Elab.async false



set_option Elab.async false

-- merged module PortFrontA
section Merged_PortFrontA
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
namespace P0_4
noncomputable section
open Polynomial P0
private theorem threeUAt_eq (q : ℕ) (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) :
    threeUAt q a β = K1_8.threeUAt q a β := by
  delta threeUAt K1_8.threeUAt P0.liftX K1.liftX P0.seed K1.seed P0.twist K1.twist P0.p K1.p
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem relationOnAt_eq (q : ℕ) (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOnAt q u S U V W = K1_8.relationOnAt q u S U V W := by
  delta relationOnAt K1_8.relationOnAt P0.node K1.node P0.Words K1.Words P0.I K1.I
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem columnRankAt_eq (q : ℕ) (U V : Bivar) :
    columnRankAt q U V = K1_8.columnRankAt q U V := by
  delta columnRankAt K1_8.columnRankAt P0.seed K1.seed P0.extendSeed K1.extendSeed
    P0.Bivar K1.Bivar P0.Frac K1.Frac P0.K K1.K
  rfl
open K1_8 (threeUAt_native)
private theorem native_threeU :
    threeUAt P0.p = (P0.threeU : (Polynomial K) → (Fin 2 → (Polynomial K)) → Bivar) := by
  unfold threeUAt P0.threeU
  rfl
theorem threeU_eq (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) :
    P0.threeU a β = K1.threeU a β := by
  calc
    P0.threeU a β = threeUAt P0.p a β := congrFun (congrFun native_threeU.symm a) β
    _ = K1_8.threeUAt P0.p a β := threeUAt_eq P0.p a β
    _ = K1_8.threeUAt K1.p a β := congrArg (fun q => K1_8.threeUAt q a β) (show P0.p = K1.p from rfl)
    _ = K1.threeU a β := congrFun (congrFun K1_8.threeUAt_native a) β
theorem relationOn_eq (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOn u S U V W = K1_8.relationOnAt K1.p u S U V W := by
  calc
    _ = relationOnAt P0.p u S U V W := by delta P0.relationOn relationOnAt; rfl
    _ = K1_8.relationOnAt P0.p u S U V W := relationOnAt_eq P0.p u S U V W
    _ = K1_8.relationOnAt K1.p u S U V W :=
      congrArg (fun q => K1_8.relationOnAt q u S U V W) (show P0.p = K1.p from rfl)
theorem columnRank_eq (U V : Bivar) : columnRank U V = K1.columnRank U V := by
  calc
    _ = columnRankAt P0.p U V := by delta P0.columnRank columnRankAt; rfl
    _ = K1_8.columnRankAt P0.p U V := columnRankAt_eq P0.p U V
    _ = K1_8.columnRankAt K1.p U V := congrArg (fun q => K1_8.columnRankAt q U V) (show P0.p = K1.p from rfl)
    _ = _ := by delta K1_8.columnRankAt K1.columnRank; rfl
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P0_4
noncomputable section
open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective extendSeedHom AmplitudeDirection)
open K1_8 (transfer_at)
open K1_8 (threeU_height threeV_height common_multiplier multiplier_degree_zero seed_scalar_coeff descend_scalar proportional_amplitudes rescale_threeU)
theorem sameDirection_eq (U V P Q : Bivar) :
    sameDirection U V P Q = K1.sameDirection U V P Q := by
  delta P0.sameDirection K1.sameDirection
  rfl
theorem threeV_eq (b : (Polynomial K)) (α : Fin 2 → (Polynomial K)) :
    threeV b α = K1.threeV b α := by
  delta P0.threeV K1.threeV P0.liftX K1.liftX P0.seed K1.seed
  rfl
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace P0_5
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)
open K1_9 (seedCoeff_degree)
abbrev heightBound : ℕ := 32781
structure PolarData (u : Words) where
  a : (Polynomial K)
  b : (Polynomial K)
  A : Fin 2 → (Polynomial K)
  Q : K → K → (Polynomial K)
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
theorem pow_eq_twist (z : K) : z ^ P0.p = twist z :=
  (frobenius_def P0.p z).symm
theorem threeUAt_native : threeUAt P0.p = P0.threeU := by
  unfold threeUAt P0.threeU
  rfl
theorem relationOnAt_native : relationOnAt P0.p = P0.relationOn := by
  unfold relationOnAt P0.relationOn
  rfl
theorem coefficientsAt (q : ℕ) (hq : 1 < q) (hσ : ∀ z : K, z ^ q = twist z)
    (u : Words) (deleted : Finset I) (a b : (Polynomial K)) (A B : Fin 2 → (Polynomial K))
    (output : P0.Bivar) (hp : A = B)
    (hn : relationOnAt q u deleted (threeUAt q a B) (P0.threeV b A) output)
    (i : I) (hi : i ∉ deleted) :
    (seedCoeff output 0).eval (node i) = crossValue u a b A i 0 0 ∧
    (seedCoeff output 1).eval (node i) = crossValue u a b A i 0 1 ∧
    (seedCoeff output q).eval (node i) = crossValue u a b A i 1 0 ∧
    (seedCoeff output (q + 1)).eval (node i) = crossValue u a b A i 1 1 := by
  subst B
  exact K1_9.coefficients_at_node u a b A i q hq hσ output (threeUAt q a A)
    (K1_9.eval_first a A i q) (hn i hi).symm
end
end P0_5
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P0_7
open P0 Finset
open K1_11 (V J)
def countRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (s + 1 - i) * (t + 1 - j)
def gradeRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (i + j) * ((s + 1 - i) * (t + 1 - j))
def count (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), countRow B s t i
def grade (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), gradeRow B s t i
def contactRow (m s t i : ℕ) : ℕ :=
  ∑ j ∈ range (m - i), (m - i - j) * (s + 1 - i) * (t + 1 - j)
theorem V_affine (D w B s t : ℕ) (hB : w * B ≤ D + 1) :
    V D w B s t + w * grade B s t = (D + 1) * count B s t := by
  unfold V count grade countRow gradeRow
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hij : i + j ≤ B := by
    simp only [mem_range] at hi hj
    omega
  have hw := (Nat.mul_le_mul_left w hij).trans hB
  calc
    _ = ((D + 1 - w * (i + j)) + w * (i + j)) * ((s + 1 - i) * (t + 1 - j)) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hw]
theorem rational_fee (E M exceptionFee limit a b : ℕ) (hb : 0 < b)
    (h : exceptionFee * b^2 + 5 * E * (a*M)^2 ≤ limit * b^2) :
    (exceptionFee : ℚ) + 5 * ((E : ℚ) * (((a : ℚ) / b) * M)^2) ≤ limit := by
  have hb' : 0 < (b : ℚ) := by exact_mod_cast hb
  have h' : (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 ≤
      (limit : ℚ) * (b : ℚ)^2 := by exact_mod_cast h
  refine le_of_mul_le_mul_right ?_ (pow_pos hb' 2)
  calc
    _ = (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 := by
      field_simp
    _ ≤ _ := h'
end P0_7
end

end Merged_PortFrontA

-- merged module RungFront
section Merged_RungFront
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace P1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective
  lift_locator_dvd coprime_after_factor)
open K1_8 (certificate_output_zero)
theorem eval_liftX (f : (Polynomial K)) (x : K) : (liftX f).eval (C x) = C (f.eval x) :=
  K1_8.eval_liftX f x
def constantsInFrac : K →+* Frac :=
  K1_8.seedInclusion.comp Polynomial.C
theorem extend_liftX (G : (Polynomial K)) :
    extendSeed (liftX G) = G.map constantsInFrac :=
  Polynomial.map_map Polynomial.C seedInclusion G
end
end P1
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open P0 (type_one_bad_count_of_syndromes)
open P0 (constantRankCount nativeMoments independent_nativeMoments)
open K1_1
theorem excludes_full_rank {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) [ExpChar F q] (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ q = x i) (u v : ι → F) (γ : F) (k l t : ℕ)
    (hsize : k + l + t ≤ Fintype.card ι) (P : (Polynomial F)) (hp : P.degree < k)
    (S : Finset ι) (hs : S.card ≤ t) (hagree : ∀ i ∉ S, u i + γ * v i = P.eval (x i)) :
    ((stacked q x u v l t).map (evalRingHom γ)).rank ≠ t + 1 := by
  classical
  let E := locator x S
  have hd : E.natDegree ≤ t := (locator_natDegree x S).le.trans hs
  let z : Fin (t+1) → F := fun j => E.coeff j.val
  let B := (stacked q x u v l t).map (evalRingHom γ)
  have hv : B.mulVecLin z = 0 :=
    locator_annihilates_stacked q x hx hfixed u v γ k l t hsize P hp S hs hagree
  intro hr
  have hi := Strata.matrix_injective_of_full_column_rank B (by rwa [Fintype.card_fin])
  have hz : z = 0 := hi (hv.trans (map_zero B.mulVecLin).symm)
  have h := congrFun hz (⟨E.natDegree, by omega⟩ : Fin (t+1))
  change E.coeff E.natDegree = 0 at h
  exact one_ne_zero ((locator_monic x S).coeff_natDegree.symm.trans h)
end
end P1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P1
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K1_6 (certificate_shifts_annihilate_generic)
open K1_6 (lift_common_divisor specialize_factor eval_atSlope root_outside_of_dvd_locator common_node_count)
theorem count_bound {c n n' H b : ℕ}
    (hn : n = n') (hc : c ≤ n * H) (hb : n' * H = b) : c ≤ b :=
  hb ▸ hn ▸ hc
end P1
end

end Merged_RungFront

-- merged module PortLow8
section Merged_PortLow8
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_8
open K1_13 (Shape InBox FatEligible)
open K1_13_8 (Valid zeroShape  availableMass)
open K1_13_8_2 (Threshold orderFor)
abbrev oneStart : Shape := ⟨1, 3, 1⟩
abbrev twoStart : Shape := ⟨2, 6, 2⟩
def oneOrder (x : Shape) : ℕ := if x.j ≤ 3 then 1 else (3 * x.j - 4) / 2
def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (48 - r.j)
end P0_9_8
end
section
namespace P0_9_8
open K1_13 (Shape InBox FatEligible remaining)
open K1_13_8 (Valid zeroShape  availableMass layerTerm)
open K1_13_8_2 (Threshold orderFor)
open scoped BigOperators
theorem symbol_count : ∀ b j, remaining b j = K1_13_8.fastRemaining b j :=
  K1_13_8_1.proof
theorem availableMass_anti_prefix {r y x : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j)
    (hb : y.b ≤ x.b) (hidx : y.j ≤ x.j) :
    availableMass r x L ≤ availableMass r y L := by
  let N := max (L + 1650 / (r.j + x.j)) (L + 1650 / (r.j + y.j))
  have hjx : 0 < r.j + x.j := by omega
  rw [← K1_13_8.availableMass_eq_sum symbol_count hr hjx (N := N) (le_max_left _ _),
    ← K1_13_8.availableMass_eq_sum symbol_count hr hj (N := N) (le_max_right _ _)]
  exact Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
    (Nat.add_le_add_left (Nat.mul_le_mul_left (k + 1 - L) hb) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left (k + 1 - L) hidx) _)
theorem orderFor_select (b j : ℕ) (ss : List Threshold) :
    1 ≤ orderFor b j ss ∧
    (orderFor b j ss = 1 ∨ ∃ s ∈ ss, s.b ≤ b ∧ s.j ≤ j ∧ orderFor b j ss = s.l) := by
  induction ss with
  | nil => simp [orderFor]
  | cons s ss ih =>
    unfold orderFor
    let p := if s.b ≤ b ∧ s.j ≤ j then s.l else 1
    change 1 ≤ max p (orderFor b j ss) ∧
      (max p (orderFor b j ss) = 1 ∨ ∃ q ∈ s :: ss,
        q.b ≤ b ∧ q.j ≤ j ∧ max p (orderFor b j ss) = q.l)
    refine ⟨ih.1.trans (le_max_right _ _), ?_⟩
    rcases le_total p (orderFor b j ss) with h | h
    · rw [max_eq_right h]
      rcases ih.2 with h1 | ⟨q, hq, hb, hj, hl⟩
      · exact Or.inl h1
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hb, hj, hl⟩
    · rw [max_eq_left h]
      by_cases hbox : s.b ≤ b ∧ s.j ≤ j
      · exact Or.inr ⟨s, List.mem_cons_self, hbox.1, hbox.2, ite_eq_left hbox⟩
      · exact Or.inl (ite_eq_right hbox)
theorem orderFor_mono {b b' j j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ss : List Threshold) :
    orderFor b j ss ≤ orderFor b' j' ss := by
  induction ss with
  | nil => exact le_rfl
  | cons s ss ih =>
    unfold orderFor
    by_cases h : s.b ≤ b ∧ s.j ≤ j
    · rw [ite_eq_left h, ite_eq_left ⟨h.1.trans hb, h.2.trans hj⟩]
      exact max_le_max le_rfl ih
    · rw [ite_eq_right h, max_eq_right (orderFor_select b j ss).1]
      exact ih.trans (le_max_right _ _)
end P0_9_8
end
section
namespace P0_9_8_3
open K1_13
open K1_13_8_2 (Chamber mixed_mono)
end P0_9_8_3
end
section
namespace P0_9_8_5
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open P0_9 ( physicalDegree  primaryBox taylorLength )
end P0_9_8_5
end

end Merged_PortLow8

-- merged module PortHighFinish
section Merged_PortHighFinish
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_10R
noncomputable section
open P0 (AnchorModel AnchoredFamily K highPrefix)
open P0_10 (BufferedPair BankVanishes freeShape movingShape fullShape MarkOn band TerminalDivisibility)
open K1_14 (Banks Equation)
open K1_14_3 (Surface Parent ProjectedProduct)
def SurfacePass {w : ℤ} {rows : Banks} {i : Fin 2} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ K1_14_3R.compatible pair.free pair.moving q
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) where
  kept : Finset K
  subset : kept ⊆ Γ
  paid : (Γ \ kept).card ≤ highPrefix M.overhead
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, (pairs 0).free ∈ q.asIdeal ∧ (pairs 0).moving ∈ q.asIdeal
  survives : ∀ q ∈ parents, SurfacePass (pairs 1) q
  terminal : ∀ q ∈ parents, BankVanishes rows (fullShape M.overhead) q
  covers : ∀ γ ∈ kept, ∃ q ∈ parents, MarkOn M F q γ
  equation : Equation
  projected : ProjectedProduct parents equation
  y_bound : equation.natDegree ≤ (band M.overhead).yBound
  divides : TerminalDivisibility M.overhead rows equation
end
end P0_10R
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily agreement p K t)
open P0_10 (BufferedPair)
open K1_14 (Banks Equation Jet Shape)
open K1_14_2 (Ambient ODE OnJet SmallRootCurve OnRoot endpointDegree)
open K1_14_2_2 (Active Fits)
open Polynomial
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def initialCap : Fin 4 → ℕ := ![5548, 125234, 577116, 5169640]
def initialE₀ : ℕ := 6242936
def initialFee : ℕ := (p+1)*577116 + initialE₀ + 5548 + (p+1)*(1036+4990)
structure InitialCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (P Q : Jet) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  initial : ∀ I ∈ parents, K1_14_2.toJet P ∈ I ∧ K1_14_2.toJet Q ∈ I
  masses : Fits parents initialCap
  direct : Finset K
  paid : direct.card ≤ initialFee
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end P0_10R.Bridge
namespace P0_10R.Later
noncomputable section
open Polynomial
open P0 (agreement)
open K1_14 (Jet Shape atX jetAt)
open K1_14_3 (Surface Parent MassCap mass JetPlane JetCaps SeedCover fixedAt)
open K1_14_3_2 (AtSurface)
structure InitialCover (P Q : Jet) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, P ∈ q.asIdeal ∧ Q ∈ q.asIdeal
  masses : MassCap parents 1643 28355 183584
  jetMass : mass parents .jets ≤ 1221580
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 183584 + 515 + 1857
  seedPoints : seeds.points.card ≤ 1221580
  ordinates : Finset K1_14.FX
  ordinateCount : ordinates.card ≤ 1643
  lowJet : JetPlane
  fixedFree : JetPlane
  fixedMoving : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedFree_ne : fixedFree ≠ 0
  fixedMoving_ne : fixedMoving ≠ 0
  lowJet_caps : JetCaps lowJet 183584 28355
  fixedFree_caps : JetCaps fixedFree 47 10
  fixedMoving_caps : JetCaps fixedMoving 93 18
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    seeds.Covers z ∨ atX S ∈ ordinates ∨ fixedAt lowJet S = 0 ∨
    fixedAt fixedFree S = 0 ∨ fixedAt fixedMoving S = 0 ∨
    ∃ q ∈ parents, AtSurface q z S
end
end P0_10R.Later
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 900000
namespace P0_10R.Bridge
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily agreement p lowCutoff)
open P0_10 (  terminalShape fullShape fullCutoff)
open K1_14 (Banks Shape Jet Equation Seeds FX seedHasse)
open K1_14_2 (Ambient toJet FibreRing mapGenericSeed mapGenericJets eval_toJet generic)
open K1_14_2_2 (Active dual)
open K1_14_3 (Surface Parent SeedClosure SeedField JetField JetClosure JetPlane seedFibreEval
  seedGeneric jetGeneric fixedEmbedding OrderAt ProjectedProduct)
open K1_14_2_6 (genericSeedPoint genericJetPoint)
open K1_14_2_2_4_1 (ambientToJet toJet_equiv)
open K1_14_2_6_1 (fibreHom seedMap jetMap seedPoint jetPoint)
open K1_14_3R_1 (seed_chart toJet_C toJet_y toJet_v toJet_seed jetCoordinates fractionCoordinates generic_C generic_Y generic_V seedGeneric_C)
def surfaceOf (I : Ideal Ambient) (hI : I.IsPrime) : Surface :=
  ⟨I.comap toJet, hI.comap _⟩
private theorem fixed_chart (a b : SeedClosure) :
    (genericJetPoint a b).comp (toJet.comp fixedEmbedding) =
      seedGeneric.comp jetCoordinates.symm.toRingHom := by
  have hV : ((genericJetPoint a b).comp (toJet.comp fixedEmbedding)) (Polynomial.X (R := (Polynomial FX))) =
      (seedGeneric.comp jetCoordinates.symm.toRingHom) Polynomial.X := by
    simp [fixedEmbedding, generic_V, toJet_v, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hV
  have hY : (((genericJetPoint a b).comp (toJet.comp fixedEmbedding)).comp C)
      (Polynomial.X (R := FX)) =
      ((seedGeneric.comp jetCoordinates.symm.toRingHom).comp C) Polynomial.X := by
    simp [fixedEmbedding, generic_Y, toJet_y, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hY
  ext x
  simp [fixedEmbedding, generic_C, toJet_C, genericJetPoint, seedGeneric_C]
private theorem surface_height {I : Ideal Ambient} (hI : I.IsPrime) (hh : I.height = 2) :
    (surfaceOf I hI).asIdeal.height = 2 := by
  change (I.comap toJet).height = 2
  rw [toJet_equiv]
  exact (ambientToJet.symm.height_comap I).trans hh
private theorem seed_side_of_active {I : Ideal Ambient} (hI : Active I) :
    ∃ y v, K1_14_3.OnSeedFibre (surfaceOf I hI.prime) y v ∧
      IsSeparable SeedField y ∧ IsSeparable SeedField v := by
  obtain ⟨f, hf, hsep⟩ := @fibreHom mapGenericSeed _ seedMap I hI.prime
    hI.seed_finite hI.seed_size.1 hI.seed_size.2
  refine ⟨f (MvPolynomial.X 0), f (MvPolynomial.X 1), ?_, hsep _, hsep _⟩
  unfold K1_14_3.OnSeedFibre
  rw [← seed_chart, ← RingHom.comap_ker, seedPoint, hf]
  rfl
private theorem jet_side_transport {I : Ideal Ambient} (hI : I.IsPrime)
    (a b : SeedClosure) (hjker : RingHom.ker (genericJetPoint a b) = I)
    (ha : IsSeparable SeedField a) (hb : IsSeparable SeedField b) :
    ∃ g : Jet →+* JetClosure,
      g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = (surfaceOf I hI).asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i)))) := by
  let e := fractionCoordinates.symm
  let top : JetField →+* JetClosure := algebraMap JetField JetClosure
  let : Algebra SeedField JetClosure := (top.comp e.toRingHom).toAlgebra
  let l : SeedClosure →ₐ[SeedField] JetClosure :=
    IsAlgClosed.lift (R := SeedField) (S := SeedClosure) (M := JetClosure)
  let F := l.toRingHom.comp ((genericJetPoint a b).comp toJet)
  have hscalar (x : SeedField) :
      l (algebraMap SeedField SeedClosure x) = algebraMap JetField JetClosure (e x) := by
    exact l.commutes x
  refine ⟨F, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l ((genericJetPoint a b).comp (toJet.comp fixedEmbedding) x) = _
    rw [fixed_chart, RingHom.comp_apply]
    change l (algebraMap SeedField SeedClosure (algebraMap Seeds SeedField
      (jetCoordinates.symm x))) = _
    rw [hscalar]
    change top (e (algebraMap Seeds SeedField (jetCoordinates.symm x))) =
      top (algebraMap JetPlane JetField x)
    apply congrArg top
    apply fractionCoordinates.injective
    rw [RingEquiv.apply_symm_apply]
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := JetPlane)
      (K := JetField) (B := Seeds) (L := SeedField) jetCoordinates.symm x).symm
  · change RingHom.ker (l.toRingHom.comp ((genericJetPoint a b).comp toJet)) = _
    rw [RingHom.ker_comp_of_injective _ l.injective, ← RingHom.comap_ker, hjker]
    rfl
  · have hs (x : SeedClosure) (hx : IsSeparable SeedField x) : IsSeparable JetField (l x) := by
      have hx' : (minpoly SeedField x).Separable := hx
      apply (hx'.map (f := e.toRingHom)).of_dvd
      apply minpoly.dvd
      rw [aeval_def, Polynomial.eval₂_map]
      change (minpoly SeedField x).eval₂ (algebraMap SeedField JetClosure) (l x) = 0
      rw [← aeval_def, aeval_algHom_apply l, minpoly.aeval, map_zero]
    intro i
    fin_cases i
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 0))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs a ha
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 1))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs b hb
theorem parent_of_dual {I : Ideal Ambient} (hI : Active I) (hh : I.height = 2) (hj : dual I) :
    Parent (surfaceOf I hI.prime) := by
  obtain ⟨g, hg, hsep⟩ := @fibreHom mapGenericJets _ jetMap I hI.prime hI.jet_finite hj hI.jet_lt
  have hker : RingHom.ker (genericJetPoint (g (MvPolynomial.X 0)) (g (MvPolynomial.X 1))) = I := by
    rw [jetPoint, hg]
  exact ⟨surface_height hI.prime hh, seed_side_of_active hI,
    jet_side_transport hI.prime _ _ hker (hsep _) (hsep _)⟩
end
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
private theorem donor_2_1 : K1_14_2_2_7_2.c1 :=
  K1_14_2_2_7_2_1.proof
private theorem donor_2_2_1 : K1_14_2_2_7_2_2.c1 :=
  K1_14_2_2_7_2_2_1.proof
private theorem donor_2_2_2 : K1_14_2_2_7_2_2.c2 :=
  K1_14_2_2_7_2_2_2.proof
private theorem donor_2_2_3 : K1_14_2_2_7_2_2.c3 :=
  K1_14_2_2_7_2_2_3.proof
private theorem donor_2_2 : K1_14_2_2_7_2.c2 :=
  K1_14_2_2_7_2_2.of_children donor_2_2_1 donor_2_2_2 donor_2_2_3
private theorem donor_2_3 : K1_14_2_2_7_2.c3 :=
  K1_14_2_2_7_2_3.proof
private theorem donor_2_4 : K1_14_2_2_7_2.c4 :=
  K1_14_2_2_7_2_4.proof
private theorem donor_2_5 : K1_14_2_2_7_2.c5 :=
  K1_14_2_2_7_2_5.proof
theorem cut_seed_mass : K1_14_2_2_7.c2 :=
  K1_14_2_2_7_2.of_children donor_2_1 donor_2_2 donor_2_3 donor_2_4 donor_2_5
private theorem donor_3_1 : K1_14_2_2_7_3.c1 :=
  K1_14_2_2_7_3_1.proof
private theorem donor_3_2 : K1_14_2_2_7_3.c2 :=
  K1_14_2_2_7_3_2.proof
private theorem donor_3_3_1_1 : K1_14_2_2_7_3_3_1.c1 :=
  K1_14_2_2_7_3_3_1_1.proof
private theorem donor_3_3_1_2 : K1_14_2_2_7_3_3_1.c2 :=
  K1_14_2_2_7_3_3_1_2.proof
private theorem donor_3_3_1_3 : K1_14_2_2_7_3_3_1.c3 :=
  K1_14_2_2_7_3_3_1_3.proof
private theorem donor_3_3_1_4 : K1_14_2_2_7_3_3_1.c4 :=
  K1_14_2_2_7_3_3_1_4.proof
private theorem donor_3_3_1 : K1_14_2_2_7_3_3.c1 :=
  K1_14_2_2_7_3_3_1.of_children donor_3_3_1_1 donor_3_3_1_2 donor_3_3_1_3 donor_3_3_1_4
private theorem donor_3_3_2 : K1_14_2_2_7_3_3.c2 :=
  K1_14_2_2_7_3_3_2.proof
private theorem donor_3_3 : K1_14_2_2_7_3.c3 :=
  K1_14_2_2_7_3_3.of_children donor_3_3_1 donor_3_3_2
theorem cut_ordinate_mass : K1_14_2_2_7.c3 :=
  K1_14_2_2_7_3.of_children donor_3_1 donor_3_2 donor_3_3
private theorem donor_4_1 : K1_14_2_2_7_4.c1 :=
  K1_14_2_2_7_4_1.proof
private theorem donor_4_2 : K1_14_2_2_7_4.c2 :=
  K1_14_2_2_7_4_2.proof
private theorem donor_4_3 : K1_14_2_2_7_4.c3 :=
  K1_14_2_2_7_4_3.proof
private theorem donor_4_4_1 : K1_14_2_2_7_4_4.c1 :=
  K1_14_2_2_7_4_4_1.proof
private theorem donor_4_4_2 : K1_14_2_2_7_4_4.c2 :=
  K1_14_2_2_7_4_4_2.proof
private theorem donor_4_4_3 : K1_14_2_2_7_4_4.c3 :=
  K1_14_2_2_7_4_4_3.proof
private theorem donor_4_4_4 : K1_14_2_2_7_4_4.c4 :=
  K1_14_2_2_7_4_4_4.proof
private theorem donor_4_4_5 : K1_14_2_2_7_4_4.c5 :=
  K1_14_2_2_7_4_4_5.proof
private theorem donor_4_4_6 : K1_14_2_2_7_4_4.c6 :=
  K1_14_2_2_7_4_4_6.proof
private theorem donor_4_4_7_1 : K1_14_2_2_7_4_4_7.c1 :=
  K1_14_2_2_7_4_4_7_1.proof
private theorem donor_4_4_7_2 : K1_14_2_2_7_4_4_7.c2 :=
  K1_14_2_2_7_4_4_7_2.proof
private theorem donor_4_4_7 : K1_14_2_2_7_4_4.c7 :=
  K1_14_2_2_7_4_4_7.of_children donor_4_4_7_1 donor_4_4_7_2
private theorem donor_4_4_8 : K1_14_2_2_7_4_4.c8 :=
  K1_14_2_2_7_4_4_8.proof
private theorem donor_4_4 : K1_14_2_2_7_4.c4 :=
  K1_14_2_2_7_4_4.of_children
    donor_4_4_1 donor_4_4_2 donor_4_4_3 donor_4_4_4 donor_4_4_5 donor_4_4_6 donor_4_4_7 donor_4_4_8
theorem cut_constant_count : K1_14_2_2_7.c4 :=
  K1_14_2_2_7_4.of_children donor_4_1 donor_4_2 donor_4_3 donor_4_4
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
private theorem donor_1_1_1 : K1_14_2_4_1_1.c1 :=
  K1_14_2_4_1_1_1.proof
private theorem donor_1_1_2 : K1_14_2_4_1_1.c2 :=
  K1_14_2_4_1_1_2.proof
theorem donor_1_1 : K1_14_2_4_1.c1 :=
  K1_14_2_4_1_1.of_children donor_1_1_1 donor_1_1_2
private theorem donor_1_2_1 : K1_14_2_4_1_2.c1 :=
  K1_14_2_4_1_2_1.proof
private theorem donor_1_2_2 : K1_14_2_4_1_2.c2 :=
  K1_14_2_4_1_2_2.proof
theorem donor_1_2 : K1_14_2_4_1.c2 :=
  K1_14_2_4_1_2.of_children donor_1_2_1 donor_1_2_2
private theorem donor_1_3_1 : K1_14_2_4_1_3.c1 :=
  K1_14_2_4_1_3_1.proof
private theorem donor_1_3_2_1 : K1_14_2_4_1_3_2.c1 :=
  K1_14_2_4_1_3_2_1.proof
private theorem donor_1_3_2_2 : K1_14_2_4_1_3_2.c2 :=
  K1_14_2_4_1_3_2_2.proof
private theorem donor_1_3_2 : K1_14_2_4_1_3.c2 :=
  K1_14_2_4_1_3_2.of_children donor_1_3_2_1 donor_1_3_2_2
private theorem donor_1_3_3_1 : K1_14_2_4_1_3_3.c1 :=
  K1_14_2_4_1_3_3_1.proof
private theorem donor_1_3_3_2 : K1_14_2_4_1_3_3.c2 :=
  K1_14_2_4_1_3_3_2.proof
private theorem donor_1_3_3_3 : K1_14_2_4_1_3_3.c3 :=
  K1_14_2_4_1_3_3_3.proof
private theorem donor_1_3_3 : K1_14_2_4_1_3.c3 :=
  K1_14_2_4_1_3_3.of_children donor_1_3_3_1 donor_1_3_3_2 donor_1_3_3_3
theorem donor_1_3 : K1_14_2_4_1.c3 :=
  K1_14_2_4_1_3.of_children donor_1_3_1 donor_1_3_2 donor_1_3_3
private theorem donor_1_4_1 : K1_14_2_4_1_4.c1 :=
  K1_14_2_4_1_4_1.proof
private theorem donor_1_4_2 : K1_14_2_4_1_4.c2 :=
  K1_14_2_4_1_4_2.proof
private theorem donor_1_4_3 : K1_14_2_4_1_4.c3 :=
  K1_14_2_4_1_4_3.proof
theorem donor_1_4 : K1_14_2_4_1.c4 :=
  K1_14_2_4_1_4.of_children donor_1_4_1 donor_1_4_2 donor_1_4_3
private theorem donor_1_5_1 : K1_14_2_4_1_5.c1 :=
  K1_14_2_4_1_5_1.proof
private theorem donor_1_5_2 : K1_14_2_4_1_5.c2 :=
  K1_14_2_4_1_5_2.proof
theorem donor_1_5 : K1_14_2_4_1.c5 :=
  K1_14_2_4_1_5.of_children donor_1_5_1 donor_1_5_2
private theorem donor_3_1_1 : K1_14_2_4_3_1.c1 :=
  K1_14_2_4_3_1_1.proof
private theorem donor_3_1_2 : K1_14_2_4_3_1.c2 :=
  K1_14_2_4_3_1_2.proof
private theorem donor_3_1_P0_10RBridgeRootDonors : K1_14_2_4_3.c1 :=
  K1_14_2_4_3_1.of_children donor_3_1_1 donor_3_1_2
private theorem donor_3_2_1 : K1_14_2_4_3_2.c1 :=
  K1_14_2_4_3_2_1.proof
private theorem donor_3_2_2 : K1_14_2_4_3_2.c2 :=
  K1_14_2_4_3_2_2.proof
private theorem donor_3_2_P0_10RBridgeRootDonors : K1_14_2_4_3.c2 :=
  K1_14_2_4_3_2.of_children donor_3_2_1 donor_3_2_2
theorem root_embedding : K1_14_2_4.c3 :=
  K1_14_2_4_3.of_children donor_3_1_P0_10RBridgeRootDonors donor_3_2_P0_10RBridgeRootDonors
end P0_10R.Bridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace P0_10R_1
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open P0_10R.Bridge (InitialCover OnParent initialCap initialE₀ initialFee)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover seed_count joinCovers joinCovers_degree joinCovers_points
  joinCovers_covers scalar_atX_injective)
open scoped BigOperators Classical
open K1_14_2_2_2_3 (jetEquiv jetEquiv_apply)
open K1_14_2_2_2_5_1 (properPair_height)
theorem section_bound : K1_14_2_2_2.c4 :=
  K1_14_2_2_2_4.of_children K1_14_2_2_2_4_1.proof K1_14_2_2_2_4_2.proof K1_14_2_2_2_4_3.proof
theorem seed_projection : K1_14_2_2_2.c6 :=
  K1_14_2_2_2_6.of_children K1_14_2_2_2_6_1.proof K1_14_2_2_2_6_2.proof
private theorem height_le {I : Ideal Ambient} (hI : I.IsPrime)
    (hdim : ringKrullDim (CoordinateRing I) = 2) : I.height ≤ 2 := by
  let x : PrimeSpectrum Ambient := ⟨I, hI⟩
  have hc : Order.coheight x = 2 := by
    rw [ringKrullDim_quotient] at hdim
    change Order.krullDim (Set.Ici x) = 2 at hdim
    rw [← Order.coheight_eq_krullDim_Ici] at hdim
    exact WithBot.coe_injective hdim
  have hd : ringKrullDim Ambient = 4 := by simp [ringKrullDim_eq_zero_of_field]
  have hh : (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ ringKrullDim Ambient := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : PrimeSpectrum Ambient =>
      Order.height y + Order.coheight y) x)
  rw [hc, ← x.height_eq_orderHeight, hd] at hh
  have hh' : I.height + 2 ≤ (2 : ℕ∞) + 2 := WithBot.coe_le_coe.mp hh
  exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp hh'
theorem component_height {P Q : Jet} {I : Ideal Ambient} (hp : ProperPair P Q)
    (hI : I.IsPrime) (hdim : ringKrullDim (CoordinateRing I) = 2)
    (hP : toJet P ∈ I) (hQ : toJet Q ∈ I) : I.height = 2 := by
  let J := I.comap K1_14_2_2_2_3.jetEquiv.toRingHom
  let : J.IsPrime := hI.comap _
  have hP' : P ∈ J := by change K1_14_2_2_2_3.jetEquiv P ∈ I; rwa [jetEquiv_apply]
  have hQ' : Q ∈ J := by change K1_14_2_2_2_3.jetEquiv Q ∈ I; rwa [jetEquiv_apply]
  exact le_antisymm (height_le hI hdim)
    ((K1_14_2_2_2_3.jetEquiv.height_comap I) ▸ properPair_height hp J hP' hQ')
theorem ordinary_cover (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient),
      (∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet (C f) ∈ I) ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨g, a, hclear, hproper, hfCaps, hgCaps⟩ := K1_14_3_4_2.proof f hi hd hp
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hproper
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hproper
    ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩
    (Nat.zero_le _) hd hfCaps hgCaps S hS
  refine ⟨S, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
    exact ⟨hprime, hdim, component_height hproper hprime hdim hrow hcut, hfinite I hI, hrow⟩
  · intro k
    have h := hfits k
    fin_cases k <;> simpa [residualBudget, ordinaryBudget, two_mul, Nat.add_mul] using h
  · intro z R hz
    exact hcover z R (by simpa [jetAt, atMark] using hz) (K1_14_3R.chainCutter_zero hclear hz)
end
end P0_10R_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P0_10R_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open K1_14_2_2_4_1 (factor_caps natDegree_zero_of_factors dvd_of_dvd_residual toJet_equiv ambientToJet)
structure SharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t) where
  ordinary : Equation
  left : Jet
  right : Jet
  ordinary_ne : ordinary ≠ 0
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  left_factor : P = fixedIncl A.equation * (C ordinary * left)
  right_factor : Q = fixedIncl B.equation * (C ordinary * right)
  relativelyPrime : IsRelPrime (toJet left) (toJet right)
  seed_le : seedDegree ordinary ≤ s.U
  ordinate_le : ordinary.natDegree ≤ s.B
  left_caps : RowCaps left (residualShape s (seedDegree ordinary) ordinary.natDegree)
  right_caps : RowCaps right (residualShape t (seedDegree ordinary) ordinary.natDegree)
theorem sharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPs : RowCaps P s) (hQs : RowCaps Q t)
    (hno : K1_14_3.NoMovingCommon P Q) : Nonempty (SharedGcd A B) := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  let gcdJet : GCDMonoid Jet := UniqueFactorizationMonoid.toGCDMonoid Jet
  let D : Jet := gcdJet.gcd A.residual B.residual
  obtain ⟨L, R, hL, hR, hrel⟩ := @extract_gcd Jet _ gcdJet A.residual B.residual
  change A.residual = D * L at hL
  change B.residual = D * R at hR
  have hF : P = fixedIncl A.equation * (D * L) :=
    A.factorization.trans (congrArg (fixedIncl A.equation * ·) hL)
  have hG : Q = fixedIncl B.equation * (D * R) :=
    B.factorization.trans (congrArg (fixedIncl B.equation * ·) hR)
  have hFL := right_ne_zero_of_mul (hF ▸ hP)
  have hGR := right_ne_zero_of_mul (hG ▸ hQ)
  have hDne := left_ne_zero_of_mul hFL
  have hDdeg : D.natDegree = 0 := by
    apply natDegree_zero_of_factors
    intro F hIrr hfd
    by_contra hpos
    have hleft := hfd.trans (gcdJet.gcd_dvd_left A.residual B.residual)
    have hright := hfd.trans (gcdJet.gcd_dvd_right A.residual B.residual)
    obtain ⟨G, hG⟩ := hno F hIrr (dvd_of_dvd_residual A hleft)
      (dvd_of_dvd_residual B hright) (Nat.pos_of_ne_zero hpos)
    exact A.stripped G (hG ▸ hIrr) (hG ▸ hleft)
  let H := D.coeff 0
  have hD : D = C H := eq_C_of_natDegree_eq_zero hDdeg
  have hH : H ≠ 0 := fun hz => hDne (by rw [hD, hz, map_zero])
  rw [hD] at hF hG
  obtain ⟨hFu, hFb, hLc⟩ := factor_caps hP hH hPs hF
  obtain ⟨_, _, hRc⟩ := factor_caps hQ hH hQs hG
  have hprime : IsRelPrime (toJet L) (toJet R) := by
    have hr := (@gcd_isUnit_iff_isRelPrime Jet _ gcdJet L R).mp hrel
    rw [toJet_equiv]
    intro E hEL hER
    have h1 : ambientToJet E ∣ L := by
      simpa using map_dvd ambientToJet.toRingHom hEL
    have h2 : ambientToJet E ∣ R := by
      simpa using map_dvd ambientToJet.toRingHom hER
    simpa using (hr h1 h2).map ambientToJet.symm.toRingHom
  exact ⟨⟨H, L, R, hH, right_ne_zero_of_mul hFL, right_ne_zero_of_mul hGR,
    hF, hG, hprime, hFu, hFb, hLc, hRc⟩⟩
end
end P0_10R_2
end

end Merged_PortHighFinish

end Merged6967_PortHighFinish

section Merged6967_PortLow6
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_6
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (SmallFactor physicalDegree primaryBox primaryCutoff taylorLength TrueWeightLE)
open K1_13 (Geom Row Shape shape extend InBox OnFactor OrderAt chart mixed32)
open K1_13_6 (HighChart toGeneric markIdeal separant jetNumerator divisorIdeal cycleLength)
structure CutInput (Γ : Finset K) (s : K → (Polynomial K)) (f Q : Row 4) (l : ℕ) : Prop where
  distinct : Set.InjOn s (Γ : Set K)
  degree : ∀ γ ∈ Γ, (s γ).natDegree ≤ physicalDegree
  small : SmallFactor f
  onFactor : ∀ γ ∈ Γ, OnFactor f (extend (s γ))
  positive : 0 < l
  proper : ¬ f ∣ Q
  box : InBox (shape Q) primaryBox
  weight : TrueWeightLE Q primaryCutoff
  order : ∀ γ ∈ Γ, OrderAt Q (extend (s γ)) l
def membershipTest (g : Row 4) : Row 4 := jetNumerator g taylorLength
def nextTest (g : Row 4) : Row 4 := jetNumerator g (taylorLength + 1)
def auxCurves32 (x : Shape) : ℕ :=
  let p := x.chamber
  let h := chart taylorLength p
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) h + 2 * x.t * mixed32 p p p h
def auxPoints32 (x : Shape) : ℕ :=
  let p := x.chamber
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) p + 2 * x.t * mixed32 p p p p
end
end P0_9_6
end
section
namespace P0_9_6_1
noncomputable section
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_1 (anchorBox DerivativeWeight)
open P0_9 (primaryBox)
def SurfaceCut (f Q : Row 4) (surface : Ideal GeoJets) (P : Row 4) : Prop :=
  ∃ (hZ : (intersectionIdeal f Q).IsMinimalPrime surface) (v w : ℕ),
    0 < v ∧ cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
    (w = 0 ∨ ∃ r, 0 < r ∧ r < (shape f).t ∧ DerivativeWeight f surface r w) ∧
    toGeneric P ∉ surface ∧
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale (4*v + 2*w)))
end
end P0_9_6_1
end
section
namespace P0_9_6_1
noncomputable section
open Polynomial
open K1_13 (Row Geom Shape shape InBox extend atJet OnFactor OrderAt)
open K1_13_6 (GeoJets CanonicalChart HighMark Invariant separant toGeneric
  markIdeal intersectionIdeal cycleLength genericCoeffs)
open K1_13_6_1 (HasMark anchorBox tangentCut DerivativeWeight
  mem_markIdeal orderAt_vanishes tangentCut_vanishes)
open K1_13_6_1_2 (VanishesTo multiOrder hassePartial map_hassePartial
  cycleLength_pos cycleLength_ge_order pair_height hasse_inBox hasse_atJet_eq_zero)
open K1_13_6_1_3 (tangent_proper tangent_box anchor_fits derivative_fits)
open P0_9 (SmallFactor primaryBox)
open P0_9_6 (CutInput)
open K1_13_7_1 (topAt topAt_coeff eval_topAt topView_separant)
theorem canonicalChart {f : Row 4} {surface : Ideal GeoJets} {S : (Polynomial Geom)}
    (htop : (shape f).t ≤ 10) (hon : OnFactor f S)
    (hfmem : toGeneric f ∈ surface) (hmark : surface ≤ markIdeal S) :
    ∃ r, CanonicalChart f surface r ∧
      InBox (shape (separant ((separant^[r]) f))) (anchorBox f) := by
  classical
  let t := (shape f).t
  let P := topAt S f
  have hdeg : P.natDegree ≤ t := Polynomial.natDegree_map_le.trans_eq
    (K1_13_1.topView_degree f)
  have hnz : (derivative^[t] P).coeff 0 ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    change (t.factorial : (Polynomial Geom)) * P.coeff t ≠ 0
    rw [← map_natCast (Polynomial.C : Geom →+* (Polynomial Geom))]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      (K1_13_7_1.factorial_cast_ne_zero (htop.trans_lt (by decide : 10 < K1.p))))
      (by simpa only [P, t, topAt_coeff] using hon.2)
  have hc : derivative^[t] P = Polynomial.C ((derivative^[t] P).coeff 0) :=
    eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans
      (by omega : P.natDegree - t ≤ 0))
  have he (k : ℕ) : atJet ((separant^[k]) f) S =
      (derivative^[k] P).eval (K1_13.jet S (3 : Fin 4)) := by
    rw [← eval_topAt]
    congr 1
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      change (K1_13_1.topView (separant ((separant^[k]) f))).map
        (MvPolynomial.eval (K1_13.jet S)) = _
      rw [topView_separant, ← derivative_map]
      exact congrArg derivative ih
  have htSurface : toGeneric ((separant^[t]) f) ∉ surface := by
    intro hm
    have hv := mem_markIdeal.mp (hmark hm)
    rw [he, hc, Polynomial.eval_C] at hv
    exact hnz hv
  have hex : ∃ i, toGeneric ((separant^[i]) f) ∉ surface := ⟨t, htSurface⟩
  let n := Nat.find hex
  have hn : toGeneric ((separant^[n]) f) ∉ surface := Nat.find_spec hex
  have hnt : n ≤ (shape f).t := Nat.find_min' hex htSurface
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (by simpa only [h, Function.iterate_zero_apply] using hfmem)
  have hstep : (n - 1).succ = n := by omega
  have hsep : separant ((separant^[n - 1]) f) = (separant^[n]) f := by
    rw [← Function.iterate_succ_apply' separant (n - 1) f, hstep]
  refine ⟨n - 1, ⟨by omega, ?_, ?_⟩, ?_⟩
  · intro i hi
    by_contra h
    exact Nat.find_min hex (show i < n by omega) h
  · rwa [hsep]
  · rw [hsep]
    exact derivative_fits f n
theorem lowHasse {f Q : Row 4} {l : ℕ} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal f Q).IsMinimalPrime surface)
    (hf : Irreducible f) (hproper : ¬ f ∣ Q) (hbox : InBox (shape Q) primaryBox) :
    ∃ v : ℕ, 0 < v ∧ v ≤ (shape f).b * primaryBox.b ∧
      cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) ∧
      (v < l → ∃ P : Row 4, toGeneric P ∉ surface ∧ InBox (shape P) primaryBox ∧
        ∀ S, OrderAt Q S l → atJet P S = 0) := by
  let _ : surface.IsPrime := hZ.isPrime
  have hf0 : toGeneric f ≠ 0 := fun h =>
    hf.ne_zero (K1_13_7_1.toGeneric_injective (h.trans (map_zero _).symm))
  have hrel := K1_13_7_1.proper_generic f Q hf hproper
  have hheight : surface.height = 2 := pair_height hf0 hrel hZ
  have hdeg (P : Row 4) : (toGeneric P).totalDegree ≤ (shape P).b :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hup : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≤
      (↑((shape f).b * primaryBox.b) : ℕ∞) :=
    (K1_13_6_1_2_1.proof _ _ _ hZ hf0 hrel).trans
      (by exact_mod_cast Nat.mul_le_mul (hdeg f) ((hdeg Q).trans hbox.1))
  have hnotop : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≠ ⊤ :=
    ne_of_lt (hup.trans_lt (ENat.natCast_lt_top _))
  let v := (cycleLength (intersectionIdeal f Q) surface hZ.isPrime).toNat
  have hv : cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) :=
    (ENat.natCast_toNat hnotop).symm
  have hpos := cycleLength_pos hZ.isPrime hZ.le
  rw [hv] at hpos hup
  refine ⟨v, by exact_mod_cast hpos, by exact_mod_cast hup, hv, ?_⟩
  intro hl
  have hcut : ∃ a : Fin 4 →₀ ℕ, multiOrder a < v + 1 ∧
      toGeneric (hassePartial a Q) ∉ surface := by
    by_contra! hn
    have horder : VanishesTo surface (toGeneric Q) (v + 1) := by
      apply K1_13_6_1_2_2.proof _ surface (v + 1) hheight
      intro a ha
      change hassePartial a (MvPolynomial.map genericCoeffs Q) ∈ surface
      rw [← map_hassePartial genericCoeffs a Q]
      exact hn a ha
    have hfp : toGeneric f ∈ surface := hZ.le (Ideal.subset_span (by simp))
    have hge := cycleLength_ge_order hheight hfp horder
    rw [hv] at hge
    exact (by omega : ¬ v + 1 ≤ v) (by exact_mod_cast hge)
  obtain ⟨a, ha, hproper'⟩ := hcut
  exact ⟨hassePartial a Q, hproper', hasse_inBox a hbox,
    fun S hS => hasse_atJet_eq_zero (by omega) hS⟩
theorem chart_cut {g P : Row 4} {surface : Ideal GeoJets}
    (hZ : (intersectionIdeal g P).IsMinimalPrime surface)
    (hrel : IsRelPrime (toGeneric g) (toGeneric P)) (hsep : toGeneric (separant g) ∉ surface)
    (hi : ¬ Invariant g surface) {v : ℕ} (hv : 0 < v) (hchar : v < K1.p)
    (hlen : cycleLength (intersectionIdeal g P) surface hZ.isPrime = (v : ℕ∞)) :
    toGeneric (tangentCut g P v) ∉ surface := by
  have hg : toGeneric g ∈ surface := hZ.le (Ideal.subset_span (Set.mem_insert _ _))
  have hlen' := K1_13_6_1_3_3.proof g P surface hZ v hlen hchar
  have hn := K1_13_6_1_3_2.proof g P surface hZ v hrel hsep hv hlen'
  exact tangent_proper hZ.isPrime hg hi hchar hn
theorem derivative_proper {f : Row 4} (hf : Irreducible f) (ht : 0 < (shape f).t) (j : ℕ)
    (hj : 0 < j) (hg : (separant^[j]) f ≠ 0) : ¬ f ∣ (separant^[j]) f := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hz
    exact hg (by rw [hq, hz, mul_zero])
  have hd := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hq0
  have h := K1_13_7_1.derivative_degree f j
  change ((separant^[j]) f).degreeOf 3 ≤ f.degreeOf 3 - j at h
  change 0 < f.degreeOf 3 at ht
  rw [hq, hd] at h
  omega
theorem box_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) ((anchorBox f).scale k)) (hkj : k ≤ j) :
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h2.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _)),
    h3.trans ((Nat.mul_le_mul_right _ hkj).trans (Nat.le_add_left _ _))⟩
theorem box_cutter_charge {f P : Row 4} {k j : ℕ}
    (hP : InBox (shape P) (primaryBox.plus ((anchorBox f).scale k))) (hkj : k ≤ j) :
    InBox (shape P) (primaryBox.plus ((anchorBox f).scale j)) := by
  rcases hP with ⟨h1, h2, h3⟩
  exact ⟨h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _),
    h3.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hkj) _)⟩
end
end P0_9_6_1
end
section
namespace P0_9_6
noncomputable section
open Polynomial
open P0 (K)
open P0_9 ( primaryBox  taylorLength)
open K1_13 (Row Shape Geom extend atJet shape ceilDiv)
open K1_13_6 (Pieces toGeneric
  separant jetNumerator HighMark divisorIdeal cycleLength eval_jetNumerator)
open K1_13_6_1 (mem_markIdeal mark_curve)
open scoped BigOperators
def c1 : Prop :=
  ∀ Γ s f Q l, CutInput Γ s f Q l →
    ∃ (C : Pieces Γ) (B : Finset K),
      C.curves s ∧
      (∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      32 * C.total ≤ auxCurves32 (shape f) ∧
      32 * (B.card + C.n) ≤ 2 * auxPoints32 (shape f)
end
end P0_9_6
end
section
namespace P0_9_6_1_1
noncomputable section
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength divisorIdeal separant)
open K1_13_6_1 (anchorBox DerivativeWeight CurveOnFactor sectionDegree)
open K1_13_6_1_4 (FullChamber pair_dimension curve_of_proper_cut surfaceDegree)
open K1_13_7_1 (Chamber GeoFits toGeneric_fits toGeneric_injective proper_generic shape_chamber chart_chamber)
open P0_9 (SmallFactor primaryBox taylorLength)
open P0_9_6_1 (SurfaceCut)
open scoped BigOperators
theorem proper_divisor : K1_13_6_1_4.c1 :=
  K1_13_6_1_4_1.of_children K1_13_6_1_4_1_1.proof K1_13_6_1_4_1_2.proof
theorem additive_sections : K1_13_6_1_4.c2 := by
  apply K1_13_6_1_4_2.of_children
  · apply K1_13_6_1_4_2_1.of_children
    · exact K1_13_6_1_4_2_1_1.of_children
        K1_13_6_1_4_2_1_1_1.proof K1_13_6_1_4_2_1_1_2.proof
    · exact K1_13_6_1_4_2_1_2.of_children K1_13_6_1_4_2_1_2_1.proof
        (K1_13_6_1_4_2_1_2_2.of_children
          K1_13_6_1_4_2_1_2_2_1.proof K1_13_6_1_4_2_1_2_2_2.proof)
  · exact K1_13_6_1_4_2_2.of_children
      K1_13_6_1_4_2_2_1.proof K1_13_6_1_4_2_2_2.proof
theorem weighted_pair : K1_13_6_1_4.c3 := by
  refine K1_13_6_1_4_3.of_children K1_13_6_1_4_3_1.proof K1_13_6_1_4_3_2.proof ?_
  apply K1_13_6_1_4_3_3.of_children
  · exact K1_13_6_1_4_3_3_1.of_children
      K1_13_6_1_4_3_3_1_1.proof K1_13_6_1_4_3_3_1_2.proof
  · exact K1_13_6_1_4_3_3_2.of_children
      K1_13_6_1_4_3_3_2_1.proof K1_13_6_1_4_3_3_2_2.proof
  · exact K1_13_6_1_4_3_3_3.of_children K1_13_6_1_4_3_3_3_1.proof
      (K1_13_6_1_4_3_3_3_2.of_children
        K1_13_6_1_4_3_3_3_2_1.proof K1_13_6_1_4_3_3_3_2_2.proof)
theorem full_chart (L : ℕ) (hL : 0 < L) (p : Shape) : FullChamber (chart L p) := by
  refine ⟨chart_chamber _ _, ?_⟩
  change 0 < min (2*L*(p.t-1)+L+1) ((2*L*(p.j-3)+L+3)/3)
  omega
theorem full_plus {a b : Shape} (ha : FullChamber a) (hb : Chamber b) :
    FullChamber (a.plus b) := by
  obtain ⟨⟨ha₁, ha₂⟩, ha₃⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  change (a.j + b.j ≤ a.b + b.b ∧ 3 * (a.t + b.t) ≤ a.j + b.j) ∧ 0 < a.t + b.t
  exact ⟨⟨by omega, by omega⟩, by omega⟩
theorem chamber_scale {a : Shape} (ha : Chamber a) (k : ℕ) :
    Chamber (a.scale k) := by
  refine ⟨Nat.mul_le_mul_left k ha.1, ?_⟩
  simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k ha.2
theorem full_scale {a : Shape} (ha : FullChamber a) {k : ℕ} (hk : 0 < k) :
    FullChamber (a.scale k) :=
  ⟨chamber_scale ha.1 k, Nat.mul_pos hk ha.2⟩
private theorem charge_coord (q p v w : ℕ) (hv : 0 < v) :
    q + (4*v + 2*w) * p ≤ v*(q + 4*p) + (2*w)*p := by
  calc
    _ = q + v*(4*p) + (2*w)*p := by ring
    _ ≤ v*q + v*(4*p) + (2*w)*p := by
      have hq : q ≤ v*q := Nat.le_mul_of_pos_left q hv
      exact Nat.add_le_add_right (Nat.add_le_add_right hq _) _
    _ = _ := by ring
theorem supported_charge {f P : Row 4} {v w : ℕ} (hv : 0 < v)
    (h : InBox (shape P) (primaryBox.plus ((anchorBox f).scale (4*v + 2*w)))) :
    GeoFits (toGeneric P)
      (((primaryBox.plus ((anchorBox f).scale 4)).scale v).plus ((anchorBox f).scale (2*w))) :=
  toGeneric_fits ⟨h.1.trans (charge_coord _ _ _ _ hv),
    h.2.1.trans (charge_coord _ _ _ _ hv), h.2.2.trans (charge_coord _ _ _ _ hv)⟩
theorem sum_biUnion_bound {α β : Type*} [DecidableEq β]
    (s : Finset α) (pieces : α → Finset β) (d : β → ℕ) :
    (∑ b ∈ s.biUnion pieces, d b) ≤ ∑ a ∈ s, ∑ b ∈ pieces a, d b := by
  rw [← Finset.sup_eq_biUnion]
  refine s.apply_sup_le_sum (f := fun t => ∑ b ∈ t, d b) (by simp) ?_
  intro u v
  change (∑ b ∈ u ∪ v, d b) ≤ _
  have heq := Finset.sum_union_inter (s₁ := u) (s₂ := v) (f := d)
  omega
theorem toGeneric_ne_zero {F : Row 4} (hF : F ≠ 0) : toGeneric F ≠ 0 := by
  intro h
  apply hF
  apply toGeneric_injective
  simpa only [toGeneric, map_zero] using h
end
end P0_9_6_1_1
end
section
namespace P0_9_6_1_2
noncomputable section
open Polynomial MvPolynomial
open K1 (K)
open K1_13 (Row Shape Geom InBox embed extend chart atJet)
open K1_13_6 (GeoJets GeoField genericCoeffs evalGeneric toGeneric separant jetNumerator
  eval_jetNumerator)
open K1_13_6_2_1 (three_weights separant_pow_bound jet_bound)
open K1_13_7 (RegularAt)
open K1_13_7_1 (Chamber GeoFits weight_X_le weight_const_mul_le factorial_cast_ne_zero
  evalGeneric_toGeneric genericCoeffs_injective)
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private structure TaylorChart (L : ℕ) where
  denom : GeoJets
  numerator : Fin L → GeoJets
private def TaylorChart.Fits {L : ℕ} (T : TaylorChart L) (h : Shape) : Prop :=
  GeoFits T.denom h ∧ ∀ i, GeoFits (T.numerator i) h
private def TaylorChart.Recovers {L : ℕ} (T : TaylorChart L) (S : (Polynomial Geom)) : Prop :=
  evalGeneric S T.denom ≠ 0 ∧
    ∀ i, evalGeneric S (T.numerator i) =
      evalGeneric S T.denom * genericCoeffs (hasseDeriv i.val S)
private abbrev AffineForm (L : ℕ) := GeoField × (Fin L → GeoField)
private def TaylorChart.pullback {L : ℕ} (T : TaylorChart L) (a : AffineForm L) : GeoJets :=
  MvPolynomial.C a.1 * T.denom + ∑ i, MvPolynomial.C (a.2 i) * T.numerator i
private theorem TaylorChart.pullback_fits {L : ℕ} (T : TaylorChart L) {h : Shape}
    (hT : T.Fits h) (a : AffineForm L) : GeoFits (T.pullback a) h := by
  classical
  have hw (w : Fin 4 → ℕ) (d : ℕ) (hD : T.denom.weightedTotalDegree w ≤ d)
      (hN : ∀ i, (T.numerator i).weightedTotalDegree w ≤ d) :
      (T.pullback a).weightedTotalDegree w ≤ d := by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans hD)
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans (hN i))
  refine ⟨?_, hw Fin.val h.j hT.1.2.1 (fun i => (hT.2 i).2.1), ?_⟩
  · simpa only [weightedTotalDegree_one] using hw 1 h.b
      (by simpa only [weightedTotalDegree_one] using hT.1.1)
      (fun i => by simpa only [weightedTotalDegree_one] using (hT.2 i).1)
  · simpa only [weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) h.t
      (by simpa only [weightedTotalDegree_piSingle] using hT.1.2.2)
      (fun i => by simpa only [weightedTotalDegree_piSingle] using (hT.2 i).2.2)
private def denominator (L : ℕ) (g : Row 4) : Row 4 :=
  separant g ^ (2 * L)
private def numerator (L : ℕ) (g : Row 4) (i : Fin L) : Row 4 :=
  if hi : i.val < 4 then MvPolynomial.X ⟨i.val, hi⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - i.val)) * jetNumerator g i.val)
private def recoveryChart (L : ℕ) (g : Row 4) : TaylorChart L where
  denom := toGeneric (denominator L g)
  numerator i := toGeneric (numerator L g i)
private theorem numerator_bound {L : ℕ} (w : Fin 4 → ℕ) (Δ d₀ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : Fin L) :
    W w (numerator L g i) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  have hi : i.val ≤ L := i.isLt.le
  unfold numerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (separant_pow_bound w hg _)).trans
        (Nat.le_add_right _ _))
  · apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - i.val) * (B - w 3) + (w 0 + i.val * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add (separant_pow_bound w hg _) (jet_bound w Δ hshift hB hg i.val)
      _ = w 0 + 2 * (i.val + (L - i.val)) * (B - w 3) + i.val * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hi]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hi)
private theorem chart_fits {L : ℕ} {g : Row 4} {p : Shape}
    (hg : InBox (K1_13.shape g) p) (hp : Chamber p) (ht : 0 < p.t) :
    (recoveryChart L g).Fits (chart L p) := by
  constructor
  · apply three_weights hg hp ht
    intro w Δ d₀ B _ _ _ hB
    exact (separant_pow_bound w hB (2 * L)).trans (by omega)
  · intro i
    exact three_weights hg hp ht (fun w Δ d₀ _ hs hw hwB hB =>
      numerator_bound w Δ d₀ hs hw hwB hB i)
private theorem ordinary_eq_hasse (S : (Polynomial Geom)) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
private theorem chart_recovers {L : ℕ} (hL : L ≤ K1.p) {g : Row 4} {S : (Polynomial Geom)}
    (hg : atJet g S = 0) (hr : RegularAt g S) : (recoveryChart L g).Recovers S := by
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (K1_13.jet S : Fin 4 → (Polynomial Geom))) _ _
  constructor
  · change evalGeneric S (toGeneric (denominator L g)) ≠ 0
    rw [evalGeneric_toGeneric, map_ne_zero_iff _ genericCoeffs_injective, hden]
    exact pow_ne_zero _ hr
  · intro i
    change evalGeneric S (toGeneric (numerator L g i)) =
      evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv i.val S)
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (K1_13.jet S : Fin 4 → (Polynomial Geom))
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - i.val)) *
        atJet (jetNumerator g i.val) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ *
          Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero (i.isLt.trans_le hL)), map_one]
      have hpow : 2 * (L - i.val) + 2 * i.val = 2 * L := by
        rw [← Nat.mul_add, Nat.sub_add_cancel i.isLt.le]
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - i.val)) * atJet (separant g) S ^ (2 * i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]
private abbrev constants : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
private abbrev center : GeoField := genericCoeffs Polynomial.X
private def valueForm (L : ℕ) (x a : K) : AffineForm L :=
  (-constants (embed a), fun i => (constants (embed x) - center) ^ i.val)
private theorem eval_at_center (S : (Polynomial Geom)) : (S.map constants).eval center = genericCoeffs S := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂RingHom constants center S = genericCoeffs S
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [constants]
  · simp [center]
private theorem taylor_value {L : ℕ} (S : (Polynomial Geom)) (hS : S.natDegree < L) (x : Geom) :
    (∑ i : Fin L, genericCoeffs (hasseDeriv i.val S) * (constants x - center) ^ i.val) =
      constants (S.eval x) := by
  let P := S.map constants
  have hdeg : (taylor center P).natDegree < L := by
    rw [natDegree_taylor]
    exact natDegree_map_le.trans_lt hS
  have hcoeff (i : ℕ) :
      (taylor center P).coeff i = genericCoeffs (hasseDeriv i S) := by
    rw [taylor_coeff]
    change (hasseDeriv i (S.map constants)).eval center = _
    rw [hasseDeriv_map, eval_at_center]
  have heval := (taylor center P).eval_eq_sum_range' hdeg (constants x - center)
  rw [← Fin.sum_univ_eq_sum_range] at heval
  simp only [hcoeff] at heval
  rw [taylor_eval_sub, show P.eval (constants x) = constants (S.eval x) from
    Polynomial.eval_map_apply constants x] at heval
  exact heval.symm
private theorem value_cut_eval {L : ℕ} (T : TaylorChart L) {S : (Polynomial K)}
    (hS : S.natDegree < L) (hT : T.Recovers (extend S)) (x a : K) :
    evalGeneric (extend S) (T.pullback (valueForm L x a)) = 0 ↔ S.eval x = a := by
  have hdeg : (extend S).natDegree < L := natDegree_map_le.trans_lt hS
  have hval := taylor_value (extend S) hdeg (embed x)
  rw [Polynomial.eval_map_apply] at hval
  have hsum :
      (∑ i : Fin L, (constants (embed x) - center) ^ i.val *
        (evalGeneric (extend S) T.denom * genericCoeffs (hasseDeriv i.val (extend S)))) =
        evalGeneric (extend S) T.denom * constants (embed (S.eval x)) := by
    rw [← hval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold TaylorChart.pullback valueForm
  simp only [map_add, map_sum, map_mul, evalGeneric, MvPolynomial.eval_C]
  change (-constants (embed a)) * evalGeneric (extend S) T.denom +
      (∑ i : Fin L, (constants (embed x) - center) ^ i.val *
        evalGeneric (extend S) (T.numerator i)) = 0 ↔ _
  simp only [hT.2, hsum]
  rw [show -constants (embed a) * evalGeneric (extend S) T.denom +
      evalGeneric (extend S) T.denom * constants (embed (S.eval x)) =
      evalGeneric (extend S) T.denom * (constants (embed (S.eval x)) - constants (embed a)) by ring,
    mul_eq_zero, or_iff_right hT.1, sub_eq_zero]
  exact (genericCoeffs_injective.comp Polynomial.C_injective).eq_iff.trans embed.injective.eq_iff
theorem exists_value_cut {L : ℕ} (hL : L ≤ K1.p) {g : Row 4} {p : Shape}
    (hg : InBox (K1_13.shape g) p) (hp : Chamber p) (ht : 0 < p.t) (x a : K) :
    ∃ D : GeoJets, GeoFits D (chart L p) ∧
      ∀ S : (Polynomial K), S.natDegree < L → atJet g (extend S) = 0 → RegularAt g (extend S) →
        (evalGeneric (extend S) D = 0 ↔ S.eval x = a) := by
  let T := recoveryChart L g
  exact ⟨T.pullback (valueForm L x a), T.pullback_fits (chart_fits hg hp ht) _,
    fun S hS hvan hreg => value_cut_eval T hS (chart_recovers hL hvan hreg) x a⟩
end
end P0_9_6_1_2
end
section
namespace P0_9_6_1_2
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (taylorLength)
open K1_13 (Shape InBox chart extend embed shape atJet)
open K1_13_6 (GeoJets CanonicalChart CurveSections evalGeneric markIdeal separant)
open K1_13_6_1 (CurveOnFactor anchorBox sectionDegree mem_markIdeal)
open K1_13_6_1_5 (coordinate_cut markPoint markPoint_injective)
open K1_13_7 (RegularAt)
open K1_13_7_1 (Chamber GeoFits derivative_in_box shape_chamber toGeneric_fits)
theorem count_points : K1_13_6_1_5.c2 :=
  K1_13_6_1_5_2.of_children K1_13_6_1_5_2_1.proof K1_13_6_1_5_2_2.proof
theorem count_marks {f C s p D} {Γ : Finset K}
    (hc : CurveOnFactor f C) (hp : InBox ⟨1, 3, 1⟩ p)
    (hD : GeoFits D p) (hproper : D ∉ C) (hinj : Set.InjOn s (Γ : Set K))
    {L : Finset K} (hL : L ⊆ Γ)
    (hmarks : ∀ γ ∈ L, C ≤ markIdeal (extend (s γ)) ∧ evalGeneric (extend (s γ)) D = 0) :
    6 * L.card ≤ sectionDegree C (p.scale 6) := by
  classical
  let point := fun γ => markPoint (extend (s γ))
  have hinjL : Set.InjOn point (L : Set K) := by
    intro γ hγ η hη he
    exact hinj (hL hγ) (hL hη)
      (Polynomial.map_injective embed embed.injective (markPoint_injective he))
  have hcount := count_points C p hc.prime hc.dim hp D hD hproper (L.image point) (by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact hmarks γ hγ)
  rwa [Finset.card_image_of_injOn hinjL] at hcount
theorem chart_has_simplex (L : ℕ) (p : Shape) :
    InBox ⟨1, 3, 1⟩ (chart L p) := by
  unfold chart
  simp only [InBox]
  exact ⟨(Nat.le_add_right _ _).trans (le_max_left _ _),
    Nat.le_add_left _ _, le_min (by omega) (by omega)⟩
end
end P0_9_6_1_2
end
section
namespace P0_9_6_2
noncomputable section
open Polynomial
open P0 (K)
open P0_9 (physicalDegree primaryBox taylorLength)
open P0_9_6 (membershipTest nextTest)
open K1_13 (Row Shape Geom shape extend chart liftedChart mixed32)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength CanonicalChart
  Invariant separant divisorIdeal partialFlow)
open K1_13_6_2 (JetPoint GeoJets5 actualPoint Box4 Box5 graphBox)
open scoped BigOperators
structure Branch (f Q : Row 4) (l : ℕ) where
  surface : Ideal GeoJets
  r : ℕ
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  chart : CanonicalChart f surface r
  invariant : Invariant ((separant^[r]) f) surface
  proper : toGeneric (membershipTest ((separant^[r]) f)) ∉ surface
  curve : Ideal GeoJets
  divisor : (divisorIdeal surface (membershipTest ((separant^[r]) f))).IsMinimalPrime curve
  regularCurve : toGeneric (separant ((separant^[r]) f)) ∉ curve
  terminal :
    cycleLength (divisorIdeal surface (membershipTest ((separant^[r]) f))) curve
      divisor.isPrime ≠ 1 ∨ toGeneric (nextTest ((separant^[r]) f)) ∉ curve
namespace Branch
variable {f Q : Row 4} {l : ℕ} (b : Branch f Q l)
end Branch
def budget5 (p : Shape) : ℕ :=
  let a := liftedChart (taylorLength + 1) p
  let b := liftedChart (taylorLength + 2) p
  mixed32 p primaryBox a b + (taylorLength + 1) * mixed32 p primaryBox (graphBox p) b +
    (taylorLength + 2) * mixed32 p primaryBox (graphBox p) a
end
end P0_9_6_2
end
section
namespace P0_9_6_2_3
noncomputable section
open P0_9 (primaryBox taylorLength)
open P0_9_6_2 (budget5)
open K1_13 (Shape liftedChart mixed32)
open K1_13_6 (GeoField)
open K1_13_6_2 (graphBox)
open K1_13_6_2_4 (Boxes Chamber Allowed Admissible allowed_coordinate
  DivisorBound divisor_bound mixedDegree diagonalExponents)
open K1_13_6_2_4_3 (volumeProduct sumCap diagonal)
open MvPolynomial
open scoped BigOperators
open K1_13_6_2_4 (chart_chamber)
open K1_13_6_2_4_3 (diagonal_coeff)
open K1_13_6_2_4_3 (alt alt_insert alt_empty capDiff five_differences signed4_le)
theorem proper_cut_comparison : K1_13_6_2_4.ProperCutComparison :=
  K1_13_6_2_4_1.of_children K1_13_6_2_4_1_1.proof K1_13_6_2_4_1_2.proof
theorem cycle_comparison : K1_13_6_2_4.CycleComparison :=
  K1_13_6_2_4_2.of_children K1_13_6_2_4_2_1.proof
    (K1_13_6_2_4_2_2.of_children K1_13_6_2_4_2_2_1.proof K1_13_6_2_4_2_2_2.proof)
theorem divisor_comparison : DivisorBound :=
  divisor_bound proper_cut_comparison cycle_comparison
end
end P0_9_6_2_3
end
section
namespace P0_9_6_2_3
noncomputable section
open K1_13 (Row)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength GenericField GeoField)
open K1_13_6_2 (GeoJets5)
open K1_13_6_2_4 (sectionIdeal cylinder oldEmbedding OfDim LengthAt)
open RingTheory.Sequence
open K1_13_6_3_6 (weaklyRegular_pair_iff geometry_flat)
open K1_13_6_2_4_4 (cylinder_regular cylinder_dimension relPrime_of_regular cylinder_minimal cylinder_length)
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem geometric_regular {f Q : Row 4} (hf : Irreducible f) (hQ : ¬ f ∣ Q) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {toGeneric f}) (toGeneric Q)) := by
  let I : Ideal (Row 4) := Ideal.span {f}
  let : I.IsPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf.prime
  have hphysical : IsWeaklyRegular (Row 4) [f, Q] := by
    rw [weaklyRegular_pair_iff]
    exact ⟨IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hf.ne_zero,
      IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
        (mt Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_span_singleton.not.mpr hQ))⟩
  let B := MvPolynomial (Fin 4) GenericField
  let T := (nonZeroDivisors (Polynomial K1_13.Geom)).map (MvPolynomial.C (σ := Fin 4))
  have h₁ := hphysical.of_isLocalization B T
  have := geometry_flat
  have h₂ := h₁.of_flat (S := GeoJets)
  simp only [List.map_cons, List.map_nil] at h₂
  change IsWeaklyRegular GeoJets
    [MvPolynomial.map (algebraMap GenericField GeoField)
      (MvPolynomial.map (algebraMap (Polynomial K1_13.Geom) GenericField) f),
     MvPolynomial.map (algebraMap GenericField GeoField)
      (MvPolynomial.map (algebraMap (Polynomial K1_13.Geom) GenericField) Q)] at h₂
  have h₃ : IsWeaklyRegular GeoJets [toGeneric f, toGeneric Q] := by
    simpa only [toGeneric, K1_13_6.genericCoeffs, MvPolynomial.map_map] using h₂
  exact ((weaklyRegular_pair_iff ..).mp h₃).2
theorem cylinder_comparison (f Q : Row 4) (hf : Irreducible f) (hQ : ¬ f ∣ Q) :
    let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
    let J := sectionIdeal A (oldEmbedding (toGeneric Q))
    IsLeftRegular (Ideal.Quotient.mk A (oldEmbedding (toGeneric Q))) ∧
    ∀ P : Ideal GeoJets, ∀ h : (intersectionIdeal f Q).IsMinimalPrime P,
      OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P),
          cycleLength (intersectionIdeal f Q) P h.isPrime ≤ LengthAt J (cylinder P) hc.isPrime := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have hA : sectionIdeal ⊥ (oldEmbedding (toGeneric f)) = cylinder F := by
    simp [sectionIdeal, cylinder, F, Ideal.map_span]
  have hJ : sectionIdeal (sectionIdeal ⊥ (oldEmbedding (toGeneric f))) (oldEmbedding (toGeneric Q)) =
      cylinder (intersectionIdeal f Q) := by
    rw [hA, intersectionIdeal, Ideal.span_insert]
    simp [sectionIdeal, cylinder, F, Ideal.map_sup, Ideal.map_span]
  have hreg := geometric_regular hf hQ
  have hF := K1_13_6_3_6.toGeneric_ne_zero hf.ne_zero
  dsimp only
  constructor
  · exact (congrArg (fun I : Ideal GeoJets5 =>
      IsLeftRegular (Ideal.Quotient.mk I (oldEmbedding (toGeneric Q)))) hA).mpr
      (cylinder_regular hreg)
  · intro P hP
    refine ⟨cylinder_dimension (K1_13_6_1_4.pair_dimension hF (relPrime_of_regular hF hreg) hP),
      ?_⟩
    apply (congrArg (fun I : Ideal GeoJets5 => ∃ hc : I.IsMinimalPrime (cylinder P),
      cycleLength (intersectionIdeal f Q) P hP.isPrime ≤ LengthAt I (cylinder P) hc.isPrime) hJ).mpr
    exact ⟨cylinder_minimal hP, (cylinder_length (intersectionIdeal f Q) P hP.isPrime).le⟩
end
end P0_9_6_2_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 (Row shape)
open K1_13_6 (toGeneric divisorIdeal intersectionIdeal cycleLength)
open K1_13_6_3 (CoeffIdeal JetIdeal dimension cycleWeight)
open P0_9 (primaryBox)
open P0_9_6 (membershipTest nextTest)
open MvPolynomial
open scoped BigOperators
structure CutCycle (f Q : Row 4) : Prop where
  local_bound : ∀ surface (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    dimension surface = 2 ∧ (1 : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime ∧
    cycleLength (intersectionIdeal f Q) surface hz.isPrime ≤ ((shape f).b * primaryBox.b : ℕ)
  weighted_degree :
    ∑ surface ∈ (intersectionIdeal f Q).minimalPrimesFinset,
      (cycleWeight (intersectionIdeal f Q) surface : ℚ) * affineDegree surface
      ≤ ((shape f).b * primaryBox.b : ℕ)
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6 MvPolynomial
private theorem pderiv_degree (P : Row 4) (i : Fin 4) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  simpa only [weightedTotalDegree_one, Pi.one_apply] using
    weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) i P
private theorem pderiv_zero_of_degree_zero {P : Row 4} (h : P.totalDegree = 0) (i : Fin 4) :
    pderiv i P = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C]
private theorem coefficientDerivative_degree (P : Row 4) :
    (coefficientDerivative P).totalDegree ≤ P.totalDegree := by
  unfold coefficientDerivative
  exact totalDegree_finsetSum_le fun m hm =>
    (totalDegree_monomial_le _ _).trans (le_totalDegree hm)
private theorem partialFlow_degree (P : Row 4) :
    (partialFlow P).totalDegree ≤ P.totalDegree := by
  unfold partialFlow
  apply (totalDegree_add _ _).trans
  refine max_le (coefficientDerivative_degree P) (totalDegree_finsetSum_le ?_)
  intro i _
  by_cases h : P.totalDegree = 0
  · simp [pderiv_zero_of_degree_zero h]
  · refine (totalDegree_mul _ _).trans ?_
    have hc : (MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) *
        MvPolynomial.X i.succ : Row 4).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
    have hd := pderiv_degree P i.castSucc
    omega
private theorem flowNumerator_degree {g P : Row 4} {d : ℕ} (hd : g.totalDegree ≤ d) :
    (flowNumerator g P).totalDegree ≤ (d - 1) + P.totalDegree := by
  unfold flowNumerator
  apply (totalDegree_sub _ _).trans
  refine max_le ?_ ?_
  · apply (totalDegree_mul _ _).trans
    exact Nat.add_le_add (by exact (pderiv_degree g 3).trans (Nat.sub_le_sub_right hd _))
      (partialFlow_degree P)
  · by_cases h : P.totalDegree = 0
    · simp [separant, pderiv_zero_of_degree_zero h]
    · apply (totalDegree_mul _ _).trans
      have hg := (partialFlow_degree g).trans hd
      have hP : (separant P).totalDegree ≤ P.totalDegree - 1 := pderiv_degree P 3
      omega
private theorem clearedStep_degree {g P : Row 4} (a : ℕ) {d : ℕ} (hd : g.totalDegree ≤ d) :
    (clearedStep g a P).totalDegree ≤ P.totalDegree + 2 * (d - 1) := by
  unfold clearedStep
  apply (totalDegree_sub _ _).trans
  have hs : (separant g).totalDegree ≤ d - 1 :=
    (pderiv_degree g 3).trans (Nat.sub_le_sub_right hd _)
  refine max_le ?_ ?_
  · apply (totalDegree_mul _ _).trans
    have hp : (flowNumerator g P).totalDegree ≤ _ := flowNumerator_degree hd
    omega
  · apply (totalDegree_mul _ _).trans
    have hc : ((a : Row 4) * flowNumerator g (separant g)).totalDegree ≤
        (flowNumerator g (separant g)).totalDegree := by
      rw [← map_natCast (MvPolynomial.C : Polynomial Geom →+* Row 4) a]
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])
    have hflow : (flowNumerator g (separant g)).totalDegree ≤ _ := flowNumerator_degree hd
    omega
theorem jetNumerator_degree {g : Row 4} {d : ℕ} (hd : g.totalDegree ≤ d) (n : ℕ) :
    (jetNumerator g n).totalDegree ≤ 1 + 2 * n * (d - 1) := by
  induction n with
  | zero => simp [jetNumerator]
  | succ n ih =>
    rw [jetNumerator]
    apply (clearedStep_degree (2 * n) hd).trans
    rw [Nat.mul_succ, Nat.add_mul]
    omega
theorem iterate_separant_degree (f : Row 4) (r : ℕ) :
    ((separant^[r]) f).totalDegree ≤ f.totalDegree := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ((pderiv_degree _ 3).trans (Nat.sub_le _ _)).trans ih
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal)
open K1_13_6_3_1
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem flat_sepToGeo : Module.Flat SepJets GeoJets := by
  have h : Algebra.IsPushout SepField SepJets GeoField GeoJets := inferInstance
  exact Module.Flat.isBaseChange SepField SepJets GeoField GeoJets h.out
theorem map_eq_maximal_of_length_one (J P : JetIdeal) [P.IsPrime]
    (h : cycleLength J P ‹P.IsPrime› = 1) :
    J.map (algebraMap GeoJets (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  unfold cycleLength at h
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  exact h
theorem step_in_sep (g : Row 4) (D : Derivation ℤ SepJets SepJets)
    (hD : ∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U))
    (n : ℕ) :
    rowToSep (jetNumerator g (n+1)) =
      rowToSep (separant g) * D (rowToSep (jetNumerator g n)) -
        (↑(2*n) : SepJets) * D (rowToSep (separant g)) * rowToSep (jetNumerator g n) := by
  simp only [jetNumerator, clearedStep, map_sub, map_mul, map_natCast, ← hD]
theorem sep_sq_dvd_jet (g : Row 4) (D : Derivation ℤ SepJets SepJets)
    (hD : ∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U))
    (n : ℕ) (hn : 1 ≤ n) :
    rowToSep (separant g)^2 ∣ rowToSep (jetNumerator g n) := by
  let s := rowToSep (separant g)
  change s^2 ∣ _
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hz : separant (MvPolynomial.X (0 : Fin 4) : Row 4) = 0 := by
        simp [separant, MvPolynomial.pderiv_X]
      use rowToSep (partialFlow (MvPolynomial.X 0))
      rw [step_in_sep g D hD 0, jetNumerator, hD, flowNumerator, hz]
      simp [s, pow_two, mul_assoc]
    | succ n =>
      obtain ⟨w, hw⟩ := ih (Nat.succ_pos _)
      rw [step_in_sep g D hD (n+1)]
      change s^2 ∣ s * D (rowToSep (jetNumerator g (n+1))) -
        (↑(2*(n+1)) : SepJets) * D s * rowToSep (jetNumerator g (n+1))
      rw [hw]
      use s * D w + 2 * D s * w - (↑(2*(n+1)) : SepJets) * D s * w
      simp only [pow_two, D.leibniz, smul_eq_mul]
      ring
theorem nonvanishing_of_simple_cut {R : Type*} [CommRing R]
    (T P : Ideal R) [T.IsPrime] (hle : T ≤ P) {s e : R}
    (hs : s ∉ T) (he : s^2 ∣ e)
    (hsat : ∀ x ∈ P, ∃ t ∉ P, t * x ∈ T ⊔ Ideal.span {e}) : s ∉ P := by
  intro hsp
  obtain ⟨v, hv, hvs⟩ := hsat s hsp
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvs
  obtain ⟨w, hw⟩ := he
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hrel : s * (v - s * (w*c)) = a := by
    rw [hc, hw] at hab
    linear_combination -hab
  have hmem : v - s * (w*c) ∈ T :=
    (‹T.IsPrime›.mem_or_mem (hrel.symm ▸ ha)).resolve_left hs
  apply hv
  have hm := P.add_mem (hle hmem) (P.mul_mem_right (w*c) hsp)
  simpa using hm
theorem stable_of_simple_cut {R : Type*} [CommRing R]
    (T P : Ideal R) [P.IsPrime] (hle : T ≤ P)
    (D : Derivation ℤ R R) (hT : ∀ u ∈ T, D u ∈ T)
    {e : R} (he : e ∈ P) (hDe : D e ∈ P)
    (hsat : ∀ x ∈ P, ∃ t ∉ P, t * x ∈ T ⊔ Ideal.span {e}) :
    ∀ u ∈ P, D u ∈ P := by
  intro u hu
  obtain ⟨t, ht, htu⟩ := hsat u hu
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hDb : D b ∈ P := by
    rw [hc, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ he) (P.mul_mem_left _ hDe)
  have hDtu : D (t*u) ∈ P := by
    rw [← hab, map_add]
    exact P.add_mem (hle (hT a ha)) hDb
  rw [D.leibniz, smul_eq_mul, smul_eq_mul] at hDtu
  exact (‹P.IsPrime›.mem_or_mem
    ((P.add_mem_iff_left (P.mul_mem_right (D t) hu)).mp hDtu)).resolve_left ht
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6
open K1_13_6_3 (JetIdeal dimension cycleWeight)
open K1_13_6_3_6 MvPolynomial RingTheory.Sequence
open scoped BigOperators TensorProduct Pointwise
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem coefficient_budget (J : JetIdeal) (hd : dimension J ≤ 2) : by
    classical
    exact (∀ P (hp : J.IsMinimalPrime P), cycleLength J P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ J.minimalPrimesFinset,
        (cycleWeight J P : ℚ) * (affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial J).coeff 2 := by
  classical
  let T := J.minimalPrimesFinset
  suffices aux : ∀ I : JetIdeal, J ≤ I →
      (∀ P (hp : J.IsMinimalPrime P), cycleLength I P hp.isPrime ≠ ⊤) ∧
      ∑ P ∈ T, (cycleWeight I P : ℚ) * (affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial I).coeff 2 from aux J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α := JetIdeal)) with
  | h I ih =>
    intro hJI
    by_cases hI : I = ⊤
    · subst I
      have hz (P : JetIdeal) (hp : P.IsPrime) : cycleLength ⊤ P hp = 0 :=
        length_eq_zero_of_not_le hp (by simpa using hp.ne_top)
      exact ⟨fun P hp => by simp [hz P hp.isPrime], by
        refine le_of_eq ?_
        simp only [cycleWeight, affineHilbertPolynomial_top, Polynomial.coeff_zero]
        apply Finset.sum_eq_zero
        intro P hP
        have hp := (Ideal.mem_minimalPrimesFinset.mp hP).isPrime
        simp [dite_eq_left hp, hz P hp]⟩
    obtain ⟨g, hg, hprime⟩ := exists_prime_colon I hI
    let A : JetIdeal := I.colon {g}
    let B : JetIdeal := I ⊔ Ideal.span {g}
    have hIA : I ≤ A := Ideal.le_colon
    have hIB : I < B := lt_of_le_not_ge le_sup_left
      (fun h => hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    obtain ⟨hfin, hbudget⟩ := ih B hIB (hJI.trans hIB.le)
    have hstep (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength I P hp.isPrime =
          cycleLength A P hp.isPrime + cycleLength B P hp.isPrime :=
      length_step I P hp.isPrime g
    have hterm (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength A P hp.isPrime = if P = A then 1 else 0 := by
      split_ifs with h
      · subst P
        exact length_self A hp.isPrime
      · exact length_eq_zero_of_not_le hp.isPrime
          (fun hAP => h (le_antisymm (hp.2 ⟨hprime, hJI.trans hIA⟩ hAP) hAP))
    have hfinite (P : JetIdeal) (hp : J.IsMinimalPrime P) :
        cycleLength A P hp.isPrime ≠ ⊤ := by rw [hterm P hp]; split_ifs <;> simp
    have hweight (P : JetIdeal) (hP : P ∈ T) :
        (cycleWeight I P : ℚ) = (cycleWeight B P : ℚ) + (if P = A then 1 else 0) := by
      have hp := Ideal.mem_minimalPrimesFinset.mp hP
      simp only [cycleWeight, dite_eq_left hp.isPrime]
      rw [hstep P hp, ENat.toNat_add (hfinite P hp) (hfin P hp), hterm P hp, Nat.cast_add]
      split_ifs <;> simp [add_comm]
    have hdim := (natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    refine ⟨fun P hp => by
      rw [hstep P hp]
      exact WithTop.add_ne_top.mpr ⟨hfinite P hp, hfin P hp⟩, ?_⟩
    calc
      _ = (∑ P ∈ T, (cycleWeight B P : ℚ) * (affineHilbertPolynomial P).coeff 2) +
          (if A ∈ T then (affineHilbertPolynomial A).coeff 2 else 0) := by
        rw [← Finset.sum_ite_eq' T A (fun P => (affineHilbertPolynomial P).coeff 2),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hweight P hP, add_mul, ite_mul, one_mul, zero_mul]
      _ ≤ (affineHilbertPolynomial B).coeff 2 + (affineHilbertPolynomial A).coeff 2 := by
        apply add_le_add hbudget
        split_ifs
        · exact le_rfl
        · exact coeff_two_nonneg A ((natDegree_affineHilbertPolynomial_le_of_le hIA).trans hdim)
      _ ≤ _ := hilbert_coeff_step I g hdim
end
end P0_9_6_3
end
section
set_option autoImplicit false
namespace P0_9_6_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
private theorem recovery_of_generators (rec : K1_13_6_3_3.c2) (g : Row 4) (h : FreshCoeffRing) :
    ∃ (u : GeoJets) (e : ℕ), ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime →
      toGeneric g ∈ freshImage A → toGeneric (separant g) ∉ freshImage A →
      h * freshJetMap (toGeneric (separant g)) ^ e - freshJetMap u ∈ extendIdeal A := by
  let s := toGeneric (separant g)
  induction h using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a, 0, fun A _ _ _ _ => ?_⟩
    simp [freshJetMap]
  | add h h' ih ih' =>
    obtain ⟨u, e, hu⟩ := ih
    obtain ⟨v, d, hv⟩ := ih'
    refine ⟨u * s ^ d + v * s ^ e, e + d, fun A hp he hg hs => ?_⟩
    let q := Ideal.Quotient.mk (extendIdeal A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h * freshJetMap s ^ e - freshJetMap u) = 0 at hu'
    change q (h' * freshJetMap s ^ d - freshJetMap v) = 0 at hv'
    change q ((h + h') * freshJetMap s ^ (e + d) - freshJetMap
      (u * s ^ d + v * s ^ e)) = 0
    simp only [map_add, map_mul, map_sub, map_pow, pow_add] at hu' hv' ⊢
    linear_combination q (freshJetMap s) ^ d * hu' + q (freshJetMap s) ^ e * hv'
  | mul_X h i ih =>
    obtain ⟨u, e, hu⟩ := ih
    obtain ⟨v, d, hv⟩ := rec g i
    refine ⟨u * v, e + d, fun A hp he hg hs => ?_⟩
    let q := Ideal.Quotient.mk (extendIdeal A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h * freshJetMap s ^ e - freshJetMap u) = 0 at hu'
    change q (MvPolynomial.X i * freshJetMap s ^ d - freshJetMap v) = 0 at hv'
    change q ((h * MvPolynomial.X i) * freshJetMap s ^ (e + d) - freshJetMap
      (u * v)) = 0
    simp only [map_mul, map_sub, map_pow, pow_add, sub_eq_zero] at hu' hv' ⊢
    calc
      _ = (q h * q (freshJetMap s) ^ e) *
          (q (MvPolynomial.X i) * q (freshJetMap s) ^ d) := by ac_rfl
      _ = _ := by rw [hu', hv']
theorem fresh_prime {A : CoeffIdeal} (hA : (extendIdeal A).IsPrime) :
    (freshImage A).IsPrime := by
  let _ := hA
  exact inferInstanceAs ((extendIdeal A).comap freshJetMap).IsPrime
theorem fresh_birational (rec : K1_13_6_3_3.c2) {A : CoeffIdeal} (hA : A.IsPrime)
    (hext : (extendIdeal A).IsPrime) {g : Row 4}
    (hg : toGeneric g ∈ freshImage A) (hs : toGeneric (separant g) ∉ freshImage A) :
    FreshBirational A := by
  intro h
  obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
  refine ⟨u, toGeneric (separant g) ^ e, ?_, ?_⟩
  · intro hp
    exact hs ((fresh_prime hext).mem_of_pow_mem e hp)
  · rw [map_pow]
    exact hrel A hA hext hg hs
private def freshJetAlgHom : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  MvPolynomial.aeval (fun i : Fin 4 => jetLinear genericArgument i.val)
private theorem freshJetAlgHom_toRingHom : freshJetAlgHom.toRingHom = freshJetMap := by
  ext a <;> simp [freshJetAlgHom, freshJetMap]
theorem dim_fresh_of_recovery (rec : K1_13_6_3_3.c2) {A : CoeffIdeal}
    (hA : A.IsPrime) (hext : (extendIdeal A).IsPrime) {g : Row 4}
    (hg : toGeneric g ∈ freshImage A) (hs : toGeneric (separant g) ∉ freshImage A) :
    dimension (freshImage A) = dimension (extendIdeal A) := by
  let I := extendIdeal A
  let J := freshImage A
  let v := toGeneric (separant g)
  have hJ : J = I.comap freshJetAlgHom := by
    change I.comap freshJetMap = I.comap freshJetAlgHom.toRingHom
    rw [freshJetAlgHom_toRingHom]
  let F := Ideal.quotientMapₐ I freshJetAlgHom hJ.le
  have hinj : Function.Injective F := Ideal.quotientMap_injective' (H := hJ.le) hJ.ge
  apply le_antisymm (natDegree_affineHilbertPolynomial_le_of_injective F hinj)
  let vI := freshJetMap v
  have hFv : F (Ideal.Quotient.mk J v) = Ideal.Quotient.mk I vI := by
    rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk I (freshJetAlgHom.toRingHom v) = _
    rw [freshJetAlgHom_toRingHom]
  let L := Localization.Away (Ideal.Quotient.mk I vI)
  let _ : IsLocalization.Away (F (Ideal.Quotient.mk J v)) L := by
    rw [hFv]
    infer_instance
  let G := IsLocalization.Away.mapₐ (R := GeoField)
    (Localization.Away (Ideal.Quotient.mk J v)) L F (Ideal.Quotient.mk J v)
  have hsurj : Function.Surjective G := by
    apply (IsLocalization.Away.map_surjective_iff _ _ F.toRingHom (Ideal.Quotient.mk J v)).mpr
    intro x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
    have hEq := sub_eq_zero.mp (show
      Ideal.Quotient.mk I (h * vI ^ e) - Ideal.Quotient.mk I (freshJetMap u) = 0 by
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrel A hA hext hg hs))
    refine ⟨Ideal.Quotient.mk J u, e, ?_⟩
    change F (Ideal.Quotient.mk J u) = F (Ideal.Quotient.mk J v) ^ e * Ideal.Quotient.mk I h
    rw [hFv, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk I (freshJetAlgHom.toRingHom u) = _
    rw [freshJetAlgHom_toRingHom, ← hEq, map_mul, map_pow, mul_comm]
  let _ : I.IsPrime := hext
  have hreg : IsLeftRegular (Ideal.Quotient.mk I vI) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg G hsurj
theorem dim_lt_of_prime_lt {P J : JetIdeal} (hP : P.IsPrime) (hJ : J.IsPrime)
    (hlt : P < J) : dimension J < dimension P := by
  classical
  obtain ⟨s, hJmem, hPmem⟩ := SetLike.exists_of_lt hlt
  have hcut : P ⊔ Ideal.span {s} ≤ J :=
    sup_le hlt.le ((Ideal.span_singleton_le_iff_mem J).mpr hJmem)
  let _ := hJ
  obtain ⟨T, hT, hle⟩ := Ideal.exists_minimalPrimes_le hcut
  let _ := hP
  have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hPmem hT
  have hlt' : dimension T < dimension P := by
    change dimension T + 1 = dimension P at hd
    omega
  exact lt_of_le_of_lt (natDegree_affineHilbertPolynomial_le_of_le hle) hlt'
private theorem injective_on_regular (base : K1_13_6_3_3.c1) (rec : K1_13_6_3_3.c2) (f : Row 4) :
    Set.InjOn freshImage {A | A.IsPrime ∧ FreshRegular f A} := by
  intro A hA B hB himage
  obtain ⟨hAp, hAr⟩ := hA
  obtain ⟨hBp, _⟩ := hB
  obtain ⟨hAe, _, hAc⟩ := base A hAp
  obtain ⟨hBe, _, hBc⟩ := base B hBp
  obtain ⟨r, hgA, hsA⟩ := hAr
  let g := (separant^[r]) f
  have hgB : toGeneric g ∈ freshImage B := himage ▸ hgA
  have hsB : toGeneric (separant g) ∉ freshImage B := himage ▸ hsA
  have hEq : extendIdeal A = extendIdeal B := by
    ext h
    obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
    let s := freshJetMap (toGeneric (separant g))
    have transfer (D : CoeffIdeal) (hDp : D.IsPrime) (hDe : (extendIdeal D).IsPrime)
        (hgD : toGeneric g ∈ freshImage D) (hsD : toGeneric (separant g) ∉ freshImage D) :
        h ∈ extendIdeal D ↔ u ∈ freshImage D := by
      have hdiff : h * s ^ e - freshJetMap u ∈ extendIdeal D := hrel D hDp hDe hgD hsD
      have hn : s ^ e ∉ extendIdeal D := fun hp => hsD (hDe.mem_of_pow_mem e hp)
      change _ ↔ freshJetMap u ∈ extendIdeal D
      constructor
      · intro hh
        have hm := Ideal.mul_mem_right (s ^ e) (extendIdeal D) hh
        exact ((extendIdeal D).sub_mem_iff_right hm).1 hdiff
      · intro hu
        have hm := ((extendIdeal D).sub_mem_iff_left hu).1 hdiff
        exact (hDe.mem_or_mem hm).resolve_right hn
    rw [transfer A hAp hAe hgA hsA, transfer B hBp hBe hgB hsB, himage]
  rw [← hAc, ← hBc, hEq]
theorem freshImage_injective (f : Row 4) :
    Set.InjOn freshImage {A | A.IsPrime ∧ FreshRegular f A} :=
  injective_on_regular K1_13_6_3_3_1.proof K1_13_6_3_3_2.proof f
end
end P0_9_6_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace P0_9_6_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open K1_13_6_3
open P0_9 (primaryBox)
open scoped BigOperators
theorem curve_degree : K1_13_6_3.c4 :=
  K1_13_6_3_4.of_children K1_13_6_3_4_1.proof K1_13_6_3_4_2.proof K1_13_6_3_4_3.proof
theorem markPoint_inj {Γ : Finset K} {s : K → (Polynomial K)}
    (hdistinct : Set.InjOn s (Γ : Set K))
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength) :
    Set.InjOn (markPoint s) (Γ : Set K) := by
  intro α hα β hβ hEq
  apply hdistinct hα hβ
  apply Polynomial.ext
  intro n
  by_cases hn : n < taylorLength
  · have hcoeff := congrFun hEq ⟨n, hn⟩
    exact embed.injective (by simpa only [markPoint, coeffPoint, Polynomial.coeff_map] using hcoeff)
  · have hlt := Nat.le_of_not_lt hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hdegree α hα).trans_le hlt),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hdegree β hβ).trans_le hlt)]
theorem canonical_unique {f : Row 4} {surface : JetIdeal} {r t : ℕ}
    (hr : CanonicalChart f surface r) (ht : CanonicalChart f surface t) : r = t := by
  rcases lt_trichotomy r t with h | h | h
  · have hm := ht.2.1 (r + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (hr.2.2 hm)
  · exact h
  · have hm := hr.2.1 (t + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (ht.2.2 hm)
theorem cycleWeight_ge {f Q : Row 4} (hc : CutCycle f Q) {surface : JetIdeal}
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface) {l : ℕ}
    (hl : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime) :
    l ≤ cycleWeight (intersectionIdeal f Q) surface := by
  classical
  have hne : cycleLength (intersectionIdeal f Q) surface hz.isPrime ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hc.local_bound surface hz).2.2
  simpa only [cycleWeight, dite_eq_left hz.isPrime, ENat.toNat_natCast] using ENat.toNat_le_toNat hl hne
theorem surface_sum {f Q : Row 4} (hc : CutCycle f Q) (T : Finset JetIdeal)
    (hT : ∀ P ∈ T, (intersectionIdeal f Q).IsMinimalPrime P) :
    ∑ P ∈ T, affineDegree P ≤ ((shape f).b * primaryBox.b : ℕ) := by
  classical
  let S := (intersectionIdeal f Q).minimalPrimesFinset
  have hsub : T ⊆ S := fun P hP => Ideal.mem_minimalPrimesFinset.mpr (hT P hP)
  calc
    _ ≤ ∑ P ∈ S, affineDegree P :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)
    _ ≤ ∑ P ∈ S, (cycleWeight (intersectionIdeal f Q) P : ℚ) * affineDegree P := by
      apply Finset.sum_le_sum
      intro P hP
      have hz := Ideal.mem_minimalPrimesFinset.mp hP
      have h1 := cycleWeight_ge hc hz (hc.local_bound P hz).2.1
      exact le_mul_of_one_le_left (affineDegree_nonneg P) (by exact_mod_cast h1)
    _ ≤ _ := hc.weighted_degree
end
end P0_9_6_3
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace P0_9_6_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2 Polynomial
theorem iterate_zero_of_le {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (y : F) {L n : ℕ}
    (hcut : ((D : F → F)^[L]) y = 0) (hn : L ≤ n) :
    ((D : F → F)^[n]) y = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm L j, Function.iterate_add_apply, hcut]
  exact Function.iterate_fixed (f := (D : F → F)) D.map_zero j
theorem differentialTaylor_degree {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (x y : F) {L : ℕ} (hL : 0 < L) (hbound : L ≤ taylorLength)
    (hcut : ((D : F → F)^[L]) y = 0) : (differentialTaylor D x y).natDegree < L := by
  have htrim : differentialTaylor D x y =
      fromTaylor (M := L) x (fun i => dividedIterate D y i.val) := by
    let term (i : ℕ) := C (dividedIterate D y i) * (Polynomial.X - C x) ^ i
    change (∑ i : Fin taylorLength, term i.val) = ∑ i : Fin L, term i.val
    rw [Fin.sum_univ_eq_sum_range term, Fin.sum_univ_eq_sum_range term]
    symm
    apply Finset.sum_subset (Finset.range_mono hbound)
    intro i _ hi
    have htail : L ≤ i := Nat.le_of_not_lt (fun h => hi (Finset.mem_range.mpr h))
    simp only [term, dividedIterate, iterate_zero_of_le D y hcut htail, zero_div, map_zero,
      zero_mul]
  rw [htrim]
  exact fromTaylor_degree _ _ hL
theorem rowAt_eval (P : JetIdeal) (H : Row 4) :
    MvPolynomial.eval₂ (Polynomial.aeval (abscissa (rowAt P))).toRingHom
      (jetCoordinate (rowAt P)) H = rowAt P H := by
  change MvPolynomial.eval₂Hom _ _ H = rowAt P H
  have hc : (Polynomial.aeval (abscissa (rowAt P))).toRingHom =
      (rowAt P).comp MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, RingHom.comp_apply]
      rfl
    · simp [abscissa]
  rw [hc]
  have h : MvPolynomial.eval₂Hom ((rowAt P).comp MvPolynomial.C)
      (jetCoordinate (rowAt P)) = rowAt P := by
    apply MvPolynomial.ringHom_ext <;> simp [jetCoordinate]
  rw [h]
theorem initial_dividedIterate {F : Type} [Field F] [Algebra Geom F]
    (e : Row 4 →+* F) (D : Derivation Geom F F)
    (shift : ∀ i : Fin 3, D (jetCoordinate e i.castSucc) =
      ((i.val + 1 : ℕ) : F) * jetCoordinate e i.succ) (i : Fin 4) :
    dividedIterate D (jetCoordinate e 0) i.val = jetCoordinate e i := by
  have raw (j : Fin 4) : ((D : F → F)^[j.val]) (jetCoordinate e 0) =
      (j.val.factorial : F) * jetCoordinate e j := by
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
      rw [Fin.val_succ, Function.iterate_succ_apply', ← Fin.val_castSucc j, ih]
      simp only [D.leibniz, D.map_natCast, smul_eq_mul, mul_zero, add_zero, shift,
        Fin.val_castSucc, Nat.factorial_succ, Nat.cast_mul]
      ring
  have hfact := factorial_ne_zero (algebraMap Geom F)
    (i.isLt.trans (by decide : 4 < K1.p))
  rw [dividedIterate, raw i, mul_div_cancel_left₀ _ hfact]
theorem chartTaylor_toComponent (P : JetIdeal) [P.IsPrime] (g : Row 4) :
    (chartTaylor (rowAt P) g).map (toComponent P) = chartTaylor (componentRow P) g := by
  unfold chartTaylor abscissa
  rw [map_fromTaylor]
  simp only [map_div₀, map_pow, map_natCast, toComponent_rowAt]
end
end P0_9_6_3_1
end

end Merged6967_PortLow6

section Merged6967_Wide50EulerPrimaryRank
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Wide50EulerPrimary
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 TaperBudget
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
open TaperBudget (fees saved_by_fees fees_le_baseline sumRange_fin sumRange_eq)
open K1_13_2_3 (baseline_budget_on sum_add_pointwise_eq)
open TaperBudget (sum_checked)
open K1_13_2_3_7 (sum_embed_le)


def inWindow (i : BlockIndex) : Prop :=
  3514 ≤ i.1.val ∧ i.1.val < 3594 ∧ 77 ≤ i.2.val ∧ i.2.val < 121

private instance (i : BlockIndex) : Decidable (inWindow i) := by
  unfold inWindow
  infer_instance

private def windowPower (t j : ℕ) : Powers :=
  ⟨819 - 2*t - 4*(12+j), 275 - 2*t - 9*j/2, 0⟩

private def alternate (i : BlockIndex) : ℕ :=
  TaperNormalize.bound (cap i.1.val) i
    (windowPower (i.1.val - 3514) (i.2.val - 77)).expand

def gain (i : BlockIndex) : ℕ :=
  if inWindow i then
    min (baseline i) (TaperNormalize.bound (cap i.1.val) i (power i)) - alternate i
  else 0

private def window : Fin 80 × Fin 44 ↪ BlockIndex where
  toFun x := (⟨3514 + x.1.val, by omega⟩, ⟨77 + x.2.val, by omega⟩)
  inj' := by
    intro x y h
    apply Prod.ext <;> apply Fin.ext
    · have h₁ := congrArg (fun i : BlockIndex => i.1.val) h
      change 3514 + x.1.val = 3514 + y.1.val at h₁
      omega
    · have h₂ := congrArg (fun i : BlockIndex => i.2.val) h
      change 77 + x.2.val = 77 + y.2.val at h₂
      omega

private def numericCell (t j : ℕ) : ℕ :=
  if ht : t < 80 then if hj : j < 44 then
    let i := window (⟨t,ht⟩,⟨j,hj⟩)
    let k := cap i.1.val
    let v := valuePower k i.1.val i.2.val
    let p := windowPower t j
    min (twoFactorBoundI 1650 i 0 0) (twoFactorBoundI k i v 0) -
      twoFactorBoundI k i p.value p.top
  else 0 else 0

private theorem cell_eq (t : Fin 80) (j : Fin 44) :
    numericCell t.val j.val = gain (window (t,j)) := by
  have hw : inWindow (window (t,j)) := by
    unfold inWindow
    change 3514 ≤ 3514 + t.val ∧ 3514 + t.val < 3594 ∧
      77 ≤ 77 + j.val ∧ 77 + j.val < 121
    omega
  have ht : (window (t,j)).1.val - 3514 = t.val := by
    change 3514 + t.val - 3514 = t.val
    omega
  have hj : (window (t,j)).2.val - 77 = j.val := by
    change 77 + j.val - 77 = j.val
    omega
  have hzero : (Powers.expand ⟨0,0,0⟩) = (fun _ : Fin 11 => 0) := by
    funext j
    fin_cases j <;> rfl
  simp only [numericCell, t.isLt, j.isLt, dite_true, gain, hw, ite_true, alternate,
    ht, hj, twoFactorBoundI_eq, twoFactorBound_eq, power, windowPower, hzero, old_bound_eq, baseline]

private def row (t : ℕ) : ℕ := sumRange (numericCell t) 44

private def rowTotals : Fin 80 → ℕ :=
  ![21821534, 21505240, 21188447, 20871239, 20553702, 20235923, 19917990, 19599992,
    19282022, 18964176, 18646550, 18329243, 18012358, 17695996, 17380258, 17065248,
    16751070, 16437828, 16125626, 15814571, 15504770, 15196328, 14889354, 14583957,
    14280245, 13978328, 13678317, 13380324, 13084459, 12790835, 12499567, 12210767,
    11924550, 11641032, 11360329, 11082557, 10807833, 10536277, 10268006, 10003139,
    9741798, 9484103, 9229933, 8979410, 8732478, 8489230, 8249607, 8013640,
    7781387, 7552787, 7327955, 7106769, 6889341, 6675606, 6465643, 6259386,
    6056853, 5858091, 5663030, 5471770, 5284184, 5100368, 4920250, 4743895,
    4571228, 4402257, 4237015, 4075425, 3917572, 3763322, 3612758, 3465798,
    3322495, 3182765, 3046604, 2914034, 2784968, 2659478, 2537423, 2418871]

set_option maxHeartbeats 0 in
private theorem row_checked (t : Fin 80) : row t.val = rowTotals t := by
  fin_cases t <;> decide +kernel

theorem window_gain : 854889514 ≤ ∑ i : BlockIndex, gain i := by
  have h : (∑ x : Fin 80 × Fin 44, gain (window x)) = 854889514 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    calc
      _ = ∑ t : Fin 80, row t.val := by
        apply Finset.sum_congr rfl
        intro t _
        rw [row, sumRange_fin]
        apply Finset.sum_congr rfl
        intro j _
        exact (cell_eq t j).symm
      _ = ∑ t : Fin 80, rowTotals t := Finset.sum_congr rfl fun t _ => row_checked t
      _ = 854889514 := by decide
  exact h ▸ sum_embed_le window gain

def charged (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) : ℕ :=
  if inWindow i then min (fees p₁ p₂ p₃ i) (alternate i)
  else fees p₁ p₂ p₃ i

theorem charged_add_gain (p₁ p₂ p₃ : BlockIndex → Powers) (i : BlockIndex) :
    charged p₁ p₂ p₃ i + gain i = fees p₁ p₂ p₃ i := by
  by_cases hi : inWindow i
  · have hg : ¬ i.1.val < 3514 := by unfold inWindow at hi; omega
    simp only [charged, gain, ite_eq_left hi, fees, ite_eq_right hg]
    omega
  · simp [charged, gain, hi]


end Wide50EulerPrimary

end Merged6967_Wide50EulerPrimaryRank
