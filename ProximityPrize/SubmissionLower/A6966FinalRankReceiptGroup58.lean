import ProximityPrize.SubmissionLower.A6966FinalRankBlocks

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
  match i.val with
  | 0 => ⟨1,0,0,0⟩ | 1 => ⟨1,0,0,0⟩ | 2 => ⟨1,0,0,0⟩ | 3 => ⟨1,1,0,0⟩ | 4 => ⟨1,1,0,0⟩
  | 5 => ⟨1,0,1,0⟩ | 6 => ⟨2,0,1,0⟩ | 7 => ⟨1,3,0,0⟩ | _ => ⟨2,3,0,0⟩
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
