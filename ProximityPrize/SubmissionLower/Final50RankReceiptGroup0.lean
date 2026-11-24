import ProximityPrize.SubmissionLower.Final50RankBlocks

-- merged module Final50RankReceiptBase
section Merged_Final50RankReceiptBase
set_option Elab.async false
namespace Final50RankReceipt
open K1_13_1_1 (bandCount)
open AnchorPivot82180 (monoData)
abbrev Row := RankRows82190.Row
def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 59 ∧ x.top ≤ 14 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)
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
def fee (s : ℕ) (r : Row) : ℕ := 105 + r.index - (s + r.ord)
def triangle (n : ℕ) : ℕ := n * (n+1) / 2
def stageRange : ℕ → ℕ × ℕ
  | 36 => (141, 142)
  | 37 => (140, 141)
  | 38 => (139, 140)
  | 39 => (138, 139)
  | 40 => (137, 138)
  | 41 => (136, 137)
  | 42 => (135, 136)
  | 43 => (134, 135)
  | 44 => (133, 134)
  | 45 => (132, 133)
  | 46 => (131, 132)
  | 47 => (130, 131)
  | 48 => (129, 130)
  | 49 => (128, 129)
  | 50 => (127, 128)
  | 51 => (126, 127)
  | 52 => (125, 126)
  | 53 => (124, 125)
  | 54 => (123, 124)
  | 55 => (122, 123)
  | 56 => (121, 122)
  | 57 => (120, 121)
  | 58 => (119, 120)
  | 59 => (60, 119)
  | _ => (142, 142)
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

private def cert0_0 := witnessFinal50 0 0 0 0 0 1 105
  0x0 (by decide +kernel)
private def chunks0 : List (Chunk 0) := [
  cert0_0]
def rows0 := rowsFrom chunks0

theorem good0 : ∀ r ∈ rows0, good 0 r = true := rowsFrom_good chunks0

theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks0 0 (by decide +kernel)).1

theorem mass0 (i : Fin 60) :
    bandCount 0 (i.val : ℤ) 59 14 ≤ (rows0.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks0).filter _).length
  rw [mass_eq]
  have h : (List.range 60).all
      (fun j => decide (bandCount 0 (j : ℤ) 59 14 ≤ mass j chunks0)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total0 : (rows0.map (price 0)).sum = 105 :=
  (total_eq chunks0).trans (by decide +kernel)

private def cert1_0 := witnessFinal50 1 3 0 64 64 1 105
  0x0 (by decide +kernel)
private def cert1_1 := witnessFinal50 1 2 0 10001 10001 1 105
  0x0 (by decide +kernel)
private def cert1_2 := witnessFinal50 1 1 0 20000 20000 1 105
  0x0 (by decide +kernel)
private def cert1_3 := witnessFinal50 1 0 0 30000 30000 1 101
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

theorem mass1 (i : Fin 60) :
    bandCount 1 (i.val : ℤ) 59 14 ≤ (rows1.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks1).filter _).length
  rw [mass_eq]
  have h : (List.range 60).all
      (fun j => decide (bandCount 1 (j : ℤ) 59 14 ≤ mass j chunks1)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total1 : (rows1.map (price 1)).sum = 416 :=
  (total_eq chunks1).trans (by decide +kernel)

private def cert2_0 := witnessFinal50 2 6 0 128 128 1 105
  0x0 (by decide +kernel)
private def cert2_1 := witnessFinal50 2 5 0 10065 10065 1 105
  0x0 (by decide +kernel)
private def cert2_2 := witnessFinal50 2 4 0 20002 20064 2 210
  0x0 (by decide +kernel)
private def cert2_3 := witnessFinal50 2 3 0 30001 30064 2 206
  0x488 (by decide +kernel)
private def cert2_4 := witnessFinal50 2 2 0 40000 40001 2 206
  0x488 (by decide +kernel)
private def cert2_5 := witnessFinal50 2 1 0 50000 50000 1 101
  0x91 (by decide +kernel)
private def cert2_6 := witnessFinal50 2 0 0 60000 60000 1 97
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

theorem mass2 (i : Fin 60) :
    bandCount 2 (i.val : ℤ) 59 14 ≤ (rows2.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks2).filter _).length
  rw [mass_eq]
  have h : (List.range 60).all
      (fun j => decide (bandCount 2 (j : ℤ) 59 14 ≤ mass j chunks2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total2 : (rows2.map (price 2)).sum = 1030 :=
  (total_eq chunks2).trans (by decide +kernel)

private def cert3_0 := witnessFinal50 3 9 0 192 192 1 105
  0x0 (by decide +kernel)
private def cert3_1 := witnessFinal50 3 8 0 10129 10129 1 105
  0x0 (by decide +kernel)
private def cert3_2 := witnessFinal50 3 7 0 20066 20128 2 210
  0x0 (by decide +kernel)
private def cert3_3 := witnessFinal50 3 6 0 30003 30128 3 311
  0x2440 (by decide +kernel)
private def cert3_4 := witnessFinal50 3 5 0 40002 40065 3 311
  0x2440 (by decide +kernel)
private def cert3_5 := witnessFinal50 3 4 0 50001 50064 3 307
  0x244488 (by decide +kernel)
private def cert3_6 := witnessFinal50 3 3 0 60000 60064 3 303
  0x444488 (by decide +kernel)
private def cert3_7 := witnessFinal50 3 2 0 70000 70001 2 198
  0x88891 (by decide +kernel)
private def cert3_8 := witnessFinal50 3 1 0 80000 80000 1 97
  0x111 (by decide +kernel)
private def cert3_9 := witnessFinal50 3 0 0 90000 90000 1 93
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

theorem mass3 (i : Fin 60) :
    bandCount 3 (i.val : ℤ) 59 14 ≤ (rows3.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks3).filter _).length
  rw [mass_eq]
  have h : (List.range 60).all
      (fun j => decide (bandCount 3 (j : ℤ) 59 14 ≤ mass j chunks3)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total3 : (rows3.map (price 3)).sum = 2040 :=
  (total_eq chunks3).trans (by decide +kernel)

private def cert4_0 := witnessFinal50 4 12 0 256 256 1 105
  0x0 (by decide +kernel)
private def cert4_1 := witnessFinal50 4 11 0 10193 10193 1 105
  0x0 (by decide +kernel)
private def cert4_2 := witnessFinal50 4 10 0 20130 20192 2 210
  0x0 (by decide +kernel)
private def cert4_3 := witnessFinal50 4 9 0 30067 30192 3 311
  0x2440 (by decide +kernel)
private def cert4_4 := witnessFinal50 4 8 0 40004 40129 4 416
  0x12200 (by decide +kernel)
private def cert4_5 := witnessFinal50 4 7 0 50003 50128 4 412
  0x1222440 (by decide +kernel)
private def cert4_6 := witnessFinal50 4 6 0 60002 60128 5 509
  0x1111220488 (by decide +kernel)
private def cert4_7 := witnessFinal50 4 5 0 70001 70065 4 404
  0x222244488 (by decide +kernel)
private def cert4_8 := witnessFinal50 4 4 0 80000 80064 4 400
  0x222444488 (by decide +kernel)
private def cert4_9 := witnessFinal50 4 3 0 90000 90064 3 291
  0x64488891 (by decide +kernel)
private def cert4_10 := witnessFinal50 4 2 0 100000 100001 2 190
  0xc8911 (by decide +kernel)
private def cert4_11 := witnessFinal50 4 1 0 110000 110000 1 93
  0x191 (by decide +kernel)
private def cert4_12 := witnessFinal50 4 0 0 120000 120000 1 89
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

theorem mass4 (i : Fin 60) :
    bandCount 4 (i.val : ℤ) 59 14 ≤ (rows4.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks4).filter _).length
  rw [mass_eq]
  have h : (List.range 60).all
      (fun j => decide (bandCount 4 (j : ℤ) 59 14 ≤ mass j chunks4)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total4 : (rows4.map (price 4)).sum = 3535 :=
  (total_eq chunks4).trans (by decide +kernel)


end Final50RankReceipt

end Merged_Final50RankReceiptGroup0
