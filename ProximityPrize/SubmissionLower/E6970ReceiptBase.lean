import ProximityPrize.SubmissionLower.Z6970RankFactorRule
import ProximityPrize.SubmissionLower.E6970FinalRankBlocks

set_option Elab.async false

-- merged module A6966FinalRankReceiptGroup0
section Merged_A6966FinalRankReceiptGroup0

-- merged module A6966FinalRankReceiptBase
section Merged_A6966FinalRankReceiptBase
set_option Elab.async false
namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)
open AnchorPivot82180 (monoData)
abbrev Row := A6966Rows.Row
def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 60 ∧ x.top ≤ 16 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)
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
  (List.range (min (min d 16) (i / 3) + 1)).flatMap fun f =>
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
def fee (s : ℕ) (r : Row) : ℕ := 107 + r.index - (s + r.ord)
def triangle (n : ℕ) : ℕ := n * (n+1) / 2
def stageRange : ℕ → ℕ × ℕ
  | 36 => (143, 144)
  | 37 => (142, 143)
  | 38 => (141, 142)
  | 39 => (140, 141)
  | 40 => (139, 140)
  | 41 => (138, 139)
  | 42 => (137, 138)
  | 43 => (136, 137)
  | 44 => (135, 136)
  | 45 => (134, 135)
  | 46 => (133, 134)
  | 47 => (132, 133)
  | 48 => (131, 132)
  | 49 => (130, 131)
  | 50 => (129, 130)
  | 51 => (128, 129)
  | 52 => (127, 128)
  | 53 => (126, 127)
  | 54 => (125, 126)
  | 55 => (124, 125)
  | 56 => (123, 124)
  | 57 => (122, 123)
  | 58 => (121, 122)
  | 59 => (120, 121)
  | 60 => (61, 120)
  | _ => (144, 144)
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

private def rowsWithRule (i : ℕ) : List E → ℕ → List (List Factor) → List Row
  | [], _, _ => []
  | e :: es, mask, exceptions =>
    if mask % 2 = 1 then
      let planned := RankFactor6970.schedule ⟨e.a,e.b,e.c,60-i,16-e.f⟩
      decodeRow e planned :: rowsWithRule i es (mask/2) exceptions
    else
      decodeRow e (exceptions.headD []) :: rowsWithRule i es (mask/2) exceptions.tail

private def decodeWithRule (d i start n mask bits : ℕ) : List Row :=
  rowsWithRule i (((pivots d i).drop start).take n) mask (readSchedules n bits)

def witnessRule (d i start lo hi n total mask bits : ℕ)
    (checked : checkRows d i hi lo (decodeWithRule d i start n mask bits) = true ∧
      (decodeWithRule d i start n mask bits).length = n ∧
      ((decodeWithRule d i start n mask bits).map (price d)).sum = total) : Chunk d :=
  ⟨i, lo, hi, n, total, decodeWithRule d i start n mask bits, checked.1, checked.2.1, checked.2.2⟩

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
end E6970FinalRankReceipt

end Merged_A6966FinalRankReceiptBase
end Merged_A6966FinalRankReceiptGroup0
