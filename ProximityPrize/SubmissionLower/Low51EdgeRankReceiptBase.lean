import ProximityPrize.SubmissionLower.RankRows82190

set_option Elab.async false
namespace Low51EdgeRankReceipt
open K1_13_1_1 (bandCount)
open AnchorPivot82180 (monoData)
abbrev Row := RankRows82190.Row

def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 53 ∧ x.top ≤ 13 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

/-- Leading exponents of the nine factors, in the order of `AnchorPivot82190.allData`. -/
private def pivot (i : Fin 9) : AnchorPivot82180.E :=
  ![⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,1,0,0⟩, ⟨1,1,0,0⟩,
    ⟨1,0,1,0⟩, ⟨2,0,1,0⟩, ⟨1,3,0,0⟩, ⟨2,3,0,0⟩] i

private abbrev E := AnchorPivot82180.E
private abbrev Factor := RankRows82190.Factor

/-- The low 4 bits select a factor and the next 4 bits give its multiplicity.
  If the multiplicity field is zero, the next 6 bits give the multiplicity. -/
def readFactors : ℕ → ℕ → List Factor × ℕ
  | 0, bits => ([], bits)
  | n+1, bits =>
    let i : Fin 9 := ⟨(bits % 16) % 9, Nat.mod_lt _ (by decide)⟩
    let k := bits / 16 % 16
    let rest := bits / 256
    let (fs, tail) := readFactors n (if k = 0 then rest / 64 else rest)
    ((i, if k = 0 then rest % 64 else k) :: fs, tail)

/-- Read the 3-bit factor count at the start of each row. -/
def readSchedules : ℕ → ℕ → List (List Factor)
  | 0, _ => []
  | n+1, bits =>
    let (fs, rest) := readFactors (bits % 8) (bits / 8)
    fs :: readSchedules n rest

def pivots (d i : ℕ) : List E :=
  (List.range (min (min d 13) (i / 3) + 1)).flatMap fun f =>
    let lo := i - (d + 2*f)
    let hi := min (d-f) ((i-3*f)/2)
    (List.range (hi+1-lo)).map fun k =>
      let c := lo+k
      let b := i-2*c-3*f
      ⟨d-b-c-f, b, c, f⟩

def subtractPivot (e : E) (f : Factor) : E :=
  let p := pivot f.1
  ⟨e.a-f.2*p.a, e.b-f.2*p.b, e.c-f.2*p.c, e.f-f.2*p.f⟩

def decodeRow (e : E) (fs : List Factor) : Row :=
  let r := fs.foldl subtractPivot e
  let x := (monoData r).plus (RankRows82190.measure fs)
  ⟨x.tag, x.lo, x.ord, r, fs⟩

def decode (d i start n data : ℕ) : List Row :=
  ((pivots d i).drop start).zipWith decodeRow (readSchedules n data)

def fee (s : ℕ) (r : Row) : ℕ := 94 + r.index - (s + r.ord)
def triangle (n : ℕ) : ℕ := n * (n+1) / 2

def extra : ℕ → ℕ
  | 31 => 125
  | 33 => 123
  | 35 => 121
  | 37 => 119
  | 39 => 117
  | 41 => 115
  | 43 => 113
  | 45 => 111
  | 47 => 110
  | 48 => 109
  | 49 => 108
  | 50 => 107
  | 51 => 106
  | 52 => 105
  | _ => 127

def price (d : ℕ) (r : Row) : ℕ :=
  if d = 53 then triangle (fee 53 r) - triangle (fee 105 r)
  else fee d r + if extra d < 127 then
    fee (extra d) r + if d ≤ 45 then fee (extra d + 1) r else 0
    else 0

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

end Low51EdgeRankReceipt

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt (Row triangle)

def fee (s : ℕ) (r : Row) : ℕ := 96 + r.index - (s + r.ord)

def extra : ℕ → ℕ × ℕ
  | 32 => (128, 2)
  | 34 => (126, 2)
  | 36 => (124, 2)
  | 39 => (122, 2)
  | 41 => (120, 2)
  | 43 => (118, 2)
  | 45 => (116, 2)
  | 47 => (114, 2)
  | 49 => (112, 2)
  | 51 => (110, 2)
  | 53 => (54, 56)
  | _ => (130, 0)

def price (d : ℕ) (r : Row) : ℕ :=
  fee d r + (triangle (fee (extra d).1 r) - triangle (fee ((extra d).1 + (extra d).2) r))

end Cutter53AnchorRankReceipt

namespace Low51EdgeRankReceipt
open AnchorPivot82180 (monoData)

/-- Check each decoded row and accumulate its retained c53 fee in the same pass. -/
private def scan (d i upper lower : ℕ) : List E → List (List Factor) → Bool × ℕ × ℕ
  | e :: es, fs :: fss =>
    let r := fs.foldl subtractPivot e
    let x := (monoData r).plus (RankRows82190.measure fs)
    match scan d i upper (x.tag+1) es fss with
    | (ok, n, fees) =>
      (decide (lower ≤ x.tag ∧ x.tag ≤ upper ∧ x.lo = i) &&
        decide (x.deg = d ∧ x.hi ≤ 53 ∧ x.top ≤ 13) && ok,
       n+1, Cutter53AnchorRankReceipt.price d ⟨x.tag,x.lo,x.ord,r,fs⟩ + fees)
  | _, _ => (true, 0, 0)

private theorem scan_eq (d i upper lower : ℕ) (es : List E) (ss : List (List Factor)) :
    scan d i upper lower es ss =
      let rows := es.zipWith decodeRow ss
      (checkRows d i upper lower rows, rows.length,
        (rows.map (Cutter53AnchorRankReceipt.price d)).sum) := by
  induction es generalizing ss lower with
  | nil => rfl
  | cons e es ih =>
    cases ss with
    | nil => rfl
    | cons fs ss =>
      simp [scan, ih, List.zipWith, checkRows, decodeRow, good, RankRows82190.Row.bounds]

def scanChunk (d i start lo hi n bits : ℕ) : Bool × ℕ × ℕ :=
  scan d i hi lo ((pivots d i).drop start) (readSchedules n bits)

theorem scanChunk_eq (d i start lo hi n bits : ℕ) :
    scanChunk d i start lo hi n bits =
      let rows := decode d i start n bits
      (checkRows d i hi lo rows, rows.length,
        (rows.map (Cutter53AnchorRankReceipt.price d)).sum) :=
  scan_eq ..

structure Chunk (d : ℕ) where
  index : ℕ
  lower : ℕ
  upper : ℕ
  size : ℕ
  charged : ℕ
  rows : List Row
  checked : checkRows d index upper lower rows = true
  length_eq : rows.length = size
  charge_eq : (rows.map (Cutter53AnchorRankReceipt.price d)).sum = charged

/-- Assemble a data chunk from its single checked summary. -/
def witnessLow51 (d i start lo hi n charged bits : ℕ)
    (checked : scanChunk d i start lo hi n bits = (true, n, charged)) : Chunk d := by
  rw [scanChunk_eq] at checked
  exact ⟨i, lo, hi, n, charged, decode d i start n bits,
    congrArg Prod.fst checked, congrArg (fun r => r.2.1) checked,
    congrArg (fun r => r.2.2) checked⟩


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

def chunkFees {d : ℕ} (cs : List (Chunk d)) : ℕ :=
  (cs.map Chunk.charged).sum

theorem chunkFees_eq {d : ℕ} (cs : List (Chunk d)) :
    ((rowsFrom cs).map (Cutter53AnchorRankReceipt.price d)).sum = chunkFees cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change ((c.rows ++ rowsFrom cs).map (Cutter53AnchorRankReceipt.price d)).sum = _
    rw [List.map_append, List.sum_append, c.charge_eq, ih]
    rfl
end Low51EdgeRankReceipt
