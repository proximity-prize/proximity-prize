import ProximityPrize.SubmissionLower.RankRows82190

set_option Elab.async false
namespace Final50RankReceipt
open K1_13_1_1 (bandCount)
open AnchorPivot82180 (monoData)
abbrev Row := RankRows82190.Row

def good (d : ℕ) (r : Row) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 55 ∧ x.top ≤ 14 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

/-- Leading exponents of the nine factors, in the order of `AnchorPivot82190.allData`. -/
private def pivot (i : Fin 9) : AnchorPivot82180.E :=
  ![⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,0,0,0⟩, ⟨1,1,0,0⟩, ⟨1,1,0,0⟩,
    ⟨1,0,1,0⟩, ⟨2,0,1,0⟩, ⟨1,3,0,0⟩, ⟨2,3,0,0⟩] i

private abbrev E := AnchorPivot82180.E
private abbrev Factor := RankRows82190.Factor

/-- The low 4 bits select a factor and the next 4 bits give its multiplicity.
  If the multiplicity field is zero, the next 6 bits give the multiplicity. -/
private def readFactors : ℕ → ℕ → List Factor × ℕ
  | 0, bits => ([], bits)
  | n+1, bits =>
    let i : Fin 9 := ⟨(bits % 16) % 9, Nat.mod_lt _ (by decide)⟩
    let k := bits / 16 % 16
    let rest := bits / 256
    let (fs, tail) := readFactors n (if k = 0 then rest / 64 else rest)
    ((i, if k = 0 then rest % 64 else k) :: fs, tail)

/-- Read the 3-bit factor count at the start of each row. -/
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

def fee (s : ℕ) (r : Row) : ℕ := 99 + r.index - (s + r.ord)
def triangle (n : ℕ) : ℕ := n * (n+1) / 2

def stageRange : ℕ → ℕ × ℕ
  | 33 => (132, 133)
  | 34 => (131, 132)
  | 35 => (130, 131)
  | 36 => (129, 130)
  | 37 => (128, 129)
  | 38 => (127, 128)
  | 39 => (126, 127)
  | 40 => (125, 126)
  | 41 => (124, 125)
  | 42 => (123, 124)
  | 43 => (122, 123)
  | 44 => (121, 122)
  | 45 => (120, 121)
  | 46 => (119, 120)
  | 47 => (118, 119)
  | 48 => (117, 118)
  | 49 => (116, 117)
  | 50 => (115, 116)
  | 51 => (114, 115)
  | 52 => (113, 114)
  | 53 => (112, 113)
  | 54 => (111, 112)
  | 55 => (56, 111)
  | _ => (133, 133)

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

/-- `allData` as a `Nat` match: the kernel reads it without unfolding `![…]` (`Fin.cons`). -/
private def allDataN : ℕ → AnchorPivot82180.Data
  | 0 => ⟨1,0,1,0,1,30000⟩
  | 1 => ⟨1,0,2,0,2,30000⟩
  | 2 => ⟨1,0,3,1,3,30000⟩
  | 3 => ⟨2,1,2,0,2,50000⟩
  | 4 => ⟨2,1,3,1,3,50000⟩
  | 5 => ⟨2,2,4,1,4,40001⟩
  | 6 => ⟨3,2,3,1,3,70001⟩
  | 7 => ⟨4,3,4,1,3,90000⟩
  | _ => ⟨5,3,6,2,6,120000⟩

private theorem allDataN_eq (i : Fin 9) : allDataN i.val = AnchorPivot82190.allData i := by
  fin_cases i <;> first | rfl | decide

private def measureF : List Factor → AnchorPivot82180.Data
  | [] => AnchorPivot82180.Data.unit
  | (i,k)::xs => ((allDataN i.val).times k).plus (measureF xs)

private theorem measureF_eq (fs : List Factor) : measureF fs = RankRows82190.measure fs := by
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i, k⟩ := x
    rw [measureF, RankRows82190.measure, ih, allDataN_eq]

/-- `pivot` as a `Nat` match. -/
private def pivotN : ℕ → E
  | 0 => ⟨1,0,0,0⟩
  | 1 => ⟨1,0,0,0⟩
  | 2 => ⟨1,0,0,0⟩
  | 3 => ⟨1,1,0,0⟩
  | 4 => ⟨1,1,0,0⟩
  | 5 => ⟨1,0,1,0⟩
  | 6 => ⟨2,0,1,0⟩
  | 7 => ⟨1,3,0,0⟩
  | _ => ⟨2,3,0,0⟩

private theorem pivotN_eq (i : Fin 9) : pivotN i.val = pivot i := by
  fin_cases i <;> rfl

private def subtractPivotN (e : E) (f : Factor) : E :=
  let p := pivotN f.1.val
  ⟨e.a-f.2*p.a, e.b-f.2*p.b, e.c-f.2*p.c, e.f-f.2*p.f⟩

private theorem subtractPivotN_eq : subtractPivotN = subtractPivot := by
  funext e f
  simp only [subtractPivotN, subtractPivot, pivotN_eq]

/-- Check each decoded row and accumulate its price in the same pass. -/
private def scan (d i upper lower : ℕ) : List E → List (List Factor) → Bool × ℕ × ℕ
  | e :: es, fs :: fss =>
    let r := fs.foldl subtractPivotN e
    let x := (monoData r).plus (measureF fs)
    match scan d i upper (x.tag+1) es fss with
    | (ok, n, total) =>
      (decide (lower ≤ x.tag ∧ x.tag ≤ upper ∧ x.lo = i) &&
        decide (x.deg = d ∧ x.hi ≤ 55 ∧ x.top ≤ 14) && ok,
       n+1, price d ⟨x.tag,x.lo,x.ord,r,fs⟩ + total)
  | _, _ => (true, 0, 0)

private theorem scan_eq (d i upper lower : ℕ) (es : List E) (ss : List (List Factor)) :
    scan d i upper lower es ss =
      let rows := es.zipWith decodeRow ss
      (checkRows d i upper lower rows, rows.length, (rows.map (price d)).sum) := by
  induction es generalizing ss lower with
  | nil => rfl
  | cons e es ih =>
    cases ss with
    | nil => rfl
    | cons fs ss =>
      simp [scan, ih, measureF_eq, subtractPivotN_eq, List.zipWith, checkRows, decodeRow, good,
        RankRows82190.Row.bounds]

def scanChunk (d i start lo hi n bits : ℕ) : Bool × ℕ × ℕ :=
  scan d i hi lo ((pivots d i).drop start) (readSchedules n bits)

theorem scanChunk_eq (d i start lo hi n bits : ℕ) :
    scanChunk d i start lo hi n bits =
      let rows := decode d i start n bits
      (checkRows d i hi lo rows, rows.length, (rows.map (price d)).sum) :=
  scan_eq ..

/-! Raw-`Nat` evaluator for the data chunks (same values as `scanChunk`; the kernel
  evaluates `Nat.add`/`Nat.sub`/`Nat.mul`/`Nat.div`/`Nat.ble`/`Nat.beq` directly). -/
private def nmin (a b : Nat) : Nat := cond (Nat.ble a b) a b
private theorem nmin_eq (a b : Nat) : nmin a b = min a b := by
  unfold nmin; cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; cases h
    show b = min a b; omega
  · have : a ≤ b := Nat.le_of_ble_eq_true h
    show a = min a b; omega

private def pivotsR (d i : Nat) : List E :=
  (List.range (Nat.succ (nmin (nmin d 14) (Nat.div i 3)))).flatMap fun f =>
    let lo := Nat.sub i (Nat.add d (Nat.mul 2 f))
    let hi := nmin (Nat.sub d f) (Nat.div (Nat.sub i (Nat.mul 3 f)) 2)
    (List.range (Nat.sub (Nat.succ hi) lo)).map fun k =>
      let c := Nat.add lo k
      let b := Nat.sub (Nat.sub i (Nat.mul 2 c)) (Nat.mul 3 f)
      ⟨Nat.sub (Nat.sub (Nat.sub d b) c) f, b, c, f⟩

private theorem pivotsR_eq (d i : Nat) : pivotsR d i = pivots d i := by
  simp only [pivotsR, pivots, nmin_eq]; rfl

private def readFactorsR : Nat → Nat → List Factor × Nat
  | 0, bits => ([], bits)
  | n+1, bits =>
    let k := Nat.mod (Nat.div bits 16) 16
    let rest := Nat.div bits 256
    match Nat.beq k 0 with
    | true => match readFactorsR n (Nat.div rest 64) with
      | (fs, tail) => ((⟨Nat.mod (Nat.mod bits 16) 9, Nat.mod_lt _ (by decide)⟩, Nat.mod rest 64) :: fs, tail)
    | false => match readFactorsR n rest with
      | (fs, tail) => ((⟨Nat.mod (Nat.mod bits 16) 9, Nat.mod_lt _ (by decide)⟩, k) :: fs, tail)

private theorem readFactorsR_eq (n bits : Nat) : readFactorsR n bits = readFactors n bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    cases h : Nat.beq (Nat.mod (Nat.div bits 16) 16) 0
    · have hk : ¬ bits / 16 % 16 = 0 := Nat.ne_of_beq_eq_false h
      simp only [readFactorsR, readFactors, hk, ite_false, h, ← ih]
      rfl
    · have hk : bits / 16 % 16 = 0 := Nat.eq_of_beq_eq_true h
      simp only [readFactorsR, readFactors, hk, ite_true, h, ← ih]
      rfl

private def readSchedulesR : Nat → Nat → List (List Factor)
  | 0, _ => []
  | n+1, bits =>
    match readFactorsR (Nat.mod bits 8) (Nat.div bits 8) with
    | (fs, rest) => fs :: readSchedulesR n rest

private theorem readSchedulesR_eq (n bits : Nat) : readSchedulesR n bits = readSchedules n bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    simp only [readSchedulesR, readSchedules, readFactorsR_eq, ih]; rfl

/-- One decoded row, all in raw `Nat` arithmetic: subtract the pivots and add the factor data. -/
private def rowF (a b c f dg lo hi tp od tg : Nat) : List Factor → AnchorPivot82180.Data
  | [] =>
    let idx := Nat.add b (Nat.add (Nat.mul 2 c) (Nat.mul 3 f))
    ⟨Nat.add dg (Nat.add a (Nat.add b (Nat.add c f))), Nat.add lo idx, Nat.add hi idx, Nat.add tp f,
     Nat.add od (Nat.add c (Nat.mul 2 f)),
     Nat.add tg (Nat.add (Nat.mul 30000 a) (Nat.add (Nat.mul 20000 b) (Nat.add (Nat.mul 10001 c) (Nat.mul 64 f))))⟩
  | (i,k)::xs =>
    match i.val with
    | 0 => rowF (Nat.sub a k) b c f (Nat.add dg k) lo (Nat.add hi k) tp (Nat.add od k) (Nat.add tg (Nat.mul 30000 k)) xs
    | 1 => rowF (Nat.sub a k) b c f (Nat.add dg k) lo (Nat.add hi (Nat.mul 2 k)) tp (Nat.add od (Nat.mul 2 k)) (Nat.add tg (Nat.mul 30000 k)) xs
    | 2 => rowF (Nat.sub a k) b c f (Nat.add dg k) lo (Nat.add hi (Nat.mul 3 k)) (Nat.add tp k) (Nat.add od (Nat.mul 3 k)) (Nat.add tg (Nat.mul 30000 k)) xs
    | 3 => rowF (Nat.sub a k) (Nat.sub b k) c f (Nat.add dg (Nat.mul 2 k)) (Nat.add lo k) (Nat.add hi (Nat.mul 2 k)) tp (Nat.add od (Nat.mul 2 k)) (Nat.add tg (Nat.mul 50000 k)) xs
    | 4 => rowF (Nat.sub a k) (Nat.sub b k) c f (Nat.add dg (Nat.mul 2 k)) (Nat.add lo k) (Nat.add hi (Nat.mul 3 k)) (Nat.add tp k) (Nat.add od (Nat.mul 3 k)) (Nat.add tg (Nat.mul 50000 k)) xs
    | 5 => rowF (Nat.sub a k) b (Nat.sub c k) f (Nat.add dg (Nat.mul 2 k)) (Nat.add lo (Nat.mul 2 k)) (Nat.add hi (Nat.mul 4 k)) (Nat.add tp k) (Nat.add od (Nat.mul 4 k)) (Nat.add tg (Nat.mul 40001 k)) xs
    | 6 => rowF (Nat.sub a (Nat.mul k 2)) b (Nat.sub c k) f (Nat.add dg (Nat.mul 3 k)) (Nat.add lo (Nat.mul 2 k)) (Nat.add hi (Nat.mul 3 k)) (Nat.add tp k) (Nat.add od (Nat.mul 3 k)) (Nat.add tg (Nat.mul 70001 k)) xs
    | 7 => rowF (Nat.sub a k) (Nat.sub b (Nat.mul k 3)) c f (Nat.add dg (Nat.mul 4 k)) (Nat.add lo (Nat.mul 3 k)) (Nat.add hi (Nat.mul 4 k)) (Nat.add tp k) (Nat.add od (Nat.mul 3 k)) (Nat.add tg (Nat.mul 90000 k)) xs
    | _ => rowF (Nat.sub a (Nat.mul k 2)) (Nat.sub b (Nat.mul k 3)) c f (Nat.add dg (Nat.mul 5 k)) (Nat.add lo (Nat.mul 3 k)) (Nat.add hi (Nat.mul 6 k)) (Nat.add tp (Nat.mul 2 k)) (Nat.add od (Nat.mul 6 k)) (Nat.add tg (Nat.mul 120000 k)) xs

private theorem rowF_eq (fs : List Factor) : ∀ (a b c f dg lo hi tp od tg : Nat),
    rowF a b c f dg lo hi tp od tg fs =
      (AnchorPivot82180.Data.mk dg lo hi tp od tg).plus ((monoData (fs.foldl subtractPivotN ⟨a,b,c,f⟩)).plus (measureF fs)) := by
  induction fs with
  | nil =>
    intro a b c f dg lo hi tp od tg
    simp only [rowF, List.foldl, monoData, measureF, AnchorPivot82180.Data.plus, AnchorPivot82180.Data.unit, AnchorPivot82180.E.deg, AnchorPivot82180.E.index, AnchorPivot82180.E.key,
      Nat.add_eq, Nat.mul_eq, AnchorPivot82180.Data.mk.injEq]
    omega
  | cons x xs ih =>
    intro a b c f dg lo hi tp od tg
    obtain ⟨⟨i, hi'⟩, k⟩ := x
    rcases i with _|_|_|_|_|_|_|_|_|i
    all_goals first
      | (exfalso; omega)
      | (simp only [rowF, ih, List.foldl, subtractPivotN, pivotN, measureF, allDataN, AnchorPivot82180.Data.plus, AnchorPivot82180.Data.times,
          monoData, AnchorPivot82180.E.deg, AnchorPivot82180.E.index, AnchorPivot82180.E.key, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.mul_one, Nat.mul_zero,
          Nat.sub_zero, AnchorPivot82180.Data.mk.injEq]
         omega)

private theorem rowF_e (e : E) (fs : List Factor) :
    rowF e.a e.b e.c e.f 0 0 0 0 0 0 fs = (monoData (fs.foldl subtractPivotN e)).plus (measureF fs) := by
  rw [rowF_eq]
  generalize (monoData (fs.foldl subtractPivotN ⟨e.a, e.b, e.c, e.f⟩)).plus (measureF fs) = y
  cases y; simp only [AnchorPivot82180.Data.plus, Nat.zero_add]

private theorem ndiv_eq (a b : Nat) : Nat.div a b = a / b := rfl

private theorem ble_dec (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; cases h
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

private theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

private def priceR (d lo hi idx ord : Nat) : Nat :=
  Nat.add (Nat.sub (Nat.add 99 idx) (Nat.add d ord))
    (Nat.sub (Nat.div (Nat.mul (Nat.sub (Nat.add 99 idx) (Nat.add lo ord)) (Nat.succ (Nat.sub (Nat.add 99 idx) (Nat.add lo ord)))) 2)
      (Nat.div (Nat.mul (Nat.sub (Nat.add 99 idx) (Nat.add hi ord)) (Nat.succ (Nat.sub (Nat.add 99 idx) (Nat.add hi ord)))) 2))

/-- `scan` with accumulators and raw arithmetic. -/
private def scanF (d i upper lo hi : Nat) : Nat → Bool → Nat → Nat → List E → List (List Factor) → Bool × Nat × Nat
  | lower, ok, n, total, e :: es, fs :: fss =>
    let x := rowF e.a e.b e.c e.f 0 0 0 0 0 0 fs
    scanF d i upper lo hi (Nat.succ x.tag)
      (ok && Nat.ble lower x.tag && Nat.ble x.tag upper && Nat.beq x.lo i &&
        Nat.beq x.deg d && Nat.ble x.hi 55 && Nat.ble x.top 14)
      (Nat.succ n) (Nat.add (priceR d lo hi x.lo x.ord) total) es fss
  | _, ok, n, total, _, _ => (ok, n, total)

private theorem scanF_eq (d i upper : Nat) (es : List E) : ∀ (fss : List (List Factor)) (lower : Nat) (ok : Bool) (n t : Nat),
    scanF d i upper (lateLo d) (lateHi d) lower ok n t es fss =
      ((ok && (scan d i upper lower es fss).1), n + (scan d i upper lower es fss).2.1,
        (scan d i upper lower es fss).2.2 + t) := by
  induction es with
  | nil => intro fss lower ok n t; simp [scanF, scan]
  | cons e es ih =>
    intro fss lower ok n t
    cases fss with
    | nil => simp [scanF, scan]
    | cons fs fss =>
      simp only [scanF, scan, rowF_e]
      rw [ih]
      generalize scan d i upper ((monoData (List.foldl subtractPivotN e fs)).plus (measureF fs)).tag.succ es fss = s
      obtain ⟨ok', n', t'⟩ := s
      simp only [ble_dec, beq_dec, Bool.decide_and, Bool.and_assoc, Prod.mk.injEq, price, fee, triangle, priceR,
        Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ndiv_eq, Nat.succ_eq_add_one]
      refine ⟨?_, by omega, by omega⟩
      cases ok <;> simp

def scanChunkF (d i start lo hi n bits : Nat) : Bool × Nat × Nat :=
  scanF d i hi (lateLo d) (lateHi d) lo true 0 0 ((pivotsR d i).drop start) (readSchedulesR n bits)

theorem scanChunk_of_fast {d i start lo hi n total bits : Nat}
    (h : scanChunkF d i start lo hi n bits = (true, n, total)) :
    scanChunk d i start lo hi n bits = (true, n, total) := by
  rw [scanChunkF, scanF_eq, pivotsR_eq, readSchedulesR_eq] at h
  simp only [Bool.true_and, Nat.zero_add, Nat.add_zero] at h
  exact h

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

/-- Assemble a data chunk from its single checked summary (one fused decode/check/price pass). -/
def witnessFinal50 (d i start lo hi n total bits : ℕ)
    (checked : scanChunkF d i start lo hi n bits = (true, n, total)) : Chunk d := by
  have checked := scanChunk_of_fast checked
  rw [scanChunk_eq] at checked
  exact ⟨i, lo, hi, n, total, decode d i start n bits,
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
