import ProximityPrize.SubmissionLower.Final50RankReceiptBase

set_option Elab.async false

namespace Final50RankReceipt
open AnchorPivot82180 (monoData)
open private pivot readFactors readSchedules pivots subtractPivot decodeRow
  from ProximityPrize.SubmissionLower.Final50RankReceiptBase

private abbrev E := AnchorPivot82180.E
private abbrev Factor := RankRows82190.Factor

/-!
The fused rank checker is adapted from peer submission
51ae3460-7335-4d6d-a02e-2e94e4d62f1f, commit
1dfb4484462fc7bb527496261e77c10a39978735, ProximityPrize/SubmissionLower/Final50RankReceiptBase.lean
lines 118–359 and 372–379. Its checker uses the current bound of 56 and
the current price schedule from Final50RankReceiptBase.
-/

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
        decide (x.deg = d ∧ x.hi ≤ 56 ∧ x.top ≤ 14) && ok,
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
  Nat.add (Nat.sub (Nat.add 102 idx) (Nat.add d ord))
    (Nat.sub (Nat.div (Nat.mul (Nat.sub (Nat.add 102 idx) (Nat.add lo ord)) (Nat.succ (Nat.sub (Nat.add 102 idx) (Nat.add lo ord)))) 2)
      (Nat.div (Nat.mul (Nat.sub (Nat.add 102 idx) (Nat.add hi ord)) (Nat.succ (Nat.sub (Nat.add 102 idx) (Nat.add hi ord)))) 2))

/-- `scan` with accumulators and raw arithmetic. -/
private def scanF (d i upper lo hi : Nat) : Nat → Bool → Nat → Nat → List E → List (List Factor) → Bool × Nat × Nat
  | lower, ok, n, total, e :: es, fs :: fss =>
    let x := rowF e.a e.b e.c e.f 0 0 0 0 0 0 fs
    scanF d i upper lo hi (Nat.succ x.tag)
      (ok && Nat.ble lower x.tag && Nat.ble x.tag upper && Nat.beq x.lo i &&
        Nat.beq x.deg d && Nat.ble x.hi 56 && Nat.ble x.top 14)
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

private def unpackRankBlock (s : String) : Nat :=
  s.toByteArray.data.toList.foldl (fun acc byte =>
    let b := byte.toNat
    Nat.add (Nat.mul acc 92)
      (Nat.sub b (cond (Nat.blt b 35) 33 (cond (Nat.blt b 93) 34 35)))) 0

/-- Read base-92 blocks, least significant first. Only the last can have fewer
than 64 ASCII digits. Short string literals avoid rebuilding a long byte array. -/
private def unpackRankBlocks (blocks : List String) : Nat :=
  -- The multiplier is 92^64.
  blocks.foldr (fun block high =>
    Nat.add (unpackRankBlock block) (Nat.mul 0x2d816085efa8903779c0cd4688cc50b7595093cccfdaa9edb2ef95325559f5891482c320100000000000000000000000000000000 high)) 0

/-- Assemble a data chunk from its single checked summary. -/
def witnessFinal50Fast (d i start lo hi n total : ℕ) (blocks : List String)
    (checked : scanChunkF d i start lo hi n (unpackRankBlocks blocks) = (true, n, total) := by
      decide +kernel) : Chunk d := by
  let bits := unpackRankBlocks blocks
  have checked := scanChunk_of_fast (bits := bits) checked
  rw [scanChunk_eq] at checked
  exact ⟨i, lo, hi, n, total, decode d i start n bits,
    congrArg Prod.fst checked, congrArg (fun r => r.2.1) checked,
    congrArg (fun r => r.2.2) checked⟩

end Final50RankReceipt
