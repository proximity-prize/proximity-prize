import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof
import ProximityPrize.SubmissionLower.Beyond70Hall
import ProximityPrize.SubmissionLower.Beyond70Slice

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace R6970Scalar84Rank
open CJ1 (Block total total_eq_sum entryZ)
open CJ0 (Jet blockRows blockCols blockMatrix)
open scoped BigOperators
def source : CJ0.Source := ⟨62,84,26,11,CJ0.fullBox 84 26 11⟩
def rowLo (q u h : ℕ) := u + 2*q + h + 1 - 88
def rowHi (q u h : ℕ) := min (q + 1 - h) (u + 2*q + h + 1 - 26)
def rowLen (q u h : ℕ) := rowHi q u h - rowLo q u h
def colLo (u b : ℕ) := (27 - (u+b)) / 2
def colHi (q b : ℕ) := min 12 (min (q-b+1) ((26-b)/2+1))
def colLen (q u b : ℕ) := colHi q b - colLo u b
abbrev Row (q u : ℕ) := (h : Fin (q+1)) × Fin (rowLen q u h)
abbrev Col (q u : ℕ) := (b : Fin (min q 26 + 1)) × Fin (colLen q u b)
def rowAt (q u h i : ℕ) : CJ0.Jet :=
  let d := rowLo q u h + i
  ⟨q - (h+d), d, h⟩
def rowJet (q u : ℕ) (r : Row q u) : CJ0.Jet := rowAt q u r.1 r.2
def colAt (q u b i : ℕ) : CJ0.Jet :=
  let c := colLo u b + i
  ⟨c, b, q - (b+c)⟩
def colJet (q u : ℕ) (s : Col q u) : CJ0.Jet := colAt q u s.1 s.2
def packet (q u : ℕ) : Matrix (Row q u) (Col q u) (ZMod CJ0.p) :=
  fun r s => CJ0.blockEntry (rowJet q u r) (colJet q u s)
def rows (q u : ℕ) := total (rowLen q u) (q+1)
def cols (q u : ℕ) := total (colLen q u) (min q 26 + 1)
def nominal (q u : ℕ) := min (rows q u) (cols q u)
def outer (onRows : Bool) (q : ℕ) := if onRows then q+1 else min q 26+1
def fiber (onRows : Bool) (q u : ℕ) := if onRows then rowLen q u else colLen q u
abbrev Axis (onRows : Bool) (q u : ℕ) :=
  (i : Fin (outer onRows q)) × Fin (fiber onRows q u i)
def orientedEntry (onRows : Bool) (q u i k b t : ℕ) : ℤ :=
  if onRows then entryZ (rowAt q u b t) (colAt q u i k)
  else entryZ (rowAt q u i k) (colAt q u b t)
def dot (q u : ℕ) (z : Block) (j i k : ℕ) : ℤ :=
  total (fun b => total (fun t =>
    let w := z.coeff j b t
    if w = 0 then 0 else orientedEntry z.bank.onRows q u i k b t * (w : ℤ))
    (fiber z.bank.onRows q u b)) (outer z.bank.onRows q)
def Dots (q u : ℕ) (z : Block) : Prop :=
  ∀ j < z.free.length, ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
def VectorDots (q u : ℕ) (z : Block) (j : ℕ) : Prop :=
  ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
private theorem row_bounds (q u c d h : ℕ)
    (hr : (⟨c,d,h⟩ : Jet) ∈ blockRows 62 q ((u : ℤ)-26)) :
    h < q+1 ∧ rowLo q u h ≤ d ∧ d < rowHi q u h ∧ q-(h+d) = c := by
  simp only [blockRows, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_singleton, Jet.v, Jet.b, Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hr
  unfold rowLo rowHi
  omega
private theorem col_bounds (q u c b a : ℕ)
    (hs : (⟨c,b,a⟩ : Jet) ∈ blockCols source q ((u : ℤ)-26)) :
    b < min q 26 + 1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change (⟨c,b,a⟩ : Jet) ∈ (CJ0.fullBox 84 26 11).filter _ at hs
  rw [Finset.mem_filter, CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega
private def rowIndex (q u : ℕ) :
    ↥(blockRows 62 q ((u : ℤ)-26)) → Row q u
  | ⟨⟨c,d,h⟩, hr⟩ =>
    let H := row_bounds q u c d h hr
    ⟨⟨h,H.1⟩, ⟨d-rowLo q u h, by
      change d - rowLo q u h < rowHi q u h - rowLo q u h
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private def colIndex (q u : ℕ) :
    ↥(blockCols source q ((u : ℤ)-26)) → Col q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H := col_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < colHi q b - colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private theorem rowJet_index (q u : ℕ) (r : ↥(blockRows 62 q ((u : ℤ)-26))) :
    rowJet q u (rowIndex q u r) = r.val := by
  rcases r with ⟨⟨c,d,h⟩,hr⟩
  obtain ⟨_, hlo, _, hc⟩ := row_bounds q u c d h hr
  change (⟨q-(h+(rowLo q u h+(d-rowLo q u h))),rowLo q u h+(d-rowLo q u h),h⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, hc]
private theorem colJet_index (q u : ℕ) (s : ↥(blockCols source q ((u : ℤ)-26))) :
    colJet q u (colIndex q u s) = s.val := by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_, hlo, _, ha⟩ := col_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, ha]
theorem block_rank_le (q u : ℕ) :
    (blockMatrix source q ((u : ℤ)-26)).rank ≤ (packet q u).rank := by
  have he : blockMatrix source q ((u : ℤ)-26) =
      (packet q u).submatrix (rowIndex q u) (colIndex q u) := by
    ext r s
    change CJ0.blockEntry r.val s.val =
      CJ0.blockEntry (rowJet q u (rowIndex q u r)) (colJet q u (colIndex q u s))
    exact congrArg₂ CJ0.blockEntry (rowJet_index q u r).symm (colJet_index q u s).symm
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _
theorem card_row (q u : ℕ) : Fintype.card (Row q u) = rows q u := by
  simp only [Row, Fintype.card_sigma, Fintype.card_fin, rows, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem card_col (q u : ℕ) : Fintype.card (Col q u) = cols q u := by
  simp only [Col, Fintype.card_sigma, Fintype.card_fin, cols, total_eq_sum,
    Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
theorem rank_le_nominal (q u : ℕ) : (packet q u).rank ≤ nominal q u := by
  exact le_min ((packet q u).rank_le_card_height.trans_eq (card_row q u))
    ((packet q u).rank_le_card_width.trans_eq (card_col q u))
open CJ1 (fastChoose right_witness)
open scoped BigOperators
local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩
def Guard (q u : ℕ) (z : Block) : Prop :=
  total (fiber z.bank.onRows q u) (outer z.bank.onRows q) ≤ z.cap + z.free.length ∧
  (∀ j : Fin z.free.length,
    z.free[j].1 < outer z.bank.onRows q ∧
    z.free[j].2 < fiber z.bank.onRows q u z.free[j].1) ∧
  ∀ j k : Fin z.free.length, z.coeff k z.free[j].1 z.free[j].2 = if j = k then 1 else 0
instance (q u : ℕ) (z : Block) : Decidable (Guard q u z) := by
  unfold Guard
  infer_instance
private theorem entryZ_cast (r c : CJ0.Jet) : (entryZ r c : ZMod CJ0.p) = CJ0.blockEntry r c := by
  unfold entryZ CJ0.blockEntry
  split <;> simp [fastChoose, ← Nat.choose_eq_descFactorial_div_factorial, *]
private def oriented (side : Bool) (q u : ℕ) :
    Matrix (Axis (!side) q u) (Axis side q u) (ZMod CJ0.p) :=
  fun r c => (orientedEntry side q u r.1 r.2 c.1 c.2 : ZMod CJ0.p)
private theorem oriented_rank (side : Bool) (q u : ℕ) :
    (oriented side q u).rank = (packet q u).rank := by
  cases side
  · have he : oriented false q u = packet q u := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    rfl
  · have he : oriented true q u = (packet q u).transpose := by
      ext r c
      exact entryZ_cast _ _
    rw [he]
    exact Matrix.rank_transpose _
private def vectors (q u : ℕ) (z : Block) :
    Matrix (Axis z.bank.onRows q u) (Fin z.free.length) (ZMod CJ0.p) :=
  fun c j => (z.coeff j c.1 c.2 : ZMod CJ0.p)
private theorem sum_axis {α : Type*} [AddCommMonoid α] (side : Bool) (q u : ℕ) (f : ℕ → ℕ → α) :
    (∑ x : Axis side q u, f x.1 x.2) =
      total (fun i => total (f i) (fiber side q u i)) (outer side q) := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma, total_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [total_eq_sum, ← Fin.sum_univ_eq_sum_range]
private theorem mul_eq_dot (q u : ℕ) (z : Block) (r : Axis (!z.bank.onRows) q u)
    (j : Fin z.free.length) :
    (oriented z.bank.onRows q u * vectors q u z) r j = (dot q u z j r.1 r.2 : ZMod CJ0.p) := by
  rw [Matrix.mul_apply, dot, ← sum_axis, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  change (orientedEntry z.bank.onRows q u r.1 r.2 c.1 c.2 : ZMod CJ0.p) * (z.coeff j c.1 c.2 : ZMod CJ0.p) = _
  by_cases hh : z.coeff j c.1 c.2 = 0 <;> simp [hh]
theorem rank_of_dots {q u : ℕ} {z : Block} (hg : Guard q u z) (hd : Dots q u z) :
    (packet q u).rank ≤ z.cap := by
  obtain ⟨hsize, hfree, hid⟩ := hg
  let f (j : Fin z.free.length) : Axis z.bank.onRows q u :=
    ⟨⟨z.free[j].1,(hfree j).1⟩, ⟨z.free[j].2,(hfree j).2⟩⟩
  have hm : oriented z.bank.onRows q u * vectors q u z = 0 := by
    ext r j
    rw [mul_eq_dot, Matrix.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero (hd j j.isLt r.1 r.1.isLt r.2 r.2.isLt)
  have hi : (vectors q u z).submatrix f id = 1 := by
    ext j k
    change (z.coeff k z.free[j].1 z.free[j].2 : ZMod CJ0.p) = _
    rw [hid]
    by_cases h : j = k <;> simp [Matrix.one_apply, h]
  have hr := right_witness (oriented z.bank.onRows q u) (vectors q u z) f hm hi
  have hc (side : Bool) :
      Fintype.card (Axis side q u) = total (fiber side q u) (outer side q) := by
    cases side
    · exact card_col q u
    · exact card_row q u
  rw [hc, oriented_rank] at hr
  exact Nat.le_of_add_le_add_right (hr.trans hsize)

namespace Fast
open CJ1 (Block total)
open CJ6.Packed
def point (row : Bool) (q u i k : ℕ) : CJ0.Jet := if row then rowAt q u i k else colAt q u i k
def inputs (q u : ℕ) (z : Block) (j : ℕ) : List Input :=
  axisList (outer z.bank.onRows q) (fiber z.bank.onRows q u)
    (fun i k => (point z.bank.onRows q u i k, z.coeff j i k))
def outputs (q u : ℕ) (z : Block) : List CJ0.Jet :=
  axisList (outer (!z.bank.onRows) q) (fiber (!z.bank.onRows) q u) (point (!z.bank.onRows) q u)
private theorem dot_eq (q u : ℕ) (z : Block) (j i k : ℕ) :
    dot q u z j i k = ((inputs q u z j).map (intTerm z.bank.onRows (point (!z.bank.onRows) q u i k))).sum := by
  rw [inputs, CJ6.Packed.sum_axis, dot]
  congr 1
  funext b
  congr 1
  funext t
  by_cases h : z.coeff j b t = 0
  · simp [h, intTerm]
  · cases hs : z.bank.onRows <;> simp [h, intTerm, point, orientedEntry]
theorem vector {q u : ℕ} {z : Block} {j : ℕ} (bands : List Band) (bs : List Bucket)
    (hi : (inputs q u z j).all (fun v => v.1.q == q) = true)
    (hc : (outputs q u z).all (covers z.bank.onRows q bands) = true)
    (hp : pack z.bank.onRows q (inputs q u z j) = bs)
    (hb : bands.all (checkBand z.bank.onRows bs) = true) : VectorDots q u z j := by
  intro i hᵢ k hₖ
  rw [dot_eq]
  subst bs
  apply int_sum_zero hi _ hb
  apply List.all_eq_true.mp hc
  exact mem_axis hᵢ hₖ

def vectorOK (q u : ℕ) (z : Block) (j : ℕ) (bands : List Band) : Bool :=
  let side := z.bank.onRows
  let xs := inputs q u z j
  xs.all (fun v => v.1.q == q) && (outputs q u z).all (covers side q bands) &&
    bands.all (checkBand side (pack side q xs))

theorem cell {q u : ℕ} {z : Block} (bands : List Band) (guard : Guard q u z)
    (cert : (List.range z.free.length).all (fun j => vectorOK q u z j bands) = true) :
    (CJ0.blockMatrix source q ((u : ℤ)-26)).rank ≤ z.cap := by
  apply (block_rank_le _ _).trans
  apply rank_of_dots guard
  intro j hj
  have h := List.all_eq_true.mp cert j (List.mem_range.mpr hj)
  simp only [vectorOK, Bool.and_eq_true] at h
  exact vector bands _ h.1.1 h.1.2 rfl h.2

def bands (xs : List (ℕ × ℕ × ℕ)) : List Band :=
  xs.map fun (a,lo,n) => (a, List.range' lo n)

end Fast

open CJ0 (ShapeOK mem_fullBox fullBox Surplus SilentTail RankCertificate)
open Finset

theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 84) (J := 26) (C := 11) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 84
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 84 - (b+c) + 1
private def bRange (c : ℕ) := range (26 - 2*c + 1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (runLength c b * (runLength c b - 1) / 2 + runLength c b * (b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b * (b+2*c)
private theorem box_count : source.E.card = ∑ c ∈ range 12, countRow c := by
  simp only [source, fullBox, card_sigma, card_range, countRow, bRange, runLength]
private theorem box_total : (∑ j ∈ source.E, j.q) = ∑ c ∈ range 12, totalRow c := by
  simp only [source, fullBox, sum_sigma, totalRow, bRange, runLength, Jet.q, Jet.a, Jet.b, Jet.c]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range, smul_eq_mul, Nat.mul_add]
private theorem box_index : (∑ j ∈ source.E, j.v) = ∑ c ∈ range 12, indexRow c := by
  simp only [source, fullBox, sum_sigma, indexRow, bRange, runLength, Jet.v, Jet.b, Jet.c,
    sum_const, card_range, smul_eq_mul]
private theorem row0 : countRow 0 = 1944 ∧ totalRow 0 = 93465 ∧ indexRow 0 = 23634 := by decide +kernel
private theorem row1 : countRow 1 = 1800 ∧ totalRow 1 = 86650 ∧ indexRow 1 = 23900 := by decide +kernel
private theorem row2 : countRow 2 = 1656 ∧ totalRow 2 = 79810 ∧ indexRow 2 = 23828 := by decide +kernel
private theorem row3 : countRow 3 = 1512 ∧ totalRow 3 = 72947 ∧ indexRow 3 = 23422 := by decide +kernel
private theorem row4 : countRow 4 = 1368 ∧ totalRow 4 = 66063 ∧ indexRow 4 = 22686 := by decide +kernel
private theorem row5 : countRow 5 = 1224 ∧ totalRow 5 = 59160 ∧ indexRow 5 = 21624 := by decide +kernel
private theorem row6 : countRow 6 = 1080 ∧ totalRow 6 = 52240 ∧ indexRow 6 = 20240 := by decide +kernel
private theorem row7 : countRow 7 = 936 ∧ totalRow 7 = 45305 ∧ indexRow 7 = 18538 := by decide +kernel
private theorem row8 : countRow 8 = 792 ∧ totalRow 8 = 38357 ∧ indexRow 8 = 16522 := by decide +kernel
private theorem row9 : countRow 9 = 648 ∧ totalRow 9 = 31398 ∧ indexRow 9 = 14196 := by decide +kernel
private theorem row10 : countRow 10 = 504 ∧ totalRow 10 = 24430 ∧ indexRow 10 = 11564 := by decide +kernel
private theorem row11 : countRow 11 = 360 ∧ totalRow 11 = 17455 ∧ indexRow 11 = 8630 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 12, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 13824 ∧ (∑ j ∈ source.E, j.q) = 667280 ∧ (∑ j ∈ source.E, j.v) = 228784 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1, row11.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1, row11.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2, row11.2.2]

def cutRowLen (q u t h : ℕ) :=
  min (rowLen q u h) (q+1-(h+t+rowLo q u h))

def cutColLen (q u t b : ℕ) :=
  min (colLen q u b) (t - colLo u b)

def cutRows (q u t : ℕ) := total (cutRowLen q u t) (q+1)
def cutCols (q u t : ℕ) := total (cutColLen q u t) (min q 26+1)

private theorem card_sigma_fin {n : ℕ} (f : ℕ → ℕ) :
    Fintype.card ((i : Fin n) × Fin (f i)) = total f n := by
  simp only [Fintype.card_sigma, Fintype.card_fin, total_eq_sum, Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]

private theorem card_cut_rows (q u t : ℕ) :
    Fintype.card {r : Row q u // t ≤ (rowJet q u r).c} ≤ cutRows q u t := by
  rw [cutRows, ← card_sigma_fin]
  let f (r : {r : Row q u // t ≤ (rowJet q u r).c}) : (i : Fin (q+1)) × Fin (cutRowLen q u t i) :=
    ⟨r.val.fst, ⟨r.val.snd, by
      apply lt_min r.val.snd.isLt
      have h := r.property
      change t ≤ q - (r.val.fst.val + (rowLo q u r.val.fst + r.val.snd.val)) at h
      have hi := r.val.snd.isLt
      have hd := r.val.fst.isLt
      unfold rowLen rowHi at hi
      omega⟩⟩
  apply Fintype.card_le_of_injective f
  intro ⟨⟨i,k⟩, hi⟩ ⟨⟨j,l⟩, hj⟩ h
  have h₁ : i = j := congrArg Sigma.fst h
  subst j
  have h₂ := (Sigma.mk.inj_iff.mp h).2
  have h₃ : k.val = l.val := congrArg (fun z : Fin (cutRowLen q u t i) => z.val) (eq_of_heq h₂)
  have h₄ : k = l := Fin.ext h₃
  subst l
  rfl

private theorem card_cut_cols (q u t : ℕ) :
    Fintype.card {s : Col q u // (colJet q u s).c < t} ≤ cutCols q u t := by
  rw [cutCols, ← card_sigma_fin]
  let f (s : {s : Col q u // (colJet q u s).c < t}) :
      (i : Fin (min q 26+1)) × Fin (cutColLen q u t i) :=
    ⟨s.val.fst, ⟨s.val.snd, by
      apply lt_min s.val.snd.isLt
      have hs := s.property
      change colLo u s.val.fst + s.val.snd.val < t at hs
      omega⟩⟩
  apply Fintype.card_le_of_injective f
  intro ⟨⟨i,k⟩, hi⟩ ⟨⟨j,l⟩, hj⟩ h
  have h₁ : i = j := congrArg Sigma.fst h
  subst j
  have h₂ := (Sigma.mk.inj_iff.mp h).2
  have h₃ : k.val = l.val := congrArg (fun z : Fin (cutColLen q u t i) => z.val) (eq_of_heq h₂)
  have h₄ : k = l := Fin.ext h₃
  subst l
  rfl

theorem rank_le_cut (q u t : ℕ) : (packet q u).rank ≤ cutRows q u t + cutCols q u t := by
  apply (Beyond70Hall.rank_cut (packet q u) (fun r => t ≤ (rowJet q u r).c)
    (fun s => (colJet q u s).c < t) ?_).trans
    (Nat.add_le_add (card_cut_rows q u t) (card_cut_cols q u t))
  intro i j hi hj
  have h : ¬ (colJet q u j).c ≤ (rowJet q u i).c := by
    omega
  simp [packet, CJ0.blockEntry, h]


end R6970Scalar84Rank
