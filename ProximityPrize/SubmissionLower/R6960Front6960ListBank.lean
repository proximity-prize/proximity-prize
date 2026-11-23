import ProximityPrize.SubmissionLower.Numeric6Defs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Front6960ListBank
open CJ1 (Block total total_eq_sum entryZ)
open CJ0 (Jet blockRows blockCols blockMatrix)
open scoped BigOperators
def source : CJ0.Source := ⟨58,79,23,10,CJ0.fullBox 79 23 10⟩
def rowLo (q u h : ℕ) := u + 2*q + h + 1 - 81
def rowHi (q u h : ℕ) := min (q + 1 - h) (u + 2*q + h + 1 - 23)
def rowLen (q u h : ℕ) := rowHi q u h - rowLo q u h
def colLo (u b : ℕ) := (24 - (u+b)) / 2
def colHi (q b : ℕ) := min 11 (min (q-b+1) ((23-b)/2+1))
def colLen (q u b : ℕ) := colHi q b - colLo u b
abbrev Row (q u : ℕ) := (h : Fin (q+1)) × Fin (rowLen q u h)
abbrev Col (q u : ℕ) := (b : Fin (min q 23 + 1)) × Fin (colLen q u b)
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
def cols (q u : ℕ) := total (colLen q u) (min q 23 + 1)
def nominal (q u : ℕ) := min (rows q u) (cols q u)
def outer (onRows : Bool) (q : ℕ) := if onRows then q+1 else min q 23+1
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
    (hr : (⟨c,d,h⟩ : Jet) ∈ blockRows 58 q ((u : ℤ)-23)) :
    h < q+1 ∧ rowLo q u h ≤ d ∧ d < rowHi q u h ∧ q-(h+d) = c := by
  simp only [blockRows, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_singleton, Jet.v, Jet.b, Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hr
  unfold rowLo rowHi
  omega
private theorem col_bounds (q u c b a : ℕ)
    (hs : (⟨c,b,a⟩ : Jet) ∈ blockCols source q ((u : ℤ)-23)) :
    b < min q 23 + 1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change (⟨c,b,a⟩ : Jet) ∈ (CJ0.fullBox 79 23 10).filter _ at hs
  rw [Finset.mem_filter, CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega
private def rowIndex (q u : ℕ) :
    ↥(blockRows 58 q ((u : ℤ)-23)) → Row q u
  | ⟨⟨c,d,h⟩, hr⟩ =>
    let H := row_bounds q u c d h hr
    ⟨⟨h,H.1⟩, ⟨d-rowLo q u h, by
      change d - rowLo q u h < rowHi q u h - rowLo q u h
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private def colIndex (q u : ℕ) :
    ↥(blockCols source q ((u : ℤ)-23)) → Col q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H := col_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < colHi q b - colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private theorem rowJet_index (q u : ℕ) (r : ↥(blockRows 58 q ((u : ℤ)-23))) :
    rowJet q u (rowIndex q u r) = r.val := by
  rcases r with ⟨⟨c,d,h⟩,hr⟩
  obtain ⟨_, hlo, _, hc⟩ := row_bounds q u c d h hr
  change (⟨q-(h+(rowLo q u h+(d-rowLo q u h))),rowLo q u h+(d-rowLo q u h),h⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, hc]
private theorem colJet_index (q u : ℕ) (s : ↥(blockCols source q ((u : ℤ)-23))) :
    colJet q u (colIndex q u s) = s.val := by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_, hlo, _, ha⟩ := col_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, ha]
theorem block_rank_le (q u : ℕ) :
    (blockMatrix source q ((u : ℤ)-23)).rank ≤ (packet q u).rank := by
  have he : blockMatrix source q ((u : ℤ)-23) =
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
    (CJ0.blockMatrix source q ((u : ℤ)-23)).rank ≤ z.cap := by
  apply (block_rank_le _ _).trans
  apply rank_of_dots guard
  intro j hj
  have h := List.all_eq_true.mp cert j (List.mem_range.mpr hj)
  simp only [vectorOK, Bool.and_eq_true] at h
  exact vector bands _ h.1.1 h.1.2 rfl h.2

def bands (xs : List (ℕ × ℕ × ℕ)) : List Band :=
  xs.map fun (a,lo,n) => (a, List.range' lo n)

end Fast
end Front6960ListBank
