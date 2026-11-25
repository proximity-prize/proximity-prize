import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof

set_option Elab.async false

-- merged module Front6963ListBank
section Merged_Front6963ListBank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Front6963ListBank
open CJ1 (Block total total_eq_sum entryZ)
open CJ0 (Jet blockRows blockCols blockMatrix)
open scoped BigOperators
def source : CJ0.Source := ⟨59,80,24,10,CJ0.fullBox 80 24 10⟩
def rowLo (q u h : ℕ) := u + 2*q + h + 1 - 83
def rowHi (q u h : ℕ) := min (q + 1 - h) (u + 2*q + h + 1 - 24)
def rowLen (q u h : ℕ) := rowHi q u h - rowLo q u h
def colLo (u b : ℕ) := (25 - (u+b)) / 2
def colHi (q b : ℕ) := min 11 (min (q-b+1) ((24-b)/2+1))
def colLen (q u b : ℕ) := colHi q b - colLo u b
abbrev Row (q u : ℕ) := (h : Fin (q+1)) × Fin (rowLen q u h)
abbrev Col (q u : ℕ) := (b : Fin (min q 24 + 1)) × Fin (colLen q u b)
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
def cols (q u : ℕ) := total (colLen q u) (min q 24 + 1)
def nominal (q u : ℕ) := min (rows q u) (cols q u)
def outer (onRows : Bool) (q : ℕ) := if onRows then q+1 else min q 24+1
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
    (hr : (⟨c,d,h⟩ : Jet) ∈ blockRows 59 q ((u : ℤ)-24)) :
    h < q+1 ∧ rowLo q u h ≤ d ∧ d < rowHi q u h ∧ q-(h+d) = c := by
  simp only [blockRows, Finset.mem_filter, Finset.mem_sigma, Finset.mem_range,
    Finset.mem_singleton, Jet.v, Jet.b, Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hr
  unfold rowLo rowHi
  omega
private theorem col_bounds (q u c b a : ℕ)
    (hs : (⟨c,b,a⟩ : Jet) ∈ blockCols source q ((u : ℤ)-24)) :
    b < min q 24 + 1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change (⟨c,b,a⟩ : Jet) ∈ (CJ0.fullBox 80 24 10).filter _ at hs
  rw [Finset.mem_filter, CJ0.mem_fullBox (by decide) (by decide)] at hs
  simp only [Jet.q, Jet.v, Jet.a, Jet.b, Jet.c, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] at hs
  unfold colLo colHi
  omega
private def rowIndex (q u : ℕ) :
    ↥(blockRows 59 q ((u : ℤ)-24)) → Row q u
  | ⟨⟨c,d,h⟩, hr⟩ =>
    let H := row_bounds q u c d h hr
    ⟨⟨h,H.1⟩, ⟨d-rowLo q u h, by
      change d - rowLo q u h < rowHi q u h - rowLo q u h
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private def colIndex (q u : ℕ) :
    ↥(blockCols source q ((u : ℤ)-24)) → Col q u
  | ⟨⟨c,b,a⟩, hs⟩ =>
    let H := col_bounds q u c b a hs
    ⟨⟨b,H.1⟩, ⟨c-colLo u b, by
      change c - colLo u b < colHi q b - colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩
private theorem rowJet_index (q u : ℕ) (r : ↥(blockRows 59 q ((u : ℤ)-24))) :
    rowJet q u (rowIndex q u r) = r.val := by
  rcases r with ⟨⟨c,d,h⟩,hr⟩
  obtain ⟨_, hlo, _, hc⟩ := row_bounds q u c d h hr
  change (⟨q-(h+(rowLo q u h+(d-rowLo q u h))),rowLo q u h+(d-rowLo q u h),h⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, hc]
private theorem colJet_index (q u : ℕ) (s : ↥(blockCols source q ((u : ℤ)-24))) :
    colJet q u (colIndex q u s) = s.val := by
  rcases s with ⟨⟨c,b,a⟩,hs⟩
  obtain ⟨_, hlo, _, ha⟩ := col_bounds q u c b a hs
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo, ha]
theorem block_rank_le (q u : ℕ) :
    (blockMatrix source q ((u : ℤ)-24)).rank ≤ (packet q u).rank := by
  have he : blockMatrix source q ((u : ℤ)-24) =
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
    (CJ0.blockMatrix source q ((u : ℤ)-24)).rank ≤ z.cap := by
  apply (block_rank_le _ _).trans
  apply rank_of_dots guard
  intro j hj
  have h := List.all_eq_true.mp cert j (List.mem_range.mpr hj)
  simp only [vectorOK, Bool.and_eq_true] at h
  exact vector bands _ h.1.1 h.1.2 rfl h.2

def bands (xs : List (ℕ × ℕ × ℕ)) : List Band :=
  xs.map fun (a,lo,n) => (a, List.range' lo n)

end Fast
end Front6963ListBank

end Merged_Front6963ListBank

-- merged module Front6963ListCells0
section Merged_Front6963ListCells0

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6963ListBank
open scoped BigOperators

private def allowance_0 (u : ℕ) : ℕ :=
  nominal 0 u

private theorem bound_0 (u : ℕ) :
    (CJ0.blockMatrix source 0 ((u : ℤ)-24)).rank ≤ allowance_0 u := by
  unfold allowance_0
  exact (block_rank_le 0 _).trans (rank_le_nominal 0 _)

theorem grade_0 : (∑ u ∈ Finset.range (83-0), (CJ0.blockMatrix source 0 ((u : ℤ)-24)).rank) ≤ 59 := by
  refine (Finset.sum_le_sum fun u _ => bound_0 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_0)]
  decide +kernel

private def allowance_1 (u : ℕ) : ℕ :=
  nominal 1 u

private theorem bound_1 (u : ℕ) :
    (CJ0.blockMatrix source 1 ((u : ℤ)-24)).rank ≤ allowance_1 u := by
  unfold allowance_1
  exact (block_rank_le 1 _).trans (rank_le_nominal 1 _)

theorem grade_1 : (∑ u ∈ Finset.range (83-1), (CJ0.blockMatrix source 1 ((u : ℤ)-24)).rank) ≤ 174 := by
  refine (Finset.sum_le_sum fun u _ => bound_1 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_1)]
  decide +kernel

private def allowance_2 (u : ℕ) : ℕ :=
  nominal 2 u

private theorem bound_2 (u : ℕ) :
    (CJ0.blockMatrix source 2 ((u : ℤ)-24)).rank ≤ allowance_2 u := by
  unfold allowance_2
  exact (block_rank_le 2 _).trans (rank_le_nominal 2 _)

theorem grade_2 : (∑ u ∈ Finset.range (83-2), (CJ0.blockMatrix source 2 ((u : ℤ)-24)).rank) ≤ 342 := by
  refine (Finset.sum_le_sum fun u _ => bound_2 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_2)]
  decide +kernel

private def allowance_3 (u : ℕ) : ℕ :=
  nominal 3 u

private theorem bound_3 (u : ℕ) :
    (CJ0.blockMatrix source 3 ((u : ℤ)-24)).rank ≤ allowance_3 u := by
  unfold allowance_3
  exact (block_rank_le 3 _).trans (rank_le_nominal 3 _)

theorem grade_3 : (∑ u ∈ Finset.range (83-3), (CJ0.blockMatrix source 3 ((u : ℤ)-24)).rank) ≤ 560 := by
  refine (Finset.sum_le_sum fun u _ => bound_3 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_3)]
  decide +kernel

private def allowance_4 (u : ℕ) : ℕ :=
  nominal 4 u

private theorem bound_4 (u : ℕ) :
    (CJ0.blockMatrix source 4 ((u : ℤ)-24)).rank ≤ allowance_4 u := by
  unfold allowance_4
  exact (block_rank_le 4 _).trans (rank_le_nominal 4 _)

theorem grade_4 : (∑ u ∈ Finset.range (83-4), (CJ0.blockMatrix source 4 ((u : ℤ)-24)).rank) ≤ 825 := by
  refine (Finset.sum_le_sum fun u _ => bound_4 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_4)]
  decide +kernel

private def allowance_5 (u : ℕ) : ℕ :=
  nominal 5 u

private theorem bound_5 (u : ℕ) :
    (CJ0.blockMatrix source 5 ((u : ℤ)-24)).rank ≤ allowance_5 u := by
  unfold allowance_5
  exact (block_rank_le 5 _).trans (rank_le_nominal 5 _)

theorem grade_5 : (∑ u ∈ Finset.range (83-5), (CJ0.blockMatrix source 5 ((u : ℤ)-24)).rank) ≤ 1134 := by
  refine (Finset.sum_le_sum fun u _ => bound_5 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_5)]
  decide +kernel

private def allowance_6 (u : ℕ) : ℕ :=
  nominal 6 u

private theorem bound_6 (u : ℕ) :
    (CJ0.blockMatrix source 6 ((u : ℤ)-24)).rank ≤ allowance_6 u := by
  unfold allowance_6
  exact (block_rank_le 6 _).trans (rank_le_nominal 6 _)

theorem grade_6 : (∑ u ∈ Finset.range (83-6), (CJ0.blockMatrix source 6 ((u : ℤ)-24)).rank) ≤ 1484 := by
  refine (Finset.sum_le_sum fun u _ => bound_6 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_6)]
  decide +kernel

private def allowance_7 (u : ℕ) : ℕ :=
  nominal 7 u

private theorem bound_7 (u : ℕ) :
    (CJ0.blockMatrix source 7 ((u : ℤ)-24)).rank ≤ allowance_7 u := by
  unfold allowance_7
  exact (block_rank_le 7 _).trans (rank_le_nominal 7 _)

theorem grade_7 : (∑ u ∈ Finset.range (83-7), (CJ0.blockMatrix source 7 ((u : ℤ)-24)).rank) ≤ 1872 := by
  refine (Finset.sum_le_sum fun u _ => bound_7 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_7)]
  decide +kernel

private def allowance_8 (u : ℕ) : ℕ :=
  nominal 8 u

private theorem bound_8 (u : ℕ) :
    (CJ0.blockMatrix source 8 ((u : ℤ)-24)).rank ≤ allowance_8 u := by
  unfold allowance_8
  exact (block_rank_le 8 _).trans (rank_le_nominal 8 _)

theorem grade_8 : (∑ u ∈ Finset.range (83-8), (CJ0.blockMatrix source 8 ((u : ℤ)-24)).rank) ≤ 2295 := by
  refine (Finset.sum_le_sum fun u _ => bound_8 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_8)]
  decide +kernel

private def allowance_9 (u : ℕ) : ℕ :=
  nominal 9 u

private theorem bound_9 (u : ℕ) :
    (CJ0.blockMatrix source 9 ((u : ℤ)-24)).rank ≤ allowance_9 u := by
  unfold allowance_9
  exact (block_rank_le 9 _).trans (rank_le_nominal 9 _)

theorem grade_9 : (∑ u ∈ Finset.range (83-9), (CJ0.blockMatrix source 9 ((u : ℤ)-24)).rank) ≤ 2750 := by
  refine (Finset.sum_le_sum fun u _ => bound_9 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_9)]
  decide +kernel

private def allowance_10 (u : ℕ) : ℕ :=
  nominal 10 u

private theorem bound_10 (u : ℕ) :
    (CJ0.blockMatrix source 10 ((u : ℤ)-24)).rank ≤ allowance_10 u := by
  unfold allowance_10
  exact (block_rank_le 10 _).trans (rank_le_nominal 10 _)

theorem grade_10 : (∑ u ∈ Finset.range (83-10), (CJ0.blockMatrix source 10 ((u : ℤ)-24)).rank) ≤ 3234 := by
  refine (Finset.sum_le_sum fun u _ => bound_10 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_10)]
  decide +kernel

private def allowance_11 (u : ℕ) : ℕ :=
  nominal 11 u

private theorem bound_11 (u : ℕ) :
    (CJ0.blockMatrix source 11 ((u : ℤ)-24)).rank ≤ allowance_11 u := by
  unfold allowance_11
  exact (block_rank_le 11 _).trans (rank_le_nominal 11 _)

theorem grade_11 : (∑ u ∈ Finset.range (83-11), (CJ0.blockMatrix source 11 ((u : ℤ)-24)).rank) ≤ 3696 := by
  refine (Finset.sum_le_sum fun u _ => bound_11 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_11)]
  decide +kernel

private def allowance_12 (u : ℕ) : ℕ :=
  nominal 12 u

private theorem bound_12 (u : ℕ) :
    (CJ0.blockMatrix source 12 ((u : ℤ)-24)).rank ≤ allowance_12 u := by
  unfold allowance_12
  exact (block_rank_le 12 _).trans (rank_le_nominal 12 _)

theorem grade_12 : (∑ u ∈ Finset.range (83-12), (CJ0.blockMatrix source 12 ((u : ℤ)-24)).rank) ≤ 4136 := by
  refine (Finset.sum_le_sum fun u _ => bound_12 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_12)]
  decide +kernel

private def matrix_13_47 : CJ1.Block where
  bank := .leftLow
  cap := 98
  free := [(11, 0)]
  vectors := [
    [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_13_47 : (CJ0.blockMatrix source 13 ((47 : ℤ)-24)).rank ≤ 98 :=
  Fast.cell (z := matrix_13_47) (Fast.bands [(0, 0, 11), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 10), (5, 5, 9), (6, 6, 8), (7, 7, 7), (8, 8, 6), (9, 9, 5), (10, 10, 4), (11, 11, 3), (12, 12, 2), (13, 13, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_13 (u : ℕ) : ℕ :=
  match u with
  | 47 => 98
  | u => nominal 13 u

private theorem bound_13 (u : ℕ) :
    (CJ0.blockMatrix source 13 ((u : ℤ)-24)).rank ≤ allowance_13 u := by
  unfold allowance_13
  split
  · exact cell_13_47
  · exact (block_rank_le 13 _).trans (rank_le_nominal 13 _)

theorem grade_13 : (∑ u ∈ Finset.range (83-13), (CJ0.blockMatrix source 13 ((u : ℤ)-24)).rank) ≤ 4554 := by
  refine (Finset.sum_le_sum fun u _ => bound_13 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_13)]
  decide +kernel

private def matrix_14_45 : CJ1.Block where
  bank := .rightLow
  cap := 109
  free := [(14, 0)]
  vectors := [
    [[1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1], [2130706419, 2130706303, 2130705893, 2130705113, 2130704333, 2130704165, 2130704753, 2130705593, 2130706163, 2130706383, 2130706429], [91, 780, 2970, 6600, 9450, 9072, 5880, 2520, 675, 100, 6], [2130706069, 2130703573, 2130696533, 2130686633, 2130681233, 2130685265, 2130694673, 2130702233, 2130705533, 2130706333, 2130706429], [1001, 7150, 22275, 39600, 44100, 31752, 14700, 4200, 675, 50, 1], [2130704431, 2130693563, 2130670793, 2130650993, 2130653513, 2130674681, 2130694673, 2130703913, 2130706163, 2130706423], [3003, 17160, 41580, 55440, 44100, 21168, 5880, 840, 45], [2130703001, 2130689273, 2130670793, 2130666833, 2130681233, 2130697361, 2130704753, 2130706313], [3003, 12870, 22275, 19800, 9450, 2268, 210], [2130704431, 2130699283, 2130696533, 2130699833, 2130704333, 2130706181], [1001, 2860, 2970, 1320, 210], [2130706069, 2130705653, 2130705893, 2130706313], [91, 130, 45], [2130706419, 2130706423], [1]]
  ]
private theorem cell_14_45 : (CJ0.blockMatrix source 14 ((45 : ℤ)-24)).rank ≤ 109 :=
  Fast.cell (z := matrix_14_45) (Fast.bands [(0, 0, 15), (1, 0, 14), (2, 0, 13), (3, 0, 12), (4, 0, 11), (5, 0, 10), (6, 0, 9), (7, 0, 8), (8, 0, 7), (9, 0, 6), (10, 1, 4), (11, 2, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_14_46 : CJ1.Block where
  bank := .leftLow
  cap := 107
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_14_46 : (CJ0.blockMatrix source 14 ((46 : ℤ)-24)).rank ≤ 107 :=
  Fast.cell (z := matrix_14_46) (Fast.bands [(0, 0, 11), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 10), (6, 6, 9), (7, 7, 8), (8, 8, 7), (9, 9, 6), (10, 10, 5), (11, 11, 4), (12, 12, 3), (13, 13, 2), (14, 14, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_14 (u : ℕ) : ℕ :=
  match u with
  | 45 => 109
  | 46 => 107
  | u => nominal 14 u

private theorem bound_14 (u : ℕ) :
    (CJ0.blockMatrix source 14 ((u : ℤ)-24)).rank ≤ allowance_14 u := by
  unfold allowance_14
  split
  · exact cell_14_45
  · exact cell_14_46
  · exact (block_rank_le 14 _).trans (rank_le_nominal 14 _)

theorem grade_14 : (∑ u ∈ Finset.range (83-14), (CJ0.blockMatrix source 14 ((u : ℤ)-24)).rank) ≤ 4950 := by
  refine (Finset.sum_le_sum fun u _ => bound_14 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_14)]
  decide +kernel

private def matrix_15_44 : CJ1.Block where
  bank := .leftLow
  cap := 118
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 12], [0, 0, 0, 11], [0, 0, 0, 10], [0, 0, 0, 9], [0, 0, 0, 8], [0, 0, 0, 7], [0, 0, 0, 6], [0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_15_44 : (CJ0.blockMatrix source 15 ((44 : ℤ)-24)).rank ≤ 118 :=
  Fast.cell (z := matrix_15_44) (Fast.bands [(0, 0, 10), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 10), (7, 7, 9), (8, 8, 8), (9, 9, 7), (10, 10, 6), (11, 11, 5), (12, 12, 4), (13, 13, 3), (14, 14, 2), (15, 15, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_15_45 : CJ1.Block where
  bank := .leftLow
  cap := 115
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_15_45 : (CJ0.blockMatrix source 15 ((45 : ℤ)-24)).rank ≤ 115 :=
  Fast.cell (z := matrix_15_45) (Fast.bands [(0, 0, 10), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 10), (7, 7, 9), (8, 8, 8), (9, 9, 7), (10, 10, 6), (11, 11, 5), (12, 12, 4), (13, 13, 3), (14, 14, 2), (15, 15, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_15 (u : ℕ) : ℕ :=
  match u with
  | 44 => 118
  | 45 => 115
  | u => nominal 15 u

private theorem bound_15 (u : ℕ) :
    (CJ0.blockMatrix source 15 ((u : ℤ)-24)).rank ≤ allowance_15 u := by
  unfold allowance_15
  split
  · exact cell_15_44
  · exact cell_15_45
  · exact (block_rank_le 15 _).trans (rank_le_nominal 15 _)

theorem grade_15 : (∑ u ∈ Finset.range (83-15), (CJ0.blockMatrix source 15 ((u : ℤ)-24)).rank) ≤ 5280 := by
  refine (Finset.sum_le_sum fun u _ => bound_15 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_15)]
  decide +kernel

private def matrix_16_43 : CJ1.Block where
  bank := .leftLow
  cap := 126
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 12], [0, 0, 0, 0, 11], [0, 0, 0, 0, 10], [0, 0, 0, 0, 9], [0, 0, 0, 0, 8], [0, 0, 0, 0, 7], [0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_16_43 : (CJ0.blockMatrix source 16 ((43 : ℤ)-24)).rank ≤ 126 :=
  Fast.cell (z := matrix_16_43) (Fast.bands [(0, 0, 9), (1, 1, 10), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 10), (8, 8, 9), (9, 9, 8), (10, 10, 7), (11, 11, 6), (12, 12, 5), (13, 13, 4), (14, 14, 3), (15, 15, 2), (16, 16, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_16_44 : CJ1.Block where
  bank := .leftLow
  cap := 122
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_16_44 : (CJ0.blockMatrix source 16 ((44 : ℤ)-24)).rank ≤ 122 :=
  Fast.cell (z := matrix_16_44) (Fast.bands [(0, 0, 9), (1, 1, 10), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 10), (8, 8, 9), (9, 9, 8), (10, 10, 7), (11, 11, 6), (12, 12, 5), (13, 13, 4), (14, 14, 3), (15, 15, 2), (16, 16, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_16 (u : ℕ) : ℕ :=
  match u with
  | 43 => 126
  | 44 => 122
  | u => nominal 16 u

private theorem bound_16 (u : ℕ) :
    (CJ0.blockMatrix source 16 ((u : ℤ)-24)).rank ≤ allowance_16 u := by
  unfold allowance_16
  split
  · exact cell_16_43
  · exact cell_16_44
  · exact (block_rank_le 16 _).trans (rank_le_nominal 16 _)

theorem grade_16 : (∑ u ∈ Finset.range (83-16), (CJ0.blockMatrix source 16 ((u : ℤ)-24)).rank) ≤ 5547 := by
  refine (Finset.sum_le_sum fun u _ => bound_16 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_16)]
  decide +kernel

private def matrix_17_42 : CJ1.Block where
  bank := .leftLow
  cap := 133
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_17_42 : (CJ0.blockMatrix source 17 ((42 : ℤ)-24)).rank ≤ 133 :=
  Fast.cell (z := matrix_17_42) (Fast.bands [(0, 0, 8), (1, 1, 9), (2, 2, 10), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 10), (9, 9, 9), (10, 10, 8), (11, 11, 7), (12, 12, 6), (13, 13, 5), (14, 14, 4), (15, 15, 3), (16, 16, 2), (17, 17, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_17_43 : CJ1.Block where
  bank := .leftLow
  cap := 128
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_17_43 : (CJ0.blockMatrix source 17 ((43 : ℤ)-24)).rank ≤ 128 :=
  Fast.cell (z := matrix_17_43) (Fast.bands [(0, 0, 8), (1, 1, 9), (2, 2, 10), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 10), (9, 9, 9), (10, 10, 8), (11, 11, 7), (12, 12, 6), (13, 13, 5), (14, 14, 4), (15, 15, 3), (16, 16, 2), (17, 17, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_17 (u : ℕ) : ℕ :=
  match u with
  | 42 => 133
  | 43 => 128
  | u => nominal 17 u

private theorem bound_17 (u : ℕ) :
    (CJ0.blockMatrix source 17 ((u : ℤ)-24)).rank ≤ allowance_17 u := by
  unfold allowance_17
  split
  · exact cell_17_42
  · exact cell_17_43
  · exact (block_rank_le 17 _).trans (rank_le_nominal 17 _)

theorem grade_17 : (∑ u ∈ Finset.range (83-17), (CJ0.blockMatrix source 17 ((u : ℤ)-24)).rank) ≤ 5754 := by
  refine (Finset.sum_le_sum fun u _ => bound_17 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_17)]
  decide +kernel

private def matrix_18_41 : CJ1.Block where
  bank := .leftLow
  cap := 139
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_18_41 : (CJ0.blockMatrix source 18 ((41 : ℤ)-24)).rank ≤ 139 :=
  Fast.cell (z := matrix_18_41) (Fast.bands [(0, 0, 7), (1, 1, 8), (2, 2, 9), (3, 3, 10), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 10), (10, 10, 9), (11, 11, 8), (12, 12, 7), (13, 13, 6), (14, 14, 5), (15, 15, 4), (16, 16, 3), (17, 17, 2), (18, 18, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_18_42 : CJ1.Block where
  bank := .leftLow
  cap := 133
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_18_42 : (CJ0.blockMatrix source 18 ((42 : ℤ)-24)).rank ≤ 133 :=
  Fast.cell (z := matrix_18_42) (Fast.bands [(0, 0, 7), (1, 1, 8), (2, 2, 9), (3, 3, 10), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 10), (10, 10, 9), (11, 11, 8), (12, 12, 7), (13, 13, 6), (14, 14, 5), (15, 15, 4), (16, 16, 3), (17, 17, 2), (18, 18, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_18 (u : ℕ) : ℕ :=
  match u with
  | 41 => 139
  | 42 => 133
  | u => nominal 18 u

private theorem bound_18 (u : ℕ) :
    (CJ0.blockMatrix source 18 ((u : ℤ)-24)).rank ≤ allowance_18 u := by
  unfold allowance_18
  split
  · exact cell_18_41
  · exact cell_18_42
  · exact (block_rank_le 18 _).trans (rank_le_nominal 18 _)

theorem grade_18 : (∑ u ∈ Finset.range (83-18), (CJ0.blockMatrix source 18 ((u : ℤ)-24)).rank) ≤ 5904 := by
  refine (Finset.sum_le_sum fun u _ => bound_18 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_18)]
  decide +kernel

private def matrix_19_40 : CJ1.Block where
  bank := .leftLow
  cap := 144
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_19_40 : (CJ0.blockMatrix source 19 ((40 : ℤ)-24)).rank ≤ 144 :=
  Fast.cell (z := matrix_19_40) (Fast.bands [(0, 0, 6), (1, 1, 7), (2, 2, 8), (3, 3, 9), (4, 4, 10), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 10), (11, 11, 9), (12, 12, 8), (13, 13, 7), (14, 14, 6), (15, 15, 5), (16, 16, 4), (17, 17, 3), (18, 18, 2), (19, 19, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_19_41 : CJ1.Block where
  bank := .leftLow
  cap := 137
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_19_41 : (CJ0.blockMatrix source 19 ((41 : ℤ)-24)).rank ≤ 137 :=
  Fast.cell (z := matrix_19_41) (Fast.bands [(0, 0, 6), (1, 1, 7), (2, 2, 8), (3, 3, 9), (4, 4, 10), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 10), (11, 11, 9), (12, 12, 8), (13, 13, 7), (14, 14, 6), (15, 15, 5), (16, 16, 4), (17, 17, 3), (18, 18, 2), (19, 19, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_19 (u : ℕ) : ℕ :=
  match u with
  | 40 => 144
  | 41 => 137
  | u => nominal 19 u

private theorem bound_19 (u : ℕ) :
    (CJ0.blockMatrix source 19 ((u : ℤ)-24)).rank ≤ allowance_19 u := by
  unfold allowance_19
  split
  · exact cell_19_40
  · exact cell_19_41
  · exact (block_rank_le 19 _).trans (rank_le_nominal 19 _)

theorem grade_19 : (∑ u ∈ Finset.range (83-19), (CJ0.blockMatrix source 19 ((u : ℤ)-24)).rank) ≤ 6000 := by
  refine (Finset.sum_le_sum fun u _ => bound_19 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_19)]
  decide +kernel

end Front6963ListBank

end Merged_Front6963ListCells0
