import ProximityPrize.SubmissionLower.CurveListSparsePackets

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace CurveListScalarWide55
open Finset CJ0 CurveListSparsePackets
open scoped BigOperators

def support : Source := ⟨55,75,22,10,(fullBox 75 22 10).filter fun j => j.b+3*j.c ≤ 31⟩

theorem shapeOK : ShapeOK support := by
  have hmem := mem_fullBox (B := 75) (J := 22) (C := 10) (by decide) (by decide)
  refine ⟨by decide,by decide,by decide,by decide,by decide,?_,?_⟩
  · intro j hj
    exact (hmem j).mp (mem_filter.mp hj).1
  · intro j hj _
    obtain ⟨hb,hf⟩ := mem_filter.mp hj
    have h := (hmem j).mp hb
    refine mem_filter.mpr ⟨(hmem _).mpr ?_,hf⟩
    exact ⟨by simpa [Jet.q,Jet.a,Jet.b,Jet.c] using (show j.a-1+j.b+j.c ≤ 75 by unfold Jet.q at h; omega),h.2⟩

theorem facet (j : Jet) (hj : j ∈ support.E) : j.b+3*j.c ≤ 31 := (mem_filter.mp hj).2

private def width (c b : ℕ) := if b+3*c ≤ 31 then 76-(b+c) else 0
private def bRange (c : ℕ) := range (22-2*c+1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, width c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (width c b*(width c b-1)/2+width c b*(b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, width c b*(b+2*c)

theorem ragged : support.E =
    (range 11).sigma (fun c => (bRange c).sigma (fun b => range (width c b))) := by
  ext j
  rcases j with ⟨c,b,a⟩
  change (⟨c,b,a⟩ : Jet) ∈ (fullBox 75 22 10).filter (fun j => j.b+3*j.c ≤ 31) ↔ _
  rw [mem_filter, mem_fullBox (B := 75) (J := 22) (C := 10) (by decide) (by decide)]
  simp only [mem_sigma, mem_range, bRange, width, Jet.q, Jet.v, Jet.a, Jet.b, Jet.c]
  split_ifs <;> omega

theorem moments : support.E.card = 9231 ∧ (∑ j ∈ support.E, j.q) = 395185 ∧
    (∑ j ∈ support.E, j.v) = 129580 := by
  have h₁ : ∑ c ∈ range 11, countRow c = 9231 := by decide +kernel
  have h₂ : ∑ c ∈ range 11, totalRow c = 395185 := by decide +kernel
  have h₃ : ∑ c ∈ range 11, indexRow c = 129580 := by decide +kernel
  refine ⟨?_,?_,?_⟩
  · simpa only [ragged, card_sigma, card_range, countRow] using h₁
  · rw [ragged, sum_sigma]
    refine Eq.trans (sum_congr rfl (fun c _ => ?_)) h₂
    simp only [sum_sigma, totalRow, Jet.q, Jet.a, Jet.b, Jet.c]
    apply sum_congr rfl
    intro b _
    simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range,
      smul_eq_mul, Nat.mul_add]
  · simpa only [ragged, sum_sigma, indexRow, Jet.v, Jet.b, Jet.c, sum_const, card_range,
      smul_eq_mul] using h₃

private def rowLo (q u a : ℕ) := u+2*q+a+1-77
private def rowHi (q u a : ℕ) := min (q+1-a) (u+2*q+a+1-22)
private def colLo (u b : ℕ) := (23-(u+b))/2
private def colHi (q b : ℕ) :=
  min (min 11 (min (q-b+1) ((22-b)/2+1))) ((31-b)/3+1)

def axes : Axes where
  outer side q := if side then q+1 else min q 22+1
  fiber side q u i := if side then rowHi q u i-rowLo q u i else colHi q i-colLo u i
  point side q u i j := if side then
    let b := rowLo q u i+j
    ⟨q-(i+b),b,i⟩
  else
    let c := colLo u i+j
    ⟨c,i,q-(i+c)⟩

private theorem row_bounds (q u c b a : ℕ)
    (h : (⟨c,b,a⟩ : Jet) ∈ blockRows support.m q ((u : ℤ)-support.J)) :
    a < q+1 ∧ rowLo q u a ≤ b ∧ b < rowHi q u a ∧ q-(a+b) = c := by
  change _ ∈ blockRows 55 q ((u : ℤ)-22) at h
  simp only [blockRows, mem_filter, mem_sigma, mem_range, mem_singleton, Jet.v, Jet.b,
    Jet.c, Jet.a, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  unfold rowLo rowHi
  omega

private theorem col_bounds (q u c b a : ℕ)
    (h : (⟨c,b,a⟩ : Jet) ∈ blockCols support q ((u : ℤ)-support.J)) :
    b < min q 22+1 ∧ colLo u b ≤ c ∧ c < colHi q b ∧ q-(b+c) = a := by
  change _ ∈ (((fullBox 75 22 10).filter fun j => j.b+3*j.c ≤ 31).filter
    fun j => j.q = q ∧ 0 ≤ (u : ℤ)-22+(j.v : ℤ)) at h
  rw [mem_filter,mem_filter,mem_fullBox (B := 75) (J := 22) (C := 10) (by decide) (by decide)] at h
  simp only [Jet.q,Jet.v,Jet.a,Jet.b,Jet.c,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h
  unfold colLo colHi at *
  omega

private def rowIndex (q u : ℕ) : ↥(blockRows support.m q ((u : ℤ)-support.J)) → Axis axes true q u
  | ⟨⟨c,b,a⟩,h⟩ =>
    let H := row_bounds q u c b a h
    ⟨⟨a,H.1⟩,⟨b-rowLo q u a,by
      change b-rowLo q u a < rowHi q u a-rowLo q u a
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩

private def colIndex (q u : ℕ) : ↥(blockCols support q ((u : ℤ)-support.J)) → Axis axes false q u
  | ⟨⟨c,b,a⟩,h⟩ =>
    let H := col_bounds q u c b a h
    ⟨⟨b,H.1⟩,⟨c-colLo u b,by
      change c-colLo u b < colHi q b-colLo u b
      obtain ⟨_,hlo,hhi,_⟩ := H
      omega⟩⟩

theorem rowIndex_point (q u : ℕ) (i : ↥(blockRows support.m q ((u : ℤ)-support.J))) :
    axes.point true q u (rowIndex q u i).1 (rowIndex q u i).2 = i.val := by
  rcases i with ⟨⟨c,b,a⟩,h⟩
  obtain ⟨_,hlo,_,heq⟩ := row_bounds q u c b a h
  change (⟨q-(a+(rowLo q u a+(b-rowLo q u a))),rowLo q u a+(b-rowLo q u a),a⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo,heq]

theorem colIndex_point (q u : ℕ) (i : ↥(blockCols support q ((u : ℤ)-support.J))) :
    axes.point false q u (colIndex q u i).1 (colIndex q u i).2 = i.val := by
  rcases i with ⟨⟨c,b,a⟩,h⟩
  obtain ⟨_,hlo,_,heq⟩ := col_bounds q u c b a h
  change (⟨colLo u b+(c-colLo u b),b,q-(b+(colLo u b+(c-colLo u b)))⟩ : Jet) = _
  rw [Nat.add_sub_of_le hlo,heq]

theorem block_rank_le (q u : ℕ) : (blockMatrix support q ((u : ℤ)-22)).rank ≤ (packet axes q u).rank :=
  rank_of_coverage axes support q u (rowIndex q u) (colIndex q u) (rowIndex_point q u) (colIndex_point q u)

def nominal (q u : ℕ) := min (size axes true q u) (size axes false q u)

theorem block_rank_nominal (q u : ℕ) : (blockMatrix support q ((u : ℤ)-22)).rank ≤ nominal q u :=
  (block_rank_le q u).trans (rank_le_nominal axes q u)

end CurveListScalarWide55
