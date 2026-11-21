import ProximityPrize.SubmissionLower.Final50Price

set_option Elab.async false
namespace Final50PriceLayer
open K1_13 (Shape)
open K1_13_8 (fastRemaining)
open Final50Price (remaining symbolCount)
open P0_9_8 (symbol_count)
open scoped BigOperators

abbrev layerCount : ℕ := 1 + Final50Price.primaryCutoff / Final50Price.layerWidth

def layerTerm (r y : Shape) (L i : ℕ) : ℕ :=
  remaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)

def fastLayer (r y : Shape) (L i : ℕ) : ℕ :=
  min symbolCount (fastRemaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j))

def massLength (r y : Shape) (L : ℕ) : ℕ := L + 1650 / (r.j + y.j)

def availableMass (r y : Shape) (L : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (massLength r y L), fastLayer r y L i

theorem remaining_anti {b j b' j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') :
    remaining b' j' ≤ remaining b j :=
  min_le_min_left _ (K1_13_8.remaining_anti hb hj)

theorem layerTerm_eq_fast (r y : Shape) (L i : ℕ) :
    layerTerm r y L i = fastLayer r y L i := by
  simp only [layerTerm, fastLayer, remaining, symbol_count]

private theorem fastLayer_zero {r y : Shape} {L i : ℕ}
    (hj : 0 < r.j+y.j) (hi : massLength r y L ≤ i) : fastLayer r y L i = 0 := by
  have h := K1_13_8.index_over hj (k := i-L) (show 1650 / (r.j+y.j) ≤ i-L by
    unfold massLength at hi; omega)
  have hr : (i-L+1)*r.j ≤ (i+1)*r.j := Nat.mul_le_mul_right _ (by omega)
  have hLi : L ≤ i := (Nat.le_add_right L (1650 / (r.j+y.j))).trans hi
  have hy : i-L+1 = i+1-L := (Nat.sub_add_comm hLi).symm
  rw [Nat.mul_add, hy] at h
  unfold fastLayer
  rw [K1_13_8.fastRemaining_zero (h.trans_le (Nat.add_le_add_right (by simpa only [hy] using hr) _)),
    Nat.min_zero]

theorem availableMass_eq_sum {r y : Shape} {L N : ℕ}
    (hj : 0 < r.j+y.j) (hN : massLength r y L ≤ N) :
    (∑ i ∈ Finset.range N, fastLayer r y L i) = availableMass r y L :=
  K1_13_8.sum_range_truncate (fun _ hi => fastLayer_zero hj hi) hN

theorem layerSum_le_available {r y : Shape} {L : ℕ} (hj : 0 < r.j + y.j) :
    (∑ i ∈ Finset.range layerCount, layerTerm r y L i) ≤ availableMass r y L := by
  let N := max layerCount (massLength r y L)
  rw [← availableMass_eq_sum hj (N := N) (le_max_right _ _)]
  exact K1_13_8.sum_range_mono (le_max_left _ _) fun i _ => (layerTerm_eq_fast r y L i).le

theorem availableMass_mono {r y : Shape} {l u : ℕ}
    (hj : 0 < r.j+y.j) (hl : l ≤ u) : availableMass r y l ≤ availableMass r y u := by
  let N := max (massLength r y l) (massLength r y u)
  rw [← availableMass_eq_sum hj (N := N) (le_max_left _ _),
    ← availableMass_eq_sum hj (N := N) (le_max_right _ _)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← layerTerm_eq_fast, ← layerTerm_eq_fast]
  exact remaining_anti
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hl _)) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hl _)) _)

theorem availableMass_anti_prefix {r y x : Shape} {L : ℕ} (hj : 0 < r.j+y.j)
    (hb : y.b ≤ x.b) (hidx : y.j ≤ x.j) : availableMass r x L ≤ availableMass r y L := by
  let N := max (massLength r x L) (massLength r y L)
  have hx : 0 < r.j+x.j := hj.trans_le (Nat.add_le_add_left hidx _)
  rw [← availableMass_eq_sum hx (N := N) (le_max_left _ _),
    ← availableMass_eq_sum hj (N := N) (le_max_right _ _)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← layerTerm_eq_fast, ← layerTerm_eq_fast]
  exact remaining_anti
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hb) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hidx) _)
end Final50PriceLayer
