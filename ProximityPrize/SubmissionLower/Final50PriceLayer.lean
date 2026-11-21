import ProximityPrize.SubmissionLower.Final50Price

set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Final50PriceLayer
open K1_13 (Shape)
open K1_13_8 (zeroShape zeroMass fastRemaining)
open Final50Price (remaining symbolCount)
open P0_9_8 (symbol_count)
open scoped BigOperators

abbrev layerCount : ℕ := 1 + Final50Price.primaryCutoff / Final50Price.layerWidth

def layerTerm (r y : Shape) (L i : ℕ) : ℕ :=
  remaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)

def fastLayer (r y : Shape) (L i : ℕ) : ℕ :=
  if r.j = 0 ∧ i < L then symbolCount else
    fastRemaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)

def availableMass (r y : Shape) (L : ℕ) : ℕ :=
  if r.j = 0 then L * symbolCount + zeroMass y.b y.j
  else K1_13_8.availableMass r y L

theorem remaining_anti {b j b' j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') :
    remaining b' j' ≤ remaining b j :=
  min_le_min_left _ (K1_13_8.remaining_anti hb hj)

private theorem layerTerm_le (r y : Shape) (L i : ℕ) : layerTerm r y L i ≤ fastLayer r y L i := by
  unfold layerTerm fastLayer remaining
  split
  · exact min_le_left _ _
  · rw [← symbol_count]
    exact min_le_right _ _

theorem availableMass_eq_sum {r y : Shape} {L N : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) (hN : L + 1650 / (r.j + y.j) ≤ N) :
    (∑ i ∈ Finset.range N, fastLayer r y L i) = availableMass r y L := by
  rcases hr with rfl | hp
  · simp only [zeroShape, Nat.zero_add] at hj hN
    have hL := (Nat.le_add_right L (1650 / y.j)).trans hN
    rw [← Nat.add_sub_of_le hL, Finset.sum_range_add]
    have hfirst : (∑ i ∈ Finset.range L, fastLayer zeroShape y L i) = L * symbolCount := by
      calc
        _ = ∑ _i ∈ Finset.range L, symbolCount := Finset.sum_congr rfl fun i hi => by
          simp [fastLayer, zeroShape, Finset.mem_range.mp hi]
        _ = _ := by simp
    have htail (i : ℕ) : fastLayer zeroShape y L (L+i) =
        fastRemaining ((i+1)*y.b) ((i+1)*y.j) := by
      have hi : ¬ L+i < L := by omega
      have hi' : L+i+1-L = i+1 := by omega
      simp [fastLayer, zeroShape, hi, hi']
    rw [hfirst]
    simp_rw [htail]
    rw [K1_13_8.sum_range_truncate (m := 1650/y.j)
      (fun i hi => K1_13_8.fastRemaining_zero (K1_13_8.index_over hj hi)) (by omega)]
    rfl
  · rw [availableMass, ite_eq_right hp.ne']
    rw [← K1_13_8.availableMass_eq_sum symbol_count (Or.inr hp) hj hN]
    simp [fastLayer, K1_13_8.layerTerm, symbol_count, hp.ne']

theorem layerSum_le_available {r y : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j) :
    (∑ k ∈ Finset.range layerCount, layerTerm r y L k) ≤ availableMass r y L := by
  let N := max layerCount (L + 1650 / (r.j + y.j))
  rw [← availableMass_eq_sum hr hj (N := N) (le_max_right _ _)]
  exact K1_13_8.sum_range_mono (le_max_left _ _) fun k _ => layerTerm_le r y L k

theorem availableMass_mono {r y : Shape} {l u : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) (hl : l ≤ u) : availableMass r y l ≤ availableMass r y u := by
  rcases hr with rfl | hp
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right symbolCount hl) _
  · simp only [availableMass, ite_eq_right hp.ne']
    exact K1_13_8.availableMass_mono symbol_count (Or.inr hp) hj hl

theorem availableMass_anti_prefix {r y x : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j+y.j)
    (hb : y.b ≤ x.b) (hidx : y.j ≤ x.j) : availableMass r x L ≤ availableMass r y L := by
  rcases hr with rfl | hp
  · have h := P0_9_8.availableMass_anti_prefix (L := 0) (Or.inl rfl : zeroShape = zeroShape ∨ 0 < zeroShape.j) hj hb hidx
    have hz (a : Shape) : K1_13_8.availableMass zeroShape a 0 = zeroMass a.b a.j := by
      simp [K1_13_8.availableMass, zeroShape, zeroMass]
    rw [hz, hz] at h
    exact Nat.add_le_add_left h _
  · simp only [availableMass, ite_eq_right hp.ne']
    exact P0_9_8.availableMass_anti_prefix (Or.inr hp) hj hb hidx
end Final50PriceLayer
