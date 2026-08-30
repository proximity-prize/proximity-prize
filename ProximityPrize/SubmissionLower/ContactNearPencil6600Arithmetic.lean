import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower.ContactNearPencil6600Arithmetic

open scoped BigOperators

theorem identity_degree_weight_cross_le
    (n a w k : ℕ) (hk : k ≤ w) (hwa : w < a) (han : a ≤ n) :
    (n - k) * (a - w) * (w - k) * a ≤
      n * (a - w) * w * (a - k) := by
  have hka : k ≤ a := hk.trans hwa.le
  have hkn : k ≤ n := hka.trans han
  let d := w - k
  let g := a - w
  let c := n - w
  have hdw : d ≤ w := by dsimp [d]; omega
  have haw : a = w + g := by dsimp [g]; omega
  have hnw : n = w + c := by dsimp [c]; omega
  have hak : a - k = d + g := by dsimp [d, g]; omega
  have hnk : n - k = d + c := by dsimp [d, c]; omega
  change (n - k) * g * d * a ≤ n * g * w * (a - k)
  rw [hnk, hak, haw, hnw]
  calc
    (d + c) * g * d * (w + g) ≤
        (d + c) * g * d * (w + g) +
          g * (w - d) * (w * d + g * (w + d) + c * g) := by omega
    _ = (w + c) * g * w * (d + g) := by
      let t := w - d
      have hwt : w = t + d := by
        dsimp [t]
        omega
      rw [hwt]
      have hsub : t + d - d = t := by omega
      simp only [hsub]
      ring

theorem identity_unit_weight_le
    (n a w k : ℕ) (hk : k ≤ w) (hwa : w < a) (han : a ≤ n) :
    (n - k) * (a - w) ≤ (n - w) * (a - k) := by
  have hka : k ≤ a := hk.trans hwa.le
  have hkn : k ≤ n := hka.trans han
  have hak : a - k = (w - k) + (a - w) := by omega
  have hnk : n - k = (w - k) + (n - w) := by omega
  rw [hak, hnk]
  have hgap : a - w ≤ n - w := Nat.sub_le_sub_right han w
  nlinarith [Nat.zero_le (w - k), Nat.zero_le (a - w), Nat.zero_le (n - w)]

theorem stratified_incidence_linear
    (q n a w k degreeCost unitCost U V : ℕ)
    (hk : k ≤ w) (hwa : w < a)
    (hraw : q * (a - k) ≤
      (n - k) * ((w - k) * degreeCost + unitCost))
    (hdegree : (n - k) * (a - w) * (w - k) ≤ U * (a - k))
    (hunit : (n - k) * (a - w) ≤ V * (a - k)) :
    q * (a - w) ≤ U * degreeCost + V * unitCost := by
  have hak : 0 < a - k := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hak
  calc
    q * (a - w) * (a - k) = (q * (a - k)) * (a - w) := by ring
    _ ≤ ((n - k) * ((w - k) * degreeCost + unitCost)) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hraw
    _ = ((n - k) * (a - w) * (w - k)) * degreeCost +
        ((n - k) * (a - w)) * unitCost := by ring
    _ ≤ (U * (a - k)) * degreeCost +
        (V * (a - k)) * unitCost :=
      Nat.add_le_add (Nat.mul_le_mul_right degreeCost hdegree)
        (Nat.mul_le_mul_right unitCost hunit)
    _ = (U * degreeCost + V * unitCost) * (a - k) := by ring

end ProximityPrize.SubmissionLower.ContactNearPencil6600Arithmetic
