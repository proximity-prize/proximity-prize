import ProximityPrize.SubmissionLower.HighJoint6921Arithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighJoint6921

open K1_14 Finset
open scoped BigOperators

def nodeCostAt (s : Shape) (q : ℕ) : ℕ :=
  let d := s.m + min q s.J - q
  let n := min (min q s.J + 1) ((d+1)/2)
  n*d - 2*(n*(n-1)/2)

def poleCostAt (s : Shape) (q : ℕ) : ℕ :=
  (min q s.J + 1) * ((s.B+s.J-q)*(s.B-q))

def fixedDebit (s : Shape) : ℕ :=
  triangle s.U * 262144 * ∑ q ∈ range (s.B+1), nodeCostAt s q

def linearDebit (s : Shape) : ℕ :=
  2*(s.U+1)*(∑ q ∈ range (s.B+1), poleCostAt s q)

private theorem sum_debit_at (p q u : ℕ) :
    (∑ i ∈ range u, (p - (q + 2*i))) =
      let d := p-q
      let n := min u ((d+1)/2)
      n*d - 2*(n*(n-1)/2) := by
  let d := p-q
  let n := min u ((d+1)/2)
  have htrim : (∑ i ∈ range n, (p - (q + 2*i))) = ∑ i ∈ range u, (p - (q+2*i)) := by
    apply sum_subset (range_mono (min_le_left _ _))
    intro i hi hin
    have hi' := mem_range.mp hi
    simp only [mem_range] at hin
    change ¬ i < min u ((d+1)/2) at hin
    have hd : d ≤ 2*i := by omega
    dsimp [d] at hd
    omega
  rw [← htrim]
  have hadd : (∑ i ∈ range n, (p - (q+2*i))) + 2*(∑ i ∈ range n, i) = n*d := by
    rw [mul_sum, ← sum_add_distrib]
    calc
      _ = ∑ _i ∈ range n, d := by
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        change i < min u ((d+1)/2) at hi'
        have hd : 2*i ≤ d := by omega
        dsimp [d] at *
        omega
      _ = _ := by simp
  rw [sum_range_id] at hadd
  change _ = n*d - 2*(n*(n-1)/2)
  omega

theorem debit_affine (s : Shape) (h : ℕ) :
    sourceDebit h s = fixedDebit s + h * linearDebit s := by
  unfold sourceDebit fixedDebit linearDebit
  have hnode : shapeSum s (fun q i => s.m + min q s.J - (q+2*i)) =
      ∑ q ∈ range (s.B+1), nodeCostAt s q := by
    unfold shapeSum
    apply sum_congr rfl
    intro q _
    exact sum_debit_at (s.m+min q s.J) q (min q s.J+1)
  have hpole : shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q)) =
      ∑ q ∈ range (s.B+1), poleCostAt s q := by
    simp [shapeSum, poleCostAt]
  rw [hnode, hpole]
  ring

def affineCost (s : Shape) (e step : ℕ) : ℕ :=
  linearDebit s + 2 * ordinatePenalty s e step

def affineSlope (s : Shape) : ℕ := triangle s.U * gradeMoment s

def affineValue (s : Shape) : ℕ :=
  triangle s.U * (top s * columnCount s + indexMoment s)

/-- The bounded-height certificate consists of the left endpoint inequality
and comparison of the two slopes. Neither assertion grows with the cutoff range. -/
def AffineCertificate (s : Shape) (lo e step : ℕ) : Prop :=
  fixedDebit s + lo * affineCost s e step + base lo * affineSlope s < affineValue s ∧
    affineCost s e step ≤ affineSlope s

theorem strict_of_affine (s : Shape) (h lo e step : ℕ)
    (hh : 0 < h) (hle : lo ≤ h) (hhi : h ≤ 131071) (he : 0 < e)
    (hwidth : s.B * base lo ≤ top s)
    (hc : AffineCertificate s lo e step) :
    sourceDebit h s + quotientVolume s h e step < rawVolume s h := by
  have hbase : base lo = base h + (h-lo) := by unfold base; omega
  have hwidth' : s.B * base h ≤ top s :=
    (Nat.mul_le_mul_left _ (by omega : base h ≤ base lo)).trans hwidth
  have hs : fixedDebit s + h * affineCost s e step + base h * affineSlope s <
      affineValue s := by
    calc
      _ = fixedDebit s + lo * affineCost s e step + base h * affineSlope s +
          (h-lo)*affineCost s e step := by
        have hmul : h * affineCost s e step =
            lo * affineCost s e step + (h-lo)*affineCost s e step := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hle]
        rw [hmul]
        ring
      _ ≤ fixedDebit s + lo * affineCost s e step + base h * affineSlope s +
          (h-lo)*affineSlope s :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hc.2) _
      _ = fixedDebit s + lo * affineCost s e step + base lo * affineSlope s := by
        rw [hbase]
        ring
      _ < _ := hc.1
  have hd : sourceDebit h s + quotientVolume s h e step ≤ fixedDebit s + h * affineCost s e step := by
    rw [debit_affine]
    unfold affineCost
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm h 2, ← Nat.add_assoc]
    exact Nat.add_le_add_left (quotient_le s h e step hh he) _
  have hraw := raw_add_grade s h hwidth'
  have hra : rawVolume s h + base h * affineSlope s = affineValue s := by
    simpa only [affineSlope, affineValue, Nat.mul_assoc, Nat.mul_left_comm] using hraw
  omega

/-- Small sums are evaluated by natural recursion instead of enumerating the
bank's individual cutoff nodes. -/
def natSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => natSum f n + f n

theorem range_sum_eq (f : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ range n, f i) = natSum f n := by
  induction n with
  | zero => simp [natSum]
  | succ n ih => rw [sum_range_succ, ih, natSum]

end HighJoint6921
