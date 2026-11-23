import ProximityPrize.SubmissionLower.FadicRaw
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option Elab.async false

namespace FadicGate
open scoped BigOperators

private def rSumIndices (n : ℕ) : ℕ :=
  Nat.div (Nat.mul n (Nat.sub n 1)) 2

private def rSumSquares (n : ℕ) : ℕ :=
  Nat.div (Nat.mul (Nat.mul n (Nat.sub n 1)) (Nat.sub (Nat.mul 2 n) 1)) 6

private theorem sum_indices_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, i) = rSumIndices n :=
  Finset.sum_range_id n

private theorem sum_squares_mul_six (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), i ^ 2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

private theorem sum_squares_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, i ^ 2) = rSumSquares n := by
  cases n with
  | zero => rfl
  | succ n =>
    change (∑ i ∈ Finset.range (n + 1), i ^ 2) =
      ((n + 1) * (n + 1 - 1) * (2 * (n + 1) - 1)) / 6
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.add_sub_cancel,
      mul_comm (n + 1) n, ← sum_squares_mul_six, Nat.mul_div_cancel _ (by decide : 0 < 6)]

private theorem sum_cubes_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, i ^ 3) = (∑ i ∈ Finset.range n, i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h := Finset.sum_range_id_mul_two n
    cases n with
    | zero => norm_num at *
    | succ n =>
      rw [show n.succ - 1 = n by omega] at h
      calc
        (∑ i ∈ Finset.range n.succ, i) ^ 2 + n.succ ^ 3 =
            (∑ i ∈ Finset.range n.succ, i) ^ 2 + n.succ ^ 2 +
              n.succ * (n.succ * n) := by
          simp only [Nat.succ_eq_add_one]
          ring
        _ = (∑ i ∈ Finset.range n.succ, i) ^ 2 + n.succ ^ 2 +
              n.succ * ((∑ i ∈ Finset.range n.succ, i) * 2) := by rw [h]
        _ = ((∑ i ∈ Finset.range n.succ, i) + n.succ) ^ 2 := by ring

/-- Sum a cubic with natural coefficients on the indices from zero to `n - 1`. -/
def rSumCubic (n c0 c1 c2 c3 : ℕ) : ℕ :=
  let s1 := rSumIndices n
  let s2 := rSumSquares n
  Nat.add (Nat.add (Nat.mul n c0) (Nat.mul c1 s1))
    (Nat.add (Nat.mul c2 s2) (Nat.mul c3 (Nat.mul s1 s1)))

theorem rSumCubic_eq (n c0 c1 c2 c3 : ℕ) :
    rSumCubic n c0 c1 c2 c3 =
      ∑ i ∈ Finset.range n, (c0 + c1 * i + (c2 * i ^ 2 + c3 * i ^ 3)) := by
  change n * c0 + c1 * rSumIndices n +
      (c2 * rSumSquares n + c3 * (rSumIndices n * rSumIndices n)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_squares_eq, sum_cubes_eq, sum_indices_eq]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, Nat.cast_id]

/-- Sum `rDenomQR (q + w * i) r` on a range where the remainder `r` is fixed. -/
def rDenomQRProg (n q w r : ℕ) : ℕ :=
  let c0 := Nat.add 2 (Nat.mul r (Nat.add r 1))
  let c1 := Nat.add (Nat.add 11 (Nat.mul 7 r)) (Nat.mul r r)
  let c2 := Nat.add 21 (Nat.mul 6 r)
  let c3 := 12
  Nat.div (rSumCubic n
    (Nat.add c0 (Nat.mul q (Nat.add c1 (Nat.mul q (Nat.add c2 (Nat.mul c3 q))))))
    (Nat.mul w (Nat.add c1 (Nat.mul q (Nat.add (Nat.mul 2 c2) (Nat.mul (Nat.mul 3 c3) q)))))
    (Nat.mul (Nat.mul w w) (Nat.add c2 (Nat.mul (Nat.mul 3 c3) q)))
    (Nat.mul c3 (Nat.mul (Nat.mul w w) w))) 2

private theorem denom_double (q r : ℕ) :
    rDenomQR q r * 2 =
      (2 + r * (r + 1)) + (11 + 7 * r + r * r) * q + (21 + 6 * r) * q ^ 2 + 12 * q ^ 3 := by
  change (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) * 2 = _
  simp only [add_mul, mul_assoc, Nat.div_mul_cancel (Nat.two_dvd_mul_add_one r),
    Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one r), Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one q)]
  rcases q with _ | _ | q
  · rcases r with _ | r <;> simp
  · rcases r with _ | r
    · simp
    · simp
      ring
  · have h1 : q + 1 + 1 - 1 = q + 1 := by omega
    have h2 : q + 1 + 1 - 2 = q := by omega
    rcases r with _ | r <;> simp [h1, h2] <;> ring

theorem rDenomQRProg_eq (n q w r : ℕ) :
    rDenomQRProg n q w r = ∑ i ∈ Finset.range n, rDenomQR (q + w * i) r := by
  change rSumCubic n _ _ _ _ / 2 = _
  rw [rSumCubic_eq]
  have h := Finset.sum_congr (s₁ := Finset.range n) rfl
    (fun (i : ℕ) _ => denom_double (q + w * i) r)
  rw [← Finset.sum_mul] at h
  rw [← Nat.mul_div_cancel (∑ i ∈ Finset.range n, rDenomQR (q + w * i) r)
    (by decide : 0 < 2), h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.add_eq, Nat.mul_eq]
  ring

private def rResidueCount (n p r : ℕ) : ℕ :=
  cond (Nat.blt r n) (Nat.add (Nat.div (Nat.sub (Nat.sub n 1) r) p) 1) 0

private theorem residueCount_iff {n p r j : ℕ} (hp : 0 < p) :
    j < rResidueCount n p r ↔ r + p * j < n := by
  simp only [rResidueCount, cond_eq_ite, Nat.blt_eq]
  split
  · change j < (n - 1 - r) / p + 1 ↔ _
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hp, Nat.mul_comm j p]
    omega
  · omega

private theorem sum_mod_groups (f : ℕ → ℕ) (n p : ℕ) (hp : 0 < p) :
    (∑ r ∈ Finset.range p, ∑ j ∈ Finset.range (rResidueCount n p r), f (r + p * j)) =
      ∑ i ∈ Finset.range n, f i := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => x.1 + p * x.2) (fun i => ⟨i % p, i / p⟩)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    exact Finset.mem_range.mpr <| (residueCount_iff hp).mp <|
      Finset.mem_range.mp (Finset.mem_sigma.mp hx).2
  · intro i hi
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt i hp), Finset.mem_range.mpr <|
        (residueCount_iff hp).mpr <| (Nat.mod_add_div i p).symm ▸ Finset.mem_range.mp hi⟩
  · rintro ⟨r, j⟩ hx
    have hr := Finset.mem_range.mp (Finset.mem_sigma.mp hx).1
    change (⟨(r + p * j) % p, (r + p * j) / p⟩ : Σ _ : ℕ, ℕ) = ⟨r, j⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.add_mul_div_left r j hp,
      Nat.div_eq_of_lt hr, zero_add]
  · intro i _
    exact Nat.mod_add_div i p

private theorem prefix_eq_sum (f : ℕ → ℕ) (n : ℕ) :
    rPrefix f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [rPrefix]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

/-- Sum the denominators on an arithmetic progression by grouping indices modulo its period. -/
def rDenomProg (n a step : ℕ) : ℕ :=
  let g := Nat.gcd 6 step
  let p := Nat.div 6 g
  let w := Nat.div step g
  rPrefix (fun r =>
    let x := Nat.add a (Nat.mul step r)
    cond (Nat.blt r n)
      (rDenomQRProg (Nat.add (Nat.div (Nat.sub (Nat.sub n 1) r) p) 1)
        (Nat.div x 6) w (Nat.mod x 6))
      0) p

theorem rDenomProg_eq (n a step : ℕ) :
    rDenomProg n a step = ∑ i ∈ Finset.range n, rDenom (a + step * i) := by
  let g := Nat.gcd 6 step
  let p := 6 / g
  let w := step / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left step (by decide)
  have hp : 0 < p := Nat.div_pos (Nat.gcd_le_left step (by decide)) hg
  have hpg : p * g = 6 := Nat.div_mul_cancel (Nat.gcd_dvd_left 6 step)
  have hwg : w * g = step := Nat.div_mul_cancel (Nat.gcd_dvd_right 6 step)
  have hperiod : step * p = 6 * w := by
    apply Nat.mul_right_cancel hg
    calc
      step * p * g = step * (p * g) := by ring
      _ = 6 * (w * g) := by rw [hpg, hwg, Nat.mul_comm]
      _ = 6 * w * g := by ring
  change rPrefix _ p = _
  rw [prefix_eq_sum, ← sum_mod_groups (fun i => rDenom (a + step * i)) n p hp]
  apply Finset.sum_congr rfl
  intro r _
  change (cond (Nat.blt r n)
    (rDenomQRProg ((n - 1 - r) / p + 1) ((a + step * r) / 6) w ((a + step * r) % 6)) 0) = _
  simp only [cond_eq_ite, Nat.blt_eq, rResidueCount]
  by_cases hr : r < n
  · simp only [ite_eq_left hr, rDenomQRProg_eq]
    apply Finset.sum_congr rfl
    intro j _
    have hx : a + step * (r + p * j) = (a + step * r) + 6 * (w * j) := by
      rw [Nat.mul_add, ← Nat.mul_assoc step p j, hperiod, Nat.mul_assoc, Nat.add_assoc]
    rw [hx]
    change rDenomQR ((a + step * r) / 6 + w * j) ((a + step * r) % 6) =
      rDenomQR (((a + step * r) + 6 * (w * j)) / 6) (((a + step * r) + 6 * (w * j)) % 6)
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 6), Nat.add_mul_mod_self_left]
  · simp [hr]

end FadicGate
