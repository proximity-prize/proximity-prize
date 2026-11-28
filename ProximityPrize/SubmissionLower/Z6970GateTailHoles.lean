import ProximityPrize.SubmissionLower.Z6970H2307GateAmbientFast

set_option Elab.async false
set_option autoImplicit false

namespace Gate6970Leading

open Gate6966Cell (sumUpTo)
open ExpandedGate6970.H2307Numeric (cap)

def tailSum (g P : ℕ → ℤ) (L : ℕ) : ℤ :=
  P 1598 - P (cap (3514 + L) + 1) -
    sumUpTo (fun i => g (1573 - 26 * i)) ((L + 1) / 25)

private def tailStep (L : ℕ) : Bool :=
  let prev := cap (3514 + L)
  let next := cap (3514 + (L + 1))
  if (L + 2) % 25 = 0 then
    decide (prev = next + 2 ∧ next + 1 = 1573 - 26 * ((L + 1) / 25))
  else
    decide (prev = next + 1)

private theorem tailStep_valid (L : ℕ) (bound : L < 511) : tailStep L = true := by
  have allSteps : (List.range 511).all tailStep = true := by decide +kernel
  exact List.all_eq_true.mp allSteps L (List.mem_range.mpr bound)

theorem tailSum_eq (g P : ℕ → ℤ) (hP : ∀ n, P n = sumUpTo g n)
    (L : ℕ) (bound : L ≤ 511) :
    sumUpTo (fun k => g (cap (3514 + k))) L = tailSum g P L := by
  have addOne (n : ℕ) : P (n + 1) = P n + g n := by
    rw [hP (n + 1), hP n]
    rfl
  induction L with
  | zero =>
    have start : cap (3514 + 0) + 1 = 1598 := by decide
    simp [tailSum, sumUpTo, start]
  | succ L ih =>
    have step := tailStep_valid L (by omega)
    change sumUpTo (fun k => g (cap (3514 + k))) L + g (cap (3514 + L)) =
      tailSum g P (L + 1)
    rw [ih (by omega)]
    unfold tailSum
    by_cases skip : (L + 2) % 25 = 0
    · have caps : cap (3514 + L) = cap (3514 + (L + 1)) + 2 ∧
          cap (3514 + (L + 1)) + 1 = 1573 - 26 * ((L + 1) / 25) := by
        simpa [tailStep, skip] using step
      have count : (L + 1 + 1) / 25 = (L + 1) / 25 + 1 := by omega
      have prev : P (cap (3514 + L) + 1) =
          P (cap (3514 + (L + 1)) + 1) +
            g (1573 - 26 * ((L + 1) / 25)) + g (cap (3514 + L)) := by
        rw [addOne (cap (3514 + L)), caps.1]
        rw [show cap (3514 + (L + 1)) + 2 = (cap (3514 + (L + 1)) + 1) + 1 by omega,
          addOne (cap (3514 + (L + 1)) + 1), caps.2]
      rw [prev, count, sumUpTo]
      ring
    · have caps : cap (3514 + L) = cap (3514 + (L + 1)) + 1 := by
        simpa [tailStep, skip] using step
      have count : (L + 1 + 1) / 25 = (L + 1) / 25 := by omega
      rw [addOne (cap (3514 + L)), count, caps]
      ring

end Gate6970Leading
