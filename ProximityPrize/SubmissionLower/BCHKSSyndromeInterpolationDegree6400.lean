import ProximityPrize.SubmissionLower.BCHKSLocatorProductionPencil6400
import ProximityPrize.SubmissionLower.BCHKSReedSolomonSyndrome6400

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

variable {K : Type} [Field K]

/-- A zero prefix of `rows` barycentric moments removes the top `rows`
coefficients of the full-domain Lagrange interpolant. -/
theorem rsSyndromeInterpolation_natDegree_lt_card_sub_of_zero_prefix
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι ↪ K) (e : ι → K) (rows : ℕ)
    (hrows : rows < Fintype.card ι)
    (hmoment : ∀ t, t < rows → rsSyndromeMoment α e t = 0) :
    (Lagrange.interpolate Finset.univ (fun i : ι => α i) e).natDegree <
      Fintype.card ι - rows := by
  classical
  let Q : K[X] :=
    Lagrange.interpolate Finset.univ (fun i : ι => α i) e
  have hQeval : ∀ i, Q.eval (α i) = e i := by
    intro i
    exact Lagrange.eval_interpolate_at_node e α.injective.injOn
      (Finset.mem_univ i)
  have hQdegree : Q.degree < (Fintype.card ι : WithBot ℕ) := by
    change
      ((Lagrange.interpolate Finset.univ (fun i : ι => α i)) e).degree <
        (Fintype.card ι : WithBot ℕ)
    simpa only [Finset.card_univ] using
      (Lagrange.degree_interpolate_lt
        (s := Finset.univ) (v := fun i : ι => α i)
        e α.injective.injOn)
  by_cases hQzero : Q = 0
  · simp only [Q, hQzero, Polynomial.natDegree_zero]
    omega
  have hQnat : Q.natDegree < Fintype.card ι := by
    rw [Polynomial.degree_eq_natDegree hQzero] at hQdegree
    exact WithBot.coe_lt_coe.mp hQdegree
  have hQbound : ∀ t, t ≤ rows →
      Q.natDegree < Fintype.card ι - t := by
    intro t ht
    induction t with
    | zero => simpa using hQnat
    | succ t ih =>
        have htRows : t ≤ rows := by omega
        have hi := ih htRows
        by_contra hnext
        have htltRows : t < rows := by omega
        have hdegreeExact :
            Q.natDegree = Fintype.card ι - (t + 1) := by
          omega
        have hsum :
            Q.natDegree + t = Fintype.card ι - 1 := by
          omega
        let P : K[X] := Q * Polynomial.X ^ t
        have hPne : P ≠ 0 := by
          exact mul_ne_zero hQzero
            (pow_ne_zero t (Polynomial.X_ne_zero :
              (Polynomial.X : K[X]) ≠ 0))
        have hPnat : P.natDegree = Fintype.card ι - 1 := by
          simpa only [P, Polynomial.natDegree_mul_X_pow t hQzero] using hsum
        have hnpos : 0 < Fintype.card ι := by omega
        have hPdegree : P.degree < (Fintype.card ι : WithBot ℕ) := by
          rw [Polynomial.degree_eq_natDegree hPne, hPnat]
          exact WithBot.coe_lt_coe.mpr (Nat.sub_lt hnpos Nat.one_pos)
        have htop := Lagrange.coeff_eq_sum
          (s := Finset.univ) (v := fun i : ι => α i)
          α.injective.injOn hPdegree
        have htopzero : P.coeff (Fintype.card ι - 1) = 0 := by
          calc
            P.coeff (Fintype.card ι - 1) =
                rsSyndromeMoment α e t := by
              simpa [P, rsSyndromeMoment, rsBarycentricDenominator,
                hQeval, mul_comm] using htop
            _ = 0 := hmoment t htltRows
        have hleadzero : Q.leadingCoeff = 0 := by
          calc
            Q.leadingCoeff = Q.coeff Q.natDegree := rfl
            _ = (Q * Polynomial.X ^ t).coeff
                (Q.natDegree + t) :=
              (Polynomial.coeff_mul_X_pow Q t Q.natDegree).symm
            _ = P.coeff (Fintype.card ι - 1) := by rw [hsum]
            _ = 0 := htopzero
        exact (Polynomial.leadingCoeff_ne_zero.mpr hQzero) hleadzero
  simpa only [Q] using hQbound rows le_rfl

end ProximityPrize.SubmissionLower
