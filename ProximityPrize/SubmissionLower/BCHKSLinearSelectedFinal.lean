import ProximityPrize.SubmissionLower.BCHKSLinearBranchFinal
import ProximityPrize.SubmissionLower.BCHKSDoubleCounting

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The final incidence adapter for a selected linear factor.  The hypotheses
`hQdeg`, `hQzero`, and `hHroot` are deliberately stated for the two concrete
specializations: in applications `Q x` is obtained by putting
`X=x, Y=U₀ x + Z*U₁ x` in the selected trivariate factor and `H z x` by
putting `Z=z, X=x`.  This formulation keeps all polynomial bookkeeping local
to the selection stage while making the double-counting/final-linear step
reusable. -/
theorem bchksLinearSelectedFinal
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (P : F → F[X]) (U₀ U₁ : F → F)
    (T : Finset F) (Arow : F → Finset F)
    (Q : F → F[X]) (Hlin : F → F → F[X])
    (hcardF : Fintype.card F = 262144)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (Arow z).card)
    (hsize : 2 * 111624646 * 1 * 1 * 63303 + 76721 + 1 ≤ T.card)
    (hQdeg : ∀ x, (Q x).natDegree ≤ 63303)
    (hQzero : ∀ x z, z ∈ T → x ∈ Arow z → (Q x).eval z = 0)
    (hHdeg : ∀ z ∈ T, ∀ x, (Hlin z x).natDegree = 1)
    (hPzero : ∀ z ∈ T, ∀ x,
      (Hlin z x).eval ((P z).eval x) = 0)
    (hHroot : ∀ z ∈ T, ∀ x, Q x = 0 →
      (Hlin z x).eval (U₀ x + z * U₁ x) = 0) :
    ∃ Tgood : Finset F, Tgood ⊆ T ∧ bchksErrors < Tgood.card ∧
      ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 131071 ∧
        p₁.natDegree ≤ 131071 ∧ ∀ z ∈ Tgood,
          P z = p₀ + Polynomial.C z * p₁ := by
  classical
  let A : Finset F := Finset.univ.filter fun x =>
    63303 < (T.filter fun z => x ∈ Arow z).card
  have hAcard : 131072 ≤ A.card := by
    simpa [A] using concrete_many_large_fibers T Arow 1 1 63303
      hcardF hrow hsize
  let Fib : {x // x ∈ A} → Finset F := fun x =>
    T.filter fun z => (x : F) ∈ Arow z
  have hline := bchksLinearBranchFinal 131071 63303 T A P U₀ U₁ Q Hlin
    hPdeg hAcard (by rw [hcardF]; omega) Fib
    (by intro x; exact Finset.filter_subset _ _)
    (by
      intro x
      have hx := (Finset.mem_filter.mp x.property).2
      simpa [Fib] using hx)
    (by intro x hx; exact hQdeg x)
    (by
      intro x z hz
      exact hQzero x z (Finset.mem_filter.mp hz).1
        (Finset.mem_filter.mp hz).2)
    hHdeg hPzero hHroot
  refine ⟨T, Finset.Subset.rfl, ?_, hline⟩
  dsimp [bchksErrors]
  omega

end ProximityPrize.SubmissionLower
