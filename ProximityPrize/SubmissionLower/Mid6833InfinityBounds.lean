/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833NormalizedTwist
namespace Frontier6969.GenuineMoving
open Polynomial Finset ProximityPrize.SubmissionLower
open Koala6831Separation (NormalForm Seeds pairDegree)
open Koala6831Moving (affineDenominator)
open Koala6831Comparison (SymbolicRow primitiveExcess)
open scoped Polynomial Classical
noncomputable section
variable {K : Type} [Field K]

/-- A full-degree denominator transfers the selected polynomial's degree cap to
both candidate coordinates whenever the moving determinant has small degree. -/
theorem infinity_small {q : SymbolicRow (Seeds K)} {w δ : ℕ} (N : NormalForm q w δ)
    (g : K) (P T : K[X]) (deg : P.natDegree≤w)
    (full : affineDenominator (N.A 0) (N.A 1) g≠0)
    (lead : pairDegree N.A≤(affineDenominator (N.A 0) (N.A 1) g).natDegree)
    (row : N.d₀*P+affineDenominator (N.C 0) (N.C 1) g =
      affineDenominator (N.A 0) (N.A 1) g*T)
    (small : (N.A 0*N.C 1-N.A 1*N.C 0).natDegree≤w+N.d₀.natDegree+pairDegree N.A) :
    ∀ j, (N.A j*T-N.C j).natDegree≤w+N.d₀.natDegree := by
  let A := affineDenominator (N.A 0) (N.A 1) g
  let M := N.A 0*N.C 1-N.A 1*N.C 0
  have expand (j : Fin 2) : A*(N.A j*T-N.C j) =
      N.A j*(N.d₀*P)+(if j=0 then C g else -1)*M := by
    dsimp [M,A,affineDenominator] at row ⊢
    fin_cases j <;> simp
    · linear_combination -(N.A 0)*row
    · linear_combination -(N.A 1)*row
  intro j
  by_cases nz : N.A j*T-N.C j=0
  · simp [nz]
  have da : (N.A j).natDegree≤pairDegree N.A := by
    fin_cases j <;> first | exact le_max_left _ _ | exact le_max_right _ _
  have dd := @natDegree_mul_le _ _ N.d₀ P
  have dp := @natDegree_mul_le _ _ (N.A j) (N.d₀*P)
  have c : ((if j=0 then C g else -1)*M).natDegree≤M.natDegree := by
    split
    · exact natDegree_C_mul_le _ _
    · simp
  have total := natDegree_add_le (N.A j*(N.d₀*P)) ((if j=0 then C g else -1)*M)
  rw [←expand j,natDegree_mul full nz] at total
  change M.natDegree≤_ at small
  omega
#print axioms infinity_small
end
end Frontier6969.GenuineMoving
