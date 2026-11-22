import ProximityPrize.SubmissionLower.CurveListPairInterpolation

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace CurveListTripleSupport
open CJ0 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative CurveListJointWeight
open scoped Polynomial
open private jetView column_jet_injective from ProximityPrize.SubmissionLower.CurveListPairInterpolation

noncomputable section

abbrev JetExponent := Fin 3 →₀ ℕ

private abbrev exponent {A : ℕ} {s : Source} (i : ColumnIndex A s) : JetExponent :=
  (column A s i).exponent.some

private theorem exponent_degree {A : ℕ} {s : Source} (i : ColumnIndex A s) :
    (exponent i).degree = i.1.val.q := by
  rw [← totalJetDegree_eq_degree_some, totalJetDegree_eq_sum]
  simp [column, Jet.q, Fin.sum_univ_succ, SourceColumn.exponent_succ, Nat.add_assoc]

private theorem column_eq_of_exponent {A : ℕ} {s : Source} {i j : ColumnIndex A s}
    (hm : exponent i = exponent j) (hx : i.2.val = j.2.val) : i = j := by
  have hj := column_jet_injective hm
  rcases i with ⟨a,x⟩
  rcases j with ⟨b,y⟩
  change a = b at hj
  subst b
  exact congrArg (fun t : Fin (width A s a.val) => (⟨a,t⟩ : ColumnIndex A s)) (Fin.ext hx)

end
end CurveListTripleSupport
