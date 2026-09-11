import ProximityPrize.SubmissionLower.Part.G039


section Compact_RootMultiplicityFlag
/-! Interface from bounded polynomial coefficients to the moving-coordinate
height bound used in the lower submission's flag geometry. -/
namespace ProximityPrize.SubmissionLower.RootMultiplicityFlag
open scoped Classical BigOperators WithZero
open RCN026 RCN095 RCN187 RCN204
open RCN344 (constant_value_le_one)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem moving_bound (P : Polynomial (MvPolynomial (Fin 3) K)) (p : FlagDegree)
    (hPflag : ∀ i, RCN095.PolynomialInFlag p (P.coeff i)) (x : Fin 3 → L)
    (t : L) (d : ℕ)
    (hP : P.map (MvPolynomial.eval₂Hom (algebraMap K L) x) ≠ 0)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣
      P.map (MvPolynomial.eval₂Hom (algebraMap K L) x))
    (C A : ℤ)
    (hbudget : ∀ W : Finset (Place K L), (∑ v ∈ W, flagPole v.val x p) ≤ C)
    (halpha : ∀ W : Finset (Place K L), (∑ v ∈ W, flagPole v.val x unitAllFlag) ≤ A)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*flagPole v.val x unitAllFlag)
      (flagPole v.val x unitYZFlag+poleOrder v.val t)) ≤ 2*(d : ℤ)*A+C := by
  apply RootMultiplicityHeight.moving_height_bound K L
    (P.map (MvPolynomial.eval₂Hom (algebraMap K L) x)) hP t d hd
    (fun v => flagPole v.val x p) _ _ C A _ hbudget _ _ halpha W
  · intro v i
    rw [Polynomial.coeff_map]
    exact valuation_eval_le_flag v.val (algebraMap K L) (constant_value_le_one K L v)
      x p (P.coeff i) (hPflag i)
  · intro v
    exact flagPole_nonneg v.val x unitAllFlag
  · intro v
    rw [flagPole_unitYZ, flagPole_unitAll]
    exact le_max_right _ _

end
end ProximityPrize.SubmissionLower.RootMultiplicityFlag

end Compact_RootMultiplicityFlag
