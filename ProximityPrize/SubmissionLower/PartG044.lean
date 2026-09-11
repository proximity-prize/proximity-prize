import ProximityPrize.SubmissionLower.PartG043


section Compact_SecondJetRelaxedFlag
/-! The weighted R+2S source gives affine coefficient pole budgets. The final
height application still requires a nonzero component polynomial, its root
multiplicity, and a geometric budget for the resulting flag. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedFlag
open scoped BigOperators WithZero
open ProximityPrize.SubmissionLower.RootMultiplicityValuation
open MvPolynomial RCN095 RCN026 RCN187 RCN204
open SecondJetCoefficients SecondJetSupport SecondJetFlagCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K L : Type*} [Field K] [Field L]

def coefficientFlag (B U T j : ℕ) : FlagDegree := ⟨T-U,U-B+j,B-2*j⟩

def budgetFlag (B U T d n0 : ℕ) : FlagDegree := ⟨T-U,U-B+n0,B-2*(n0-d)⟩

theorem coefficient_bounds (P : Poly (K := K)) (B U T : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (j : ℕ) (e : Fin 4 →₀ ℕ) (he : e ∈ ((asS (K := K) P).coeff j).support) :
    2*j+e 2 ≤ B ∧ j+e 1+e 2 ≤ U ∧ j+e 1+e 2+e 3 ≤ T := by
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rwa [h1,h2,h3,h4] at hh

theorem frozen_coefficient_flag (P : Poly (K := K)) (x : K) (B U T : ℕ)
    (hBU : B ≤ U) (hUT : U ≤ T)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T) (j : ℕ) :
    PolynomialInFlag (coefficientFlag B U T j) (freeze x ((asS (K := K) P).coeff j)) := by
  apply freeze_inFlag
  intro e he
  have hb := coefficient_bounds P B U T hP j e he
  change e 2 ≤ B-2*j ∧ e 1+e 2 ≤ U-B+j+(B-2*j) ∧
    e 1+e 2+e 3 ≤ T-U+(U-B+j)+(B-2*j)
  omega

theorem coefficient_flag_pole (v : Valuation L Value) (x : Fin 3 → L)
    (B U T j : ℕ) (hj : 2*j ≤ B) :
    flagPole v x (coefficientFlag B U T j) =
      flagPole v x (coefficientFlag B U T 0) -
        (j : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag) := by
  simp only [flagPole, coefficientFlag, unitAllFlag, unitYZFlag, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  rw [Nat.cast_sub hj]
  push_cast
  ring

theorem budget_flag_pole (v : Valuation L Value) (x : Fin 3 → L)
    (B U T d n0 : ℕ) (hd : d ≤ n0) (hB : 2*(n0-d) ≤ B) :
    flagPole v x (budgetFlag B U T d n0) =
      flagPole v x (coefficientFlag B U T 0) + (d : ℤ)*flagPole v x unitYZFlag -
        ((n0-d : ℕ) : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag) := by
  simp only [flagPole, budgetFlag, coefficientFlag, unitAllFlag, unitYZFlag, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  simp only [Nat.cast_sub hB, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd, Nat.cast_add]
  ring

theorem frozen_coefficient_valuation (P : Poly (K := K)) (freezeX : K)
    (B U T : ℕ) (hBU : B ≤ U) (hUT : U ≤ T)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (v : Valuation L Value) (coeff : K →+* L) (hc : ∀ c, v (coeff c) ≤ 1)
    (x : Fin 3 → L) (j : ℕ) :
    v (MvPolynomial.eval₂Hom coeff x (freeze freezeX ((asS (K := K) P).coeff j))) ≤
      WithZero.exp (flagPole v x (coefficientFlag B U T 0) -
        (j : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag)) := by
  by_cases hz : (asS (K := K) P).coeff j = 0
  · simp only [hz, map_zero]
    exact zero_le
  have hs : ((asS (K := K) P).coeff j).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hz
  obtain ⟨e,he⟩ := hs
  have hj : 2*j ≤ B := by have := coefficient_bounds P B U T hP j e he; omega
  rw [← coefficient_flag_pole v x B U T j hj]
  exact valuation_eval_le_flag v coeff hc x (coefficientFlag B U T j) _
    (frozen_coefficient_flag P freezeX B U T hBU hUT hP j)

section FunctionField
variable [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- The numerical weighted flag used by the scout is sufficient for the generic
moving-height theorem. Nonvanishing and multiplicity are explicit premises. -/
theorem moving_bound (P : Poly (K := K)) (freezeX : K) (B U T d n0 : ℕ)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : d ≤ n0) (hB : 2*(n0-d) ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (x : Fin 3 → L) (Q : Polynomial L)
    (hQcoeff : ∀ j, Q.coeff j = MvPolynomial.eval₂Hom (algebraMap K L) x
      (freeze freezeX ((asS (K := K) P).coeff j)))
    (hQ : Q ≠ 0) (hn : n0 ≤ Q.natDegree) (t : L)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ Q) (C : ℤ)
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, flagPole v.val x (budgetFlag B U T d n0)) ≤ C)
    (V : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ V, max (2*flagPole v.val x unitAllFlag)
      (flagPole v.val x unitYZFlag+poleOrder v.val t)) ≤ C := by
  apply RootMultiplicityWeightedHeight.moving_height_bound_of_degree K Q hQ t d n0 hn hd
    (fun v => flagPole v.val x (coefficientFlag B U T 0))
    (fun v => flagPole v.val x unitAllFlag) (fun v => flagPole v.val x unitYZFlag) C
    (fun v => flagPole_nonneg v.val x unitAllFlag) ?_ ?_ ?_ V
  · intro v
    rw [flagPole_unitYZ, flagPole_unitAll]
    exact le_max_right _ _
  · intro v j
    rw [hQcoeff j]
    exact frozen_coefficient_valuation P freezeX B U T hBU hUT hP v.val
      (algebraMap K L) (RCN344.constant_value_le_one K L v) x j
  · intro W
    convert hbudget W using 1
    apply Finset.sum_congr rfl
    intro v _
    exact (budget_flag_pole v.val x B U T d n0 hdn hB).symm

end FunctionField

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedFlag

end Compact_SecondJetRelaxedFlag
