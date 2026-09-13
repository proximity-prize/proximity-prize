/-
UNCOMPILED. Actual refined-coefficient interface for the first rational cut.
Copy FirstCutValuation6807.lean into ProximityPrize/SubmissionLower/ first.
This theorem has no first-tail-zero premise and does not manufacture a graph.
-/
import ProximityPrize.SubmissionLower.FirstCutValuation6807
import ProximityPrize.SubmissionLower.BoundaryTailPole

namespace ProximityPrize.SubmissionLower.ActualFirstCutPole6807
open scoped BigOperators
open RCN055 RCN057 RCN095 RCN136 RCN156 RCN204 RCN234 RCN313
open BoundaryTailAlgebra FirstCutValuation6807
set_option autoImplicit false
noncomputable section
variable {K Ω L : Type} [Field K] [Field Ω] [Field L]

def firstBaseFlag (m r v z : ℕ) : FlagDegree :=
  ⟨m*z,m*v-(m+1),m*(r-2)⟩

theorem actual_first_normalized_value_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a : Ω, V (coeff a) ≤ 1)
    (x : Fin 3 → L) (φ : Polynomial K →+* Ω)
    (F : MvPolynomial (Fin 4) K) (m r v z : ℕ)
    (hm : 1 ≤ m) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (hH : MvPolynomial.eval₂Hom coeff x (surfaceMap φ (polyH K F)) ≠ 0) :
    let ev := (MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
    let theta := max (2*flagPole V x unitAllFlag)
      (flagPole V x unitYZFlag+RCN187.poleOrder V (ev (polyG K F)/ev (polyH K F)))
    V (ev (baseNumerator F m)/ev (polyH K F)^(m+1)) ≤
      WithZero.exp (flagPole V x (firstBaseFlag m r v z)+(m+1 : ℕ)*theta) := by
  classical
  let ev := (MvPolynomial.eval₂Hom coeff x).comp (surfaceMap φ)
  let H := ev (polyH K F)
  let G := ev (polyG K F)
  let J := ev (boundaryJ F)
  let u := flagPole V x unitAllFlag
  let t := flagPole V x unitYZFlag
  let A := flagPole V x (⟨z,v,r-1⟩ : FlagDegree)
  let D := A-u
  let delta := 2*u-t
  let M := max delta (RCN187.poleOrder V (G/H))
  obtain ⟨ht0,htu,huA,hJcap,hGcap⟩ := boundary_flag_poles V x r v z hr (by omega)
  obtain ⟨hHF,hGF,hJF⟩ := boundary_surfaceMap_flags φ F r v z
    (by omega) (by omega) hR hYR hAll
  have hJ : V J ≤ WithZero.exp D := by
    dsimp only [J,D,A,u]
    rw [← hJcap]
    exact valuation_eval_le_flag V coeff hcoeff x _ _ hJF
  have hC (i : Fin (m+2)) :
      V (ev (refinedCoefficients F m i.val)) ≤ WithZero.exp
        ((i.val : ℤ)*delta+((min (2*i.val) m : ℕ) : ℤ)*D) := by
    dsimp only [delta,D,A,u,t]
    rw [← hJcap]
    exact refinedCoefficients_value_le V coeff hcoeff x φ F m i.val r v z hm
      (by omega) (by omega) hv hR hYR hAll
  have hsigma : V (G/H) ≤ WithZero.exp M := by
    apply WithZero.le_exp_of_log_le
    exact (le_max_right 0 _).trans (le_max_right delta _)
  have hs := first_sum_value_le V (n := m+2) (by omega) (G/H) J
    (fun i => ev (refinedCoefficients F m i.val)) delta D M
    (le_max_left _ _) hsigma hJ (by simpa using hC)
  have hn : V (ev (baseNumerator F m)/H^(m+1)) ≤
      WithZero.exp ((m : ℤ)*D+((m+1 : ℕ) : ℤ)*M) := by
    rw [map_baseNumerator_refined ev F m]
    rw [show m+1 = m+2-1 by omega]
    rw [divide_refined_sum (m+2) H G J _ hH]
    simpa only [show m+2-2=m by omega,show m+2-1=m+1 by omega] using hs
  have htheta : max (2*u) (t+RCN187.poleOrder V (G/H)) = t+M := by
    dsimp [M,delta]
    omega
  have hsafe : m+1 ≤ m*v := by nlinarith
  have hbase : flagPole V x (firstBaseFlag m r v z) = (m : ℤ)*D-((m+1 : ℕ) : ℤ)*t := by
    dsimp [firstBaseFlag,D,A,u,t]
    simp only [flagPole,unitAllFlag,unitYZFlag,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ r by omega),Nat.cast_sub (show 2 ≤ r by omega),
      Nat.cast_sub hsafe,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero,
      zero_mul,one_mul,zero_add,add_zero]
    ring
  change V (ev (baseNumerator F m)/H^(m+1)) ≤
    WithZero.exp (flagPole V x (firstBaseFlag m r v z)+
      ((m+1 : ℕ) : ℤ)*max (2*u) (t+RCN187.poleOrder V (G/H)))
  rw [htheta,hbase]
  convert hn using 1 <;> congr 1 <;> ring


/-- Includes zero-valued terms: logarithms are not applied as if they were units. -/
theorem pole_le_of_value_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (a : L) (bound : ℤ) (hb : 0 ≤ bound)
    (ha : V a ≤ WithZero.exp bound) : RCN187.poleOrder V a ≤ bound := by
  unfold RCN187.poleOrder
  apply max_le hb
  by_cases hz : V a = 0
  · simpa [hz] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr ha

end
end ProximityPrize.SubmissionLower.ActualFirstCutPole6807
