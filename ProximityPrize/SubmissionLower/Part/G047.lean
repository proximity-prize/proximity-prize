import ProximityPrize.SubmissionLower.Part.G046


section Compact_SecondJetClearedHelper
/-! Clearing the second-derivative denominator preserves the interpolant's
vanishing on every regular codeword carried by F. -/
namespace ProximityPrize.SubmissionLower.SecondJetClearedHelper
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetSpecialize
open SecondJetCoefficientSpecialization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def cleared {R : Type*} [CommRing R] (P : Polynomial R) (n : ℕ) (H G : R) : R :=
  ∑ j : Fin (n+1), P.coeff j.val*H^(n-j.val)*G^j.val

theorem map_cleared {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (P : Polynomial R) (n : ℕ) (H G : R) :
    φ (cleared P n H G) = cleared (P.map φ) n (φ H) (φ G) := by
  simp [cleared,Polynomial.coeff_map]

theorem cleared_eval {R : Type*} [CommRing R] (P : Polynomial R) (n : ℕ)
    (hn : P.natDegree ≤ n) (H G t : R) (hrel : H*t = G) :
    cleared P n H G = H^n*P.eval t := by
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < n+1)]
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => P.coeff j*t^j)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hrel,mul_pow]
  have hh : H^(n-j.val)*H^j.val = H^n := by rw [← pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
  calc
    _ = P.coeff j.val*(H^(n-j.val)*H^j.val)*t^j.val := by ring
    _ = _ := by rw [hh]; ring

theorem coefficientSpecialize_eq (f : Polynomial K) (z : K) :
    (coefficientSpecialize f z).toRingHom = RCN319.specialization K f z := by
  rfl

theorem hasse_two (f : Polynomial K) :
    (2 : Polynomial K)*Polynomial.hasseDeriv 2 f = f.derivative.derivative := by
  have hh := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := 2)) f
  simpa [Function.iterate_succ_apply',nsmul_eq_mul] using hh

def helper (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K) (n d : ℕ) :
    MvPolynomial (Fin 4) K :=
  cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F)

theorem helper_vanish (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (n d : ℕ) (hn : (asS ((pderiv 1)^[d] P)).natDegree ≤ n)
    (f : Polynomial K) (z : K)
    (hF : RCN319.specialization K f z F = 0)
    (hP : specialize f z ((pderiv 1)^[d] P) = 0) :
    RCN319.specialization K f z (helper P F n d) = 0 := by
  have hrel : RCN319.specialization K f z (2*RCN313.polyH K F)*Polynomial.hasseDeriv 2 f =
      RCN319.specialization K f z (RCN313.polyG K F) := by
    rw [map_mul,map_ofNat]
    calc
      _ = RCN319.specialization K f z (RCN313.polyH K F)*
          ((2 : Polynomial K)*Polynomial.hasseDeriv 2 f) := by ring
      _ = _ := by rw [hasse_two]; exact RCN231.solution_slope_identity K F f z hF
  change (RCN319.specialization K f z).toRingHom
    (cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F)) = 0
  rw [map_cleared]
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
  rw [cleared_eval _ n (Polynomial.natDegree_map_le.trans hn) _ _ _ hrel]
  have hv : ((asS ((pderiv 1)^[d] P)).map (RCN319.specialization K f z)).eval
      (Polynomial.hasseDeriv 2 f) = 0 := by
    rw [Polynomial.eval_map,← coefficientSpecialize_eq,← specialize_eq]
    exact hP
  rw [hv,mul_zero]

end
end ProximityPrize.SubmissionLower.SecondJetClearedHelper

end Compact_SecondJetClearedHelper
