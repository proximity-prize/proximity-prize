import ProximityPrize.SubmissionLower.Rect51HilbertBase
import ProximityPrize.SubmissionLower.Rect51TangentSection

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000

namespace Rect51Hilbert
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82706Tangent_3 (JetRing ordinate seedVar)
open Rect51Tangent (Axes Bounded Weighted Section)
open MvPolynomial
open scoped BigOperators

private def term (a t : ℕ) (v : Axes) (j k : ℕ) (m : Fin 2 →₀ ℕ) (c : FX) : Cox :=
  (C c * MvPolynomial.X (seed₀ 1)^(m 0) * MvPolynomial.X (seed₁ 1)^(m 1) * MvPolynomial.X h₁^k * MvPolynomial.X v₁^j) *
    (MvPolynomial.X h₀^(a-(k+2*j)) * MvPolynomial.X v₀^(t-j) * MvPolynomial.X (seed₀ 0)^(v 0-m 0) * MvPolynomial.X (seed₁ 0)^(v 1-m 1))

private theorem term_weight {a t : ℕ} {v : Axes} {j k : ℕ} {m : Fin 2 →₀ ℕ} (c : FX)
    (ha : k+2*j ≤ a) (ht : j ≤ t) (h₀s : m 0 ≤ v 0) (h₁s : m 1 ≤ v 1) :
    (term a t v j k m c).IsWeightedHomogeneous coxWeight (a,t,v 0,v 1) := by
  let H q := isWeightedHomogeneous_X FX coxWeight q
  have hd := (((((isWeightedHomogeneous_C coxWeight c).mul ((H (seed₀ 1)).pow (m 0))).mul
    ((H (seed₁ 1)).pow (m 1))).mul ((H h₁).pow k)).mul ((H v₁).pow j)).mul
      (((((H h₀).pow (a-(k+2*j))).mul ((H v₀).pow (t-j))).mul
        ((H (seed₀ 0)).pow (v 0-m 0))).mul ((H (seed₁ 0)).pow (v 1-m 1)))
  have e₀ : k+j*2+(a-(k+2*j)) = a := by omega
  simpa [H, term, coxWeight, h₀, h₁, v₀, v₁, seed₀, seed₁, Prod.mk_add_mk,
    Prod.smul_mk, e₀, Nat.add_sub_of_le ht, Nat.add_sub_of_le h₀s, Nat.add_sub_of_le h₁s] using hd

private theorem term_dehom (a t : ℕ) (v : Axes) (j k : ℕ) (m : Fin 2 →₀ ℕ) (c : FX) :
    dehom (term a t v j k m c) = Polynomial.monomial j (Polynomial.monomial k (monomial m c)) := by
  have hC : dehom (C c) = Polynomial.C (Polynomial.C (C c)) := by
    exact dehom.commutes c
  have hv₀ : dehom (MvPolynomial.X v₀) = (1 : JetRing) := by simp [dehom,affineCoord,v₀]
  have hv₁ : dehom (MvPolynomial.X v₁) = (Polynomial.X : JetRing) := by simp [dehom,affineCoord,v₁]
  have hh₀ : dehom (MvPolynomial.X h₀) = (1 : JetRing) := by simp [dehom,affineCoord,h₀]
  have hh₁ : dehom (MvPolynomial.X h₁) = ordinate := by simp [dehom,affineCoord,h₁]
  have hs₀ : dehom (MvPolynomial.X (seed₀ 0)) = (1 : JetRing) := by simp [dehom,affineCoord,seed₀]
  have hs₁ : dehom (MvPolynomial.X (seed₁ 0)) = (1 : JetRing) := by simp [dehom,affineCoord,seed₁]
  have ht₀ : dehom (MvPolynomial.X (seed₀ 1)) = seedVar 0 := by simp [dehom,affineCoord,seed₀]
  have ht₁ : dehom (MvPolynomial.X (seed₁ 1)) = seedVar 1 := by simp [dehom,affineCoord,seed₁]
  simp only [term,map_mul,map_pow,hC,hv₀,hv₁,hh₀,hh₁,hs₀,hs₁,ht₀,ht₁,one_pow,mul_one]
  have hseed : (Polynomial.C (Polynomial.C (C c)) * seedVar 0^(m 0) * seedVar 1^(m 1) : JetRing) =
      Polynomial.C (Polynomial.C (monomial m c)) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [seedVar, Polynomial.C_mul, Polynomial.C_pow]
    rw [mul_assoc]
  rw [hseed]
  unfold ordinate
  rw [← Polynomial.C_pow, ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.C_mul_X_pow_eq_monomial]

/-- Lift an affine polynomial with rectangular support to the required Cox piece. -/
theorem lift {P : JetRing} {a t : ℕ} {v : Axes}
    (hb : Bounded P t v) (hw : Weighted P a) :
    ∃ p : Cox, p.IsWeightedHomogeneous coxWeight (a,t,v 0,v 1) ∧ dehom p = P := by
  classical
  refine ⟨∑ j ∈ P.support, ∑ k ∈ (P.coeff j).support,
    ∑ m ∈ ((P.coeff j).coeff k).support, term a t v j k m (((P.coeff j).coeff k).coeff m), ?_, ?_⟩
  · apply IsWeightedHomogeneous.sum
    intro j hj
    apply IsWeightedHomogeneous.sum
    intro k hk
    apply IsWeightedHomogeneous.sum
    intro m hm
    apply term_weight
    · exact Nat.le_of_not_gt (fun h => (Polynomial.mem_support_iff.mp hk) (hw _ _ h))
    · exact (Polynomial.le_natDegree_of_mem_supp _ hj).trans hb.1
    · exact (monomial_le_degreeOf 0 hm).trans (hb.2 j k 0)
    · exact (monomial_le_degreeOf 1 hm).trans (hb.2 j k 1)
  · simp only [map_sum,term_dehom]
    conv_rhs => rw [← P.sum_monomial_eq, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro j _
    have inner (k : ℕ) :
        (∑ m ∈ ((P.coeff j).coeff k).support, Polynomial.monomial j
          (Polynomial.monomial k (monomial m (((P.coeff j).coeff k).coeff m)))) =
        Polynomial.monomial j (Polynomial.monomial k ((P.coeff j).coeff k)) := by
      rw [← map_sum (Polynomial.monomial j), ← map_sum (Polynomial.monomial k)]
      rw [← ((P.coeff j).coeff k).as_sum]
    simp_rw [inner]
    rw [← map_sum (Polynomial.monomial j)]
    congr 1
    exact (P.coeff j).sum_monomial_eq

#print axioms lift
end
end Rect51Hilbert
