import ProximityPrize.SubmissionLower.GoldBranch4
import ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

namespace HighCore82258GeometryGoals
end HighCore82258GeometryGoals

set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_1
noncomputable section
open K1_14 (Equation)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3 (JetRing ordinate openFactor graphIdeal tangentEquation 
  )
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative)
open HighCore82258Upper_3_1_2
open Polynomial (C)
open TrivSqZeroExt
open scoped BigOperators Ring
open private flow flow_mul flow_C flow_sep flow_tangentEquation coeffDiff_one
  coeff_coeffDiff dx_nat from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
end
end HighCore82258GeometryCert_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_1
noncomputable section
open K1_14 (Equation Seeds)
open HighCore82258Upper_3 (JetRing ordinate)
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative secondAlongVelocity)
open HighCore82258Upper_3_1_2
open Polynomial (C eval₂RingHom)
open private flow flow_mul flow_C flow_X coeffDiff_add coeffDiff_mul coeff_coeffDiff
  coeffDiff_derivative from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
end
end HighCore82258GeometryCert_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2
end HighCore82258GeometryCert_2
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_1
noncomputable section
open K1_14 (FX)
open HighCore82258Upper_3 HighCore82258Upper_3_2_4 MvPolynomial
open scoped BigOperators MonomialOrder
end
end HighCore82258GeometryCert_2_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_2
noncomputable section
open HighCore82258Upper_3 HighCore82258Upper_3_2_4
def rootFree (B : Block) : Finset (Fin 2) :=
  Finset.univ.filter fun i => Sum.inl i ∈ B.free
def seedFree (B : Block) : Finset (Fin 3) :=
  Finset.univ.filter fun i => tᵢ i ∈ B.free
def rv {R : Type} [Semiring R] (r : ℕ) (a b : Prop) [Decidable a] [Decidable b]
    (T H HT HT₂ : R) : R :=
  if r = 0 then 0
  else if a then
    if b then T * (if r = 1 then 1 else HT)
    else if r = 1 then 1 else HT₂
  else if b then if r = 1 then 1 else H
  else 0
def seeds {R : Type} [Semiring R] (r : ℕ) (S S₂ Q : R) : R :=
  if r = 1 then 1 else if r = 2 then S else if r = 3 then Q * S * S₂ else 0
private def velocities (B : Block) (b : ℕ) : Finset ℕ :=
  if v₀ ∈ B.free then (if v₁ ∈ B.free then Finset.range (b+1) else {b})
  else if v₁ ∈ B.free then {0} else ∅
private theorem mem_velocities (B : Block) {b j : ℕ} (hb : 0 < b) :
    j ∈ velocities B b ↔ j ≤ b ∧ (v₀ ∉ B.free → j = 0) ∧
      (v₁ ∉ B.free → b-j = 0) := by
  by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [velocities, h₀', h₁'] <;> omega
private theorem mem_comp {n d : ℕ} {F : Finset (Fin n)} {f : Fin n →₀ ℕ} :
    f ∈ F.finsuppAntidiag d ↔ (∑ i, f i) = d ∧ ∀ i ∉ F, f i = 0 := by
  rw [Finset.mem_finsuppAntidiag', Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun h i hi => Finsupp.notMem_support_iff.mp (fun hm => hi (h hm))
  · intro h i hi
    by_contra hf
    exact (Finsupp.mem_support_iff.mp hi) (h i hf)
private def project {n : ℕ} (m : Exponent) (f : Fin n → CoxVar) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (f i))
private def pack (r : Fin 2 →₀ ℕ) (j b : ℕ) (z : Fin 3 →₀ ℕ) : Exponent :=
  Finsupp.equivFunOnFinite.symm (Sum.elim r (Sum.elim ![j,b-j] z))
private abbrev Increments (B : Block) (d : Degree) :=
  {m : Exponent // (∀ i ∉ B.free, m i = 0) ∧ Finsupp.weight coxWeight m = d}
private def enum (B : Block) (a b c : ℕ) (hb : 0 < b) :
    Increments B (nefDegree a b c) ≃
      (Σ j : velocities B b, (rootFree B).finsuppAntidiag (a+2*j.val)) ×
        (seedFree B).finsuppAntidiag c where
  toFun m := by
    have hz := m.prop.1
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have ha := congrArg Prod.fst hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    have hc := congrArg (fun d : Degree => d.2.2) hw
    change m.val h₀ + m.val h₁ + 2*m.val v₁ = a+2*b at ha
    change m.val v₀ + m.val v₁ = b at hv
    change m.val (tᵢ 0) + m.val (tᵢ 1) + m.val (tᵢ 2) = c at hc
    refine ⟨⟨⟨m.val v₀, (mem_velocities B hb).mpr ⟨by omega, hz _, ?_⟩⟩,
      ⟨project m.val Sum.inl, mem_comp.mpr ⟨?_, ?_⟩⟩⟩,
      ⟨project m.val tᵢ, mem_comp.mpr ⟨?_, ?_⟩⟩⟩
    · intro h
      have := hz v₁ h
      omega
    · rw [Fin.sum_univ_two]
      change m.val h₀ + m.val h₁ = a+2*m.val v₀
      omega
    · exact fun i hi => hz (Sum.inl i) (by simpa [rootFree] using hi)
    · rw [Fin.sum_univ_three]
      exact hc
    · exact fun i hi => hz (tᵢ i) (by simpa [seedFree] using hi)
  invFun p := by
    rcases p with ⟨⟨j, r⟩, z⟩
    have hj := ((mem_velocities B hb).mp j.prop).1
    have hj₀ := ((mem_velocities B hb).mp j.prop).2.1
    have hj₁ := ((mem_velocities B hb).mp j.prop).2.2
    have hr := (mem_comp.mp r.prop).1
    have hrz := (mem_comp.mp r.prop).2
    have hs := (mem_comp.mp z.prop).1
    have hsz := (mem_comp.mp z.prop).2
    rw [Fin.sum_univ_two] at hr
    rw [Fin.sum_univ_three] at hs
    refine ⟨pack r.val j.val b z.val, ?_, ?_⟩
    · intro i hi
      rcases i with i | (i | i)
      · exact hrz i (by simpa [rootFree] using hi)
      · fin_cases i
        · exact hj₀ hi
        · exact hj₁ hi
      · apply hsz i
        intro hz
        unfold seedFree at hz
        exact hi (Finset.mem_filter.mp hz).2
    · rw [weight_coordinates]
      change (r.val 0 + r.val 1 + 2*(b-j.val), j.val+(b-j.val),
        z.val 0+z.val 1+z.val 2) = (a+2*b,b,c)
      rw [hr, hs]
      congr 1
      · omega
      · congr 1
        omega
  left_inv m := by
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    change m.val v₀ + m.val v₁ = b at hv
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rcases i with i | (i | i)
    · rfl
    · fin_cases i
      · rfl
      · change b-m.val v₀ = m.val v₁
        omega
    · rfl
  right_inv p := by
    rcases p with ⟨⟨j,r⟩,z⟩
    apply Prod.ext
    · exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subtype.ext (Finsupp.ext fun _ => rfl)))
    · exact Subtype.ext (Finsupp.ext fun _ => rfl)
end
end HighCore82258GeometryCert_2_2
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_2
noncomputable section
open HighCore82258Upper_3 HighCore82258Upper_3_2 HighCore82258Upper_3_2_4 MvPolynomial
private def affine (i j : Fin 3) (r b : ℚ) : HilbertPoly :=
  MvPolynomial.X i + C r * MvPolynomial.X j + C b
private def baseDegree (B : Block) : Degree := Finsupp.weight coxWeight B.base
private def profile (B : Block) : HilbertPoly :=
  let (u,v,w) := baseDegree B
  rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
    (affine 1 1 0 (1-v)) (affine 0 0 0 (1+2*v-u))
    (affine 0 1 1 (1+v-u)) (affine 0 1 2 (1-u)) *
  seeds (seedFree B).card
    (affine 2 2 0 (1-w)) (affine 2 2 0 (2-w)) (C (1/2))
end
end HighCore82258GeometryCert_2_2
end
