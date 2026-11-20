import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

noncomputable def specializeAffine {K : Type*} [Field K] (A : Fin 2 → Polynomial K) (g : K) :
    Polynomial K :=
  A 0 + C g * A 1

def affineDegree {K : Type*} [Field K] (A : Fin 2 → Polynomial K) : ℕ :=
  max (A 0).natDegree (A 1).natDegree

structure CenteredVirtualData {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]
    (x : I ↪ K) (nodes : Finset I) (σ : K ≃+* K) (w agreement errors excess : ℕ) where
  seeds : Finset K
  zero_mem : 0 ∈ seeds
  selected : K → Polynomial K
  normalized : K → Polynomial K
  received : Fin 2 → I → K
  fixedWord : I → K
  A0 : Fin 2 → Polynomial K
  C1 : Polynomial K
  D1 : Polynomial K
  d0 : Polynomial K
  d1 : Polynomial K
  d0_ne : d0 ≠ 0
  d1_ne : d1 ≠ 0
  coprime_content : IsCoprime d0 d1
  coprime_A0 : IsCoprime (A0 0) (A0 1)
  degree_content : d1.natDegree = d0.natDegree
  support_le : d0.natDegree + affineDegree A0 ≤ excess
  degree_C1 : C1.natDegree ≤ w + d0.natDegree
  degree_D1 : D1.natDegree ≤ w + d1.natDegree
  content0_off_domain : ∀ i ∈ nodes, d0.eval (x i) ≠ 0
  content1_off_domain : ∀ i ∈ nodes, d1.eval (x i) ≠ 0
  active : ¬ d1 ∣ D1
  selected_degree : ∀ g ∈ seeds, (selected g).natDegree ≤ w
  normalized_degree : ∀ g ∈ seeds,
    (normalized g).natDegree ≤ w + d0.natDegree - affineDegree A0
  denominator_degree : ∀ g ∈ seeds,
    (specializeAffine A0 g).natDegree = affineDegree A0
  denominator_ne : ∀ g ∈ seeds, specializeAffine A0 g ≠ 0
  denominator_on_domain : ∀ g ∈ seeds, ∀ i ∈ nodes,
    (specializeAffine A0 g).eval (x i) ≠ 0
  coprime_denominator0 : ∀ g ∈ seeds, IsCoprime (specializeAffine A0 g) d0
  coprime_denominator1 : ∀ g ∈ seeds,
    IsCoprime ((specializeAffine A0 g).map σ.toRingHom) d1
  equation0 : ∀ g ∈ seeds,
    specializeAffine A0 g * normalized g = d0 * selected g + C g * C1
  equation1 : ∀ g ∈ seeds,
    (specializeAffine A0 g).map σ.toRingHom * normalized g =
      d1 * (selected g).map σ.toRingHom + C (σ g) * D1
  homogeneous : ∀ g ∈ seeds,
    d1 * (normalized g).map σ.toRingHom = d0.map σ.toRingHom * normalized g
  received_equation : ∀ i ∈ nodes, ∀ j : Fin 2,
    d0.eval (x i) * received j i + j.val * C1.eval (x i) =
      fixedWord i * (A0 j).eval (x i)
  agreements : ∀ g ∈ seeds,
    agreement ≤ (nodes.filter fun i =>
      (selected g).eval (x i) = received 0 i + g * received 1 i).card
  normalized_agreements : ∀ g ∈ seeds,
    agreement ≤ (nodes.filter fun i => (normalized g).eval (x i) = fixedWord i).card
  pencil : ∀ P0 P1 : Polynomial K, P0.natDegree ≤ w → P1.natDegree ≤ w →
    (seeds.filter fun g => selected g = P0 + C g * P1).card ≤ errors + 1

end ProximityPrize.SubmissionLower.Koala6844Normalization
