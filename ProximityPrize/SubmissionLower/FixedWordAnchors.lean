/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.FixedWordGenerator
import ProximityPrize.SubmissionLower.Koala6844ActiveGerm
import Mathlib.RingTheory.EuclideanDomain

namespace ProximityPrize.SubmissionLower.FixedWordAnchors
open Polynomial Koala6844Normalization
open scoped Classical
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w A errors excess : ℕ}

structure Model (data : CenteredVirtualData x nodes σ w A errors excess) where
  generator : K[X]
  pole : K[X]
  carrier : K[X]
  offset : K[X]
  words : K → K[X]
  received : I → K
  generator_ne : generator ≠ 0
  pole_nonzero : pole ≠ 0
  pole_divides : pole ∣ data.d0
  adjacent_divides : pole.map σ.toRingHom ∣ data.d1
  adjacent_coprime : IsCoprime pole (pole.map σ.toRingHom)
  carrier_coprime : IsCoprime carrier pole
  degree_balance : data.d0.natDegree + carrier.natDegree = pole.natDegree + generator.natDegree
  fixed : ∀ g ∈ data.seeds, (words g).map σ.toRingHom = words g
  injective : Set.InjOn words (↑data.seeds : Set K)
  degree : ∀ g ∈ data.seeds,
    (words g).natDegree ≤ w + data.d0.natDegree - affineDegree data.A0 - generator.natDegree
  agreements : ∀ g ∈ data.seeds,
    A ≤ (nodes.filter fun i => (words g).eval (x i) = received i).card
  equation : ∀ g ∈ data.seeds,
    specializeAffine data.A0 g * carrier * words g = pole * data.selected g + C g * offset

local instance : GCDMonoid K[X] := EuclideanDomain.gcdMonoid _

/-- Division by a minimal twisted solution gives an injective fixed-word list and
two coprime adjacent pole constraints for the original decoders. -/
theorem exists_model (data : CenteredVirtualData x nodes σ w A errors excess)
    (points_fixed : ∀ i ∈ nodes, σ (x i) = x i) (many : 1 < data.seeds.card) :
    Nonempty (Model data) := by
  classical
  have introSol (g : K) (hg : g ∈ data.seeds) :
      FixedWordGenerator.Solution σ data.d1 (data.d0.map σ.toRingHom) (data.normalized g) :=
    data.homogeneous g hg
  have anySol : ∃ P : K[X], P ≠ 0 ∧ FixedWordGenerator.Solution σ data.d1 (data.d0.map σ.toRingHom) P := by
    by_contra! hall
    apply many.not_ge (Finset.card_le_one.mpr ?_)
    intro g hg k hk
    apply Koala6844ActiveGerm.normalized_injOn data hg hk
    have hz (v : K) (hv : v ∈ data.seeds) : data.normalized v = 0 := by
      by_contra hn
      exact hall _ hn (introSol v hv)
    rw [hz g hg,hz k hk]
  obtain ⟨T,hn,hT,off,factors⟩ := FixedWordGenerator.exists_generator σ data.d1
    (data.d0.map σ.toRingHom) data.d1_ne anySol
  let G := GCDMonoid.gcd data.d0 T
  let E := data.d0 / G
  let B := T / G
  have hG : G ≠ 0 := gcd_ne_zero_of_left data.d0_ne
  have hE : G*E = data.d0 := EuclideanDomain.mul_div_cancel' hG (gcd_dvd_left _ _)
  have hB : G*B = T := EuclideanDomain.mul_div_cancel' hG (gcd_dvd_right _ _)
  have hEn : E ≠ 0 := fun h => data.d0_ne (by rw [← hE,h,mul_zero])
  have hBn : B ≠ 0 := fun h => hn (by rw [← hB,h,mul_zero])
  have cop : IsCoprime E B := isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hG
  have divides : E ∣ data.d0 := ⟨G,by rw [mul_comm,hE]⟩
  have heq : data.d1 * B.map σ.toRingHom = E.map σ.toRingHom * T := by
    unfold FixedWordGenerator.Solution at hT
    rw [← hB,Polynomial.map_mul, ← hE, Polynomial.map_mul] at hT
    apply mul_left_cancel₀ (show G.map σ.toRingHom ≠ 0 by simpa using hG)
    calc
      _ = data.d1 * (G.map σ.toRingHom * B.map σ.toRingHom) := by ring
      _ = G.map σ.toRingHom * E.map σ.toRingHom * (G*B) := hT
      _ = _ := by rw [hB]; ring
  have nextPole : E.map σ.toRingHom ∣ data.d1 :=
    ((isCoprime_map σ.toRingHom).mpr cop).dvd_of_dvd_mul_right ⟨T,heq⟩
  let word (g : K) := data.normalized g / T
  have rep (g : K) (hg : g ∈ data.seeds) :
      (word g).map σ.toRingHom = word g ∧ T*word g = data.normalized g := by
    obtain ⟨S,fixed,equation⟩ := factors _ (introSol g hg)
    have same : word g = S := by
      change data.normalized g / T = S
      rw [equation,mul_div_cancel_left₀ _ hn]
    exact ⟨same ▸ fixed, by rw [same,equation]⟩
  obtain ⟨z,hz,nonzero⟩ : ∃ z ∈ data.seeds, z ≠ 0 := by
    by_contra! hall
    exact many.not_ge (Finset.card_le_one.mpr fun g hg k hk => (hall g hg).trans (hall k hk).symm)
  have leftDiv (g : K) (hg : g ∈ data.seeds) : G ∣ C g * data.C1 := by
    have eqn := data.equation0 g hg
    rw [← (rep g hg).2, ← hB, ← hE] at eqn
    refine ⟨specializeAffine data.A0 g * B * word g - E*data.selected g, ?_⟩
    linear_combination -eqn
  have unit : IsCoprime G (C z) := ⟨0,C z⁻¹,by simp [← C_mul,nonzero]⟩
  have divQ : G ∣ data.C1 := unit.dvd_of_dvd_mul_left (leftDiv z hz)
  obtain ⟨Q,hQ⟩ := divQ
  refine ⟨{ generator := T, pole := E, carrier := B, offset := Q, words := word,
            received := fun i => data.fixedWord i / T.eval (x i), generator_ne := hn,
            pole_nonzero := hEn, pole_divides := divides, adjacent_divides := nextPole,
            adjacent_coprime := (data.coprime_content.of_isCoprime_of_dvd_left divides).of_isCoprime_of_dvd_right nextPole,
            carrier_coprime := cop.symm, degree_balance := ?_, fixed := fun g hg => (rep g hg).1,
            injective := ?_, degree := ?_, agreements := ?_, equation := ?_ }⟩
  · rw [← hE, ← hB,natDegree_mul hG hEn,natDegree_mul hG hBn]
    omega
  · intro g hg k hk h
    apply Koala6844ActiveGerm.normalized_injOn data hg hk
    rw [← (rep g hg).2,← (rep k hk).2,h]
  · intro g hg
    by_cases h : word g = 0
    · simp [h]
    have hd := congrArg Polynomial.natDegree (rep g hg).2
    rw [natDegree_mul hn h] at hd
    have old := data.normalized_degree g hg
    omega
  · intro g hg
    apply (data.normalized_agreements g hg).trans (Finset.card_le_card ?_)
    intro i hi
    obtain ⟨hin,hw⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hin,(eq_div_iff (off _ (points_fixed _ hin))).mpr ?_⟩
    rw [mul_comm,← eval_mul,(rep g hg).2]
    exact hw
  · intro g hg
    have eqn := data.equation0 g hg
    rw [← (rep g hg).2,← hB,← hE,hQ] at eqn
    apply mul_left_cancel₀ hG
    linear_combination eqn

/-- The two residue equations hold to the full multiplicities of the divisors. -/
theorem Model.contacts {data : CenteredVirtualData x nodes σ w A errors excess} (m : Model data)
    (g : K) (hg : g ∈ data.seeds) :
    m.pole ∣ specializeAffine data.A0 g * m.carrier * m.words g - C g * m.offset ∧
    m.pole.map σ.toRingHom ∣ (specializeAffine data.A0 g * m.carrier).map σ.toRingHom *
      m.words g - C (σ g) * m.offset.map σ.toRingHom := by
  have heq := m.equation g hg
  constructor
  · exact ⟨data.selected g,by rw [heq]; ring⟩
  · refine ⟨(data.selected g).map σ.toRingHom, ?_⟩
    have h := congrArg (Polynomial.map σ.toRingHom) heq
    simp only [Polynomial.map_add,Polynomial.map_mul,map_C,m.fixed g hg] at h
    change (specializeAffine data.A0 g).map σ.toRingHom * m.carrier.map σ.toRingHom * m.words g =
      m.pole.map σ.toRingHom * (data.selected g).map σ.toRingHom + C (σ g) * m.offset.map σ.toRingHom at h
    rw [Polynomial.map_mul]
    linear_combination h

#print axioms exists_model
#print axioms Model.contacts
end
end ProximityPrize.SubmissionLower.FixedWordAnchors
