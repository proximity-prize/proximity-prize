import ProximityPrize.SubmissionLower.Koala6844VirtualHighPolePower
import ProximityPrize.SubmissionLower.Koala6831IntrinsicH2
import Mathlib.FieldTheory.KummerPolynomial


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
open RCN022 RCN344 Koala6831Intrinsic

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option linter.style.haveILetI false

variable {K E : Type} [Field K] [Field E] [Algebra K E]

def parameterDegree (x : E) : ℕ :=
  Module.finrank (IntermediateField.adjoin K ({x} : Set E)) E

theorem degree_eq_finrank_parameter (x : E) (hx : Transcendental K x) :
    letI := (elementEmbedding K E x hx).toRingHom.toAlgebra
    Module.finrank (RatFunc K) E = parameterDegree (K := K) x := by
  letI := (elementEmbedding K E x hx).toRingHom.toAlgebra
  let e := RatFunc.algEquivOfTranscendental x hx
  apply Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl E)
  apply RingHom.ext
  intro z
  change (e z : E) = elementEmbedding K E x hx z
  rw [elementEmbedding_eq_adjoin_comp]
  rfl

theorem parameterDegree_pow (p : ℕ) [ExpChar K p] (hp : p.Prime)
    (u : E) (hx : Transcendental K (u ^ p)) :
    parameterDegree (K := K) (u ^ p) = p * parameterDegree (K := K) u := by
  let F := IntermediateField.adjoin K ({u ^ p} : Set E)
  let U := IntermediateField.adjoin K ({u} : Set E)
  let x : F := ⟨u ^ p, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  let e : RatFunc K ≃ₐ[K] F := RatFunc.algEquivOfTranscendental (u ^ p) hx
  letI : ExpChar (RatFunc K) p :=
    expChar_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
  have hex : e RatFunc.X = x := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X (u ^ p) hx
  have hn (b : F) : b ^ p ≠ x := by
    intro hb
    apply ratFunc_X_ne_pow p hp (e.symm b)
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hb, hex]
  let P : Polynomial F := Polynomial.X ^ p - Polynomial.C x
  have hP : Irreducible P := X_pow_sub_C_irreducible_of_prime hp hn
  have hmon : P.Monic := Polynomial.monic_X_pow_sub_C x hp.ne_zero
  have hroot : Polynomial.aeval u P = 0 := by
    simp [P, x]
  have hInt : IsIntegral F u := ⟨P, hmon, hroot⟩
  let L := IntermediateField.adjoin F ({u} : Set E)
  have hdeg : Module.finrank F L = p := by
    rw [IntermediateField.adjoin.finrank hInt,
      ← minpoly.eq_of_irreducible_of_monic hP hroot hmon,
      Polynomial.natDegree_X_pow_sub_C]
  have hFU : F ≤ U := by
    apply IntermediateField.adjoin_simple_le_iff.mpr
    exact U.toSubfield.toSubring.pow_mem
      (IntermediateField.subset_adjoin K ({u} : Set E) (Set.mem_singleton u)) p
  have hL : L.restrictScalars K = U := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    exact sup_eq_right.mpr hFU
  have hrank : Module.finrank L E = Module.finrank U E := by
    change Module.finrank (L.restrictScalars K) E = Module.finrank U E
    rw [hL]
  change Module.finrank F E = p * Module.finrank U E
  rw [← hrank, ← hdeg, Module.finrank_mul_finrank F L E]

theorem separating_power_parameter (p : ℕ) [ExpChar K p] [ExpChar E p]
    [PerfectRing K p] (hp : p.Prime) (s : E) (hs : Transcendental K s)
    (seedFinite : letI := (elementEmbedding K E s hs).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) E)
    (seedSeparable : letI := (elementEmbedding K E s hs).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) E)
    (x : E) (hx : Transcendental K x) :
    ∃ (c : SeparableCoordinate K E) (n : ℕ),
      c.value K E ^ n = x ∧ n * c.degree K E = parameterDegree (K := K) x := by
  classical
  have finiteParameter (v : E) (hv : Transcendental K v) :
      letI := (elementEmbedding K E v hv).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) E :=
    finiteDimensional_elementEmbedding K E _ seedFinite v hv
  suffices aux : ∀ d : ℕ, ∀ v : E, Transcendental K v →
      parameterDegree (K := K) v = d →
      ∃ (c : SeparableCoordinate K E) (n : ℕ),
        c.value K E ^ n = v ∧ n * c.degree K E = d from
    aux _ x hx rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro v hv hd
    by_cases hn : v ∈ powerField E p
    · obtain ⟨u, hu⟩ := mem_powerField_iff.mp hn
      have hut : Transcendental K u := fun h => hv (hu ▸ h.pow p)
      have step : parameterDegree (K := K) v = p * parameterDegree (K := K) u := by
        rw [← hu]
        exact parameterDegree_pow p hp u (hu.symm ▸ hv)
      have hpos : 0 < parameterDegree (K := K) u := by
        letI := (elementEmbedding K E u hut).toRingHom.toAlgebra
        letI := finiteParameter u hut
        rw [← degree_eq_finrank_parameter u hut]
        exact Module.finrank_pos
      have hlt : parameterDegree (K := K) u < d := by
        rw [← hd, step]
        have h := Nat.mul_lt_mul_of_pos_right hp.one_lt hpos
        simpa using h
      obtain ⟨c, n, hvalue, hdegree⟩ := ih _ hlt u hut rfl
      refine ⟨c, n * p, ?_, ?_⟩
      · rw [pow_mul, hvalue, hu]
      · rw [← hd, step, ← hdegree]
        ac_rfl
    · let c : SeparableCoordinate K E :=
        ⟨elementEmbedding K E v hv, finiteParameter v hv,
          separable_affine_projection_from_seed p hp s v hs hv hn seedSeparable
            (finiteParameter v hv)⟩
      refine ⟨c, 1, ?_, ?_⟩
      · rw [pow_one]
        exact elementEmbedding_variable K E v hv
      · rw [one_mul, ← hd]
        exact degree_eq_finrank_parameter v hv

open RCN002 RCN007 RCN187 RCN341

theorem finite_pole_sum_le_actualCoordinateDegree [IsAlgClosed K]
    (p : ℕ) [ExpChar K p] [PerfectRing K p] (hp : p.Prime)
    (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (seed : SeparableLiteralCoordinate P) (i : Fin 3)
    (W : Finset (Place K (CoordinateField K P))) :
    (∑ v ∈ W, poleOrder v.val (coordinate K P i)) ≤
      (actualCoordinateDegree K P i : ℤ) := by
  classical
  let L := CoordinateField K P
  letI : ExpChar L p := expChar_of_injective_algebraMap
    (algebraMap K L).injective p
  by_cases hi : Transcendental K (coordinate K P i)
  · obtain ⟨c, n, hpower, hdegree⟩ := separating_power_parameter p hp
      (coordinate K P seed.index) seed.transcendental seed.finite seed.separable
      (coordinate K P i) hi
    have hd : actualCoordinateDegree K P i =
        parameterDegree (K := K) (coordinate K P i) := by
      rw [actualCoordinateDegree_of_transcendental _ _ _ hi]
      exact degree_eq_finrank_parameter (coordinate K P i) hi
    exact finite_pole_sum_le_of_separating_power c _ n _ hpower
      (by rw [hdegree, hd]) W
  · change ¬ ¬ IsAlgebraic K (coordinate K P i) at hi
    obtain ⟨a, ha⟩ := coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)
    have zero (v : Place K L) : poleOrder v.val (coordinate K P i) = 0 := by
      rw [← ha]
      exact RCN346.poleOrder_eq_zero_of_le_one K L v _
        (constant_value_le_one K L v a)
    simp only [zero, Finset.sum_const_zero, Nat.cast_nonneg]

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh


