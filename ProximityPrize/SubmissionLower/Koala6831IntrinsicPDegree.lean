import ProximityPrize.SubmissionLower.Koala6831IntrinsicPowers

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

variable {K E : Type*} [Field K] [Field E]

private theorem adjoin_powerField_singleton_eq_top_of_base [Algebra K E] (p : ℕ)
    [ExpChar K p] [ExpChar E p] [Algebra.IsSeparable K E] (z : E)
    (hbase : ∀ c : K, algebraMap K E c ∈
      IntermediateField.adjoin (powerField E p) ({z} : Set E)) :
    IntermediateField.adjoin (powerField E p) ({z} : Set E) = ⊤ := by
  let A := IntermediateField.adjoin (powerField E p) ({z} : Set E)
  let D : IntermediateField K E := A.toSubfield.toIntermediateField hbase
  have hgen : IntermediateField.adjoin K (Set.range (fun x : E => x ^ p)) = ⊤ := by
    rw [← Set.image_univ, ← IntermediateField.adjoin_eq_adjoin_pow_expChar_of_isSeparable'
      K E (Set.univ : Set E) p, IntermediateField.adjoin_univ]
  have hle : IntermediateField.adjoin K (Set.range (fun x : E => x ^ p)) ≤ D := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨x, rfl⟩
    exact A.algebraMap_mem ⟨x ^ p, pow_mem_powerField p x⟩
  apply eq_top_iff.mpr
  intro x _
  exact hle (by rw [hgen]; exact IntermediateField.mem_top)

theorem adjoin_powerField_singleton_eq_top_of_ratFunc [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] (p : ℕ)
    [ExpChar (RatFunc K) p] [ExpChar E p] [PerfectRing K p]
    [Algebra.IsSeparable (RatFunc K) E] :
    IntermediateField.adjoin (powerField E p)
      ({algebraMap (RatFunc K) E RatFunc.X} : Set E) = ⊤ := by
  let z := algebraMap (RatFunc K) E (RatFunc.X : RatFunc K)
  let A := IntermediateField.adjoin (powerField E p) ({z} : Set E)
  have hz : z ∈ A :=
    IntermediateField.subset_adjoin (powerField E p) ({z} : Set E) (Set.mem_singleton z)
  have hC (c : K) : algebraMap K E c ∈ A :=
    A.algebraMap_mem ⟨algebraMap K E c, algebraMap_mem_powerField p c⟩
  have hpoly (f : Polynomial K) :
      algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) f) ∈ A := by
    induction f using Polynomial.induction_on' with
    | add f g hf hg =>
      simpa only [map_add] using A.add_mem hf hg
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow,
        RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C,
        ← IsScalarTower.algebraMap_apply K (RatFunc K) E]
      change algebraMap K E c * z ^ n ∈ A
      exact A.mul_mem (hC c) (pow_mem hz n)
  apply adjoin_powerField_singleton_eq_top_of_base (K := RatFunc K) p z
  intro f
  rw [← RatFunc.num_div_denom f, map_div₀]
  exact A.div_mem (hpoly f.num) (hpoly f.denom)

theorem isIntegral_powerField (p : ℕ) [ExpChar E p] (z : E) :
    IsIntegral (powerField E p) z := by
  let a : powerField E p := ⟨z ^ p, pow_mem_powerField p z⟩
  have hp : p ≠ 0 := by
    cases (show ExpChar E p from inferInstance) with
    | zero => exact one_ne_zero
    | prime h => exact h.ne_zero
  refine ⟨Polynomial.X ^ p - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hp, ?_⟩
  change (Polynomial.aeval z) (Polynomial.X ^ p - Polynomial.C a) = 0
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  change z ^ p - z ^ p = 0
  exact sub_self _

theorem finiteDimensional_powerField (p : ℕ) [ExpChar E p] (z : E)
    (hgen : IntermediateField.adjoin (powerField E p) ({z} : Set E) = ⊤) :
    FiniteDimensional (powerField E p) E :=
  (PowerBasis.ofAdjoinSimpleEqTop (isIntegral_powerField p z) hgen).finite

theorem finrank_powerField (p : ℕ) [ExpChar E p] (hp : p.Prime) (z : E)
    (hz : z ∉ powerField E p)
    (hgen : IntermediateField.adjoin (powerField E p) ({z} : Set E) = ⊤) :
    Module.finrank (powerField E p) E = p := by
  let b := PowerBasis.ofAdjoinSimpleEqTop (isIntegral_powerField p z) hgen
  rw [Module.finrank_eq_card_basis b.basis, Fintype.card_fin]
  exact (PowerBasis.ofAdjoinSimpleEqTop_dim _ _).trans (minpoly_powerField_degree p hp z hz)

theorem adjoin_powerField_singleton_eq_top_of_finrank (p : ℕ) [ExpChar E p]
    [FiniteDimensional (powerField E p) E] (hp : p.Prime) (z : E)
    (hz : z ∉ powerField E p) (hdeg : Module.finrank (powerField E p) E = p) :
    IntermediateField.adjoin (powerField E p) ({z} : Set E) = ⊤ := by
  let A := powerField E p
  let F : IntermediateField (↥A) E := IntermediateField.adjoin (↥A) ({z} : Set E)
  have hF : Module.finrank (↥A) (↥F) = p :=
    (IntermediateField.adjoin.finrank (isIntegral_powerField p z)).trans
      (minpoly_powerField_degree p hp z hz)
  have hprod := Module.finrank_mul_finrank (↥A) (↥F) E
  rw [hF, hdeg] at hprod
  have hEF : Module.finrank (↥F) E = 1 :=
    Nat.eq_of_mul_eq_mul_left hp.pos (hprod.trans (Nat.mul_one p).symm)
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp hEF

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
