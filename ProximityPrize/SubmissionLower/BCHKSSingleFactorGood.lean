import ProximityPrize.SubmissionLower.BCHKSConcreteGoodSpecialization
import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpecialization
namespace ProximityPrize.SubmissionLower
open Polynomial
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {F : Type} [Field F] [Fintype F]

theorem exists_single_factor_primitive_base
    (R : Polynomial (Polynomial (Polynomial F))) (hR : Irreducible R)
    (hpos : 0 < R.natDegree) (hchar : R.natDegree < ringChar F)
    (w : ClearedPrimitiveCertificate F R)
    (hdeg : w.obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F) :
    ∃ x₀ : F, Polynomial.eval x₀ w.obstruction ≠ 0 ∧
      Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive := by
  classical
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  let ps : Bool → Polynomial (RatFunc F) := fun b => if b then
    w.obstruction.map (algebraMap F (RatFunc F)) else (factorXObstruction R).map g
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hobs : factorXObstruction R ≠ 0 := mul_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr hR.ne_zero)
    (rawSepResultant_ne_zero_of_irreducible (ringChar F) R hR hpos hchar)
  have hpne : ∀ b ∈ (Finset.univ : Finset Bool), ps b ≠ 0 := by
    intro b hb; cases b <;> simp [ps, w.obstruction_ne_zero, Polynomial.map_ne_zero_iff hg, hobs]
  have hd : (∑ b ∈ (Finset.univ : Finset Bool), (ps b).natDegree) < Fintype.card F := by
    simp [ps, Polynomial.natDegree_map_eq_of_injective hg, hdeg]
  obtain ⟨x₀, hx⟩ := exists_base_point_avoiding_ratfunc_polynomials
    (Finset.univ : Finset Bool) ps hpne hd
  have hp : Polynomial.eval x₀ w.obstruction ≠ 0 := by
    have hh := hx true (by simp)
    simpa [ps] using hh
  have ho : Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 := by
    intro hz
    have hh := hx false (by simp)
    apply hh
    simp only [ps, Bool.false_eq_true, if_false]
    rw [← Polynomial.eval₂_eq_eval_map]
    have heq : g (Polynomial.C x₀) = algebraMap F (RatFunc F) x₀ := by simp [g]
    rw [← heq, Polynomial.eval₂_hom, hz]
    exact map_zero _
  exact ⟨x₀, hp, ho, w.isPrimitive_of_eval_ne_zero x₀ hp⟩

/-- Effective-obstruction variant of `exists_single_factor_primitive_base`. -/
theorem exists_single_factor_primitive_base_effective
    (R : Polynomial (Polynomial (Polynomial F))) (hR : Irreducible R)
    (hpos : 0 < R.natDegree) (hchar : R.natDegree < ringChar F)
    (w : EffectivePrimitiveObstruction F R)
    (hdeg : w.obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F) :
    ∃ x₀ : F, Polynomial.eval x₀ w.obstruction ≠ 0 ∧
      Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive := by
  classical
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  let ps : Bool → Polynomial (RatFunc F) := fun b => if b then
    w.obstruction.map (algebraMap F (RatFunc F)) else (factorXObstruction R).map g
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hobs : factorXObstruction R ≠ 0 := mul_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr hR.ne_zero)
    (rawSepResultant_ne_zero_of_irreducible (ringChar F) R hR hpos hchar)
  have hpne : ∀ b ∈ (Finset.univ : Finset Bool), ps b ≠ 0 := by
    intro b hb; cases b <;> simp [ps, w.ne, Polynomial.map_ne_zero_iff hg, hobs]
  have hd : (∑ b ∈ (Finset.univ : Finset Bool), (ps b).natDegree) < Fintype.card F := by
    simp [ps, Polynomial.natDegree_map_eq_of_injective hg, hdeg]
  obtain ⟨x₀, hx⟩ := exists_base_point_avoiding_ratfunc_polynomials
    (Finset.univ : Finset Bool) ps hpne hd
  have hp : Polynomial.eval x₀ w.obstruction ≠ 0 := by
    have hh := hx true (by simp)
    simpa [ps] using hh
  have ho : Polynomial.eval (Polynomial.C x₀) (factorXObstruction R) ≠ 0 := by
    intro hz
    have hh := hx false (by simp)
    apply hh
    simp only [ps, Bool.false_eq_true, if_false]
    rw [← Polynomial.eval₂_eq_eval_map]
    have heq : g (Polynomial.C x₀) = algebraMap F (RatFunc F) x₀ := by simp [g]
    rw [← heq, Polynomial.eval₂_hom, hz]
    exact map_zero _
  exact ⟨x₀, hp, ho, w.property x₀ hp⟩

end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
open Polynomial
variable {F : Type} [Field F] [Fintype F]

/-- A single irreducible factor admits a primitive full-degree specialization;
outside a controlled set of `Z`-values all its rational roots are simple. -/
theorem exists_single_factor_good
    [DecidableEq F]
    (R : Polynomial (Polynomial (Polynomial F))) (hR : Irreducible R)
    (hpos : 0 < R.natDegree) (hchar : R.natDegree < ringChar F)
    (w : ClearedPrimitiveCertificate F R)
    (d DZ : ℕ)
    (hxcap : w.obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F)
    (hzcap : ∀ x : F,
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * d * DZ) :
    ∃ x₀ : F, ∃ Bad : Finset F,
      Bad.card ≤ 2 * d * DZ ∧
      (triSpecializeX R x₀).natDegree = R.natDegree ∧
      triSpecializeX R x₀ ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  obtain ⟨x₀, hw, hxObs, hprim⟩ :=
    exists_single_factor_primitive_base R hR hpos hchar w hxcap
  let zObs : Polynomial F :=
    Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)
  let Bad : Finset F := zObs.roots.toFinset
  have hzObs : zObs ≠ 0 := hxObs
  have hBadcard : Bad.card ≤ 2 * d * DZ := by
    dsimp [Bad]
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' zObs).trans (hzcap x₀))
  have hleadne : Polynomial.eval (Polynomial.C x₀) R.leadingCoeff ≠ 0 := by
    intro hlead
    apply hxObs
    rw [factorXObstruction, Polynomial.eval_mul, hlead, zero_mul]
  have hdegEq : (triSpecializeX R x₀).natDegree = R.natDegree := by
    apply le_antisymm (triSpecializeX_natDegree_le R x₀)
    apply Polynomial.le_natDegree_of_ne_zero
    simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
      Polynomial.leadingCoeff] using hleadne
  have hnonzero : triSpecializeX R x₀ ≠ 0 := by
    intro hz
    have : (triSpecializeX R x₀).natDegree = 0 := by rw [hz]; simp
    omega
  refine ⟨x₀, Bad, hBadcard, hdegEq, hnonzero, hprim, ?_⟩
  intro z hzBad y hy
  have hzO : Polynomial.eval z zObs ≠ 0 := by
    intro hz
    apply hzBad
    dsimp [Bad]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hzObs]
    exact hz
  have hresEval : Polynomial.eval z
      (Polynomial.eval (Polynomial.C x₀) (rawSepResultant R)) ≠ 0 := by
    intro hzres
    apply hzO
    dsimp [zObs]
    rw [factorXObstruction, Polynomial.eval_mul, Polynomial.eval_mul, hzres, mul_zero]
  have hresX : Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) =
      Polynomial.resultant (triSpecializeX R x₀)
        (triSpecializeX R.derivative x₀)
        R.natDegree (R.natDegree - 1) := by
    simp [rawSepResultant, triSpecializeX, Polynomial.derivative_map]
  have hder : triSpecializeX R.derivative x₀ =
      (triSpecializeX R x₀).derivative := by
    simp [triSpecializeX, Polynomial.derivative_map]
  have hresB : Polynomial.eval z
      (Polynomial.resultant (triSpecializeX R x₀)
        (triSpecializeX R x₀).derivative
        (triSpecializeX R x₀).natDegree
        ((triSpecializeX R x₀).natDegree - 1)) ≠ 0 := by
    rw [hdegEq, ← hder, ← hresX]
    exact hresEval
  have hsimple := simple_root_of_fixed_resultant_eval_ne_zero
    (triSpecializeX R x₀) z y (by rw [hdegEq]; exact hpos) hresB hy
  rw [← hder] at hsimple
  exact hsimple


/-- Effective-obstruction overload of the single-factor good specialization. -/
theorem exists_single_factor_good_effective
    [DecidableEq F]
    (R : Polynomial (Polynomial (Polynomial F))) (hR : Irreducible R)
    (hpos : 0 < R.natDegree) (hchar : R.natDegree < ringChar F)
    (w : EffectivePrimitiveObstruction F R)
    (d DZ : ℕ)
    (hxcap : w.obstruction.natDegree + (factorXObstruction R).natDegree < Fintype.card F)
    (hzcap : ∀ x : F,
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * d * DZ) :
    ∃ x₀ : F, ∃ Bad : Finset F,
      Bad.card ≤ 2 * d * DZ ∧
      (triSpecializeX R x₀).natDegree = R.natDegree ∧
      triSpecializeX R x₀ ≠ 0 ∧
      (triSpecializeX R x₀).IsPrimitive ∧
      (∀ z ∉ Bad, ∀ y,
        Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
        Polynomial.eval y
          (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0) := by
  classical
  obtain ⟨x₀, hw, hxObs, hprim⟩ :=
    exists_single_factor_primitive_base_effective R hR hpos hchar w hxcap
  let zObs : Polynomial F :=
    Polynomial.eval (Polynomial.C x₀) (factorXObstruction R)
  let Bad : Finset F := zObs.roots.toFinset
  have hzObs : zObs ≠ 0 := hxObs
  have hBadcard : Bad.card ≤ 2 * d * DZ := by
    dsimp [Bad]
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' zObs).trans (hzcap x₀))
  have hleadne : Polynomial.eval (Polynomial.C x₀) R.leadingCoeff ≠ 0 := by
    intro hlead
    apply hxObs
    rw [factorXObstruction, Polynomial.eval_mul, hlead, zero_mul]
  have hdegEq : (triSpecializeX R x₀).natDegree = R.natDegree := by
    apply le_antisymm (triSpecializeX_natDegree_le R x₀)
    apply Polynomial.le_natDegree_of_ne_zero
    simpa only [triSpecializeX, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
      Polynomial.leadingCoeff] using hleadne
  have hnonzero : triSpecializeX R x₀ ≠ 0 := by
    intro hz
    have : (triSpecializeX R x₀).natDegree = 0 := by rw [hz]; simp
    omega
  refine ⟨x₀, Bad, hBadcard, hdegEq, hnonzero, hprim, ?_⟩
  intro z hzBad y hy
  have hzO : Polynomial.eval z zObs ≠ 0 := by
    intro hz
    apply hzBad
    dsimp [Bad]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hzObs]
    exact hz
  have hresEval : Polynomial.eval z
      (Polynomial.eval (Polynomial.C x₀) (rawSepResultant R)) ≠ 0 := by
    intro hzres
    apply hzO
    dsimp [zObs]
    rw [factorXObstruction, Polynomial.eval_mul, Polynomial.eval_mul, hzres, mul_zero]
  have hresX : Polynomial.eval (Polynomial.C x₀) (rawSepResultant R) =
      Polynomial.resultant (triSpecializeX R x₀)
        (triSpecializeX R.derivative x₀)
        R.natDegree (R.natDegree - 1) := by
    simp [rawSepResultant, triSpecializeX, Polynomial.derivative_map]
  have hder : triSpecializeX R.derivative x₀ =
      (triSpecializeX R x₀).derivative := by
    simp [triSpecializeX, Polynomial.derivative_map]
  have hresB : Polynomial.eval z
      (Polynomial.resultant (triSpecializeX R x₀)
        (triSpecializeX R x₀).derivative
        (triSpecializeX R x₀).natDegree
        ((triSpecializeX R x₀).natDegree - 1)) ≠ 0 := by
    rw [hdegEq, ← hder, ← hresX]
    exact hresEval
  have hsimple := simple_root_of_fixed_resultant_eval_ne_zero
    (triSpecializeX R x₀) z y (by rw [hdegEq]; exact hpos) hresB hy
  rw [← hder] at hsimple
  exact hsimple

end ProximityPrize.SubmissionLower
