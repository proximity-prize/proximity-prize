import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedProjection6600Research
import ProximityPrize.SubmissionLower.ContactFlagProjectionPositivity6543Research
import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactWeakSeparableSeparatorResearch

/-!
# Characteristic-free terminal literal projection

A safe literal-`Z` gate and survival of the surface `S` derivative provide a
finite-separable literal normalization on every retained regular component.
No literal-`Y` resultant or mixed-degree characteristic gate is used.
-/

namespace ProximityPrize.SubmissionLower.CharFreeTerminal

open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualPlaneCoordinateKernel
open ContactRegularComponentCover ContactWeakSeparableSeparatorResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveProjectionCoordinateResearch
open ContactFlagProjectionPositivity6543Research
open ContactGenericSurface ContactProperCutSeedCount ContactRegularFactorGate

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]

/-- A polynomial relation whose derivative is nonzero at the root makes the
root separable, without any degree/characteristic hypothesis. -/
theorem isSeparable_of_aeval_derivative_ne_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (f : Polynomial F)
    (hf : f ≠ 0) (hroot : Polynomial.aeval x f = 0)
    (hderiv : Polynomial.aeval x f.derivative ≠ 0) :
    IsSeparable F x := by
  have hxint : IsIntegral F x :=
    IsAlgebraic.isIntegral ⟨f, hf, hroot⟩
  have hm : minpoly F x ∣ f := minpoly.dvd F x hroot
  have hmderiv : (minpoly F x).derivative ≠ 0 := by
    intro hzero
    obtain ⟨q, rfl⟩ := hm
    apply hderiv
    simp [Polynomial.derivative_mul, hzero, minpoly.aeval F x]
  exact (Polynomial.separable_iff_derivative_ne_zero
    (minpoly.irreducible hxint)).2 hmderiv

variable {G T H Surface : MvPolynomial (Fin 3) Omega}

/-- On a retained regular component, if `Surface = G*Q` and
`H = dSurface/dS`, then `dG/dS` cannot vanish in the component prime. -/
theorem pderiv_one_not_mem_of_regular_factor
    (P : Ideal (MvPolynomial (Fin 3) Omega))
    (hGmem : G ∈ P) (hHnot : H ∉ P)
    (hfactor : G ∣ Surface)
    (hH : H = MvPolynomial.pderiv (1 : Fin 3) Surface) :
    MvPolynomial.pderiv (1 : Fin 3) G ∉ P := by
  rintro hGp
  obtain ⟨Q, rfl⟩ := hfactor
  apply hHnot
  rw [hH, MvPolynomial.pderiv_mul]
  exact P.add_mem (P.mul_mem_right _ hGp) (P.mul_mem_right _ hGmem)

/-- If `Y` is transcendental, `Z` is constant over the algebraically closed
base, and the `S`-partial of a relation survives in the prime quotient, then
the literal `Y` projection is finite separable in every characteristic. -/
theorem finite_separable_at_Y_of_Z_algebraic
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (G : MvPolynomial (Fin 3) Omega)
    (hGmem : G ∈ P)
    (hGderiv : MvPolynomial.pderiv (1 : Fin 3) G ∉ P)
    (hY : Transcendental Omega (coordinate Omega P 0))
    (hZ : IsAlgebraic Omega (coordinate Omega P 2)) :
    letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
      rationalBaseAlgebra Omega P 0 hY
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) ∧
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := by
  let L := CoordinateField Omega P
  let y : L := coordinate Omega P 0
  let s : L := coordinate Omega P 1
  let z : L := coordinate Omega P 2
  letI : Algebra (RatFunc Omega) L := rationalBaseAlgebra Omega P 0 hY
  letI : IsScalarTower Omega (RatFunc Omega) L :=
    rationalBaseScalarTower Omega P 0 hY
  obtain ⟨c, hc⟩ := coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZ
  let z0 : RatFunc Omega := algebraMap Omega (RatFunc Omega) c
  let coeffEval : Polynomial (RatFunc Omega) →+* RatFunc Omega :=
    Polynomial.evalRingHom z0
  let order : Fin 3 ≃ Fin 3 := Equiv.refl (Fin 3)
  let f : Polynomial (RatFunc Omega) := (planeMap Omega order G).map coeffEval
  have hcoeff :
      (algebraMap (RatFunc Omega) L).comp coeffEval =
        Polynomial.eval₂RingHom
          (rationalBaseEmbedding Omega P 0 hY).toRingHom z := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, coeffEval, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change rationalBaseEmbedding Omega P 0 hY a =
        rationalBaseEmbedding Omega P 0 hY a
      rfl
    · simp only [RingHom.comp_apply, coeffEval, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      change algebraMap (RatFunc Omega) L z0 = z
      change algebraMap (RatFunc Omega) L
          (algebraMap Omega (RatFunc Omega) c) = coordinate Omega P 2
      exact (IsScalarTower.algebraMap_apply Omega (RatFunc Omega) L c).symm.trans hc
  have heval (A : PlaneRing Omega) :
      Polynomial.aeval s (A.map coeffEval) =
        actualPlaneEvaluation Omega order P hY A := by
    change Polynomial.eval₂ (algebraMap (RatFunc Omega) L) s
        (A.map coeffEval) = _
    rw [Polynomial.eval₂_map, hcoeff]
    simp [actualPlaneEvaluation, Polynomial.eval₂_eq_eval_map, order, s, z]
  have hfroot : Polynomial.aeval s f = 0 := by
    rw [show Polynomial.aeval s f =
        actualPlaneEvaluation Omega order P hY (planeMap Omega order G) by
      exact heval (planeMap Omega order G)]
    exact (actualPlane_root_iff Omega order P hY G).2 hGmem
  have hfderiv : Polynomial.aeval s f.derivative ≠ 0 := by
    have hmap : f.derivative =
        (planeMap Omega order (MvPolynomial.pderiv (1 : Fin 3) G)).map coeffEval := by
      simp only [f, Polynomial.derivative_map]
      rw [derivative_planeMap]
      rfl
    rw [hmap, heval]
    exact fun hzero => hGderiv
      ((actualPlane_root_iff Omega order P hY
        (MvPolynomial.pderiv (1 : Fin 3) G)).1 hzero)
  have hfne : f ≠ 0 := by
    intro hzero
    apply hfderiv
    simp [hzero]
  have hssep : IsSeparable (RatFunc Omega) s :=
    isSeparable_of_aeval_derivative_ne_zero s f hfne hfroot hfderiv
  have hsint : IsIntegral (RatFunc Omega) s := hssep.isIntegral
  have hzbot : z ∈ (⊥ : IntermediateField (RatFunc Omega) L) := by
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap Omega (RatFunc Omega) c, ?_⟩
    rw [← IsScalarTower.algebraMap_apply Omega (RatFunc Omega) L]
    exact hc
  have hpair : IntermediateField.adjoin (RatFunc Omega) ({z, s} : Set L) = ⊤ := by
    simpa only [order, Equiv.refl_apply] using
      (adjoin_two_coordinates_over_ratFunc_eq_top Omega P 0 2 1 hY
        (by intro i; fin_cases i <;> simp))
  have hsingle : IntermediateField.adjoin (RatFunc Omega) ({s} : Set L) = ⊤ := by
    apply top_unique
    rw [← hpair]
    apply IntermediateField.adjoin_le_iff.mpr
    intro a ha
    rcases ha with (rfl | ha)
    · exact (bot_le : (⊥ : IntermediateField (RatFunc Omega) L) ≤
        IntermediateField.adjoin (RatFunc Omega) ({s} : Set L)) hzbot
    · have : a = s := Set.mem_singleton_iff.mp ha
      subst a
      exact IntermediateField.subset_adjoin (RatFunc Omega) {s}
        (Set.mem_singleton s)
  let A : IntermediateField (RatFunc Omega) L :=
    IntermediateField.adjoin (RatFunc Omega) ({s} : Set L)
  letI : FiniteDimensional (RatFunc Omega) A :=
    IntermediateField.adjoin.finiteDimensional hsint
  have hfinite : FiniteDimensional (RatFunc Omega) L := by
    letI : FiniteDimensional (RatFunc Omega)
        (⊤ : IntermediateField (RatFunc Omega) L) := by
      rw [← hsingle]
      infer_instance
    exact Module.Finite.of_surjective
      (IntermediateField.topEquiv (F := RatFunc Omega) (E := L)).toLinearMap
      (IntermediateField.topEquiv (F := RatFunc Omega) (E := L)).surjective
  letI : FiniteDimensional (RatFunc Omega) L := hfinite
  have hsepA : Algebra.IsSeparable (RatFunc Omega) A :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (RatFunc Omega) L).2 hssep
  have hsepTop : Algebra.IsSeparable (RatFunc Omega)
      (⊤ : IntermediateField (RatFunc Omega) L) := by
    rw [← hsingle]
    exact hsepA
  letI : Algebra.IsSeparable (RatFunc Omega)
      (⊤ : IntermediateField (RatFunc Omega) L) := hsepTop
  have hsepL : Algebra.IsSeparable (RatFunc Omega) L :=
    AlgEquiv.Algebra.isSeparable
      (IntermediateField.topEquiv (F := RatFunc Omega) (E := L))
  exact ⟨hfinite, hsepL⟩

/-- A safe literal-`Z` gate plus survival of the surface `S` derivative
supplies one literal finite-separable coordinate on every retained regular
component. -/
theorem exists_separableLiteralCoordinate_of_Z_gate_regular_factor
    {G T H Surface : MvPolynomial (Fin 3) Omega}
    (C : RegularComponent Omega G T H)
    (hfactor : G ∣ Surface)
    (hH : H = MvPolynomial.pderiv (1 : Fin 3) Surface)
    (hZgate : LiteralProjectionGate C 2) :
    Nonempty (SeparableLiteralCoordinate C.1) := by
  by_cases hz : Transcendental Omega (coordinate Omega C.1 2)
  · exact ⟨⟨2, hz, (hZgate hz).1, (hZgate hz).2⟩⟩
  have hzalg : IsAlgebraic Omega (coordinate Omega C.1 2) := not_not.mp hz
  by_cases hy : Transcendental Omega (coordinate Omega C.1 0)
  · have hGderiv : MvPolynomial.pderiv (1 : Fin 3) G ∉ C.1 :=
      pderiv_one_not_mem_of_regular_factor C.1
        (regularComponent_G_mem Omega G T H C)
        (regularComponent_H_not_mem Omega G T H C) hfactor hH
    have hYgate := finite_separable_at_Y_of_Z_algebraic
      C.1 G (regularComponent_G_mem Omega G T H C) hGderiv hy hzalg
    exact ⟨⟨0, hy, hYgate.1, hYgate.2⟩⟩
  have hyalg : IsAlgebraic Omega (coordinate Omega C.1 0) := not_not.mp hy
  obtain ⟨i, hi⟩ :=
    exists_transcendental_coordinate_of_ne_point_kernel Omega C.1
      (regularComponent_ne_point Omega G T H C)
  have hi1 : i = (1 : Fin 3) := by
    fin_cases i <;> simp_all
  subst i
  have hSgate := finite_separable_at_S_of_other_coordinates_algebraic
    C.1 hi hyalg hzalg
  exact ⟨⟨1, hi, hSgate.1, hSgate.2⟩⟩

/-- The replacement for the old literal-`Y` gate in the first affine
projection: either a `Y/Z` differential is active, or both are algebraic. -/
theorem YZ_differential_active_or_both_algebraic
    {G T H Surface : MvPolynomial (Fin 3) Omega}
    (C : RegularComponent Omega G T H)
    (hfactor : G ∣ Surface)
    (hH : H = MvPolynomial.pderiv (1 : Fin 3) Surface)
    (hZgate : LiteralProjectionGate C 2) :
    (KaehlerDifferential.D Omega (CoordinateField Omega C.1)
        (coordinate Omega C.1 0) ≠ 0 ∨
      KaehlerDifferential.D Omega (CoordinateField Omega C.1)
        (coordinate Omega C.1 2) ≠ 0) ∨
      (IsAlgebraic Omega (coordinate Omega C.1 0) ∧
        IsAlgebraic Omega (coordinate Omega C.1 2)) := by
  by_cases hz : Transcendental Omega (coordinate Omega C.1 2)
  · exact Or.inl (Or.inr (differential_ne_zero_of_gate _ hz (hZgate hz)))
  have hzalg : IsAlgebraic Omega (coordinate Omega C.1 2) := not_not.mp hz
  by_cases hy : Transcendental Omega (coordinate Omega C.1 0)
  · have hGderiv : MvPolynomial.pderiv (1 : Fin 3) G ∉ C.1 :=
      pderiv_one_not_mem_of_regular_factor C.1
        (regularComponent_G_mem Omega G T H C)
        (regularComponent_H_not_mem Omega G T H C) hfactor hH
    have hYgate := finite_separable_at_Y_of_Z_algebraic
      C.1 G (regularComponent_G_mem Omega G T H C) hGderiv hy hzalg
    exact Or.inl (Or.inl (differential_ne_zero_of_gate _ hy hYgate))
  · exact Or.inr ⟨not_not.mp hy, hzalg⟩

/-- Production-shaped wrapper for the actual regularity surface. -/
theorem exists_terminal_separableLiteralCoordinate_of_Z_gate
    {K : Type} [Field K]
    (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Omega)
    (C : RegularComponent Omega G T (regularitySurface phi F))
    (hfactor : G ∣ surfaceMap phi F)
    (hZgate : LiteralProjectionGate C 2) :
    Nonempty (SeparableLiteralCoordinate C.1) := by
  apply exists_separableLiteralCoordinate_of_Z_gate_regular_factor
    C hfactor
  · exact (surfaceMap_pderiv_R phi F).symm
  · exact hZgate

end

end ProximityPrize.SubmissionLower.CharFreeTerminal

#print axioms ProximityPrize.SubmissionLower.CharFreeTerminal.isSeparable_of_aeval_derivative_ne_zero
#print axioms ProximityPrize.SubmissionLower.CharFreeTerminal.pderiv_one_not_mem_of_regular_factor
#print axioms ProximityPrize.SubmissionLower.CharFreeTerminal.finite_separable_at_Y_of_Z_algebraic
#print axioms ProximityPrize.SubmissionLower.CharFreeTerminal.exists_separableLiteralCoordinate_of_Z_gate_regular_factor
#print axioms ProximityPrize.SubmissionLower.CharFreeTerminal.YZ_differential_active_or_both_algebraic
#print axioms ProximityPrize.SubmissionLower.CharFreeTerminal.exists_terminal_separableLiteralCoordinate_of_Z_gate
