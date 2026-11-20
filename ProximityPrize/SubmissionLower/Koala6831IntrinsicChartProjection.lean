import ProximityPrize.SubmissionLower.Koala6831IntrinsicChart


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped Classical BigOperators
open MvPolynomial RCN002 RCN011 RCN021 RCN042 RCN093 RCN102 RCN103 RCN104 RCN106 RCN107
  RCN108 RCN109 RCN111 RCN112 RCN113 RCN120 RCN125 RCN135 RCN136 RCN195 RCN219
  RCN255 RCN264 RCN333 RCN344

noncomputable section

set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 12000
set_option Elab.async false
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {K : Type} [Field K] {A : Type} [Fintype A]
variable (F : Carrier K) (w p : ℕ) [CharP K p] (hp : p.Prime)
variable {G T H : MvPolynomial (Fin 3) (GenericField K)}

variable (component : A → RegularComponent (GenericField K) G T H)
  (charts : ∀ a, CurveChartData F w (component a).1)
  (lam mu nu : (GenericField K)) (order : Fin 3 ≃ Fin 3)
  (ht : ∀ a, Transcendental (GenericField K)
    (flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 0))))
  (hfinite : ∀ a, letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
    FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1))
  (hgen : ∀ a, letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
    IntermediateField.adjoin (RatFunc (GenericField K))
      ({flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 2)),
        flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 1))} :
        Set (CoordinateField (GenericField K) (component a).1)) = ⊤)

private def projectedTailMembership
    (q : Polynomial (RatFunc (GenericField K))) (hq : Irreducible q)
    (a : IndexedFactorFiber component lam mu nu order ht q) (multiplicity : ℕ) : Prop :=
  indexedFiberTail q hq (flagPlaneMap (GenericField K) lam mu nu order T) ∈
    Ideal.span {indexedFiberSurface q hq (flagPlaneMap (GenericField K) lam mu nu order G)} ⊔
      indexedFiberRelation component lam mu nu order ht q hq a ^ multiplicity

private def projectedWeightedOrder (multiplicity : A → ℕ)
    (q : Polynomial (RatFunc (GenericField K))) : ℕ :=
  ∑ a : IndexedFactorFiber component lam mu nu order ht q,
    multiplicity a.1 * indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1

include hfinite hgen hp

private theorem fiber_tail_mem_primary
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hTail : T = surfaceMap (polynomialEmbedding K) (tailNumerator F w))
    (q : Polynomial (RatFunc (GenericField K))) (hq : Irreducible q)
    (a : IndexedFactorFiber component lam mu nu order ht q) :
    projectedTailMembership component lam mu nu order ht q hq a
      (curveTailOrder F w (component a.1).1 (charts a.1)) := by
  let plane := flagPlaneMap (GenericField K) lam mu nu order
  let localize := fiberLocalizePlane q hq
  let J := indexedFiberRelation component lam mu nu order ht q hq a
  let C := (component a.1).1
  let f := (localize.comp plane).comp (surfaceMap (polynomialEmbedding K))
  letI : J.IsMaximal := indexedFiberRelation_isMaximal component lam mu nu order ht
    hfinite hgen q hq a
  have hfactor : f F ∈ Ideal.span {localize (plane G)} := by
    exact Ideal.mem_span_singleton.mpr (map_dvd (localize.comp plane) hdiv)
  have hs : localize (plane G) ∈ J := by
    exact Ideal.mem_map_of_mem localize (flagPlaneMap_mem_relation C lam mu nu order (ht a.1)
      (regularComponent_G_mem (GenericField K) G T H (component a.1)))
  have hplane : (relationKernel (GenericField K) (CoordinateField (GenericField K) C) order
      (flagEvaluation (GenericField K) C lam mu nu) (ht a.1)).comap plane = C := by
    change (relationKernel (GenericField K) (CoordinateField (GenericField K) C) order (flagEvaluation (GenericField K) C lam mu nu)
      (ht a.1)).comap
      ((planeMap (GenericField K) order).comp (flagAlgHom lam mu nu).toRingHom) = C
    rw [← Ideal.comap_comap, relationKernel_contract, flagEvaluation_kernel_contract]
  have hcontract : J.comap f = originalPrime C := by
    change J.comap ((localize.comp plane).comp (surfaceMap (polynomialEmbedding K))) = originalPrime C
    rw [← Ideal.comap_comap, ← Ideal.comap_comap,
      indexedFiberRelation_under component lam mu nu order ht q hq a, hplane]
    rfl
  change localize (plane T) ∈ Ideal.span {localize (plane G)} ⊔ J ^ _
  have hleft : localize (plane T) = f (tailNumerator F w) :=
    congrArg (fun Q => localize (plane Q)) hTail
  rw [hleft]
  have hlocal := curve_tail_mem_projected_primary F w p hp C (charts a.1)
    (A := Polynomial (FiberCoefficient q hq)) f (localize (plane G)) J hfactor hs hcontract
  exact hlocal

theorem intrinsic_grouped_resultant_power_dvd
    (hinj : Function.Injective component)
    (hirr : Irreducible G) (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hTail : T = surfaceMap (polynomialEmbedding K) (tailNumerator F w)) (hproper : ¬ G ∣ T)
    (hpositive : 0 < (flagPlaneMap (GenericField K) lam mu nu order G).natDegree)
    (q : Polynomial (RatFunc (GenericField K))) (hq : Irreducible q) (hqmonic : q.Monic)
    (a₀ : IndexedFactorFiber component lam mu nu order ht q) :
    q ^ projectedWeightedOrder component lam mu nu order ht hfinite
      (fun a => curveTailOrder F w (component a).1 (charts a)) q ∣
      flagPlaneResultant lam mu nu order G T := by
  let surface := flagPlaneMap (GenericField K) lam mu nu order G
  let tail := flagPlaneMap (GenericField K) lam mu nu order T
  letI : (Ideal.span {indexedFiberSurface q hq surface}).IsPrime :=
    indexedFiberSurface_span_isPrime component lam mu nu order ht hirr q hq a₀
  have hsurface (a : IndexedFactorFiber component lam mu nu order ht q) :
      surface ∈ relationKernel (GenericField K) (CoordinateField (GenericField K) (component a.1).1) order
        (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1) := by
    exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
      (regularComponent_G_mem (GenericField K) G T H (component a.1))
  have htailRoot (a : IndexedFactorFiber component lam mu nu order ht q) :
      tail ∈ relationKernel (GenericField K) (CoordinateField (GenericField K) (component a.1).1) order
        (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1) := by
    exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
      (regularComponent_T_mem (GenericField K) G T H (component a.1))
  have hbarne (a : IndexedFactorFiber component lam mu nu order ht q) :
      indexedFiberRelationBar component lam mu nu order ht q hq surface a ≠ ⊥ :=
    indexedFiberRelationBar_ne_bot component lam mu nu order ht q hq surface tail htailRoot
      (indexedFiberTail_not_mem_surface component lam mu nu order ht hirr hproper q hq a₀) a
  have hR := flagPlaneResultant_ne (G := G) (T := T) (H := H)
    lam mu nu order hirr hproper (component a₀.1) (ht a₀.1) hpositive
  have hresultant : Polynomial.resultant surface tail surface.natDegree tail.natDegree ≠ 0 := by
    simpa only [flagPlaneResultant, surface, tail, flagPlaneMap, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hR
  have hPbar : (indexedFiberSurface q hq surface).map
      (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0 := by
    have hirrPlane := transformedSurface_irreducible (G := G) (T := T) (H := H)
      lam mu nu order hirr (component a₀.1) (ht a₀.1)
    have hirrSurface : Irreducible surface := by
      simpa only [surface, flagPlaneMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] using hirrPlane
    have hspecial := planeSurface_map_adjoinRoot_ne_zero q hq surface hirrSurface hpositive
    rcases a₀ with ⟨a, rfl⟩
    exact localized_surface_residue_ne_zero (GenericField K) (CoordinateField (GenericField K) (component a).1) order
      (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a) (hfinite a) surface hspecial
  exact indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
    component hinj lam mu nu order ht hfinite hgen q hq hqmonic
    surface tail surface.natDegree tail.natDegree hsurface hbarne
    (fun a => curveTailOrder F w (component a.1).1 (charts a.1))
    (fiber_tail_mem_primary F w p hp component charts lam mu nu order ht hfinite hgen hdiv hTail q hq)
    Polynomial.natDegree_map_le Polynomial.natDegree_map_le hresultant hPbar

theorem intrinsic_sum_order_mul_coordinateDegree_le
    (hinj : Function.Injective component)
    (hirr : Irreducible G) (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hTail : T = surfaceMap (polynomialEmbedding K) (tailNumerator F w)) (hproper : ¬ G ∣ T)
    (hpositive : 0 < (flagPlaneMap (GenericField K) lam mu nu order G).natDegree)
    (hgate : ∀ a, ∀ hx : Transcendental (GenericField K)
        (flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 0))),
      (letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order hx
       FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1)) ∧
      (letI := flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order hx
       Algebra.IsSeparable (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1)))
    (budget : ℕ) (hdegree : (flagPlaneResultant lam mu nu order G T).natDegree ≤ budget) :
    (∑ a : A, curveTailOrder F w (component a).1 (charts a) *
      coordinateDegree (GenericField K) (CoordinateField (GenericField K) (component a).1)
        (coordinateOfGate
          (flagEvaluation (GenericField K) (component a).1 lam mu nu (MvPolynomial.X (order 0)))
          (hgate a))) ≤ budget := by
  classical
  by_cases ha : Nonempty A
  · obtain ⟨a₀⟩ := ha
    have hresultant := flagPlaneResultant_ne (G := G) (T := T) (H := H) lam mu nu order hirr hproper
      (component a₀) (ht a₀) hpositive
    exact (indexedWeightedFlagPlaneChannel_of_fixedFactors component
      lam mu nu order ht hfinite hgen hgate
      (fun a => curveTailOrder F w (component a).1 (charts a))
      (flagPlaneResultant lam mu nu order G T) budget hresultant hdegree
      (intrinsic_grouped_resultant_power_dvd F w p hp component charts lam mu nu order ht
        hfinite hgen hinj hirr hdiv hTail hproper hpositive)).sum_mul_cost_le
  · letI : IsEmpty A := not_nonempty_iff.mp ha
    simp

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
