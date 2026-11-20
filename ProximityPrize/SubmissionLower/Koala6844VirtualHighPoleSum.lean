import ProximityPrize.SubmissionLower.LowerFoundation
-- Modified from prior Proximity Prize sources.


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
open MvPolynomial RCN002 RCN011 RCN021 RCN042 RCN093 RCN102 RCN103 RCN104 RCN106 RCN107
  RCN108 RCN109 RCN111 RCN112 RCN113 RCN120 RCN125 RCN135 RCN136 RCN195 RCN219
  RCN255 RCN264 RCN333 RCN343 RCN344 RCN226 RCN014

noncomputable section

set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 12000
set_option Elab.async false
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private theorem map_mem_of_mul_mem_span_sup_pow
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (C : Ideal R) (J : Ideal S) [J.IsMaximal] (contract : J.comap f = C)
    (g t : R) (hg : f g ∈ J) (n : ℕ) (positive : 1 ≤ n)
    (primary : ∃ s ∉ C, s * t ∈ Ideal.span {g} ⊔ C ^ n) :
    f t ∈ Ideal.span {f g} ⊔ J ^ n := by
  obtain ⟨s, hsnot, hsT⟩ := primary
  have hmapG : Ideal.map f (Ideal.span {g}) ≤ Ideal.span {f g} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmapC : Ideal.map f C ≤ J := by
    rw [Ideal.map_le_iff_le_comap, contract]
  have hmapPow : Ideal.map f (C ^ n) ≤ J ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmapC _
  have htarget : Ideal.map f (Ideal.span {g} ⊔ C ^ n) ≤
      Ideal.span {f g} ⊔ J ^ n := by
    rw [Ideal.map_sup]
    exact sup_le (hmapG.trans le_sup_left) (hmapPow.trans le_sup_right)
  have hmul : f s * f t ∈ Ideal.span {f g} ⊔ J ^ n := by
    rw [← map_mul]
    exact htarget (Ideal.mem_map_of_mem f hsT)
  have hfs : f s ∉ J := by
    intro hmem
    apply hsnot
    rw [← contract]
    exact hmem
  exact RCN310.mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
    (f g) (f t) (f s) J hg n positive hfs hmul

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A : Type} [Fintype A]
variable {G T H : MvPolynomial (Fin 3) Ω}

variable (component : A → RegularComponent Ω G T H)
  (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
  (ht : ∀ a, Transcendental Ω
    (flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 0))))
  (hfinite : ∀ a, letI := flagBaseAlgebra Ω (component a).1 lam mu nu order (ht a)
    FiniteDimensional (RatFunc Ω) (CoordinateField Ω (component a).1))
  (hgen : ∀ a, letI := flagBaseAlgebra Ω (component a).1 lam mu nu order (ht a)
    IntermediateField.adjoin (RatFunc Ω)
      ({flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 2)),
        flagEvaluation Ω (component a).1 lam mu nu (MvPolynomial.X (order 1))} :
        Set (CoordinateField Ω (component a).1)) = ⊤)

private def projectedTailMembership
    (q : Polynomial (RatFunc Ω)) (hq : Irreducible q)
    (a : IndexedFactorFiber component lam mu nu order ht q) (multiplicity : ℕ) : Prop :=
  indexedFiberTail q hq (flagPlaneMap Ω lam mu nu order T) ∈
    Ideal.span {indexedFiberSurface q hq (flagPlaneMap Ω lam mu nu order G)} ⊔
      indexedFiberRelation component lam mu nu order ht q hq a ^ multiplicity

private def projectedWeightedOrder (multiplicity : A → ℕ)
    (q : Polynomial (RatFunc Ω)) : ℕ :=
  ∑ a : IndexedFactorFiber component lam mu nu order ht q,
    multiplicity a.1 * indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1

omit [IsAlgClosed Ω] in
include hfinite hgen in
private theorem projected_tail_mem_primary
    (orderCount : A → ℕ) (positive : ∀ a, 1 ≤ orderCount a)
    (primary : ∀ a, ∃ s ∉ (component a).1,
      s * T ∈ Ideal.span {G} ⊔ (component a).1 ^ orderCount a)
    (q : Polynomial (RatFunc Ω)) (hq : Irreducible q)
    (a : IndexedFactorFiber component lam mu nu order ht q) :
    projectedTailMembership component lam mu nu order ht q hq a (orderCount a.1) := by
  let plane := flagPlaneMap Ω lam mu nu order
  let localize := fiberLocalizePlane q hq
  let J := indexedFiberRelation component lam mu nu order ht q hq a
  let C := (component a.1).1
  let f := localize.comp plane
  have hmax : J.IsMaximal := indexedFiberRelation_isMaximal component lam mu nu order ht
    hfinite hgen q hq a
  have hs : localize (plane G) ∈ J := by
    exact Ideal.mem_map_of_mem localize (flagPlaneMap_mem_relation C lam mu nu order (ht a.1)
      (regularComponent_G_mem Ω G T H (component a.1)))
  have hplane : (relationKernel Ω (CoordinateField Ω C) order
      (flagEvaluation Ω C lam mu nu) (ht a.1)).comap plane = C := by
    change (relationKernel Ω (CoordinateField Ω C) order (flagEvaluation Ω C lam mu nu)
      (ht a.1)).comap
      ((planeMap Ω order).comp (flagAlgHom lam mu nu).toRingHom) = C
    rw [← Ideal.comap_comap, relationKernel_contract, flagEvaluation_kernel_contract]
  have hcontract : J.comap f = C := by
    change J.comap (localize.comp plane) = C
    rw [← Ideal.comap_comap,
      indexedFiberRelation_under component lam mu nu order ht q hq a, hplane]

  change f T ∈ Ideal.span {f G} ⊔ J ^ orderCount a.1
  let iR := (inferInstance : CommRing (MvPolynomial (Fin 3) Ω))
  let iS := (inferInstance : CommRing (Polynomial (FiberCoefficient q hq)))
  refine @map_mem_of_mul_mem_span_sup_pow _ _ iR iS f C J hmax ?_ G T ?_
    (orderCount a.1) ?_ ?_
  · exact hcontract
  · exact hs
  · exact positive a.1
  · exact primary a.1

include hfinite hgen in
private theorem projected_grouped_resultant_power_dvd
    (orderCount : A → ℕ) (positive : ∀ a, 1 ≤ orderCount a)
    (primary : ∀ a, ∃ s ∉ (component a).1,
      s * T ∈ Ideal.span {G} ⊔ (component a).1 ^ orderCount a)
    (hinj : Function.Injective component)
    (hirr : Irreducible G) (hproper : ¬ G ∣ T)
    (hpositive : 0 < (flagPlaneMap Ω lam mu nu order G).natDegree)
    (q : Polynomial (RatFunc Ω)) (hq : Irreducible q) (hqmonic : q.Monic)
    (a₀ : IndexedFactorFiber component lam mu nu order ht q) :
    q ^ projectedWeightedOrder component lam mu nu order ht hfinite orderCount q ∣
      flagPlaneResultant lam mu nu order G T := by
  let surface := flagPlaneMap Ω lam mu nu order G
  let tail := flagPlaneMap Ω lam mu nu order T
  letI : (Ideal.span {indexedFiberSurface q hq surface}).IsPrime :=
    indexedFiberSurface_span_isPrime component lam mu nu order ht hirr q hq a₀
  have hsurface (a : IndexedFactorFiber component lam mu nu order ht q) :
      surface ∈ relationKernel Ω (CoordinateField Ω (component a.1).1) order
        (flagEvaluation Ω (component a.1).1 lam mu nu) (ht a.1) := by
    exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
      (regularComponent_G_mem Ω G T H (component a.1))
  have htailRoot (a : IndexedFactorFiber component lam mu nu order ht q) :
      tail ∈ relationKernel Ω (CoordinateField Ω (component a.1).1) order
        (flagEvaluation Ω (component a.1).1 lam mu nu) (ht a.1) := by
    exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
      (regularComponent_T_mem Ω G T H (component a.1))
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
    exact localized_surface_residue_ne_zero Ω (CoordinateField Ω (component a).1) order
      (flagEvaluation Ω (component a).1 lam mu nu) (ht a) (hfinite a) surface hspecial
  exact indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
    component hinj lam mu nu order ht hfinite hgen q hq hqmonic
    surface tail surface.natDegree tail.natDegree hsurface hbarne
    (fun a => orderCount a.1)
    (projected_tail_mem_primary component lam mu nu order ht hfinite hgen orderCount positive primary q hq)
    Polynomial.natDegree_map_le Polynomial.natDegree_map_le hresultant hPbar



def projectedFiniteDegree (a : A) : ℕ :=
  letI := flagBaseAlgebra Ω (component a).1 lam mu nu order (ht a)
  Module.finrank (RatFunc Ω) (CoordinateField Ω (component a).1)

include hgen in
private theorem projected_degree_eq_factor_weight (a : A) :
    projectedFiniteDegree component lam mu nu order ht a =
      (indexedComponentFactor component lam mu nu order ht a).natDegree *
        indexedPlaneResidueWeight component lam mu nu order ht hfinite a := by
 let F:=RatFunc Ω
 let L:=CoordinateField Ω (component a).1
 let e:=flagEvaluation Ω (component a).1 lam mu nu
 let q:=projectedFactor Ω L order e (ht a)
 let J:=relationKernel Ω L order e (ht a)
 letI:Algebra F L:=flagBaseAlgebra Ω (component a).1
   lam mu nu order (ht a)
 letI:FiniteDimensional F L:=hfinite a
 letI:J.IsMaximal:=relationKernel_isMaximal Ω L order e (ht a)
   (hfinite a) (hgen a)
 let aResidue:=residueAlgebra q J
   (relationKernel_comap_C Ω L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Ω ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (PlaneRing Ω ⧸ J):=aResidue.toSMul
 let targetSemiring:Semiring (PlaneRing Ω ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Ω ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Ω ⧸ J):=Algebra.toModule
 have hq:Irreducible q:=projectedFactor_irreducible Ω L order e
   (ht a) (hfinite a)
 let phi:PlaneRing Ω →ₐ[F] L:={
   toRingHom:=planeEvaluation Ω L order e (ht a)
   commutes':=fun c => by
     change planeEvaluation Ω L order e (ht a)
       (Polynomial.C (Polynomial.C c))=algebraMap F L c
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) (hgen a)
 let eqv:(PlaneRing Ω ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing Ω ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 have hquot:Module.finrank F (PlaneRing Ω ⧸ J)=
     Module.finrank F L:=eqv.toLinearEquiv.finrank_eq
 change Module.finrank F L=q.natDegree*
   indexedPlaneResidueWeight component lam mu nu order ht hfinite a
 rw [show indexedPlaneResidueWeight component lam mu nu order ht hfinite a=
     Module.finrank (AdjoinRoot q) (PlaneRing Ω ⧸ J) by rfl]
 calc
   Module.finrank F L=Module.finrank F (PlaneRing Ω ⧸ J):=hquot.symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (PlaneRing Ω ⧸ J):=
     quotient_finrank_eq_natDegree_mul_residue_finrank q hq J
       (relationKernel_comap_C Ω L order e (ht a))

include hgen in
private def weighted_projection_channel
    (orderCount : A → ℕ) (resultant : Polynomial (RatFunc Ω)) (budget : ℕ)
    (hresultant : resultant ≠ 0) (hdegree : resultant.natDegree ≤ budget)
    (hfixed : ∀ (q : Polynomial (RatFunc Ω)), Irreducible q → q.Monic →
      IndexedFactorFiber component lam mu nu order ht q →
        q ^ projectedWeightedOrder component lam mu nu order ht hfinite orderCount q ∣ resultant) :
    WeightedGroupedResultantChannel (Base := RatFunc Ω) orderCount
      (projectedFiniteDegree component lam mu nu order ht) budget := by
 let factor:=indexedComponentFactor component lam mu nu order ht
 let weight:=indexedPlaneResidueWeight component lam mu nu order ht hfinite
 refine {
   resultant:=resultant
   factor:=factor
   residueWeight:=weight
   resultant_ne:=hresultant
   factor_irreducible:=?_
   factor_monic:=?_
   groupedPowerDvd:=?_
   cost_le_residue_mul_degree:=?_
   resultant_degree_le:=hdegree}
 · intro a
   exact projectedFactor_irreducible Ω
     (CoordinateField Ω (component a).1) order
       (flagEvaluation Ω (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro a
   exact projectedFactor_monic Ω
     (CoordinateField Ω (component a).1) order
       (flagEvaluation Ω (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro q hqmem
   obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hqmem
   subst q
   have hqirr:Irreducible (factor a):=projectedFactor_irreducible Ω
     (CoordinateField Ω (component a).1) order
       (flagEvaluation Ω (component a).1 lam mu nu) (ht a) (hfinite a)
   have hqmonic:(factor a).Monic:=projectedFactor_monic Ω
     (CoordinateField Ω (component a).1) order
       (flagEvaluation Ω (component a).1 lam mu nu) (ht a) (hfinite a)
   let a₀:IndexedFactorFiber component lam mu nu order ht (factor a):=⟨a,rfl⟩
   have hpow:=hfixed (factor a) hqirr hqmonic a₀
   have hsum:
       (∑ b with factor b=factor a,orderCount b*weight b)=
         ∑ b:IndexedFactorFiber component lam mu nu order ht (factor a),
           orderCount b.1*weight b.1:=by
     simpa only [Finset.subtype_univ,eq_comm] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset A))
         (fun b↦orderCount b*weight b)
         (p:=fun b↦factor a=factor b)).symm
   rw [hsum]
   exact hpow
 · intro a
   have hcost := projected_degree_eq_factor_weight component lam mu nu order ht hfinite hgen a
   simpa only [factor, weight, Nat.mul_comm] using hcost.le


include hfinite hgen in



theorem sum_weighted_projection_degree_le
    (orderCount : A → ℕ) (positive : ∀ a, 1 ≤ orderCount a)
    (primary : ∀ a, ∃ s ∉ (component a).1,
      s * T ∈ Ideal.span {G} ⊔ (component a).1 ^ orderCount a)
    (hinj : Function.Injective component)
    (hirr : Irreducible G) (hproper : ¬ G ∣ T)
    (hpositive : 0 < (flagPlaneMap Ω lam mu nu order G).natDegree)
    (budget : ℕ) (hdegree : (flagPlaneResultant lam mu nu order G T).natDegree ≤ budget) :
    (∑ a, orderCount a * projectedFiniteDegree component lam mu nu order ht a) ≤ budget := by
  classical
  by_cases ha : Nonempty A
  · obtain ⟨a₀⟩ := ha
    have hresultant := flagPlaneResultant_ne (G := G) (T := T) (H := H) lam mu nu order
      hirr hproper (component a₀) (ht a₀) hpositive
    exact (weighted_projection_channel component lam mu nu order ht hfinite hgen orderCount
      (flagPlaneResultant lam mu nu order G T) budget hresultant hdegree
      (fun q hq hm a => projected_grouped_resultant_power_dvd component lam mu nu order ht
        hfinite hgen orderCount positive primary hinj hirr hproper hpositive q hq hm a)).sum_mul_cost_le
  · letI : IsEmpty A := not_nonempty_iff.mp ha
    simp

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh


