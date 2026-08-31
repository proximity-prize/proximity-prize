import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CharacteristicFreeMatrixMultiplicityResearch
import ProximityPrize.SubmissionLower.ActualPlaneCoordinateDegree
namespace ProximityPrize.SubmissionLower.CharacteristicFreeProjectionAdapter
open scoped Classical BigOperators
open CharacteristicFreeMatrixMultiplicityResearch
noncomputable section
section ScalarBridge
variable {K B E:Type} [Field K] [Field B] [Field E]
  [Algebra K B] [Algebra K E] [Algebra B E] [IsScalarTower K B E]
theorem adjoin_singleton_eq_top_of_pair_eq_top
    (y r:E)
    (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
    (hy:∃ b:B,algebraMap B E b=y):
    IntermediateField.adjoin B ({r}:Set E)=⊤:=by
  have hgenAll:IntermediateField.adjoin B ({y,r}:Set E)=⊤:=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top
      (F:=K) (E:=B) (K:=E) hgen
  apply le_antisymm le_top
  rw [←hgenAll]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hxy | hxr
  · subst x
    obtain ⟨b,rfl⟩:=hy
    exact IntermediateField.adjoin.algebraMap_mem B {r} b
  · have:x=r:=Set.mem_singleton_iff.mp hxr
    subst x
    exact IntermediateField.subset_adjoin B {r} (Set.mem_singleton r)
end ScalarBridge
section MinpolyTower
variable {K E:Type} [Field K] [DecidableEq K] [Field E] [Algebra K E]
  [FiniteDimensional K E]
theorem minpoly_natDegree_dvd_finrank (y:E):
    (minpoly K y).natDegree∣Module.finrank K E:=by
  classical
  have hyIntegral:IsIntegral K y:=IsIntegral.of_finite K y
  let mu:Polynomial K:=minpoly K y
  have hmuIrreducible:Irreducible mu:=minpoly.irreducible hyIntegral
  letI:Fact (Irreducible mu):=⟨hmuIrreducible⟩
  let baseHom:AdjoinRoot mu →ₐ[K] E:=
    AdjoinRoot.liftAlgHom mu (Algebra.ofId K E) y (by
      change Polynomial.aeval y mu=0
      exact minpoly.aeval K y)
  letI:Algebra (AdjoinRoot mu) E:=baseHom.toRingHom.toAlgebra
  haveI:IsScalarTower K (AdjoinRoot mu) E:=
    IsScalarTower.of_algebraMap_eq fun c => (baseHom.commutes c).symm
  letI:Module.Finite (AdjoinRoot mu) E:=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot mu) E
  letI:FiniteDimensional K (AdjoinRoot mu):=
    (AdjoinRoot.powerBasis hmuIrreducible.ne_zero).finite
  have hbase:Module.finrank K (AdjoinRoot mu)=mu.natDegree:=by
    change Module.finrank K (Polynomial K ⧸ Ideal.span {mu})=mu.natDegree
    exact finrank_quotient_span_eq_natDegree
  refine ⟨Module.finrank (AdjoinRoot mu) E,?_⟩
  rw [←Module.finrank_mul_finrank K (AdjoinRoot mu) E,hbase]
end MinpolyTower
section FixedResiduePolynomial
variable {K:Type} [Field K] [DecidableEq K]
variable {I:Type*} [Fintype I]
theorem sum_relative_finrank_le_sylvester_corank
    (mu:Polynomial K) [Fact (Irreducible mu)]
    (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
    [∀ i,Algebra (AdjoinRoot mu) (E i)]
    [∀ i,IsScalarTower K (AdjoinRoot mu) (E i)]
    [∀ i,FiniteDimensional (AdjoinRoot mu) (E i)]
    (r:∀ i,E i)
    (hgen:∀ i,IntermediateField.adjoin (AdjoinRoot mu)
      ({r i}:Set (E i))=⊤)
    (hkernels:Function.Injective (fun i =>
      PlaneFunctionFieldDegree.relationIdeal K (E i)
        (algebraMap (AdjoinRoot mu) (E i) (AdjoinRoot.root mu)) (r i)))
    (P Q:Polynomial (Polynomial K)) (m n:ℕ)
    (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
    (hPne:P.map (AdjoinRoot.mk mu)≠0)
    (hProot:∀ i,Polynomial.aeval (r i) (P.map (AdjoinRoot.mk mu))=0)
    (hQroot:∀ i,Polynomial.aeval (r i) (Q.map (AdjoinRoot.mk mu))=0):
    (∑ i,Module.finrank (AdjoinRoot mu) (E i)) ≤
      m+n-(Polynomial.sylvester
        (P.map (AdjoinRoot.mk mu)) (Q.map (AdjoinRoot.mk mu)) m n).rank:=by
  classical
  let D:I → Polynomial (AdjoinRoot mu):=
    fun i => minpoly (AdjoinRoot mu) (r i)
  have hmonic:∀ i,(D i).Monic:=fun i =>
    minpoly.monic (IsIntegral.of_finite (AdjoinRoot mu) (r i))
  have hcoprime:Pairwise fun i j => IsCoprime (D i) (D j):=by
    exact relative_minpolys_pairwise_coprime_of_relationIdeal_injective
      mu E r hkernels
  have hDp:∀ i,D i∣P.map (AdjoinRoot.mk mu):=fun i =>
    minpoly.dvd (AdjoinRoot mu) (r i) (hProot i)
  have hDq:∀ i,D i∣Q.map (AdjoinRoot.mk mu):=fun i =>
    minpoly.dvd (AdjoinRoot mu) (r i) (hQroot i)
  have hdegree:∀ i,(D i).natDegree=
      Module.finrank (AdjoinRoot mu) (E i):=fun i =>
    (Field.primitive_element_iff_minpoly_natDegree_eq
      (AdjoinRoot mu) (r i)).mp (hgen i)
  have hbound:=sum_common_divisor_natDegrees_le_sylvester_corank
    (P.map (AdjoinRoot.mk mu)) (Q.map (AdjoinRoot.mk mu)) D m n
    (Polynomial.natDegree_map_le.trans hPcap)
    (Polynomial.natDegree_map_le.trans hQcap) hPne
    hmonic hcoprime hDp hDq
  simpa only [hdegree] using hbound
end FixedResiduePolynomial
section MinpolyGrouping
variable {K:Type} [Field K] [DecidableEq K]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
variable {I:Type*} [Fintype I]
theorem sum_grouped_weights_le_det_natDegree
    (M:Matrix ι ι (Polynomial K))
    (mu:I → Polynomial K) (relativeDegree:I → ℕ)
    (hmonic:∀ i,(mu i).Monic)
    (hirreducible:∀ i,Irreducible (mu i))
    (fiberCorank:∀ f∈(Finset.univ.image mu),
      (∑ i with mu i=f,relativeDegree i) ≤
        Fintype.card ι-((AdjoinRoot.mk f).mapMatrix M).rank)
    (hdet:M.det≠0):
    (∑ i,relativeDegree i*(mu i).natDegree) ≤ M.det.natDegree:=by
  classical
  let roots:Finset (Polynomial K):=Finset.univ.image mu
  let c:roots → ℕ:=fun f => ∑ i with mu i=f.1,relativeDegree i
  have hrootsMonic:∀ f:roots,(f.1).Monic:=by
    intro f
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
    simpa only [hi] using hmonic i
  have hrootsIrreducible:∀ f:roots,Irreducible f.1:=by
    intro f
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
    simpa only [hi] using hirreducible i
  have hrootsCoprime:Pairwise fun f g:roots => IsCoprime f.1 g.1:=by
    intro f g hfg
    apply (hrootsIrreducible f).coprime_iff_not_dvd.mpr
    intro hdvd
    have hassociated:=
      (hrootsIrreducible f).associated_of_dvd (hrootsIrreducible g) hdvd
    have heq:f.1=g.1:=Polynomial.eq_of_monic_of_associated
      (hrootsMonic f) (hrootsMonic g) hassociated
    exact hfg (Subtype.ext heq)
  have hc:∀ f:roots,
      c f ≤ Fintype.card ι-((AdjoinRoot.mk f.1).mapMatrix M).rank:=by
    intro f
    exact fiberCorank f.1 f.2
  have houter:=sum_irreducible_coranks_le_det_natDegree
    (K:=K) (I:=roots) M (fun f:roots => f.1) c
      hrootsMonic hrootsIrreducible hrootsCoprime hc hdet
  have hregroup:
      (∑ f:roots,c f*f.1.natDegree)=
        ∑ i,relativeDegree i*(mu i).natDegree:=by
    change (∑ f:roots,
      (∑ i with mu i=f.1,relativeDegree i)*f.1.natDegree)=_
    have hattach:
        (∑ f:roots,
          (∑ i with mu i=f.1,relativeDegree i)*f.1.natDegree)=
        ∑ f∈roots,
          (∑ i with mu i=f,relativeDegree i)*f.natDegree:=by
      rw [show (Finset.univ:Finset roots)=roots.attach from
        Finset.univ_eq_attach roots]
      exact Finset.sum_attach roots (fun f:Polynomial K =>
        (∑ i with mu i=f,relativeDegree i)*f.natDegree)
    rw [hattach]
    simp_rw [Finset.sum_mul]
    calc
      (∑ f∈roots,∑ i with mu i=f,
          relativeDegree i*f.natDegree)=
          ∑ f∈roots,∑ i with mu i=f,
            relativeDegree i*(mu i).natDegree:=by
        apply Finset.sum_congr rfl
        intro f hf
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _=∑ i∈(Finset.univ:Finset I),
          relativeDegree i*(mu i).natDegree:=
        Finset.sum_fiberwise_of_maps_to
          (s:=Finset.univ) (t:=roots) (g:=mu)
          (fun i _ => Finset.mem_image_of_mem mu (Finset.mem_univ i)) _
      _=∑ i,relativeDegree i*(mu i).natDegree:=by rfl
  rwa [hregroup] at houter
end MinpolyGrouping
section FinitePlaneFamily
variable {K:Type} [Field K] [DecidableEq K]
variable {I:Type*} [Fintype I]
variable (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
  [∀ i,FiniteDimensional K (E i)]
theorem sum_finrank_le_resultant_of_relationIdeal_injective
    (P Q:Polynomial (Polynomial K)) (m n:ℕ)
    (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
    (y r:∀ i,E i)
    (hgen:∀ i,IntermediateField.adjoin K
      ({y i,r i}:Set (E i))=⊤)
    (hkernels:Function.Injective (fun i =>
      PlaneFunctionFieldDegree.relationIdeal K (E i) (y i) (r i)))
    (hProot:∀ i,PlaneFunctionFieldDegree.planeEval K (E i)
      (y i) (r i) P=0)
    (hQroot:∀ i,PlaneFunctionFieldDegree.planeEval K (E i)
      (y i) (r i) Q=0)
    (hPspecial:∀ f∈
      (Finset.univ.image (fun i => minpoly K (y i))),
        P.map (AdjoinRoot.mk f)≠0)
    (hresultant:Polynomial.resultant P Q m n≠0):
    (∑ i,Module.finrank K (E i)) ≤
      (Polynomial.resultant P Q m n).natDegree:=by
  classical
  let mu:I → Polynomial K:=fun i => minpoly K (y i)
  let relativeDegree:I → ℕ:=fun i =>
    Module.finrank K (E i)/(mu i).natDegree
  have hmuMonic:∀ i,(mu i).Monic:=fun i =>
    minpoly.monic (IsIntegral.of_finite K (y i))
  have hmuIrreducible:∀ i,Irreducible (mu i):=fun i =>
    minpoly.irreducible (IsIntegral.of_finite K (y i))
  have htotal:∀ i,relativeDegree i*(mu i).natDegree=
      Module.finrank K (E i):=by
    intro i
    exact Nat.div_mul_cancel (minpoly_natDegree_dvd_finrank (K:=K) (y i))
  have hfiber:∀ f∈(Finset.univ.image mu),
      (∑ i with mu i=f,relativeDegree i) ≤
        m+n-((AdjoinRoot.mk f).mapMatrix
          (Polynomial.sylvester P Q m n)).rank:=by
    intro f hf
    let J:={i:I//mu i=f}
    have hJnonempty:Nonempty J:=by
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hf
      exact ⟨⟨i,hi⟩⟩
    let j₀:J:=Classical.choice hJnonempty
    have hfIrreducible:Irreducible f:=by
      simpa only [←j₀.property] using hmuIrreducible j₀.1
    letI:Fact (Irreducible f):=⟨hfIrreducible⟩
    let fiberBaseHom:∀ j:J,AdjoinRoot f →ₐ[K] E j.1:=fun j =>
      AdjoinRoot.liftAlgHom f (Algebra.ofId K (E j.1)) (y j.1) (by
        change Polynomial.aeval (y j.1) f=0
        calc
          _=Polynomial.aeval (y j.1) (mu j.1):=
            congrArg (Polynomial.aeval (y j.1)) j.property.symm
          _=0:=minpoly.aeval K (y j.1))
    letI:∀ j:J,Algebra (AdjoinRoot f) (E j.1):=
      fun j => (fiberBaseHom j).toRingHom.toAlgebra
    letI:∀ j:J,IsScalarTower K (AdjoinRoot f) (E j.1):=
      fun j => IsScalarTower.of_algebraMap_eq
        (fun c => ((fiberBaseHom j).commutes c).symm)
    letI:∀ j:J,Module.Finite (AdjoinRoot f) (E j.1):=
      fun j => Module.Finite.of_restrictScalars_finite K (AdjoinRoot f) (E j.1)
    letI:FiniteDimensional K (AdjoinRoot f):=
      (AdjoinRoot.powerBasis hfIrreducible.ne_zero).finite
    have hroot (j:J):
        algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f)=y j.1:=by
      change fiberBaseHom j (AdjoinRoot.root f)=y j.1
      exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId K (E j.1))
        (y j.1) _
    have hgenRelative:∀ j:J,
        IntermediateField.adjoin (AdjoinRoot f)
          ({r j.1}:Set (E j.1))=⊤:=by
      intro j
      exact adjoin_singleton_eq_top_of_pair_eq_top
        (y j.1) (r j.1) (hgen j.1)
          ⟨AdjoinRoot.root f,hroot j⟩
    have hkernelFiber:Function.Injective (fun j:J =>
        PlaneFunctionFieldDegree.relationIdeal K (E j.1)
          (algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f)) (r j.1)):=by
      intro a b hab
      apply Subtype.ext
      apply hkernels
      simpa only [hroot] using hab
    have hProotFiber:∀ j:J,
        Polynomial.aeval (r j.1) (P.map (AdjoinRoot.mk f))=0:=by
      intro j
      rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
      exact hProot j.1
    have hQrootFiber:∀ j:J,
        Polynomial.aeval (r j.1) (Q.map (AdjoinRoot.mk f))=0:=by
      intro j
      rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
      exact hQroot j.1
    have hfixed:=sum_relative_finrank_le_sylvester_corank
      (K:=K) (I:=J) f (fun j:J => E j.1) (fun j => r j.1)
      hgenRelative hkernelFiber P Q m n hPcap hQcap
      (hPspecial f (by simpa only [mu] using hf)) hProotFiber hQrootFiber
    have hbase:Module.finrank K (AdjoinRoot f)=f.natDegree:=by
      change Module.finrank K (Polynomial K ⧸ Ideal.span {f})=f.natDegree
      exact finrank_quotient_span_eq_natDegree
    have hrelative (j:J):relativeDegree j.1=
        Module.finrank (AdjoinRoot f) (E j.1):=by
      change Module.finrank K (E j.1)/(mu j.1).natDegree=_
      rw [j.property, ←Module.finrank_mul_finrank K (AdjoinRoot f) (E j.1),
        hbase]
      exact Nat.mul_div_cancel_left _ hfIrreducible.natDegree_pos
    have hsum:(∑ i with mu i=f,relativeDegree i)=
        ∑ j:J,Module.finrank (AdjoinRoot f) (E j.1):=by
      calc
        _=∑ j:J,relativeDegree j.1:=by
          simpa only [J,Finset.subtype_univ] using
            (Finset.sum_subtype_eq_sum_filter
              (s:=(Finset.univ:Finset I)) relativeDegree
              (p:=fun i => mu i=f)).symm
        _=_:=by
          apply Finset.sum_congr rfl
          intro j _
          exact hrelative j
    rw [hsum]
    simpa only [Fintype.card_fin, ←Polynomial.sylvester_map_map] using hfixed
  have hdet:(Polynomial.sylvester P Q m n).det≠0:=by
    simpa only [Polynomial.resultant] using hresultant
  have hfiber':∀ f∈(Finset.univ.image mu),
      (∑ i with mu i=f,relativeDegree i) ≤
        Fintype.card (Fin (m+n))-((AdjoinRoot.mk f).mapMatrix
          (Polynomial.sylvester P Q m n)).rank:=by
    simpa only [Fintype.card_fin] using hfiber
  have houter:=sum_grouped_weights_le_det_natDegree
    (K:=K) (I:=I) (M:=Polynomial.sylvester P Q m n)
    mu relativeDegree hmuMonic hmuIrreducible hfiber' hdet
  simpa only [Polynomial.resultant,htotal] using houter
theorem sum_finrank_le_planar_bound_without_separability
    (P Q:Polynomial (Polynomial K))
    (hP:Irreducible P) (hpositive:0 < P.natDegree)
    (hproper:¬ P∣Q)
    (y r:∀ i,E i)
    (hgen:∀ i,IntermediateField.adjoin K
      ({y i,r i}:Set (E i))=⊤)
    (hkernels:Function.Injective (fun i =>
      PlaneFunctionFieldDegree.relationIdeal K (E i) (y i) (r i)))
    (hProot:∀ i,PlaneFunctionFieldDegree.planeEval K (E i)
      (y i) (r i) P=0)
    (hQroot:∀ i,PlaneFunctionFieldDegree.planeEval K (E i)
      (y i) (r i) Q=0):
    (∑ i,Module.finrank K (E i)) ≤
      Q.natDegree*Polynomial.Bivariate.degreeX P+
        P.natDegree*Polynomial.Bivariate.degreeX Q:=by
  classical
  have hspecial:∀ f∈
      (Finset.univ.image (fun i => minpoly K (y i))),
        P.map (AdjoinRoot.mk f)≠0:=by
    intro f hf
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
    letI:Fact (Irreducible (minpoly K (y i))):=
      ⟨minpoly.irreducible (IsIntegral.of_finite K (y i))⟩
    have hcoeff:Polynomial.eval₂RingHom
        (algebraMap K (AdjoinRoot (minpoly K (y i))))
          (AdjoinRoot.root (minpoly K (y i)))=
        AdjoinRoot.mk (minpoly K (y i)):=by
      apply Polynomial.ringHom_ext
      · intro c
        simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
          AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
      · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
          AdjoinRoot.mk_X]
    have h:=PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap K (AdjoinRoot (minpoly K (y i)))) P
      (hP.isPrimitive (Nat.ne_of_gt hpositive))
      (AdjoinRoot.root (minpoly K (y i)))
    rw [PlaneCoefficientExtension.bimap_specialization,hcoeff] at h
    exact h
  have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
    PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
      P Q hP hpositive hproper
  exact (sum_finrank_le_resultant_of_relationIdeal_injective
    (K:=K) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
      hkernels hProot hQroot hspecial hresultant).trans
        (bivariate_resultant_natDegree_le
          (F:=K) P Q P.natDegree Q.natDegree)
end FinitePlaneFamily
end
end ProximityPrize.SubmissionLower.CharacteristicFreeProjectionAdapter
