import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.MatrixRootMultiplicity
import ProximityPrize.SubmissionLower.PlaneResultantPointCount
import ProximityPrize.SubmissionLower.PlaneFunctionFieldDegree
import ProximityPrize.SubmissionLower.PlaneRootSeparability
namespace ProximityPrize.SubmissionLower.CharacteristicFreeMatrixMultiplicityResearch
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_dvd_columns
    (M:Matrix ι ι (Polynomial K)) (a:Polynomial K) (columns:Finset ι)
    (hdiv:∀ j∈columns,∀ i,a∣M i j):
    a^columns.card∣M.det:=by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro permutation _
  have hpart:
      (∏ _j∈columns,a)∣∏ j∈columns,M (permutation j) j:=by
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    exact hdiv j hj (permutation j)
  have hfull:
      (∏ j∈columns,M (permutation j) j)∣
        ∏ j:ι,M (permutation j) j:=
    Finset.prod_dvd_prod_of_subset columns Finset.univ
      (fun j => M (permutation j) j) (Finset.subset_univ columns)
  have hproduct:a^columns.card∣∏ j:ι,M (permutation j) j:=by
    simpa using hpart.trans hfull
  exact dvd_mul_of_dvd_right hproduct _
theorem irreducible_pow_corank_dvd_det
    (M:Matrix ι ι (Polynomial K)) (mu:Polynomial K)
    (hmu:Irreducible mu):
    mu^(Fintype.card ι-((AdjoinRoot.mk mu).mapMatrix M).rank)∣M.det:=by
  classical
  letI:Fact (Irreducible mu):=⟨hmu⟩
  let reduceMatrix:Matrix ι ι (Polynomial K) →+*
      Matrix ι ι (AdjoinRoot mu):=(AdjoinRoot.mk mu).mapMatrix
  let reduced:Matrix ι ι (AdjoinRoot mu):=reduceMatrix M
  obtain ⟨V,U,e,hV,hU,hnormal⟩:=Matrix.exists_rank_normal_form reduced
  let liftEntry:AdjoinRoot mu → Polynomial K:=
    Function.surjInv (AdjoinRoot.mk_surjective (g:=mu))
  have hliftEntry (x:AdjoinRoot mu):AdjoinRoot.mk mu (liftEntry x)=x:=by
    exact Function.surjInv_eq (AdjoinRoot.mk_surjective (g:=mu)) x
  let Vlift:Matrix ι ι (Polynomial K):=fun i j => liftEntry (V i j)
  let Ulift:Matrix ι ι (Polynomial K):=fun i j => liftEntry (U i j)
  have hmapV:reduceMatrix Vlift=V:=by
    ext i j
    exact hliftEntry (V i j)
  have hmapU:reduceMatrix Ulift=U:=by
    ext i j
    exact hliftEntry (U i j)
  let transformed:Matrix ι ι (Polynomial K):=Vlift*M*Ulift
  have hmapTransformed:reduceMatrix transformed=
      (Matrix.fromBlocks 1 0 0 0).submatrix e e:=by
    change reduceMatrix (Vlift*M*Ulift)=_
    rw [map_mul,map_mul,hmapV,hmapU]
    exact hnormal
  let zeroEmbedding:Fin (Fintype.card ι-reduced.rank) ↪ ι:={
    toFun:=fun j => e.symm (Sum.inr j)
    inj':=by
      intro i j hij
      exact Sum.inr.inj (e.symm.injective hij)
  }
  let zeroColumns:Finset ι:=Finset.univ.map zeroEmbedding
  have hcard:zeroColumns.card=Fintype.card ι-reduced.rank:=by
    simp [zeroColumns]
  have hcolumns:∀ j∈zeroColumns,∀ i,mu∣transformed i j:=by
    intro j hj i
    obtain ⟨j0,_,rfl⟩:=Finset.mem_map.mp hj
    apply AdjoinRoot.mk_eq_zero.mp
    change reduceMatrix transformed i (e.symm (Sum.inr j0))=0
    rw [hmapTransformed]
    simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
    cases e i <;> rfl
  have hVdet:¬mu∣Vlift.det:=by
    intro hdiv
    have hzero:AdjoinRoot.mk mu Vlift.det=0:=AdjoinRoot.mk_eq_zero.mpr hdiv
    have hdetmap:AdjoinRoot.mk mu Vlift.det=V.det:=by
      rw [(AdjoinRoot.mk mu).map_det,hmapV]
    have hVdetUnit:IsUnit V.det:=(Matrix.isUnit_iff_isUnit_det _).mp hV
    exact hVdetUnit.ne_zero (hdetmap ▸ hzero)
  have hUdet:¬mu∣Ulift.det:=by
    intro hdiv
    have hzero:AdjoinRoot.mk mu Ulift.det=0:=AdjoinRoot.mk_eq_zero.mpr hdiv
    have hdetmap:AdjoinRoot.mk mu Ulift.det=U.det:=by
      rw [(AdjoinRoot.mk mu).map_det,hmapU]
    have hUdetUnit:IsUnit U.det:=(Matrix.isUnit_iff_isUnit_det _).mp hU
    exact hUdetUnit.ne_zero (hdetmap ▸ hzero)
  have hdetdiv:=pow_card_dvd_det_of_dvd_columns
    transformed mu zeroColumns hcolumns
  rw [hcard] at hdetdiv
  change mu^(Fintype.card ι-reduced.rank)∣
      (Vlift*M*Ulift).det at hdetdiv
  rw [Matrix.det_mul,Matrix.det_mul] at hdetdiv
  have hprime:Prime mu:=hmu.prime
  have hafterV:mu^(Fintype.card ι-reduced.rank)∣M.det*Ulift.det:=
    hprime.pow_dvd_of_dvd_mul_left _ hVdet (by simpa [mul_assoc] using hdetdiv)
  have hafterU:mu^(Fintype.card ι-reduced.rank)∣M.det:=
    hprime.pow_dvd_of_dvd_mul_right _ hUdet hafterV
  simpa [reduced,reduceMatrix] using hafterU
section SylvesterCorank
variable {F:Type*} [Field F] [DecidableEq F]
def remainderOn (D:Polynomial F) (N:ℕ) (hD:D.Monic):
    Polynomial.degreeLT F N →ₗ[F] Polynomial.degreeLT F D.natDegree where
  toFun p:=⟨(p:Polynomial F) %ₘ D,
    Polynomial.mem_degreeLT.mpr (by
      simpa only [Polynomial.degree_eq_natDegree hD.ne_zero] using
        Polynomial.degree_modByMonic_lt (p:Polynomial F) hD)⟩
  map_add' p q:=Subtype.ext (Polynomial.add_modByMonic _ _)
  map_smul' c p:=Subtype.ext (Polynomial.smul_modByMonic c (p:Polynomial F))
theorem remainderOn_surjective (D:Polynomial F) (N:ℕ) (hD:D.Monic)
    (hdegree:D.natDegree ≤ N):Function.Surjective (remainderOn D N hD):=by
  intro q
  have hqN:(q:Polynomial F).degree < (N:WithBot ℕ):=
    (Polynomial.mem_degreeLT.mp q.property).trans_le (by exact_mod_cast hdegree)
  refine ⟨⟨q,Polynomial.mem_degreeLT.mpr hqN⟩,?_⟩
  apply Subtype.ext
  exact (Polynomial.modByMonic_eq_self_iff hD).mpr (by
    rw [Polynomial.degree_eq_natDegree hD.ne_zero]
    exact Polynomial.mem_degreeLT.mp q.property)
theorem sylvester_rank_eq_finrank_range
    (p q:Polynomial F) (m n:ℕ)
    (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n):
    (Polynomial.sylvester p q m n).rank=
      Module.finrank F (LinearMap.range (Polynomial.sylvesterMap p q hp hq)):=by
  have hmatrix:LinearMap.toMatrix
      (Polynomial.degreeLT.basisProd F m n)
      (Polynomial.degreeLT.basis F (m+n))
      (Polynomial.sylvesterMap p q hp hq)=Polynomial.sylvester p q m n:=
    Polynomial.toMatrix_sylvesterMap' p q hp hq
  rw [Matrix.rank_eq_finrank_range_toLin _
    (Polynomial.degreeLT.basis F (m+n)) (Polynomial.degreeLT.basisProd F m n)]
  rw [←hmatrix,Matrix.toLin_toMatrix]
theorem common_divisor_natDegree_le_sylvester_corank
    (p q D:Polynomial F) (m n:ℕ)
    (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
    (hD:D.Monic) (hDdegree:D.natDegree ≤ m+n)
    (hDp:D∣p) (hDq:D∣q):
    D.natDegree ≤ m+n-(Polynomial.sylvester p q m n).rank:=by
  let R:=remainderOn D (m+n) hD
  let L:=Polynomial.sylvesterMap p q hp hq
  have hsurj:Function.Surjective R:=
    remainderOn_surjective D (m+n) hD hDdegree
  have hcontain:LinearMap.range L ≤ LinearMap.ker R:=by
    rintro output ⟨input,rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change ((R (L input):Polynomial F))=0
    simp only [R,L,remainderOn,Polynomial.sylvesterMap,LinearMap.coe_mk,
      AddHom.coe_mk]
    apply (Polynomial.modByMonic_eq_zero_iff_dvd hD).mpr
    exact dvd_add (dvd_mul_of_dvd_left hDp _) (dvd_mul_of_dvd_left hDq _)
  have hremainderRank:Module.finrank F (LinearMap.range R)=D.natDegree:=by
    rw [LinearMap.range_eq_top.mpr hsurj,finrank_top]
    simpa using Module.finrank_eq_card_basis
      (Polynomial.degreeLT.basis F D.natDegree)
  have hnull:=LinearMap.finrank_range_add_finrank_ker R
  rw [hremainderRank] at hnull
  have hdomain:Module.finrank F (Polynomial.degreeLT F (m+n))=m+n:=by
    simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F (m+n))
  rw [hdomain] at hnull
  have hmono:=Submodule.finrank_mono hcontain
  have hmatrix:=sylvester_rank_eq_finrank_range p q m n hp hq
  change (Polynomial.sylvester p q m n).rank=
    Module.finrank F (LinearMap.range L) at hmatrix
  omega
theorem sum_common_divisor_natDegrees_le_sylvester_corank
    {I:Type*} [Fintype I]
    (p q:Polynomial F) (D:I → Polynomial F) (m n:ℕ)
    (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n) (hpne:p≠0)
    (hmonic:∀ i,(D i).Monic)
    (hcoprime:Pairwise fun i j => IsCoprime (D i) (D j))
    (hDp:∀ i,D i∣p) (hDq:∀ i,D i∣q):
    (∑ i,(D i).natDegree) ≤
      m+n-(Polynomial.sylvester p q m n).rank:=by
  classical
  let Dprod:Polynomial F:=∏ i,D i
  have hDprodMonic:Dprod.Monic:=by
    dsimp [Dprod]
    simpa using Polynomial.monic_prod_of_monic Finset.univ D
      (fun i _ => hmonic i)
  have hDprodP:Dprod∣p:=by
    dsimp [Dprod]
    exact Fintype.prod_dvd_of_coprime hcoprime hDp
  have hDprodQ:Dprod∣q:=by
    dsimp [Dprod]
    exact Fintype.prod_dvd_of_coprime hcoprime hDq
  have hDprodDegree:Dprod.natDegree=∑ i,(D i).natDegree:=by
    dsimp [Dprod]
    simpa using Polynomial.natDegree_prod_of_monic
      (s:=Finset.univ) (f:=D) (fun i _ => hmonic i)
  have hDdegree:Dprod.natDegree ≤ m+n:=by
    have hle:=Polynomial.natDegree_le_of_dvd hDprodP hpne
    omega
  rw [←hDprodDegree]
  exact common_divisor_natDegree_le_sylvester_corank p q Dprod m n
    hp hq hDprodMonic hDdegree hDprodP hDprodQ
end SylvesterCorank
section IrreducibleAggregation
theorem sum_irreducible_coranks_le_det_natDegree
    {I:Type*} [Fintype I]
    (M:Matrix ι ι (Polynomial K)) (mu:I → Polynomial K) (c:I → ℕ)
    (hmonic:∀ i,(mu i).Monic)
    (hirreducible:∀ i,Irreducible (mu i))
    (hcoprime:Pairwise fun i j => IsCoprime (mu i) (mu j))
    (hcorank:∀ i,
      c i ≤ Fintype.card ι-((AdjoinRoot.mk (mu i)).mapMatrix M).rank)
    (hdet:M.det≠0):
    (∑ i,c i*(mu i).natDegree) ≤ M.det.natDegree:=by
  classical
  have hfactor (i:I):(mu i)^c i∣M.det:=
    (pow_dvd_pow (mu i) (hcorank i)).trans
      (irreducible_pow_corank_dvd_det M (mu i) (hirreducible i))
  have hpowersCoprime:Pairwise fun i j =>
      IsCoprime ((mu i)^c i) ((mu j)^c j):=by
    intro i j hij
    exact (hcoprime hij).pow
  have hprodDvd:(∏ i,(mu i)^c i)∣M.det:=
    Fintype.prod_dvd_of_coprime hpowersCoprime hfactor
  have hprodMonic:(∏ i,(mu i)^c i).Monic:=by
    simpa using Polynomial.monic_prod_of_monic Finset.univ
      (fun i => (mu i)^c i) (fun i _ => (hmonic i).pow _)
  have hdegree:(∏ i,(mu i)^c i).natDegree=
      ∑ i,c i*(mu i).natDegree:=by
    rw [Polynomial.natDegree_prod_of_monic
      (s:=Finset.univ) (f:=fun i => (mu i)^c i)
      (fun i _ => (hmonic i).pow _)]
    apply Finset.sum_congr rfl
    intro i _
    exact Polynomial.natDegree_pow (mu i) (c i)
  rw [←hdegree]
  exact Polynomial.natDegree_le_of_dvd hprodDvd hdet
end IrreducibleAggregation
section RelationKernel
variable {K₀ E₁ E₂:Type} [Field K₀] [DecidableEq K₀]
  [Field E₁] [Field E₂] [Algebra K₀ E₁] [Algebra K₀ E₂]
theorem planeEval_quotientRoot_eq_aeval_map
    (mu:Polynomial K₀) [Fact (Irreducible mu)]
    [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
    (r:E₁) (P:Polynomial (Polynomial K₀)):
    PlaneFunctionFieldDegree.planeEval K₀ E₁
      (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r P=
      Polynomial.aeval r (P.map (AdjoinRoot.mk mu)):=by
  let y:E₁:=algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)
  have hcoeff:
      (algebraMap (AdjoinRoot mu) E₁).comp (AdjoinRoot.mk mu)=
        Polynomial.eval₂RingHom (algebraMap K₀ E₁) y:=by
    apply Polynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply,AdjoinRoot.mk_C,
        Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
        AdjoinRoot.algebraMap_eq] using
        (IsScalarTower.algebraMap_apply K₀ (AdjoinRoot mu) E₁ c).symm
    · simp only [RingHom.comp_apply,AdjoinRoot.mk_X,
        Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,y]
  let rhs:Polynomial (Polynomial K₀) →+*E₁:=
    (Polynomial.aeval r).toRingHom.comp
      (Polynomial.mapRingHom (AdjoinRoot.mk mu))
  have heq:PlaneFunctionFieldDegree.planeEval K₀ E₁ y r=rhs:=by
    apply Polynomial.ringHom_ext
    · intro c
      simpa only [PlaneFunctionFieldDegree.planeEval,RingHom.comp_apply,
        Polynomial.coe_mapRingHom,Polynomial.map_C,
        Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.aeval_C,
        rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using
        (congrFun (congrArg DFunLike.coe hcoeff) c).symm
    · simp only [PlaneFunctionFieldDegree.planeEval,RingHom.comp_apply,
        Polynomial.coe_mapRingHom,Polynomial.map_X,
        Polynomial.coe_evalRingHom,Polynomial.eval_X,Polynomial.aeval_X,
        rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
  exact DFunLike.congr_fun heq P
theorem mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map
    (mu:Polynomial K₀) [Fact (Irreducible mu)]
    [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
    (r:E₁) (P:Polynomial (Polynomial K₀)):
    P∈PlaneFunctionFieldDegree.relationIdeal K₀ E₁
        (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r ↔
      minpoly (AdjoinRoot mu) r∣P.map (AdjoinRoot.mk mu):=by
  change PlaneFunctionFieldDegree.planeEval K₀ E₁
      (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r P=0 ↔ _
  rw [planeEval_quotientRoot_eq_aeval_map]
  exact minpoly.dvd_iff.symm
theorem relationIdeal_eq_of_adjoinRoot_minpoly_eq
    (mu:Polynomial K₀) [Fact (Irreducible mu)]
    [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
    [Algebra (AdjoinRoot mu) E₂] [IsScalarTower K₀ (AdjoinRoot mu) E₂]
    (r₁:E₁) (r₂:E₂)
    (hmin:minpoly (AdjoinRoot mu) r₁=minpoly (AdjoinRoot mu) r₂):
    PlaneFunctionFieldDegree.relationIdeal K₀ E₁
        (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r₁=
      PlaneFunctionFieldDegree.relationIdeal K₀ E₂
        (algebraMap (AdjoinRoot mu) E₂ (AdjoinRoot.root mu)) r₂:=by
  apply Ideal.ext
  intro P
  rw [mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map,
    mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map,hmin]
theorem relative_minpolys_pairwise_coprime_of_relationIdeal_injective
    {I:Type*} [Fintype I]
    (mu:Polynomial K₀) [Fact (Irreducible mu)]
    (E:I → Type) [∀ i,Field (E i)]
    [∀ i,Algebra K₀ (E i)]
    [∀ i,Algebra (AdjoinRoot mu) (E i)]
    [∀ i,IsScalarTower K₀ (AdjoinRoot mu) (E i)]
    [∀ i,FiniteDimensional (AdjoinRoot mu) (E i)]
    (r:∀ i,E i)
    (hkernels:Function.Injective (fun i =>
      PlaneFunctionFieldDegree.relationIdeal K₀ (E i)
        (algebraMap (AdjoinRoot mu) (E i) (AdjoinRoot.root mu)) (r i))):
    Pairwise fun i j => IsCoprime
      (minpoly (AdjoinRoot mu) (r i)) (minpoly (AdjoinRoot mu) (r j)):=by
  intro i j hij
  have hiIntegral:IsIntegral (AdjoinRoot mu) (r i):=
    IsIntegral.of_finite (AdjoinRoot mu) (r i)
  have hjIntegral:IsIntegral (AdjoinRoot mu) (r j):=
    IsIntegral.of_finite (AdjoinRoot mu) (r j)
  have hiIrreducible:=minpoly.irreducible hiIntegral
  have hjIrreducible:=minpoly.irreducible hjIntegral
  apply hiIrreducible.coprime_iff_not_dvd.mpr
  intro hdvd
  have hassociated:=hiIrreducible.associated_of_dvd hjIrreducible hdvd
  have hmin:minpoly (AdjoinRoot mu) (r i)=
      minpoly (AdjoinRoot mu) (r j):=
    Polynomial.eq_of_monic_of_associated
      (minpoly.monic hiIntegral) (minpoly.monic hjIntegral) hassociated
  have hk:=relationIdeal_eq_of_adjoinRoot_minpoly_eq
    (K₀:=K₀) (E₁:=E i) (E₂:=E j) mu (r i) (r j) hmin
  exact hij (hkernels hk)
end RelationKernel
section SingleComponent
variable {E:Type*} [Field E] [Algebra K E]
theorem finrank_le_resultant_natDegree_of_adjoinRoot_component
    (P Q:Polynomial (Polynomial K)) (m n:ℕ) (mu:Polynomial K)
    [Fact (Irreducible mu)]
    [Algebra (AdjoinRoot mu) E] [IsScalarTower K (AdjoinRoot mu) E]
    [FiniteDimensional (AdjoinRoot mu) E]
    (r:E)
    (hgen:IntermediateField.adjoin (AdjoinRoot mu) ({r}:Set E)=⊤)
    (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
    (hPne:P.map (AdjoinRoot.mk mu)≠0)
    (hProot:Polynomial.aeval r (P.map (AdjoinRoot.mk mu))=0)
    (hQroot:Polynomial.aeval r (Q.map (AdjoinRoot.mk mu))=0)
    (hresultant:Polynomial.resultant P Q m n≠0):
    Module.finrank K E ≤ (Polynomial.resultant P Q m n).natDegree:=by
  have hmu:Irreducible mu:=Fact.out
  letI:FiniteDimensional K (AdjoinRoot mu):=
    (AdjoinRoot.powerBasis hmu.ne_zero).finite
  let p:Polynomial (AdjoinRoot mu):=P.map (AdjoinRoot.mk mu)
  let q:Polynomial (AdjoinRoot mu):=Q.map (AdjoinRoot.mk mu)
  let D:Polynomial (AdjoinRoot mu):=minpoly (AdjoinRoot mu) r
  have hDmonic:D.Monic:=minpoly.monic (IsIntegral.of_finite (AdjoinRoot mu) r)
  have hDp:D∣p:=minpoly.dvd (AdjoinRoot mu) r hProot
  have hDq:D∣q:=minpoly.dvd (AdjoinRoot mu) r hQroot
  have hpCap:p.natDegree ≤ m:=Polynomial.natDegree_map_le.trans hPcap
  have hqCap:q.natDegree ≤ n:=Polynomial.natDegree_map_le.trans hQcap
  have hDdegree:D.natDegree ≤ m+n:=by
    have hle:D.natDegree ≤ p.natDegree:=
      Polynomial.natDegree_le_of_dvd hDp hPne
    omega
  have hcorank:D.natDegree ≤ m+n-(Polynomial.sylvester p q m n).rank:=
    common_divisor_natDegree_le_sylvester_corank p q D m n
      hpCap hqCap hDmonic hDdegree hDp hDq
  have hpow:
      mu^(m+n-(Polynomial.sylvester p q m n).rank)∣
        Polynomial.resultant P Q m n:=by
    simpa only [Polynomial.resultant,Fintype.card_fin,
      ←Polynomial.sylvester_map_map] using
      (irreducible_pow_corank_dvd_det
        (M:=Polynomial.sylvester P Q m n) mu Fact.out)
  have hpowDegree:
      (mu^(m+n-(Polynomial.sylvester p q m n).rank)).natDegree ≤
        (Polynomial.resultant P Q m n).natDegree:=
    Polynomial.natDegree_le_of_dvd hpow hresultant
  have hrelative:D.natDegree=Module.finrank (AdjoinRoot mu) E:=
    (Field.primitive_element_iff_minpoly_natDegree_eq (AdjoinRoot mu) r).mp hgen
  have hbase:Module.finrank K (AdjoinRoot mu)=mu.natDegree:=by
    change Module.finrank K (Polynomial K ⧸ Ideal.span {mu})=mu.natDegree
    exact finrank_quotient_span_eq_natDegree
  have htotal:Module.finrank K E=mu.natDegree*D.natDegree:=by
    rw [←Module.finrank_mul_finrank K (AdjoinRoot mu) E,hbase, ←hrelative]
  rw [htotal]
  calc
    mu.natDegree*D.natDegree ≤
        mu.natDegree*(m+n-(Polynomial.sylvester p q m n).rank):=
      Nat.mul_le_mul_left _ hcorank
    _=(mu^(m+n-(Polynomial.sylvester p q m n).rank)).natDegree:=by
      rw [Polynomial.natDegree_pow,Nat.mul_comm]
    _ ≤ (Polynomial.resultant P Q m n).natDegree:=hpowDegree
end SingleComponent
section SingleComponentBidegree
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
  [Field E₀] [Algebra K₀ E₀]
theorem finrank_le_bidegree_of_adjoinRoot_component
    (P Q:Polynomial (Polynomial K₀)) (m n:ℕ) (mu:Polynomial K₀)
    [Fact (Irreducible mu)]
    [Algebra (AdjoinRoot mu) E₀] [IsScalarTower K₀ (AdjoinRoot mu) E₀]
    [FiniteDimensional (AdjoinRoot mu) E₀]
    (r:E₀)
    (hgen:IntermediateField.adjoin (AdjoinRoot mu) ({r}:Set E₀)=⊤)
    (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
    (hPne:P.map (AdjoinRoot.mk mu)≠0)
    (hProot:Polynomial.aeval r (P.map (AdjoinRoot.mk mu))=0)
    (hQroot:Polynomial.aeval r (Q.map (AdjoinRoot.mk mu))=0)
    (hresultant:Polynomial.resultant P Q m n≠0):
    Module.finrank K₀ E₀ ≤
      n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
  exact (finrank_le_resultant_natDegree_of_adjoinRoot_component P Q m n mu r
    hgen hPcap hQcap hPne hProot hQroot hresultant).trans
      (bivariate_resultant_natDegree_le (F:=K₀) P Q m n)
end SingleComponentBidegree
section ExistingGeneratingPair
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
  [Field E₀] [Algebra K₀ E₀] [FiniteDimensional K₀ E₀]
theorem finrank_le_planar_bound_without_separability
    (P Q:Polynomial (Polynomial K₀))
    (hP:Irreducible P) (hpositive:0 < P.natDegree) (hproper:¬P∣Q)
    (y r:E₀)
    (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤)
    (hPy:PlaneFunctionFieldDegree.planeEval K₀ E₀ y r P=0)
    (hQy:PlaneFunctionFieldDegree.planeEval K₀ E₀ y r Q=0):
    Module.finrank K₀ E₀ ≤
      Q.natDegree*Polynomial.Bivariate.degreeX P+
        P.natDegree*Polynomial.Bivariate.degreeX Q:=by
  classical
  have hyIntegral:IsIntegral K₀ y:=IsIntegral.of_finite K₀ y
  let mu:Polynomial K₀:=minpoly K₀ y
  have hmuIrreducible:Irreducible mu:=minpoly.irreducible hyIntegral
  letI:Fact (Irreducible mu):=⟨hmuIrreducible⟩
  let S:IntermediateField K₀ E₀:=IntermediateField.adjoin K₀ {y}
  let baseEquiv:AdjoinRoot mu ≃ₐ[K₀] S:=
    IntermediateField.adjoinRootEquivAdjoin K₀ hyIntegral
  let baseHom:AdjoinRoot mu →ₐ[K₀] E₀:=S.val.comp baseEquiv.toAlgHom
  letI:Algebra (AdjoinRoot mu) E₀:=baseHom.toRingHom.toAlgebra
  haveI:IsScalarTower K₀ (AdjoinRoot mu) E₀:=
    IsScalarTower.of_algebraMap_eq fun c => (baseHom.commutes c).symm
  letI:Module.Finite (AdjoinRoot mu) E₀:=
    Module.Finite.of_restrictScalars_finite K₀ (AdjoinRoot mu) E₀
  have hroot:algebraMap (AdjoinRoot mu) E₀ (AdjoinRoot.root mu)=y:=by
    change baseHom (AdjoinRoot.root mu)=y
    change ((S.val.comp baseEquiv.toAlgHom) (AdjoinRoot.root mu):E₀)=y
    rw [AlgHom.comp_apply]
    change ((baseEquiv (AdjoinRoot.root mu):S):E₀)=y
    rw [show baseEquiv=IntermediateField.adjoinRootEquivAdjoin K₀ hyIntegral from rfl,
      IntermediateField.adjoinRootEquivAdjoin_apply_root]
    rfl
  have hgenAll:IntermediateField.adjoin (AdjoinRoot mu)
      ({y,r}:Set E₀)=⊤:=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top
      (F:=K₀) (E:=AdjoinRoot mu) (K:=E₀) hgen
  have hgenRelative:IntermediateField.adjoin (AdjoinRoot mu)
      ({r}:Set E₀)=⊤:=by
    apply le_antisymm le_top
    rw [←hgenAll]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxy | hxr
    · subst x
      rw [←hroot]
      exact IntermediateField.adjoin.algebraMap_mem (AdjoinRoot mu) {r}
        (AdjoinRoot.root mu)
    · have:x=r:=Set.mem_singleton_iff.mp hxr
      subst x
      exact IntermediateField.subset_adjoin (AdjoinRoot mu) {r}
        (Set.mem_singleton r)
  have hcoeff:Polynomial.eval₂RingHom
      (algebraMap K₀ (AdjoinRoot mu)) (AdjoinRoot.root mu)=
      AdjoinRoot.mk mu:=by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
        AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
    · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
        AdjoinRoot.mk_X]
  have hPne:P.map (AdjoinRoot.mk mu)≠0:=by
    have hspecial:=PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap K₀ (AdjoinRoot mu)) P
      (hP.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root mu)
    rw [PlaneCoefficientExtension.bimap_specialization,hcoeff] at hspecial
    exact hspecial
  have hProot:Polynomial.aeval r (P.map (AdjoinRoot.mk mu))=0:=by
    rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
    exact hPy
  have hQroot:Polynomial.aeval r (Q.map (AdjoinRoot.mk mu))=0:=by
    rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
    exact hQy
  have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
    PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
      P Q hP hpositive hproper
  exact finrank_le_bidegree_of_adjoinRoot_component
    P Q P.natDegree Q.natDegree mu r hgenRelative le_rfl le_rfl
      hPne hProot hQroot hresultant
end ExistingGeneratingPair
section FiniteWithoutSeparability
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
  [Field E₀] [Algebra K₀ E₀]
theorem finiteDimensional_of_integral_generating_pair
    (y r:E₀) (hy:IsIntegral K₀ y) (hr:IsIntegral K₀ r)
    (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
    FiniteDimensional K₀ E₀:=by
  letI:FiniteDimensional K₀
      (IntermediateField.adjoin K₀ ({y,r}:Set E₀)):=
    IntermediateField.finiteDimensional_adjoin_pair hy hr
  letI:FiniteDimensional K₀ (⊤:IntermediateField K₀ E₀):=by
    rw [←hgen]
    infer_instance
  exact Module.Finite.of_surjective
    (IntermediateField.topEquiv (F:=K₀) (E:=E₀)).toLinearMap
    (IntermediateField.topEquiv (F:=K₀) (E:=E₀)).surjective
theorem finite_of_proper_plane_roots
    (P Q:Polynomial (Polynomial K₀))
    (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
    (hproper:¬P∣Q) (y r:E₀)
    (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r P=0)
    (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r Q=0)
    (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
    FiniteDimensional K₀ E₀:=by
  classical
  have hresne:=PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
    P Q hirreducible hpositive hproper
  have hresroot:=PlaneRootSeparability.resultant_aeval_eq_zero_of_common_root P Q
    P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive))
      y r hP hQ
  have hyIntegral:IsIntegral K₀ y:=
    IsAlgebraic.isIntegral ⟨Polynomial.resultant P Q P.natDegree Q.natDegree,
      hresne,hresroot⟩
  let S:IntermediateField K₀ E₀:=IntermediateField.adjoin K₀ {y}
  let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K₀ y⟩
  let g:Polynomial K₀ →+*S:=Polynomial.eval₂RingHom (algebraMap K₀ S) yS
  let Py:Polynomial S:=P.map g
  have hPyne:Py≠0:=by
    have h:=PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap K₀ S) P
      (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
    rw [PlaneCoefficientExtension.bimap_specialization] at h
    exact h
  have hcoefficient:(algebraMap S E₀).comp g=
      Polynomial.eval₂RingHom (algebraMap K₀ E₀) y:=by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap S E₀
          (Polynomial.eval₂ (algebraMap K₀ S) yS (Polynomial.C c))=
        Polynomial.eval₂ (algebraMap K₀ E₀) y (Polynomial.C c)
      rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K₀ S E₀ c).symm
    · change algebraMap S E₀
          (Polynomial.eval₂ (algebraMap K₀ S) yS Polynomial.X)=
        Polynomial.eval₂ (algebraMap K₀ E₀) y Polynomial.X
      rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
      rfl
  have hPyroot:Polynomial.aeval r Py=0:=by
    change Polynomial.eval₂ (algebraMap S E₀) r (P.map g)=0
    rw [Polynomial.eval₂_map,hcoefficient]
    exact hP
  have hrIntegralS:IsIntegral S r:=
    IsAlgebraic.isIntegral ⟨Py,hPyne,hPyroot⟩
  letI:FiniteDimensional K₀ S:=
    IntermediateField.adjoin.finiteDimensional hyIntegral
  letI:Algebra.IsIntegral K₀ S:=Algebra.IsIntegral.of_finite K₀ S
  have hrIntegral:IsIntegral K₀ r:=isIntegral_trans r hrIntegralS
  exact finiteDimensional_of_integral_generating_pair y r hyIntegral hrIntegral hgen
theorem finrank_le_planar_bound_from_proper_roots
    (P Q:Polynomial (Polynomial K₀))
    (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
    (hproper:¬P∣Q) (y r:E₀)
    (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r P=0)
    (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r Q=0)
    (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
    Module.finrank K₀ E₀ ≤
      Q.natDegree*Polynomial.Bivariate.degreeX P+
        P.natDegree*Polynomial.Bivariate.degreeX Q:=by
  letI:FiniteDimensional K₀ E₀:=
    finite_of_proper_plane_roots P Q hirreducible hpositive hproper y r hP hQ hgen
  apply finrank_le_planar_bound_without_separability P Q
    hirreducible hpositive hproper y r hgen
  · change (P.map (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y)).eval r=0
    simpa only [Polynomial.eval₂_eq_eval_map] using hP
  · change (Q.map (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y)).eval r=0
    simpa only [Polynomial.eval₂_eq_eval_map] using hQ
end FiniteWithoutSeparability
end
end ProximityPrize.SubmissionLower.CharacteristicFreeMatrixMultiplicityResearch
