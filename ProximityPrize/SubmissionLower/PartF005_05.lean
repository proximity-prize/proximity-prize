import ProximityPrize.SubmissionLower.PartF005_04
section Compact_PackedLegacyCore2
section PackedLegacy_R7
namespace ProximityPrize.SubmissionLower.RCN351
open scoped Classical TensorProduct
open Polynomial KaehlerDifferential RCN369 RCN370 RCN022
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
section FiniteFamily
variable {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)

theorem exists_common_nonzero_shear_coefficient
   [Infinite K] (hdz:∀ i,D K (E i) (z i)≠0):
   ∃ a:K,a≠0∧∀ i,
     D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq I:=Classical.decEq I
 let Bad:I → K → Prop:=fun i a↦
   D K (E i) (r i)+a • D K (E i) (z i)=0
 have hsingle:∀ i {a b},Bad i a → Bad i b → a=b:=by
   intro i a b ha hb
   exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
     (hdz i) ha hb
 let forbidden:Finset K:=Finset.univ.biUnion fun i↦
   if h:∃ a,Bad i a then {Classical.choose h} else ∅
 obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (insert 0 forbidden)
 refine ⟨a,?_,?_⟩
 · intro hzero
   exact ha (hzero ▸ Finset.mem_insert_self 0 forbidden)
 · intro i hbad
   have hex:∃ b,Bad i b:=⟨a,hbad⟩
   let b:=Classical.choose hex
   have hbbad:Bad i b:=Classical.choose_spec hex
   have heq:a=b:=hsingle i hbad hbbad
   have hbmem:b∈forbidden:=by
     change b∈Finset.univ.biUnion (fun i↦
       if h:∃ a,Bad i a then {Classical.choose h} else ∅)
     apply Finset.mem_biUnion.mpr
     refine ⟨i,Finset.mem_univ i,?_⟩
     simpa only [dif_pos hex,Finset.mem_singleton,b]
   exact ha (Finset.mem_insert_of_mem (heq ▸ hbmem))
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN351
end PackedLegacy_R7

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DE. -/
section PackedLegacy_DE
namespace ProximityPrize.SubmissionLower.RCN024
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
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
   RCN361.planeEval K₀ E₁
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
 have heq:RCN361.planeEval K₀ E₁ y r=rhs:=by
   apply Polynomial.ringHom_ext
   · intro c
     simpa only [RCN361.planeEval,RingHom.comp_apply,
       Polynomial.coe_mapRingHom,Polynomial.map_C,
       Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.aeval_C,
       rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using
       (congrFun (congrArg DFunLike.coe hcoeff) c).symm
   · simp only [RCN361.planeEval,RingHom.comp_apply,
       Polynomial.coe_mapRingHom,Polynomial.map_X,
       Polynomial.coe_evalRingHom,Polynomial.eval_X,Polynomial.aeval_X,
       rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
 exact DFunLike.congr_fun heq P
theorem mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   (r:E₁) (P:Polynomial (Polynomial K₀)):
   P∈RCN361.relationIdeal K₀ E₁
       (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r ↔
     minpoly (AdjoinRoot mu) r∣P.map (AdjoinRoot.mk mu):=by
 change RCN361.planeEval K₀ E₁
     (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r P=0 ↔ _
 rw [planeEval_quotientRoot_eq_aeval_map]
 exact minpoly.dvd_iff.symm
theorem relationIdeal_eq_of_adjoinRoot_minpoly_eq
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   [Algebra (AdjoinRoot mu) E₂] [IsScalarTower K₀ (AdjoinRoot mu) E₂]
   (r₁:E₁) (r₂:E₂)
   (hmin:minpoly (AdjoinRoot mu) r₁=minpoly (AdjoinRoot mu) r₂):
   RCN361.relationIdeal K₀ E₁
       (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r₁=
     RCN361.relationIdeal K₀ E₂
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
     RCN361.relationIdeal K₀ (E i)
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
end SingleComponent
section SingleComponentBidegree
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀]
end SingleComponentBidegree
section ExistingGeneratingPair
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀] [FiniteDimensional K₀ E₀]
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
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=RCN364.resultant_aeval_eq_zero_of_common_root P Q
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
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K₀ S) P
     (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.bimap_specialization] at h
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
end FiniteWithoutSeparability
end
end ProximityPrize.SubmissionLower.RCN024
end PackedLegacy_DE

/-! Packed from ProximityPrize.SubmissionLower.DF. -/
section PackedLegacy_DF
namespace ProximityPrize.SubmissionLower.RCN025
open scoped Classical BigOperators
open RCN024
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
 {I:Type*} [Fintype I]
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
     RCN361.relationIdeal K (E i)
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
 {ι:Type*} [Fintype ι] [DecidableEq ι]
 {I:Type*} [Fintype I]
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
 {I:Type*} [Fintype I]
 (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 [∀ i,FiniteDimensional K (E i)]
theorem sum_finrank_le_resultant_of_relationIdeal_injective
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval K (E i)
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
       RCN361.relationIdeal K (E j.1)
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
     RCN361.relationIdeal K (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval K (E i)
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
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K (AdjoinRoot (minpoly K (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly K (y i)))
   rw [RCN360.bimap_specialization,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 exact (sum_finrank_le_resultant_of_relationIdeal_injective
   (K:=K) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
     hkernels hProot hQroot hspecial hresultant).trans
       (bivariate_resultant_natDegree_le
         (F:=K) P Q P.natDegree Q.natDegree)
end FinitePlaneFamily
end
end ProximityPrize.SubmissionLower.RCN025
end PackedLegacy_DF

/-! Packed from ProximityPrize.SubmissionLower.AW. -/
section PackedLegacy_AW
namespace ProximityPrize.SubmissionLower.RCN008
open scoped Classical BigOperators
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
 RCN024
 RCN025
noncomputable section
variable (K:Type) [Field K]
private def familyFiniteSummary {I:Type} [Fintype I]
   (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem rationalBaseAlgebra_congr
   (P:Ideal (Original K)) [P.IsPrime]
   (i j:Fin 3) (hij:i=j)
   (hi:Transcendental K (coordinate K P i))
   (hj:Transcendental K (coordinate K P j)):
   rationalBaseAlgebra K P i hi=rationalBaseAlgebra K P j hj:=by
 subst j
 rfl
theorem plane_budget_le_original (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (planeMap K order H).natDegree*
         Polynomial.Bivariate.degreeX (planeMap K order G)+
       (planeMap K order G).natDegree*
         Polynomial.Bivariate.degreeX (planeMap K order H) ≤
     originalMixedDegree K order G H:=
 Nat.add_le_add
   (Nat.mul_le_mul (planeMap_natDegree_le K order H)
     (planeMap_degreeX_le K order G))
   (Nat.mul_le_mul (planeMap_natDegree_le K order G)
     (planeMap_degreeX_le K order H))
section FixedOrder
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem actual_finite_sum_finrank_bound_without_separability
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i)
   (hHmem:∀ i,H∈P i) (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       (planeMap K order H).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
   fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀)
         G hG (hGmem i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀)
         G H hG (hGmem i₀)).mp hdiv)
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K)
         (CoordinateField K (P i))
         (coordinate K (P i) (order 2))
         (coordinate K (P i) (order 1)) (planeMap K order G)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i)
       (planeMap K order G)=0
     exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K)
         (CoordinateField K (P i))
         (coordinate K (P i) (order 2))
         (coordinate K (P i) (order 1)) (planeMap K order H)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i)
       (planeMap K order H)=0
     exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
   have hfinite:∀ i,
       FiniteDimensional (RatFunc K) (CoordinateField K (P i)):=by
     intro i
     have hGeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom
           (algebraMap (RatFunc K) (CoordinateField K (P i)))
           (coordinate K (P i) (order 2)))
         (coordinate K (P i) (order 1)) (planeMap K order G)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hGroots i
     have hHeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom
           (algebraMap (RatFunc K) (CoordinateField K (P i)))
           (coordinate K (P i) (order 2)))
         (coordinate K (P i) (order 1)) (planeMap K order H)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hHroots i
     exact finite_of_proper_plane_roots
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (coordinate K (P i) (order 2))
       (coordinate K (P i) (order 1))
       hGeval hHeval (actual_generators K order (P i) (ht i))
   letI:∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)):=
     hfinite
   have hkernels:Function.Injective (fun i =>
       RCN361.relationIdeal (RatFunc K)
         (CoordinateField K (P i))
         (coordinate K (P i) (order 2))
         (coordinate K (P i) (order 1))):=by
     change Function.Injective (fun i =>
       actualRelationKernel K order (P i) (ht i))
     exact actualRelationKernel_family_injective K order P ht hinj
   constructor
   · exact hfinite
   · exact sum_finrank_le_planar_bound_without_separability
       (K:=RatFunc K) (I:=I)
       (fun i => CoordinateField K (P i))
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (fun i => coordinate K (P i) (order 2))
       (fun i => coordinate K (P i) (order 1))
       (fun i => actual_generators K order (P i) (ht i))
       hkernels hGroots hHroots
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end FixedOrder
section OriginalOrder
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem original_finite_sum_finrank_bound_without_separability
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i)
   (hHmem:∀ i,H∈P i) (hproper:¬ G∣H):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   obtain ⟨order',hor,hbase,hpositive⟩:=
     exists_positive_outer_order K order (P i₀) G hG (hGmem i₀) (ht i₀)
   have hbudget:originalMixedDegree K order' G H=
       originalMixedDegree K order G H:=by
     rcases hor with rfl | rfl
     · rfl
     · exact originalMixedDegree_swap K order G H
   have ht':∀ i,
       Transcendental K (coordinate K (P i) (order' 0)):=by
     intro i
     simpa only [hbase] using ht i
   have hresult:
       letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
         fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
       (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
         (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
           originalMixedDegree K order' G H:=by
     letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
       fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     obtain ⟨hfinite,hbound⟩:=
       actual_finite_sum_finrank_bound_without_separability
         K order' P ht' hinj G H hG hGmem hHmem hproper hpositive
     exact ⟨hfinite,hbound.trans (plane_budget_le_original K order' G H)⟩
   have halg:
       (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
         (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
     funext i
     exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0)
       hbase (ht' i) (ht i)
   change familyFiniteSummary K P
     (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
       (originalMixedDegree K order' G H) at hresult
   rw [halg,hbudget] at hresult
   exact hresult
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end OriginalOrder
end
end ProximityPrize.SubmissionLower.RCN008
end PackedLegacy_AW

/-! Packed from ProximityPrize.SubmissionLower.X7. -/
section PackedLegacy_X7
namespace ProximityPrize.SubmissionLower.RCN021
open scoped Classical BigOperators
open RCN371 RCN011
 RCN009 RCN013
 RCN008
 RCN024
 RCN025 RCN022
noncomputable section
set_option maxHeartbeats 1000000
variable (K:Type) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance:IsLocalization (coefficientDenominators K)
   (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
section OneEvaluation
variable (L:Type) [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3) (e:Original K →ₐ[K] L)
def collectedEvaluation:Collected K →+*L:=
 e.toRingHom.comp (collect K order).symm.toRingHom
@[simp] theorem collectedEvaluation_collect (F:Original K):
   collectedEvaluation K L order e (collect K order F)=e F:=by
 simp [collectedEvaluation]
@[simp] theorem collectedEvaluation_C (H:Polynomial K):
   collectedEvaluation K L order e (MvPolynomial.C H)=
     Polynomial.aeval (e (MvPolynomial.X (order 0))) H:=by
 have hhom:e.toRingHom.comp (coefficientLift K order)=
     (Polynomial.aeval (e (MvPolynomial.X (order 0)))).toRingHom:=by
   apply Polynomial.ringHom_ext
   · intro a
     change e (coefficientLift K order (Polynomial.C a))=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) (Polynomial.C a)
     rw [coefficientLift_C,Polynomial.aeval_C]
     exact e.commutes a
   · change e (coefficientLift K order Polynomial.X)=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) Polynomial.X
     rw [coefficientLift_X,Polynomial.aeval_X]
 exact RingHom.congr_fun hhom H
theorem coefficientDenominators_disjoint_of_evaluation
   (G:Original K) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collect K order G}:Set (Collected K)):Set (Collected K)):=by
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨H,hH,rfl⟩:=Submonoid.mem_map.mp ha
 have hH0:H≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hH
 obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hI
 have hzero:Polynomial.aeval (e (MvPolynomial.X (order 0))) H=0:=by
   have heval:=congrArg (collectedEvaluation K L order e) hU
   simpa only [map_mul,collectedEvaluation_collect,collectedEvaluation_C,
     hroot,zero_mul] using heval
 exact hH0 (transcendental_iff.mp ht H hzero)
theorem rationalMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (rationalMap K order G):=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collect K order G}:Set (Collected K)))
   (collected_principal_isPrime K order G hG)
   (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)
 have hp':
     (Ideal.span ({rationalMap K order G}:Set (RationalPolynomials K))).IsPrime:=by
   simpa only [Ideal.map_span,Set.image_singleton, ←rationalMap_eq] using hp
 exact ((Ideal.span_singleton_prime
   (rationalMap_ne_zero K order G hG.ne_zero)).mp hp').irreducible
theorem rationalMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   rationalMap K order G∣rationalMap K order H ↔ G∣H:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collect K order H)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalMap_eq] using hdiv
   have hu:collect K order H∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K order G hG)
     (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)] at hu
   obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collect K order).symm U,?_⟩
   apply (collect K order).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
 · exact fun hdiv↦map_dvd (rationalMap K order) hdiv
theorem planeMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (planeMap K order G):=
 (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_evaluation K L order e G hG hroot ht)
theorem planeMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_evaluation K L order e G H hG hroot ht).mp hrat
 · exact fun hdiv↦map_dvd (planeMap K order) hdiv
def planeEvaluation
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   PlaneRing K →+*L:=
 (Polynomial.evalRingHom (e (MvPolynomial.X (order 1)))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
       (e (MvPolynomial.X (order 2)))))
@[simp] theorem planeEvaluation_C_C
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))) (a:RatFunc K):
   planeEvaluation K L order e ht (Polynomial.C (Polynomial.C a))=
     elementEmbedding K L (e (MvPolynomial.X (order 0))) ht a:=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht Polynomial.X=
     e (MvPolynomial.X (order 1)):=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_C_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
     e (MvPolynomial.X (order 2)):=by
 simp [planeEvaluation]
theorem elementEmbedding_polynomial (s:L) (hs:Transcendental K s)
   (f:Polynomial K):
   elementEmbedding K L s hs (algebraMap (Polynomial K) (RatFunc K) f)=
     Polynomial.aeval s f:=
 RatFunc.liftRingHom_algebraMap _ _ f
theorem planeEvaluation_comp_planeMap
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (planeEvaluation K L order e ht).comp (planeMap K order)=e.toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,planeEvaluation_C_C,
     elementEmbedding_polynomial,Polynomial.aeval_C]
   exact (e.commutes a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,planeEvaluation_C_C,
       elementEmbedding_variable]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,planeEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h↦hj (Fin.ext h)
     have hjone:j.val≠1:=fun h↦hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,planeEvaluation_C_X]
   rfl
def relationKernel
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=RingHom.ker (planeEvaluation K L order e ht)
theorem relationKernel_contract
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (relationKernel K L order e ht).comap (planeMap K order)=
     RingHom.ker e.toRingHom:=by
 rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_planeMap]
end OneEvaluation
section FixedFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (e:∀ i,Original K →ₐ[K] E i)
theorem finite_sum_finrank_bound
   (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
   (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree):
   letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
     (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i)) ≤
       (planeMap K order H).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
   (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hHroot i
   have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=by
     intro i
     have hGeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hGroots i
     have hHeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hHroots i
     exact finite_of_proper_plane_roots (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
       hGeval hHeval (hgen i)
   letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change relationKernel K (E i) order (e i) (ht i)=
       relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [relationKernel_contract] using hc
   exact ⟨hfinite,
     sum_finrank_le_planar_bound_without_separability
       (K:=RatFunc K) (I:=I) E
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (fun i↦e i (MvPolynomial.X (order 2)))
       (fun i↦e i (MvPolynomial.X (order 1))) hgen
       hrelation hGroots hHroots⟩
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end FixedFamily
end
end ProximityPrize.SubmissionLower.RCN021
end PackedLegacy_X7

/-! Packed from ProximityPrize.SubmissionLower.EE. -/
section PackedLegacy_EE
namespace ProximityPrize.SubmissionLower.RCN124
open scoped Classical BigOperators
open RCN371 RCN011
 RCN009 RCN013
 RCN008
 RCN024
 RCN025 RCN022
 RCN021 RCN012
noncomputable section
theorem sum_finrank_le_ordinary_resultant_without_separability
   {F:Type} [Field F] {I:Type*} [Fintype I]
   (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra F (E i)]
   [∀ i,FiniteDimensional F (E i)]
   (P Q:Polynomial (Polynomial F))
   (hP:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin F
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦
     RCN361.relationIdeal F (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval F (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval F (E i)
     (y i) (r i) Q=0):
   (∑ i,Module.finrank F (E i)) ≤
     (Polynomial.resultant P Q).natDegree:=by
 classical
 letI:DecidableEq F:=Classical.decEq F
 have hspecial:∀ f∈
     (Finset.univ.image (fun i↦minpoly F (y i))),
       P.map (AdjoinRoot.mk f)≠0:=by
   intro f hf
   obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
   letI:Fact (Irreducible (minpoly F (y i))):=
     ⟨minpoly.irreducible (IsIntegral.of_finite F (y i))⟩
   have hcoeff:Polynomial.eval₂RingHom
       (algebraMap F (AdjoinRoot (minpoly F (y i))))
         (AdjoinRoot.root (minpoly F (y i)))=
       AdjoinRoot.mk (minpoly F (y i)):=by
     apply Polynomial.ringHom_ext
     · intro c
       simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
         AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
     · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
         AdjoinRoot.mk_X]
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap F (AdjoinRoot (minpoly F (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly F (y i)))
   rw [RCN360.bimap_specialization,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 simpa only using
   (sum_finrank_le_resultant_of_relationIdeal_injective
     (K:=F) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
       hkernels hProot hQroot hspecial hresultant)
variable (K:Type) [Field K]
theorem finite_sum_finrank_bound_trapezoid
   (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
   (E:I → Type)
   [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   (e:∀ i,Original K →ₐ[K] E i)
   (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
         (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
   (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree)
   (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hHouter:(planeMap K order H).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hHsupport:∀ d∈(rationalMap K order H).support,
     d 0+d 1 ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalH-m*n ≤ cap):
   letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
     (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
       (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i)) ≤ cap:=by
 classical
 letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
   (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
     (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hbase:=finite_sum_finrank_bound K order E e ht hgen hkernels
     G H hG hGroot hHroot hproper hpositive
   have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=hbase.1
   letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order G)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order H)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hHroot i
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change relationKernel K (E i) order (e i) (ht i)=
       relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [relationKernel_contract] using hc
   refine ⟨hfinite,?_⟩
   exact (sum_finrank_le_ordinary_resultant_without_separability E
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     (fun i↦e i (MvPolynomial.X (order 2)))
     (fun i↦e i (MvPolynomial.X (order 1))) hgen hrelation
     hGroots hHroots).trans
       (planeMap_trapezoid_resultant_natDegree_le K order G H
         n mCap totalG totalH cap hHne hGouter hHouter
         hGsupport hHsupport hbudget)
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end
end ProximityPrize.SubmissionLower.RCN124
end PackedLegacy_EE

/-! Packed from ProximityPrize.SubmissionLower.Y7. -/
section PackedLegacy_Y7
namespace ProximityPrize.SubmissionLower.RCN093
open scoped Classical BigOperators
open RCN002 RCN005
 RCN022 RCN011
 RCN371
open RCN125 RCN124
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def affineU (lam:K):CoordinateField K P:=
 coordinate K P 0+lam • coordinate K P 2
def affineV (μ ν:K):CoordinateField K P:=
 coordinate K P 1+μ • coordinate K P 0+ν • coordinate K P 2
def flagEvaluation (lam μ ν:K):
   MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P:=
 MvPolynomial.aeval ![affineU K P lam,affineV K P μ ν,
   coordinate K P 2]
@[simp] theorem flagEvaluation_X_zero (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 0)=affineU K P lam:=by
 simp [flagEvaluation]
@[simp] theorem flagEvaluation_X_one (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 1)=affineV K P μ ν:=by
 simp [flagEvaluation]
@[simp] theorem flagEvaluation_X_two (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 2)=coordinate K P 2:=by
 simp [flagEvaluation]
end
end ProximityPrize.SubmissionLower.RCN093
end PackedLegacy_Y7
end Compact_PackedLegacyCore2
