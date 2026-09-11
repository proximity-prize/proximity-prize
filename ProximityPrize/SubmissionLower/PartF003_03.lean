import ProximityPrize.SubmissionLower.PartF003_02
section Compact_PackedLegacyCore1
section PackedLegacy_H1
namespace ProximityPrize.SubmissionLower.RCN009
open RCN371 RCN011
noncomputable section
variable (K:Type) [Field K]
section FirstCoordinate
variable {A:Type} [Field A]

theorem firstMap_monomial (φ:Polynomial K →+*A)
   (d:Fin 3 →₀ ℕ) (a:K):
   firstMap K φ (MvPolynomial.monomial d a)=
     MvPolynomial.monomial d.tail (φ (Polynomial.C a)*(φ Polynomial.X)^d 0):=by
 rw [firstMap_eq_eval₂Hom,MvPolynomial.eval₂Hom_monomial]
 simp only [RingHom.comp_apply,Finsupp.prod_pow,Fin.prod_univ_succ,Fin.cases_zero,
   Fin.cases_succ,MvPolynomial.monomial_eq,Finsupp.tail_apply,map_mul,map_pow]
 ring
theorem support_firstMap_subset (φ:Polynomial K →+*A)
   (F:MvPolynomial (Fin 3) K):
   (firstMap K φ F).support ⊆ F.support.image Finsupp.tail:=by
 classical
 have hsum:firstMap K φ F=
     ∑ d∈F.support,firstMap K φ (MvPolynomial.monomial d (MvPolynomial.coeff d F)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 intro e he
 rw [hsum] at he
 obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
 rw [firstMap_monomial] at hed
 have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
 exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
theorem firstMap_degreeOf_le (φ:Polynomial K →+*A)
   (F:MvPolynomial (Fin 3) K) (i:Fin 2):
   (firstMap K φ F).degreeOf i ≤ F.degreeOf i.succ:=by
 classical
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro e he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_firstMap_subset K φ F he)
 exact MvPolynomial.monomial_le_degreeOf i.succ hd
end FirstCoordinate
theorem rationalMap_eq_firstMap (order:Fin 3 ≃ Fin 3) (F:Original K):
   rationalMap K order F=firstMap K (algebraMap (Polynomial K) (RatFunc K))
     (MvPolynomial.rename order.symm F):=rfl
theorem rationalMap_degreeOf_le (order:Fin 3 ≃ Fin 3) (F:Original K) (i:Fin 2):
   (rationalMap K order F).degreeOf i ≤ F.degreeOf (order i.succ):=by
 rw [rationalMap_eq_firstMap]
 calc
   _ ≤ (MvPolynomial.rename order.symm F).degreeOf i.succ:=
     firstMap_degreeOf_le K _ _ i
   _=F.degreeOf (order i.succ):=by
     simpa only [Equiv.symm_apply_apply] using
       (MvPolynomial.degreeOf_rename_of_injective (p:=F) order.symm.injective
         (order i.succ))
section NestedDegrees
variable (A:Type) [Field A]
theorem bivariateEquiv_natDegree (f:MvPolynomial (Fin 2) A):
   (bivariateEquiv A f).natDegree=f.degreeOf 0:=by
 change (Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
   (MvPolynomial.finSuccEquiv A 1 f)).natDegree=f.degreeOf 0
 rw [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.uniqueAlgEquiv A (Fin 1)).injective]
 exact MvPolynomial.natDegree_finSuccEquiv f
theorem uniqueAlgEquiv_natDegree_le (f:MvPolynomial (Fin 1) A):
   (MvPolynomial.uniqueAlgEquiv A (Fin 1) f).natDegree ≤ f.degreeOf 0:=by
 classical
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 rw [MvPolynomial.coeff_uniqueAlgEquiv]
 by_contra hne
 have hd:=MvPolynomial.monomial_le_degreeOf (0:Fin 1)
   (MvPolynomial.mem_support_iff.mpr hne)
 have hdefault:(default:Fin 1)=0:=Subsingleton.elim _ _
 simp only [hdefault,Finsupp.single_eq_same] at hd
 omega
theorem bivariateEquiv_degreeX_le (f:MvPolynomial (Fin 2) A):
   Polynomial.Bivariate.degreeX (bivariateEquiv A f) ≤ f.degreeOf 1:=by
 classical
 unfold Polynomial.Bivariate.degreeX
 apply Finset.sup_le
 intro j _
 rw [show (bivariateEquiv A f).coeff j=
   MvPolynomial.uniqueAlgEquiv A (Fin 1) ((MvPolynomial.finSuccEquiv A 1 f).coeff j) by
   simp [bivariateEquiv]]
 exact (uniqueAlgEquiv_natDegree_le A _).trans
   (MvPolynomial.degreeOf_coeff_finSuccEquiv f (0:Fin 1) j)
end NestedDegrees
theorem planeMap_natDegree_le (order:Fin 3 ≃ Fin 3) (F:Original K):
   (planeMap K order F).natDegree ≤ F.degreeOf (order 1):=by
 change (bivariateEquiv (RatFunc K) (rationalMap K order F)).natDegree ≤ _
 rw [bivariateEquiv_natDegree]
 exact rationalMap_degreeOf_le K order F (0:Fin 2)
theorem planeMap_degreeX_le (order:Fin 3 ≃ Fin 3) (F:Original K):
   Polynomial.Bivariate.degreeX (planeMap K order F) ≤ F.degreeOf (order 2):=by
 exact (bivariateEquiv_degreeX_le (RatFunc K) (rationalMap K order F)).trans
   (rationalMap_degreeOf_le K order F (1:Fin 2))
theorem planeMap_resultant_natDegree_le (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree ≤
     H.degreeOf (order 1)*G.degreeOf (order 2)+
       G.degreeOf (order 1)*H.degreeOf (order 2):=by
 exact (bivariate_resultant_natDegree_le (planeMap K order G) (planeMap K order H)
   (planeMap K order G).natDegree (planeMap K order H).natDegree).trans
     (Nat.add_le_add
       (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
       (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H)))
theorem original_characteristic_gates (order:Fin 3 ≃ Fin 3) (G H:Original K) (p:ℕ)
   (houter:G.degreeOf (order 1) < p)
   (hmixed:H.degreeOf (order 1)*G.degreeOf (order 2)+
     G.degreeOf (order 1)*H.degreeOf (order 2) < p):
   (planeMap K order G).natDegree < p∧
     (Polynomial.resultant (planeMap K order G) (planeMap K order H)).natDegree < p:=
 ⟨(planeMap_natDegree_le K order G).trans_lt houter,
   (planeMap_resultant_natDegree_le K order G H).trans_lt hmixed⟩
end
end ProximityPrize.SubmissionLower.RCN009
end PackedLegacy_H1

/-! Packed from ProximityPrize.SubmissionLower.X5. -/
section PackedLegacy_X5
namespace ProximityPrize.SubmissionLower.RCN013
open RCN002 RCN371 RCN011 RCN009
noncomputable section
variable (K:Type) [Field K]
def swapOtherOrder (order:Fin 3 ≃ Fin 3):Fin 3 ≃ Fin 3:=
 (Equiv.swap (1:Fin 3) 2).trans order
@[simp] theorem swapOtherOrder_zero (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 0=order 0:=by
 simp [swapOtherOrder,Equiv.swap_apply_def]
@[simp] theorem swapOtherOrder_one (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 1=order 2:=by
 simp [swapOtherOrder]
@[simp] theorem swapOtherOrder_two (order:Fin 3 ≃ Fin 3):
   swapOtherOrder order 2=order 1:=by
 simp [swapOtherOrder]
theorem rationalMap_first (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 0))=
     MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X):=by
 simp [rationalMap]
theorem rationalMap_outer (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 1))=MvPolynomial.X 0:=by
 have h:=collect_X_other K order (0:Fin 2)
 change collect K order (MvPolynomial.X (order 1))=MvPolynomial.X 0 at h
 simp [rationalMap,h]
theorem rationalMap_inner (order:Fin 3 ≃ Fin 3):
   rationalMap K order (MvPolynomial.X (order 2))=MvPolynomial.X 1:=by
 have h:=collect_X_other K order (1:Fin 2)
 change collect K order (MvPolynomial.X (order 2))=MvPolynomial.X 1 at h
 simp [rationalMap,h]
theorem rationalMap_swapOtherOrder (order:Fin 3 ≃ Fin 3):
   rationalMap K (swapOtherOrder order)=
     (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)).toRingHom.comp
       (rationalMap K order):=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp [rationalMap]
 · intro j
   obtain ⟨i,rfl⟩:=order.surjective j
   have hi:i=0∨i=1∨i=2:=by omega
   rcases hi with rfl | rfl | rfl
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 0))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 0)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 0))=
         MvPolynomial.C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) by
       simpa only [swapOtherOrder_zero] using rationalMap_first K (swapOtherOrder order)]
     rw [rationalMap_first]
     simp
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 1))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 1)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 1))=
         MvPolynomial.X 1 by
       simpa only [swapOtherOrder_two] using rationalMap_inner K (swapOtherOrder order)]
     rw [rationalMap_outer]
     simp
   · change rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 2))=
       MvPolynomial.rename (Equiv.swap (0:Fin 2) 1)
         (rationalMap K order (MvPolynomial.X (order 2)))
     rw [show rationalMap K (swapOtherOrder order) (MvPolynomial.X (order 2))=
         MvPolynomial.X 0 by
       simpa only [swapOtherOrder_one] using rationalMap_outer K (swapOtherOrder order)]
     rw [rationalMap_inner]
     simp
theorem swapped_outer_degree (order:Fin 3 ≃ Fin 3) (F:Original K):
   (planeMap K (swapOtherOrder order) F).natDegree=
     (rationalMap K order F).degreeOf 1:=by
 change (bivariateEquiv (RatFunc K) (rationalMap K (swapOtherOrder order) F)).natDegree=_
 rw [bivariateEquiv_natDegree,rationalMap_swapOtherOrder]
 change (MvPolynomial.rename (Equiv.swap (0:Fin 2) 1) (rationalMap K order F)).degreeOf 0=_
 simpa only [Equiv.swap_apply_right] using
   (MvPolynomial.degreeOf_rename_of_injective (p:=rationalMap K order F)
     (Equiv.swap (0:Fin 2) 1).injective (1:Fin 2))
theorem positive_degree_of_irreducible {A:Type} [Field A]
   (f:MvPolynomial (Fin 2) A) (hf:Irreducible f):
   0 < f.degreeOf 0∨0 < f.degreeOf 1:=by
 classical
 by_cases h0:0 < f.degreeOf 0
 · exact Or.inl h0
 by_cases h1:0 < f.degreeOf 1
 · exact Or.inr h1
 exfalso
 have hdeg:∀ i:Fin 2,f.degreeOf i=0:=by
   intro i
   have hi:i=0∨i=1:=by omega
   rcases hi with rfl | rfl <;> omega
 have hconst:f=MvPolynomial.C (MvPolynomial.coeff 0 f):=by
   apply MvPolynomial.ext
   intro d
   by_cases hd:d=0
   · subst d
     simp
   · have hzero:MvPolynomial.coeff d f=0:=by
       by_contra hne
       have hm:d∈f.support:=MvPolynomial.mem_support_iff.mpr hne
       apply hd
       apply Finsupp.ext
       intro i
       have hle:=MvPolynomial.monomial_le_degreeOf i hm
       rw [hdeg i] at hle
       exact Nat.eq_zero_of_le_zero hle
     simp [hzero,Ne.symm hd]
 have ha:MvPolynomial.coeff 0 f≠0:=by
   intro h
   apply hf.ne_zero
   rw [hconst,h,map_zero]
 apply hf.not_isUnit
 rw [hconst]
 exact (isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C
theorem exists_positive_outer_order (order:Fin 3 ≃ Fin 3)
   (P:Ideal (Original K)) [P.IsPrime] (G:Original K)
   (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0))):
   ∃ order':Fin 3 ≃ Fin 3,
     (order'=order∨order'=swapOtherOrder order)∧
     order' 0=order 0∧0 < (planeMap K order' G).natDegree:=by
 have hirr:=rationalMap_irreducible_of_component K order P G hG hmem ht
 rcases positive_degree_of_irreducible (rationalMap K order G) hirr with h0 | h1
 · refine ⟨order,Or.inl rfl,rfl,?_⟩
   change 0 < (bivariateEquiv (RatFunc K) (rationalMap K order G)).natDegree
   rwa [bivariateEquiv_natDegree]
 · exact ⟨swapOtherOrder order,Or.inr rfl,swapOtherOrder_zero order,
     by rwa [swapped_outer_degree]⟩
def originalMixedDegree (order:Fin 3 ≃ Fin 3) (G H:Original K):ℕ:=
 H.degreeOf (order 1)*G.degreeOf (order 2)+
   G.degreeOf (order 1)*H.degreeOf (order 2)
@[simp] theorem originalMixedDegree_swap (order:Fin 3 ≃ Fin 3) (G H:Original K):
   originalMixedDegree K (swapOtherOrder order) G H=originalMixedDegree K order G H:=by
 simp only [originalMixedDegree,swapOtherOrder_one,swapOtherOrder_two]
 ring
theorem exists_positive_characteristic_order (order:Fin 3 ≃ Fin 3)
   (P:Ideal (Original K)) [P.IsPrime] (G H:Original K) (p:ℕ)
   (hG:Irreducible G) (hmem:G∈P)
   (ht:Transcendental K (coordinate K P (order 0)))
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   ∃ order':Fin 3 ≃ Fin 3,
     order' 0=order 0∧
     originalMixedDegree K order' G H=originalMixedDegree K order G H∧
     0 < (planeMap K order' G).natDegree∧
     (planeMap K order' G).natDegree < p∧
     (Polynomial.resultant (planeMap K order' G) (planeMap K order' H)).natDegree < p:=by
 obtain ⟨order',hor,hbase,hpos⟩:=exists_positive_outer_order K order P G hG hmem ht
 have hbudget:originalMixedDegree K order' G H=originalMixedDegree K order G H:=by
   rcases hor with rfl | rfl
   · rfl
   · exact originalMixedDegree_swap K order G H
 have hout:G.degreeOf (order' 1) < p:=by
   rcases hor with rfl | rfl
   · exact h1
   · simpa only [swapOtherOrder_one] using h2
 have hmix':H.degreeOf (order' 1)*G.degreeOf (order' 2)+
     G.degreeOf (order' 1)*H.degreeOf (order' 2) < p:=by
   change originalMixedDegree K order' G H < p
   rwa [hbudget]
 exact ⟨order',hbase,hbudget,hpos,
   original_characteristic_gates K order' G H p hout hmix'⟩
end
end ProximityPrize.SubmissionLower.RCN013
end PackedLegacy_X5

/-! Packed from ProximityPrize.SubmissionLower.G9. -/
section PackedLegacy_G9
namespace ProximityPrize.SubmissionLower.RCN004
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
noncomputable section
variable (K:Type) [Field K]
theorem rationalBaseAlgebra_congr (P:Ideal (Original K)) [P.IsPrime]
   (i j:Fin 3) (hij:i=j)
   (hi:Transcendental K (coordinate K P i))
   (hj:Transcendental K (coordinate K P j)):
   rationalBaseAlgebra K P i hi=rationalBaseAlgebra K P j hj:=by
 subst j
 rfl
private def singleSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)) (B:ℕ):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
   Module.finrank (RatFunc K) (CoordinateField K P) ≤ B
private def fieldsSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
private def familySummary {I:Type} [Fintype I] (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem plane_budget_le_original (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
     (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H) ≤
       originalMixedDegree K order G H:=
 Nat.add_le_add
   (Nat.mul_le_mul (planeMap_natDegree_le K order H) (planeMap_degreeX_le K order G))
   (Nat.mul_le_mul (planeMap_natDegree_le K order G) (planeMap_degreeX_le K order H))
section Single
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
theorem original_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order G H:=by
 obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
   exists_positive_characteristic_order K order P G H p hG hGmem ht h1 h2 hmixed
 have ht':Transcendental K (coordinate K P (order' 0)):=by
   simpa only [hbase] using ht
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
       Module.finrank (RatFunc K) (CoordinateField K P) ≤ originalMixedDegree K order' G H:=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order' 0) ht'
   obtain ⟨hfd,hsep,hbound⟩:=actual_finite_separable_finrank_bound
     K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
   exact ⟨hfd,hsep,hbound.trans (plane_budget_le_original K order' G H)⟩
 change singleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
   (originalMixedDegree K order' G H) at hresult
 rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht,hbudget] at hresult
 exact hresult
end Single
section Family
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem original_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   obtain ⟨order',hbase,hbudget,hpos,houter,hres⟩:=
     exists_positive_characteristic_order K order (P i₀) G H p
       hG (hGmem i₀) (ht i₀) h1 h2 hmixed
   have ht':∀ i,Transcendental K (coordinate K (P i) (order' 0)):=by
     intro i
     simpa only [hbase] using ht i
   have hresult:
       letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
         fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
       (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
         Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
         (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
           originalMixedDegree K order' G H:=by
     letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
       fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     obtain ⟨hfields,hbound⟩:=actual_finite_separable_sum_finrank_bound
       K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
     exact ⟨hfields,hbound.trans (plane_budget_le_original K order' G H)⟩
   have halg:(fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
       (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
     funext i
     exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0) hbase (ht' i) (ht i)
   change familySummary K P (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
     (originalMixedDegree K order' G H) at hresult
   rw [halg,hbudget] at hresult
   exact hresult
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end Family
theorem all_transcendental_coordinates_finite_separable
   (P:Ideal (Original K)) [P.IsPrime] (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:∀ j k:Fin 3,j≠k →
     H.degreeOf j*G.degreeOf k+G.degreeOf j*H.degreeOf k < p):
   ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 intro i hi
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hneq:order 1≠order 2:=by
   intro h
   have heq:=order.injective h
   exact (by decide:(1:Fin 3)≠2) heq
 have hbudget:originalMixedDegree K order G H < p:=
   hmixed (order 1) (order 2) hneq
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hbudget
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end ProximityPrize.SubmissionLower.RCN004
end PackedLegacy_G9

/-! Packed from ProximityPrize.SubmissionLower.AV. -/
section PackedLegacy_AV
namespace ProximityPrize.SubmissionLower.RCN001
open RCN002 RCN005
 RCN371 RCN007 RCN013
 RCN004
noncomputable section
variable (K:Type) [Field K]
section Family
variable {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem sum_actualCoordinateDegree_le_original
   (order:Fin 3 ≃ Fin 3) (hinj:Function.Injective P)
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (h1:G.degreeOf (order 1) < p) (h2:G.degreeOf (order 2) < p)
   (hmixed:originalMixedDegree K order G H < p):
   (∑ i,actualCoordinateDegree K (P i) (order 0)) ≤ originalMixedDegree K order G H:=by
 classical
 let s:Set I:={i | Transcendental K (coordinate K (P i) (order 0))}
 let D:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (CoordinateField K (P i)):=
     rationalBaseAlgebra K (P i) (order 0) i.2
   Module.finrank (RatFunc K) (CoordinateField K (P i))
 have hinj':Function.Injective (fun i:s => P i):=by
   intro i j h
   apply Subtype.ext
   exact hinj h
 have hbound:(∑ i:s,D i) ≤ originalMixedDegree K order G H:=by
   have h:=original_finite_separable_sum_finrank_bound K order (fun i:s => P i)
     (fun i => i.2) hinj' p G H hG (fun i => hGmem i) (fun i => hHmem i)
     hproper h1 h2 hmixed
   exact h.2
 calc
   _=∑ i:s,D i:=by
     apply Finset.sum_congr_set s (fun i => actualCoordinateDegree K (P i) (order 0)) D
     · intro i hi
       exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
     · intro i hi
       change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
       exact dif_neg hi
   _ ≤ _:=hbound
end Family
def coordinateMixedDegree (G H:Original K) (i:Fin 3):ℕ:=
 originalMixedDegree K (Equiv.swap 0 i) G H
@[simp] theorem coordinateMixedDegree_zero (G H:Original K):
   coordinateMixedDegree K G H 0=
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_one (G H:Original K):
   coordinateMixedDegree K G H 1=
     H.degreeOf 0*G.degreeOf 2+G.degreeOf 0*H.degreeOf 2:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def]
@[simp] theorem coordinateMixedDegree_two (G H:Original K):
   coordinateMixedDegree K G H 2=
     H.degreeOf 0*G.degreeOf 1+G.degreeOf 0*H.degreeOf 1:=by
 simp [coordinateMixedDegree,originalMixedDegree,Equiv.swap_apply_def] <;> ring
theorem sum_actualCoordinateDegree_at_le
   {I:Type} [Fintype I] (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (hinj:Function.Injective P) (j:Fin 3) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H) (hdegree:∀ k:Fin 3,G.degreeOf k < p)
   (hmixed:coordinateMixedDegree K G H j < p):
   (∑ i,actualCoordinateDegree K (P i) j) ≤ coordinateMixedDegree K G H j:=by
 have h:=sum_actualCoordinateDegree_le_original K P (Equiv.swap 0 j) hinj p G H
   hG hGmem hHmem hproper (hdegree ((Equiv.swap 0 j) 1))
     (hdegree ((Equiv.swap 0 j) 2)) hmixed
 simpa only [coordinateMixedDegree,Equiv.swap_apply_left] using h
end
end ProximityPrize.SubmissionLower.RCN001
end PackedLegacy_AV

/-! Packed from ProximityPrize.SubmissionLower.F. -/
section PackedLegacy_F
namespace ProximityPrize.SubmissionLower.RCN243
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN319 RCN238 RCN264
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def regularitySurface (F:MvPolynomial (Fin 4) K):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)
theorem selectedPoint_evaluation (selected:K → Polynomial K) (γ:K)
   (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ Q)=
     MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X)) Q:=by
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
theorem noLargeSelectedPencil_mono
   (selected:K → Polynomial K) (Γ Δ:Finset K) (w e:ℕ)
   (hsub:Δ ⊆ Γ) (hno:NoLargeSelectedPencil selected Γ w e):
   NoLargeSelectedPencil selected Δ w e:=by
 intro P₀ P₁ h₀ h₁
 apply le_trans (Finset.card_le_card ?_) (hno P₀ P₁ h₀ h₁)
 intro γ hγ
 obtain ⟨hΔ,hp⟩:=Finset.mem_filter.mp hγ
 exact Finset.mem_filter.mpr ⟨hsub hΔ,hp⟩
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem proper_cut_seed_bound_of_projection_sum
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i):
   Γ.card*(a-w) ≤ (nodes.card-w)*(∑ i,cap i*budget i)+
     (e+1)*(a-w)*budget 2:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let degree:RegularComponent Ω G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Ω C.1 i
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have htmem:=regularComponent_T_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Ω C.1:=
     all_transcendental_coordinates_finite_separable Ω C.1 p G T hG hgmem htmem
       hproper hGdegree hcutDegree
   have hcount:=prime_seed_incidence_sharp φ C.1 hproj
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ => hdegree γ (hsub hγ))
     (fun γ hγ => hsolution γ (hsub hγ))
     (fun γ hγ => hregular γ (hsub hγ))
     (fun γ hγ => componentSeeds_on_prime Ω G T H Γ (selectedPoint φ selected) C γ hγ)
     (fun γ hγ => hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil) cap hcap
   exact hcount
 exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   cap budget degree hcomponent hbudget
theorem regularComponents_degree_budget
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (p:ℕ) [CharP Ω p] (hG:Irreducible G) (hproper:¬ G∣T)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p):
   ∀ i,(∑ C:RegularComponent Ω G T (regularitySurface φ F),
     actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i:=by
 intro i
 letI:∀ C:RegularComponent Ω G T (regularitySurface φ F),C.1.IsPrime:=
   fun C => regularComponent_isPrime Ω G T (regularitySurface φ F) C
 have hneq:(Equiv.swap (0:Fin 3) i) 1≠(Equiv.swap (0:Fin 3) i) 2:=
   (Equiv.swap (0:Fin 3) i).injective.ne (by decide)
 have hmixed:coordinateMixedDegree Ω G T i < p:=
   hcutDegree ((Equiv.swap (0:Fin 3) i) 1) ((Equiv.swap (0:Fin 3) i) 2) hneq
 exact sum_actualCoordinateDegree_at_le Ω
   (fun C:RegularComponent Ω G T (regularitySurface φ F) => C.1)
   Subtype.val_injective i p G T hG
   (regularComponent_G_mem Ω G T (regularitySurface φ F))
   (regularComponent_T_mem Ω G T (regularitySurface φ F))
   hproper hGdegree hmixed
theorem proper_cut_seed_bound
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,cap i*coordinateMixedDegree Ω G T i)+
     (e+1)*(a-w)*coordinateMixedDegree Ω G T 2:=
 proper_cut_seed_bound_of_projection_sum φ F G T hG hdiv hproper selected Γ
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree hcutDegree
   hdegree hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
   (coordinateMixedDegree Ω G T) hcap
   (regularComponents_degree_budget φ F G T p hG hproper hGdegree hcutDegree)
end
end ProximityPrize.SubmissionLower.RCN243
end PackedLegacy_F

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.AI. -/
section PackedLegacy_AI
namespace ProximityPrize.SubmissionLower.RCN301
open RCN174 RCN256
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def agreements:ℕ:=182807
def errors:ℕ:=n-agreements
def gap:ℕ:=agreements-w
structure Profile where
 multiplicity:ℕ
 seedCap:ℕ
 slopeCap:ℕ
 deriving DecidableEq
def profileA:Profile:=⟨25,5263,7⟩
def profileB:Profile:=⟨47,598,14⟩
def profileC:Profile:=⟨27,579299,6⟩
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
def yCap (P:Profile):ℕ:=(P.weightedCap-1)/w
def characteristicCap (P:Profile):ℕ:=
 (2*P.slopeCap-1)*P.weightedCap
def coefficients (P:Profile):ℕ:=
 coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P:Profile):ℕ:=
 localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P:Profile):ℕ:=n*P.localRank
def nullity (P:Profile):ℕ:=P.coefficients-P.totalRank
end Profile
theorem coefficientCount_eq_sum_range_of_weighted_cutoff
   (D w L s t:ℕ) (ht:t ≤ L+1) (hD:D ≤ w*t):
   coefficientCount D w L s=
     ∑ i∈Finset.range t,
       ∑ j∈Finset.range (s+1),
         (L+1-i)*(D-w*i-(w-1)*j):=by
 have hsplit:L+1=t+(L+1-t):=by omega
 unfold coefficientCount
 rw [hsplit,Finset.sum_range_add]
 have htail:
     (∑ x∈Finset.range (L+1-t),
       ∑ j∈Finset.range (s+1),
         (t+(L+1-t)-(t+x))*
           (D-w*(t+x)-(w-1)*j))=0:=by
   apply Finset.sum_eq_zero
   intro i hi
   apply Finset.sum_eq_zero
   intro j hj
   have hti:t ≤ t+i:=by omega
   have hzero:D-w*(t+i)=0:=
     Nat.sub_eq_zero_of_le (hD.trans (Nat.mul_le_mul_left w hti))
   simp [hzero]
 rw [htail,add_zero]
theorem base_values:
   errors=79337∧gap=51736:=by
 norm_num [errors,gap,n,agreements,w]
theorem profileA_coefficients_exact:
   profileA.coefficients=2811431653128:=by
 change coefficientCount (25*182807) 131071 5263 7=2811431653128
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (25*182807) 131071 5263 7 35 (by norm_num) (by norm_num)]
 decide
theorem profileA_localRank_exact:profileA.localRank=10724760:=by
 change localRankBound 25 5263 7=10724760
 decide
theorem profileA_values:
   profileA.weightedCap=4570175∧profileA.yCap=34∧
     profileA.localRank=10724760∧
     profileA.coefficients=2811431653128∧
     profileA.nullity=167688:=by
 refine ⟨by norm_num [Profile.weightedCap,profileA,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileA,agreements,w],
   profileA_localRank_exact,profileA_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileA_coefficients_exact,
   profileA_localRank_exact]
 norm_num [n]
theorem profileB_coefficients_exact:
   profileB.coefficients=1997482954410:=by
 change coefficientCount (47*182807) 131071 598 14=1997482954410
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (47*182807) 131071 598 14 66 (by norm_num) (by norm_num)]
 decide
theorem profileB_localRank_exact:profileB.localRank=7619680:=by
 change localRankBound 47 598 14=7619680
 decide
theorem profileB_values:
   profileB.weightedCap=8591929∧profileB.yCap=65∧
     profileB.localRank=7619680∧
     profileB.coefficients=1997482954410∧
     profileB.nullity=29560490:=by
 refine ⟨by norm_num [Profile.weightedCap,profileB,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileB,agreements,w],
   profileB_localRank_exact,profileB_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileB_coefficients_exact,
   profileB_localRank_exact]
 norm_num [n]
theorem profileC_coefficients_exact:
   profileC.coefficients=329531914715570:=by
 change coefficientCount (27*182807) 131071 579299 6=329531914715570
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (27*182807) 131071 579299 6 38 (by norm_num) (by norm_num)]
 decide
theorem profileC_localRank_exact:profileC.localRank=1257064494:=by
 change localRankBound 27 579299 6=1257064494
 decide
theorem profileC_values:
   profileC.weightedCap=4935789∧profileC.yCap=37∧
     profileC.localRank=1257064494∧
     profileC.coefficients=329531914715570∧
     profileC.nullity=434:=by
 refine ⟨by norm_num [Profile.weightedCap,profileC,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileC,agreements,w],
   profileC_localRank_exact,profileC_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileC_coefficients_exact,
   profileC_localRank_exact]
 norm_num [n]
theorem interpolation_gates:
     profileA.totalRank < profileA.coefficients∧
     profileB.totalRank < profileB.coefficients∧
     profileC.totalRank < profileC.coefficients:=by
 simp only [Profile.totalRank]
 rw [profileA_coefficients_exact,profileA_localRank_exact,
   profileB_coefficients_exact,profileB_localRank_exact,
   profileC_coefficients_exact,profileC_localRank_exact]
 norm_num [n]
theorem characteristic_gates:
   profileA.characteristicCap < prime∧
     (2*profileA.slopeCap-1)*profileA.seedCap < prime∧
     profileA.slopeCap < prime∧
   profileB.characteristicCap < prime∧
     (2*profileB.slopeCap-1)*profileB.seedCap < prime∧
     profileB.slopeCap < prime∧
   profileC.characteristicCap < prime∧
     (2*profileC.slopeCap-1)*profileC.seedCap < prime∧
     profileC.slopeCap < prime:=by
 norm_num [Profile.characteristicCap,Profile.weightedCap,profileA,profileB,
   profileC,agreements,prime]
theorem meet_caps:
   (min profileA.multiplicity profileB.multiplicity,
       min profileA.seedCap profileB.seedCap,
       min profileA.slopeCap profileB.slopeCap)=(25,598,7)∧
     (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
       min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
       min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap)=
         (25,598,6):=by
 norm_num [profileA,profileB,profileC]
end ProximityPrize.SubmissionLower.RCN301
end PackedLegacy_AI

/-! Packed from ProximityPrize.SubmissionLower.H. -/
section PackedLegacy_H
namespace ProximityPrize.SubmissionLower.RCN213
open scoped BigOperators
theorem stratified_incidence_linear
   (q n a w k degreeCost unitCost U V:ℕ)
   (hk:k ≤ w) (hwa:w < a)
   (hraw:q*(a-k) ≤
     (n-k)*((w-k)*degreeCost+unitCost))
   (hdegree:(n-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:(n-k)*(a-w) ≤ V*(a-k)):
   q*(a-w) ≤ U*degreeCost+V*unitCost:=by
 have hak:0 < a-k:=by omega
 refine Nat.le_of_mul_le_mul_right ?_ hak
 calc
   q*(a-w)*(a-k)=(q*(a-k))*(a-w):=by ring
   _ ≤ ((n-k)*((w-k)*degreeCost+unitCost))*(a-w):=
     Nat.mul_le_mul_right (a-w) hraw
   _=((n-k)*(a-w)*(w-k))*degreeCost+
       ((n-k)*(a-w))*unitCost:=by ring
   _ ≤ (U*(a-k))*degreeCost+
       (V*(a-k))*unitCost:=
     Nat.add_le_add (Nat.mul_le_mul_right degreeCost hdegree)
       (Nat.mul_le_mul_right unitCost hunit)
   _=(U*degreeCost+V*unitCost)*(a-k):=by ring
def n:ℕ:=262144
def errors:ℕ:=78958
def agreements:ℕ:=n-errors
def w:ℕ:=131071
def gap:ℕ:=agreements-w
def degreeIncidence:ℕ:=9775005205
def unitIncidence:ℕ:=n-w
theorem parameter_values:
   agreements=183186∧gap=52115∧unitIncidence=131073:=by
 norm_num [agreements,gap,unitIncidence,n,errors,w]
def mixedQuadratic:ℕ:=3425875
def mixedLinear:ℕ:=15465
def mixedUnit:ℕ:=8
def zLinear:ℕ:=1205
def zUnit:ℕ:=8
def stratifiedPrimary:ℕ:=
 mixedQuadratic*degreeIncidence^2+
   2*mixedLinear*degreeIncidence*unitIncidence+
   mixedUnit*unitIncidence^2
def stratifiedZTail:ℕ:=
 (errors+1)*gap*
   (zLinear*degreeIncidence+zUnit*unitIncidence)
def retainedSingularContribution:ℕ:=6714916701272010710818955
def stratifiedTotalNumerator:ℕ:=
 stratifiedPrimary+stratifiedZTail+retainedSingularContribution
def gapSquared:ℕ:=gap^2
def ledgerCeiling:ℕ:=
 (stratifiedTotalNumerator+gapSquared-1)/gapSquared
def alignmentBudget:ℕ:=137490364055697543
end ProximityPrize.SubmissionLower.RCN213
end PackedLegacy_H

/-! Packed from ProximityPrize.SubmissionLower.R. -/
section PackedLegacy_R
namespace ProximityPrize.SubmissionLower.RCN223
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def alignmentBudget:ℕ:=137490364055697543
def errors:ℕ:=78958
def agreements:ℕ:=n-errors
def multiplicity:ℕ:=31
def seedTotalCap:ℕ:=495
def slopeCap:ℕ:=8
def weightedCap:ℕ:=multiplicity*agreements
def yCap:ℕ:=(weightedCap-1)/w
def gap:ℕ:=agreements-w
def algebraicCap:ℕ:=(2*slopeCap-1)*seedTotalCap
def implicitWeightedCap:ℕ:=(2*slopeCap-1)*weightedCap
def implicitYCap:ℕ:=(implicitWeightedCap-1)/w
def coefficientCount:ℕ:=
 ∑ i∈range (seedTotalCap+1),
   ∑ j∈range (slopeCap+1),
     (seedTotalCap+1-i)*
       (weightedCap-w*i-(w-1)*j)
def contactExponent (r:ℕ):ℕ:=min (r+1) (multiplicity-r)
def localContactRank:ℕ:=
 ∑ r∈range multiplicity,
   (((slopeCap+1)*
       (∑ f∈range (min r seedTotalCap+1),
         (seedTotalCap+1-f)))-
     ((slopeCap+1-contactExponent r)*
       (∑ f∈range (min r seedTotalCap+1-contactExponent r),
         (seedTotalCap+1-contactExponent r-f))))
def totalContactRank:ℕ:=n*localContactRank
def rankMargin:ℕ:=coefficientCount-totalContactRank
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq
def mixed (a b c:DegreeVector):ℕ:=
 a.y*b.r*c.z+a.y*b.z*c.r+
 a.r*b.y*c.z+a.r*b.z*c.y+
 a.z*b.y*c.r+a.z*b.r*c.y
def unitZ:DegreeVector:=⟨0,0,1⟩
def liftedSurface:DegreeVector:=⟨implicitYCap,1,algebraicCap⟩
def implicitCut:DegreeVector:=⟨implicitYCap,0,algebraicCap⟩
def liftedLast:DegreeVector:=
 ⟨1+2*implicitWeightedCap*implicitYCap,
   implicitWeightedCap,
   2*implicitWeightedCap*algebraicCap⟩
def liftedAgreement:DegreeVector:=
 ⟨1+2*w*implicitYCap,
   w,
   2*w*algebraicCap+1⟩
def retainedSingularNumerator:ℕ:=
 gap*(algebraicCap+2*algebraicCap^2+
     mixed liftedSurface implicitCut liftedLast+
     (errors+1)*mixed liftedSurface implicitCut unitZ)+
   (n-w)*mixed liftedSurface implicitCut liftedAgreement
def retainedSingularContribution:ℕ:=gap*retainedSingularNumerator
theorem parameter_values:
   agreements=183186∧weightedCap=5678766∧yCap=43∧
   gap=52115∧algebraicCap=7425∧
   implicitWeightedCap=85181490∧implicitYCap=649:=by
 norm_num [agreements,n,errors,weightedCap,multiplicity,yCap,w,
   gap,algebraicCap,slopeCap,seedTotalCap,implicitWeightedCap,
   implicitYCap]
theorem coefficient_count_exact:coefficientCount=453847251690:=by
  change (∑ i ∈ Finset.range (44 + 452),
    ∑ j ∈ Finset.range 9,
      (496 - i) * (5678766 - 131071 * i - 131070 * j)) = 453847251690
  rw [Finset.sum_range_add _ 44 452]
  have hzero : (∑ i ∈ Finset.range 452,
      ∑ j ∈ Finset.range 9,
        (496 - (44 + i)) *
          (5678766 - 131071 * (44 + i) - 131070 * j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hz : 5678766 - 131071 * (44 + i) = 0 :=
      Nat.sub_eq_zero_of_le (by omega)
    simp only [hz, Nat.zero_sub, Nat.mul_zero]
  rw [hzero, Nat.add_zero]
  simp_rw [← KernelEval.sumRange_eq]
  decide
theorem local_contact_rank_exact:localContactRank=1731288:=by
 unfold localContactRank
 simp_rw [← KernelEval.sumRange_eq]
 decide
theorem total_contact_rank_exact:totalContactRank=453846761472:=by
 rw [show totalContactRank=n*localContactRank by rfl,
   local_contact_rank_exact]
 norm_num [n]
theorem interpolation_gate:totalContactRank < coefficientCount:=by
 rw [coefficient_count_exact,total_contact_rank_exact]
 norm_num
theorem characteristic_gates:
   weightedCap < prime∧implicitWeightedCap < prime∧
     algebraicCap < prime∧slopeCap < prime:=by
 norm_num [weightedCap,multiplicity,agreements,n,errors,
   implicitWeightedCap,algebraicCap,slopeCap,seedTotalCap,prime]
end ProximityPrize.SubmissionLower.RCN223
end PackedLegacy_R

/-! Packed from ProximityPrize.SubmissionLower.CB. -/
section PackedLegacy_CB
namespace ProximityPrize.SubmissionLower.RCN294
open scoped BigOperators
open RCN223
def sumVector {I:Type} [Fintype I] (v:I-> DegreeVector):DegreeVector:=
 ⟨∑ i,(v i).y,∑ i,(v i).r,∑ i,(v i).z⟩
def vectorLE (a b:DegreeVector):Prop:=
 a.y ≤ b.y∧a.r ≤ b.r∧a.z ≤ b.z
def dot (a b:DegreeVector):Nat:=
 a.y*b.y+a.r*b.r+a.z*b.z
theorem dot_mono_left {a b:DegreeVector} (c:DegreeVector)
   (h:vectorLE a b):dot a c ≤ dot b c:=
 Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1)
     (Nat.mul_le_mul_right c.r h.2.1))
   (Nat.mul_le_mul_right c.z h.2.2)
theorem dot_sum_left {I:Type} [Fintype I]
   (v:I-> DegreeVector) (a:DegreeVector):
   dot (sumVector v) a=∑ i,dot (v i) a:=by
 simp only [dot,sumVector,Finset.sum_add_distrib,Finset.sum_mul]
def implicitAggregateCost:DegreeVector:=
 ⟨algebraicCap,2*implicitYCap*algebraicCap,implicitYCap⟩
def implicitCoefficients:DegreeVector:=
 ⟨(n-w)*liftedAgreement.y,
   (n-w)*liftedAgreement.r,
   (n-w)*liftedAgreement.z+(errors+1)*gap⟩
def implicitCoreNumerator:Nat:=
 (n-w)*mixed liftedSurface implicitCut liftedAgreement+
   (errors+1)*gap*mixed liftedSurface implicitCut unitZ
theorem implicit_bound_eq_dot (v:DegreeVector):
   (n-w)*dot liftedAgreement v+(errors+1)*gap*v.z=
     dot v implicitCoefficients:=by
 simp only [implicitCoefficients,dot]
 ring
theorem implicit_aggregate_eq_core:
   dot implicitAggregateCost implicitCoefficients=implicitCoreNumerator:=by
 simp only [implicitAggregateCost,implicitCoefficients,
   implicitCoreNumerator,dot,mixed,liftedSurface,implicitCut,unitZ]
 ring
theorem sum_implicit_counts_bound {I:Type} [Fintype I]
   (count:I-> Nat) (cost:I-> DegreeVector)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:forall i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z):
   (∑ i,count i)*gap ≤ implicitCoreNumerator:=by
 calc
   _=∑ i,count i*gap:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (cost i) implicitCoefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←implicit_bound_eq_dot]
     exact hcount i
   _=dot (sumVector cost) implicitCoefficients:=
     (dot_sum_left cost implicitCoefficients).symm
   _ ≤ dot implicitAggregateCost implicitCoefficients:=
     dot_mono_left implicitCoefficients ⟨hy,hr,hz⟩
   _=implicitCoreNumerator:=implicit_aggregate_eq_core
theorem retained_singular_padding:
   retainedSingularNumerator=
     implicitCoreNumerator+
       gap*(algebraicCap+2*algebraicCap^2+
         mixed liftedSurface implicitCut liftedLast):=by
 simp only [retainedSingularNumerator,implicitCoreNumerator]
 ring
theorem implicit_with_exceptions_bound {I:Type} [Fintype I]
   (count:I-> Nat) (cost:I-> DegreeVector) (exceptions:Nat)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:forall i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2):
   ((∑ i,count i)+exceptions)*gap ≤ retainedSingularNumerator:=by
 have hmain:=sum_implicit_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*gap+exceptions*gap:=Nat.add_mul _ _ _
   _ ≤ implicitCoreNumerator+2*algebraicCap^2*gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
   _ ≤ retainedSingularNumerator:=by
     rw [retained_singular_padding]
     apply Nat.add_le_add_left
     calc
       2*algebraicCap^2*gap=gap*(2*algebraicCap^2):=by ring
       _ ≤ gap*(algebraicCap+2*algebraicCap^2+
           mixed liftedSurface implicitCut liftedLast):=
         Nat.mul_le_mul_left gap (by omega)
end ProximityPrize.SubmissionLower.RCN294
end PackedLegacy_CB

/-! Packed from ProximityPrize.SubmissionLower.AK. -/
section PackedLegacy_AK
namespace ProximityPrize.SubmissionLower.RCN318
open scoped BigOperators
open RCN223 RCN294
structure TightParameters where
 n:ℕ
 w:ℕ
 a:ℕ
 D:ℕ
 L:ℕ
 s:ℕ
 deriving DecidableEq
namespace TightParameters
def errors (P:TightParameters):ℕ:=P.n-P.a
def gap (P:TightParameters):ℕ:=P.a-P.w
def kappa (P:TightParameters):ℕ:=2*P.s-1
def implicitYCap (P:TightParameters):ℕ:=(P.kappa*P.D-1)/P.w
def algebraicCap (P:TightParameters):ℕ:=P.kappa*P.L
def agreement (P:TightParameters):DegreeVector:=
 ⟨1+2*P.w*P.implicitYCap,
   P.w,
   2*P.w*P.algebraicCap+1⟩
def aggregateCost (P:TightParameters):DegreeVector:=
 ⟨P.algebraicCap,
   2*P.implicitYCap*P.algebraicCap,
   P.implicitYCap⟩
def coefficients (P:TightParameters):DegreeVector:=
 ⟨(P.n-P.w)*P.agreement.y,
   (P.n-P.w)*P.agreement.r,
   (P.n-P.w)*P.agreement.z+(P.errors+1)*P.gap⟩
def coreNumerator (P:TightParameters):ℕ:=
 (P.n-P.w)*dot P.agreement P.aggregateCost+
   (P.errors+1)*P.gap*P.implicitYCap
def tightNumerator (P:TightParameters):ℕ:=
 P.coreNumerator+2*P.algebraicCap^2*P.gap
def countCap (P:TightParameters):ℕ:=P.tightNumerator/P.gap
theorem bound_eq_dot (P:TightParameters) (v:DegreeVector):
   (P.n-P.w)*dot P.agreement v+
       (P.errors+1)*P.gap*v.z=
     dot v P.coefficients:=by
 simp only [coefficients,errors,gap,dot]
 ring
theorem aggregate_eq_core (P:TightParameters):
   dot P.aggregateCost P.coefficients=P.coreNumerator:=by
 simp only [aggregateCost,coefficients,coreNumerator,dot]
 ring
theorem sum_counts_bound (P:TightParameters) {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector)
   (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
   (hcount:∀ i,count i*P.gap ≤
     (P.n-P.w)*dot P.agreement (cost i)+
       (P.errors+1)*P.gap*(cost i).z):
   (∑ i,count i)*P.gap ≤ P.coreNumerator:=by
 calc
   _=∑ i,count i*P.gap:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (cost i) P.coefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←P.bound_eq_dot]
     exact hcount i
   _=dot (sumVector cost) P.coefficients:=
     (dot_sum_left cost P.coefficients).symm
   _ ≤ dot P.aggregateCost P.coefficients:=
     dot_mono_left P.coefficients ⟨hy,hr,hz⟩
   _=P.coreNumerator:=P.aggregate_eq_core
theorem with_exceptions_bound (P:TightParameters) {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
   (hy:(∑ i,(cost i).y) ≤ P.algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*P.implicitYCap*P.algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ P.implicitYCap)
   (hcount:∀ i,count i*P.gap ≤
     (P.n-P.w)*dot P.agreement (cost i)+
       (P.errors+1)*P.gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*P.algebraicCap^2):
   ((∑ i,count i)+exceptions)*P.gap ≤ P.tightNumerator:=by
 have hmain:=P.sum_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*P.gap+exceptions*P.gap:=Nat.add_mul _ _ _
   _ ≤ P.coreNumerator+2*P.algebraicCap^2*P.gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right P.gap hexceptions)
   _=P.tightNumerator:=rfl
theorem count_le_countCap (P:TightParameters) (count:ℕ)
   (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.tightNumerator):
   count ≤ P.countCap:=by
 exact (Nat.le_div_iff_mul_le hgap).mpr hcount
end TightParameters
def maximalResidualQA:TightParameters:=
 ⟨262144,131071,182807,4570175,5263,7⟩
def maximalResidualH:TightParameters:=
 ⟨262144,131071,182807,4570175,598,7⟩
end ProximityPrize.SubmissionLower.RCN318
end PackedLegacy_AK

/-! Packed from ProximityPrize.SubmissionLower.N5. -/
section PackedLegacy_N5
namespace ProximityPrize.SubmissionLower.RCN260
open scoped BigOperators
open RCN318 RCN223 RCN294
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
structure UnequalParameters where
 n:ℕ
 w:ℕ
 a:ℕ
 leftY:ℕ
 leftR:ℕ
 leftZ:ℕ
 rightY:ℕ
 rightR:ℕ
 rightZ:ℕ
 deriving DecidableEq
namespace UnequalParameters
def errors (P:UnequalParameters):ℕ:=P.n-P.a
def gap (P:UnequalParameters):ℕ:=P.a-P.w
def leftAgreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.leftY,
   P.w*(2*P.leftR-1),
   2*P.w*P.leftZ+1⟩
def rightAgreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨1+2*P.w*P.rightY,
   P.w*(2*P.rightR-1),
   2*P.w*P.rightZ+1⟩
def agreement (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨max P.leftAgreement.y P.rightAgreement.y,
   max P.leftAgreement.r P.rightAgreement.r,
   max P.leftAgreement.z P.rightAgreement.z⟩
def mixedCost (P:UnequalParameters):RCN223.DegreeVector:=
 ⟨P.leftR*P.rightZ+P.leftZ*P.rightR,
   P.leftY*P.rightZ+P.leftZ*P.rightY,
   P.leftY*P.rightR+P.leftR*P.rightY⟩
def regularNumerator (P:UnequalParameters):ℕ:=
 (P.n-P.w)*dot P.agreement P.mixedCost+
   (P.errors+1)*P.gap*P.mixedCost.z
def regularCountCap (P:UnequalParameters):ℕ:=P.regularNumerator/P.gap
theorem regular_count_le (P:UnequalParameters) (count:ℕ)
   (hgap:0 < P.gap) (hcount:count*P.gap ≤ P.regularNumerator):
   count ≤ P.regularCountCap:=
 (Nat.le_div_iff_mul_le hgap).mpr hcount
end UnequalParameters
def residualStageOne:UnequalParameters:=
 ⟨262144,131071,182807,34,7,5263,65,14,598⟩
def residualStageTwo:UnequalParameters:=
 ⟨262144,131071,182807,34,7,598,37,6,579299⟩
end ProximityPrize.SubmissionLower.RCN260
end PackedLegacy_N5

/-! Packed from ProximityPrize.SubmissionLower.C. -/
section PackedLegacy_C
namespace ProximityPrize.SubmissionLower.RCN081
open RCN174
noncomputable section
def weightEmbed (weights:Fin 4 → ℕ):(Fin 4 →₀ ℕ) →+(Fin 5 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+
   Finsupp.single 4 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ) (i:Fin 4):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   weightEmbed weights d (4:Fin 5)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 5 →₀ ℕ => a i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
variable {K:Type*} [Field K]
def weightedLift (K:Type*) [Field K] (weights:Fin 4 → ℕ):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 5) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem weightedLift_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightedLift K weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)
theorem weightedLift_ne_zero (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K)
   (hP:P≠0):weightedLift K weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).support=P.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).degreeOf (4:Fin 5)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift K weights P).degreeOf (4:Fin 5)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
 funext d
 exact weightEmbed_last weights d
theorem weightedTotalDegree_mul (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift K weights (P*Q)).degreeOf (4:Fin 5):=
     (degree_weightedLift weights (P*Q)).symm
   _=(weightedLift K weights P*weightedLift K weights Q).degreeOf (4:Fin 5):=by
     rw [map_mul]
   _=(weightedLift K weights P).degreeOf (4:Fin 5)+
       (weightedLift K weights Q).degreeOf (4:Fin 5):=
     MvPolynomial.degreeOf_mul_eq (weightedLift_ne_zero weights P hP)
       (weightedLift_ne_zero weights Q hQ)
   _=MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
     rw [degree_weightedLift,degree_weightedLift]
theorem weightedTotalDegree_le_of_dvd (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_le_iff (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (cap:ℕ):
   MvPolynomial.weightedTotalDegree weights P ≤ cap ↔
     ∀ d∈P.support,Finsupp.weight weights d ≤ cap:=by
 simp only [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
theorem weight_fin4 (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2+d 3*weights 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 calc
   Finsupp.weight weights d=Finsupp.weight weights
       (Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
         Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)):=congrArg _ hd
   _=_:=by simp only [map_add,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id]
def seedWeights:Fin 4 → ℕ:=![0,1,0,1]
def slopeWeights:Fin 4 → ℕ:=![0,0,1,0]
def contactWeights (w:ℕ):Fin 4 → ℕ:=![1,w,w-1,0]
theorem seed_weight (d:Fin 4 →₀ ℕ):Finsupp.weight seedWeights d=d 1+d 3:=by
 rw [weight_fin4]
 simp [seedWeights]
theorem slope_weight (d:Fin 4 →₀ ℕ):Finsupp.weight slopeWeights d=d 2:=by
 rw [weight_fin4]
 simp [slopeWeights]
theorem contact_weight (w:ℕ) (d:Fin 4 →₀ ℕ):
   Finsupp.weight (contactWeights w) d=d 0+w*d 1+(w-1)*d 2:=by
 rw [weight_fin4]
 simp [contactWeights,Nat.mul_comm]
theorem mem_globalCoefficientBox_iff (P:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hD:0 < D):
   P∈globalCoefficientBox K D w L s ↔
     MvPolynomial.weightedTotalDegree seedWeights P ≤ L∧
     MvPolynomial.weightedTotalDegree slopeWeights P ≤ s∧
     MvPolynomial.weightedTotalDegree (contactWeights w) P ≤ D-1:=by
 constructor
 · intro h
   refine ⟨?_,?_,?_⟩
   · apply (weightedTotalDegree_le_iff seedWeights P L).mpr
     intro d hd
     rw [seed_weight]
     exact (h hd).1
   · apply (weightedTotalDegree_le_iff slopeWeights P s).mpr
     intro d hd
     rw [slope_weight]
     exact (h hd).2.1
   · apply (weightedTotalDegree_le_iff (contactWeights w) P (D-1)).mpr
     intro d hd
     rw [contact_weight]
     have hh:=(h hd).2.2
     omega
 · rintro ⟨hseed,hslope,hcontact⟩ d hd
   have hs:=(MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hseed
   have hr:=(MvPolynomial.le_weightedTotalDegree slopeWeights hd).trans hslope
   have hc:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hcontact
   rw [seed_weight] at hs
   rw [slope_weight] at hr
   rw [contact_weight] at hc
   exact ⟨hs,hr,by omega⟩
theorem mem_globalCoefficientBox_of_dvd
   (F Q:MvPolynomial (Fin 4) K) (D w L s:ℕ)
   (hQ:Q≠0) (hdiv:F∣Q)
   (hbox:Q∈globalCoefficientBox K D w L s):
   F∈globalCoefficientBox K D w L s:=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have hh:=(hbox hd).2.2
   omega
 have hcaps:=(mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
 apply (mem_globalCoefficientBox_iff F D w L s hD).mpr
 exact ⟨(weightedTotalDegree_le_of_dvd seedWeights F Q hdiv hQ).trans hcaps.1,
   (weightedTotalDegree_le_of_dvd slopeWeights F Q hdiv hQ).trans hcaps.2.1,
   (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hcaps.2.2⟩
theorem degreeOf_le_of_dvd (i:Fin 4) (F Q:MvPolynomial (Fin 4) K)
   (hdiv:F∣Q) (hQ:Q≠0):F.degreeOf i ≤ Q.degreeOf i:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hF,hG⟩
 rw [MvPolynomial.degreeOf_mul_eq hF hG]
 exact Nat.le_add_right _ _
theorem sum_degreeOf_le_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q) (i:Fin 4):
   (∑ j∈I,(f j).degreeOf i) ≤ Q.degreeOf i:=by
 classical
 have hprod:(∏ j∈I,f j)≠0:=by
   intro hz
   rcases hdiv with ⟨G,hG⟩
   apply hQ
   rw [hG,hz,zero_mul]
 have hf:∀ j∈I,f j≠0:=Finset.prod_ne_zero_iff.mp hprod
 calc
   (∑ j∈I,(f j).degreeOf i)=(∏ j∈I,f j).degreeOf i:=
     (MvPolynomial.degreeOf_prod_eq (n:=i) I f hf).symm
   _ ≤ Q.degreeOf i:=degreeOf_le_of_dvd i _ Q hdiv hQ
theorem separated_degree_budgets_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ j∈I,f j)∣Q):
   (∑ j∈I,(f j).degreeOf (1:Fin 4)) ≤ Q.degreeOf (1:Fin 4)∧
   (∑ j∈I,(f j).degreeOf (2:Fin 4)) ≤ Q.degreeOf (2:Fin 4)∧
   (∑ j∈I,(f j).degreeOf (3:Fin 4)) ≤ Q.degreeOf (3:Fin 4):=
 ⟨sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 1,
   sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 2,
   sum_degreeOf_le_of_prod_dvd I f Q hQ hdiv 3⟩
theorem degreeOf_Y_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (1:Fin 4) ≤ (D-1)/w:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 apply (Nat.le_div_iff_mul_le hw).mpr
 have hc:=(hbox hd).2.2
 have hm:d 1*w=w*d 1:=Nat.mul_comm _ _
 omega
theorem degreeOf_R_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (2:Fin 4) ≤ s:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hbox hd).2.1
theorem degreeOf_Z_le_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (3:Fin 4) ≤ L:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=(hbox hd).1
 omega
theorem degree_bounds_of_mem_box (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s):
   Q.degreeOf (1:Fin 4) ≤ (D-1)/w∧
   Q.degreeOf (2:Fin 4) ≤ s∧Q.degreeOf (3:Fin 4) ≤ L:=
 ⟨degreeOf_Y_le_of_mem_box Q D w L s hw hbox,
   degreeOf_R_le_of_mem_box Q D w L s hbox,
   degreeOf_Z_le_of_mem_box Q D w L s hbox⟩
theorem separated_factor_caps_of_prod_dvd {ι:Type*}
   (I:Finset ι) (f:ι → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (D w L s:ℕ) (hw:0 < w) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K D w L s) (hdiv:(∏ j∈I,f j)∣Q):
   (∑ j∈I,(f j).degreeOf (1:Fin 4)) ≤ (D-1)/w∧
   (∑ j∈I,(f j).degreeOf (2:Fin 4)) ≤ s∧
   (∑ j∈I,(f j).degreeOf (3:Fin 4)) ≤ L:=by
 have hsum:=separated_degree_budgets_of_prod_dvd I f Q hQ hdiv
 have hcaps:=degree_bounds_of_mem_box Q D w L s hw hbox
 exact ⟨hsum.1.trans hcaps.1,hsum.2.1.trans hcaps.2.1,hsum.2.2.trans hcaps.2.2⟩
end
end ProximityPrize.SubmissionLower.RCN081
end PackedLegacy_C

/-! Packed from ProximityPrize.SubmissionLower.J1. -/
section PackedLegacy_J1
namespace ProximityPrize.SubmissionLower.RCN082
open UniqueFactorizationMonoid RCN136 RCN174
noncomputable section
variable {K L:Type*} [Field K] [Field L]
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K):=
 UniqueFactorizationMonoid.strongNormalizationMonoid
def activeFactors (Q:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (normalizedFactors Q).toFinset.filter
   (fun F => 0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
theorem activeFactors_spec (Q F:MvPolynomial (Fin 4) K)
   (hF:F∈activeFactors Q):
   Irreducible F∧F∣Q∧0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 classical
 obtain ⟨hm,hp⟩:=Finset.mem_filter.mp hF
 have hmem:F∈normalizedFactors Q:=Multiset.mem_toFinset.mp hm
 exact ⟨irreducible_of_normalized_factor F hmem,
   dvd_of_mem_normalizedFactors hmem,hp⟩
theorem exists_normalized_factor_of_map_zero
   {A:Type*} [CommRing A] [IsDomain A]
   (ψ:MvPolynomial (Fin 4) K →+*A)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hzero:ψ Q=0):
   ∃ F∈normalizedFactors Q,ψ F=0:=by
 have hassoc:=Associated.map ψ (prod_normalizedFactors hQ)
 rw [hzero] at hassoc
 have hp:ψ (normalizedFactors Q).prod=0:=
   (associated_zero_iff_eq_zero _).mp hassoc
 rw [map_multiset_prod] at hp
 exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
theorem eq_C_of_all_degreeOf_zero (P:MvPolynomial (Fin 3) L)
   (h:∀ i,P.degreeOf i=0):P=MvPolynomial.C (P.coeff 0):=by
 classical
 apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
 apply Nat.eq_zero_of_le_zero
 rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
 intro d hd
 have hd0:d=0:=by
   ext i
   have hi:=MvPolynomial.monomial_le_degreeOf i hd
   rw [h i] at hi
   exact Nat.eq_zero_of_le_zero hi
 simp [hd0]
theorem positive_seed_degree_of_surface_zero
   (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (v:Fin 3 → L)
   (hzero:MvPolynomial.eval v (surfaceMap φ F)=0):
   0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3:=by
 by_contra hn
 have hy:F.degreeOf 1 ≤ 0:=by omega
 have hr:F.degreeOf 2 ≤ 0:=by omega
 have hz:F.degreeOf 3 ≤ 0:=by omega
 have hc:=surfaceMap_separated_caps φ F 0 0 0 hy hr hz
 have hconst:surfaceMap φ F=MvPolynomial.C ((surfaceMap φ F).coeff 0):=by
   apply eq_C_of_all_degreeOf_zero
   intro i
   fin_cases i
   · exact Nat.eq_zero_of_le_zero hc.1
   · exact Nat.eq_zero_of_le_zero hc.2.1
   · exact Nat.eq_zero_of_le_zero hc.2.2
 have hvalue:=hzero
 rw [hconst,MvPolynomial.eval_C] at hvalue
 apply surfaceMap_ne_zero φ hφ F hF
 rw [hconst,hvalue,map_zero]
end
end ProximityPrize.SubmissionLower.RCN082
end PackedLegacy_J1
end Compact_PackedLegacyCore1
