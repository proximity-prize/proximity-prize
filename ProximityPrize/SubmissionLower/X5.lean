import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.H1
namespace ProximityPrize.SubmissionLower.RCN013
open RCN002 RCN371
open RCN011 RCN009
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
