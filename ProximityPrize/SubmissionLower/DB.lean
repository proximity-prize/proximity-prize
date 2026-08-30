import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.X8
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate Matrix
open scoped BigOperators
variable {F:Type} [Field F]
private theorem natDegree_det_le_of_perm_products_le
   {ι:Type} [Fintype ι] [DecidableEq ι]
   (M:Matrix ι ι F[X]) {N:ℕ}
   (h:∀ σ:Equiv.Perm ι,(∏ i:ι,M (σ i) i).natDegree ≤ N):
   M.det.natDegree ≤ N:=by
 classical
 rw [Matrix.det_apply']
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro σ _
 exact (Polynomial.natDegree_C_mul_le
   ((Equiv.Perm.sign σ:ℤ):F) (∏ i:ι,M (σ i) i)).trans (h σ)
theorem bivariate_resultant_natDegree_le_of_coefficient_heights
   (B H:F[X][Y]) (n m:ℕ)
   (heightB heightH:ℕ → ℕ) (C:ℕ)
   (hB:∀ i,(B.coeff i).natDegree ≤ heightB i)
   (hH:∀ i,(H.coeff i).natDegree ≤ heightH i)
   (hassignment:∀ σ:Equiv.Perm (Fin (n+m)),
     (∀ j:Fin n,
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m)) →
     (∀ j:Fin m,
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n)) →
     (∑ j:Fin n,
         heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)))+
       (∑ j:Fin m,
         heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))) ≤ C):
   (Polynomial.resultant B H n m).natDegree ≤ C:=by
 classical
 let M:Matrix (Fin (n+m)) (Fin (n+m)) F[X]:=
   Polynomial.sylvester B H n m
 rw [Polynomial.resultant]
 change M.det.natDegree ≤ C
 apply natDegree_det_le_of_perm_products_le (M:=M)
 intro σ
 by_cases hzero:∃ i:Fin (n+m),M (σ i) i=0
 · rcases hzero with ⟨i,hi⟩
   have hprod:(∏ i:Fin (n+m),M (σ i) i)=0:=
     Finset.prod_eq_zero (Finset.mem_univ i) hi
   simp [hprod]
 · have hne (i:Fin (n+m)):M (σ i) i≠0:=by
     intro hi
     exact hzero ⟨i,hi⟩
   have hleft_Icc (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+m)
         then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.castAdd m j) (by simp [hentry,hc])
   have hright_Icc (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+n)
         then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.natAdd n j) (by simp [hentry,hc])
   have hleft (j:Fin n):
       (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree ≤
         heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
           if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+m)
           then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hleft_Icc j)]
     rw [hentry]
     exact hH _
   have hright (j:Fin m):
       (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree ≤
         heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
           if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+n)
           then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hright_Icc j)]
     rw [hentry]
     exact hB _
   have hsum_deg_split:
       (∑ i:Fin (n+m),(M (σ i) i).natDegree)=
         (∑ j:Fin n,
           (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree)+
         (∑ j:Fin m,
           (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree):=by
     simpa using (Fin.sum_univ_add
       (fun i:Fin (n+m) => (M (σ i) i).natDegree))
   calc
     (∏ i:Fin (n+m),M (σ i) i).natDegree ≤
         ∑ i:Fin (n+m),(M (σ i) i).natDegree:=by
       simpa using Polynomial.natDegree_prod_le Finset.univ
         (fun i:Fin (n+m) => M (σ i) i)
     _=(∑ j:Fin n,
           (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree)+
         (∑ j:Fin m,
           (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree):=
       hsum_deg_split
     _ ≤ (∑ j:Fin n,
           heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)))+
         (∑ j:Fin m,
           heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))):=
       Nat.add_le_add
         (Finset.sum_le_sum (fun j _ => hleft j))
         (Finset.sum_le_sum (fun j _ => hright j))
     _ ≤ C:=hassignment σ hleft_Icc hright_Icc
theorem bivariate_resultant_natDegree_le_of_sylvester_dual
   (B H:F[X][Y]) (n m:ℕ)
   (heightB heightH:ℕ → ℕ) (C:ℕ)
   (hB:∀ i,(B.coeff i).natDegree ≤ heightB i)
   (hH:∀ i,(H.coeff i).natDegree ≤ heightH i)
   (rowPotential:Fin (n+m) → ℤ)
   (leftPotential:Fin n → ℤ) (rightPotential:Fin m → ℤ)
   (hleft:∀ (row:Fin (n+m)) (j:Fin n),
     (row:ℕ)∈Set.Icc (j:ℕ) ((j:ℕ)+m) →
     (heightH ((row:ℕ)-(j:ℕ)):ℤ) ≤
       rowPotential row+leftPotential j)
   (hright:∀ (row:Fin (n+m)) (j:Fin m),
     (row:ℕ)∈Set.Icc (j:ℕ) ((j:ℕ)+n) →
     (heightB ((row:ℕ)-(j:ℕ)):ℤ) ≤
       rowPotential row+rightPotential j)
   (hbudget:(∑ row,rowPotential row)+
     (∑ j,leftPotential j)+(∑ j,rightPotential j) ≤ (C:ℤ)):
   (Polynomial.resultant B H n m).natDegree ≤ C:=by
 apply bivariate_resultant_natDegree_le_of_coefficient_heights
   B H n m heightB heightH C hB hH
 intro σ hleft_Icc hright_Icc
 have hleft_sum:
     (∑ j:Fin n,
         (heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ)) ≤
       (∑ j:Fin n,
         (rowPotential (σ (Fin.castAdd m j))+leftPotential j)):=by
   exact Finset.sum_le_sum (fun j _ => hleft _ j (hleft_Icc j))
 have hright_sum:
     (∑ j:Fin m,
         (heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ)) ≤
       (∑ j:Fin m,
         (rowPotential (σ (Fin.natAdd n j))+rightPotential j)):=by
   exact Finset.sum_le_sum (fun j _ => hright _ j (hright_Icc j))
 have hperm_sum:
     (∑ row:Fin (n+m),rowPotential (σ row))=
       ∑ row:Fin (n+m),rowPotential row:=by
   simpa using (Equiv.sum_comp σ rowPotential)
 have hrows_split:
     (∑ row:Fin (n+m),rowPotential (σ row))=
       (∑ j:Fin n,rowPotential (σ (Fin.castAdd m j)))+
         (∑ j:Fin m,rowPotential (σ (Fin.natAdd n j))):=by
   simpa using Fin.sum_univ_add
     (fun row:Fin (n+m) => rowPotential (σ row))
 have hrow_sum:
     (∑ j:Fin n,rowPotential (σ (Fin.castAdd m j)))+
         (∑ j:Fin m,rowPotential (σ (Fin.natAdd n j)))=
       ∑ row:Fin (n+m),rowPotential row:=by
   rw [←hrows_split,hperm_sum]
 have hcast:
     (((∑ j:Fin n,
         heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)))+
       (∑ j:Fin m,
         heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))):ℕ):ℤ) ≤
       (C:ℤ):=by
   calc
     _=(∑ j:Fin n,
           (heightH (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ))+
         (∑ j:Fin m,
           (heightB (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):ℤ)):=by
       simp
     _ ≤ (∑ j:Fin n,
           (rowPotential (σ (Fin.castAdd m j))+leftPotential j))+
         (∑ j:Fin m,
           (rowPotential (σ (Fin.natAdd n j))+rightPotential j)):=
       add_le_add hleft_sum hright_sum
     _=(∑ row:Fin (n+m),rowPotential row)+
         (∑ j:Fin n,leftPotential j)+
         (∑ j:Fin m,rightPotential j):=by
       rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
       linear_combination hrow_sum
     _ ≤ (C:ℤ):=hbudget
 exact_mod_cast hcast
namespace CornerStaircase
def surfaceHeight (i:ℕ):ℕ:=
 if i ≤ 24 then 178-i else if i=25 then 5 else 0
def tailHeight (K j:ℕ):ℕ:=
 if j=0 then 178*K
 else if j ≤ 24*K+1 then 178*K+1-j
 else if j ≤ 25*K+1 then 3730*K+149-149*j
 else 0
def rowPrice (K r:ℕ):ℤ:=
 178-((r-1:ℕ):ℤ)-
   148*((r-(24*K+25):ℕ):ℤ)
def rowPotential (K:ℕ) (r:Fin (25+(25*K+1))):ℤ:=
 rowPrice K r
def scaledColumnPotential (K:ℕ) (b:Fin 25):ℤ:=
 178*(K:ℤ)-178+(b:ℕ)
def surfaceColumnPrice (K a:ℕ):ℤ:=
 ((a-1:ℕ):ℤ)+
   148*((a-(24*K+1):ℕ):ℤ)
def surfaceColumnPotential (K:ℕ) (a:Fin (25*K+1)):ℤ:=
 surfaceColumnPrice K a
theorem tailHeight_le_potentials (K:ℕ) (hK:1 ≤ K)
   (row:Fin (25+(25*K+1))) (b:Fin 25)
   (hrow:(row:ℕ)∈Set.Icc (b:ℕ) ((b:ℕ)+(25*K+1))):
   (tailHeight K ((row:ℕ)-(b:ℕ)):ℤ) ≤
     rowPotential K row+scaledColumnPotential K b:=by
 rcases Set.mem_Icc.mp hrow with ⟨hbr,hrb⟩
 have hb:(b:ℕ) ≤ 24:=Nat.le_pred_of_lt b.isLt
 unfold tailHeight rowPotential rowPrice scaledColumnPotential
 split_ifs with hzero hfirst hsecond
 · push_cast
   omega
 · push_cast
   omega
 · push_cast
   omega
 · omega
theorem surfaceHeight_le_potentials (K:ℕ) (hK:1 ≤ K)
   (row:Fin (25+(25*K+1))) (a:Fin (25*K+1))
   (hrow:(row:ℕ)∈Set.Icc (a:ℕ) ((a:ℕ)+25)):
   (surfaceHeight ((row:ℕ)-(a:ℕ)):ℤ) ≤
     rowPotential K row+surfaceColumnPotential K a:=by
 rcases Set.mem_Icc.mp hrow with ⟨har,hra⟩
 unfold surfaceHeight rowPotential rowPrice surfaceColumnPotential surfaceColumnPrice
 split_ifs with hfirst hlast
 · push_cast
   omega
 · push_cast
   omega
 · omega
private theorem sum_fin_natSub_cast (A L:ℕ):
   (∑ i:Fin (A+L+1),(((i:ℕ)-A:ℕ):ℤ))=
     ∑ i∈Finset.range (L+1),(i:ℤ):=by
 calc
   _=∑ i∈Finset.range (A+L+1),
         (((i:ℕ)-A:ℕ):ℤ):=by
     simpa using (Fin.sum_univ_eq_sum_range (n:=A+L+1)
       (fun i:ℕ => (((i:ℕ)-A:ℕ):ℤ)))
   _=_:=by
     have hp:
         (∑ x∈Finset.range A,(((x-A:ℕ):ℤ)))=0:=by
       apply Finset.sum_eq_zero
       intro x hx
       rw [Nat.sub_eq_zero_of_le
         (Nat.le_of_lt (Finset.mem_range.mp hx))]
       simp
     rw [show A+L+1=A+(L+1) by omega]
     rw [Finset.sum_range_add]
     rw [hp]
     simp
theorem potentialBudget (K:ℕ) (hK:1 ≤ K):
   (∑ row,rowPotential K row)+
       (∑ b,scaledColumnPotential K b)+
       (∑ a,surfaceColumnPotential K a)=(8127*K+178:ℕ):=by
 have hrowBase:
     (∑ r:Fin (25+(25*K+1)),
         ((((r:ℕ)-1:ℕ):ℤ)))=
       ∑ i∈Finset.range (25*K+25),(i:ℤ):=by
   have hcard:25+(25*K+1)=1+(25*K+24)+1:=by omega
   rw [hcard]
   simpa only [show 25*K+24+1=25*K+25 by omega] using
     sum_fin_natSub_cast 1 (25*K+24)
 have hrowTail:
     (∑ r:Fin (25+(25*K+1)),
         ((((r:ℕ)-(24*K+25):ℕ):ℤ)))=
       ∑ i∈Finset.range (K+1),(i:ℤ):=by
   have hcard:25+(25*K+1)=(24*K+25)+K+1:=by omega
   rw [hcard]
   exact sum_fin_natSub_cast (24*K+25) K
 have hcolumnBase:
     (∑ a:Fin (25*K+1),
         ((((a:ℕ)-1:ℕ):ℤ)))=
       ∑ i∈Finset.range (25*K),(i:ℤ):=by
   have hcard:25*K+1=1+(25*K-1)+1:=by omega
   rw [hcard]
   simpa only [show 25*K-1+1=25*K by omega] using
     sum_fin_natSub_cast 1 (25*K-1)
 have hcolumnTail:
     (∑ a:Fin (25*K+1),
         ((((a:ℕ)-(24*K+1):ℕ):ℤ)))=
       ∑ i∈Finset.range K,(i:ℤ):=by
   have hcard:25*K+1=(24*K+1)+(K-1)+1:=by omega
   rw [hcard]
   simpa only [show K-1+1=K by omega] using
     sum_fin_natSub_cast (24*K+1) (K-1)
 have hlongDifference:
     (∑ i∈Finset.range (25*K+25),(i:ℤ))=
       (∑ i∈Finset.range (25*K),(i:ℤ))+
         (625*K+300):=by
   rw [Finset.sum_range_add]
   norm_num [Finset.sum_range_succ]
   ring
 have htailDifference:
     (∑ i∈Finset.range (K+1),(i:ℤ))=
       (∑ i∈Finset.range K,(i:ℤ))+K:=by
   rw [Finset.sum_range_succ]
 unfold rowPotential rowPrice scaledColumnPotential surfaceColumnPotential surfaceColumnPrice
 simp only [Finset.sum_sub_distrib, ←Finset.mul_sum,Finset.sum_add_distrib,
   Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
 rw [hrowBase,hrowTail,hcolumnBase,hcolumnTail,
   hlongDifference,htailDifference]
 norm_num [Fin.sum_univ_succ]
 ring
def partialBudget (K m:ℕ):ℤ:=
 (∑ row:Fin (25+m),rowPrice K row)+
   (∑ b:Fin 25,scaledColumnPotential K b)+
   (∑ a:Fin m,surfaceColumnPrice K a)
def rowPotentialUpTo (K m:ℕ) (row:Fin (25+m)):ℤ:=
 rowPrice K row
def surfaceColumnPotentialUpTo (K m:ℕ) (a:Fin m):ℤ:=
 surfaceColumnPrice K a
private def basePotential (K:ℕ):ℤ:=
 (∑ row∈Finset.range 25,rowPrice K row)+
   ∑ b:Fin 25,scaledColumnPotential K b
private def pairPotential (K a:ℕ):ℤ:=
 rowPrice K (25+a)+surfaceColumnPrice K a
private theorem partialBudget_eq_base_add_pairs (K m:ℕ):
   partialBudget K m=basePotential K+
     ∑ a∈Finset.range m,pairPotential K a:=by
 unfold partialBudget basePotential pairPotential rowPrice surfaceColumnPrice
 rw [show (∑ row:Fin (25+m),
     (178-(((row:ℕ)-1:ℕ):ℤ)-
       148*(((row:ℕ)-(24*K+25):ℕ):ℤ)))=
     ∑ row∈Finset.range (25+m),
     (178-(((row:ℕ)-1:ℕ):ℤ)-
       148*(((row:ℕ)-(24*K+25):ℕ):ℤ)) by
   simpa using (Fin.sum_univ_eq_sum_range (n:=25+m)
     (fun row:ℕ => (178:ℤ)-((row-1:ℕ):ℤ)-
       148*((row-(24*K+25):ℕ):ℤ)))]
 rw [show (∑ a:Fin m,
     ((((a:ℕ)-1:ℕ):ℤ)+
       148*(((a:ℕ)-(24*K+1):ℕ):ℤ)))=
     ∑ a∈Finset.range m,
     ((((a:ℕ)-1:ℕ):ℤ)+
       148*(((a:ℕ)-(24*K+1):ℕ):ℤ)) by
   simpa using (Fin.sum_univ_eq_sum_range (n:=m)
     (fun a:ℕ => (((a-1:ℕ):ℤ)+
       148*((a-(24*K+1):ℕ):ℤ))))]
 rw [Finset.sum_range_add]
 simp only [Finset.sum_add_distrib]
 ring
theorem pairPotential_nonnegative (K a:ℕ)
   (ha:a < 25*K+1):0 ≤ pairPotential K a:=by
 unfold pairPotential rowPrice surfaceColumnPrice
 push_cast
 omega
theorem partialBudget_le (K m:ℕ) (hm:m ≤ 25*K+1) (hK:1 ≤ K):
   partialBudget K m ≤ (8127*K+178:ℕ):=by
 rw [partialBudget_eq_base_add_pairs]
 calc
   _ ≤ basePotential K+
       ∑ a∈Finset.range (25*K+1),pairPotential K a:=by
     gcongr
     intro a ha _
     exact pairPotential_nonnegative K a (Finset.mem_range.mp ha)
   _=partialBudget K (25*K+1):=
     (partialBudget_eq_base_add_pairs K (25*K+1)).symm
   _=(8127*K+178:ℕ):=by
     simpa [partialBudget,rowPotential,surfaceColumnPotential] using
       potentialBudget K hK
theorem tailHeight_le_potentials_upTo (K m:ℕ) (hK:1 ≤ K)
   (hm:m ≤ 25*K+1) (row:Fin (25+m)) (b:Fin 25)
   (hrow:(row:ℕ)∈Set.Icc (b:ℕ) ((b:ℕ)+m)):
   (tailHeight K ((row:ℕ)-(b:ℕ)):ℤ) ≤
     rowPotentialUpTo K m row+scaledColumnPotential K b:=by
 rcases Set.mem_Icc.mp hrow with ⟨hbr,hrb⟩
 have hb:(b:ℕ) ≤ 24:=Nat.le_pred_of_lt b.isLt
 unfold tailHeight rowPotentialUpTo rowPrice scaledColumnPotential
 split_ifs with hzero hfirst hsecond
 · push_cast
   omega
 · push_cast
   omega
 · push_cast
   omega
 · omega
theorem surfaceHeight_le_potentials_upTo (K m:ℕ) (hK:1 ≤ K)
   (hm:m ≤ 25*K+1) (row:Fin (25+m)) (a:Fin m)
   (hrow:(row:ℕ)∈Set.Icc (a:ℕ) ((a:ℕ)+25)):
   (surfaceHeight ((row:ℕ)-(a:ℕ)):ℤ) ≤
     rowPotentialUpTo K m row+surfaceColumnPotentialUpTo K m a:=by
 rcases Set.mem_Icc.mp hrow with ⟨har,hra⟩
 unfold surfaceHeight rowPotentialUpTo rowPrice
   surfaceColumnPotentialUpTo surfaceColumnPrice
 split_ifs with hfirst hlast
 · push_cast
   omega
 · push_cast
   omega
 · omega
theorem resultant_natDegree_le_actual_tail
   (B H:F[X][Y]) (K m:ℕ) (hK:1 ≤ K)
   (hm:m ≤ 25*K+1)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i):
   (Polynomial.resultant B H 25 m).natDegree ≤ 8127*K+178:=by
 apply bivariate_resultant_natDegree_le_of_sylvester_dual
   B H 25 m surfaceHeight (tailHeight K) (8127*K+178)
   hB hH (rowPotentialUpTo K m) (scaledColumnPotential K)
     (surfaceColumnPotentialUpTo K m)
 · exact tailHeight_le_potentials_upTo K m hK hm
 · exact surfaceHeight_le_potentials_upTo K m hK hm
 · exact partialBudget_le K m hm hK
theorem ordinary_resultant_natDegree_le
   (B H:F[X][Y]) (K:ℕ) (hK:1 ≤ K) (hHne:H≠0)
   (hBouter:B.natDegree ≤ 25)
   (hHouter:H.natDegree ≤ 25*K+1)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i):
   (Polynomial.resultant B H).natDegree ≤ 8127*K+178:=by
 by_cases hres:Polynomial.resultant B H=0
 · simp [hres]
 · have hfixed:=resultant_natDegree_le_actual_tail
     B H K H.natDegree hK hHouter hB hH
   have hcoeff:H.coeff H.natDegree≠0:=by
     rw [Polynomial.coeff_natDegree]
     exact Polynomial.leadingCoeff_ne_zero.mpr hHne
   let factor:F[X]:=
     (-1)^(H.natDegree*(25-B.natDegree))*
       H.coeff H.natDegree^(25-B.natDegree)
   have hfactor:factor≠0:=by
     apply _root_.mul_ne_zero
     · exact pow_ne_zero _ (by norm_num)
     · exact pow_ne_zero _ hcoeff
   have hpad:=Polynomial.resultant_add_left_deg
     (f:=B) (g:=H) (m:=B.natDegree)
     (k:=25-B.natDegree) (n:=H.natDegree) le_rfl
   have hsum:B.natDegree+(25-B.natDegree)=25:=
     Nat.add_sub_of_le hBouter
   rw [hsum] at hpad
   change Polynomial.resultant B H 25 H.natDegree=
     factor*Polynomial.resultant B H at hpad
   calc
     (Polynomial.resultant B H).natDegree ≤
         (factor*Polynomial.resultant B H).natDegree:=by
       rw [Polynomial.natDegree_mul hfactor hres]
       omega
     _=(Polynomial.resultant B H 25 H.natDegree).natDegree:=by
       rw [hpad]
     _ ≤ 8127*K+178:=hfixed
theorem resultant_natDegree_le_of_budget
   (B H:F[X][Y]) (K:ℕ) (hK:1 ≤ K)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i)
   (hbudget:(∑ row,rowPotential K row)+
       (∑ b,scaledColumnPotential K b)+
       (∑ a,surfaceColumnPotential K a) ≤ (8127*K+178:ℕ)):
   (Polynomial.resultant B H 25 (25*K+1)).natDegree ≤
     8127*K+178:=by
 apply bivariate_resultant_natDegree_le_of_sylvester_dual
   B H 25 (25*K+1) surfaceHeight (tailHeight K) (8127*K+178)
   hB hH (rowPotential K) (scaledColumnPotential K)
     (surfaceColumnPotential K)
 · exact tailHeight_le_potentials K hK
 · exact surfaceHeight_le_potentials K hK
 · exact hbudget
theorem resultant_natDegree_le
   (B H:F[X][Y]) (K:ℕ) (hK:1 ≤ K)
   (hB:∀ i,(B.coeff i).natDegree ≤ surfaceHeight i)
   (hH:∀ i,(H.coeff i).natDegree ≤ tailHeight K i):
   (Polynomial.resultant B H 25 (25*K+1)).natDegree ≤
     8127*K+178:=by
 apply resultant_natDegree_le_of_budget B H K hK hB hH
 exact (potentialBudget K hK).le
end CornerStaircase
theorem bivariate_resultant_natDegree_le_totalDegree
   (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree ≤
     m*totalDegree B+n*totalDegree H-m*n:=by
 classical
 let M:Matrix (Fin (n+m)) (Fin (n+m)) F[X]:=
   Polynomial.sylvester B H n m
 rw [Polynomial.resultant]
 change M.det.natDegree ≤ _
 apply natDegree_det_le_of_perm_products_le (M:=M)
 intro σ
 by_cases hzero:∃ i:Fin (n+m),M (σ i) i=0
 · rcases hzero with ⟨i,hi⟩
   have hprod:(∏ i:Fin (n+m),M (σ i) i)=0:=
     Finset.prod_eq_zero (Finset.mem_univ i) hi
   simp [hprod]
 · have hne (i:Fin (n+m)):M (σ i) i≠0:=by
     intro hi
     exact hzero ⟨i,hi⟩
   let lidx:Fin n → ℕ:=fun j =>
     ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)
   let ridx:Fin m → ℕ:=fun j =>
     ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)
   let ldeg:Fin n → ℕ:=fun j =>
     (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree
   let rdeg:Fin m → ℕ:=fun j =>
     (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree
   have hleft_Icc (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+m)
         then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.castAdd m j) (by simp [hentry,hc])
   have hright_Icc (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+n)
         then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.natAdd n j) (by simp [hentry,hc])
   have hleft (j:Fin n):lidx j+ldeg j ≤ totalDegree H:=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
           if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+m)
           then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hleft_Icc j)]
     have hcoeff:H.coeff (lidx j)≠0:=by
       have hh:=hne (Fin.castAdd m j)
       rw [hentry] at hh
       simpa only [lidx] using hh
     have hsupp:lidx j∈H.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:ldeg j=(H.coeff (lidx j)).natDegree:=by
       dsimp [ldeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le H hsupp
   have hright (j:Fin m):ridx j+rdeg j ≤ totalDegree B:=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
           if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+n)
           then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hright_Icc j)]
     have hcoeff:B.coeff (ridx j)≠0:=by
       have hh:=hne (Fin.natAdd n j)
       rw [hentry] at hh
       simpa only [ridx] using hh
     have hsupp:ridx j∈B.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:rdeg j=(B.coeff (ridx j)).natDegree:=by
       dsimp [rdeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le B hsupp
   have hleft_sum:
       (∑ j:Fin n,(lidx j+ldeg j)) ≤ n*totalDegree H:=by
     calc
       _ ≤ ∑ _j:Fin n,totalDegree H:=
         Finset.sum_le_sum (fun j _ => hleft j)
       _=n*totalDegree H:=by simp
   have hright_sum:
       (∑ j:Fin m,(ridx j+rdeg j)) ≤ m*totalDegree B:=by
     calc
       _ ≤ ∑ _j:Fin m,totalDegree B:=
         Finset.sum_le_sum (fun j _ => hright j)
       _=m*totalDegree B:=by simp
   have hidxsum:
       (∑ j:Fin n,lidx j)+(∑ j:Fin m,ridx j)=m*n:=by
     have hleft_row (j:Fin n):
         ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)=(j:ℕ)+lidx j:=by
       dsimp [lidx]
       have hle:=(Set.mem_Icc.mp (hleft_Icc j)).1
       omega
     have hright_row (j:Fin m):
         ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)=(j:ℕ)+ridx j:=by
       dsimp [ridx]
       have hle:=(Set.mem_Icc.mp (hright_Icc j)).1
       omega
     have hsum_left_rows:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin n,lidx j):=by
       calc
         _=∑ j:Fin n,((j:ℕ)+lidx j):=
           Finset.sum_congr rfl (fun j _ => hleft_row j)
         _=_:=Finset.sum_add_distrib
     have hsum_right_rows:
         (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin m,(j:ℕ))+(∑ j:Fin m,ridx j):=by
       calc
         _=∑ j:Fin m,((j:ℕ)+ridx j):=
           Finset.sum_congr rfl (fun j _ => hright_row j)
         _=_:=Finset.sum_add_distrib
     have hperm_sum:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           ∑ i:Fin (n+m),(i:ℕ):=by
       simpa using (Equiv.sum_comp σ (fun i:Fin (n+m) => (i:ℕ)))
     have hrows_split:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ)):=by
       simpa using (Fin.sum_univ_add
         (fun i:Fin (n+m) => ((σ i:Fin (n+m)):ℕ)))
     have hcols_split:
         (∑ i:Fin (n+m),(i:ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin m,(n+(j:ℕ))):=by
       simpa using (Fin.sum_univ_add (fun i:Fin (n+m) => (i:ℕ)))
     have hright_cols:
         (∑ j:Fin m,(n+(j:ℕ)))=
           m*n+∑ j:Fin m,(j:ℕ):=by
       simp [Finset.sum_add_distrib,Finset.sum_const]
     have hmain:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+
             (m*n+∑ j:Fin m,(j:ℕ)):=by
       rw [←hrows_split,hperm_sum,hcols_split,hright_cols]
     omega
   have hsum:
       ((∑ j:Fin n,lidx j)+(∑ j:Fin n,ldeg j))+
           ((∑ j:Fin m,ridx j)+(∑ j:Fin m,rdeg j)) ≤
         n*totalDegree H+m*totalDegree B:=by
     simpa only [Finset.sum_add_distrib] using Nat.add_le_add hleft_sum hright_sum
   have hdeg_parts:
       (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j) ≤
         m*totalDegree B+n*totalDegree H-m*n:=by
     omega
   have hsum_deg_split:
       (∑ i:Fin (n+m),(M (σ i) i).natDegree)=
         (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=by
     simpa only [ldeg,rdeg] using
       (Fin.sum_univ_add (fun i:Fin (n+m) => (M (σ i) i).natDegree))
   calc
     (∏ i:Fin (n+m),M (σ i) i).natDegree ≤
         ∑ i:Fin (n+m),(M (σ i) i).natDegree:=by
       simpa using Polynomial.natDegree_prod_le Finset.univ
         (fun i:Fin (n+m) => M (σ i) i)
     _=(∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=hsum_deg_split
     _ ≤ _:=hdeg_parts
end ProximityPrize.SubmissionLower
