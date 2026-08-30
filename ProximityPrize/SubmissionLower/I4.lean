import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.C
namespace ProximityPrize.SubmissionLower.RCN071
open scoped BigOperators
open RCN081
noncomputable section
variable {K:Type*} [Field K]
theorem weightedTotalDegree_prod_eq
   {I:Type*} [DecidableEq I] (weights:Fin 4 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 4) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=
       Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul weights (f a) (∏ i∈s,f i) hfa hprod,
       ih hfs]
theorem sum_weightedTotalDegree_le_of_prod_dvd
   {I:Type*} [DecidableEq I] (weights:Fin 4 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ i∈s,f i)∣Q):
   (∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈s,f i)≠0:=by
   intro hzero
   obtain ⟨R,hR⟩:=hdiv
   apply hQ
   rw [hR,hzero,zero_mul]
 have hf:∀ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [←weightedTotalDegree_prod_eq weights s f hf]
 exact weightedTotalDegree_le_of_dvd weights _ Q hdiv hQ
def weightEmbed3 (weights:Fin 3 → ℕ):
   (Fin 3 →₀ ℕ) →+(Fin 4 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+
   Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed3_original (weights:Fin 3 → ℕ)
   (d:Fin 3 →₀ ℕ) (i:Fin 3):
   weightEmbed3 weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed3]
theorem weightEmbed3_last (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   weightEmbed3 weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed3]
theorem weightEmbed3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightEmbed3 weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 4 →₀ ℕ↦a i.castSucc) h
 simpa only [weightEmbed3_original] using hi
def weightedLift3 (weights:Fin 3 → ℕ):
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed3 weights)
theorem weightedLift3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightedLift3 (K:=K) weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed3_injective weights)
theorem weightedLift3_ne_zero (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K) (hP:P≠0):
   weightedLift3 weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift3_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).support=
     P.support.image (weightEmbed3 weights):=by
 change (Finsupp.mapDomain (weightEmbed3 weights)
     (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed3 weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective
   (weightEmbed3_injective weights) _
theorem degree_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift3 weights P).degreeOf (3:Fin 4)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift3,Finset.sup_image]
 apply congrArg (fun f:(Fin 3 →₀ ℕ) → ℕ↦P.support.sup f)
 funext d
 exact weightEmbed3_last weights d
theorem weightedTotalDegree_mul_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift3 weights (P*Q)).degreeOf (3:Fin 4):=
     (degree_weightedLift3 weights (P*Q)).symm
   _=(weightedLift3 weights P*weightedLift3 weights Q).degreeOf
       (3:Fin 4):=by rw [map_mul]
   _=(weightedLift3 weights P).degreeOf (3:Fin 4)+
       (weightedLift3 weights Q).degreeOf (3:Fin 4):=
     MvPolynomial.degreeOf_mul_eq
       (weightedLift3_ne_zero weights P hP)
       (weightedLift3_ne_zero weights Q hQ)
   _=_:=by rw [degree_weightedLift3,degree_weightedLift3]
theorem weightedTotalDegree_le_of_dvd_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul_fin3 weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_prod_eq_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul_fin3 weights (f a) (∏ i∈s,f i)
         hfa hprod,ih hfs]
theorem sum_weightedTotalDegree_le_of_prod_dvd_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K) (Q:MvPolynomial (Fin 3) K)
   (hQ:Q≠0) (hdiv:(∏ i∈s,f i)∣Q):
   (∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈s,f i)≠0:=by
   intro hzero
   obtain ⟨R,hR⟩:=hdiv
   apply hQ
   rw [hR,hzero,zero_mul]
 have hf:∀ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [←weightedTotalDegree_prod_eq_fin3 weights s f hf]
 exact weightedTotalDegree_le_of_dvd_fin3 weights _ Q hdiv hQ
end
end ProximityPrize.SubmissionLower.RCN071
