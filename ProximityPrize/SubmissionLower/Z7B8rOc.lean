import ProximityPrize.SubmissionLower.ZPMTD6c
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qwWTALb
noncomputable section
open Polynomial MvPolynomial Finset
open P5_7_1
open qaySLPd
open cu (L)
open scoped BigOperators
abbrev up:X3 →+* TopRow :=
 (MvPolynomial.rename (R:=L[X]) (Fin.castSucc:Fin 3→Fin 4)).toRingHom
private abbrev flat :=(optionEquivRight L (Fin 3)).symm
private theorem bcz (f :X3) (m:Fin 3 →₀ ℕ) (i:ℕ) :
  (flat f).coeff (m.optionElim i)=(f.coeff m).coeff i:= by
 rw [← optionEquivRight_coeff_coeff,AlgEquiv.apply_symm_apply]
private abbrev deg (x :ℕ) (w:Fin 3→ℕ) (f :X3) :=
 (flat f).weightedTotalDegree (fun i=>i.elim x w)
private theorem deg_le_iff (x :ℕ) (w:Fin 3→ℕ) (f :X3) (b:ℕ) :
   deg x w f≤b ↔
     ∀ m∈f.support,x*(f.coeff m).natDegree+m.weight w≤b:= by
 classical
 change (flat f).weightedTotalDegree (fun i=>i.elim x w)≤b↔_
 rw [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
 constructor
 · intro h m hm
   have hc:=Polynomial.leadingCoeff_ne_zero.mpr (mem_support_iff.mp hm)
   have hu:m.optionElim (f.coeff m).natDegree∈(flat f).support :=
     mem_support_iff.mpr (by rwa [bcz])
   simpa only [Finsupp.weight_optionElim] using h _ hu
 · intro h m hm
   have hn: (f.coeff m.some).coeff (m none)≠0:= by
     rw [← bcz,Finsupp.optionElim_some]
     exact mem_support_iff.mp hm
   have hs :=h m.some (mem_support_iff.mpr (fun hz=>hn (by simp [hz])))
   rw [← Finsupp.optionElim_some m,Finsupp.weight_optionElim]
   exact (Nat.add_le_add_right (Nat.mul_le_mul_left x (le_natDegree_of_ne_zero hn)) _).trans hs
private theorem coeff_origin (B:TopRow) (j:ℕ) (m:Fin 3 →₀ ℕ)
   (hm:m∈((YN L[X] B).coeff j).support) :
   ∃ e∈B.support,B.coeff e=((YN L[X] B).coeff j).coeff m ∧
     (∀ i:Fin 3,e i.castSucc=m i)∧e 3=j:= by
 have hs :m.optionElim j∈(rename finSuccEquivLast B).support :=
   (mem_support_coeff_optionEquivLeft _).mp hm
 rw [support_rename_of_injective finSuccEquivLast.injective] at hs
 obtain ⟨e,he,h⟩:=Finset.mem_image.mp hs
 refine ⟨e,he,?_,?_,?_⟩
 · change B.coeff e=((optionEquivLeft _ _ (rename finSuccEquivLast B)).coeff j).coeff m
   rw [optionEquivLeft_coeff_coeff,← h,coeff_rename_mapDomain _ finSuccEquivLast.injective]
 · intro i
   rw [← Finsupp.mapDomain_apply_of_injective finSuccEquivLast.injective e i.castSucc,
     h,finSuccEquivLast_castSucc,Finsupp.optionElim_apply_some]
 · change e (Fin.last 3)=j
   rw [← Finsupp.mapDomain_apply_of_injective finSuccEquivLast.injective e (Fin.last 3),
     h,finSuccEquivLast_last,Finsupp.optionElim_apply_none]
private theorem b0v {n b:ℕ} (w:Option (Fin 3)→ℕ)
   (M:Matrix (Fin n) (Fin n) (MvPolynomial (Option (Fin 3)) L))
   (h : ∀ i j,(M i j).weightedTotalDegree w≤b) :
   M.det.weightedTotalDegree w≤n*b:= by
 classical
 rw [Matrix.det_apply]
 refine AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun σ _ => ?_)
 have hv : (∏ j,M (σ j) j).weightedTotalDegree w≤n*b:= by
   refine (AddMonoidAlgebra.supDegree_prod_le (map_zero (Finsupp.weight w))
     (map_add (Finsupp.weight w))).trans ?_
   change (∑ j,(M (σ j) j).weightedTotalDegree w)≤n*b
   calc
     _ ≤ ∑ _j:Fin n,b:=sum_le_sum fun j _=>h (σ j) j
     _ = _:= by simp
 change (Equiv.Perm.sign σ•(∏ i,M (σ i) i)).weightedTotalDegree w≤n*b
 rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
 · simpa only [hs,one_smul] using hv
 · have hsign:Equiv.Perm.sign σ•(∏ i,M (σ i) i) = -(∏ i,M (σ i) i) := by simp [hs]
   rw [hsign]
   exact (AddMonoidAlgebra.supDegree_neg).le.trans hv
private theorem gMe (w:Fin 3→ℕ) (m:Fin 3 →₀ ℕ) :
  m.weight w=w 0*m 0+w 1*m 1+w 2*m 2 := by
 simp only [Finsupp.weight_eq_sum,Fin.sum_univ_three,smul_eq_mul,Nat.mul_comm,add_assoc]
end
end qwWTALb
