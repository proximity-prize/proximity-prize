import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactGenericSurface
noncomputable section
variable {K L:Type*} [Field K] [Field L]
def collectX (K:Type*) [Field K]:
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 3) (Polynomial K):=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 3)).trans
    (MvPolynomial.optionEquivRight K (Fin 3))
@[simp] theorem collectX_C (a:K):
    collectX K (MvPolynomial.C a)=MvPolynomial.C (Polynomial.C a):=by
  simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_zero:
    collectX K (MvPolynomial.X (0:Fin 4))=MvPolynomial.C Polynomial.X:=by
  simp [collectX,MvPolynomial.renameEquiv_apply]
@[simp] theorem collectX_X_succ (i:Fin 3):
    collectX K (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
  simp [collectX,MvPolynomial.renameEquiv_apply]
def surfaceMap (φ:Polynomial K →+*L):
    MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 3) L:=
  (MvPolynomial.map φ).comp (collectX K).toRingHom
@[simp] theorem surfaceMap_C (φ:Polynomial K →+*L) (a:K):
    surfaceMap φ (MvPolynomial.C a)=MvPolynomial.C (φ (Polynomial.C a)):=by
  simp [surfaceMap]
@[simp] theorem surfaceMap_X_zero (φ:Polynomial K →+*L):
    surfaceMap φ (MvPolynomial.X (0:Fin 4))=MvPolynomial.C (φ Polynomial.X):=by
  simp [surfaceMap]
@[simp] theorem surfaceMap_X_succ (φ:Polynomial K →+*L) (i:Fin 3):
    surfaceMap φ (MvPolynomial.X i.succ)=MvPolynomial.X i:=by
  simp [surfaceMap]
theorem surfaceMap_injective (φ:Polynomial K →+*L) (hφ:Function.Injective φ):
    Function.Injective (surfaceMap φ):=
  (MvPolynomial.map_injective φ hφ).comp (collectX K).injective
theorem surfaceMap_ne_zero (φ:Polynomial K →+*L) (hφ:Function.Injective φ)
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0):surfaceMap φ Q≠0:=by
  intro h
  apply hQ
  apply surfaceMap_injective φ hφ
  simpa only [map_zero] using h
theorem surfaceMap_eq_eval₂Hom (φ:Polynomial K →+*L):
    surfaceMap φ=
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (φ.comp Polynomial.C))
        (Fin.cases (MvPolynomial.C (φ Polynomial.X)) MvPolynomial.X):=by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem eval_surfaceMap (φ:Polynomial K →+*L)
    (v:Fin 3 → L) (Q:MvPolynomial (Fin 4) K):
    MvPolynomial.eval v (surfaceMap φ Q)=
      MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v) Q:=by
  have hhom:(MvPolynomial.eval v).comp (surfaceMap φ)=
      MvPolynomial.eval₂Hom (φ.comp Polynomial.C) (Fin.cases (φ Polynomial.X) v):=by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact RingHom.congr_fun hhom Q
theorem surfaceMap_monomial (φ:Polynomial K →+*L)
    (d:Fin 4 →₀ ℕ) (a:K):
    surfaceMap φ (MvPolynomial.monomial d a)=
      MvPolynomial.monomial d.tail (φ (Polynomial.C a)*(φ Polynomial.X)^d 0):=by
  rw [surfaceMap_eq_eval₂Hom,MvPolynomial.eval₂Hom_monomial]
  simp only [RingHom.comp_apply,Finsupp.prod_pow,Fin.prod_univ_succ,Fin.cases_zero,
    Fin.cases_succ,MvPolynomial.monomial_eq,Finsupp.tail_apply,
    map_mul,map_pow]
  ring
theorem support_surfaceMap_subset (φ:Polynomial K →+*L)
    (Q:MvPolynomial (Fin 4) K):
    (surfaceMap φ Q).support ⊆ Q.support.image Finsupp.tail:=by
  classical
  have hsum:surfaceMap φ Q=
      ∑ d∈Q.support,surfaceMap φ (MvPolynomial.monomial d (MvPolynomial.coeff d Q)):=by
    rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
  intro e he
  rw [hsum] at he
  obtain ⟨d,hd,hed⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  rw [surfaceMap_monomial] at hed
  have heq:e=d.tail:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
  exact Finset.mem_image.mpr ⟨d,hd,heq.symm⟩
theorem surfaceMap_degreeOf_le (φ:Polynomial K →+*L)
    (Q:MvPolynomial (Fin 4) K) (i:Fin 3):
    (surfaceMap φ Q).degreeOf i ≤ Q.degreeOf i.succ:=by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
  exact MvPolynomial.monomial_le_degreeOf i.succ hd
theorem surfaceMap_separated_caps (φ:Polynomial K →+*L)
    (Q:MvPolynomial (Fin 4) K) (ell s zcap:ℕ)
    (hy:Q.degreeOf 1 ≤ ell) (hr:Q.degreeOf 2 ≤ s) (hz:Q.degreeOf 3 ≤ zcap):
    (surfaceMap φ Q).degreeOf 0 ≤ ell∧
      (surfaceMap φ Q).degreeOf 1 ≤ s∧
      (surfaceMap φ Q).degreeOf 2 ≤ zcap:=
  ⟨(surfaceMap_degreeOf_le φ Q 0).trans hy,
    (surfaceMap_degreeOf_le φ Q 1).trans hr,
    (surfaceMap_degreeOf_le φ Q 2).trans hz⟩
theorem surfaceMap_joint_seed_cap (φ:Polynomial K →+*L)
    (Q:MvPolynomial (Fin 4) K) (cap:ℕ)
    (hcap:∀ d∈Q.support,d 1+d 3 ≤ cap):
    ∀ e∈(surfaceMap φ Q).support,e 0+e 2 ≤ cap:=by
  classical
  intro e he
  obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
  exact hcap d hd
end
end ProximityPrize.SubmissionLower.ContactGenericSurface
