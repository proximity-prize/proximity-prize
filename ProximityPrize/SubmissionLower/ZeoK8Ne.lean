import ProximityPrize.SubmissionLower.ZEe4bHc
set_option Elab.async false
open _root_ renaming Nat.sub_add_cancel → zxt, Polynomial.X → z7y, Polynomial.algebra → z86, Polynomial.isLocalization → zyz, Polynomial.map_injective → zTo, Polynomial.map_zero → zgY
set_option backward.isDefEq.respectTransparency false
namespace qWIOgVd
noncomputable section
open Polynomial Finset
open scoped nonZeroDivisors
open P5_7 (OneSeedEquation)
open cu (L FX)
open P5_7_7 (phys embed Dg)
open qGnV2ac (coeff_seedDerivative)
open q7kdBxd (Input)
theorem embed_coeff (F:Dg) (i:ℕ) :
 (embed F).coeff i=(F.coeff i).map phys :=coeff_map _ _
theorem embed_degree (F:Dg) : (embed F).natDegree=F.natDegree :=
 natDegree_map_eq_of_injective (zTo _ phys_inj) F
def scaleY {R:Type*} [CommRing R] (u v :R) (h:u*v=1) :R[X] ≃+* R[X] := by
  have h' : v*u=1 :=(mul_comm v u).trans h
  exact (algEquivOfCompEqX (C u*z7y) (C v*z7y)
    (by simp only [mul_comp,C_comp,X_comp,← mul_assoc,← C_mul,h,C_1,one_mul])
    (by simp only [mul_comp,C_comp,X_comp,← mul_assoc,← C_mul,h',C_1,one_mul])).toRingEquiv
theorem scaleY_apply {R:Type*} [CommRing R] (u v :R) (h:u*v=1) (f :R[X]) :
  scaleY u v h f=f.comp (C u*z7y) :=
 comp_eq_aeval.symm
theorem scaleY_coeff {R:Type*} [CommRing R] (u v :R) (h:u*v=1) (f :R[X]) (i:ℕ) :
   (scaleY u v h f).coeff i=f.coeff i*u^i :=
 (congrArg (fun g:R[X]=>g.coeff i) (scaleY_apply u v h f)).trans comp_C_mul_X_coeff
private theorem embed_irred (J:Input) :Irreducible (embed J.F) := by
 let:Algebra (L[X][X]) (FX[X]) :=z86 (L[X]) FX
 let:Algebra Dg OneSeedEquation :=z86 (L[X][X]) FX[X]
 let M:=(L[X])⁰.map (C:L[X] →+* L[X][X])
 let:IsLocalization M FX[X] :=zyz (L[X])⁰ FX
 let N :=M.map (C:L[X][X] →+* Dg)
 let:IsLocalization N OneSeedEquation := by
  exact zyz M (Polynomial FX)
 have hp:Prime J.F :=
  (UniqueFactorizationMonoid.irreducible_iff_prime (α:=Dg)).mp J.Ca.irreducible
 have hd : ¬ IsUnit (embed J.F) := fun h=> by
  have hd:=natDegree_eq_zero_of_isUnit h
  rw [embed_degree,J.Ca.jU] at hd
  have :=J.Ca.two_le
  omega
 have hn:embed J.F≠0 :=
  (map_ne_zero_iff embed (zTo _ (zTo _ phys_inj))).mpr hp.ne_zero
 let f :=IsLocalization.toLocalizationMap (R:=Dg) N OneSeedEquation
 have h:Prime (f J.F) :=
  @Submonoid.LocalizationMap.map_prime Dg OneSeedEquation _ _ N f J.F hp hn hd
 exact h.irreducible
private def mapCoeff {R A:Type*} [Semiring R] [Semiring A] (f :R[X])
  (g:ℕ→R→A) :A[X] :=
 f.sum fun i q=>monomial i (g i q)
private theorem mapCoeff_coeff {R A:Type*} [Semiring R] [Semiring A]
   (f :R[X]) (g:ℕ→R→A) (hg : ∀ i,g i 0=0) (i:ℕ) :
   (mapCoeff f g).coeff i=g i (f.coeff i) := by
 classical
 rw [mapCoeff,Polynomial.sum_def,finsetSum_coeff,Finset.sum_eq_single i]
 · exact coeff_monomial_same _ _
 · exact fun k _ hk=>coeff_monomial_of_ne _ hk.symm
 · intro h
   rw [notMem_support_iff.mp h,hg,monomial_zero_right,coeff_zero]
@[simp] private theorem rev_zero (a :L) (n:ℕ) :rev a n 0=0:= by simp [rev,reflect_zero]
private def paddedEq (J:Input) (a :L) :Dg :=
 mapCoeff J.F fun i f=>mapCoeff f fun _ q=>rev a (J.b+(J.l-i)*J.s) q
private theorem padded_coeff (J:Input) (a :L) (i j:ℕ) :
   ((paddedEq J a).coeff i).coeff j=rev a (J.b+(J.l-i)*J.s) ((J.F.coeff i).coeff j) := by
 rw [paddedEq,mapCoeff_coeff,mapCoeff_coeff]
 · intro k
   exact rev_zero _ _
 · intro k
   simp [mapCoeff]
private theorem pad_bound (J:Input) (i j:ℕ) :
   ((J.F.coeff i).coeff j).natDegree≤J.b+(J.l-i)*J.s := by
 by_cases h: (J.F.coeff i).coeff j=0
 · simp [h]
 have hi:i≤J.l:= by
   rw [← J.Ca.jU]
   exact le_natDegree_of_ne_zero fun hz=>h (by simp [hz])
 have he : (J.l-i)*J.s+i*J.s=J.l*J.s := by rw [← add_mul,zxt hi]
 have :=J.weight i j h
 omega
private theorem padded_repr (J:Input) {a :L} (D:Chart a) (i:ℕ) :
    (embed (paddedEq J a)).coeff i =
      C (x^(J.b+J.l*J.s)*((x^J.s)⁻¹)^i)*((embed J.F).coeff i).map D.changeX.toRingHom:= by
  ext j
  simp only [embed_coeff,coeff_map,coeff_C_mul,padded_coeff]
  by_cases hi:i≤J.l
  · rw [D.CJ _ _ (pad_bound J i j)]
    have he :J.b+J.l*J.s=(J.b+(J.l-i)*J.s)+J.s*i:= by
      rw [Nat.mul_comm J.s i,Nat.add_assoc,← add_mul,zxt hi]
    have hp:x^(J.b+J.l*J.s)*((x^J.s)⁻¹)^i=x^(J.b+(J.l-i)*J.s) := by
      rw [he,pow_add,pow_mul,inv_pow,mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ x_ne)),mul_one]
    rw [hp]
    rfl
  · have hz :J.F.coeff i=0:=coeff_eq_zero_of_natDegree_lt
      (J.Ca.jU.symm ▸ Nat.lt_of_not_ge hi)
    simp [hz]
private theorem padded_data (J:Input) {a :L} (D:Chart a) :
  Irreducible (embed (paddedEq J a))∧(embed (paddedEq J a)).natDegree=J.l:= by
 let u:FX:=(x^J.s)⁻¹
 let v :FX:=x^(J.b+J.l*J.s)
 have hu:u≠0:=inv_ne_zero (pow_ne_zero _ x_ne)
 have hv :v≠0:=pow_ne_zero _ x_ne
 let e :=mapEquiv (mapEquiv D.changeX)
 let t:=scaleY (C u) (C u⁻¹) (by rw [← map_mul,mul_inv_cancel₀ hu,map_one])
 have he :embed (paddedEq J a)=C (C v)*t (e (embed J.F)) := by
  ext i:1
  rw [padded_repr J D,coeff_C_mul,scaleY_coeff]
  change C (v*u^i)*_ = _
  simp only [e,mapEquiv_apply,coeff_map,← map_pow,map_mul]
  ac_rfl
 rw [he]
 refine ⟨(irreducible_isUnit_mul ((hv.isUnit.map (C:FX →+* FX[X])).map C)).mpr
  (((embed_irred J).map e).map t),?_⟩
 rw [natDegree_C_mul (C_ne_zero.mpr hv)]
 change (t (e (embed J.F))).natDegree=J.l
 rw [scaleY_apply,natDegree_comp,natDegree_C_mul (C_ne_zero.mpr hu),natDegree_X,mul_one]
 exact (natDegree_map_eq_of_injective (zTo _ D.changeX.injective) _).trans
  ((embed_degree J.F).trans J.Ca.jU)
theorem rechart (J:Input) {a :L} (D:Chart a) :Nonempty (Rechart J D) := by
  let R:=paddedEq J a
  obtain ⟨hi,hd⟩:=padded_data J D
  change Irreducible (embed R) at hi
  change (embed R).natDegree=J.l at hd
  let:StrongNormalizationMonoid L[X][X] :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let:NormalizedGCDMonoid L[X][X] :=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  let G:=R.primPart
  obtain ⟨c,hc,hfact⟩ : ∃ c:L[X],c≠0∧R=C (C c)*G:= by
    have hfact :=R.eq_C_content_mul_primPart
    have hu:=(hi.isPrimitive (by rw [hd]; have :=J.Ca.two_le; omega))
      ((R.content).map phys) ⟨embed G,by
        simpa only [map_mul,embed,coe_mapRingHom,map_C,phys,G] using congrArg embed hfact⟩
    have hdeg:R.content.natDegree=0:= by
      rw [← natDegree_map_eq_of_injective phys_inj]
      exact natDegree_eq_zero_of_isUnit hu
    have hc:R.content=C (R.content.coeff 0) :=eq_C_of_natDegree_eq_zero hdeg
    exact ⟨_,fun hz=>hu.ne_zero (by rw [hc,hz,C_0,zgY]),hc ▸ hfact⟩
  have hG (i j:ℕ) : ((R.coeff i).coeff j)=c*(G.coeff i).coeff j:= by
    conv_lhs=>rw [hfact,coeff_C_mul,coeff_C_mul]
  have hGdeg (i j:ℕ) (hn: (G.coeff i).coeff j≠0) :
      ((G.coeff i).coeff j).natDegree≤J.b+(J.l-i)*J.s := by
    refine le_trans ?_ (rev_bound a (pad_bound J i j))
    rw [← padded_coeff,show paddedEq J a=R from rfl,hG,natDegree_mul hc hn]
    omega
  let m:=(phys c)⁻¹*x^(J.b+J.l*J.s)
  have hm:m≠0:=mul_ne_zero (inv_ne_zero (phys_ne hc)) (pow_ne_zero _ x_ne)
  have hrepr (i:ℕ) : (embed G).coeff i =
      C (m*((x^J.s)⁻¹)^i)*((embed J.F).coeff i).map D.changeX.toRingHom:= by
    have h:=padded_repr J D i
    change (embed R).coeff i= _ at h
    rw [hfact,map_mul,show embed (C (C c))=C (C (phys c)) by simp [embed,phys],coeff_C_mul] at h
    dsimp only [m]
    rw [mul_assoc,map_mul,mul_assoc,← h,← mul_assoc,← map_mul,
      inv_mul_cancel₀ (phys_ne hc),map_one,one_mul]
  have hir :Irreducible G:=(R.isPrimitive_primPart.irreducible_of_irreducible_map_of_injective
    (φ:=mapRingHom phys) (zTo _ phys_inj)) (by
      have h:=hfact
      apply_fun embed at h
      rw [map_mul,show embed (C (C c))=C (C (phys c)) by simp [embed,phys]] at h
      exact (irreducible_isUnit_mul (((phys_ne hc).isUnit.map (C:FX →+* FX[X])).map C)).mp
        (h ▸ hi))
  refine ⟨⟨G,⟨hir,?_,J.Ca.two_le,J.Ca.tame,?_,?_⟩,?_,m,hm,hrepr⟩⟩
  · exact R.natDegree_primPart.trans ((embed_degree R).symm.trans hd)
  · intro i
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    have hf :=coeff_eq_zero_of_natDegree_lt ((J.Ca.height i).trans_lt hj)
    exact (mul_eq_zero.mp ((hG i j).symm.trans (by rw [padded_coeff,hf,rev_zero]))).resolve_left hc
  · intro hz
    apply J.Ca.moving
    ext i:1
    rw [coeff_seedDerivative,coeff_zero]
    have h:=congrArg derivative (hrepr i)
    rw [derivative_C_mul,derivative_map,embed_coeff,derivative_map,← coeff_seedDerivative,
      hz,coeff_zero,zgY] at h
    have hn:C (m*((x^J.s)⁻¹)^i)≠0 :=
      C_ne_zero.mpr (mul_ne_zero hm (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ x_ne))))
    have he :=(mul_eq_zero.mp h.symm).resolve_left hn
    have he' : ((embed J.F).coeff i).derivative=0 :=
      zTo _ D.changeX.injective (by rw [he,zgY])
    rw [embed_coeff,derivative_map] at he'
    exact zTo _ phys_inj (by rw [he',zgY])
  · intro i j hn
    have hi:i≤J.l:= by
      rw [← J.Ca.jU]
      apply le_natDegree_of_ne_zero
      intro hz
      exact (mul_ne_zero hc hn) ((hG i j).symm.trans (by rw [padded_coeff,hz,coeff_zero,rev_zero]))
    have he : (J.l-i)*J.s+i*J.s=J.l*J.s := by rw [← add_mul,zxt hi]
    have :=hGdeg i j hn
    omega
end
end qWIOgVd
