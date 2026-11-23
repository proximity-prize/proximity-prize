import ProximityPrize.SubmissionLower.T
import ProximityPrize.SubmissionLower.R
import ProximityPrize.SubmissionLower.Zyuvo1c
set_option Elab.async false
open _root_ renaming Field → zrb, Fin.lastCases_castSucc → zwu, Fin.lastCases_last → zTz, Fintype.card_fin → zgY, Ideal → znc, Ideal.Quotient.factor_surjective → zuo, Ideal.Quotient.factorₐ → z5F, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.map_span → zlN, Ideal.quotientMapₐ → zwL, Ideal.span → zye, Ideal.span_union → zuD, Ideal.subset_span → zCn, Module.Finite → zAa, Module.Finite.of_surjective → zIU, Module.finrank → zsE, Module.finrank_eq_zero_of_subsingleton → z6g, MvPolynomial.eval → zY9, MvPolynomial.uniqueFactorizationMonoid → zhK, Nat.card_eq_fintype_card → zey, Nat.eq_zero_of_le_zero → za7, Polynomial.ext → zXJ, Polynomial.natDegree_C → zti, Set.image_insert_eq → z6c, Set.image_singleton → zyk, Set.insert_subset_iff → z61, Set.singleton_subset_iff → zSy, Submodule → zpI, Submodule.span → zLD, Submodule.subset_span → zBO, Subsingleton → zOt
set_option maxHeartbeats 1200000
section
set_option autoImplicit true
namespace atd
noncomputable section
open cu gT pI Polynomial
open qQ (Slice)
instance (s :Slice) :zrb (jY s) := by
  cases s <;> infer_instance
abbrev PlaneQuotient {F:Type} [zrb F] (P Q:lK F) :=
  gk (zye {P,Q})
def BidegreeLE {F:Type} [zrb F] (P:lK F) (a b:ℕ) :Prop :=
  P.degreeOf 0≤a∧P.degreeOf 1≤b
end
end atd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_4
noncomputable section
open MvPolynomial Polynomial
variable {k :Type*} [zrb k]
local notation "Biv" => MvPolynomial (Fin 2) k
private theorem noPrincipalOver {J:znc Biv}
    (hfin:zAa k (Biv ⧸ J))
    {D:Biv} (hD : ¬ IsUnit D) (hle :J≤zye {D}) :False := by
  let:zAa k (Biv ⧸ J) :=hfin
  let:zAa k (Biv ⧸ zye ({D} : Set Biv)) :=
    zIU (z5F k hle).toLinearMap
      (zuo hle)
  have hn: (affineHilbertPolynomial (zye {D})).natDegree=0:= by
    rw [affineHilbertPolynomial_eq_C_finrank,zti]
  by_cases hzero :D =0
  · simp [hzero,natDegree_affineHilbertPolynomial_bot,zey] at hn
  · have hd:=natDegree_affineHilbertPolynomial_span_singleton_add_one hzero
      (mt Ideal.span_singleton_eq_top.mp hD)
    rw [hn] at hd
    simp [zey] at hd
theorem univariate_plane_length_zero (i:k[X] →+* Biv) (A B:k[X])
    (hfin:zAa k (Biv ⧸ zye {i A,i B})) :
    zsE k (Biv ⧸ zye {i A,i B})=0:= by
  let I:znc k[X] :=zye {A,B}
  let J:znc Biv :=zye {i A,i B}
  let d:=Submodule.IsPrincipal.generator I
  have hgen:zye {d} = I:=Ideal.span_singleton_generator I
  have hJ:J=zye {i d} := by
    have h:I.map i=J:= by simp [I,J,zlN,z6c,zyk]
    rw [← h,← hgen,zlN,zyk]
  have hu:IsUnit (i d) := by
    by_contra hn
    exact noPrincipalOver (J:=J) hfin hn (le_of_eq hJ)
  have htop:J = ⊤ := hJ.trans (Ideal.span_singleton_eq_top.mpr hu)
  let:zOt (Biv ⧸ J) :=Ideal.Quotient.subsingleton_iff.mpr htop
  change zsE k (Biv ⧸ J)=0
  exact z6g k _
theorem planeBezout (F G:Biv) (u:ℕ)
    (hfin:zAa k (Biv ⧸ zye {F,G}))
    (hF:F.totalDegree≤u) (hG:G.totalDegree≤u) :
    zsE k (Biv ⧸ zye {F,G})≤u^2 := by
  let J:znc Biv :=zye {F,G}
  let I:znc Biv :=zye {F}
  change zsE k (Biv ⧸ J)≤_
  by_cases htop:J = ⊤
  · let:zOt (Biv ⧸ J) :=Ideal.Quotient.subsingleton_iff.mpr htop
    rw [z6g]
    exact Nat.zero_le _
  let:zAa k (Biv ⧸ J) :=hfin
  have hFJ:F∈J:=zCn (by simp)
  have hGJ:G∈J:=zCn (by simp)
  have hIle :I≤J:=(Ideal.span_singleton_le_iff_mem J).mpr hFJ
  have hI:I ≠ ⊤ := fun he=>htop (top_le_iff.mp (he ▸ hIle))
  have hFne :F≠0:= by
    intro h
    have hGun : ¬ IsUnit G:= by
      intro hu
      exact htop (Ideal.eq_top_of_isUnit_mem J hGJ hu)
    apply noPrincipalOver (J:=J) hfin hGun
    rw [show J=Ideal.span ({0,G} : Set Biv) by simp [J,h],
      Ideal.span_pair_comm,Ideal.span_pair_zero]
  let:UniqueFactorizationMonoid k :=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid Biv :=zhK (Fin 2)
  have hprime : ∀ {D:Biv},D ∣F→D ∣G → ¬ Prime D:= by
    intro D hDF hDG hD
    apply noPrincipalOver (J:=J) hfin hD.not_isUnit
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr hDF
    · exact Ideal.mem_span_singleton.mpr hDG
  have hreg:IsLeftRegular (zVv I G) := by
    intro x y he
    obtain ⟨x,rfl⟩:=zld x
    obtain ⟨y,rfl⟩:=zld y
    let q:Biv →+* Biv ⧸ I:=zVv I
    have hmul :q ((x - y)*G)=0:= by
      rw [mul_comm,map_mul,map_sub,mul_sub]
      exact sub_eq_zero.mpr he
    have hd:F∣(x - y)*G :=
      Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem (I:=I)).mp hmul)
    have hdiv :F∣x - y :=
      UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors hFne @hprime hd
    have hmem:x - y∈I:=Ideal.mem_span_singleton.mpr hdiv
    have hz :q (x - y)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_sub,sub_eq_zero] at hz
    exact hz
  have hd: (affineHilbertPolynomial I).natDegree=1 := by
    have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one hFne hI
    rw [zey,zgY] at h
    change (affineHilbertPolynomial (zye {F})).natDegree=1
    omega
  have hl: (affineHilbertPolynomial I).leadingCoeff=(F.totalDegree :ℚ) := by
    have he :=affineDegree_span_singleton hFne
    change affineDegree I= _ at he
    simpa [affineDegree,hd] using he
  have hJ:I ⊔ zye {G} = J:= by
    change zye ({F} : Set Biv) ⊔ zye {G} = zye {F,G}
    rw [← zuD]
    congr 1
  have h:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg hG).2
  rw [hJ,hd,hl,affineHilbertPolynomial_eq_C_finrank] at h
  have h' : (zsE k (Biv ⧸ J) :ℚ) ≤
      (u:ℚ)*(F.totalDegree :ℚ) := by simpa using h
  rw [pow_two]
  have hF' : (F.totalDegree :ℚ)≤(u:ℚ) := by exact_mod_cast hF
  have h'' := h'.trans (mul_le_mul_of_nonneg_left hF' (Nat.cast_nonneg u))
  exact_mod_cast h''
end
end K1_14_3_2_4
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace atd
noncomputable section
open MvPolynomial Polynomial
open scoped BigOperators
private abbrev aer (F:Type) [zrb F] :=MvPolynomial (Option (Fin 1)) F
private theorem principal_finite_is_unit {F:Type} [zrb F] {D:aer F}
    (hfin:zAa F (aer F ⧸ zye {D})) :IsUnit D:= by
  let _:=hfin
  have hz : (affineHilbertPolynomial (zye {D})).natDegree=0:= by
    rw [affineHilbertPolynomial_eq_C_finrank,zti]
  by_contra hu
  by_cases hD:D =0
  · simp [hD,natDegree_affineHilbertPolynomial_bot] at hz
  · have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one hD
      (mt Ideal.span_singleton_eq_top.mp hu)
    simp [hz] at h
private theorem regular_plane_pair {F:Type} [zrb F] {A B:aer F}
    (hfin:zAa F (aer F ⧸ zye {A,B}))
    (hproper :zye ({A,B} : Set (aer F)) ≠ ⊤) :
    A≠0∧IsLeftRegular (zVv (zye {A}) B) := by
  let J:znc (aer F) :=zye {A,B}
  let I:znc (aer F) :=zye {A}
  let _:=hfin
  have hAu:A≠0:= by
    intro hz
    have he :J=zye {B} := by
      simp [J,hz,Ideal.span_pair_comm]
    have hf :zAa F (aer F ⧸ zye {B}) := by
      rw [← he]
      exact hfin
    exact hproper (he.trans (Ideal.span_singleton_eq_top.mpr (principal_finite_is_unit hf)))
  let:UniqueFactorizationMonoid F:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid (aer F) :=
    zhK (Option (Fin 1))
  have hprime : ∀ {D:aer F},D ∣A→D ∣B → ¬ Prime D:= by
    intro D ha hb hD
    have hle :J≤zye {D} := Ideal.span_le.mpr (by
      simp only [z61,zSy]
      exact ⟨Ideal.mem_span_singleton.mpr ha,Ideal.mem_span_singleton.mpr hb⟩)
    have hfin' := zIU (z5F F hle).toLinearMap
      (zuo hle)
    exact hD.not_isUnit (principal_finite_is_unit hfin')
  refine ⟨hAu,?_⟩
  intro x y hxy
  obtain ⟨x,rfl⟩:=zld x
  obtain ⟨y,rfl⟩:=zld y
  let q:=zVv I
  have hd:A∣(x-y)*B:= by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((x-y)*B)=0
    rw [mul_comm,map_mul,map_sub,mul_sub]
    exact sub_eq_zero.mpr hxy
  have he :=UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors hAu @hprime hd
  change q x=q y
  rw [← sub_eq_zero,← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr he)
private theorem box_length {F:Type} [zrb F] {A B:aer F} {u b d:ℕ}
    (hu:0< u) (hd:0<d) (hfin:zAa F (aer F ⧸ zye {A,B}))
    (hA:A∈restrictBidegree (Fin 1) F u b) (hB:B∈restrictBidegree (Fin 1) F u d) :
    zsE F (aer F ⧸ zye {A,B})≤u*(b+d) := by
  let I:znc (aer F) :=zye {A}
  let J:znc (aer F) :=zye {A,B}
  by_cases hJ:J = ⊤
  · let _:zOt (aer F ⧸ J) :=Ideal.Quotient.subsingleton_iff.mpr hJ
    change zsE F (aer F ⧸ J)≤_
    rw [z6g]
    exact Nat.zero_le _
  obtain ⟨hAz,hreg⟩:=regular_plane_pair hfin hJ
  have hIJ:I≤J:=Ideal.span_mono (by simp)
  have hI:I ≠ ⊤ := fun he=>hJ (top_le_iff.mp (he ▸ hIJ))
  let e :=bidegreeMap (Fin 1) F u d
  let h:=bidegreeLift B hB
  have he :Function.Surjective e.toRingHom:=bidegreeMap_surjective hu hd
  have hh:e h=B:=bidegreeMap_bidegreeLift B hB
  let K:=I.comap e.toRingHom
  let D:=K ⊔ zye {h}
  have hDmap :D.map e.toRingHom=J:= by
    change (I.comap e.toRingHom ⊔ zye {h}).map e.toRingHom=J
    rw [Ideal.map_sup,Ideal.map_comap_of_surjective _ he,zlN,zyk,
      show e.toRingHom h=B from hh,← zuD]
    congr 1
  have hD:J.comap e.toRingHom=D:= by
    rw [← hDmap,Ideal.comap_map_of_surjective _ he,sup_eq_left]
    exact (Ideal.comap_mono bot_le :Ideal.comap e.toRingHom ⊥ ≤ K).trans le_sup_left
  let q:=zwL J e hD.ge
  let q' := zwL I e (le_rfl :K≤I.comap e.toRingHom)
  let eq :=AlgEquiv.ofBijective q ⟨Ideal.quotientMap_injective' (H :=hD.ge) hD.le,
    Ideal.quotientMap_surjective (H :=hD.ge) he⟩
  let _:=hfin
  let _:=zIU eq.symm.toLinearMap eq.symm.surjective
  have hK: (affineHilbertPolynomial K).natDegree=1 := by
    have ht:=natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton hu hd hAz hI
    rw [← show ((zye {A}).comap (bidegreeMap (Fin 1) F u d))=K from rfl]
    simpa only [zey,zgY] using ht
  have hL: (affineHilbertPolynomial K).leadingCoeff≤(u*(b+d) :ℕ) := by
    have ht:=affineDegree_comap_bidegreeMap_span_singleton_le hu hd hAz hA
    rw [show ((zye {A}).comap (bidegreeMap (Fin 1) F u d))=K from rfl,affineDegree,hK]
      at ht
    simpa [Nat.mul_add,Nat.mul_comm,add_comm] using ht
  have hreg' : IsLeftRegular (zVv K h) := by
    intro x y hxy
    apply (Ideal.quotientMap_injective (I:=I) (f :=e.toRingHom))
    change q' x=q' y
    apply hreg
    exact (by
      have heq :=congrArg q' hxy
      simpa only [map_mul,q',Ideal.quotient_map_mkₐ,Ideal.Quotient.mkₐ_eq_mk,hh] using heq)
  have ht:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg'
    (totalDegree_bidegreeLift_le_one B hB)).2
  change (affineHilbertPolynomial D).coeff ((affineHilbertPolynomial K).natDegree - 1)≤_ at ht
  rw [affineHilbertPolynomial_eq_C_finrank,hK] at ht
  have hdim:=eq.toLinearEquiv.finrank_eq
  have hr : (zsE F (aer F ⧸ J) :ℚ)≤(u*(b+d) :ℕ) := by
    rw [← hdim]
    exact (by simpa using ht:_≤(affineHilbertPolynomial K).leadingCoeff).trans hL
  exact_mod_cast hr
private theorem one_variable {F:Type} [zrb F] {A:lK F} (hA:A.degreeOf 0≤0) :
    ∃ f :F[X],Polynomial.aeval (MvPolynomial.X 1 :lK F) f=A:= by
  classical
  refine ⟨∑ m∈A.support,Polynomial.monomial (m 1) (A.coeff m),?_⟩
  conv_rhs=>rw [MvPolynomial.as_sum A]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hz :m 0=0:=za7 (MvPolynomial.degreeOf_le_iff.mp hA m hm)
  have he :m=Finsupp.single 1 (m 1) := by
    ext i
    fin_cases i
    · simpa using hz
    · simp
  rw [Polynomial.aeval_monomial,MvPolynomial.algebraMap_eq,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial,mul_one]
  exact congrArg (fun n=>MvPolynomial.monomial n (A.coeff m)) he.symm
theorem rectangle_length {F:Type} [zrb F] (A B:lK F) (u b d:ℕ)
    (hd:0<d) (hfin:zAa F (PlaneQuotient A B))
    (hA:BidegreeLE A u b) (hB:BidegreeLE B u d) :
    zsE F (PlaneQuotient A B)≤u*(b+d) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · obtain ⟨a,ha⟩:=one_variable hA.1
    obtain ⟨b',hb⟩:=one_variable hB.1
    let g:F[X] →+* lK F:=(Polynomial.aeval (MvPolynomial.X 1 :lK F)).toRingHom
    change g a=A at ha
    change g b' = B at hb
    rw [← ha,← hb] at hfin ⊢
    simp only [K1_14_3_2_4.univariate_plane_length_zero g a b' hfin,Nat.zero_mul,le_refl]
  let ρ:=MvPolynomial.renameEquiv F (finSuccEquiv 1)
  have hbox {P:lK F} {w:ℕ} (hP:BidegreeLE P u w) :
      ρ P∈restrictBidegree (Fin 1) F u w:= by
    have h0: (ρ P).degreeOf none≤u:= by
      simpa only [ρ,renameEquiv_apply,← show finSuccEquiv 1 0=none from rfl,
        degreeOf_rename_of_injective (finSuccEquiv 1).injective] using hP.1
    have h1 : (ρ P).degreeOf (some 0)≤w:= by
      simpa only [ρ,renameEquiv_apply,← show finSuccEquiv 1 1=some 0 from rfl,
        degreeOf_rename_of_injective (finSuccEquiv 1).injective] using hP.2
    refine mem_restrictBidegree.mpr fun m hm=>⟨degreeOf_le_iff.mp h0 m hm,?_⟩
    simpa [Finsupp.degree_eq_sum,Fin.sum_univ_one] using degreeOf_le_iff.mp h1 m hm
  let q:=Ideal.quotientEquivAlg (zye ({A,B} : Set (lK F))) ρ (J :=
    zye {ρ A,ρ B}) (by
      simp [zlN,z6c,zyk])
  let _:=hfin
  have hf :=zIU q.toLinearMap q.surjective
  have hq:=q.toLinearEquiv.finrank_eq
  exact hq.trans_le (box_length hu hd hf (hbox hA) (hbox hB))
end
end atd
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qhmtljc
noncomputable section
open Finset MvPolynomial
open P6 (K)
open P6_7_1 q3rjQGe qINqgHe
open cu (L FX Jet)
open DP (Source qC U4 complete Z7)
open UniqueFactorizationMonoid
open private avoid from ProximityPrize.SubmissionLower.Zr07w3a
private def coefficients (V:zpI L Source) :Set qC :=
  {f | ∃ Q∈V,∃ j i a,f=Bg Q j i a}
private theorem missing_divisor (V:zpI L Source)
    (hV : ∀ {d Q},d≠0→Sl d*Q∈V→Q∈V)
    {A:qC} (hA:A∈coefficients V) (hne :A≠0)
    {d:qC} (hd:Irreducible d) : ∃ B∈coefficients V,¬ d∣B:= by
  classical
  by_contra! h
  obtain ⟨Q,hQ,j,i,a,rfl⟩:=hA
  have hex : ∃ n,∃ T∈V,Bg T j i a≠0∧(Bg T j i a).totalDegree=n :=
    ⟨_,Q,hQ,hne,rfl⟩
  obtain ⟨T,hT,hnz,hdeg⟩:=Nat.find_spec hex
  have hdiv :Sl d∣T:=(seedC_dvd d T).mpr fun j' i' a' =>
    h _ ⟨T,hT,j',i',a',rfl⟩
  obtain ⟨R,hR⟩:=hdiv
  have hr :R∈V:=hV hd.ne_zero (hR ▸ hT)
  rw [hR,seedCoeff_mul] at hnz hdeg
  have hrz :Bg R j i a≠0:=right_ne_zero_of_mul hnz
  have hd' : 0<d.totalDegree := by
    by_contra! hn
    have hz :=za7 hn
    have he :=totalDegree_eq_zero_iff_eq_C.mp hz
    have hnz :d.coeff 0≠0:= fun hc=>hd.ne_zero (he.trans (by simp [hc]))
    apply hd.not_isUnit
    rw [he]
    exact (isUnit_iff_ne_zero.mpr hnz).map MvPolynomial.C
  rw [totalDegree_mul_of_isDomain hd.ne_zero hrz] at hdeg
  exact Nat.find_min hex (show (Bg R j i a).totalDegree<Nat.find hex by omega)
    ⟨R,hr,hrz,rfl⟩
private theorem choose_pair (V:zpI L Source)
    (hV : ∀ {d Q},d≠0→Sl d*Q∈V→Q∈V)
    {A:qC} (hA:A∈coefficients V) (hne :A≠0) :
    ∃ B∈zLD L (coefficients V),∀ d,Prime d→d∣A → ¬ d∣B:= by
  classical
  let:UniqueFactorizationMonoid L:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid qC:=zhK (Fin 2)
  let:StrongNormalizationMonoid qC:=UniqueFactorizationMonoid.strongNormalizationMonoid
  let I (d:qC) :=(zye ({d} : Set qC)).restrictScalars L
  have hh (d B:qC) :B∈I d↔d∣B:=Ideal.mem_span_singleton
  obtain ⟨B,hB,havoid⟩:=avoid (zLD L (coefficients V))
    (normalizedFactors A).toFinset I (by
      intro d hd
      obtain ⟨b,hb,hm⟩:=missing_divisor V hV hA hne
        (irreducible_of_normalized_factor d (Multiset.mem_toFinset.mp hd))
      exact ⟨b,zBO hb,fun hz=>hm ((hh d b).mp hz)⟩)
  refine ⟨B,hB,fun d hd hda hdb => ?_⟩
  obtain ⟨e,he,hae⟩:=exists_mem_normalizedFactors_of_dvd hne hd.irreducible hda
  exact havoid e (Multiset.mem_toFinset.mpr he) ((hh e B).mpr (hae.dvd_iff_dvd_left.mp hdb))
private theorem intersection_finite {A B:qC} (hA:A≠0)
    (hn : ¬ IsUnit A) (hAB : ∀ d,Prime d→d∣A → ¬ d∣B) :
    zAa L (qC ⧸ zye {A,B}) := by
  let:UniqueFactorizationMonoid L:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid qC:=zhK (Fin 2)
  let J:znc qC:=zye {A}
  have hJ:J ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hn
  have hd:=natDegree_affineHilbertPolynomial_span_singleton_add_one hA hJ
  have hd' : (affineHilbertPolynomial J).natDegree=1 := by
    rw [zey,zgY] at hd
    change (affineHilbertPolynomial J).natDegree+1=2 at hd
    omega
  let q:=zVv J
  have hr :IsLeftRegular (q B) := by
    intro x y he
    obtain ⟨x,rfl⟩:=zld x
    obtain ⟨y,rfl⟩:=zld y
    have hz :q ((x-y)*B)=0:= by
      rw [mul_comm,map_mul,map_sub,mul_sub]
      exact sub_eq_zero.mpr he
    have hdiv :A∣(x-y)*B :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have h:=dvd_of_dvd_mul_left_of_no_prime_factors hA
      (fun {d} hda hdb hd=>hAB d hd hda hdb) hdiv
    change q x=q y
    rw [← sub_eq_zero,← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  have hh:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hr le_rfl).1
  rw [hd',Nat.sub_self,← zuD] at hh
  exact moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero (za7 hh)
private theorem count {V:zpI L Source} {C:zpI L qC} (S:Finset (Fin 2→L))
    (hV : ∀ {d Q},d≠0→Sl d*Q∈V→Q∈V)
    (hn : ∃ Q∈V,Q≠0)
    (hC : ∀ Q∈V,∀ j i a,Bg Q j i a∈C)
    (hz : ∀ v∈S,∀ Q∈V,∀ j i a,zY9 v (Bg Q j i a)=0)
    {N :ℕ} (hN : ∀ A∈C,∀ B∈C,zAa L (qC ⧸ zye {A,B}) →
      zsE L (qC ⧸ zye {A,B})≤N) :S.card≤N := by
  classical
  by_cases hS:S.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨Q,hQ,hQn⟩:=hn
  have hex : ∃ j i a,Bg Q j i a≠0:= by
    by_contra! hh
    exact hQn (zXJ fun j=>zXJ fun i=>zXJ fun a=> by
      simpa only [Bg,Polynomial.coeff_zero] using hh j i a)
  obtain ⟨j,i,a,ha⟩:=hex
  let A:=Bg Q j i a
  obtain ⟨B,hB,hAB⟩:=choose_pair V hV (A:=A) ⟨Q,hQ,j,i,a,rfl⟩ ha
  have hCA:zLD L (coefficients V)≤C:=Submodule.span_le.mpr (by
    rintro _ ⟨T,hT,j',i',a',rfl⟩
    exact hC T hT j' i' a')
  have hzeros (v) (hv :v∈S) :
      zY9 v A=0∧zY9 v B=0:= by
    have hker :zLD L (coefficients V)≤LinearMap.ker (MvPolynomial.aeval v).toLinearMap :=
      Submodule.span_le.mpr (by
        rintro _ ⟨T,hT,j',i',a',rfl⟩
        exact LinearMap.mem_ker.mpr (hz v hv T hT j' i' a'))
    exact ⟨hz v hv Q hQ j i a,LinearMap.mem_ker.mp (hker hB)⟩
  obtain ⟨v,hv⟩:=hS
  have hnA : ¬ IsUnit A:= fun hu=>(hu.map (zY9 v)).ne_zero (hzeros v hv).1
  let J:znc qC:=zye {A,B}
  let hf :zAa L (qC ⧸ J) :=intersection_finite ha hnA hAB
  have hs : (S:Set (Fin 2→L))⊆zeroLocus L J:= by
    intro v hv
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    rcases hzeros v hv with ⟨ha',hb'⟩
    exact Ideal.span_le.mpr (by
      simp only [z61,zSy]
      exact ⟨RingHom.mem_ker.mpr ha',RingHom.mem_ker.mpr hb'⟩)
  have card:=Set.ncard_le_ncard hs (finite_zeroLocus_of_finite_quotient J)
  rw [Set.ncard_coe_finset] at card
  exact card.trans ((ncard_zeroLocus_le_finrank_quotient J).trans (hN A (hC Q hQ j i a) B (hCA hB) hf))
private theorem total_count (A B:qC) (u:ℕ)
    (hA:A∈restrictTotalDegree (Fin 2) L u) (hB:B∈restrictTotalDegree (Fin 2) L u)
    (hf :zAa L (qC ⧸ zye {A,B})) :
    zsE L (qC ⧸ zye {A,B})≤u^2 :=
  K1_14_3_2_4.planeBezout A B u hf
    ((mem_restrictTotalDegree (Fin 2) u A).mp hA) ((mem_restrictTotalDegree (Fin 2) u B).mp hB)
private theorem bVY (A B:qC) {u:ℕ} (hu:0< u)
    (hA:A∈restrictDegree (Fin 2) L u) (hB:B∈restrictDegree (Fin 2) L u)
    (hf :zAa L (qC ⧸ zye {A,B})) :
    zsE L (qC ⧸ zye {A,B})≤2*u*u :=
  (atd.rectangle_length A B u u u hu hf
    ⟨(mem_restrictDegree_iff_degreeOf_le A u).mp hA 0,(mem_restrictDegree_iff_degreeOf_le A u).mp hA 1⟩
    ⟨(mem_restrictDegree_iff_degreeOf_le B u).mp hB 0,(mem_restrictDegree_iff_degreeOf_le B u).mp hB 1⟩).trans_eq
    (by ring)
open scoped Classical BigOperators
private def Ju (x :Input) (B:zpI FX Jet) :Finset K :=
  x.Γ.filter fun γ=>(∃ g∈B,g≠0) ∧
    ∀ g∈B,seedSpecialize g (x.M.label γ)=0
private theorem source_bound (x :Input) (V:zpI L Source) (C:zpI L qC)
    (hV : ∀ {d Q},d≠0→Sl d*Q∈V→Q∈V)
    (hC : ∀ Q∈V,∀ j i a,Bg Q j i a∈C)
    {N :ℕ} (hN : ∀ A∈C,∀ B∈C,zAa L (qC ⧸ zye {A,B}) →
      zsE L (qC ⧸ zye {A,B})≤N) :
    (Ju x (zLD FX (U4 '' (V:Set Source)))).card≤N := by
  classical
  let B:=zLD FX (U4 '' (V:Set Source))
  let T:=Ju x B
  change T.card≤N
  by_cases hT:T.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hT]
  obtain ⟨γ,hγ⟩:=hT
  obtain ⟨g,hg,hg0⟩:=(mem_filter.mp hγ).2.1
  have hn : ∃ Q∈V,Q≠0:= by
    by_contra! h
    have hB:B ≤ ⊥ := Submodule.span_le.mpr (by
      rintro _ ⟨Q,hQ,rfl⟩
      simp [h Q hQ])
    exact hg0 ((Submodule.mem_bot FX).mp (hB hg))
  let label (a :K) :=Z7 (x.M.label a)
  have hi:Function.Injective label := by
    intro a b hab
    apply sub_left_inj.mp
    apply (algebraMap K L).injective
    exact congrFun hab 0
  rw [← card_image_of_injective T hi]
  apply count (V:=V) (C:=C) (T.image label) hV hn hC _ hN
  intro v hv Q hQ j i a
  obtain ⟨δ,hδ,rfl⟩:=mem_image.mp hv
  exact physical_seed_zero ((mem_filter.mp hδ).2.2 _
    (zBO ⟨Q,hQ,rfl⟩)) j i a
private theorem free_bound {x :Input} (P:Poles x) (i:Free) :
    (Ju x (aV P i.castSucc)).card≤(stage i).free.U^2 := by
  rw [free_bank]
  let s :=(stage i).free
  let W:=cutoff s
  change (Ju x (zLD FX
    (U4 '' (complete P.crt x.word s W:Set Source)))).card≤ s.U^2
  exact source_bound x _ (restrictTotalDegree (Fin 2) L s.U)
    (fun hd hQ=>complete_cancel P.crt x.word s W hd hQ)
    (fun Q hQ j i a=>(mem_restrictTotalDegree (Fin 2) s.U _).mpr (ambient_caps hQ.1.1 j i a))
    (fun A hA B hB hf=>total_count A B s.U hA hB hf)
private theorem terminal_bound {x :Input} (P:Poles x) :
    (Ju x (aV P termTrial)).card≤2*terminal.z*terminal.t:= by
  rw [terminal_bank]
  change (Ju x (zLD FX
    (U4 '' (rectComplete P terminal (rectCut terminal) :Set Source)))).card ≤
    2*terminal.z*terminal.z
  refine source_bound x _ (restrictDegree (Fin 2) L terminal.z) (fun hd hQ => ?_) ?_
    (fun A hA B hB hf=>bVY A B (by decide) hA hB hf)
  · exact ⟨complete_cancel P.crt x.word terminal.box (rectCut terminal) hd hQ.1,
      box_cancel hd hQ.2⟩
  · intro Q hQ j i a
    apply (mem_restrictDegree_iff_degreeOf_le _ _).mpr
    intro k
    have h:=box_caps hQ.2 j i a k
    fin_cases k <;> exact h
private def bw (t:Trial) :ℕ :=
  Fin.lastCases (2*terminal.z*terminal.t) (fun i:Free=>(stage i).free.U^2) t
private theorem fee_sum: (∑ t:Trial,bw t)=bankFee := by
  rw [Fin.sum_univ_castSucc]
  simp only [bw,zwu,zTz,Fin.sum_univ_succ,
    Fin.sum_univ_zero,add_zero]
  change (1740^2+(1051^2+(2098^2 + 3668^2)))+2*60836*60836=0x1ba81a4dd
  decide
theorem proof :q3rjQGe.c2 := by
  classical
  intro x P
  let T (t:Trial) :=Ju x (aV P t)
  have hsub:bankBook P⊆univ.biUnion T:= by
    intro γ hγ
    obtain ⟨hΓ,t,hn,hz⟩:=mem_filter.mp hγ
    exact mem_biUnion.mpr ⟨t,mem_univ _,mem_filter.mpr ⟨hΓ,hn,hz⟩⟩
  have ht (t:Trial) : (T t).card≤bw t:= by
    refine Fin.lastCases ?_ (fun i:Free => ?_) t
    · simpa only [T,bw,zTz] using terminal_bound P
    · simpa only [T,bw,zwu] using free_bound P i
  exact (card_le_card hsub).trans (card_biUnion_le.trans ((sum_le_sum fun t _=>ht t).trans_eq fee_sum))
end
end qhmtljc
end
