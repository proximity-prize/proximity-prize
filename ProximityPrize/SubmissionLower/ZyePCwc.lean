import ProximityPrize.SubmissionLower.ZiWgK3c
import ProximityPrize.SubmissionLower.ZIrsLvc
set_option Elab.async false
open _root_ renaming Field → zrb, Finsupp.single → zhf, Finsupp.sum_single_index → zHG, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.span → zye, Module.Finite → zAa, Module.Finite.equiv → zZc, Module.finrank → zsE, MvPolynomial.X → z9v, MvPolynomial.map_C → zpw, Nat.pos_of_ne_zero → zOl, Polynomial → zM1, Polynomial.C → z1z, Polynomial.mapRingHom → zhd
section
set_option autoImplicit true
namespace qOdMfWd
noncomputable section
open MvPolynomial aR dN agL
open lB (SZ amo)
open P6_6_7 (genericOrder)
open P6_6_7_3 (order_mem agr)
open private hasse_one from ProximityPrize.SubmissionLower.ZiWgK3c
private abbrev tu:=MvPolynomial (Fin 3) GeoField
private def u7:GeoJets ≃ₐ[GeoField] zM1 tu :=
  (renameEquiv GeoField finSuccEquivLast).trans (optionEquivLeft GeoField (Fin 3))
private def low:tu →+* GeoJets :=u7.symm.toRingHom.comp z1z
private theorem plane_C (c:GeoField) :u7 (C c)=z1z (C c) := by
  simp [u7,optionEquivLeft_C]
private theorem plane_X_low (i:Fin 3) :
    u7 (z9v i.castSucc)=z1z (z9v i) := by
  simp [u7]
private theorem plane_X_top:u7 (z9v 3)=Polynomial.X:= by
  simp [u7,show finSuccEquivLast (3:Fin 4)=none from finSuccEquivLast_last]
private theorem eLN (P:GeoJets) : (u7 P).natDegree=P.degreeOf 3:= by
  change (optionEquivLeft _ _ (rename finSuccEquivLast P)).natDegree=P.degreeOf (Fin.last 3)
  rw [natDegree_optionEquivLeft]
  simpa only [finSuccEquivLast_last] using
    degreeOf_rename_of_injective (p:=P) finSuccEquivLast.injective (Fin.last 3)
private theorem plane_deriv (P:GeoJets) :
    u7 (pderiv 3 P)=(u7 P).derivative := by
  change optionEquivLeft _ _ (rename finSuccEquivLast (pderiv (Fin.last 3) P))= _
  rw [← pderiv_rename finSuccEquivLast.injective,finSuccEquivLast_last,
    optionEquivLeft_pderiv_none]
  rfl
private theorem degree_generic (R:af 4) :
    (u7 (bC R)).natDegree=(shape R).t:= by
  rw [eLN]
  change (MvPolynomial.map j8 R).degreeOf 3=R.degreeOf 3
  rw [degreeOf_def,degreeOf_def,degrees_map_of_injective R SZ]
private theorem axis_injective :zq4 (fun _:Unit=>(3:Fin 4)) :=
  fun _ _ _=>Subsingleton.elim _ _
private def axisTaylor :GeoJets →+* zM1 GeoJets :=
  (uniqueAlgEquiv GeoJets Unit).toRingHom.comp
    ((killCompl axis_injective).toRingHom.comp Uz)
private theorem axisTaylor_coeff (P:GeoJets) (n:ℕ) :
    (axisTaylor P).coeff n=BV (zhf 3 n) P:= by
  change ((uniqueAlgEquiv GeoJets Unit) (killCompl axis_injective (Uz P))).coeff n= _
  rw [coeff_uniqueAlgEquiv,coeff_killCompl,Finsupp.mapDomain_single,taylor_coeff]
private theorem axisTaylor_eq (P:GeoJets) :
    axisTaylor P=((u7 P).map low).taylor (z9v 3) := by
  classical
  let v :GeoJets :=z9v 3
  let t:GeoJets →+* zM1 GeoJets :=
    (Polynomial.compRingHom (Polynomial.X+Polynomial.C v)).comp
      ((zhd low).comp u7.toRingHom)
  change axisTaylor P=t P
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext ?_ ?_) P
  · intro c
    have hl:low (C c)=C c:= by
      apply u7.injective
      simp [low,plane_C]
    simp [axisTaylor,Uz,t,plane_C,hl]
  · intro i
    change (uniqueAlgEquiv GeoJets Unit) (killCompl axis_injective
      (Uz (z9v i)))=((u7 (z9v i)).map low).taylor v
    have hX:Uz (A:=GeoField) (z9v i) =
        C (z9v i)+MvPolynomial.X i:=eval₂Hom_X' _ _ _
    have hC (x :GeoJets) : (uniqueAlgEquiv GeoJets Unit) (C x)=z1z x := by simp
    rw [hX,map_add,killCompl_C,map_add,hC]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change _=((u7 (z9v 3)).map low).taylor v
      have hm: (3:Fin 4)∈Set.range (fun _:Unit=>(3:Fin 4)) :=⟨(),rfl⟩
      rw [show Fin.last 3=(3:Fin 4) by rfl,killCompl,aeval_X,dite_eq_left hm,
        uniqueAlgEquiv_apply,eval₂_X,plane_X_top,Polynomial.map_X,Polynomial.taylor_X]
      exact add_comm _ _
    · have hn:j.castSucc≠(3:Fin 4) :=Fin.castSucc_ne_last j
      have hm:j.castSucc∉Set.range (fun _:Unit=>(3:Fin 4)) := by
        simpa only [Set.range_const,Set.mem_singleton_iff] using hn
      have hl:low (z9v j)=z9v j.castSucc:= by
        apply u7.injective
        simp [low,plane_X_low]
      rw [killCompl,aeval_X,dite_eq_right hm,map_zero,add_zero,plane_X_low,
        Polynomial.map_C,hl,Polynomial.taylor_C]
private def project (z :znc GeoJets) :GeoJets →+* zM1 (GeoJets ⧸ z) :=
  (zhd ((zVv z).comp low)).comp u7.toRingHom
private abbrev extended (z :znc GeoJets) :=RingHom.ker (project z)
private theorem extended_le (z :znc GeoJets) :extended z≤z := by
  intro P hP
  have h:=RingHom.mem_ker.mp hP
  have hp:u7 P∈z.comap u7.symm.toRingHom:= by
    apply Ideal.polynomial_mem_ideal_of_coeff_mem_ideal
    intro n
    change low ((u7 P).coeff n)∈z
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa [project] using congrArg (fun q:zM1 (GeoJets ⧸ z)=>q.coeff n) h)
  change u7.symm (u7 P)∈z at hp
  rwa [AlgEquiv.symm_apply_apply] at hp
private theorem extended_deriv {z :znc GeoJets} {P:GeoJets} (h:P∈extended z) :
    pderiv 3 P∈extended z := by
  apply RingHom.mem_ker.mpr
  have h0: (u7 P).map ((zVv z).comp low)=0:=RingHom.mem_ker.mp h
  change (u7 (pderiv 3 P)).map ((zVv z).comp low)=0
  rw [plane_deriv,← Polynomial.derivative_map,h0,Polynomial.derivative_zero]
private theorem extended_of_low {z :znc GeoJets} {P:GeoJets}
    (hd: (u7 P).natDegree=0) (h:P∈z) :P∈extended z := by
  apply RingHom.mem_ker.mpr
  change (u7 P).map ((zVv z).comp low)=0
  have hh:=Polynomial.eq_C_of_natDegree_eq_zero hd
  conv_lhs=>rw [hh]
  rw [Polynomial.map_C,RingHom.comp_apply]
  have he :low ((u7 P).coeff 0)=P:= by
    change u7.symm (z1z ((u7 P).coeff 0))=P
    rw [← hh,AlgEquiv.symm_apply_apply]
  rw [he,Ideal.Quotient.eq_zero_iff_mem.mpr h,map_zero]
private theorem extended_of_order {R:af 4} {z :znc GeoJets}
    (h: (shape R).t<genericOrder R z) :bC R∈extended z := by
  let q:=zVv z
  let P:=bC R
  have ht: (axisTaylor P).natDegree≤(shape R).t:= by
    rw [axisTaylor_eq,Polynomial.natDegree_taylor,← degree_generic R]
    exact Polynomial.natDegree_map_le
  have hz : (axisTaylor P).map q=0:= by
    ext n
    rw [Polynomial.coeff_map,Polynomial.coeff_zero,axisTaylor_coeff]
    by_cases hn:n≤(shape R).t
    · apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have ho:EY (zhf (3:Fin 4) n)=n:= by
        simp [EY,zHG]
      have hm:EY (zhf (3:Fin 4) n)<genericOrder R z := by
        rw [ho]
        exact hn.trans_lt h
      simpa only [P,bC,bft] using order_mem R z hm
    · rw [← axisTaylor_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt
        (ht.trans_lt (Nat.lt_of_not_ge hn)),map_zero]
  rw [axisTaylor_eq,Polynomial.map_taylor,Polynomial.map_map,Polynomial.taylor_eq_zero] at hz
  exact RingHom.mem_ker.mpr hz
private theorem btv {R:af 4} (hR:R≠0) (i:Fin 4)
    (hi:0<R.degreeOf i) (hb:R.totalDegree<K1.p) : ¬ R∣pderiv i R:= by
  let _:CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
  let _:CharP (zM1 ao) K1.p:=charP_of_injective_ringHom Polynomial.C_injective K1.p
  have hc: (R.degreeOf i:zM1 ao)≠0:= by
    intro hz
    exact (not_le_of_gt ((degreeOf_le_totalDegree R i).trans_lt hb))
      (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (zM1 ao) K1.p _).mp hz))
  have hd0:=pderiv_ne_zero_of_natCast_ne_zero i R hc
  rintro ⟨U,hU⟩
  have hu0:U≠0:= fun he=>hd0 (by rw [hU,he,mul_zero])
  have hd:=degreeOf_pderiv_le_sub_one i R
  rw [hU,degreeOf_mul_eq hR hu0] at hd
  omega
theorem proof :P6_6_7_3.c2 := by
  classical
  intro R G f z a hR hG hb hz ha
  let:=hz.isPrime
  let J:=extended z
  let _:J.IsPrime :=RingHom.ker_isPrime (project z)
  have hchart:bC ((separant^[a]) f)∈z :=ha.2.1 a le_rfl
  have hstrict :J<z := by
    refine lt_of_le_of_ne (extended_le z) fun e=>ha.2.2 ?_
    have h:=extended_deriv (e.symm ▸ hchart)
    exact e ▸ (by simpa only [separant,bC,pderiv_map] using h :
      bC (separant ((separant^[a]) f))∈J)
  have hR0:=agr hR.ne_zero
  have hz2 :=(aD7 hR0 (amo R G hR hG) hz).le
  have hJ1 :J.height≤1 :=
    (ENat.lt_add_one_iff (by simp : (1 :ℕ∞) ≠ ⊤)).mp ((Ideal.height_le_iff.mp hz2) J ‹_› hstrict)
  have hRg:bC R∈z :=hz.le (Ideal.subset_span (by simp))
  have incompatible {D:af 4} (hd : ¬ R∣D)
      (hr :bC R∈J) (hD:bC D∈J) :False := by
    have hne :J ≠ ⊥ := fun e=>hR0 (Ideal.mem_bot.mp (e ▸ hr))
    have h1 :J.height = 1 :=
      hJ1.antisymm (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hne))
    obtain ⟨u,hu,hp⟩:=Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹J.IsPrime› hne
    have he :=Ideal.eq_span_singleton_of_height_eq_one h1 hu hp
    exact hp.not_isUnit (amo R D hR hd
      (Ideal.mem_span_singleton.mp (he ▸ hr)) (Ideal.mem_span_singleton.mp (he ▸ hD)))
  by_contra! h
  by_cases ht: (shape R).t=0
  · have hvars :R.vars.Nonempty := by
      by_contra he
      have hc:=vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp he)
      have hunit :IsUnit (bC R) := by
        rw [hc,bC,zpw]
        exact (isUnit_iff_ne_zero.mpr fun h0=>hR0 (by
          rw [hc,bC,zpw,h0,map_zero])).map C
      exact z.notMem_of_isUnit hunit hRg
    obtain ⟨i,hi⟩:=hvars
    have hw:EY (zhf i 1)=1 := by
      simp [EY,zHG]
    have hD:=order_mem R z (show EY (zhf i 1)<genericOrder R z from
      hw.symm ▸ (le_max_left 1 (shape R).t).trans_lt h)
    rw [hasse_one] at hD
    have hlow: (shape (pderiv i R)).t=0 :=
      Nat.eq_zero_of_le_zero ((degreeOf_pderiv_le i 3 R).trans (le_of_eq ht))
    exact incompatible (btv hR.ne_zero i
      (zOl (mem_vars_iff_degreeOf_ne_zero.mp hi)) hb)
      (extended_of_low ((degree_generic R).trans ht) hRg)
      (extended_of_low ((degree_generic (pderiv i R)).trans hlow) hD)
  · have hr :=extended_of_order ((le_max_right 1 (shape R).t).trans_lt h)
    exact incompatible (btv hR.ne_zero 3 (zOl ht) hb) hr
      (by simpa only [bC,pderiv_map] using extended_deriv hr)
end
end qOdMfWd
end
section
set_option autoImplicit true
namespace qOZqUid
noncomputable section
open aR (Shape)
open UH (lattice gQ fZ ap1)
open MvPolynomial (monomial)
open scoped nonZeroDivisors
abbrev rank (k :Type) [zrb k] (P:Fin 4→Shape) :=
  zsE (fZ k P) (ap1 k P)
abbrev Coeff (P:Fin 4→Shape) (d:Shape) :=
  lattice d ⊕ (Σ i:Fin 4,lattice (P i))
abbrev jo (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :=
  MvPolynomial (Coeff P d) k
abbrev CommonField (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :=
  FractionRing (jo k P d)
def row (k :Type) [zrb k] (P:Fin 4→Shape) (d p:Shape)
    (ι:lattice p→ Coeff P d) :gQ (CommonField k P d) := by
  classical
  letI:=(UH.afS p).fintype
  exact ∑ e :lattice p,monomial e.val
    (algebraMap (jo k P d) (CommonField k P d) (z9v (ι e)))
abbrev literalTuple (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :
    Fin 4→ gQ (CommonField k P d) :=
  fun i=>row k P d (P i) (fun e=>Sum.inr ⟨i,e⟩)
abbrev extraRow (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :=
  row k P d d Sum.inl
abbrev replaceFirst {α:Type} (a :α) (f :Fin 4→α) :Fin 4→α :=
  Fin.cons a (fun i=>f i.succ)
abbrev padTuple (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :=
  replaceFirst (extraRow k P d) (literalTuple k P d)
abbrev tailIdeal {k :Type} [zrb k] (f :Fin 4→ gQ k) :znc (gQ k) :=
  zye (Set.range (fun i:Fin 3=>f i.succ))
end
end qOZqUid
end
section
set_option autoImplicit true
namespace qOZqUid
noncomputable section
open aR (Shape gI Dn)
open P6_6 (wP)
open ap7 (aJ9)
open UH
open lB (bF)
open MvPolynomial
open scoped Pointwise nonZeroDivisors
open private efT from ProximityPrize.SubmissionLower.K
open private bJi from ProximityPrize.SubmissionLower.AG
open private bwo a8w from ProximityPrize.SubmissionLower.T
theorem mul_support {k :Type} [zrb k] {F G:gQ k} {p q:Shape}
    (hF:aJ9 F p) (hG:aJ9 G q) :aJ9 (F*G) (p.plus q) := by
  intro e he
  obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_add.mp (support_mul F G he)
  obtain ⟨h₁,hb₁,hj₁,ht₁⟩:=hF u hu
  obtain ⟨h₂,hb₂,hj₂,ht₂⟩:=hG v hv
  refine ⟨fun i=> by simp only [Finsupp.add_apply,Nat.cast_add]; exact add_nonneg (h₁ i) (h₂ i),
    ?_,?_,?_⟩ <;>
    simp only [Finsupp.add_apply,Nat.cast_add,Shape.plus] <;> linarith
theorem bvn (k :Type) [zrb k] (P:Fin 4→Shape) (d p:Shape)
    (ι:lattice p→ Coeff P d) :aJ9 (row k P d p ι) p:= by
  classical
  intro e he
  unfold row at he
  obtain ⟨v,_,hv⟩:=Finset.mem_biUnion.mp (support_sum he)
  have h:=Finset.mem_singleton.mp (support_monomial_subset hv)
  subst e
  exact aON.mp v.property
private theorem cutIdeal_eq {k :Type} [zrb k] (f :Fin 4→ gQ k) :
    Su f=tailIdeal f ⊔ zye {f 0} := by
  have hf :f=Fin.cons (f 0) (fun i:Fin 3=>f i.succ) := by
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  rw [← Ideal.span_union,Set.union_singleton,← Fin.range_cons,← hf]
theorem replaceIdeal {k :Type} [zrb k] (f :Fin 4→ gQ k) (g:gQ k) :
    Su (replaceFirst g f)=tailIdeal f ⊔ zye {g} :=
  cutIdeal_eq (replaceFirst g f)
private def quotientHead {k :Type} [zrb k] (I:znc (gQ k)) (g:gQ k) :
    (gQ k ⧸ (I ⊔ zye {g})) ≃ₐ[k]
      ((gQ k ⧸ I) ⧸ zye {zVv I g}) := by
  have h: (zye {g}).map (Ideal.Quotient.mkₐ k I) =
      zye {zVv I g} := by
    change (zye {g}).map (zVv I)= _
    rw [Ideal.map_span,Set.image_singleton]
  exact h ▸ (DoubleQuot.quotQuotEquivQuotSupₐ k I (zye {g})).symm
theorem eOZ {k :Type} [zrb k] (f :Fin 4→ gQ k) (g:gQ k)
    (hf :zAa k (Rh f))
    (hg:zAa k (Rh (replaceFirst g f)))
    (hreg:zVv (tailIdeal f) g∈(gQ k ⧸ tailIdeal f)⁰) :
    zAa k (Rh (replaceFirst (f 0*g) f)) ∧
      zsE k (Rh (replaceFirst (f 0*g) f)) =
        zsE k (Rh f)+Module.finrank k (Rh (replaceFirst g f)) := by
  let I:=tailIdeal f
  let S:=gQ k ⧸ I
  let a :=zVv I (f 0)
  let b:=zVv I g
  let A:znc S:=zye {a}
  let B:znc S:=zye {b}
  let J:znc S:=zye {a*b}
  have hJ:b•A=J:= by
    rw [← Submodule.ideal_span_singleton_smul,Ideal.smul_eq_mul,
      Ideal.span_singleton_mul_span_singleton,mul_comm]
  let e₁:Rh f ≃ₐ[k] (S ⧸ A) := by
    change (gQ k ⧸ Su f) ≃ₐ[k] _
    rw [cutIdeal_eq]
    exact quotientHead I (f 0)
  let e₂:Rh (replaceFirst g f) ≃ₐ[k] (S ⧸ B) := by
    change (gQ k ⧸ Su _) ≃ₐ[k] _
    rw [replaceIdeal]
    exact quotientHead I g
  let e₃:Rh (replaceFirst (f 0*g) f) ≃ₐ[k] (S ⧸ J) := by
    change (gQ k ⧸ Su _) ≃ₐ[k] _
    rw [replaceIdeal]
    change _ ≃ₐ[k] S ⧸ zye {zVv I (f 0)* zVv I g}
    rw [← map_mul]
    exact quotientHead I (f 0*g)
  let _:=hf
  let _:=hg
  let _:=zZc e₁.toLinearEquiv
  let _:=zZc e₂.toLinearEquiv
  let e : (S ⧸ (b•A)) ≃ₗ[k] (S ⧸ J) :=
    (Submodule.quotEquivOfEq _ _ hJ).restrictScalars k
  let j:=(Ideal.mulQuot b A).restrictScalars k
  let q:=(Ideal.quotOfMul b A).restrictScalars k
  have hj:zq4 j:=Ideal.mulQuot_injective A hreg
  have hq:Function.Surjective q:=Ideal.quotOfMul_surjective A
  have hex :Function.Exact j q:=Ideal.exact_mulQuot_quotOfMul A
  let _:=Module.Finite.of_exact hex hq
  let _:=zZc e
  refine ⟨zZc e₃.toLinearEquiv.symm,?_⟩
  have hlen:=Module.length_eq_add_of_exact j q hj hq hex
  simp only [Module.length_eq_finrank,← Nat.cast_add,Nat.cast_inj] at hlen
  rw [e₃.toLinearEquiv.finrank_eq,← e.finrank_eq,hlen,
    ← e₁.toLinearEquiv.finrank_eq,← e₂.toLinearEquiv.finrank_eq]
theorem compare_rank (k :Type) [zrb k] (P:Fin 4→Shape) (f :Fin 4→ gQ k)
    (hs : ∀ i,aJ9 (f i) (P i)) (hf :zAa k (Rh f)) :
    zsE k (Rh f)≤ rank k P:= by
  have hc:=aKo.of_children
    cyk.proof cyl.proof
  exact hc k P f (fun i _ he=>aON.mpr (hs i _ he)) hf
    (akO.b4E k P)
theorem chamber_rank (k :Type) [zrb k] (P:Fin 4→Shape)
    (hP : ∀ i,bF (P i)∧Even (P i).j∧Even (P i).t) :
    (32 :ℤ)*rank k P=wP (P 0) (P 1) (P 2) (P 3) := by
  have h:=akO.of_children cym.proof
    (aFS.of_children cyn.proof
      baq.proof)
  have he :=(efT h k P hP).2
  have hv :=bJi (P 0) (P 1) (P 2) (P 3) (hP 0).1 (hP 1).1 (hP 2).1 (hP 3).1
  rw [← he] at hv
  exact_mod_cast hv
theorem mixed_add (p a q r s :Shape) :
    wP (p.plus a) q r s=wP p q r s+wP a q r s :=
  bwo p a q r s
theorem mixed_third (p q r s h:Shape) :
    wP p q (r.plus s) h=wP p q r h+wP p q s h:= by
  exact (a8w _ _ _ _).trans ((a8w _ _ _ _).trans
    ((mixed_add r s h p q).trans (congrArg₂ (· + ·)
      ((a8w _ _ _ _).trans (a8w _ _ _ _))
      ((a8w _ _ _ _).trans (a8w _ _ _ _)))))
theorem bNV (p q r s :Shape) (i j k l:ℕ) :
    wP (p.scale i) (q.scale j) (r.scale k) (s.scale l) =
      (i:ℤ)*j*k*l*wP p q r s := by
  simp only [Ds.wP,FI.oL,gI,Dn,Shape.plus,Shape.scale,
    Nat.cast_add,Nat.cast_mul,Nat.cast_zero]
  ring
end
end qOZqUid
end
