import ProximityPrize.SubmissionLower.ZoYisee
import ProximityPrize.SubmissionLower.ZV9jLRa
set_option Elab.async false
open _root_ renaming AlgHom.comp_apply → zip, Fin.eq_castSucc_or_eq_last → zOq, Fin.last → zym, Fin.lastCases → zsB, Fin.lastCases_last → zTz, Function.Injective → zq4, Function.Surjective → zpX, Ideal → znc, Ideal.Quotient.factor_surjective → zuo, Ideal.Quotient.factorₐ → z5F, Ideal.Quotient.mk → zVv, Ideal.Quotient.mkₐ → zvR, Ideal.comap_map_mk → z7Z, Ideal.pow_le_pow_right → zdr, Ideal.pow_mem_pow → z2s, Module.Finite → zAa, Module.Finite.of_surjective → zIU, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.algHom_ext → zpH, MvPolynomial.eval → zY9, MvPolynomial.ringHom_ext → zXT, Polynomial.hasseDeriv → z75, RingHom.mem_ker → zry
section
set_option autoImplicit true
namespace qlfNNLe
noncomputable section
open scoped BigOperators
private theorem pow_strict {A:Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {m:znc A} (hm:m ≠ ⊤) (hm₀:m ≠ ⊥) (i:ℕ) :m^(i+1)< m^i:= by
  refine lt_of_le_of_ne (zdr (Nat.le_succ i)) fun h => ?_
  have he : (m^i:znc A)≤ m•(m^i:znc A) := by
    rw [smul_eq_mul,← pow_succ',h]
  obtain ⟨r,hr,hann⟩:=Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    m (m^i:znc A) (IsNoetherian.noetherian _) he
  have hr₀:r≠0:= by
    rintro rfl
    exact hm (Ideal.eq_top_of_isUnit_mem _ hr (by simp))
  obtain ⟨x,hx,hx₀⟩:=(Submodule.ne_bot_iff _).mp hm₀
  exact (mul_ne_zero hr₀ (pow_ne_zero i hx₀)) (hann _ (z2s hx i))
private theorem pow_finrank {k A:Type*} [Field k] [CommRing A] [Algebra k A] [IsDomain A]
    [IsNoetherianRing A] {m I:znc A} (hm:m ≠ ⊤) (hm₀:m ≠ ⊥)
    [zAa k (A ⧸ I)] {n:ℕ} (hI:I≤ m^n) :
    n≤zsE k (A ⧸ m^n) := by
  have hfin (i:ℕ) (hi:i≤n) :zAa k (A ⧸ m^i) := by
    have hle :=hI.trans (zdr hi)
    exact zIU (z5F k hle).toLinearMap
      (zuo hle)
  suffices ∀ i≤n,i≤zsE k (A ⧸ m^i) from this n le_rfl
  intro i
  induction i with
  | zero=>simp
  | succ i ih =>
    intro hi
    let _:=hfin (i+1) hi
    obtain ⟨x,hx,hx'⟩:=SetLike.exists_of_lt (pow_strict hm hm₀ i)
    let hle :=zdr (I:=m) (Nat.le_succ i)
    let f :=(z5F k hle).toLinearMap
    have hs :zpX f :=zuo hle
    have hker :0<zsE k (LinearMap.ker f) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      refine ⟨⟨zVv _ x,LinearMap.mem_ker.mpr ?_⟩,?_⟩
      · change zVv (m^i) x=0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
      · intro hz
        exact hx' (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hz))
    have hf :=f.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs,finrank_top] at hf
    have hi' := ih (Nat.le_of_succ_le hi)
    change i.succ≤zsE k (A ⧸ m^i.succ)
    omega
theorem sum_orders_le_finrank {k A ι:Type*} [Field k] [CommRing A] [Algebra k A]
    [IsDomain A] [IsNoetherianRing A] [Fintype ι] {I:znc A}
    [zAa k (A ⧸ I)] {m:ι→ znc A} {n:ι→ℕ}
    (hm : ∀ i,(m i).IsMaximal) (hm₀ : ∀ i,m i ≠ ⊥)
    (hinj:zq4 m) (hI : ∀ i,I≤ m i^n i) :
    (∑ i,n i)≤zsE k (A ⧸ I) := by
  let f :=LinearMap.pi fun i=>(z5F k (hI i)).toLinearMap
  have hcop:Pairwise (fun i j=>IsCoprime (m i^n i) (m j^n j)) := fun i j hij =>
    (Ideal.isCoprime_iff_sup_eq.mpr ((hm i).coprime_of_ne (hm j) (hinj.ne hij))).pow
  have hf :zpX f := by
    intro x
    obtain ⟨r,hr⟩:=Ideal.pi_quotient_surjective hcop x
    exact ⟨zVv I r,funext hr⟩
  have hd:=LinearMap.finrank_le_finrank_of_surjective hf
  let _ (i:ι) :zAa k (A ⧸ m i^n i) :=
    zIU (z5F k (hI i)).toLinearMap
      (zuo (hI i))
  rw [Module.finrank_pi_fintype] at hd
  exact (Finset.sum_le_sum fun i _=>pow_finrank (hm i).ne_top (hm₀ i) (hI i)).trans hd
end
end qlfNNLe
end
section
set_option autoImplicit true
namespace qlfNNLe
noncomputable section
open MvPolynomial P6_6 P6_6_7 q0TFWAc
open aR (ao af Shape shape jet extend Z8 wU)
open dN (GeoField bC j8 Ch An)
open lB (SZ)
open scoped BigOperators Polynomial
private abbrev value (S:ao[X]) (i:Fin 4) :=j8 (jet S i)
private abbrev pt (S:ao[X]) (i:Fin 3) :=value S i.castSucc
private abbrev point (S:ao[X]) :znc Lower :=RingHom.ker (zY9 (pt S))
private theorem point_maximal (S:ao[X]) : (point S).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c=>⟨znf c,MvPolynomial.eval_C c⟩)
private theorem point_le {S:ao[X]} {T:znc dN.GeoJets} (h:T≤Ch S) :
    lowerIdeal T≤point S:= by
  have he : (An S).comp up.toRingHom=zY9 (pt S) := by
    apply zXT
    · intro c
      simp [An]
    · intro i
      simp [An]
  intro f hf
  apply RingHom.mem_ker.mpr
  change zY9 (pt S) f=0
  rw [← he]
  exact RingHom.mem_ker.mp (h hf)
private theorem btI:zq4 point := by
  intro S T h
  have hx : (z9v 0-MvPolynomial.C (pt S 0) :Lower)∈point S:= by
    simp [point,zry]
  rw [h,zry] at hx
  have he :pt T 0=pt S 0:= by simpa [sub_eq_zero] using hx
  change j8 (z75 0 T) =
    j8 (z75 0 S) at he
  simpa only [Polynomial.hasseDeriv_zero'] using (SZ he).symm
private theorem cY8 {V:af 4} {S:ao[X]} {n:ℕ}
    (hV: (shape V).t=0) (ho:wU V S n) :
    down (bC V)∈point S^n:= by
  classical
  let t:Fin 4→Lower :=zsB 0 (fun i=>z9v i-MvPolynomial.C (pt S i))
  let back :=eval₂Hom (MvPolynomial.C.comp j8) t
  let shift:=eval₂Hom znf (fun i:Fin 4=>z9v i+MvPolynomial.C (jet S i))
  let atLast:dN.GeoJets →ₐ[GeoField] Lower :=
    aeval (zsB (znf (value S (zym 3))) z9v)
  have he :back.comp shift=atLast.toRingHom.comp (MvPolynomial.map j8) := by
    apply zXT
    · intro c
      simp [back,shift,atLast]
    · intro i
      rcases zOq i with ⟨i,rfl⟩ | rfl
      · simp [back,shift,atLast,t]
      · simp [back,shift,atLast]
        change t (zym 3)+MvPolynomial.C (value S (zym 3)) =
          zsB (znf (value S (zym 3))) z9v (zym 3)
        simp only [t,zTz,zero_add]
  have hleft:atLast.comp up=AlgHom.id GeoField Lower := by
    apply zpH
    intro i
    simp [atLast]
  have hb:back (Z8 V S)=down (bC V) := by
    change (back.comp shift) V= _
    rw [he]
    change atLast (bC V)= _
    nth_rw 1 [← up_down_physical hV]
    exact AlgHom.congr_fun hleft _
  have ht (i:Fin 4) :t i∈point S:= by
    rcases zOq i with ⟨i,rfl⟩ | rfl
    · simp [t,point,zry]
    · simp only [t,zTz,Ideal.zero_mem]
  rw [← hb,(Z8 V S).as_sum,map_sum]
  apply Ideal.sum_mem
  intro e he'
  rw [eval₂Hom_monomial]
  apply Ideal.mul_mem_left
  have hp:=Ideal.prod_mem_prod (s :=e.support) (I:= fun i=>point S^e i)
    (x := fun i=>t i^e i) (fun i _=>z2s (ht i) (e i))
  rw [Finset.prod_pow_eq_pow_sum] at hp
  exact zdr (ho e he') hp
private theorem bound_section {C:Context} {T:znc dN.GeoJets}
    (hT:T.IsPrime) (hd: (affineHilbertPolynomial (lowerIdeal T)).natDegree≤1)
    {a :Shape} (hb:0<a.b) (hj:2≤a.j) (ht:0<a.t) :SectionBound C T a := by
  classical
  intro V hV hv M hM hm j ho
  let Q:=lowerIdeal T
  let W:=down (bC V)
  have hV₀: (shape V).t=0:=Nat.eq_zero_of_le_zero hV.1.2.2
  have hW:W∉Q:= by
    intro h
    change up W∈T at h
    rw [up_down_physical hV₀] at h
    exact hv h
  let _:Q.IsPrime :=hT.comap _
  let A:=Lower ⧸ Q
  let I:znc A:=Ideal.span {zVv Q W^2}
  obtain ⟨hfin,hrank⟩:=section_finrank hT hd hb hj ht hV hv
  let _:zAa GeoField (A ⧸ I) :=hfin
  let H :=M.filter fun γ=>0<j γ
  let S (γ:H) :=extend (C.s γ)
  let m (γ:H) :=(point (S γ)).map (zVv Q)
  have hmem (γ:H) :=(Finset.mem_filter.mp γ.property).1
  have hQ (γ:H) :Q≤point (S γ) :=point_le (hm _ (hmem γ))
  have hmax (γ:H) : (m γ).IsMaximal:= by
    let _:=point_maximal (S γ)
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hQ γ)
  have hmW (γ:H) :zVv Q W∈m γ^j γ:= by
    have h:=Ideal.mem_map_of_mem (zVv Q) (cY8 hV₀ (ho _ (hmem γ)))
    simpa only [Ideal.map_pow] using h
  have hmI (γ:H) :I≤ m γ^(2*j γ) := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [Nat.mul_comm 2 (j γ),pow_mul (m γ) (j γ) 2]
    exact z2s (hmW γ) 2
  have hnonzero (γ:H) :m γ ≠ ⊥ := by
    intro hz
    have hn:=(Finset.mem_filter.mp γ.property).2
    have hh:=Ideal.pow_le_self (Nat.ne_of_gt hn) (hmW γ)
    rw [hz,Ideal.mem_bot,Ideal.Quotient.eq_zero_iff_mem] at hh
    exact hW hh
  have hinj:zq4 m:= by
    intro γ δ h
    have he :point (S γ)=point (S δ) := by
      simpa only [m,z7Z (hQ γ),z7Z (hQ δ)] using
        congrArg (Ideal.comap (zVv Q)) h
    apply Subtype.ext
    apply C.messages.distinct (hM (hmem γ)) (hM (hmem δ))
    exact Polynomial.map_injective aR.embed aR.embed.injective (btI he)
  have hcount:=sum_orders_le_finrank (k :=GeoField) hmax hnonzero hinj hmI
  have hcast: ((∑ γ:H,2*j γ:ℕ) :ℚ)≤2*curveDegree T a :=
    (Nat.cast_le.mpr hcount).trans hrank
  have hsum: (∑ γ:H,2*j γ)=2 * ∑ γ∈M,j γ:= by
    rw [Finset.sum_coe_sort H (fun γ=>2*j γ),Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    by_cases hp:0<j γ
    · simp [hp]
    · simp [Nat.eq_zero_of_not_pos hp]
  rw [hsum,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] at hcast
  linarith
theorem proof :q0TFWAc.c2 := by
  intro C R l ell h T hT
  have hd:=lower_dimension h hT
  have hj:2≤(body R).j:=h.1.2.2.2
  have hb:0<(body R).b:=(Nat.zero_lt_succ _).trans_le (le_max_right _ _)
  have ht:0<(body R).t:= by
    change 0<(shape R).j/2
    change 2≤(shape R).j at hj
    omega
  have htaylor :4≤bf := by decide
  let a :=lowerTaylor (body R)
  have haj:bf - 1≤a.j:= by
    unfold a lowerTaylor
    exact Nat.le_add_left _ _
  have hab:a.j≤a.b:=le_max_right _ _
  have haj₂:2≤a.j:= by omega
  have hat :0<a.t:= by
    unfold a lowerTaylor
    apply lt_min
    · have ha :bf - 2≤(2*bf - 7)*((body R).t - 1)+bf - 2 := by omega
      omega
    · change 0<a.j/2
      omega
  exact ⟨bound_section hT.isPrime hd hb hj ht,
    bound_section hT.isPrime hd (by omega :0<a.b) haj₂ hat⟩
end
end qlfNNLe
end
section
set_option autoImplicit true
namespace qRBUAkb
noncomputable section
open MvPolynomial P6_6 q6t08kb q0TFWAc
open aR (ao af Shape cK extend qE jet shape)
open dN (GeoField GeoJets j8 bC)
open Dr (dimension aQG)
open lB (amo aFf)
open scoped Polynomial
private theorem exists_cut {T:znc GeoJets} (hT:dimension T=2)
    (a :Fin 3→GeoField) :
    ∃ i:Fin 3,z9v i.castSucc - C (a i)∉T:= by
  by_contra! h
  let φ:GeoJets →ₐ[GeoField] MvPolynomial (Fin 1) GeoField :=
    aeval (zsB (z9v 0) (fun i=>C (a i)))
  let ψ:MvPolynomial (Fin 1) GeoField →ₐ[GeoField] (GeoJets ⧸ T) :=
    aeval (fun _=>zVv T (z9v (zym 3)))
  have hcomp:ψ.comp φ=zvR GeoField T:= by
    apply zpH
    intro i
    refine zsB ?_ (fun j => ?_) i
    · change ψ (φ (z9v (zym 3)))=zVv T (z9v (zym 3))
      simp only [φ,ψ,aeval_X,zTz]
    · have he :=Ideal.Quotient.eq_zero_iff_mem.mpr (h j)
      rw [map_sub,sub_eq_zero] at he
      change zVv T (z9v j.castSucc) =
        algebraMap GeoField (GeoJets ⧸ T) (a j) at he
      simpa [φ,ψ] using he.symm
  have hright:φ.comp (rename (fun _:Fin 1=>zym 3))=AlgHom.id _ _:= by
    apply zpH
    intro i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp only [zip,rename_X,AlgHom.id_apply,φ,aeval_X,zTz]
  have hsurj:zpX φ:= fun p =>
    ⟨rename (fun _:Fin 1=>zym 3) p,AlgHom.congr_fun hright p⟩
  have hle :RingHom.ker φ≤T:= by
    intro p hp
    have hz :φ p=0:=RingHom.mem_ker.mp hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (zvR GeoField T) p=0
    rw [← hcomp,zip,hz,map_zero]
  have hd:=natDegree_affineHilbertPolynomial_le_of_le hle
  rw [natDegree_affineHilbertPolynomial_ker_of_surjective φ hsurj,Nat.card_fin] at hd
  change dimension T≤1 at hd
  rw [hT] at hd
  omega
private def center (S:ao[X]) (i:Fin 3) :af 4 :=
  z9v i.castSucc - C (jet S i.castSucc)
private theorem center_fits (S:ao[X]) (i:Fin 3) {a :Shape}
    (hb:1≤a.b) (hj:2≤a.j) (ht:1≤a.t) :
    lowerFits (center S i) a := by
  have hi: (i.castSucc:Fin 4).val≤2 := by
    change i.val≤2
    have :=i.isLt
    omega
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · change (center S i).totalDegree≤a.b
    exact (totalDegree_sub_C_le _ _).trans (by simpa using hb)
  · change qE (center S i)≤a.j
    rw [Ex.C6,← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
    exact Submodule.sub_mem _ (X_mem_restrictWeightedDegree _ _ _ (hi.trans hj))
      (C_mem_restrictWeightedDegree _ _ _)
  · change (center S i).degreeOf 3≤0
    refine (degreeOf_sub_le _ _ _).trans ?_
    have hne : (3:Fin 4)≠i.castSucc:=(Fin.castSucc_ne_last i).symm
    rw [degreeOf_C,degreeOf_X_of_ne hne,max_self]
  · exact (degreeOf_sub_le _ _ _).trans (by
      rw [degreeOf_C,max_zero]
      exact (degreeOf_X_le _ _).trans ht)
theorem proof :qdWgQqc.c2 := by
  classical
  intro Ctx R l ell h T hT hm
  obtain ⟨γ,hγ,hmark⟩:=hm
  let S:=extend (Ctx.s γ)
  have hn:bC R≠0:= fun he =>
    h.1.1.1.ne_zero (aFf (he.trans (map_zero _).symm))
  have hd:=aQG hn (amo _ _ h.1.1.1 (nonzero_proper h).2) hT
  obtain ⟨i,hi⟩:=exists_cut hd (fun j=>j8 (jet S j.castSucc))
  have hp:bC (center S i)∉T:= by
    simpa only [center,bC,map_sub,MvPolynomial.map_X,MvPolynomial.map_C] using hi
  have hb:1≤(body R).b :=
    (show 1≤(shape R).j+3 by omega).trans (le_max_right _ _)
  have hj:2≤(body R).j:=h.1.2.2.2
  have ht:1≤(body R).t:= by
    change 1≤(body R).j/2
    omega
  have hΔ:γ∈Ctx.Δ:=(Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).1
  have hvan:cK (center S i) S=0:= by
    simp [cK,center]
  have hbound:=(qlfNNLe.proof Ctx R l ell h T hT).1
    (center S i) (center_fits S i hb hj ht) hp {γ}
    (Finset.singleton_subset_iff.mpr hΔ)
    (fun δ hδ=>(Finset.mem_singleton.mp hδ).symm ▸ hmark) (fun _=>1)
    (fun δ hδ=>(Finset.mem_singleton.mp hδ).symm ▸ order_one hvan)
  simpa only [Finset.sum_singleton,Nat.cast_one] using hbound
end
end qRBUAkb
end
