import ProximityPrize.SubmissionLower.ZuuSwCe
import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap
set_option Elab.async false
open _root_ renaming AlgHom.comp_toLinearMap → zB0, Fin.sum_univ_four → zmL, Finset.sum_eq_single → zi6, Finsupp.add_apply → zSs, Finsupp.degree_eq_sum → zFi, Finsupp.single → zhf, Finsupp.single_add → zIh, Finsupp.weight_eq_sum → z1K, Function.Injective → zq4, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.mkₐ → zvR, Ideal.comap → zK3, Ideal.comap_isPrime → zG1, Ideal.map_le_iff_le_comap → zo0, Ideal.mem_comap → zAV, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.mul_mem_right → zx6, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, Ideal.subset_span → zCn, LinearMap.finrank_range_of_inj → z0K, LinearMap.ker → z83, LinearMap.mulLeft → zzN, LinearMap.range_domRestrict → zyK, Module.Finite → zAa, Module.Finite.of_basis → zwB, Module.finrank → zsE, MvPolynomial → z3y, Nat.lt_succ_of_le → zB1, Polynomial → zM1, Polynomial.C → z1z, Set.mem_add → zvS, Set.mem_zero → zkx, Submodule.equivMapOfInjective → zW6, Submodule.map_comp → z1U, Submodule.map_le_iff_le_comap → zPy, Submodule.span_induction → zt0
section
set_option autoImplicit true
namespace qkYPzab
noncomputable section
open aR (Shape)
open dN (GeoField GeoJets)
open yz (aCt)
open qXuDJRd
open MvPolynomial
open scoped Pointwise
abbrev V (s :Shape) :Submodule GeoField GeoJets :=restrictSupport GeoField (aCt s 0)
instance (s :Shape) :zAa GeoField (V s) :=
  zwB (basisRestrictSupport GeoField (aCt s 0))
theorem finrank_V (s :Shape) :zsE GeoField (V s)=lattice s := by
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _),Nat.card_coe_set_eq]
theorem mem_V {s :Shape} {p:GeoJets} : p∈V s↔p.degreeOf 3=0∧p.totalDegree≤ s.b ∧
    p.weightedTotalDegree (fun i:Fin 4=>i.val)≤ s.j∧p.degreeOf 2≤ s.t:= by
  rw [mem_restrictSupport_iff]
  constructor
  · intro h
    have hb : ∀ e∈p.support,e 0+e 1+e 2≤ s.b∧e 1+2*e 2≤ s.j∧e 2≤ s.t ∧
        e 3≤0:= fun e he=>h (Finset.mem_coe.mpr he)
    refine ⟨Nat.eq_zero_of_le_zero (degreeOf_le_iff.mpr fun e he=>(hb e he).2.2.2),?_,?_,
      degreeOf_le_iff.mpr fun e he=>(hb e he).2.2.1⟩
    · unfold totalDegree
      refine Finset.sup_le fun e he => ?_
      have :=hb e he
      change e.degree≤ s.b
      rw [zFi,zmL]
      omega
    · unfold weightedTotalDegree
      refine Finset.sup_le fun e he => ?_
      have :=hb e he
      rw [z1K,zmL]
      simp only [smul_eq_mul]
      change e 0*0+e 1*1+e 2*2+e 3*3≤_
      omega
  · rintro ⟨h3,h1,h2,h4⟩ e he
    have he' := Finset.mem_coe.mp he
    have a1 :e.degree≤ s.b:=(le_totalDegree he').trans h1
    have a2 :Finsupp.weight (fun i:Fin 4=>i.val) e≤ s.j :=
      (le_weightedTotalDegree (fun i:Fin 4=>i.val) he').trans h2
    have a3:e 2≤ s.t:=(degreeOf_le_iff.mp h4) e he'
    have a4 :e 3≤0:=h3 ▸ (degreeOf_le_iff.mp le_rfl) e he'
    rw [zFi,zmL] at a1
    rw [z1K,zmL] at a2
    simp only [smul_eq_mul] at a2
    change e 0*0+e 1*1+e 2*2+e 3*3≤_ at a2
    exact ⟨by omega,by omega,a3,a4⟩
theorem mul_mem {h p:GeoJets} {s :Shape} (hh:h≠0) (h3:h.degreeOf 3=0) (hp:p∈V s) :
    h*p∈V (s.plus (lowerShape h)) := by
  by_cases hp0:p=0
  · simp [hp0]
  obtain ⟨a1,a2,a3,a4⟩:=mem_V.mp hp
  refine mem_V.mpr ⟨?_,?_,?_,?_⟩
  · rw [degreeOf_mul_eq hh hp0]; omega
  · rw [totalDegree_mul_of_isDomain hh hp0]
    change _≤ s.b+h.totalDegree
    omega
  · rw [weightedTotalDegree_mul _ _ _ hh hp0]
    change _≤ s.j+h.weightedTotalDegree (fun i:Fin 4=>i.val)
    omega
  · rw [degreeOf_mul_eq hh hp0]
    change _≤ s.t+h.degreeOf 2
    omega
theorem div_mem {h c:GeoJets} {s :Shape} (hh:h≠0) (h3:h.degreeOf 3=0)
    (hc:h*c∈V (s.plus (lowerShape h))) :c∈V s := by
  by_cases hc0:c=0
  · simp [hc0]
  obtain ⟨a1,a2,a3,a4⟩:=mem_V.mp hc
  rw [degreeOf_mul_eq hh hc0] at a1 a4
  rw [totalDegree_mul_of_isDomain hh hc0] at a2
  rw [weightedTotalDegree_mul _ _ _ hh hc0] at a3
  change _≤ s.b+h.totalDegree at a2
  change _≤ s.j+h.weightedTotalDegree (fun i:Fin 4=>i.val) at a3
  change _≤ s.t+h.degreeOf 2 at a4
  exact mem_V.mpr ⟨by omega,by omega,by omega,by omega⟩
theorem nsmul_box (s :Shape) (N :ℕ) : ∀ e∈N•aCt s 0,
    e∈aCt ⟨N*s.b,N*s.j,N*s.t⟩ 0:= by
  induction N with
  | zero =>
    intro e he
    rw [zero_nsmul] at he
    rw [zkx] at he
    subst he
    simp [aCt]
  | succ N ih =>
    intro e he
    rw [succ_nsmul,zvS] at he
    obtain ⟨u,hu,v,hv,rfl⟩:=he
    have hu' : u 0+u 1+u 2≤N*s.b∧u 1+2*u 2≤N*s.j ∧
        u 2≤N*s.t∧u 3≤0:=ih u hu
    have hv' : v 0+v 1+v 2≤ s.b∧v 1+2*v 2≤ s.j∧v 2≤ s.t ∧
        v 3≤0:=hv
    clear ih hu hv
    obtain ⟨c1,c2,c3,c4⟩:=hu'
    obtain ⟨b1,b2,b3,b4⟩:=hv'
    have :=Nat.add_one_mul N s.b
    have :=Nat.add_one_mul N s.j
    have :=Nat.add_one_mul N s.t
    change (u+v) 0+(u+v) 1+(u+v) 2≤(N+1)*s.b ∧
      (u+v) 1+2*(u+v) 2≤(N+1)*s.j∧(u+v) 2≤(N+1)*s.t∧(u+v) 3≤0
    simp only [zSs]
    omega
theorem proof :qXuDJRd.c2 := by
  intro f g hf hg hrel hf3 hg3 a d n x q r
  let M:=V ((x.plus q).plus r)
  let φ:=capMap a 0
  have hM : ∀ P:z3y (aCt (a.scale 2) 0) GeoField,P.totalDegree≤n →
      φ P∈M:= by
    intro P hP
    have h0: (0:Fin 4 →₀ ℕ)∈aCt (a.scale 2) 0:= by simp [aCt]
    refine restrictSupport_mono GeoField ?_ (monomialMap_mem_restrictSupport_nsmul h0 hP)
    intro e he
    have he' : e 0+e 1+e 2≤n*(2*a.b)∧e 1+2*e 2≤n*(2*a.j) ∧
      e 2≤n*(2*a.t)∧e 3≤0:=nsmul_box _ n e he
    clear he
    obtain ⟨c1,c2,c3,c4⟩:=he'
    change _∧_∧_∧_
    have u1 :n*(2*a.b)=2*n*a.b:= by ring
    have u2 :n*(2*a.j)=2*n*a.j:= by ring
    have u3:n*(2*a.t)=2*n*a.t:= by ring
    refine ⟨?_,?_,?_,?_⟩
    · change e 0+e 1+e 2≤(2*n*a.b+d.b)+q.b+r.b
      omega
    · change e 1+2*e 2≤(2*n*a.j+d.j)+q.j+r.j
      omega
    · change e 2≤(2*n*a.t+d.t)+q.t+r.t
      omega
    · exact c4
  have h1 :capHilbert (pair f g) a 0 n ≤
      zsE GeoField (M.map (zvR GeoField (pair f g)).toLinearMap) :=
    affineHilbertFunction_comap_le_finrank_map φ (pair f g) M hM
  let A:=(V (x.plus r)).map (zzN GeoField f)
  let B:=(V (x.plus q)).map (zzN GeoField g)
  let C:=(V x).map (zzN GeoField (f * g))
  have hfg:f * g≠0:=mul_ne_zero hf hg
  have shape1 : (x.plus q).plus r=(x.plus r).plus q:= by
    simp only [Shape.plus,Shape.mk.injEq]; omega
  have hAM:A≤M:= by
    rintro _ ⟨p,hp,rfl⟩
    change f*p∈V ((x.plus q).plus r)
    rw [shape1]
    exact mul_mem hf hf3 hp
  have hBM:B≤M:= by
    rintro _ ⟨p,hp,rfl⟩
    change g*p∈V ((x.plus q).plus r)
    exact mul_mem hg hg3 hp
  have hfA:zsE GeoField A=lattice (x.plus r) := by
    rw [← finrank_V,← (zW6 (zzN GeoField f)
      (mul_right_injective₀ hf) _).finrank_eq]
  have hfB:zsE GeoField B=lattice (x.plus q) := by
    rw [← finrank_V,← (zW6 (zzN GeoField g)
      (mul_right_injective₀ hg) _).finrank_eq]
  have hfC:zsE GeoField C=lattice x := by
    rw [← finrank_V,← (zW6 (zzN GeoField (f * g))
      (mul_right_injective₀ hfg) _).finrank_eq]
  have hAB:A ⊓ B≤C:= by
    rintro y ⟨⟨p,hp,rfl⟩,⟨p',hp',hy⟩⟩
    change g*p' = f*p at hy
    have hdvd:g∣p:=hrel.symm.dvd_of_dvd_mul_left ⟨p',hy.symm⟩
    obtain ⟨c,rfl⟩:=hdvd
    exact ⟨c,div_mem hg hg3 hp,by change f * g*c=f*(g*c); ring⟩
  have hinf :zsE GeoField (A ⊓ B:Submodule GeoField GeoJets)≤lattice x :=
    hfC ▸ Submodule.finrank_mono hAB
  have hsup:=Submodule.finrank_sup_add_finrank_inf_eq A B
  have hKM:A ⊔ B≤M:=sup_le hAM hBM
  let π:=(zvR GeoField (pair f g)).toLinearMap.domRestrict M
  have hker : ∀ y∈A ⊔ B,(zvR GeoField (pair f g)).toLinearMap y=0:= by
    intro y hy
    have :A ⊔ B≤z83 (zvR GeoField (pair f g)).toLinearMap:= by
      refine sup_le ?_ ?_
      · rintro _ ⟨p,hp,rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (zKg (zx6 _ _ (zCn rfl)))
      · rintro _ ⟨p,hp,rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (zs0 (zx6 _ _ (zCn rfl)))
    exact this hy
  let L: (A ⊔ B:Submodule GeoField GeoJets) →ₗ[GeoField] z83 π :=
    ((Submodule.inclusion hKM).codRestrict (z83 π) fun y=> by
      rw [LinearMap.mem_ker]
      exact hker _ y.2)
  have hL:zq4 L:= fun x y hxy =>
    Subtype.ext (congrArg (fun z=>(z :M).1) (congrArg Subtype.val hxy))
  have hK:=LinearMap.finrank_le_finrank_of_injective hL
  have hrank :=π.finrank_range_add_finrank_ker
  rw [zyK] at hrank
  have hlat :zsE GeoField M=lattice ((x.plus q).plus r) :=finrank_V _
  omega
end
end qkYPzab
end
section
set_option autoImplicit true
namespace qKvzzcc
noncomputable section
open MvPolynomial
open scoped Pointwise
variable {k :Type} [Field k] {τ σ:Type}
theorem map_degreeLE {S:Set (σ →₀ ℕ)} (h0:0∈S) (n:ℕ) :
    (restrictTotalDegree (↥S) k n).map (monomialMap k S).toLinearMap=restrictSupport k (n•S) := by
  classical
  apply le_antisymm
  · rw [zPy]
    intro P hP
    exact monomialMap_mem_restrictSupport_nsmul h0 ((mem_restrictTotalDegree _ _ _).mp hP)
  · have key : ∀ n:ℕ,∀ m∈n•S,∃ q:z3y S k,q.totalDegree≤n ∧
        monomialMap k S q=monomial m 1 := by
      intro n
      induction n with
      | zero =>
        intro m hm
        rw [zero_nsmul,zkx] at hm
        subst hm
        exact ⟨1,by simp,by simp⟩
      | succ n ih =>
        intro m hm
        rw [succ_nsmul',zvS] at hm
        obtain ⟨s,hs,m',hm',rfl⟩:=hm
        obtain ⟨q,hq,hqm⟩:=ih m' hm'
        let xs :z3y S k :=MvPolynomial.X ⟨s,hs⟩
        refine ⟨xs*q,?_,?_⟩
        · calc (xs*q).totalDegree≤xs.totalDegree +
                q.totalDegree :=totalDegree_mul _ _
            _≤1+n:=Nat.add_le_add (totalDegree_X _).le hq
            _=n+1 :=Nat.add_comm _ _
        · rw [map_mul,hqm,monomialMap_X,monomial_mul_monomial,one_mul]
    rw [restrictSupport_eq_span,Submodule.span_le]
    rintro _ ⟨m,hm,rfl⟩
    obtain ⟨q,hq,hqm⟩:=key n m hm
    exact ⟨q,(mem_restrictTotalDegree _ _ _).mpr hq,hqm⟩
theorem finrank_quotientDegreeLE_comap {S:Set (σ →₀ ℕ)} (h0:0∈S)
    (T:Ideal (z3y σ k)) (n:ℕ) :
    zsE k (quotientDegreeLE (T.comap (monomialMap k S).toRingHom) n) =
      zsE k ((restrictSupport k (n•S)).map (zvR k T).toLinearMap) := by
  let f :=monomialMap k S
  let I:=T.comap f.toRingHom
  let g:z3y S k ⧸ I →ₐ[k] z3y σ k ⧸ T :=
    Ideal.quotientMapₐ T f le_rfl
  let L:=g.toLinearMap.domRestrict (quotientDegreeLE I n)
  have hL:zq4 L:= by
    intro x y hxy
    exact Subtype.ext (Ideal.quotientMap_injective (I:=T) (f :=f.toRingHom) hxy)
  have hcomp:g.comp (zvR k I)=(zvR k T).comp f :=
    Ideal.quotient_map_comp_mkₐ T f le_rfl
  have hrange :LinearMap.range L =
      (restrictSupport k (n•S)).map (zvR k T).toLinearMap:= by
    dsimp only [L]
    rw [zyK,quotientDegreeLE,← z1U,
      ← zB0,hcomp,zB0,z1U,
      map_degreeLE h0]
  change zsE k (quotientDegreeLE I n)= _
  rw [← z0K hL,hrange]
end
end qKvzzcc
end
section
set_option autoImplicit true
namespace qKvzzcc
noncomputable section
open MvPolynomial
open scoped Pointwise
variable {k :Type} [Field k]
def E (k :Type) [Field k] :z3y (Fin 4) k ≃ₐ[k] zM1 (z3y (Fin 3) k) :=
  (renameEquiv k (finSuccEquivLast:Fin (3+1) ≃ Option (Fin 3))).trans
    (optionEquivLeft k (Fin 3))
theorem E_X_last :E k (MvPolynomial.X 3)=Polynomial.X:= by
  have h:finSuccEquivLast (3:Fin (3+1))=none :=finSuccEquivLast_last
  show optionEquivLeft k (Fin 3) (rename finSuccEquivLast (MvPolynomial.X 3))= _
  rw [rename_X,h,optionEquivLeft_X_none]
theorem E_X_ne {i:Fin 4} (hi:i≠3) : ∃ q,E k (MvPolynomial.X i)=z1z q:= by
  have hi' : i≠Fin.last 3:=hi
  obtain ⟨j,rfl⟩:=Fin.exists_castSucc_eq.mpr hi'
  refine ⟨MvPolynomial.X j,?_⟩
  show optionEquivLeft k (Fin 3) (rename finSuccEquivLast (MvPolynomial.X j.castSucc))= _
  rw [rename_X,finSuccEquivLast_castSucc,optionEquivLeft_X_some]
theorem E_free {w:z3y (Fin 4) k}
    (hw:w∈restrictSupport k {m:Fin 4 →₀ ℕ | m 3=0}) :
    ∃ w0,E k w=z1z w0:= by
  rw [restrictSupport_eq_span] at hw
  induction hw using zt0 with
  | mem x hx =>
    obtain ⟨m,hm,rfl⟩:=hx
    have hm3:m 3=0:=hm
    have hprod: (monomial m (1 :k))=m.prod (fun i e=>(MvPolynomial.X i:z3y (Fin 4) k)^e) := by
      rw [monomial_eq,C_1,one_mul]
    have hmem:E k (monomial m (1 :k)) ∈
        (z1z:z3y (Fin 3) k →+* zM1 (z3y (Fin 3) k)).range := by
      rw [hprod,Finsupp.prod,map_prod]
      refine prod_mem (fun i hi => ?_)
      rw [map_pow]
      refine pow_mem ?_ _
      have hi3:i≠3:= fun h=> by subst h; exact (Finsupp.mem_support_iff.mp hi) hm3
      obtain ⟨q,hq⟩:=E_X_ne (k :=k) hi3
      exact ⟨q,hq.symm⟩
    obtain ⟨q,hq⟩:=hmem
    exact ⟨q,hq.symm⟩
  | zero=>exact ⟨0,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,ha⟩:=hx
    obtain ⟨b,hb⟩:=hy
    exact ⟨a+b,by rw [map_add,ha,hb,Polynomial.C_add]⟩
  | smul c x _ hx =>
    obtain ⟨a,ha⟩:=hx
    exact ⟨c•a,by rw [map_smul,ha,Polynomial.smul_C]⟩
def Vn (n:ℕ) :Set (Fin 4 →₀ ℕ) := {m | ∃ c≤n,m=zhf 3 c}
theorem hilbert_cyl (T:Ideal (z3y (Fin 4) k)) (J:Ideal (z3y (Fin 3) k))
    (hT : ∀ p,p∈T↔E k p∈J.map (z1z))
    (D:Set (Fin 4 →₀ ℕ)) (hD : ∀ m∈D,m 3=0) (hfin:D.Finite) (n:ℕ) :
    zsE k ((restrictSupport k (D + Vn n)).map (zvR k T).toLinearMap) =
      (n+1)*zsE k
        ((restrictSupport k D).map (zvR k T).toLinearMap) := by
  classical
  set π:=zvR k T with hπ
  set W:=restrictSupport k D with hWdef
  set Q0:=W.map π.toLinearMap with hQ0
  have :Finite D:=hfin.to_subtype
  have :zAa k W:=zwB (basisRestrictSupport k D)
  have :zAa k Q0:=inferInstance
  have hW0 : ∀ w∈W,∃ w0,E k w=z1z w0:= fun w hw =>
    E_free (restrictSupport_mono k (fun m hm=>hD m hm) hw)
  let Λ: (Fin (n+1)→Q0) →ₗ[k] z3y (Fin 4) k ⧸ T :=
    ∑ c:Fin (n+1),(zzN k (π (MvPolynomial.X 3)^(c:ℕ))).comp
      (Q0.subtype.comp (LinearMap.proj c))
  have hΛ : ∀ f,Λ f = ∑ c:Fin (n+1),π (MvPolynomial.X 3)^(c:ℕ)*((f c:Q0) :z3y (Fin 4) k ⧸ T) := by
    intro f
    simp [Λ,LinearMap.sum_apply]
  have hmulY : ∀ c≤n,∀ w∈W,w*(MvPolynomial.X 3:z3y (Fin 4) k)^c ∈
      restrictSupport k (D + Vn n) := by
    intro c hc w hw
    rw [restrictSupport_add]
    refine Submodule.mul_mem_mul hw ?_
    rw [ X_pow_eq_monomial]
    exact (monomial_mem_restrictSupport k).mpr (Or.inl ⟨c,hc,rfl⟩)
  have hrange :LinearMap.range Λ =
      (restrictSupport k (D + Vn n)).map π.toLinearMap:= by
    apply le_antisymm
    · rintro _ ⟨f,rfl⟩
      rw [hΛ]
      refine Submodule.sum_mem _ (fun c _ => ?_)
      obtain ⟨w,hw,hwf⟩:=Submodule.mem_map.mp (f c).2
      refine Submodule.mem_map.mpr ⟨w*(MvPolynomial.X 3:z3y (Fin 4) k)^(c:ℕ),
        hmulY c (Nat.lt_succ_iff.mp c.2) w hw,?_⟩
      change π (w*(MvPolynomial.X 3:z3y (Fin 4) k)^(c:ℕ))= _
      rw [map_mul,map_pow,mul_comm]
      congr 1
    · rw [zPy,restrictSupport_add,Submodule.mul_le]
      intro w hw y hy
      rw [restrictSupport_eq_span] at hy
      induction hy using zt0 with
      | mem y hy =>
        obtain ⟨m,⟨c,hc,rfl⟩,rfl⟩:=hy
        rw [Submodule.mem_comap,LinearMap.mem_range]
        refine ⟨Pi.single (⟨c,zB1 hc⟩:Fin (n+1))
          (⟨π w,Submodule.mem_map_of_mem hw⟩:Q0),?_⟩
        rw [hΛ,zi6 (⟨c,zB1 hc⟩:Fin (n+1))]
        · rw [Pi.single_eq_same]
          change _=π (w*monomial (zhf 3 c) 1)
          rw [← X_pow_eq_monomial,map_mul,map_pow,mul_comm]
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb]
          simp
        · intro h
          exact absurd (Finset.mem_univ _) h
      | zero=>simp
      | add a b _ _ ha hb =>
        rw [mul_add]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ ha
  have hinj:zq4 Λ:= by
    rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro f hf
    rw [hΛ] at hf
    have hw : ∀ c,∃ w∈W,π w=((f c:Q0) :z3y (Fin 4) k ⧸ T) := fun c=> by
      obtain ⟨w,hw,h⟩:=Submodule.mem_map.mp (f c).2
      exact ⟨w,hw,h⟩
    choose w hwW hwf using hw
    have hsum0:π (∑ c:Fin (n+1),w c*(MvPolynomial.X 3:z3y (Fin 4) k)^(c:ℕ))=0:= by
      rw [map_sum,← hf]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [map_mul,map_pow,hwf c,mul_comm]
    have hsum: (∑ c:Fin (n+1),w c*(MvPolynomial.X 3:z3y (Fin 4) k)^(c:ℕ))∈T :=
      (z1Q (I:=T)).mp hsum0
    have hw0 : ∀ c,∃ w0,E k (w c)=z1z w0:= fun c=>hW0 _ (hwW c)
    choose w0 hw0 using hw0
    have hE :E k (∑ c:Fin (n+1),w c*(MvPolynomial.X 3:z3y (Fin 4) k)^(c:ℕ)) =
        ∑ c:Fin (n+1),z1z (w0 c)*Polynomial.X ^(c:ℕ) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [map_mul,map_pow,hw0 c,E_X_last]
    have hmem: (∑ c:Fin (n+1),z1z (w0 c)*Polynomial.X ^(c:ℕ)) ∈
        J.map (z1z:z3y (Fin 3) k →+* zM1 (z3y (Fin 3) k)) := by
      rw [← hE]; exact (hT _).mp hsum
    have hcoef :=Ideal.mem_map_C_iff.mp hmem
    funext c0
    have h1 :=hcoef (c0:ℕ)
    rw [Polynomial.finset_sum_coeff] at h1
    simp only [Polynomial.coeff_C_mul_X_pow] at h1
    rw [zi6 c0 (fun c _ hc=>if_neg (fun h=>hc (Fin.ext h.symm)))
      (fun h=>absurd (Finset.mem_univ _) h),if_pos rfl] at h1
    have hwT:w c0∈T:=(hT _).mpr (by rw [hw0 c0]; exact z7X _ h1)
    apply Subtype.ext
    rw [Pi.zero_apply,Submodule.coe_zero,← hwf c0]
    exact (z1Q (I:=T)).mpr hwT
  rw [← hrange,z0K hinj,Module.finrank_pi_fintype]
  simp
end
end qKvzzcc
end
section
set_option autoImplicit true
namespace qKvzzcc
noncomputable section
open MvPolynomial
variable {k :Type} [Field k]
theorem free_of_degreeOf {f :z3y (Fin 4) k} (hf :f.degreeOf 3=0) :
    ∃ f0,E k f=z1z f0:= by
  apply E_free
  rw [mem_restrictSupport_iff]
  intro m hm
  have h:=monomial_le_degreeOf 3 (Finset.mem_coe.mp hm)
  exact Nat.le_zero.mp (hf ▸ h)
theorem exists_J {f g:z3y (Fin 4) k} (hf :f.degreeOf 3=0) (hg:g.degreeOf 3=0)
    {T:Ideal (z3y (Fin 4) k)}
    (hT:T=zye {f} ⊔ zye {g} ∨
      (zye {f} ⊔ zye {g}).IsMinimalPrime T) :
    ∃ J:Ideal (z3y (Fin 3) k),∀ p,p∈T↔E k p∈J.map Polynomial.C:= by
  obtain ⟨f0,hf0⟩:=free_of_degreeOf hf
  obtain ⟨g0,hg0⟩:=free_of_degreeOf hg
  have hfs : (E k).symm (z1z f0)=f := by rw [AlgEquiv.symm_apply_eq,hf0]
  have hgs : (E k).symm (z1z g0)=g:= by rw [AlgEquiv.symm_apply_eq,hg0]
  rcases hT with rfl | hmin
  · refine ⟨zye {f0,g0},fun p=>⟨fun hp => ?_,fun hp => ?_⟩⟩
    · have hle :zye {f} ⊔ zye {g} ≤
          zK3 (E k) ((zye {f0,g0}).map (z1z:z3y (Fin 3) k →+*
            zM1 (z3y (Fin 3) k))) := by
        rw [sup_le_iff,zvl,zvl,
          zAV,zAV,hf0,hg0]
        exact ⟨Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp)),
          Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))⟩
      exact hle hp
    · have hle : (zye {f0,g0}).map (z1z:z3y (Fin 3) k →+*
            zM1 (z3y (Fin 3) k)) ≤
          zK3 (E k).symm (zye {f} ⊔ zye {g}) := by
        rw [zo0,Ideal.span_le]
        intro r hr
        rcases hr with rfl | rfl
        · rw [SetLike.mem_coe,zAV,zAV]
          exact zKg (zCn (by simpa using hfs))
        · rw [SetLike.mem_coe,zAV,zAV]
          exact zs0 (zCn (by simpa using hgs))
      have :=hle hp
      rwa [zAV,AlgEquiv.symm_apply_apply] at this
  · have hTp:T.IsPrime :=hmin.isPrime
    have hpair :zye {f} ⊔ zye {g} ≤ T:=hmin.le
    let P:Ideal (z3y (Fin 3) k) :=
      zK3 (z1z:z3y (Fin 3) k →+* zM1 (z3y (Fin 3) k))
        (zK3 (E k).symm T)
    have hPp:P.IsPrime :=zG1 _ _
    have hPT : ∀ q∈P.map (z1z:z3y (Fin 3) k →+*
        zM1 (z3y (Fin 3) k)),(E k).symm q∈T:= by
      intro q hq
      have :P.map (z1z:z3y (Fin 3) k →+*
          zM1 (z3y (Fin 3) k))≤zK3 (E k).symm T:= by
        rw [zo0]
      exact this hq
    refine ⟨P,fun p=>⟨fun hp => ?_,fun hp => ?_⟩⟩
    · let Q:Ideal (z3y (Fin 4) k) :=zK3 (E k) (P.map (z1z :
        z3y (Fin 3) k →+* zM1 (z3y (Fin 3) k)))
      have hQp:Q.IsPrime := by
        have : (P.map (z1z:z3y (Fin 3) k →+*
          zM1 (z3y (Fin 3) k))).IsPrime :=Ideal.isPrime_map_C_of_isPrime
        exact zG1 _ _
      have hpairQ:zye {f} ⊔ zye {g} ≤ Q:= by
        rw [sup_le_iff,zvl,zvl]
        refine ⟨?_,?_⟩
        · change E k f∈P.map (z1z:z3y (Fin 3) k →+*
            zM1 (z3y (Fin 3) k))
          rw [hf0]
          refine z7X _ ?_
          show (E k).symm (z1z f0)∈T
          rw [hfs]
          exact hpair (zKg (z5J f))
        · change E k g∈P.map (z1z:z3y (Fin 3) k →+*
            zM1 (z3y (Fin 3) k))
          rw [hg0]
          refine z7X _ ?_
          show (E k).symm (z1z g0)∈T
          rw [hgs]
          exact hpair (zs0 (z5J g))
      have hQT:Q≤T:= by
        intro q hq
        have :=hPT _ hq
        rwa [AlgEquiv.symm_apply_apply] at this
      exact hmin.2 ⟨hQp,hpairQ⟩ hQT hp
    · have :=hPT _ hp
      rwa [AlgEquiv.symm_apply_apply] at this
end
end qKvzzcc
end
section
set_option autoImplicit true
namespace qKvzzcc
noncomputable section
open aR (Shape)
open dN (GeoField)
open yz (aCt)
open MvPolynomial
open scoped Pointwise
theorem Vn_zero :Vn 0=0:= by
  ext m
  simp [Vn]
theorem Vn_add (n:ℕ) :Vn 1+Vn n=Vn (n+1) := by
  ext m
  simp only [zvS]
  constructor
  · rintro ⟨x,⟨c1,hc1,rfl⟩,y,⟨c2,hc2,rfl⟩,rfl⟩
    exact ⟨c1+c2,by omega,(zIh _ _ _).symm⟩
  · rintro ⟨c,hc,rfl⟩
    by_cases h0:c=0
    · subst h0
      exact ⟨zhf 3 0,⟨0,by omega,rfl⟩,zhf 3 0,⟨0,by omega,rfl⟩,by simp⟩
    · refine ⟨zhf 3 1,⟨1,le_rfl,rfl⟩,zhf 3 (c - 1),
        ⟨c - 1,by omega,rfl⟩,?_⟩
      rw [← zIh]
      congr 1
      omega
theorem bI2 {s :Shape} {h:ℕ} {a :Fin 4 →₀ ℕ} :
    a∈aCt s h ↔
      a 0+a 1+a 2≤ s.b∧a 1+2*a 2≤ s.j∧a 2≤ s.t∧a 3≤h:=Iff.rfl
theorem box_succ (s :Shape) :aCt s 1=aCt s 0+Vn 1 := by
  ext a
  simp only [zvS]
  constructor
  · intro h
    obtain ⟨h1,h2,h3,h4⟩:=bI2.mp h
    refine ⟨a.erase 3,?_,zhf 3 (a 3),⟨a 3,h4,rfl⟩,Finsupp.erase_add_single 3 a⟩
    rw [bI2]
    simp only [Finsupp.erase_apply]
    simp
    omega
  · rintro ⟨x,hx,y,⟨c,hc,rfl⟩,rfl⟩
    obtain ⟨h1,h2,h3,h4⟩:=bI2.mp hx
    rw [bI2]
    simp only [zSs,Finsupp.single_apply]
    simp
    omega
theorem nsmul_box (s :Shape) (n:ℕ) :
    n•aCt s 1=n•aCt s 0+Vn n:= by
  induction n with
  | zero=>rw [zero_nsmul,zero_nsmul,Vn_zero,zero_add]
  | succ n ih =>
    rw [succ_nsmul',succ_nsmul',ih,box_succ,add_add_add_comm,Vn_add]
theorem nsmul_box0 (s :Shape) (n:ℕ) : ∀ m∈n•aCt s 0,m 3=0:= by
  induction n with
  | zero =>
    intro m hm
    rw [zero_nsmul,zkx] at hm
    subst hm
    rfl
  | succ n ih =>
    intro m hm
    rw [succ_nsmul',zvS] at hm
    obtain ⟨x,hx,y,hy,rfl⟩:=hm
    have h4 :=(bI2.mp hx).2.2.2
    simp only [zSs]
    have :=ih y hy
    omega
theorem bqc (s :Shape) (n:ℕ) : (n•aCt s 0).Finite := by
  induction n with
  | zero=>rw [zero_nsmul]; exact Set.finite_singleton _
  | succ n ih =>
    rw [succ_nsmul']
    exact (Set.toFinite (aCt s 0)).add ih
theorem zero_mem_box (s :Shape) (h:ℕ) : (0:Fin 4 →₀ ℕ)∈aCt s h:= by
  rw [bI2]
  simp
theorem proof :qXuDJRd.c1 := by
  intro f g hf hg T hT a n
  obtain ⟨J,hJ⟩:=exists_J hf hg hT
  have e1 :qXuDJRd.capHilbert T a 1 n=zsE GeoField
      ((restrictSupport GeoField ((n:ℕ)•aCt (a.scale 2) 1)).map
        (zvR GeoField T).toLinearMap) :=
    finrank_quotientDegreeLE_comap (zero_mem_box _ 1) T n
  have e0:qXuDJRd.capHilbert T a 0 n=zsE GeoField
      ((restrictSupport GeoField ((n:ℕ)•aCt (a.scale 2) 0)).map
        (zvR GeoField T).toLinearMap) :=
    finrank_quotientDegreeLE_comap (zero_mem_box _ 0) T n
  rw [e1,e0,nsmul_box]
  exact hilbert_cyl T J hJ _ (nsmul_box0 _ n) (bqc _ n) n
end
end qKvzzcc
end
