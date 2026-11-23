import ProximityPrize.SubmissionLower.ZJHC8Rc
import ProximityPrize.SubmissionLower.ZyePCwc
import ProximityPrize.SubmissionLower.Z66HSdc
set_option Elab.async false
open _root_ renaming Field → zrb, Fin.lastCases → zsB, Fin.lastCases_castSucc → zwu, Fin.lastCases_last → zTz, Fin.snoc_castSucc → zDN, Fin.snoc_last → zrK, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.map → zDK, Nat.add_le_add_right → zlr, Nat.le_add_left → zmL, Nat.le_add_right → z8K, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf
section
set_option autoImplicit true
namespace qOZqUid
noncomputable section
open P6_6 P6_6_7 P6_6_7_3
open aR (Shape af aO shape)
open dN (GeoJets kC oA bC)
open GJ (vE bf6 Ux)
open lB (bF abr amo Tn)
open ap7
open UH (gQ Su Rh BP)
open private dgn dgo dew from ProximityPrize.SubmissionLower.AG
open private gEF from ProximityPrize.SubmissionLower.K
open private literal_chamber join_chamber weighted_chamber from ProximityPrize.SubmissionLower.ZJHC8Rc
open private iU taylor_simplex from ProximityPrize.SubmissionLower.Z66HSdc
open private c5M cAI b4b b4c from ProximityPrize.SubmissionLower.B5
open scoped BigOperators
theorem sum_budget
    (bezout : ∀ (k :Type) [zrb k] (P:Fin 4→Shape) (f :Fin 4→ gQ k),
      3*(P 0).t≤(P 0).j→(∀ i:Fin 3,bF (P i.succ)) →
      (∀ i,aJ9 (f i) (P i))→zAa k (Rh f) →
      (32 :ℤ)*zsE k (Rh f) ≤
        wP (P 0) (P 1) (P 2) (P 3)) :
    P6_6_7_3.c3:= by
  have degree {R G:af 4} {r q a h:Shape}
      (hR:Irreducible R) (hG : ¬ R∣G) (hr :3*r.t≤ r.j)
      (hq:bF q) (ha :vE a) (hh:vE h)
      (hbR:aO (shape R) r) (hbG:aO (shape G) q)
      (zs :Finset (znc GeoJets)) (v :znc GeoJets→ℕ)
      (hzs : ∀ z∈zs,∃ hz : (kC R G).IsMinimalPrime z,
        oA (kC R G) z hz.isPrime=(v z :ℕ∞)) :
      (32 :ℤ)*(↑(∑ z∈zs,v z*Ux z (a.scale 6) (h.scale 6)) :ℤ) ≤
        36*wP r q a h:= by
    let A:=a.scale 6
    let H :=h.scale 6
    let J:=kC R G
    have hA:=b4c ha (by decide :0<6)
    have hH :=b4c hh (by decide :0<6)
    have hf :=cyh.proof J A H hA hH
      (fun z hz=>(bf6 (agr hR.ne_zero) (amo _ _ hR hG) hz).le)
    have hc:=aY2.proof J A H hA hH hf zs v hzs
    let P:Fin 4→Shape := ![r,q,A,H]
    let f :Fin 4→ gQ (GJ.VM A H) :=
      ![EG A H (bC R),EG A H (bC G),
        a4d A H,a8j A H]
    have hch (i:Fin 3) :bF (P i.succ) := by
      fin_cases i
      · exact hq
      · exact hA.1
      · exact hH.1
    have hs (i:Fin 4) :aJ9 (f i) (P i) := by
      fin_cases i
      · exact dgn (abr hbR) _ _
      · exact dgn (abr hbG) _ _
      · exact dgo _ _
      · exact dgo _ _
    have he :Su f=J.map (EG A H) ⊔ Ideal.span {a4d A H,a8j A H} := by
      dsimp only [f]
      rw [gEF]
      exact (dew _ _ A H).symm
    have hf' : zAa (GJ.VM A H) (Rh f) := by
      change zAa _ (ae9 A H ⧸ Su f)
      rw [he]
      exact hf
    have hd:=bezout _ P f hr hch hs hf'
    change 32*(↑(zsE (GJ.VM A H)
      (ae9 A H ⧸ Su f)) :ℤ) ≤
      wP r q (a.scale 6) (h.scale 6) at hd
    rw [he] at hd
    have hm:wP r q (a.scale 6) (h.scale 6)=36*wP r q a h:= by
      simpa [Shape.scale] using bNV r q a h 1 1 6 6
    rw [hm] at hd
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by decide : (0:ℤ)≤32)).trans hd
  classical
  intro C R G ell cs input zs v F
  dsimp only
  intro data h hh
  let p:=chartBody C R cs
  let r :=firstSlot C R cs
  let q:=cutterBody C ell
  let b:=commonBody C R ell cs
  let m:=max ell (topBound C R cs)
  let a :=p.plus b
  have hp:vE p:= by
    obtain ⟨γ,hγ⟩:=C.nonempty
    obtain ⟨i,hi⟩: (chartIndices C cs).Nonempty := by
      cases cs with
      | union l =>
        obtain ⟨i,hi,_⟩:=C.marks.Eh γ hγ
        exact ⟨i,hi⟩
      | own i=>exact ⟨i,Finset.mem_singleton_self _⟩
    exact ⟨iU,(C.marks.factors i (charter input hi)).2.1.trans_le
      ((bW2 input).2 i hi).2.2⟩
  have hq:bF q:=literal_chamber _
  have hb:bF b:=join_chamber (by
    cases cs
    · exact literal_chamber _
    · exact Tn R) hq
  have ha :vE a :=b4b hp hb
  have hhr :3*r.t≤ r.j:= by
    cases cs <;> exact input.factor.2.1.2.1
  have hR:aO (shape R) r := by
    cases cs with
    | union l=>exact ⟨le_rfl,le_rfl,le_rfl⟩
    | own i=>exact first_fits input
  have hh' : vE h:= by
    rcases hh with he | he
    · exact he.symm ▸ ⟨weighted_chamber _ _,(taylor_simplex (by decide) p).2.2⟩
    · exact he.symm ▸ hp
  let E (z :znc GeoJets) :=Ux z (p.scale 6) (h.scale 6)
  let B (z :znc GeoJets) :=Ux z (a.scale 6) (h.scale 6)
  let w (z :znc GeoJets) :=ell*genericOrder R z
  have point (z :znc GeoJets) (hz :z∈zs) :
      6*(w z*an0 h z (F z))≤v z*B z+(2*m)*(v z*E z) := by
    obtain ⟨⟨hZ,_⟩,hw,hF,hbF⟩:=data z hz
    have hdim:=bf6 (agr input.factor.1.ne_zero)
      (amo R G input.factor.1 input.proper) hZ
    have pla {s :Shape} (hS:vE s) (hFs :aO (shape (F z)) s) :
        6*an0 h z (F z)≤Ux z (s.scale 6) (h.scale 6) :=
      c5M z _ s h hZ.isPrime hdim hS hh' hF (abr hFs)
    rcases hbF with hfit | ⟨j,_,hj,hfit⟩
    · have h₀:=pla ha (cDD hfit
        ⟨z8K ..,z8K ..,z8K ..⟩)
      calc
        _=w z*(6*an0 h z (F z)) := by ac_rfl
        _≤w z*B z :=zBI _ h₀
        _≤_:=(ztf _ hw).trans (z8K ..)
    · have h₀:=pla (b4b ha (BP hp.1 (2*j)))
        (cDD hfit ⟨zlr (zmL ..) _,zlr (zmL ..) _,
          zlr (zmL ..) _⟩)
      have h₁:=cAI z a p h 1 (2*j) hZ.isPrime hdim ha hp hh' (by decide)
      have hs : (a.scale 1)=a := by cases a; simp [Shape.scale]
      rw [hs,one_mul] at h₁
      calc
        _=w z*(6*an0 h z (F z)) := by ac_rfl
        _≤w z*(B z+(2*j)*E z) :=zBI _ (h₀.trans h₁)
        _=w z*B z+(2*(w z*j))*E z := by ring
        _≤v z*B z+(2*(m*v z))*E z :=
          Nat.add_le_add (ztf _ hw)
            (ztf _ (zBI _ hj))
        _ = _:= by ring
  have hsum:6*(∑ z∈zs,w z*an0 h z (F z)) ≤
      (∑ z∈zs,v z*B z)+(2*m)*(∑ z∈zs,v z*E z) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum point
  have hbase :=degree input.factor.1 input.proper hhr hq ha hh' hR input.H6
    zs v (fun z hz=>(data z hz).1)
  have hextra :=degree input.factor.1 input.proper hhr hq hp hh' hR input.H6
    zs v (fun z hz=>(data z hz).1)
  have hbZ: (6:ℤ)*(↑(∑ z∈zs,w z*an0 h z (F z)) :ℤ) ≤
      (↑(∑ z∈zs,v z*B z) :ℤ)+2*(m:ℤ)*(↑(∑ z∈zs,v z*E z) :ℤ) := by
    exact_mod_cast hsum
  change _≤6*(wP r q p h+wP r q b h +
    2*(m:ℤ)*wP r q p h)
  change 32*(↑(∑ z∈zs,v z*B z) :ℤ)≤_ at hbase
  change 32*(↑(∑ z∈zs,v z*E z) :ℤ)≤_ at hextra
  change 36*(wP r q (p.plus b) h)≥_ at hbase
  rw [mixed_third] at hbase
  have hmul :=mul_le_mul_of_nonneg_left hextra (show 0≤2*(m:ℤ) by positivity)
  nlinarith only [hbZ,hbase,hmul]
end
end qOZqUid
end
section
set_option autoImplicit true
namespace qOZqUid
noncomputable section
open aR (Shape)
open UH
open akO (mo b4E)
open abG (cC2)
open private bGF from ProximityPrize.SubmissionLower.BG
open MvPolynomial
open scoped TensorProduct nonZeroDivisors
private abbrev Idx (P:Fin 4→Shape) :=Σ i:Fin 4,lattice (P i)
private def coeffLift (k :Type) [zrb k] {T P:Fin 4→Shape} {d:Shape}
    (ι:Idx T ↪ Coeff P d) :fZ k T →+* CommonField k P d :=
  IsFractionRing.lift
    (g:=(algebraMap (jo k P d) (CommonField k P d)).comp (rename ι).toRingHom)
    ((IsFractionRing.injective (jo k P d) (CommonField k P d)).comp
      (MvPolynomial.rename_injective ι ι.injective))
private theorem map_row (k :Type) [zrb k] {T P:Fin 4→Shape} {d:Shape}
    (ι:Idx T ↪ Coeff P d) (i:Fin 4) :
    zDK (coeffLift k ι) (ve k T i) =
      row k P d (T i) (fun a=>ι ⟨i,a⟩) := by
  simp only [ve,row,map_sum,map_monomial,coeffLift,
    IsFractionRing.lift_algebraMap,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom,rename_X]
private theorem transported (k :Type) [zrb k] {T P:Fin 4→Shape} {d:Shape}
    (ι:Idx T ↪ Coeff P d) :
    let f := fun i=>row k P d (T i) (fun a=>ι ⟨i,a⟩)
    zAa (CommonField k P d) (Rh f) ∧
      zsE (CommonField k P d) (Rh f)=rank k T:= by
  dsimp only
  let:=(coeffLift k ι).toAlgebra
  let:=b4E k T
  have H :=bGF (L:=CommonField k P d) (Su (ve k T))
  have he : (Su (ve k T)).map
      (zDK (algebraMap (fZ k T) (CommonField k P d))) =
      Su (fun i=>row k P d (T i) (fun a=>ι ⟨i,a⟩)) := by
    change (Su (ve k T)).map (zDK (coeffLift k ι))= _
    rw [Ideal.map_span,← Set.range_comp']
    simp only [map_row]
  rw [he] at H
  exact H
theorem literal_rank (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :
    zAa (CommonField k P d) (Rh (literalTuple k P d)) ∧
      zsE (CommonField k P d) (Rh (literalTuple k P d))=rank k P :=
  transported (T:=P) (P:=P) (d:=d) k ⟨Sum.inr,Sum.inr_injective⟩
abbrev padLast (P:Fin 4→Shape) (d:Shape) :Fin 4→Shape :=
  Fin.snoc (α:= fun _=>Shape) (fun i:Fin 3=>P i.succ) d
private def castCap {p q:Shape} (h:p=q) (a :lattice p) :lattice q :=
  ⟨a.val,h ▸ a.property⟩
private theorem row_cast (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape)
    {p q:Shape} (h:p=q) (ι:lattice q→ Coeff P d) :
    row k P d p (fun a=>ι (castCap h a))=row k P d q ι:= by
  subst q
  rfl
private def padIndex {P:Fin 4→Shape} {d:Shape} :
    ∀ i:Fin 4,lattice (padLast P d i)→ Coeff P d :=
  zsB (motive := fun i=>lattice (padLast P d i)→ Coeff P d)
    (fun a=>Sum.inl (castCap (zrK ..) a))
    (fun i a=>Sum.inr ⟨i.succ,castCap (zDN ..) a⟩)
private def padEmbedding (P:Fin 4→Shape) (d:Shape) :
    Idx (padLast P d) ↪ Coeff P d where
  toFun v :=padIndex v.1 v.2
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    change padIndex i a=padIndex j b at h
    revert a b h
    induction i using zsB <;> induction j using zsB <;>
      simp only [padIndex,zTz,zwu] <;>
      intros a b h
    · congr 1
      exact Subtype.ext (congrArg Subtype.val (Sum.inl.inj h))
    · exact (Sum.inl_ne_inr h).elim
    · exact (Sum.inr_ne_inl h).elim
    · obtain ⟨h,e⟩:=Sigma.mk.inj (Sum.inr.inj h)
      obtain rfl :=Fin.succ_injective _ h
      congr 1
      have hv :=congrArg Subtype.val (eq_of_heq e)
      exact Subtype.ext hv
private abbrev paddedLast (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :=
  fun i=>row k P d (padLast P d i) (fun a=>padIndex i a)
private theorem padLast_last (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :
    paddedLast k P d (Fin.last 3)=extraRow k P d:= by
  unfold paddedLast padIndex
  rw [zTz]
  exact row_cast k P d (zrK ..) Sum.inl
private theorem padLast_tail (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) (i:Fin 3) :
    paddedLast k P d i.castSucc=literalTuple k P d i.succ:= by
  unfold paddedLast padIndex
  rw [zwu]
  exact row_cast k P d (zDN ..) (fun a=>Sum.inr ⟨i.succ,a⟩)
theorem pad_rank (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :
    zAa (CommonField k P d) (Rh (padTuple k P d)) ∧
      zsE (CommonField k P d) (Rh (padTuple k P d)) =
        rank k (padLast P d) := by
  have h:=transported k (padEmbedding P d)
  have hf :paddedLast k P d=Fin.snoc (fun i:Fin 3=>literalTuple k P d i.succ)
      (extraRow k P d) := by
    funext i
    induction i using zsB
    · rw [zrK,padLast_last]
    · rw [zDN,padLast_tail]
  have eq :Su (paddedLast k P d)=Su (padTuple k P d) := by
    rw [replaceIdeal,← Ideal.span_union,Set.union_singleton,← Fin.range_snoc,← hf]
  change zAa _ (gQ _ ⧸ Su (paddedLast k P d)) ∧
    zsE _ (gQ _ ⧸ Su (paddedLast k P d))= _ at h
  let L:=CommonField k P d
  let form (J:znc (gQ L)) :=
    zAa L (gQ L ⧸ J)∧zsE L (gQ L ⧸ J)=rank k (padLast P d)
  exact (congrArg form eq).mp h
set_option maxHeartbeats 400000 in
private theorem transport_regular {K L:Type} [zrb K] [zrb L] [Algebra K L]
    (I:znc (gQ K)) (g:gQ K)
    (hr :zq4 (fun x :gQ K ⧸ I=>zVv I g*x)) :
    let f :=zDK (σ:=Fin 4) (algebraMap K L)
    zVv (I.map f) (f g)∈(gQ L ⧸ I.map f)⁰:= by
  intro f
  let A:=gQ K ⧸ I
  let B:=gQ L ⧸ I.map f
  let e :L ⊗[K] A ≃ₐ[L] B:=cC2 I
  let m:=LinearMap.mul K A (zVv I g)
  have hm:zq4 (m.baseChange L) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M:=L) m hr
  have he (p:gQ K) :e (1 ⊗ₜ[K] (zVv I p)) =
      zVv (I.map f) (f p) := by
    unfold e cC2
    rw [AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
      Ideal.quotientEquivAlg_mk,MvPolynomial.algebraTensorAlgEquiv_tmul,one_smul]
  have hn (z :L ⊗[K] A) :e (m.baseChange L z) =
      zVv (I.map f) (f g)*e z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy=>rw [map_add,map_add,hx,hy,map_add,mul_add]
    | tmul l x =>
      obtain ⟨a,rfl⟩:=zld x
      rw [TensorProduct.tmul_eq_smul_one_tmul,map_smul,map_smul,map_smul,
        LinearMap.baseChange_tmul]
      change l•e (1 ⊗ₜ[K] (zVv I g* zVv I a))= _
      rw [← map_mul,he,he,map_mul,map_mul]
      exact (Algebra.mul_smul_comm l _ _).symm
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  have h:=hn (e.symm x)
  rw [e.apply_symm_apply,hx,← map_zero e,← (m.baseChange L).map_zero] at h
  have hz :=hm (e.injective h)
  simpa using congrArg e hz
theorem pad_regular (k :Type) [zrb k] (P:Fin 4→Shape) (d:Shape) :
    zVv (tailIdeal (literalTuple k P d)) (extraRow k P d) ∈
      (gQ (CommonField k P d) ⧸ tailIdeal (literalTuple k P d))⁰:= by
  let T:=padLast P d
  let L:=CommonField k P d
  let K:=fZ k T
  let:Algebra K L:=(coeffLift k (padEmbedding P d)).toAlgebra
  let I:=mo k T 3
  let g:=ve k T (Fin.last 3)
  let f :=zDK (σ:=Fin 4) (algebraMap K L)
  have hrow (i:Fin 4) :f (ve k T i)=paddedLast k P d i :=
    map_row k (padEmbedding P d) i
  have hI:I.map f=tailIdeal (literalTuple k P d) := by
    unfold I mo
    rw [Ideal.map_span,Set.image_image,← Fin.range_castSucc,← Set.range_comp]
    simp only [hrow]
    change Ideal.span (Set.range (fun i:Fin 3=>paddedLast k P d i.castSucc))= _
    simp only [padLast_tail,tailIdeal]
  have hg:f g=extraRow k P d:=(hrow _).trans (padLast_last k P d)
  have hr :zq4 (fun x :gQ K ⧸ I=>zVv I g*x) := by
    intro x y h
    obtain ⟨a,rfl⟩:=zld x
    obtain ⟨b,rfl⟩:=zld y
    have hm:g*(a - b)∈I:= by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul,map_sub,mul_sub,sub_eq_zero] using h
    have hz :a - b∈I:=cym.proof k T (Fin.last 3) (a - b) hm
    simpa only [map_sub,sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hh:=transport_regular (L:=L) I g hr
  change zVv (I.map f) (f g)∈(gQ L ⧸ I.map f)⁰ at hh
  rwa [hI,hg] at hh
end
end qOZqUid
end
section
set_option autoImplicit true
namespace qOZqUid
noncomputable section
open P6_6 (wP)
open aR (Shape)
open lB (bF)
open ap7 (aJ9)
open UH
open private a8w from ProximityPrize.SubmissionLower.T
private theorem even_bound (k :Type) [zrb k] (Q:Fin 4→Shape)
    (ht:3*(Q 0).t≤(Q 0).j) (hc : ∀ i:Fin 3,bF (Q i.succ))
    (he : ∀ i,Even (Q i).j∧Even (Q i).t) :
    (32 :ℤ)*rank k Q≤wP (Q 0) (Q 1) (Q 2) (Q 3) := by
  let d:Shape :=⟨(Q 0).j,0,0⟩
  let L:=CommonField k Q d
  let f :=literalTuple k Q d
  let g:=extraRow k Q d
  let p:=(Q 0).plus d
  let T:=replaceFirst p Q
  let u:=replaceFirst (f 0*g) f
  have hh:bF p∧Even p.j∧Even p.t:= by
    exact ⟨⟨zmL _ _,ht⟩,(he 0).1,(he 0).2⟩
  have hd:bF d∧Even d.j∧Even d.t :=
    ⟨⟨Nat.zero_le _,le_rfl⟩,Even.zero,Even.zero⟩
  have hT (i:Fin 4) :bF (T i)∧Even (T i).j∧Even (T i).t :=
    Fin.cases hh (fun j=>⟨hc j,he j.succ⟩) i
  have hpad (i:Fin 4) :
      bF (padLast Q d i)∧Even (padLast Q d i).j∧Even (padLast Q d i).t:= by
    induction i using zsB
    · simpa only [padLast,zrK] using hd
    · simpa only [padLast,zDN] using And.intro (hc _) (he _)
  have hf :=literal_rank k Q d
  have hg:=pad_rank k Q d
  have hprod:=eOZ f g hf.1 hg.1 (pad_regular k Q d)
  have hs (i:Fin 4) :aJ9 (u i) (T i) :=
    Fin.cases (mul_support (bvn k Q d (Q 0) _) (bvn k Q d d _))
      (fun j=>bvn k Q d (Q j.succ) _) i
  have area :=compare_rank L T u hs hprod.1
  rw [hprod.2,hf.2,hg.2] at area
  have hm:=chamber_rank L T hT
  change _=wP p (Q 1) (Q 2) (Q 3) at hm
  have hb:=chamber_rank k (padLast Q d) hpad
  change _=wP (Q 1) (Q 2) (Q 3) d at hb
  have hb' : (32 :ℤ)*rank k (padLast Q d)=wP d (Q 1) (Q 2) (Q 3) :=
    hb.trans (a8w d (Q 1) (Q 2) (Q 3)).symm
  change _=wP ((Q 0).plus d) (Q 1) (Q 2) (Q 3) at hm
  rw [mixed_add] at hm
  have hz : (↑(rank k Q) :ℤ)+rank k (padLast Q d)≤ rank L T:= by exact_mod_cast area
  linarith only [hm,hb',hz]
private theorem literal_bezout (k :Type) [zrb k] (P:Fin 4→Shape) (f :Fin 4→ gQ k)
    (ht:3*(P 0).t≤(P 0).j) (hc : ∀ i:Fin 3,bF (P i.succ))
    (hs : ∀ i,aJ9 (f i) (P i)) (hf :zAa k (Rh f)) :
    (32 :ℤ)*zsE k (Rh f)≤wP (P 0) (P 1) (P 2) (P 3) := by
  let Q:= fun i=>(P i).scale 2
  have hsp (i:Fin 4) :aJ9 ((f i)^2) (Q i) := by
    have he :Q i=(P i).plus (P i) := by simp [Q,Shape.plus,Shape.scale,two_mul]
    rw [pow_two,he]
    exact mul_support (hs i) (hs i)
  obtain ⟨hv,hl⟩:=aA4.of_children
    cyi.proof cyj.proof k f hf
  have hb:=compare_rank k Q (fun i=>f i^2) hsp hv
  rw [hl] at hb
  have htop:3*(Q 0).t≤(Q 0).j:= by
    simpa only [Q,Shape.scale,Nat.mul_left_comm 3 2] using zBI 2 ht
  have hm:=even_bound k Q htop (fun i=>BP (hc i) 2)
    (fun i=>⟨⟨(P i).j,by simp [Q,Shape.scale,two_mul]⟩,
      ⟨(P i).t,by simp [Q,Shape.scale,two_mul]⟩⟩)
  change _≤wP ((P 0).scale 2) ((P 1).scale 2) ((P 2).scale 2) ((P 3).scale 2) at hm
  rw [bNV] at hm
  change _≤16*wP (P 0) (P 1) (P 2) (P 3) at hm
  have hz : (16:ℤ)*zsE k (Rh f)≤ rank k Q:= by exact_mod_cast hb
  linarith only [hm,hz]
theorem proof :P6_6_7_3.c3:=sum_budget literal_bezout
end
end qOZqUid
end
