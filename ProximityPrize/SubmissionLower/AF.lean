import ProximityPrize.SubmissionLower.T
import ProximityPrize.SubmissionLower.U
set_option Elab.async false
open _root_ renaming AddMonoidAlgebra.mapAlgHom→v9,AddMonoidAlgebra.mapAlgHom_single→Dz,AddMonoidAlgebra.single→ oY,AddMonoidAlgebra.single_mul_single→Du,AlgHom.comp_apply→uh,Algebra→nI,Algebra.FiniteType→xL,Algebra.IsAlgebraic→G5,Algebra.adjoin→Cy,Algebra.algebraMap→lJ,Algebra.smul_def→x7,Algebra.subset_adjoin→Aa,Algebra.trdeg→qJ,AlgebraicIndependent→yB,Cardinal.mk_fintype→FV,CommRing→mD,CommSemiring→yQ,DFunLike.congr_fun→vk,Equiv.optionSubtypeNe→G6,Field→ oD,Fin.castSucc_ne_last→G8,Fin.sum_univ_eq_sum_range→GY,Finset.attach_eq_univ→ IT,Finset.range→ oZ,Finset.sum_attach→zg,Finset.sum_congr→pC,Finset.sum_le_sum→zk,Finset.univ→zS,Finsupp.degree_eq_sum→EP,Finsupp.prod→Bf,Finsupp.single→t9,Finsupp.single_apply→HZ,Finsupp.weight→ oy,Finsupp.weight_apply→Ef,Finsupp.weight_eq_sum→C9,Finsupp.weight_single→th,Fintype→p6,Fintype.card→sH,Fintype.card_congr→Gi,Fintype.ofFinite→zm,Fintype.sum_sum_type→GF,FractionRing→qz,Function.Injective→t4,Function.Surjective→ In,Ideal→c9,Ideal.Quotient.mk→ ov,Ideal.Quotient.mk_surjective→G7
open _root_ renaming Ideal.Quotient.mkₐ→C4,Ideal.Quotient.mkₐ_eq_mk→u8,Ideal.comap_comap→G2,Ideal.comap_map_of_bijective→wB,Ideal.map_map→uJ,Ideal.mem_comap→t6,Ideal.mem_homogeneousCore_of_homogeneous_of_mem→Fa,Ideal.mem_sup_left→FK,Ideal.span→pL,Ideal.subset_span→v8,Ideal.toIdeal_homogeneousCore_le→EK,IsDomain→yL,IsFractionRing.injective→y5,IsLocalization→xm,IsLocalization.Away.liftAlgHom→wR,IsLocalization.Away.lift_eq→Gr,IsLocalization.mk'→ IU,IsLocalization.mk'_mem_map_algebraMap_iff→FR,IsNoetherian.noetherian→FQ,IsScalarTower→vl,IsScalarTower.toAlgHom→wA,LinearMap.comp_apply→Hw,LinearMap.mulLeft_apply→zc,Localization.AtPrime→G4,Localization.Away→t7,MvPolynomial→cy,MvPolynomial.IsWeightedHomogeneous.mul→xu,MvPolynomial.X→lV,MvPolynomial.algebraMap_eq→qx,MvPolynomial.cappedDegreeExponents→ze,MvPolynomial.commAlgEquiv→vG,MvPolynomial.eval→t8,MvPolynomial.eval₂→Gk,MvPolynomial.induction_on'→zi,MvPolynomial.isLocalization→Et,MvPolynomial.isWeightedHomogeneous_monomial→yo,MvPolynomial.ker_map→F9,MvPolynomial.map→nq,MvPolynomial.map_C→yJ,MvPolynomial.map_X→uW,MvPolynomial.map_map→Dv,MvPolynomial.map_monomial→Fz,MvPolynomial.monomial→ oq,MvPolynomial.renameEquiv_apply→C5,MvPolynomial.ringHom_ext→u9,MvPolynomial.weightedHomogeneousComponent→t3,MvPolynomial.weightedHomogeneousComponent_eq_self→G1,MvPolynomial.weightedHomogeneousComponent_mem→GB
open _root_ renaming MvPolynomial.weightedHomogeneousComponent_mem_of_mem→Dw,MvPolynomial.weightedHomogeneousComponent_of_mem→vw,Nat.add_sub_cancel→Df,Nat.card_coe_set_eq→FU,Nat.card_eq_fintype_card→G0,Nat.mul_le_mul_right→ Iw,Order.krullDim_eq_iSup_length→Eg,Polynomial.mapRingHom→z8,PrimeSpectrum→p9,RingHom.comap_ker→zf,RingHom.comp_assoc→ II,RingHom.ker→pz,RingHom.ker_isPrime→G3,RingHom.mem_ker→Au,Set.mem_range_self→Gn,Set.mem_singleton_iff→ Il,Submodule.sum_mem→Ar,Submonoid.mem_powers→zh,Subtype.ext→p7,Subtype.val→qM,Subtype.val_injective→yU,Sum.elim→sS,Sum.elim_inl→u5,Sum.elim_inr→vj,Sum.inl→nX,Sum.inr→n5,YU.Coeff→ ox,YU.leftMul→qy,YU.leftSection→xW,YU.rightMul→qU,YU.rightSection→vZ,aR.Shape→aU,aR.Shape.plus→xI,aR.Shape.scale→vH,aR.shape→p5,add_assoc→yl,congrArg→ oz,dN.GeoField→lz,dN.GeoJets→lI,dN.separant→pQ,faithfulSMul_iff_algebraMap_injective→Gj,le_antisymm→zE,le_max_left→Ea,map_add→pU,map_mul→ oj,map_one→vh
open _root_ renaming map_sum→pG,map_zero→qG,mul_assoc→t5,mul_comm→qm,mul_one→uz,nonZeroDivisors→z7,not_le_of_gt→z9,ringKrullDim→sI,smul_eq_mul→Av,trdeg_add_eq→zd
set_option autoImplicit true
section
namespace akN
noncomputable section
open aR dN BO GJ E6 YU
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
abbrev Generator (a h:aU) :=nE a ⊕ nE h
abbrev am2 (a h:aU) :=cy (Generator a h) (ox a h)
def weight {α β:Type} : α ⊕ β→ℕ×ℕ:=sS (fun _=>(1,0)) (fun _=>(0,1))
abbrev cV {k α β:Type} [yQ k] (d:ℕ×ℕ) :
  Submodule k (cy (α ⊕ β) k) :=
 weightedHomogeneousSubmodule k weight d
def aod {a h:aU} : Generator a h→Fin 4 →₀ ℕ :=
 sS qM qM
def ew (aI:c9 lI) (a h:aU) :
    am2 a h →ₐ[ox a h] Oa aI a h :=
  (C4 _ _).comp (aeval fun v=>oq (aod v) 1)
def relations (aI:c9 lI) (a h:aU) :c9 (am2 a h) :=
 ((pz (ew aI a h).toRingHom).homogeneousCore cV).toIdeal
def afh {p:aU} (m:uL p) :Fin 4 →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm (fun i=>(m i).val)
theorem aTj (p:aU) (m:Bz (p.scale 6)) :
  afh m.val∈nE p:= by
 change (fun i=>afh m.val i)∈rU (p.scale 6)
 simpa only [afh,Finsupp.coe_equivFunOnFinite_symm] using
  (bI6 _ m.val).2 m.property
def avm (a h:aU) :am2 a h :=
  ∑ m∈(Bz (a.scale 6)).attach,
    C (lJ
        (cy (aav (a.scale 6) (h.scale 6)) lz) (ox a h)
        (lV (nX m.val))) *
      lV (nX ⟨afh m.val,aTj a m⟩)
def asa (a h:aU) :am2 a h :=
  ∑ m∈(Bz (h.scale 6)).attach,
    C (lJ
        (cy (aav (a.scale 6) (h.scale 6)) lz) (ox a h)
        (lV (n5 m.val))) *
      lV (n5 ⟨afh m.val,aTj h m⟩)
def ajA (aI:c9 lI) (a h:aU) :c9 (am2 a h) :=
 relations aI a h ⊔ pL {avm a h}
def bY {k α β:Type} [yQ k] (x :α) (y :β) :
    cy (α ⊕ β) k :=
  lV (nX x)*lV (n5 y)
end
end akN
end
section
namespace anb
noncomputable section
open aR dN BO GJ E6
 YU akN ap6 MvPolynomial
abbrev tu (aI:c9 lI) :=lI ⧸ aI
abbrev FunctionField (aI:c9 lI) :=qz (tu aI)
def ahS (aI:c9 lI) (x :Fin 4 →₀ ℕ) :tu aI :=
 ov aI (oq x 1)
def ZU (aI:c9 lI) (x :Fin 4 →₀ ℕ) :FunctionField aI :=
 lJ (tu aI) (FunctionField aI) (ahS aI x)
def alG (aI:c9 lI) [aI.IsPrime] (a h:aU)
    (e :nE a×nE h) :Generator a h→FunctionField aI :=
  sS (fun x=>ZU aI x.val/ZU aI e.1.val)
    (fun y=>ZU aI y.val/ZU aI e.2.val)
def adp (aI:c9 lI) [aI.IsPrime] (a h:aU)
    (e :nE a×nE h) :Subalgebra lz (FunctionField aI) :=
  Cy lz (Set.range (alG aI a h e))
instance (aI:c9 lI) [aI.IsPrime] (a h:aU)
  (e :nE a×nE h) :xL lz (adp aI a h e) :=
 Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
def bcn (aI:c9 lI) [aI.IsPrime] (a h:aU)
    (e :nE a×nE h) (i:Generator a h) :adp aI a h e :=
  ⟨alG aI a h e i,Aa ⟨i,rfl⟩⟩
def aRh (p:aU) :nE p:=⟨0,brA p⟩
def aEK (p:aU) (m:Bz (p.scale 6)) :nE p :=
 ⟨afh m.val,aTj p m⟩
def buJ {k :Type} [oD k] (I:c9 (cy (Fin 4) k)) (a h:aU)
    (e :nE a×nE h)
    {E :Type} [oD E] [nI k E] (φ:yH I a h →ₐ[k] E) :
    Generator a h→E :=
  sS
    (fun x=>φ (aaX I a h x) /
      φ (aaX I a h e.1))
    (fun y=>φ (abh I a h y) /
      φ (abh I a h e.2))
end
end anb
end
section
namespace akN
noncomputable section
open aR dN BO lB GJ E6 YU
open MvPolynomial
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem bIm (a h:aU) :avm a h∈cV (1,0) := by
 apply Ar
 intro m _
 exact (isWeightedHomogeneous_X (ox a h) weight
  (nX ⟨afh m.val,aTj a m⟩:Generator a h)).C_mul _
theorem cfs (a h:aU) :asa a h∈cV (0,1) := by
 apply Ar
 intro m _
 exact (isWeightedHomogeneous_X (ox a h) weight
  (n5 ⟨afh m.val,aTj h m⟩:Generator a h)).C_mul _
private theorem cDB {k :Type} [mD k] {p:aU} (m:uL p) :
   (∏ i:Fin 4,(lV i:cy (Fin 4) k)^(m i).val) =
     oq (afh m) 1 := by
 have he :Finsupp.indicator zS (fun i _=>(m i).val)=afh m:= by
   ext i
   simp [Finsupp.indicator_apply,afh]
 rw [prod_X_pow,he]
theorem cKc (aI:c9 lI) (a h:aU) :
  ew aI a h (avm a h) =
   ov (gN aI a h) (xW a h) := by
 unfold avm xW Uq ew
 simp only [uh,pG,oj,aeval_C,aeval_X,
  aod,u5 ,qx ,cDB,u8]
 exact zg (Bz (a.scale 6)) fun m =>
  ov (gN aI a h) (C (lJ
   (cy (aav (a.scale 6) (h.scale 6)) lz) (ox a h)
   (lV (nX m)))) *
  ov (gN aI a h) (oq (afh m) 1)
theorem cKg (aI:c9 lI) (a h:aU) :
  ew aI a h (asa a h) =
   ov (gN aI a h) (vZ a h) := by
 unfold asa vZ Uq ew
 simp only [uh,pG,oj,aeval_C,aeval_X,
  aod,vj,qx ,cDB,u8]
 exact zg (Bz (h.scale 6)) fun m =>
  ov (gN aI a h) (C (lJ
   (cy (aav (a.scale 6) (h.scale 6)) lz) (ox a h)
   (lV (n5 m)))) *
  ov (gN aI a h) (oq (afh m) 1)
theorem c8a (aI:c9 lI) (a h:aU) :
   (relations aI a h).IsHomogeneous cV :=
 ((pz (ew aI a h).toRingHom).homogeneousCore cV).isHomogeneous
theorem dVM {aI:c9 lI} {a h:aU}
  {f :am2 a h} (hf :f∈relations aI a h) :
  ew aI a h f=0 :=
 EK cV _ hf
theorem eAe {aI:c9 lI} {a h:aU}
  {d:ℕ×ℕ} {f :am2 a h} (hm:f∈cV d)
  (hf :ew aI a h f=0) :f∈relations aI a h :=
 Fa ⟨d,hm⟩ hf
private def Zs (a h:aU) (d:ℕ×ℕ) :Shape :=
 (a.scale d.1).plus (h.scale d.2)
private theorem cDu (a h:aU) (s t:ℕ×ℕ) :
  Zs a h (s+t)=(Zs a h s).plus (Zs a h t) := by
 cases a
 cases h
 simp [Zs,vH,xI,Nat.add_mul,yl,add_left_comm]
private theorem bBQ {a h:aU} (ha :bF a) (hh:bF h)
  (d:ℕ×ℕ) :bF (Zs a h d) :=
 Nc (E6.BP ha d.1) (E6.BP hh d.2)
private theorem bVV (a h:aU) :
   nE (Zs a h 0) = {0} := by
 have hz :Zs a h 0=⟨0,0,0⟩:= by simp [Zs,vH,xI]
 rw [hz]
 ext e
 change (fun i=>e i)∈rU ⟨0,0,0⟩↔e∈({0} : Set (Fin 4 →₀ ℕ))
 rw [bFF,Il,Il]
 constructor
 · intro he
   ext i
   exact congrFun he i
 · rintro rfl
   rfl
private theorem cDv (a h:aU) :Zs a h (1,0)=a := by
 cases a
 simp [Zs,xI,vH]
private theorem cDw (a h:aU) :Zs a h (0,1)=h:= by
 cases h
 simp [Zs,xI,vH]
private theorem d5l {a h:aU} (ha :bF a) (hh:bF h)
   (d:Generator a h →₀ ℕ) :
   oy aod d∈nE (Zs a h (oy weight d)) := by
 have hplus (u v :ℕ×ℕ) :nE (Zs a h (u+v)) =
     nE (Zs a h u)+nE (Zs a h v) := by
   rw [cDu,a44 (bBQ ha hh _) (bBQ ha hh _)]
 have hgen (v :Generator a h) :aod v∈nE (Zs a h (weight v)) := by
   cases v with
   | inl x=>exact (cDv a h).symm ▸ x.property
   | inr y=>exact (cDw a h).symm ▸ y.property
 induction d using Finsupp.induction_linear with
 | zero=>simp [bVV]
 | add u v hu hv=>simpa only [map_add,hplus] using Set.add_mem_add hu hv
 | single v n =>
   rw [th,th]
   induction n with
   | zero=>simp [bVV]
   | succ n ih=>simpa only [succ_nsmul,hplus] using Set.add_mem_add ih (hgen v)
set_option maxHeartbeats 800000 in
private theorem b2u {a h:aU} (ha :bF a) (hh:bF h)
    (i j:ℕ) {e :Fin 4 →₀ ℕ} (he :e∈nE (Zs a h (i,j))) :
    ∃ d:Generator a h →₀ ℕ,
      oy weight d=(i,j)∧oy aod d=e := by
  have hplus (u v :ℕ×ℕ) :nE (Zs a h (u+v)) =
      nE (Zs a h u)+nE (Zs a h v) := by
    rw [cDu,a44 (bBQ ha hh _) (bBQ ha hh _)]
  induction i generalizing j e with
  | zero =>
    induction j generalizing e with
    | zero =>
      have he' : e=0:=Set.mem_singleton_iff.mp ((bVV a h) ▸ he)
      exact ⟨0,rfl,by simp [he']⟩
    | succ j ih =>
      have hm:e∈nE (Zs a h (0,j))+nE h:= by
        have hsum:=hplus (0,j) (0,1)
        rw [cDw] at hsum
        rw [← hsum]
        exact he
      obtain ⟨u,hu,v,hv,rfl⟩:=hm
      obtain ⟨d,hd,hdu⟩:=ih (e :=u) hu
      refine ⟨d+Finsupp.single (n5 ⟨v,hv⟩) 1,?_,?_⟩
      · (rw [pU,hd,th]; rfl)
      · (rw [pU,hdu,th,one_nsmul]; rfl)
  | succ i ih =>
    have hm:e∈nE (Zs a h (i,j))+nE a := by
      have hsum:=hplus (i,j) (1,0)
      rw [cDv] at hsum
      rw [← hsum]
      exact he
    obtain ⟨u,hu,v,hv,rfl⟩:=hm
    obtain ⟨d,hd,hdu⟩:=ih j (e :=u) hu
    refine ⟨d+Finsupp.single (nX ⟨v,hv⟩) 1,?_,?_⟩
    · (rw [pU,hd,th]; rfl)
    · (rw [pU,hdu,th,one_nsmul]; rfl)
private theorem cKd (aI:c9 lI) (a h:aU)
   (d:Generator a h →₀ ℕ) (c:ox a h) :
   ew aI a h (oq d c) =
     ov (gN aI a h) (oq (oy aod d) c) := by
 unfold ew
 rw [uh,aeval_monomial,Bf ,Ef ,Finsupp.sum]
 simp only [monomial_pow,one_pow,← monomial_sum_one,qx ,
   C_mul_monomial,uz]
 rfl
theorem cKb (aI:c9 lI) {a h:aU} (ha :bF a) (hh:bF h)
   (i j:ℕ) : (cV (i,j)).map (ew aI a h).toLinearMap=AL aI a h i j:= by
 apply zE
 · rintro _ ⟨f,hf,rfl⟩
   change ew aI a h f∈AL aI a h i j
   rw [f.as_sum,pG]
   apply Ar
   intro d hd
   have hweight:oy weight d=(i,j) :=hf (mem_support_iff.mp hd)
   have hexp:=d5l ha hh d
   rw [hweight] at hexp
   rw [cKd]
   refine ⟨_,?_,rfl⟩
   intro e he
   have he' : oy aod d=e := by
     change e∈(oq (oy aod d) (f.coeff d)).support at he
     have hne :=mem_support_iff.mp he
     rw [coeff_monomial] at hne
     split at hne
     next hEq=>exact hEq
     next=>exact (hne rfl).elim
   exact he' ▸ hexp
 · unfold AL dO
   rw [restrictSupport_eq_span,Submodule.map_span,Submodule.span_le]
   rintro _ ⟨_,⟨e,he,rfl⟩,rfl⟩
   obtain ⟨d,hd,hde⟩:=b2u ha hh i j he
   refine ⟨oq d 1,yo _ _ _ hd,?_⟩
   change ew aI a h (oq d 1)= _
   rw [cKd,hde]
   rfl
end
end akN
end
section
namespace anb
noncomputable section
open aR dN BO GJ E6
 YU akN ap6 MvPolynomial
abbrev bz8 (a :aU) :=(Bz (a.scale 6) :Type)
abbrev bAE (h:aU) :=(Bz (h.scale 6) :Type)
abbrev Parameters (a h:aU) :=aav (a.scale 6) (h.scale 6)
def parameter (a h:aU) (i:Parameters a h) :ox a h :=
 lJ (cy (Parameters a h) lz) (ox a h) (lV i)
theorem dcm (p:aU) :In (aEK p) := by
 intro x
 have hx : (fun i=>x.val i)∈rU (p.scale 6) :=x.property
 rw [cNO] at hx
 obtain ⟨m,hm,he⟩:=hx
 refine ⟨⟨m,hm⟩,p7 ?_⟩
 ext i
 exact congrFun he i
private theorem cUS {k ι:Type} [oD k] {I:c9 (cy (Fin 4) k)}
  {a h:aU} (d:ℕ×ℕ) (s :Finset ι) (w:ι→k) (x :ι→Affine I)
  (hx : ∀ i,x i∈box I a h d) (y :Affine I) (hy :y∈box I a h d)
  (heq :y = ∑ i∈s,w i•x i) :
  homogeneous d y hy = ∑ i∈s,w i•homogeneous d (x i) (hx i) := by
 apply p7
 change oY d y=(yH I a h).val _
 rw [pG]
 simp_rw [map_smul,aJW,← AddMonoidAlgebra.lsingle_apply (R:=k),
  ← map_smul,← pG,← heq]
theorem eve (aI:c9 lI) (a h:aU) :
   aOt aI a h = ∑ m:bz8 a,
     parameter a h (nX m.val)•aaX (rT aI a h) a h (aEK a m) := by
 classical
 unfold aOt
 apply cUS (I:=rT aI a h) (a :=a) (h:=h) (d:=(1,0))
 change ov (gN aI a h) (xW a h)= _
 rw [← cKc aI a h]
 simp only [avm,IT,pG,oj,ew,uh,
   aeval_C,aeval_X,aod,u5 ,u8 ,
   qx]
 refine pC rfl fun m _ => ?_
 exact (x7 (parameter a h (nX m.val))
   (ov (gN aI a h) (oq (afh m.val) 1))).symm
theorem fXx (aI:c9 lI) (a h:aU) :
   aPV aI a h = ∑ m:bAE h,
     parameter a h (n5 m.val)•abh (rT aI a h) a h (aEK h m) := by
 classical
 unfold aPV
 apply cUS (I:=rT aI a h) (a :=a) (h:=h) (d:=(0,1))
 change ov (gN aI a h) (vZ a h)= _
 rw [← cKg aI a h]
 simp only [asa,IT,pG,oj,ew,uh,
   aeval_C,aeval_X,aod,vj,u8 ,
   qx]
 refine pC rfl fun m _ => ?_
 exact (x7 (parameter a h (n5 m.val))
   (ov (gN aI a h) (oq (afh m.val) 1))).symm
theorem gqe (aI:c9 lI) (a h:aU) :
  shift (rT aI a h) a h =
    Wi (rT aI a h) a h (aRh a,aRh h) := by
 apply p7
 change oY (1,1) (1 :Oa aI a h) =
  (yH (rT aI a h) a h).val
    (aaX (rT aI a h) a h (aRh a) *
    abh (rT aI a h) a h (aRh h))
 simp only [oj,aaX,abh,aJW,aRh,monomial_zero',vh,
  Du,uz]
 rfl
end
end anb
end
section
namespace anb
noncomputable section
open aR dN E6 YU ap6 MvPolynomial
def bAU (aI:c9 lI) (a h:aU) :
    tu aI →ₐ[lz] Oa aI a h :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId lz (ox a h)))
    Ideal.le_comap_map
private theorem cAU (aI:c9 lI) (a h:aU) (q:lI) :
    bAU aI a h (ov aI q) =
      ov (gN aI a h)
        (nq (lJ lz (ox a h)) q) :=rfl
def bLd (aI:c9 lI) (a h:aU) :
    yH aI a h →ₐ[lz] Rees aI a h:= by
  let f :=bAU aI a h
  let g:=(v9 (ℕ×ℕ) f).comp (yH aI a h).val
  refine g.codRestrict ((yH (rT aI a h) a h).restrictScalars lz) ?_
  intro p d
  change (v9 (ℕ×ℕ) f p.val).coeff d∈_
  rw [AddMonoidAlgebra.coeff_mapAlgHom]
  obtain ⟨q,hq,he⟩:=p.property d
  refine ⟨nq (lJ lz (ox a h)) q,?_,?_⟩
  · intro m hm
    exact hq (support_map_subset _ _ hm)
  · rw [← he]
    rfl
@[simp] theorem gRD (aI:c9 lI) (a h:aU) (x :nE a) :
    bLd aI a h (aaX aI a h x) =
      aaX (rT aI a h) a h x := by
  apply p7
  change v9 (ℕ×ℕ) (bAU aI a h)
    (oY (1,0) (ahS aI x.val))= _
  rw [Dz]
  change oY (1,0) _ =
    oY (1,0) (ov (gN aI a h) (oq x.val 1))
  apply oz (oY (1,0))
  rw [ahS,cAU,Fz ,vh]
@[simp] theorem gRF (aI:c9 lI) (a h:aU) (y :nE h) :
    bLd aI a h (abh aI a h y) =
      abh (rT aI a h) a h y := by
  apply p7
  change v9 (ℕ×ℕ) (bAU aI a h)
    (oY (0,1) (ahS aI y.val))= _
  rw [Dz]
  change oY (0,1) _ =
    oY (0,1) (ov (gN aI a h) (oq y.val 1))
  apply oz (oY (0,1))
  rw [ahS,cAU,Fz ,vh]
@[simp] theorem gRE (aI:c9 lI) (a h:aU)
    (e :nE a×nE h) :
    bLd aI a h (Wi aI a h e) =
      Wi (rT aI a h) a h e := by
  simp [Wi]
end
end anb
end
section
set_option linter.style.haveILetI false
namespace anb
noncomputable section
open dN E6 Algebra
open scoped nonZeroDivisors
theorem bT2 (k A:Type) [oD k] [mD A] [yL A]
   [nI k A] [xL k A] :
   ∃ d:ℕ,sI A=d∧qJ k A=(d:Cardinal) := by
 obtain ⟨d,g,hg,hfin⟩:=exists_finite_inj_algHom_of_fg k A
 let N :=cy (Fin d) k
 letI:nI N A:=g.toRingHom.toAlgebra
 letI:vl k N A:=IsScalarTower.of_algebraMap_eq fun a=>(g.commutes a).symm
 letI:FaithfulSMul N A:=(Gj N A).mpr hg
 letI:Module.Finite N A:=hfin
 letI:Algebra.IsIntegral N A:=Algebra.IsIntegral.of_finite N A
 let p:=PrimeSpectrum.comap (lJ N A)
 have hmono:StrictMono p:= by
   intro x y hxy
   letI:x.asIdeal.IsPrime :=x.2
   exact Ideal.IsIntegral.under_lt_under (R:=N) hxy
 have hdim:sI A=sI N := by
   refine (Order.krullDim_le_of_strictMono p hmono).antisymm ?_
   change Order.krullDim (p9 N)≤Order.krullDim (p9 A)
   rw [Eg ,Eg]
   apply WithBot.coe_le_coe.mpr
   apply iSup_le
   intro l
   obtain ⟨P,hP⟩:=Algebra.IsIntegral.comap_surjective N A l.head
   letI:P.asIdeal.IsPrime :=P.2
   letI:P.asIdeal.LiesOver l.head.asIdeal:=⟨(oz PrimeSpectrum.asIdeal hP).symm⟩
   obtain ⟨L,hL,_,_⟩:=Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
   exact hL ▸ le_iSup (fun L:LTSeries (p9 A)=>(L.length:ℕ∞)) L
 refine ⟨d,?_,?_⟩
 · simp [hdim,N,MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
     ringKrullDim_eq_zero_of_field]
 · letI:G5 N A:=Algebra.IsAlgebraic.of_finite N A
   simpa [N,trdeg_eq_zero (R:=N) (A:=A),Cardinal.mk_fin] using
     (zd (A:=A) k N).symm
theorem dIU (aI:c9 lI) [aI.IsPrime] (a h:aU)
  (e :nE a×nE h)
  (hdim:sI (tu aI)=2) :
  qJ lz (adp aI a h e)≤2 := by
 obtain ⟨d,hd,ht⟩:=bT2 lz (tu aI)
 have hd' : d = 2 := by exact_mod_cast hd.symm.trans hdim
 have hfield :qJ lz (FunctionField aI)=2 := by
  letI:G5 (tu aI) (FunctionField aI) :=
    IsLocalization.isAlgebraic _ (tu aI)⁰
  rw [← zd lz (tu aI) (A:=FunctionField aI),
    trdeg_eq_zero (R:=tu aI) (A:=FunctionField aI),add_zero,ht,hd']
  rfl
 exact (trdeg_le_of_injective (adp aI a h e).val yU).trans hfield.le
end
end anb
end
section
set_option maxHeartbeats 800000
namespace anb
noncomputable section
open aR dN BO GJ E6
 YU ap6 MvPolynomial
def c1 :Prop :=
  ∀ (aI:c9 lI) [aI.IsPrime] (a h:aU)
    (e :nE a×nE h)
    {E :Type} [oD E] [nI lz E]
    (φ:yH aI a h →ₐ[lz] E),φ (Wi aI a h e)≠0 →
    ZU aI e.1.val≠0∧ZU aI e.2.val≠0 ∧
      ∃ f :adp aI a h e →ₐ[lz] E,
        ∀ i,f (bcn aI a h e i)=buJ aI a h e φ i
def c2 :Prop :=
  ∀ {k A E σ τ:Type} [oD k] [mD A] [yL A] [nI k A]
    [xL k A] [oD E] [nI k E] [p6 σ] [p6 τ]
    (t:σ ⊕ τ→E),yB k t →
    qJ k A≤2 →
    ∀ (b:A),b≠0 → ∀ f :A →ₐ[k] E,f b=0 →
    ∀ (i:σ) (j:τ),
    ∀ (u:σ→A) (v :τ→A),u i=1→v j=1 →
    (∑ m,t (nX m)*f (u m))=0 →
    (∑ m,t (n5 m)*f (v m))=0→False
private theorem eER (h1 :c1) (h2 :c2)
    (aI:c9 lI) [aI.IsPrime] (a h:aU)
    (hdim:sI (tu aI)=2) (e :nE a×nE h)
    {E :Type} [oD E] [nI (ox a h) E] [nI lz E]
    [vl lz (ox a h) E]
    (φ:Rees aI a h →ₐ[ox a h] E)
    (hchart:φ (Wi (rT aI a h) a h e)≠0)
    (hleft:φ (aOt aI a h)=0) (hright:φ (aPV aI a h)=0)
    (hshift:φ (shift (rT aI a h) a h)=0) :False := by
  classical
  let ψ:=(φ.restrictScalars lz).comp (bLd aI a h)
  have hψ:ψ (Wi aI a h e)≠0:= by simpa [ψ] using hchart
  obtain ⟨hα,hβ,f,hratio⟩:=h1 aI a h e ψ hψ
  have hcoord (i:akN.Generator a h) :
      f (bcn aI a h e i)=buJ (rT aI a h) a h e φ i:= by
    rw [hratio]
    cases i with
    | inl x =>
      change ψ (aaX aI a h x)/ψ (aaX aI a h e.1) =
        φ (aaX (rT aI a h) a h x)/φ (aaX (rT aI a h) a h e.1)
      simp [ψ]
    | inr y =>
      change ψ (abh aI a h y)/ψ (abh aI a h e.2) =
        φ (abh (rT aI a h) a h y)/φ (abh (rT aI a h) a h e.2)
      simp [ψ]
  let b:=bcn aI a h e (nX (aRh a)) *
    bcn aI a h e (n5 (aRh h))
  have hb:b≠0:= by
    intro hz
    have hzero :ZU aI 0=1 := by simp [ZU,ahS]
    have hv :=oz qM hz
    change (ZU aI 0/ZU aI e.1.val) *
      (ZU aI 0/ZU aI e.2.val)=0 at hv
    rw [hzero] at hv
    exact mul_ne_zero (div_ne_zero one_ne_zero hα) (div_ne_zero one_ne_zero hβ) hv
  have hbzero :f b=0:= by
    dsimp only [b]
    rw [oj,hcoord,hcoord]
    simp only [buJ,u5 ,vj,← mul_div_mul_comm,← oj]
    change φ (Wi (rT aI a h) a h (aRh a,aRh h)) /
      φ (Wi (rT aI a h) a h e)=0
    rw [← gqe,hshift,zero_div]
  let P:=cy (Parameters a h) lz
  let F:=ox a h
  let t (l:bz8 a ⊕ bAE h) :E :=
    lJ F E (parameter a h (Sum.map qM qM l))
  have htFull:yB lz (fun l:Parameters a h =>
      lJ F E (parameter a h l)) :=
    ((algebraicIndependent_X (Parameters a h) lz).map'
      (f :=wA lz P F) (y5 P F)).map'
        (f :=wA lz F E) (lJ F E).injective
  have ht:yB lz t :=
    htFull.comp (Sum.map qM qM)
      (Sum.map_injective.mpr ⟨yU,yU⟩)
  let u (m:bz8 a) :=bcn aI a h e (nX (aEK a m))
  let v (m:bAE h) :=bcn aI a h e (n5 (aEK h m))
  obtain ⟨i,hi⟩:=dcm a e.1
  obtain ⟨j,hj⟩:=dcm h e.2
  have hui:u i=1 := by
    apply p7
    change alG aI a h e (nX (aEK a i))=1
    simp [hi,alG,hα]
  have hvj:v j=1 := by
    apply p7
    change alG aI a h e (n5 (aEK h j))=1
    simp [hj,alG,hβ]
  have hu: (∑ m,t (nX m)*f (u m))=0:= by
    rw [eve] at hleft
    simp only [pG,x7,oj,AlgHom.commutes] at hleft
    calc
      _=(∑ m:bz8 a,t (nX m) *
          φ (aaX (rT aI a h) a h (aEK a m))) /
            φ (aaX (rT aI a h) a h e.1) := by
        rw [Finset.sum_div]
        refine pC rfl fun m _ => ?_
        dsimp only [u]
        rw [hcoord]
        exact (mul_div_assoc _ _ _).symm
      _=0:= by rw [show (∑ m,t (Sum.inl m) *
        φ (aaX (rT aI a h) a h (aEK a m)))=0 from hleft,zero_div]
  have hv : (∑ m,t (n5 m)*f (v m))=0:= by
    rw [fXx] at hright
    simp only [pG,x7,oj,AlgHom.commutes] at hright
    calc
      _=(∑ m:bAE h,t (n5 m) *
          φ (abh (rT aI a h) a h (aEK h m))) /
            φ (abh (rT aI a h) a h e.2) := by
        rw [Finset.sum_div]
        refine pC rfl fun m _ => ?_
        dsimp only [v]
        rw [hcoord]
        exact (mul_div_assoc _ _ _).symm
      _=0:= by rw [show (∑ m,t (Sum.inr m) *
        φ (abh (rT aI a h) a h (aEK h m)))=0 from hright,zero_div]
  exact h2 t ht (dIU aI a h e hdim)
    b hb f hbzero i j u v hui hvj hu hv
theorem of_children (h1 :c1) (h2 :c2) :ap6.c2 := by
 intro aI a h hsurface hdim _ _ e
 let:aI.IsPrime :=hsurface
 let I:=b51 aI a h
 change Wi (rT aI a h) a h e∈I.radical
 rw [Ideal.radical_eq_sInf]
 refine Ideal.mem_sInf.mpr fun {J} hJ => ?_
 obtain ⟨hIJ,hprime⟩:=hJ
 let:J.IsPrime :=hprime
 by_contra hchart
 let F:=ox a h
 let D:=Rees aI a h ⧸ J
 let:mD D:=Ideal.Quotient.commRing (R:=Rees aI a h) J
 let:yL D:=Ideal.Quotient.isDomain J
 let:nI F D:=inferInstanceAs (nI (ox a h) (Rees aI a h ⧸ J))
 let E :=qz D
 let:oD E :=inferInstanceAs (oD (qz D))
 let:nI D E :=inferInstanceAs (nI D (qz D))
 let:nI F E :=inferInstanceAs (nI F (qz D))
 let:vl F D E :=inferInstanceAs (vl F D (qz D))
 let:nI lz E :=Algebra.compHom E (lJ lz F)
 let:vl lz F E :=IsScalarTower.of_algebraMap_eq' rfl
 let φ:Rees aI a h →ₐ[F] E :=
  (wA F D E).comp (C4 F J)
 have hvanish (x :Rees aI a h) (hx :x∈I) :φ x=0:= by
  change lJ D E (ov J x)=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx),qG]
 have hnonzero :φ (Wi (rT aI a h) a h e)≠0:= by
  intro hz
  apply hchart
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply y5 D E
  change lJ D E (ov J (Wi (rT aI a h) a h e))=0 at hz
  rw [qG]
  exact hz
 exact eER h1 h2 aI a h hdim e φ hnonzero
  (hvanish _ (FK (v8 (by simp))))
  (hvanish _ (FK (v8 (by simp))))
  (hvanish _ (Ideal.mem_sup_right (v8 (by simp))))
end
end anb
end
section
set_option maxHeartbeats 800000
namespace cyd
noncomputable section
open aR dN E6 akN
 ap6 anb
private theorem cCA {k R F:Type*} [mD k] [mD R] [oD F]
    [nI k R] [nI k F] (b x :R) (g:R →ₐ[k] F) (hb:g b≠0) :
    wR (S:=t7 b) b (f :=g) hb.isUnit
      (IU (t7 b) x ⟨b,zh b⟩) =
        g x/g b:= by
  let f :t7 b →ₐ[k] F:=wR b (f :=g) hb.isUnit
  have hf (y :R) :f (lJ R (t7 b) y)=g y :=
    Gr b (g:=g.toRingHom) hb.isUnit y
  change f _ = _
  apply (eq_div_iff hb).2
  simpa only [oj,hf] using
    oz f (IsLocalization.mk'_spec (t7 b) x ⟨b,zh b⟩)
private theorem d3k {k R K L E ι:Type*}
   [mD k] [mD R] [mD K] [oD L] [oD E]
   [nI k R] [nI k K] [nI k L] [nI k E]
   (j:R →ₐ[k] L) (hj:t4 j)
   (b:R) (φ:R →ₐ[k] E) (hb:φ b≠0)
   (c:K →ₐ[k] L) (r :ι→K) (n:ι→R)
   (hr : ∀ t,c (r t)*j b=j (n t)) :
   ∃ f :Cy k (Set.range r) →ₐ[k] E,
     ∀ t,f ⟨r t,Aa (Gn t)⟩=φ (n t)/φ b:= by
 let S:=t7 b
 let fraction (x :R) :S:=IU S x ⟨b,zh b⟩
 have hjb:j b≠0:= by
   intro hz
   have h:b=0:=hj (hz.trans (qG j).symm)
   exact hb (h ▸ qG φ)
 let lift:S →ₐ[k] L:=wR b (f :=j) hjb.isUnit
 have hlift (x :R) :lift (lJ R S x)=j x :=
   Gr b (g:=j.toRingHom) hjb.isUnit x
 have hinj:t4 lift:= by
   apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers b) lift.toRingHom).2
   intro x y
   change lJ R S x=lJ R S y ↔
     lift (lJ R S x)=lift (lJ R S y)
   rw [hlift,hlift]
   constructor
   · exact fun h=>(hlift x).symm.trans ((oz lift h).trans (hlift y))
   · exact fun h=>oz (lJ R S) (hj h)
 have hlift_fraction (t:ι) :lift (fraction (n t))=c (r t) :=
   (cCA b (n t) j hjb).trans ((eq_div_iff hjb).2 (hr t)).symm
 let bY:=Cy k (Set.range r)
 have hchart:bY≤lift.range.comap c:= by
   apply Algebra.adjoin_le
   rintro _ ⟨t,rfl⟩
   exact ⟨fraction (n t),hlift_fraction t⟩
 let g:bY →ₐ[k] lift.range :=
   (c.comp bY.val).codRestrict lift.range fun x=>hchart x.property
 let u:S ≃ₐ[k] lift.range :=AlgEquiv.ofInjective lift hinj
 let ev :S →ₐ[k] E :=wR b (f :=φ) hb.isUnit
 refine ⟨(ev.comp u.symm.toAlgHom).comp g,fun t => ?_⟩
 have ht:g ⟨r t,Aa (Gn t)⟩=u (fraction (n t)) :=
   p7 (hlift_fraction t).symm
 change ev (u.symm (g ⟨r t,_⟩))= _
 rw [ht,AlgEquiv.symm_apply_apply]
 exact cCA b (n t) φ hb
theorem proof :anb.c1 := by
  intro aI hprime a h e E hE hAlgebra φ hφ
  let:aI.IsPrime :=hprime
  let:oD E :=hE
  let:nI lz E :=hAlgebra
  let A:=AddMonoidAlgebra (tu aI) (ℕ×ℕ)
  let L:=qz A
  let embed:=wA lz A L
  let j:=embed.comp (yH aI a h).val
  have hj:t4 j:=(y5 A L).comp yU
  let constant:tu aI →ₐ[lz] L:=embed.comp AddMonoidAlgebra.singleZeroAlgHom
  have hconstant:t4 constant:= by
    intro x y hxy
    have hs : (oY 0 x :A)=oY 0 y :=
      y5 A L hxy
    simpa only [AddMonoidAlgebra.coeff_single,Finsupp.single_eq_same] using
      oz (fun p:A=>p.coeff 0) hs
  let c:FunctionField aI →ₐ[lz] L:=IsFractionRing.liftAlgHom hconstant
  have hconstant_monomial (x :Fin 4 →₀ ℕ) :
      c (ZU aI x) =
        embed (oY 0 (ahS aI x)) :=
    IsFractionRing.lift_algebraMap (g:=constant.toRingHom) hconstant _
  let degree (d:ℕ×ℕ) :=embed (oY d 1)
  have homogeneous_image (d:ℕ×ℕ) (x :Fin 4 →₀ ℕ)
      (hx :ahS aI x∈box aI a h d) :
      j (homogeneous d (ahS aI x) hx) =
        c (ZU aI x)*degree d:= by
    change embed (oY d (ahS aI x)) =
      c (ZU aI x)*embed (oY d 1)
    rw [hconstant_monomial,← oj,Du,zero_add,uz]
  have hleft (x :nE a) :
      j (aaX aI a h x)=c (ZU aI x.val)*degree (1,0) :=
    homogeneous_image (1,0) x.val _
  have hright (y :nE h) :
      j (abh aI a h y)=c (ZU aI y.val)*degree (0,1) :=
    homogeneous_image (0,1) y.val _
  have hp:φ (aaX aI a h e.1)*φ (abh aI a h e.2)≠0:= by
    simpa only [Wi,oj] using hφ
  obtain ⟨hφleft,hφright⟩:=mul_ne_zero_iff.mp hp
  have coeff_ne_zero (x :Fin 4 →₀ ℕ) (p:yH aI a h) (d:ℕ×ℕ)
      (hj' : j p=c (ZU aI x)*degree d) (hp' : φ p≠0) :
      ZU aI x≠0:= by
    intro hz
    have heq :j p=j 0:= by rw [hj',hz,qG,zero_mul,qG]
    have hzero :p=0:=hj heq
    exact hp' (hzero ▸ qG φ)
  have hα:=coeff_ne_zero e.1.val (aaX aI a h e.1) (1,0) (hleft e.1) hφleft
  have hβ:=coeff_ne_zero e.2.val (abh aI a h e.2) (0,1) (hright e.2) hφright
  have left_ratio (x :nE a) :
      c (ZU aI x.val/ZU aI e.1.val) *
        j (aaX aI a h e.1)=j (aaX aI a h x) := by
    rw [map_div₀,hleft,hleft,← t5 ,div_mul_cancel₀ _ ((map_ne_zero c).2 hα)]
  have right_ratio (y :nE h) :
      c (ZU aI y.val/ZU aI e.2.val) *
        j (abh aI a h e.2)=j (abh aI a h y) := by
    rw [map_div₀,hright,hright,← t5 ,div_mul_cancel₀ _ ((map_ne_zero c).2 hβ)]
  let n:Generator a h→yH aI a h :=
    sS (fun x=>Wi aI a h (x,e.2)) (fun y=>Wi aI a h (e.1,y))
  have hratio (i:Generator a h) :
      c (alG aI a h e i)*j (Wi aI a h e)=j (n i) := by
    cases i with
    | inl x =>
      simp only [alG,n,u5 ,Wi,oj]
      rw [← t5 ,left_ratio]
    | inr y =>
      simp only [alG,n,vj,Wi,oj]
      rw [mul_left_comm,right_ratio]
  obtain ⟨f,hf⟩:=d3k j hj (Wi aI a h e) φ hφ c
    (alG aI a h e) n hratio
  refine ⟨hα,hβ,f,fun i=>(hf i).trans ?_⟩
  cases i with
  | inl x =>
    simp only [n,buJ,u5 ,Wi,oj]
    exact mul_div_mul_right _ _ hφright
  | inr y =>
    simp only [n,buJ,vj,Wi,oj]
    exact mul_div_mul_left _ _ hφleft
end
end cyd
end
section
namespace akN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem Zy {k α β:Type} [yQ k]
   {g:cy (α ⊕ β) k} {e :ℕ×ℕ} (hg:g∈cV e)
   (p:cy (α ⊕ β) k) (d:ℕ×ℕ) :
   t3 weight (d+e) (p*g) =
     t3 weight d p*g:= by
 induction p using zi with
 | monomial b r =>
   have hb:=yo weight b r rfl
   simp only [vw (hb.mul hg),
     vw hb,add_right_cancel_iff]
   split <;> simp_all
 | add a b ha hb=>simp [add_mul,ha,hb]
theorem bqX {k α β:Type} [mD k]
   {I:c9 (cy (α ⊕ β) k)} (hI:I.IsHomogeneous cV)
   {g:cy (α ⊕ β) k} {e :ℕ×ℕ} (hg:g∈cV e) :
   (I.colon {g}).IsHomogeneous cV:= by
 intro d p hp
 rw [Submodule.mem_colon_singleton,Av] at hp ⊢
 have he : (DirectSum.decompose cV p d:cy (α ⊕ β) k) =
     weightedHomogeneousComponent weight d p :=
   weightedDecomposition.decompose'_apply k weight p d
 rw [he,← Zy hg]
 exact Dw _ _ hI hp _
section Noetherian
variable {k α β:Type} [oD k] [p6 α] [p6 β]
private abbrev P:=cy (α ⊕ β) k
private theorem dIN (d:α ⊕ β →₀ ℕ) (r :k) (n:ℕ)
    (hleft:sH α*n<(oy weight d).1)
    (hright:sH β *n<(oy weight d).2) :
    ∃ x :α,∃ y :β,(bY x y :P (k :=k))^n∣oq d r := by
  classical
  have hs₁: (oy weight d).1 = ∑ x :α,d (nX x) := by
    simp [C9,GF,weight,Prod.fst_sum]
  have hs₂: (oy weight d).2 = ∑ y :β,d (n5 y) := by
    simp [C9,GF,weight,Prod.snd_sum]
  have hx : ∃ x :α,n≤d (nX x) := by
    by_contra! hnone
    have hsum:=zk (s :=zS) fun x _=>(hnone x).le
    rw [hs₁] at hleft
    exact (z9 hleft) (by simpa using hsum)
  have hy : ∃ y :β,n≤d (n5 y) := by
    by_contra! hnone
    have hsum:=zk (s :=zS) fun y _=>(hnone y).le
    rw [hs₂] at hright
    exact (z9 hright) (by simpa using hsum)
  obtain ⟨x,hx⟩:=hx
  obtain ⟨y,hy⟩:=hy
  let t:=t9 (nX x) n+Finsupp.single (n5 y) n
  have ht:t≤d:= by
    intro z
    rcases z with z | z
    · by_cases h:z=x
      · subst z
        simpa [t,HZ] using hx
      · simp [t,h]
    · by_cases h:z=y
      · subst z
        simpa [t,HZ] using hy
      · simp [t,h]
  refine ⟨x,y,oq (d - t) r,?_⟩
  rw [bY,mul_pow,X_pow_eq_monomial,X_pow_eq_monomial,monomial_mul_monomial,
    one_mul,← show t= _ from rfl,monomial_mul_monomial,one_mul,
    add_comm t,tsub_add_cancel_of_le ht]
private theorem gGV (I K:c9 (P (k :=k) (α:= α) (β:=β)))
   (hlocal : ∀ x :α,∀ y :β,∀ p∈K,∃ n:ℕ,bY x y ^n*p∈I) :
   ∃ n:ℕ,∀ x :α,∀ y :β,∀ p∈K,bY x y ^n*p∈I:= by
 classical
 obtain ⟨s,hs⟩:=FQ K
 have hg (v :α×β × ↥s) : ∃ n:ℕ,bY v.1 v.2.1^n*v.2.2.val∈I :=
   hlocal v.1 v.2.1 _ (hs ▸ v8 v.2.2.property)
 choose n hn using hg
 let N :=Finset.univ.sup n
 refine ⟨N,fun x y p hp => ?_⟩
 have hf :K≤I.colon {bY x y ^N} := by
   rw [← hs]
   apply Ideal.span_le.mpr
   intro q hq
   change q∈I.colon {bY x y ^N}
   apply Submodule.mem_colon_singleton.mpr
   let v :α×β × ↥s :=(x,y,⟨q,hq⟩)
   have hnv :n v≤N :=Finset.le_sup (Finset.mem_univ v)
   have hq' : bY x y ^n v*q∈I:=hn v
   rw [Av,qm,
     show N=N - n v+n v from (Nat.sub_add_cancel hnv).symm,
     pow_add,t5]
   exact I.mul_mem_left _ hq'
 exact qm p _ ▸ (Submodule.mem_colon_singleton.mp (hf hp))
theorem emM (I K:c9 (P (k :=k) (α:= α) (β:=β)))
    (hK:K.IsHomogeneous cV)
    (hlocal : ∀ x :α,∀ y :β,∀ p∈K,∃ n:ℕ,bY x y ^n*p∈I) :
    ∃ N :ℕ,∀ i j:ℕ,N≤ i→N≤j → ∀ p∈K,p∈cV (i,j)→p∈I:= by
  classical
  obtain ⟨n,hn⟩:=gGV I K hlocal
  let S:Set (P (k :=k) (α:= α) (β:=β)) :=
    {p | p∈K ∧ ∃ e :ℕ×ℕ,p∈cV e}
  have hS:pL S=K:= by
    apply zE (Ideal.span_le.mpr fun _ hp=>hp.1)
    have hle : (K.homogeneousCore cV).toIdeal≤pL S:= by
      change pL _≤_
      apply Ideal.span_mono
      rintro _ ⟨⟨q,hq⟩,hmem,rfl⟩
      exact ⟨hmem,hq⟩
    simpa only [hK.toIdeal_homogeneousCore_eq_self] using hle
  obtain ⟨s,hsS,hs⟩:=(Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (hS.symm ▸ FQ K)
  have hsg (q : ↥s) : ∃ d:ℕ×ℕ,q.val∈cV d:=(hsS q.property).2
  choose e he using hsg
  let B:=Finset.univ.sup fun q : ↥s=>max (e q).1 (e q).2
  let N :=(sH α+Fintype.card β)*n+B+1
  refine ⟨N,fun i j hi hj p hp hpg => ?_⟩
  let proj:=t3 weight (i,j) (R:=k) (σ:= α ⊕ β)
  have hgen (q : ↥s) (u:P (k :=k) (α:= α) (β:=β)) :proj (u*q.val)∈I:= by
    have hbound:=Finset.le_sup (f := fun q : ↥s=>max (e q).1 (e q).2) (Finset.mem_univ q)
    have hb₁: (e q).1≤B:=(Ea _ _).trans hbound
    have hb₂: (e q).2≤B:=(le_max_right _ _).trans hbound
    induction u using zi with
    | add u v hu hv=>simpa only [add_mul,map_add] using I.add_mem hu hv
    | monomial d c =>
      have hm:=yo weight d c rfl
      change t3 weight (i,j) (oq d c*q.val)∈I
      rw [vw (hm.mul (he q))]
      split
      next h =>
        have h₁:=oz Prod.fst h
        have h₂:=oz Prod.snd h
        change i=(oy weight d).1+(e q).1 at h₁
        change j=(oy weight d).2+(e q).2 at h₂
        have hc₁:=Iw n (Nat.le_add_right (sH α) (sH β))
        have hc₂:=Iw n (Nat.le_add_left (sH β) (sH α))
        dsimp only [N] at hi hj
        obtain ⟨x,y,t,ht⟩:=dIN d c n
          (by omega :_<(Finsupp.weight weight d).1) (by omega :_<(Finsupp.weight weight d).2)
        rw [ht,qm (_^n),t5]
        exact I.mul_mem_left t (hn x y _ (hsS q.property).1)
      next=>exact I.zero_mem
  have hmem:p∈Submodule.span (P (k :=k) (α:= α) (β:=β)) (↑s :Set _) := by
    rw [← hs]
    change p∈pL S
    rwa [hS]
  have hproj : ∀ u:P (k :=k) (α:= α) (β:=β),proj (u*p)∈I:= by
    refine Submodule.span_induction (p:= fun q _ => ∀ u,proj (u*q)∈I)
      (fun q hq u=>hgen ⟨q,hq⟩ u) ?_ ?_ ?_ hmem
    · intro u
      simp
    · intro x y hx hy hpx hpy u
      simpa only [mul_add,pU] using I.add_mem (hpx u) (hpy u)
    · intro c x hx hpx u
      simpa only [Av,t5] using hpx (u*c)
  simpa only [one_mul,proj,G1 hpg] using hproj 1
end Noetherian
end
end akN
end
section
set_option maxHeartbeats 1200000
namespace bap
noncomputable section
open aR dN BO GJ E6 YU akN
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.weightedGradedAlgebra MvPolynomial.algebraMvPolynomial
private def block {α β:Type} : α ⊕ β→Bool:=sS (fun _=>false) (fun _=>true)
private def degree : (Bool →₀ ℕ) →+ ℕ×ℕ where
 toFun d:=(d false,d true)
 map_zero' := rfl
 map_add' _ _:=rfl
private theorem degree_apply (d:Bool →₀ ℕ) :degree d=(d false,d true) :=rfl
private theorem dVr :t4 degree := by
 intro u v hv
 ext b
 cases b
 · exact oz Prod.fst hv
 · exact oz Prod.snd hv
private theorem aT5 {α β:Type} (d:α ⊕ β →₀ ℕ) :
  degree (oy (fun i=>t9 (block i) 1) d)=oy weight d:= by
 have h:degree.comp (oy (fun i:α ⊕ β=>t9 (block i) 1)) =
   oy (R:=ℕ) (weight:α ⊕ β→ℕ×ℕ) := by
  apply Finsupp.addHom_ext
  intro v n
  cases v <;> simp [degree_apply,block,weight,th]
 exact vk h d
private def homogenize {k B α β:Type} [mD k] [mD B] [nI k B]
  (f :cy (α ⊕ β) k →ₐ[k] B) :
  cy (α ⊕ β) k →ₐ[k] cy Bool B :=
 aeval fun v=>oq (t9 (block v) 1) (f (lV v))
private theorem cGc {k B α β:Type} [mD k] [mD B] [nI k B]
    (f :cy (α ⊕ β) k →ₐ[k] B) (p:cy (α ⊕ β) k) (b:Bool →₀ ℕ) :
    (homogenize f p).coeff b=f (t3 weight (degree b) p) := by
  classical
  induction p using zi with
  | add p q hp hq =>
    rw [pU,pU,pU]
    change (homogenize f p).coeff b+(homogenize f q).coeff b= _
    rw [hp,hq]
  | monomial d c =>
    let w:= fun v :α ⊕ β=>t9 (block v) (1 :ℕ)
    have hm:homogenize f (oq d c) =
        oq (oy w d) (f (oq d c)) := by
      unfold homogenize
      rw [aeval_monomial,Bf ,Ef ,Finsupp.sum]
      simp only [monomial_pow,← monomial_sum_prod]
      change C (lJ k B c)*oq _ _ = _
      rw [C_mul_monomial]
      congr 1
      symm
      have hmono:oq d c=C c*(d.prod fun i n=>(lV i:cy (α ⊕ β) k)^n) :=
        monomial_eq
      have hC:f (C c)=lJ k B c:=f.commutes c
      rw [oz f hmono,oj,hC,Bf ,map_prod]
      simp only [map_pow]
    have hh:oq d c∈weightedHomogeneousSubmodule k weight (oy weight d) :=
      yo _ _ _ rfl
    rw [hm,coeff_monomial,vw hh]
    by_cases he :degree b=oy weight d
    · have he' : oy w d=b:=dVr ((aT5 d).trans he.symm)
      simp [he,he']
    · have he' : oy w d≠b:= fun h=>he ((oz degree h).symm.trans (aT5 d))
      simp [he,he']
private abbrev Target :=Bool ⊕ Fin 4
private def qO (k :Type) [mD k] :
  cy (Fin 4) k →ₐ[k] cy Target k :=
 rename n5
private def model (k :Type) [mD k] (a h:aU) :
  cy (Generator a h) k →ₐ[k] cy Target k :=
 aeval fun v=>lV (nX (block v)) *
  qO k (oq (aod v) 1)
private def aQJ (k :Type) [mD k] [nI lz k]
  (aI:c9 lI) :c9 (cy Target k) :=
 aI.map ((qO k).toRingHom.comp (nq (lJ lz k)))
def ajR (k :Type) [mD k] [nI lz k]
    (aI:c9 lI) (a h:aU) :c9 (cy (Generator a h) k) :=
  (aQJ k aI).comap (model k a h).toRingHom
private def aSQ {k :Type} [mD k] (I:c9 (cy (Fin 4) k)) (a h:aU) :
   cy (Generator a h) k →ₐ[k] (cy (Fin 4) k ⧸ I) :=
 (C4 _ _).comp (aeval fun v=>oq (aod v) 1)
private theorem enl {k :Type} [mD k]
   (I:c9 (cy (Fin 4) k)) (a h:aU) :
   ((pz (aSQ I a h).toRingHom).homogeneousCore cV).toIdeal =
     (I.map (qO k).toRingHom).comap (model k a h).toRingHom:= by
 classical
 let Q:=cy (Fin 4) k ⧸ I
 let e :=sumAlgEquiv k Bool (Fin 4)
 let q:cy (Fin 4) k →+* Q:=ov I
 let g:cy Target k →+* cy Bool Q:=(nq q).comp e.toRingHom
 have hcomp:e.toRingHom.comp (qO k).toRingHom=(C:cy (Fin 4) k →+* _) :=
   oz AlgHom.toRingHom (sumAlgEquiv_comp_rename_inr (R:=k) (S₁:=Bool) (S₂:=Fin 4))
 have hk :pz g=I.map (qO k).toRingHom:= by
   change pz ((nq q).comp e.toRingHom)= _
   rw [← zf ,F9,Ideal.mk_ker,← hcomp,← uJ]
   exact wB e.toRingHom e.bijective
 have hg:g.comp (model k a h).toRingHom=(homogenize (aSQ I a h)).toRingHom:= by
   apply u9
   · intro c
     change g (model k a h (C c))=homogenize (aSQ I a h) (C c)
     rw [model,aeval_C,homogenize,aeval_C]
     change nq q (e (C c))=C (lJ k Q c)
     rw [sumAlgEquiv_C_inl,yJ]
     rfl
   · intro v
     change g (model k a h (lV v))=homogenize (aSQ I a h) (lV v)
     rw [model,aeval_X,homogenize,aeval_X]
     have hi:=vk hcomp (oq (aod v) (1 :k))
     change e (qO k (oq (aod v) 1))= _ at hi
     change nq q (e (_ *_))= _
     rw [oj,sumAlgEquiv_X_inl,hi,oj,uW,yJ,qm]
     change C (q _)*oq _ 1= _
     rw [C_mul_monomial,uz]
     simp only [aSQ,uh,aeval_X,u8 ,q]
 rw [← hk,zf ,hg]
 let J:=(pz (aSQ I a h).toRingHom).homogeneousCore cV
 change J.toIdeal= _
 ext p
 rw [mem_iff_weightedHomogeneousComponent_mem _ _ J.isHomogeneous,Au]
 constructor
 · intro hp
   ext1 b
   change (homogenize (aSQ I a h) p).coeff b=0
   rw [cGc]
   exact EK cV _ (hp (degree b))
 · intro hp d
   apply Fa
     ⟨d,GB _ _ _⟩
   let b:=t9 false d.1+Finsupp.single true d.2
   have hb:degree b=d:= by simp [b,degree_apply]
   have hz :=oz (fun z :cy Bool Q=>z.coeff b) hp
   change (homogenize (aSQ I a h) p).coeff b=0 at hz
   rw [cGc,hb] at hz
   exact RingHom.mem_ker.mpr hz
theorem fV2 (aI:c9 lI) (a h:aU) :
  relations aI a h=ajR (ox a h) aI a h:= by
 unfold ajR aQJ
 rw [← uJ]
 exact enl (gN aI a h) a h
private theorem c0B {k L:Type} [mD k] [mD L] (g:k →+* L) (a h:aU) :
   (nq g).comp (model k a h).toRingHom =
     (model L a h).toRingHom.comp (nq g) := by
 apply u9
 · intro r
   simp [model,qx]
 · intro i
   simp [model,qO,MvPolynomial.map_rename]
private theorem dgN {k L:Type} [mD k] [mD L]
   [nI lz k] [nI lz L] (g:k →+* L)
   (hg:g.comp (lJ lz k)=lJ lz L) (aI:c9 lI) :
   (aQJ k aI).map (nq g)=aQJ L aI:= by
 unfold aQJ
 rw [uJ,← II,show (nq g).comp
   (qO k).toRingHom=(qO L).toRingHom.comp (nq g) from
     MvPolynomial.map_comp_rename g n5 ,II]
 congr 2
 exact (RingHom.ext fun p=>Dv _ g p).trans (oz nq hg)
theorem bnE (k σ τ:Type) [mD k] :
   (vG k σ τ).toRingHom.comp (nq C) =
     (C:cy σ k →+* cy τ (cy σ k)) := by
 apply u9
 · intro c
   simp
 · intro i
   simp
theorem eA6 (τ:Type) (aI:c9 lI) (a h:aU) :
    ajR (cy τ lz) aI a h =
      (ajR lz aI a h).map (nq C) := by
  let k :=lz
  let P:=cy τ k
  let e :=vG k (Generator a h) τ
  let E :=vG k Target τ
  let f :=(model k a h).toRingHom
  let g:=(model P a h).toRingHom
  have hcomm:E.toRingHom.comp g=(nq f).comp e.toRingHom:= by
    apply u9
    · intro c
      change E (model P a h (C c))=nq f (e (C c))
      rw [model,aeval_C,qx ,commAlgEquiv_C,commAlgEquiv_C,
        Dv]
      have hC:f.comp (C (σ:=Generator a h))=C (σ:=Target) := by
        apply RingHom.ext
        intro r
        change model k a h (C r)=C r
        simp [model,qx]
      rw [hC]
    · intro i
      change E (model P a h (lV i)) =
        nq f (e (lV i))
      have hi:=vk (c0B (C:k →+* P) a h) (lV i)
      change nq C (model k a h (lV i)) =
        model P a h (nq C (lV i)) at hi
      rw [uW] at hi
      rw [← hi,commAlgEquiv_X,yJ]
      exact vk (bnE k Target τ) _
  have hI: (aQJ P aI).map E.toRingHom =
      (aQJ k aI).map (C (σ:=τ)) := by
    rw [← dgN (k :=k) (L:=P) C (by ext; simp [k,P,MvPolynomial.algebraMap_eq]),
      uJ ,bnE]
  have hJ: ((ajR k aI a h).map (nq C)).map e.toRingHom =
      (ajR k aI a h).map (C (σ:=τ)) := by
    rw [uJ,bnE]
  change (aQJ P aI).comap g= _
  rw [← wB E.toRingHom E.bijective (I:=aQJ P aI),
    hI,G2 ,hcomm,← G2]
  rw [← wB e.toRingHom e.bijective
    (I:=(ajR k aI a h).map (nq C)),hJ]
  congr 1
  ext p
  simp only [t6,MvPolynomial.mem_map_C_iff,MvPolynomial.coeff_map]
  rfl
private theorem dNR {A B A' B' : Type} [mD A] [mD B]
   [mD A'] [mD B'] [nI A A'] [nI B B']
   (g:A →+* B) (h:A' →+* B') (M:Submonoid A)
   [xm M A'] [xm (M.map g) B']
   (hcomm:h.comp (lJ A A')=(lJ B B').comp g) (I:c9 B) :
   (I.map (lJ B B')).comap h=(I.comap g).map (lJ A A') := by
 have he :h=IsLocalization.map B' g M.le_comap_map := by
   apply IsLocalization.ringHom_ext M
   rw [hcomm,IsLocalization.map_comp]
 ext p
 obtain ⟨r,s,rfl⟩:=IsLocalization.exists_mk'_eq M p
 rw [t6,he,IsLocalization.map_mk',FR,
   FR]
 constructor
 · rintro ⟨_,⟨d,hd,rfl⟩,he⟩
   exact ⟨d,hd,by simpa only [t6,oj] using he⟩
 · rintro ⟨d,hd,he⟩
   exact ⟨g d,Submonoid.mem_map_of_mem _ hd,by simpa only [t6,oj] using he⟩
abbrev UG (a h:aU) :=cy (aav (a.scale 6) (h.scale 6)) lz
abbrev bjq (a h:aU) :=cy (Generator a h) (UG a h)
theorem eA5 (aI:c9 lI) (a h:aU) :
    ajR (ox a h) aI a h =
      (ajR (UG a h) aI a h).map
        (lJ (bjq a h) (am2 a h)) := by
  let P:=UG a h
  let F:=ox a h
  let M:=(z7 P).map (C (σ:=Generator a h))
  let f :=(model P a h).toRingHom
  have hC (p:P) :f (C p)=C p:= by
    change model P a h (C p)=C p
    simp [model,qx]
  have hM:M.map f=(z7 P).map (C (σ:=Target)) := by
    ext p
    constructor
    · rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩
      exact ⟨r,hr,(hC r).symm⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨C r,⟨r,hr,rfl⟩,hC r⟩
  have :xm (M.map f) (cy Target F) :=hM ▸ Et _ _
  have hcomm:=c0B (lJ P F) a h
  rw [ajR,← dgN (lJ P F)
    (IsScalarTower.algebraMap_eq lz P F).symm]
  exact dNR f (model F a h).toRingHom M hcomm.symm _
end
end bap
end
section
namespace cye
noncomputable section
open Algebra MvPolynomial
open scoped BigOperators
private theorem dz3 {k A E :Type} [oD k] [mD A] [yL A]
   [nI k A] [xL k A] [oD E] [nI k E]
   (hdim:qJ k A≤2) (b:A) (hb:b≠0) (f :A →ₐ[k] E) (hfb:f b=0) :
   qJ k (A ⧸ pz f)≤1 := by
 let P:=pz f
 let:P.IsPrime :=G3 f
 obtain ⟨d,hA,htA⟩:=anb.bT2 k A
 obtain ⟨e,hQ,htQ⟩:=anb.bT2 k (A ⧸ P)
 have hd:d≤2 := by
   rw [htA] at hdim
   exact_mod_cast hdim
 have hbq:ov P b=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hfb
 have hdrop:=ringKrullDim_succ_le_of_surjective (ov P)
   G7 (mem_nonZeroDivisors_of_ne_zero hb) hbq
 have hcast: ((e+1 :ℕ) :WithBot ℕ∞)≤(d:WithBot ℕ∞) := by
   simpa only [hQ,hA,Nat.cast_add,Nat.cast_one,WithBot.coe_add,WithBot.coe_one]
     using hdrop
 have hle :e+1≤d:= by exact_mod_cast hcast
 have he :e≤1 := by omega
 rw [htQ]
 exact_mod_cast he
private def a1P {D I J:Type} [mD D] [p6 I] [DecidableEq I]
  (i:I) (tag : {m:I // m≠i} → J) (w:I→D) (m:I) :cy J D :=
 if hm:m≠i then lV (tag ⟨m,hm⟩)
 else -∑ x,lV (tag x)*C (w x)
private theorem cMN {D E I J:Type} [mD D] [mD E]
   [p6 I] [DecidableEq I]
   (f :D →+* E) (z :J→E) (i:I) (tag : {m:I // m≠i} → J)
   (w:I→D) (p:I→E) (hw:f (w i)=1)
   (hvar : ∀ x,z (tag x)=p x.val) (hz : (∑ m,p m*f (w m))=0)
   (m:I) :eval₂Hom f z (a1P i tag w m)=p m:= by
 by_cases hm:m≠i
 · rw [a1P,dite_eq_left hm,eval₂Hom_X']
   exact hvar ⟨m,hm⟩
 · have heq :m=i:=not_ne_iff.mp hm
   subst m
   rw [a1P,dite_eq_right hm]
   simp only [map_neg,pG,oj,eval₂Hom_X',eval₂Hom_C,hvar]
   rw [Fintype.sum_eq_add_sum_subtype_ne _ i,hw,uz] at hz
   exact (eq_neg_of_add_eq_zero_left hz).symm
theorem proof :anb.c2 := by
  classical
  intro k A E σ τ _ _ _ _ _ _ _ _ _ t ht hd b hb f hfb i j u v hui hvj hu hv
  let P:=pz f
  let:P.IsPrime :=G3 f
  let D:=A ⧸ P
  let J := {m:σ // m≠i} ⊕ {m:τ // m≠j}
  let g:D →ₐ[k] E :=Ideal.kerLiftAlg f
  let u' (m:σ) :D:=ov P (u m)
  let v' (m:τ) :D:=ov P (v m)
  let z :J→E :=t ∘ Sum.map qM qM
  let ev :cy J D →ₐ[k] E :=
    { eval₂Hom g.toRingHom z with
      commutes' := fun a=> by
        change eval₂Hom g.toRingHom z (C (lJ k D a))= _
        rw [eval₂Hom_C]
        exact g.commutes a }
  let s :σ ⊕ τ→cy J D :=
    sS (a1P i nX u') (a1P j n5 v')
  have hcomp:ev ∘ s=t:= by
    funext l
    cases l with
    | inl m =>
      exact cMN g.toRingHom z i nX u' (fun x=>t (nX x))
        (by change f (u i)=1; rw [hui,vh]) (fun _=>rfl) hu m
    | inr m =>
      exact cMN g.toRingHom z j n5 v' (fun x=>t (n5 x))
        (by change f (v j)=1; rw [hvj,vh]) (fun _=>rfl) hv m
  have hs :yB k s :=
    AlgebraicIndependent.of_comp ev (hcomp.symm ▸ ht)
  have hD:qJ k D ≤1 :=dz3 hd b hb f hfb
  let:FaithfulSMul D (cy J D) :=
    (Gj _ _).mpr (C_injective J D)
  have hdim:qJ k (cy J D)=qJ k D + Cardinal.mk J:= by
    rw [← zd k D (A:=cy J D),MvPolynomial.trdeg_of_isDomain,
      Cardinal.lift_id]
  have hle :Cardinal.mk (σ ⊕ τ)≤1+Cardinal.mk J:= by
    refine hs.cardinalMk_le_trdeg.trans ?_
    rw [hdim]
    gcongr
  have hcard:sH (σ ⊕ τ)≤1+Fintype.card J:= by
    rw [FV,FV] at hle
    exact_mod_cast hle
  have hσ:=Gi (G6 i)
  have hτ:=Gi (G6 j)
  simp only [Fintype.card_option] at hσ hτ
  simp only [J,Fintype.card_sum] at hcard
  omega
end
end cye
end
section
namespace akN
noncomputable section
open aR dN GJ E6 YU
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 :Prop :=
  ∀ (aI:c9 lI) (a h:aU),
    aI.IsPrime→ sI (lI ⧸ aI)=2 →
    vE a→vE h →
    t4 (qy aI a h)∧t4 (qU aI a h)
def c2 :Prop :=
  ∀ (aI:c9 lI) (a h:aU),
    aI.IsPrime→ sI (lI ⧸ aI)=2 →
    vE a→vE h →
    ∀ (x :nE a) (y :nE h) (p:am2 a h),
      p*asa a h∈ajA aI a h →
      ∃ n:ℕ,bY x y ^n*p∈ajA aI a h
private theorem b0f (aI:c9 lI) (a h:aU)
   (p:am2 a h) :
   ew aI a h (p*avm a h) =
     qy aI a h (ew aI a h p) := by
 rw [oj,cKc,qy ,zc]
 exact qm (ew aI a h p)
   (ov (gN aI a h) (xW a h))
private theorem cKf (aI:c9 lI) (a h:aU)
   (p:am2 a h) :
   ew aI a h (p*asa a h) =
     qU aI a h (ew aI a h p) := by
 rw [oj,cKg,qU,zc]
 exact qm (ew aI a h p)
   (ov (gN aI a h) (vZ a h))
private theorem c05 (aI:c9 lI) (a h:aU)
  (x :Oa aI a h) :
  qU aI a h (qy aI a h x) =
    qy aI a h (qU aI a h x) := by
 simp only [qy ,qU,zc]
 exact mul_left_comm _ _ x
private theorem b7G (aI:c9 lI) {a h:aU}
  (ha :vE a) (hh:vE h) {i j:ℕ}
  {w:Oa aI a h} (hw:w∈AL aI a h i j) :
  ∃ p:am2 a h,p∈cV (i,j)∧ew aI a h p=w:= by
 rw [← cKb aI ha.1 hh.1] at hw
 exact hw
private theorem b0e (aI:c9 lI) {a h:aU}
  (ha :vE a) (hh:vE h) {i j:ℕ}
  {p:am2 a h} (hp:p∈cV (i,j)) :
  ew aI a h p∈AL aI a h i j:= by
 rw [← cKb aI ha.1 hh.1]
 exact ⟨p,hp,rfl⟩
private theorem ebp (aI:c9 lI) (a h:aU) :
  (ajA aI a h).IsHomogeneous cV:= by
 unfold ajA
 apply (c8a aI a h).sup
 apply Ideal.homogeneous_span
 rintro _ ⟨⟩
 exact ⟨(1,0),bIm a h⟩
private theorem d4i (h2 :c2) (aI:c9 lI) (a h:aU)
    (hs :aI.IsPrime) (hd:sI (lI ⧸ aI)=2)
    (ha :vE a) (hh:vE h) :
    ∃ N :ℕ,∀ i j:ℕ,N≤ i→N≤j →
      (AL aI a h i (j+1)).map (qy aI a h) ⊓
        (AL aI a h (i+1) j).map (qU aI a h) =
      (AL aI a h i j).map ((qy aI a h).comp (qU aI a h)) := by
  classical
  let:p6 (nE a) :=zm _
  let:p6 (nE h) :=zm _
  let I:=ajA aI a h
  let K:=I.colon {asa a h}
  have hI:=ebp aI a h
  have hK:K.IsHomogeneous cV:=bqX hI (cfs a h)
  have hlocal (x :nE a) (y :nE h) (p:am2 a h)
      (hp:p∈K) : ∃ n:ℕ,bY x y ^n*p∈I :=
    h2 aI a h hs hd ha hh x y p (Submodule.mem_colon_singleton.mp hp)
  obtain ⟨N,hN⟩:=emM I K hK hlocal
  refine ⟨N,fun i j hi hj=>zE ?_ ?_⟩
  · rintro w ⟨hw₁,hw₂⟩
    obtain ⟨u,hu,hue⟩:=Submodule.mem_map.mp hw₁
    obtain ⟨v,hv,hve⟩:=Submodule.mem_map.mp hw₂
    obtain ⟨p,hp,hpu⟩:=b7G aI ha hh hu
    obtain ⟨q,hq,hqv⟩:=b7G aI ha hh hv
    have hpL:p*avm a h∈cV (i+1,j+1) :=
      xu hp (bIm a h)
    have hqR:q*asa a h∈cV (i+1,j+1) :=
      xu hq (cfs a h)
    have hsubloc:q*asa a h - p*avm a h∈relations aI a h:= by
      have hgrade :q*asa a h - p*avm a h∈cV (i+1,j+1) :=
        Submodule.sub_mem (cV (k :=ox a h) (α:=nE a)
          (β:=nE h) (i+1,j+1)) hqR hpL
      apply eAe hgrade
      rw [map_sub,cKf,b0f,hqv,hpu,hve,hue,sub_self]
    have hpLcut:p*avm a h∈I :=
      Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨p,rfl⟩)
    have hqK:q∈K:= by
      apply Submodule.mem_colon_singleton.mpr
      change q*asa a h∈I
      rw [← sub_add_cancel (q*asa a h) (p*avm a h)]
      exact I.add_mem (Submodule.mem_sup_left hsubloc) hpLcut
    have hqI:=hN (i+1) j (hi.trans (Nat.le_succ i)) hj q hqK hq
    obtain ⟨r,hr,s,hspan,hsum⟩:=Submodule.mem_sup.mp hqI
    obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton'.mp hspan
    let z :=t3 weight (i,j) t
    have hz :z∈cV (i,j) :=GB _ _ _
    have hcomp:=oz (t3 weight ((i,j)+(1,0))) hsum
    have hq' : q∈cV ((i,j)+(1,0)) :=hq
    rw [pU,Zy (bIm a h),
      G1 hq'] at hcomp
    have hrel :=Dw _ _
      (c8a aI a h) hr ((i,j)+(1,0))
    have hdiv :qy aI a h (ew aI a h z)=v := by
      have he :=oz (ew aI a h) hcomp
      rw [pU,dVM hrel,zero_add,b0f,hqv] at he
      exact he
    refine Submodule.mem_map.mpr ⟨ew aI a h z,b0e aI ha hh hz,?_⟩
    rw [Hw ,← hve,← hdiv]
    exact (c05 aI a h _).symm
  · rintro w hw
    obtain ⟨u,hu,hue⟩:=Submodule.mem_map.mp hw
    obtain ⟨p,hp,hpu⟩:=b7G aI ha hh hu
    have hpL:p*avm a h∈cV (i+1,j) :=
      xu hp (bIm a h)
    have hpR:p*asa a h∈cV (i,j+1) :=
      xu hp (cfs a h)
    refine ⟨Submodule.mem_map.mpr ⟨_,b0e aI ha hh hpR,?_⟩,
      Submodule.mem_map.mpr ⟨_,b0e aI ha hh hpL,?_⟩⟩
    · rw [cKf,hpu]
      exact hue
    · rw [b0f,hpu,← hue,Hw]
      exact c05 aI a h u
theorem of_children (h1 :c1) (h2 :c2) :YU.c1 := by
 intro aI a h hs hd ha hh
 obtain ⟨hl,hr⟩:=h1 aI a h hs hd ha hh
 exact ⟨hl,hr,d4i h2 aI a h hs hd ha hh⟩
end
end akN
end
section
set_option maxHeartbeats 1200000
namespace bap
noncomputable section

open dN BO GJ E6 YU akN
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private def coordinate {γ:Type} (b:aU) (i:nE b→γ)
  (m:uL (b.scale 6)) :cy γ GeoField :=
 if hm:m∈Bz (b.scale 6) then
  lV (i ⟨afh m,aTj b ⟨m,hm⟩⟩)
 else 0
private def beH {γ τ:Type} (b:aU) (i:nE b→γ)
   (j:uL (b.scale 6)→τ) :cy γ (cy τ lz) :=
 ∑ m∈Bz (b.scale 6),C (lV (j m)) *
   nq C (coordinate b i m)
private abbrev a5d (a h:aU) :bjq a h:=beH a nX nX
private abbrev a7S (a h:aU) :bjq a h:=beH h n5 n5
private theorem cVn {γ τ:Type} (b:aU) (i:nE b→γ)
    (j:uL (b.scale 6)→τ) :
    let P:=cy τ lz
    let F:=qz P
    nq (lJ P F) (beH b i j) =
      ∑ m∈(Bz (b.scale 6)).attach,
        C (lJ P F (lV (j m.val))) *
          lV (i ⟨afh m.val,aTj b m⟩) := by
  dsimp only
  unfold beH
  rw [pG]
  rw [← zg (Bz (b.scale 6))]
  apply pC rfl
  intro m _
  simp [coordinate,m.property]
private theorem dPN {γ:Type} (b:aU) (i:nE b→γ)
  (y :nE b) : ∃ m∈Bz (b.scale 6),coordinate b i m=lV (i y) := by
 have hy : (fun j=>y.val j)∈rU (b.scale 6) :=y.property
 rw [cNO] at hy
 obtain ⟨m,hm,he⟩:=hy
 have hey : (⟨afh m,aTj b ⟨m,hm⟩⟩:nE b)=y := by
  apply p7
  ext j
  simpa [afh] using congrFun he j
 have hm' : m∈Bz (b.scale 6) :=hm
 exact ⟨m,hm',by simp only [coordinate,dite_eq_left hm',hey]⟩
private theorem bra (aI:c9 lI) (a h:aU)
   (x :nE a) (y :nE h) (p:bjq a h)
   (hp:p*a7S a h ∈
     ajR (UG a h) aI a h ⊔ pL {a5d a h}) :
   ∃ n:ℕ,bY x y ^n*p ∈
     ajR (UG a h) aI a h ⊔ pL {a5d a h} := by
 let α:=uL (a.scale 6)
 let β:=uL (h.scale 6)
 let σ:=Generator a h
 let J:=ajR lz aI a h
 let Q:=cy σ lz ⧸ J
 let:mD Q:=inferInstanceAs (mD (cy σ lz ⧸ J))
 let q:cy σ lz →+* Q:=ov J
 let e :=vG lz σ (α ⊕ β)
 let f :=(nq q).comp e.toRingHom
 let E :=(renameEquiv Q (Equiv.sumComm α β)).trans (sumAlgEquiv Q β α)
 let g:=E.toRingHom.comp f
 have hf :pz f=ajR (UG a h) aI a h:= by
   change pz ((nq q).comp e.toRingHom)= _
   rw [← zf ,F9,Ideal.mk_ker,
     eA6,← bnE lz σ (α ⊕ β),
     ← uJ]
   exact wB e.toRingHom e.bijective
 have hg:pz g=ajR (UG a h) aI a h:= by
   rw [show g=E.toRingHom.comp f from rfl,← hf]
   ext z
   rw [Au,Au]
   change E (f z)=0↔f z=0
   rw [← qG E]
   exact E.injective.eq_iff
 have hconst (v :cy σ lz) :
     g (nq C v)=C (C (q v)) := by
   change E (nq q (e (nq C v)))= _
   have hv :=vk (bnE lz σ (α ⊕ β)) v
   change e (nq C v)=C v at hv
   rw [hv,yJ]
   simp [E,C5 ,sumAlgEquiv_C_inl]
 have hleft (m:α) :g (C (lV (nX m)))=C (lV m) := by
   change E (nq q (e (C (lV (nX m)))))= _
   rw [commAlgEquiv_C_X,uW]
   simp [E,C5 ,sumAlgEquiv_X_inr]
 have hright (m:β) :g (C (lV (n5 m)))=lV m:= by
   change E (nq q (e (C (lV (n5 m)))))= _
   rw [commAlgEquiv_C_X,uW]
   simp [E,C5 ,sumAlgEquiv_X_inl]
 let l:cy α Q := ∑ m∈Bz (a.scale 6),
   C (q (coordinate a nX m))*lV m
 let w:β→Q:= fun m=>q (coordinate h n5 m)
 have hl:g (a5d a h)=C l:= by
   simp only [a5d,beH,pG,oj,hleft,hconst,l]
   exact pC rfl fun _ _=>qm _ _
 have hr :g (a7S a h) = ∑ m∈Bz (h.scale 6),C (C (w m))*lV m:= by
   simp only [a7S,beH,pG,oj,hright,hconst,w]
   exact pC rfl fun _ _=>qm _ _
 obtain ⟨m,hm,he⟩:=dPN h (n5 :nE h→σ) y
 have hchart:g (bY x y)=C (C (q (lV (nX x))*w m)) := by
   have hh:=hconst (bY x y :cy σ lz)
   simpa only [bY,oj,uW,w,he] using hh
 have hsurj:In g :=
   E.surjective.comp ((MvPolynomial.map_surjective q G7).comp e.surjective)
 have hcut: (pL {C l}).comap g =
     ajR (UG a h) aI a h ⊔ pL {a5d a h} := by
   rw [← hl,Ideal.comap_span_singleton_of_surjective g hsurj,hg]
 rw [← hcut,t6,oj,hr] at hp
 obtain ⟨n,hn⟩:=dEg l _ w m hm (q (lV (nX x))) (g p) hp
 refine ⟨n,?_⟩
 rwa [← hcut,t6,oj,map_pow,hchart]
theorem proof :akN.c2 := by
 intro aI a h _ _ _ _ x y p hp
 let A:=bjq a h
 let B:=am2 a h
 let M:=(z7 (UG a h)).map (C (σ:=Generator a h))
 let g:=lJ A B
 let I:=ajR (UG a h) aI a h ⊔ pL {a5d a h}
 have :xm M B:=Et _ _
 have hl:g (a5d a h)=avm a h:=cVn a nX nX
 have hr :g (a7S a h)=asa a h:=cVn h n5 n5
 have hz :g (bY x y)=bY x y := by
   change nq (lJ (UG a h) (ox a h)) (bY x y)= _
   simp [bY]
 have hI:I.map g=ajA aI a h:= by
   simp only [I,ajA,Ideal.map_sup,Ideal.map_span,Set.image_singleton,hl,
     fV2,eA5,g]
   rfl
 have hreg : ∀ q:A,q*a7S a h∈I → ∃ n:ℕ,bY x y ^n*q∈I :=
   bra aI a h x y
 have hmem:p*g (a7S a h)∈I.map g:= by rwa [hr,hI]
 have hres : ∃ n:ℕ,g (bY x y)^n*p∈I.map g :=
   dEi M I (bY x y) (a7S a h) hreg p hmem
 rwa [hz,hI] at hres
end
end bap
end
section
set_option maxHeartbeats 0
set_option maxRecDepth 50000
namespace acY
open acY.Compact
private def p0:Chunk 3012 4 224745017 :=
 cert _ _ _ 0x552a0504292854275326522503245123022250210120004f579806b66bdb0f51edbda2ca96ef01527df76875c53ec012f65338a81410a4a1349d30992c940c91288c088924840480002d5e655b7543a83557a8f6ded1654a61ae693e53b0d6e69f6009862a8e3e0a088c3c8a3a8838368634328430062e2c822a042826802402220016af300d0ea0d55ea3db7b4595298721b71beed0eb8b418026acbdf8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c0900888005b20d775b287506b0fbeadbebae3f4c35cd27ca761b5c5a09ab2f (by decide +kernel) (by decide +kernel)
private def p4 :Chunk 3016 4 227485736 :=
 cert _ _ _ 0x154a81410a4a1509d4c9948940c91448c088940840480013d5f655b7543a83557a8f80f9153fa6180aa45d9a1f6e69f6049862a9c540a0852509a4e984c964a064894460444924202400016aff00d0ea0d55ea3db7b454fedde02a4f94ec35b9a7d8125eca638f8282230f228ea20e0da18d0ca10c018b8b208a810a09a00900888005abed775b287506b0fbeb01da2ca94fe98602a9176687db9a7d95a704c5f8f82821f0f1e8e9e0e0d9d8d0c9d0c018b8b1c8a810a099c0900888005abeb7543a83557a8f6ded153fa61ae693e53b0d6e69f6569ab2f (by decide +kernel) (by decide +kernel)
private def p8:Chunk 3020 4 231657831 :=
 cert _ _ _ 0x154a81410a4a1509d4c9948940c91448c088940840480013c34dd50ea0d55ea3e039eb4c6dde05adb49eecd0fbb539b034c1954e2a050429284d274c264b2503244a23022249210120000b0d5775b287506b0f51f01f23959aea98d30c0b5b6a45d9a1f76a736579a42d8e3e0a088c3c8a3a8838368634328430062e2c822a042826802402220016aff2adbaa1d41aabd47c072b2d153fa6180ab6d27bb343edcd3ecaf39864fc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002d5fe01ad9af6c3d47b6f68a9fdbbc0b5b6a45d9b0d6e6736049b630 (by decide +kernel) (by decide +kernel)
private def zF:Chunk 3024 4 235952446 :=
 cert _ _ _ 0xaa540a085250a84ea64ca44a0648a2460444a0420240009e1ab65a5b287506b0f51eedcf5df94c2b7548c0f3eb2c4f6d813105738a81410a4a1349d30992c940c91288c088924840480002d6964dd50ea0d55f616c1bb73d698d30c0b5ba93e079f576a736c09962c8e3e0a088c3c8a3a8838368634328430062e2c822a0428268024022200161aae806b66bdb0f51eedcf5a636eeb7548c0f43eed4f6c0d36060fc7c1410f878f474f0706cec6864e8600c5c58e45408504ce0480444002c352ad6ca1d41aabd479ebaea98d30c0b5b6a46079f576a736069be31 (by decide +kernel) (by decide +kernel)
private def TF:Chunk 3028 4 239565727 :=
 cert _ _ _ 0x2a95028214942a13a993291281922891811128108090002786ad96831710ea0d55ede4f5d874c6984f0a4f772b7cfacb13db2cccc16ce2a050429284d274c264b2503244a23022249210120000b5a592d062d941aabdbcbb72b2a4d31b775baa45dcadf3eaeeec4c113365b1c7c14111879147510706d0c686508600c5c59045408504d00480444002c355cb018b650ea0d61f615bc9ebb0e98d30add522ee56f9f59627b6089d6347e3e0a087c3c7a3a7838367634327430062e2c722a0428267024022200161ab8586ea87506aafb0b60ddb959b0e98dbbadd49f03d6fa1f76a736089d934 (by decide +kernel) (by decide +kernel)
private def c:Chunk 3012 20 1159406757 :=
 add p0 <| add p4 <| add p8 <| add zF <| TF
end acY
end
section
namespace lB
noncomputable section
open Polynomial MvPolynomial K1 aR Ex dN
theorem ahA {n:ℕ} (h:n<K1.p) : (n.factorial:ao)≠0:= by
 let _:CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
 intro hz
 have hp:=CharP.char_is_prime_of_two_le ao K1.p (by decide)
 exact (z9 h) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff ao K1.p _).mp hz))
private theorem ctN (i:Fin 4) :
   YN (lV i) =
    if h:i=3 then Polynomial.X else Polynomial.C (lV (i.castPred h)) := by
 refine Fin.lastCases ?_ (fun j => ?_) i
 · have hlast :finSuccEquivLast (3:Fin 4)=none :=finSuccEquivLast_last
   simp [YN,hlast,optionEquivLeft_X_none,show Fin.last 3=(3:Fin 4) by rfl]
 · have h:j.castSucc≠(3:Fin 4) :=G8 j
   simp [YN,optionEquivLeft_X_some,h]
private theorem bxU (f :af 4) :
   YN (pQ f)=derivative (YN f) := by
 classical
 induction f using MvPolynomial.induction_on with
 | C c=>simp [separant,YN,optionEquivLeft_C]
 | add f g hf hg =>
   simp only [pQ,pU] at hf hg ⊢
   rw [hf,hg]
 | mul_X f i ih =>
   simp only [pQ,pderiv_mul,pU,oj] at ih ⊢
   rw [derivative_mul,ih,ctN]
   by_cases h:i=3
   · subst i
     simp
   · simp only [dite_eq_right h,pderiv_X_of_ne h,qG,derivative_C,mul_zero,add_zero]
private def ur (S:ao[X]) (f :af 4) :ao[X][X] :=
 (YN f).map (t8 (jet S))
private theorem bFv (S:ao[X]) (f :af 4) :
   (ur S f).eval (jet S (3:Fin 4))=cK f S:= by
 let e :=(Polynomial.evalRingHom (jet S (3:Fin 4))).comp
   ((z8 (t8 (jet S))).comp YN.toRingHom)
 change e f=(t8 (jet S)) f
 have he :e=t8 (jet S) := by
   apply u9
   · intro c
     simp [e,YN,optionEquivLeft_C]
   · intro i
     refine Fin.lastCases ?_ (fun j => ?_) i
     · simp [e,ctN,show Fin.last 3=(3:Fin 4) by rfl]
     · simp [e,ctN,show j.castSucc≠(3:Fin 4) from G8 j,jet]
 rw [he]
private theorem bO1 (S:ao[X]) (f :af 4) :
  (ur S f).coeff (p5 f).t=bhZ f S:= by
 rw [ur,Polynomial.coeff_map,← a3E,cK,X7,
  Polynomial.leadingCoeff,aQU]
theorem bD9 (f :af 4) (j:ℕ) :
  (p5 ((pQ^[j]) f)).t≤(p5 f).t - j:= by
 rw [← aQU,← aQU]
 have h:YN ((pQ^[j]) f)=derivative^[j] (YN f) := by
  induction j with
  | zero=>rfl
  | succ j ih=>simp only [Function.iterate_succ_apply',bxU,ih]
 rw [h]
 exact natDegree_iterate_derivative _ _
theorem a3t (f :af 4) (j:ℕ) :
  aO (p5 ((pQ^[j]) f)) (p5 f) := by
 have h (w:Fin 4→ℕ) :
    ((pQ^[j]) f).weightedTotalDegree w≤f.weightedTotalDegree w:= by
  induction j with
  | zero=>exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',pQ]
    exact (weightedTotalDegree_pderiv_le _ _ _).trans ih
 exact ⟨by simpa only [shape,weightedTotalDegree_one] using h 1,
  by simpa only [p5 ,C6] using h Fin.val,
  (bD9 f j).trans (Nat.sub_le _ _)⟩
end
end lB
end
section
namespace wH
noncomputable section
open Polynomial aR
def qg (f :af 4) (S:ao[X]) :Prop :=
 cK (MvPolynomial.pderiv (3:Fin 4) f) S≠0
def Gh (P:af 3) (b j:ℕ) :Prop :=
 P.totalDegree≤b∧qE P≤j
abbrev iP:=qz ao[X]
abbrev cH :=AlgebraicClosure iP
abbrev Lower :=cy (Fin 3) cH
abbrev Sz :=Fin 3→cH
abbrev qY:ao[X] →+* cH :=
 (lJ iP cH).comp (lJ ao[X] iP)
def fW (P:af 3) :Lower :=nq qY P
def Ud (S:ao[X]) :Sz :=
 fun i=>qY (jet S i)
def bbj (P Q:af 3) :Prop :=
 P≠0∧Q≠0∧IsRelPrime (fW P) (fW Q)
def oF (y :Sz) :c9 Lower :=
 pz (t8 y)
def Ib (P Q:af 3) :c9 Lower :=
 pL {fW P,fW Q}
def asD (P Q R:af 3) :c9 Lower :=
 pL {fW P,fW Q,fW R}
def localColength (q:p9 Lower) (J:c9 Lower) :ℕ∞ :=
 let A:=G4 q.asIdeal
 Module.length A (A ⧸ J.map (lJ Lower A))
def rH (x :aU) :Shape :=
 if x.t=1 then ajN x.iU else bY (bf+4) x.iU
end
end wH
end
section
namespace K1_13_7_6
noncomputable section
open wH MvPolynomial
def cap (b j:ℕ) :Set (Fin 3 →₀ ℕ) :=
 {e | e.degree≤b∧e 1+2*e 2≤j}
instance gO8 (b j:ℕ) :Finite (cap b j) :=
 ((Finsupp.finite_of_degree_le b).subset (fun _ h=>h.1 :
   cap b j ⊆ {e | e.degree≤b})).to_subtype
def aGW {σ:Type} [Finite σ]
    (φ:cy σ cH →ₐ[cH] Lower) (p:p9 Lower) :ℚ :=
  affineDegree (p.asIdeal.comap φ)
def zeroPrime :p9 Lower :=⟨⊥,inferInstance⟩
def ke (p:p9 Lower) (f :Lower) :c9 Lower :=
 p.asIdeal ⊔ pL {f}
def a3c (D:p9 Lower→ℚ) (p:p9 Lower) (f :Lower)
    (qs :Finset (p9 Lower)) :ℚ :=
  ∑ q∈qs,(localColength q (ke p f)).toNat*D q
end
end K1_13_7_6
end
section
namespace K1_13_7_6
noncomputable section
open MvPolynomial
private theorem boR (e :Fin 3 →₀ ℕ) :e.degree=e 0+e 1+e 2 := by
 rw [EP ,Fin.sum_univ_three,yl]
private theorem degree_fin_two (e :Fin 2 →₀ ℕ) :e.degree=e 0+e 1 := by
 rw [EP ,Fin.sum_univ_two]
private def dEC (b m:ℕ) (hb:2*m≤b) :
  cap b (2*m) ≃ Σ z :Fin (m+1),
   ze (Fin 2) 1 (b - z) (2*(m - z)) where
 toFun e := by
  have htotal:=e.property.1
  rw [boR] at htotal
  have hindex :=e.property.2
  let z :Fin (m+1) :=⟨e.val 2,by omega⟩
  refine ⟨z,⟨Finsupp.equivFunOnFinite.symm ![e.val 0,e.val 1],?_⟩⟩
  rw [mem_cappedDegreeExponents,degree_fin_two]
  change e.val 0+e.val 1≤b-e.val 2∧e.val 1≤2*(m-e.val 2)
  omega
 invFun p:= by
  obtain ⟨z,u⟩:=p
  have htotal:=u.property.1
  rw [degree_fin_two] at htotal
  have hindex :=u.property.2
  have hz :=z.isLt
  refine ⟨Finsupp.equivFunOnFinite.symm ![u.val 0,u.val 1,z.val],?_⟩
  change (Finsupp.equivFunOnFinite.symm ![u.val 0,u.val 1,z.val]).degree≤b∧_
  rw [boR]
  change u.val 0+u.val 1+z.val≤b∧u.val 1+2*z.val≤2*m
  omega
 left_inv e := by
  apply p7
  ext i
  fin_cases i <;> rfl
 right_inv p:= by
  rcases p with ⟨⟨z,hz⟩,u⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply p7
  ext i
  fin_cases i <;> rfl
private theorem d96 (b m z :ℕ) (hb:2*m≤b) (hz :z≤ m) :
   (ze (Fin 2) 1 (b - z) (2*(m - z))).ncard =
     (2*(m - z)+1)*(b+1 - m) := by
 have hc:2*(m - z)≤b - z := by omega
 have h:=two_mul_ncard_cappedDegreeExponents_fin_two (b - z) (2*(m - z)) hc
 have hfactor :2*(b - z)+2 - 2*(m - z)=(b+1 - m)*2 := by omega
 rw [hfactor,← t5 ,← qm 2] at h
 exact Nat.eq_of_mul_eq_mul_left (show 0<2 by decide) h
private theorem gwV (m:ℕ) :
    (∑ z∈oZ (m+1),(2*(m - z)+1))=(m+1)^2 := by
  calc
    _ = ∑ z∈oZ (m+1),(2*z+1) := by
      simpa only [Df] using Finset.sum_range_reflect (fun z=>2*z+1) (m+1)
    _ = _:= by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
        Nat.nsmul_eq_mul,uz]
      rw [← Finset.mul_sum,qm 2,Finset.sum_range_id_mul_two]
      simp only [Df]
      ring
theorem dE8 (b m:ℕ) (hb:2*m≤b) :
    (cap b (2*m)).ncard=(m+1)^2*(b+1 - m) := by
  classical
  let (z :Fin (m+1)) :p6
      (ze (Fin 2) 1 (b - z) (2*(m - z))) :=zm _
  rw [← FU,Nat.card_congr (dEC b m hb),G0 ,
    Fintype.card_sigma]
  calc
    _ = ∑ z :Fin (m+1),(2*(m - z.val)+1)*(b+1 - m) := by
      apply pC rfl
      intro z _
      rw [← G0 ,FU,d96 b m z hb (by omega)]
    _ = _:= by
      rw [← Finset.sum_mul,GY (fun z=>2*(m - z)+1),
        gwV]
end
end K1_13_7_6
end
section
namespace Rl
noncomputable section
open Polynomial K1 aR dN wH
def He (q:af 3) :af 4 :=MvPolynomial.rename Fin.castSucc q
def acp (q:af 3) :af 4 :=pK (He q)
structure aqk (f :af 4) (q:af 3) (aI:c9 lI) :Prop where
 minimal: (kC f (He q)).IsMinimalPrime aI
 leading:bC (He (Ex.X7 f))∉aI
 regular :bC (pQ f)∉aI
def Ve {L:Type} [oD L] [nI ao L] (P:af 4) (S:L[X]) :L[X] :=
  Gk (z8 (lJ ao L))
    (fun i=>Polynomial.hasseDeriv i.val S) P
structure Li (f :af 4) where
 denom:af 4
 Fr :Fin bf→af 4
 test :af 4
 denom_box :aO (p5 denom) (rH (p5 f))
 numer_box : ∀ i,aO (p5 (Fr i)) (rH (p5 f))
 aX4 :aO (p5 test) (rH (p5 f))
 test_iff : ∀ (aI:c9 lI),aI.IsPrime→bC f∈aI →
  bC (pQ f)∉aI →
  (bC test∈aI↔bC (vU f)∈aI)
 ar5 : ∀ (L:Type) [oD L] [nI ao L] (S:L[X]),
  S.natDegree≤133671→Ve f S=0 →
  Ve (pQ f) S≠0 →
  Ve denom S≠0∧Ve test S=0 ∧
    ∀ i,Ve (Fr i) S=Ve denom S*C (S.coeff i.val)
def bkW (f :af 4) (q:af 3) (E :af 4) (S:ao[X]) :Prop :=
  ∃ aI,aqk f q aI∧aI≤Ch S ∧
    (bC E∉aI∨bC (acp q)∉aI)
abbrev jo:=cy (Fin bf) ao
def Sp:jo[X] :=
 ∑ i:Fin bf,C (lV i)*Polynomial.X ^i.val
def aip (f :af 4) :jo[X] :=
  Gk (z8 (MvPolynomial.C:ao →+* jo))
    (fun i=>hasseDeriv i.val Sp) f
def aG7 (S:ao[X]) :c9 jo :=
 pz (t8 (fun i:Fin bf=>S.coeff i.val))
structure akB (f :af 4) (P:c9 jo) :Prop where
 prime :P.IsPrime
 dimension :2≤(MvPolynomial.affineHilbertPolynomial P).natDegree
 solves : ∀ i,(aip f).coeff i∈P
 regular : ∃ i,(aip (pQ f)).coeff i∉P
def aYV (f :af 4) (S:ao[X]) :Prop :=
 ∃ P,akB f P∧P≤aG7 S
def bbz (Γ:Finset K) (s :K→K[X]) (d:ℕ) :Prop := by
  classical
  exact ∀ x a :K,(∃ γ∈Γ,(s γ).eval x≠a) →
    let H :=Γ.filter (fun γ=>(s γ).eval x=a)
    ∃ C:DA H,H⊆C.union∧C.uG s∧(∀ i,0<C.degree i)∧C.total≤d
def bTH {Γ:Finset K} (C:DA Γ) (s :K→K[X]) :Prop :=
 ∀ i,bbz (C.dO i) s (C.degree i)
end
end Rl
end
section
namespace K1_13_7_4
noncomputable section
open Polynomial aR wH
open scoped BigOperators
def EY (a :Fin 3 →₀ ℕ) :ℕ :=
 a.sum (fun _ k=>k)
def BV {A:Type*} [yQ A]
    (a :Fin 3 →₀ ℕ) (F:cy (Fin 3) A) :cy (Fin 3) A :=
  ∑ m∈F.support,
    oq (m-a) (F.coeff m * ∏ i:Fin 3,((m i).choose (a i) :A))
def afc (q:p9 Lower) (F:Lower) (d:ℕ) :Prop :=
 let A:=G4 q.asIdeal
 lJ Lower A F∈IsLocalRing.maximalIdeal A^d
end
end K1_13_7_4
end
