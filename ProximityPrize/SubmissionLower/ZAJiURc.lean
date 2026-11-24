import ProximityPrize.SubmissionLower.A2
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Valuation.ValuationSubring
import ProximityPrize.SubmissionLower.ZvqS6Fa
import ProximityPrize.SubmissionLower.Zgvu91a
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.FiniteType → zUK, Algebra.FiniteType.adjoin_of_finite → zTV, Algebra.adjoin → zum, Algebra.adjoin_induction → z90, Algebra.smul_def → zd5, Algebra.subset_adjoin → zkk, CommRing → za6, Field → zrb, Function.Injective → zq4, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.div_surjective → zJC, IsFractionRing.injective → zxb, IsLocalization → zNo, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, IsScalarTower.of_algebraMap_eq' → zD8, Module.Finite → zAa, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Subalgebra → zTg, Subalgebra.fg_iff_finiteType → ztE, Subalgebra.inclusion → zDu, Submodule.span → zLD, Submonoid → zdT
set_option maxHeartbeats 750000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q6hv5Ed
noncomputable section
open E7 aFU WithZero
open private cNx from ProximityPrize.SubmissionLower.V
open private eaZ bJK from ProximityPrize.SubmissionLower.V
open private bQb a6a bRu.center aDm bsy from ProximityPrize.SubmissionLower.A2
open scoped WithZero IntermediateField.algebraAdjoinAdjoin
theorem seed_model {k E :Type} [zrb k] [IsAlgClosed k] [zrb E] [zZE k E]
    (w:CurvePlace k E) (hE :CurveField k E) :
    ∃ B:zTg k E,zUK k B∧z0o B E ∧
      (∀ b:B,w.value (b:E)≤1) ∧
      ∀ a :w.value.valuationSubring,∃ b s :B,
        w.value (s :E)=1∧(a :E)*(s :E)=b:= by
  obtain ⟨t,ht⟩:=w.normalized (exp (-1 :ℤ))
  have ht0:t≠0:=w.value.ne_zero_iff.mp (ht.trans_ne exp_ne_zero)
  have ht1 :w.value t<1 :=ht.trans_lt (by simp)
  have ht' : Transcendental k t:= by
    by_contra h
    obtain ⟨c,rfl⟩:=cNx h
    exact ht1.ne (w.on_constants c (fun e=>ht0 (by simp [e])))
  let R:=DT k E t
  let N :=DR k E t
  let K:=IntermediateField.adjoin k ({t} : Set E)
  have :zAa K E :=eaZ hE ht'
  have :zAa R N :=bRt.proof k E t ht' inferInstance
  have :IsDedekindDomain N :=bJK ht'
  have :z0o N E :=integralClosure.isFractionRing_of_finite_extension K E
  have :zUK k R :=
    zTV (Set.finite_singleton t)
  have hN :zUK k N :=Algebra.FiniteType.trans ‹zUK k R› inferInstance
  let B:=(integralClosure R E).restrictScalars k
  let v :ax5 k E t:=⟨w,(bQb w.value ht0).mpr ht1⟩
  let q:=aDm ht' (bRu.center v ht')
  have hreg (b:N) :w.value (b:E)≤1 :=a6a v ht0 b
  have hunit (s :q.asIdeal.primeCompl) :w.value (s.val :E)=1 :=
    le_antisymm (hreg s) (le_of_not_gt fun h=>s.property ((bsy v ht0 s).mpr h))
  have hbelow:q.valuationSubringAtPrime E≤w.value.valuationSubring := by
    intro a ha
    rw [q.valuationSubringAtPrime_eq_valuationSubring] at ha
    obtain ⟨b,s,hs⟩:=q.exists_primeCompl_mul_eq_of_integer a ha
    have he :=congrArg w.value hs
    rw [map_mul,show w.value (algebraMap N E s)=1 from hunit s,mul_one] at he
    exact he.trans_le (hreg b)
  have heq :q.valuationSubringAtPrime E=w.value.valuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top _ hbelow (by
      rw [ne_eq,Valuation.valuationSubring_eq_top_iff,not_not]
      exact (Valuation.isNontrivial_iff_exists_lt_one w.value).mpr ⟨t,ht0,ht1⟩)
  refine ⟨B,hN,‹z0o N E›,hreg,fun a => ?_⟩
  have ha : (a :E)∈q.valuationSubringAtPrime E :=heq.symm ▸ a.property
  rw [q.valuationSubringAtPrime_eq_valuationSubring] at ha
  obtain ⟨b,s,hs⟩:=q.exists_primeCompl_mul_eq_of_integer (a :E) ha
  exact ⟨b,s.val,hunit s,hs⟩
end
end q6hv5Ed
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q6hv5Ed
noncomputable section
private theorem finite_localization {D C F:Type} [za6 D] [za6 C] [zrb F]
    [zZE D F] [zZE D C] [zZE C F] [zsf D C F]
    (M:zdT D) [zNo M C] [zAa D (integralClosure D F)] :
    zAa C (integralClosure C F) := by
  let N :=integralClosure D F
  let N' := integralClosure C F
  classical
  let j:N →ₛₗ[algebraMap D C] N' :=
    { toFun:= fun x=>⟨x,x.property.tower_top⟩
      map_add' _ _:=rfl
      map_smul' a x :=Subtype.ext (by
        change a•(x :F)=algebraMap D C a•(x :F)
        simp only [zd5,zG3 D C F]) }
  obtain ⟨s,hs⟩:=Module.Finite.fg_top (R:=D) (M:=N)
  let T:=zLD C ((s.image j:Finset N') :Set N')
  refine ⟨s.image j,top_unique fun x _ => ?_⟩
  have hj (y :N) :j y∈T:= by
    have hle :zLD D (s :Set N)≤T.comap j :=
      Submodule.span_le.mpr fun a ha =>
        Submodule.subset_span (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    rw [hs] at hle
    exact hle (Submodule.mem_top (x :=y))
  obtain ⟨m,hm⟩:=IsIntegral.exists_multiple_integral_of_isLocalization M (x :F) x.property
  let y :N :=⟨_,hm⟩
  have he :j y=algebraMap D C m•x :=Subtype.ext (by
    change (m:D)•(x :F)=algebraMap D C m•(x :F)
    simp only [zd5,zG3 D C F])
  have hmul :=hj y
  rw [he] at hmul
  obtain ⟨u,hu⟩:=IsLocalization.map_units C m
  have h:=T.smul_mem (↑u⁻¹:C) hmul
  rw [← mul_smul,← hu,Units.inv_mul,one_smul] at h
  exact h
private theorem normal_of_localization (k D C F:Type) [zrb k] [IsAlgClosed k]
    [za6 D] [ztn D] [za6 C] [zrb F]
    [zZE k D] [zUK k D] [zZE D F] [z0o D F]
    [zZE D C] [zZE C F] [zsf D C F]
    (M:zdT D) [zNo M C] :
    IsNoetherianRing (integralClosure C F)∧zAa C (integralClosure C F) := by
  have :IsNoetherianRing C :=
    IsLocalization.isNoetherianRing M C (Algebra.FiniteType.isNoetherianRing k D)
  have :zAa D (integralClosure D F) :=finite_affine k D F
  have h:zAa C (integralClosure C F) :=finite_localization M
  exact ⟨IsNoetherianRing.of_finite C (integralClosure C F),h⟩
private theorem adjoin_fractions {k F:Type} [zrb k] [zrb F] [zZE k F]
    (D:zTg k F) (M:zdT D) (S:Set F)
    (hS : ∀ x∈S,∃ b t:D,t∈M∧x*(t:F)=(b:F))
    {x :F} (hx :x∈zum k S) :
    ∃ b t:D,t∈M∧x*(t:F)=(b:F) := by
  induction hx using z90 with
  | mem x hx=>exact hS x hx
  | algebraMap c=>exact ⟨algebraMap k D c,1,one_mem M,mul_one _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b,s,hs,hx⟩:=hx
    obtain ⟨c,t,ht,hy⟩:=hy
    refine ⟨b*t+c*s,s*t,mul_mem hs ht,?_⟩
    change (x+y)*((s :F)*(t:F))=(b:F)*t+(c:F)*s
    calc
      _=(x*(s :F))*t+(y*(t:F))*s := by ring
      _ = _:= by rw [hx,hy]
  | mul x y _ _ hx hy =>
    obtain ⟨b,s,hs,hx⟩:=hx
    obtain ⟨c,t,ht,hy⟩:=hy
    refine ⟨b*c,s*t,mul_mem hs ht,?_⟩
    change (x*y)*((s :F)*(t:F))=(b:F)*c
    rw [mul_mul_mul_comm,hx,hy]
private theorem normal_of_fractions {k F:Type} [zrb k] [IsAlgClosed k]
    [zrb F] [zZE k F] (D C:zTg k F) (M:zdT D) (hle :D ≤C)
    [zUK k D] [z0o D F]
    (hu : ∀ m:M,IsUnit (zDu hle m.val))
    (hf : ∀ x∈C,∃ b t:D,t∈M∧x*(t:F)=(b:F)) :
    IsNoetherianRing (integralClosure C F)∧zAa C (integralClosure C F) := by
  let:zZE D C:=(zDu hle).toRingHom.toAlgebra
  have :=zsL (R:=D) (S:=C) (A:=F) fun _=>rfl
  have :zNo M C:= by
    refine ⟨⟨hu,?_,?_⟩⟩
    · intro a
      obtain ⟨b,s,hs,he⟩:=hf a.val a.property
      exact ⟨⟨b,⟨s,hs⟩⟩,Subtype.ext he⟩
    · intro a b h
      have hab:=Subalgebra.inclusion_injective hle h
      exact ⟨1,by rw [hab]⟩
  exact normal_of_localization k D C F M
theorem chart_of_seed {k E F Γ:Type} [zrb k] [IsAlgClosed k]
    [zrb E] [zZE k E] [zrb F] [zZE k F] [LinearOrderedCommGroupWithZero Γ]
    (v :Valuation E Γ) (f :E →ₐ[k] F) (B:zTg k E) (s :Set F)
    (hB:zUK k B) (hs :s.Finite)
    (hreg : ∀ b:B,v (b:E)≤1)
    (hden : ∀ a :v.valuationSubring,∃ b t:B,v (t:E)=1∧(a :E)*(t:E)=b)
    (hf :z0o (B.map f ⊔ zum k s :zTg k F) F) :
    let C:=zum k (Set.range (fun a :v.valuationSubring=>f (a :E))∪s)
    IsNoetherianRing (integralClosure C F)∧zAa C (integralClosure C F) := by
  let D:=B.map f ⊔ zum k s
  let C:=zum k (Set.range (fun a :v.valuationSubring=>f (a :E))∪s)
  have :z0o D F:=hf
  have :zUK k D:=(ztE D).mp
    (((ztE B).mpr hB).map f |>.sup
      ((ztE _).mpr (zTV hs)))
  have hle :D ≤C:= by
    apply sup_le
    · rintro _ ⟨b,hb,rfl⟩
      exact zkk (Or.inl ⟨⟨b,hreg ⟨b,hb⟩⟩,rfl⟩)
    · exact Algebra.adjoin_le fun _ ha=>zkk (Or.inr ha)
  let seedD:B →+* D:=(f.toRingHom.comp (algebraMap B E)).codRestrict D.toSubring (fun a =>
    (show B.map f≤D from le_sup_left) ⟨a,a.property,rfl⟩)
  let U:zdT B :=
    { carrier := {s | v (s :E)=1}
      one_mem' := map_one v
      mul_mem' := by
        intro a b ha hb
        change v (a :E)=1 at ha
        change v (b:E)=1 at hb
        change v ((a :E)*(b:E))=1
        rw [map_mul,ha,hb,mul_one] }
  let M:=U.map seedD.toMonoidHom
  apply normal_of_fractions D C M hle
  · rintro ⟨_,b,hb,rfl⟩
    change v (b:E)=1 at hb
    let a :v.valuationSubring :=⟨(b:E)⁻¹,by
      change v ((b:E)⁻¹)≤1
      rw [map_inv₀,hb,inv_one]⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨f (a :E),zkk (Or.inl ⟨a,rfl⟩)⟩,Subtype.ext ?_⟩
    change f (b:E)*f ((b:E)⁻¹)=1
    rw [← map_mul,mul_inv_cancel₀ (v.ne_zero_iff.mp (hb.trans_ne one_ne_zero)),map_one]
  · intro x hx
    refine adjoin_fractions D M _ (fun y hy => ?_) hx
    rcases hy with ⟨a,rfl⟩ | hy
    · obtain ⟨b,t,ht,he⟩:=hden a
      refine ⟨seedD b,seedD t,⟨t,ht,rfl⟩,?_⟩
      change f (a :E)*f (t:E)=f (b:E)
      rw [← map_mul,he]
    · exact ⟨⟨y,(show zum k s≤D from le_sup_right) (zkk hy)⟩,
        1,one_mem M,mul_one y⟩
end
end q6hv5Ed
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q6hv5Ed
noncomputable section
open cu (L)
open qNu3xvc
variable {E :Type} [zrb E] [zZE L E]
private def coords (A:Equation E) (r :Bool) :Set (EC A) :=
  {amm A,jU A r,jet A r}
private abbrev seedAlg (A:Equation E) :E →ₐ[L] EC A :=
  ⟨seed A,fun _=>rfl⟩
private abbrev AffineChart (A:Equation E) (B:zTg L E) (r :Bool) :=
  B.map (seedAlg A) ⊔ zum L (coords A r)
private theorem affineSeed_mem (A:Equation E) (B:zTg L E) (r :Bool) (a :B) :
    seed A (a :E)∈AffineChart A B r :=
  (show B.map (seedAlg A)≤AffineChart A B r from le_sup_left) ⟨a,a.property,rfl⟩
private theorem affineCoord_mem (A:Equation E) (B:zTg L E) (r :Bool)
    {z :EC A} (hz :z∈coords A r) :z∈AffineChart A B r :=
  (show zum L (coords A r)≤AffineChart A B r from le_sup_right)
    (zkk hz)
private theorem poly_mem {R F:Type} [za6 R] [zrb F] (f :zM1 R →+* F)
    (T:Subfield F) (hC : ∀ a,f (z1z a)∈T) (hX:f z7y∈T)
    (q:zM1 R) :f q∈T:= by
  induction q using Polynomial.induction_on' with
  | add a b ha hb=>rw [map_add]; exact T.add_mem ha hb
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow]
    exact T.mul_mem (hC _) (T.pow_mem hX _)
private theorem affine_fraction (A:Equation E) (B:zTg L E) (r :Bool)
    [z0o B E] :z0o (AffineChart A B r) (EC A) := by
  let D:=AffineChart A B r
  let F:=EC A
  let g:FractionRing D →ₐ[D] F :=
    IsFractionRing.liftAlgHom (g:=Algebra.ofId D F) (show zq4 (algebraMap D F)
      from Subtype.val_injective)
  let T:=g.toRingHom.fieldRange
  have hD {a :F} (ha :a∈D) :a∈T :=
    ⟨algebraMap D (FractionRing D) ⟨a,ha⟩,g.commutes ⟨a,ha⟩⟩
  have hseed (a :E) :seed A a∈T:= by
    obtain ⟨b,s,_,rfl⟩:=zJC B a
    rw [map_div₀]
    exact T.div_mem (hD (affineSeed_mem A B r b)) (hD (affineSeed_mem A B r s))
  have hx :amm A∈T:=hD (affineCoord_mem A B r (Set.mem_insert _ _))
  have hy :a7W A z7y∈T:= by
    have hy' : jU A r∈T :=
      hD (affineCoord_mem A B r (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    cases r with
    | false=>exact hy'
    | true =>
      change (a7W A z7y)⁻¹∈T at hy'
      exact inv_mem_iff.mp hy'
  have hinner (p:zM1 E) :a7W A (z1z p)∈T :=
    poly_mem ((a7W A).comp z1z) T hseed hx p
  have hlo (b:AdjoinRoot A.f) :algebraMap (AdjoinRoot A.f) F b∈T:= by
    obtain ⟨p,rfl⟩:=AdjoinRoot.mk_surjective b
    exact poly_mem (a7W A) T hinner hy p
  apply IsFractionRing.of_algEquiv (AlgEquiv.ofBijective g ⟨g.injective,?_⟩)
  intro a
  apply (RingHom.mem_fieldRange (f :=g.toRingHom)).mp
  obtain ⟨b,s,_,rfl⟩:=zJC (AdjoinRoot A.f) a
  exact T.div_mem (hlo b) (hlo s)
end
end q6hv5Ed
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
namespace qc2iTLd
noncomputable section


open qrKC9pb
open qyUzJvd
open aKx (bzg)
open scoped nonZeroDivisors
private theorem finite_frobenius (k A:Type) [zrb k] [IsAlgClosed k]
    [za6 A] [zZE k A] [zUK k A] (p n:ℕ) [ExpChar A p] :
    zAa (bzg A p n) A:= by
  obtain ⟨s,hs⟩:=(inferInstance :zUK k A).out
  let S:=bzg A p n
  let U:=zum S (s :Set A)
  have hU (a :A) (ha :a∈zum k (s :Set A)) :a∈U:= by
    induction ha using z90 with
    | mem a ha=>exact Algebra.subset_adjoin ha
    | algebraMap c =>
      obtain ⟨b,hb⟩:=IsAlgClosed.exists_pow_nat_eq c (expChar_pow_pos A p n)
      refine U.algebraMap_mem ⟨algebraMap k A c,⟨algebraMap k A b,?_⟩⟩
      calc
        _=algebraMap k A (b^p^n) :=(map_pow (algebraMap k A) b _).symm
        _=algebraMap k A c:=congrArg (algebraMap k A) hb
    | add a b _ _ ha hb=>exact U.add_mem ha hb
    | mul a b _ _ ha hb=>exact U.mul_mem ha hb
  have htop:U = ⊤ := top_unique fun a _=>hU a (by rw [hs]; exact Algebra.mem_top)
  have :zAa S (⊤ : zTg S A) := by
    rw [← htop]
    refine Module.Finite.of_fg (fg_adjoin_of_finite (R:=S) s.finite_toSet ?_)
    intro a _
    apply IsIntegral.of_pow (expChar_pow_pos A p n)
    exact isIntegral_algebraMap (x :=(iterateFrobenius A p n).rangeRestrict a)
  exact Module.Finite.equiv (Subalgebra.topEquiv (R:=S) (A:=A)).toLinearEquiv
private theorem b29 (A E :Type) [za6 A] [ztn A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [zrb E]
    [zZE A E] [zZE (FractionRing A) E] [zsf A (FractionRing A) E]
    [FiniteDimensional (FractionRing A) E]
    (hf : ∀ p n:ℕ,∀ [ExpChar A p],zAa (bzg A p n) A) :
    zAa A (integralClosure A E) := by
  let K:=FractionRing A
  let F:=separableClosure K E
  let B:=integralClosure A E
  let C:=integralClosure A F
  have :zsf A F E :=zsL fun _=>rfl
  have :zAa A C:=IsIntegralClosure.finite A K F C
  let p:=ringExpChar E
  have :ExpChar E p:=ringExpChar.expChar E
  have hinj:zq4 (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (zxb A K)
  have :ExpChar A p:=(algebraMap A E).expChar hinj p
  have :ExpChar F p:=(algebraMap F E).expChar (algebraMap F E).injective p
  let n:=IsPurelyInseparable.exponent F E
  let S:=bzg A p n
  let σ:A →+* S:=(iterateFrobenius A p n).rangeRestrict
  let e :A ≃+* S:=RingEquiv.ofBijective σ
    ⟨fun _ _ h=>iterateFrobenius_inj A p n (congrArg Subtype.val h),
      (iterateFrobenius A p n).rangeRestrict_surjective⟩
  have :RingHomInvPair (e :A →+* S) (e.symm:S →+* A) :=RingHomInvPair.of_ringEquiv e
  have :RingHomInvPair (e.symm:S →+* A) (e :A →+* S) :=RingHomInvPair.of_ringEquiv e.symm
  have :IsNoetherianRing S:=isNoetherianRing_of_ringEquiv A e
  have :zAa S A:=hf p n
  have :zAa S C:=Module.Finite.trans A C
  let φ:E →+* F:=IsPurelyInseparable.iterateFrobenius F E p (n:=n) le_rfl
  have hφ (b:E) :algebraMap F E (φ b)=b^p^n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius F p le_rfl b
  let g:B →+* C :=
    (φ.comp B.val.toRingHom).codRestrict C.toSubring (fun b=> by
      change IsIntegral A (φ b.val)
      apply (IntermediateField.coe_isIntegral_iff (R:=A)).mp
      change IsIntegral A (algebraMap F E (φ b.val))
      rw [hφ]
      exact (show IsIntegral A b.val from b.property).pow _)
  let f :B →ₛₗ[(e :A →+* S)] C :=
    { g with
      map_smul' a b:= by
        apply Subtype.ext
        apply (algebraMap F E).injective
        change algebraMap F E (φ (a•b.val)) =
          algebraMap F E ((a^p^n)•φ b.val)
        simp only [zd5]
        rw [hφ,mul_pow,map_mul,← zG3 A F E,map_pow,hφ] }
  apply Module.Finite.of_injective f
  intro b b' hb
  apply Subtype.ext
  apply iterateFrobenius_inj E p n
  change b.val^p^n=b'.val^p^n
  rw [← hφ,← hφ]
  exact congrArg (fun c:C=>algebraMap F E c.val) hb
private theorem finite_fraction_extension (A B K E :Type) [za6 A] [ztn A]
    [za6 B] [ztn B] [zrb K] [zrb E] [zZE A K] [zZE A B] [zZE A E]
    [zZE B E] [zZE K E] [z0o B E] [zsf A B E]
    [zsf A K E] [zAa A B] (hinj:zq4 (algebraMap A E)) :
    FiniteDimensional K E := by
  classical
  obtain ⟨s,hs⟩ := ‹zAa A B›
  refine ⟨⟨s.image (algebraMap B E),?_⟩⟩
  have hi: (↑(Ideal.span ({(1 :B)} : Set B)) :Set B)⊆zLD A (s :Set B) := by
    rw [hs]
    exact Set.subset_univ _
  have hall:=IsFractionRing.ideal_span_singleton_map_subset A (K:=K) hinj hi
  rw [map_one,Ideal.span_singleton_one] at hall
  rw [Finset.coe_image]
  exact top_unique fun z _=>hall (show z∈(⊤ : Ideal E) from trivial)
private theorem finite_affine_normalization (k B E :Type) [zrb k] [IsAlgClosed k]
    [za6 B] [ztn B] [zZE k B] [zUK k B]
    [zrb E] [zZE B E] [z0o B E] :
    zAa B (integralClosure B E) := by
  obtain ⟨d,g,hg,hfin⟩:=exists_finite_inj_algHom_of_fg k B
  let A:=MvPolynomial (Fin d) k
  let:zZE A B:=g.toRingHom.toAlgebra
  have :zAa A B:=hfin
  let:zZE A E :=((algebraMap B E).comp (algebraMap A B)).toAlgebra
  have :zsf A B E :=zD8 rfl
  have hinj:zq4 (algebraMap A E) :=(zxb B E).comp hg
  have :FaithfulSMul A E :=(faithfulSMul_iff_algebraMap_injective A E).2 hinj
  let K:=FractionRing A
  let:zZE K E :=FractionRing.liftAlgebra A E
  have :zsf A K E :=FractionRing.isScalarTower_liftAlgebra A E
  have :FiniteDimensional K E :=finite_fraction_extension A B K E hinj
  have :zAa A (integralClosure A E) :=
    b29 A E (fun p n _=>finite_frobenius k A p n)
  let C:=integralClosure B E
  let:zZE A C:=((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have :zsf A B C:=zD8 rfl
  have hf :zAa A C:= by
    let f :integralClosure A E →ₗ[A] C :=
      { toFun:= fun z=>⟨z.val,z.property.tower_top⟩
        map_add' := fun _ _=>rfl
        map_smul' := fun _ _=>rfl }
    apply Module.Finite.of_surjective f
    intro z
    exact ⟨⟨z.val,isIntegral_trans z.val z.property⟩,rfl⟩
  exact Module.Finite.of_restrictScalars_finite A B C
end
end qc2iTLd
end
