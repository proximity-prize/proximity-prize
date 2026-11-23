import ProximityPrize.SubmissionLower.Z1qPXJc
set_option Elab.async false
open _root_ renaming Algebra → zZE, Function.Injective → zq4, Function.Surjective → zpX, Ideal → znc, Ideal.Quotient.mk_surjective → zld, IsFractionRing.injective → zxb, IsFractionRing.lift_algebraMap → zoc, IsLocalization.Away.invSelf → zdx, IsLocalization.Away.lift → ztx, IsLocalization.Away.lift_eq → zaz, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.map → zDK, MvPolynomial.rename → zHw, MvPolynomial.ringHom_ext → zXT, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace P5_7_3_3_4_1_6_2
noncomputable section
open MvPolynomial
open cu (FX aZ)
open gT (aQ ek B4)
open GK (SG i9 toSlice)
open DQ (jY SourceRing Qd)
open Cu
open aqd (O4 bv8 ddp ddg)
open P5_7_3_3_4_1_6 (bzm Section gN aEL)
open scoped TensorProduct
private abbrev E :=jY 2
private abbrev W:=SourceRing 2
private def pivot:W:=z9v (some 0)
private abbrev Away :=Localization.Away pivot
private def num (i:Fin 2) :W:=z9v (![some 1,none] i)
private theorem lift_inverse {T:Type} [CommRing T] (g:W →+* T) (h:IsUnit (g pivot)) :
    g pivot* ztx (S:=Away) pivot h
      (zdx pivot)=1 := by
  simpa only [map_mul,map_one,zaz] using
    congrArg (ztx (S:=Away) pivot h)
      (IsLocalization.Away.mul_invSelf (S:=Away) pivot)
private def unnormalize :W →+* aZ :=
  eval₂Hom C (fun i:Option (Fin 2)=>i.elim (z9v 1)
    (fun j=>if j=0 then 1 else z9v 0))
private theorem unnormalize_pivot:unnormalize pivot=1 := by
  simp [unnormalize,pivot]
private def normalizeAway :aZ →+* Away :=
  eval₂Hom ((algebraMap W Away).comp C)
    (fun i=>algebraMap W Away (num i)* zdx pivot)
private theorem normalizeAway_injective :zq4 normalizeAway := by
  let h:IsUnit (unnormalize pivot) := by rw [unnormalize_pivot]; exact isUnit_one
  let r :Away →+* aZ:=ztx pivot h
  have hr :r (zdx pivot)=1 := by
    simpa only [unnormalize_pivot,one_mul] using lift_inverse unnormalize h
  have hinv :r.comp normalizeAway=RingHom.id aZ:= by
    apply zXT
    · intro a
      simp [r,normalizeAway,unnormalize]
    · intro i
      simp only [zQb,normalizeAway,eval₂Hom_X',map_mul,hr,mul_one]
      fin_cases i <;> simp [r,unnormalize,num]
  exact (show Function.LeftInverse r normalizeAway from fun p =>
    zLs hinv p).injective
private theorem pivot_ne :algebraMap W E pivot≠0 :=
  (map_ne_zero_iff _ (zxb W E)).mpr (MvPolynomial.X_ne_zero _)
private def intoE :Away →+* E :=
  ztx pivot pivot_ne.isUnit
private theorem intoE_injective :zq4 intoE := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M:=Submonoid.powers pivot)
  intro x hx
  rw [intoE,zaz] at hx
  obtain rfl :=(injective_iff_map_eq_zero _).mp (zxb W E) x hx
  exact map_zero _
private def normalScalars :aQ →+* E :=
  IsFractionRing.lift (g:=intoE.comp normalizeAway)
    (intoE_injective.comp normalizeAway_injective)
private theorem normalize_coeff (a :FX) :
    normalScalars (algebraMap FX aQ a)=algebraMap FX E a := by
  change normalScalars (algebraMap aZ aQ (C a))= _
  rw [normalScalars,zoc]
  simp only [zQb,normalizeAway,eval₂Hom_C,intoE,
    zaz]; rfl
private theorem normalize_variable (i:Fin 2) :
    Qd (some 0)*normalScalars (ek i)=algebraMap W E (num i) := by
  rw [ek,normalScalars,zoc]
  simp only [zQb,normalizeAway,eval₂Hom_X']
  change algebraMap W E pivot *
    intoE (algebraMap W Away (num i)* zdx pivot)= _
  rw [map_mul,mul_left_comm]
  change intoE (algebraMap W Away (num i)) *
    (algebraMap W E pivot*intoE (zdx pivot))= _
  rw [show algebraMap W E pivot*intoE (zdx pivot)=1
    from lift_inverse (algebraMap W E) pivot_ne.isUnit,mul_one,intoE,
    zaz]
private abbrev S {n:ℕ} (B:znc (Gc n)) :=
  Section B (Sum.inl:Fin 2→bzm n)
private abbrev ke {n:ℕ} (B:znc (Gc n)) :=
  gN B E ⊔ Ideal.span {aEL (Sum.inl:Fin 2→bzm n)}
private abbrev a8k {n:ℕ} (B:znc (Gc n)) :
    z3y (bzm n) E →ₐ[E] S B :=
  Ideal.Quotient.mkₐ E (ke B)
private theorem sectionMk_coeff {n:ℕ} (B:znc (Gc n)) (a :E) :
    a8k B (C a)=algebraMap E (S B) a :=
  (a8k B).commutes a
private def rawMk {n:ℕ} (B:znc (Gc n)) :Gc n →+* S B :=
  (a8k B).toRingHom.comp (zDK (algebraMap FX E))
private theorem raw_zero {n:ℕ} (B:znc (Gc n)) {p:Gc n}
    (hp:p∈B) :rawMk B p=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show gN B E≤ke B from le_sup_left) (Ideal.mem_map_of_mem _ hp))
private abbrev a8p {n:ℕ} : aZ →+* Gc n :=
  (zHw Sum.inl).toRingHom
private theorem chart_seed {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :
    (W8 A).comp a8p=O4 C₀:= by
  apply zXT
  · intro a
    simp [W8,O4]
  · intro i
    simp [W8,O4]
private def planePoly {n:ℕ} (B:znc (Gc n)) :
    z3y (Fin 2) aQ →+* S B :=
  eval₂Hom ((algebraMap E (S B)).comp normalScalars)
    (fun i=>a8k B (z9v (Sum.inl i)))
private theorem planePoly_raw {n:ℕ} (B:znc (Gc n)) :
    (planePoly B).comp (zDK (algebraMap FX aQ)) =
      (rawMk B).comp a8p:= by
  apply zXT
  · intro a
    change planePoly B (zDK (algebraMap FX aQ) (C a)) =
      a8k B (zDK (algebraMap FX E) (zHw Sum.inl (C a)))
    simp only [MvPolynomial.map_C,MvPolynomial.rename_C,planePoly,eval₂Hom_C,
      zQb,normalize_coeff,sectionMk_coeff]
  · intro i
    simp [planePoly,rawMk]
private theorem planePoly_line {n:ℕ} (B:znc (Gc n)) :
    planePoly B (B4 0 1)=0:= by
  let a :=algebraMap E (S B) (Qd (some 0))
  have ha :IsUnit a :=pivot_ne.isUnit.map (algebraMap E (S B))
  apply ha.mul_left_cancel
  rw [mul_zero]
  have hcut:a8k B (aEL (Sum.inl:Fin 2→bzm n))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {aEL (Sum.inl:Fin 2→bzm n)} ≤ ke B from le_sup_right)
        (Ideal.mem_span_singleton_self _))
  simp only [B4,map_sub,map_add,map_mul,planePoly,eval₂Hom_X',eval₂Hom_C,
    zQb,mul_sub,mul_add,← mul_assoc,a,← map_mul (algebraMap E (S B)),
    normalize_variable]
  simpa only [aEL,Fin.sum_univ_two,map_sub,map_add,map_mul,sectionMk_coeff,
    Qd,num,Matrix.cons_val_zero,Matrix.cons_val_one] using hcut
private def Yx {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) :
    SG (BI C₀) →+* S (EF A) :=
  Ideal.Quotient.lift _ (planePoly (EF A)) (by
    change i9 (BI C₀) 0 1≤RingHom.ker (planePoly (EF A))
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      change ((planePoly (EF A)).comp (zDK (algebraMap FX aQ))) p=0
      rw [planePoly_raw]
      apply raw_zero
      change ((W8 A).comp a8p) p=0
      rw [chart_seed]
      exact RingHom.mem_ker.mp ((bRL.proof C₀).kernel.symm ▸ hp)
    · intro p hp
      obtain rfl :=Set.mem_singleton_iff.mp hp
      exact planePoly_line _)
private abbrev planeRaw (I:znc aZ) :aZ →+* SG I :=
  (toSlice I 0 1).comp (Ideal.Quotient.mk I)
private theorem planeMap_raw {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) (p:aZ) :
    Yx A (planeRaw (BI C₀) p)=rawMk (EF A) (a8p p) :=
  zLs (planePoly_raw (EF A)) p
private theorem chart_coordinate {C₀:sQ} [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n) (i:bzm n) :
    ∃ u,Yx A u=a8k (EF A) (z9v i) := by
  cases i with
  | inl i =>
    exact ⟨planeRaw _ (z9v i),by
      rw [planeMap_raw]
      simp [rawMk]⟩
  | inr j =>
    let I:=BI C₀
    let B:=EF A
    let hC:=bRL.proof C₀
    let:I.IsPrime := by
      change (BI C₀).IsPrime
      exact hC.kernel ▸ RingHom.ker_isPrime (O4 C₀)
    let:IsDomain (aZ ⧸ I) :=Ideal.Quotient.isDomain I
    let:zZE (aZ ⧸ I) (y7 C₀) :=(bv8 C₀ hC.kernel).toAlgebra
    let:IsFractionRing (aZ ⧸ I) (y7 C₀) :=hC.localized
    let x :Gc n:=z9v (Sum.inr j)
    obtain ⟨p,q,hq,hfrac⟩:=IsFractionRing.div_surjective (aZ ⧸ I) (W8 A x)
    obtain ⟨p,rfl⟩:=zld p
    obtain ⟨q,rfl⟩:=zld q
    have hq₀:=mem_nonZeroDivisors_iff_ne_zero.mp hq
    have hq₁:O4 C₀ q≠0 :=
      (map_ne_zero_iff _ (zxb (aZ ⧸ I) (y7 C₀))).mpr hq₀
    have hrel :a8p p-a8p q*x∈B:= by
      change W8 A (a8p p-a8p q*x)=0
      rw [map_sub,map_mul,sub_eq_zero]
      change ((W8 A).comp a8p) p =
        ((W8 A).comp a8p) q*W8 A x
      rw [chart_seed]
      exact ((div_eq_iff hq₁).mp hfrac).trans (mul_comm _ _)
    have he :=raw_zero B hrel
    rw [map_sub,map_mul,sub_eq_zero,← planeMap_raw A,← planeMap_raw A] at he
    have hf :=bzY.eLP C₀ hC
    let:Nontrivial (SG I) :=hf.nontrivial
    have hqf :planeRaw I q≠0 :=
      (map_ne_zero_iff _ (bzY.gBU I)).mpr hq₀
    obtain ⟨u,hu⟩:=hf.mul_inv_cancel hqf
    refine ⟨planeRaw I p*u,?_⟩
    change Yx A (planeRaw I p*u)=a8k B (z9v (Sum.inr j))
    have hx :rawMk B x=a8k B (z9v (Sum.inr j)) := by simp [rawMk,x]
    rw [← hx,map_mul,he,mul_right_comm,← map_mul,show planeRaw I q*u=1 from hu,
      map_one,one_mul]
private theorem finite_of_generators {F G D T:Type} [Field F] [Field G]
    [CommRing D] [CommRing T] [zZE F D] [zZE G T] [zAa F D]
    {ι:Type} (s :F →+* G) (f :D →+* T)
    (hf : ∀ a,f (algebraMap F D a)=algebraMap G T (s a))
    (q:z3y ι G →ₐ[G] T) (hq:zpX q)
    (hx : ∀ i,∃ u,f u=q (z9v i)) :
    zAa G T∧zsE G T≤zsE F D:= by
  let:zZE F G:=s.toAlgebra
  let:zZE F T:=((algebraMap G T).comp s).toAlgebra
  let:IsScalarTower F G T:=IsScalarTower.of_algebraMap_eq' rfl
  let f' : D →ₐ[F] T:=⟨f,hf⟩
  let w:G ⊗[F] D →ₐ[G] T:=f'.liftEquiv F G D T
  have hw:zpX w:= by
    intro z
    obtain ⟨p,rfl⟩:=hq z
    change q p∈w.range
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨algebraMap G _ a,(w.commutes a).trans (q.commutes a).symm⟩
    | add p r hp hr =>
      rw [map_add]
      exact w.range.add_mem hp hr
    | mul_X p i hp =>
      rw [map_mul]
      obtain ⟨u,hu⟩:=hx i
      exact w.range.mul_mem hp ⟨(1 :G) ⊗ₜ[F] u,by simpa [w,f'] using hu⟩
  refine ⟨Module.Finite.of_surjective w.toLinearMap hw,?_⟩
  exact (w.toLinearMap.finrank_le_finrank_of_surjective hw).trans_eq Module.finrank_baseChange
theorem proof :P5_7_3_3_4_1_6.c2 := by
  intro C₀ hC J g n R A
  change zAa E (S (EF A))∧zsE E (S (EF A))≤C₀.totalDegree
  let:zAa aQ (SG (BI C₀)) :=Module.finite_of_finrank_pos (by
    rw [ddp]
    exact ddg C₀ hC.out)
  have hsc (a :aQ) :
      Yx A (algebraMap aQ (SG (BI C₀)) a) =
        algebraMap E (S (EF A)) (normalScalars a) := by
    change planePoly (EF A) (C a)= _
    exact eval₂Hom_C _ _ _
  obtain ⟨hf,hr⟩:=finite_of_generators (D:=SG (BI C₀))
    (T:=S (EF A)) normalScalars (Yx A) hsc
    (a8k (EF A)) zld (chart_coordinate A)
  exact ⟨hf,hr.trans_eq (ddp C₀)⟩
end
end P5_7_3_3_4_1_6_2
