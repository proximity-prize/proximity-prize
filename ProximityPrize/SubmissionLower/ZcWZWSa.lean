import ProximityPrize.SubmissionLower.ZTNySHa
import ProximityPrize.SubmissionLower.Zc6ZBRc
import ProximityPrize.SubmissionLower.ZwuC0Sd
import ProximityPrize.SubmissionLower.ZVybVna
set_option Elab.async false
open _root_ renaming Algebra.FormallySmooth → ziC, Algebra.IsSeparable → zw7, Fin.sum_univ_four → zmL, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.ringHom_ext → zXT, Nat.mul_le_mul_left → zBI, Polynomial → zM1, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.ker → zdq, Set.image_singleton → zyk
set_option maxHeartbeats 900000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qcYgGze
noncomputable section
open Polynomial
open cu (FX Shape Jet)
open gT (Ambient aQ gk iJ)
open pI (xN oU pN dot weight F7)
open ac3 (a2T)
open ac4 (aJA gtR de3 Hr btg aMp)
open P6_7 (RectTail)
open P6_7_2_3 (terminalAllowance pointWeight sectionMass)
open qu56FMb (RectCaps points s PaidOn)
open TD (FP)
open private coeff_toJet from ProximityPrize.SubmissionLower.ZTNySHa
open private aqH bOX from ProximityPrize.SubmissionLower.AH
open private exK from ProximityPrize.SubmissionLower.H
open private dX0 from ProximityPrize.SubmissionLower.CR
open scoped Classical BigOperators
private def triangle (S:Shape) :Shape :=⟨S.m,S.B,S.J,2*S.U⟩
theorem nested_caps {S:Shape} {F:Ambient} (hc:RectCaps S F) :
    ∃ P:Jet,iJ P=F∧oU P (triangle S) := by
  have he :iJ (aqH F)=F:= by rw [bOX]; exact aqH.symm_apply_apply _
  refine ⟨aqH F,he,?_⟩
  generalize aqH F=P at he ⊢
  subst F
  intro j i h
  have term (d:Fin 2 →₀ ℕ) (hd: ((P.coeff j).coeff i).coeff d≠0) :
      d 0≤S.U∧d 1≤S.U∧i+j≤S.B∧j≤S.J:= by
    let a :Fin 4 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![d 0,d 1,i,j]
    have hcoeff : (iJ P).coeff a=((P.coeff j).coeff i).coeff d:= by
      rw [coeff_toJet]
      congr 1
      ext k
      fin_cases k <;> rfl
    exact hc a (MvPolynomial.mem_support_iff.mpr (hcoeff ▸ hd))
  obtain ⟨d,hd⟩:=Finset.nonempty_iff_ne_empty.mpr
    (fun hx=>h (MvPolynomial.support_eq_empty.mp hx))
  obtain ⟨_,_,hB,hJ⟩:=term d (MvPolynomial.mem_support_iff.mp hd)
  refine ⟨hB,hJ,Finset.sup_le fun e he' => ?_⟩
  obtain ⟨h₀,h₁,_,_⟩:=term e (MvPolynomial.mem_support_iff.mp he')
  change e.degree≤2*S.U
  rw [Finsupp.degree_eq_sum,Fin.sum_univ_two]
  omega
theorem btG (b:RectTail) {Q:znc Ambient} {F:Ambient}
    (hQ:xN Q) (hc:RectCaps (s b) F) (hf :F∉Q) :
    ((points Q F).card:ℚ)≤FP (terminalAllowance b) (sectionMass Q) := by
  obtain ⟨P,rfl,hP⟩:=nested_caps hc
  have hs : (s b).J≤(s b).B:= by cases b <;> decide
  have h:=ac6.Bridge.dSJ (triangle (s b)) Q P hs hQ hP hf
  change ((a2T Q P).card:ℚ)≤_
  have hcast: (dot (weight (triangle (s b)) 2) (pN Q) :ℚ) =
      FP (terminalAllowance b) (sectionMass Q) := by
    simp [dot,FP,weight,triangle,terminalAllowance,pointWeight,sectionMass,
      zmL]
  rw [← hcast]
  exact_mod_cast h
theorem ordinate_class (I:znc Ambient) (hp:I.IsPrime) :
    To 2 I = ⊤ ∨ ((To 2 I).IsPrime∧(To 2 I).comap sliceBase=I) := by
  by_cases hi:zq4 ((zVv I).comp F7)
  · exact Or.inr ((btg I hp).1 hi)
  · exact Or.inl ((btg I hp).2 hi)
theorem eHU {S:Shape} {Q:znc Ambient} {F:Ambient}
    (hQ:xN Q) (hc:RectCaps S F) (hf :F∉Q) :
    zAa aQ (gk (cutSlice 2 Q F)) ∧
    zsE aQ (gk (cutSlice 2 Q F)) ≤
      2*S.U*pN Q 1+S.J*pN Q 3:= by
  obtain ⟨P,rfl,hP⟩:=nested_caps hc
  obtain ⟨hprime,hcomap⟩:=(btg Q hQ.prime).1 hQ.ordinate_dominant
  have hd:=czb.proof Q hQ.prime hQ.dimension hQ.ordinate_dominant
  obtain ⟨hseed,hv,hseedRank,hvRank⟩ :=
    czc.proof Q hQ.a6j hQ.jet_finite
  obtain ⟨hJ,hU⟩:=gtR hP
  have hmem:aMp (aJA P) - sliceBase (iJ P)∈Hr Q:= by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,de3]
    exact sub_self _
  have hproper :aMp (aJA P)∉Hr Q:= by
    intro h
    apply hf
    rw [← hcomap]
    exact show sliceBase (iJ P)∈Hr Q from
      (Submodule.sub_mem_iff_right _ h).mp hmem
  have hbound:=dX0 aQ (Hr Q) (2*S.U) S.J _
    hprime hd hseed hv hJ hU hproper
  have heq :Hr Q ⊔ zye {aMp (aJA P)} =
      cutSlice 2 Q (iJ P) := by
    change Hr Q ⊔ zye {_} = Hr Q ⊔ zye {_}
    apply le_antisymm <;> refine sup_le le_sup_left ((zvl _).mpr ?_)
    · simpa only [sub_add_cancel] using
        Ideal.add_mem _ (zKg hmem)
          (zs0 (z5J (sliceBase (iJ P))))
    · simpa only [sub_sub_cancel] using
        Ideal.sub_mem _ (zs0 (z5J
          (aMp (aJA P)))) (zKg hmem)
  rw [heq,hseedRank,hvRank] at hbound
  exact hbound
private theorem taylor_eq :
    (Rk.taylor :Ambient →+* MvPolynomial (Fin 4) Ambient) =
      agL.Uz := by
  apply zXT
  · intro a
    simp [Rk.taylor,agL.Uz]
  · intro i
    simp [Rk.taylor,agL.Uz,add_comm]
theorem paid_order {I:znc Ambient} [I.IsPrime]
    [ziC FX (IsLocalRing.ResidueField (Localization.AtPrime I))]
    {F:Ambient} {r :ℕ} (h:PaidOn F r I) :
    ∃ a :Ambient,a∉I∧a*F∈I^(r+1) := by
  let A:=Localization.AtPrime I
  let loc:Ambient →ₐ[FX] A:=IsScalarTower.toAlgHom FX Ambient A
  have hg (e :Fin 4 →₀ ℕ) (he :agL.EY e< r+1) :
      loc (agL.BV e F)∈IsLocalRing.maximalIdeal A:= by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff A I _).mpr
    have he' : (∑ i,e i)≤ r := by
      simpa [agL.EY,Finsupp.sum_fintype] using Nat.le_of_lt_succ he
    simpa only [Rk.KR,taylor_eq,agL.taylor_coeff] using h e he'
  have hw:=exK (K:=FX) (A:=A) (n:=4) loc F (r+1) hg
  change algebraMap Ambient A F∈_ at hw
  rwa [← Localization.AtPrime.map_eq_maximalIdeal (I:=I),← Ideal.map_pow,
    IsLocalization.algebraMap_mem_map_algebraMap_iff I.primeCompl A] at hw
end
end qcYgGze
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qcYgGze
noncomputable section
open cu (FX Shape jz aZ)
open gT (Ambient aQ gk ek B4)
open pI (xN pN)
open WJ
open qu56FMb (RectCaps)


open private qw vV aEa deu gr6 from ProximityPrize.SubmissionLower.U
open scoped nonZeroDivisors
open private dYa from ProximityPrize.SubmissionLower.CR
def jetElim:SliceRing →ₐ[aQ] yT aQ :=
  MvPolynomial.aeval ![z9v (some 0),z9v (some 1),
    znf (ek 1)-MvPolynomial.C (ek 0)*z9v none,
    z9v none]
theorem jetElim_base :jetElim.toRingHom.comp sliceBase=Mv := by
  apply zXT
  · intro a
    simp [jetElim,Mv,zQb]
  · intro i
    simp [jetElim,Mv,zQb]
private def reinsert :yT aQ →ₐ[aQ] SliceRing :=
  MvPolynomial.rename fun i=>i.elim 3 (Fin.castAdd 2)
private theorem jetElim_right:Function.RightInverse reinsert jetElim:= by
  have h:jetElim.comp reinsert=AlgHom.id aQ (yT aQ) := by
    ext i
    cases i with
    | none=>simp [jetElim,reinsert]
    | some i=>fin_cases i <;> simp [jetElim,reinsert]
  exact AlgHom.congr_fun h
private theorem jetElim_ker :zdq jetElim.toRingHom=zye {B4 2 3} := by
  let D:znc SliceRing:=zye {B4 2 3}
  let q:=zVv D
  have hzero :q (B4 2 3)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
    (z5J _)
  have h: ((q.comp reinsert.toRingHom).comp jetElim.toRingHom)=q:= by
    apply zXT
    · intro a
      simp [jetElim,reinsert,zQb]
    · intro i
      change q (reinsert (jetElim (z9v i)))=q (z9v i)
      rw [jetElim,MvPolynomial.aeval_X]
      fin_cases i
      · simp [reinsert]
      · simp [reinsert]
      · change q (reinsert (znf (ek 1) -
          znf (ek 0)*z9v none))=q (z9v 2)
        simp only [map_sub,map_mul,reinsert,MvPolynomial.rename_C,MvPolynomial.rename_X,
          Option.elim_none]
        simp only [B4,map_add,map_sub,map_mul] at hzero
        linear_combination -hzero
      · simp [reinsert]
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he :=zLs h x
    rw [zQb,RingHom.mem_ker.mp hx,map_zero] at he
    exact he.symm
  · apply (zvl _).mpr
    apply RingHom.mem_ker.mpr
    simp [jetElim,B4]
theorem jet_comap (I:znc Ambient) :
    (RV I).comap jetElim.toRingHom=To 3 I:= by
  rw [RV,← jetElim_base,← Ideal.map_map,
    Ideal.comap_map_of_surjective jetElim.toRingHom jetElim_right.surjective,← RingHom.ker_eq_comap_bot,
    jetElim_ker]
  rfl
def jet_equiv (I:znc Ambient) :
    gk (To 3 I) ≃ₐ[aQ] XS I:= by
  let f :=(Ideal.Quotient.mkₐ aQ (RV I)).comp jetElim
  have hker :zdq f=To 3 I:= by
    change (zdq (zVv (RV I))).comap jetElim.toRingHom= _
    rw [Ideal.mk_ker,jet_comap]
  exact (Ideal.quotientEquivAlgOfEq aQ hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp jetElim_right.surjective :Function.Surjective f))
theorem avh {S:Shape} {Q:znc Ambient} {F:Ambient}
    (hQ:xN Q) (hc:RectCaps S F) (hf :F∉Q) :
    zAa aQ (gk (cutSlice 3 Q F)) ∧
    zsE aQ (gk (cutSlice 3 Q F)) ≤
      2*S.U*pN Q 2+S.B*pN Q 3:= by
  obtain ⟨P,rfl,hP⟩:=nested_caps hc
  let F:=gT.iJ P
  let D:= Q ⊔ zye {F}
  obtain ⟨hp,hd,hcomap⟩ :=
    bzV.proof Q 1 hQ.prime hQ.dimension (Or.inl (drU hQ))
  have hf' : Mv F∉RV Q:= fun h=>hf (hcomap ▸ h)
  obtain ⟨hseed,hseedRank⟩:=czh.proof Q hQ.bfE
  obtain ⟨hv,hvRank⟩:=czi.proof Q hQ.jet_finite
  let:CharP aQ K1.p:=charP_of_injective_ringHom
    ((algebraMap FX aQ).comp jz).injective K1.p
  obtain ⟨hfin,hlen⟩:=dYa aQ K1.p (RV Q) (Mv F) (2*S.U) S.B
    hp hd hf' (gsj hP) hseed hv (hseedRank.trans_lt hQ.mixed_lt)
      (hvRank.trans_lt hQ.jet_lt)
  have hD:RV D =RV Q ⊔ zye {Mv F} := by
    simp only [D,RV,Ideal.map_sup,Ideal.map_span,zyk]
  have hcut:To 3 D =cutSlice 3 Q F:= by
    simp only [D,Ideal.map_sup,Ideal.map_span,zyk,cutSlice,To]
    ac_rfl
  rw [← hcut]
  let e :=jet_equiv D
  let _:zAa aQ (XS D) := by
    change zAa aQ (gk (RV D))
    rw [hD]
    exact hfin
  refine ⟨Module.Finite.equiv e.symm.toLinearEquiv,?_⟩
  rw [e.toLinearEquiv.finrank_eq]
  change zsE aQ (gk (RV D))≤_
  rw [hD]
  exact hlen.trans (Nat.add_le_add (zBI _ hseedRank) (zBI _ hvRank))
theorem jet_class (I:znc Ambient) (hp:I.IsPrime) :
    To 3 I = ⊤ ∨ ((To 3 I).IsPrime∧(To 3 I).comap sliceBase=I) := by
  let:I.IsPrime :=hp
  by_cases hi:zq4 (qw I)
  · let:CommRing (zM1 (gk I)) :=
      @Polynomial.commRing (gk I) (Ideal.Quotient.commRing I)
    let:Algebra (zM1 (gk I)) (XS I) :=(vV I).toAlgebra
    have :=deu I hi
    have hM: (aZ⁰).map (qw I)≤(zM1 (gk I))⁰:= by
      rintro _ ⟨a,ha,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (fun h =>
        (mem_nonZeroDivisors_iff_ne_zero.mp ha) (hi (h.trans (map_zero _).symm)))
    have :IsDomain (XS I) :=IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
    have hprime : (RV I).IsPrime :=(Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    refine Or.inr ⟨jet_comap I ▸ hprime.comap jetElim.toRingHom,?_⟩
    rw [← jet_comap,Ideal.comap_comap,jetElim_base,gr6 I hi]
  · obtain ⟨a,b,he,hn⟩:=Function.not_injective_iff.mp hi
    let c:=algebraMap aZ aQ (a-b)
    have hc:c≠0:= fun h =>
      hn (sub_eq_zero.mp ((IsFractionRing.injective aZ aQ) (h.trans (map_zero _).symm)))
    have hz :algebraMap aQ (XS I) c=0:= by
      have hh:=zLs (aEa I) (a-b)
      simpa only [zQb,map_sub,he,sub_self,map_zero,← show
        algebraMap aZ aQ (a-b)=c from rfl] using hh.symm
    have hm:znf c∈RV I:=Ideal.Quotient.eq_zero_iff_mem.mp hz
    have htop:=(RV I).eq_top_of_isUnit_mem hm
      ((isUnit_iff_ne_zero.mpr hc).map (znf:aQ →+* yT aQ))
    exact Or.inl (by rw [← jet_comap,htop,Ideal.comap_top])
end
end qcYgGze
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qcYgGze
noncomputable section
open Finset
open P6 (p)

open P6_7_2_3 (sectionMass)
open qu56FMb (RectCaps qv curveMass divisorMass paidWeight PaidOn firstMass firstWeight s r)
open cu (FX Shape)
open gT (Ambient aQ gk)
open pI (xN pN)
open ac3 (aYy bZk)
open YY (aef)
open TD (FP)
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ (I:znc Ambient) [I.IsPrime],ringKrullDim (gk I)=1 →
    ¬ aYy I→aef I<p →
    zw7 (SeedParameterField I) (SlopedResidue I)
def c2 :Prop :=
  ∀ (I:znc Ambient) [I.IsPrime],ringKrullDim (gk I)=1 →
    ¬ aYy I→zw7 (SeedParameterField I) (SlopedResidue I) →
    ziC FX (CurveResidue I)
private theorem slice_weighted (hsep:c1) (hsmooth:c2) {Q:znc Ambient} {F:Ambient} {S:Shape}
    {r :ℕ} (hQ:xN Q) (hF:F∉Q) (hc:RectCaps S F)
    (hsmall : ∀ I∈qv Q F,aef I<p) (k :Fin 4)
    (hclass : ∀ I:znc Ambient,I.IsPrime →
      To k I = ⊤ ∨ ((To k I).IsPrime∧(To k I).comap sliceBase=I))
    (hfinite :zAa aQ (gk (cutSlice k Q F))) :
    divisorMass Q F r (fun I=>curveMass I k) ≤
      (zsE aQ (gk (cutSlice k Q F)) :ℚ) := by
  let C:=qv Q F
  let H :=To k Q
  let M (i:C) :=To k i.val
  have hcut (i:C) :Q ⊔ zye {F} ≤ i.val :=
    (Ideal.mem_minimalPrimesFinset.mp (mem_filter.mp i.property).1).le
  have hle (i:C) :cutSlice k Q F≤M i:= by
    apply sup_le (sup_le_sup (Ideal.map_mono (le_sup_left.trans (hcut i))) le_rfl)
    apply (zvl _).mpr
    exact zKg (z7X _ (hcut i
      (zs0 (z5J _))))
  rcases hclass Q hQ.prime with htop | ⟨hprime,hcomap⟩
  · have hz :divisorMass Q F r (fun I=>curveMass I k)=0:= by
      apply sum_eq_zero
      intro I hI
      have hI' : To k I = ⊤ := top_unique (htop ▸ le_sup_left.trans (hle ⟨I,hI⟩))
      have he :zsE aQ (gk (To k I))=0:= by
        rw [hI']
        exact Module.finrank_zero_of_subsingleton
      change (paidWeight F r I:ℚ)*(zsE aQ
        (gk (To k I)) :ℚ)=0
      rw [he]
      simp
    rw [hz]
    exact Nat.cast_nonneg _
  have hf' : sliceBase F∉H := fun h=>hF (hcomap ▸ h)
  obtain ⟨P,hP,_⟩:=nested_caps hc
  have hg (i:C) :i.val.IsPrime∧ringKrullDim (gk i.val)=1 := by
    apply bZk hQ (hP.symm ▸ hF)
    simpa only [ac3.aT1,qu56FMb.cut,hP] using (mem_filter.mp i.property).1
  have hM (i:C) :=hclass i.val (hg i).1
  have hdis (i j:C) (hij:i≠j) (hi:M i ≠ ⊤) (hj:M j ≠ ⊤) :M i≠M j:= by
    intro he
    apply hij
    apply Subtype.ext
    exact (((hM i).resolve_left hi).2.symm.trans
      (congrArg (Ideal.comap sliceBase) he)).trans ((hM j).resolve_left hj).2
  have hw (i:C) :0<paidWeight F r i.val := by
    by_cases h:PaidOn F r i.val <;> simp [paidWeight,h]
  have hp (i:C) (hi:M i ≠ ⊤) :
      ∃ a :SliceRing,a∉M i∧a*sliceBase F∈M i^paidWeight F r i.val := by
    by_cases hd:PaidOn F r i.val
    · let:i.val.IsPrime :=(hg i).1
      have hmove : ¬ aYy i.val :=(mem_filter.mp i.property).2
      let:ziC FX (CurveResidue i.val) :=
        hsmooth i.val (hg i).2 hmove (hsep i.val (hg i).2 hmove (hsmall i.val i.property))
      obtain ⟨a,ha,he⟩:=paid_order hd
      refine ⟨sliceBase a,fun ham=>ha (((hM i).resolve_left hi).2 ▸ ham),?_⟩
      rw [paidWeight,ite_eq_left hd,← map_mul]
      have hm:=z7X sliceBase he
      rw [Ideal.map_pow] at hm
      exact Ideal.pow_right_mono (show i.val.map sliceBase≤M i from le_sup_left) _ hm
    · obtain ⟨hprime,_⟩:=(hM i).resolve_left hi
      refine ⟨1,fun h=>hprime.ne_top ((Ideal.eq_top_iff_one _).mpr h),?_⟩
      simp only [paidWeight,ite_eq_right hd,pow_one,one_mul]
      exact hle i (zs0 (z5J _))
  let _:=hfinite
  have hb:=dlW (k :=aQ) hprime hf' M (fun i=>paidWeight F r i.val)
    (fun i=>(hM i).imp_right And.left) hdis hle hw hp
  change (∑ I∈C,(paidWeight F r I:ℚ) *
    (zsE aQ (gk (To k I)) :ℚ))≤_
  rw [← sum_attach]
  exact_mod_cast hb
theorem of_children (h1 :c1) (h2 :c2) :qu56FMb.c2 := by
  intro b x o Q hQ _ _ _ F hsmall
  have hc:RectCaps (s b) F.row:=F.caps
  refine ⟨?_,btG b hQ hc F.proper⟩
  intro k hk
  rcases hk with rfl | rfl
  · obtain ⟨hfin,hlen⟩:=eHU hQ hc F.proper
    apply (slice_weighted h1 h2 hQ F.proper hc hsmall 2 ordinate_class hfin).trans
    have hp:firstMass (s b) Q 2 =
        ((2*(s b).U*pN Q 1+(s b).J*pN Q 3:ℕ) :ℚ) := by
      simp [firstMass,firstWeight,FP,sectionMass,zmL]
    rw [hp]
    exact_mod_cast hlen
  · obtain ⟨hfin,hlen⟩:=avh hQ hc F.proper
    apply (slice_weighted h1 h2 hQ F.proper hc hsmall 3 jet_class hfin).trans
    have hs : (s b).J≤(s b).B:= by cases b <;> decide
    have hp:firstMass (s b) Q 3 =
        ((2*(s b).U*pN Q 2+(s b).B*pN Q 3:ℕ) :ℚ) := by
      simp [firstMass,firstWeight,FP,sectionMass,zmL,Nat.cast_sub hs]
    rw [hp]
    exact_mod_cast hlen
end
end qcYgGze
end
