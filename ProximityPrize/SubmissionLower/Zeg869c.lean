import ProximityPrize.SubmissionLower.AR
import ProximityPrize.SubmissionLower.ZskDvCd
set_option Elab.async false
open _root_ renaming Fin.sum_univ_four → zmL, Finset.sum_le_sum → zQk, Finsupp.degree_eq_sum → zFi, Finsupp.weight_eq_sum → z1K, LinearMap.ker → z83, LinearMap.mulLeft → zzN, LinearMap.range → zWl, Module.finrank → zsE, MvPolynomial.monomial → ztt, Submodule.finrank_mono → zFM, Submodule.sum_mem → zo3
section
set_option autoImplicit true
namespace P6_6_2
noncomputable section
open aR (ao)
open xE (M7 UT Local topWeight)
open akL (Jp MI ahV arP BU Oq oH
  La alM KP cpn)
open P6_6 (primaryM Wk)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open private bhx bhy Ce asF NH aWg dck coL blU eH8 aid cwS aQH bv2 cva caB from ProximityPrize.SubmissionLower.AR
open private b5V b3b from ProximityPrize.SubmissionLower.AR
open scoped BigOperators
abbrev sP:=Fin (Wk.b+1)×Offset
def TO (i:sP) :Set UT :=
  {e | FF e∧e none<primaryM∧e.weight jetDegreeWeight=i.1.val ∧
    (e none :ℤ)-e.weight jetDerivativeWeight=aQj i.2}
def aFx (i:sP) :Submodule ao M7 :=
  restrictSupport ao (TO i)
instance (i:sP) :Module.Finite ao (aFx i) :=
  restrictSupport_finite ((bFE).subset (fun _ h=>h.1))
def af3 (i:sP) :aFx i →ₗ[ao] Local :=
  (localConstraintAt primaryM 0 0).domRestrict (aFx i)
private def jO (i:sP) :ℕ:=i.1.val - iO i.1.val
private def Ra (i:sP) (e :UT) :Jp :=
  Finsupp.equivFunOnFinite.symm
    ![e (some 0) - jO i,e (some 1),e (some 2),e (some 3)]
private theorem buZ (i:sP) (e :TO i) :
    jO i≤e.val (some 0) := by
  have hd:=e.property.2.2.1
  have hp:=e.property.1.2.2.2.2
  have hgrade :e.val.some.degree=i.1.val := by
    rw [bhx] at hd
    simpa [zFi,zmL] using hd
  simp only [hgrade] at hp
  rw [bhx] at hd
  unfold jO iO
  omega
private theorem cqD (i:sP) (e :TO i) :
    Ra i e∈arP (alp i.1.val i.2) := by
  have hd:=e.property.2.2.1
  have hj:=e.property.1.2.1
  have hc:=e.property.1.2.2.1
  have hx :=e.property.2.1
  have hg:=e.property.2.2.2
  have ha :=buZ i e
  rw [bhx] at hd
  rw [bhy] at hj hg
  change e.val (some 1)+2*e.val (some 2)+3*e.val (some 3)≤1710 at hj
  change e.val none<3000 at hx
  simp [z1K,Fintype.sum_option,topWeight,Pi.single_apply,
    smul_eq_mul] at hc
  change ((Ra i e).weight BU:ℤ)=(alp i.1.val i.2).degree ∧
    -aQj i.2≤((Ra i e).weight Oq:ℤ) ∧
    ((Ra i e).weight Oq:ℤ)≤ min (Wk.j:ℤ) ((primaryM:ℤ) - 1-aQj i.2) ∧
    ((Ra i e) 3:ℤ)≤(Wk.t:ℤ)
  change _=(iO i.1.val :ℤ)∧_
  simp [z1K,zmL,BU,Oq,Ra,
    smul_eq_mul,Nat.mul_comm]
  simp only [jO,iO] at ha ⊢
  omega
private def bpl (i:sP) (e :TO i) :ahV (alp i.1.val i.2) := by
  refine ⟨monomial (Ra i e) 1,?_⟩
  change monomial (Ra i e) 1∈restrictSupport ao (arP (alp i.1.val i.2))
  exact (monomial_mem_restrictSupport ao).mpr (Or.inl (cqD i e))
private def encode (i:sP) :aFx i →ₗ[ao] ahV (alp i.1.val i.2) :=
  (basisRestrictSupport ao (TO i)).constr ao (bpl i)
private theorem b1y (i:sP) (e :TO i) :
    ((encode i (basisRestrictSupport ao (TO i) e)) :MI) =
      monomial (Ra i e) 1 :=
  congrArg Subtype.val
    ((basisRestrictSupport ao (TO i)).constr_basis ao (bpl i) e)
local notation "T" => (MvPolynomial.X (localT 3) :Local)
private theorem cqE (i:sP) (e :UT) :
    bind₁ NH (alM (monomial (Ra i e) 1)) =
    asF^(e (some 0) - jO i) *
      (T*Ce 0)^e (some 1)*(T^2*Ce 1)^e (some 2)*(T^3*Ce 2)^e (some 3) := by
  rw [alM,bind₁_bind₁,blU,Fin.prod_univ_four]
  have h1 :=coL (0:Fin 3)
  have h2 :=coL (1 :Fin 3)
  have h3:=coL (2 :Fin 3)
  change bind₁ NH (La 1)=T^1*Ce 0 at h1
  change bind₁ NH (La 2)=T^2*Ce 1 at h2
  change bind₁ NH (La 3)=T^3*Ce 2 at h3
  simp [dck,h1,h2,h3,Ra]
private theorem gqG (i:sP) (e :TO i) :
    T^(-aQj i.2).toNat*aWg (monomial e.val 1) =
    T^(aQj i.2).toNat*asF^jO i *
      bind₁ NH (alM (monomial (Ra i e) 1)) := by
  have hx :=e.property.2.2.2
  rw [bhy] at hx
  have ht: (-aQj i.2).toNat+e.val none =
      (aQj i.2).toNat+e.val (some 1)+2*e.val (some 2)+3*e.val (some 3) := by omega
  have ha :jO i+(e.val (some 0) - jO i)=e.val (some 0) := by
    have :=buZ i e
    omega
  have hT:T^(-aQj i.2).toNat*T^e.val none =
      T^(aQj i.2).toNat*T^e.val (some 1)*T^(2*e.val (some 2)) *
        T^(3*e.val (some 3)) := by
    simpa only [pow_add] using congrArg (T ^ ·) ht
  have hA:asF^e.val (some 0) =
      asF^jO i*asF^(e.val (some 0) - jO i) := by
    rw [← pow_add,ha]
  rw [eH8,cqE]
  simp only [mul_pow,← pow_mul]
  calc
    _=(T^(-aQj i.2).toNat*T^e.val none) *
        (asF^e.val (some 0)*(Ce 0)^e.val (some 1) *
          (Ce 1)^e.val (some 2)*(Ce 2)^e.val (some 3)) := by ring
    _ = _:= by rw [hT,hA]; ring
private theorem gqF (i:sP) (p:aFx i) :
    T^(-aQj i.2).toNat*aWg (p:M7) =
    T^(aQj i.2).toNat*asF^jO i *
      bind₁ NH (alM ((encode i p:ahV (alp i.1.val i.2)) :MI)) := by
  let l:=(zzN ao (T^(-aQj i.2).toNat)).comp
    (aWg.toLinearMap.comp (aFx i).subtype)
  let r :=(zzN ao (T^(aQj i.2).toNat*asF^jO i)).comp
    ((bind₁ NH).toLinearMap.comp
      (alM.toLinearMap.comp ((ahV (alp i.1.val i.2)).subtype.comp (encode i))))
  have h:l=r := by
    apply (basisRestrictSupport ao (TO i)).ext
    intro e
    change T^(-aQj i.2).toNat *
      aWg (↑(basisRestrictSupport ao (TO i) e) :M7) =
      T^(aQj i.2).toNat*asF^jO i *
        bind₁ NH (alM
          (↑(encode i (basisRestrictSupport ao (TO i) e)) :MI))
    rw [b1y,coe_basisRestrictSupport_apply]
    exact gqG i e
  exact LinearMap.congr_fun h p
private theorem brp (i:sP) :
    z83 ((KP (alp i.1.val i.2)).comp (encode i))≤z83 (af3 i) := by
  intro p hp
  let q:ahV (alp i.1.val i.2) :=encode i p
  let J6:MI:=alM (q:MI)
  let cut:=(alp i.1.val i.2).order.toNat
  have hz :weightedTruncation oH cut J6=0:=LinearMap.mem_ker.mp hp
  have hcontact :=(weightedTruncation_eq_zero_iff _ _ _).mp hz
  have hgrade : (q:MI).IsWeightedHomogeneous BU (iO i.1.val) := by
    intro e he
    have hd:=(q.property (mem_support_iff.mpr he)).1
    change (e.weight BU:ℤ)=(iO i.1.val :ℤ) at hd
    omega
  have hshear :J6.IsWeightedHomogeneous BU (iO i.1.val) :=
    hgrade.bind₁ cpn
  have hscaled:J6∈restrictWeightedOrder aid (cut+iO i.1.val) := by
    intro e he
    have hg:=hshear (mem_support_iff.mp he)
    have hc:=mem_restrictWeightedOrder.mp hcontact e he
    change cut+iO i.1.val≤e.weight aid
    rw [cwS,hg]
    exact Nat.add_le_add_right hc _
  have hprod:=mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder (aQH (aQj i.2).toNat)
      (by simpa using pow_mem_restrictWeightedOrder cva (jO i)))
    (bind₁_mem_restrictWeightedOrder bv2 hscaled)
  have hbound:primaryM+(-aQj i.2).toNat ≤
      (aQj i.2).toNat+jO i+(cut+iO i.1.val) := by
    change primaryM+(-aQj i.2).toNat≤(aQj i.2).toNat+jO i +
      (((primaryM:ℤ)-(i.1.val :ℤ)-aQj i.2).toNat+iO i.1.val)
    have hr :iO i.1.val≤ i.1.val :=min_le_left _ _
    unfold jO
    omega
  have hshift:T^(-aQj i.2).toNat*aWg (p:M7) ∈
      restrictWeightedOrder (localContactWeight 3) (primaryM+(-aQj i.2).toNat) := by
    rw [gqF]
    exact restrictWeightedOrder_anti _ hbound hprod
  apply LinearMap.mem_ker.mpr
  change weightedTruncation (localContactWeight 3) primaryM (aWg (p:M7))=0
  exact (weightedTruncation_eq_zero_iff _ _ _).mpr (caB hshift)
theorem fTc (i:sP) :
    zsE ao (zWl (af3 i)) ≤
      zsE ao (zWl (KP (alp i.1.val i.2))) := by
  let f :=(KP (alp i.1.val i.2)).comp (encode i)
  have hker :=zFM (brp i)
  change zsE ao (z83 f) ≤
    zsE ao (z83 (af3 i)) at hker
  have h₁:=f.finrank_range_add_finrank_ker
  have h₂:=(af3 i).finrank_range_add_finrank_ker
  exact (show zsE ao (zWl (af3 i)) ≤
      zsE ao (zWl f) by omega).trans
    (zFM (LinearMap.range_comp_le_range _ _))
private theorem rank_of_monomials {ι:Type} [Fintype ι]
    (blocks :ι→Submodule ao Local) [∀ i,Module.Finite ao (blocks i)]
    (hcol : ∀ e,FF e → ∀ c,
      localConstraintAt primaryM 0 0 (ztt e c)=0 ∨
        ∃ i,localConstraintAt primaryM 0 0 (ztt e c)∈blocks i) :
    zsE ao (zWl (nodeMap 0 0)) ≤
      ∑ i,zsE ao (blocks i) := by
  classical
  have cover :zWl (nodeMap 0 0)≤Finset.univ.sup blocks := by
    intro R hR
    obtain ⟨Q,hQ⟩:=LinearMap.mem_range.mp hR
    rw [← hQ]
    let l:=localConstraintAt (d:=3) primaryM (0:ao) 0
    change l Q.1∈Finset.univ.sup blocks
    rw [Q.1.as_sum,map_sum]
    refine zo3 _ fun e he => ?_
    rcases hcol e (Q.2 he) (Q.1.coeff e) with h | ⟨i,hi⟩
    · change l (ztt e _)=0 at h
      rw [h]
      exact Submodule.zero_mem _
    · exact (Finset.le_sup (f :=blocks) (Finset.mem_univ i)) hi
  exact (zFM cover).trans (b3b blocks _)
theorem eIb (bound:ℕ→Offset→ℕ)
    (hr : ∀ i:sP,zsE ao
      (zWl (KP (alp i.1.val i.2)))≤bound i.1.val i.2) :
    zsE ao (zWl (nodeMap 0 0)) ≤
      ∑ q∈Finset.range (Wk.b+1),∑ r :Offset,bound q r := by
  let ranges (i:sP) :Submodule ao Local:=zWl (af3 i)
  refine (rank_of_monomials ranges ?_).trans ?_
  · intro e he c
    by_cases hx :e none<primaryM
    · let q:=e.weight jetDegreeWeight
      let j:=e.weight jetDerivativeWeight
      have hq:q≤Wk.b:=he.1
      have hj:j≤Wk.j:=he.2.1
      let i:sP:=(⟨q,by omega⟩,⟨e none+(Wk.j - j),by omega⟩)
      have hi:e∈TO i:= by
        refine ⟨he,hx,rfl,?_⟩
        change (e none :ℤ) - j=((e none+(Wk.j - j) :ℕ) :ℤ)-Wk.j
        omega
      exact Or.inr ⟨i,⟨⟨_,(monomial_mem_restrictSupport ao).mpr (Or.inl hi)⟩,rfl⟩⟩
    · exact Or.inl (b5V e c (Nat.le_of_not_gt hx))
  · calc
      _ ≤ ∑ i:sP,bound i.1.val i.2 :=
        zQk fun i _=>(fTc i).trans (hr i)
      _ = _:= by
        rw [Fintype.sum_prod_type]
        exact Fin.sum_univ_eq_sum_range (fun q => ∑ r :Offset,bound q r) (Wk.b+1)
end
end P6_6_2
end
section
set_option autoImplicit true
namespace P6_6_2
noncomputable section
open aR Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open xE (UT Ky)
open P6 (I K node)
open P6_6 (gZ aWx Wk primaryM Dj aRG)
open private bFD from ProximityPrize.SubmissionLower.I
open private aqS weight_eq_sum eMe from ProximityPrize.SubmissionLower.AR
open MvPolynomial (mem_support_iff)
theorem bLI (Q:W2) :
    aO (shape (Ky Q.1)) Wk∧aRG (Ky Q.1) ∧
      P6_6.tB (Ky Q.1) aWx := by
  classical
  have h (m:Fin 4 →₀ ℕ) (hm:m∈(Ky Q.1).support) :
      m.sum (fun _ a=>a)≤Wk.b ∧
      m.sum (fun i a=>i.val*a)≤Wk.j∧m 3≤Wk.t ∧
      ((Ky Q.1).coeff m).natDegree+m.sum (fun i a=>(gZ - i.val)*a) ≤
        aWx∧m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a)) := by
    let n:=((Ky Q.1).coeff m).natDegree
    have hc:Q.1.coeff (m.optionElim n)≠0:= by
      rw [← MvPolynomial.optionEquivRight_coeff_coeff]
      change ((Ky Q.1).coeff m).coeff n≠0
      rw [Polynomial.coeff_natDegree,Polynomial.leadingCoeff_ne_zero]
      exact mem_support_iff.mp hm
    have supportBound : ∀ e∈Q.1.support,FF e := Q.2
    obtain ⟨hb,hj,ht,hw,hp⟩:=supportBound _ (mem_support_iff.mpr hc)
    have jb:jetDegreeWeight (d:=3)=(fun v=>v.elim 0 (fun _=>1)) := by
      funext v; cases v <;> rfl
    have ji:jetDerivativeWeight (d:=3)=(fun v=>v.elim 0 (fun i=>i.val)) := by
      funext v; cases v <;> rfl
    have jw:differentialWeight (d:=3) gZ =
        (fun v=>v.elim 1 (fun i=>gZ - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v=>v.elim 0 (Pi.single (3:Fin 4) (1 :ℕ)))≤Wk.t at ht
    simp only [Finsupp.weight_optionElim,zero_mul,zero_add,one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _=>1)] at hb
    rw [weight_eq_sum m (fun i=>i.val)] at hj
    rw [weight_eq_sum m (fun i=>gZ - i.val)] at hw
    have hsome : (m.optionElim n).some=m:= by
      ext i
      simp
    rw [hsome,Finsupp.degree_apply] at hp
    simp only [Finsupp.optionElim_apply_some] at hp
    change m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a)) at hp
    exact ⟨by simpa only [one_mul] using hb,hj,ht,hw,hp⟩
  exact ⟨⟨Finset.sup_le fun m hm=>(h m hm).1,Finset.sup_le fun m hm=>(h m hm).2.1,
    MvPolynomial.degreeOf_le_iff.mpr fun m hm=>(h m hm).2.2.1⟩,
    fun m hm=>(h m hm).2.2.2.2,fun m hm=>(h m hm).2.2.2.1⟩
private def plateau (q:ℕ) :ℕ :=
  if q<3307 then 1710 else
  if q<3335 then 1700 else
  if q<3407 then 1650 else
  if q<3470 then 1600 else
  if q<3537 then 1550 else
  if q<3585 then 1500 else
  if q<3630 then 1450 else
  if q<3678 then 1400 else
  if q<3733 then 1350 else
  if q<3781 then 1300 else
  if q<3830 then 1250 else
  if q<3878 then 1200 else
  if q<3927 then 1150 else
  if q<3975 then 1100 else
  if q<4020 then 1050 else
  if q<4025 then 1000 else
  850
private theorem plateau_spec :Antitone plateau ∧ ∀ q,plateau q≤1710 := by
  unfold plateau
  apply aqS 3307 (by decide :1700≤1710)
  apply aqS 3335 (by decide :1650≤1700)
  apply aqS 3407 (by decide :1600≤1650)
  apply aqS 3470 (by decide :1550≤1600)
  apply aqS 3537 (by decide :1500≤1550)
  apply aqS 3585 (by decide :1450≤1500)
  apply aqS 3630 (by decide :1400≤1450)
  apply aqS 3678 (by decide :1350≤1400)
  apply aqS 3733 (by decide :1300≤1350)
  apply aqS 3781 (by decide :1250≤1300)
  apply aqS 3830 (by decide :1200≤1250)
  apply aqS 3878 (by decide :1150≤1200)
  apply aqS 3927 (by decide :1100≤1150)
  apply aqS 3975 (by decide :1050≤1100)
  apply aqS 4020 (by decide :1000≤1050)
  apply aqS 4025 (by decide :850≤1000)
  exact ⟨fun _ _ _=>le_rfl,fun _=>le_rfl⟩
private theorem gradeCap_eq (q:ℕ) :Dj q=min q (plateau q) := by
  by_cases h:q<3307
  · simp only [Dj,plateau,ite_eq_left h]
  · have hle :=(plateau_spec.2 q).trans (show 1710≤q by omega)
    rw [min_eq_right hle]
    simp only [Dj,plateau,ite_eq_right h]
private theorem profile_mono {d q r :ℕ} (hqr :q≤ r) (hd:d≤q)
    (h:d≤Dj r) :d≤Dj q:= by
  rw [gradeCap_eq] at h ⊢
  exact le_min hd ((h.trans (min_le_right _ _)).trans (plateau_spec.1 hqr))
private theorem b1o {u v :UT} (h:v≤u)
    (hu:FF u) :FF v := by
  have hw (w:JetVariable 3→ℕ) :v.weight w≤u.weight w:= by
    rw [z1K,z1K]
    exact zQk fun j _=>Nat.mul_le_mul_right (w j) (h j)
  have hd:v.some.degree≤u.some.degree := by
    rw [zFi,zFi]
    exact zQk fun j _=>h (some j)
  have hv :v (some 1)+v (some 2)+v (some 3)≤v.some.degree := by
    rw [zFi,zmL]
    simp only [Finsupp.some_apply]
    omega
  obtain ⟨hdeg,hi,hf,hwt,hp⟩:=hu
  exact ⟨(hw _).trans hdeg,(hw _).trans hi,(hw _).trans hf,(hw _).trans hwt,
    profile_mono hd hv ((add_le_add (add_le_add (h _) (h _)) (h _)).trans hp)⟩
private theorem gDK (x y :ao) (Q:W2) :
    globalPointTranslation x y Q.1∈W2 := by
  classical
  let f :=globalPointTranslation (d:=3) x y
  change f Q.1∈W2
  rw [Q.1.as_sum,map_sum]
  refine zo3 _ fun u hu => ?_
  change globalPointTranslation x y (ztt u _) ∈
    MvPolynomial.restrictSupport ao {v | FF v}
  apply (MvPolynomial.mem_restrictSupport_iff ao).mpr
  intro v hv
  exact b1o (bFD x y u v _ hv) (Q.property hu)
theorem eE5 (x y :ao) :
    zWl (nodeMap x y)≤zWl (nodeMap 0 0) := by
  rintro _ ⟨Q,rfl⟩
  refine ⟨⟨globalPointTranslation x y Q.1,gDK x y Q⟩,?_⟩
  exact (localConstraintAt_eq_zero_globalPointTranslation (m:=primaryM) x y Q.1).symm
theorem dPo (w:I→K) (Q:W2)
    (hQ:asI w Q=0) :P6_6.Contact w (Ky Q.1) := by
  intro i S hS
  rw [xE.duE]
  have hi:SatisfiesLocalConstraints (d:=3) primaryM (embed (node i)) (embed (w i)) Q.1 :=
    congrFun hQ i
  have hd:=eMe (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd
end
end P6_6_2
end
