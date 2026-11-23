import ProximityPrize.SubmissionLower.ZXxMpWa
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
section
set_option autoImplicit true
namespace qAzl5me
noncomputable section
open Polynomial
open P6_6 (bf)
open P6_6_7
open aR (af ao extend cK)
open dN (bC Ch su arh)
open rW (n8)
open BO (Ue bsq)
def c1 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ A:SurfaceAssignment C R G,∀ dR,
      let p:=chartBody C R cs
      let r :=firstSlot C R cs
      let q:=cutterBody C ell
      let T:=terminalMarks C R G ell cs A
      aid C R G ell A T≤terminalCap dR p r q
def c2 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (A:SurfaceAssignment C R G) γ,γ∈active C R G ell cs A →
      ∀ i a,Selected C cs (A.aI γ) γ i a →
        ContinueAt (chartRow C i a) (A.aI γ) (extend (C.s γ)) →
          CurveWitness C cs (A.aI γ) γ∨SurfaceWitness C R G ell cs (A.aI γ) γ
def c3:Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (A:SurfaceAssignment C R G) (T:Finset P6.K),T⊆active C R G ell cs A →
      (∀ γ∈T,CurveWitness C cs (A.aI γ) γ) →
        aid C R G ell A T≤ curveCap (chartBody C R cs) (firstSlot C R cs) (cutterBody C ell)
def c4 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (A:SurfaceAssignment C R G) (T:Finset P6.K),T⊆active C R G ell cs A →
      (∀ γ∈T,SurfaceWitness C R G ell cs (A.aI γ) γ) →
        aid C R G ell A T≤fresh32 (firstSlot C R cs) (cutterBody C ell)
private theorem selected_exists {C:Context} {cs :ChartCase C.n} {aI:n8}
    {γ:P6.K} (h:RegularInvariant C cs aI γ) : ∃ i a,Selected C cs aI γ i a := by
  obtain ⟨i,hi,hz,hmin,a,ha,hr,hinv⟩:=h
  exact ⟨i,a,hi,hz,hmin,ha,hr,hinv⟩
theorem Selected.unique {C:Context} {cs :ChartCase C.n} {aI:n8}
    {γ δ:P6.K} {i j:Fin C.n} {a b:ℕ}
    (h:Selected C cs aI γ i a) (h' : Selected C cs aI δ j b) :i=j∧a=b:= by
  have hij:=le_antisymm (h.least j h'.index_mem h'.contains) (h'.least i h.index_mem h.contains)
  subst j
  have order {x y :ℕ} (hx :dN.YR (C.f i) aI x)
      (hy :dN.YR (C.f i) aI y) : ¬ x<y := by
    intro hxy
    have hm:=hy.2.1 (x+1) (Nat.succ_le_of_lt hxy)
    rw [Function.iterate_succ_apply'] at hm
    exact hx.2.2 hm
  exact ⟨rfl,le_antisymm (Nat.le_of_not_gt (order h'.canonical h.canonical))
    (Nat.le_of_not_gt (order h.canonical h'.canonical))⟩
private theorem d29 (g:af 4) (U:ao[X]) (hg:cK g U=0)
    (n:ℕ) (hU:U.natDegree<n) :cK (su g n) U=0:= by
  rw [arh _ _ hg,iterate_derivative_eq_zero hU,mul_zero]
private theorem cases_of_selected {C:Context} {cs :ChartCase C.n} {aI:n8}
    {γ:P6.K} {i:Fin C.n} {a :ℕ} (h:Selected C cs aI γ i a)
    (hγ:γ∈C.Δ) (hZ:aI≤Ch (extend (C.s γ))) :
    TerminalAt (chartRow C i a) aI (extend (C.s γ)) ∨
      ContinueAt (chartRow C i a) aI (extend (C.s γ)) := by
  classical
  let g:=chartRow C i a
  let U:=extend (C.s γ)
  have hg:cK g U=0:=Ue.mp (hZ (h.canonical.2.1 a le_rfl))
  have hU:U.natDegree<bf := by
    rw [show U.natDegree=(C.s γ).natDegree from natDegree_map _]
    exact Nat.lt_succ_of_le (C.messages.degree γ hγ)
  by_cases he :bC (memberTest g)∈aI
  · exact Or.inr (Or.inl he)
  have hE :cK (memberTest g) U=0:= by
    unfold memberTest
    exact d29 g U hg bf hU
  obtain ⟨P,hp,hpoint⟩:=bsq hZ hE
  let hm:MemberCurve g aI P:=⟨he,hp⟩
  by_cases hs :hm.simple
  · by_cases hn:bC (ZV g)∈P
    · exact Or.inr (Or.inr ⟨P,hm,hpoint,hs,hn⟩)
    · exact Or.inl ⟨P,hm,hpoint,Or.inr hn⟩
  · exact Or.inl ⟨P,hm,hpoint,Or.inl hs⟩
private theorem active_weight (C:Context) (R G:af 4) (ell:ℕ) (cs :ChartCase C.n)
    (A:SurfaceAssignment C R G) :
    (highInv C R G ell cs A:ℤ) = ∑ γ∈active C R G ell cs A,(genericOrder R (A.aI γ) :ℤ) := by
  classical
  rw [highInv,Nat.cast_sum,active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro γ _
  by_cases ho:0<ord C R γ <;>
    by_cases hh:ell≤genericOrder G (A.aI γ)∧RegularInvariant C cs (A.aI γ) γ <;>
    simp only [ho,hh,surfaceOrder,true_and,false_and,ite_true,ite_false,Nat.cast_zero]
private theorem filter_weight (C:Context) (R G:af 4) (ell:ℕ) (A:SurfaceAssignment C R G)
    (T:Finset P6.K) (p:P6.K→Prop) [DecidablePred p] :
    aid C R G ell A (T.filter p)+aid C R G ell A (T.filter fun γ => ¬ p γ) =
      aid C R G ell A T:= by
  rw [aid,aid,aid,← mul_add,Finset.sum_filter_add_sum_filter_not]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_6_7.c4 := by
  classical
  intro C R G ell cs h A dR
  let T:=active C R G ell cs A
  let terminal (γ:P6.K) :=TerminalMark C cs (A.aI γ) γ
  let curve (γ:P6.K) :=CurveWitness C cs (A.aI γ) γ
  let U:=T.filter fun γ => ¬ terminal γ
  have hU : ∀ γ∈U,curve γ∨SurfaceWitness C R G ell cs (A.aI γ) γ:= by
    intro γ hγ
    obtain ⟨ha,ht⟩:=Finset.mem_filter.mp hγ
    obtain ⟨hmem,ho,_,hreg⟩:=Finset.mem_filter.mp ha
    obtain ⟨i,a,hi⟩:=selected_exists hreg
    rcases cases_of_selected hi hmem (A.valid γ hmem ho).2 with hc | hc
    · exact (ht ⟨i,a,hi,hc⟩).elim
    · exact h2 C R G ell cs h A γ ha i a hi hc
  have ht:=h1 C R G ell cs h A dR
  have hc:=h3 C R G ell cs h A (U.filter curve)
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    (fun γ hγ=>(Finset.mem_filter.mp hγ).2)
  have hs :=h4 C R G ell cs h A (U.filter fun γ => ¬ curve γ)
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    (fun γ hγ=>(hU γ (Finset.mem_filter.mp hγ).1).resolve_left (Finset.mem_filter.mp hγ).2)
  dsimp only at ht ⊢
  rw [active_weight]
  change aid C R G ell A T≤_
  rw [← filter_weight C R G ell A T terminal,← filter_weight C R G ell A U curve]
  calc
    _≤terminalCap dR (chartBody C R cs) (firstSlot C R cs) (cutterBody C ell) +
        (curveCap (chartBody C R cs) (firstSlot C R cs) (cutterBody C ell) +
          fresh32 (firstSlot C R cs) (cutterBody C ell)) :=
      add_le_add ht (add_le_add hc hs)
    _ = _:= by
      dsimp only [terminalCap,curveCap,memberDegree,taylor32]
      ring
end
end qAzl5me
end
section
set_option autoImplicit true
namespace q5l8jMe
noncomputable section
open aR (af)
open dN hiding ZV
open rW (n8)
open aFT
open P6_6 (bf)
open qAzl5me (MemberCurve memberTest ZV)
attribute [local instance] MvPolynomial.algebraMvPolynomial
open private cSI bIU from ProximityPrize.SubmissionLower.V
open private dfw dfn from ProximityPrize.SubmissionLower.V
private theorem cpE (H :af 4) (aI P:n8) [P.IsPrime]
    (hdesc: (aI.comap Ow).map Ow=aI)
    (hone :oA (AX aI H) P ‹P.IsPrime› = 1) :
    ∀ x∈P.comap Ow,∃ t∉P.comap Ow,
      t*x∈aI.comap Ow ⊔ Ideal.span {Q0 H} := by
  let q:=P.comap Ow
  have :q.IsPrime :=Ideal.comap_isPrime _ _
  have :P.LiesOver q:=⟨rfl⟩
  let A:=Localization.AtPrime q
  let B:=Localization.AtPrime P
  let _:Algebra A B:=Localization.AtPrime.algebraOfLiesOver q P
  have :Module.Flat PJ GeoJets :=cSI
  have :IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q P Ow rfl)
    infer_instance
  have :Module.FaithfullyFlat A B:=Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J:Ideal PJ:=aI.comap Ow ⊔ Ideal.span {Q0 H}
  have hJ:J.map (algebraMap PJ GeoJets)=AX aI H := by
    change (aI.comap Ow ⊔ Ideal.span {Q0 H}).map Ow= _
    rw [Ideal.map_sup,hdesc,Ideal.map_span,Set.image_singleton,aQd,AX]
  have hJB: (J.map (algebraMap PJ A)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B:= by
    rw [Ideal.map_map,← IsScalarTower.algebraMap_eq PJ A B,
      IsScalarTower.algebraMap_eq PJ GeoJets B,← Ideal.map_map,hJ]
    exact bIU _ P hone
  intro x hx
  have hxB:algebraMap A B (algebraMap PJ A x)∈IsLocalRing.maximalIdeal B:= by
    rw [← IsScalarTower.algebraMap_apply PJ A B,
      IsScalarTower.algebraMap_apply PJ GeoJets B,← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  rw [← hJB] at hxB
  have hxA:algebraMap PJ A x∈J.map (algebraMap PJ A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B:=B) (J.map (algebraMap PJ A))]
    exact hxB
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A J x).mp hxA
theorem invariant_of_simple {R G g:af 4} {aI P:n8}
    (hz : (kC R G).IsMinimalPrime aI)
    (hlen:oA (kC R G) aI hz.isPrime<(K1.p:ℕ∞))
    (hI:Invariant g aI) (hcut:MemberCurve g aI P) (hone :hcut.simple)
    (hs :bC (separant g)∉P) (hnext:bC (ZV g)∈P) :
    Invariant g P:= by
  let T:=aI.comap Ow
  let q:=P.comap Ow
  let e := Q0 (memberTest g)
  have :P.IsPrime :=hcut.minimal.isPrime
  have :q.IsPrime := ‹P.IsPrime›.comap Ow
  have hle :T≤q:=Ideal.comap_mono (le_sup_left.trans hcut.minimal.le)
  obtain ⟨D,hD,hstable⟩:=cyu.proof g aI hz.isPrime hI
  have transfer (H :af 4) :Q0 H∈q↔bC H∈P:= by
    change Ow (Q0 H)∈P↔_
    rw [aQd]
  have he :e∈q:=(transfer _).mpr
    (hcut.minimal.le (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hN :=(transfer _).mpr hnext
  change Q0 (su g (bf+1))∈q at hN
  rw [dfw g D hD bf] at hN
  have hDe :D e∈q:=(‹q.IsPrime›.mem_or_mem
    ((q.sub_mem_iff_left (q.mul_mem_left _ he)).mp hN)).resolve_left (mt (transfer _).mp hs)
  have hsat :=cpE (memberTest g) aI P
    (bzE.proof R G aI hz hlen) hone
  intro H hH
  apply (transfer _).mp
  rw [← hD]
  exact dfn T q hle D hstable he hDe hsat _ ((transfer _).mpr hH)
end
end q5l8jMe
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q5l8jMe
noncomputable section
open aR dN rW as6 Polynomial
open P6_6 (aWx)
theorem c2l {H :af 4} {B:ℕ} (h:P6_6.tB H B) :
    tB H (2*B) := by
  intro m hm
  have hs :m.sum (fun i a=>(133671 - i.val)*a) ≤
      2*m.sum (fun i a=>(P6_6.gZ - i.val)*a) := by
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Nat.mul_assoc]
    apply Nat.mul_le_mul_right
    have hi:=i.isLt
    change 133671 - i.val≤2*(133425 - i.val)
    omega
  have hnew :=h m hm
  change (H.coeff m).natDegree+m.sum (fun i a=>(133671 - i.val)*a)≤2*B
  omega
private theorem iterate_zero {F:Type} [Field F] [Algebra ao F]
    (D:Derivation ao F F) (y :F) {L n:ℕ}
    (hcut: ((D:F→F)^[L]) y=0) (hn:L≤n) :
    ((D:F→F)^[n]) y=0:= by
  obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm L j,Function.iterate_add_apply,hcut]
  exact Function.iterate_fixed (f :=(D:F→F)) D.map_zero j
private theorem dW0 {F:Type} [Field F] [Algebra ao F]
    (D:Derivation ao F F) (x y :F) {L:ℕ} (hL:0<L) (hbound:L≤bf)
    (hcut: ((D:F→F)^[L]) y=0) : (aHA D x y).natDegree<L:= by
  have htrim:aHA D x y =
      ahG (M:=L) x (fun i=>ZD D y i.val) := by
    let term (i:ℕ) :=C (ZD D y i)*(Polynomial.X - C x)^i
    change (∑ i:Fin bf,term i.val) = ∑ i:Fin L,term i.val
    rw [Fin.sum_univ_eq_sum_range term,Fin.sum_univ_eq_sum_range term]
    symm
    apply Finset.sum_subset (Finset.range_mono hbound)
    intro i _ hi
    have htail:L≤ i:=Nat.le_of_not_lt (fun h=>hi (Finset.mem_range.mpr h))
    simp only [term,ZD,iterate_zero D y hcut htail,zero_div,map_zero,zero_mul]
  rw [htrim]
  exact bG3 _ _ hL
open private c8X cVf cFc from ProximityPrize.SubmissionLower.A0
theorem integrate {R G g:af 4} {P:n8} [P.IsPrime]
    (hR:P6_6.tB R aWx) (hG:P6_6.tB G aWx)
    (hW:tB g (2*aWx)) (hcut:kC R G≤P)
    (hg:bC g∈P) (hsep:bC (separant g)∉P)
    (hmem:bC (qAzl5me.memberTest g)∈P) (hinv :Invariant g P) :
    ∃ U: (tJ P)[X],bjr R G g P U∧U.natDegree<P6_6.bf ∧
      ∀ H :af 4,P6_6.tB H aWx→bC H∈P →
        jW (CX P) H U=0:= by
  let e :=ee P
  let x :=KK e
  let y :=ajH e 0
  let k :=aQP P
  obtain ⟨D,hx,hshift,haction⟩:=cyv.proof g P ‹P.IsPrime› hg hsep hinv
  have hs :e (separant g)≠0:= fun hz=>hsep ((bgQ P _).mp hz)
  have hM: ((D:am4 P→am4 P)^[P6_6.bf]) y=0:= by
    have hz :=(bgQ P (qAzl5me.memberTest g)).mpr hmem
    change e (su g P6_6.bf)=0 at hz
    rw [cVU e g D haction] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hs)
  have hlength:P6_6.bf≤bf := by decide
  have hpos :0<P6_6.bf := by decide
  have hOldM:=iterate_zero D y hM hlength
  have hcanon :ab2 e g=aHA D x y := by
    unfold ab2 aHA
    apply congrArg (ahG (M:=bf) x)
    funext i
    unfold ZD
    rw [cVU e g D haction,mul_div_cancel_left₀ _ (pow_ne_zero _ hs)]
  have hmap : (aHA D x y).map k=ab2 (Zx P) g:= by
    rw [← hcanon]
    exact cFc P g
  have hdegree : (ab2 (Zx P) g).natDegree<P6_6.bf := by
    rw [← hmap]
    exact natDegree_map_le.trans_lt (dW0 D x y hpos hlength hM)
  have hinitial (i:Fin 4) :ZD D y i.val=ajH e i :=
    cVf e D hshift i
  have hconstants :k.comp (algebraMap ao (am4 P))=CX P:= by
    ext a
    exact gBL P a
  have hguard :2*aWx+3<K1.p:= by
    change 0x404fa751<0x7f000001
    decide
  have hcontinue (H :af 4) (hw:tB H (2*aWx)) (hH :bC H∈P) :
      jW (CX P) H (ab2 (Zx P) g)=0:= by
    have hzero :MvPolynomial.eval₂ (Polynomial.aeval x).toRingHom
        (fun i=>ZD D y i.val) H=0:= by
      simp only [hinitial]
      exact (c8X P H).trans ((bgQ P H).mpr hH)
    have hh:=congrArg (fun U: (am4 P)[X]=>U.map k)
      (cyw.proof (am4 P) D x y hx hOldM H _ hw hguard hzero)
    rw [aVM,hconstants,hmap,Polynomial.map_zero] at hh
    exact hh
  have hRP:bC R∈P :=
    hcut (Ideal.subset_span (by simp :bC R∈({bC R,bC G} : Set GeoJets)))
  have hGP:bC G∈P :=
    hcut (Ideal.subset_span (by simp :bC G∈({bC R,bC G} : Set GeoJets)))
  refine ⟨_,⟨hdegree.trans_le hlength,?_,hcontinue R (c2l hR) hRP,
      hcontinue G (c2l hG) hGP,hcontinue g hW hg,?_⟩,hdegree,
      fun H hw=>hcontinue H (c2l hw)⟩
  · intro i
    rw [← hmap]
    change (hasseDeriv i.val ((aHA D x y).map k)).eval
      (K4 P (MvPolynomial.C rI))= _
    rw [Polynomial.hasseDeriv_map,← gBK P]
    change ((hasseDeriv i.val (aHA D x y)).map k).eval (k x)= _
    rw [Polynomial.eval_map_apply]
    have hT:=bG4 x (fun j=>ZD D y j.val)
      (i.castLE (by decide :4≤bf))
    change (hasseDeriv i.val (aHA D x y)).eval x=ZD D y i.val at hT
    rw [hT,hinitial]
    exact gBM P i
  · exact bzF.proof g P ‹P.IsPrime› hg hsep
end
end q5l8jMe
end
