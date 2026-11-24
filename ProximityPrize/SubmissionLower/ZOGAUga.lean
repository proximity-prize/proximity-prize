import ProximityPrize.SubmissionLower.ZXrG2Fd
import ProximityPrize.SubmissionLower.ZskDvCd
set_option Elab.async false
set_option autoImplicit true
namespace P6_6_3
noncomputable section
open Polynomial
open P6 (I K node)
open P6_6
open aR (ao embed af Shape shape aO wU extend cK jet qE)
open aiI (Symbol LY acO)
open anm (akp bxm dgu bhd aXI c2E)
open private b2h crB from ProximityPrize.SubmissionLower.AB
open private aio from ProximityPrize.SubmissionLower.Zb3VwYd
open scoped BigOperators
def c1 :Prop :=
  ∀ (w:I→K) (x :ao),aJ5 w→(∀ i:I,x≠embed (node i)) →
    ∃ r :ℕ→ℕ,x5 ≤ ∑ T∈Finset.range (aWx+1),r T ∧
      ∀ T≤aWx,∃ e :Fin (r T)→af 4,
        (∀ i,Pq w T (e i))∧LinearIndependent ao (fun i=>LY x (e i))
def c2 :Prop :=
  ∀ (F:Symbol),F≠0 → ∀ r (e :Fin r→Symbol),
    LinearIndependent ao e →
    (∀ i,aO (akp (e i)) Wk ∧
      SymbolInProfile (e i)∧F∣e i) →
    r≤Gq (akp F)
def c3:Prop :=
  ∀ (Δ:Finset K) (s :K→K[X]) (P Q:af 4) l,
    Q≠0→aO (shape Q) (firstCaps (shape P) l)→tB Q aWx →
    (∀ γ∈Δ,aR.cK P (extend (s γ))≠0) →
    (∀ γ∈Δ,wU Q (extend (s γ)) l) →
    ∃ (n:ℕ) (R:Fin n→af 4) (e :Fin n→ℕ),
      bjg Δ s P (shape P) l R e ∧
      ∀ i,R i^e i∣Q ∧ ¬ R i^(e i+1)∣Q
def c4 :Prop :=
  ∀ (Δ:Finset K) (s :K→K[X]) (Q R:af 4) (q:Shape) d a,
    JetFactor R→aO q Wk→aO (shape Q) q→tB Q aWx →
    (∀ γ∈Δ,wU Q (extend (s γ)) d)→a<d →
    R^a∣Q→(¬ R^(a+1)∣Q) →
    ProperCutter Δ s R (literalBody q).iU (d-a)
private theorem need_le {m:ℕ} (hm:x5≤ sC*m) :gG≤ m:= by
  by_contra! h
  have hlt:sC*(gG - 1)<x5:= by
    change 0xfa50f30e66e4710<0xfa50f30e66eec9d
    decide
  exact (not_le_of_gt hlt) (hm.trans (Nat.mul_le_mul_left _ (by omega)))
private theorem cKp (T:ℕ) :depth T≤ack :=
  Nat.add_le_add_left (Nat.div_le_div_right (Nat.sub_le _ _)) _
private theorem shape_specialized {x :ao} {Q:af 4}
    (h: (LY x Q).support= Q.support) :akp (LY x Q)=shape Q:= by
  simp only [akp,shape,acO,qE,MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_eq_sup,h]
private theorem bst (hr :c1) (hs :c2) {w} (hbank :aJ5 w)
    {F:ℕ→af 4} (hnz : ∀ d,F d≠0) {m:ℕ} (hm:m≤ack)
    (hrows : ∀ T≤aWx,∀ Q,Q≠0→Pq w T Q→depth T≤ m∧F (depth T)∣Q) :
    gG ≤ ∑ k∈Finset.range m,Gq (shape (F (k+1))) := by
  classical
  obtain ⟨x,hx,hsup⟩:=b2h (fun i:Fin ack=>F (i.val+1))
  obtain ⟨r,hsum,hfamily⟩:=hr w x hbank hx
  let cost (k :ℕ) :=if k< m then Gq (shape (F (k+1))) else 0
  have hbound (T:ℕ) (hT:T≤aWx) :r T≤ cost ((aWx - T)/sC) := by
    by_cases hz :r T=0
    · rw [hz]
      exact Nat.zero_le _
    obtain ⟨e,he,hli⟩:=hfamily T hT
    have hne (i:Fin (r T)) :e i≠0:= fun h=>hli.ne_zero i (by rw [h,map_zero])
    let k :=(aWx - T)/sC
    have hk :k+1=depth T:=Nat.add_comm _ _
    have hkL:k<ack := by have :=cKp T; omega
    have hkm:k< m:= by
      have h:=(hrows T hT _ (hne ⟨0,Nat.pos_of_ne_zero hz⟩) (he _)).1
      omega
    have hsup' : (LY x (F (k+1))).support=(F (k+1)).support :=hsup ⟨k,hkL⟩
    have hb:=hs (LY x (F (k+1))) (bxm (hnz _) hsup') (r T) _ hli (by
      intro i
      obtain ⟨hb,hj,ht⟩:=dgu x (e i)
      exact ⟨⟨hb.trans (he i).1.1,hj.trans (he i).1.2.1,ht.trans (he i).1.2.2⟩,
        fun u hu=>(he i).2.1 _ (MvPolynomial.support_map_subset _ _ hu),
        map_dvd (LY x) (hk.symm ▸ (hrows T hT _ (hne i) (he i)).2)⟩)
    rw [shape_specialized hsup'] at hb
    change r T≤ cost k
    simpa only [cost,ite_eq_left hkm] using hb
  have hvol:=(hsum.trans (Finset.sum_le_sum fun T hT =>
    hbound T (Nat.le_of_lt_succ (Finset.mem_range.mp hT)))).trans
    (crB aWx sC (by decide) cost)
  have htrunc : ∑ k∈Finset.range m,Gq (shape (F (k+1))) =
      ∑ k∈Finset.range ack,cost k := by
    calc
      _ = ∑ k∈Finset.range m,cost k :=
        Finset.sum_congr rfl fun k hk=>(ite_eq_left (Finset.mem_range.mp hk)).symm
      _ = _:=Finset.sum_subset (Finset.range_mono hm) fun k _ hk =>
        ite_eq_right (fun h=>hk (Finset.mem_range.mpr h))
  rw [htrunc]
  exact need_le hvol
private theorem prod_shape {n:ℕ} (f :Fin n→af 4) (S:Finset (Fin n))
    (hn : ∀ i,f i≠0) :shape (factorProd f S)=wD (shape ∘ f) S:= by
  classical
  induction S using Finset.induction_on with
  | empty=>simp [factorProd,wD,shape,qE]
  | insert i S hi ih =>
    unfold factorProd at ih ⊢
    rw [Finset.prod_insert hi,bhd (hn i) (Finset.prod_ne_zero_iff.mpr (fun j _=>hn j)),ih]
    simp [wD,Shape.plus,Finset.sum_insert hi]
private theorem forced_product {w n} {f :Fin n→af 4}
    (hf : ∀ i,wm (f i)) (hd : ∀ i j,i≠j → ¬ Associated (f i) (f j))
    {T Q} (hT:T≤aWx) (hQ:Pq w T Q) :
    factorProd f (EarlyIndices w f)^depth T∣Q:= by
  classical
  rw [factorProd,← Finset.prod_pow]
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _ j _ hij
    exact ((hf i).1.isRelPrime_iff_not_dvd.mpr
      (fun h=>hd i j hij ((hf i).1.associated_of_dvd (hf j).1 h))).pow
  · intro i hi
    change i∈Finset.univ.filter (fun j=>ForcesZero w (f j)) at hi
    exact (Finset.mem_filter.mp hi).2 T hT Q hQ
private theorem cwR {Q H :af 4} (hn:Q≠0) (hd:H∣Q)
    (hw:tB Q aWx) :tB H aWx := by
  let e :=MvPolynomial.optionEquivRight ao (Fin 4)
  have hn' : e.symm Q≠0:= fun h=>hn (e.symm.injective (h.trans (map_zero _).symm))
  exact (aio H).mpr
    ((MvPolynomial.weightedTotalDegree_le_of_dvd _ (map_dvd e.symm hd) hn').trans
      ((aio Q).mp hw))
private theorem strip {Δ:Finset K} {s :K→K[X]} {P Q:af 4} {l d:ℕ}
    (hn:Q≠0) (hd:P^l∣Q) (hb:aO (shape Q) Wk)
    (hw:tB Q aWx)
    (hP : ∀ γ∈Δ,cK P (extend (s γ))≠0)
    (ho : ∀ γ∈Δ,wU Q (extend (s γ)) d) :
    ∃ H :af 4,Q=P^l*H∧H≠0∧aO (shape H) (firstCaps (shape P) l) ∧
      tB H aWx ∧ ∀ γ∈Δ,wU H (extend (s γ)) d:= by
  obtain ⟨H,hH⟩:=hd
  have hprod:P^l*H≠0:=hH ▸ hn
  have hnH :=right_ne_zero_of_mul hprod
  have hPd:shape (P^l)=(shape P).scale l:= by
    cases l with
    | zero=>simp [Shape.scale,shape,qE]
    | succ l =>
      apply aXI
      intro hz
      apply left_ne_zero_of_mul hprod
      simp [hz]
  rw [hH,bhd (left_ne_zero_of_mul hprod) hnH,hPd] at hb
  have hbox :aO (shape H) (firstCaps (shape P) l) := by
    obtain ⟨hB,hJ,hT⟩:=hb
    simp only [aO,Shape.plus,firstCaps,rawResidual] at hB hJ hT ⊢
    exact ⟨by omega,by omega,by omega⟩
  refine ⟨H,hH,hnH,hbox,cwR hn ⟨P^l,hH.trans (mul_comm _ _)⟩ hw,?_⟩
  intro γ hγ
  apply c2E (F:=P^l) _ (hH ▸ ho γ hγ)
  change MvPolynomial.eval (jet (extend (s γ))) (P^l)≠0
  rw [map_pow]
  exact pow_ne_zero _ (hP γ hγ)
private theorem exponent_below {Q R:af 4} {d ell:ℕ}
    (hell:0<ell) (hn : ¬ R^(d+1-ell)∣Q) :
    ∃ a,a<d∧ell≤d-a∧R^a∣Q ∧ ¬ R^(a+1)∣Q:= by
  classical
  have hex : ∃ b,¬ R^b∣Q:=⟨_,hn⟩
  let b:=Nat.find hex
  have hb : ¬ R^b∣Q:=Nat.find_spec hex
  have hbpos :0<b:=Nat.pos_of_ne_zero fun hz=>hb (by rw [hz,pow_zero]; exact one_dvd _)
  have hle :b≤d+1-ell:=Nat.find_min' hex hn
  refine ⟨b - 1,by omega,by omega,?_,?_⟩
  · by_contra h
    exact Nat.find_min hex (by omega :b - 1<b) h
  · rwa [show b - 1+1=b by omega]
private theorem fE {Q:af 4} {S:ao[X]} {u d:ℕ}
    (h:u≤d) (ha :wU Q S d) :wU Q S u :=
  fun a ha' => h.trans (ha a ha')
theorem of_children (hr :c1) (hs :c2) (hfactors :c3) (hcut:c4) :P6_6.c3:= by
  classical
  intro w Δ s hm hbank n f hf hdiff
  dsimp only
  intro hmarks
  let zo:=EarlyIndices w f
  let P:=factorProd f zo
  let v :=wD (shape ∘ f) zo
  have hP:P≠0:=Finset.prod_ne_zero_iff.mpr fun i _=>(hf i).1.ne_zero
  have hshape :shape P=v :=prod_shape f zo fun i=>(hf i).1.ne_zero
  have hunit (γ) (hγ:γ∈Δ) :cK P (extend (s γ))≠0:= by
    change MvPolynomial.eval (jet (extend (s γ))) (∏ i∈zo,f i)≠0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i hi=>hmarks γ hγ i hi
  have hforce {T Q} (hT:T≤aWx) (hQ:Pq w T Q) :P^depth T∣Q :=
    forced_product hf hdiff hT hQ
  have hweight {T Q} (hT:T≤aWx) (hQ:Pq w T Q) :
      tB Q aWx := fun a ha=>(hQ.2.2.1 a ha).trans hT
  change RetainedSource Δ s f zo
  refine ⟨?_,?_,?_⟩
  · have h:=bst hr hs hbank (F:= fun d=>P^d) (fun _=>pow_ne_zero _ hP)
        (m:=ack) le_rfl (fun T hT Q _ hQ=>⟨cKp T,hforce hT hQ⟩)
    simpa only [AdmissibleEarly,aXI P hP,hshape] using h
  · intro l test
    have hw : ∃ T,T≤aWx ∧ ∃ Q,Q≠0∧Pq w T Q∧l≤depth T:= by
      by_contra! hn
      have h:=bst hr hs hbank (F:= fun d=>P^d) (fun _=>pow_ne_zero _ hP)
        (m:=l - 1) ((Nat.sub_le _ _).trans test.2.1) (fun T hT Q hQ hb =>
          ⟨by have :=hn T hT Q hQ hb; omega,hforce hT hb⟩)
      apply (not_le_of_gt test.2.2.2)
      simpa only [aXI P hP,hshape] using h
    obtain ⟨T,hT,Q,hQ,hb,hl⟩:=hw
    obtain ⟨H,_,hH,hc,hw,ho⟩:=strip hQ ((pow_dvd_pow P hl).trans (hforce hT hb))
      hb.1 (hweight hT hb) hunit (cax hm hT hb)
    obtain ⟨m,R,e,hfac,_⟩:=hfactors Δ s P H l hH hc hw hunit
      (fun γ hγ=>fE hl (ho γ hγ))
    exact ⟨m,R,e,by simpa only [hshape] using hfac⟩
  · intro R hR hdiffR ell hell _ test
    have hw : ∃ T,T≤aWx ∧ ∃ Q,Pq w T Q ∧ ¬ R^(depth T+1-ell)∣Q:= by
      rcases test with hmass | ⟨he,i,hi,hassoc⟩
      · by_contra! hn
        have hrel :=hR.1.isRelPrime_iff_not_dvd.mpr hdiffR
        have h:=bst hr hs hbank
          (F:= fun d=>P^d*R^(d+1-ell))
          (fun _=>mul_ne_zero (pow_ne_zero _ hP) (pow_ne_zero _ hR.1.ne_zero))
          (m:=ack) le_rfl (fun T hT Q _ hQ =>
            ⟨cKp T,hrel.symm.pow.mul_dvd (hforce hT hQ) (hn T hT Q hQ)⟩)
        apply (not_le_of_gt hmass)
        simpa only [bhd (pow_ne_zero _ hP) (pow_ne_zero _ hR.1.ne_zero),
          aXI P hP,aXI R hR.1.ne_zero,hshape,← Nat.add_assoc] using h
      · subst ell
        have hbad : ¬ ForcesZero w (f i) := by
          intro h
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
        unfold ForcesZero at hbad
        push Not at hbad
        obtain ⟨T,hT,Q,hQ,hnd⟩:=hbad
        refine ⟨T,hT,Q,hQ,fun hd=>hnd ?_⟩
        exact (pow_dvd_pow_of_dvd hassoc.dvd' _).trans (by simpa only [Nat.add_sub_cancel] using hd)
    obtain ⟨T,hT,Q,hQ,hn⟩:=hw
    obtain ⟨a,had,ha,hdiv,hnext⟩:=exponent_below hell hn
    have hQne :Q≠0:= fun h=>hn (h ▸ dvd_zero _)
    have helld:ell≤depth T:=ha.trans (Nat.sub_le _ _)
    obtain ⟨H,heq,_,hb,hw,ho⟩:=strip hQne ((pow_dvd_pow P helld).trans (hforce hT hQ))
      hQ.1 (hweight hT hQ) hunit (cax hm hT hQ)
    have hp:Prime R:=hR.1.prime
    have hdivH :R^a∣H :=
      hp.pow_dvd_of_dvd_mul_left _ (fun h=>hdiffR (hp.dvd_of_dvd_pow h)) (heq ▸ hdiv)
    have hnextH : ¬ R^(a+1)∣H := fun h=>hnext (h.trans ⟨P^ell,heq.trans (mul_comm _ _)⟩)
    have hcap:aO (firstCaps (shape P) ell) Wk :=
      ⟨Nat.sub_le _ _,Nat.sub_le _ _,Nat.sub_le _ _⟩
    obtain ⟨G,hG,hc,hwG,hoG⟩:=hcut Δ s H R _ _ a hR hcap hb hw ho had hdivH hnextH
    refine ⟨G,hG,?_,hwG,fun γ hγ=>fE ha (hoG γ hγ)⟩
    simpa only [residualBody,hshape] using hc
end
end P6_6_3
