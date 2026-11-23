import ProximityPrize.SubmissionLower.ZJlWI6a
set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 1200000
namespace qgLc7la
noncomputable section
open aR (af ao extend shape)
open Ex (X7 bUq)
open oR (qg separant)
open we (eT cH fW qY Yk
  a3H zq cVV D7)
open P6_6 (Messages gZ mV)
open q6t08kb (roots regular lowerBody lowerMixed freshBudget d1C ee8)
open qSCPCwb (Vk BW Lx aGt acU Bk Uj avD c1x dRT)
open qeu0RUc (yD avw cHt dOv)
open MvPolynomial Finset
open scoped BigOperators Polynomial
open private coefficient_family from ProximityPrize.SubmissionLower.ZkT0QFc
open private orderAt_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
def c1 :Prop :=
  ∀ a (f :af 3),FactorBox a f→Gf a f →
    (∑ P∈yD f,((Lx f P).toNat :ℚ)*pN a f P) ≤
      (lowerMixed a :ℚ)
def c2 :Prop :=
  ∀ a (f :af 3),FactorBox a f → ∀ T:Gf a f,∀ P∈yD f,
    (fW (Vk f)∉P →
      (avD f P).Finite∧((avD f P).ncard:ℚ)≤pN a f P) ∧
    (2≤(Lx f P).toNat →
      ∃ Q:Bk,Q.IsPrime∧(affineHilbertPolynomial Q).natDegree≤1 ∧
        affineDegree Q≤pN a f P ∧
        ∀ y∈D7 f P,Uj f T.numerator y∈zeroLocus cH Q)
private theorem degree_of_label {w Γ s} (hm:Messages w Γ s) {γ:P6.K} (hγ:γ∈Γ) :
    (extend (s γ)).natDegree≤gZ:= by
  simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
private theorem component_exists {a f} (hf :FactorBox a f) (T:Gf a f)
    {S:ao[X]} (hd:S.natDegree≤gZ) (hr :qg 2 f S) :
    ∃ P∈yD f,zq S∈D7 f P:= by
  have hz :zq S∈zeroLocus cH (BW f) := by
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    apply Ideal.span_le.mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    change g∈RingHom.ker (aeval (zq S))
    rw [RingHom.mem_ker,aeval_eq_eval]
    rcases hg with rfl | rfl
    · rw [a3H,hr.1,map_zero]
    · rw [a3H,(T.actual S hd hr).1,map_zero]
  have hsep:eval (zq S) (fW (separant f))≠0:= by
    rw [a3H]
    exact fun h=>hr.2 ((map_eq_zero_iff qY Yk).mp h)
  obtain ⟨P,hP,hy⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus
    (BW f) (fW (separant f)) (zq S) hz hsep
  exact ⟨P,avw.mpr ⟨hf.proper,hP⟩,hy,hsep⟩
private def marks (f :af 3) (Γ:Finset P6.K) (s :P6.K→P6.K[X])
    (P:Ideal (eT 3)) :Finset P6.K:= by
  classical
  exact Γ.filter fun γ=>zq (extend (s γ))∈D7 f P
private theorem mixed_count {w Γ s a f P} (hm:Messages w Γ s)
    (hr : ∀ γ∈Γ,qg 2 f (extend (s γ)))
    {T:Gf a f} (h2 :c2) (hf :FactorBox a f)
    (hP:P∈yD f) (hn : ¬ aGt f P) {d:ℕ}
    (hd:0<d) (he :pN a f P=(d:ℚ)) :
    (marks f Γ s P).card≤(Lx f P).toNat*d:= by
  classical
  let e :=(Lx f P).toNat
  have hL:=h2 a f hf T P hP
  by_cases hs :e=1
  · have hs' : Lx f P=1 := by
      rw [← cHt hP,show (Lx f P).toNat=1 from hs,Nat.cast_one]
    obtain ⟨hfin,hdeg⟩:=hL.1 (fun h=>hn ⟨hs',h⟩)
    let pt:= fun γ=>zq (n:=3) (extend (s γ))
    have hsub: (↑((marks f Γ s P).image pt) :Set _)⊆avD f P:= by
      intro y hy
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hy
      obtain ⟨hg,hmem⟩:=mem_filter.mp hγ
      exact ⟨hmem,by rw [a3H,(T.actual _ (degree_of_label hm hg)
        (hr γ hg)).2.1,map_zero]⟩
    have hcard:=Set.ncard_le_ncard hsub hfin
    have hinj:Set.InjOn pt (marks f Γ s P:Set P6.K) :=
      (cVV s Γ hm.distinct).mono (fun _ h=>(mem_filter.mp h).1)
    rw [Set.ncard_coe_finset,card_image_of_injOn hinj] at hcard
    change _≤e*d
    rw [hs,one_mul]
    exact hcard.trans (Nat.cast_le.mp (hdeg.trans_eq he))
  · have htwo:2≤e := by have :=dOv hP; omega
    obtain ⟨Q,hp,hdim,hdegree,hrec⟩:=hL.2 htwo
    have hm' := hm.mono (Δ:=marks f Γ s P) (filter_subset _ _)
    have hcap:=c1x hm' Q hp hdim (hdegree.trans_eq he) (by
      intro γ hγ
      obtain ⟨hg,hy⟩:=mem_filter.mp hγ
      rw [← (T.actual _ (degree_of_label hm hg) (hr γ hg)).2.2]
      exact hrec _ hy)
    exact (dRT hm' hd hcap).trans (Nat.mul_le_mul_right _ htwo)
private theorem aM6 {k σ:Type*} [Field k] [Finite σ]
    (Q:Ideal (MvPolynomial σ k)) (hQ:Q.IsPrime)
    (hdim: (affineHilbertPolynomial Q).natDegree=1) :
    ∃ d:ℕ,0<d∧affineDegree Q=(d:ℚ) := by
  let H :=affineHilbertPolynomial Q
  have hlin:H=Polynomial.C (H.coeff 0)+Polynomial.C (H.coeff 1)*Polynomial.X:= by
    have hH :H.natDegree<2 := by change (affineHilbertPolynomial Q).natDegree<2; omega
    simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
  have evalH (u:ℚ) :H.eval u=H.coeff 0+H.coeff 1*u:= by
    conv_lhs=>rw [hlin]
    simp
  obtain ⟨N,hN⟩:=exists_eval_affineHilbertPolynomial Q
  let m:=affineHilbertFunction Q (N+1)
  let n:=affineHilbertFunction Q N
  have hdiff :affineDegree Q=(m:ℚ)-(n:ℚ) := by
    rw [affineDegree,hdim,Nat.factorial_one,Nat.cast_one,one_mul,Polynomial.leadingCoeff,hdim]
    dsimp only [m,n]
    rw [← hN (N+1) (Nat.le_succ _),← hN N le_rfl]
    change H.coeff 1=H.eval ((N+1 :ℕ) :ℚ) - H.eval (N :ℚ)
    rw [evalH,evalH,Nat.cast_add,Nat.cast_one]
    ring
  have hmn:n< m:= by
    have hpos :=affineDegree_pos hQ.ne_top
    rw [hdiff] at hpos
    exact_mod_cast sub_pos.mp hpos
  exact ⟨m - n,Nat.sub_pos_of_lt hmn,hdiff.trans (Nat.cast_sub hmn.le).symm⟩
private def directComponents (f :af 3) :Finset (Ideal (eT 3)) := by
  classical
  exact (yD f).filter fun P => ¬ aGt f P
private theorem mixed_cover {w Γ s a f} (hm:Messages w Γ s)
    (hr : ∀ γ∈Γ,qg 2 f (extend (s γ))) (h1 :c1) (h2 :c2)
    (hf :FactorBox a f) (T:Gf a f) :
    ((directComponents f).biUnion (marks f Γ s)).card≤lowerMixed a := by
  classical
  let D:=(yD f).filter fun P => ¬ aGt f P
  have hex (P:Ideal (eT 3)) : ∃ d:ℕ,P∈yD f →
      0<d∧pN a f P=(d:ℚ) := by
    by_cases hp:P∈yD f
    · obtain ⟨hprime,hdim⟩:=gnI (a :=a) hf.irreducible hp
      obtain ⟨d,hpos,he⟩:=aM6 (i9 a f P) hprime hdim
      exact ⟨d,fun _=>⟨hpos,he⟩⟩
    · exact ⟨0,fun h=>False.elim (hp h)⟩
  let d (P:Ideal (eT 3)) :=(hex P).choose
  have hd (P) (hP:P∈yD f) :=(hex P).choose_spec hP
  have hsum: (∑ P∈yD f,(Lx f P).toNat*d P)≤lowerMixed a := by
    apply (Nat.cast_le (α:=ℚ)).mp
    rw [Nat.cast_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun P hP => ?_)) (h1 a f hf T)
    rw [Nat.cast_mul,(hd P hP).2]
  calc
    (D.biUnion (marks f Γ s)).card ≤ ∑ P∈D,(marks f Γ s P).card:=card_biUnion_le
    _ ≤ ∑ P∈D,(Lx f P).toNat*d P:=sum_le_sum fun P hP =>
      mixed_count hm hr (T:=T) h2 hf (mem_filter.mp hP).1 (mem_filter.mp hP).2
        (hd P (mem_filter.mp hP).1).1 (hd P (mem_filter.mp hP).1).2
    _ ≤ ∑ P∈yD f,(Lx f P).toNat*d P :=
      sum_le_sum_of_subset (filter_subset _ _)
    _≤lowerMixed a :=hsum
theorem of_children (h1 :c1) (h2 :c2) :q6t08kb.c2 := by
  classical
  intro C R l ell h hw
  let a :=lowerBody (shape R)
  let f :=X7 R
  let Γ:=regular C R
  have hf :FactorBox a f :=factorBox h hw
  have hm:Messages C.w Γ C.s :=C.messages.mono
    ((filter_subset _ (roots C R)).trans (filter_subset _ C.Δ))
  have hr (γ) (hγ:γ∈Γ) :qg 2 f (extend (C.s γ)) := by
    obtain ⟨hroot,hsep⟩:=mem_filter.mp hγ
    refine ⟨?_,hsep⟩
    rw [← bUq R _ h.2.2.1]
    exact BO.bfW (mem_filter.mp hroot).2 (orderAt_ord C R γ)
  let T:=(qP hf).some
  let isolated:=(directComponents f).biUnion (marks f Γ C.s)
  have hmix :isolated.card≤lowerMixed a :=mixed_cover hm hr h1 h2 hf T
  let stable :=(yD f).filter fun P=>aGt f P
  have hex (P:stable) :=guz hf (anchor_weight h.1.2.2)
    (mem_filter.mp P.property).1 (mem_filter.mp P.property).2
  choose Q hQ hrec using hex
  let qv :=stable.attach.image Q
  have hsource (P) (hP:P∈qv) :acU f P:= by
    obtain ⟨P',_,rfl⟩:=mem_image.mp hP
    exact hQ P'
  obtain ⟨d,hd,hsum⟩:=ed8 hf qv hsource
  obtain ⟨F,hn,hcap,hmem⟩:=coefficient_family hm qv d (fun P hP =>
    ⟨(hsource P hP).solution.prime,(hsource P hP).solution.dimension.le,(hd P hP).2.le⟩)
  have hbudget:F.BJ≤freshBudget a :=hcap.trans_le hsum
  have hnum :F.n≤freshBudget a := calc
    F.n = ∑ P∈qv,1 :=hn.trans (card_eq_sum_ones qv)
    _ ≤ ∑ P∈qv,d P:=sum_le_sum fun P hP=>(hd P hP).1
    _≤freshBudget a :=hsum
  have hfresh:mV*F.CF.card≤(P6.t+2*mV)*freshBudget a := by
    rw [ee8,d1C]
    calc
      _≤82317*F.BJ+46402*F.n:=P6_6_5.bJG F hm
      _≤82317*freshBudget a+46402*freshBudget a :=
        add_le_add (Nat.mul_le_mul_left _ hbudget) (Nat.mul_le_mul_left _ hnum)
      _≤_:= by rw [Nat.add_mul]; omega
  have hcover :Γ⊆isolated∪F.CF:= by
    intro γ hγ
    have hdeg:=degree_of_label hm hγ
    obtain ⟨P,hP,hy⟩:=component_exists hf T hdeg (hr γ hγ)
    by_cases hs :aGt f P
    · let p:stable :=⟨P,mem_filter.mpr ⟨hP,hs⟩⟩
      exact mem_union_right _ (hmem γ hγ (Q p) (mem_image.mpr ⟨p,mem_attach _ _,rfl⟩)
        (hrec p _ hdeg (hr γ hγ) hy))
    · exact mem_union_left _ (mem_biUnion.mpr
        ⟨P,mem_filter.mpr ⟨hP,hs⟩,mem_filter.mpr ⟨hγ,hy⟩⟩)
  calc
    mV*Γ.card≤ mV*(isolated.card+F.CF.card) :=
      Nat.mul_le_mul_left _ ((card_le_card hcover).trans (card_union_le _ _))
    _=mV*isolated.card+mV*F.CF.card:=Nat.mul_add _ _ _
    _≤_:=add_le_add (Nat.mul_le_mul_left _ hmix) hfresh
end
end qgLc7la
