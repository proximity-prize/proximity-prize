import ProximityPrize.SubmissionLower.Z877yta
set_option Elab.async false
open _root_ renaming CommRing → za6, DFunLike.congr_fun → zmU, Finset.mul_sum → zxw, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Fintype.card → zhP, Function.Injective → zq4, IsFractionRing.injective → zxb, IsFractionRing.lift → zIj, Matrix.of → zd7, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.homogeneousComponent_isHomogeneous → z8k, MvPolynomial.sum_homogeneousComponent → zjO, Polynomial.coeff_X_pow_mul' → zT3, Polynomial.coeff_zero_eq_eval_zero → zTt, Polynomial.evalRingHom → zhy, Polynomial.finsetSum_coeff → zaW, Polynomial.mul_coeff_zero → zwh, RingHom.comp_apply → zQb, RingHom.id → zz4
section
namespace qOuTtVa
noncomputable section
open scoped Classical Polynomial
open cu (L)
open qfbIfsd (Slot Vars)
open qBl3Pad (jo Chart zeroSlot rest bcm incidenceArg incidence map_rest)
open MvPolynomial (eval₂Hom homogeneousComponent rename ringHom_ext)
local notation "T" => Polynomial.X
local notation "Cₚ" => Polynomial.C
local notation "Cₘ" => MvPolynomial.C
local notation "C₂" => Polynomial.C.comp MvPolynomial.C
private theorem principal {A B:Type*} [za6 A] [IsDomain A]
    [UniqueFactorizationMonoid A] [za6 B] [IsDomain B]
    (f :A[X] →+* B) (hf :zq4 (f.comp Cₚ))
    (hne : ∃ q,q≠0∧f q=0) :
    ∃ p,p≠0∧f p=0 ∧ ∀ q,f q=0→p∣q:= by
  let I:=RingHom.ker f
  have hI:I ≠ ⊥ := by
    obtain ⟨q,hq,hq0⟩:=hne
    exact fun h=>hq (Ideal.mem_bot.mp (h ▸ (show q∈I from hq0)))
  obtain ⟨p,hp0,hp⟩:=(RingHom.ker_isPrime f).exists_mem_prime_of_ne_bot hI
  refine ⟨p,hp.ne_zero,hp0,fun q hq => ?_⟩
  have hdeg:p.natDegree≠0:= by
    intro h
    have hC:=Polynomial.eq_C_of_natDegree_eq_zero h
    have hz : (f.comp Cₚ) (p.coeff 0)=0:=(congrArg f hC).symm.trans hp0
    exact hp.ne_zero (hC.trans (by rw [(injective_iff_map_eq_zero _).mp hf _ hz,map_zero]))
  have hprim:=hp.irreducible.isPrimitive hdeg
  let K:=FractionRing A
  let E :=FractionRing B
  let ι:B →+* E :=algebraMap B E
  let i:A →+* E :=ι.comp (f.comp Cₚ)
  have hi:zq4 i:=(zxb B E).comp hf
  let j:K →+* E :=zIj hi
  let ev :=Polynomial.eval₂RingHom j (ι (f T))
  have hev (r :A[X]) :ev (r.map (algebraMap A K))=ι (f r) := by
    have h:ev.comp (Polynomial.mapRingHom (algebraMap A K))=ι.comp f := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [zQb,Polynomial.coe_mapRingHom,Polynomial.map_C,
          ev,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,j,IsFractionRing.lift_algebraMap,i]
      · simp [ev]
    exact zmU h r
  have hpi:Irreducible (p.map (algebraMap A K)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hp.irreducible
  apply hprim.dvd_of_fraction_map_dvd_fraction_map (K:=K)
  by_contra hn
  obtain ⟨u,v,huv⟩:=(hpi.coprime_iff_not_dvd.mpr hn :
    IsCoprime (p.map (algebraMap A K)) (q.map (algebraMap A K)))
  have h:=congrArg ev huv
  simp only [map_add,map_mul,map_one,hev,show f p=0 from hp0,hq,map_zero,
    mul_zero,add_zero] at h
  exact zero_ne_one h
private def BZ {k α B:Type*} [za6 k] [za6 B] (c:k →+* B)
  (g:α→B[X]) :z3y α k →+* B[X] :=
 eval₂Hom (Polynomial.C.comp c) (fun i=>T*g i)
private theorem ray_homogeneous {k α B:Type*} [za6 k] [za6 B] (c:k →+* B)
  (g:α→B[X]) {p:z3y α k} {n:ℕ} (hp:p.IsHomogeneous n) :
  BZ c g p=T^n*p.eval₂ (Polynomial.C.comp c) g:= by
 simp only [BZ,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq,zxw]
 apply zUo rfl
 intro m hm
 have hm' : m.support.sum m=n:= by
  rw [← Finsupp.degree_apply,Finsupp.degree_eq_weight_one]
  exact hp (MvPolynomial.mem_support_iff.mp hm)
 simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hm']
 ac_rfl
private theorem ray_injective {k α β:Type*} [za6 k] {j:α→β}
    (hj:zq4 j) (g:α→(z3y β k)[X])
    (hg : ∀ i,(g i).coeff 0=z9v (j i)) :
    zq4 (BZ Cₘ g) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  by_contra hn
  have hex : ∃ n,homogeneousComponent n p≠0:= by
    by_contra! h
    apply hn
    rw [← zjO p]
    simp [h]
  let n:=Nat.find hex
  have hne :homogeneousComponent n p≠0:=Nat.find_spec hex
  have hnle :n≤p.totalDegree := by
    by_contra! h
    exact hne (MvPolynomial.homogeneousComponent_eq_zero _ _ h)
  have heval (r :z3y α k) :
      (r.eval₂ C₂ g).coeff 0=rename j r := by
    rw [zTt]
    change (zhy 0) (r.eval₂ C₂ g)= _
    rw [MvPolynomial.hom_eval₂]
    have hc: (zhy 0).comp C₂ =
        (Cₘ:k →+* z3y β k) := by
      ext a
      simp
    rw [hc,MvPolynomial.rename_eq_aeval,MvPolynomial.aeval_def]
    congr 1
    funext i
    simpa [← zTt] using hg i
  have hcoeff : (BZ Cₘ g p).coeff n =
      rename j (homogeneousComponent n p) := by
    conv_lhs=>rw [← zjO p]
    rw [map_sum,zaW,zi6 n]
    · rw [ray_homogeneous _ _ (z8k _ _)]
      simpa [zT3] using heval (homogeneousComponent n p)
    · intro i _ hi
      rcases lt_or_gt_of_ne hi with h | h
      · have hz :homogeneousComponent i p=0:= by
          by_contra hne'
          exact (Nat.find_min' hex hne').not_gt h
        simp [hz]
      · rw [ray_homogeneous _ _ (z8k _ _),
          zT3,ite_eq_right h.not_ge]
    · exact fun h=>(h (Finset.mem_range.mpr (Nat.lt_succ_of_le hnle))).elim
  exact hne ((MvPolynomial.rename_eq_zero_iff_of_injective _ hj).mp
    (hcoeff.symm.trans (by rw [hp,Polynomial.coeff_zero])))
private theorem independent_of_first_coeff {k α β:Type*} [za6 k] {j:α→β}
    (hj:zq4 j) (g:α→(z3y β k)[X]) (c:α→k)
    (h0 : ∀ i,(g i).coeff 0=Cₘ (c i))
    (h1 : ∀ i,(g i).coeff 1=z9v (j i)) :
    zq4 (eval₂Hom C₂ g) := by
  let f :=eval₂Hom C₂ g
  let trans :=eval₂Hom Cₘ (fun i=>z9v i - Cₘ (c i))
  let inv :=eval₂Hom Cₘ (fun i=>z9v i+Cₘ (c i))
  have hs :Function.Surjective trans := by
    have hh:trans.comp inv=zz4 (z3y α k) := by
      apply ringHom_ext <;> intro a <;> simp [trans,inv]
    exact fun p=>⟨inv p,zmU hh p⟩
  have h:f.comp trans=BZ Cₘ (fun i=>(g i).divX) := by
    apply ringHom_ext
    · intro a
      simp [trans,f,BZ]
    · intro i
      simp only [zQb,trans,f,BZ,MvPolynomial.eval₂Hom_X',map_sub,
        MvPolynomial.eval₂Hom_C,zQb]
      rw [← h0,sub_eq_iff_eq_add,Polynomial.X_mul_divX_add]
  have hf :zq4 (f ∘ trans) := by
    change zq4 (f.comp trans)
    rw [h]
    exact ray_injective hj _ (fun i=> by simpa [Polynomial.coeff_divX] using h1 i)
  exact hf.of_comp_right hs
private def constant (s :ℕ) (b e :Fin 3→ℕ) (t:Fin 3) :Vars s b e :=
 ⟨t,zeroSlot s (b t) (e t)⟩
private abbrev Free (s :ℕ) (b e :Fin 3→ℕ) := {v :Vars s b e // v≠constant s b e 2}
private def ordinateSlot {s :ℕ} {b e :Fin 3→ℕ} (he :0<e 0) :
   Slot s (b 0) (e 0) :=
 ⟨⟨1,by omega⟩,⟨0,Nat.zero_lt_succ _⟩⟩
private def abscissaSlot {s :ℕ} {b e :Fin 3→ℕ} (hb:0<b 1) :
   Slot s (b 1) (e 1) :=
 ⟨⟨0,Nat.zero_lt_succ _⟩,⟨1,by omega⟩⟩
private def special {s :ℕ} {b e :Fin 3→ℕ} (he :0<e 0) (hb:0<b 1)
  (v :Vars s b e) :L :=
 if v=⟨0,ordinateSlot he⟩∨v=⟨1,abscissaSlot hb⟩ then -1 else 0
private def lab {s :ℕ} {b e :Fin 3→ℕ} (i:Free s b e) :Fin 2 ⊕ Vars s b e :=
 if i.val=constant s b e 0 then .inl 1
 else if i.val=constant s b e 1 then .inl 0 else .inr i.val
private theorem lab_injective {s :ℕ} {b e :Fin 3→ℕ} :
  zq4 (lab (s :=s) (b:=b) (e :=e)) := by
 intro i j h
 apply Subtype.ext
 unfold lab at h
 split_ifs at h with hi hj hk hl <;> simp_all
private theorem slot_degree_pos {s b e :ℕ} (i:Slot s b e)
  (hi:i≠zeroSlot s b e) :0< i.2.val+i.1.val := by
 rcases i with ⟨⟨i,hi'⟩,⟨j,hj'⟩⟩
 change 0<j+i
 by_contra! hz
 obtain rfl :i=0:= by omega
 obtain rfl :j=0:= by omega
 exact hi rfl
private theorem scaled_term {B:Type*} [za6 B] (d:B[X]) (x y :B) (a b:ℕ) :
  d*(T*Cₚ x)^a*(T*Cₚ y)^b =
    T^(a+b)*(d*Cₚ (x^a*y^b)) := by
 simp only [mul_pow,pow_add,map_mul,map_pow]
 ac_rfl
private theorem rest_coeff_zero {s :ℕ} {b e :Fin 3→ℕ} {B:Type} [za6 B]
  (d:Vars s b e→B[X]) (t:Fin 3) (x y :B) :
  (rest d t (T*Cₚ x) (T*Cₚ y)).coeff 0=0:= by
 rw [rest,zaW]
 apply Finset.sum_eq_zero
 intro i hi
 rw [scaled_term,zT3,ite_eq_right]
 exact (slot_degree_pos i (Finset.mem_erase.mp hi).1).not_ge
private theorem rest_coeff_one {s :ℕ} {b e :Fin 3→ℕ} {B:Type} [za6 B]
   (d:Vars s b e→B[X]) (t:Fin 3) (x y :B) (i:Slot s (b t) (e t))
   (hi:i.2.val+i.1.val=1) (hd : ∀ j≠i,(d ⟨t,j⟩).coeff 0=0) :
   (rest d t (T*Cₚ x) (T*Cₚ y)).coeff 1 =
     (d ⟨t,i⟩).coeff 0*(x^i.2.val*y ^i.1.val) := by
 rw [rest,zaW,zi6 i]
 · rw [scaled_term,hi,pow_one,Polynomial.coeff_X_mul]
   simp only [zwh,Polynomial.coeff_C_zero]
 · intro j hj hji
   have hpos :=slot_degree_pos j (Finset.mem_erase.mp hj).1
   rw [scaled_term,zT3]
   split_ifs with h
   · have heq :1-(j.2.val+j.1.val)=0:= by omega
     simp [heq,Polynomial.mul_coeff_zero,hd j hji]
   · rfl
 · intro h
   apply (h (Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩)).elim
   intro hz
   rw [hz] at hi
   exact (by decide : ¬ (0:ℕ)+0=1) hi
private theorem independent {s :ℕ} {b e :Fin 3→ℕ} (he :0<e 0) (hb:0<b 1) :
    zq4 ((incidence s b e).comp
      (rename (Subtype.val :Free s b e→Vars s b e)).toRingHom) := by
  let d (v :Vars s b e) : (Chart s b e)[X] :=
    Cₚ (Cₘ (special he hb v))+T*Cₚ (bcm v)
  let x :Chart s b e :=z9v (.inl 0)
  let y :Chart s b e :=z9v (.inl 1)
  let deform :Chart s b e →+* (Chart s b e)[X] :=
    eval₂Hom C₂
      (Sum.elim (fun i=>T*Cₚ (z9v (.inl i))) d)
  let f :=(incidence s b e).comp (rename (Subtype.val :Free s b e→Vars s b e)).toRingHom
  let g (i:Free s b e) :=deform (incidenceArg i.val)
  have hdc (v :Vars s b e) :deform (bcm v)=d v := by simp [deform,bcm]
  have hd0 (v :Vars s b e) : (d v).coeff 0=Cₘ (special he hb v) := by
    simp [d,zwh]
  have hd1 (v :Vars s b e) : (d v).coeff 1=bcm v := by simp [d]
  have hrest (t:Fin 3) :
      deform (rest bcm t x y) =
        rest d t (T*Cₚ x) (T*Cₚ y) := by
    rw [map_rest,show deform ∘ bcm=d from funext hdc]
    simp [deform,x,y]
  have hconst (t:Fin 3) :deform (incidenceArg (constant s b e t)) =
      -rest d t (T*Cₚ x) (T*Cₚ y) := by
    simpa [incidenceArg,constant,x,y] using congrArg Neg.neg (hrest t)
  have hnormal (i:Free s b e)
      (h0:i.val≠constant s b e 0) (h1 :i.val≠constant s b e 1) :g i=d i.val := by
    have hn:i.val.2≠zeroSlot s (b i.val.1) (e i.val.1) := by
      intro hz
      have heq :i.val=constant s b e i.val.1 :=Sigma.ext rfl (heq_of_eq hz)
      generalize ht:i.val.1=t at heq
      fin_cases t
      · exact h0 heq
      · exact h1 heq
      · exact i.property heq
    simpa only [g,incidenceArg,ite_eq_right hn] using hdc i.val
  let c (i:Free s b e) :L :=
    if i.val=constant s b e 0∨i.val=constant s b e 1 then 0 else special he hb i.val
  have hc0 (i:Free s b e) : (g i).coeff 0=Cₘ (c i) := by
    by_cases h0:i.val=constant s b e 0
    · change (deform (incidenceArg i.val)).coeff 0= _
      rw [h0,hconst,Polynomial.coeff_neg,rest_coeff_zero]
      simp [c,h0]
    by_cases h1 :i.val=constant s b e 1
    · change (deform (incidenceArg i.val)).coeff 0= _
      rw [h1,hconst,Polynomial.coeff_neg,rest_coeff_zero]
      simp [c,h1]
    rw [hnormal i h0 h1,hd0]
    simp [c,h0,h1]
  have hs0 (j:Slot s (b 0) (e 0)) :
      special he hb ⟨0,j⟩=if j=ordinateSlot he then -1 else 0:= by
    simp [special,show (0:Fin 3)≠1 by decide]
  have hs1 (j:Slot s (b 1) (e 1)) :
      special he hb ⟨1,j⟩=if j=abscissaSlot hb then -1 else 0:= by
    simp [special,show (1 :Fin 3)≠0 by decide]
  have hc1 (i:Free s b e) : (g i).coeff 1=z9v (lab i) := by
    by_cases h0:i.val=constant s b e 0
    · have hh:=rest_coeff_one d 0 x y (ordinateSlot he) rfl
          (fun j hj=> by rw [hd0,hs0,ite_eq_right hj,map_zero])
      change (deform (incidenceArg i.val)).coeff 1= _
      rw [h0,hconst,Polynomial.coeff_neg,hh,hd0,hs0]
      simp [lab,h0,ordinateSlot,y]
    by_cases h1 :i.val=constant s b e 1
    · have hh:=rest_coeff_one d 1 x y (abscissaSlot hb) rfl
          (fun j hj=> by rw [hd0,hs1,ite_eq_right hj,map_zero])
      change (deform (incidenceArg i.val)).coeff 1= _
      rw [h1,hconst,Polynomial.coeff_neg,hh,hd0,hs1]
      simp [lab,h1,abscissaSlot,x,constant]
    rw [hnormal i h0 h1,hd1]
    simp [lab,h0,h1,bcm]
  have hcomp:deform.comp f=eval₂Hom C₂ g:= by
    apply ringHom_ext <;> intro a <;> simp [f,incidence,deform,g]
  have hi:zq4 (deform ∘ f) := by
    change zq4 (deform.comp f)
    rw [hcomp]
    exact independent_of_first_coeff lab_injective g c hc0 hc1
  exact hi.of_comp
theorem proof :qBl3Pad.c2 := by
 intro s b e he hb hQ
 let A:=z3y (Free s b e) L
 let eqv :jo s b e ≃ₐ[L] A[X] :=
   (MvPolynomial.renameEquiv L (Equiv.optionSubtypeNe (constant s b e 2)).symm).trans
     (MvPolynomial.optionEquivLeft L (Free s b e))
 let f :=(incidence s b e).comp eqv.symm.toRingEquiv.toRingHom
 have heq :eqv.symm.toRingEquiv.toRingHom.comp Cₚ =
     (rename (Subtype.val :Free s b e→Vars s b e)).toRingHom:= by
   apply ringHom_ext
   · intro a
     change eqv.symm (Cₚ (Cₘ a))= _
     simp [eqv,A]
   · intro i
     change eqv.symm (Cₚ (z9v i))= _
     simp [eqv,A]
 have hf :zq4 (f.comp Cₚ) := by
   change zq4 (((incidence s b e).comp eqv.symm.toRingEquiv.toRingHom).comp Cₚ)
   rw [RingHom.comp_assoc,heq]
   exact independent (he 0) hb
 obtain ⟨q,hq,hz⟩:=hQ
 obtain ⟨p,hp,hp0,hdiv⟩:=principal f hf
   ⟨eqv q,fun h=>hq (eqv.injective (h.trans (eqv.map_zero).symm)),by simpa [f] using hz⟩
 refine ⟨eqv.symm p,fun h=>hp (eqv.symm.injective (h.trans (eqv.symm.map_zero).symm)),hp0,?_⟩
 intro r hr
 have hfr :f (eqv r)=0:= by simpa [f] using hr
 simpa using map_dvd eqv.symm (hdiv (eqv r) hfr)
end
end qOuTtVa
end
section
set_option autoImplicit true
open MvPolynomial renaming IsWeightedHomogeneous→qz0
namespace qDttdYd
noncomputable section
open scoped Classical Matrix
open cu (L)
open MvPolynomial
open qfbIfsd (Slot Vars form)
open qBl3Pad
private def includePair {s :ℕ} {b e :Fin 3→ℕ} {k :Fin 3} :
   PairCoeffs s b e k →+* jo s b e :=
 (rename Subtype.val).toRingHom
private theorem includePair_X {s :ℕ} {b e :Fin 3→ℕ} {k :Fin 3}
  (v :OtherVars s b e k) :includePair (z9v v)=z9v v.val := by
 change rename Subtype.val (z9v v :PairCoeffs s b e k)=z9v v.val
 exact rename_X _ _
private theorem pair_degree {s :ℕ} {b e :Fin 3→ℕ} {k :Fin 3}
  (p:PairCoeffs s b e k) : (includePair p).weightedTotalDegree (blockWeight k)=0:= by
 change (rename Subtype.val p).weightedTotalDegree (blockWeight k)=0
 rw [weightedTotalDegree_rename_of_injective Subtype.val_injective]
 have hw:blockWeight k ∘ (Subtype.val :OtherVars s b e k→Vars s b e)=fun _=>0:= by
  funext v
  exact ite_eq_right v.property
 simp [hw,weightedTotalDegree,Finsupp.weight_apply,Finsupp.sum]
private theorem a3u {V ι:Type} [Fintype ι] [DecidableEq ι] (w:V→ℕ)
    (D:Matrix ι ι (z3y V L))
    (h : ∀ i j,qz0 w (D i j) 1) :
    D.det.weightedTotalDegree w≤zhP ι:= by
  have hd:qz0 w D.det (zhP ι) := by
    rw [Matrix.det_apply]
    apply IsWeightedHomogeneous.sum
    intro π _
    have hp:qz0 w (∏ i,D (π i) i) (zhP ι) := by
      simpa using IsWeightedHomogeneous.prod Finset.univ (fun i=>D (π i) i)
        (fun _=>1) (fun i _=>h (π i) i)
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hπ | hπ
    · simpa [hπ,Units.smul_def] using hp
    · simpa [hπ,Units.smul_def] using hp.neg
  exact Finset.sup_le fun _ hm=>(hd (mem_support_iff.mp hm)).le
private theorem form_incidence {s :ℕ} {b e :Fin 3→ℕ} (t:Fin 3) :
   form (incidenceArg (s :=s) (b:=b) (e :=e)) t (z9v (.inl 0)) (z9v (.inl 1))=0:= by
 rw [form_eq]
 have h:rest incidenceArg t (z9v (.inl 0)) (z9v (.inl 1)) =
     rest (bcm (s :=s) (b:=b) (e :=e)) t (z9v (.inl 0)) (z9v (.inl 1)) := by
   unfold rest
   refine zUo rfl fun i hi => ?_
   rw [incidenceArg,ite_eq_right (Finset.ne_of_mem_erase hi)]
 simp [h,incidenceArg]
set_option maxHeartbeats 600000 in
theorem proof :qBl3Pad.c3:= by
  classical
  intro s b e _ _ k hfinite
  let O:=PairCoeffs s b e k
  let F:=MY s b e k
  let A:=PairAlgebra s b e k
  let E :=FractionRing (Chart s b e)
  let γ:Chart s b e →+* E :=algebraMap _ _
  let φ:jo s b e →+* E :=γ.comp (incidence s b e)
  let q0:O →+* jo s b e :=includePair
  let ι:=Fin (Module.finrank F A)
  let B:Module.Basis ι F A:=Module.finBasis F A
  let z :=zeroSlot s (b k) (e k)
  let q:=Ideal.Quotient.mk (Ib s b e k)
  let u (w:Slot s (b k) (e k)) :A :=
    q ((z9v 0:lK s b e k)^w.2.val*z9v 1^w.1.val)
  have u_zero :u z=1 := by simp [u,z,zeroSlot]
  have hγ:zq4 γ:=zxb (Chart s b e) E
  by_cases hinj:zq4 (φ.comp q0)
  swap
  · obtain ⟨p,r,hpr,hn⟩:=Function.not_injective_iff.mp hinj
    refine ⟨q0 (p-r),?_,?_,?_⟩
    · exact (map_ne_zero_iff _ (rename_injective _ Subtype.val_injective)).2 (sub_ne_zero.mpr hn)
    · apply hγ
      change (φ.comp q0) (p-r)=γ 0
      rw [map_sub,hpr,sub_self,map_zero]
    · rw [pair_degree]
      exact Nat.zero_le _
  let g:F →+* E :=zIj hinj
  have hg (p:O) :g (algebraMap O F p)=φ (q0 p) :=IsLocalization.lift_eq _ p
  let x :E :=γ (z9v (.inl 0))
  let y :E :=γ (z9v (.inl 1))
  have q1 (t:Fin 3) :form (fun v=>φ (z9v v)) t x y=0:= by
    have hv (v :Vars s b e) :φ (z9v v)=γ (incidenceArg v) := by
      simp [φ,incidence]
    simpa only [form,map_sum,map_mul,map_pow,map_zero,hv,x,y]
      using congrArg γ (form_incidence (s :=s) (b:=b) (e :=e) t)
  let f :lK s b e k →+* E :=eval₂Hom g ![x,y]
  have hf : ∀ p∈Ib s b e k,f p=0:= by
    have hle :Ib s b e k≤RingHom.ker f := by
      apply Ideal.span_le.mpr
      rintro _ ⟨t,ht,rfl⟩
      change f (pairForm s b e k t)=0
      have hc (w:Slot s (b t) (e t)) :
          g (pairCoeff k ⟨t,w⟩)=φ (z9v ⟨t,w⟩) := by
        rw [pairCoeff,dite_eq_left (show t≠k from ht),hg]
        change φ (includePair (z9v (⟨⟨t,w⟩,ht⟩:OtherVars s b e k)))= _
        rw [includePair_X]
      simpa [pairForm,form,f,hc] using q1 t
    exact fun p hp=>hle hp
  let ψ:A →+* E :=Ideal.Quotient.lift _ f hf
  have hψ (a :F) :ψ (algebraMap F A a)=g a := by
    change f (C a)=g a
    simp [f]
  have q4 (c:F) (p:A) :ψ (c•p)=g c*ψ p:= by
    rw [Algebra.smul_def c p,map_mul,hψ]
  have hψu (w:Slot s (b k) (e k)) :ψ (u w)=x^w.2.val*y ^w.1.val := by
    change f ((z9v 0:lK s b e k)^w.2.val*z9v 1^w.1.val)= _
    simp [f]
  have hsum : ∑ w:Slot s (b k) (e k),φ (z9v ⟨k,w⟩)*ψ (u w)=0:= by
    simpa only [form,hψu,mul_assoc] using q1 k
  let a (v :ι×ι×Slot s (b k) (e k)) :F:=B.repr (u v.2.2*B v.2.1) v.1
  obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) a
  choose num hnum using hd
  simp only [Algebra.smul_def] at hnum
  let D:Matrix ι ι (jo s b e) := fun i j =>
    ∑ w:Slot s (b k) (e k),q0 (num (i,j,w))*z9v ⟨k,w⟩
  have hD {M:Type} [Field M] (ev :jo s b e →+* M) (lift:F →+* M)
      (h : ∀ p:O,ev (q0 p)=lift (algebraMap O F p)) :
      D.map ev=lift (algebraMap O F (d:O))•(zd7 fun i j =>
        ∑ w:Slot s (b k) (e k),ev (z9v ⟨k,w⟩)*lift (a (i,j,w))) := by
    apply Matrix.ext
    intro i j
    change ev (D i j)=lift (algebraMap O F (d:O)) *
      ∑ w,ev (z9v ⟨k,w⟩)*lift (a (i,j,w))
    simp only [D,map_sum,map_mul,h,hnum,zxw]
    exact zUo rfl fun w _=> by ring
  let ε:jo s b e →+* F :=
    eval₂Hom ((algebraMap O F).comp C) fun v =>
      if h:v.1≠k then algebraMap O F (z9v ⟨v,h⟩) else
        if v=⟨k,z⟩ then 1 else 0
  have hε:ε.comp q0=algebraMap O F:= by
    apply MvPolynomial.ringHom_ext
    · intro l
      simp [ε,q0,includePair]
    · rintro ⟨v,hv⟩
      simp [ε,q0,includePair,hv]
  have q3 (w:Slot s (b k) (e k)) :ε (z9v ⟨k,w⟩)=if w=z then 1 else 0:= by
    simp [ε]
  have hId: (zd7 fun i j:ι =>
      ∑ w:Slot s (b k) (e k),ε (z9v ⟨k,w⟩)*a (i,j,w))=1 := by
    apply Matrix.ext
    intro i j
    change (∑ w,ε (z9v ⟨k,w⟩)*a (i,j,w))= _
    rw [zi6 z]
    · rw [q3,ite_eq_left rfl,one_mul]
      change B.repr (u z*B j) i= _
      rw [u_zero,one_mul,Module.Basis.repr_self_apply,Matrix.one_apply]
      by_cases hij:i=j
      · subst j
        rfl
      · rw [ite_eq_right (Ne.symm hij),ite_eq_right hij]
    · intro w _ hw
      rw [q3,ite_eq_right hw,zero_mul]
    · simp
  have hDne :D.det≠0:= by
    have q2 :=hD ε (zz4 F) (RingHom.congr_fun hε)
    rw [show (zd7 fun i j:ι =>
      ∑ w:Slot s (b k) (e k),ε (z9v ⟨k,w⟩)*(zz4 F) (a (i,j,w))) =
      1 from hId] at q2
    have hn:algebraMap O F (d:O)≠0 :=
      (map_ne_zero_iff _ (zxb O F)).2
        (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
    intro hz
    have he :=ε.map_det D
    change ε D.det=(D.map ε).det at he
    rw [hz,map_zero,q2,Matrix.det_smul,Matrix.det_one,mul_one] at he
    exact pow_ne_zero _ hn he.symm
  have hker : (fun i=>ψ (B i)) ᵥ* (D.map φ)=0:= by
    rw [hD φ g (fun p=>(hg p).symm),Matrix.vecMul_smul]
    suffices h: (fun i=>ψ (B i)) ᵥ* (zd7 fun i j =>
        ∑ w:Slot s (b k) (e k),φ (z9v ⟨k,w⟩)*g (a (i,j,w)))=0 by
      rw [h,smul_zero]
    funext j
    rw [Matrix.vecMul_apply_eq_sum,Pi.zero_apply]
    simp only [Matrix.of_apply,zxw]
    rw [Finset.sum_comm]
    have hcol (w:Slot s (b k) (e k)) :
        ∑ i:ι,ψ (B i)*g (a (i,j,w))=ψ (u w)*ψ (B j) := by
      simpa only [a,map_sum,q4,map_mul,mul_comm (g _) (ψ _)]
        using congrArg ψ (B.sum_repr (u w*B j))
    calc
      _ = ∑ w,φ (z9v ⟨k,w⟩)*(∑ i:ι,ψ (B i)*g (a (i,j,w))) := by
        refine zUo rfl fun w _ => ?_
        rw [zxw]
        exact zUo rfl fun i _=> by ring
      _=(∑ w,φ (z9v ⟨k,w⟩)*ψ (u w))*ψ (B j) := by
        rw [Finset.sum_mul]
        simp only [hcol,mul_assoc]
      _=0:= by rw [hsum,zero_mul]
  have hvec: (fun i=>ψ (B i))≠0:= by
    intro h
    have hz (i:ι) :ψ (B i)=0:=congrFun h i
    have he :=congrArg ψ (B.sum_repr (1 :A))
    simp only [map_sum,q4,hz,mul_zero,Finset.sum_const_zero,
      map_one,zero_ne_one] at he
  have hdet: (D.map φ).det=0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨_,hvec,hker⟩
  refine ⟨D.det,hDne,?_,?_⟩
  · apply hγ
    rw [map_zero]
    change φ D.det=0
    rw [φ.map_det]
    exact hdet
  · refine (a3u (blockWeight k) D ?_).trans (Fintype.card_fin (Module.finrank F A)).le
    intro i j
    apply IsWeightedHomogeneous.sum
    intro w _
    have h₀:qz0 (blockWeight k) (q0 (num (i,j,w))) 0 :=
      isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero.mpr (pair_degree _)
    have h₁:qz0 (blockWeight k) (z9v (R:=L) ⟨k,w⟩) 1 := by
      simpa [blockWeight] using isWeightedHomogeneous_X (R:=L) (blockWeight (s :=s) (b:=b) (e :=e) k) ⟨k,w⟩
    exact h₀.mul h₁
end
end qDttdYd
end
