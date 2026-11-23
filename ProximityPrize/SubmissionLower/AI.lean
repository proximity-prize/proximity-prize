import ProximityPrize.SubmissionLower.L
import ProximityPrize.SubmissionLower.AH
import ProximityPrize.SubmissionLower.C
set_option Elab.async false
open _root_ renaming Algebra.algebraMap→nq,AlgebraicIndependent→qy,Finset.le_sup→pC,Finset.mem_univ→pz,Finsupp.single→ oj,Ideal→mD,Ideal.Quotient.eq_zero_iff_mem→p7,Ideal.Quotient.mk→nX,Ideal.Quotient.mk_surjective→qz,Ideal.span→pU,Ideal.subset_span→p6,Module.finrank→pL,MvPolynomial→lJ,MvPolynomial.X→ ov,MvPolynomial.exists_eval_affineHilbertPolynomial→qx,MvPolynomial.homogeneousComponent→ oq,MvPolynomial.homogeneousComponent_isHomogeneous→p9,MvPolynomial.map→nI,MvPolynomial.mk_mem_quotientDegreeLE→pG,MvPolynomial.monomial→c9,MvPolynomial.quotientDegreeLE→ oD,Option→ ox,Submodule.mem_bot→qm,Submodule.mem_colon_singleton→ oz,Subtype.ext→ oy,aaq.Degree→n5,aaq.shift→cy,bzP.Ambient→lI,bzP.model→lz,bzP.stamp→aU,le_max_left→p5,le_max_right→pQ,map_sub→ oY,mul_comm→ oK,smul_eq_mul→ oZ,zP.Exponent→lV
set_option autoImplicit true
section
namespace bzP
noncomputable section
open zP aaq aA9 MvPolynomial
open scoped Pointwise
variable {A:Fin 4→Finset lV}
private def bLg (I:mD (af A)) :mD (lz A) where
 carrier := {f | ∀ d,(f :lI A).coeff d∈I}
 zero_mem' := by simp
 add_mem' := by
  intro f g hf hg d
  exact I.add_mem (hf d) (hg d)
 smul_mem' := by
  classical
  intro f g hg d
  change ((f :lI A)*(g:lI A)).coeff d∈I
  rw [coeff_mul]
  exact I.sum_mem fun e _=>I.mul_mem_left _ (hg e.2)
private theorem eAd {I:mD (af A)} {f :lz A} {d:lV}
   {p:af A} (h: (f :lI A)=c9 d p) (hp:p∈I) :f∈bLg I:= by
 classical
 intro k
 rw [h,coeff_monomial]
 split_ifs
 · exact hp
 · exact I.zero_mem
private def cut (i:Fin 4) :lz A :=
 tag (oj i 1) (p:=ve A i) (by
   have h: (1 :af A)∈dO A 0:= by
     have h0: (0:lV)∈Bc A 0:= by simp [Bc]
     exact Submodule.subset_span ⟨⟨0,h0⟩,rfl⟩
   simpa [cy ,Finsupp.single_eq_pi_single] using bFi i h)
private def target (A:Fin 4→Finset lV) (i:Fin 4) :mD (lz A) :=
 pU {cut i} ⊔ bLg (mo A i.val)
private theorem c0i {i:Fin 4} {f :lz A} :
   f∈target A i ↔ ∃ r :lz A,f - cut i*r∈bLg (mo A i.val) := by
 rw [target,Ideal.mem_span_singleton_sup]
 constructor
 · rintro ⟨r,b,hb,rfl⟩
   exact ⟨r,by simpa [oK r (cut i)] using hb⟩
 · rintro ⟨r,hr⟩
   exact ⟨r,_,hr,by rw [oK r,add_sub_cancel]⟩
private theorem extract {i:Fin 4} {d:n5} {p:af A}
   (hp:p∈dO A (cy d i 1))
   (h:tag (aU (cy d i 1)) hp∈target A i) :
   ∃ r∈dO A d,p - ve A i*r∈mo A i.val := by
 obtain ⟨r,hr⟩:=c0i.mp h
 refine ⟨(r :lI A).coeff (aU d),bXQ r (aU d),?_⟩
 have H :=hr (aU (cy d i 1))
 change (c9 (aU (cy d i 1)) p -
   c9 (oj i 1) (ve A i)*(r :lI A)).coeff
     (aU (cy d i 1))∈mo A i.val at H
 rw [MvPolynomial.coeff_sub,coeff_monomial,ite_eq_left rfl,dft,
   add_comm (aU d),coeff_monomial_mul] at H
 exact H
private theorem adr (d:n5) (i:Fin 4) (m:ℕ) :
   aU (fun _=>m)+stamp (cy d i 1) =
     oj i 1+stamp (d+fun _=>m) := by
 rw [dft]
 ext j
 change m+(d j+(oj i 1 :lV) j)=(oj i 1 :lV) j+(d j+m)
 omega
private theorem eDX {R:Type*} [CommRing R] (a b c d:lV)
  (h:a+b=c+d) (p q r s :R) :
  (c9 a p:lJ (Fin 4) R)*c9 b q - c9 c r*c9 d s =
    c9 (c+d) (p*q - r*s) := by
 simp only [monomial_mul_monomial,h,oY]
private theorem dIG (h:byY A) (i:Fin 4) (d:n5) {p:af A}
    (hp:p∈dO A (cy d i 1)) (hrel :p∈mo A (i.val+1)) (a :Chart A) :
    ∃ m:ℕ,bY a^m*tag (aU (cy d i 1)) hp∈target A i:= by
  obtain ⟨m,r,hr,hrel'⟩:=h i d p hp hrel a
  let dm:Degree :=d+(fun _:Fin 4=>m)
  have hr' : r∈dO A (aU dm) := by
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact hr
  let t:lz A:=tag (A:=A) (p:=r) (aU dm) hr'
  let g:lz A:=tag (A:=A) (p:=p) (aU (cy d i 1)) hp
  let f :lz A:=bY a^m*g - cut i*t
  refine ⟨m,(c0i (A:=A) (i:=i) (f :=bY a^m*g)).mpr ⟨t,?_⟩⟩
  change f∈bLg (mo A i.val)
  refine eAd (A:=A) (I:=mo A i.val) (f :=f)
    (d:=oj i 1+stamp dm)
    (p:=a2m a m*p - ve A i*r) ?_ hrel'
  calc
    (f :lI A) =
        ((bY a^m:lz A) :lI A)*c9 (aU (cy d i 1)) p -
          c9 (oj i 1) (ve A i)*c9 (aU dm) r :=rfl
    _ = _:= by
      rw [dIO]
      exact eDX _ _ _ _ (adr d i m) (a2m a m) p (ve A i) r
private theorem c42 {R:Type*} [CommRing R] (J:mD R) (x f :R)
  {l m:ℕ} (h:l≤ m) (hl:x^l*f∈J) :x^m*f∈J:= by
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le h
 rw [add_comm l k,pow_add,mul_assoc]
 exact J.mul_mem_left _ hl
private theorem gGW {R:Type*} [CommRing R] [IsNoetherianRing R]
   (J:mD R) (x :R) : ∃ M:ℕ,∀ f :R,
     (∃ m:ℕ,x^m*f∈J)→x^M*f∈J:= by
 let C:ℕ →o Submodule R R :=
   ⟨fun m=>J.colon {x^m},fun l m hlm f hf=> by
     rw [oz ,oZ,oK f] at hf ⊢
     exact c42 J x f hlm hf⟩
 obtain ⟨M,hM⟩:=monotone_stabilizes_iff_noetherian.mpr (inferInstance :IsNoetherian R R) C
 refine ⟨M,fun f ⟨m,hm⟩ => ?_⟩
 have hle :C m≤C M:= by
   rcases le_total m M with hl | hl
   · exact C.monotone hl
   · exact (hM m hl).ge
 have hmem:f∈C m:= by
   change f∈J.colon {x^m}
   simpa only [oz ,oZ,oK f] using hm
 have hmem' : f∈J.colon {x^M} := hle hmem
 simpa only [oz ,oZ,oK f] using hmem'
private def bHr (A:Fin 4→Finset lV) (i:Fin 4) (b:ℕ) :Set (lz A) :=
 {f | ∃ (d:n5) (p:af A) (hp:p∈dO A (cy d i 1)),
   (∀ j,d j≤b)∧p∈mo A (i.val+1)∧f=tag (aU (cy d i 1)) hp}
private theorem dz8 (i:Fin 4) : ∃ B:ℕ,∀ (d:n5) {p:af A}
   (hp:p∈dO A (cy d i 1)),p∈mo A (i.val+1) →
     tag (aU (cy d i 1)) hp∈pU (bHr A i B) := by
 classical
 let C:ℕ →o Submodule (lz A) (lz A) :=
   ⟨fun b=>pU (bHr A i b),fun _ _ hn=>Ideal.span_mono (by
     rintro _ ⟨d,p,hp,hd,hrel,rfl⟩
     exact ⟨d,p,hp,fun j=>(hd j).trans hn,hrel,rfl⟩)⟩
 obtain ⟨B,hB⟩:=monotone_stabilizes_iff_noetherian.mpr inferInstance C
 refine ⟨B,fun d p hp hrel => ?_⟩
 have h:tag (aU (cy d i 1)) hp∈C (max B (Finset.univ.sup d)) :=
   p6 ⟨d,p,hp,fun j=>(pC (pz j)).trans (pQ _ _),
     hrel,rfl⟩
 rwa [← hB _ (p5 _ _)] at h
private theorem eO9 {f :lz A} {d e :lV} {p:af A}
  (hp:p∈dO A e) :proj (d+e) (f*tag e hp)=proj d f*tag e hp:= by
 apply oy
 change c9 (d+e) (((f :lI A)*c9 e p).coeff (d+e)) =
  c9 d ((f :lI A).coeff d)*c9 e p
 rw [monomial_mul_monomial,coeff_mul_monomial]
private theorem eO8 (d:lV) (f g:lz A) :
  proj d (f+g)=proj d f+proj d g:= by
 apply oy
 change c9 d (((f :lI A)+(g:lI A)).coeff d) =
  c9 d ((f :lI A).coeff d)+monomial d ((g:lI A).coeff d)
 change c9 d ((f :lI A).coeff d+(g:lI A).coeff d)= _
 exact map_add (c9 d) _ _
private theorem guA (hz : ∀ i,0∈A i) (h:byY A) (i:Fin 4) :
    ∃ b:ℕ,∀ (d:n5),(∀ j,b≤d j) →
      ∀ p∈dO A (cy d i 1),p∈mo A (i.val+1) →
        ∃ r∈dO A d,p - ve A i*r∈mo A i.val := by
  classical
  obtain ⟨B,hB⟩:=dz8 (A:=A) i
  choose M hM using fun a :Chart A=>gGW (target A i) (bY a)
  let m:=Finset.univ.sup M
  let N :=Finset.univ.sup fun j=>(A j).card*m
  have hkill (g:lz A) (hg:g∈bHr A i B) :
      Jy A m≤(target A i).colon {g} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change bY a^m∈(target A i).colon {g}
    rw [oz ,oZ]
    obtain ⟨d,p,hp,_,hrel,rfl⟩:=hg
    apply c42 _ _ _ (show M a≤ m from pC (pz a))
    exact hM a _ (dIG h i d hp hrel a)
  have hhigh (f :lz A) (hf :f∈pU (bHr A i B)) :
      ∀ (q:lz A) (e :lV),(∀ j,B+1+N≤e j)→proj e (q*f)∈target A i:= by
    induction hf using Submodule.span_induction with
    | mem g hg =>
      intro q e he
      obtain ⟨d,p,hp,hd,hrel,rfl⟩:=hg
      let k :=aU (cy d i 1)
      have hk (j:Fin 4) :k j≤B+1 := by
        change d j+(Pi.single i 1 :n5) j≤B+1
        by_cases hij:j=i
        · subst j
          simpa only [Pi.single_eq_same] using Nat.succ_le_succ (hd i)
        · rw [Pi.single_eq_of_ne hij,add_zero]
          exact (hd j).trans (Nat.le_succ B)
      have hle :k≤e := fun j=>(hk j).trans ((Nat.le_add_right _ _).trans (he j))
      have hsub:e - k+k=e :=tsub_add_cancel_of_le hle
      have hs (j:Fin 4) : (A j).card*m≤(e - k) j:= by
        have hN : (A j).card*m≤N :=
          pC (f := fun j=>(A j).card*m) (pz j)
        change (A j).card*m≤e j - k j
        have :=hk j
        have :=he j
        omega
      have hm:=Submodule.mem_colon_singleton.mp (hkill _ ⟨d,p,hp,hd,hrel,rfl⟩
        (gyT hz hs (bXQ q (e - k))))
      rw [← hsub]
      exact (eO9 (f :=q) (d:=e - k) (e :=k) (show p∈dO A k from hp)).symm ▸ hm
    | zero =>
      intro q e he
      rw [mul_zero]
      have hz' : proj e (0:lz A)=0:= by
        apply oy
        change c9 e ((0:lI A).coeff e)=0
        simp
      rw [hz']
      exact (target A i).zero_mem
    | add f g _ _ hf hg =>
      intro q e he
      rw [mul_add,eO8]
      exact (target A i).add_mem (hf q e he) (hg q e he)
    | smul r f _ hf =>
      intro q e he
      simpa only [oZ,mul_assoc] using hf (q*r) e he
  refine ⟨B+1+N,fun d hd p hp hrel=>extract hp ?_⟩
  have H :=hhigh _ (hB d hp hrel) 1 (aU (cy d i 1)) (fun j =>
    (hd j).trans (Nat.le_add_right _ _))
  rw [one_mul] at H
  convert H using 1
  apply oy
  change c9 (aU (cy d i 1)) p =
    c9 (aU (cy d i 1)) ((c9 (aU (cy d i 1)) p).coeff (aU (cy d i 1)))
  rw [coeff_monomial,ite_eq_left rfl]
theorem proof :aA9.c2 := by
 classical
 intro A hz h
 choose b hb using guA hz h
 exact ⟨Finset.univ.sup b,fun i d hd=>hb i d (fun j =>
  (pC (pz i)).trans (hd j))⟩
end
end bzP
end
section
namespace czg
theorem proof :axk.c4 :=
 bRN.proof
end czg
end
section
namespace bzU
theorem proof :OH.c3 :=
 eFW aKx.proof aZc.proof
  czD.proof bRM.proof bRN.proof
end bzU
end
section
set_option maxHeartbeats 750000
set_option maxRecDepth 2000
namespace bzG
noncomputable section
open NS lB aFV ata MvPolynomial
variable {k E σ:Type} [Field k] [Field E] [Algebra k E]
private theorem bIT (p:lJ σ k) (n:ℕ) :
   nI (nq k E) (oq n p) =
     oq n (nI (nq k E) p) := by
 ext d
 by_cases hd:d.degree=n <;>
   simp only [MvPolynomial.coeff_map,coeff_homogeneousComponent,hd,ite_true,ite_false,map_zero]
private theorem enB [Finite σ]
  {A B:mD (lJ σ E)} (hAB:A≤B)
  (h:affineHilbertPolynomial A=affineHilbertPolynomial B) :A=B:= by
 obtain ⟨a,ha⟩:=qx A
 obtain ⟨b,hb⟩:=qx B
 refine le_antisymm hAB ?_
 intro p hp
 let n:=max p.totalDegree (max a b)
 let V:=oD A n
 let W:=oD B n
 let q:=(Ideal.Quotient.factorₐ E hAB).toLinearMap
 have hq (x :V) :q x∈W:= by
  obtain ⟨r,hr,he⟩:=mem_quotientDegreeLE.mp x.property
  rw [← he]
  exact pG hr
 let f :V →ₗ[E] W:=(q.domRestrict V).codRestrict W hq
 have hsurj:Function.Surjective f := by
  intro y
  obtain ⟨r,hr,he⟩:=mem_quotientDegreeLE.mp y.property
  exact ⟨⟨nX A r,pG hr⟩,oy he⟩
 have he :pL E V=pL E W:= by
  have hna :a≤n:=(p5 _ _).trans (pQ _ _)
  have hnb:b≤n:=(pQ _ _).trans (pQ _ _)
  have he :=(ha n hna).symm.trans ((congrArg (Polynomial.eval (n:ℚ)) h).trans (hb n hnb))
  change ((pL E V:ℕ) :ℚ)=(pL E W:ℚ) at he
  exact_mod_cast he
 have hinj:=(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he (f :=f)).mpr hsurj
 let x :V:=⟨nX A p,pG (p5 _ _)⟩
 have hx :f x=f 0:= by
  rw [map_zero]
  exact oy (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
 exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val (hinj hx))
private theorem bmp (I:mD (lJ AK k)) :
   lW (I.map (nI (nq k E))) =
     (lW I).map (nI (nq k E)) := by
 let f :lJ AK k →+* lJ AK E :=
   nI (nq k E)
 symm
 apply enB
 · apply Ideal.map_le_iff_le_comap.mpr
   apply Ideal.span_le.mpr
   rintro _ ⟨p,n,hp,hn,rfl⟩
   change f (oq n p)∈lW (I.map f)
   rw [bIT]
   apply p6
   exact ⟨f p,n,Ideal.mem_map_of_mem _ hp,
     (Finset.sup_mono (support_map_subset (nq k E) p)).trans hn,rfl⟩
 · rw [Ey.ZI,YT.bqR,
     YT.bqR,Ey.ZI]
private theorem dsG {t:ox AK→E} (ht:qy k t)
   (I:mD (lJ AK k)) :
   IsLeftRegular (nX (I.map (nI (nq k E)))
     (ahd t)) := by
 classical
 rw [isLeftRegular_iff_right_eq_zero_of_mul]
 intro x hx
 obtain ⟨p,rfl⟩:=qz x
 rw [← map_mul,p7] at hx
 rw [p7]
 let a :ox AK→lJ AK k :=
   fun i=>i.elim 1 ov
 have he : (∑ i,C (t i)*nI (nq k E) (a i))=ahd t:= by
   simp [Fintype.sum_option,a,ahd]
 obtain ⟨m,hm⟩:=bHq ht I a none p (he.symm ▸ hx)
 simpa [a] using hm
private def slope (t:ox AK→E) :lJ AK E :=
 ∑ i,C (t (some i))*ov i
private theorem aDK {σ F:Type} [Fintype σ] [Field F] (a :σ→F) :
   (∑ i,C (a i)*ov i).IsHomogeneous 1 :=
 (homogeneousSubmodule σ F 1).sum_mem fun i _=>isHomogeneous_C_mul_X _ i
private theorem cpZ (t:ox AK→E) : (slope t).IsHomogeneous 1 :=
 aDK (fun i:AK=>t (some i))
private theorem ef6 {t:ox AK→E}
   (ht:qy k t) (I:mD (lJ AK k)) :
   bze
     (lW (I.map (nI (nq k E)))) (slope t) := by
 let J:=I.map (nI (nq k E))
 let B:=lW J
 apply bRD.proof B (slope t) (bBP J) (cpZ t)
 intro P hP hi hℓ
 obtain ⟨i,hi⟩:=hi
 obtain ⟨x,he⟩:=(isAssociatedPrime_iff.mp hP).2
 obtain ⟨p,rfl⟩:=qz x
 have hmul :slope t*p∈B:= by
   rw [he,oz ,qm] at hℓ
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   rw [map_mul]
   exact hℓ
 have hgen:=bHq (ht.comp some (Option.some_injective AK))
   (lW I) ov i p
 simp only [MvPolynomial.map_X,Function.comp_apply,← bmp] at hgen
 obtain ⟨m,hm⟩:=hgen hmul
 have hpow:ov i^m∈P:= by
   rw [he,oz ,qm]
   change nX B (ov i^m)* nX B p=0
   rw [← map_mul]
   exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
 exact hi (hP.isPrime.mem_of_pow_mem _ hpow)
private theorem dVq {p:lJ σ E} {n:ℕ}
  (hp:p.totalDegree≤n+1) (h:oq (n+1) p=0) :
  p.totalDegree≤n:= by
 apply Finset.sup_le
 intro d hd
 have hle :=(le_totalDegree hd).trans hp
 have hne :d.degree≠n+1 := by
  intro he
  apply mem_support_iff.mp hd
  simpa [coeff_homogeneousComponent,he] using congrArg (fun q:lJ σ E=>q.coeff d) h
 exact Nat.le_of_lt_succ (lt_of_le_of_ne (show d.degree≤n+1 from hle) hne)
private theorem guV {t:ox AK→E}
    {J:mD (lJ AK E)}
    (h:bze (lW J) (slope t)) :
    ∃ N :ℕ,∀ n≥N,∀ x∈oD J (n+1),
      nX J (ahd t)*x∈oD J (n+1) →
      x∈oD J n:= by
  obtain ⟨N,hN⟩:=h
  refine ⟨N,fun n hn x hx hfx => ?_⟩
  obtain ⟨p,hp,rfl⟩:=mem_quotientDegreeLE.mp hx
  obtain ⟨q,hq,hqeq⟩:=mem_quotientDegreeLE.mp hfx
  have hrel :ahd t*p - q∈J:= by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [oY ,map_mul,hqeq,sub_self]
  have hform :ahd t=C (t none)+slope t:=rfl
  have hlin:=(cpZ t).totalDegree_le
  have hdeg: (ahd t*p - q).totalDegree≤n+2 := by
    have hfd: (ahd t).totalDegree≤1 := by
      rw [hform]
      exact (totalDegree_add _ _).trans (max_le (by simp) hlin)
    exact (totalDegree_sub _ _).trans (max_le
      ((totalDegree_mul _ _).trans (by omega)) (by omega))
  have hcomp:oq (n+2) (ahd t*p - q) =
      slope t*oq (n+1) p:= by
    rw [hform,add_mul,oY ,map_add,
      homogeneousComponent_eq_zero _ q (by omega),sub_zero,
      homogeneousComponent_eq_zero _ (C (t none)*p) (by
        apply (totalDegree_mul _ _).trans_lt
        simp only [totalDegree_C,zero_add]
        omega),zero_add,bYu (cpZ t)]
  have hlead:slope t*oq (n+1) p∈lW J:= by
    rw [← hcomp]
    exact p6 ⟨_,n+2,hrel,hdeg,rfl⟩
  have hmem:=hN (n+1) (by omega) _ (p9 _ _) hlead
  obtain ⟨r,hr,hrd,htop⟩:=YT.a5m J hmem (n+1)
  have hd: (p - r).totalDegree≤n :=
    dVq ((totalDegree_sub _ _).trans (max_le hp hrd)) (by
      rw [oY ,htop,homogeneousComponent_eq_self (p9 _ _),
        sub_self])
  have hq' : nX J (p - r)=nX J p:= by
    rw [oY ,Ideal.Quotient.eq_zero_iff_mem.mpr hr,sub_zero]
  rw [← hq']
  exact pG hd
theorem proof :aFV.c1 := by
 intro k E _ _ _ t ht I
 exact ⟨dsG ht I,guV (ef6 ht I)⟩
end
end bzG
end
