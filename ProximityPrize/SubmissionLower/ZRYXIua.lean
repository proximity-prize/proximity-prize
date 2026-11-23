import ProximityPrize.SubmissionLower.Zg1hxlb
set_option Elab.async false
open _root_ renaming Algebra.smul_def → zd5, Fintype.linearCombination → z3d, Fintype.linearCombination_apply → zGl, Ideal → znc, Ideal.Quotient.mk → zVv, Ideal.Quotient.mkₐ → zvR, Ideal.homogeneous_span → zqZ, Ideal.mem_sup_right → zs0, Ideal.subset_span → zCn, LinearMap.ker → z83, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.constantCoeff → zuE, Polynomial.C → z1z, Set.mem_singleton → zT1
section
namespace qi87Bgb
noncomputable section
open MvPolynomial
open scoped Polynomial
open cu (L)
open P5 (K)
open qLXroAb (linear markJet evalXY)
open q9uVqha



attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev A:=z3y (Fin 4) L
private abbrev Coeff :=Fin 4→L
private theorem graph_homogeneous {R M:Type} [CommRing R] [Field M]
   (j:R →+* M) (v :Fin 4→M) {p:z3y (Fin 4) R} {n:ℕ}
   (hp:p.IsHomogeneous n) :
   zp j v p=z1z (p.eval₂ j v)*Polynomial.X ^n:= by
 classical
 have scale {T:Type} [CommRing T] (f :R →+* T) (u:Fin 4→T) (t:T) :
     p.eval₂ f (fun i=>u i*t)=p.eval₂ f u*t^n:= by
   simp only [eval₂_eq,Finset.sum_mul]
   apply Finset.sum_congr rfl
   intro d hd
   have he :d.degree=n:= by
     by_contra h
     exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
   simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
     ← Finsupp.degree_apply,he,mul_assoc]
 rw [zp,coe_eval₂Hom,scale]
 congr 1
 exact (hom_eval₂ p j (z1z:M →+* M[X]) v).symm
private theorem fibre_homogeneous {R M:Type} [CommRing R] [Field M]
    (j:R →+* M) (r :R →+* L) (v :Fin 4→M) :
    (TY j r v).IsHomogeneous (homogeneousSubmodule (Fin 4) L) := by
  classical
  let I:=RingHom.ker (zp j v)
  have hI:I.IsHomogeneous (homogeneousSubmodule (Fin 4) R) := by
    rw [Ideal.isHomogeneous_iff_forall_subset]
    intro n p hp
    have hproj:GradedRing.proj (homogeneousSubmodule (Fin 4) R) n p =
        homogeneousComponent n p:=decomposition.decompose'_apply p n
    change _∈I
    rw [hproj]
    have hc: (zp j v p).coeff n=(homogeneousComponent n p).eval₂ j v := by
      conv_lhs=>rw [← sum_homogeneousComponent (φ:=p)]
      simp only [map_sum,Polynomial.finsetSum_coeff,
        graph_homogeneous j v (homogeneousComponent_isHomogeneous _ _),
        Polynomial.coeff_C_mul_X_pow]
      by_cases hn:n∈Finset.range (p.totalDegree+1)
      · simp [hn]
      · have hdeg:p.totalDegree<n:= by simpa [Nat.lt_succ_iff] using hn
        simp [hn,homogeneousComponent_eq_zero n p hdeg]
    change zp j v (homogeneousComponent n p)=0
    rw [graph_homogeneous j v (homogeneousComponent_isHomogeneous _ _),
      ← hc,RingHom.mem_ker.mp hp]
    simp
  obtain ⟨s,hs⟩:=(Ideal.IsHomogeneous.iff_exists _ _).mp hI
  change (I.map (MvPolynomial.map r)).IsHomogeneous _
  rw [hs,Ideal.map_span,Set.image_image]
  apply zqZ
  rintro _ ⟨p,_,rfl⟩
  obtain ⟨n,hn⟩:SetLike.IsHomogeneousElem (homogeneousSubmodule (Fin 4) R)
      (p:z3y (Fin 4) R) :=p.property
  exact ⟨n,IsHomogeneous.map hn r⟩
private abbrev qform (P:znc A) :=
 z3d L (fun i:Fin 4=>zVv P (z9v i))
private theorem qform_apply (P:znc A) (a :Coeff) :
  qform P a=zVv P (P5 a) := by
 simp only [qform,zGl,P5,map_sum]
 apply Finset.sum_congr rfl
 intro i _
 change a i•(zvR L P) (z9v i) =
  (zvR L P) (MvPolynomial.C (a i)*z9v i)
 rw [← map_smul,zd5,MvPolynomial.algebraMap_eq]
private theorem proper_kernel {W:Type} [AddCommMonoid W] [Module L W]
  (v :Fin 4→W) {i:Fin 4} (hi:v i≠0) :
  z83 (z3d L v) ≠ ⊤ := by
 intro h
 have hm:Pi.single i (1 :L)∈z83 (z3d L v) := by
  rw [h]
  trivial
 exact hi (by simpa using LinearMap.mem_ker.mp hm)
private theorem choose_form {ι τ:Type} [Finite ι] [Finite τ]
    (I:ι→ znc A) (bad:τ→Submodule L Coeff) (hbad : ∀ t,bad t ≠ ⊤) :
    ∃ a :Coeff,(∀ t,a∉bad t) ∧
      ∀ i P,P∈(I i).minimalPrimes→(∃ j:Fin 4,z9v j∉P) →
        P5 a∉P:= by
  classical
  let exc (i:ι) :Set (znc A) :=
    {P | P∈(I i).minimalPrimes ∧ ∃ j:Fin 4,z9v j∉P}
  let (i:ι) :Finite (exc i) :=
    (((I i).finite_minimalPrimes_of_isNoetherianRing A).subset fun _ h=>h.1).to_subtype
  let B: (Σ i,exc i) ⊕ τ→Submodule L Coeff :=
    Sum.elim (fun s=>z83 (qform s.2.val)) bad
  have hb (t: (Σ i,exc i) ⊕ τ) :B t ≠ ⊤ := by
    cases t with
    | inl s =>
      obtain ⟨j,hj⟩:=s.2.property.2
      exact proper_kernel _ (fun h=>hj (Ideal.Quotient.eq_zero_iff_mem.mp h))
    | inr t=>exact hbad t
  have hcover : (⋃ t,(B t:Set Coeff))≠Set.univ := by
    intro h
    obtain ⟨t,ht⟩:=Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hb t ht
  obtain ⟨a,ha⟩:=Set.nonempty_compl.mpr hcover
  simp only [Set.mem_compl_iff,Set.mem_iUnion,not_exists] at ha
  refine ⟨a,fun t=>ha (Sum.inr t),fun i P hP hX hp => ?_⟩
  apply ha (Sum.inl ⟨i,⟨P,hP,hX⟩⟩)
  exact LinearMap.mem_ker.mpr (by rw [qform_apply,Ideal.Quotient.eq_zero_iff_mem]; exact hp)
private abbrev origin :znc A:=RingHom.ker zuE
private theorem prime_le_origin (P:znc A) [P.IsPrime]
  (hP:P.IsHomogeneous (homogeneousSubmodule (Fin 4) L)) :P≤origin := by
 intro p hp
 have h:=homogeneousComponent_mem_of_mem hP hp 0
 rw [homogeneousComponent_zero] at h
 exact RingHom.mem_ker.mpr (by
  change p.coeff 0=0
  by_contra hc
  exact P.notMem_of_isUnit ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C) h)
private theorem no_chain (I P Q R T:znc A) [P.IsPrime] [Q.IsPrime] [R.IsPrime] [T.IsPrime]
  (hd:ringKrullDim (A ⧸ I)≤2) (hI:I≤P)
  (hPQ:P<Q) (hQR:Q<R) (hRT:R<T) :False := by
 let e :=(Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm
 let p:=e ⟨⟨P,inferInstance⟩,hI⟩
 let q:=e ⟨⟨Q,inferInstance⟩,hI.trans hPQ.le⟩
 let r :=e ⟨⟨R,inferInstance⟩,hI.trans (hPQ.trans hQR).le⟩
 let t:=e ⟨⟨T,inferInstance⟩,hI.trans ((hPQ.trans hQR).trans hRT).le⟩
 let u:LTSeries (PrimeSpectrum (A ⧸ I)) :=⟨3,![p,q,r,t],by
  intro i
  fin_cases i
  · exact e.strictMono hPQ
  · exact e.strictMono hQR
  · exact e.strictMono hRT⟩
 have h: (3:WithBot ℕ∞)≤2 :=(Order.LTSeries.length_le_krullDim u).trans hd
 exact (by decide : ¬ (3:WithBot ℕ∞)≤2) h
private abbrev cut (I:znc A) (a :Coeff) :=I+Ideal.span {P5 a}
private theorem cut_homogeneous (I:znc A) (a :Coeff)
  (hI:I.IsHomogeneous (homogeneousSubmodule (Fin 4) L)) :
  (cut I a).IsHomogeneous (homogeneousSubmodule (Fin 4) L) := by
 apply hI.sup
 apply zqZ
 rintro _ (rfl :_=P5 a)
 exact ⟨1,(homogeneousSubmodule (Fin 4) L 1).sum_mem fun i _ =>
  isHomogeneous_C_mul_X (a i) i⟩
private theorem graph_cut (I:znc A) (a b:Coeff)
   (hI:I.IsHomogeneous (homogeneousSubmodule (Fin 4) L))
   (hd:ringKrullDim (A ⧸ I)≤2)
   (ha : ∀ P∈I.minimalPrimes,(∃ j:Fin 4,z9v j∉P)→P5 a∉P)
   (hb : ∀ P∈(cut I a).minimalPrimes,(∃ j:Fin 4,z9v j∉P)→P5 b∉P) :
   GraphCut I a b:= by
 intro i
 by_contra hi
 have hs : ({P5 a,P5 b} : Set A) = {P5 a} ∪ {P5 b} := by
   ext p
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_union]
 rw [Ideal.add_eq_sup,hs,Ideal.span_union,← sup_assoc] at hi
 have hJ:=cut_homogeneous _ b (cut_homogeneous I a hI)
 change z9v i∉(cut (cut I a) b).radical at hi
 rw [hJ.radical_eq,Ideal.mem_sInf] at hi
 push Not at hi
 obtain ⟨R,⟨hr,hJR,hR⟩,hiR⟩:=hi
 let:=hR
 obtain ⟨Q,hQ,hQR⟩:=(cut I a).exists_minimalPrimes_le
   ((le_sup_left:cut I a≤ cut (cut I a) b).trans hJR)
 let:=hQ.isPrime
 obtain ⟨P,hP,hPQ⟩:=I.exists_minimalPrimes_le ((le_sup_left:I≤ cut I a).trans hQ.le)
 let:=hP.isPrime
 have hX:z9v i∈origin :=RingHom.mem_ker.mpr (constantCoeff_X L i)
 have hPM:P<Q:=lt_of_le_of_ne hPQ fun e =>
   ha P hP ⟨i,fun h=>hiR (hQR (hPQ h))⟩
     (e ▸ hQ.le (zs0 (zCn (zT1 _))))
 have hQM:Q<R:=lt_of_le_of_ne hQR fun e =>
   hb Q hQ ⟨i,fun h=>hiR (hQR h)⟩
     (e ▸ hJR (zs0 (zCn (zT1 _))))
 let:origin.IsPrime :=RingHom.ker_isPrime zuE
 exact no_chain I P Q R origin hd hP.le hPM hQM
   (lt_of_le_of_ne (prime_le_origin R hr) fun e=>hiR (e.symm ▸ hX))
private def KT (S:K→K[X]) (γ:K) (x :L) :Coeff →ₗ[L] L :=
 z3d L (fun i=>(markJet S γ i).eval x)
private theorem jetForm_apply (S:K→K[X]) (γ:K) (x :L) (a :Coeff) :
  KT S γ x a=(linear (z1z:L →+* L[X]) a (markJet S γ)).eval x := by
 change _=Polynomial.evalRingHom x (linear (z1z:L →+* L[X]) a (markJet S γ))
 simp only [KT,linear,zGl,smul_eq_mul,map_sum,map_mul,
  Polynomial.coe_evalRingHom,Polynomial.eval_C]
private theorem jet_ker (S:K→K[X]) (γ:K) (x :L) :
  z83 (KT S γ x) ≠ ⊤ :=
 proper_kernel _ (i:=0) (by change (1 :L[X]).eval x≠0; simp)
theorem proof :q9uVqha.c4 := by
 classical
 intro q Cq z S F V G hd
 let:Algebra L G.M:=G.constants.toAlgebra
 let I (γ:V.marks) :=G.RS γ.val (V.Bp γ.property)
 let points :=Σ γ:V.marks,↑(insert (0:L) (V.den γ.val).roots.toFinset)
 let g:=z3d L G.point
 have hg (a :Coeff) :g a=G.form a := by
   simp only [g,zGl,zd5,linear]
   rfl
 let bad:Unit ⊕ points→Submodule L Coeff :=
   Sum.elim (fun _=>z83 g)
     (fun p=>z83 (KT S p.1.val p.2.val))
 have hbad (t:Unit ⊕ points) :bad t ≠ ⊤ := by
   cases t with
   | inl _=>exact proper_kernel _ (i:=0) G.polar_ne
   | inr p=>exact jet_ker S p.1.val p.2.val
 obtain ⟨a,habad,hcutA⟩:=choose_form I bad hbad
 have ha :G.form a≠0:= fun h=>habad (Sum.inl ()) (LinearMap.mem_ker.mpr ((hg a).trans h))
 have haj (γ:V.marks) (x :L) (hx :x∈insert (0:L) (V.den γ.val).roots.toFinset) :
     (linear (z1z:L →+* L[X]) a (markJet S γ.val)).eval x≠0:= fun h =>
   habad (Sum.inr ⟨γ,x,hx⟩) (LinearMap.mem_ker.mpr ((jetForm_apply S γ.val x a).trans h))
 have hsep : ∃ j:Fin 4,G.deriv (G.point j/G.form a)≠0:= by
   by_contra! h
   have he :G.point 1/G.form a=G.x*(G.point 0/G.form a) := by
     change (G.x*evalXY F.f.derivative G.x G.y)/G.form a= _
     exact mul_div_assoc _ _ _
   have hz :=h 1
   rw [he,G.deriv.leibniz,h 0,G.deriv_x,smul_zero,zero_add,smul_eq_mul,mul_one] at hz
   exact (div_ne_zero G.polar_ne ha) hz
 let d:=z3d L (fun i=>G.deriv (G.point i/G.form a))
 have hmul (c:L) (w:G.M) :
     G.deriv (G.constants c*w)=G.constants c*G.deriv w:= by
   change G.deriv (algebraMap Cq.E G.M (algebraMap L Cq.E c)*w) =
     algebraMap Cq.E G.M (algebraMap L Cq.E c)*G.deriv w
   rw [← zd5,G.deriv.map_smul,zd5]
 have hdb (b:Coeff) :d b=G.deriv (G.form b/G.form a) := by
   rw [← hg b]
   simp only [d,g,zGl,zd5]
   change (∑ i,G.constants (b i)*G.deriv (G.point i/G.form a)) =
     G.deriv ((∑ i,G.constants (b i)*G.point i)/G.form a)
   simp only [div_eq_mul_inv,Finset.sum_mul,mul_assoc,map_sum,hmul]
 obtain ⟨j,hj⟩:=hsep
 obtain ⟨b,hbbad,hcutB⟩:=choose_form (fun γ=>cut (I γ) a)
   (fun _:Unit=>z83 d) (fun _=>proper_kernel _ hj)
 refine ⟨a,b,ha,fun h=>hbbad () (LinearMap.mem_ker.mpr ((hdb b).trans h)),
   fun γ hγ=>⟨?_,?_,?_⟩⟩
 · exact graph_cut (I ⟨γ,hγ⟩) a b (fibre_homogeneous _ _ _) (hd γ hγ)
     (hcutA ⟨γ,hγ⟩) (hcutB ⟨γ,hγ⟩)
 · intro h
   exact haj ⟨γ,hγ⟩ 0 (Finset.mem_insert_self _ _) (by rw [h,Polynomial.eval_zero])
 · intro x hx
   exact haj ⟨γ,hγ⟩ x (Finset.mem_insert_of_mem
     (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (V.den_ne γ hγ)).mpr hx)))
end
end qi87Bgb
end
section
set_option autoImplicit true
namespace qMDQ8Za
theorem proof :qJh2f6d.c4 :=
 qi87Bgb.proof
end qMDQ8Za
end
