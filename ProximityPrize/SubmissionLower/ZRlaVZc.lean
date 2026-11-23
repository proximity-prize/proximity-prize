import ProximityPrize.SubmissionLower.ZQtCuFa
import ProximityPrize.SubmissionLower.ZFZJbJc
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.ZsDvnmd
import ProximityPrize.SubmissionLower.ZqZuDUb
import ProximityPrize.SubmissionLower.ZeLOjNb
set_option Elab.async false
section
open _root_ renaming DFunLike.congr_fun→lJ,Fin.sum_univ_three→ ox,Finsupp.add_apply→ oz,Finsupp.degree_eq_sum→nI,Function.Injective→cy,KoalaBear.is_prime→ ov,LinearMap.ker→mD,LinearMap.mem_ker→ oD,Module.finrank_pi→nX,Module.finrank_prod→ oy,MvPolynomial.X→nq,Nat.add_comm→ oj,Nat.card_eq_fintype_card→n5,P5_8_1.contactChange→lI,P5_8_1.sourceOrders→lV,Prod.fst→lz,Prod.snd→c9,Subtype.ext→ oq,congrArg→aU
section
set_option autoImplicit true
namespace q1EkR5c
open i4 (Jet)
open P5_8_1 MvPolynomial
open scoped BigOperators Pointwise
noncomputable section
local instance :Fact (Nat.Prime i4.p) :=⟨ov⟩
private abbrev Block (q u:ℕ) :=flagSpace (iO q) (blockFlags q u)
private def jetExp (s :Jet) :Exp:=exponent s.a s.b s.c
private def Ac (q u:ℕ) (s :qB q u) :Exp:=jetExp (bYa q u s)
private def restore (q:ℕ) (p:lK) :lK:=nq 0^(q-iO q)*p
private theorem colExp_injective (q u:ℕ) :cy (Ac q u) := by
 intro s t h
 obtain ⟨⟨b,hb⟩,⟨i,hi⟩⟩:=s
 obtain ⟨⟨b',hb'⟩,⟨i',hi'⟩⟩:=t
 have h1 :=lJ h 1
 have h2 :=lJ h 2
 simp only [Ac,jetExp,bYa,bny,Jet.b,Jet.c,bpQ,d5n] at h1 h2
 subst b'
 have :i=i' := by omega
 subst i'
 rfl
private theorem source_col {q u:ℕ} (p:Block q u) (hq:q<84) {e :Exp}
  (he :e∈(restore q p).support) : ∃ s :qB q u,Ac q u s=e := by
 classical
 rw [restore,X_pow_eq_monomial] at he
 obtain ⟨a,ha,z,hz,rfl⟩:=Finset.mem_add.mp (support_mul _ _ he)
 have ha' := Finset.mem_singleton.mp (support_monomial_subset ha)
 subst a
 have hp:=((mem_restrictSupport_iff F).mp (Submodule.mem_inf.mp p.property).1) hz
 change z.degree=iO q∧lV (blockFlags q u) z at hp
 have hd:z 0+z 1+z 2=iO q:= by
  simpa [nI,ox] using hp.1
 have hf :=hp.2
 change 0≤z 1+z 2∧25-u≤z 1+2*z 2 ∧
  iO q-11≤z 0+z 1∧2*iO q-25≤2*z 0+z 1 at hf
 have hq' := min_le_left q (25-(q-76)/2)
 have hd' := min_le_right q (25-(q-76)/2)
 change iO q≤q at hq'
 change iO q≤25-(q-76)/2 at hd'
 have hcut: (q-76)/2≤3:= by omega
 have hb:z 1< min q 25+1 := by omega
 have hlo:ayp u (z 1)≤z 2 := by unfold ayp; omega
 have hhi:z 2<bnz q (z 1) := by unfold bnz; omega
 let s :qB q u:=⟨⟨z 1,hb⟩,⟨z 2-ayp u (z 1),by
  change z 2-ayp u (z 1)<bC1 q u (z 1)
  unfold bC1
  omega⟩⟩
 refine ⟨s,?_⟩
 have hc:ayp u (z 1)+(z 2-ayp u (z 1))=z 2 := by omega
 change exponent (q-(z 1+(ayp u (z 1)+(z 2-ayp u (z 1))))) (z 1)
  (ayp u (z 1)+(z 2-ayp u (z 1)))=Finsupp.single 0 (q-iO q)+z
 rw [hc]
 ext i
 fin_cases i <;> simp [oz]
 omega
private def coords (q u:ℕ) :Block q u →ₗ[F] (qB q u→F) where
 toFun p s :=(restore q p).coeff (Ac q u s)
 map_add' := by intro p t; funext s; simp [restore,mul_add]
 map_smul' := by intro v p; funext s; simp [restore,Algebra.mul_smul_comm]
private theorem rebuild {q u:ℕ} (p:Block q u) (hq:q<84) :
   restore q p = ∑ s :qB q u,monomial (Ac q u s) (coords q u p s) := by
 classical
 ext e
 rw [coeff_sum]
 simp only [coeff_monomial]
 by_cases he : ∃ s :qB q u,Ac q u s=e
 · obtain ⟨s,rfl⟩:=he
   rw [Finset.sum_eq_single_of_mem s (Finset.mem_univ _),ite_eq_left rfl]
   · rfl
   · intro t _ hne
     exact ite_eq_right (fun h=>hne (colExp_injective q u h))
 · rw [notMem_support_iff.mp (fun h=>he (source_col p hq h))]
   symm
   exact Finset.sum_eq_zero (fun s _=>ite_eq_right (fun h=>he ⟨s,h⟩))
private theorem coords_injective {q u:ℕ} (hq:q<84) :cy (coords q u) := by
 intro p t h
 have he :restore q p=restore q t:= by rw [rebuild p hq,rebuild t hq,h]
 exact oq (mul_left_cancel₀ (pow_ne_zero _ (X_ne_zero 0)) he)
private theorem bvo (q u:ℕ) (r :af q u) :
  2*(rowJet q u r).a+(rowJet q u r).c<86-q-u:= by
 rcases r with ⟨⟨h,hh⟩,⟨i,hi⟩⟩
 let b:=aAa q u h+i
 have hlo:aAa q u h≤b:= by dsimp [b]; omega
 have hhi:b<bvg q u h:= by change i<bvg q u h-aAa q u h at hi; dsimp [b]; omega
 unfold aAa at hlo
 unfold bvg at hhi
 change 2*h+(q-(h+b))<86-q-u
 omega
private theorem target_zero {q u:ℕ} (p:Block q u) (r :af q u) :
  (lI (restore q p)).coeff (jetExp (rowJet q u r))=0:= by
 apply notMem_support_iff.mp
 intro h
 rw [restore,map_mul] at h
 obtain ⟨a,_,z,hz,he⟩:=Finset.mem_add.mp (support_mul _ _ h)
 have hp:=((mem_restrictSupport_iff F).mp (Submodule.mem_comap.mp (Submodule.mem_inf.mp p.property).2)) hz
 change 0≤z 0+z 2∧86-q-u≤2*z 0+z 2 at hp
 have he0:=lJ he 0
 have he2 :=lJ he 2
 simp only [oz ,jetExp,exponent_zero,d5n] at he0 he2
 have hw:=bvo q u r
 omega
private theorem kernel_mem {q u:ℕ} (p:Block q u) (hq:q<84) :
   coords q u p∈mD (Bs q u).mulVecLin:= by
 rw [oD]
 funext r
 have he : (lI (restore q p)).coeff (jetExp (rowJet q u r)) =
     ∑ s :qB q u,Bs q u r s*coords q u p s := by
   rw [rebuild p hq,map_sum,coeff_sum]
   exact Finset.sum_congr rfl fun s _=>contact_coeff _ _ _
 change (∑ s :qB q u,Bs q u r s*coords q u p s)=0
 exact he.symm.trans (target_zero p r)
theorem proof :P5_8_1.c1 := by
 intro q u hq _
 let M:=(Bs q u).mulVecLin
 let f :=(coords q u).codRestrict (mD M) (fun p=>kernel_mem p hq)
 have hf :cy f := fun p t h=>coords_injective hq (aU Subtype.val h)
 have h:=LinearMap.finrank_le_finrank_of_injective hf
 rw [← cEe q u,← Module.finrank_fintype_fun_eq_card F,
  ← LinearMap.finrank_range_add_finrank_ker M]
 exact Nat.add_le_add_left h _
end
end q1EkR5c
end
section
namespace qokZnNd
open P5_8_1 MvPolynomial
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime i4.p) :=⟨ov⟩
private abbrev Exponent:=Fin 3 →₀ ℕ
private abbrev asU (d:ℕ) := ↥({e :Exponent | e.degree=d} : Set Exponent)
private abbrev Triangle (n:ℕ) :=(s :Fin n)×Fin (s.val+1)
private theorem degree_three (e :Exponent) :e.degree=e 0+e 1+e 2 := by
 rw [nI,ox ,add_assoc]
private theorem exponents_ext {d:ℕ} {e e' : asU d} {i j:Fin 3} (hij:i≠j)
   (hi:e.val i=e'.val i) (hj:e.val j=e'.val j) :e=e' := by
 apply oq
 apply Finsupp.ext
 intro k
 by_cases hki:k=i
 · simpa only [hki] using hi
 by_cases hkj:k=j
 · simpa only [hkj] using hj
 have hin:i∉({j,k} : Finset (Fin 3)) := by simp [hij,Ne.symm hki]
 have hall: ({i,j,k} : Finset (Fin 3))=Finset.univ := by
   apply Finset.eq_univ_of_card
   rw [Finset.card_insert_of_notMem hin,Finset.card_pair_eq_two_iff.mpr (Ne.symm hkj),
     Fintype.card_fin]
 have total (p:asU d) :p.val i+(p.val j+p.val k)=d:= by
   have h:p.val.degree=d:=p.property
   rw [nI,← hall,Finset.sum_insert hin,Finset.sum_pair (Ne.symm hkj)] at h
   exact h
 have he :=total e
 have he' := total e'
 omega
private def trianglePair {n:ℕ} (t:Triangle n) :ℕ×ℕ :=
 (t.1.val,t.2.val)
private theorem trianglePair_injective (n:ℕ) :cy (@trianglePair n) := by
 rintro ⟨s,t⟩ ⟨s',t'⟩ h
 have hs :s=s' := Fin.ext (aU lz h)
 subst s'
 have ht:t=t' := Fin.ext (aU c9 h)
 subst t'
 rfl
private theorem dFB (n:ℕ) :Nat.card (Triangle n)=triangle n:= by
 rw [Nat.card_sigma]
 simp only [Nat.card_fin]
 rw [Fin.sum_univ_eq_sum_range (fun s=>s+1)]
 have h:=Finset.sum_range_id (n+1)
 rw [Finset.sum_range_succ' (fun x :ℕ=>x) n] at h
 simpa [triangle,Nat.mul_comm] using h
private def exponentsTriangle (d:ℕ) :asU d ≃ Triangle (d+1) := by
 let pack (e :asU d) :Triangle (d+1) := by
   have h:e.val.degree=d:=e.property
   rw [degree_three] at h
   exact ⟨⟨e.val 1+e.val 2,by omega⟩,⟨e.val 2,by change e.val 2<e.val 1+e.val 2+1; omega⟩⟩
 refine Equiv.ofBijective pack ⟨?_,?_⟩
 · intro e e' h
   have hs :=aU lz (aU trianglePair h)
   have ht:=aU c9 (aU trianglePair h)
   change e.val 1+e.val 2=e'.val 1+e'.val 2 at hs
   change e.val 2=e'.val 2 at ht
   exact exponents_ext (i:=1) (j:=2) (by decide) (by omega) ht
 · rintro ⟨s,t⟩
   have hs :=s.isLt
   have ht:=t.isLt
   let e :Exponent:=Finsupp.equivFunOnFinite.symm ![d - s.val,s.val - t.val,t.val]
   have he :e.degree=d:= by
     rw [degree_three]
     change (d - s.val)+(s.val - t.val)+t.val=d
     omega
   refine ⟨⟨e,he⟩,trianglePair_injective _ ?_⟩
   change (s.val - t.val+t.val,t.val)=(s.val,t.val)
   congr 1
   omega
private abbrev Bad (d:ℕ) (i j:Fin 3) (a :Orders) :=
 {e :asU d // ¬ (a.1≤e.val i+e.val j∧a.2≤e.val i+2*e.val j)}
private theorem card_bad (d:ℕ) {i j:Fin 3} (hij:i≠j) (a :Orders) :
    Nat.card (Bad d i j a)≤ cost a := by
  let b:=max a.1 ((a.2+1)/2)
  have hb:a.1≤b:=le_max_left _ _
  let s (e :Bad d i j a) :=e.val.val i+e.val.val j
  let y (e :Bad d i j a) :=e.val.val j
  have upper (e :Bad d i j a) (he : ¬s e<b) :s e+y e<a.2 := by
    have hs :a.1≤ s e :=hb.trans (Nat.le_of_not_gt he)
    have h:=e.property
    change ¬(a.1≤ s e∧a.2≤e.val.val i+2*y e) at h
    dsimp [s,y] at h hs ⊢
    omega
  let pack (e :Bad d i j a) :Triangle b ⊕ Triangle (a.2 - b) :=
    if h:s e<b then
      .inl ⟨⟨s e,h⟩,⟨y e,by change y e<s e+1; dsimp [s,y]; omega⟩⟩
    else
      have h' := upper e h
      .inr ⟨⟨a.2 - 1 - s e,by omega⟩,⟨y e,by change y e<a.2 - 1 - s e+1; omega⟩⟩
  have hpack :cy pack := by
    intro e e' h
    have hcoords :s e=s e' ∧ y e=y e' := by
      by_cases he :s e<b <;> by_cases he' : s e' < b
      · simp only [pack,dite_eq_left he,dite_eq_left he',Sum.inl.injEq] at h
        exact ⟨aU lz (aU trianglePair h),
          aU c9 (aU trianglePair h)⟩
      · simp [pack,he,he'] at h
      · simp [pack,he,he'] at h
      · simp only [pack,dite_eq_right he,dite_eq_right he',Sum.inr.injEq] at h
        have hs :a.2 - 1 - s e=a.2 - 1 - s e' := aU lz (aU trianglePair h)
        have hy :y e=y e' := aU c9 (aU trianglePair h)
        have hu:=upper e he
        have hu' := upper e' he'
        exact ⟨by omega,hy⟩
    obtain ⟨hs,hy⟩:=hcoords
    dsimp [s,y] at hs hy
    exact oq (exponents_ext hij (by omega) hy)
  have h:=Nat.card_le_card_of_injective pack hpack
  rw [Nat.card_sum,dFB,dFB] at h
  exact h
private abbrev Forms (d:ℕ) :Submodule F lK :=
 restrictSupport F {e | e.degree=d}
private instance exponentsFinite (d:ℕ) :Finite (asU d) :=
 Finite.of_injective _ (exponentsTriangle d).injective
private instance badFintype (d:ℕ) (i j:Fin 3) (a :Orders) :Fintype (Bad d i j a) :=
 Fintype.ofFinite _
private instance formsFinite (d:ℕ) :Module.Finite F (Forms d) := by
 let:Finite (asU d) :=exponentsFinite d
 exact Module.Finite.of_basis (basisRestrictSupport F {e | e.degree=d})
private theorem forms_rank (d:ℕ) :Module.finrank F (Forms d)=triangle (d+1) := by
 rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport F {e | e.degree=d})]
 exact (Nat.card_congr (exponentsTriangle d)).trans (dFB _)
private def badCoeffs (d:ℕ) (i j:Fin 3) (a :Orders) :
  lK →ₗ[F] (Bad d i j a→F) :=
 LinearMap.pi fun e=>lcoeff F e.val.val
private theorem coeffs_zero_iff (d:ℕ) (i j:Fin 3) (a :Orders) {P:lK}
   (hP:P∈Forms d) :badCoeffs d i j a P=0 ↔
     ∀ e∈P.support,a.1≤e i+e j∧a.2≤e i+2*e j:= by
 have hdeg : ∀ e∈P.support,e.degree=d:=hP
 constructor
 · intro hz e he
   by_contra hf
   exact (mem_support_iff.mp he) (congrFun hz ⟨⟨e,hdeg e he⟩,hf⟩)
 · intro h
   funext e
   change P.coeff e.val.val=0
   by_contra hn
   exact e.property (h _ (mem_support_iff.mpr hn))
private theorem contact_mem {d:ℕ} {P:lK} (hP:P∈Forms d) :
  lI P∈Forms d:= by
 have heq :homogeneousSubmodule (Fin 3) F d=Forms d :=
  homogeneousSubmodule_eq_finsupp_supported _ _ _
 rw [← heq] at hP ⊢
 have hx (i:Fin 3) : (nq i:lK).IsHomogeneous 1 :=isHomogeneous_X _ _
 have h:P.IsHomogeneous d:=hP
 let x :=(nq:Fin 3→lK)
 let g:Fin 3→lK := ![x 0 + x 1 - x 2,x 1,x 2]
 have hg (i:Fin 3) : (g i).IsHomogeneous 1 := by
  fin_cases i
  · exact ((hx 0).add (hx 1)).sub (hx 2)
  · exact hx 1
  · exact hx 2
 change (aeval g P).IsHomogeneous d
 simpa only [one_mul] using h.aeval g hg
theorem proof :P5_8_1.c2 := by
  intro d f
  let u:=badCoeffs d 1 2 f.1
  let v :=badCoeffs d 1 0 f.2.1
  let w:=(badCoeffs d 2 0 f.2.2).comp contactChange.toLinearMap
  let L:=(u.prod (v.prod w)).domRestrict (Forms d)
  have hle :flagSpace d f≤Forms d:= by
    intro P h
    change (∀ e∈P.support,e.degree=d∧lV f e)∧_ at h
    exact fun e he=>(h.1 e he).1
  have hker :mD L=(flagSpace d f).comap (Forms d).subtype := by
    ext P
    rw [oD]
    have hc:=contact_mem P.property
    change (u P.val,v P.val,w P.val)=(0,0,0)↔P.val∈flagSpace d f
    simp only [Prod.mk.injEq,u,v,w,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
      coeffs_zero_iff d 1 2 _ P.property,coeffs_zero_iff d 1 0 _ P.property,
      coeffs_zero_iff d 2 0 _ hc]
    change _ ↔
      (∀ e∈P.val.support,e.degree=d∧lV f e) ∧
      ∀ e∈(lI P.val).support,targetOrders f e
    have hd : ∀ e∈P.val.support,e.degree=d:=P.property
    simp only [lV,targetOrders]
    constructor
    · rintro ⟨h₁,h₂,h₃⟩
      refine ⟨?_,fun e he=> by simpa [oj] using h₃ e he⟩
      intro e he
      obtain ⟨hp,hp'⟩:=h₁ e he
      obtain ⟨hq,hq'⟩:=h₂ e he
      exact ⟨hd e he,hp,hp',by simpa [Nat.add_comm] using hq,
        by simpa [oj ] using hq'⟩
    · rintro ⟨hs,ht⟩
      exact ⟨fun e he=>⟨(hs e he).2.1,(hs e he).2.2.1⟩,
        fun e he=> by simpa [oj] using (hs e he).2.2.2,
        fun e he=> by simpa [oj] using ht e he⟩
  have hdim:=L.finrank_range_add_finrank_ker
  rw [hker,(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,forms_rank] at hdim
  have hrange :=(LinearMap.range L).finrank_le
  rw [oy ,oy ,nX ,nX ,
    nX ,← n5 ,← n5 ,
    ← n5] at hrange
  have h₁:=card_bad d (i:=1) (j:=2) (by decide) f.1
  have h₂:=card_bad d (i:=1) (j:=0) (by decide) f.2.1
  have h₃:=card_bad d (i:=2) (j:=0) (by decide) f.2.2
  unfold rawLower
  omega
end
end qokZnNd
end
end
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open K1 aR jA aFP
open scoped Polynomial BigOperators
open private ct0 bxX index_prod bpE from ProximityPrize.SubmissionLower.CS
open private bJx from ProximityPrize.SubmissionLower.E2
private theorem b9h {a :mA →₀ ℕ} (ha :a≠0) :0<Dl a := by
  by_contra! h
  change 7062*a none+48758*a.some.degree≤0 at h
  have hn:a none=0:= by omega
  have hd:a.some.degree=0:= by omega
  have hs :=(Finsupp.degree_eq_zero_iff _).mp hd
  apply ha
  ext i
  cases i with
  | none=>simpa using hn
  | some i=>simpa using DFunLike.congr_fun hs i
private theorem cau (A B:ko) (d:ℕ) (hA:A.coeff 0≠0)
    (hAB : ∀ a,Dl a<d→(A*B).coeff a=0) :
    ∀ a,Dl a<d→B.coeff a=0:= by
  classical
  suffices h : ∀ n a,Dl a=n→n<d→B.coeff a=0 by
    exact fun a ha=>h _ a rfl ha
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a ha hd
    have hab:=hAB a (ha.symm ▸ hd)
    rw [MvPolynomial.coeff_mul,Finset.sum_eq_single_of_mem (0,a) (by simp)] at hab
    · exact (mul_eq_zero.mp hab).resolve_left hA
    · intro b hb hbne
      have hs :=Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hb₁:b.1≠0:= by
        intro hz
        apply hbne
        exact Prod.ext hz (by simpa [hz] using hs)
      have hw:=aOR b.1 b.2
      rw [hs,ha] at hw
      have hpos :=b9h hb₁
      rw [ih (Dl b.2) (by omega) b.2 rfl (by omega),mul_zero]
private theorem bsG (A B:ko) (z :iP) (y :Fin 3→iP) (d:ℕ)
    (hA:MvPolynomial.eval (ED z y) A≠0) (h:NT (A*B) z y d) :
    NT B z y d:= by
  intro a ha
  by_contra! hlt
  refine (MvPolynomial.mem_support_iff.mp ha) (cau
    (translate (ED z y) A) (translate (ED z y) B) d ?_ ?_ a hlt)
  · rwa [ct0]
  · intro b hb
    rw [← map_mul]
    by_contra hne
    exact (Nat.not_lt_of_ge (h b (MvPolynomial.mem_support_iff.mpr hne))) hb
theorem b1p (Γ:Finset K) (z :K→ao) (S:K→ao[X])
    (hzinj:Function.Injective z) {F G:ko} (D:awY F G)
    (hOrders : ∀ γ∈Γ,aqw F G (DI (z γ)) (jW (S γ))) :
      ∃ (book :Finset K) (Q:Lower),book.card≤80000∧Q≠0 ∧
        Q.totalDegree≤P6_6.aHc∧H9 Q≤P6_6.aM1 ∧
        ∀ γ∈Γ,γ∉book→MvPolynomial.eval (jW (S γ)) Q=0 ∨
          aqw D.left D.right (DI (z γ)) (jW (S γ)) := by
  classical
  have fix_ne (f :ko) (hf :f∈D.fixed) :f≠0 :=
    (D.fixed_kind f hf).1.ne_zero
  have mov_ne (f :ko) (hf :f∈D.moving) :f≠0 :=
    (D.moving_kind f hf).1.ne_zero
  have mov_total: (∑ f∈D.moving,vC f)≤17:= by
    simpa only [vC,MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_total
  have mov_index : (∑ f∈D.moving,lP f)≤5:= by
    simpa only [lP,MvPolynomial.weightedTotalDegree_prod _ _ _ mov_ne]
      using D.moving_index
  have mov_seed : (∑ f∈D.moving,gY f)≤103:= by
    simpa only [gY,MvPolynomial.degreeOf_prod_eq _ _ mov_ne] using D.moving_seed
  have acI (f :ko) (hf :f∈D.moving) :gY f≤103 :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) hf).trans mov_seed
  choose! q qn qt qi qe using
    (fun f hf=>cSA f (fix_ne f hf) (D.fixed_kind f hf).2.2)
  have exists_moving (f :ko) (hf :f∈D.moving) :=
    bJx f (D.moving_kind f hf).1 (D.moving_kind f hf).2.1
      ((Finset.single_le_sum (fun _ _=>Nat.zero_le _) hf).trans mov_total)
      (D.moving_kind f hf).2.2.1 (D.moving_kind f hf).2.2.2
  choose! r rn rt ri re using exists_moving
  let P:Lower := ∏ f∈D.fixed,q f
  let R:Lower := ∏ f∈D.moving,r f
  have Pn:P≠0:=Finset.prod_ne_zero_iff.mpr qn
  have Rn:R≠0:=Finset.prod_ne_zero_iff.mpr rn
  have Pt:P.totalDegree≤121 := by
    change (∏ f∈D.fixed,q f).totalDegree≤121
    rw [bxX _ _ qn]
    calc
      _ = ∑ f∈D.fixed,vC f :=Finset.sum_congr rfl qt
      _≤_:= by
        simpa only [vC,MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_total
  have Pi:H9 P≤41 := by
    change H9 (∏ f∈D.fixed,q f)≤41
    rw [index_prod _ _ qn]
    calc
      _ = ∑ f∈D.fixed,lP f :=Finset.sum_congr rfl qi
      _≤_:= by
        simpa only [lP,MvPolynomial.weightedTotalDegree_prod _ _ _ fix_ne]
          using D.fixed_index
  have Rt:R.totalDegree≤2*103*17:= by
    change (∏ f∈D.moving,r f).totalDegree≤2*103*17
    rw [bxX _ _ rn]
    calc
      _ ≤ ∑ f∈D.moving,(2*103)*vC f :=
        Finset.sum_le_sum fun f hf=>(rt f hf).trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (acI f hf)))
      _≤_:= by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ mov_total
  have Ri:H9 R≤(2*5+1)*103:= by
    change H9 (∏ f∈D.moving,r f)≤(2*5+1)*103
    rw [index_prod _ _ rn]
    calc
      _ ≤ ∑ f∈D.moving,((2*103)*lP f+gY f) := by
        apply Finset.sum_le_sum
        intro f hf
        refine (ri f hf).trans ?_
        rw [Nat.add_mul,one_mul,Nat.mul_right_comm 2]
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (acI f hf))) _
      _≤_:= by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        have hh:=Nat.mul_le_mul_left (2*103) mov_index
        omega
  let book :=a8n Γ z D.pure
  have hbook :book.card≤80000 :=
    (cIv Γ z hzinj D.pure D.pure_ne).trans D.pure_degree
  refine ⟨book,P*R,hbook,mul_ne_zero Pn Rn,?_,?_,?_⟩
  · simp only [← MvPolynomial.weightedTotalDegree_one] at Pt Rt ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pt Rt).trans (show 121+2*103*17≤P6_6.aHc by decide)
  · simp only [aOE] at Pi Ri ⊢
    rw [MvPolynomial.weightedTotalDegree_mul _ _ _ Pn Rn]
    exact (Nat.add_le_add Pi Ri).trans (show 41+(2*5+1)*103≤P6_6.aM1 by decide)
  · intro γ hγ hnot
    let a :=DI (z γ)
    let y :=jW (S γ)
    change MvPolynomial.eval y (P*R)=0∨aqw D.left D.right a y
    by_cases hn:MvPolynomial.eval y (P*R)=0
    · exact Or.inl hn
    rw [map_mul] at hn
    have hfixed (f :ko) (hf :f∈D.fixed) :
        MvPolynomial.eval (ED a y) f≠0:= by
      rw [qe f hf]
      exact bpE (left_ne_zero_of_mul hn) hf
    have hmoving (f :ko) (hf :f∈D.moving) :
        MvPolynomial.eval (ED a y) f≠0:= by
      intro h0
      exact (bpE (right_ne_zero_of_mul hn) hf) (re f hf _ _ h0)
    have hp:D.pure.eval a≠0:= fun he=>hnot (b81.mpr ⟨hγ,he⟩)
    let A:=YB D.pure*(∏ f∈D.fixed,f^D.exponent f) *
      (∏ f∈D.moving,f^D.exponent f)
    have hA:MvPolynomial.eval (ED a y) A≠0:= by
      simp only [A,map_mul,map_prod,map_pow,c5T]
      exact mul_ne_zero (mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr
        fun f hf=>pow_ne_zero _ (hfixed f hf))) (Finset.prod_ne_zero_iff.mpr
        fun f hf=>pow_ne_zero _ (hmoving f hf))
    refine Or.inr ⟨bsG A D.left a y _ hA ?_,
      bsG A D.right a y _ hA ?_⟩
    · simpa only [A,← D.azo] using (hOrders γ hγ).1
    · simpa only [A,← D.az7] using (hOrders γ hγ).2
end
end P6_6_4
end
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open aR jA Polynomial
open scoped Polynomial
open bjx (bbK)
open private UA aHD asy bYO bpL bnY aL9 from ProximityPrize.SubmissionLower.A2
open private aNa boN from ProximityPrize.SubmissionLower.A2
set_option maxRecDepth 4000
private theorem bto (F:ko) (hF:F≠0)
    (hcap:gY F≤40000) (a :ao) :
    (qN (pad F (((Polynomial.X:ao[X]) - C a) ^
      (40000-(qN F).natDegree)))).natDegree=40000:= by
  have hcap' : (qN F).natDegree≤40000:= by
    simpa only [qN,MvPolynomial.natDegree_optionEquivLeft,gY] using hcap
  rw [bbK,Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    natDegree_mul (aL9 hF) (pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_pow,natDegree_X_sub_C,mul_one,Nat.add_sub_of_le hcap']
theorem cbb {F G:ko} (hF:F≠0) (hG:G≠0)
    (hfg:IsRelPrime F G) (hf :gY F≤40000) (hg:gY G≤40000) :
    ∃ a b:ao[X],(qN (pad F a)).natDegree=40000 ∧
      (qN (pad G b)).natDegree=40000∧YI (pad F a) (pad G b)≠0:= by
  classical
  let f :=(qN F).map UA
  let g:=(qN G).map UA
  have hf0:f≠0:=(Polynomial.map_ne_zero_iff asy).mpr (aL9 hF)
  have hg0:g≠0:=(Polynomial.map_ne_zero_iff asy).mpr (aL9 hG)
  have hcop:IsCoprime f g:= by
    apply bYO (aL9 hF)
    intro d hdf hdg
    let e :=MvPolynomial.optionEquivLeft iP (Fin 3)
    have hu:IsUnit (e.symm d) :=
      hfg (by simpa [e,qN] using map_dvd e.symm.toRingHom hdf)
        (by simpa [e,qN] using map_dvd e.symm.toRingHom hdg)
    have he :=hu.map e.toRingHom
    change IsUnit (e (e.symm d)) at he
    rwa [e.apply_symm_apply] at he
  obtain ⟨a,ha,_⟩:=bpL g hg0 ∅
  obtain ⟨b,hb,hba⟩:=bpL f hf0 {UA (aHD a)}
  let p:=((Polynomial.X:ao[X]) - C a)^(40000-(qN F).natDegree)
  let q:=((Polynomial.X:ao[X]) - C b)^(40000-(qN G).natDegree)
  have hp: (qN (pad F p)).natDegree=40000:=bto F hF hf a
  have hq: (qN (pad G q)).natDegree=40000:=bto G hG hg b
  refine ⟨p,q,hp,hq,?_⟩
  have hab:UA (aHD a)≠UA (aHD b) := by
    simpa using (Finset.notMem_singleton.mp hba).symm
  have hpad:IsCoprime ((qN (pad F p)).map UA)
      ((qN (pad G q)).map UA) := by
    simp only [bbK,Polynomial.map_mul,p,q,Polynomial.map_pow,Polynomial.map_sub,
      Polynomial.map_X,Polynomial.map_C]
    exact (hcop.mul_right (bnY f hb).symm.pow_right).mul_left
      ((bnY g ha).pow_left.mul_right
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).pow)
  have hn:=resultant_ne_zero _ _ hpad
  rw [natDegree_map_eq_of_injective asy,
    natDegree_map_eq_of_injective asy,hp,hq,resultant_map_map] at hn
  intro hz
  exact hn ((congrArg UA hz).trans (map_zero _))
theorem eJp {F G:ko} (hF:F≠0) (hG:G≠0)
    (hfg:IsRelPrime F G)
    (hf :vC F≤6789∧lP F≤2300∧gY F≤40000)
    (hg:vC G≤6820∧lP G≤2300∧gY G≤40000) :
    ∃ a b:ao[X],(qN (pad F a)).natDegree=40000 ∧
      (qN (pad G b)).natDegree=40000 ∧
      YI (pad F a) (pad G b)≠0 ∧
      (YI (pad F a) (pad G b)).totalDegree≤P6_6.aPr ∧
      H9 (YI (pad F a) (pad G b))≤P6_6.aWz := by
  obtain ⟨a,b,ha,hb,hn⟩:=cbb hF hG hfg hf.2.2 hg.2.2
  refine ⟨a,b,ha,hb,hn,?_,?_⟩
  · have h:=boN (1 :Fin 3→ℕ) (qN (pad F a)) (qN (pad G b))
      40000 40000 6789 6820 (fun i=>(aNa _ F a i).trans hf.1)
      (fun i=>(aNa _ G b i).trans hg.1)
    have hn:40000*6789+40000*6820=(P6_6.aPr :ℕ) := by decide
    simpa only [MvPolynomial.weightedTotalDegree_one,YI,hn] using h
  · have h:=boN Fin.val (qN (pad F a)) (qN (pad G b))
      40000 40000 2300 2300 (fun i=>(aNa _ F a i).trans hf.2.1)
      (fun i=>(aNa _ G b i).trans hg.2.1)
    have hn:40000*2300+40000*2300=(P6_6.aWz :ℕ) := by decide
    simpa only [MvPolynomial.weightedTotalDegree,Finsupp.weight_apply,Nat.nsmul_eq_mul,
      Nat.mul_comm,H9,YI,hn] using h
end
end P6_6_4
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qzTRNDe
noncomputable section
open Polynomial aR dN wH lB Tx
open K1 (K)
open private dMZ from ProximityPrize.SubmissionLower.ZsDvnmd
open private bnw from ProximityPrize.SubmissionLower.Z5cYAOe
open private lB.denominator from ProximityPrize.SubmissionLower.ZceTCvc
open private VT cGH bR8.bnw from ProximityPrize.SubmissionLower.ZxReCna
theorem gKX (f :af 4) (hpos :0<(shape f).t) :
    ∃ C:a1h (P6_6_6.rH (shape f)),
      ∀ S:K[X],S.natDegree≤P6_6.gZ→Dd f (extend S) →
        qg f (extend S)→C.ar5 S:= by
  have hchar :P6_6.bf<K1.p:= by
    change 133426<0x7f000001
    decide
  by_cases ht: (shape f).t=1
  · rw [P6_6_6.rH,ite_eq_left ht]
    obtain ⟨hD,hN⟩:=dMZ P6_6.bf f ht
    obtain ⟨C,hC⟩:=aKK.djr _ _ hD hN
    exact ⟨C,fun S hS hon hr =>
      hC S (Nat.lt_succ_of_le hS) (bnw hchar ht (extend S) hon.1 hr)⟩
  · rw [P6_6_6.rH,ite_eq_right ht]
    let L:=P6_6.bf+4
    have horder (j:Fin P6_6.bf) :j.val≤L :=
      j.isLt.le.trans (Nat.le_add_right _ _)
    obtain ⟨hD,hN⟩:=cGH L f (shape f).iU
      ⟨le_max_left _ _,le_rfl,le_rfl⟩ (Tn f) hpos
    obtain ⟨C,hC⟩:=aKK.djr (bC (lB.denominator L f))
      (fun j:Fin P6_6.bf=>bC (VT L f j.val))
      hD (fun j=>hN j.val (horder j))
    refine ⟨C,fun S hS hon hr => ?_⟩
    obtain ⟨hne,hcoeff⟩:=bR8.bnw L f (extend S) hon.1 hr
    exact hC S (Nat.lt_succ_of_le hS) ⟨hne,fun j=>hcoeff j.val (horder j) (j.isLt.trans hchar)⟩
end
end qzTRNDe
end
section
set_option autoImplicit true
namespace P6_8
noncomputable section
open i4 PolynomialDifferential
open P5_8 (Equation small bo8 Moments small_shape donor_shape)
theorem agreement_ok :aRk A:=⟨by decide,by decide,by decide,by decide⟩
theorem donor_width :bo8.m≤bo8.m*A-N*bo8.B:= by decide
private theorem stack_le {a :ℕ} {s :Source} {r :ℕ} (hs :Rz s)
    (hw:s.m≤ s.m*a-N*s.B) (hr :aWw s (s.B+1)≤ r) (w:Node→K) :
    Vv a s w≤n*r := by
  have ht:axY s (s.B+1) := by
    intro j hj hj'
    have :=(hs.support j hj).1
    omega
  exact (cw9.proof a s hs hw w).trans
    (Nat.mul_le_mul_left _ ((a9M.proof a s (s.B+1) hs hw le_rfl ht).trans hr))
theorem small_equation (w:Node→K) :
    ∃ Q:Equation,ato small Q ∧ ∀ f∈close A w,differentialSpecialization Q f=0:= by
  obtain ⟨hr,hm⟩:=P5_8_1.of_children q1EkR5c.proof qokZnNd.proof q2aXx2a.proof
  have hw:small.m≤ small.m*A-N*small.B:= by decide
  have hR:=stack_le small_shape hw hr w
  have hdim:=cqa A small small_shape hw
  rcases hm with ⟨hT,hS,hV⟩
  rw [hT,hS,hV] at hdim
  have hnum :n*232369+N*610160<small.m*A*12850+205216:= by decide
  have hlt:Vv A small w<Fintype.card (apU A small) := by omega
  obtain ⟨Q,hQ,hwt,hlocal⟩:=interpolant small_shape hw w hlt
  exact ⟨Q,hQ,specializes hwt hlocal⟩
theorem donor_surplus (hr :aWw bo8 6252≤0x62703852f02)
    (hm:Moments bo8 0x12e20e912 0x1098bf757c00 0x5e143ee4d6c) (w:Node→K) :
    DonorSurplus w:= by
  have hR:=stack_le donor_shape donor_width hr w
  have hdim:=cqa A bo8 donor_shape donor_width
  rcases hm with ⟨hT,hS,hV⟩
  rw [hT,hS,hV] at hdim
  have hnum :n*0x62703852f02+donorMargin+N*0x1098bf757c00 =
      bo8.m*A*0x12e20e912+0x5e143ee4d6c:= by decide
  unfold DonorSurplus
  omega
end
end P6_8
end
