import ProximityPrize.SubmissionLower.DdZQtCuFa
import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.DdBG
import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdAA
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.DdZgdIx1d
import ProximityPrize.SubmissionLower.RingHomShortcuts
import ProximityPrize.SubmissionLower.DdP6Defs
import ProximityPrize.SubmissionLower.DdA2
import ProximityPrize.SubmissionLower.DdA3
import ProximityPrize.SubmissionLower.DdB4
import ProximityPrize.SubmissionLower.DdZqZuDUb
import ProximityPrize.SubmissionLower.DdZeLOjNb
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
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
 simp only [coeff_monomial,Finsupp.single_apply]
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
open DdK1 aR
open scoped Polynomial BigOperators





























































































































































end
end P6_6_4
end
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open aR Polynomial
open scoped Polynomial



set_option maxRecDepth 4000







































































end
end P6_6_4
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qzTRNDe
noncomputable section
open Polynomial aR
open DdK1 (K)





























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
