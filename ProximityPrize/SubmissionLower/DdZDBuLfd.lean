import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdA2
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdB4
import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.DdBG
import ProximityPrize.SubmissionLower.DdZ1iXjHc
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.DdZ8H1fka
import ProximityPrize.SubmissionLower.DdZQtCuFa
import ProximityPrize.SubmissionLower.DdZeLOjNb
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ReedSolomon_MutualCorrelatedAgreement_Johnson_Agreement
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Finset_PairwiseIntersection
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_LinearAlgebra_FiniteDimensional
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Basis
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Degree_IsMonicOfDegree
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_TrivSqZeroExt_Ideal
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_BoxIntegral_UnitPartition
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Measure
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Visible
import ProximityPrize.SubmissionLower.LibraryMathlib_Combinatorics_Pigeonhole
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Finsupp_Interval
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Set_Card_Arithmetic
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Sym_NatCard
import ProximityPrize.SubmissionLower.LibraryMathlib_GroupTheory_CosetCover
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_FreeModule_Norm
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_TensorProduct_Free
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_FunctionField
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_RatFunc_Ostrowski
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_DedekindDomain_Factorization
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Finiteness_Descent
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Flat_Equalizer
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_GradedAlgebra_Radical
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Ideal_IsPrincipalPowQuotient
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Localization_NormTrace
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_OrderOfVanishing_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_PowerSeries_Inverse
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RamificationInertia_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Regular_Flat
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Surjective
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Unramified
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Spectrum_Prime_Homeomorph
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_Discrete_RankOne
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_LocalSubring
import ProximityPrize.SubmissionLower.LibraryMathlib_Topology_Algebra_MvPolynomial
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_DdZDBuLfd
set_option Elab.async false




















set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Function.iterate_succ_apply' → zLk, MvPolynomial.aeval_X → zTw, MvPolynomial.eval₂Hom → zOD, MvPolynomial.map → zDK, MvPolynomial.pderiv → zWe, MvPolynomial.pderiv_mul → zGW
section
set_option autoImplicit true
namespace qC8CERb
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative gR
open aR (ao embed af jet cK Z8)
open i4 (K N)

open P5_8_3 (rows)

private abbrev weight (i:Fin 3) :ℕ:=N - i.val
abbrev coeffForm:=MvPolynomial.optionEquivRight ao (Fin 3)
theorem specialize (Q:DifferentialPolynomial ao 2) (S:(Polynomial ao)) :
  cK (coeffForm Q) S=differentialSpecialization Q S:= by
 let x :Option (Fin 3)→(Polynomial ao) := fun
  | none=>Polynomial.X
  | some i=>jet S i
 have h:=MvPolynomial.aeval_map_optionEquivRight (R:=ao) x Q
 rw [show x none=Polynomial.X from rfl,
  show (fun j=>x (some j))=jet S from rfl,Polynomial.aeval_X_left] at h
 rw [show (AlgHom.id ao (Polynomial ao)).toRingHom=RingHom.id ((Polynomial ao)) from rfl,
  MvPolynomial.map_id,MvPolynomial.aeval_eq_eval] at h
 refine h.trans (AlgHom.congr_fun ?_ Q)
 apply MvPolynomial.algHom_ext
 intro v
 rw [differentialSpecializationHom,zTw,zTw]
 cases v <;> rfl
theorem Yw {w T R} (hR:R∈rows w T) :
    ∀ e∈(coeffForm (zDK embed R)).support,
      ((coeffForm (zDK embed R)).coeff e).natDegree +
        e.sum (fun i k=>weight i*k)≤T:= by
  let P:=coeffForm (zDK embed R)
  intro e he
  have hw:R∈MvPolynomial.restrictWeightedDegree (differentialWeight N) T:=hR.1.2
  have h:=MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp hw
  let j:=(P.coeff e).natDegree
  have hc: (P.coeff e).coeff j≠0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp he)
  rw [MvPolynomial.optionEquivRight_coeff_coeff] at hc
  have hs :e.optionElim j∈R.support :=
    MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr hc)
  have hb:=(Finset.sup_le_iff.mp h) _ hs
  change (e.optionElim j).weight (differentialWeight N)≤T at hb
  rw [show differentialWeight (d:=2) N=fun v=>v.elim 1 weight from by
    funext v; cases v <;> rfl,Finsupp.weight_optionElim,one_mul] at hb
  simpa only [Finsupp.weight_apply,smul_eq_mul,Nat.mul_comm] using hb
private theorem shift_partial (i:Fin 3) (P:af 3) (S:(Polynomial ao)) :
   Z8 (zWe i P) S=zWe i (Z8 P S) := by
 classical
 let g:=zOD MvPolynomial.C
   (fun j:Fin 3=>MvPolynomial.X j+MvPolynomial.C (jet S j))
 change g (zWe i P)=zWe i (g P)
 induction P using MvPolynomial.induction_on with
 | C c=>simp [g]
 | add P Q hP hQ=>simp [hP,hQ]
 | mul_X P j hP =>
   rw [zGW,map_add,map_mul,map_mul,hP,map_mul,zGW]
   by_cases hj:j=i
   · subst j
     simp [g]
   · simp [g,MvPolynomial.pderiv_X_of_ne hj]
theorem shift_jetDerivative (Q:DifferentialPolynomial K 2) (S:(Polynomial ao))
    (i:Fin 3) (r :ℕ) :
    Z8 (coeffForm (zDK embed (jetDerivative Q i r))) S =
      (zWe i)^[r] (Z8 (coeffForm (zDK embed Q)) S) := by
  induction r with
  | zero=>rfl
  | succ r ih =>
    rw [jetDerivative_succ,map_separant,zLk]
    have he (F:DifferentialPolynomial ao 2) :
        coeffForm (separant F i)=zWe i (coeffForm F) := by
      apply coeffForm.symm.injective
      rw [MvPolynomial.optionEquivRight_symm_pderiv,AlgEquiv.symm_apply_apply,
        AlgEquiv.symm_apply_apply]
      rfl
    rw [he,shift_partial,ih]
theorem coeff_iterate_zero (i:Fin 3) (P:af 3) {D:ℕ}
   (h : ∀ e :Fin 3 →₀ ℕ,e.degree<D→P.coeff e=0)
   (r :ℕ) (e :Fin 3 →₀ ℕ) (he :e.degree+r<D) :
   ((zWe i)^[r] P).coeff e=0:= by
 induction r generalizing e with
 | zero=>exact h e (by simpa using he)
 | succ r ih =>
   rw [zLk,MvPolynomial.coeff_pderiv,ih,zero_mul]
   rw [map_add,Finsupp.degree_single]
   omega
theorem atJet_eq_const (P:af 3) (S:(Polynomial ao)) :
  cK P S=(Z8 P S).coeff 0:= by
 let g:Fin 3→af 3:= fun i=>MvPolynomial.X i+MvPolynomial.C (jet S i)
 change (MvPolynomial.eval (jet S)) P =
  (MvPolynomial.constantCoeff.comp (zOD MvPolynomial.C g)) P
 congr 1
 ext <;> simp [g]
end
end qC8CERb
end
section
set_option autoImplicit true
namespace qfaXGOd
noncomputable section
open i4 (Jet)

open P5_8_3 (symbolBand)
open Finset
open P5_8_6 (row box_formula)
private def S5:Jet ≃ (Fin 3 →₀ ℕ) where
 toFun j:=Finsupp.equivFunOnFinite.symm ![j.a,j.b,j.c]
 invFun u:=⟨u 2,u 1,u 0⟩
 left_inv := by rintro ⟨c,b,a⟩; rfl
 right_inv := by intro u; ext i; fin_cases i <;> rfl
private def tuples (B J C:ℕ) :Finset Jet :=
 (range (C+1)).sigma fun c =>
   (range (J+1-2*c)).sigma fun b=>range (B+1-(c+b))
private theorem exponent_set (B J C:ℕ) :
   (↑((tuples B J C).map S5.toEmbedding) :Set (Fin 3 →₀ ℕ)) =
     {u | u.degree≤B∧u.weight Fin.val≤J∧u (Fin.last 2)≤C} := by
 ext u
 obtain ⟨⟨c,b,a⟩,rfl⟩:=S5.surjective u
 rw [Finset.mem_coe,mem_map_equiv,Equiv.symm_apply_apply]
 simp only [tuples,mem_sigma,mem_range,Set.mem_ofPred_eq,Finsupp.degree_eq_sum,
   Finsupp.weight_eq_sum,Fin.sum_univ_three]
 change (c<C+1∧b<J+1-2*c∧a<B+1-(c+b)) ↔
   a+b+c≤B∧a*0+b*1+c*2≤J∧c≤C
 omega
theorem proof :P5_8_3.c7:= by
 rintro ⟨B,J,C⟩
 rw [symbolBand,← exponent_set,MvPolynomial.finrank_restrictSupport_finset,card_map,
  box_formula]
 simp only [tuples,card_sigma,card_range,row,le_refl]
end
end qfaXGOd
end

end Merged6967_DdZDBuLfd

section Merged6967_DdZRlaVZc
set_option Elab.async false


































































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

end Merged6967_DdZRlaVZc

section Merged6967_DdZZ4xzRc
set_option Elab.async false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open _root_ renaming Algebra.algebraMap→c9,CommRing→nI,DecompositionMonoid→ ox,Fin.sum_univ_two→ oK,Finset.filter_subset→pz,Finset.prod_dvd_prod_of_subset→ oY,Function.Injective→n5,Ideal.mem_span_singleton→pU,Ideal.span→ ov,IsDomain→ oj,IsRelPrime→lJ,Module.Finite→ oy,Module.Flat→nX,Multiset.toFinset_prod_dvd_prod→pG,MvPolynomial→lI,MvPolynomial.map→ oz,MvPolynomial.optionEquivRight→p5,Nat.mul_le_mul_left→ oZ,P5_8.Equation→aU,PolynomialDifferential.jetDegree→cy,PolynomialDifferential.jetTotalDegree→mD,PolynomialDifferential.separant→lz,ReedSolomon.HiddenDerivative.SourceColumn.interpolant→lV,StrongNormalizationMonoid→pL,Submodule→ oq,UniqueFactorizationMonoid→pQ,UniqueFactorizationMonoid.strongNormalizationMonoid→pC,apQ.initial→ oD,ringChar→nq
section
set_option autoImplicit true
namespace qyOiD7d
open i4 (K p)

open P5_8_3 (mem_nativeBand)
open PolynomialDifferential MvPolynomial
private theorem separant_not_dvd {F:aU} {i:Fin 3}
  (hF:F≠0) (hi:0<cy F i) (hc:cy F i< nq K) :
  ¬ F∣lz F i:= by
 have hn:=separant_ne_zero F i
  (jetDegreeCastsNeZero_of_ringChar (Or.inr hc) _ hi le_rfl)
 have hd:=jetDegree_separant_le_sub_one F i
 rintro ⟨S,he⟩
 have hS:S≠0:= fun h=>hn (by rw [he,h,mul_zero])
 unfold cy at hd hi
 rw [he,degreeOf_mul_eq hF hS] at hd
 omega
private theorem cNr (i:Fin 3) {F:aU} (hF:Prime F)
    (hsep : ¬ F∣lz F i) (a :ℕ) (ha :a< nq K)
    {S:aU} (hS : ¬ F∣S) :
    ¬ F∣jetDerivative (F^a*S) i a := by
  induction a generalizing S with
  | zero=>simpa only [pow_zero,one_mul,jetDerivative_zero] using hS
  | succ a ih =>
    let V:=((a+1 :ℕ) :aU)*(lz F i*S)+F*lz S i
    have hstep:lz (F^(a+1)*S) i=F^a*V:= by
      rw [lz ,pderiv_mul,pderiv_pow,Nat.add_sub_cancel,pow_succ F a]
      dsimp only [V,lz]
      ring
    have hu:IsUnit ((a+1 :ℕ) :aU) := by
      rw [← map_natCast (C:K →+* aU)]
      exact (isUnit_iff_ne_zero.mpr
        (natCast_ne_zero_of_ringChar_eq_zero_or_lt (Or.inr ha) (Nat.succ_pos _) le_rfl)).map C
    have hV : ¬ F∣V:= by
      intro hd
      have h:=(dvd_add_left (dvd_mul_right F (lz S i))).mp hd
      exact (hF.dvd_or_dvd (hu.dvd_mul_left.mp h)).elim hsep hS
    rw [jetDerivative_eq_iterate,Function.iterate_succ_apply]
    change ¬ F∣jetDerivative (lz (F^(a+1)*S) i) i a
    rw [hstep]
    exact ih (Nat.lt_of_succ_lt ha) hV
private theorem exact_power {F R:aU} {l:ℕ}
   (h : ¬ F^l∣R) : ∃ a<l,F^a∣R ∧ ¬ F^(a+1)∣R:= by
 induction l with
 | zero=>exact (h (by rw [pow_zero]; exact one_dvd _)).elim
 | succ a ih =>
   by_cases hd:F^a∣R
   · exact ⟨a,Nat.lt_succ_self a,hd,h⟩
   · obtain ⟨b,hb,hdiv,hnext⟩:=ih hd
     exact ⟨b,hb.trans (Nat.lt_succ_self a),hdiv,hnext⟩
theorem proof :P5_8_3.c3:= by
 intro F R l hF hpos hsmall hband hderiv
 obtain ⟨i,hi⟩ : ∃ i:Fin 3,0<cy F i:= by
  by_contra! hn
  have hw:=jetTotalDegree_le_mul F hn
  simp only [Nat.mul_zero] at hw
  exact (Nat.not_lt_of_ge hw) hpos
 have hchar :nq K=p:=ringChar.eq K p
 have hf :cy F i< nq K:= by
  rw [hchar]
  exact (jetDegree_le_total F i).trans_lt (hsmall.trans_lt (by decide))
 have hr :cy R i< nq K:= by
  rw [hchar]
  exact (jetDegree_le_total R i).trans_lt ((mem_nativeBand.mp hband).1.trans_lt (by decide))
 by_contra hnot
 obtain ⟨a,hal,⟨S,hRS⟩,hnext⟩:=exact_power hnot
 have hR:R≠0:= by
  rintro rfl
  exact hnot (dvd_zero _)
 have hS:S≠0:= fun h=>hR (by rw [hRS,h,mul_zero])
 have hquot : ¬ F∣S:= by
  rintro ⟨U,rfl⟩
  exact hnext ⟨U,hRS.trans (by rw [pow_succ F a,mul_assoc])⟩
 have hdeg:cy R i=a*cy F i+jetDegree S i:= by
  rw [hRS]
  simp only [cy ,degreeOf_mul_eq (pow_ne_zero _ hF.ne_zero) hS,
    degreeOf_pow_eq _ _ _ hF.ne_zero]
 have ha :a≤ cy R i:= by
  rw [hdeg]
  calc
    a=a*1 :=(Nat.mul_one a).symm
    _≤a*cy F i:=oZ a hi
    _≤_:=Nat.le_add_right _ _
 exact cNr i hF.prime (separant_not_dvd hF.ne_zero hi hf)
  a (ha.trans_lt hr) hquot (hRS ▸ hderiv i a hal)
end qyOiD7d
end
section
set_option autoImplicit true
namespace qVHZuid
noncomputable section
open i4 P5_8 PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance :pL Equation :=
 pC
private def cVd:aU →+* BL 2 :=
 (oz apQ.RG).comp
   (p5 K (Fin 3)).toAlgHom.toRingHom
private theorem initialHom_apply (F:aU) :cVd F=oD F :=
 (apQ.b6h F).symm
private theorem initial_unit {F:aU} (hn:F≠0) (hd:mD F=0) :
  IsUnit (cVd F) := by
 rw [initialHom_apply]
 have hdeg: (oD F).totalDegree=0 :=
  (congrArg Jn.B (P5_8_3.initial_caps F)).trans hd
 have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
 have hc: (oD F).coeff 0≠0:= by
  intro hz
  exact apQ.b6j hn (by rw [he,hz,map_zero])
 rw [he]
 exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
theorem proof :P5_8_3.c4 := by
  classical
  intro Q P hQ _
  obtain ⟨L,R,D,hrel,hL,hR⟩:=exists_reduced_factors Q hQ P
  have hDQ:D ∣Q:=⟨L,hL.symm⟩
  have hDP:D ∣P:=⟨R,hR.symm⟩
  have hD:=ne_zero_of_dvd_ne_zero hQ hDQ
  let fs :=normalizedFactors D
  let js :=fs.toFinset.filter (fun F=>0< mD F)
  let G:Equation := ∏ F∈js,F
  have hmem {F:aU} (hf :F∈js) :F∈normalizedFactors D :=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp hf).1
  have hprod:Associated fs.prod D:=prod_normalizedFactors hD
  have hG:G∣D :=
    (oY js fs.toFinset id (pz _ _)).trans
      ((pG fs).trans hprod.dvd)
  refine ⟨⟨G,D,L,R,hG,hL.symm,hR.symm,hrel,?_,?_⟩⟩
  · refine ⟨fs.card,?_⟩
    rw [← initialHom_apply,← initialHom_apply]
    refine (map_dvd cVd hprod.symm.dvd).trans ?_
    rw [map_multiset_prod]
    have hf (F:aU) (hm:F∈fs) :cVd F∣cVd G:= by
      by_cases hj:0< mD F
      · exact map_dvd cVd (Finset.dvd_prod_of_mem id
          (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hm,hj⟩:F∈js))
      · exact (initial_unit (ne_zero_of_mem_normalizedFactors hm) (Nat.eq_zero_of_not_pos hj)).dvd
    simpa only [Multiset.map_const',Multiset.prod_replicate] using
      (Multiset.prod_dvd_prod_of_dvd cVd (fun _=>cVd G) hf)
  · intro T l hall
    unfold G
    rw [← Finset.prod_pow]
    have hirr (F:aU) (hf :F∈js) :Irreducible F :=
      irreducible_of_normalized_factor F (hmem hf)
    apply Finset.prod_dvd_of_isRelPrime
    · intro F hf E he hne
      exact ((hirr F hf).isRelPrime_iff_not_dvd.mpr
        (fun hd=>hne (normalizedFactors_eq_of_dvd D F (hmem hf) E (hmem he) hd))).pow
    · intro F hf
      have hd:=dvd_of_mem_normalizedFactors (hmem hf)
      exact hall F (hirr F hf) (hd.trans hDQ) (hd.trans hDP) (Finset.mem_filter.mp hf).2
end
end qVHZuid
end
section
set_option autoImplicit true
namespace q0KdFsb
noncomputable section
open i4 apQ MvPolynomial RingTheory.Sequence
open scoped Pointwise Polynomial
private theorem regular_pair_iff {R:Type*} [nI R] [oj R]
   [ox R] {a b:R} (ha :a≠0) :
   IsWeaklyRegular R [a,b]↔lJ a b:= by
 rw [isWeaklyRegular_cons_iff,isWeaklyRegular_singleton_iff]
 have hreg:IsSMulRegular R a := fun _ _ h=>mul_left_cancel₀ ha h
 rw [and_iff_right hreg]
 have hI:a•(⊤ : oq R R)=(ov {a} : Ideal R) := by
   rw [← Submodule.ideal_span_singleton_smul]
   exact Ideal.mul_top (ov ({a} : Set R))
 unfold QuotSMulTop
 rw [hI,isSMulRegular_iff_right_eq_zero_of_smul]
 let q:=Ideal.Quotient.mk (ov {a})
 change (∀ x,b•x=0→x=0)↔lJ a b
 have hq (x :R) :q x=0↔a∣x := by
   rw [Ideal.Quotient.eq_zero_iff_mem,pU]
 constructor
 · intro h d hdA hdB
   obtain ⟨u,hu⟩:=hdA
   obtain ⟨v,hv⟩:=hdB
   have hm:a∣b*u:=⟨v,by rw [hv,hu]; ac_rfl⟩
   have hz :b•q u=0:=(hq _).mpr hm
   obtain ⟨w,hw⟩:=(hq _).mp (h _ hz)
   exact isUnit_iff_dvd_one.mpr ⟨w,mul_left_cancel₀ ha (calc
     a*1=d*u:= by rw [mul_one,hu]
     _=a*(d*w) := by rw [hw]; ac_rfl)⟩
 · intro h x hx
   obtain ⟨u,rfl⟩:=Ideal.Quotient.mk_surjective x
   exact (hq _).mpr (h.dvd_of_dvd_mul_left ((hq _).mp hx))
private theorem flat_relPrime {R S:Type*} [nI R] [nI S] [oj R]
   [oj S] [ox R] [ox S] [Algebra R S]
   [nX R S] (hinj:n5 (c9 R S))
   {a b:R} (h:lJ a b) :lJ (c9 R S a) (c9 R S b) := by
 by_cases ha :a=0
 · subst a
   rw [map_zero,isRelPrime_zero_left]
   exact (isRelPrime_zero_left.mp h).map (c9 R S)
 have ha' : c9 R S a≠0:= fun h0=>ha (hinj (h0.trans (map_zero _).symm))
 exact (regular_pair_iff ha').mp
   ((regular_pair_iff ha).mpr h |>.of_flat)
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem map_relPrime {R S σ:Type*} [nI R] [nI S] [oj R]
    [oj S] [pQ R] [pQ S] [Algebra R S]
    [nX R S] (hinj:n5 (c9 R S))
    {a b:lI σ R} (h:lJ a b) :
    lJ (oz (c9 R S) a) (oz (c9 R S) b) := by
  have :nX (lI σ R) (lI σ S) :=
    Module.Flat.isBaseChange R (lI σ R) S (lI σ S)
      (Algebra.IsPushout.out (R:=R) (S:=lI σ R) (R' := S)
        (S' := lI σ S))
  exact flat_relPrime (MvPolynomial.map_injective _ hinj) h
theorem proof :P5_8_3.c5:= by
 intro L R h
 let e :=p5 K (Fin 3)
 have he :lJ (e L) (e R) :=
  IsRelPrime.of_map e.symm (by simpa only [AlgEquiv.symm_apply_apply] using h)
 have :nX (Polynomial K) FX:=IsLocalization.flat _ (nonZeroDivisors (Polynomial K))
 have :nX (Polynomial K) nU:=Module.Flat.trans (Polynomial K) FX nU
 have hcenter :c9 (Polynomial K) nU=RG:=IsScalarTower.algebraMap_eq (Polynomial K) FX nU
 have hi:n5 (c9 (Polynomial K) nU) :=hcenter.symm ▸ bch
 rw [b6h,b6h,← hcenter]
 exact map_relPrime hi he
end
end q0KdFsb
end
section
set_option autoImplicit true
namespace qmRQvQa
noncomputable section
open i4 P5_8 P5_8_3 PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open i4 (bYf)

set_option backward.isDefEq.respectTransparency false
theorem finiteWeighted {d:ℕ} (v :JetVariable d→ℕ) (hv : ∀ i,v i≠0) (T:ℕ) :
  oy K (restrictWeightedDegree v T:oq K (DifferentialPolynomial K d)) :=
 Module.Finite.iff_fg.mpr (restrictWeightedDegree_fg v hv T)
instance finiteRows (w:Node→K) (T:ℕ) :oy K (rows w T) := by
 let:=finiteWeighted (differentialWeight (d:=2) N) (by
   intro i
   cases i with
   | none=>decide
   | some j=>exact (differentialWeight_some_pos_of_order_lt_degree (by decide :2<N) j).ne') T
 exact Submodule.finiteDimensional_of_le
   (show rows w T≤ restrictWeightedDegree (differentialWeight N) T from
     fun _ h=>h.1.2)
theorem matrix_dimension (a :ℕ) (s :Source) (hshape :Rz s)
    (hb:N*s.B≤ s.m*a) (hp:0<s.m*a) (w:Node→K)
    (V:oq K aU) [oy K V]
    (hV : ∀ R:aU,R∈nativeBand ⟨s.B,s.J,s.C⟩ →
      differentialWeightedDegree N R<s.m*a →
      (∀ i,SatisfiesLocalConstraints s.m (node i) (w i) R)→R∈V) :
    Fintype.card (apU a s)≤Vv a s w+Module.finrank K V:= by
  classical
  let cols :=column a s
  let M:=localConstraintMatrix s.m (fun i=>node i) w cols
  let f : (apU a s→K) →ₗ[K] Equation := {
    toFun:=lV cols
    map_add' v z := by
      simp only [lV,Pi.add_apply,map_add,Finset.sum_add_distrib]
    map_smul' c v := by
      simp only [lV,Pi.smul_apply,map_smul,
        Finset.smul_sum,RingHom.id_apply] }
  have hf (v :M.mulVecLin.ker) :f v.val∈V:= by
    have hsupp (u) (hu:u∈(f v.val).support) : ∃ i,u=(cols i).exponent:= by
      apply amZ.ef8 (RingHom.id K) cols v.val u
      change u∈(lV cols v.val).support at hu
      simpa only [MvPolynomial.map_id] using hu
    refine hV _ ?_ ?_ ?_
    · refine mem_nativeBand.mpr ⟨?_,?_,?_⟩
      · apply Finset.sup_le
        intro u hu
        obtain ⟨i,rfl⟩:=hsupp u hu
        change totalJetDegree (cols i).exponent≤ s.B
        simpa [cols,column,Jet.q,oK,Nat.add_assoc] using
          (hshape.support _ i.1.property).1
      · apply Finset.sup_le
        intro u hu
        obtain ⟨i,rfl⟩:=hsupp u hu
        change (cols i).exponent.weight i4.indexWeight≤ s.J
        simpa [cols,column,i4.indexWeight,SourceColumn.weight_exponent,oK,
          Jet.v,Nat.mul_comm] using (hshape.support _ i.1.property).2.1
      · apply MvPolynomial.degreeOf_le_iff.mpr
        intro u hu
        obtain ⟨i,rfl⟩:=hsupp u hu
        change (cols i).exponent (some (1 :Fin 2).succ)≤ s.C
        rw [SourceColumn.exponent_succ]
        exact (hshape.support _ i.1.property).2.2
    · apply (Finset.sup_lt_iff hp).mpr
      intro u hu
      obtain ⟨i,rfl⟩:=hsupp u hu
      have hx :=i.2.isLt
      have hq:=(oZ N (hshape.support _ i.1.property).1).trans hb
      simp only [width,Jet.q,Jet.v,N] at hx hq
      rw [SourceColumn.weight_exponent]
      simp [cols,column,differentialWeight,oK,N]
      omega
    · exact (localConstraintMatrix_mulVec_eq_zero_iff s.m node w cols v.val).mp v.property
  let g:M.mulVecLin.ker →ₗ[K] V :=
    (f.comp M.mulVecLin.ker.subtype).codRestrict V hf
  have hg:n5 g:= by
    intro v z h
    have he :f v.val=f z.val :=congrArg Subtype.val h
    apply Subtype.ext
    funext i
    have hc:=congrArg (fun Q:aU=>Q.coeff (cols i).exponent) he
    change (lV cols v.val).coeff (cols i).exponent =
      (lV cols z.val).coeff (cols i).exponent at hc
    have ci:n5 cols :=bYf a s
    simpa only [SourceColumn.coeff_interpolant ci] using hc
  have hdim:=LinearMap.finrank_le_finrank_of_injective hg
  have hrank :=M.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  change Vv a s w+Module.finrank K M.mulVecLin.ker =
    Fintype.card (apU a s) at hrank
  exact hrank.ge.trans (Nat.add_le_add_left hdim _)
end
end qmRQvQa
end

end Merged6967_DdZZ4xzRc
