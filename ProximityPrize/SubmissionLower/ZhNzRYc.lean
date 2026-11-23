import Mathlib.Data.Nat.Basic
import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.E7
import ProximityPrize.SubmissionLower.Z3BnLje
import ProximityPrize.SubmissionLower.Z7Epuse
import ProximityPrize.SubmissionLower.ZlfuKwd
import ProximityPrize.SubmissionLower.ZPSk6xb
import ProximityPrize.SubmissionLower.ZQmiAIb
import ProximityPrize.SubmissionLower.ZQpU10d
import ProximityPrize.SubmissionLower.ZCuFj9c
import ProximityPrize.SubmissionLower.ZlyD2pd
import ProximityPrize.SubmissionLower.ZjZ6ihd
import ProximityPrize.SubmissionLower.Zw0beKa
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.ZOcoJLa
import ProximityPrize.SubmissionLower.ZiuGIoc
import ProximityPrize.SubmissionLower.ZDlyzqd
import ProximityPrize.SubmissionLower.Z66Jm5b
import ProximityPrize.SubmissionLower.Z7r9bnb
import ProximityPrize.SubmissionLower.ZEe4bHc
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.EssFiniteType → zl5, Algebra.FiniteType → zUK, Ideal.Quotient.mk → zVv, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, Module.Finite → zAa, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, Polynomial.C → z1z, PowerSeries.C → zMG, RingHom.ker → zdq
section
section
set_option autoImplicit true
namespace qisrtXb






set_option quotPrecheck false in
scoped notation "p!" a "," K "," C "," W "," l "," n "," p "," S =>
 certificate a K C W l n p S rfl (by decide) rfl rfl rfl rfl (by decide) (by
  repeat' first
  | refine ⟨?_,?_⟩
    · as_aux_lemma=>rfl
  | as_aux_lemma=>rfl)
end qisrtXb
end
end
section
section
namespace qhFwyvc
noncomputable section
open Polynomial
open P5 (K)
open cu (L)
open P5_7_7 (phys)
open qNu3xvc qoCymac
def c1 :Prop :=
  ∀ {E :Type} [Field E] [zZE L E] (A:Equation E) (S:Sections A)
    (γ:K) (hγ:γ∈S.marks) (r :Bool),(r=true→S.P γ≠0) →
    zdq (ek A (S.place γ) r)≤zdq (aJB S γ hγ r)
def c2 :Prop :=
  ∀ {E :Type} [Field E] [zZE L E] (A:Equation E) (S:Sections A)
    (γ:K) (hγ:γ∈S.marks) (δ:Derivation L E E),
    LocalDerivation (S.atPlace γ hγ) (S.place γ) δ →
    ∀ (r :Bool),(r=true→S.P γ≠0) →
    ∀ J:EM A (S.place γ) δ r,
      let s :=aJB S γ hγ r
      s J.sep≠0 ∧
      s J.dx/s J.sep=sectionJet (S.P γ) (S.Q γ) r ∧
      s J.num/s J.sep=aIF (S.P γ) (S.Q γ) r*(phys (S.num γ)/phys (S.den γ))
theorem of_children (h1 :c1) (h2 :c2) :qoCymac.c2 := by
 intro E _ _ A S γ hγ δ hδ x
 have q0 (r :Bool) (hden: (denominator (S.P γ) (S.Q γ) r).eval x≠0) :
    Nonempty (MarkChart A S γ hγ δ x r) := by
   have hr :r=true→S.P γ≠0:= by
    rintro rfl hp
    exact hden (by simp [denominator,hp])
   obtain ⟨J⟩:=integralJets A (S.place γ) (S.regular γ hγ) δ hδ r
   obtain ⟨hs,hj,hv⟩:=h2 A S γ hγ δ hδ r hr J
   exact assemble S γ hγ δ x r J (h1 A S γ hγ r hr) hden hs hj hv
 by_cases hq: (S.Q γ).eval x=0
 · refine ⟨true,q0 true ?_⟩
   intro hp
   change (S.P γ).eval x=0 at hp
   obtain ⟨a,b,hab⟩:=S.coprime γ hγ
   have h:=congrArg (fun f :L[X]=>f.eval x) hab
   simp only [eval_add,eval_mul,hp,hq,mul_zero,add_zero,eval_one,zero_ne_one] at h
 · exact ⟨false,q0 false hq⟩
end
end qhFwyvc
end
section
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace qIGP9Qa
noncomputable section
open scoped WithZero IntermediateField.algebraAdjoinAdjoin
open cu (L)
open E7 (CurvePlace CurveField)
open aFU
open qNu3xvc qoCymac
open private eaZ bJK from ProximityPrize.SubmissionLower.V
open private bQb eLz aDm from ProximityPrize.SubmissionLower.A2
open private cfl from ProximityPrize.SubmissionLower.A3
variable {E :Type} [Field E] [zZE L E]
theorem LX (w:CurvePlace L E) :
  ∃ t:E,Transcendental L t∧w.value t<1 := by
 let:w.value.IsTrivialOn L:=⟨w.on_constants⟩
 obtain ⟨t,ht⟩:=w.normalized (WithZero.exp (-1 :ℤ))
 have ht₀:t≠0:= fun h=>WithZero.exp_ne_zero (by rw [← ht,h,map_zero])
 have ht₁:w.value t<1 := by
  rw [ht,WithZero.exp_lt_one_iff]
  decide
 exact ⟨t,Valuation.transcendental_of_ne_one L (v :=w.value) t ht₀ ht₁.ne,ht₁⟩
theorem seedResidue (hE :CurveField L E) (w:CurvePlace L E)
  (a :w.value.valuationSubring) : ∃ c:L,w.value ((a :E)-algebraMap L E c)<1 := by
 obtain ⟨t,ht,hw⟩:=LX w
 exact cfl hE w.value ⟨w.on_constants⟩ ⟨t,ht.ne_zero,hw.ne⟩ a a.property
scoped instance seedIntegersAlgebra (w:CurvePlace L E) :
  zZE L w.value.valuationSubring := by
 let:w.value.IsTrivialOn L:=⟨w.on_constants⟩
 exact ((algebraMap L E).codRestrict w.value.valuationSubring.toSubring
  (Valuation.IsTrivialOn.valuation_algebraMap_le_one w.value)).toAlgebra
theorem seedEssential (hE :CurveField L E) (w:CurvePlace L E) :
   zl5 L w.value.valuationSubring := by
 obtain ⟨t,ht,hw⟩:=LX w
 let R:=DT L E t
 let B:=DR L E t
 let T:=IntermediateField.adjoin L ({t} : Set E)
 have :zAa T E :=eaZ hE ht
 have :zAa R B:=bRt.proof L E t ht inferInstance
 have :IsDedekindDomain B:=bJK ht
 have :IsFractionRing B E :=integralClosure.isFractionRing_of_finite_extension T E
 let z :ax5 L E t:=⟨w,(bQb w.value ht.ne_zero).mpr hw⟩
 obtain ⟨P,hP⟩:=eLz ht z
 let D:=aDm ht P
 have hv :D.valuation E=w.value :=
   congrArg (fun u:ax5 L E t=>u.1.value) hP
 let C:=D.valuationSubringAtPrime E
 have he :C=w.value.valuationSubring :=
   (D.valuationSubringAtPrime_eq_valuationSubring (K:=E)).trans
     (congrArg Valuation.valuationSubring hv)
 let:zZE L C:=((algebraMap B C).comp (algebraMap L B)).toAlgebra
 have :IsScalarTower L B C:=IsScalarTower.of_algebraMap_eq' rfl
 have :zUK L R:=Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton _)
 have :zUK L B:=Algebra.FiniteType.trans
   (show zUK L R from inferInstance) (show zUK R B from inferInstance)
 have :zl5 B C:=Algebra.EssFiniteType.of_isLocalization C D.asIdeal.primeCompl
 have hC:zl5 L C:=Algebra.EssFiniteType.comp L B C
 let e :C ≃ₐ[L] w.value.valuationSubring :=
   { RingEquiv.subringCongr (congrArg ValuationSubring.toSubring he) with
     commutes' := fun c=>Subtype.ext ((IsScalarTower.algebraMap_apply L B E c).symm) }
 exact (Algebra.EssFiniteType.iff_of_algEquiv e).mp hC
end
end qIGP9Qa
end
end
section
namespace qqpP4De
noncomputable section
open MvPolynomial qQ9yWTb qb0hmCe q1kuFjb
open cu (L)

open scoped WithZero
private theorem arc_kernel {q:Curve} (hq:Irreducible q)
    (a :Fin 2→PowerSeries L) (hq0:MvPolynomial.eval₂ zMG a q=0)
    {i:Fin 2} (hi:PowerSeries.coeff 1 (a i)≠0) :
    zdq (zIe (fun j=>(a j:LaurentSeries L))).toRingHom =
      zye {q} := by
  let g:Curve →ₐ[L] LaurentSeries L:=zIe fun j=>(a j:LaurentSeries L)
  let I:Ideal Curve :=zye {q}
  have hq' : g q=0:= by
    have hC: (HahnSeries.ofPowerSeries ℤ L).comp zMG=algebraMap L (LaurentSeries L) :=
      RingHom.ext fun c=>(HahnSeries.ofPowerSeries_C c).trans (LaurentSeries.algebraMap_apply L c).symm
    have h:=MvPolynomial.hom_eval₂ q zMG (HahnSeries.ofPowerSeries ℤ L) a
    rw [hq0,map_zero,hC] at h
    exact h.symm
  have hI:I≤zdq g.toRingHom:=(zvl _).mpr hq'
  refine le_antisymm (fun r hr => ?_) hI
  by_contra hn
  let J:=I ⊔ zye {r}
  have hP:I.IsPrime :=(Ideal.span_singleton_prime hq.ne_zero).mpr hq.prime
  have hdim: (affineHilbertPolynomial I).natDegree=1 := by
    have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one hq.ne_zero hP.ne_top
    change (affineHilbertPolynomial I).natDegree+1=Nat.card (Fin 2) at h
    simpa [Nat.card_eq_fintype_card] using h
  have hcut:=(principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hP hn (le_refl r.totalDegree)).1
  have hJ: (affineHilbertPolynomial J).natDegree=0 :=
    Nat.eq_zero_of_le_zero (by simpa only [hdim,Nat.sub_self] using hcut)
  let:zAa L (Curve ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
  have hker :J≤zdq g.toRingHom :=
    sup_le hI ((zvl _).mpr hr)
  let b:=Ideal.Quotient.liftₐ J g hker
  have hb:IsIntegral L (b (zVv J (z9v i))) := by
    obtain ⟨p,hp,hz⟩:=IsIntegral.of_finite L (zVv J (z9v i))
    exact ⟨p,hp,(Polynomial.aeval_algHom_apply b _ p).trans
      ((congrArg b hz).trans (map_zero b))⟩
  change IsIntegral L (g (z9v i)) at hb
  rw [show g (z9v i)=(a i:LaurentSeries L) from MvPolynomial.aeval_X _ _] at hb
  have hc:=mem_algebraicClosure_iff'.mpr hb
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure L (LaurentSeries L))] at hc
  obtain ⟨c,hc⟩:=IntermediateField.mem_bot.mp hc
  have he : (zMG c:PowerSeries L)=a i :=
    HahnSeries.ofPowerSeries_injective (Γ:=ℤ) (by
      rw [HahnSeries.ofPowerSeries_C,← LaurentSeries.algebraMap_apply]
      exact hc)
  exact hi (by rw [← he,PowerSeries.coeff_C_of_ne_zero (by decide)])
theorem proof :q1kuFjb.c2 :=q5azJba.arc
end
end qqpP4De
end
section
set_option autoImplicit true
namespace qoRVxvd
open aR (ao)
open aFN (Slot exponent)
open qzLARrc (derivativeIndex)
open qmb8rCe (box cap rankCut cutMatrix)
open MvPolynomial
open scoped Polynomial BigOperators
noncomputable section
local notation "T" => (Polynomial.X:ao[X])
local notation "x" => (MvPolynomial.X 1 :Target)
local notation "y" => (MvPolynomial.X 0:Target)
private def exp₂ (b c:ℕ) :Fin 2 →₀ ℕ:=(Finsupp.single (0:Fin 1) b).cons c
private def nested:Target →+* ao[X][X] :=
  (Polynomial.mapRingHom (uniqueAlgEquiv ao (Fin 1)).toRingHom).comp
    (finSuccEquiv ao 1).toRingHom
private theorem coeff_nested (P:Target) (b c:ℕ) :
    ((nested P).coeff c).coeff b=P.coeff (exp₂ b c) := by
  change ((Polynomial.map (uniqueAlgEquiv ao (Fin 1)).toRingHom
    (finSuccEquiv ao 1 P)).coeff c).coeff b= _
  rw [Polynomial.coeff_map]
  change ((uniqueAlgEquiv ao (Fin 1) ((finSuccEquiv ao 1 P).coeff c)) :ao[X]).coeff b= _
  rw [coeff_uniqueAlgEquiv,finSuccEquiv_coeff_coeff]
  rfl
private theorem coeff_chart (b c u v :ℕ) :
    (((1+x)^b*(x+y)^c:Target).coeff (exp₂ u v)) =
      if v≤ c∧c-v≤u then (c.choose v :ao)*(b.choose (u-(c-v)) :ao) else 0:= by
  classical
  have hx :nested x=z1z T:= by
    have hx' := finSuccEquiv_X_succ (R:=ao) (j:=(0:Fin 1))
    rw [show (0:Fin 1).succ=(1 :Fin 2) from rfl] at hx'
    change Polynomial.map (uniqueAlgEquiv ao (Fin 1)).toRingHom (finSuccEquiv ao 1 x)= _
    rw [hx',Polynomial.map_C]
    simp [uniqueAlgEquiv_apply]
  have hy :nested y=Polynomial.X:= by simp [nested,finSuccEquiv_X_zero]
  have hprod:nested ((1+x)^b*(x+y)^c)=z1z ((1+T)^b) *
      (Polynomial.X+Polynomial.C T)^c:= by
    simp only [map_mul,map_pow,map_add,map_one,hx,hy]
    rw [add_comm (z1z T) Polynomial.X]
  rw [← coeff_nested]
  rw [hprod,Polynomial.coeff_C_mul,Polynomial.coeff_X_add_C_pow]
  by_cases hv :v≤ c
  · rw [← mul_assoc,← Polynomial.C_eq_natCast,Polynomial.coeff_mul_C,
      Polynomial.coeff_mul_X_pow']
    simp [hv,Polynomial.coeff_one_add_X_pow,mul_comm]
  · have hv' : c<v := by omega
    simp [hv,Nat.choose_eq_zero_of_lt hv']
private def test (q d h:ℕ) :Source q d →ₗ[ao] (Slot box q→ao) :=
  LinearMap.pi fun r =>
    if derivativeIndex r<h then
      (MvPolynomial.lcoeff ao (exp₂ r.2.val r.1.val)).comp (bY.toLinearMap.comp (Source q d).subtype)
    else 0
private theorem test_apply (q d h:ℕ) (P:Source q d) (r :Slot box q) :
    test q d h P r=if derivativeIndex r<h then
      (bY P.val).coeff (exp₂ r.2.val r.1.val) else 0:= by
  by_cases hr :derivativeIndex r<h <;> simp [test,hr,lcoeff]
private theorem slot_mem {q d:ℕ} (s :Slot box q) (hd:d≤ s.1.val+s.2.val) :
    exponent box q s∈masks q d:= by
  have hc:=s.1.isLt
  have hb:=s.2.isLt
  change s.1.val< min q (min 12 (27/2))+1 at hc
  change s.2.val< min (q-s.1.val) (27-2*s.1.val)+1 at hb
  simp [exponent,masks]
  omega
private theorem col_mem (q d h:ℕ) (s :Slot box q) :
    (cutMatrix box q d h).col s∈(test q d h).range := by
  classical
  by_cases hd:d≤ s.1.val+s.2.val
  · let P:Source q d :=
      ⟨monomial (exponent box q s) 1,(monomial_mem_restrictSupport ao).mpr (Or.inl (slot_mem s hd))⟩
    refine ⟨P,?_⟩
    have hP:bY P.val=(1+x)^s.2.val*(x+y)^s.1.val := by
      change bY (monomial _ _)= _
      rw [bY,aeval_monomial,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fin.prod_univ_three]
      simp [exponent]
    funext r
    rw [test_apply,hP,coeff_chart]
    change _=cutMatrix box q d h r s
    by_cases hr :derivativeIndex r<h <;> simp [cutMatrix,hd,hr]
  · refine ⟨0,?_⟩
    funext r
    simp [cutMatrix,hd,Matrix.col]
private theorem test_zero {q d h:ℕ} (P:Source q d)
    (hP:bY P.val∈restrictWeightedOrder wt h) :test q d h P=0:= by
  funext r
  rw [test_apply]
  by_cases hr :derivativeIndex r<h
  · rw [ite_eq_left hr]
    change (bY P.val).coeff (exp₂ r.2.val r.1.val)=0
    by_contra hn
    have he :=mem_restrictWeightedOrder.mp hP _ (MvPolynomial.mem_support_iff.mpr hn)
    have hw: (exp₂ r.2.val r.1.val).weight wt=derivativeIndex r := by
      have hb:exp₂ r.2.val r.1.val 1=r.2.val := by
        exact (Finsupp.cons_succ (0:Fin 1) _ _).trans Finsupp.single_eq_same
      rw [Finsupp.weight_eq_sum,Fin.sum_univ_two,hb]
      change r.1.val•2+r.2.val•1=r.2.val+2*r.1.val
      simp only [Nat.nsmul_eq_mul,Nat.mul_one]
      omega
    rw [hw] at he
    omega
  · exact ite_eq_right hr
theorem rank_le_cap (q d h:ℕ) (hq:q≤27) (hd:d≤q) :
    rankCut box q d h≤ cap box q d h:= by
  classical
  let:zAa ao (Source q d) :=finiteSource hq hd
  let f :=test q d h
  let v (j:Index q d h) :f.ker :=
    ⟨⟨_,witnessSource hq hd j⟩,LinearMap.mem_ker.mpr (test_zero _ (witnessOrder hq hd j))⟩
  have hv :LinearIndependent ao v :=
    LinearIndependent.of_comp ((Source q d).subtype.comp f.ker.subtype) (witnessIndependent hq hd)
  have hk :=hv.fintype_card_le_finrank
  have hn:=f.finrank_range_add_finrank_ker
  have hr :rankCut box q d h≤Module.finrank ao f.range := by
    rw [rankCut,Matrix.rank_eq_finrank_span_cols]
    exact Submodule.finrank_mono (Submodule.span_le.mpr fun _ ⟨s,hs⟩=>hs ▸ col_mem q d h s)
  rw [stock hq hd] at hn
  have hs :=count q d h
  rw [kept_eq] at hs
  omega
end
end qoRVxvd
end
