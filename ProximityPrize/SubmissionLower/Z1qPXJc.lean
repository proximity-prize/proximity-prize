import ProximityPrize.SubmissionLower.Zgvu91a
import ProximityPrize.SubmissionLower.ZXGF8Ec
import ProximityPrize.SubmissionLower.Z4nC3pd
import ProximityPrize.SubmissionLower.ZW8Nc6b
import ProximityPrize.SubmissionLower.ZQTNHBe
import ProximityPrize.SubmissionLower.ZMyjDge
import ProximityPrize.SubmissionLower.ZwDGfQd
import ProximityPrize.SubmissionLower.ZE3M1Qc
import ProximityPrize.SubmissionLower.Zfobjva
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, CommRing → za6, Field → zrb, Function.Injective → zq4, Ideal.span → zye, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.rename → zHw, MvPolynomial.ringHom_ext → zXT, Nat.add_le_add_left → z3b, Polynomial.X → z7y, Polynomial.map_map → zoi, Polynomial.map_mul → zNl, Polynomial.map_pow → z5m, PowerSeries → zpm, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, PowerSeries.isUnit_iff_constantCoeff → zRV, RingHom.comp_assoc → zxS
set_option maxHeartbeats 1200000
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qvWbALd
noncomputable section
open Polynomial

open cu (L)
open Cu
open E7 (CurvePlace poleOrder Tq)
open quN7Z4a (Sheet)
open qBajpRb (incl tupleMap cls ek yq)
open qRoCwuc (coord coeff disc genericDisc ConstantOddPart)
open qrsE1ie (discriminant geomSquare)
open scoped WithZero
variable {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
theorem scaled_disc (S:Sheet C₀ J 2 H T z s) :
  genericDisc S=C ((S.bY.scale :oO C₀)^2) *
   discriminant S.root.equation := by
 simp only [genericDisc,disc,discrim,Polynomial.map_sub,zNl,
  z5m,Polynomial.map_ofNat,qRoCwuc.coeff_generic,discriminant,
  Polynomial.C_ofNat,map_pow]
 ring
theorem not_constantOddPart (S:Sheet C₀ J 2 H T z s)
   (hn : ¬ geomSquare S.root.equation) : ¬ ConstantOddPart (genericDisc S) := by
 rintro ⟨a,Q,h⟩
 let u:oO C₀:=S.bY.scale
 let c:=u⁻¹^2*a
 have hh:discriminant S.root.equation=C c*Q^2 := by
   have h' := congrArg (fun f=>C (u⁻¹^2)*f) ((scaled_disc S).symm.trans h)
   change C (u⁻¹^2)*(C (u^2)*discriminant S.root.equation) =
     C (u⁻¹^2)*(C a*Q^2) at h'
   simpa only [c,← mul_assoc,← map_mul,← mul_pow,
     inv_mul_cancel₀ (show u≠0 from S.bY.scale.ne_zero),one_pow,map_one,one_mul] using h'
 let E :=AlgebraicClosure (oO C₀)
 let e :=algebraMap (oO C₀) E
 obtain ⟨r,hr⟩:=IsAlgClosed.exists_pow_nat_eq (e c) zero_lt_two
 apply hn
 refine ⟨C r*Q.map e,?_⟩
 rw [hh,zNl,Polynomial.map_C,z5m,mul_pow,← map_pow,hr]
private theorem coord_bound (S:Sheet C₀ J 2 H T z s)
   (w:CurvePlace L (oO C₀)) (j:Fin S.n) :
   w.value (S.bY.coordinate j)≤WithZero.exp (Tq w.value S.bY.coordinate :ℤ) := by
 have hb:poleOrder w.value (S.bY.coordinate j)≤Tq w.value S.bY.coordinate :=
   Finset.le_sup (s :=Finset.univ) (f := fun i=>poleOrder w.value (S.bY.coordinate i))
     (Finset.mem_univ j)
 by_cases h:S.bY.coordinate j=0
 · simp [h]
 apply (WithZero.log_le_iff_le_exp (w.value.ne_zero_iff.mpr h)).mp
 have hb' : ((poleOrder w.value (S.bY.coordinate j) :ℕ) :ℤ) ≤
     (Tq w.value S.bY.coordinate :ℤ) := by exact_mod_cast hb
 unfold poleOrder at hb'
 omega
theorem disc_bound (S:Sheet C₀ J 2 H T z s)
    (w:CurvePlace L (oO C₀)) (j:ℕ) :
    w.value ((genericDisc S).coeff j)≤WithZero.exp (2*(Tq w.value S.bY.coordinate :ℤ)) := by
  classical
  let q:=(disc S).coeff j
  let h:=Tq w.value S.bY.coordinate
  let B:ℤᵐ⁰:=WithZero.exp (h:ℤ)
  have hB:1≤B:=WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg _)
  have hbound:q.totalDegree≤2 :=qRoCwuc.disc_height S j
  have hc (a :L) :w.value (zT C₀ a)≤1 := by
    by_cases ha :a=0
    · simp [ha]
    · exact (w.on_constants a ha).le
  rw [genericDisc,coeff_map]
  change w.value (MvPolynomial.eval₂ (zT C₀) S.bY.coordinate q)≤_
  rw [MvPolynomial.eval₂_eq']
  apply w.value.map_sum_le
  intro d hd
  have hm:d.degree≤2 :=(Finset.le_sup (f :=Finsupp.degree) hd).trans hbound
  calc
    _ ≤ ∏ i,B^d i:= by
      rw [map_mul,map_prod,← one_mul (∏ i,B^d i)]
      exact mul_le_mul' (hc _) (Finset.prod_le_prod fun i _=> by
        rw [map_pow]
        exact pow_le_pow_left' (coord_bound S w i) _)
    _=B^d.degree := by rw [Finset.prod_pow_eq_pow_sum,← Finsupp.degree_eq_sum]
    _≤B^2 :=pow_le_pow_right' hB hm
    _ = _:= by rw [show B= _ from rfl,← WithZero.exp_nsmul]; congr 1
private theorem incl_tupleMap (S:Sheet C₀ J 2 H T z s) :
   (incl S.bY).comp (tupleMap S.bY).toRingHom=coord S:= by
 apply zXT
 · intro a
   change incl S.bY (cls S.bY (zHw Sum.inr _))= _
   rw [qBajpRb.incl_cls]
   simp [ek,coord]
 · intro i
   change incl S.bY (cls S.bY (zHw Sum.inr _))= _
   rw [qBajpRb.incl_cls]
   simp [ek,coord]
private theorem atMark_tupleMap (S:Sheet C₀ J 2 H T z s) (γ:T) :
   (yq S.bY (z γ) (S.parameter γ) (S.onBase γ γ.property)).toRingHom.comp
     (tupleMap S.bY).toRingHom=zY9 (S.parameter γ) := by
 apply zXT
 · intro a
   change yq S.bY (z γ) (S.parameter γ) (S.onBase γ γ.property)
     (cls S.bY (zHw Sum.inr _))= _
   rw [qBajpRb.atMark_cls]
   simp
 · intro i
   change yq S.bY (z γ) (S.parameter γ) (S.onBase γ γ.property)
     (cls S.bY (zHw Sum.inr _))= _
   rw [qBajpRb.atMark_cls]
   simp
def localDisc (S:Sheet C₀ J 2 H T z s) (M:MarkedPlaces S) (γ:T) :
    ((M.place γ).value.valuationSubring)[X] :=
  (disc S).map ((M.lift γ).comp (tupleMap S.bY).toRingHom)
theorem localDisc_generic (S:Sheet C₀ J 2 H T z s) (M:MarkedPlaces S) (γ:T) :
   (localDisc S M γ).map (M.place γ).value.valuationSubring.toSubring.subtype =
     genericDisc S:= by
 rw [localDisc,zoi,← zxS,M.include_lift,incl_tupleMap]
 rfl
theorem localDisc_fibre (S:Sheet C₀ J 2 H T z s) (M:MarkedPlaces S) (γ:T) :
  (localDisc S M γ).map (M.residue γ)=(disc S).map (zY9 (S.parameter γ)) := by
 rw [localDisc,zoi,← zxS,M.cqr,atMark_tupleMap]
end
end qvWbALd
end
section
namespace qHJDQEb
noncomputable section
open scoped Classical
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index jo block aMp spectral)
def zeroSlot (d D W:ℕ) :Slot d D W:=⟨(0,0),by simp⟩
def IsFree {d D W:ℕ} : Index d D W→Prop
 | .inl i=>i≠zeroSlot d D W
 | .inr (.inl i)=>i≠zeroSlot d D W
 | .inr (.inr i)=>i≠zeroSlot (d-1) D (W-D)
abbrev Free (d D W:ℕ) := {i:Index d D W // IsFree i}
abbrev IncRing (d D W:ℕ) :=MvPolynomial (Bool ⊕ Free d D W) L
abbrev Incident (d D W:ℕ) :=FractionRing (IncRing d D W)
def coordX (d D W:ℕ) :IncRing d D W:=z9v (.inl false)
def coordY (d D W:ℕ) :IncRing d D W:=z9v (.inl true)
def raw {d D W:ℕ} (i:Index d D W) :IncRing d D W :=
 if h:IsFree i then z9v (.inr ⟨i,h⟩) else 0
def adjust {F:Type} [za6 F] {d D W:ℕ}
    (u:Slot d D W→F) (x y :F) (i:Slot d D W) :F :=
  u i - if i=zeroSlot d D W then aMp u x y else 0
def incCoeff {d D W:ℕ} : Index d D W→ IncRing d D W
 | .inl i=>adjust (fun j=>raw (.inl j)) (coordX d D W) (coordY d D W) i
 | .inr (.inl i)=>adjust (fun j=>raw (.inr (.inl j))) (coordX d D W) (coordY d D W) i
 | .inr (.inr i)=>adjust (fun j=>raw (.inr (.inr j))) (coordX d D W) (coordY d D W) i
def incidence (d D W:ℕ) :jo d D W →ₐ[L] IncRing d D W :=
 MvPolynomial.aeval incCoeff
def pointX (d D W:ℕ) :Incident d D W:=algebraMap (IncRing d D W) _ (coordX d D W)
def pointY (d D W:ℕ) :Incident d D W:=algebraMap (IncRing d D W) _ (coordY d D W)
def atInc {d D W:ℕ} (i:Index d D W) :Incident d D W :=
 algebraMap (IncRing d D W) _ (incCoeff i)
def pairField (d D W:ℕ) (k :Fin 3) :IntermediateField L (Incident d D W) :=
 IntermediateField.adjoin L (atInc '' {i:Index d D W | block i≠k})
def pointField (d D W:ℕ) (k :Fin 3) :
    IntermediateField (pairField d D W k) (Incident d D W) :=
  IntermediateField.adjoin (pairField d D W k) {pointX d D W}
def projectedCoeff {d D W:ℕ} (i : {i:Index d D W // i≠spectral d D W}) :
    Incident d D W:=atInc i.val
def blockWeight {d D W:ℕ} (k :Fin 3) (i:Index d D W) :ℕ :=
 if block i=k then 1 else 0
end
end qHJDQEb
end
section
namespace qnSUPza
noncomputable section
open cu (L)
open qAW6lac (Index aMp)
abbrev Germ (B:Type) [zrb B] :=zpm (AlgebraicClosure B)
def motion {B:Type} [zrb B] [zZE L B] (a :B) (z :L) :Germ B :=
  PowerSeries.C (algebraMap B (AlgebraicClosure B) a) +
    PowerSeries.C (algebraMap B (AlgebraicClosure B) (algebraMap L B z))*PowerSeries.X
def branchValue {B:Type} [zrb B] [zZE L B] {d D W:ℕ}
    (α:Index d D W→B) (δ:Index d D W→L) (xy :Germ B×Germ B) :Germ B :=
  aMp (fun i=>motion (α (.inr (.inr i))) (δ (.inr (.inr i)))) xy.1 xy.2
end
end qnSUPza
end
end
section
section
set_option autoImplicit true
namespace qTLMB9a
theorem proof :qLXroAb.c1 :=qd4QhDd.proof
end qTLMB9a
end
section
set_option autoImplicit true
namespace qaAXjzc
theorem proof :q0mTRkc.c1 :=qTLMB9a.proof
end qaAXjzc
end
section
set_option autoImplicit true
namespace quA006b
theorem proof :q0mTRkc.c2 :=qU4m8Td.proof
end quA006b
end
section
set_option autoImplicit true
namespace q6s3Ofd
theorem proof :qRoCwuc.c2 := by
 intro A _ ρ π hρ hπ P Q m n D hm hn hD hd hp hq
 have :Nontrivial A:=ρ.domain_nontrivial
 exact qvWbALd.cfp ρ π hρ hπ P Q hm hn hD hd hp hq
end q6s3Ofd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qlbihNe
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing
open P5 (p)
open qqV3gre (aQ PhysicalField EC)
open qCtoYwb
open qcuqT2c (TamePlace)
open scoped WithZero
abbrev parameter (π:tu) [Fact (Irreducible π)] :Local π:=algebraMap tu (Local π) π
abbrev aVF (π:tu) [Fact (Irreducible π)] :Local π :=
 algebraMap tu (Local π) (C seedScalar)
theorem local_base (π:tu) [Fact (Irreducible π)] (y :EC) (b:tu) :
   localIn π y (algebraMap tu (Local π) b)=baseIn y b:= by
 change algebraMap PhysicalField (Simple y) (algebraMap (Local π) PhysicalField
     (algebraMap tu (Local π) b))=algebraMap PhysicalField (Simple y) (algebraMap tu PhysicalField b)
 rw [← zG3 tu (Local π) PhysicalField]
private theorem residue_not_power (π:tu) [hπ:Fact (Irreducible π)] (hs :π.Separable)
   (b:ResidueField (Local π)) :b^p≠residue _ (aVF π) := by
 have hroot :IsSeparable aQ (AdjoinRoot.root π) := by
   change (minpoly aQ (AdjoinRoot.root π)).Separable
   rw [AdjoinRoot.minpoly_root hπ.out.ne_zero]
   exact hs.mul_unit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
     (inv_ne_zero (leadingCoeff_ne_zero.mpr hπ.out.ne_zero))))
 have hsep:=(IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
   aQ (AdjoinRoot π)).2 hroot
 rw [IntermediateField.adjoin_root_eq_top,IntermediateField.isSeparable_top] at hsep
 let:zw7 aQ (AdjoinRoot π) :=hsep
 let e :AdjoinRoot π ≃+* ResidueField (Local π) :=
   IsLocalization.AtPrime.equivQuotMaximalIdeal (primeIdeal π) (Local π)
 have he :e (algebraMap aQ (AdjoinRoot π) seedScalar)=residue _ (aVF π) :=
   IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk _ _ _
 intro hb
 let d:=e.symm b
 have hd:d^p=algebraMap aQ (AdjoinRoot π) seedScalar := by
   apply e.injective
   simpa only [d,map_pow,RingEquiv.apply_symm_apply,he] using hb
 let:ExpChar aQ p:=expChar_of_injective_ringHom
   (((algebraMap cu.L aQ).comp (algebraMap P5.K cu.L))).injective p
 have hbasis :=IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable
   aQ (AdjoinRoot π) (Algebra.IsSeparable.isSeparable aQ d) p
 have hd' : d^p∈(⊥ : IntermediateField aQ (AdjoinRoot π)) :=
   IntermediateField.mem_bot.mpr ⟨seedScalar,hd.symm⟩
 rw [IntermediateField.adjoin_simple_eq_bot_iff.mpr hd'] at hbasis
 have hm:=hbasis ▸ IntermediateField.mem_adjoin_simple_self aQ d
 obtain ⟨a,ha⟩:=IntermediateField.mem_bot.mp hm
 exact seed_not_power a ((algebraMap aQ (AdjoinRoot π)).injective (by rw [map_pow,ha,hd]))
private theorem integral_of_tame_values_aux (A F E :Type)
   [za6 A] [IsDomain A] [IsDiscreteValuationRing A] [zrb F] [zrb E]
   [zZE A F] [IsFractionRing A F] [zZE A E] [zZE F E] [zsf A F E]
   [zw7 F E] [zAa F E]
   (hdeg:zsE F E<p) (w:E) {z t:A} (hz :IsUnit z)
   (hm:maximalIdeal A=zye {t}) (ht0:algebraMap A E t≠0)
   (hn : ∀ b:ResidueField A,b^p≠residue A z)
   (hw : ∀ v :Valuation E ℤᵐ⁰,TamePlace v (algebraMap A E z) (algebraMap A E t) →
     (∀ a :A,v (algebraMap A E a)≤1)→v w≤1) :IsIntegral A w:= by
 let B:=integralClosure A E
 let:zsf A B E :=zsL (fun _=>rfl)
 let:Module.IsTorsionFree A E := .trans_faithfulSMul A F E
 let:Module.Free A B:=IsIntegralClosure.module_free A F E B
 let:zAa A B:=IsIntegralClosure.finite A F E B
 let:IsDedekindDomain B:=IsIntegralClosure.isDedekindDomain A F E B
 let:IsFractionRing B E :=integralClosure.isFractionRing_of_finite_extension F E
 let:Algebra.IsIntegral A B:=IsIntegralClosure.isIntegral_algebra A E
 have hB:zsE A B<p:=(IsIntegralClosure.rank A F E B).symm ▸ hdeg
 have hvals (q:HeightOneSpectrum B) :q.valuation E w≤1 := by
   let:q.asIdeal.LiesOver (maximalIdeal A) :=
     ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)).symm⟩
   have ht0' : algebraMap A B t≠0:= fun h=>ht0 (by rw [zG3 A B E,h,map_zero])
   have hcoord (a :A) :algebraMap B E (algebraMap A B a)=algebraMap A E a :=
     (zG3 A B E a).symm
   apply hw (q.valuation E)
   · rw [← hcoord,← hcoord]
     exact qGA3mAd.tame_of_adic q hm ht0' hz prime_p hB hn
   · intro a
     rw [← hcoord,q.valuation_of_algebraMap]
     exact q.intValuation_le_one _
 obtain ⟨b,rfl⟩:=HeightOneSpectrum.mem_integers_of_valuation_le_one (R:=B) E w hvals
 exact b.property
theorem integral_of_tame_values (π:tu) [hπ:Fact (Irreducible π)] (hs :π.Separable)
   (y :EC) (hy :IsSeparable PhysicalField y)
   (hdeg:zsE PhysicalField (Simple y)<p) (w:Simple y)
   (hw : ∀ v :Valuation (Simple y) ℤᵐ⁰,TamePlace v (a8p y) (baseIn y π) →
     (∀ a :Local π,v (localIn π y a)≤1)→v w≤1) :IntegralAt π y w:= by
 let A:=Local π
 let E :=Simple y
 let:zZE A E :=(localIn π y).toAlgebra
 let:zsf A PhysicalField E :=zsL (fun _=>rfl)
 let:zw7 PhysicalField E :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hy
 let:zAa PhysicalField E :=IntermediateField.finiteDimensional_adjoin
   (fun b hb=>(Set.mem_singleton_iff.mp hb).symm ▸ hy.isIntegral)
 let:IsDiscreteValuationRing A :=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain tu (aDm π).ne_bot A
 have hm:maximalIdeal A=zye {parameter π} := by
   rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (primeIdeal π) A]
   change Ideal.map _ (zye {π})= _
   rw [Ideal.map_span,Set.image_singleton]
 have hz :IsUnit (aVF π) :=
   IsUnit.map ((algebraMap tu A).comp C)
     (isUnit_iff_ne_zero.mpr (fun h=>seed_not_power 0 (by simp [h,prime_p.ne_zero])))
 have ht0:algebraMap A E (parameter π)≠0:= by
   change localIn π y (parameter π)≠0
   rw [local_base]
   exact (map_ne_zero_iff _ (baseIn_injective y)).2 hπ.out.ne_zero
 have hi:IsIntegral A w:=integral_of_tame_values_aux A PhysicalField E
   hdeg w hz hm ht0 (residue_not_power π hs) (by
     intro v hv hvA
     apply hw v _ hvA
     change TamePlace v (baseIn y (C seedScalar)) (baseIn y π)
     rw [← local_base π y (C seedScalar),← local_base π y π]
     exact hv)
 exact hi
end
end qlbihNe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qlbihNe
noncomputable section
open P5 (K p)
open cu (L)
open qqV3gre (aQ)
open qCtoYwb
open qcuqT2c (TamePlace)
open scoped WithZero
private theorem derive_pow {E :Type} [zrb E] (D:Derivation ℤ E E)
   (x b:E) (h:D x=x*b) (n:ℕ) :D (x^n)=x^n*((n:E)*b) := by
 cases n with
 | zero=>simp
 | succ n =>
   rw [D.leibniz_pow]
   simp only [nsmul_eq_mul,smul_eq_mul,Nat.succ_sub_one,h,pow_succ x n]
   ring
private theorem tame_le {E :Type} [zrb E] [CharP E p] (D:Derivation ℤ E E)
   (v :Valuation E ℤᵐ⁰) {z t w r s :E} (hv :TamePlace v z t)
   (hr :D z=z*r) (hs :D t=t*s) (hvr :v r≤1) (hvs :v s≤1)
   (c:Fin p→Fin p→E)
   (hw:w = ∑ j,∑ i,c j i^p*z^(i:ℕ)*t^(j:ℕ)) :v (D w)≤v w:= by
 have hpow (a :E) :D (a^p)=0:= by
   rw [D.leibniz_pow,← Nat.cast_smul_eq_nsmul E,CharP.cast_eq_zero,zero_smul]
 have hn (n:ℕ) :v (n:E)≤1 := by
   induction n with
   | zero=>simp
   | succ n ih =>
     rw [Nat.cast_succ]
     exact (v.map_add _ _).trans (max_le ih (by rw [map_one]))
 rw [hw,map_sum]
 apply v.map_sum_le
 intro j _
 rw [map_sum]
 apply v.map_sum_le
 intro i _
 refine le_trans ?_ (qbY56ta.proof v hv c i j)
 have hterm :D (c j i^p*z^(i:ℕ)*t^(j:ℕ)) =
     (c j i^p*z^(i:ℕ)*t^(j:ℕ))*(((i:ℕ) :E)*r+((j:ℕ) :E)*s) := by
   simp only [D.leibniz,hpow,derive_pow D z r hr,derive_pow D t s hs,
     smul_eq_mul,mul_zero,add_zero]
   ring
 have h:v (((i:ℕ) :E)*r+((j:ℕ) :E)*s)≤1 := by
   apply (v.map_add _ _).trans
   simpa only [map_mul] using
     (max_le (mul_le_one' (hn (i:ℕ)) hvr) (mul_le_one' (hn (j:ℕ)) hvs))
 rw [hterm,map_mul]
 exact mul_le_of_le_one_right' h
theorem proof :qCtoYwb.c2 := by
 intro π hπ y hsep hy hdeg D hD hT w hw
 let f :K →+* Simple y :=(baseIn y).comp (Polynomial.C.comp
   ((algebraMap L aQ).comp (algebraMap K L)))
 let:CharP (Simple y) p:=charP_of_injective_ringHom f.injective p
 apply integral_of_tame_values π hsep y hy hdeg
 intro v hv hV
 obtain ⟨r,hr⟩:=hD (aVF π)
 obtain ⟨s,hs⟩:=hT
 let a :=D (a8p y)/a8p y
 have hz :a8p y≠0:=v.ne_zero_iff.mp (hv.seed_unit.trans_ne one_ne_zero)
 have ha :v a≤1 := by
   change v (D (a8p y)/a8p y)≤1
   rw [v.map_div,hv.seed_unit,div_one,
     show a8p y=localIn π y (aVF π) from (local_base π y _).symm,hr]
   exact hV r
 have hza :D (a8p y)=a8p y*a := by
   rw [show a=D (a8p y)/a8p y from rfl,mul_comm,div_mul_cancel₀ _ hz]
 obtain ⟨c,hc⟩:=cLN π hsep y hy w
 rw [v.map_div]
 exact (div_le_one₀ (v.pos_iff.mpr hw)).2
   (tame_le D v hv hza hs ha (hV s) c hc)
end
end qlbihNe
end
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qaJ7jxd
noncomputable section
open Polynomial qAjZDhd
def c1 :Prop :=TameLog
def c2 :Prop :=
  TameLog →
    ∀ (k :Type) [zrb k] (p:ℕ) [CharP k p] (M:LocalMark k p) (b:Bool)
      (q: (kq k)[X]),Irreducible q→q∣toFrac M.r →
        ∀ i:ℕ,∃ e : (kq k)[X],¬q∣e ∧
          toFrac (denom M)∣e*toFrac ((Fr M b).coeff i)
private theorem dvd_of_local {R:Type} [CommMonoidWithZero R] [UniqueFactorizationMonoid R] {d r v :R} {n:ℕ} (hd:d≠0) (hs :d∣r^n)
    (h : ∀ q:R,Irreducible q→q∣r → ∃ e :R,¬q∣e∧d∣e*v) :d∣v := by
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hd).mpr
  intro q hq
  apply emultiplicity_le_emultiplicity_iff.mpr
  intro j hj
  by_cases h0:j=0
  · simp [h0]
  have hqpow:q∣q^j:= by
    simpa only [pow_one] using pow_dvd_pow q (Nat.one_le_iff_ne_zero.mpr h0)
  have hqd:=hqpow.trans hj
  obtain ⟨e,he,hv⟩:=h q hq.irreducible (hq.dvd_of_dvd_pow (hqd.trans hs))
  exact hq.pow_dvd_of_dvd_mul_left j he (hj.trans hv)
variable {k :Type} [zrb k] {p:ℕ} [CharP k p]
private theorem denom_reduce (M:LocalMark k p) :reduce (denom M)≠0:= by
  rw [denom_eq,map_mul,map_pow,map_neg,map_one]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) M.branch_nonzero
private theorem primitive_denom (M:LocalMark k p) : (denom M).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro s hs
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  obtain ⟨F,hF⟩:=hs
  have hm:reduce (denom M)=reduce (C s*F) :=congrArg reduce hF
  apply denom_reduce M
  simpa [reduce,hz] using hm
private theorem denom_support (M:LocalMark k p) :
    ∃ n:ℕ,toFrac (denom M)∣toFrac M.r^n:= by
  obtain ⟨n,hn⟩:=M.support
  refine ⟨n,dvd_trans (map_dvd toFrac ?_) hn⟩
  rw [denom_eq]
  have hs :IsUnit (-1 :Physical k) :=(isUnit_one :IsUnit (1 :Physical k)).neg
  exact (hs.pow M.g).mul_left_dvd.mpr dvd_rfl
theorem of_children (h1 :c1) (h2 :c2) :qAjZDhd.c1 := by
  classical
  intro k inst p inst' M b
  have hd:denom M≠0:= fun h=>denom_reduce M (by rw [h,map_zero])
  have hfrac:zq4 (toFrac (k :=k)) :=
    Polynomial.map_injective _ (IsFractionRing.injective _ _)
  have hdF:toFrac (denom M)≠0 :=
    fun h=>hd (hfrac (h.trans (map_zero _).symm))
  obtain ⟨n,hn⟩:=denom_support M
  have hc (i:ℕ) :denom M∣(Fr M b).coeff i :=
    (primitive_denom M).dvd_of_fraction_map_dvd_fraction_map
      (dvd_of_local hdF hn (fun q hq hr=>h2 h1 k p M b q hq hr i))
  obtain ⟨Q,hQ⟩:=(C_dvd_iff_dvd_coeff _ _).mpr hc
  have hdL:bL9 (denom M)≠0 :=
    fun h=>hd (splitMap_injective (h.trans (map_zero _).symm))
  have he :RootProduct M (M.numerator b) Q:= by
    have heq :=congrArg (Polynomial.map bL9) hQ
    rw [zNl,map_C] at heq
    unfold RootProduct
    exact mul_left_cancel₀ (C_ne_zero.mpr hdL) (heq.symm.trans (scaled_product M b hdL))
  refine ⟨Q,splitMap_injective.monic_map_iff.mpr ?_,he⟩
  rw [he]
  exact monic_multiset_prod_of_monic _ _ (fun y _=>monic_X_sub_C _)
end
end qaJ7jxd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_6
noncomputable section
open MvPolynomial Finset
open P5 (K)
open quN7Z4a (Z7)
open qL2osVa (Cut MarkedSheet)
open cu (L FX jz)
open DQ (jY)
open Cu
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
open private gn5 from ProximityPrize.SubmissionLower.ZFFuWqa
def c1 :Prop :=
  ∀ (n:ℕ) (B:Ideal (Gc n)) (seed :Bool),
    let E :=jY (blockSize n seed)
    let J:=gN B E
    ∃ N :ℕ,∀ a b:ℕ,N≤a→N≤b →
      ∀ x :MvPolynomial (bzm n) E ⧸ J,
        Ideal.Quotient.mk J (aEL (bml n seed))*x ∈
          Box J (a+seedStep seed) (b+coeffStep seed)→x∈Box J a b
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] {J g n}
    {R:wJ C₀ J g} (A:yI R n),
    let S:=Section (EF A) (Sum.inl:Fin 2→bzm n)
    zAa (jY 2) S∧zsE (jY 2) S≤C₀.totalDegree
private theorem iterate_rank (f :ℕ→ℕ) (d N k :ℕ)
    (hs : ∀ i≥N,f (i+1)≤f i+d) :
    f (N+k)≤f N+k*d:= by
  induction k with
  | zero=>simp
  | succ k ih =>
    rw [← Nat.add_assoc,Nat.succ_mul]
    exact (hs (N+k) (Nat.le_add_right _ _)).trans (by omega)
private abbrev toGraph {n:ℕ} : Cut n →+* Gc n :=
  MvPolynomial.map (algebraMap L FX)
private theorem chart_generic {C₀:sQ} [Fact (Irreducible C₀)]
    (C:MarkedSheet C₀) :
    (W8 C.sheet.bY).comp toGraph=(Mu C₀).comp C.bee := by
  apply zXT
  · intro c
    simp only [RingHom.comp_apply,toGraph,MvPolynomial.map_C,W8,
      MarkedSheet.bee,MvPolynomial.eval₂Hom_C]
    exact b1t C₀ c
  · intro i
    cases i <;> simp [toGraph,W8,MarkedSheet.bee]
private theorem map_pair {F E :Type} [Semiring F] [Semiring E]
    (f :F →+* E) (z :F) (p:ℕ) :
    (![f z,(f z)^p] :Fin 2→E)=f ∘ ![z,z^p] := by
  funext i
  fin_cases i
  · rfl
  · exact (map_pow f z p).symm
private theorem base_mark_eq {n:ℕ} (z :K1.K) (t:Fin n→L) :
    aCn z t=(algebraMap L FX) ∘ Sum.elim (Z7 z) t:= by
  funext i
  cases i with
  | inl i =>
    change (![jz z,(jz z)^K1.p] :Fin 2→FX) i =
      algebraMap L FX (Z7 z i)
    rw [gn5]
    exact congrFun (map_pair (algebraMap L FX) (algebraMap K1.K L z) K1.p) i
  | inr i=>rfl
private theorem chart_mark {C₀:sQ} [Fact (Irreducible C₀)]
    (C:MarkedSheet C₀) (γ:K) (q:Cut C.sheet.n) :
    aeval (aCn (C.z γ) (C.sheet.parameter γ)) (toGraph q) =
      algebraMap L FX (C.markedCut γ q) := by
  change eval (aCn (C.z γ) (C.sheet.parameter γ)) (toGraph q) =
    algebraMap L FX (eval (Sum.elim (Z7 (C.z γ)) (C.sheet.parameter γ)) q)
  rw [toGraph,MvPolynomial.eval_map,MvPolynomial.eval₂_comp,base_mark_eq]
theorem of_children (h1 :c1) (h2 :c2) :qL2osVa.c6:= by
  classical
  intro C₀ _ C q u v hq hproper
  let n:=C.sheet.n
  let B:=EF C.sheet.bY
  let V:=C.smoothMarks.filter fun γ=>C.markedCut γ q=0
  let pt:V→zeroLocus FX B:= fun i=>⟨aCn (C.z i) (C.sheet.parameter i),
    C.sheet.onBase i ((filter_subset _ _) (mem_filter.mp i.property).1)⟩
  have hpt:zq4 pt:= by
    intro i j hij
    have h:=congrArg (fun f :zeroLocus FX B=>f.val (Sum.inl 0)) hij
    apply Subtype.ext
    exact C.injective ((filter_subset _ _) (mem_filter.mp i.property).1)
      ((filter_subset _ _) (mem_filter.mp j.property).1) (jz.injective h)
  let e :=zeroLocusPointHom B ∘ pt
  have he :zq4 e :=(zeroLocusPointHom_injective B).comp hpt
  let:B.IsPrime :=RingHom.ker_isPrime (W8 C.sheet.bY)
  have hqB:toGraph q∉B:= by
    intro h
    have hz :=RingHom.mem_ker.mp h
    change ((W8 C.sheet.bY).comp toGraph) q=0 at hz
    rw [chart_generic] at hz
    exact hproper ((Mu C₀).injective (hz.trans (map_zero _).symm))
  have hdeg:toGraph q∈BoxPoly FX n u v :=
    fun m hm=>hq m (support_map_subset _ _ hm)
  obtain ⟨Nm,hm⟩:=rank_marks e he (toGraph q) u v hdeg hqB (fun i=> by
    change aeval (pt i).val (toGraph q)=0
    rw [chart_mark,(mem_filter.mp i.property).2,map_zero])
  obtain ⟨Ns,hs⟩:=h1 n B true
  obtain ⟨Nc,hc⟩:=h1 n B false
  obtain ⟨hsfinite,hslen⟩:=h2 C₀ C.sheet.bY
  let:zAa (jY 2) (Section B (Sum.inl:Fin 2→bzm n)) :=hsfinite
  let:zAa (jY n) (Section B (Sum.inr :Fin n→bzm n)) :=
    C.sheet.height.finite
  let N :=max Nm (max Ns Nc)
  have hn:Nm≤N :=le_max_left _ _
  have hns :Ns≤N :=(le_max_left _ _).trans (le_max_right _ _)
  have hnc:Nc≤N :=(le_max_right _ _).trans (le_max_right _ _)
  let f := fun a b=>zsE FX (Box B a b)
  have stepS (a :ℕ) (ha :N≤a) :f (a+1) N≤f a N+C₀.totalDegree := by
    have h:=cev (B:=gN B (jY 2))
      (aEL (Sum.inl:Fin 2→bzm n)) a N (a+1) N
      (hs a N (hns.trans ha) hns)
    rw [box_rank_extend,box_rank_extend] at h
    exact h.trans (z3b hslen _)
  have stepC (b:ℕ) (hb:N≤b) :f (N+u) (b+1)≤f (N+u) b+C.H := by
    have h:=cev (B:=gN B (jY n))
      (aEL (Sum.inr :Fin n→bzm n)) (N+u) b (N+u) (b+1)
      (hc (N+u) b (hnc.trans (Nat.le_add_right _ _)) (hnc.trans hb))
    rw [box_rank_extend,box_rank_extend] at h
    exact h.trans (z3b C.sheet.height.length _)
  have hS:=iterate_rank (fun a=>f a N) C₀.totalDegree N u stepS
  have hC:=iterate_rank (f (N+u)) C.H N v stepC
  have hM:=hm N N hn hn
  rw [Fintype.card_coe] at hM
  change f N N+V.card≤f (N+u) (N+v) at hM
  change V.card≤_
  omega
end
end P5_7_3_3_4_1_6
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7R
noncomputable section
open Polynomial qL2osVa
open P5_7_3_3_4_1_7 (targetDen det localEquation LocalGuard ZeroJet seedFibre expand markedJet markedSeparant arcEval bfj physicalCentre)
open private arc_marked arc_zero hit_den coeff_local unitOfInitial unitLead rationalValue from ProximityPrize.SubmissionLower.Zfobjva
open P5 (K p)
open cu (L)
open Cu (sQ)
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀) (x :L) (r :Target),
    2≤C.g→C.g<p→C.bee (targetDen r)≠0 →
    ∃ a :L,C.bee (((normalized C x r a).coeff C.g).coeff 0)≠0 ∧
      (det (normalized C x r a) C.g).map C.bee≠0
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀)
    (x a :L) (r :Target),2≤C.g → ∀ d j:ℕ,
      MixedDegree ((det (normalized C x r a) C.g).coeff d)
        ((2*C.g-1)*C.g*r.cost) (2*C.g-1) ∧
      MixedDegree (((normalized C x r a).coeff j).coeff 0) (C.g*r.cost) 1
def c3:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (C:MarkedSheet C₀) (A:ArcFamily C)
    (x a :L) (r :Target) (γ:K) (hγ:γ∈C.smoothMarks),
    C.simple γ→ r.hit (C:=C) x γ →
    let f :=localEquation (A ⟨γ,hγ⟩) (normalized C x r a)
    ∃ s :Series,zbO s=0∧(seedFibre f).eval s=0 ∧
      ∀ v :Series,ZeroJet f s v → ∃ w:Series,
        zbO w=r.slope A γ ∧
        expand x (markedJet (A ⟨γ,hγ⟩))+expand x (markedSeparant C γ)*w=0
variable {C₀:sQ} [Fact (Irreducible C₀)]
theorem normalized_degree (C:MarkedSheet C₀) (x :L) (r :Target) (a :L) :
    (normalized C x r a).natDegree≤C.g:= by
  unfold normalized
  dsimp only
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i≤C.g:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hv (u: (Cut C.sheet.n)[X]) : (1+Polynomial.C u*z7y).natDegree≤1 := by
    exact (natDegree_add_le _ _).trans (max_le (by simp)
      ((natDegree_C_mul_le _ _).trans (by simp)))
  have hn (u w: (Cut C.sheet.n)[X]) :
      (Polynomial.C u*(1+Polynomial.C w*z7y)+Polynomial.X).natDegree≤1 := by
    exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans (hv w)) (by simp))
  exact natDegree_mul_le.trans (by
    refine (add_le_add (natDegree_C_mul_le _ _ |>.trans (natDegree_pow_le_of_le _ (hn _ _)))
      (natDegree_pow_le_of_le _ ((natDegree_C_mul_le _ _).trans (hv _)))).trans ?_
    simpa only [mul_one] using (Nat.add_sub_of_le hi').le)
private theorem local_guard {C:MarkedSheet C₀} {γ:K}
    (x a :L) (r :Target) (d j:ℕ)
    (hg:0<C.g)
    (hl:C.bee (((normalized C x r a).coeff C.g).coeff 0)≠0)
    (hd : ∀ i<d,C.bee ((det (normalized C x r a) C.g).coeff i)=0)
    (hj : ∀ i<j,C.bee (((normalized C x r a).coeff i).coeff 0)=0)
    (A:Arc C γ)
    (h₁:C.markedCut γ ((det (normalized C x r a) C.g).coeff d)≠0)
    (h₂:C.markedCut γ (((normalized C x r a).coeff j).coeff 0)≠0) :
    LocalGuard (localEquation A (normalized C x r a)) C.g d j:= by
  let F:=normalized C x r a
  let f :=localEquation A F
  have hf :f.natDegree≤C.g:=natDegree_map_le.trans (normalized_degree C x r a)
  have hcoeff (i k :ℕ) :z2o k (f.coeff i)=arcEval A ((F.coeff i).coeff k) := by
    change z2o k ((F.map (bfj A)).coeff i)= _
    rw [coeff_map,coeff_local]
  have hdet (i:ℕ) :z2o i (det f C.g)=arcEval A ((det F C.g).coeff i) := by
    change z2o i
      ((F.map (bfj A)).resultant (F.map (bfj A)).derivative C.g (C.g - 1))= _
    rw [derivative_map,resultant_map_map,coeff_local]
    rfl
  have hlead:zbO (f.coeff C.g)≠0:= by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,hcoeff]
    exact fun hz=>hl ((arc_zero A).mp hz)
  obtain ⟨u,hu,he⟩:=unitOfInitial (det f C.g) d
    (fun i hi=> by rw [hdet,arc_zero]; exact hd i hi)
    (by rw [hdet,zRV,arc_marked,isUnit_iff_ne_zero]; exact h₁)
  refine ⟨hf,unitLead hg hf hlead hu he,⟨u,hu,he⟩,?_,?_⟩
  · intro i hi
    rw [physicalCentre,← PowerSeries.coeff_zero_eq_constantCoeff,hcoeff,arc_zero]
    exact hj i hi
  · rw [physicalCentre,← PowerSeries.coeff_zero_eq_constantCoeff,hcoeff,
      zRV,arc_marked,isUnit_iff_ne_zero]
    exact h₂
private theorem first_nonzero {S:Type*} [Semiring S] (f :S[X]) (h:f≠0) :
    ∃ j,f.coeff j≠0 ∧ ∀ i<j,f.coeff i=0:= by
  classical
  have he : ∃ j,f.coeff j≠0:=⟨_,leadingCoeff_ne_zero.mpr h⟩
  exact ⟨Nat.find he,Nat.find_spec he,fun _ hi=>not_not.mp (Nat.find_min he hi)⟩
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (hlocal:P5_7_3_3_4_1_7.c2) :
    qL2osVa.c7:= by
  intro C₀ inst C A x r hg hp
  by_cases hn:C.bee (targetDen r)=0
  · have hunit (u v :ℕ) :MixedDegree (1 :Cut C.sheet.n) u v := by
      intro e he
      obtain rfl :e=0:= by simpa using he
      simp
    refine ⟨1,1,hunit _ _,hunit _ _,by simp,by simp,?_⟩
    intro γ hγ _ hhit _ _
    have ha :=(arc_zero (A ⟨γ,hγ⟩)).mpr hn
    have hm:=arc_marked (A ⟨γ,hγ⟩) (targetDen r)
    rw [ha,map_zero] at hm
    exact (hit_den hhit hm.symm).elim
  · obtain ⟨a,hlead,hdet⟩:=h1 C₀ C x r hg hp hn
    let F:=normalized C x r a
    let e :=(Polynomial.evalRingHom (0:Cu.oO C₀)).comp
      (Polynomial.mapRingHom C.bee)
    have hcoeff (i:ℕ) : (F.map e).coeff i=C.bee ((F.coeff i).coeff 0) := by
      rw [coeff_map]
      simp [e,← coeff_zero_eq_eval_zero]
    have hcentre :F.map e≠0:= by
      intro hz
      exact hlead (by rw [← hcoeff,hz,coeff_zero])
    obtain ⟨d,hd,hd₀⟩:=first_nonzero _ hdet
    simp only [coeff_map] at hd hd₀
    obtain ⟨j,hj,hj₀⟩:=first_nonzero _ hcentre
    simp only [hcoeff] at hj hj₀
    obtain ⟨hdeg₁,hdeg₂⟩:=h2 C₀ C x a r hg d j
    refine ⟨_,_,hdeg₁,hdeg₂,hd,hj,?_⟩
    intro γ hγ hs hhit h₁ h₂
    let f :=localEquation (A ⟨γ,hγ⟩) F
    obtain ⟨s,hzero,hroot,hv⟩:=h3 C₀ C A x a r γ hγ hs hhit
    have hguard :LocalGuard f C.g d j :=
      local_guard x a r d j (by omega) hlead hd₀ hj₀ _ h₁ h₂
    obtain ⟨v,hjet⟩:=hlocal f C.g d j hg hp hguard s hzero hroot
    obtain ⟨w,hw,he⟩:=hv v hjet
    rw [ArcFamily.variation,dite_eq_left hγ,← hw]
    exact rationalValue hs x he
end
end P5_7_3_3_4_1_7R
end
section
set_option autoImplicit true
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7_2
noncomputable section
open Polynomial P5_7_3_3_4_1_7
open qL2osVa (Series)


abbrev aQ:=SeparableClosure (FractionRing Series)
def jz :Series →+* aQ :=
  (algebraMap (FractionRing Series) aQ).comp (algebraMap Series (FractionRing Series))
def ramify {E :Type} [zrb E] (φ:Series →+* E) (n:ℕ) (hn:n≠0) :
    DoubleSeries →+* zpm E :=
  (PowerSeries.expand n hn (R:=E)).toRingHom.comp
    (PowerSeries.map φ)
def SplitAt (f :LocalEquation) (g n:ℕ) (hn:n≠0)
    (b:Fin g→zpm aQ) :Prop :=
  let e :=ramify jz n hn
  f.map e=C (e (f.coeff g)) * ∏ i,(z7y - C (b i))
def ExtendsSeed (D:aQ →+ aQ) :Prop :=
  (∀ a b,D (a*b)=a*D b+b*D a) ∧
  (∀ a :Series,D (jz a)=jz (PowerSeries.derivative a))
def Lv {R:Type} [za6 R]
    (a :zpm (zpm R)) :zpm (zpm R) :=
  PowerSeries.mk fun i=>PowerSeries.derivative (z2o i a)
def mapAdd {R S:Type} [Semiring R] [Semiring S] (D:R →+ S) (f :R[X]) :S[X] :=
  ⟨AddMonoidAlgebra.map D f.toFinsupp⟩
def jetDerivative {R:Type} [za6 R]
    (f : (zpm (zpm R))[X]) : (zpm (zpm R))[X] :=
  mapAdd { toFun:=Lv
           map_zero' := by ext i; simp [Lv]
           map_add' := by intro a b; ext i; simp [Lv] } f
def embed {R:Type} [za6 R] :R →+* R[X][X] :=C.comp C
def an1 {R:Type} [za6 R] (f q:R[X]) :R[X][X][X] :=
  let z :R[X][X][X] :=C (z7y:R[X][X])
  let w:R[X][X][X] :=C (C (z7y:R[X]))
  let u:R[X][X][X] :=z7y
  (f.map embed).derivative*(z - u)+w*q.map embed
def numerator (f :LocalEquation) (g:ℕ) :DoubleSeries[X][X] :=
  (f.map embed).resultant (an1 f (jetDerivative f)) g g
def denominator (f :LocalEquation) (g:ℕ) :DoubleSeries :=
  f.coeff g*det f g
def CentreShape {R:Type} [za6 R] (T:R[X][X]) (j:ℕ) (a b:R) :Prop :=
  (∀ i<j,T.coeff i=0)∧a*(T.coeff j).eval 0=b
end
end P5_7_3_3_4_1_7_2
end
