import ProximityPrize.SubmissionLower.ZL8fo3b
import ProximityPrize.SubmissionLower.Z3swOYa
import ProximityPrize.SubmissionLower.ZkEhKoc
import ProximityPrize.SubmissionLower.ZpWrDCd
import ProximityPrize.SubmissionLower.ZvqS6Fa
import ProximityPrize.SubmissionLower.ZWWU4Jd
import ProximityPrize.SubmissionLower.ZW8Nc6b
import ProximityPrize.SubmissionLower.ZEdS9yd
import Mathlib.RingTheory.Localization.Submodule
import ProximityPrize.SubmissionLower.ZK8GpQb
import ProximityPrize.SubmissionLower.Z3aw2hc
import ProximityPrize.SubmissionLower.ZO7Azpb
import ProximityPrize.SubmissionLower.ZexDIsb
import ProximityPrize.SubmissionLower.ZtyYfOe
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.EssFiniteType → zl5, Algebra.FiniteType → zUK, Algebra.smul_def → zd5, Algebra.subset_adjoin → zkk, Algebra.toSMul → zGD, CommRing → za6, Field → zrb, Finset → zJe, Function.Injective → zq4, Ideal → znc, Ideal.Quotient.mk → zVv, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsFractionRing.map → zJ1, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.eval₂Hom → zOD, MvPolynomial.mem_restrictTotalDegree → zpJ, MvPolynomial.quotientDegreeLE → z9e, MvPolynomial.rename → zHw, MvPolynomial.zeroLocus → zSD, Nat.add_le_add_left → z3b, Nat.cast_nonneg → zqJ, Nat.le_mul_of_pos_left → zCV, Nat.mul_le_mul_right → ztf, Polynomial.C → z1z, Polynomial.coe_mapRingHom → zKC, Polynomial.coeff_zero → zO6, Polynomial.eval_map_apply → zdm, Polynomial.mapRingHom → zhd, PowerSeries.C → zMG, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, RingHom.ker → zdq, Submodule.finrank_mono → zFM
set_option maxHeartbeats 1000000
section
section
set_option autoImplicit true
namespace qvWbALd
noncomputable section
open Polynomial

open cu (L)
open Cu
open E7 (CurvePlace)
open quN7Z4a (Sheet)
open qBajpRb (CurveRing incl yq)
open scoped WithZero
scoped instance gRK (C₀:sQ) [Fact (Irreducible C₀)] :
    zZE L (oO C₀) :=(zT C₀).toAlgebra
variable {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
structure MarkedPlaces (S:Sheet C₀ J 2 H T z s) where
  place :T→CurvePlace L (oO C₀)
  distinct :zq4 place
  lift: (γ:T)→CurveRing S.bY →+* (place γ).value.valuationSubring
  include_lift : ∀ γ,(place γ).value.valuationSubring.toSubring.subtype.comp (lift γ) =
    incl S.bY
  residue : (γ:T)→(place γ).value.valuationSubring →+* L
  cqr : ∀ γ,(residue γ).comp (lift γ) =
    (yq S.bY (z γ) (S.parameter γ) (S.onBase γ γ.property)).toRingHom
  uniformizer : (γ:T)→(place γ).value.valuationSubring
  uniformizer_value : ∀ γ,(place γ).value (uniformizer γ:oO C₀) =
    WithZero.exp (-1)
  kernel : ∀ γ,zdq (residue γ)=Ideal.span {uniformizer γ}
end
end qvWbALd
end
section
namespace qZfVj1b
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open gT (kM)
open DQ (DT)
open Cu
open E7 (CurvePlace)
open qBajpRb (CurveRing incl yq)
open scoped WithZero
abbrev gRK (Q:sQ) :zZE L (oO Q) :=
 (zT Q).toAlgebra
attribute [local instance] gRK
def normalize {E :Type} [zrb E] (f :E[X][X]) :E[X][X] :=
 C (C f.leadingCoeff.leadingCoeff⁻¹)*f
variable {Q:sQ} [Fact (Irreducible Q)] {J:znc kM}
 {e H n:ℕ} {T:zJe K} {z :K→K} {s :K→K[X]}
def pivot (S:quN7Z4a.Sheet Q J e H T z s) :DT S.n :=
 (S.bY.equation.coeff e).coeff (S.root.equation.coeff e).natDegree
structure ChartPlace {R:wJ Q J e} (A:yI R n)
   {x :K} {t:Fin n→L} (h:aCn x t∈zSD FX (EF A)) where
 place :CurvePlace L (oO Q)
 map :oO Q →ₐ[L] LaurentSeries L
 value : ∀ c,place.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (map c)
 series :CurveRing A →ₐ[L] PowerSeries L
 lift_eq : ∀ a,(series a :LaurentSeries L)=map (incl A a)
 reduce : ∀ a,zbO (series a)=yq A x t h a
end
end qZfVj1b
end
section
namespace qbEWDkb
theorem proof :qCe4xzb.c1 :=qb1WXKc.infinity_discr
end qbEWDkb
end
section
set_option maxRecDepth 4000
namespace qc2iTLd
noncomputable section
open cu (L)
open P5_7_7 (Dg)
open qrKC9pb
open qyUzJvd
open scoped nonZeroDivisors
theorem chart_fraction (J:Input) (r :Bool) :z0o (Chart J r) (EC J) := by
  let A:=Chart J r
  let E :=EC J
  let T:=Subfield.closure (Set.range (algebraMap A E))
  have hmem (a :A) : (a :E)∈T:=Subfield.subset_closure ⟨a,rfl⟩
  have hX:a7W J (Polynomial.X:Dg)∈T:= by
    have h:=hmem (coord J r 2)
    change jU J r∈T at h
    cases r
    · exact h
    · exact (inv_inv (a7W J (Polynomial.X:Dg))).symm ▸ T.inv_mem h
  have hc (a :Polynomial (Polynomial L)) :a7W J (z1z a)∈T:= by
    have h:=hmem (evalSeed J r a)
    rwa [show ((evalSeed J r a :A) :E)=a7W J (z1z a) from
      DFunLike.congr_fun (coe_evalSeed J r) a] at h
  have hp (a :Dg) :a7W J a∈T:= by
    induction a using Polynomial.induction_on' with
    | add a b ha hb=>rw [map_add]; exact T.add_mem ha hb
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow]
      exact T.mul_mem (hc a) (T.pow_mem hX n)
  have htop:T = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨a,b,_,rfl⟩:=IsFractionRing.div_surjective (AdjoinRoot J.F) z
    obtain ⟨a,rfl⟩:=AdjoinRoot.mk_surjective a
    obtain ⟨b,rfl⟩:=AdjoinRoot.mk_surjective b
    exact T.div_mem (hp a) (hp b)
  let f :FractionRing A →ₐ[A] E :=
    IsFractionRing.liftAlgHom (g:=Algebra.ofId A E) Subtype.val_injective
  have hr :f.toRingHom.fieldRange = ⊤ :=
    (IsFractionRing.ringHom_fieldRange_eq_of_comp_eq
      (show f.toRingHom.comp (algebraMap A (FractionRing A))=algebraMap A E from
        RingHom.ext f.commutes)).trans htop
  refine IsFractionRing.of_algEquiv (AlgEquiv.ofBijective f ⟨f.injective,?_⟩)
  intro z
  have hz :z∈f.toRingHom.fieldRange :=hr.symm ▸ Subfield.mem_top z
  exact hz
theorem proof :qyUzJvd.c2 := by
  intro J r
  have :zUK L (Chart J r) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range (aD J r))
  have :z0o (Chart J r) (EC J) :=chart_fraction J r
  exact q6hv5Ed.finite_affine L (Chart J r) (EC J)
end
end qc2iTLd
end
end
section
set_option autoImplicit true
namespace P5_7_3_3_4_1_6
noncomputable section
open cu (FX)
open DQ (jY Qd)
open Cu (Gc)
open MvPolynomial
abbrev bzm (n : ℕ) := Fin 2 ⊕ Fin n
def aCt (n a b : ℕ) : Set (bzm n →₀ ℕ) :=
  {e | (∑ i : Fin 2, e (Sum.inl i)) ≤ a ∧ (∑ i : Fin n, e (Sum.inr i)) ≤ b}
abbrev BoxPoly (F : Type) [zrb F] (n a b : ℕ) :=
  restrictSupport F (aCt n a b)
abbrev Box {F : Type} [zrb F] {n : ℕ} (B : znc (z3y (bzm n) F))
    (a b : ℕ) :=
  (BoxPoly F n a b).map (Ideal.Quotient.mkₐ F B).toLinearMap
abbrev gN {n : ℕ} (B : znc (Gc n)) (E : Type) [zrb E] [zZE FX E] :=
  B.map (MvPolynomial.map (algebraMap FX E))
def aEL {n m : ℕ} (i : Fin m → bzm n) : z3y (bzm n) (jY m) :=
  (∑ j : Fin m, C (Qd (some j)) * MvPolynomial.X (i j)) -
    C (Qd (n := m) none)
abbrev Section {n m : ℕ} (B : znc (Gc n)) (i : Fin m → bzm n) :=
  z3y (bzm n) (jY m) ⧸
    (gN B (jY m) ⊔ Ideal.span {aEL i})
def blockSize (n : ℕ) (seed : Bool) : ℕ := if seed then 2 else n
def bml (n : ℕ) (seed : Bool) : Fin (blockSize n seed) → bzm n :=
  match seed with
  | true => Sum.inl
  | false => Sum.inr
def seedStep (seed : Bool) : ℕ := if seed then 1 else 0
def coeffStep (seed : Bool) : ℕ := if seed then 0 else 1
end
end P5_7_3_3_4_1_6
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_3_3_4_1_7
noncomputable section
open Polynomial qL2osVa
open cu (L j9)
open Cu (sQ)
open scoped BigOperators
variable {C₀ : sQ} [Fact (Irreducible C₀)]
def targetDen {n : ℕ} : Target → Cut n
  | .constant _ => 1
  | .projective i a b _ => MvPolynomial.C a + MvPolynomial.X (Sum.inl i) * MvPolynomial.C b
def targetNum {n : ℕ} : Target → Cut n
  | .constant v => MvPolynomial.C v
  | .projective i _ _ c => MvPolynomial.C c * MvPolynomial.X (Sum.inl i)
abbrev CutEquation (n : ℕ) := (Cut n)[X][X]
def normalized (C : MarkedSheet C₀) (x : L) (r : Target) (a : L) : CutEquation C.sheet.n :=
  let e := (taylorAlgHom (MvPolynomial.C (σ := Fin 2 ⊕ Fin C.sheet.n) x)).toRingHom.comp
    (zhd (zHw (Sum.inr : Fin C.sheet.n → Fin 2 ⊕ Fin C.sheet.n)).toRingHom)
  let c := (z1z : (Cut C.sheet.n)[X] →+* CutEquation C.sheet.n).comp z1z
  let v := 1 + c (MvPolynomial.C a) * X
  let n := c (targetNum r) * v + X
  let d := c (targetDen r) * v
  ∑ i ∈ Finset.range (C.g + 1), z1z (e (C.sheet.bY.equation.coeff i)) *
    n ^ i * d ^ (C.g - i)
def det {R : Type*} [za6 R] (f : R[X]) (g : ℕ) : R :=
  f.resultant f.derivative g (g - 1)
def arcEval {C : MarkedSheet C₀} {γ : P5.K} (A : Arc C γ) : Cut C.sheet.n →+* Series :=
  zOD zMG (Sum.elim A.seed A.parameter)
abbrev DoubleSeries := PowerSeries Series
abbrev LocalEquation := DoubleSeries[X]
def bfj {C : MarkedSheet C₀} {γ : P5.K} (A : Arc C γ) :
    (Cut C.sheet.n)[X] →+* DoubleSeries :=
  Polynomial.coeToPowerSeries.ringHom.comp (zhd (arcEval A))
def localEquation {C : MarkedSheet C₀} {γ : P5.K} (A : Arc C γ)
    (F : CutEquation C.sheet.n) : LocalEquation :=
  F.map (bfj A)
def physicalCentre : DoubleSeries →+* Series :=
  zbO
def seedFibre (f : LocalEquation) : Series[X] :=
  f.map (PowerSeries.map zbO)
def seedFirst (s : DoubleSeries) : Series :=
  PowerSeries.mk fun i => z2o 1 (z2o i s)
def LocalGuard (f : LocalEquation) (g d j : ℕ) : Prop :=
  f.natDegree ≤ g ∧ IsUnit (f.coeff g) ∧
  (∃ u : DoubleSeries, IsUnit u ∧ det f g = PowerSeries.X^d * u) ∧
  (∀ i < j, physicalCentre (f.coeff i) = 0) ∧
  IsUnit (physicalCentre (f.coeff j))
def ZeroJet (f : LocalEquation) (s v : Series) : Prop :=
  zbO v = 0 ∧
    seedFirst (f.eval (PowerSeries.map zMG s)) +
      (seedFibre f).derivative.eval s * v = 0
def expand (x : L) : L[X] →+* Series :=
  Polynomial.coeToPowerSeries.ringHom.comp (taylorAlgHom x).toRingHom
def markedJet {C : MarkedSheet C₀} {γ : P5.K} (A : Arc C γ) : L[X] :=
  let f := C.sheet.bY.equation.map
    (zhd (zOD zMG A.parameter))
  firstCoeff (f.eval ((j9 (C.s γ)).map zMG))
def markedSeparant (C : MarkedSheet C₀) (γ : P5.K) : L[X] :=
  (C.markedEquation γ).derivative.eval (j9 (C.s γ))
end
end P5_7_3_3_4_1_7
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace Cmp55E
noncomputable section
open scoped nonZeroDivisors
open q6hv5Ed (finite_affine)
private theorem finite_localization {D C F:Type} [za6 D] [za6 C] [zrb F]
    [zZE D F] [zZE D C] [zZE C F] [zsf D C F]
    (M:Submonoid D) [IsLocalization M C] [zAa D (integralClosure D F)] :
    zAa C (integralClosure C F) := by
  let N :=integralClosure D F
  let N' := integralClosure C F
  classical
  let j:N →ₛₗ[algebraMap D C] N' :=
    { toFun:= fun x=>⟨x,x.property.tower_top⟩
      map_add' _ _:=rfl
      map_smul' a x :=Subtype.ext (by
        change a•(x :F)=algebraMap D C a•(x :F)
        simp only [zd5,zG3 D C F]) }
  obtain ⟨s,hs⟩:=Module.Finite.fg_top (R:=D) (M:=N)
  let T:=Submodule.span C ((s.image j:zJe N') :Set N')
  refine ⟨s.image j,top_unique fun x _ => ?_⟩
  have hj (y :N) :j y∈T:= by
    have hle :Submodule.span D (s :Set N)≤T.comap j :=
      Submodule.span_le.mpr fun a ha =>
        Submodule.subset_span (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    rw [hs] at hle
    exact hle (Submodule.mem_top (x :=y))
  obtain ⟨m,hm⟩:=IsIntegral.exists_multiple_integral_of_isLocalization M (x :F) x.property
  let y :N :=⟨_,hm⟩
  have he :j y=algebraMap D C m•x :=Subtype.ext (by
    change (m:D)•(x :F)=algebraMap D C m•(x :F)
    simp only [zd5,zG3 D C F])
  have hmul :=hj y
  rw [he] at hmul
  obtain ⟨u,hu⟩:=IsLocalization.map_units C m
  have h:=T.smul_mem (↑u⁻¹:C) hmul
  rw [← mul_smul,← hu,Units.inv_mul,one_smul] at h
  exact h
theorem finiteNormalization (k R F:Type) [zrb k] [IsAlgClosed k]
   [za6 R] [IsDomain R] [zZE k R] [zl5 k R]
   [zrb F] [zZE R F] [z0o R F] :
   IsNoetherianRing (integralClosure R F)∧zAa R (integralClosure R F) := by
 let A:=Algebra.EssFiniteType.subalgebra k R
 let S:=Algebra.EssFiniteType.submonoid k R
 let:zZE A F:=((algebraMap R F).comp (algebraMap A R)).toAlgebra
 let:SMul A R:=zGD
 let:SMul A F:=zGD
 have :zsf A R F:=IsScalarTower.of_algebraMap_eq' rfl
 have :z0o A F:= by
   change IsLocalization A⁰ F
   have hinj:zq4 (algebraMap A R) :=Subtype.val_injective
   have he : (R⁰).comap (algebraMap A R)=A⁰:= by
     ext x
     simp [mem_nonZeroDivisors_iff_ne_zero,map_ne_zero_iff _ hinj]
   rw [← he]
   exact IsLocalization.localization_localization_isLocalization_of_has_all_units S R⁰ F
     (fun x hx=>mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)
 have :IsNoetherianRing A:=Algebra.FiniteType.isNoetherianRing k A
 have :IsNoetherianRing R:=IsLocalization.isNoetherianRing S R inferInstance
 have :zAa A (integralClosure A F) :=finite_affine k A F
 let hfin:zAa R (integralClosure R F) :=finite_localization S
 exact ⟨IsNoetherianRing.of_finite R (integralClosure R F),hfin⟩
end
end Cmp55E
end
section
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false
namespace q6hv5Ed
noncomputable section
open Polynomial qNu3xvc qoCymac
open cu (L)
open E7 (CurvePlace CurveField)
open qIGP9Qa (seedRingHom seedEssential chartFraction)
open scoped qIGP9Qa
variable {E :Type} [zrb E] [zZE L E]
theorem chartEssential (A:Equation E) (w:CurvePlace L E)
   (hE :CurveField L E) (r :Bool) :zl5 L (Chart A w r) := by
 classical
 let W:=w.value.valuationSubring
 let R:=Chart A w r
 let:zZE W R:=(seedRingHom A w r).toAlgebra
 let:SMul W R:=zGD
 have :zsf L W R:=IsScalarTower.of_algebraMap_eq fun _=>rfl
 let x :=xAt A w r
 let y :R:=⟨jU A r,zkk (Or.inr (by simp))⟩
 let j:R:=⟨jet A r,zkk (Or.inr (by simp))⟩
 let B:=Algebra.adjoin W ({x,y,j} : Set R)
 have hB:R≤(B.restrictScalars L).map R.val :=Algebra.adjoin_le fun u hu=> by
   rcases hu with ⟨a,rfl⟩ | hu
   · exact ⟨aee A w r a,B.algebraMap_mem a,rfl⟩
   · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
     rcases hu with rfl | rfl | rfl
     · exact ⟨x,zkk (by simp),rfl⟩
     · exact ⟨y,zkk (by simp),rfl⟩
     · exact ⟨j,zkk (by simp),rfl⟩
 have htop:B = ⊤ := top_unique fun a _=> by
   obtain ⟨b,hb,e⟩:=hB a.property
   exact (Subtype.ext e :b=a) ▸ hb
 have :zUK W R:=⟨⟨{x,y,j},by simpa [B] using htop⟩⟩
 have :zl5 L W:=seedEssential hE w
 exact Algebra.EssFiniteType.comp L W R
theorem proof :qoCymac.c4 := by
 intro E _ _ A w hE r
 have :=chartFraction A w r
 have :=chartEssential A w hE r
 exact Cmp55E.finiteNormalization L (Chart A w r) (EC A)
end
end q6hv5Ed
end
end
section
section
namespace q6CrDDe
noncomputable section
open Polynomial
open P5 (K p)
open cu (L FX)
open gT (kM)
open Cu
open qBajpRb (CurveRing yq)
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:znc kM}
 {g n:ℕ} {R:wJ C₀ J g} (A:yI R n)
def thickMarks (T:zJe K) (z :K→K) (t:K→Fin n→L)
    (hT : ∀ γ∈T,aCn (z γ) (t γ)∈zSD FX (EF A))
    (q:ℕ) :znc (CurveRing A) :=
  ⨅ γ : ↥T,zdq (yq A (z γ) (t γ) (hT γ γ.property)).toRingHom^q
def frobPoly (B:Type) [za6 B] [CharP B p] (r :ℕ) :B[X] →+* B[X] :=
 zhd (iterateFrobenius B p r)
def frobEquation (B:Type) [za6 B] [CharP B p] (r :ℕ) :
    B[X][X] →+* B[X][X] :=zhd (frobPoly B r)
end
end q6CrDDe
end
section
set_option backward.isDefEq.respectTransparency false
namespace q6CrDDe
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L j9)
open gT (kM)
open Cu
open quN7Z4a (Sheet)
open qBajpRb
variable {C₀:sQ} [Fact (Irreducible C₀)] {J:znc kM}
 {g n:ℕ} {R:wJ C₀ J g} (A:yI R n)
theorem tuple_mono {u v :ℕ} (h:u≤v) :tuple A u≤tuple A v :=
 Submodule.map_mono fun _ hx=>(zpJ _ _ _).mpr
  (((zpJ _ _ _).mp hx).trans h)
theorem tuple_mul (u v :ℕ) :tuple A u*tuple A v≤tuple A (u+v) :=
 block_mul (tupleMap A) u v
private theorem tuple_rank (k :ℕ) :
   zsE L (tuple A k) =
     MvPolynomial.affineHilbertFunction (XW.TU A) k := by
 let I:=XW.TU A
 have hm: (incl A).comp (tupleMap A).toRingHom =
     zOD (zT C₀) A.coordinate := by
   apply MvPolynomial.ringHom_ext
   · intro a
     change incl A (cls A (zHw Sum.inr _))= _
     rw [incl_cls]
     simp [ek]
   · intro i
     change incl A (cls A (zHw Sum.inr _))= _
     rw [incl_cls]
     simp [ek]
 have hk :zdq (tupleMap A).toRingHom=I:= by
   rw [← RingHom.ker_comp_of_injective _ (incl_injective A),hm]
   rfl
 let f : (z3y (Fin n) L ⧸ I) →ₐ[L] CurveRing A :=
   ⟨Ideal.Quotient.lift _ (tupleMap A).toRingHom (fun x hx=>RingHom.mem_ker.mp (hk.symm ▸ hx)),
     fun x=>(tupleMap A).commutes x⟩
 have hf :zq4 f :=
   (Ideal.injective_lift_iff _).mpr hk
 have hU: (z9e I k).map f.toLinearMap=tuple A k := by
   rw [z9e,← Submodule.map_comp]
   rfl
 rw [← hU]
 exact (Submodule.equivMapOfInjective f.toLinearMap hf _).finrank_eq.symm
theorem choose_rank :
   ∃ r k :ℕ,2*k≤p^r ∧
     zsE L (tuple A k*tuple A (p^r))<4*zsE L (tuple A k) := by
 let I:=XW.TU A
 obtain ⟨N,hN⟩:=MvPolynomial.exists_eval_affineHilbertPolynomial I
 obtain ⟨a,b,he⟩:=exists_eq_X_add_C_of_natDegree_le_one
   (XW.aTz A).2
 let e (j:ℕ) :=zsE L (tuple A j)
 have hlin (j:ℕ) (hj:N≤j) : (e j:ℚ)=a*j+b:= by
   change (zsE L (tuple A j) :ℚ)= _
   rw [tuple_rank A,← hN j hj,he]
   simp
 have hpos :0<e N := by
   have ho: (1 :CurveRing A)∈tuple A N :=
     ⟨1,(zpJ _ _ _).mpr (by simp),map_one (tupleMap A)⟩
   exact Submodule.one_le_finrank_iff.mpr (fun h=>one_ne_zero
     (show (1 :CurveRing A)∈(⊥ : Submodule L (CurveRing A)) from h ▸ ho))
 have ha :0≤a := by
   have hm: (e N :ℚ)≤e (N+1) :=
     by exact_mod_cast zFM (tuple_mono A (Nat.le_succ N))
   rw [hlin N le_rfl,hlin (N+1) (Nat.le_succ _)] at hm
   push_cast at hm
   linarith
 let r :=6*N+6
 let q:=p^r
 let k :=q/2
 have hq:r<q:=Nat.lt_pow_self (by decide :1<p)
 have hk :N≤k := by dsimp [r,k] at *; omega
 have hs :q≤3*(k-N) := by dsimp [r,k] at *; omega
 have hd:e (k+q)<4*e k := by
   have hsQ: (q:ℚ)≤3*((k :ℚ)-N) := by
     rw [← Nat.cast_sub hk]
     exact_mod_cast hs
   have hpQ: (0:ℚ)<e N := by exact_mod_cast hpos
   have hn:=hlin N le_rfl
   have h:=mul_le_mul_of_nonneg_left hsQ ha
   rw [hn] at hpQ
   have hg: (e (k+q) :ℚ)<4*(e k :ℚ) := by
     rw [hlin (k+q) (hk.trans (Nat.le_add_right _ _)),hlin k hk]
     push_cast
     nlinarith only [hpQ,h]
   exact_mod_cast hg
 exact ⟨r,k,by dsimp [k]; omega,(zFM (tuple_mul A k q)).trans_lt hd⟩
theorem frob_coeff (r i a :ℕ) (F: (CurveRing A)[X][X])
   (hF : ∀ i a,(F.coeff i).coeff a∈tuple A 1)
   [CharP (CurveRing A) p] :
   ((((frobEquation (CurveRing A) r) F).coeff i).coeff a)∈tuple A (p^r) := by
 obtain ⟨x,hx,he⟩:=hF i a
 refine ⟨x^(p^r),(zpJ _ _ _).mpr
   ((MvPolynomial.totalDegree_pow _ _).trans ?_),?_⟩
 · simpa using ztf (p^r) ((zpJ _ _ _).mp hx)
 · simp only [frobEquation,frobPoly,zKC,coeff_map,iterateFrobenius_def]
   change (tupleMap A) (x^(p^r))= _
   rw [map_pow,show tupleMap A x=(F.coeff i).coeff a from he]
theorem thick_root {T:zJe K} {z :K→K} {s :K→K[X]} {H D:ℕ}
   (S:Sheet C₀ J g H T z s) [CharP (CurveRing S.bY) p]
   (r :ℕ) {γ:K} (hγ:γ∈T) (hd: (s γ).natDegree≤D) :
   let B:=CurveRing S.bY
   let φ:=yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ)
   let ψ:=zVv (zdq φ.toRingHom^(p^r))
   ∃ u: (B ⧸ zdq φ.toRingHom^(p^r))[X],u.natDegree≤D ∧
     (((frobEquation B r) (equation S.bY)).map (zhd ψ)).eval u=0:= by
 dsimp only
 let B:=CurveRing S.bY
 let φ:=yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ)
 let I:=zdq φ.toRingHom^(p^r)
 let ψ:=zVv I
 let F:=equation S.bY
 let v :=(j9 (s γ)).map (algebraMap L B)
 have hmap :v.map φ.toRingHom=j9 (s γ) := by
   rw [Polynomial.map_map,show φ.toRingHom.comp (algebraMap L B)=RingHom.id _ from
     RingHom.ext φ.commutes,Polynomial.map_id]
 have he : (F.eval v).map φ.toRingHom=0:= by
   change (zhd φ.toRingHom) (F.eval v)=0
   rw [← zdm,show F=equation S.bY from rfl,equation_mark S.bY (S.onBase γ hγ),
     zKC,hmap]
   exact S.identity γ hγ
 let u:=((frobPoly B r) v).map ψ
 refine ⟨u,natDegree_map_le.trans (natDegree_map_le.trans (natDegree_map_le.trans
   (natDegree_map_le.trans hd))),?_⟩
 change (((F.map (frobPoly B r)).map (zhd ψ)).eval u)=0
 rw [show u=(zhd ψ) ((frobPoly B r) v) from rfl,
   zdm,zdm]
 apply Polynomial.ext
 intro i
 simp only [frobPoly,zKC,coeff_map,coeff_zero]
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 rw [zKC,coeff_map,iterateFrobenius_def]
 apply Ideal.pow_mem_pow
 exact RingHom.mem_ker.mpr (by
   have h:=congrArg (fun f :L[X]=>f.coeff i) he
   simpa only [coeff_map,coeff_zero] using h)
end
end q6CrDDe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qISdf9a
open Polynomial
open scoped BigOperators
private noncomputable abbrev extendAbscissa {F E :Type} [zrb F] [zrb E] (f :F →+* E) :
  FractionRing F[X] →+* FractionRing E[X] :=
 zJ1 (j:=zhd f) (Polynomial.map_injective f f.injective)
theorem clear_abscissa_relation {F E A ι:Type} [zrb F] [zrb E] [za6 A]
   [zZE F A] [Fintype ι]
   (f :F →+* E) (g:A →+* E) (hg:zq4 g)
   (hgf : ∀ c,g (algebraMap F A c)=f c)
   (r :ι→A) (hr :LinearIndependent F r) (c:ι→FractionRing F[X])
   (he : (∑ j,extendAbscissa f (c j) *
     algebraMap E[X] (FractionRing E[X]) (z1z (g (r j))))=0) :
   ∀ i,c i=0:= by
 classical
 intro i
 let fX:=extendAbscissa f
 let Cx :=algebraMap E[X] (FractionRing E[X])
 change (∑ j,fX (c j)*Cx (z1z (g (r j))))=0 at he
 obtain ⟨b,hb⟩:=IsLocalization.exist_integer_multiples_of_finite
   (nonZeroDivisors F[X]) c
 choose d hd using hb
 have hmap (p:F[X]) :fX (algebraMap F[X] (FractionRing F[X]) p)=Cx (p.map f) := by
   unfold fX extendAbscissa zJ1
   exact IsLocalization.map_eq _ _
 have hm' (j:ι) :algebraMap E[X] (FractionRing E[X]) ((d j).map f) =
     fX (algebraMap F[X] (FractionRing F[X]) (b:F[X]))*fX (c j) := by
   rw [← hmap,hd j,zd5,map_mul]
 have hz : (∑ j,(d j).map f*z1z (g (r j)))=0:= by
   apply (zxb E[X] (FractionRing E[X]))
   rw [map_sum,map_zero]
   simp only [map_mul,hm',mul_assoc]
   change (∑ j,fX (algebraMap F[X] (FractionRing F[X]) (b:F[X])) *
     (fX (c j)*Cx (z1z (g (r j)))))=0
   rw [← Finset.mul_sum,he,mul_zero]
 have hcoeff (k :ℕ) : (∑ j,(d j).coeff k•r j)=0:= by
   apply hg
   simpa only [Polynomial.finsetSum_coeff,Polynomial.coeff_mul_C,Polynomial.coeff_map,
     zO6,map_sum,zd5,map_mul,hgf,map_zero]
     using congrArg (fun a :E[X]=>a.coeff k) hz
 have hi:d i=0:=Polynomial.ext fun k =>
   (Fintype.linearIndependent_iff.mp hr _ (hcoeff k) i).trans (zO6 k).symm
 have hc' := hd i
 rw [hi,map_zero,zd5] at hc'
 exact (mul_eq_zero.mp hc'.symm).resolve_left
   (fun h=>(mem_nonZeroDivisors_iff_ne_zero.mp b.property)
     ((zxb F[X] (FractionRing F[X])) (h.trans (map_zero _).symm)))
end qISdf9a
end
section
set_option backward.isDefEq.respectTransparency false
namespace qBajpRb
noncomputable section
open Polynomial Finset
open P5 (K)
open qAxtVye (wX)
open quN7Z4a (compressionWidth)
open cu (L FX j9)
open gT (kM)
open Cu
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:znc kM)
    (g n H :ℕ) (R:wJ C₀ J g) (A:yI R n),
    a9K (EF A) H →
    ∀ (V:zJe K) (z :K→K) (t:K→Fin n→L)
      (hV : ∀ γ∈V,aCn (z γ) (t γ)∈zSD FX (EF A)),
      Set.InjOn z (V:Set K) →
      ∀ (k j:ℕ) (q:CurveRing A),q∈stock A k j→q≠0 →
      (∀ γ (hγ:γ∈V),yq A (z γ) (t γ) (hV γ hγ) q=0) →
      V.card≤k*C₀.totalDegree+j*H
def c2 :Prop :=
  ∀ (B:Type) [za6 B] [IsDomain B] [zZE L B]
    (V W:Submodule L B) [zAa L V] [zAa L W]
    (D g:ℕ) (F:B[X][X]),
    0<D→0<g→F≠0→F.natDegree≤g →
    (∀ i a,(F.coeff i).coeff a∈W) →
    aia D g*zsE L (V*W)<compressionWidth D g*zsE L V →
    ∃ G:B[X][X],G≠0∧G.natDegree≤g ∧
      (∀ i a,(G.coeff i).coeff a∈V*W) ∧
      (∀ i a,(G.coeff i).coeff a≠0→a+i*D <compressionWidth D g) ∧
      (∀ (φ:B →ₐ[L] L) (u:L[X]),u.natDegree≤D →
        (F.map (zhd φ.toRingHom)).eval u=0 →
        (G.map (zhd φ.toRingHom)).eval u=0)
private theorem output_rank (h1 :c1)
   {C₀:sQ} [Fact (Irreducible C₀)] {J:znc kM}
   {g n H :ℕ} {R:wJ C₀ J g} (A:yI R n)
   (hH :a9K (EF A) H) (T:zJe K) (z :K→K) (t:K→Fin n→L)
   (hT : ∀ γ∈T,aCn (z γ) (t γ)∈zSD FX (EF A))
   (hz :Set.InjOn z (T:Set K)) {k :ℕ} (hbig:k*C₀.totalDegree+H<T.card) :
   zsE L (stock A k 1)≤k*C₀.totalDegree+H+1 := by
 classical
 obtain ⟨V,hVT,hc⟩:=exists_subset_card_eq (Nat.succ_le_of_lt hbig)
 let hV γ (hγ:γ∈V) :=hT γ (hVT hγ)
 let e :stock A k 1 →ₗ[L] (↥V→L) :=
   LinearMap.pi fun γ=>(yq A (z γ) (t γ) (hV γ γ.property)).toLinearMap.comp
     (stock A k 1).subtype
 have he :zq4 e := by
   apply LinearMap.ker_eq_bot.mp
   apply LinearMap.ker_eq_bot'.mpr
   intro q hq
   apply Subtype.ext
   change (q:CurveRing A)=0
   by_contra hn
   have h:=h1 C₀ J g n H R A hH V z t hV (hz.mono hVT) k 1 q q.property hn
     (fun γ hγ=>congrFun hq ⟨γ,hγ⟩)
   omega
 have h:=LinearMap.finrank_le_finrank_of_injective he
 simpa [Module.finrank_fintype_fun_eq_card,hc] using h
theorem of_children (h1 :c1) (h2 :c2) :quN7Z4a.c2 := by
  classical
  intro b C₀ hC J T z s w g d H S hb hg hd hpos _ hlarge hz W
  let k :=multiplierDegree d H
  obtain ⟨hkl,hku⟩:=multiplier_bounds (H :=H) hpos
  have hpay : (↑(g*k*d+(g+g)*H) :ℚ) ≤
      (2*(d:ℚ)/3+1)*(d*g:ℚ)+(3*(g:ℚ)+1)*H+g:= by
    push_cast
    change (k :ℚ)*d≤_ at hku
    have h:=mul_le_mul_of_nonneg_left hku (zqJ (α:=ℚ) g)
    have hh: (0:ℚ)≤g*H := by positivity
    nlinarith only [h,hh,zqJ (α:=ℚ) H,zqJ (α:=ℚ) g]
  suffices h:T.card≤g*k*d+(g+g)*H by
    exact (show (T.card:ℚ)≤(↑(g*k*d+(g+g)*H) :ℚ) by exact_mod_cast h).trans hpay
  by_cases hT:T.card≤k*d+H
  · refine hT.trans ?_
    have hg0:0<g:= by omega
    rw [mul_assoc]
    exact Nat.add_le_add (zCV _ hg0)
      (zCV _ (by omega))
  have hr :=output_rank h1 S.bY S.height T z S.parameter S.onBase hz
    (k :=k) (by rw [hd]; omega)
  rw [hd] at hr
  have hlow:=lower_rank S.bY (k :=k) hd hpos
  have hdimQ: (zsE L (stock S.bY k 1) :ℚ) <
      4*(zsE L (u7 S.bY k) :ℚ) := by
    have hh: (zsE L (stock S.bY k 1) :ℚ)≤(k :ℚ)*d+H+1 :=
      by exact_mod_cast hr
    change (H :ℚ)+2*(d:ℚ)^2<3*(k :ℚ)*d at hkl
    linarith only [hh,hlow,hkl]
  have hdim:zsE L (stock S.bY k 1)<4*zsE L (u7 S.bY k) :=
    by exact_mod_cast hdimQ
  let D:=wX b
  have hD:0<D:= by rcases hb with rfl | rfl <;> decide
  have hg0:0<g:= by omega
  have hM:0<compressionWidth D g:= by unfold compressionWidth; positivity
  have hrow:0<aia D g:= by
    rw [← row_count D g] at hM
    omega
  have hsurplus :aia D g*zsE L (stock S.bY k 1) <
      compressionWidth D g*zsE L (u7 S.bY k) := calc
    _<aia D g*(4*zsE L (u7 S.bY k)) :=
      Nat.mul_lt_mul_of_pos_left hdim hrow
    _ = _:= by rw [← row_count D g]; ring
  obtain ⟨G,hG0,hGd,hG,hsmall,htransfer⟩:=h2 (CurveRing S.bY) (u7 S.bY k)
    (tuple S.bY 1) D g (equation S.bY) hD hg0 (equation_nonzero S.bY)
    (equation_degree S.bY).le (equation_coeff S.bY) hsurplus
  obtain ⟨q,hq,hq0,hcut⟩:=resultant_cut S.bY hg0 hM hlarge hG0 hGd hsmall hG
  have hcard:=h1 C₀ J g S.n H S.root S.bY S.height T z S.parameter S.onBase hz
    (g*k) (g+G.natDegree) q hq hq0 (by
      intro γ hγ
      let φ:=yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ)
      have hf : ((equation S.bY).map (zhd φ.toRingHom)).eval
          (j9 (s γ))=0:= by
        rw [equation_mark S.bY (S.onBase γ hγ)]
        exact S.identity γ hγ
      have hdeg: (j9 (s γ)).natDegree≤D:=natDegree_map_le.trans (W.degree γ hγ)
      exact hcut φ (j9 (s γ)) hf (htransfer φ (j9 (s γ)) hdeg hf))
  rw [hd] at hcard
  exact hcard.trans (z3b (ztf H (z3b hGd g)) _)
end
end qBajpRb
end
end
