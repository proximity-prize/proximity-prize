import ProximityPrize.SubmissionLower.ZrU0ida
import ProximityPrize.SubmissionLower.ZbbSEle
import ProximityPrize.SubmissionLower.ZODErLe
import ProximityPrize.SubmissionLower.ZoqNZ8b
import ProximityPrize.SubmissionLower.ZATKiYa
import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.ZjZ6ihd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Field → zrb, Polynomial.X → z7y, Polynomial.ringHom_ext → z86
set_option maxRecDepth 4000
section
section
namespace qps5rle
noncomputable section
open Polynomial qe6nVeb qE3Ebna
open P5 (K)
open cu (L FX)
open E7 (CurvePlace poleOrder)
open qb0hmCe (CurveModel cLN SiteTarget.det SiteTarget.height)
open scoped Classical WithZero
abbrev SeedSeries :=LaurentSeries L
abbrev PhysicalSeries :=LaurentSeries SeedSeries
abbrev vSeed :Valuation SeedSeries ℤᵐ⁰:=Valued.v
abbrev vPhysical:Valuation PhysicalSeries ℤᵐ⁰:=Valued.v
def finiteAt (x :L) (t:FX) :Prop :=
 ∃ P Q:L[X],Q.eval x≠0∧t=phys P/phys Q
def atArc {E :Type} [zrb E] [zZE L E] (a :E →ₐ[L] SeedSeries)
    (f :E[X][X]) :SeedSeries[X][X] :=
  f.map (mapRingHom a.toRingHom)
abbrev residue (f :SeedSeries[X][X]) (i:ℤ) :L[X][X] :=
 cLN (AlgHom.id L SeedSeries) i f
structure SiteJet (f :SeedSeries[X][X]) (x :L) where
 w:FX
 delta :FX
 finite :finiteAt x w
 root : (residue f 0).eval₂ phys w=0
 simple : (residue f 0).derivative.eval₂ phys w≠0
 zD: (residue f 1).eval₂ phys w+delta*(residue f 0).derivative.eval₂ phys w=0
def O7 {E :Type} [zrb E] [zZE L E] (a b:L) (z :E) :E :=
 algebraMap L E a+algebraMap L E b*z
abbrev physicalParameter {E :Type} [zrb E] [zZE L E] (x :L) :E[X] :=
 z7y (R:=E) - C (algebraMap L E x)
def siteMatrix {E :Type} [zrb E] [zZE L E] (R:SiteTarget) (z :E)
    (V:Fin 2→L) (M:Matrix (Fin 2) (Fin 2) L) :Matrix (Fin 2) (Fin 2) E[X] :=
  !![C (O7 R.a R.b z),physicalParameter R.center*C (algebraMap L E (V 0));
     C (O7 R.c R.d z),physicalParameter R.center*C (algebraMap L E (V 1))] *
    M.map (C.comp (algebraMap L E))
def targetDet {E :Type} [zrb E] [zZE L E] (R:SiteTarget) (z :E) (V:Fin 2→L) :E :=
 O7 R.a R.b z*algebraMap L E (V 1) -
 O7 R.c R.d z*algebraMap L E (V 0)
def changeOrdinate {E :Type} [zrb E] (f :E[X][X])
    (M:Matrix (Fin 2) (Fin 2) E[X]) :E[X][X] :=
  ∑ i∈Finset.range (f.natDegree+1),C (f.coeff i) *
    (C (M 0 0)+C (M 0 1)*X)^i *
    (C (M 1 0)+C (M 1 1)*X)^(f.natDegree-i)
def initialAt {E :Type} [zrb E] [zZE L E] (x :L) (g:E[X]) :E :=
 (g.taylor (algebraMap L E x)).trailingCoeff
def leadAt {E :Type} [zrb E] [zZE L E] (x :L) (g:E[X][X]) :E :=
 g.leadingCoeff.eval (algebraMap L E x)
structure SiteChart {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
   {C:CurveModel q} (S:Sheet B C) (R:SiteTarget) where
 V:Fin 2→L
 M:Matrix (Fin 2) (Fin 2) L
 matrix_ne :M.det≠0
 det_ne :targetDet R (C.seed R.coord) V≠0
 k :ℕ
 g:C.E[X][X]
 transformed:Polynomial.C (physicalParameter R.center^k)*g =
   changeOrdinate S.f (siteMatrix R (C.seed R.coord) V M)
 degree :g.natDegree=S.d
 lead_ne :leadAt R.center g≠0
 lead_height: (∑ᶠ v :CurvePlace L C.E,poleOrder v.value (leadAt R.center g)) ≤
   S.h+S.d*R.height q
 det_unit : ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ →
   (S.atPlace γ hγ (targetDet R (C.seed R.coord) V)).coeff 0≠0
 integral : ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ → ∀ i j,
   vSeed (((atArc (S.atPlace γ hγ) g).coeff i).coeff j)≤1
 jet : ∀ γ (hγ:γ∈S.marks),matchesTarget R B γ →
   ∃ A:SiteJet (atArc (S.atPlace γ hγ) g) R.center,
     finiteAt R.center A.delta →
     ((S.num γ).eval R.center=0↔R.det=0∨S.direction γ R.coord=0)
def physExpansion (x :L) :SeedSeries[X] →+* PhysicalSeries :=
  eval₂RingHom (algebraMap SeedSeries PhysicalSeries)
    (HahnSeries.single 1 1+algebraMap L PhysicalSeries x)
def seedDerivative (f :SeedSeries[X][X]) :SeedSeries[X][X] :=
 f.sum fun i g=>monomial i (g.sum fun j c=>monomial j (LaurentSeries.derivative L c))
def evalRoot (x :L) (f :SeedSeries[X][X]) (w:AlgebraicClosure PhysicalSeries) :
    AlgebraicClosure PhysicalSeries :=
  f.eval₂ ((algebraMap PhysicalSeries (AlgebraicClosure PhysicalSeries)).comp (physExpansion x)) w
def tameDerivative (x :L) (f :SeedSeries[X][X]) :Prop :=
  ∀ w:AlgebraicClosure PhysicalSeries,evalRoot x f w=0 →
    IsIntegral vPhysical.valuationSubring
      (-(evalRoot x (seedDerivative f) w/evalRoot x f.derivative w))
end
end qps5rle
end
section
namespace qZu9hjc
noncomputable section
open Polynomial Finset
open P5 (K)
open qe6nVeb (Input DualWord SeedPlane phys)
open qE3Ebna (Sheet poleOrderAt)
open qb0hmCe (CurveModel coeffHeight cLN specialize zD)
open qFD8jve (sheetPole)
open cu (L)
open E7 (CurvePlace poleOrder KB Tq)
open scoped Classical WithZero
def HE {E :Type} [zrb E] (f :E[X][X]) (s a :ℕ) :Prop :=
 ∀ i,f.coeff i≠0→(f.coeff i).natDegree+i*s≤a
def discrDegree (d a s :ℕ) :ℤ :=
 (2*(d:ℤ)-2)*a-(d:ℤ)*(d-1)*s
def valueDegree (d a s :ℕ) :ℤ :=
 (6*(d:ℤ)-4)*a-(3*(d:ℤ)^2-4*d+2)*s+(2*(d:ℤ)-2)
structure Chart {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
   {C:CurveModel q} (S:Sheet B C) (s a :ℕ) where
 f :C.E[X][X]
 irreducible :Irreducible f
 degree :f.natDegree=S.d
 weight:HE f s a
 height:coeffHeight f≤S.h
 integral : ∀ γ∈S.marks,∀ i j,(S.place γ).value ((f.coeff i).coeff j)≤1
 P:K→ L[X]
 Q:K→ L[X]
 denom : ∀ γ∈S.marks,Q γ≠0
 coprime : ∀ γ∈S.marks,IsCoprime (P γ) (Q γ)
 fWS : ∀ γ (hγ:γ∈S.marks),(cLN (S.atPlace γ hγ) 0 f).natDegree=S.d
 root : ∀ γ (hγ:γ∈S.marks),specialize (cLN (S.atPlace γ hγ) 0 f) (P γ) (Q γ)=0
 separable : ∀ γ (hγ:γ∈S.marks),((cLN (S.atPlace γ hγ) 0 f).map phys).Separable
 simple : ∀ γ (hγ:γ∈S.marks),
   specialize (cLN (S.atPlace γ hγ) 0 f).derivative (P γ) (Q γ)≠0
 num :K→ L[X]
 den:K→ L[X]
 den_ne : ∀ γ∈S.marks,den γ≠0
 reduced : ∀ γ∈S.marks,IsCoprime (num γ) (den γ)
 formula : ∀ γ (hγ:γ∈S.marks),
   phys (num γ)/phys (den γ)=zD (S.atPlace γ hγ) f (P γ) (Q γ)
 moved : ∀ γ∈S.marks,poleOrderAt S γ≤(den γ).natDegree
def atPair {E F:Type} [zrb E] [zrb F] (j:E →+* F) (x y :F) (f :E[X][X]) :F :=
 f.eval₂ (eval₂RingHom j x) y
def physicalDeriv {E :Type} [zrb E] (f :E[X][X]) :E[X][X] :=
 f.sum fun i c=>monomial i c.derivative
def jacobian {E F:Type} [zrb E] [zrb F] (j:E →+* F) (x y :F) (f g:E[X][X]) :F :=
  atPair j x y (physicalDeriv f)*atPair j x y g.derivative -
    atPair j x y f.derivative*atPair j x y (physicalDeriv g)
def gauge {E :Type} [zrb E] [zZE L E] (b c:L) (y :E) :E :=
 algebraMap L E b+algebraMap L E c*y
def valueCoeffs {E :Type} [zrb E] (N :E[X]) (i:Fin (N.natDegree+1)) :E :=
 N.coeff i
def valueZeros {E :Type} [zrb E] (v :Valuation E ℤᵐ⁰) (N :E[X]) :ℕ :=
 Tq v (valueCoeffs N) - poleOrder v (N.coeff 0)+KB v (N.coeff 0)
structure Slice {E :Type} [zrb E] [zZE L E] (f :E[X][X]) (s a :ℕ) where
 g:E[X][X]
 degree :g.natDegree≤f.natDegree
 weight:HE g s (a+s+1)
 common : ∀ v :CurvePlace L E,sheetPole v.value g≤ sheetPole v.value f
 b:L
 c:L
 c_ne :c≠0
 size :ℕ
 pt:Fin size→AlgebraicClosure E×AlgebraicClosure E
 distinct :Function.Injective pt
 f_zero : ∀ i,atPair (algebraMap E _) (pt i).1 (pt i).2 f=0
 g_zero : ∀ i,atPair (algebraMap E _) (pt i).1 (pt i).2 g=0
 simple : ∀ i,jacobian (algebraMap E _) (pt i).1 (pt i).2 f g≠0
 gauge_ne : ∀ i,gauge b c (pt i).2≠0
 N :E[X]
 monic:N.Monic
 constant_ne :N.coeff 0≠0
 product :N.map (algebraMap E (AlgebraicClosure E)) =
   ∏ i,((z7y: (AlgebraicClosure E)[X])-Polynomial.C
     (atPair (algebraMap E _) (pt i).1 (pt i).2 f.derivative /
     gauge b c (pt i).2^(f.natDegree-2)))
end
end qZu9hjc
end
end
section
section
set_option autoImplicit true
namespace qCQTZAc
noncomputable section
open Polynomial
open P5 (K)
open P5_7_2 (A)
open P5_7_1 (TopRow topLift atTop)
open qaySLPd (SupportCaps orient topLabel)
open cu (FX Jet)
open DP (Source U4 Fg)
abbrev degreeBound:ℕ:=131071+2703
abbrev cheapHeight:ℕ:=64*A - 1+114*2707
abbrev liftHeight:ℕ:=0x5f5e100
def Weighted (d W:ℕ) (B:TopRow) :Prop :=
 ∀ e∈B.support,(B.coeff e).natDegree+d*e 1+(d-1)*e 2+(d-2)*e 3≤W
structure FixedData (B:TopRow) :Prop where
 ne :B≠0
 squarefree :Squarefree (topLift B)
 support :SupportCaps 87 27 12 0 B
 weight:Weighted degreeBound cheapHeight B
def ContainsFixed (P B:TopRow) :Prop :=
  ∀ Q:MvPolynomial (Fin 4) FX,Irreducible Q→0<Q.degreeOf 3 →
    Q.degreeOf 0=0→Q∣topLift P→Q∣topLift B
def Singular (B:TopRow) (z :K) (S:K[X]) :Prop :=
  ∃ i:Fin 2,atTop (orient i B) (topLabel i z) S=0 ∧
    atTop (MvPolynomial.pderiv 3 (orient i B)) (topLabel i z) S=0
def LiftAt (d W:ℕ) (f :Jet) :Prop :=
  ∃ (P:Source) (u:FX),u≠0∧U4 P=algebraMap FX Jet u*f ∧
    ∀ j i a e,Fg P j i a e≠0→a+d*i+(d-1)*j≤W
end
end qCQTZAc
end
section
namespace qrKC9pb
noncomputable section
open Polynomial
open cu (L)
open P5_7_7 (Dg seedDerivative)
open scoped WithZero
export q7kdBxd (Input EC a7W constant amm seed chartEq physicalDerivative
 horizontalDegree polarBudget intrinsic finitePoles)
def jU (J:Input) (recip:Bool) :EC J :=
 let y :=a7W J (z7y:Dg)
 if recip then y⁻¹ else y
def KM (J:Input) (recip:Bool) :Dg →+* EC J :=
 eval₂RingHom ((a7W J).comp C) (jU J recip)
theorem chartEval_X (J:Input) (r :Bool) :
 KM J r (z7y:Dg)=jU J r :=eval₂_X _ _
theorem chartEval_false (J:Input) :KM J false=a7W J:= by
 apply z86
 · intro a
   exact eval₂_C _ _
 · exact chartEval_X J false
theorem rootMap_eq_zero_iff (J:Input) (G:Dg) :
  a7W J G=0↔J.F∣G:= by
 rw [a7W,RingHom.comp_apply,map_eq_zero_iff _
  (IsFractionRing.injective (AdjoinRoot J.F) (EC J)),AdjoinRoot.mk_eq_zero]
theorem rootMap_ne_zero_of_degree (J:Input) {G:Dg}
  (hG:G≠0) (hd:G.natDegree<J.l) :a7W J G≠0:= by
 intro hz
 exact (not_le_of_gt hd) (J.Ca.jU ▸ natDegree_le_of_dvd
  ((rootMap_eq_zero_iff J G).mp hz) hG)
theorem ordinate_false_ne_zero (J:Input) :jU J false≠0 :=
 rootMap_ne_zero_of_degree J Polynomial.X_ne_zero
  (by rw [Polynomial.natDegree_X]; exact J.Ca.two_le)
theorem chart_root (J:Input) (r :Bool) :KM J r (chartEq J r)=0:= by
 have hf :KM J false J.F=0:= by
   rw [chartEval_false,rootMap_eq_zero_iff]
 cases r
 · exact hf
 · let y :=jU J false
   let:=invertibleOfNonzero (ordinate_false_ne_zero J)
   change J.F.reverse.eval₂ ((a7W J).comp C) y⁻¹=0
   simpa only [invOf_eq_inv] using (eval₂_reverse_eq_zero_iff ((a7W J).comp C) y J.F).2 hf
def polar (J:Input) (recip:Bool) :EC J :=
 KM J recip (chartEq J recip).derivative
open private ordinate_nonzero from ProximityPrize.SubmissionLower.ZsWhgLc
theorem polar_false_ne_zero (J:Input) :polar J false≠0:= by
 rw [polar,chartEval_false]
 have hl:0<J.F.natDegree := by
  rw [J.Ca.jU]
  exact (by decide :0<2).trans_le J.Ca.two_le
 exact rootMap_ne_zero_of_degree J (ordinate_nonzero J.Ca)
  (J.Ca.jU ▸ natDegree_derivative_lt hl.ne')
def jet (J:Input) (recip:Bool) :EC J :=
 -(KM J recip (physicalDerivative (chartEq J recip)))/polar J recip
def variation (J:Input) (recip:Bool) :EC J :=
 -(KM J recip (seedDerivative (chartEq J recip)))/polar J recip
def aD (J:Input) (recip:Bool) :Fin 4→EC J :=
 ![amm J,seed J,jU J recip,jet J recip]
def ResidueConstant (J:Input) (v :Valuation (EC J) ℤᵐ⁰) (a :EC J) :Prop :=
 ∃ c:L,v (a-constant J c)<1
structure GraphPrime (J:Input) (recip:Bool) where
 val :Valuation (EC J) ℤᵐ⁰
 normalized:Function.Surjective val
 constants : ∀ a :L,a≠0→val (constant J a)=1
 regular : ∀ i,val (aD J recip i)≤1
 curve : ∃ i,¬ ResidueConstant J val (aD J recip i)
def Over (J:Input) {r :Bool} (D:GraphPrime J r) (a x :L) :Prop :=
 D.val (seed J-constant J a)<1∧D.val (amm J-constant J x)<1
def polarOrder {J:Input} {r :Bool} (D:GraphPrime J r) :ℕ :=
 (-WithZero.log (D.val (polar J r))).toNat
def NoHorizontalPole (J:Input) :Prop :=
  ∀ (r :Bool) (D:GraphPrime J r),
    1<D.val (variation J r)→ResidueConstant J D.val (seed J)
end
end qrKC9pb
end
section
namespace qWIOgVd
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys embed Dg)
open qGnV2ac (EquationBounds HE)
open q7kdBxd (Input)
def rev (a :L) (n:ℕ) (q:L[X]) :L[X] :=
 (q.taylor a).reflect n
abbrev x :FX:=phys z7y
structure Chart (a :L) where
 changeX:FX ≃+* FX
 constant : ∀ c:L,changeX (phys (C c))=phys (C c)
 CJ : ∀ (q:L[X]) (n:ℕ),q.natDegree≤n →
  phys (rev a n q)=x^n*changeX (phys q)
def width (s :ℕ) (P Q:L[X]) :ℕ :=
 max Q.natDegree (P.natDegree-s)
structure Rechart (J:Input) {a :L} (D:Chart a) where
 F:Dg
 Ca :EquationBounds F J.l J.h
 weight:HE F J.s (J.b+J.l*J.s)
 scalar :FX
 scalar_ne :scalar≠0
 coeff : ∀ i,(embed F).coeff i =
   C (scalar*((x^J.s)⁻¹)^i)*((embed J.F).coeff i).map D.changeX.toRingHom
end
end qWIOgVd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qrzQ9fc
noncomputable section
open Polynomial q7kdBxd
open cu (L)
open scoped WithZero
abbrev aQ:=FractionRing L[X]
def constantMap (J:Input) :L →+* EC J :=
 (a7W J).comp (Polynomial.C.comp (Polynomial.C.comp Polynomial.C))
def Wu (J:Input) :L[X] →+* EC J :=
 eval₂RingHom (constantMap J) (seed J)
def Horizontal {J:Input} {r :Bool} (D:GraphPrime J r) :Prop :=
 ∀ q:L[X],q≠0→D.val (Wu J q)=1
end
end qrzQ9fc
end
section
namespace qqi5QRb
noncomputable section
open Polynomial
open scoped WithZero
open P5 (K)
open cu (L FX)
open P5_7_7 (Dg phys seedDerivative)
open qGnV2ac (Sections)
open q7kdBxd
open IsDedekindDomain
instance rootAlgebra (J:Input) :zZE L (EC J) :=
 ((a7W J).comp (C.comp (C.comp C))).toAlgebra
theorem root_algebraMap (J:Input) (a :L) :
 algebraMap L (EC J) a=constant J a :=rfl
abbrev Chart (J:Input) (r :Bool) :=Algebra.adjoin L (Set.range (aD J r))
def coord (J:Input) (r :Bool) (i:Fin 4) :Chart J r :=
 ⟨aD J r i,Algebra.subset_adjoin ⟨i,rfl⟩⟩
def evalPhysical (J:Input) (r :Bool) :L[X] →+* Chart J r :=
 eval₂RingHom (algebraMap L _) (coord J r 0)
def evalSeed (J:Input) (r :Bool) :L[X][X] →+* Chart J r :=
 eval₂RingHom (evalPhysical J r) (coord J r 1)
def evalChart (J:Input) (r :Bool) :Dg →+* Chart J r :=
 eval₂RingHom (evalSeed J r) (coord J r 2)
private theorem coe_evalPhysical (J:Input) (r :Bool) :
   (algebraMap (Chart J r) (EC J)).comp (evalPhysical J r) =
     (a7W J).comp (C.comp C) := by
 apply z86
 · intro a
   change ((evalPhysical J r (C a) :Chart J r) :EC J)=constant J a
   simp only [evalPhysical,coe_eval₂RingHom,eval₂_C,Subalgebra.coe_algebraMap,root_algebraMap]
 · change ((evalPhysical J r z7y:Chart J r) :EC J)=amm J
   rw [evalPhysical,coe_eval₂RingHom,eval₂_X]
   rfl
private theorem coe_evalSeed (J:Input) (r :Bool) :
   (algebraMap (Chart J r) (EC J)).comp (evalSeed J r) =
     (a7W J).comp C:= by
 apply z86
 · intro a
   change ((evalSeed J r (C a) :Chart J r) :EC J)=a7W J (C (C a))
   rw [evalSeed,coe_eval₂RingHom,eval₂_C]
   exact DFunLike.congr_fun (coe_evalPhysical J r) a
 · change ((evalSeed J r z7y:Chart J r) :EC J)=seed J
   rw [evalSeed,coe_eval₂RingHom,eval₂_X]
   rfl
theorem coe_evalChart (J:Input) (r :Bool) (F:Dg) :
  (evalChart J r F:EC J)=KM J r F:= by
 change (algebraMap (Chart J r) (EC J)) ((evalChart J r) F)= _
 rw [evalChart,KM,coe_eval₂RingHom,coe_eval₂RingHom,hom_eval₂,coe_evalSeed]
 rfl
def sep (J:Input) (r :Bool) :Chart J r :=
 evalChart J r (chartEq J r).derivative
def num (J:Input) (r :Bool) :Chart J r :=
 -(evalChart J r (seedDerivative (chartEq J r)))
theorem coe_sep (J:Input) (r :Bool) : (sep J r :EC J)=polar J r :=
 coe_evalChart _ _ _
theorem gK6 (J:Input) (r :Bool) :
  variation J r=(num J r :EC J)/sep J r := by
 rw [variation,coe_sep,num,Subalgebra.coe_neg,coe_evalChart]
def pointPrime (x :L) :HeightOneSpectrum L[X] where
 asIdeal:=Ideal.span {z7y - C x}
 isPrime :=(Ideal.span_singleton_prime (X_sub_C_ne_zero x)).mpr (prime_X_sub_C x)
 ne_bot:=Ideal.span_singleton_eq_bot.not.mpr (X_sub_C_ne_zero x)
def pointVal (x :L) :Valuation FX ℤᵐ⁰:=(pointPrime x).valuation FX
structure MarkChart (J:Input) (S:Sections J.F) (γ:K) (x :L) (r :Bool) where
 map :Chart J r →ₐ[L] FX
 regular : ∀ u,pointVal x (map u)≤1
 physical_eq :map (coord J r 0)=phys z7y
 seed_eq :map (coord J r 1)=algebraMap L FX (algebraMap K L (S.seed γ))
 simple :map (sep J r)≠0
 gK6 : ∃ u:FX,pointVal x u=1 ∧
  map (num J r)/map (sep J r)=u*(phys (S.A γ)/phys (S.B γ))
end
end qqi5QRb
end
end
