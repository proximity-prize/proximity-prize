import ProximityPrize.SubmissionLower.ZTbQzvb
import ProximityPrize.SubmissionLower.ZzP7Fpd
set_option Elab.async false
section
namespace q1kuFjb
noncomputable section
open Polynomial Finset qQ9yWTb qb0hmCe


open cu (L)
open E7 (CurvePlace poleOrder)
open scoped Classical WithZero
def restrictOver {E :Type} [CommRing E] (b:L →+* E) (z :Fin 2→E) :
    Raw →+* E[X][X] :=
  mapRingHom (MvPolynomial.eval₂Hom (mapRingHom b) (C ∘ z))
def restrict {q:Curve} (Cq:CurveModel q) :Raw →+* Cq.E[X][X] :=
 restrictOver (algebraMap L Cq.E) Cq.seed
def coeffIntegral {E :Type} [Field E] (v :Valuation E ℤᵐ⁰) (f :E[X][X]) :Prop :=
 ∀ i j,v ((f.coeff i).coeff j)≤1
structure AtSite {q:Curve} (Cq:CurveModel q) (s :Fin 2→L) where
 map :Cq.E →ₐ[L] LaurentSeries L
 place :CurvePlace L Cq.E
 value : ∀ c,place.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (map c)
 arc : ∃ a :Fin 2→PowerSeries L,
  (∀ i,map (Cq.seed i)=(a i:LaurentSeries L)) ∧
  (∀ i,PowerSeries.constantCoeff (a i)=s i) ∧
  (∃ i,PowerSeries.coeff 1 (a i)≠0)
def headScalar {E :Type} [Semiring E] (f :E[X][X]) :E :=
 (f.coeff f.natDegree).leadingCoeff
structure Factors {q:Curve} (Cq:CurveModel q) (F:Raw) (e a s W:ℕ) where
 scalar_ne :headScalar (restrict Cq F)≠0
 scalar_height: (∑ᶠ v :CurvePlace L Cq.E,poleOrder v.value (headScalar (restrict Cq F))) ≤
   height F*q.totalDegree
 amm:Cq.E[X]
 monic:amm.Monic
 n:ℕ
 f :Fin n→Cq.E[X][X]
 product :restrict Cq F=C (C (headScalar (restrict Cq F))*amm) * ∏ j,f j
 irreducible : ∀ j,Irreducible (f j)
 positive : ∀ j,0<(f j).natDegree
 normalized : ∀ j,((f j).coeff (f j).natDegree).leadingCoeff=1
 degree : ∑ j,(f j).natDegree≤e
 height_le :coeffHeight (C amm) + ∑ j,coeffHeight (f j)≤height F*q.totalDegree
 weight : ∀ j i,((f j).coeff i).natDegree+(f j).natDegree*a+i*s≤W ∨
   (f j).coeff i=0
end
end q1kuFjb
end
section
namespace qFD8jve
noncomputable section
open Finset Polynomial qQ9yWTb qb0hmCe


open P5_7_7 (phys)
open cu (L FX)
open E7 (Tq poleOrder)
open scoped Classical WithZero
def aFA {E :Type} [Field E] (v :Valuation E ℤᵐ⁰) (F:E[X][X]) (b:ℕ) :Prop :=
 ∀ i j,v ((F.coeff i).coeff j)≤WithZero.exp (b:ℤ)
def sheetPole {E :Type} [Field E] (v :Valuation E ℤᵐ⁰) (f :E[X][X]) :ℕ :=
  Tq v (fun ij:Fin (f.natDegree+1) ×
    Fin ((f.support.sup fun i=>(f.coeff i).natDegree)+1) =>
     (f.coeff ij.1).coeff ij.2)
def seedPole {q:Curve} (C:CurveModel q) (R:SiteTarget) (v :Valuation C.E ℤᵐ⁰) :ℕ :=
 if R.b=0∧R.d=0 then 0 else poleOrder v (C.seed R.coord)
def aaD {E :Type} [Field E] (F:E[X][X]) :E[X] :=
 F.map (evalRingHom (0:E))
def polarResultant {E :Type} [Field E] (F:E[X][X]) :E[X] :=
 F.resultant F.derivative F.natDegree (F.natDegree-1)
def guard {E :Type} [Field E] (F:E[X][X]) :E :=
 (polarResultant F).trailingCoeff*(aaD F).trailingCoeff
def Vanishes (y :FX) :Prop :=
 ∃ A B:L[X],A.coeff 0=0∧B.coeff 0≠0∧y=phys A/phys B
end
end qFD8jve
end
section
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace qNu3xvc
noncomputable section
open Polynomial Finset
open P5 (p)
open cu (L)
open E7 (CurveField CurvePlace)



open scoped Classical
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d→A.d<p →
    horizontalDegree A<p→NoHorizontalPole A
def c3:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (S:Sections A),
    CurveField L E→2≤A.d→A.d<p→NoHorizontalPole A →
    ∀ γ∈S.marks,∀ x∈(S.den γ).roots.toFinset,
      ∃ (r :Bool) (v :GraphVal A r),Over v (S.place γ) x ∧
        (S.den γ).rootMultiplicity x≤poleCharge v
def c4 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),CurveField L E→2≤A.d→A.d<p →
    ∀ (ι:Type) [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L) (r :ι→Bool)
      (v : ∀ i,GraphVal A (r i)),
      Function.Injective (fun i=>(w i,x i)) →
      (∀ i,qg A (w i))→(∀ i,Over (v i) (w i) (x i)) →
      (∑ i,poleCharge (v i))≤polarRate A*A.h
def c5:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (S:Sections A),
    CurveField L E→A.d = 1→finitePoles S≤(2*A.b+A.s)*A.h
private theorem finite_budget (charge :c3) (degree :c4)
   {E :Type} [Field E] [Algebra L E] (A:Equation E) (S:Sections A)
   (hc:CurveField L E) (hd:2≤A.d) (hp:A.d<p) (hor :NoHorizontalPole A) :
   finitePoles S≤polarRate A*A.h:= by
 let U:=S.marks.sigma fun γ=>(S.den γ).roots.toFinset
 let w (i : ↥U) :=S.place i.val.1
 let x (i : ↥U) :=i.val.2
 have hw:Function.Injective (fun i=>(w i,x i)) := by
   intro i j hij
   have hi:=(Finset.mem_sigma.mp i.prop).1
   have hj:=(Finset.mem_sigma.mp j.prop).1
   exact Subtype.ext (Sigma.ext (S.distinct hi hj (congrArg Prod.fst hij))
     (heq_of_eq (congrArg Prod.snd hij)))
 have hv (i : ↥U) : ∃ (r :Bool) (v :GraphVal A r),Over v (w i) (x i) ∧
     (S.den i.val.1).rootMultiplicity (x i)≤poleCharge v := by
   obtain ⟨hγ,hx⟩:=Finset.mem_sigma.mp i.prop
   exact charge A S hc hd hp hor _ hγ _ hx
 choose r v hv hle using hv
 calc
   finitePoles S = ∑ i : ↥U,(S.den i.val.1).rootMultiplicity (x i) := by
     change finitePoles S = ∑ i∈U.attach,(S.den i.val.1).rootMultiplicity i.val.2
     rw [Finset.sum_attach U (fun i=>(S.den i.1).rootMultiplicity i.2)]
     unfold U finitePoles
     rw [Finset.sum_sigma]
     refine sum_congr rfl fun γ _ => ?_
     rw [← IsAlgClosed.card_roots_eq_natDegree,← Multiset.toFinset_sum_count_eq]
     exact sum_congr rfl fun _ _=>Polynomial.count_roots _
   _ ≤ ∑ i,poleCharge (v i) :=sum_le_sum fun i _=>hle i
   _≤polarRate A*A.h:=degree A hc hd hp _ w x r v hw
     (fun i=>S.regular _ (Finset.mem_sigma.mp i.prop).1) hv
private theorem budgets (d e b u s W F:ℕ) (hd:0<d) (hde :d≤e)
    (hW:e*F≤W) (hb:b+d*(u+s)=W) (hF:2*u+s=F) :
    (2*d-2)*b+d*(d-1)*s≤(2*e-2)*W-e*(e-1)*F ∧
    (6*d-2)*b+(3*d*d-1)*s+(2*d-1) ≤
      (6*e-2)*W-(3*e*e-2*e+1)*F+(2*e-1) := by
  have he :0<e :=hd.trans_le hde
  have hd₁:1≤d:=hd
  have he₁:1≤e :=he
  have ha :2≤2*d:= by omega
  have ha' : 2≤2*e := by omega
  have hc:2≤6*d:= by omega
  have hc' : 2≤6*e := by omega
  have hb' : 1≤3*d*d:=Nat.mul_pos (by omega) hd
  have hh:2*e≤3*e*e :=Nat.mul_le_mul_right e (by omega)
  have hx :1≤2*d:= by omega
  have hy :1≤2*e := by omega
  have heW:e*(e-1)*F≤(2*e-2)*W:= by
    have h:e-1≤2*e-2 := by omega
    calc
      _=(e-1)*(e*F) := by ring
      _≤(2*e-2)*W:=Nat.mul_le_mul h hW
  have hpW: (3*e*e-2*e+1)*F≤(6*e-2)*W:= by
    have hj:3*e*e-2*e+1≤(6*e-2)*e := by
      have hm: (6*e)*e=2*(3*e*e) := by ring
      rw [Nat.sub_mul,hm]
      omega
    exact (Nat.mul_le_mul_right _ hj).trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hW)
  zify [ha,ha',hc,hc',hb',hh,hx,hy,hd₁,he₁,heW,hpW] at hb hF hW hde ⊢
  have hu:0≤(u:ℤ) :=Int.natCast_nonneg u
  have hFF:0≤(F:ℤ) :=Int.natCast_nonneg F
  constructor
  · have h₁:0≤2*(W:ℤ)-((e :ℤ)+d-1)*F:= by
      nlinarith [mul_nonneg (show 0≤(e :ℤ)-d+1 by omega) hFF]
    nlinarith [mul_nonneg (sub_nonneg.mpr hde) h₁,
      (by linear_combination (2*(d:ℤ)-2)*hb-(d:ℤ)*((d:ℤ)-1)*hF :
        (2*(d:ℤ)-2)*b+(d:ℤ)*((d:ℤ)-1)*s =
          (2*(d:ℤ)-2)*W-(d:ℤ)*((d:ℤ)-1)*F)]
  · have h₁:0≤6*(W:ℤ)-(3*((e :ℤ)+d)-2)*F+2 := by
      nlinarith [mul_nonneg (show 0≤3*((e :ℤ)-d)+2 by omega) hFF]
    have hdZ: (0:ℤ)<d:= by exact_mod_cast hd
    have h₂:0≤(2*(d:ℤ)-2)*u:=mul_nonneg (by omega) hu
    nlinarith [mul_nonneg (sub_nonneg.mpr hde) h₁,
      (by linear_combination (6*(d:ℤ)-2)*hb-(3*(d:ℤ)^2-2*d+1)*hF :
        (6*(d:ℤ)-2)*b+(3*(d:ℤ)^2-1)*s+(2*d-1)+(2*d-2)*u =
          (6*(d:ℤ)-2)*W-(3*(d:ℤ)^2-2*d+1)*F+(2*d-1))]
end
end qNu3xvc
end
section
set_option autoImplicit true
namespace qqf9uAa
open P5_7_3 (fO Test Lc threshold apo awI)
def c1 :Prop :=RangeSigns 2704 2715
def c2 :Prop :=RangeSigns 2715 2750
def c3:Prop :=RangeSigns 2750 2800
def c4 :Prop :=RangeSigns 2800 2919
def c5:Prop :=RangeSigns 2919 2980
def c6:Prop :=RangeSigns 2980 3100
def c7:Prop :=RangeSigns 3100 3555
private theorem last (b:fO) (hb:3555≤b.jX.lo) :BandSigns b:= by
 cases b
 case uH =>
  exact ⟨ordinary3555,GradeSigns.append grades3555A grades3555B⟩
 all_goals exact ((Nat.not_le_of_lt (by decide)) hb).elim
private theorem signs_of_tests {b:fO} (hs :BandSigns b) (x :Test b) :
   Signs (Lc b x) b.jX.lo (threshold b x) (apo b x) := by
 cases x
 · exact hs.1
 · rename_i i
   exact hs.2.get i
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
  (h6:c6) (h7:c7) :P5_7_3.c4 := by
 intro b h hl hh x
 have ha :2704≤b.jX.lo:= by cases b <;> decide
 have hsign:BandSigns b:= by
  by_cases h₁:b.jX.lo<2715
  · exact h1 b ha h₁
  by_cases h₂:b.jX.lo<2750
  · exact h2 b (by omega) h₂
  by_cases h₃:b.jX.lo<2800
  · exact h3 b (by omega) h₃
  by_cases h₄:b.jX.lo<2919
  · exact h4 b (by omega) h₄
  by_cases h₅:b.jX.lo<2980
  · exact h5 b (by omega) h₅
  by_cases h₆:b.jX.lo<3100
  · exact h6 b (by omega) h₆
  by_cases h₇:b.jX.lo<3555
  · exact h7 b (by omega) h₇
  exact last b (by omega)
 obtain ⟨hp,hd⟩:=signs_of_tests hsign x
 exact strict_of_support hl (hh.trans (awI b).2.1.le) hp hd
end qqf9uAa
end
section
namespace P5_7_3_5_2
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open P5_7 (midAgreement)
open qkgz7gb (PlaneCurve rV)
open qb0hmCe (CurveModel coeffHeight cLN SiteTarget)
open P5_7_7 (phys)
open cu (L FX j9)
open E7 (CurvePlace)
def atPolynomial (f :L[X][X]) (S:K[X]) :FX :=
 f.eval₂ phys (phys (j9 S))
structure Sheet {q:PlaneCurve} (C:CurveModel q) (z :K→K) (S:K→K[X]) where
 f :C.E[X][X]
 irreducible :Irreducible f
 positive :0<f.natDegree
 normalized: (f.coeff f.natDegree).leadingCoeff=1
 marks :Finset K
 atPlace : ∀ γ∈marks,C.E →ₐ[L] LaurentSeries L
 place :K→CurvePlace L C.E
 distinct :Set.InjOn place (marks :Set K)
 value : ∀ γ (hγ:γ∈marks) c,
   (place γ).value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (atPlace γ hγ c)
 arc : ∀ γ (hγ:γ∈marks),∃ a :Fin 2→PowerSeries L,
   (∀ i,atPlace γ hγ (C.seed i)=(a i:LaurentSeries L)) ∧
   (∀ i,PowerSeries.constantCoeff (a i)=rV z γ i) ∧
   (∃ i,PowerSeries.coeff 1 (a i)≠0)
 integral : ∀ γ∈marks,∀ i j,(place γ).value ((f.coeff i).coeff j)≤1
 root : ∀ γ (hγ:γ∈marks),atPolynomial (cLN (atPlace γ hγ) 0 f) (S γ)=0
variable {q:PlaneCurve} {C:CurveModel q} {z :K→K} {S:K→K[X]}
abbrev Sheet.d (F:Sheet C z S) :=F.f.natDegree
abbrev Sheet.h (F:Sheet C z S) :=coeffHeight F.f
def Sheet.weight (F:Sheet C z S) (D W:ℕ) :Prop :=
 ∀ i,F.f.coeff i≠0→(F.f.coeff i).natDegree+i*D ≤W
structure Prepared (q:PlaneCurve) (z :K→K) (S:K→K[X]) (T:Finset K) (D e W u:ℕ) where
 curve :CurveModel q
 n:ℕ
 part:Fin n→Sheet curve z S
 inside : ∀ j,(part j).marks⊆T
 zJ: (T \ univ.biUnion (fun j=>(part j).marks)).card≤u*q.totalDegree
 degree : ∑ j,(part j).d≤e
 height : ∑ j,(part j).h≤u*q.totalDegree
 weight : ∀ j,(part j).weight D W
structure Variation (F:Sheet C z S) where
 marks :Finset K
 Bp:marks⊆F.marks
 num :K→ L[X]
 den:K→ L[X]
 den_ne : ∀ γ∈marks,den γ≠0
 reduced : ∀ γ∈marks,IsCoprime (num γ) (den γ)
 simple : ∀ γ (hγ:γ∈marks),
   atPolynomial (cLN (F.atPlace γ (Bp hγ)) 0 F.f).derivative (S γ)≠0
 formula : ∀ γ (hγ:γ∈marks),
   let a :=F.atPlace γ (Bp hγ)
   phys (num γ)/phys (den γ) =
     -(atPolynomial (cLN a 1 F.f) (S γ)/atPolynomial (cLN a 0 F.f).derivative (S γ))
def Variation.DG {F:Sheet C z S} (V:Variation F) (D:ℕ) (γ:K) :ℕ :=
 max (V.den γ).natDegree ((V.num γ).natDegree-D)
def Sheet.direction (F:Sheet C z S) (γ:K) (i:Fin 2) :L :=
 if h:γ∈F.marks then (F.atPlace γ h (C.seed i)).coeff 1 else 0
def targetHit (R:SiteTarget) (z :K→K) (S:K→K[X]) (γ:K) :Prop :=
 let a :=rV z γ R.coord
 R.c+R.d*a≠0∧(j9 (S γ)).eval R.center*(R.c+R.d*a)=R.a+R.b*a
def exception {F:Sheet C z S} (V:Variation F) (R:SiteTarget) (γ:K) :Prop :=
 targetHit R z S γ ∧ ¬ ((V.num γ).eval R.center=0↔R.det=0∨F.direction γ R.coord=0)
structure Starts (T:Finset K) (z :K→K) (S:K→K[X]) where
 target :Fin 2→SiteTarget
 distinct : (target 0).center≠(target 1).center
 coordinate : ∀ i,(target i).coord=i
 invertible : ∀ i,(target i).det≠0
 lg : ∀ γ∈T,∀ i,targetHit (target i) z S γ
def gap (D:ℕ) :ℕ:=midAgreement-D
def BranchBudget (F:Sheet C z S) (D except poles :ℕ) :Prop :=
  ∃ V:Variation F,(F.marks \ V.marks).card≤except*F.h ∧
    ∑ γ∈V.marks,V.DG D γ≤poles*F.h
end
end P5_7_3_5_2
end
