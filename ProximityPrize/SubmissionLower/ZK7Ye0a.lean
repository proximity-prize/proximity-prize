import ProximityPrize.SubmissionLower.Z6Xnfpd
import ProximityPrize.SubmissionLower.ZmepBre
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
set_option Elab.async false
section
set_option autoImplicit true
namespace qlc9qed
noncomputable section
open Polynomial
open P5_7 (midAgreement)
open P5_7_1 (Input TopRow)
open aR (ao Shape jF embed)
open jA
open NR (amn)
open acZ (OV Bu)
open private cutoff from ProximityPrize.SubmissionLower.S
open private dxP from ProximityPrize.SubmissionLower.DG
inductive Bank where
 | cheap
 | strong
def Bank.m:Bank→ℕ
 | .cheap=>64
 | .strong=>120
def Bank.box :Bank→Shape
 | .cheap=>⟨87,27,12⟩
 | .strong=>⟨164,50,19⟩
def Bank.U:Bank→ℕ
 | .cheap=>640
 | .strong=>3037
def Bank.contactRank :Bank→ℕ
 | .cheap=>292256
 | .strong=>3137221
def Bank.basePole :Bank→ℕ
 | .cheap=>991536
 | .strong=>0xa3f520
def Bank.poleExcess :Bank→ℕ
 | .cheap=>15643160
 | .strong=>0x13094c39
def Bank.az0:Bank→ℕ
 | .cheap=>0x11da33a12a
 | .strong=>0xc0b8bd8a48
def Bank.rank :Bank→ℕ
 | .cheap=>0xbed14ca
 | .strong=>0xdfd7a011eac
def Bank.cut (b:Bank) :ℕ:=b.m*midAgreement - 1
def Bank.eMG (b:Bank) (h:ℕ) :ℕ :=
 h*((b.U + 1)*b.basePole+b.poleExcess)
def Bank.ambientCount (b:Bank) (h:ℕ) :ℕ :=
 (b.U + 1)*(b.az0+b.basePole*h)
structure OnePole (x :Input) where
 data :jF x.Γ x.F.scalar
 bY:kH data
 block :data.H=x.H
 height:data.H.natDegree=x.h
 Kw : ∀ γ,data.z γ=embed (x.M.label γ)
def Aw (b:Bank) (h t:ℕ) :Submodule ao jK :=
 ((OV b.box).restrictScalars ao).comap Bu ⊓
 ((MvPolynomial.restrictWeightedDegree (R:=iP)
     (Pi.single (none :mA) 1) b.U).restrictScalars ao).comap Bu ⊓
 cutoff h (t+(b.box.b+b.box.j)*h)
def ays (m:ℕ) (x v :ao) :Submodule ao jK :=
  ⨅ e :mA →₀ ℕ,
    ((Ideal.span {((Polynomial.X-Polynomial.C x)^(m-3*e (some 0)) :
      ao[X])}).restrictScalars ao).comap
      (((MvPolynomial.lcoeff ao[X] e).restrictScalars ao).comp (dxP x v))
theorem bsz (m:ℕ) (x v :ao) (F:jK) :
    F∈ays m x v ↔ ∀ e :mA →₀ ℕ,
      (Polynomial.X-Polynomial.C x)^(m-3*e (some 0)) ∣
        (aCk x v F).coeff e := by
  simp only [ays,Submodule.mem_iInf,Submodule.mem_comap,Submodule.restrictScalars_mem,
    LinearMap.comp_apply,LinearMap.restrictScalars_apply,MvPolynomial.lcoeff_apply,
    Ideal.mem_span_singleton]
  rfl
def contacts (x :Input) (b:Bank) :Submodule ao jK :=
 ⨅ i:P5.I,ays b.m (embed (P5.node i)) (x.word i)
def pole {x :Input} (P:OnePole x) (b:Bank) :Submodule ao jK :=
 amn P.data P.bY b.box (jA.jH P.data.H)
def aV {x :Input} (P:OnePole x) (b:Bank) (t:ℕ) :Submodule ao jK :=
 Aw b x.h t ⊓ (contacts x b ⊓ pole P b)
abbrev aD:mA ≃ Fin 4 :=(finSuccEquiv 3).symm
def toTop (F:jK) :TopRow :=MvPolynomial.rename aD F
def powerAt (h t:ℕ) :ℕ:=1+(Bank.strong.cut - t)/(3*h)
end
end qlc9qed
end
section
set_option autoImplicit true
namespace qQ9yWTb
noncomputable section
open Polynomial
open P5 (K p blockLength)
open P5_7 (gap normalWidth)
open P5_7_1 (Input degree retainedFee)
open cu (L FX Equation qD)
open Qt (gY)
abbrev D:=degree
abbrev G:=gap D
abbrev width :=normalWidth D
abbrev Raw:=(MvPolynomial (Fin 2) L[X])[X]
abbrev Curve :=MvPolynomial (Fin 2) L
def embed:Raw →+* Equation :=
 Polynomial.mapRingHom (MvPolynomial.map (algebraMap L[X] FX))
abbrev height (f :Raw) :=gY (embed f)
abbrev WordChart (x :Input) (T:Finset K) :=
 P5_7_7.DualWord D x.M.word T x.F.scalar
def root {x :Input} {T:Finset K} (J:WordChart x T) (f :Raw) (γ:K) :Prop :=
 (embed f).eval₂ (qD (x.M.label γ)) (P5_7_7.dualValue J γ)=0
def weight {x :Input} {T:Finset K} (J:WordChart x T) (f :Raw) :ℕ :=
  f.support.sup fun i=>(f.coeff i).support.sup fun a =>
    ((f.coeff i).coeff a).natDegree+f.natDegree*J.u₀+i*(J.u₁-J.u₀)
def Moving (f :Raw) :Prop :=
 f≠0 ∧ ∀ q:Raw,Irreducible q→q∣f→0<q.natDegree∧0<height q
structure Witness where
 g:ℕ
 cz :ℕ
 ct :ℕ
 j:ℕ
 W:ℕ
def modulus (w:Witness) :=w.W+1+w.j*width
def highDigits (e c g:ℕ) :=e*(c+1)+e+g
def highRate (e :ℕ) (w:Witness) :=
 highDigits e w.cz w.g+p*highDigits e w.ct w.g
def polar (e W:ℕ) :=(6*e-2)*W-(3*e*e-2*e+1)*width
def lowRate (e W:ℕ) :=
 (7+6*e)*G+2*e*blockLength+polar e W+(2*e-1)
def base (e :ℕ) :=4*e*e+1
def B (e W v :ℕ) :ℚ:=((lowRate e W:ℚ)*v)/G+base e
def Good (e u:ℕ) (w:Witness) :Prop :=
  let E :=e+w.g
  let L:=width
  3≤e∧e<p∧0< u∧u<p∧0<w.cz∧0<w.ct∧w.j≤w.g ∧
  e*L≤w.W∧E*L< modulus w ∧
  ((w.cz+1)*u+1)*((w.ct+1)*u+1)*(L*E*(E+1)/2+L*w.j*(w.j+1)/2) <
    (w.g+1)*(w.cz*u+1)*(w.ct*u+1)*modulus w ∧
  e*(e-1)*L≤(2*e-2)*w.W∧(2*e-2)*w.W-e*(e-1)*L<p ∧
  (3*e*e-2*e+1)*L≤(6*e-2)*w.W∧highDigits e w.cz w.g*u<p
def gu (e u:ℕ) (w:Witness) :Prop :=
 let d:=3*G^2
 let b:=base e*G
 let c:=lowRate e w.W
 d*(highRate e w*u+(e+1))+10*b^2≤d*retainedFee ∧
 d*(e+1)+10*(c*u+b)^2≤d*retainedFee
def site (x :Input) (γ:K) :Fin 2→L :=
 let z :=algebraMap K L (x.M.label γ)
 ![z,z^p]
def Usable (q:Curve) (s :Fin 2→L) :Prop :=
  ∃ a :Fin 2→PowerSeries L,(∀ i,PowerSeries.constantCoeff (a i)=s i) ∧
    MvPolynomial.eval₂ PowerSeries.C a q=0 ∧ ∃ i,PowerSeries.coeff 1 (a i)≠0
end
end qQ9yWTb
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P5_7_7
noncomputable section
open Polynomial Finset
open P5 (I)
open P5_7 (OneSeedEquation atNative)
open scoped Classical
def c1 :Prop :=
  ∀ D w T z S,UJ D w T z S →
    ∀ f :OneSeedEquation,f.natDegree=1 →
      (∀ γ∈T,atNative f (z γ) (S γ)=0) →
      ∀ i:I,
        (T.filter fun γ=>hit w S γ i).card≤gY f ∨
        (T.filter fun γ => ¬ hit w S γ i).card≤gY f
def c2 :Prop :=
  ∀ D w T z S,UJ D w T z S →
    T.card≤1 ∨ ∃ U⊆T,T.card≤U.card+1∧Nonempty (DualWord D w U S)
end
end P5_7_7
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qd4jtSc
open qMHqmcc (GG receipt appendGrades)
private theorem vQf0 :GG b2 48 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf1 :GG b2 49 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf2 :GG b2 50 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf3 :GG b2 51 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf4 :GG b2 52 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf5 :GG b2 53 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf6 :GG b2 54 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf7 :GG b2 55 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem r1 :GG b2 48 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQf0 vQf1) vQf2) vQf3) vQf4) vQf5) vQf6) vQf7
private theorem vQf8 :GG b2 56 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf9 :GG b2 57 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf10 :GG b2 58 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf11 :GG b2 59 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf12 :GG b2 60 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf13 :GG b2 61 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf14 :GG b2 62 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem vQf15 :GG b2 63 1:= by
 repeat' apply And.intro
 all_goals first | exact True.intro | apply receipt 2535 rfl <;> with_unfolding_all rfl
private theorem r2 :GG b2 56 8:=appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades (appendGrades vQf8 vQf9) vQf10) vQf11) vQf12) vQf13) vQf14) vQf15
theorem p2_3:GG b2 48 16:=appendGrades r1 r2
end qd4jtSc
end
