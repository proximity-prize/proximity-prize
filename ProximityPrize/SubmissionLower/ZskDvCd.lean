import ProximityPrize.SubmissionLower.AR
import ProximityPrize.SubmissionLower.E1
import ProximityPrize.SubmissionLower.ZFZJbJc
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.CE
set_option Elab.async false
section
set_option autoImplicit true
section
namespace Bm
open xE (sP)

open acY Finset
open scoped BigOperators




local notation "aKH" => GI.kJ
private def choose (a b c:sP→aKH) (i:sP) :aKH :=
 if i.1.val<2008 then a i else if i.1.val<3012 then b i else c i
end Bm
end
end
section
set_option autoImplicit true
section
namespace bJ
noncomputable section
open Polynomial
open P4 (I K k node dw)
open aR (af Shape shape aO bY qP iH ceilDiv)
open scoped BigOperators
abbrev gZ:ℕ:=k - 1+P4.ajO.toNat
abbrev bf :ℕ:=gZ+1
abbrev mV:ℕ:=dw - gZ
abbrev sC:ℕ:=mV+3
abbrev m6:Shape :=⟨125, 51,13⟩
abbrev M8:ℕ:=93*dw - 1
abbrev aPd:ℕ:=50000
abbrev gV:ℕ:=0x3a25a1bb63397c6+(0x527110dea183b+aPd)
structure Messages (w:I→K) (Γ:Finset K) (s :K→K[X]) :Prop where
 distinct :Set.InjOn s (Γ:Set K)
 degree : ∀ γ∈Γ,(s γ).natDegree≤gZ
 lg : ∀ γ∈Γ,∃ T:Finset I,dw≤T.card ∧ ∀ i∈T,(s γ).eval (node i)=w i
 word_fixed : ∀ i,P4.twist (w i)=w i
 scalar_fixed : ∀ γ∈Γ,(s γ).map P4.twist=s γ
def tB {n:ℕ} (P:af n) (D:ℕ) :Prop :=
  ∀ m∈P.support,(P.coeff m).natDegree +
    m.sum (fun i a=>(gZ - i.val)*a)≤D
def wm (f :af 4) :Prop :=
 Irreducible f∧0<(shape f).t∧aO (shape f) m6∧tB f M8
export gW (wD Valid oL wP LN Bank Dj aRG
 Contact aaA V7 Gq acr PR aYp)
def x5:Bank→ℕ
 | .ag=>0xe3928b4a0a1b846
 | .dB=>0xe3e68f0e6bd9a56
abbrev Ao:ℕ:=3000*dw - 1
def Pq (b:Bank) (w:I→K) (T:ℕ) (P:af 4) :Prop :=
 aO (shape P) b.box∧aRG P∧tB P T∧Contact b w P
inductive asQ where
 | iy
 | product
 deriving DecidableEq
abbrev aHc:ℕ:=2331
abbrev aM1 :ℕ:=885
abbrev aPr :ℕ:=0x14476be8
abbrev aWz :ℕ:=0x6dac2c0
abbrev mu:ℕ:=30634
abbrev tau:ℕ:=24507
abbrev nu:ℕ:=765
def Rb (p q:Shape) :ℕ :=
  let M:=bf
  let u:=M+1
  let v :=M+2
  let g:Shape :=⟨max p.b (p.j+1),p.j+1,min (p.t+1) ((p.j+1)/3)⟩
  let a :=qP u p
  let b:=qP v p
  let iy :=iH p q (bY u p) (bY v p)
  let base :=iH p q a b+u*iH p q g b+v*iH p q g a
  if 3*(p.t+1)≤p.j+1∧2≤p.t+1 ∧
      3*(2+(u - 5)*p.t)≤a.j∧3*(2+(v - 5)*p.t)≤b.j ∧
      2*u≤a.t∧2*v≤b.t then
    let s :Shape :=⟨1,4, 2⟩
    let jO:ℤ:=(u:ℤ)*wP p q s b+(v :ℤ)*wP p q s a +
      (u:ℤ)*(v :ℤ)*(wP p q s g - wP p q s s)
    min iy (min base ((base :ℤ) - jO).toNat)
  else min iy base
def Ix (x q:Shape) :ℕ :=
  let p:=x.iU
  ceilDiv (Rb p q) 32 +
    ceilDiv ((P4.t+2*mV)*x.b*q.b*(bY (bf+1) p).b)
      mV
def sL (x q:Shape) :ℕ :=
  let p:=x.iU
  let h:=bY bf p
  let auxBox :=q.plus (p.scale 4)
  let qv :=iH p q auxBox h+2*x.t*iH p p p h
  let points :=iH p q auxBox p+2*x.t*iH p p p p
  2*gZ*x.b*q.b +
    ceilDiv (P4.t*qv+2*mV*points) (32*mV)
def W5 (mode :asQ) (x q:Shape) :ℕ :=
  match mode with
  | .iy=>sL x q
  | .product =>
    let p:=x.iU
    let h:=bY bf p
    sL x q+ceilDiv
      (P4.t*iH p q p h+2*mV*iH p q p p) (32*mV)
def aHo (mode :asQ) (x q:Shape) (l:ℕ) :ℕ :=
 W5 mode x q+ceilDiv (Ix x q) l
abbrev dJ:=aHo .iy
def ajN (p:Shape) :Shape :=
 let i:=3+bf*(p.j - 2)
 ⟨max (1+bf*(p.b - 1)) i,i,min (bf+1) (i/3)⟩
def lY (x :Shape) :ℕ :=
  let p:=x.iU
  let h:=if x.t=1 then ajN p else bY (bf+4) p
  let q:Shape :=⟨aPr,aWz,0⟩
  let big:Shape :=⟨aHc+q.b/tau,aM1+q.j/tau,0⟩
  let cut:Shape :=⟨max (max h.b big.b) (max h.j (big.j+1)),
    max h.j (big.j+1),max 1 h.t⟩
  let divisors :=ceilDiv (P4.t*iH p big cut h) (32*mV) +
    ceilDiv (iH p big cut p) 32+20*p.b*h.b^2+5*gZ*p.b*h.b+1
  let singular :=if 1<x.t then ceilDiv (4*x.t*iH p p h h) 32 + x.t*x.b^2+1 else 0
  let length:=(mu - nu+1)*(mu - tau+2 - nu)
  let qv :=ceilDiv (P4.t*iH p q q h+mV*iH p q q p)
    (32*mV*length)
  let isolated:=ceilDiv (3*q.j^2*(2*q.b - q.j)) (4*mu*(mu - tau+1)*nu)
  divisors+singular+qv+isolated
def mW (topSpend:ℕ) :Shape :=
 let j:=m6.j-3*topSpend
 ⟨max (m6.b - topSpend) (j+3),j,j/2⟩
def aIx (topSpend:ℕ) :ℕ :=
  let p:=mW topSpend
  let M:=bf
  let g:Shape :=⟨p.b,p.j+1,min (p.t+1) ((p.j+1)/2)⟩
  let x :=LN (M+1) p
  let y :=LN (M+2) p
  let kK:=oR.Wc p x y+(M - 1)*oR.Wc p g y +
    M*oR.Wc p g x
  let H :=max p.b ((2*p.t - 1)*p.b - p.t^2)
  let J:=max p.j ((2*p.t - 1)*p.j - 2*p.t^2)
  let exponent:=2*M - 5
  let a :=1+exponent*(H - 1)
  let d:=min a (exponent*(J - 1)+M - 1)
  let r :=H*d+J*(a - d)
  let initial :=1+exponent*(p.b - 1)
  let extra :=(P4.t+2*mV)*p.b*initial+P4.t*(gZ*p.b+r)
  kK+ceilDiv extra mV+p.b+H^2
abbrev ack :ℕ:=1+Ao/sC
def H6 (b:Bank) (x :Shape) (a r :ℕ) :Shape :=
 let B:=b.box.b-((a - r)*x.b+r)
 let J:=min (b.box.j-((a - r)*x.j+3*r)) (3*B)
 let T:=min (b.box.t - ((a - r)*x.t+r)) (J/3)
 ⟨max B J,J,T⟩
def Xd (a r :ℕ) :asQ:=if r=a then .iy else .product
def YK (a r t l:ℕ) :ℕ :=
  if r=a then a+l else
    max 1 ((Finset.Icc 1 t).sup fun s =>
      let gG:=ceilDiv l s
      if r*(s - 1)<gG then a*s+gG - r*(s - 1) else 0)
def can (b:Bank) (x :Shape) (v a r :ℕ) :ℕ :=
  let q:=H6 b x a r
  let h:=W5 (Xd a r) x q
  if h<v then
    let l:=max 1 (ceilDiv (Ix x q) (v - h))
    YK a r x.t l - 1
  else ack
def EW (b:Bank) (x :Shape) (v a :ℕ) :ℕ :=
 (Finset.range (a+1)).fold min ack (can b x v a)
end
end bJ
end
section
namespace bJ
noncomputable section
open Polynomial


open scoped BigOperators
theorem Messages.mono {w Γ s Δ} (h:Messages w Γ s) (hΔ:Δ⊆Γ) :Messages w Δ s :=
 ⟨h.distinct.mono hΔ,fun γ hγ=>h.degree γ (hΔ hγ),fun γ hγ=>h.lg γ (hΔ hγ),
   h.word_fixed,fun γ hγ=>h.scalar_fixed γ (hΔ hγ)⟩
end
end bJ
end
end
section
set_option autoImplicit true
namespace P6_6_3
open aiI (Symbol)
def SymbolInProfile (P:Symbol) :Prop :=
  ∀ m∈P.support,m 1+m 2+m 3≤P6_6.Dj (m.sum (fun _ a=>a))
end P6_6_3
end
section
set_option autoImplicit true
namespace P6_6_8
open aR (Shape ceilDiv)
open P6_6
def edge (j:ℕ) :ℕ :=
  if j=3 then 24 else if j=4 then 22 else if j=5 then 19 else
  if j=6 then 16 else if j=7 then 10 else 0
def W0 (v :Shape) :Prop :=v=oL∨Valid v∧v.b≤edge v.j
private def orderWord:ℕ→ℕ
  | 0=>0x2b37
  | 3=>0x5874506a4c64485f455c425840563f543d523c503a4e394d384b374a3649344734463345324432443143304230412f400000
  | 4=>0x63815874526c4d664a62475e445b435940563f543d523c513b4f3a4e384c384b374a364935483447344600000000
  | 5=>0x68875d7a5772526c4f684c644860465d445b4359415740553e533c513c503a4e394d384c00000000
  | 6=>0x84ab6d8e63815c785772536d4f684c654a62485f455c445a42584056405500000000
  | 7=>0x7a9e6b8b62805c785873546e506a4d66000000000000
  | _=>0
private def orders (v :Shape) :ℕ:=orderWord v.j >>> (16*v.b)
abbrev Cj (v :Shape) :ℕ:=orders v % 256
abbrev sharedOrder (v :Shape) :ℕ:=orders v/256 % 256
def liftChoice (v :Shape) :Bool :=
  let p:=remainingChart v
  let r :=physicalBody v (Cj v)
  let q:=physicalBody v (sharedOrder v)
  decide (pair32 true p r q≤pair32 false p r q)
abbrev quoteDen (ell:ℕ) :ℕ:=32*mV*ell*max 1 (ell - 2)
def quoteNum (v r :Shape) :ℤ :=
  let ell:=sharedOrder v
  let l:=Cj v
  let q:=physicalBody v ell
  pairNumerator (liftChoice v) (remainingChart v) r q (joinBody (physicalBody v l) q)
    ell (firstCaps v l).t
def Lw (v :Shape) :Shape :=
  let den:=quoteDen (sharedOrder v)
  ⟨ceilDiv (quoteNum v ⟨1,0,0⟩).toNat den,
   ceilDiv (quoteNum v ⟨0,1,0⟩).toNat den,
   ceilDiv (quoteNum v ⟨0,0,1⟩).toNat den⟩
def earlyCap:ℕ→ℕ
  | 1=>0x13408728ede0c7f | 2=>0x234c69a6f148c96 | _=>0
def laterCap:ℕ→ℕ
  | 0=>0x372398c17cef648 | 1=>0x2233d88160f5dcb | _=>0xce0be2b1aae8a2
end P6_6_8
end
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open K1 (I K)
open aR (ao Shape jF)
open jA (kH mA jK ko iP Lower vC lP gY aox translate ED YB qN)
open scoped Polynomial BigOperators
abbrev ahD:=ak1.ahD
abbrev Ga :=ak1.Ga
abbrev Cj:ℕ:=5080194
abbrev Fw:ℕ:=2340282
abbrev ajA:ℕ:=5000*179827 - Cj
abbrev E3:ℕ:=5000*179827-Fw
abbrev RF:ℕ:=0x2c77ff4cc20b4ad69d
def Source {Γ s} (w:I→K) (P:jF Γ s) (L:kH P)
    (box :Shape) (t:ℕ) (F:jK) :Prop :=
  jA.Source w P L box t F∧gY F≤40000
def ap2 {Γ s} (w:I→K) (P:jF Γ s) (L:kH P)
    (box :Shape) (t n:ℕ) :Prop :=
  ∃ e :Fin n→jK,LinearIndependent ao e ∧
    ∀ i,Source w P L box t (e i)
def YI (F G:ko) :Lower :=
  Polynomial.resultant (qN F) (qN G) 40000 40000
def Dl (a :mA →₀ ℕ) :ℕ :=
  7062*a none+48758*a.some.degree
theorem aOR (a b:mA →₀ ℕ) :
    Dl (a+b)=Dl a+Dl b:= by
  simp only [Dl,Finsupp.add_apply,Finsupp.some_add,map_add,Nat.mul_add]
  ac_rfl
def akX {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) :
    Submodule ao jK :=
  Submodule.span ao {Q | ∃ t F a,Source w P L Ga t F ∧
    t+Dl a≤E3∧Q=aox a F}
def NT (F:ko) (z :iP) (y :Fin 3→iP) (d:ℕ) :Prop :=
  ∀ a∈(translate (ED z y) F).support,d≤Dl a
def aqw (F G:ko) (z :iP) (y :Fin 3→iP) :Prop :=
  NT F z y Cj∧NT G z y Fw
structure awY (F G:ko) where
  fixed:Finset ko
  moving:Finset ko
  pure :iP[X]
  exponent:ko→ℕ
  left:ko
  right:ko
  pure_ne :pure≠0
  pure_degree :pure.natDegree≤80000
  fixed_kind : ∀ f∈fixed,Irreducible f∧0<vC f∧gY f=0
  moving_kind : ∀ f∈moving,Irreducible f∧0<vC f ∧
    0<gY f∧f.degreeOf (some 2)=0
  fixed_total:vC (∏ f∈fixed,f)≤121
  fixed_index :lP (∏ f∈fixed,f)≤41
  moving_total:vC (∏ f∈moving,f)≤17
  moving_index :lP (∏ f∈moving,f)≤5
  moving_seed :gY (∏ f∈moving,f)≤103
  azo:F=(YB pure*(∏ f∈fixed,f^exponent f) *
    (∏ f∈moving,f^exponent f))*left
  az7:G=(YB pure*(∏ f∈fixed,f^exponent f) *
    (∏ f∈moving,f^exponent f))*right
  left_ne :left≠0
  right_ne :right≠0
  proper :IsRelPrime left right
  left_caps :vC left≤6789∧lP left≤2300∧gY left≤40000
  right_caps :vC right≤6820∧lP right≤2300∧gY right≤40000
end
end P6_6_4
end
section
set_option autoImplicit true
namespace qqJLTVc
noncomputable section
open aR (Shape)
open agM (a1Z)
open NU (aD ic azm)
open P6_6 (wP)
abbrev slots :Finset (Fin 5) := {1, 2,3,4}
def subtractHorizontal (a :Shape×ℕ) (d:Shape) :Shape×ℕ :=
  (⟨a.1.b - d.b,a.1.j - d.j,a.1.t - d.t⟩,a.2)
def horizontalDerivative (d x :ℚ×ℚ×ℚ) :ℚ :=
  let b:=x.1
  let j:=x.2.1
  let f :=x.2.2
  d.1*(8*j^2*f - 24*j*f^2+24*f^3) +
    d.2.1*(16*b*j*f - 24*b*f^2 - 12*j^2*f+28*j*f^2 - 20*f^3) +
    d.2.2*(8*b*j^2 - 48*b*j*f+72*b*f^2 - 4*j^3+28*j^2*f-60*j*f^2 + 36*f^3)
def volumeDerivative (d:Shape) (a :Shape×ℕ) :ℚ :=
  let F (s :ℚ) :=horizontalDerivative (aD d) (ic s a)
  ((7/90)*F 0+(32/90)*F (1/4)+(12/90)*F (1/2) +
    (32/90)*F (3/4)+(7/90)*F 1)*(a.2 :ℚ)
def volumeDifference (d:Shape) (a :Shape×ℕ) :ℚ :=
  azm (a1Z a (d,0))-azm a
def signedVolume (d q g a b:Shape) (u v :ℕ) :ℚ :=
  let V (x y :Shape) :ℚ:=(wP d q x y :ℚ)
  let s :Shape :=⟨1,4, 2⟩
  V a b+(u:ℚ)*V g b+(v :ℚ)*V g a -
    ((u:ℚ)*V s b+(v :ℚ)*V s a+(u:ℚ)*(v :ℚ)*(V s g-V s s))
end
end qqJLTVc
end
section
set_option autoImplicit true
namespace P6_6_1
noncomputable section
open aR (ao)
open fP (lP)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P6_6 (gZ m6 M8)
abbrev Exponent:=JetVariable 3 →₀ ℕ
def asu (q:ℕ) :ℕ :=
  if q≤111 then 56 else
  if q≤129 then 54 - 2*((q - 112)/2) else 35 - 2*((q - 130)/2)
theorem gAu:Antitone asu:= by
  intro q r h
  unfold asu
  split <;> split <;> (try split) <;> (try split) <;> omega
def FF (u:Exponent) :Prop :=
  u.some.degree≤ m6.b∧u.some.weight lP≤ m6.j∧u (some 3)≤ m6.t ∧
    u (some 1)+u (some 2)+u (some 3)≤asu u.some.degree ∧
    u.weight (differentialWeight gZ)≤M8
def space :Submodule ao (DifferentialPolynomial ao 3) :=
  restrictSupport ao {u | FF u}
def DV (center received :ao) :space →ₗ[ao] LocalPolynomial ao 3 :=
  (localConstraintAt 99 center received).domRestrict space
instance :Module.Finite ao space := by
  have hpositive (j:JetVariable 3) :differentialWeight gZ j≠0:= by
    cases j with
    | none=>decide
    | some j =>
      have hj:=j.isLt
      change 133425 - j.val≠0
      omega
  exact restrictSupport_finite <|
    (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu=>hu.2.2.2.2
end
end P6_6_1
end
section
set_option autoImplicit true
namespace P6_6_2
noncomputable section
open aR (ao embed)
open xE (M7 UT Local topWeight Flag
  oldCount m5 BH U1 denominator)
open P6 (I K node)
open P6_6 (gZ aWx primaryM Wk Dj)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def FF (e :UT) :Prop :=
  e.weight jetDegreeWeight≤Wk.b ∧
  e.weight jetDerivativeWeight≤Wk.j ∧
  e.weight topWeight≤Wk.t ∧
  e.weight (differentialWeight gZ)≤aWx ∧
  e (some 1)+e (some 2)+e (some 3)≤Dj e.some.degree
def rU:Set UT := {e | FF e}
theorem bFE :rU.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d:=3) gZ)
    ?_ aWx).subset (fun _ he=>he.2.2.2.1)
  intro v
  cases v with
  | none=>decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide :3<gZ) j).ne'
def columns :Finset UT:=bFE.toFinset
def W2 :Submodule ao M7 :=
  MvPolynomial.restrictSupport ao rU
instance :Module.Finite ao W2 :=
  MvPolynomial.restrictSupport_finite bFE
theorem ebi:Module.finrank ao W2=columns.card:= by
  have h: (↑columns :Set UT)=rU :=
    Set.Finite.coe_toFinset bFE
  rw [W2,← h]
  exact MvPolynomial.finrank_restrictSupport_finset (K:=ao) columns
def nodeMap (x y :ao) :W2 →ₗ[ao] Local :=
  (localConstraintAt primaryM x y).domRestrict W2
def asI (w:I→K) :W2 →ₗ[ao] (I→Local) :=
  LinearMap.pi fun i=>nodeMap (embed (node i)) (embed (w i))
abbrev rankCap:ℕ:=0x155faabc89085
abbrev Offset :=Fin (primaryM+Wk.j)
def aQj (r :Offset) :ℤ:=(r.val :ℤ)-Wk.j
def iO (q:ℕ) :ℕ:=min q (Dj q)
def pT (q:ℕ) (r :Offset) :Flag :=
  ⟨iO q,-aQj r,Wk.j,Wk.t,
    (primaryM:ℤ) - q-aQj r⟩
def alp (q:ℕ) (r :Offset) :Flag :=
  { pT q r with upper :=min Wk.j ((primaryM:ℤ) - 1-aQj r) }
def latticeAllowance (F:Flag) :ℤ :=
  let x :=max 0 (min F.degree F.upper-(F.order+2)/3+1)
  let y :=2*max 0 (min F.degree (F.upper/2) - max 0 ((F.order-F.degree+1)/2)+1)
  let z :=3*max 0 (min (min F.cap F.degree) (F.upper-F.order)+1)
  let u:=F.lower - 1
  denominator u - denominator (u - x) - denominator (u - y) - denominator (u - z) +
    denominator (u - x - y)+denominator (u - x - z)+denominator (u - y - z) -
    denominator (u - x - y - z)
def oppositeBound (F:Flag) :ℕ :=
  if F.order≤0 then 0 else
  let below:=U1 F.degree (min F.upper (F.order - 1)) F.cap
  if F.lower≤0 then below.toNat else
  let tail:=U1 F.degree F.upper F.cap - below
  (oldCount F - tail+min (latticeAllowance F) tail).toNat
def prescribedBound (q:ℕ) (r :Offset) (power :Fin 11→ℕ) :ℕ :=
  let F:=pT q r
  if F.order≤0 then 0 else
    let lower :=max 0 (max (m5 F) (m5 (BH F power)))
    (min (oldCount (alp q r)) (oldCount F-lower)).toNat
def xR (q:ℕ) (r :Offset) (power :Fin 11→ℕ) :ℕ :=
  min (prescribedBound q r power) (oppositeBound (pT q r))
abbrev kJ:=ℕ→Offset→Fin 11→ℕ
def al2 (q:ℕ) (power :Offset→Fin 11→ℕ) :ℕ :=
  ∑ r,xR q r (power r)
def rankBand (p:kJ) (lo hi:ℕ) :ℕ :=
  ∑ q∈Finset.Ico lo hi,al2 q (p q)
end
end P6_6_2
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
namespace P6_6_3
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open P6 (I K node dw)
open P6_6 (tB gZ primaryM aWx sC depth Pq Messages)
open aR (ao embed af jet wU extend)
open bzr (line)
open scoped BigOperators
open private bdm cX8 from ProximityPrize.SubmissionLower.A2
open private bfX from ProximityPrize.SubmissionLower.A2
private def Bounded (Q:Polynomial ao[X]) (b:ℕ) :Prop :=
  ∀ j,(Q.coeff j).natDegree≤b+sC*j
private theorem afg {F G:Polynomial ao[X]} {a b:ℕ}
    (hF:Bounded F a) (hG:Bounded G b) :Bounded (F*G) (a+b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum,Nat.mul_add]
  omega
private theorem aCs (f :ao[X]) {a :ℕ} (hf :f.natDegree≤a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h:j=0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C,h]
private theorem bmr {ι:Type*} (A:Finset ι)
    (f :ι→Polynomial ao[X]) (b:ι→ℕ) (hf : ∀ i∈A,Bounded (f i) (b i)) :
    Bounded (∏ i∈A,f i) (∑ i∈A,b i) := by
  classical
  induction A using Finset.induction_on with
  | empty=>simpa using aCs (1 :ao[X]) (a :=0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact afg (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk=>hf k (Finset.mem_insert_of_mem hk))
private theorem aMs {f :Polynomial ao[X]} {b:ℕ} (hf :Bounded f b) (n:ℕ) :
    Bounded (f^n) (b*n) := by
  induction n with
  | zero=>simpa using aCs (1 :ao[X]) (a :=0) (by simp)
  | succ n ih =>
    rw [pow_succ,Nat.mul_succ]
    exact afg ih hf
private theorem avr (P:af 4) (S U:ao[X]) (T:ℕ)
    (hP:tB P T) (hS:S.natDegree≤gZ)
    (hU:U.natDegree≤dw+3) (j:ℕ) :
    ((line P S U).coeff j).natDegree≤T+sC*j:= by
  let b (i:Fin 4) :ℕ:=gZ - i.val
  let F (i:Fin 4) :Polynomial ao[X] :=
    Polynomial.C (jet S i)+Polynomial.C (jet U i)*Polynomial.X
  have hF (i:Fin 4) :Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree≤b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu: (jet U i).natDegree≤b i+sC:= by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi:i.val≤gZ:=(Nat.le_of_lt_succ i.isLt).trans (by decide)
      have hwidth :dw+3=sC+gZ:=rfl
      change dw+3 - i.val≤(gZ - i.val)+sC
      rw [hwidth,Nat.add_sub_assoc hi,Nat.add_comm sC]
    change ((Polynomial.C (jet S i)+Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree≤b i+sC*k
    rw [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul_X]
    by_cases h0:k=0
    · simpa [h0] using hs
    · by_cases h1 :k=1
      · simpa [h1] using hu
      · simp [h0,h1]
  unfold line
  rw [MvPolynomial.eval₂_eq,Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm :=afg (aCs (P.coeff m) le_rfl)
    (bmr m.support (fun i=>F i^m i) (fun i=>b i*m i)
      (fun i _=>aMs (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
private theorem brV (w:I→K) (T:ℕ) (P:af 4) (S:ao[X])
    (hP:Pq w T P) (hS:S.natDegree≤gZ)
    (A:Finset I) (hA:A.card=dw)
    (hhit : ∀ i∈A,S.eval (embed (node i))=embed (w i))
    (V:ao[X]) (hV:V.natDegree≤3) (j:ℕ)
    (hj:T+sC*j≤aWx) :
    (line P S (mL (fun i=>embed (node i)) A*V)).coeff j=0:= by
  classical
  let x (i:I) :ao:=embed (node i)
  let L:=mL x A
  let U:=L*V
  have hU:U.natDegree≤dw+3:= by
    exact natDegree_mul_le.trans (by rw [ZQ,hA]; exact Nat.add_le_add_left hV _)
  let Q:=line P S U
  have hcontact (i:I) (hi:i∈A) (c:ao) :
      (Polynomial.X - C (x i))^primaryM∣Q.eval (C c) := by
    rw [show Q=line P S U from rfl,bdm]
    apply hP.2.2.2
    have hL:L.eval (x i)=0:=arK x A i hi
    have hU0:U.eval (x i)=0:= by simp [U,hL]
    simpa [x,eval_smul,hU0] using hhit i hi
  have hx :Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb:=(avr P S U T hP.2.2.1 hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree<primaryM*A.card:= by
    rw [hA]
    exact hb.trans_lt (by change 0x2027d3a7<0x2027d3a8; decide)
  exact cX8 Q A x hx primaryM hcontact j hdegree
theorem dPp (w:I→K) (T:ℕ) (P:af 4)
    (hT:T≤aWx) (hP:Pq w T P)
    (S:ao[X]) (hS:S.natDegree≤gZ)
    (lg : ∃ H :Finset I,dw≤H.card ∧
      ∀ i∈H,S.eval (embed (node i))=embed (w i)) :
    wU P S (depth T) := by
  obtain ⟨H,hH,hhits⟩:=lg
  obtain ⟨A,hAH,hA⟩:=Finset.exists_subset_card_eq hH
  let x (i:I) :=embed (node i)
  apply bfX P S (mL x A) (S8 x A).ne_zero
  intro V hV j hj
  apply brV w T P S hP hS A hA (fun i hi=>hhits i (hAH hi)) V hV j
  have hdepth:depth T=(aWx - T)/sC+1 :=Nat.add_comm 1 _
  rw [hdepth] at hj
  have hj' : j≤(aWx - T)/sC:=Nat.lt_succ_iff.mp hj
  have hq:=Nat.div_mul_le_self (aWx - T) sC
  rw [Nat.mul_comm _ sC] at hq
  calc
    T+sC*j≤T+sC*((aWx - T)/sC) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left sC hj') T
    _≤T+(aWx - T) :=Nat.add_le_add_left hq T
    _=aWx :=Nat.add_sub_of_le hT
theorem cax {w Δ s} (hm:Messages w Δ s) {T Q}
    (hT:T≤aWx) (hQ:Pq w T Q) :
    ∀ γ∈Δ,wU Q (extend (s γ)) (depth T) := by
  intro γ hγ
  apply dPp w T Q hT hQ
  · simpa only [extend,natDegree_map_eq_of_injective (RingHom.injective embed)] using hm.degree γ hγ
  · obtain ⟨H,hcard,hH⟩:=hm.lg γ hγ
    refine ⟨H,hcard,fun i hi => ?_⟩
    rw [extend,eval_map,eval₂_at_apply,hH i hi]
end
end P6_6_3
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P6_6_6
noncomputable section
open aR (Shape bY ceilDiv iH af)
open wH (Lower Sz Ib asD oF localColength)
open P6_6 (ajN bf gZ mV aHc aM1 aPr aWz mu tau nu)
def IG:Shape :=⟨aPr,aWz,0⟩
def Kq:Shape :=
  ⟨aHc+IG.b/tau,aM1+IG.j/tau,0⟩
theorem aNk :Kq=⟨23329,7835,0⟩:= by
  have hb:aHc+aPr/tau=23329:= by decide
  have hj:aM1+aWz/tau=7835:= by decide
  unfold Kq IG
  rw [hb,hj]
def rH (x :Shape) :Shape :=
  if x.t=1 then ajN x.iU else bY (bf+4) x.iU
def anZ (x :Shape) :Shape :=
  let h:=rH x
  let big:=Kq
  ⟨max (max h.b big.b) (max h.j (big.j+1)),max h.j (big.j+1),max 1 h.t⟩
def bHL (x :Shape) :ℕ :=
  let p:=x.iU
  let h:=rH x
  let big:=Kq
  let cut:=anZ x
  ceilDiv (P6.t*iH p big cut h) (32*mV) +
    ceilDiv (iH p big cut p) 32+20*p.b*h.b^2+5*gZ*p.b*h.b+1
def bwr (x :Shape) :ℕ :=
  let p:=x.iU
  let h:=rH x
  if 1<x.t then ceilDiv (4*x.t*iH p p h h) 32 + x.t*x.b^2+1 else 0
abbrev Fw:ℕ:=mu - tau+1
abbrev ahv :ℕ:=0xc216c57
abbrev Ny :ℕ:=0x2febbbf285
theorem dRW: (mu - nu+1)*(mu - tau+2 - nu)=ahv := by
  decide
theorem a6E :mu*(mu - tau+1)*nu=Ny := by
  decide
def bHH (x :Shape) :ℕ :=
  let p:=x.iU
  let h:=rH x
  let q:=IG
  let length:=(mu - nu+1)*(mu - tau+2 - nu)
  ceilDiv (P6.t*iH p q q h+mV*iH p q q p)
    (32*mV*length)
def brg:ℕ :=
  let q:=IG
  ceilDiv (3*q.j^2*(2*q.b - q.j)) (4*mu*(mu - tau+1)*nu)
theorem d9C (x :Shape) :P6_6.lY x =
    bHL x+bwr x+bHH x+brg:=rfl
def bac (P Q:af 3) (y :Sz) :Prop :=
  ∃ q:PrimeSpectrum Lower,
    q.asIdeal∈(Ib P Q).minimalPrimes∧q.asIdeal.height=2 ∧
      q.asIdeal≤oF y ∧
      (↑ahv :ℕ∞)≤localColength q (Ib P Q) ∧
      localColength q (Ib P Q) < ⊤
def bzn (P Q R:af 3) (y :Sz) :Prop :=
  ∃ q:PrimeSpectrum Lower,
    q.asIdeal=oF y∧q.asIdeal∈(asD P Q R).minimalPrimes ∧
      (↑Ny :ℕ∞)≤localColength q (asD P Q R) ∧
      localColength q (asD P Q R) < ⊤
end
end P6_6_6
end
