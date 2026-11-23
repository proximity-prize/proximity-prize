import ProximityPrize.SubmissionLower.B7
import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.range → z4x, Finset.univ → zdB, MvPolynomial → z3y, MvPolynomial.eval → zY9, Polynomial.C → z1z
section
set_option autoImplicit true
namespace P6_4
noncomputable section
open P6 MvPolynomial
def bTM (h:ℕ) (U V:z3y (Fin 5) K) :Prop :=
  (L - h)*U.degreeOf 3≤h∧(L - h)*U.degreeOf 4≤L ∧
    (L - h)*V.degreeOf 3≤L∧(L - h)*V.degreeOf 4≤h
structure ap3 {u:e9} {T:qo u} (R:Relation T) where
  U:z3y (Fin 5) K
  V:z3y (Fin 5) K
  U_omits :Qo.yV U
  V_omits :Qo.yV V
  heights :U.degreeOf 0≤T.height∧V.degreeOf 0≤T.height
  Ca :bTM T.height U V
  primitive : ∀ q:z3y (Fin 2) K,
    rename (![3,4] :Fin 2→Fin 5) q∣U →
    rename (![3,4] :Fin 2→Fin 5) q∣V→ IsUnit q
  content:Polynomial K
  content_ne :content≠0
  graphU:Qo.graph p U=z1z content*y1 R
  graphV:Qo.graph p V=z1z content*zv R
structure aLU {u:e9} {T:qo u} {R:Relation T}
    (D:Reduction u T R) (A:ap3 R) where
  U:z3y (Fin 5) K
  V:z3y (Fin 5) K
  U_omits :Qo.yV U
  V_omits :Qo.yV V
  U_ne :U≠0
  V_ne :V≠0
  U_dvd:U∣A.U
  V_dvd:V∣A.V
  relPrime :IsRelPrime U V
  height:max (U.degreeOf 0) (V.degreeOf 0)=D.height
  graphU:Qo.graph p U=z1z A.content*D.U
  graphV:Qo.graph p V=z1z A.content*D.V
abbrev N7:=WN.N7
open wT (Qb ME MD D9)
structure UJ (u:e9) (deleted:zJe I) (Γ:zJe K) where
  mark : ∀ γ∈Γ,B5 u γ
  survives : ∀ γ (hγ:γ∈Γ) i,i∈(mark γ hγ).support→i∉deleted
abbrev Bank :=WN.Bank
abbrev asP := @WN.asP
def bes :Bank→ℕ
  | .Mi | .w22Swapped | .NK | .Mh=>24378
  | _=>32504
abbrev normalCap:ℕ:=0x1f0d2ea082df883
def chartRate (b:Bank) :ℚ:=(131073/48756:ℚ)*b.M
def bcp (b:Bank) :ℚ:=b.E*chartRate b^2
abbrev apL:ℕ:=4*dw - 1
abbrev D4 :=WN.D4
abbrev LV:=WN.LV
structure biX {u:e9} {deleted:zJe I} {Γ:zJe K}
    (F:UJ u deleted Γ) (b:Bank) where
  Q:z3y (Fin 4) K
  nonzero :Q≠0
  degreeY:Q.weightedTotalDegree Qb≤5
  degreeS:Q.weightedTotalDegree ME≤b.a
  degreeT:Q.weightedTotalDegree MD ≤b.b
  degreeTotal :Q.weightedTotalDegree LV≤b.E
  aiq : ∀ γ (hγ:γ∈Γ),
    aeval (D9 (F.mark γ hγ).decoder γ (γ^p)) Q=0
structure TaylorChart (u:e9) {deleted:zJe I} (P:N7 deleted)
    {Γ:zJe K} (F:UJ u deleted Γ) (b:Bank) (Λ:zJe K) where
  subset :Λ⊆Γ
  equation :z3y (Fin 3) kB
  equation_ne :equation≠0
  equation_degree :equation.totalDegree≤b.E
  numerator :Polynomial (z3y (Fin 3) kB)
  af0:numerator.natDegree≤131071
  denominator :z3y (Fin 3) kB
  cut_degree : ∀ i,(D4 u P numerator denominator i).totalDegree≤b.M
  point :K→Fin 3→kB
  slope : ∀ γ∈Λ,point γ 1=algebraMap K kB γ
  on_equation : ∀ γ∈Λ,zY9 (point γ) equation=0
  regular : ∀ γ∈Λ,zY9 (point γ) denominator≠0
  reconstruction : ∀ γ (hγ:γ∈Λ),
    numerator.map (zY9 (point γ)) =
      z1z (zY9 (point γ) denominator) *
        (F.mark γ (subset hγ)).decoder.map (algebraMap K kB)
end
end P6_4
end
section
set_option autoImplicit true
namespace P6_6
noncomputable section
open Polynomial
open P6 (I K k node dw)
open aR (ao embed extend af Shape shape aO cK Dd wU qE
  bY qP iH ceilDiv)
open scoped BigOperators
abbrev gZ:ℕ:=k - 1+P6.ajO.toNat
abbrev bf :ℕ:=gZ+1
abbrev mV:ℕ:=dw - gZ
abbrev sC:ℕ:=mV+3
abbrev m6:Shape :=⟨133,56,16⟩
abbrev M8:ℕ:=99*dw - 1
abbrev aPd:ℕ:=183500
abbrev gV:=P6.lowRegular
structure Messages (w:I→K) (Γ:zJe K) (s :K→K[X]) :Prop where
  distinct :Set.InjOn s (Γ:Set K)
  degree : ∀ γ∈Γ,(s γ).natDegree≤gZ
  lg : ∀ γ∈Γ,∃ T:zJe I,dw≤T.card ∧ ∀ i∈T,(s γ).eval (node i)=w i
  word_fixed : ∀ i,P6.twist (w i)=w i
  scalar_fixed : ∀ γ∈Γ,(s γ).map P6.twist=s γ
def tB {n:ℕ} (P:af n) (D:ℕ) :Prop :=
  ∀ m∈P.support,(P.coeff m).natDegree +
    m.sum (fun i a=>(gZ - i.val)*a)≤D
def wm (f :af 4) :Prop :=
  Irreducible f∧0<(shape f).t∧aO (shape f) m6∧tB f M8
def axx (topSpend:ℕ) (g:af 3) :Prop :=
  g≠0∧g.totalDegree+topSpend≤ m6.b ∧
    qE g+3*topSpend≤ m6.j∧tB g M8
export gW (wD Valid oL wP LN V7)
structure Cover {n:ℕ} (Γ:zJe K) (s :K→K[X])
    (g:af 3) (f :Fin n→af 4) :Prop where
  lower :axx (wD (fun i=>shape (f i)) zdB).t g
  factors : ∀ i,wm (f i)
  different : ∀ i j,i≠j → ¬ Associated (f i) (f j)
  valid : ∀ i,Valid (shape (f i))
  fits :aO (wD (fun i=>shape (f i)) zdB) m6
  Eh : ∀ γ∈Γ,cK g (extend (s γ))=0 ∨ ∃ i,Dd (f i) (extend (s γ))
  regular : ∀ γ∈Γ,cK g (extend (s γ))≠0 →
    ∀ i,aR.bhZ (f i) (extend (s γ))≠0
abbrev aHc:ℕ:=3623
abbrev aM1 :ℕ:=1174
abbrev aPr :ℕ:=0x20724640
abbrev aWz :ℕ:=0xaf79e00
abbrev mu:ℕ:=34529
abbrev tau:ℕ:=27623
abbrev nu:ℕ:=863
structure aw1 where
  common :af 3
  residual:af 3
  common_ne :common≠0
  residual_ne :residual≠0
  common_total:common.totalDegree≤aHc
  common_index :qE common≤aM1
  residual_total:residual.totalDegree≤aPr
  residual_index :qE residual≤aWz
def aw1.bqU (E :aw1) (S:ao[X]) :Prop :=
  cK E.common S=0∨wU E.residual S mu
def ajN (p:Shape) :Shape :=
  let i:=3+bf*(p.j - 2)
  ⟨max (1+bf*(p.b - 1)) i,i,min (bf+1) (i/3)⟩
def acX (x :Shape) :Prop :=
  (max x.b x.j)*(aHc+aPr/tau)<P6.p
def lY (x :Shape) :ℕ :=
  let p:=x.iU
  let h:=if x.t=1 then ajN p else bY (bf+4) p
  let q:Shape :=⟨aPr,aWz,0⟩
  let big:Shape :=⟨aHc+q.b/tau,aM1+q.j/tau,0⟩
  let cut:Shape :=⟨max (max h.b big.b) (max h.j (big.j+1)),
    max h.j (big.j+1),max 1 h.t⟩
  let divisors :=ceilDiv (P6.t*iH p big cut h) (32*mV) +
    ceilDiv (iH p big cut p) 32+20*p.b*h.b^2+5*gZ*p.b*h.b+1
  let singular :=if 1<x.t then ceilDiv (4*x.t*iH p p h h) 32 + x.t*x.b^2+1 else 0
  let length:=(mu - nu+1)*(mu - tau+2 - nu)
  let qv :=ceilDiv (P6.t*iH p q q h+mV*iH p q q p)
    (32*mV*length)
  let isolated:=ceilDiv (3*q.j^2*(2*q.b - q.j)) (4*mu*(mu - tau+1)*nu)
  divisors+singular+qv+isolated
def mW (topSpend:ℕ) :Shape :=
  let j:=m6.j-3*topSpend
  ⟨max (m6.b - topSpend) (j+3),j,j/2⟩
def lowerHigh (p:Shape) :ℕ :=
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
  let extra :=(P6.t+2*mV)*p.b*initial+P6.t*(gZ*p.b+r)
  kK+ceilDiv extra mV+p.b+H^2
abbrev aIx (topSpend:ℕ) :=lowerHigh (mW topSpend)
abbrev Wk :Shape :=⟨4025,1710,570⟩
abbrev primaryM:ℕ:=3000
abbrev aWx :ℕ:=primaryM*dw - 1
abbrev x5:ℕ:=0xfa50f30e66eec9d
abbrev gG:ℕ:=0x1618310973d1
abbrev ack :ℕ:=1+aWx/sC
def Dj (q:ℕ) :ℕ :=
  if q<3307 then min q 1710 else
  if q<3335 then 1700 else if q<3407 then 1650 else
  if q<3470 then 1600 else if q<3537 then 1550 else
  if q<3585 then 1500 else if q<3630 then 1450 else
  if q<3678 then 1400 else if q<3733 then 1350 else
  if q<3781 then 1300 else if q<3830 then 1250 else
  if q<3878 then 1200 else if q<3927 then 1150 else
  if q<3975 then 1100 else if q<4020 then 1050 else
  if q<4025 then 1000 else 850
def aRG (P:af 4) :Prop :=
  ∀ m∈P.support,m 1+m 2+m 3≤Dj (m.sum (fun _ a=>a))
def Contact (w:I→K) (P:af 4) :Prop :=
  ∀ i (S:ao[X]),S.eval (embed (node i))=embed (w i) →
    (Polynomial.X - C (embed (node i)))^primaryM∣cK P S
def Pq (w:I→K) (T:ℕ) (P:af 4) :Prop :=
  aO (shape P) Wk∧aRG P∧tB P T∧Contact w P
def aJ5 (w:I→K) :Prop :=
  ∃ e :Fin x5→af 4,LinearIndependent ao e ∧
    ∀ i,Pq w aWx (e i)
def Gq (used :Shape) :ℕ :=
  if used.b≤Wk.b∧used.j≤Wk.j∧used.t≤Wk.t then
    ∑ r∈z4x (Wk.b - used.b+1),
      V7 (min r (Dj (r+used.b))) (Wk.j - used.j) (Wk.t - used.t)
  else 0
def depth (T:ℕ) :ℕ:=1+(aWx - T)/sC
def ForcesZero (w:I→K) (f :af 4) :Prop :=
  ∀ T≤aWx,∀ Q,Pq w T Q→f^depth T∣Q
def EarlyIndices {n:ℕ} (w:I→K) (f :Fin n→af 4) :zJe (Fin n) := by
  classical exact Finset.univ.filter (fun i=>ForcesZero w (f i))
def factorProd {n:ℕ} (f :Fin n→af 4) (S:zJe (Fin n)) :af 4 := ∏ i∈S,f i
def AdmissibleEarly (v :Shape) :Prop :=
  gG ≤ ∑ d∈z4x ack,Gq (v.scale (d+1))
def FirstTest (v :Shape) (l:ℕ) :Prop :=
  0<l∧l≤ack∧aO (v.scale l) Wk ∧
    (∑ d∈z4x (l - 1),Gq (v.scale (d+1)))<gG
def CompanionTest (v r :Shape) (ell:ℕ) :Prop :=
  (∑ d∈z4x ack,
    Gq ((v.scale (d+1)).plus (r.scale (d+2 - ell))))<gG
def rawResidual (box used :Shape) :Shape :=
  ⟨box.b - used.b,box.j - used.j,box.t - used.t⟩
def literalBody (q:Shape) :Shape :=
  let j:=min q.j (3*q.b)
  ⟨q.b,j,min q.t (min q.b (j/3))⟩
def residualBody (box used :Shape) :Shape :=(literalBody (rawResidual box used)).iU
def joinBody (p q:Shape) :Shape :=⟨max p.b q.b,max p.j q.j,max p.t q.t⟩
def JetShape (r :Shape) :Prop :=
  0< r.b∧3*r.t≤ r.j∧r.j≤2*r.b+r.t
def JetFactor (R:af 4) :Prop :=
  Irreducible R∧JetShape (shape R)∧tB R aWx
def ambientOrder (R:af 4) (S:ao[X]) :ℕ:= by
  classical exact Nat.findGreatest (wU R S) (shape R).b
def markedWeight (Δ:zJe K) (s :K→K[X]) (R:af 4) :ℕ :=
  ∑ γ∈Δ,ambientOrder R (extend (s γ))
structure ChartMarks {n:ℕ} (Δ:zJe K) (s :K→K[X])
    (f :Fin n→af 4) (S:zJe (Fin n)) :Prop where
  factors : ∀ i∈S,wm (f i)
  different : ∀ i∈S,∀ j∈S,i≠j → ¬ Associated (f i) (f j)
  Eh : ∀ γ∈Δ,∃ i∈S,cK (f i) (extend (s γ))=0
  leading : ∀ γ∈Δ,∀ i∈S,aR.bhZ (f i) (extend (s γ))≠0
structure bjg (Δ:zJe K) (s :K→K[X]) (P₀:af 4)
    (v :Shape) (l:ℕ) {n:ℕ} (R:Fin n→af 4) (e :Fin n→ℕ) :Prop where
  factors : ∀ i,JetFactor (R i)
  positive : ∀ i,0<e i
  newFactors : ∀ i,¬ R i∣P₀
  each : ∀ i,aO (shape (R i)) (rawResidual Wk (v.scale l))
  total:aO (wD (fun i=>(shape (R i)).scale (e i)) zdB)
    (rawResidual Wk (v.scale l))
  order : ∀ γ∈Δ,l ≤ ∑ i,e i*ambientOrder (R i) (extend (s γ))
def ProperCutter (Δ:zJe K) (s :K→K[X]) (R:af 4)
    (box :Shape) (ell:ℕ) :Prop :=
  ∃ G:af 4,(¬ R∣G)∧aO (shape G) box∧tB G aWx ∧
    ∀ γ∈Δ,wU G (extend (s γ)) ell
structure RetainedSource {n:ℕ} (Δ:zJe K) (s :K→K[X])
    (f :Fin n→af 4) (zo:zJe (Fin n)) :Prop where
  possible :AdmissibleEarly (wD (shape ∘ f) zo)
  first : ∀ l,FirstTest (wD (shape ∘ f) zo) l →
    ∃ (n' : ℕ) (R:Fin n' → af 4) (e :Fin n' → ℕ),
      bjg Δ s (factorProd f zo) (wD (shape ∘ f) zo) l R e
  companion : ∀ R,JetFactor R→(¬ R∣factorProd f zo) →
    ∀ ell,0<ell→aO ((wD (shape ∘ f) zo).scale ell) Wk →
    (CompanionTest (wD (shape ∘ f) zo) (shape R) ell ∨
      ell=1 ∧ ∃ i∉zo,Associated R (f i)) →
    ProperCutter Δ s R (residualBody Wk ((wD (shape ∘ f) zo).scale ell)) ell
abbrev firstCaps (v :Shape) (l:ℕ) :=rawResidual Wk (v.scale l)
abbrev physicalBody (v :Shape) (l:ℕ) :=residualBody Wk (v.scale l)
abbrev remainingLiteral (v :Shape) :=literalBody (rawResidual m6 v)
abbrev remainingChart (v :Shape) :=(remainingLiteral v).iU
def weightedChart (L:ℕ) (p:Shape) :Shape :=
  if p.t=1 then
    let j:=3+(L-4)*(p.j - 2)
    ⟨max (1+(L-4)*(p.b - 1)) j,j,min (L-3) (j/3)⟩
  else bY L p
def pair32 (dR:Bool) (p r q:Shape) :ℤ :=
  let u:=bf+1
  let v :=bf+2
  if dR && p.t != 1 then
    let a :=qP u p
    let b:=qP v p
    let g:Shape :=⟨max p.b (p.j+1),p.j+1,min (p.t+1) ((p.j+1)/3)⟩
    let base :=wP r q a b+u*wP r q g b+v*wP r q g a
    if 3*(p.t+1)≤p.j+1∧2≤p.t+1 ∧
        3*(2+(u - 5)*p.t)≤a.j∧3*(2+(v - 5)*p.t)≤b.j ∧
        2*u≤a.t∧2*v≤b.t then
      let s :Shape :=⟨1,4, 2⟩
      base-(u*wP r q s b+v*wP r q s a +
        (u:ℤ)*v*(wP r q s g - wP r q s s))
    else base
  else wP r q (weightedChart u p) (weightedChart v p)
def curve32 (p r q w:Shape) :ℤ :=
  P6.t*wP r q w (weightedChart bf p) +
    2*(mV:ℤ)*wP r q w p
def pairNumerator (dR:Bool) (p r q both:Shape) (ell boundT:ℕ) :ℤ :=
  let den:ℤ:=mV
  let core :ℤ:=den*pair32 dR p r q +
    32*((P6.t:ℤ)+2*den)*r.b*q.b*(weightedChart (bf+1) p).b
  let c:=curve32 p r q both
  let a :=curve32 p r q p
  let pt:=den*wP r q both both
  let aux :=(ell:ℤ)*(c+pt)+a+c+2*(max ell boundT:ℕ)*a +
    64*den*gZ*r.b*q.b
  if 3≤ell then (core+aux)*(ell - 2 :ℤ)+ell*(c+pt)
  else core+aux+ell*c
def pairFee (dR:Bool) (p r q both:Shape) (ell boundT:ℕ) :ℕ :=
  ceilDiv (pairNumerator dR p r q both ell boundT).toNat
    (32*mV*ell*max 1 (ell - 2))
def largeFee (v r :Shape) (l ell:ℕ) (dR:Bool) :ℕ :=
  let q:=physicalBody v ell
  pairFee dR (remainingChart v) r q (joinBody (physicalBody v l) q) ell (firstCaps v l).t
def selfFee (v r :Shape) (ell:ℕ) (dR:Bool) :ℕ :=
  let p:=r.iU
  let q:=physicalBody v ell
  pairFee dR p p q (joinBody p q) ell r.t
def eyA (b j:ℕ) :ℕ :=
  if j=0 then b else
    let l:=2*bf - 5
    let a :=1+l*(b - 1)
    let d:=min a (l*(j - 1)+bf - 1)
    ceilDiv (P6.t*(b*d+j*(a - d))) mV+b^2
def lowerTaylor (p:Shape) :Shape :=
  let l:=2*bf - 7
  let j:=l*(p.j - 2)+bf - 1
  ⟨max (1+l*(p.b - 1)) j,j,min (l*(p.t - 1)+bf - 2) (j/2)⟩
def smallFee (p r :Shape) :ℕ :=
  if r.t=0 then
    if r.j=0 then r.b else
      let a :Shape :=⟨max r.b (r.j+3),r.j,r.j/2⟩
      if a.t=0 then eyA a.b a.j+r.b^2 else
        lowerHigh a+ceilDiv (P6.t*oR.Wc a a (lowerTaylor a)) mV +
          3*oR.Wc a a a+r.b^3
  else
    let a :=r.iU
    let core :=(mV:ℤ)*min (pair32 false a a p) (pair32 true a a p) +
      32*((P6.t:ℤ)+2*mV)*a.b*p.b*(weightedChart (bf+1) a).b
    let E :=curve32 a a p
    let bound:=core+(2+2*(r.t:ℤ))*E a+E (joinBody a p) +
      mV*wP a p a a+64*(mV:ℤ)*gZ*r.b*p.b
    let u:=r.b - r.t
    let c:=(r.j-3*r.t)/2
    let g:=max u ((2*c - 1)*u - c^2)
    let biR:=ceilDiv (4*bf*P6.t*(r.b*u^2+g^2)) mV +
      r.b*u+g^2+u
    ceilDiv bound.toNat (32*mV)+r.b*biR
def dot (c r :Shape) :ℕ:=c.b*r.b+c.j*r.j+c.t*r.t
def LaterQuote (v :Shape) (jX:ℕ) :Prop :=
  ∃ (l ell:ℕ) (dR:Bool) (coeff :Shape),
    FirstTest v l∧0<ell∧ell≤l∧aO (v.scale ell) Wk ∧
    dot coeff (firstCaps v l)≤l*jX ∧
    ∀ r,JetShape r→aO r (firstCaps v l) →
      (CompanionTest v r ell→largeFee v r l ell dR≤dot coeff r) ∧
      (¬ CompanionTest v r ell →
        smallFee (remainingChart v) r≤dot coeff r ∧
        (0< r.t→aO r (remainingLiteral v) →
          ∃ (k :ℕ) (selfLifted:Bool),0<k∧aO (v.scale k) Wk ∧
            (CompanionTest v r k∨k=1) ∧
            selfFee v r k selfLifted≤dot coeff r))
end
end P6_6
end
