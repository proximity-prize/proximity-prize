import ProximityPrize.SubmissionLower.ZNc0LBb
import ProximityPrize.SubmissionLower.D7
import ProximityPrize.SubmissionLower.B5
import ProximityPrize.SubmissionLower.ZG8ydqc
import ProximityPrize.SubmissionLower.ZFZJbJc
set_option Elab.async false
section
open _root_ renaming Algebra.algebraMap→lI,Finset→cy,Finset.range→mD,Irreducible→nq,MvPolynomial→nX,P5_7.FarBand→aU,P5_7.NativeWitness→ oj,P5_7.OneSeedEquation→nI,P5_7.farAgreement→lz,P5_7.terminal→lV,Polynomial.mapRingHom→n5,cu.Shape→c9,frobenius→lJ
section
set_option autoImplicit true
namespace P5_7_1
noncomputable section
open Polynomial
open P5 (e9 I K p jG gJ dw)
open P5_7 (Qn YQ midAgreement)
open cu (FX Shape Jet vP kr j9 jz ku triangle slots)
open DP (jF zG aKF ad0 VY)
open gT (Ambient IZ)
open pI (xN)
open qQ (oU)
open scoped BigOperators Classical
abbrev lo:=gJ.transport.lo
abbrev hi:=gJ.transport.hi
abbrev degree :=131071+hi
abbrev introFee :ℕ:=0x46ed86e016478
abbrev prefixFee :ℕ:=0x3331cc700b3abd8
abbrev retainedFee :ℕ:=0xc820e14310447
structure Input where
 u:e9
 del:cy I
 M:jG u del
 Γ:cy K
 F:P1.bje dw M Γ
 kA:Qn lo hi M.iF
 noShift:M.shift∉Γ
 H :cu.L[X]
 bY:YQ M F H
abbrev Input.h (x :Input) :=x.M.iF.toNat
abbrev Input.word (x :Input) (i:I) :cu.L:=lI K cu.L (x.M.word i)
structure Poles (x :Input) where
 D:jF x.h
 crt:zG D
 first:D.block 0=x.H
 second:D.block 1=x.H.map (lJ cu.L p)
 offset :D.offset = ![j9 x.M.Q,(j9 x.M.Q).map (lJ cu.L p)]
 constant:D.constant = ![j9 (x.M.factor*x.M.A₀),
   (j9 (x.M.factor*x.M.A₀)).map (lJ cu.L p)]
 slope :D.slope = ![j9 (x.M.factor*x.M.A₁),
   (j9 (x.M.factor*x.M.A₁)).map (lJ cu.L p)]
 nodes : ∀ i j,(D.block i).eval (ad0 j)≠0
 marks : ∀ γ∈x.Γ,aKF D (x.M.label γ) (x.F.scalar γ)
abbrev Poles.rows {x :Input} (P:Poles x) :vP:=VY P.crt x.word
structure Ls where
 dI:ℕ
 free :c9
 moving:c9
def stages :List Ls :=
 [⟨0,⟨83,115,25,1052⟩,⟨812,1131,235,33993⟩⟩,
  ⟨1,⟨83,115,25,1474⟩,⟨880,1226,255,37149⟩⟩,
  ⟨2,⟨121,168,38,965⟩,⟨982,1368,284,40598⟩⟩,
  ⟨4,⟨106,147,32,1765⟩,⟨1139,1588,330,46996⟩⟩,
  ⟨6,⟨98,136,30,34417⟩,⟨1303,1816,377,53638⟩⟩,
  ⟨10,⟨123,171,38,18784⟩,⟨1590,2217,461,66360⟩⟩,
  ⟨16,⟨165,229,50,9720⟩,⟨2164,3017,627,86205⟩⟩,
  ⟨24,⟨277,384,86,3171⟩,⟨2287,3189,663,114680⟩⟩]
def introductions :List (ℕ× c9) :=
 [(5,⟨115,159,35,1794⟩),(6,⟨103,143,31,6175⟩),(10,⟨137,190,41,3870⟩),
  (8,⟨151,210,46,1710⟩),(13,⟨200,277,61,2021⟩),(13,⟨158,218,48,4230⟩),
  (16,⟨200,277,61,2852⟩),(20,⟨207,287,63,4913⟩),(20,⟨256,354,81,2635⟩),
  (1,⟨83,115,25,1474⟩),(4,⟨106,147,32,1765⟩),
  (24,⟨235,327,71,5546⟩),(24,⟨233,324,70,5927⟩)]
def movingOrder :List ℕ:=[2,4,5,6]
abbrev anchor :=stages[0]
abbrev IntroIndex :=Fin (introductions.length+1)
abbrev afa :=Fin stages.length
def terminal:Shape :=⟨2100,2927,619,190000⟩
def cutoff (s :c9) :ℕ:=s.m*dw - 1
def buffer (h r :ℕ) (s :c9) :=cutoff s - 2*h*r
def j3 (h:ℕ) (s :c9) :ℕ :=
 triangle s.U*0xf8eab0e80000+2*h*((s.U+1)*0x1cccacb1996 - 0x47c4a7d1ca8f0)
def contactPowerAt (A h:ℕ) (s :c9) (W:ℕ) :=1+(s.m*A-1-W)/(2*h)
def jointGainAt (A h:ℕ) (s :c9) (E v :ℕ) :ℕ :=
  ku s fun q j =>
    let g:=(q-j)/E
    let w:=s.m*A+j-q*(131071-h)
    let c:= fun a=>slots s.U (a*v)
    (∑ a∈mD g,(c a - c (a+1))*(w - 2*h*(j+a))) +
      c g*(w - 2*h*(j+g))
abbrev ZN :=jointGainAt dw
structure akE (h:ℕ) (rows :vP) (s :Ls) where
 free :Jet
 moving:Jet
 free_ne :free≠0
 moving_ne :moving≠0
 free_mem:free∈rows s.free (buffer h s.dI s.free)
 moving_mem:moving∈rows s.moving (buffer h s.dI s.moving)
 no_moving:qQ.aeH free moving
structure Picks (h:ℕ) (rows :vP) where
 main : ∀ i:afa,akE h rows (stages.get i)
 intro:Fin introductions.length→Jet
 intro_ne : ∀ i,intro i≠0
 intro_mem : ∀ i,let (r,s) :=introductions.get i; intro i∈rows s (buffer h r s)
 shared:intro ⟨9,by decide⟩=(main ⟨1,by decide⟩).free ∧
  intro ⟨10,by decide⟩=(main ⟨3,by decide⟩).free
abbrev TopRow :=nX (Fin 4) (cu.L[X])
def topLift:TopRow →+* nX (Fin 4) FX :=
 MvPolynomial.map (lI cu.L[X] FX)
def topConjugate (P:TopRow) :TopRow :=
 MvPolynomial.map (n5 (lJ cu.L p)) P
def atTop (P:TopRow) (z :K) (S:K[X]) :FX :=
  MvPolynomial.eval₂ (lI cu.L[X] FX)
    ![jz z,kr S,kr S.derivative,kr ((Polynomial.hasseDeriv 2) S)] P
def TopCaps (h m B J C U:ℕ) (P:TopRow) :Prop :=
  ∀ a∈P.support,
    a 1+a 2+a 3≤B∧a 2+2*a 3≤J∧a 3≤C∧a 0≤U ∧
    (P.coeff a).natDegree+(131071+h)*(a 1+a 2+a 3) ≤
      m*midAgreement-1+(B+J)*h+a 2+2*a 3
def wD (P:Jet) :Fin 3→ℕ :=
 ![atc.jetDegree P,P.natDegree,atc.gY P]
def bgK (s :c9) :Fin 3→ℕ := ![s.B,s.J,s.U]
def introCap (i:ℕ) :Fin 3→ℕ :=
  ((introductions.take i).foldl (fun v (r,s) j=>min (v j) (bgK s j/(r+1)))
    (bgK anchor.free))
def aOm (P:Jet) :Shape :=
 ⟨0,164+19*(wD P 0-1),50+19*(wD P 1-1),3037+19*wD P 2⟩
def lineFee (b j u:ℕ) :ℕ :=
 let t:=2*degree-3
 let a :=1+t*(b-1)
 let v :=min a (t*(j-1)+degree)
 let U:=t*u
 let kK:=u*(2*a*v-v*v)+2*U*(b*v+j*(a-v))
 let other :=u*(2*a+v)+U*(2*b+j)+b*v+j*a+u+b+j
 let q:=midAgreement-degree
 (2*(P5.blockLength-midAgreement)*(kK+other)+q-1)/q+b+u+1
structure OriginCover (x :Input) (anchorRow :Jet) where
 factors :cy Jet
 origin :Jet→ IntroIndex
 cut:Jet→Jet
 line :Jet→Bool
 lineMarks :Jet→cy K
 parents :Jet→cy (Ideal Ambient)
 gH :cy K
 paid_bound:gH.card≤ introFee
 nested : ∀ i≤ introductions.length,∀ j,
   (∑ f∈factors.filter (fun f=>i≤(origin f).val),wD f j)≤ introCap i j
 proper : ∀ f∈factors,nq f∧f∣anchorRow ∧ ¬ f∣cut f
 cut_caps : ∀ f∈factors,
   if h: (origin f).val< introductions.length then
     line f=false∧oU (cut f) (introductions.get ⟨_,h⟩).2
   else if line f then oU (cut f) ⟨0,wD f 0,wD f 1,wD f 2⟩
   else oU (cut f) (aOm f)
 shared_cut : ∀ f∈factors,∀ g∈factors,
   (origin f).val< introductions.length→ origin f=origin g→cut f=cut g
 line_bound : ∀ f∈factors,(lineMarks f).card ≤
   if line f then lineFee (wD f 0) (wD f 1) (wD f 2) else 0
 line_pos : ∀ f∈factors,line f=true→0<wD f 1∧0<wD f 2
 geometric : ∀ f∈factors,∀ q∈parents f,
   xN q∧q.height=2∧gT.iJ f∈q∧gT.iJ (cut f)∈q
 disjoint : ∀ f∈factors,∀ g∈factors,f≠g→Disjoint (parents f) (parents g)
 Eh : ∀ γ∈x.Γ,γ∈gH ∨ ∃ f∈factors,
   γ∈lineMarks f ∨ ∃ q∈parents f,IZ q (x.M.label γ) (x.F.scalar γ)
end
end P5_7_1
end
section
set_option autoImplicit true
namespace P5_7_7
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (I K node blockLength p)
open P5_7 (OneSeedEquation normalWidth)
open cu (L FX jz j9)
abbrev Dg:=L[X][X][X]
def gY (f :nI) :ℕ:=(Bivariate.swap f).natDegree
def embed:Dg →+* OneSeedEquation :=
 n5 (n5 (lI L[X] FX))
def hit (w:I→K) (S:K→K[X]) (γ:K) (i:I) :Prop :=
 (S γ).eval (node i)=w i
def sites (w:I→K) (S:K→K[X]) (γ:K) :cy I:= by
 classical exact univ.filter (hit w S γ)
structure UJ (D:ℕ) (w:I→K) (T:cy K) (z :K→K) (S:K→K[X]) :Prop where
 Kw:Set.InjOn z (T:Set K)
 sections :Set.InjOn S (T:Set K)
 degree : ∀ γ∈T,(S γ).natDegree≤D
 dw : ∀ γ∈T,lz≤(sites w S γ).card
def base (i:I) :L:=lI K L (node i)
def mL (A:cy I) :L[X] := ∏ i∈A,((Polynomial.X:L[X]) - C (base i))
def ic (D:ℕ) (a b:L[X]) (d:ℕ) :Prop :=
 (a=0∨a.natDegree+D ≤d)∧b.natDegree≤d
def zN60c (w:I→K) (U:cy K) (S:K→K[X]) (P:K→ L[X]) (a b:L[X]) :Prop :=
 ∀ γ∈U,mL (sites w S γ)*P γ=a*j9 (S γ)+b
structure DualWord (D:ℕ) (w:I→K) (U:cy K) (S:K→K[X]) where
 a₀:L[X]
 a₁:L[X]
 b₀:L[X]
 b₁:L[X]
 u₀:ℕ
 u₁:ℕ
 order :u₀≤u₁
 gMz :2*lz+(u₀+u₁)=blockLength+D
 row₀:ic D a₀ b₀ (lz+u₀)
 row₁:ic D a₁ b₁ (lz+u₁)
 determinant : ∃ c:L,c≠0∧a₀*b₁-a₁*b₀=C c*mL univ
 rows_hit : ∀ i,a₀.eval (base i)*lI K L (w i)+b₀.eval (base i)=0 ∧
   a₁.eval (base i)*lI K L (w i)+b₁.eval (base i)=0
 target : ∀ i,a₀.eval (base i)≠0∨a₁.eval (base i)≠0
 P:K→ L[X]
 Q:K→ L[X]
 denominator : ∀ γ∈U,Q γ≠0
 coprime : ∀ γ∈U,IsCoprime (P γ) (Q γ)
 numerator_ix : zN60c w U S P a₁ b₁
 denominator_ix : zN60c w U S Q a₀ b₀
 degree : ∀ γ∈U,
   (sites w S γ).card≤lz+u₀ ∧
   (Q γ).natDegree≤lz+u₀-(sites w S γ).card ∧
   (P γ).natDegree≤lz+u₁-(sites w S γ).card
 dual_hits : ∀ γ∈U,∀ i,
   (P γ).eval (base i)*a₀.eval (base i)=(Q γ).eval (base i)*a₁.eval (base i) ↔
     ¬ hit w S γ i
theorem DualWord.numerator_id {D:ℕ} {w:I→K} {U:cy K} {S:K→K[X]} (self:DualWord D w U S) :
 ∀ γ∈U,mL (sites w S γ)*self.P γ=self.a₁*j9 (S γ)+self.b₁ :=self.numerator_ix
theorem DualWord.denominator_id {D:ℕ} {w:I→K} {U:cy K} {S:K→K[X]} (self:DualWord D w U S) :
 ∀ γ∈U,mL (sites w S γ)*self.Q γ=self.a₀*j9 (S γ)+self.b₀ :=self.denominator_ix
theorem DualWord.width {D w U S} (J:DualWord D w U S) :J.u₀+J.u₁=normalWidth D:= by
 have h:=J.gMz
 unfold normalWidth
 omega
def phys :L[X] →+* FX:=lI _ _
def dualValue {D w U S} (J:DualWord D w U S) (γ:K) :FX :=
 phys (J.P γ)/phys (J.Q γ)
def atDual {D w U S} (J:DualWord D w U S) (F:Dg) (z :K) (γ:K) :FX :=
 (embed F).eval₂ (evalRingHom (jz z)) (dualValue J γ)
def Jm {D w U S} (J:DualWord D w U S) (F:Dg) (W:ℕ) :Prop :=
  ∀ i j,(F.coeff i).coeff j≠0 →
    ((F.coeff i).coeff j).natDegree+F.natDegree*J.u₀+i*(J.u₁-J.u₀)≤W
def relativeDegree {D w U S} (J:DualWord D w U S) (γ:K) :ℕ :=
 let s :=J.u₁-J.u₀
 s+2*max (J.Q γ).natDegree ((J.P γ).natDegree-s)
def highRate (l:ℕ) (x :oj) :ℕ:=l*(x.c+1)+l+x.g
def poleRate (D l:ℕ) (x :oj) :ℕ :=
 (6*l-4)*x.W-(3*l*l-4*l+2)*normalWidth D
def exclusions (l:ℕ) :ℕ:=7+6*l
def nodeRate (l:ℕ) :ℕ:=2*l+1
def ek (f :nI) :Polynomial (FractionRing FX[X]) :=
 f.map (lI FX[X] (FractionRing FX[X]))
def seedDerivative (F:Dg) :Dg:=F.sum fun i b=>monomial i b.derivative
def seedPullback (F:Dg) (r :ℕ) :Dg :=
 F.map (eval₂RingHom C ((Polynomial.X:L[X][X])^(p^r)))
structure Variation {D w U S} (J:DualWord D w U S)
   (T:cy K) (z :K→K) (F:Dg) (l h pole :ℕ) where
 reducedEquation :Dg
 compression :ℕ
 recovered:F=seedPullback reducedEquation compression
 good:cy K
 Bp:good⊆T
 zJ: (T \ good).card≤exclusions l*h
 A:K→ L[X]
 B:K→ L[X]
 nonzero : ∀ γ∈good,A γ≠0
 denominator : ∀ γ∈good,B γ≠0
 reduced : ∀ γ∈good,IsCoprime (A γ) (B γ)
 simple : ∀ γ∈good,atDual J reducedEquation.derivative (z γ^(p^compression)) γ≠0
 formula : ∀ γ∈good,
   phys (A γ)/phys (B γ) =
     -(atDual J (seedDerivative reducedEquation) (z γ^(p^compression)) γ /
       atDual J reducedEquation.derivative (z γ^(p^compression)) γ)*phys (J.Q γ)^2
 node_budget : ∀ i:I,
   (good.filter fun γ => ¬ hit w S γ i∧(A γ).eval (base i)≠0).card≤nodeRate l*h
 pole_budget : ∑ γ∈good,max (B γ).natDegree ((A γ).natDegree-relativeDegree J γ)≤pole*h
end
end P5_7_7
end
section
set_option autoImplicit true
namespace P5_7_5
noncomputable section
open Polynomial
open P5 (p blockLength)
open P5_7 (Ls O2 farAgreement)
open cu (Shape vP)
open gT (Ambient)
open pI (weight)

open scoped BigOperators Classical
export TD (GM J2 FP bCb aa3 alN bf7 aSt
 auN arC aIe running XM aBh)
def wX (hi:ℕ) :ℕ:=131071+hi
def gap (hi:ℕ) :ℕ:=lz - wX hi
def nV (b:aU) (i:ℕ) :Ls :=
 (b.row.stages[i]?).getD ⟨0,lV b,lV b⟩
theorem cqz {b:aU} {i:ℕ} (hi:i<b.row.stages.length) :
  nV b i∈b.row.stages := by
 rw [nV,List.getElem?_eq_getElem hi]
 exact List.getElem_mem hi
def Fo (b:aU) :=b.row.stages.length - 1
def Wx :aU→ℕ
 | .lZ=>2
 | .om=>1
 | _=>0
def azi (b:aU) (k :Fin 4) :
    List ℕ→(Fin 3→ℕ)→(Fin 3→ℕ)→ℕ
  | [],cap,old =>
    aIe cap old (nV b 0).moving.shape k +
      (![cap 0,cap 2,2*cap 0*cap 2,cap 2*cap 2] :Fin 4→ℕ) k
  | i :: is,cap,old =>
    let s :=nV b i
    let c:=s.free.shape
    aIe cap old c k+azi b k is
      (fun j=>min (cap j) (auN c j/(s.dI+1)))
      (fun j=>max (old j) (arC c k j))
def BC (b:aU) (k :Fin 4) :ℕ :=
  let s :=nV b 0
  if b.row.RU.isEmpty then
    (alN s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else azi b k b.row.RU (auN s.free.shape) (fun _=>0)
def al6 (b:aU) :ℕ :=
  if b.row.RU.isEmpty then
    let s :=nV b 0
    s.free.shape.U*s.moving.shape.U + (aa3 s.free.shape s.moving.shape)^2
  else BC b 3
def aE6 (b:aU) (i:ℕ) (square :Bool) :GM :=
 let s :=nV b i
 bf7 s.free.shape s.moving.shape s.dI square
def V8 (b:aU) :ℕ→GM
 | 0=> fun k=>BC b k
 | i+1=>bCb (V8 b i) (aE6 b (i+1) (decide (Wx b≤ i+1)))
def ar3 (b:aU) :GM :=
 if Wx b=0 then V8 b 0
 else bCb (V8 b (Wx b - 1)) (aE6 b (Wx b) false)
def aEt (b:aU) :ℕ:=(ar3 b 2).floor.toNat
def aEv (b:aU) :ℕ:=(ar3 b 1).floor.toNat
def a3D (s :Ls) :Shape :=
 let a :=s.free.shape
 let b:=s.moving.shape
 let j:=max a.J b.J
 ⟨0,max (a.B-a.J) (b.B-b.J)+j,j,max a.U b.U⟩
def aHp (b:aU) (i:ℕ) :Shape :=
 if i<Fo b then a3D (nV b (i+1)) else (lV b).shape
def SS (b:aU) (bw:Fin 3) (i:ℕ) :GM :=
 fun k=>weight (aHp b i) bw k
def ash (b:aU) :ℚ :=
 XM (Fo b+1) (SS b 0) (V8 b)
def cb1 (b:aU) :ℚ :=
  FP (running (SS b 2) (Fo b+1))
    ![(BC b 0:ℚ),(BC b 1 :ℚ),(BC b 2 :ℚ),(al6 b:ℚ)]
def au1 (hi B J:ℕ) :ℕ :=
 let d:=wX hi
 let q:=gap hi
 let a :=1+(2*d-3)*(B-1)
 let v :=min a ((2*d-3)*(J-1)+d)
 ((blockLength-farAgreement)*((B-J)*v+J*a)+(q-1))/q+B^2
def fF (b:aU) :List Shape :=
 (lV b).shape :: b.row.stages.flatMap (fun s=>[s.free.shape,s.moving.shape])
def a4f (b:aU) :ℕ :=
 ((fF b).map (fun s=>au1 b.row.hi s.B s.J)).sum
def contentBudget (b:aU) :ℕ :=
 (p+1)*((fF b).map Shape.U).sum
def lowSeedFee (b:aU) :ℕ:=(p+1)*BC b 2+al6 b
def lowJetFee (b:aU) :ℕ:=BC b 0+au1 b.row.hi (aEt b) (aEv b)
def pointFee (b:aU) :ℕ:=(cb1 b).ceil.toNat
def heightLimit (b:aU) :ℚ :=
 XM (Fo b+1) (SS b 1) (V8 b)
def sheetCut:aU→ℕ
 | .dbl=>14
 | .lZ=>24
 | _=>0
def alO (hi g:ℕ) :ℚ :=
 let d:=wX hi
 let beta :ℚ:=((blockLength-lz :ℕ) :ℚ)/gap hi
 (2*(g:ℚ)-1)+beta*((2*(d:ℚ)-1)*(2*(g:ℚ)-1)+1)
def lossFee (b:aU) :ℕ :=
  let D:=ash b
  let q:=sheetCut b
  let Q:ℚ:=(p+1 :ℕ)
  (if q=0 then Q*D else
    max D (Q/(q+1 :ℕ))*D + alO b.row.hi q*heightLimit b+D).ceil.toNat
def agA (rows :vP) (s :c9) (I:Ideal Ambient) :Prop :=
 ∀ P∈rows s (O2 s),gT.iJ P∈I
def axS {h rows s} (pair :P5_7.akE h rows s) (I:Ideal Ambient) :Prop :=
  agA rows s.free.shape I∧agA rows s.moving.shape I ∧
    aFX.aTw pair.free pair.moving I
structure am1 (hi dI:ℕ) (s :c9) :Prop where
 ode :aBh s.B s.J
 seed_small:s.U<p
 pos :0<s.m*lz
 buffer :2*hi*dI≤O2 s
structure aqE (b:aU) :Prop where
 aXU:0<b.row.stages.length
 zero : (nV b 0).dI=0
 bIj : ∀ i<Fo b,0<(nV b (i+1)).dI
 bN7 : ∀ i<b.row.stages.length,(nV b i).dI<p
 stop_reserve : (nV b (Wx b)).dI=b.row.stopReserve
 aE8:Wx b≤Fo b
 brd : ∀ i∈b.row.RU,0< i∧i<b.row.stages.length
 b6r : (b.row.RU).Pairwise (· < ·)
 aE7 : ∀ i<b.row.stages.length,
   let s :=nV b i
   am1 b.row.hi s.dI s.free.shape∧am1 b.row.hi s.dI s.moving.shape
 bxE :am1 b.row.hi 0 (lV b).shape
 bq6 : ∀ k,BC b k<p
 bq5:BC b 3≤al6 b
 bDl: (nV b 0).free.shape.U + (nV b 0).moving.shape.U<p
 bK5:aBh (aEt b) (aEv b)
 fixed: (∑ i∈mD b.row.stages.length,
   (au1 b.row.hi (nV b i).free.shape.B (nV b i).free.shape.J +
     au1 b.row.hi (nV b i).moving.shape.B (nV b i).moving.shape.J))≤a4f b
 content: (p+1)*((nV b 0).free.shape.U + (nV b 0).moving.shape.U)≤ contentBudget b
 seed_small:ash b<p
 gH :pointFee b+lossFee b+lowSeedFee b+lowJetFee b+a4f b +
   contentBudget b≤b.row.prefixFee
end
end P5_7_5
end
end
section
set_option autoImplicit true
namespace qAIBbfd
noncomputable section
open Polynomial MvPolynomial
open aR (af Shape ao aO extend cK jet shape)
open dN (GeoJets An bC j8 separant pK u6
  aNw)
open wH (qg)
open lB (bF yy abx Po ahA
  afz SZ abr)
open P6_6 (weightedChart)
open private br5 ew1 eGF Ur gpA from ProximityPrize.SubmissionLower.ZG8ydqc
open private aa5 from ProximityPrize.SubmissionLower.ZceTCvc
open private bdn from ProximityPrize.SubmissionLower.BE
open private ajW TaylorChart TaylorChart.mk TaylorChart.dM TaylorChart.aay TaylorChart.pullback TaylorChart.aWC L4 gKY from ProximityPrize.SubmissionLower.B5
local notation "W" => MvPolynomial.weightedTotalDegree
private def tail (g:af 4) :ℕ→af 4
  | 0=>MvPolynomial.C (Polynomial.C (-6:ao))*pK g
  | n+1=>br5 g (n+1) (tail g n)
private theorem eval_tail {g:af 4} (hg: (shape g).t=1) {S:ao[X]}
    (hon :cK g S=0) (n:ℕ) :
    cK (tail g n) S=cK (separant g) S^(n+1)*(derivative^[n+4]) S:= by
  let u:=cK (separant g) S
  have hsep:cK (pK (separant g)) S=derivative u:= by
    have hz :cK (separant (separant g)) S=0:= by
      rw [gpA hg]
      exact map_zero _
    have h:=bdn (separant g) S
    rwa [hz,mul_zero,add_zero,eq_comm] at h
  induction n with
  | zero =>
    have hz :=bdn g S
    rw [hon,derivative_zero] at hz
    have h4 : (derivative^[4]) S=Polynomial.C (6:ao)*derivative (jet S (3:Fin 4)) := by
      change (derivative^[3+1]) S= _
      rw [Function.iterate_succ_apply' (⇑derivative) 3 S,ajW,
        derivative_C_mul]
      rfl
    change (MvPolynomial.eval (jet S:Fin 4→ao[X]))
      (MvPolynomial.C (Polynomial.C (-6:ao))*pK g)=u^1*_
    rw [map_mul,MvPolynomial.eval_C,h4,pow_one,Polynomial.C_neg]
    change -Polynomial.C (6:ao)*cK (pK g) S= _
    linear_combination -Polynomial.C (6:ao)*hz.symm
  | succ n ih =>
    let e :=MvPolynomial.eval (jet S:Fin 4→ao[X])
    change e (br5 g (n+1) (tail g n))= _
    unfold br5
    rw [map_sub,map_mul,map_mul,map_natCast]
    change cK (u6 g (tail g n)) S -
      (↑(n+1) :ao[X])*cK (pK (separant g)) S*cK (tail g n) S= _
    rw [aNw _ _ _ hon,hsep,ih,eGF]
    exact congrArg (fun D:ao[X]=>u^(n+1+1)*D)
      (Function.iterate_succ_apply' (⇑derivative) (n+4) S).symm
private def denom (L:ℕ) (g:af 4) :af 4 :=separant g^(L-4)
private def num (L:ℕ) (g:af 4) (i:Fin L) :af 4 :=
  if hi:i.val<4 then MvPolynomial.X ⟨i.val,hi⟩*denom L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial:ao)⁻¹) *
      (separant g^(L-4-(i.val-4+1))*tail g (i.val-4))
private def recovery (L:ℕ) (g:af 4) :TaylorChart L :=
  TaylorChart.mk (bC (denom L g)) (fun i=>bC (num L g i))
private theorem a9A {L:ℕ} (w:Fin 4→ℕ) (Δ d:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) (hw : ∀ i,w i≤d)
    {g:af 4} {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) :
    W w (denom L g)≤d+(L-4)*(B-w 3+Δ) ∧
      ∀ i,W w (num L g i)≤d+(L-4)*(B-w 3+Δ) := by
  let a :=B - w 3+Δ
  have hpow (n:ℕ) :W w (separant g^n)≤n*a :=
    (weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _
      ((Ur w hg).trans (Nat.le_add_right _ _)))
  have htail (n:ℕ) :W w (tail g n)≤d+(n+1)*a := by
    induction n with
    | zero =>
      apply (Po _ _ _).trans
      have h:=aa5 w Δ hshift g hg
      have he :=Nat.sub_add_cancel hB
      simp only [zero_add,one_mul,a]
      exact h.trans (by have :=hw 3; omega)
    | succ n ih =>
      simpa only [tail,a,Nat.add_mul,one_mul,Nat.add_assoc] using
        ew1 w Δ hshift hB hg ih (n+1)
  refine ⟨(hpow _).trans (Nat.le_add_left ..),fun i => ?_⟩
  unfold num
  split_ifs with hi
  · exact (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add
      ((abx w _).trans (hw _)) (hpow _))
  · have hle :i.val-4+1≤L-4 := by omega
    apply (Po _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _≤(L-4-(i.val-4+1))*a+(d+(i.val-4+1)*a) :=
        Nat.add_le_add (hpow _) (htail _)
      _=d+((L-4-(i.val-4+1))+(i.val-4+1))*a := by ring
      _ = _:= by rw [Nat.sub_add_cancel hle]
private theorem recovery_fits {L:ℕ} (hL:4≤L) {g:af 4} {p:Shape}
    (hg:aO (shape g) p) (hp:bF p) (ht:p.t=1) :
    TaylorChart.dM (recovery L g) (weightedChart L p) := by
  have hj:3≤p.j:= by have :=hp.2; omega
  have hb:1≤p.b:=(by omega :1≤p.j).trans hp.1
  let w:Fin 4→ℕ:=Pi.single 3 1
  have hw3:w 3=1 := by decide
  have hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i,w i≤1 := by
    intro i
    fin_cases i <;> decide
  have hwg:W w g≤1 := by
    simpa only [w,weightedTotalDegree_piSingle,shape,ht] using hg.2.2
  have hgb:W 1 g≤p.b:= by simpa only [weightedTotalDegree_one,shape] using hg.1
  have hgj:W Fin.val g≤p.j:= by
    rw [← Ex.C6]
    exact hg.2.1
  have cb:=a9A (L:=L) 1 0 1 (fun _=> by simp) (fun _=>le_rfl) hb hgb
  have cj:=a9A (L:=L) Fin.val 1 3 (fun _=> by rfl)
    (fun j=>Nat.le_of_lt_succ j.isLt) hj hgj
  have ct :=a9A (L:=L) w 1 1 hshift hw hw3.le hwg
  have pkg (P:af 4) (h1 :W 1 P≤1+(L-4)*(p.b-1))
      (h2 :W Fin.val P≤3+(L-4)*(p.j-3+1))
      (h3:W w P≤1+(L-4)) :yy (bC P) (weightedChart L p) := by
    rw [weightedChart,ite_eq_left ht]
    have he :p.j-3+1=p.j - 2 := by omega
    rw [he] at h2
    apply abr
    refine ⟨(by simpa only [weightedTotalDegree_one] using h1 :
      P.totalDegree≤1+(L-4)*(p.b-1)).trans (le_max_left _ _),?_,?_⟩
    · simpa only [shape,Ex.C6] using h2
    · have htop:P.degreeOf 3≤1+(L-4) := by
        simpa only [w,weightedTotalDegree_piSingle] using h3
      have htop' := lB.a9d P
      change P.degreeOf 3≤ min (L-3) ((3+(L-4)*(p.j-2))/3)
      exact le_min (by omega) (by omega)
  simp only [Pi.one_apply,add_zero] at cb
  simp only [hw3,Nat.sub_self,zero_add,Nat.mul_one] at ct
  exact ⟨pkg _ cb.1 cj.1 ct.1,fun i=>pkg _ (cb.2 i) (cj.2 i) (ct.2 i)⟩
private theorem recovery_eval {L:ℕ} (hL:L≤K1.p) {g:af 4} {S:ao[X]}
    (hg: (shape g).t=1) (hon :cK g S=0) (hr :qg g S) :
    TaylorChart.aay (recovery L g) S:= by
  have hden:cK (denom L g) S=cK (separant g) S^(L-4) :=
    map_pow (MvPolynomial.eval (jet S:Fin 4→ao[X])) _ _
  constructor
  · change An S (bC (denom L g))≠0
    rw [afz,hden]
    exact (map_ne_zero_iff _ SZ).mpr (pow_ne_zero _ hr)
  · intro i
    change An S (bC (num L g i)) =
      An S (bC (denom L g))*j8 (hasseDeriv i.val S)
    rw [afz,afz,← map_mul]
    apply congrArg j8
    unfold num
    split_ifs with hi
    · unfold cK
      rw [map_mul,MvPolynomial.eval_X,mul_comm]
      rfl
    · let E :=MvPolynomial.eval (jet S:Fin 4→ao[X])
      change E (_ *(_^_ *_))= _
      rw [map_mul,map_mul,map_pow,MvPolynomial.eval_C]
      change _ *(cK (separant g) S^_ *cK (tail g (i.val-4)) S)= _
      rw [eval_tail hg hon,Nat.sub_add_cancel (show 4≤ i.val by omega),
        ajW]
      have hinv :Polynomial.C (↑i.val.factorial:ao)⁻¹ *
          Polynomial.C (↑i.val.factorial:ao)=1 := by
        rw [← map_mul,inv_mul_cancel₀ (ahA (i.isLt.trans_le hL)),map_one]
      have hpow:L-4-(i.val-4+1)+(i.val-4+1)=L-4 := by omega
      calc
        _=(Polynomial.C (↑i.val.factorial:ao)⁻¹*Polynomial.C (↑i.val.factorial:ao)) *
            ((cK (separant g) S^(L-4-(i.val-4+1))*cK (separant g) S^(i.val-4+1)) *
              hasseDeriv i.val S) := by ring
        _ = _:= by rw [hinv,one_mul,← pow_add,hpow,hden]
theorem value_cut {L:ℕ} (hl:4≤L) (hL:L≤K1.p) {g:af 4} {p:Shape}
    (hg:aO (shape g) p) (hp:bF p) (ht:0<p.t) (hs :separant g≠0)
    (x a :K1.K) :
    ∃ D:GeoJets,yy D (weightedChart L p) ∧
      ∀ S:K1.K[X],S.natDegree<L→cK g (extend S)=0→qg g (extend S) →
        (An (extend S) D =0↔S.eval x=a) := by
  by_cases h:p.t=1
  · have ht₀: (shape g).t≠0:= fun hz=>hs (pderiv_eq_zero_of_degreeOf_eq_zero hz)
    have ht₁:=hg.2.2
    rw [h] at ht₁
    have ht' : (shape g).t=1 := by omega
    let T:=recovery L g
    exact ⟨TaylorChart.pullback T (L4 L x a),TaylorChart.aWC T (recovery_fits hl hg hp h) _,
      fun S hS hon hr=>gKY T hS (recovery_eval hL ht' hon hr) x a⟩
  · simpa only [weightedChart,ite_eq_right h] using atq.d40 hL hg hp ht x a
end
end qAIBbfd
end
section
set_option autoImplicit true
namespace qnDrZ2b
noncomputable section
open Polynomial MvPolynomial aR dN
open K1 (K)
open wH (qg)
open lB (bF yy afz SZ
  abr abx Po ahA a9d)
open aY3 (aXG)
open private br5 ew1 eGF gpA ajW from ProximityPrize.SubmissionLower.ZG8ydqc
open private TaylorChart TaylorChart.mk TaylorChart.dM TaylorChart.aay TaylorChart.pullback TaylorChart.aWC L4 gKY from ProximityPrize.SubmissionLower.B5
local notation "W" => MvPolynomial.weightedTotalDegree
private def thirdJet (g:af 4) :ℕ→af 4
  | 0=>MvPolynomial.C (Polynomial.C (↑(3:ℕ).factorial:ao))*MvPolynomial.X 3
  | n+1=>br5 g n (thirdJet g n)
private theorem thirdJet_bound (w:Fin 4→ℕ) (δ:ℕ)
    (hs : ∀ i:Fin 3,w i.succ≤w i.castSucc+δ) {g:af 4} {B:ℕ}
    (hB:w 3≤B) (hg:W w g≤B) (n:ℕ) :
    W w (thirdJet g n)≤w 3+n*(B - w 3+δ) := by
  induction n with
  | zero =>
    simpa only [thirdJet,zero_mul,add_zero] using
      (Po w _ _).trans (abx (R:=ao[X]) w 3)
  | succ n ih =>
    simpa only [thirdJet,Nat.succ_mul,Nat.add_assoc] using ew1 w δ hs hB hg ih n
private theorem thirdJet_eval {g:af 4} (hg: (shape g).t=1) (S:ao[X])
    (hon :cK g S=0) (hr :qg g S) (n:ℕ) :
    cK (thirdJet g n) S=cK (separant g) S^n*derivative^[n+3] S:= by
  have hflow:=aNw g (separant g) S hon
  have hsep:cK (pK (separant g)) S=derivative (cK (separant g) S) := by
    simp only [u6,gpA hg,cK,map_mul,mul_zero,sub_zero] at hflow
    exact mul_left_cancel₀ hr hflow
  induction n with
  | zero =>
    change (MvPolynomial.eval (jet S:Fin 4→ao[X])) (_ *_)= _
    rw [map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,pow_zero,one_mul]
    exact (ajW S 3).symm
  | succ n ih =>
    let e :=MvPolynomial.eval (jet S:Fin 4→ao[X])
    change e (br5 g n (thirdJet g n))= _
    unfold br5
    rw [map_sub,map_mul,map_mul,map_natCast]
    change cK (u6 g (thirdJet g n)) S -
      (n:ao[X])*cK (pK (separant g)) S*cK (thirdJet g n) S= _
    rw [aNw _ _ _ hon,hsep,ih,eGF,
      Nat.succ_add,Function.iterate_succ_apply' (⇑(derivative :ao[X] →ₗ[ao] ao[X])) (n+3) S]
private def linearNumerator (L:ℕ) (g:af 4) (i:Fin L) :af 4 :=
  if hi:i.val<4 then MvPolynomial.X ⟨i.val,hi⟩*separant g^(L-4)
  else MvPolynomial.C (Polynomial.C ((↑i.val.factorial:ao)⁻¹)) *
    (separant g^(L-4-(i.val-3))*thirdJet g (i.val-3))
private theorem linearNumerator_bound {L:ℕ} (g:af 4) (i:Fin L)
    (w:Fin 4→ℕ) (δ:ℕ) (hs : ∀ k :Fin 3,w k.succ≤w k.castSucc+δ)
    (hw : ∀ k,w k≤w 3) {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) :
    W w (linearNumerator L g i)≤w 3+(L-4)*(B - w 3+δ) := by
  unfold linearNumerator
  split_ifs with hi
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      (Nat.add_le_add ((abx w _).trans (hw _))
        ((aXG w hg _).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))))
  · let n:=i.val-3
    have hn:n≤L-4 := by have :=i.isLt; dsimp [n]; omega
    apply (Po _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _≤(L-4 - n)*(B - w 3)+(w 3+n*(B - w 3+δ)) :=
        Nat.add_le_add (aXG w hg _) (thirdJet_bound w δ hs hB hg n)
      _≤(L-4 - n)*(B - w 3+δ)+(w 3+n*(B - w 3+δ)) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _
      _=w 3+(L-4 - n+n)*(B - w 3+δ) := by ring
      _ = _:= by rw [Nat.sub_add_cancel hn]
private theorem linear_fits {L:ℕ} {g:af 4} {p:Shape}
    (h4 :4≤L) (hg:aO (shape g) p) (hp:bF p) (ht:p.t=1) (P:af 4)
    (bound : ∀ (w:Fin 4→ℕ) (δ B:ℕ),
      (∀ k :Fin 3,w k.succ≤w k.castSucc+δ)→(∀ k,w k≤w 3) →
      w 3≤B→W w g≤B→W w P≤w 3+(L-4)*(B - w 3+δ)) :
    yy (bC P) (P6_6.weightedChart L p) := by
  rw [P6_6.weightedChart,ite_eq_left ht]
  have hj:3≤p.j:= by have :=hp.2; omega
  have h₁:=bound 1 0 p.b (fun _=> by simp) (fun _=>le_rfl)
    ((by omega :1≤p.j).trans hp.1) (by simpa only [shape,weightedTotalDegree_one] using hg.1)
  have h₂:=bound Fin.val 1 p.j (fun _=> by rfl)
    (fun i=>Nat.le_of_lt_succ i.isLt) hj (by simpa only [shape,← Ex.C6] using hg.2.1)
  change W Fin.val P≤3+(L-4)*(p.j-3+1) at h₂
  rw [show p.j-3+1=p.j - 2 by omega] at h₂
  let w:Fin 4→ℕ:=Pi.single 3 1
  have hw:w 3=1 := by decide
  have h₃:=bound w 1 1 (fun i=> by fin_cases i <;> decide)
    (fun i=> by fin_cases i <;> decide) hw.le
    (by
      have hh:=hg.2.2
      rw [ht] at hh
      simpa only [w,weightedTotalDegree_piSingle,shape] using hh)
  have htop:P.degreeOf 3≤1+(L-4) := by
    simpa only [hw,Nat.sub_self,zero_add,mul_one,w,weightedTotalDegree_piSingle] using h₃
  apply abr
  let j:=3+(L-4)*(p.j - 2)
  change P.totalDegree≤ max (1+(L-4)*(p.b - 1)) j ∧
    qE P≤j∧P.degreeOf 3≤ min (L-3) (j/3)
  refine ⟨?_,(Ex.C6 P).le.trans h₂,le_min ?_ ?_⟩
  · exact (by simpa only [Pi.one_apply,weightedTotalDegree_one,add_zero] using h₁ :
      P.totalDegree≤1+(L-4)*(p.b - 1)).trans (le_max_left _ _)
  · exact htop.trans (by omega)
  · have h:3*P.degreeOf 3≤j:=(a9d P).trans h₂
    omega
private theorem linear_recovers {L:ℕ} (hL:L≤K1.p) {g:af 4}
    (hg: (shape g).t=1) {S:ao[X]} (hon :cK g S=0) (hr :qg g S) :
    TaylorChart.aay (TaylorChart.mk (bC (separant g^(L-4)))
      (fun i=>bC (linearNumerator L g i))) S:= by
  let e :=MvPolynomial.eval (jet S:Fin 4→ao[X])
  let u:=cK (separant g) S
  have hden:e (separant g^(L-4))=u^(L-4) :=map_pow e _ _
  constructor
  · change An S (bC (separant g^(L-4)))≠0
    rw [afz,map_ne_zero_iff _ SZ]
    change e (separant g^(L-4))≠0
    rw [hden]
    exact pow_ne_zero _ hr
  · intro i
    change An S (bC (linearNumerator L g i)) =
      An S (bC (separant g^(L-4)))*j8 (hasseDeriv i.val S)
    rw [afz,afz,← map_mul]
    apply congrArg j8
    change e (linearNumerator L g i)=e (separant g^(L-4))*hasseDeriv i.val S
    unfold linearNumerator
    split_ifs with hi
    · rw [map_mul,MvPolynomial.eval_X,mul_comm]
      rfl
    · rw [map_mul,map_mul,map_pow,MvPolynomial.eval_C,hden]
      let n:=i.val-3
      change _ *(u^(L-4 - n)*cK (thirdJet g n) S)= _
      have hn:n≤L-4 := by have :=i.isLt; dsimp [n]; omega
      rw [thirdJet_eval hg S hon hr,show n+3=i.val by dsimp [n]; omega,ajW]
      have hinv :Polynomial.C (↑i.val.factorial:ao)⁻¹ *
          Polynomial.C (↑i.val.factorial:ao)=1 := by
        rw [← map_mul,inv_mul_cancel₀ (ahA (i.isLt.trans_le hL)),map_one]
      calc
        _=(Polynomial.C (↑i.val.factorial:ao)⁻¹*Polynomial.C (↑i.val.factorial:ao)) *
            ((u^(L-4 - n)*u^n)*hasseDeriv i.val S) := by ring
        _ = _:= by rw [hinv,one_mul,← pow_add,Nat.sub_add_cancel hn]
theorem d40 {L:ℕ} (h4 :4≤L) (hL:L≤K1.p) {g:af 4} {p:Shape}
    (hg:aO (shape g) p) (hp:bF p) (ht:0<p.t)
    (hgt:0<(shape g).t) (x a :K) :
    ∃ D:GeoJets,yy D (P6_6.weightedChart L p) ∧
      ∀ S:K[X],S.natDegree<L→cK g (extend S)=0→qg g (extend S) →
        (An (extend S) D =0↔S.eval x=a) := by
  by_cases h:p.t=1
  · have hs : (shape g).t=1 := by have :=hg.2.2; omega
    let T:=TaylorChart.mk (bC (separant g^(L-4)))
      (fun i:Fin L=>bC (linearNumerator L g i))
    have hfit :TaylorChart.dM T (P6_6.weightedChart L p) := by
      refine ⟨linear_fits h4 hg hp h _ ?_,fun i=>linear_fits h4 hg hp h _ ?_⟩
      · intro w δ B _ _ _ hB
        exact (aXG w hB _).trans
          ((Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans (Nat.le_add_left _ _))
      · intro w δ B hw hw' hB hg'
        exact linearNumerator_bound g i w δ hw hw' hB hg'
    exact ⟨TaylorChart.pullback T (L4 L x a),TaylorChart.aWC T hfit _,
      fun S hd hon hr=>gKY T hd (linear_recovers hL hs hon hr) x a⟩
  · simpa only [P6_6.weightedChart,ite_eq_right h] using atq.d40 hL hg hp ht x a
end
end qnDrZ2b
end
