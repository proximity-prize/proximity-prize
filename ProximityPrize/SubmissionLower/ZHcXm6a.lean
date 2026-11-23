import ProximityPrize.SubmissionLower.ZUkTKja
set_option Elab.async false
section
set_option autoImplicit true
namespace q84jfie
noncomputable section
open P6 (I K dw)
open P6_7 (RectTail)
open P6_7_2 (Input cheapWidth strongWidth)
open qlc9qed (Bank ays)
open aR (ao jF embed)
open jA
open NR (amn)
open acZ (OV Bu)
open private cutoff from ProximityPrize.SubmissionLower.S
def width (b:RectTail) :Bank→ℕ
  | .cheap=>cheapWidth b
  | .strong=>strongWidth b
def cut (a :Bank) :ℕ:=a.m*dw - 1
def az0:Bank→ℕ
  | .cheap=>0x11df582f2a
  | .strong=>0xc0f07efa48
def ambientCount (a :Bank) (h U:ℕ) :ℕ:=(U+1)*(az0 a+a.basePole*h)
def eMG (a :Bank) (h U:ℕ) :ℕ:=h*((U+1)*a.basePole+a.poleExcess)
def Aw (a :Bank) (h U t:ℕ) :Submodule ao jK :=
  ((OV a.box).restrictScalars ao).comap Bu ⊓
  ((MvPolynomial.restrictWeightedDegree (R:=iP)
    (Pi.single (none :mA) 1) U).restrictScalars ao).comap Bu ⊓
  cutoff h (t+(a.box.b+a.box.j)*h)
def contacts (w:I→K) (a :Bank) :Submodule ao jK :=
  ⨅ i:I,ays a.m (embed (P6.node i)) (embed (w i))
abbrev pole {Γ s} (P:jF Γ s) (L:kH P) (a :Bank) :Submodule ao jK :=
  amn P L a.box (jH P.H)
def aV {Γ s} (w:I→K) (P:jF Γ s) (L:kH P) (a :Bank) (U t:ℕ) :
    Submodule ao jK :=
  Aw a P.H.natDegree U t ⊓ (contacts w a ⊓ pole P L a)
def powerAt (h t:ℕ) :ℕ:=1+(cut .strong - t)/(3*h)
def aMH (a :Bank) (h U:ℕ) :ℕ :=
  match a with
  | .cheap=>0
  | .strong=>(3*h)*U*665000
structure OnePole {b:RectTail} (x :Input b) where
  data :jF x.Γ x.F.scalar
  bY:kH data
  block :data.H=x.H
  height:data.H.natDegree=x.h
  Kw : ∀ γ,data.z γ=embed (x.M.label γ)
end
end q84jfie
end
section
set_option autoImplicit true
namespace P6_7_2_3
noncomputable section
open P6 (K p)
open P6_7 (RectTail)
open P6_7_2
open cu (Jet Shape)
open gT (Ambient IZ iJ aci)
open pI (xN dual oU pN)
open TD (GM FP J2 arC auN)
open P5_7_1 (wD)
open scoped BigOperators Classical
abbrev Origin :=Fin 14
abbrev bAL:=Fin 7
abbrev FreeTest:=Fin 5
abbrev last :Origin :=13
abbrev terminalStop:bAL:=6
def introCap (b:RectTail) (o:Origin) :Fin 3→ℕ :=
  ((List.ofFn fun i:Aux=>(auxReserve i,auxiliary b i)).take o.val).foldl
    (fun v (r,s) j=>min (v j) (auN s j/(r+1))) (auN (free b 0))
def topCut (b:RectTail) (v :Fin 3→ℕ) :Shape :=
  ⟨0,164+19*(v 0-1),50+19*(v 1-1),strongWidth b+19*v 2⟩
def originShape (b:RectTail) (o:Origin) :Shape :=
  if h:o.val<13 then auxiliary b ⟨o.val,h⟩ else topCut b (introCap b last)
def kK (v :Fin 3→ℕ) (s :Shape) :GM :=
  fun k => ∑ j,(v j:ℚ)*arC s k j
def originBox (b:RectTail) (o:Origin) :GM :=
  kK (introCap b o) (originShape b o)
def BC (b:RectTail) :GM :=
  match b with
  | .pruned => ![8395,142162,679177,5128992]
  | .tailOne => ![8395,130972,622854,4359826]
  | .tailTwo => ![8395,123306,584565,3862406]
  | .tailThree => ![8395,117001,553229,3471117]
def ee3:RectTail→ℕ
  | .pruned=>0xd8a5366feb7b6
  | .tailOne=>0xac99d103018b9
  | .tailTwo=>0xa00d1de9efd79
  | .tailThree=>0x95e05d8ddf990
abbrev degree (b:RectTail) :=131071+(Bs b).hi
abbrev oldAgreement:ℕ:=179740
def lineFee (b:RectTail) (B J U:ℕ) :ℕ :=
  let t:=2*degree b-3
  let a :=1+t*(B-1)
  let v :=min a (t*(J-1)+degree b)
  let w:=t*U
  let mix :=U*(2*a*v-v*v)+2*w*(B*v+J*(a-v))
  let rest:=U*(2*a+v)+w*(2*B+J)+B*v+J*a+U+B+J
  let gap:=oldAgreement-degree b
  (2*(262144-oldAgreement)*(mix+rest)+gap-1)/gap+B+U+1
def freePass {b:RectTail} {x :Input b} (P:Poles x) (i:Ls) (Q:Ideal Ambient) :Prop :=
  ∀ G∈P.rows (free b i) (cutoff x.h 0 (free b i)),iJ G∈Q
def terminalPass {b:RectTail} {x :Input b} (P:Poles x) (Q:Ideal Ambient) :Prop :=
  ∀ G∈rectRows P (full b) (rectCutoff b x.h),iJ G∈Q
def passes {b:RectTail} {x :Input b} (P:Poles x) (s :bAL) (Q:Ideal Ambient) :Prop :=
  if s=0 then dual Q
  else if h:s.val<6 then freePass P ⟨s.val,h⟩ Q else terminalPass P Q
abbrev onMark {b:RectTail} (x :Input b) (Q:Ideal Ambient) (γ:K) :Prop :=
  IZ Q (x.M.label γ) (x.F.scalar γ)
def marks {b:RectTail} (x :Input b) (Q:Ideal Ambient) :Finset K :=
  x.Γ.filter (onMark x Q)
def lineCharge (b:RectTail) (f :Jet) (line :Bool) :ℕ :=
  if line then lineFee b (wD f 0) (wD f 1) (wD f 2) else 0
def anZ (b:RectTail) (o:Origin) (f :Jet) (line :Bool) :Shape :=
  if line then ⟨0,wD f 0,wD f 1,wD f 2⟩ else originShape b o
structure OriginCover {b:RectTail} {x :Input b} (P:Poles x) (pick :Picks (b:=b) x.h P.rows) where
  factors :Finset Jet
  origin :Jet→Origin
  cut:Jet→Jet
  line :Jet→Bool
  lineMarks :Jet→Finset K
  parents :Jet→Finset (Ideal Ambient)
  gH :Finset K
  paid_bound:gH.card≤ee3 b
  distinct : (factors :Set Jet).Pairwise fun f g => ¬ Associated f g
  nested : ∀ o j,(∑ f∈factors.filter (fun f=>o≤origin f),wD f j)≤ introCap b o j
  proper : ∀ f∈factors,Irreducible f∧f∣pick.freeRow 0 ∧ ¬ f∣cut f
  cut_caps : ∀ f∈factors,oU (cut f) (anZ b (origin f) f (line f))
  shared_cut : ∀ f∈factors,∀ g∈factors,origin f≠last→ origin f=origin g→cut f=cut g
  line_pos : ∀ f∈factors,line f=true→ origin f=last∧0<wD f 1∧0<wD f 2
  line_bound : ∀ f∈factors,(lineMarks f).card≤lineCharge b f (line f)
  geometric : ∀ f∈factors,∀ Q∈parents f,
    xN Q∧Q.height=2∧iJ f∈Q∧iJ (cut f)∈Q
  disjoint : ∀ f∈factors,∀ g∈factors,f≠g→Disjoint (parents f) (parents g)
  Eh : ∀ γ∈x.Γ,γ∈gH ∨ ∃ f∈factors,
    γ∈lineMarks f ∨ ∃ Q∈parents f,onMark x Q γ
def QV {b:RectTail} {x :Input b} {P:Poles x} {pick} (O:OriginCover P pick)
    (f :Jet) (s :bAL) :Finset (Ideal Ambient) :=
  (O.parents f).filter fun Q => ∀ t<s,passes P t Q
def Hj {b:RectTail} {x :Input b} {P:Poles x} {pick} (O:OriginCover P pick)
    (f :Jet) (s :bAL) :Finset (Ideal Ambient) :=
  (QV O f s).filter fun Q => ¬ passes P s Q
def final {b:RectTail} {x :Input b} {P:Poles x} {pick} (O:OriginCover P pick)
    (f :Jet) :Finset (Ideal Ambient) :=
  (O.parents f).filter fun Q => ∀ t,passes P t Q
def refShape (b:RectTail) (o:Origin) :Shape :=
  let s :=originShape b o
  let v :=introCap b o
  ⟨0,max s.B (v 0),max s.J (v 1),max s.U (v 2)⟩
def freeStage (i:FreeTest) :Ls :=i.succ
def freeStop (i:FreeTest) :bAL:=⟨i.val+1,by have :=i.isLt; omega⟩
def liveCap (b:RectTail) (o:Origin) (s :bAL) :GM :=
  ((List.ofFn fun i:FreeTest=>freeStage i).take (s.val-1)).foldl
    (fun a i k=>min (a k) (kK (auN (free b i)) (refShape b o) k /
      (dI i+1 :ℕ))) (originBox b o)
def memberCap (b:RectTail) (o:Origin) (s :bAL) :GM :=
  fun k=>min (liveCap b o s k) (BC b k)
def endCap (b:RectTail) (o:Origin) :GM :=
  fun k=>liveCap b o terminalStop k*(if o=last then ∑ j,introCap b o j else 1 :ℕ)
def sectionMass (Q:Ideal Ambient) :GM:= fun k=>pN Q k
def Tl (U:ℕ) (s :Shape) :GM := ![U,s.B-s.J,s.J,0]
def pointWeight (U:ℕ) (s :Shape) :GM := ![0,0,U,s.B]
def projectionBound (b:RectTail) :ℚ :=
  FP (Tl (2*(Bs b).terminal.U) (Bs b).terminal) (BC b)
def freeAllowance (b:RectTail) (i:FreeTest) :GM :=
  let s :=free b (freeStage i)
  fun k=>Tl s.U s k+pointWeight s.U s k
def terminalAllowance (b:RectTail) :GM :=
  pointWeight (2*(Bs b).terminal.U) (Bs b).terminal
def freeProjection (b:RectTail) (o:Origin) (i:FreeTest) :ℚ :=
  let s :=free b (freeStage i)
  min (projectionBound b) (FP (Tl s.U s) (memberCap b o (freeStop i)))
def terminalProjection (b:RectTail) (o:Origin) (axes :ℕ) :ℚ :=
  let s :=(Bs b).terminal
  min (projectionBound b) (FP (Tl (axes*s.U) s) (memberCap b o terminalStop)) /
    ((Bs b).paidOrder+1 :ℕ)
structure TerminalCutter {b:RectTail} (x :Input b) (Q:Ideal Ambient) where
  row:Ambient
  proper :row∉Q
  caps : ∀ a∈row.support,a 0≤(Bs b).terminal.U∧a 1≤(Bs b).terminal.U ∧
    a 2+a 3≤(Bs b).terminal.B∧a 3≤(Bs b).terminal.J
  necessary : ∀ γ∈x.Γ,∀ a :Fin 4 →₀ ℕ,(∑ i,a i)≤(Bs b).paidOrder →
    aci (x.M.label γ) (x.F.scalar γ) (Rk.KR a row)=0
def stock (b:RectTail) (o:Origin) (f :Jet) (line :Bool) :GM :=
  kK (wD f) (anZ b o f line)
def MemberFits (b:RectTail) (o:Origin) (s :bAL) (Q:Ideal Ambient) :Prop :=
  ∀ k,sectionMass Q k≤ memberCap b o s k
structure Geometry {b:RectTail} {x :Input b} {P:Poles x} {pick} (O:OriginCover P pick) :Prop where
  spend_order : ∀ f∈O.factors,wD f 1≤wD f 0
  initial : ∀ f∈O.factors,∀ k,J2 (O.parents f) k≤ stock b (O.origin f) f (O.line f) k
  bAW : ∀ k,(∑ f∈O.factors,J2 (O.parents f) k)≤BC b k
  member : ∀ f∈O.factors,∀ s Q,Q∈QV O f s→MemberFits b (O.origin f) s Q
  finalPool : ∀ o k,(∑ f∈O.factors.filter (fun f=>O.origin f=o),
    J2 (QV O f terminalStop) k)≤endCap b o k
structure aAU (b:RectTail) where
  factors :Finset Jet
  origin :Jet→Origin
  line :Jet→Bool
  arL:Jet→bAL→GM
  nonneg : ∀ f∈factors,∀ s k,0≤arL f s k
  spend_order : ∀ f∈factors,wD f 1≤wD f 0
  nested : ∀ o j,(∑ f∈factors.filter (fun f=>o≤origin f),wD f j)≤ introCap b o j
  line_pos : ∀ f∈factors,line f=true→ origin f=last∧0<wD f 1∧0<wD f 2
  initial : ∀ f∈factors,∀ k,(∑ s,arL f s k)≤ stock b (origin f) f (line f) k
  bAW : ∀ k,(∑ f∈factors,∑ s,arL f s k)≤BC b k
  finalPool : ∀ o k,(∑ f∈factors.filter (fun f=>origin f=o),arL f terminalStop k)≤endCap b o k
end
end P6_7_2_3
namespace P6_7_2_3
noncomputable section
open P6 (p)
open P6_7 (RectTail)
open P6_7_2
open cu (Jet)
open TD (GM FP)
open scoped BigOperators
def rankPrice (b:RectTail) (o:Origin) :GM :=
  let B:=memberCap b o 0 2
  let J:=min (memberCap b o 0 1) B
  let L:=(262144 :ℚ)/oldAgreement
  let gap:=oldAgreement-degree b
  let mu:=((262144-degree b:ℕ) :ℚ)/gap
  let q:=if B=0 then 0 else 4*J-2*J*J/B
  ![0,4*L*degree b*B/10+mu,L*degree b*q*9/10+B+1,0]
def persistentRate (b:RectTail) (g:ℕ) :ℚ :=
  (2*(g:ℚ)-1)*(1+2*(262144 :ℚ)/oldAgreement*degree b) +
    ((262144-degree b:ℕ) :ℚ)/(oldAgreement-degree b:ℕ)
def NativeOK (D e g c W M:ℕ) :Prop :=
  let E :=e+g
  let L:=(g+1)*c
  let j:=L/(c+1)
  0<c∧e*D ≤W∧M=W+1+j*D ∧E*D <M ∧
    (c+1)*(D*E*(E+1)/2+D*j*(j+1)/2)<L*M ∧
    (2*e-1)*W-e*e*D <p
def nativeRate (D e g c W:ℕ) :ℚ :=
  max (e*(c+1)+e+g:ℕ)
    ((7+6*e :ℕ)+((2*e+1)*262144+(6*e-2)*W-3*e*e*D:ℕ)/((oldAgreement-D:ℕ) :ℚ))
def BlendOK (b:RectTail) (g:ℕ) (q d z a h:ℚ) :Prop :=
  let gap:ℚ:=(oldAgreement-degree b:ℕ)
  (1-a/q)*persistentRate b g≤h ∨
  (g=1∧(1-a/q)*(1+3*262144/gap)≤h) ∨
  (g=2∧16≤ min z a∧(13+8*262144/gap)*(q-a)/(q-16)≤h) ∨
  (3≤g ∧ ∃ extra c W M,NativeOK (degree b) g extra c W M ∧
    let a₀:=d/(3*(g:ℚ))+4*g+8
    a₀≤ min z a∧nativeRate (degree b) g extra c W*(q-a)/(q-a₀)≤h)
def FreeOK (b:RectTail) (o:Origin) (i:FreeTest) (a h:ℚ) :Prop :=
  let d:=freeProjection b o i
  0≤d∧d<(p:ℚ)∧d≤a∧0≤h ∧
    ∀ g:ℕ,0<g→a<((p+1 :ℕ) :ℚ)/g →
      BlendOK b g (((p+1 :ℕ) :ℚ)/g) d a a h
def TerminalOK (b:RectTail) (o:Origin) (z a h:ℚ) :Prop :=
  let kd:=terminalProjection b o 1
  let d:=min (terminalProjection b o 2) (2*kd)
  0≤d∧d<(p:ℚ)∧0<a∧2*kd≤a∧a<(p:ℚ)∧2≤z∧0≤h ∧
    ∀ g:ℕ,0<g→a<(p:ℚ)/g →
      BlendOK b g ((p:ℚ)/g) d z a h
def freePrice (b:RectTail) (i:FreeTest) (a h:ℚ) :GM :=
  let s :=free b (freeStage i)
  ![a*s.U,a*(s.B-s.J:ℕ)+h*s.U,a*s.J,h*s.J]
def terminalPrice (b:RectTail) (z a h:ℚ) :GM :=
  let s :=(Bs b).terminal
  let r :=(Bs b).paidOrder
  let den:ℚ:=(r+1 :ℕ)
  let y :ℚ:=(s.B-s.J:ℕ)
  let zPrice :=if r=0 then z/den else max (s.U:ℚ) (z/den)
  let tPrice :=if r=0 then (a+1)/den else max (s.U:ℚ) ((a+1)/den)
  let yPrice :=if r=0 then h/den else max y (h/den)
  let jPrice :ℚ:=if r=0 then 0 else s.J
  ![(zPrice+tPrice)*s.U,(zPrice+tPrice)*y+2*s.U*yPrice,
    (zPrice+tPrice)*s.J+2*s.U*jPrice,s.J*yPrice+(y+s.J)*jPrice]
structure Rates (b:RectTail) where
  freeSeed :Origin→FreeTest→ℚ
  freeHeight:Origin→FreeTest→ℚ
  terminalZ:Origin→ℚ
  terminalT:Origin→ℚ
  terminalHeight:Origin→ℚ
def priceAt {b:RectTail} (R:Rates b) (o:Origin) (s :bAL) :GM :=
  if s=0 then rankPrice b o else
  if h:s.val<6 then
    let i:FreeTest:=⟨s.val-1,by omega⟩
    freePrice b i (R.freeSeed o i) (R.freeHeight o i)
  else terminalPrice b (R.terminalZ o) (R.terminalT o) (R.terminalHeight o)
def bAY (b:RectTail) (s :bAL) :GM :=
  if s=0 then 0 else
  if h:s.val<6 then freeAllowance b ⟨s.val-1,by omega⟩ else terminalAllowance b
structure cL (b:RectTail) extends Rates b where
  freeOK : ∀ o i,FreeOK b o i (freeSeed o i) (freeHeight o i)
  terminalOK : ∀ o,TerminalOK b o (terminalZ o) (terminalT o) (terminalHeight o)
  Az : ∀ B:aAU b,
    (ee3 b:ℚ)+(∑ f∈B.factors,((lineCharge b f (B.line f) :ℚ) +
      ∑ s,FP (priceAt toRates (B.origin f) s+bAY b s) (B.arL f s))) ≤
      (prefixFee b:ℚ)
end
end P6_7_2_3
end
section
set_option autoImplicit true
namespace qigFtUb
open Finset cu P6_7_2
open P6 (dw)
open P6_7 (RectTail)
open Y2 (Tb)
open private crN diagonal from ProximityPrize.SubmissionLower.D9
def stock (U spent:ℕ) :ℕ:=U+1-spent
theorem stock_anti (U:ℕ) :Antitone (stock U) :=
  fun _ _ h=>Nat.sub_le_sub_left h _
def width (b:RectTail) (h q j t:ℕ) :ℤ :=
  (((Bs b).terminal.m*dw:ℕ) :ℤ)+j -
    (131071-(h:ℤ))*q - 2*(h:ℤ)*((Bs b).dI+t)
private theorem cast_sub_le (x y :ℕ) : (x :ℤ)-y≤((x-y :ℕ) :ℤ) := by omega
theorem dma (b:RectTail) (h q j t:ℕ) (hh:h≤131071) :
    width b h q j t≤((amv b h q j - 2*h*t:ℕ) :ℤ) := by
  have hc:=cast_sub_le ((Bs b).terminal.m*dw) (1+2*h*(Bs b).dI)
  rw [← Nat.sub_sub] at hc
  have h0: (((Bs b).terminal.m*dw:ℕ) :ℤ)-2*(h:ℤ)*(Bs b).dI ≤
      (rectCutoff b h:ℤ)+1 := by
    change _≤(↑((Bs b).terminal.m*dw-1-2*h*(Bs b).dI:ℕ) :ℤ)+1
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hc ⊢
    omega
  have h1 :=cast_sub_le (rectCutoff b h+1+j) (q*(131071-h))
  have h2 :=cast_sub_le (amv b h q j) (2*h*t)
  change _≤(amv b h q j:ℤ) at h1
  push_cast [Nat.cast_sub hh] at h1 h2
  unfold width
  nlinarith only [h0,h1,h2]
def active (b:RectTail) (u:ℕ) :Shape := { (Bs b).terminal with U:=u }
def O3 (s :Shape) (E v :ℕ) (f :ℕ→ℕ→ℕ→ℤ) :ℤ :=
  ∑ q∈range (s.B+1),∑ j∈range (min q s.J+1),
    let g:=(q-j)/E
    let c:= fun a=>stock s.U (a*v)
    (∑ a∈range g,((c a - c (a+1) :ℕ) :ℤ)*f q j (j+a)) +
      (c g:ℤ)*f q j (j+g)
theorem gain_le (s :Shape) (E v :ℕ) {f g:ℕ→ℕ→ℕ→ℤ}
    (hf : ∀ q j t,f q j t≤g q j t) :O3 s E v f≤O3 s E v g:= by
  unfold O3
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro j _
  dsimp only
  apply add_le_add
  · exact sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (hf _ _ _) (Int.natCast_nonneg _)
  · exact mul_le_mul_of_nonneg_left (hf _ _ _) (Int.natCast_nonneg _)
theorem gain_add (s :Shape) (E v :ℕ) (f g:ℕ→ℕ→ℕ→ℤ) :
    O3 s E v (fun q j t=>f q j t+g q j t)=O3 s E v f+O3 s E v g:= by
  unfold O3
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  simp only [mul_add,sum_add_distrib]
  ring
theorem gain_mul (s :Shape) (E v :ℕ) (x :ℤ) (f :ℕ→ℕ→ℕ→ℤ) :
    O3 s E v (fun q j t=>x*f q j t)=x*O3 s E v f := by
  unfold O3
  simp only [mul_sum,mul_add,mul_left_comm x]
theorem gain_rect (b:RectTail) (h u x E v :ℕ) :
    (ZN b h ⟨u,x⟩ 0 E v :ℤ) =
      (x+1 :ℤ)*O3 (active b u) E v (fun q j t=>(↑(amv b h q j-2*h*t:ℕ) :ℤ)) := by
  have hs (a :ℕ) :seedStock ⟨u,x⟩ 0 a=(x+1)*stock u a := by simp [seedStock,stock]
  unfold ZN ku O3
  simp only [hs,active,← Nat.mul_sub_left_distrib,Nat.cast_sum,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one,mul_add,mul_sum,mul_assoc]
theorem debit_swap (b:RectTail) (h u x :ℕ) :
    rectDebit b h ⟨x,u⟩=rectDebit b h ⟨u,x⟩:= by unfold rectDebit; dsimp only; ring
theorem gain_swap (b:RectTail) (h u x E v :ℕ) :
    ZN b h ⟨x,u⟩ 1 E v=ZN b h ⟨u,x⟩ 0 E v := by
  have hs (a :ℕ) :seedStock ⟨x,u⟩ 1 a=seedStock ⟨u,x⟩ 0 a := by
    simp [seedStock,show (1 :Fin 2)≠0 by decide]
  simp only [ZN,hs]
def phase (s :Shape) (E v d:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :ℤ :=
  ∑ t∈range (s.J+Tb s E v),∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
    (stock s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (t-a+E*(a+d)) (s.B+1),f q (t-a) t
private theorem eNa (s :Shape) (E v q j:ℕ) (f :ℕ→ℕ→ℕ→ℤ)
    (he :0<E) (hq:q≤ s.B) (hj:j≤q) :
    let c:= fun a=>stock s.U (a*v)
    let g:=(q-j)/E
    let w:= fun d a=>(c (a+d) :ℤ)*f q j (j+a)
    (∑ a∈range g,((c a - c (a+1) :ℕ) :ℤ)*f q j (j+a))+c g*f q j (j+g) =
      (∑ a∈range (Tb s E v),if j+E*(a+0)≤q then w 0 a else 0) -
      (∑ a∈range (Tb s E v),if j+E*(a+1)≤q then w 1 a else 0) := by
  dsimp only
  let g:=(q-j)/E
  let w:= fun d a=>(stock s.U ((a+d)*v) :ℤ)*f q j (j+a)
  have hs (a :ℕ) :
      (↑(stock s.U (a*v) - stock s.U ((a+1)*v) :ℕ) :ℤ) =
        (stock s.U (a*v) :ℤ) - stock s.U ((a+1)*v) :=
    Int.ofNat_sub (stock_anti _ (Nat.mul_le_mul_right v (by omega)))
  simp only [hs,sub_mul,sum_sub_distrib]
  change (∑ a∈range g,w 0 a)-(∑ a∈range g,w 1 a)+w 0 g= _
  rw [sub_add_eq_add_sub,← sum_range_succ]
  have hz (d a :ℕ) (ha :Tb s E v≤a) (hg:a+d≤g) :w d a=0:= by
    have hcap:g≤ s.B/E :=Nat.div_le_div_right (by omega)
    unfold Tb at ha
    split at ha
    · omega
    · rename_i hv
      have hlarge :s.U/v<a+d:= by omega
      have hout:s.U<(a+d)*v := by
        by_contra! hm
        exact (not_le_of_gt hlarge) ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)).2 hm)
      simp [w,stock,Nat.sub_eq_zero_of_le (by omega :s.U+1≤(a+d)*v)]
  have hdiv (a d:ℕ) :j+E*(a+d)≤q↔a+d≤g:= by
    rw [Nat.le_div_iff_mul_le he,Nat.mul_comm (a+d) E]
    omega
  rw [crN (g+1) _ (fun a ha hb=>hz 0 a ha (by omega)),
    crN g _ (fun a ha hb=>hz 1 a ha (by omega))]
  have hzero (a :ℕ) :j+E*a≤q↔a≤g:= by simpa using hdiv a 0
  simp only [hzero,Nat.add_zero,Nat.lt_succ_iff,Nat.add_one_le_iff,w]
private def bty (s :Shape) (E v d:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :ℤ :=
  ∑ q∈range (s.B+1),∑ j∈range (s.J+1),∑ a∈range (Tb s E v),
    if j+E*(a+d)≤q then (stock s.U ((a+d)*v) :ℤ)*f q j (j+a) else 0
private theorem c30 (s :Shape) (E v d q:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :
    (∑ j∈range (min q s.J+1),∑ a∈range (Tb s E v),
      if j+E*(a+d)≤q then (stock s.U ((a+d)*v) :ℤ)*f q j (j+a) else 0) =
    ∑ j∈range (s.J+1),∑ a∈range (Tb s E v),
      if j+E*(a+d)≤q then (stock s.U ((a+d)*v) :ℤ)*f q j (j+a) else 0:= by
  apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
  intro j hj hnot
  simp only [mem_range,Nat.lt_succ_iff,le_min_iff] at hj hnot
  apply sum_eq_zero
  intro a _
  rw [ite_eq_right (by omega)]
private theorem c3Z (s :Shape) (E v d:ℕ) (f :ℕ→ℕ→ℕ→ℤ) :
    bty s E v d f=phase s E v d f := by
  have hR:Tb s E v-1+1=Tb s E v := by
    apply Nat.sub_add_cancel
    unfold Tb
    split
    · exact Nat.succ_pos _
    · exact le_min (Nat.succ_pos _) (Nat.succ_pos _)
  unfold bty phase
  rw [sum_comm]
  conv_lhs =>
    enter [2,j]
    rw [sum_comm]
  conv_lhs =>
    rw [← hR]
    rw [diagonal]
  rw [Nat.add_assoc,hR]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro a ha
  have hta :t-a+a=t:=Nat.sub_add_cancel (by have :=(mem_Ico.mp ha).2; omega)
  rw [mul_sum,← sum_filter]
  have hf : (range (s.B+1)).filter (fun q=>t-a+E*(a+d)≤q) =
      Ico (t-a+E*(a+d)) (s.B+1) := by
    ext q
    simp only [mem_range,mem_filter,mem_Ico]
    tauto
  rw [hf,hta]
theorem gain_phases (s :Shape) (E v :ℕ) (f :ℕ→ℕ→ℕ→ℤ)
    (he :0<E) :O3 s E v f=phase s E v 0 f - phase s E v 1 f := by
  rw [← c3Z s E v 0 f,← c3Z s E v 1 f]
  unfold O3 bty
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  rw [← c30 s E v 0 q,← c30 s E v 1 q,← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [mem_range,Nat.lt_succ_iff] at hq hj
  exact eNa s E v q j f he hq (hj.trans (min_le_left _ _))
end qigFtUb
end
