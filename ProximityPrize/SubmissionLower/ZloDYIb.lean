import ProximityPrize.SubmissionLower.D7
import ProximityPrize.SubmissionLower.Zqb2cFb
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
set_option Elab.async false
set_option autoImplicit true
namespace q7F2qKe
noncomputable section
open Polynomial Finset
open scoped BigOperators Classical
open P5 (K p jG)
open P5_7_2 (A fO Window Ls Aux stages introduction movingOrder topDonors Donors NodeUnits wordLift O2 terminal row)
open cu (L Shape Jet vP j9)
open DP (jF zG aKF VY)
open gT (Ambient tK IZ iJ FW)
open pI (xN dual oU abM NO acW pN weight)
open TD (GM J2 FP bCb bf7 auN arC aBh)
abbrev bTu:=Fin 3→ℕ
abbrev weakAgreement:ℕ:=179740
def wX (b:fO) :=131071+(row b).declaredHi
structure Input (b:fO) {u del} (M:jG u del) {Γ} (F:P1.bje A M Γ) where
 vo:Window b M.iF
 regular :M.shift∉Γ
 H :L[X]
 bY:P5_7.YQ M F H
 D:jF M.iF.toNat
 first:D.block 0=H
 second:D.block 1=H.map (frobenius L p)
 units :NodeUnits D
 residues : ∀ γ∈Γ,aKF D (M.label γ) (F.scalar γ)
 crt:zG D
 donors :Donors b crt (wordLift M)
abbrev Input.banks {b u del M Γ F} (x : @Input b u del M Γ F) :=VY x.crt (wordLift M)
def I0 {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (I:Ideal Ambient) (γ:K) :Prop :=IZ I (M.label γ) (F.scalar γ)
def aHl {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ)
    (C:acW) :Finset K:=Γ.filter fun γ => ∃ Q∈C.qv,I0 F Q γ
def agA (rows :vP) (s :Shape) (I:Ideal Ambient) :Prop :=
 ∀ P∈rows s (O2 s),iJ P∈I
def nV (b:fO) (i:ℕ) :Ls :=
 ((stages b)[i]?).getD ⟨0,(terminal b).shape,(terminal b).shape⟩
def originCount (b:fO) :=(introduction b).length+1
def origins (b:fO) :=range (originCount b)
def isLast (b:fO) (o:ℕ) :Prop :=o=(introduction b).length
def originBudget (b:fO) (o:ℕ) :bTu :=
  ((introduction b).take o).foldl
    (fun r a k=>min (r k) (auN a.shape k/(a.dI+1)))
    (auN (nV b 0).free)
def aur (r :bTu) :Shape :=⟨0,r 0,r 1,r 2⟩
def originCutter (b:fO) (o:ℕ) :Shape :=
  match (introduction b)[o]? with
  | some a=>a.shape
  | none =>
    let r :=originBudget b o
    let t:=(topDonors b).2
    ⟨0,t.shape.B+t.YM*(r 0-1),t.shape.J+t.YM*(r 1-1),t.shape.U+t.YM*r 2⟩
def kK (r :bTu) (s :Shape) (k :Fin 4) :ℕ := ∑ q,arC s k q*r q
def graphMass (e v :ℕ) :Fin 4→ℕ := ![e,v,2*e*v,v*v]
def BC (b:fO) (k :Fin 4) :ℕ :=
  let step:= fun old s q=>max (old q) (arC s k q)
  let update := fun (acc:ℕ×bTu) o =>
    let next:=step acc.2 (originCutter b o)
    (acc.1 + ∑ q,(next q-acc.2 q)*originBudget b o q,next)
  let r :=originBudget b (introduction b).length
  ((List.range (originCount b)).foldl update (0,fun _=>0)).1+graphMass (r 0) (r 2) k
def freeCount (b:fO) :=(stages b).length-1
def afterFree (b:fO) :=freeCount b+1
def stopCount (b:fO) :=afterFree b+(movingOrder b).length+1
def stops (b:fO) :=range (stopCount b)
def a3D (s :Ls) :Shape :=
 let j:=max s.free.J s.moving.J
 ⟨0,max (s.free.B-s.free.J) (s.moving.B-s.moving.J)+j,j,max s.free.U s.moving.U⟩
def aHp (b:fO) (j:ℕ) :Shape :=
 if j<afterFree b then (nV b j).free else
 match (movingOrder b)[j-afterFree b]? with
 | some i=>a3D (nV b i)
 | none=>(terminal b).shape
def globalCap (b:fO) (j:ℕ) :GM :=
  ((movingOrder b).take (j-afterFree b)).foldl
    (fun cap i=> let s :=nV b i; bCb cap (bf7 s.free s.moving s.dI true))
    (fun k=>BC b k)
def freeCap (b:fO) (o j:ℕ) :GM :=
  let r :=originBudget b o
  let c:=originCutter b o
  let ref :=aur fun k=>max (r k) (auN c k)
  (List.range' 1 (min (j-1) (freeCount b))).foldl
    (fun cap i =>
      let s :=nV b i
      bCb cap (fun k=>(kK (auN s.free) ref k :ℚ)/(s.dI+1 :ℕ)))
    (fun k=>kK r c k)
def originFreeCap (b:fO) (o:ℕ) :GM :=
  fun k=>(if isLast b o then (∑ q,originBudget b o q:ℕ) else 1) *
    freeCap b o (afterFree b) k
def SS (b:fO) (j:ℕ) (i:Fin 3) :GM:= fun k=>weight (aHp b j) i k
def projectionCap (b:fO) :ℚ :=
 TD.XM (stopCount b-1) (fun j=>SS b (j+1) 0) (fun j=>globalCap b (j+1))
def pointFee (b:fO) :ℕ :=
 let fF:=((stages b).drop 1).map a3D ++ [(terminal b).shape]
 let a :=(fF.map Shape.U).foldl max 0
 let t:=(fF.map (fun s=>s.B-s.J)).foldl max 0
 let j:=(fF.map Shape.J).foldl max 0
 a*BC b 2+(t+j)*BC b 3
def au1 (b:fO) (B J:ℕ) :ℕ :=
 let d:=wX b
 let q:=weakAgreement-d
 let a :=1+(2*d-3)*(B-1)
 let v :=min a ((2*d-3)*(J-1)+d)
 let t:=((262144-weakAgreement)*((B-J)*v+J*a)+(q-1))/q+B^2
 let lam:ℚ:=(262144 :ℚ)/weakAgreement
 let mu:ℚ:=((262144-d:ℕ) :ℚ)/q
 let a' := mu+2*lam*d*(B-1 :ℕ)
 let v' := min a' (lam*d*(2*J-1 :ℕ))
 min t ((((B-J:ℕ) :ℚ)*v'+J*a').ceil.toNat+B^2)
def allShapes (b:fO) :List Shape :=
  let ss :=stages b
  (ss.flatMap fun s=>[s.free,s.moving]) ++ [(terminal b).shape] ++
    (((introduction b).filter fun a =>
      !(ss.any fun s=>s.dI == a.dI && s.free.m == a.shape.m &&
        s.free.B == a.shape.B && s.free.J == a.shape.J && s.free.U == a.shape.U)).map Aux.shape)
def bankFee (b:fO) :ℕ :=
 ((allShapes b).map fun s=>(p+1)*s.U+au1 b s.B s.J).sum
def akj:ℕ :=
 let guard :=23*(64*weakAgreement-1+114*2707)
 p*p*(23*87)/(p-guard)
def eHB (b:fO) :ℕ:= match b.val with
 | 0=>0xc36e11764ea
 | 1 | 2=>0xb6afc1101f5
 | 3 | 4 | 5 | 6=>0xb55a7110338
 | 7=>0xa55ab10fedc
 | 8=>0xb2afd11013e
 | 9=>0xaeafe1100ab
 | 10 | 12 | 13=>0xaaaff110390
 | _=>0xa805510ff0e
def earlyFee (b:fO) :ℕ :=
  (p+1)*BC b 2+BC b 3+BC b 0 +
    bankFee b+eHB b+1+akj
def lineFee (b:fO) (r :bTu) :ℕ :=
 let d:=wX b
 let a :=1+(2*d-3)*(r 0-1)
 let v :=min a ((2*d-3)*(r 1-1)+d)
 let t:=(2*d-3)*r 2
 let s :=r 2*(2*a*v-v*v)+2*t*(r 0*v+r 1*(a-v))
 let q:=r 2*(2*a+v)+t*(2*r 0+r 1)+r 0*v+r 1*a+r 2+r 0+r 1
 (2*((262144-weakAgreement:ℕ) :ℚ)/(weakAgreement-d:ℕ)*(s+q:ℕ)).ceil.toNat+r 0+r 2+1
def rankPrice (b:fO) (o:ℕ) :GM :=
  let r :=bCb (freeCap b o 0) (globalCap b 0)
  let d:=wX b
  let lam:ℚ:=(262144 :ℚ)/weakAgreement
  let mu:ℚ:=((262144-d:ℕ) :ℚ)/(weakAgreement-d:ℕ)
  let B:=r 2
  let J:=r 1
  match P5_7_2.rankBlend b with
  | none => ![0,2*lam*d*B+mu,2*lam*d*J+B,0]
  | some t =>
    let j:=min B J
    let phi:=if B=0 then 0 else 4*j-2*j*j/B
    ![0,4*lam*d*B*t+mu,lam*d*phi*(1-t)+B+1,0]
def MovingFit (s :Ls) (x :GM) :Prop :=
  let m:=s.dI+1
  let f :=s.free
  let g:=s.moving
  (∀ k,x k≤(kK (auN f) g k :ℚ)/(m^2 :ℕ)) ∨
    ∃ n e v :ℕ,0<n∧n≤ m∧0<e ∧
      n*e≤ min f.B g.B∧n*v≤ min f.U g.U ∧
      (∀ k,x k≤graphMass e v k) ∧
      (n< m → ∀ k,
        let r := fun t:Shape=>⟨0,t.B-n*e,min t.J (t.B-n*e),t.U-n*v⟩
        x k≤(kK (auN (r f)) (r g) k :ℚ)/((m-n)^2 :ℕ))
def Individual (b:fO) (o j:ℕ) (x :GM) :Prop :=
 0<x 0∧(∀ k,0≤x k∧x k≤ min (globalCap b j k) (freeCap b o j k)) ∧
 ∀ i∈(movingOrder b).take (j-afterFree b),MovingFit (nV b i) x
def scalarWitness (b:fO) (g:ℕ) (dualWord:Bool) (v :ℚ) :Prop :=
  ∃ extra c:ℕ,0<c ∧
    let D:=wX b
    let l:=if dualWord then 262144+D-2*weakAgreement else D
    let e :=g+extra
    let r :=(extra+1)*c
    let j:=r/(c+1)
    let ranks :=l*(e*(e+1)+j*(j+1))/2
    let w:=max (g*l) (max ((c+1)*ranks/r-j*l) ((e-j)*l))
    let height:=w+1+j*l
    let guard :=if dualWord then (2*g-2)*w-g*(g-1)*l else (2*g-1)*w-g*g*l
    let poles :=if dualWord then (6*g-4)*w-(3*g*g-4*g+2)*l else (6*g-2)*w-3*g*g*l
    e*l<height∧(c+1)*ranks< r*height∧guard<p ∧
    7+6*(g:ℚ)+((2*g+1)*262144+poles :ℕ)/(weakAgreement-D:ℕ)≤v ∧
    ((g*(c+1)+e :ℕ) :ℚ)≤v
def aSz (b:fO) (dm a h:ℚ) :Prop :=
  let q:ℚ:=(p+1 :ℕ)
  0≤dm∧dm≤a∧q/55≤a∧0≤h ∧
  ∀ g:ℕ,0<g→ g≤54→a<q/g →
    let direct :=q/g
    let D:=wX b
    let gap:=weakAgreement-D
    let alpha :ℚ:=1+2*(262144/(weakAgreement:ℚ))*D
    let mu:ℚ:=((262144-D:ℕ) :ℚ)/gap
    (1-a/direct)*(2*alpha*g+mu-alpha)≤h ∨
      (g=1∧(1-a/direct)*(1+3*262144/(gap:ℚ))≤h) ∨
      (g=2∧(13+8*262144/(gap:ℚ))*(direct-a)/(direct-16)≤h) ∨
      (3≤g ∧ ∃ (dualWord:Bool) (v :ℚ),
        let a0:=dm/(3*(g:ℚ))+4*g+8+(if dualWord then 1 else 0)
        a0≤a∧scalarWitness b g dualWord v∧v*(direct-a)/(direct-a0)≤h)
def stopPrice (b:fO) (a h:ℕ→ℕ→ℚ) (o j:ℕ) :GM :=
 if j=0 then rankPrice b o else fun k=>a o j*SS b j 0 k+h o j*SS b j 1 k
def fibreShape (b:fO) (o:ℕ) (rescue :Bool) :Shape :=
 if rescue then aur (originBudget b o) else originCutter b o
structure TopPair {u del} (M:jG u del) {Γ} (F:P1.bje A M Γ) (b:fO) where
 raw:Fin 2→Bool→jA.jK
 nonzero : ∀ i e,raw i e≠0
 conjugate : ∀ e,raw 1 e=MvPolynomial.map (Polynomial.mapRingHom (frobenius L p)) (raw 0 e)
 caps : ∀ i e,
   let t:=if e then (topDonors b).2 else (topDonors b).1
   jA.vC (raw i e)≤t.shape.B∧jA.lP (raw i e)≤t.shape.J ∧
     (raw i e).degreeOf (some 2)≤t.YM∧jA.gY (raw i e)≤t.shape.U ∧
     jA.ahb (row b).declaredHi
       (t.shape.m*weakAgreement-1+(t.shape.B+t.shape.J)*(row b).declaredHi) (raw i e)
 zero : ∀ i e γ,γ∈Γ →
   MvPolynomial.eval (jA.ED (cu.jz (M.label γ)^(p^i.val))
     (jA.jW (j9 (F.scalar γ)))) (jA.bC (raw i e))=0
 no_moving_top : ∀ i (f :jA.ko),Irreducible f→0<f.degreeOf (some 2) →
   f∣jA.bC (raw i false)→f∣jA.bC (raw i true) →
   jA.gY f=0
def FixedTariff {u del} {M:jG u del} {Γ} (F:P1.bje A M Γ) (b:fO) :Prop :=
  ∀ B J,aBh B J → ∀ G:tK,abM G B J → ∀ T⊆Γ,
    (∀ γ∈T,FW G (F.scalar γ)=0)→T.card≤au1 b B J
structure FixedPartPair {b u del M Γ F} (x : @Input b u del M Γ F)
  (s :Ls) (hs :s∈stages b) where
 free :NO (x.donors.staged s hs).free.jet s.free
 moving:NO (x.donors.staged s hs).moving.jet s.moving
structure aAT {u del} {M:jG u del} {Γ}
   (F:P1.bje A M Γ) (b:fO) (x :Input b M F) where
 factors :ℕ→Finset Jet
 parents :ℕ→Jet→Finset (Ideal Ambient)
 cut:ℕ→Jet→Jet
 rescue :ℕ→Jet→Bool
 line :ℕ→Jet→Finset K
 zo:Finset K
 fixed : ∀ s (hs :s∈stages b),(FixedPartPair x s hs)
 firstFactor : ∀ o∈origins b,∀ f∈factors o,
   Irreducible f∧gT.alm f ∧
     ∃ hs :nV b 0∈stages b,f∣(x.donors.staged _ hs).free.jet
 tail : ∀ i∈origins b,∀ k,
   ∑ o∈(origins b).filter (i ≤ ·),∑ f∈factors o,akZ.yE f k≤originBudget b i k
 rescue_last : ∀ o∈origins b,∀ f∈factors o,rescue o f=true →
   isLast b o ∧ ∀ k,0<akZ.yE f k
 line_price : ∀ o∈origins b,∀ f∈factors o,
   (line o f).card≤ if rescue o f then lineFee b (akZ.yE f) else 0
 proper : ∀ o∈origins b,∀ f∈factors o,
   oU (cut o f) (fibreShape b o (rescue o f)) ∧ ¬ f∣cut o f
 nonlast_common : ∀ o∈origins b,¬ isLast b o → ∀ f∈factors o,∀ g∈factors o,cut o f=cut o g
 DN : ∀ o∈origins b,∀ f∈factors o,∀ I∈parents o f,
   xN I∧I.height=2∧iJ f∈I∧iJ (cut o f)∈I ∧
     ∀ s (hs :s∈stages b),¬ pI.aaS (fixed s hs).free.equation I ∧
       ¬ pI.aaS (fixed s hs).moving.equation I
 parent_unique : ∀ o∈origins b,∀ f∈factors o,∀ o' ∈ origins b,∀ f' ∈ factors o',
   ∀ I∈parents o f,I∈parents o' f' → o=o' ∧ f=f'
 factor_cap : ∀ o∈origins b,∀ f∈factors o,∀ k,
   J2 (parents o f) k≤kK (akZ.yE f) (fibreShape b o (rescue o f)) k
 mass_cap : ∀ k,∑ o∈origins b,∑ f∈factors o,J2 (parents o f) k≤BC b k
 early_price :zo.card≤earlyFee b
 Eh : ∀ γ∈Γ,γ∈zo ∨ ∃ o∈origins b,∃ f∈factors o,
   γ∈line o f ∨ ∃ I∈parents o f,I0 F I γ
def Pass {b u del M Γ F} (x : @Input b u del M Γ F) (j:ℕ) (I:Ideal Ambient) :Prop :=
  if j=0 then dual I else
  if j<afterFree b then agA x.banks (nV b j).free I else
  match (movingOrder b)[j-afterFree b]? with
  | none=>agA x.banks (terminal b).shape I
  | some n =>
    let s :=nV b n
    ∃ hs :s∈stages b,agA x.banks s.free I∧agA x.banks s.moving I ∧
      aFX.aTw (x.donors.staged s hs).free.jet (x.donors.staged s hs).moving.jet I
def partMass (F:ℕ→Finset Jet) (S:ℕ→Jet→ℕ→Finset (Ideal Ambient))
    (o j:ℕ) (k :Fin 4) :ℚ :=
  ∑ f∈F o,J2 (S o f j) k
def lossTail (b:fO) (F:ℕ→Finset Jet) (S:ℕ→Jet→ℕ→Finset (Ideal Ambient))
    (o i:ℕ) (k :Fin 4) :ℚ :=
  ∑ j∈(stops b).filter (i ≤ ·),partMass F S o j k
structure Timeline {b u del M Γ F} {x : @Input b u del M Γ F} (C:aAT F b x) where
 stopped :ℕ→Jet→ℕ→Finset (Ideal Ambient)
 Bp:ℕ→Jet→Finset (Ideal Ambient)
 cuts :ℕ→Jet→ℕ→ Ideal Ambient→acW
 stopped_at : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,∀ I∈stopped o f j,
   I∈C.parents o f ∧ ¬ Pass x j I ∧ ∀ i<j,Pass x i I
 kept_at : ∀ o∈origins b,∀ f∈C.factors o,∀ I∈Bp o f,
   I∈C.parents o f∧dual I∧agA x.banks (terminal b).shape I
 exhaust : ∀ o∈origins b,∀ f∈C.factors o,∀ I∈C.parents o f,
   I∈Bp o f ∨ ∃ j∈stops b,I∈stopped o f j
 aNI : ∀ o∈origins b,∀ f∈C.factors o,∀ k,
   ∑ j∈stops b,J2 (stopped o f j) k ≤
     kK (akZ.yE f) (fibreShape b o (C.rescue o f)) k
 global_bound : ∀ i∈stops b,∀ k,
   ∑ o∈origins b,lossTail b C.factors stopped o i k≤globalCap b i k
 free_bound : ∀ o∈origins b,∀ k,
   lossTail b C.factors stopped o (afterFree b) k≤originFreeCap b o k
 individual : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,∀ I∈stopped o f j,
   Individual b o j (fun k=>pN I k)
 cut_cost : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,0<j →
   ∀ I∈stopped o f j,∀ i,
     ((cuts o f j I).cost i:ℚ)≤FP (SS b j i) fun k=>pN I k
 cut_cover : ∀ o∈origins b,∀ f∈C.factors o,∀ j∈stops b,0<j →
   ∀ I∈stopped o f j,∀ γ∈Γ,I0 F I γ →
     γ∈(cuts o f j I).direct ∨ ∃ Q∈(cuts o f j I).qv,I0 F Q γ
 total_projection :
   (∑ o∈origins b,∑ f∈C.factors o,∑ j∈(stops b).filter (0 < ·),
     ∑ I∈stopped o f j,((cuts o f j I).cost 0:ℚ))≤projectionCap b
 total_points :
   (∑ o∈origins b,∑ f∈C.factors o,∑ j∈(stops b).filter (0 < ·),
     ∑ I∈stopped o f j,(cuts o f j I).direct.card)≤pointFee b
def dotResources (v :Fin 3→ℚ) (r :bTu) :ℚ := ∑ k,v k*r k
def factorUnit (w:GM) (s :Shape) (q:Fin 3) :ℚ := ∑ k,w k * arC s k q
def factorRunning (b:fO) (w:ℕ→GM) :ℕ→Fin 3→ℚ
 | 0,_=>0
 | i+1,q=>max (factorRunning b w i q) (factorUnit (w i) (originCutter b i) q)
def factorBill (b:fO) (w:ℕ→GM) :ℚ :=
  ∑ i∈origins b,
    dotResources (fun q=>factorRunning b w (i+1) q-factorRunning b w i q) (originBudget b i)
def sumPrefix (g:ℕ→GM) (j:ℕ) (k :Fin 4) :ℚ :=
 ∑ i∈range (j+1),g i k
structure cL (b:fO) where
 dm:ℕ→ℕ→ℚ
 a :ℕ→ℕ→ℚ
 h:ℕ→ℕ→ℚ
 global:ℕ→GM
 free :ℕ→GM
 residual:ℕ→GM
 projection_small:projectionCap b<p
 bgt : ∀ o∈origins b,∀ j∈stops b,0<j→aSz b (dm o j) (a o j) (h o j)
 individual_bound : ∀ o∈origins b,∀ j∈stops b,0<j →
   ∀ m:GM,Individual b o j m →
     min (projectionCap b) (FP (SS b j 0) m)≤dm o j
 global_nonneg : ∀ i k,0≤global i k
 free_nonneg : ∀ o k,0≤free o k
 fWE : ∀ o k,0≤ residual o k
 dominate : ∀ o∈origins b,∀ j∈stops b,∀ k,
   stopPrice b a h o j k≤ sumPrefix global j k +
     (if afterFree b≤j then free o k else 0)+residual o k
 absorb : ∀ o∈origins b,isLast b o → ∀ r :bTu,(∀ q,0< r q∧r q≤originBudget b o q) →
   r 1≤ r 0 →
   (lineFee b r :ℚ)≤dotResources
     (fun q=>factorUnit (residual o) (originCutter b o) q -
       factorUnit (residual o) (aur (originBudget b o)) q) r
 budget: ((earlyFee b+pointFee b+(projectionCap b).ceil.toNat :ℕ) :ℚ) +
     (∑ i∈stops b,FP (global i) (globalCap b i)) +
     (∑ o∈origins b,FP (free o) (originFreeCap b o)) +
     factorBill b residual≤((row b).prefixFee :ℚ)
end
end q7F2qKe
