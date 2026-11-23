import ProximityPrize.SubmissionLower.Zr07w3a
import ProximityPrize.SubmissionLower.ZaLaX1b
import ProximityPrize.SubmissionLower.ZTFKldb
import ProximityPrize.SubmissionLower.ZNBvygc
import ProximityPrize.SubmissionLower.Z1sUWDe
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZrIiE0d
import ProximityPrize.SubmissionLower.ZdZNCPb
import ProximityPrize.SubmissionLower.ZeFfOZc
import ProximityPrize.SubmissionLower.ZpWezjb
import ProximityPrize.SubmissionLower.Z6jV1pb
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.ZltF3Sb
import ProximityPrize.SubmissionLower.ZYOgAFe
import ProximityPrize.SubmissionLower.ZwEplQa
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.Z77J3Nc
import ProximityPrize.SubmissionLower.ZYfUQxc
import ProximityPrize.SubmissionLower.ZzCHpGc
set_option Elab.async false
section
section
set_option autoImplicit true
namespace P5_7_4
noncomputable section
open Polynomial
open cu (Shape ku triangle)
open DP (pW)
open Ge (kq Gm EM adk residue forward)
open P5_7 (farAgreement)
def poleRank (s :Shape) :ℕ :=
  ku s fun q j =>
    let u:=s.U-(q-j)
    (s.B+s.J-q-min q s.J+2*j)*((u+1)*(s.B-q)+triangle u)
def LocalPole :Prop :=
  ∀ (F:Type) [Field F] [CharP F K1.p] (s :Shape),
    s.J≤ s.B→s.B≤ s.U→s.B<K1.p →
    ∀ (α:F) (side :Fin 2) (a b c:F),b≠0 →
    ∃ tests :Gm F →ₗ[F] (Fin (poleRank s)→F),
      ∀ P,adk s P→tests P=0 →
        (pW ((Polynomial.X - C (algebraMap F (kq F) α))^(s.B+s.J)) :
          EM (kq F))∣forward (Polynomial.X - C α) (C (residue side a b c)) P
def PoleDebit (t:P5_7.Bank) :Prop :=
 poleRank t.shape≤triangle t.shape.U*agU.arY t.shape+t.arY
def Mq (h r :ℕ) (s :Shape) :ℕ :=
 s.m*farAgreement - 2*h*r
def amv (h r :ℕ) (s :Shape) (q j:ℕ) :ℕ :=
 Mq h r s+j - q*(131071-h)
def aL4 (h r :ℕ) (s :Shape) :Prop :=
 s.B*(131071-h)<Mq h r s
def O3 (h r :ℕ) (s :Shape) (mode :ℕ) :ℕ :=
 triangle s.U*ku s (fun q j=>amv h r s q j - mode*(2*h*j))
end
end P5_7_4
end
section
set_option autoImplicit true
namespace qHEUR1a
noncomputable section
open Polynomial
open P5 (K)
open P5_7_1 (Input degree)
open cu (Equation yq)
open Qt (gY)
abbrev Raw:=Y3.Dg
abbrev embed:=Y3.embed
abbrev height (F:Raw) :=gY (embed F)
abbrev quota :ℕ:=179740
abbrev threshold :ℕ:=9400000
abbrev modulus :ℕ:=threshold+1+degree
abbrev rate :ℕ:=0x147d357000
def weight (F:Raw) :ℕ :=
  F.support.sup fun i=>(F.coeff i).support.sup fun a =>
    ((F.coeff i).coeff a).natDegree+i*degree
def Zk (x :Input) (f :Equation) (γ:K) :Prop :=
 yq f (x.M.label γ) (x.F.scalar γ)=0
def polar (e :ℕ) :ℕ:=(6*e-2)*threshold-3*e^2*degree
end
end qHEUR1a
end
section
set_option autoImplicit true
namespace qSxbgdc
noncomputable section
open aR (ao)
open Rj
open P5_7_2 (TopRow)
open qPQ4nYa (cappedCumulative)
open MvPolynomial
def T8:TopRow :=⟨⟨128,174,52,3267⟩,22,4005848,0x196ce109⟩
def FF (b:TopRow) (e :Exp) :Prop :=
 e.weight BU≤b.shape.B∧e.weight indexWeight≤b.shape.J∧e (some 2)≤b.YM
def apR (b:TopRow) :Submodule ao Flat :=restrictSupport ao {e | FF b e}
def origin (b:TopRow) :Flat →ₗ[ao] Flat :=
 (weightedTruncation oH b.shape.m).comp J6.toLinearMap
def originRange (b:TopRow) :Submodule ao Flat :=
 LinearMap.range ((origin b).domRestrict (apR b))
def offset (b:TopRow) (k :ℕ) :ℤ:=(k :ℤ) - b.shape.J
def TO (b:TopRow) (q k :ℕ) :Set Exp :=
  {e | FF b e∧e.weight BU=q ∧
    (e none :ℤ)-(e.weight indexWeight:ℤ)=offset b k}
def Block (b:TopRow) (q k :ℕ) :Submodule ao Flat :=
 restrictSupport ao (TO b q k)
def af3 (b:TopRow) (q k :ℕ) :Block b q k →ₗ[ao] Flat :=
 (origin b).domRestrict (Block b q k)
def iO (b:TopRow) (q:ℕ) :ℕ:=min q b.shape.J
def Ic (b:TopRow) (q:ℕ) (g:ℤ) :ℤ:=(b.shape.m:ℤ) - q - g
def pT (b:TopRow) (q:ℕ) (g:ℤ) (i:Fin 3) :Flag :=
 let d:ℤ:=iO b q
 ![⟨0,-g⟩,⟨d - b.YM,2*d - b.shape.J⟩,⟨0,Ic b q g⟩] i
def K6 (b:TopRow) (q:ℕ) (p:kJ) :ℤ :=
 iO b q - ∑ j,(p j:ℤ)*yE j
def D8 (b:TopRow) (q:ℕ) (g:ℤ) (p:kJ) (i:Fin 3) :Flag :=
  ⟨(pT b q g i).iy - ∑ j,(p j:ℤ)*(Jd j i).iy,
    (pT b q g i).HE - ∑ j,(p j:ℤ)*(Jd j i).HE⟩
def Bb (b:TopRow) (q:ℕ) (g:ℤ) :ℤ :=
 let d:=iO b q
 cappedCumulative d b.YM b.shape.J - cappedCumulative d b.YM (min b.shape.J (-g - 1))
def xR (b:TopRow) (q:ℕ) (g:ℤ) (p:kJ) :ℕ :=
  if Ic b q g≤0 then 0 else
    (Bb b q g - max 0 (max
      (m5 (iO b q) (pT b q g))
      (m5 (K6 b q p) (D8 b q g p)))).toNat
def rankBudget (b:TopRow) (p:ℕ→ℕ→kJ) :ℕ :=
  ∑ q∈Finset.range (b.shape.B+1),∑ k∈Finset.range (b.shape.m+b.shape.J),
    xR b q (offset b k) (p q k)
end
end qSxbgdc
end
section
set_option autoImplicit true
namespace qB9xHGe
open P5_7_2 (fO introduction)
open q7F2qKe
open scoped BigOperators
private theorem ceil_nat {x :ℚ} {n:ℕ} (h:x≤n) :x.ceil.toNat≤n:= by
 have hz :x.ceil≤(n:ℤ) := by
  rw [Rat.ceil_eq_neg_floor_neg]
  change -⌊-x⌋ ≤ _
  rw [Int.floor_neg,neg_neg]
  exact Int.ceil_le.mpr (by exact_mod_cast h)
 simpa using Int.toNat_le_toNat hz
private theorem line_cap (b:fO) (r :bTu) (hD:wX b≤134000)
    (hb:r 0≤13) (hj:r 1≤2) :
    lineFee b r≤0x2ba7def30000*r 2+60000000:= by
  let d:=wX b
  let k :=2*d-3
  let a :=1+k*(r 0-1)
  let v :=min a (k*(r 1-1)+d)
  let t:=k*r 2
  have hk :k≤270000:= by dsimp [k,d]; omega
  have ha :a≤4000000:= by
    dsimp only [a]
    have :=Nat.mul_le_mul hk (show r 0-1≤12 by omega)
    omega
  have hv :v≤500000:= by
    refine (min_le_right _ _).trans ?_
    have :=Nat.mul_le_mul hk (show r 1-1≤1 by omega)
    change d≤134000 at hD
    omega
  have h₀:2*a*v-v*v≤0x3a352944000:= by
    have hh:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 ha) hv
    omega
  have h₁:r 0*v+r 1*(a-v)≤14500000:= by
    have h1 :=Nat.mul_le_mul hb hv
    have h2 :=Nat.mul_le_mul hj ((Nat.sub_le a v).trans ha)
    omega
  have h₂:r 0*v+r 1*a+r 0+r 1≤14500015:= by
    have h1 :=Nat.mul_le_mul hb hv
    have h2 :=Nat.mul_le_mul hj ha
    omega
  have ht:t≤ r 2*270000:= by
    rw [mul_comm]
    exact Nat.mul_le_mul_right (r 2) hk
  let s :=r 2*(2*a*v-v*v)+2*t*(r 0*v+r 1*(a-v))
  let q:=r 2*(2*a+v)+t*(2*r 0+r 1)+r 0*v+r 1*a+r 2+r 0+r 1
  have hs :s≤ r 2*0xac262f29c00:= by
    calc
      _≤ r 2*0x3a352944000+2*(r 2*270000)*14500000 :=
        Nat.add_le_add (Nat.mul_le_mul_left (r 2) h₀)
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht) h₁)
      _ = _:= by ring
  have hq:=Nat.add_le_add (Nat.mul_le_mul_left (r 2) (show 2*a+v≤8500000 by omega))
    (Nat.mul_le_mul ht (show 2*r 0+r 1≤28 by omega))
  have hq' : r 2*(2*a+v)+t*(2*r 0+r 1)≤ r 2*16060000 :=
    hq.trans_eq (by ring)
  have hp:s+q≤0xac263e7aa61*r 2+14500015:= by
    dsimp only [q]
    omega
  let gap:=weakAgreement-d
  have hgap:45740≤gap:= by dsimp [gap,weakAgreement,d]; omega
  have hgapQ: (45740:ℚ)≤(gap:ℚ) := by exact_mod_cast hgap
  have hl: (2*((262144-weakAgreement:ℕ) :ℚ))/(gap:ℚ)≤4 := by
    apply (div_le_iff₀ (by linarith only [hgapQ])).mpr
    rw [show 2*((262144-weakAgreement:ℕ) :ℚ)=164808 from by with_unfolding_all rfl]
    linarith only [hgapQ]
  have hc: (2*((262144-weakAgreement:ℕ) :ℚ))/(gap:ℚ)*(s+q:ℕ) ≤
      ((4*(s+q) :ℕ) :ℚ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (s+q)))
  change (2*((262144-weakAgreement:ℕ) :ℚ)/(gap:ℚ)*(s+q:ℕ)).ceil.toNat
    +r 0+r 2+1≤_
  have h:=ceil_nat hc
  omega
private theorem line_rows (b:fO) :
  let o:=(introduction b).length
  wX b≤134000∧originBudget b o 0≤13∧originBudget b o 1≤2 ∧
   60000000≤lineCredit b o 0∧0≤lineCredit b o 1 ∧
   0x2ba7def30000≤lineCredit b o 2 := by
 fin_cases b <;> exact ⟨by decide,by decide,by decide,
  of_decide_eq_true (by with_unfolding_all rfl),
  of_decide_eq_true (by with_unfolding_all rfl),
  of_decide_eq_true (by with_unfolding_all rfl)⟩
theorem line_paid (b:fO) (o:ℕ) (_:o∈origins b) (ho:isLast b o)
  (r :bTu) (hr : ∀ q,0< r q∧r q≤originBudget b o q) (_:r 1≤ r 0) :
  (lineFee b r :ℚ)≤dotResources (lineCredit b o) r := by
 change o=(introduction b).length at ho
 subst o
 obtain ⟨hD,hb,hj,hc0,hc1,hc2⟩:=line_rows b
 have hp:=line_cap b r hD ((hr 0).2.trans hb) ((hr 1).2.trans hj)
 have hr0: (1 :ℚ)≤(r 0:ℚ) := by exact_mod_cast (hr 0).1
 have h0:=mul_le_mul hc0 hr0 (by decide : (0:ℚ)≤60000000)
  ((by decide : (0:ℚ)≤60000000).trans hc0)
 have h1 :=mul_nonneg hc1 (Nat.cast_nonneg (α:=ℚ) (r 1))
 have h2 :=mul_le_mul_of_nonneg_right hc2 (Nat.cast_nonneg (α:=ℚ) (r 2))
 simp only [dotResources,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
 have hp' : (lineFee b r :ℚ)≤0x2ba7def30000*(r 2 :ℚ)+60000000:= by exact_mod_cast hp
 change (lineFee b r :ℚ)≤lineCredit b _ 0*(r 0:ℚ) +
  (lineCredit b _ 1*(r 1 :ℚ)+lineCredit b _ 2*(r 2 :ℚ))
 linarith only [hp',h0,h1,h2]
end qB9xHGe
end
section
set_option autoImplicit true
namespace qoK3iCb
open P5 (p)
open P5_7_2 (fO)
open q7F2qKe (wX weakAgreement scalarWitness)
def graphRate (g:ℕ) :ℚ:=((p+1 :ℕ) :ℚ)/g
def scalarSlope (dm:ℚ) (g:ℕ) :ℚ:=dm/(3*(g:ℚ))+4*g+8
private def scalarParams (b:fO) (g extra c:ℕ) :
   ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×ℕ :=
 let D:=wX b
 let e :=g+extra
 let r :=(extra+1)*c
 let j:=r/(c+1)
 let ranks :=D*(e*(e+1)+j*(j+1))/2
 let w:=max (g*D) (max ((c+1)*ranks/r-j*D) ((e-j)*D))
 (D,e,r,j,ranks,w,w+1+j*D)
def scalarPrice (b:fO) (g extra c:ℕ) :ℚ :=
  let (D,e,_,_,_,w,_) :=scalarParams b g extra c
  let poles :=(6*g-2)*w-3*g*g*D
  max (7+6*(g:ℚ)+((2*g+1)*262144+poles :ℕ)/(weakAgreement-D:ℕ))
    (((g*(c+1)+e :ℕ) :ℚ))
def scalarCheck (b:fO) (g extra c:ℕ) :Bool :=
 let (D,e,r,_,ranks,w,height) :=scalarParams b g extra c
 decide (0<c∧e*D <height∧(c+1)*ranks< r*height∧(2*g-1)*w-g*g*D <p)
theorem scalar_of_check {b:fO} {g extra c:ℕ} (hc:scalarCheck b g extra c=true) :
  scalarWitness b g false (scalarPrice b g extra c) := by
 have h:=of_decide_eq_true hc
 exact ⟨extra,c,h.1,h.2.1,h.2.2.1,h.2.2.2,le_max_left _ _,le_max_right _ _⟩
end qoK3iCb
end
section
set_option autoImplicit true
namespace q5oHm3d
open P5_7_2 (fO Ls movingOrder)
open q7F2qKe
open qB9xHGe (ng)
open TD (GM bCb auN)
open cu (Shape)
def project (d:Shape) (x :GM) :ℚ :=
 d.U*x 0+(d.B-d.J:ℕ)*x 1+d.J*x 2
def clip (b:fO) (o j:ℕ) :GM :=
 bCb (globalCap b j) (freeCap b o j)
def proper (f g:Shape) (r :ℕ) :GM :=
 fun k=>(kK (auN f) g k :ℚ)/(r^2 :ℕ)
def graph (e v :ℕ) :GM :=
 fun k=>graphMass e v k
def shrink (s :Shape) (n e v :ℕ) :Shape :=
 ⟨0,s.B-n*e,min s.J (s.B-n*e),s.U-n*v⟩
def jU (s :Ls) (n:ℕ) :ℕ:=min s.free.B s.moving.B/n
def seed (s :Ls) (n:ℕ) :ℕ:=min s.free.U s.moving.U/n
def tent (cap rise base cU v :ℚ) :ℚ :=
 min cap (min (rise*v) (base-cU*v))
def ordinateCap (s :Ls) (n e :ℕ) :ℚ :=
 min (e :ℚ) (proper (shrink s.free n e 0) (shrink s.moving n e 0) (s.dI+1-n) 0)
def PN (s :Ls) (d:Shape) (c:GM) (n e :ℕ) (v :ℚ) :ℚ :=
 let f :=shrink s.free n e 0
 let g:=shrink s.moving n e 0
 let r :=s.dI+1-n
 let q:ℚ:=(r^2 :ℕ)
 let x :=min (c 0) (ordinateCap s n e)
 let y :=tent (c 1) 1 (proper f g r 1) ((n*(f.J+g.J) :ℕ)/q) v
 let z :=tent (c 2) (2*(e :ℚ)) (proper f g r 2) ((n*(f.B+g.B) :ℕ)/q) v
 d.U*x+(d.B-d.J:ℕ)*y+d.J*z
def Peak (f :ℕ→ℚ) (hi t:ℕ) :Prop :=
 t≤hi∧(0<t→f (t-1)≤f t)∧(t<hi→f (t+1)≤f t)
def StageCheck (s :Ls) (d:Shape) (c:GM) (dm:ℚ) :Prop :=
  let m:=s.dI+1
  project d (bCb c (proper s.free s.moving m))≤dm ∧
  project d (bCb c (graph (jU s m) (seed s m)))≤dm ∧
  ∀ n,0<n→n< m → ∀ e,0<e→e≤jU s n →
    0<ordinateCap s n e → ∃ t,Peak (fun v=>PN s d c n e v) (seed s n) t∧PN s d c n e t≤dm
def ProjectionCheck (b:fO) (o j:ℕ) (dm:ℚ) :Prop :=
  project (aHp b j) (clip b o j)≤dm ∨
  ∃ i∈(movingOrder b).take (j-afterFree b),
    StageCheck (nV b i) (aHp b j) (clip b o j) dm
def dqs (b:fO) (o j:ℕ) :Prop :=
  ∃ dm a h:ℚ,ProjectionCheck b o j dm∧aSz b dm a h ∧
    ∀ k,a*SS b j 0 k+h*SS b j 1 k≤ng b o j k
end q5oHm3d
end
end
section
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b8) (x :=test b8 n) 2545 rfl rfl rfl
theorem wQd0:GG b8 107 1:=⟨r! 107,True.intro⟩
theorem wQd1:GG b8 106 1:=⟨r! 106,True.intro⟩
theorem wQd2:GG b8 105 1:=⟨r! 105,True.intro⟩
theorem wQd3:GG b8 104 1:=⟨r! 104,True.intro⟩
theorem wQd4:GG b8 103 1:=⟨r! 103,True.intro⟩
theorem wQd5:GG b8 102 1:=⟨r! 102,True.intro⟩
theorem wQd6:GG b8 101 1:=⟨r! 101,True.intro⟩
theorem wQd7:GG b8 100 1:=⟨r! 100,True.intro⟩
theorem wQd8:GG b8 99 1:=⟨r! 99,True.intro⟩
theorem wQd9:GG b8 98 1:=⟨r! 98,True.intro⟩
theorem wQd10:GG b8 97 1:=⟨r! 97,True.intro⟩
theorem wQd11:GG b8 96 1:=⟨r! 96,True.intro⟩
theorem i:GG b8 96 12 :=⟨wQd0.1,wQd1.1,wQd2.1,wQd3.1,wQd4.1,wQd5.1,wQd6.1,wQd7.1,wQd8.1,wQd9.1,wQd10.1,wQd11.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b8) (x :=test b8 n) 2545 rfl rfl rfl
theorem wQd12:GG b8 114 1:=⟨r! 114,True.intro⟩
theorem wQd13:GG b8 113 1:=⟨r! 113,True.intro⟩
theorem wQd14:GG b8 112 1:=⟨r! 112,True.intro⟩
theorem wQd15:GG b8 111 1:=⟨r! 111,True.intro⟩
theorem wQd16:GG b8 110 1:=⟨r! 110,True.intro⟩
theorem wQd17:GG b8 109 1:=⟨r! 109,True.intro⟩
theorem wQd18:GG b8 108 1:=⟨r! 108,True.intro⟩
theorem j:GG b8 108 7 :=⟨wQd12.1,wQd13.1,wQd14.1,wQd15.1,wQd16.1,wQd17.1,wQd18.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b9) (x :=test b9 n) 2555 rfl rfl rfl
theorem wQd19:GG b9 11 1:=⟨r! 11,True.intro⟩
theorem wQd20:GG b9 10 1:=⟨r! 10,True.intro⟩
theorem wQd21:GG b9 9 1:=⟨r! 9,True.intro⟩
theorem wQd22:GG b9 8 1:=⟨r! 8,True.intro⟩
theorem wQd23:GG b9 7 1:=⟨r! 7,True.intro⟩
theorem wQd24:GG b9 6 1:=⟨r! 6,True.intro⟩
theorem wQd25:GG b9 5 1:=⟨r! 5,True.intro⟩
theorem wQd26:GG b9 4 1:=⟨r! 4,True.intro⟩
theorem wQd27:GG b9 3 1:=⟨r! 3,True.intro⟩
theorem wQd28:GG b9 2 1:=⟨r! 2,True.intro⟩
theorem wQd29:GG b9 1 1:=⟨r! 1,True.intro⟩
theorem wQd30:GG b9 0 1:=⟨r! 0,True.intro⟩
theorem k:GG b9 0 12 :=⟨wQd19.1,wQd20.1,wQd21.1,wQd22.1,wQd23.1,wQd24.1,wQd25.1,wQd26.1,wQd27.1,wQd28.1,wQd29.1,wQd30.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b9) (x :=test b9 n) 2555 rfl rfl rfl
theorem wQd31:GG b9 23 1:=⟨r! 23,True.intro⟩
theorem wQd32:GG b9 22 1:=⟨r! 22,True.intro⟩
theorem wQd33:GG b9 21 1:=⟨r! 21,True.intro⟩
theorem wQd34:GG b9 20 1:=⟨r! 20,True.intro⟩
theorem wQd35:GG b9 19 1:=⟨r! 19,True.intro⟩
theorem wQd36:GG b9 18 1:=⟨r! 18,True.intro⟩
theorem wQd37:GG b9 17 1:=⟨r! 17,True.intro⟩
theorem wQd38:GG b9 16 1:=⟨r! 16,True.intro⟩
theorem wQd39:GG b9 15 1:=⟨r! 15,True.intro⟩
theorem wQd40:GG b9 14 1:=⟨r! 14,True.intro⟩
theorem wQd41:GG b9 13 1:=⟨r! 13,True.intro⟩
theorem wQd42:GG b9 12 1:=⟨r! 12,True.intro⟩
theorem l:GG b9 12 12 :=⟨wQd31.1,wQd32.1,wQd33.1,wQd34.1,wQd35.1,wQd36.1,wQd37.1,wQd38.1,wQd39.1,wQd40.1,wQd41.1,wQd42.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b9) (x :=test b9 n) 2555 rfl rfl rfl
theorem wQd43:GG b9 35 1:=⟨r! 35,True.intro⟩
theorem wQd44:GG b9 34 1:=⟨r! 34,True.intro⟩
theorem wQd45:GG b9 33 1:=⟨r! 33,True.intro⟩
theorem wQd46:GG b9 32 1:=⟨r! 32,True.intro⟩
theorem wQd47:GG b9 31 1:=⟨r! 31,True.intro⟩
theorem wQd48:GG b9 30 1:=⟨r! 30,True.intro⟩
theorem wQd49:GG b9 29 1:=⟨r! 29,True.intro⟩
theorem wQd50:GG b9 28 1:=⟨r! 28,True.intro⟩
theorem wQd51:GG b9 27 1:=⟨r! 27,True.intro⟩
theorem wQd52:GG b9 26 1:=⟨r! 26,True.intro⟩
theorem wQd53:GG b9 25 1:=⟨r! 25,True.intro⟩
theorem wQd54:GG b9 24 1:=⟨r! 24,True.intro⟩
theorem m:GG b9 24 12 :=⟨wQd43.1,wQd44.1,wQd45.1,wQd46.1,wQd47.1,wQd48.1,wQd49.1,wQd50.1,wQd51.1,wQd52.1,wQd53.1,wQd54.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b9) (x :=test b9 n) 2555 rfl rfl rfl
theorem wQd55:GG b9 47 1:=⟨r! 47,True.intro⟩
theorem wQd56:GG b9 46 1:=⟨r! 46,True.intro⟩
theorem wQd57:GG b9 45 1:=⟨r! 45,True.intro⟩
theorem wQd58:GG b9 44 1:=⟨r! 44,True.intro⟩
theorem wQd59:GG b9 43 1:=⟨r! 43,True.intro⟩
theorem wQd60:GG b9 42 1:=⟨r! 42,True.intro⟩
theorem wQd61:GG b9 41 1:=⟨r! 41,True.intro⟩
theorem wQd62:GG b9 40 1:=⟨r! 40,True.intro⟩
theorem wQd63:GG b9 39 1:=⟨r! 39,True.intro⟩
theorem wQd64:GG b9 38 1:=⟨r! 38,True.intro⟩
theorem wQd65:GG b9 37 1:=⟨r! 37,True.intro⟩
theorem wQd66:GG b9 36 1:=⟨r! 36,True.intro⟩
theorem n:GG b9 36 12 :=⟨wQd55.1,wQd56.1,wQd57.1,wQd58.1,wQd59.1,wQd60.1,wQd61.1,wQd62.1,wQd63.1,wQd64.1,wQd65.1,wQd66.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b9) (x :=test b9 n) 2555 rfl rfl rfl
theorem wQd67:GG b9 59 1:=⟨r! 59,True.intro⟩
theorem wQd68:GG b9 58 1:=⟨r! 58,True.intro⟩
theorem wQd69:GG b9 57 1:=⟨r! 57,True.intro⟩
theorem wQd70:GG b9 56 1:=⟨r! 56,True.intro⟩
theorem wQd71:GG b9 55 1:=⟨r! 55,True.intro⟩
theorem wQd72:GG b9 54 1:=⟨r! 54,True.intro⟩
theorem wQd73:GG b9 53 1:=⟨r! 53,True.intro⟩
theorem wQd74:GG b9 52 1:=⟨r! 52,True.intro⟩
theorem wQd75:GG b9 51 1:=⟨r! 51,True.intro⟩
theorem wQd76:GG b9 50 1:=⟨r! 50,True.intro⟩
theorem wQd77:GG b9 49 1:=⟨r! 49,True.intro⟩
theorem wQd78:GG b9 48 1:=⟨r! 48,True.intro⟩
theorem o:GG b9 48 12 :=⟨wQd67.1,wQd68.1,wQd69.1,wQd70.1,wQd71.1,wQd72.1,wQd73.1,wQd74.1,wQd75.1,wQd76.1,wQd77.1,wQd78.1,True.intro⟩
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
namespace qgVOTOa
open qMHqmcc (GG receipt test)
local notation "r!" n:arg=>receipt (b:=b9) (x :=test b9 n) 2555 rfl rfl rfl
theorem wQd79:GG b9 62 1:=⟨r! 62,True.intro⟩
theorem wQd80:GG b9 61 1:=⟨r! 61,True.intro⟩
theorem wQd81:GG b9 60 1:=⟨r! 60,True.intro⟩
theorem p:GG b9 60 3 :=⟨wQd79.1,wQd80.1,wQd81.1,True.intro⟩
end qgVOTOa
end
end
section
section
set_option autoImplicit true
namespace q3UL7Tb
open qMHqmcc (GG appendGrades receipts)
private theorem g4 :GG b4 0 115 :=
 appendGrades (appendGrades (appendGrades (appendGrades (appendGrades b4a b4b) b4c) b4d) b4e) b4f
private theorem g5:GG b5 0 121 :=
 appendGrades (appendGrades (appendGrades (appendGrades (appendGrades b5g b5h) b5i) b5j) b5k) b5l
theorem proof :qMHqmcc.c3:= by
 intro b hlo hhi x
 have hv :b.val = 4∨b.val=5:= by omega
 rcases hv with hv | hv
 · have hb:b=b4 :=Fin.ext hv
   subst b
   exact receipts b4 g4 x
 · have hb:b=b5:=Fin.ext hv
   subst b
   exact receipts b5 g5 x
end q3UL7Tb
end
section
set_option autoImplicit true
namespace qgVOTOa
open qMHqmcc (GG appendGrades receipts)
private theorem all8:GG b8 0 115:= by
 have h12 :=a
 have h24 :GG b8 0 24 :=appendGrades h12 b
 have h36:GG b8 0 36:=appendGrades h24 c
 have h48:GG b8 0 48:=appendGrades h36 d
 have h60:GG b8 0 60:=appendGrades h48 e
 have h72 :GG b8 0 72 :=appendGrades h60 f
 have h84 :GG b8 0 84 :=appendGrades h72 g
 have h96:GG b8 0 96:=appendGrades h84 h
 have h108:GG b8 0 108:=appendGrades h96 i
 exact appendGrades h108 j
private theorem all9:GG b9 0 63:= by
 have h12 :=k
 have h24 :GG b9 0 24 :=appendGrades h12 l
 have h36:GG b9 0 36:=appendGrades h24 m
 have h48:GG b9 0 48:=appendGrades h36 n
 have h60:GG b9 0 60:=appendGrades h48 o
 exact appendGrades h60 p
theorem proof :qMHqmcc.c5:= by
 intro b hlo hhi x
 have h:b.val=8∨b.val=9:= by omega
 rcases h with h | h
 · have hb:b=b8:=Fin.ext h
   subst b
   exact receipts b8 all8 x
 · have hb:b=b9:=Fin.ext h
   subst b
   exact receipts b9 all9 x
end qgVOTOa
end
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qJrKOKe
open qMHqmcc (GG receipt appendGrades)
local notation "az" => (receipt 2565 rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl))
private theorem r1 :GG b10 12 4 :=⟨az,az,az,az,True.intro⟩
private theorem r2 :GG b10 16 4 :=⟨az,az,az,az,True.intro⟩
private theorem r3:GG b10 20 4 :=⟨az,az,az,az,True.intro⟩
private theorem r4 :GG b10 24 4 :=⟨az,az,az,az,True.intro⟩
private theorem r5:GG b10 28 4 :=⟨az,az,az,az,True.intro⟩
theorem b:GG b10 12 20 :=
 appendGrades (appendGrades (appendGrades (appendGrades r1 r2) r3) r4) r5
end qJrKOKe
end
section
set_option autoImplicit true
namespace qJrKOKe
open qMHqmcc (GG appendGrades receipts)
theorem proof :qMHqmcc.c6:= by
 intro kA hlo hhi x
 have hb:kA.val=10∨kA.val=11 := by omega
 rcases hb with hb | hb
 · have he :kA=b10 :=Fin.ext hb
   subst kA
   have hg:GG b10 0 73:=appendGrades (appendGrades (appendGrades a b) c) d
   exact receipts b10 hg x
 · have he :kA=b11 :=Fin.ext hb
   subst kA
   have hg:GG b11 0 78:=appendGrades (appendGrades (appendGrades e f) g) h
   exact receipts b11 hg x
end qJrKOKe
end
end
section
set_option autoImplicit true
namespace q1vkLGd
noncomputable section
open P5 (K)
open cu (L)
open qQ9yWTb (Curve Usable)
open scoped Polynomial
abbrev nC := L[X][X]
def u7 : nC →+* Curve :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)
def translate (f : nC) (x y : L) : nC :=
  Polynomial.taylor (Polynomial.C y) (f.map (Polynomial.taylorEquiv x).toRingHom)
def Transverse (f : nC) (x y : L) : Prop :=
  let g := translate f x y
  ∃ r : ℕ, 0 < r ∧ (g.map (Polynomial.evalRingHom 0)).natTrailingDegree = r ∧
    ∀ i j : ℕ, i+j < r → (g.coeff j).coeff i = 0
def discr (f : nC) : L[X] :=
  f.resultant f.derivative f.natDegree (f.natDegree-1)
structure Projection (T : Finset K) (s : K → Fin 2 → L) (q : Curve) where
  point : K → Fin 2 → L
  separates : Set.InjOn (fun γ => point γ 0) (T : Set K)
  equation : nC
  monic : equation.Monic
  nonzero : discr equation ≠ 0
  degree : (discr equation).natDegree ≤ q.totalDegree*(q.totalDegree-1)
  ct4 : ∀ γ ∈ T, Transverse equation (point γ 0) (point γ 1)
  pullback : ∀ γ ∈ T, Usable (u7 equation) (point γ) → Usable q (s γ)
end
end q1vkLGd
end
section
set_option autoImplicit true
section
set_option maxHeartbeats 650000
namespace qQ9yWTb

end qQ9yWTb
end
section
set_option maxRecDepth 2048
set_option maxHeartbeats 1400000
namespace qQ9yWTb


private def af (e u:ℕ) (w:Witness) :Prop :=
 u≤3704∧(e≤2∨(Good e u w∧gu e u w))
private instance rowDecidable (e u:ℕ) (w:Witness) :Decidable (af e u w) := by
 unfold af Good gu
 infer_instance
end qQ9yWTb
end
section
set_option maxHeartbeats 800000
namespace qQ9yWTb
noncomputable section
open Polynomial Finset
open P5 (K dw)
open P5_7 (farAgreement)
open P5_7_1 (Input)
open P5_7_7 (UJ mem_sites)
open cu (L)

open scoped Classical
def c5:Prop :=
  ∀ (T:Finset K) (s :K→Fin 2→L),Set.InjOn s (T:Set K) →
    ∀ b:ℚ,0≤b →
    (∀ q:Curve,Irreducible q →
      ((T.filter fun γ=>Usable q (s γ)).card:ℚ)≤b*q.totalDegree) →
    3*(T.card:ℚ)≤10*b^2
private theorem marks (x :Input) (T:Finset K) (hT:T⊆x.Γ) :
   UJ D x.M.word T x.M.label x.F.scalar := by
 refine ⟨fun _ _ _ _ h=>sub_left_inj.mp h,x.F.distinct.mono hT,?_,?_⟩
 · intro γ hγ
   rcases (x.F.mark γ (hT hγ)).aic with h | h
   · simp [h]
   · change ((x.F.scalar γ).natDegree :ℤ)≤131071 + x.M.iF at h
     have hh:=x.kA.2
     change x.M.iF≤(P5_7_1.hi:ℤ) at hh
     change (x.F.scalar γ).natDegree≤131071+P5_7_1.hi
     omega
 · intro γ hγ
   let m:=x.F.mark γ (hT hγ)
   exact (show farAgreement≤dw by decide).trans (m.bad.dw.trans
     (card_le_card fun i hi=>mem_sites.mpr (m.scalar_hits i hi)))
end
end qQ9yWTb
end
end
section
section
set_option autoImplicit true
namespace qBZoH8d
open Finset
open cu (Shape)
def paddedColumns (s :Shape) (t q:ℕ) :ℕ :=
 min q s.J+1-(s.J-t)
def xR (s :Shape) (t u k :ℕ) :ℕ :=
  min (∑ q∈Ico (k-u) (min k s.B+1),paddedColumns s t q)
    (∑ q∈range (min k s.B+1),agU.Xq s.B s.J t q)
def paddedRank (s :Shape) :ℕ :=
  ∑ t∈range (s.B+2*s.J),∑ r∈range (s.U+1),
    ∑ k∈range (s.B+(s.U-r)+1),xR s t (s.U-r) k
end qBZoH8d
end
section
set_option autoImplicit true
namespace qpECY2d
open Dt (Bank Ls)
open agU (ad1 ajD)
open czX (dei a8x)
open jQ (cUo eE)
open aF8 (bi6 CH)
structure aqm where
 B:ℕ
 J:ℕ
 total:ℕ
 exactness :eE B J=total
def aqm.ofEq {B J total:ℕ} (h:eE B J=total) :aqm :=
 ⟨B,J,total,h⟩
instance :Inhabited aqm:=⟨⟨0,0,0,rfl⟩⟩
def bXa (t:Bank) :Bool :=
  decide ((2*t.shape.J≤t.shape.m∧t.shape.m+t.shape.J≤t.shape.B+1) ∧
    262144*a8x (t.shape.m-2*t.shape.J) t.shape.J=6*t.ad1)
def ay (t:Bank) :Prop :=
  ad1 t.shape=t.ad1 ∧
    ajD t.shape.B t.shape.J≤t.poleMoment∧t.shape.B<K1.p
def a1d (ss :List Ls) :Prop := ∀ s∈ss,ay s.free∧ay s.moving
theorem guJ:a1d [] := by
 intro s hs
 simp at hs
theorem guI {s :Ls} {ss :List Ls}
  (hf :ay s.free) (hm:ay s.moving) (rest:a1d ss) :
  a1d (s :: ss) :=
 List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,rest⟩
theorem checked (t:Bank) (c:aqm)
  (hc: (t.shape.B,t.shape.J,t.poleMoment)=(c.B,c.J,c.total))
  (hn:bXa t=true) (hB:t.shape.B<K1.p) :ay t:= by
 simp only [bXa,decide_eq_true_eq] at hn
 have hnode :=(dei t.shape hn.1.1 hn.1.2).trans hn.2
 have hB' : t.shape.B=c.B:=congrArg Prod.fst hc
 have hJ:t.shape.J=c.J:=congrArg (fun x=>x.2.1) hc
 have hp:t.poleMoment=c.total:=congrArg (fun x=>x.2.2) hc
 refine ⟨by omega,(cUo _ _).trans ?_,hB⟩
 rw [hB',hJ,hp,c.exactness]
def decode (w:ℕ) :ℕ→ℕ→List ℕ
 | 0,_=>[]
 | n+1,x=>(x % 2^w) :: decode w n (x >>> w)
def blocks (last :ℕ) :List ℕ→List (ℕ×ℕ)
 | []=>[]
 | [v]=>[(last,v)]
 | v :: w :: rest=>(256,v) :: blocks last (w :: rest)
private def packed (B J start w n x :ℕ) :=
 blocks (min 256 (B+2*J-start-256*(n-1))) (decode w n x)
def checkedMoment (B J total w n x :ℕ)
    (h:bi6 B J J (packed B J J w n x))
    (hl: ((packed B J J w n x).map Prod.fst).sum=B+J)
    (hs : ((packed B J J w n x).map Prod.snd).sum=total) :aqm :=
  .ofEq (CH _ h hl hs)
theorem appendChecked {B J start:ℕ} {xs ys :List (ℕ×ℕ)}
   (hx :bi6 B J start xs)
   (hy :bi6 B J (start+(xs.map Prod.fst).sum) ys) :
   bi6 B J start (xs ++ ys) := by
 induction xs generalizing start with
 | nil=>exact hy
 | cons x xs ih =>
   obtain ⟨len,v⟩:=x
   refine ⟨hx.1,ih hx.2 ?_⟩
   simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using hy
structure Segment (B J:ℕ) where
 start:ℕ
 rows :List (ℕ×ℕ)
 checked :bi6 B J start rows
def segment (B J start w n x :ℕ)
    (h:bi6 B J start (packed B J start w n x)) :Segment B J :=
  ⟨start,packed B J start w n x,h⟩
def contiguous {B J:ℕ} : ℕ→List (Segment B J)→Prop
 | _,[]=>True
 | start,s :: rest=>s.start=start∧contiguous (start+(s.rows.map Prod.fst).sum) rest
private theorem joined {B J:ℕ} (ss :List (Segment B J)) (start:ℕ)
   (h:contiguous start ss) :bi6 B J start (ss.flatMap Segment.rows) := by
 induction ss generalizing start with
 | nil=>trivial
 | cons a as ih =>
   exact appendChecked (h.1 ▸ a.checked) (ih _ h.2)
def join (B J total:ℕ) (ss :List (Segment B J)) (hm:contiguous J ss)
    (hl: ((ss.flatMap Segment.rows).map Prod.fst).sum=B+J)
    (hs : ((ss.flatMap Segment.rows).map Prod.snd).sum=total) :aqm :=
  .ofEq (CH _ (joined ss J hm) hl hs)
set_option quotPrecheck false in
scoped notation "m!" b:arg j:arg t:arg=>(aqm.ofEq
 (show jQ.lT b j j (b+j)=t from rfl))
set_option quotPrecheck false in
scoped notation "kU" => (by
 repeat' apply And.intro
 all_goals first | exact True.intro | rfl)
set_option quotPrecheck false in
scoped notation "p!" b:arg j:arg t:arg w:arg n:arg x:arg =>
 checkedMoment b j t w n x kU rfl rfl
set_option quotPrecheck false in
scoped notation "s!" b:arg j:arg a:arg w:arg n:arg x:arg =>
 segment b j a w n x kU
set_option quotPrecheck false in
scoped notation "j!" b:arg j:arg t:arg xs:arg=>join b j t xs kU rfl rfl
end qpECY2d
end
section
set_option autoImplicit true
namespace qzVScmb
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (p)
open P5_7_2 (fO stages introduction topDonors)
open q7F2qKe (nV originCount originBudget originCutter aur fibreShape BC)
open cu (FX Jet Shape)


open TD (arC aBh)
open akZ (yE)
abbrev last (b:fO) :=(introduction b).length
abbrev Origin (b:fO) :=Fin (originCount b)
def aOm (b:fO) (f :Jet) :Shape :=
 let t:=(topDonors b).2
 let r :=yE f
 ⟨0,t.shape.B+t.YM*(r 0-1),t.shape.J+t.YM*(r 1-1),t.shape.U+t.YM*r 2⟩
abbrev LineRow :=MvPolynomial (Fin 3) FX
def LineCaps (f :Jet) (g:LineRow) :Prop :=
  ∀ e∈g.support,e 1+e 2≤yE f 0 ∧
    e 2≤yE f 1∧e 0≤yE f 2
structure Guards (b:fO) :Prop where
 anchor_mem:nV b 0∈stages b
 anchor_small: (nV b 0).free.U<p
 staged_ode : ∀ s∈stages b,aBh s.free.B s.free.J∧aBh s.moving.B s.moving.J
 fibre_J : ∀ i≤last b,∀ e,(fibreShape b i e).J≤(fibreShape b i e).B
 rescue_weight : ∀ k j,arC (aur (originBudget b (last b))) k j ≤
  arC (originCutter b (last b)) k j
 bq6 : ∀ k,BC b k<p
end
end qzVScmb
end
end
