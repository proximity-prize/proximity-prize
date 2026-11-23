import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def d0_0:=s! 10017 2095 2095 42 8 0xdecf319ad02b2f9252b407f9540fad01605062ab4036fad05ad007425a02b400affdfbad000678ddab40
private def d0_1 :=s! 10017 2095 4143 44 8 0x89eed958c00832aefd8c007b610658c0072911cd8c0068bb3358c005ddf49d8c0051fd6058c004515fa1b97c
private def d0_2 :=s! 10017 2095 6191 44 8 0x9b362558c009ca23bd8c009d085258c009c6868d8c009ac27f58c00981695d8c009464ac58c008facc2d8c00
private def d0_3:=s! 10017 2095 8239 44 8 0x6b2317247167499894030c7d2f9e58c0084bfb4d8c008b49cb58c0090cde1d8c00954bf858c0098c40ed8c00
private def d0_4 :=s! 10017 2095 10287 43 8 0x417b68b2a10a319fa4e5658ad8b7f1f83a6c1d8a6b287bce56b38d3655ff1ef2ebb99b6a409e15812bac43
private def d0_5:=s! 10017 2095 12335 41 8 0xd6a081201cffc70d00404e9206804aeb684340434e27c1a034927fb0d025a08ec068195dbb54340
private def r0:=j! 10017 2095 0xf4625385a36c [d0_0,d0_1,d0_2,d0_3,d0_4,d0_5]
def dataK:Array aqm := #[
  r0
]
end qpECY2d
end
section
section
set_option autoImplicit true
namespace qSxbgdc
noncomputable section
open aR (ao)
open Rj (Flat Exp BU indexWeight oH La)
open P5_7_2 (TopRow)
open MvPolynomial
private theorem high_vanishes (b:TopRow) (e :Exp) (c:ao) (he :b.shape.m≤e none) :
    origin b (monomial e c)=0:= by
  change weightedTruncation oH b.shape.m (bind₁ La (monomial e c))=0
  apply (weightedTruncation_eq_zero_iff _ _ _).mpr
  refine bind₁_mem_restrictWeightedOrder
    (w:= fun v :Option (Fin 3)=>v.elim 1 (fun _=>0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa [La] using
        (X_mem_restrictWeightedOrder (R:=ao) oH
          (none :Option (Fin 3)) (m:=1) (by rfl))
    | some j=>simp
  · apply (monomial_mem_restrictWeightedOrder _ _ _ _).mpr
    exact Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he)
instance gO4 (b:TopRow) (q k :ℕ) :Module.Finite ao (Block b q k) := by
 apply restrictSupport_finite
 refine (Finsupp.finite_of_nat_weight_le (fun _:Option (Fin 3)=>1)
   (by simp) (q+k)).subset ?_
 intro e he
 change FF b e∧e.weight BU=q∧_ at he
 have hidx :=he.1.2.1
 have hg:=he.2.2
 unfold offset at hg
 have ha :e none≤k := by omega
 have hw:e.weight (fun _=>1)=e none+e.weight BU:= by
   simp only [Finsupp.weight_eq_sum,Fintype.sum_option,BU,
     Option.elim_none,Option.elim_some,smul_eq_mul,Nat.mul_one,Nat.mul_zero,zero_add]
 change e.weight (fun _=>1)≤q+k
 rw [hw,he.2.1]
 omega
private def aTg (b:TopRow) (i:ℕ×ℕ) :Submodule ao Flat :=
 LinearMap.range (af3 b i.1 i.2)
private instance (b:TopRow) (i:ℕ×ℕ) :Module.Finite ao (aTg b i) :=
 Module.Finite.range (af3 b i.1 i.2)
private def pairs (b:TopRow) :Finset (ℕ×ℕ) :=
 Finset.range (b.shape.B+1) ×ˢ Finset.range (b.shape.m+b.shape.J)
private theorem cen (b:TopRow) :originRange b≤(pairs b).sup (aTg b) := by
 classical
 intro P hP
 obtain ⟨Q,rfl⟩:=LinearMap.mem_range.mp hP
 change origin b Q.val∈(pairs b).sup (aTg b)
 have expand:=congrArg (origin b) Q.val.as_sum
 rw [map_sum] at expand
 rw [expand]
 refine Submodule.sum_mem _ fun e he => ?_
 by_cases hi:b.shape.m≤e none
 · rw [high_vanishes b e (Q.val.coeff e) hi]
   exact Submodule.zero_mem _
 have hbox :FF b e := Q.property he
 let q:=e.weight BU
 let k :=e none+(b.shape.J-e.weight indexWeight)
 have hmem: (q,k)∈pairs b:= by
   simp only [pairs,Finset.mem_product,Finset.mem_range]
   have hq:=hbox.1
   dsimp [q,k]
   omega
 apply (Finset.le_sup (f :=aTg b) hmem)
 refine LinearMap.mem_range.mpr ⟨⟨monomial e (Q.val.coeff e),?_⟩,rfl⟩
 intro u hu
 have hue :u=e := by
   by_contra hne
   exact (MvPolynomial.mem_support_iff.mp hu) (by simp [coeff_monomial,Ne.symm hne])
 subst u
 refine ⟨hbox,rfl,?_⟩
 have hj:=hbox.2.1
 dsimp [offset,k]
 omega
instance originRangeFinite (b:TopRow) :Module.Finite ao (originRange b) :=
 Module.Finite.of_injective (Submodule.inclusion (cen b))
  (Submodule.inclusion_injective (cen b))
private theorem finrank_sup_le (b:TopRow) (S:Finset (ℕ×ℕ)) :
   Module.finrank ao (S.sup (aTg b) :Submodule ao Flat) ≤
    ∑ i∈S,Module.finrank ao (aTg b i) := by
 classical
 induction S using Finset.induction_on with
 | empty=>simp
 | insert i S hi ih =>
   rw [Finset.sup_insert,Finset.sum_insert hi]
   exact (Submodule.finrank_add_le_finrank_add_finrank (aTg b i) (S.sup (aTg b))).trans
    (Nat.add_le_add_left ih _)
theorem originRange_le_sum (b:TopRow) (p:ℕ→ℕ→Rj.kJ)
   (h : ∀ q<b.shape.B+1,∀ k<b.shape.m+b.shape.J,
     Module.finrank ao (LinearMap.range (af3 b q k))≤xR b q (offset b k) (p q k)) :
   Module.finrank ao (originRange b)≤ rankBudget b p:= by
 have hr :=(Submodule.finrank_mono (cen b)).trans (finrank_sup_le b (pairs b))
 refine hr.trans ?_
 rw [rankBudget,← Finset.sum_product']
 apply Finset.sum_le_sum
 intro i hi
 have hp:=Finset.mem_product.mp hi
 exact h i.1 (Finset.mem_range.mp hp.1) i.2 (Finset.mem_range.mp hp.2)
end
end qSxbgdc
end
section
set_option autoImplicit true
namespace qSDZN5b
open Finset
open Rj (kJ sG yC m5 yE Jd)
open qSxbgdc
open qPQ4nYa (cappedCumulative)
structure Factors where
 z :ℕ
 y :ℕ
 x :ℕ
 xy :ℕ
 xz :ℕ
 conic:ℕ
def Factors.powers (p:Factors) :kJ := ![p.z,p.y,p.x,p.xy,p.xz,p.conic]
private def slot (width start bits k :ℕ) :ℕ :=
 if k<start then 0 else bits >>> (width*(k-start))
private def slopePower (q k :ℕ) :ℕ :=
 let a :=180-(2*q+k)
 if q<52∧max (180-3*q) (max (158-2*q) (128-q))≤k∧2≤a then a else 0
private def atoms (q start bits k :ℕ) :Factors :=
 if q<30 then
  ⟨0,0,slot 3 start bits k % 8,0,slopePower q k,0⟩
 else if q<99 then
  ⟨0,0,slot 3 (128-q) 0x12776 k % 8,0,slopePower q k,slot 5 start bits k % 32⟩
 else if q<119 then
  let w:=slot 8 start bits k
  ⟨0,0,w % 8,0,0,(w >>> 3) % 32⟩
 else
  let w:=slot (if q<137 then 18 else 13) start bits k
  ⟨w % 32,(w >>> 5) % 8,0,(w >>> 8) % 32,0,if q<137 then (w >>> 13) % 32 else 0⟩
private def kernel (d w t:ℤ) (p:Factors) :ℤ :=
 let a :ℤ:=p.z
 let b:ℤ:=p.y
 let c:ℤ:=p.x
 let e :ℤ:=p.xy
 let f :ℤ:=p.xz
 let z :ℤ:=p.conic
 let n:=d-(a+b+c+e+f+2*z)
 if n<0 then 0 else
   sG (n+1)-(yC ⟨-(a+b+z),w-(2*a+b+z)⟩ +
     yC ⟨d-22-(b+c+e+z),2*d-52-(b+c+2*e+2*z)⟩ +
     yC ⟨-(a+c+f+z),t-(a+c+2*f+2*z)⟩)
private def PN (q k :ℕ) (p:Factors) :ℕ :=
 let d:=min q 52
 let w:=52 - (k :ℤ)
 let t:=180-(q:ℤ) - k
 if t≤0 then 0 else
   (cappedCumulative d 22 52 - cappedCumulative d 22 (min 52 (w-1)) -
     max 0 (max (kernel d w t ⟨0,0,0,0,0,0⟩) (kernel d w t p))).toNat
private theorem cell_eq (q k :ℕ) (p:Factors) :
  xR T8 q (offset T8 k) p.powers=PN q k p:= by
 have hw : -offset T8 k=52 - (k :ℤ) := by
  change -((k :ℤ)-52)= _
  omega
 have ht:Ic T8 q (offset T8 k) =
    180-(q:ℤ) - k := by
  change 128-(q:ℤ)-((k :ℤ)-52)= _
  omega
 simp [xR,Bb,K6,
  D8,pT,hw,ht,PN,kernel,Factors.powers,
  iO,m5,Fin.sum_univ_succ,
  yE,Jd]
 simp [T8] <;> ring_nf
private def sumUp (f :ℕ→ℕ) :ℕ→ℕ
 | 0=>0
 | n+1=>sumUp f n+f n
private theorem sumUp_eq (f :ℕ→ℕ) (n:ℕ) :sumUp f n = ∑ k∈range n,f k := by
 induction n with
 | zero=>simp [sumUp]
 | succ n ih=>rw [sumUp,sum_range_succ,ih]
def Sk (q start bits :ℕ) :ℕ :=
 sumUp (fun k=>PN q k (atoms q start bits k)) (180-q)
def gradeSum (q:ℕ) (p:ℕ→kJ) :ℕ :=
 ∑ k∈range 180,xR T8 q (offset T8 k) (p k)
private theorem c85 (q start bits :ℕ) :
   gradeSum q (fun k=>(atoms q start bits k).powers)=Sk q start bits := by
 rw [Sk,sumUp_eq,gradeSum]
 rw [← sum_subset (range_mono (Nat.sub_le 180 q))]
 · exact sum_congr rfl fun k _=>cell_eq q k _
 · intro k _ hk
   rw [cell_eq,PN,ite_eq_left]
   simp only [mem_range,not_lt] at hk
   omega
structure Window (s n r :ℕ) :Prop where
 witness : ∃ p:ℕ→ℕ→kJ,∑ i∈range n,gradeSum (s+i) (p (s+i))=r
theorem row (q start bits r :ℕ) (h:Sk q start bits=r) :Window q 1 r := by
 refine ⟨⟨fun _ k=>(atoms q start bits k).powers,?_⟩⟩
 simpa [c85] using h
theorem join {s n m r t:ℕ} (h:Window s n r) (l:Window (s+n) m t) :
   Window s (n+m) (r+t) := by
 obtain ⟨p,hp⟩:=h.witness
 obtain ⟨v,hv⟩:=l.witness
 refine ⟨⟨fun q=>if q<s+n then p q else v q,?_⟩⟩
 rw [sum_range_add]
 apply congrArg₂ Nat.add
 · rw [← hp]
   refine sum_congr rfl fun i hi => ?_
   simp only [ite_eq_left (Nat.add_lt_add_left (mem_range.mp hi) s)]
 · rw [← hv]
   refine sum_congr rfl fun i _ => ?_
   simp only [← Nat.add_assoc,ite_eq_right (by omega : ¬ s+n+i<s+n)]
end qSDZN5b
end
section
set_option autoImplicit true
namespace qoK3iCb
open P5_7_2 (fO)
private def base (g:ℕ) :ℕ:=(0x82b5b8073d7e31f7bf0279ae5772eb74ed572abe706a16e2846be6869a4c6725364e3d62a21606065e1eb5b9ed595d9571be54da4525a15018e4dd754b95c4915846d464492d425153fd153d8fe3b4e738ce5368ce344b931cb62f8a02d09c2ac87284812606f23869214561ec501c4471a038178311502912821104160dc100b40a >>> (20*(g-3))) &&& 0xfffff
private def packed (b:fO) :ℕ:= match b.val with
 | 0=>0
 | 1=>0x101010101000001000100010001010000010000003f000100000000003f00000000000000000000000000000000000000000000
 | 2=>0x201020202010001010101010001010101010101006a000100000100003f00000001000000000000000000000000000000000000
 | 3=>0x202020202600101010201020001020101000101006a000101000101010000000001000000000100000001000000000000000000
 | 4=>0x303030303610101020202020001020101000101016a000101000101013f00000001000000000100000001000000000000000000
 | 5=>0x404040404610001030302030001020202000102016a000201000101013f00000001000001000100000001000000000000000000
 | 6=>0x406060605630102040404040001040303000103026b0002026d0102013f01010001010001000100000001000000000000000000
 | 7=>0x409080807650001060605060001050404010104036c0003026e0102020001010002010101000100000001000000000000000000
 | 8=>0x50b100f0e6b6401080c0b0a68020908086b0107066f000605700104043f0302000302020200020001000100000100007c000000
 | 9=>0x630b121615716a640810100f6c67090d0c6e010909726b0707720106063f0504000403020300030001000201000101007c000000
 | 10=>0x6b6b11171c78706a6a101514716b090f10726b090c756e070a746e0807700605710504020400030002000201000101007c000001
 | 11=>0x6f6f70171e7c746d6e0f1617736d6e1012746d090e766f070b766f09087106067106050204000400020002017a0101007c000001
 | _=>0xe68d939290ebe2828684828181bdbbb957beb5b451bab2484cb641484640434240410e7e7e7d7d7d067b077b7d04027c7d010101
private def delta (b:fO) (g:ℕ) :ℕ:=(packed b >>> (8*(g-3))) &&& 0xff
def extra (b:fO) (g:ℕ) :ℕ:=(base g &&& 0x3ff)+((delta b g+32) &&& 0x3f)-32
def copies (b:fO) (g:ℕ) :ℕ:=(base g >>> 10)+(delta b g >>> 6)
def uq (b:fO) (g:ℕ) :ℚ:=scalarPrice b g (extra b g) (copies b g)
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
open Finset
open P5_7_2 (fO)
open q7F2qKe
open qB9xHGe (ng StopRates)
open TD (GM bCb FP a3x)
def bEm (v x :GM) :ℚ :=
 v 0*x 0+(v 1*x 1+(v 2*x 2+(v 3*x 3+0)))
private theorem b08 (v x :GM) :bEm v x=FP v x := by
 simp only [FP,Fin.sum_univ_succ,Fin.sum_univ_zero]
 rfl
def boxDegree (b:fO) (o j:ℕ) :ℚ :=
 bEm (SS b j 0) (bCb (globalCap b j) (freeCap b o j))
def seedRate (b:fO) (o j:ℕ) :ℚ:=max (boxDegree b o j) (graphRate 55)
def b5T (b:fO) (o j:ℕ) :ℚ :=
 let w:=SS b j 0
 min ((ng b o j 1 - seedRate b o j*w 1)/w 0)
     (ng b o j 3/w 2)
def rateAt (b:fO) (dm a h:ℚ) (v :ℚ) (g:ℕ) :Bool :=
  let direct :=graphRate g
  let D:=wX b
  let gap:=weakAgreement-D
  let alpha :ℚ:=1+2*(262144/(weakAgreement:ℚ))*D
  let mu:ℚ:=((262144-D:ℕ) :ℚ)/gap
  decide (direct≤a) ||
    decide ((1-a/direct)*(2*alpha*g+mu-alpha)≤h) ||
    if g=1 then decide ((1-a/direct)*(1+3*262144/(gap:ℚ))≤h)
    else if g=2 then decide ((13+8*262144/(gap:ℚ))*(direct-a)/(direct-16)≤h)
    else decide (scalarSlope dm g≤a∧v*(direct-a)/(direct-scalarSlope dm g)≤h)
def ratesCheck (uq:fO→ℕ→ℚ) (b:fO) (o j:ℕ) :Bool :=
 let dm:=boxDegree b o j
 let a :=seedRate b o j
 let h:=b5T b o j
 (List.range 54).all fun g=>rateAt b dm a h (uq b (g+1)) (g+1)
structure atY (b:fO) (o j:ℕ) :Prop where
 dmNonneg:0≤boxDegree b o j
 hNonneg:0≤b5T b o j
 sPos :0<SS b j 0 0
 zPos :0<SS b j 0 2
 paid0:seedRate b o j*SS b j 0 0≤ng b o j 0
 paid2 :seedRate b o j*SS b j 0 2≤ng b o j 2
def rowCheck (b:fO) (o j:ℕ) :Bool :=
  decide (0≤boxDegree b o j∧0≤b5T b o j ∧
    0<SS b j 0 0∧0<SS b j 0 2 ∧
    seedRate b o j*SS b j 0 0≤ng b o j 0 ∧
    seedRate b o j*SS b j 0 2≤ng b o j 2)
theorem row_of_check {b:fO} {o j:ℕ} (h:rowCheck b o j=true) :atY b o j:= by
 have hp:=of_decide_eq_true h
 exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2⟩
theorem rate_of_checks {uq:fO→ℕ→ℚ} {b:fO} {o j:ℕ}
   (hw : ∀ g:ℕ,3≤g→ g≤54→scalarWitness b g false (uq b g))
   (hr :atY b o j) (hc:ratesCheck uq b o j=true) :
   aSz b (boxDegree b o j) (seedRate b o j) (b5T b o j) := by
 refine ⟨hr.dmNonneg,le_max_left _ _,le_max_right _ _,hr.hNonneg,?_⟩
 intro g hg hg54 hd
 obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
 have hi:i∈List.range 54 :=List.mem_range.mpr (by omega)
 have he :=List.all_eq_true.mp hc i hi
 simp only [rateAt,Bool.or_eq_true,decide_eq_true_eq] at he
 rcases he with ((h | h) | h)
 · exact (not_le_of_gt hd h).elim
 · exact Or.inl h
 by_cases h1 :i+1=1
 · rw [ite_eq_left h1,decide_eq_true_eq] at h
   exact Or.inr (Or.inl ⟨h1,h⟩)
 by_cases h2 :i+1=2
 · rw [ite_eq_right h1,ite_eq_left h2,decide_eq_true_eq] at h
   exact Or.inr (Or.inr (Or.inl ⟨h2,h⟩))
 rw [ite_eq_right h1,ite_eq_right h2,decide_eq_true_eq] at h
 have hg3:3≤ i+1 := by omega
 refine Or.inr (Or.inr (Or.inr ⟨hg3,false,uq b (i+1),?_,hw _ hg3 hg54,?_⟩))
 · simpa [scalarSlope] using h.1
 · simpa [scalarSlope,graphRate] using h.2
private theorem paid_of_row {b:fO} {o j:ℕ} (hr :atY b o j) (k :Fin 4) :
    seedRate b o j*SS b j 0 k+b5T b o j*SS b j 1 k ≤
      ng b o j k := by
  fin_cases k
  · change seedRate b o j*SS b j 0 0+b5T b o j*0≤ng b o j 0
    simpa only [mul_zero,add_zero] using hr.paid0
  · change seedRate b o j*SS b j 0 1+b5T b o j*SS b j 0 0≤ng b o j 1
    have h:=(le_div_iff₀ hr.sPos).mp (min_le_left _ _ :
      b5T b o j≤(ng b o j 1 - seedRate b o j*SS b j 0 1) /
        SS b j 0 0)
    change b5T b o j*SS b j 0 0≤_ at h
    linarith only [h]
  · change seedRate b o j*SS b j 0 2+b5T b o j*0≤ng b o j 2
    simpa only [mul_zero,add_zero] using hr.paid2
  · change seedRate b o j*0+b5T b o j*SS b j 0 2≤ng b o j 3
    rw [mul_zero,zero_add]
    exact (le_div_iff₀ hr.zPos).mp (min_le_right _ _)
theorem stop_of_rate {b:fO} {o j:ℕ} (hr :atY b o j)
  (h:aSz b (boxDegree b o j) (seedRate b o j) (b5T b o j)) :
  Nonempty (StopRates b o j) := by
 refine ⟨⟨_,_,_,h,?_,paid_of_row hr⟩⟩
 intro x hx
 apply (min_le_right _ _).trans
 rw [boxDegree,b08]
 exact a3x (fun _=>Nat.cast_nonneg _) (fun k=>(hx.2.1 k).2)
end qoK3iCb
end
end
