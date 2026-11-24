import ProximityPrize.SubmissionLower.E
import ProximityPrize.SubmissionLower.ZENrqsd
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.D3
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.ZZ0RELd
import ProximityPrize.SubmissionLower.P6Split
import ProximityPrize.SubmissionLower.CQ
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
namespace P1_6_4_1



open scoped BigOperators
abbrev avF:ℕ:=9590457918040
end P1_6_4_1
end
section
open _root_ renaming Finset.sum_congr→cy,Nat.cast_sum→lJ,P5_8.bo8→lI
section
set_option autoImplicit true
namespace P5_8
noncomputable section
open i4 PolynomialDifferential Finset
open scoped Polynomial
def c1 :Prop :=
 aWw small 84≤232369∧Moments small 12850 610160 205216
def c2 :Prop :=
  aWw bo8 6252≤0x62703852f02 ∧
    Moments bo8 0x12e20e912 0x1098bf757c00 0x5e143ee4d6c
end
end P5_8
end
section
set_option autoImplicit true
namespace P5_8_2
open i4 Finset
def bbW (c:ℕ) :=range (1959 - 2*c+1)
def len (b c:ℕ) :=6251-(b+c)+1
theorem cast_len {b c:ℕ} (hc:c∈range 980) (hb:b∈bbW c) :
  (len b c:ℤ)=6252 - b - c:= by
 have hc' := mem_range.mp hc
 have hb' := mem_range.mp hb
 change b<1959 - 2*c+1 at hb'
 unfold len
 omega
private def boxSum (f :ℤ→ℤ→ℤ) :ℤ :=
 ∑ c∈range 980,∑ b∈bbW c,f b c
private theorem card_box : (P5_8.bo8.E.card:ℤ)=boxSum (fun b c=>6252-b-c) := by
 simp only [lI,aH1,card_sigma,card_range,lJ,boxSum]
 exact cy rfl fun c hc=>cy rfl fun b hb=>cast_len hc hb
private theorem twice_grade {b c:ℕ} (hc:c∈range 980) (hb:b∈bbW c) :
  2*(∑ a∈range (len b c),(a+b+c))=len b c*(6251+b+c) := by
 have hc' := mem_range.mp hc
 have hb' : b<1959 - 2*c+1 :=mem_range.mp hb
 have hl:len b c - 1+(b+c)=6251 := by
  unfold len
  omega
 calc
  _=(∑ a∈range (len b c),a)*2+len b c*(2*(b+c)) := by
    simp only [add_assoc,sum_add_distrib,sum_const,card_range,smul_eq_mul]
    ring
  _=len b c*(len b c - 1+(b+c))+len b c*(b+c) := by
    rw [sum_range_id_mul_two]
    ring
  _ = _:= by rw [hl]; ring
private theorem grade_box :
  (2 :ℤ) * ↑(∑ j∈P5_8.bo8.E,j.q)=boxSum (fun b c=>(6252-b-c)*(6251+b+c)) := by
 simp only [lI,aH1,sum_sigma,Jet.q,Jet.a,Jet.b,Jet.c,lJ,boxSum]
 rw [mul_sum]
 refine cy rfl fun c hc => ?_
 rw [mul_sum]
 refine cy rfl fun b hb => ?_
 have h:=congrArg (fun n:ℕ=>(n:ℤ)) (twice_grade hc hb)
 push_cast at h
 rw [cast_len hc hb] at h
 simpa only [Nat.cast_add,len] using h
private theorem index_box :
  (↑(∑ j∈P5_8.bo8.E,j.v) :ℤ)=boxSum (fun b c=>(6252-b-c)*(b+2*c)) := by
 simp only [lI,aH1,sum_sigma,Jet.v,Jet.b,Jet.c,sum_const,card_range,
  smul_eq_mul,lJ,Nat.cast_mul,boxSum]
 refine cy rfl fun c hc=>cy rfl fun b hb => ?_
 rw [show (↑(6251-(b+c)+1) :ℤ)=6252-b-c from cast_len hc hb]
 push_cast
 rfl
def poly (a b c d x :ℤ) :=a+b*x+c*x^2+d*x^3
def sumFormula (a b c d n:ℤ) :=
 12*a*n+6*b*n*(n-1)+2*c*n*(n-1)*(2*n-1)+3*d*n^2*(n-1)^2
theorem gvl (a b c d:ℤ) (n:ℕ) :
   12*(∑ i∈range n,poly a b c d i)=sumFormula a b c d n:= by
 induction n with
 | zero=>simp [sumFormula]
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih,Nat.cast_succ]
   unfold poly sumFormula
   ring
private theorem box_value (f :ℤ→ℤ→ℤ) (a b c:ℤ→ℤ)
   (r s t u value :ℤ)
   (hcoeff : ∀ x y,f x y=poly (a y) (b y) (c y) 0 x)
   (hrow : ∀ y,sumFormula (a y) (b y) (c y) 0 (1960-2*y)=poly r s t u y)
   (hend:sumFormula r s t u 980=144*value) :boxSum f=value := by
 have hs :12*boxSum f = ∑ y∈range 980,poly r s t u y := by
   unfold boxSum
   rw [mul_sum]
   refine cy rfl fun y hy => ?_
   have hn: (↑(1959-2*y+1) :ℤ)=1960-2*y := by
     have :=mem_range.mp hy
     omega
   simp only [bbW,hcoeff]
   rw [gvl,hn]
   exact hrow _
 have h:=gvl r s t u 980
 change 12*(∑ y∈range 980,poly r s t u y)=sumFormula r s t u 980 at h
 rw [← hs,hend] at h
 omega
private theorem card_value :boxSum (fun b c=>6252-b-c)=0x12e20e912 := by
 apply box_value _ (fun y=>6252-y) (fun _ => -1) (fun _=>0)
   0x7643af0 (-126540) 0 0
 · intros; unfold poly; ring
 · intro; unfold poly sumFormula; ring
 · decide
private theorem grade_value :
   boxSum (fun b c=>(6252-b-c)*(6251+b+c))=0x21317eeaf800:= by
 apply box_value _ (fun y=>6252*6251+y-y^2) (fun y=>1-2*y) (fun _ => -1)
   0xcf039f1140 (-0x35294810) (-23520) 8
 · intros; unfold poly; ring
 · intro; unfold poly sumFormula; ring
 · decide
private theorem index_value :
   boxSum (fun b c=>(6252-b-c)*(b+2*c))=0x5e143ee4d6c:= by
 apply box_value _ (fun y=>(6252-y)*2*y) (fun y=>6252-3*y) (fun _ => -1)
   0x1a8733eef0 23112868 (-150060) 8
 · intros; unfold poly; ring
 · intro; unfold poly sumFormula; ring
 · decide
theorem bsK:P5_8.Moments lI 0x12e20e912 0x1098bf757c00 0x5e143ee4d6c:= by
 have ht:=card_box.trans card_value
 have hs :=grade_box.trans grade_value
 have hv :=index_box.trans index_value
 exact ⟨by omega,by omega,by omega⟩
end P5_8_2
end
section
set_option autoImplicit true
namespace qxVnKgd
open P5_8_2 Finset
def T (n:ℤ) :ℤ:=(tri n.toNat :ℤ)
def H (w:ℤ) :ℤ:=T ((w+1)/2)+T (w/2)
def P (u:ℕ) :ℤ:=1959-(u:ℤ)
def O (q u:ℕ) :ℤ:=6559-(q:ℤ)-u
def A (p o:ℤ) :ℤ:=max 0 (2*p+o-3919)
def low (q d o:ℤ) :ℤ:=T (d+1)-(max 0 (q-979))^2 - H o
def high (p o a c:ℤ) :ℤ :=
 let n:=980-a-c
 n*(n+1) - H (p-2*a-c) - H (o-a-2*c)
def line (e :ℕ) :Multiplicities := ![0,0,0,0,e,0]
def pair (a c:ℕ) :Multiplicities := ![a,0,0,a,0,c]
def pick (q u:ℕ) :Multiplicities :=
 if q<1959 then line (O q u - q).toNat
 else pair (A (P u) (O q u)).toNat (A (O q u) (P u)).toNat
abbrev Cell:=Σ _:ℤ,ℤ
def region (i:Fin 7) :Finset Cell :=
 match i.val with
 | 0=>(Icc 0 1958).sigma fun q=>Icc 1 q
 | 1=>(Icc 0 1958).sigma fun q=>Icc (max 0 (2*q-1959)) (q-1)
 | 2=>(Icc 1 1959).sigma fun o=>Icc (o-2641) 0
 | 3=>(Icc 1 1856).sigma fun p=>Icc (max 1 (p-1651)) (min (3919-2*p) ((3919-p)/2))
 | 4=>(Icc 1307 1959).sigma fun p=>Icc (max (3920-2*p) (p-1651)) ((3919-p)/2)
 | 5=>(Icc 1307 1959).sigma fun p=>Icc (3920-2*p) ((3919-p)/2)
 | _=>(Icc 2614 2939).sigma fun s=>Icc (3920-s) (2*s-3920)
def score (i:Fin 7) (x :Cell) :ℤ :=
 let p:=x.1
 let o:=x.2
 match i.val with
 | 0=>low p p o
 | 1=>low p o o
 | 2=>961380 - H p
 | 3=>high p o 0 0
 | 4 | 5=>high p o (2*p+o-3919) 0
 | _=>(2939-p)*(2940-p)
end qxVnKgd
end
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6_1
noncomputable section
open Polynomial Matrix gR P6
open ProximityPrize.Benchmark
open private a3F cG9 b7E from ProximityPrize.SubmissionLower.E
private theorem gEN (u:e9) (γ:K) :
    ((So u).map (evalRingHom γ)) =
      kL.bnN (kL.a9j (frobenius K p))
        node (fun i=>u 0 i+γ*u 1 i) L t:= by
  rw [So,kL.dfp,kL.cTe]
  have h: (fun b:Fin 2=>iterateFrobenius K p b.val) =
      kL.a9j (frobenius K p) := by
    funext b
    fin_cases b
    · exact iterateFrobenius_zero K p
    · exact iterateFrobenius_one K p
  rw [h]
private theorem fS1 {u:e9} (T:qo u) {γ:K} (hγ:Normal u γ) :
    ((So u).map (evalRingHom γ)).rank=L+T.height:= by
  change _=Vv u at hγ
  rw [hγ,aSO]
  have h:=a7J T
  omega
private theorem d1y {u:e9} {γ:K} (M:B5 u γ)
    (E :Finset I) (hE :E.card≤t)
    (hEagree : ∀ i∉E,u 0 i+γ*u 1 i=M.decoder.eval (node i)) :
    ((So u).map (evalRingHom γ)).rank =
      (kL.afy (frobenius K p) (fun i:E=>node i.val)
        (fun i:E=>u 0 i.val+γ*u 1 i.val-M.decoder.eval (node i.val)) L).rank := by
  have hfix : ∀ b i,kL.a9j (frobenius K p) b (node i)=node i:= by
    intro b i
    fin_cases b <;> simp [kL.a9j,frobenius_def,Native.ahU]
  have h:=kL.cHH
    (kL.a9j (frobenius K p)) node (fun i=>u 0 i+γ*u 1 i)
    IRSProfile.domain.injective hfix M.decoder k L t M.degree
    (by rw [IRSProfile.card_index]; decide) E (hE.trans (Nat.le_succ t)) hEagree
  rw [kL.dOW] at h
  rw [gEN]
  exact h
private theorem gKS {u:e9} {T:qo u} (R:Relation T)
    (γ:K) (S:Finset I)
    (hdegree :max (vn (y1 R) γ).natDegree (vn (zv R) γ).natDegree=T.height)
    (hG:aiE (mL node S) (vn (y1 R) γ) (vn (zv R) γ)) :
    ¬ as1 R:= by
  intro hinvalid
  rcases hinvalid with hlow | ⟨G,_,hGU,hGV,hbad⟩
  · have hle :max (vn (y1 R) γ).natDegree (vn (zv R) γ).natDegree ≤
        max (y1 R).natDegree (zv R).natDegree :=
      max_le_max Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    omega
  · have hS:mL node S∣mL node Finset.univ :=
      ⟨mL node (Finset.univ \ S),
        (Principal.cYK node S Finset.univ (Finset.subset_univ S)).symm⟩
    exact hbad ((hG.2.2.2 G (b7E γ hGU) (b7E γ hGV)).trans hS)
theorem proof :P6.c1 := by
  classical
  intro u hfront T R γ hγ M
  let U:=vn (y1 R) γ
  let V:=vn (zv R) γ
  let E :Finset I:=Finset.univ.filter (fun i=>M.decoder.eval (node i)≠u 0 i+γ*u 1 i)
  let e :E→K:= fun i=>u 0 i.val+γ*u 1 i.val-M.decoder.eval (node i.val)
  let x :E→K:= fun i=>node i.val
  have hEagree (i:I) (hi:i∉E) :u 0 i+γ*u 1 i=M.decoder.eval (node i) := by
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm h⟩)
  have hEcard:E.card≤t:= by
    have hsub:E⊆Finset.univ \ M.support := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hs => ?_⟩
      exact (Finset.mem_filter.mp hi).2 (M.lg i hs)
    have h:=Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      IRSProfile.card_index] at h
    exact h.trans (Nat.sub_le_sub_left M.dw blockLength)
  have hheight:T.height≤DY:=aEz hfront T
  have hH :T.height<L:=hheight.trans_lt (by change 33561<48755; decide)
  have hfit :k+T.height≤M.support.card :=
    have hcap:k+DY≤dw:= by
      change 164633≤179827
      decide
    ((Nat.add_le_add_left hheight k).trans hcap).trans M.dw
  have hfix (i:I) :frobenius K p (node i)=node i:=Native.ahU i
  obtain ⟨hpair,hrel⟩ :=
    kL.cEP p node (u 0) (u 1) k T.height R γ
  have hUle :U.natDegree≤T.height:=hrel.degree_U
  have hVle :V.natDegree≤T.height:=hrel.degree_V
  have hx :Function.Injective x :=IRSProfile.domain.injective.comp Subtype.val_injective
  have he (i:E) :e i≠0 :=
    sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp i.property).2)
  have herror (i:E) :U.eval (x i)*e i+V.eval (x i)*frobenius K p (e i)=0 :=
    kL.dHv p node (u 0) (u 1) IRSProfile.domain.injective
      Native.ahU k T.height R γ M.support hfit M.decoder M.degree M.lg i.val
  have hrank : (kL.afy (frobenius K p) x e L).rank=L+T.height :=
    (d1y M E hEcard hEagree).symm.trans (fS1 T hγ)
  obtain ⟨hU,hV⟩:=kL.db5 (frobenius K p) x e hx U V
    T.height L hUle hVle hpair hH he herror hrank
  let G:=GCDMonoid.gcd U V
  let C₀:=(Finset.univ :Finset E).filter (fun i=>G.eval (x i)=0)
  let S:=C₀.image (fun i:E=>i.val)
  obtain ⟨hC,hsum,_⟩:=kL.eFc (frobenius K p) x e hx
    (fun i=>hfix i.val) U V T.height L hUle hVle hpair hH he herror hrank
  have hmax :max U.natDegree V.natDegree=T.height:= by
    obtain ⟨hle,hred⟩:=kL.bed U V hU hV
    change max (U/G).natDegree (V/G).natDegree+G.natDegree=T.height at hsum
    change G.natDegree≤ max U.natDegree V.natDegree at hle
    change max (U/G).natDegree (V/G).natDegree =
      max U.natDegree V.natDegree-G.natDegree at hred
    omega
  have hS_card:S.card=G.natDegree :=
    (Finset.card_image_of_injective C₀ Subtype.val_injective).trans hC
  have hS_error (i:I) (hi:i∈S) :M.decoder.eval (node i)≠u 0 i+γ*u 1 i:= by
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp j.property).2
  have hG:aiE (mL node S) U V:= by
    apply cG9 U V hV S _ hS_card
    intro i hi
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hj).2
  refine ⟨hU,hV,hmax,⟨S,hS_error,hG⟩,?_,gKS R γ S hmax hG⟩
  intro i hi
  have hzero :=(Finset.mem_filter.mp hi).2
  have hu0:U.eval (node i)=0:= by
    change (vn (y1 R) γ).eval (node i)=0
    rw [a3F,hzero.1,eval_zero]
  have hv0:V.eval (node i)=0:= by
    change (vn (zv R) γ).eval (node i)=0
    rw [a3F,hzero.2,eval_zero]
  have hdiv : (Polynomial.X:K[X]) - C (node i)∣mL node S :=
    hG.2.2.2 _ (dvd_iff_isRoot.mpr hu0) (dvd_iff_isRoot.mpr hv0)
  have hroot : (mL node S).eval (node i)=0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdiv (by rw [eval_sub,eval_X,eval_C,sub_self])
  exact hS_error i ((Principal.aVH node IRSProfile.domain.injective S i).mp hroot)
end
end P6_1
end
section
set_option autoImplicit true
namespace P6_8
noncomputable section
open i4 PolynomialDifferential MvPolynomial
open P5_8 (Jn Equation caps bo8 smallCaps donorCaps Gq tariffShape properDegree componentCap)
open scoped Polynomial BigOperators
abbrev A:=P6.dw
abbrev donorMargin:ℕ:=0x630cb8e12adcbc
def DonorSurplus (w:Node→K) :Prop :=
  Vv A bo8 w+donorMargin≤Fintype.card (apU A bo8)
structure Allocation (a :Jn) :Prop where
  total:a.B≤83
  index :a.J≤25
  top:a.C≤11
  top_total:a.C≤a.B
  top_index :2*a.C≤a.J
  index_total:a.J≤a.B+a.C
  capacity :0<a.B→donorMargin≤(gap A+2)*Gq a
structure Companion (Q:Equation) (w:Node→K) where
  common :Equation
  common_ne :common≠0
  allocation :Allocation (caps common)
  jO:Equation
  leftNative :Equation
  azo:Q=jO*leftNative
  removed_support : ∃ l:ℕ,apQ.initial jO∣apQ.initial common^l
  right:BL 2
  right_ne :right≠0
  coprime :IsRelPrime (apQ.initial leftNative) right
  left_band : let s := (smallCaps.wD (caps common)).repair
              apQ.initial leftNative∈aFz.GS s.B s.J s.C
  right_band : let s := (donorCaps.wD (caps common)).repair
               right∈aFz.GS s.B s.J s.C
  roots : ∀ f∈close A w,differentialSpecialization common f≠0 →
    MvPolynomial.eval (apQ.ahT f) (apQ.initial leftNative)=0 ∧
    MvPolynomial.eval (apQ.ahT f) right=0
def Companion.left {Q:Equation} {w:Node→K} (d:Companion Q w) :=
  apQ.initial d.leftNative
structure FactorCharts (L R:BL 2) where
  count:ℕ
  factor :Fin count→Equation
  bKQ: (∏ i,apQ.initial (factor i))∣L
  charts : ∀ i,P5_8.ProperCharts (apQ.initial (factor i)) R
def lowFee (s :Source) :ℕ:=errors A*R₁ s+gap A*H s^2
def regularFee (s :Source) :ℕ:=errors A*(2*R₂ s)+gap A*s.B
def commonFee (a :Jn) :ℕ :=
  lowFee (tariffShape a)+if a.C=0 then 0 else regularFee (tariffShape a)
def c5H (a :Jn) :ℕ:=errors A*properDegree a+gap A*componentCap a
end
end P6_8
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6_2
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open P6 (e9 k uO)
open aBc (K I node twist qW fold ajX Bg ahu
  bi7 bfs c3U degree_sub_lt bpo
  aQk cpG aQl)
open private coU from ProximityPrize.SubmissionLower.B
open private Aj.aQO from ProximityPrize.SubmissionLower.B
open private cti from ProximityPrize.SubmissionLower.CQ
structure N6 (u:e9) (S:Finset I) (H :ℕ) where
  a :K[X]
  b:K[X]
  A:Fin 2→K[X]
  Q:K→K→K[X]
  a_ne :a≠0
  norms_ne :K1.Ox a≠K1.Ox b
  primitive :IsCoprime (A 0) (A 1)
  a_bound:a.natDegree+uO (A 0) (A 1)≤H
  b_bound:b.natDegree+uO (A 0) (A 1)≤H
  Q_degree : ∀ r s,(Q r s).degree<(k+H :ℕ)
  nodes : ∀ r s i,i∈S →
    (Q r s).eval (node i) =
      a.eval (node i)*twist ((qW (A 0) (A 1) r).eval (node i))*fold u s i -
      b.eval (node i)*(qW (A 0) (A 1) s).eval (node i)*twist (fold u r i)
abbrev N6.amp {u S H} (D:N6 u S H) :=qW (D.A 0) (D.A 1)
private theorem cGF (q:ℕ) (hq:1<q) (hσ : ∀ z :K,z^q=twist z)
    {u:e9} {S:Finset I} {a b:K[X]} {A:Fin 2→K[X]} {W:P6.nC}
    (h:Aj.ad9 q u S (Aj.NJ q a A) (K1.J9 b A) W)
    (i:I) (hi:i∉S) :
    (Bg W 0).eval (node i)=ahu u a b A i 0 0 ∧
    (Bg W 1).eval (node i)=ahu u a b A i 0 1 ∧
    (Bg W q).eval (node i)=ahu u a b A i 1 0 ∧
    (Bg W (q+1)).eval (node i)=ahu u a b A i 1 1 :=
  aBc.dM7 u a b A i q hq hσ W (Aj.NJ q a A)
    (aBc.d2k a A i q) (h i hi).symm
private theorem coefficients {u:e9} {T:P6.qo u} {R:P6.Relation T}
    {D:P6.Reduction u T R} (B:P6.KJ u T R D) (hp:P6.Parallel B)
    (i:I) (hi:i∉P6.pJ R) :
    bi7 u B.a B.b B.α B.output i:= by
  have he :=B.nodes
  change B.α=B.β at hp
  rw [aSg.c73,aSg.bxJ,cti,← Aj.aQO,← hp] at he
  exact cGF K1.p (by decide) (fun z=>(frobenius_def K1.p z).symm) he i hi
theorem eMz {u:e9} {T:P6.qo u} {R:P6.Relation T}
    {D:P6.Reduction u T R} (B:P6.KJ u T R D)
    (hp:P6.Parallel B) (hn : ¬ P6.aSM B) :
    Nonempty (N6 u (Finset.univ \ P6.pJ R) D.height) := by
  classical
  let v (j:ℕ) :=Bg B.output j
  have hd (j:ℕ) : (v j).degree<(k+D.height:ℕ) :=
    coU _ _ _ B.output_degree
  have hfirst:=(congrArg (fun A:Fin 2→K[X] =>
    B.a.natDegree+uO (A 0) (A 1)≤D.height) hp).mpr B.first_degree
  refine ⟨⟨B.a,B.b,B.α,
    fun r s=>qW (qW (v 0) (v 1) s) (qW (v P6.p) (v (P6.p+1)) s) (twist r),
    B.a_ne,hn,B.α_primitive,hfirst,B.second_degree,?_,?_⟩⟩
  · intro r s
    exact ajX (ajX (hd 0) (hd 1) s)
      (ajX (hd P6.p) (hd (P6.p+1)) s) _
  · intro r s i hi
    obtain ⟨h0,h1,h2,h3⟩:=coefficients B hp i (Finset.mem_sdiff.mp hi).2
    simp only [qW,fold,v,eval_add,eval_mul,eval_C,h0,h1,h2,h3,
      ahu,map_add,map_mul]
    ring
open private bAV residual b3K from ProximityPrize.SubmissionLower.B
private theorem N6.cBf {u S H} (D:N6 u S H) {r s :K}
    (hrs :r≠s) (i:I) : (D.amp r).eval (node i)≠0∨(D.amp s).eval (node i)≠0:= by
  by_contra! hz
  obtain ⟨hr,hs⟩:=hz
  simp only [N6.amp,qW,eval_add,eval_mul,eval_C] at hr hs
  have hb: (r-s)*(D.A 1).eval (node i)=0:= by linear_combination hr - hs
  have h1 :=(mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hrs)
  have h0: (D.A 0).eval (node i)=0:= by simpa [h1] using hr
  obtain ⟨P,Q,hPQ⟩:=D.primitive
  have h:=congrArg (Polynomial.eval (node i)) hPQ
  simp only [eval_add,eval_mul,h0,h1,mul_zero,add_zero,eval_one,zero_ne_one] at h
private def N6.afu {u S H} (D:N6 u S H) (r s :K) (P Q:K[X]) :K[X] :=
  D.a*(D.amp r).map twist*Q - D.b*D.amp s*P.map twist
private theorem N6.cIA {u S H} (D:N6 u S H) (r s :K)
    {P Q:K[X]} (hP:P.degree<k) (hQ:Q.degree<k) :
    (D.afu r s P Q).degree<(k+H :ℕ) := by
  have hl: (D.a*(D.amp r).map twist).natDegree≤H :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (natDegree_map_le.trans (c3U ..)) _).trans D.a_bound
  have hr : (D.b*D.amp s).natDegree≤H :=
    natDegree_mul_le.trans <|
      (Nat.add_le_add_left (c3U ..) _).trans D.b_bound
  exact degree_sub_lt
    (kL.ahy _ _ H k hl hQ)
    (kL.ahy _ _ H k hr (degree_map_le.trans_lt hP))
private theorem N6.cJJ {u S H} (D:N6 u S H) (z :K)
    (W:Finset I) (P:K[X]) (hW:k+H≤W.card) (hWS:W⊆S) (hP:P.degree<k)
    (lg : ∀ i∈W,P.eval (node i)=fold u z i) :D.afu z z P P=D.Q z z := by
  have hb: ((k+H :ℕ) :WithBot ℕ)≤W.card:= by exact_mod_cast hW
  apply bpo W _ _ ((D.cIA z z hP hP).trans_le hb) ((D.Q_degree z z).trans_le hb)
  intro i hi
  simp only [N6.afu,eval_sub,eval_mul,bfs,lg i hi,D.nodes z z i (hWS hi)]
private def N6.gvf {u S H} (D:N6 u S H) (P Q:K[X])
    (hP:P.degree<k) (hQ:Q.degree<k) :N6 (residual u P Q) S H where
  a :=D.a
  b:=D.b
  A:=D.A
  Q r s :=D.Q r s - D.afu r s (qW P Q r) (qW P Q s)
  a_ne :=D.a_ne
  norms_ne :=D.norms_ne
  primitive :=D.primitive
  a_bound:=D.a_bound
  b_bound:=D.b_bound
  Q_degree r s :=degree_sub_lt (D.Q_degree r s)
    (D.cIA r s (ajX hP hQ r) (ajX hP hQ s))
  nodes r s i hi:= by
    simp only [eval_sub,D.nodes r s i hi,N6.afu,eval_mul,bfs,b3K,map_sub]
    ring
private theorem N6.c1Y {u S H} (D:N6 u S H) {r s :K}
    (hcard:k+3*H≤S.card) (hr :D.amp r≠0) (hs :D.amp s≠0)
    (hrr :D.Q r r=0) (hss :D.Q s s=0) :
    D.Q r s=0:= by
  let E :=D.amp s*(D.amp r).map twist
  let d:=uO (D.A 0) (D.A 1)
  have hd:d≤H :=(Nat.le_add_left _ _).trans D.a_bound
  have hE :E.natDegree≤d+d:=natDegree_mul_le.trans
    (Nat.add_le_add (c3U ..) (natDegree_map_le.trans (c3U ..)))
  have hl: (D.b*E).natDegree≤H+H := by
    have hb:D.b.natDegree+d≤H :=D.b_bound
    exact natDegree_mul_le.trans (by omega)
  have ht: (D.a.map twist*E.map twist).natDegree≤H+H := by
    have ha :D.a.natDegree+d≤H :=D.a_bound
    exact natDegree_mul_le.trans
      ((Nat.add_le_add natDegree_map_le natDegree_map_le).trans (by omega))
  have hcut: ((k+H+(H+H) :ℕ) :WithBot ℕ)≤S.card:= by
    exact_mod_cast (show k+H+(H+H)≤S.card by omega)
  have heq :D.b*E*(D.Q r s).map twist=D.a.map twist*E.map twist*D.Q r s := by
    apply bpo S _ _
      ((kL.ahy _ _ _ _ hl (degree_map_le.trans_lt (D.Q_degree r s))).trans_le hcut)
      ((kL.ahy _ _ _ _ ht (D.Q_degree r s)).trans_le hcut)
    intro i hi
    have h₁:=(D.nodes r r i hi).symm
    have h₂:=(D.nodes s s i hi).symm
    rw [hrr,eval_zero] at h₁
    rw [hss,eval_zero] at h₂
    have hσ:=congrArg (fun x=>twist x) h₁
    simp only [map_sub,map_mul,map_zero] at hσ
    simp only [E,eval_mul,bfs,D.nodes r s i hi,map_sub,map_mul]
    linear_combination
      -(twist (D.a.eval (node i)))*twist (twist ((D.amp r).eval (node i))) *
        twist ((D.amp r).eval (node i))*h₂ +
      D.b.eval (node i)*(D.amp s).eval (node i)*twist ((D.amp s).eval (node i))*hσ
  by_contra hne
  have hn:E≠0:=mul_ne_zero hs ((Polynomial.map_ne_zero_iff twist.injective).mpr hr)
  have hN :=congrArg K1.Ox heq
  simp only [aQk,cpG] at hN
  exact D.norms_ne (mul_right_cancel₀ (aQl hn)
    (mul_right_cancel₀ (aQl hne) hN.symm))
private theorem N6.gNo {u S H} (D:N6 u S H) {r s :K}
    (hcard:k+3*H≤S.card) (hrs :r≠s) (hr :D.amp r≠0) (hs :D.amp s≠0)
    (hrr :D.Q r r=0) (hss :D.Q s s=0) (i:I) (hi:i∈S) (y z :K) :
    (D.Q y z).eval (node i)=0:= by
  have hrs' := D.c1Y hcard hr hs hrr hss
  have hsr' := D.c1Y hcard hs hr hss hrr
  let f (r s :K) :=(D.Q r s).eval (node i)
  have nodes (a b:K) :=D.nodes a b i hi
  have right (x γ:K) :f x γ=f x 0+id γ*(f x 1 - f x 0) := by
    simp only [f,nodes,qW,fold,eval_add,eval_mul,eval_C,id_eq]
    ring
  have left (x γ:K) :f γ x=f 0 x+twist γ*(f 1 x - f 0 x) := by
    simp only [f,nodes,qW,fold,eval_add,eval_mul,eval_C,map_add,map_mul,
      map_zero,map_one]
    ring
  have h₁:f r z=0:=bAV (f r) id Function.injective_id hrs (right r)
    (by simp [f,hrr]) (by simp [f,hrs']) z
  have h₂:f s z=0:=bAV (f s) id Function.injective_id hrs (right s)
    (by simp [f,hsr']) (by simp [f,hss]) z
  exact bAV (fun γ=>f γ z) twist twist.injective hrs (left z) h₁ h₂ y
private theorem N6.dU3 {u S H} (D:N6 u S H) {r :K}
    (hr :D.amp r≠0) (hQ : ∀ i∈S,∀ y z,(D.Q y z).eval (node i)=0) (z :K)
    (W:Finset I) (P:K[X]) (hW:k+H≤W.card) (hWS:W⊆S)
    (hP:P.degree<k) (lg : ∀ i∈W,P.eval (node i)=fold u z i) :P=0:= by
  have hb: ((k+H :ℕ) :WithBot ℕ)≤W.card:= by exact_mod_cast hW
  have h0: (0:K[X]).degree<k := by rw [degree_zero]; exact WithBot.bot_lt_coe _
  by_cases hz :D.amp z=0
  · have hcross :D.afu r z 0 P=D.a*(D.amp r).map twist*P:= by
      rw [N6.afu,hz,mul_zero,zero_mul,sub_zero]
    have hc:D.a*(D.amp r).map twist*P=0:= by
      have hd:=D.cIA r z (P:=0) (Q:=P) h0 hP
      rw [hcross] at hd
      apply bpo W _ _ (hd.trans_le hb)
        (by rw [degree_zero]; exact WithBot.bot_lt_coe _)
      intro i hi
      rw [eval_mul,eval_mul,bfs,lg i hi,eval_zero]
      have he : (D.Q r z).eval (node i) =
          D.a.eval (node i)*twist ((D.amp r).eval (node i))*fold u z i -
          D.b.eval (node i)*(D.amp z).eval (node i)*twist (fold u r i) :=
        D.nodes r z i (hWS hi)
      rw [hQ i (hWS hi) r z,hz,eval_zero,mul_zero,zero_mul,sub_zero] at he
      exact he.symm
    exact (mul_eq_zero.mp hc).resolve_left
      (mul_ne_zero D.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hr))
  · have he :=D.cJJ z W P hW hWS hP lg
    have hq:D.Q z z=0:= by
      apply bpo W _ _ ((D.Q_degree z z).trans_le hb)
        (by rw [degree_zero]; exact WithBot.bot_lt_coe _)
      intro i hi
      rw [hQ i (hWS hi) z z,eval_zero]
    rw [hq,N6.afu] at he
    by_contra hne
    have hN :=congrArg K1.Ox (sub_eq_zero.mp he)
    simp only [aQk,cpG] at hN
    exact D.norms_ne (mul_right_cancel₀ (aQl hz)
      (mul_right_cancel₀ (aQl hne) hN))
theorem eKY {u:e9} {S H A} (D:N6 u S H) (Γ:Finset K)
    (hcard:k+3*H≤S.card) (hA:k+H≤A)
    (M : ∀ z∈Γ,P6.a9J A u z) (hMS : ∀ z hz,(M z hz).support⊆S) :
    Γ.card≤2 ∨ ∃ P Q:K[X],P.degree<k∧Q.degree<k ∧
      ∀ z (hz :z∈Γ),(M z hz).decoder=qW P Q z := by
  classical
  let G:=Γ.filter (fun z=>D.amp z≠0)
  by_cases hsmall:G.card≤1
  · let Ju:=Γ.filter (fun z=>D.amp z=0)
    have hZ:Ju.card≤1 := by
      apply Finset.card_le_one_iff.mpr
      intro r s hr hs
      by_contra hrs
      have hr' := (Finset.mem_filter.mp hr).2
      have hs' := (Finset.mem_filter.mp hs).2
      simpa [hr',hs'] using D.cBf hrs (0:I)
    have hsum:Ju.card+G.card=Γ.card:=Finset.card_filter_add_card_filter_not ..
    exact Or.inl (by omega)
  right
  obtain ⟨r,hr,s,hs,hrs⟩:=Finset.one_lt_card.mp (by omega :1<G.card)
  obtain ⟨hrΓ,hrA⟩:=Finset.mem_filter.mp hr
  obtain ⟨hsΓ,hsA⟩:=Finset.mem_filter.mp hs
  let Wr :=(M r hrΓ).decoder
  let Ws :=(M s hsΓ).decoder
  let Q:=C ((s-r)⁻¹)*(Ws-Wr)
  let P:=Wr - C r*Q
  have hWr :Wr.degree<k :=(M r hrΓ).degree
  have hWs :Ws.degree<k :=(M s hsΓ).degree
  have scale (c:K) (V:K[X]) (hV:V.degree<k) : (C c*V).degree<k := by
    by_cases hc:c=0
    · rw [hc,map_zero,zero_mul,degree_zero]
      exact WithBot.bot_lt_coe k
    · simpa only [degree_C_mul hc] using hV
  have hQ:Q.degree<k :=scale _ _ (degree_sub_lt hWs hWr)
  have hP:P.degree<k :=degree_sub_lt hWr (scale _ _ hQ)
  have hpr :qW P Q r=Wr := by simp [qW,P]
  have hps :qW P Q s=Ws := by
    have hc: (C s - C r :K[X])*C ((s-r)⁻¹)=1 := by
      rw [← map_sub,← map_mul,mul_inv_cancel₀ (sub_ne_zero.mpr hrs.symm),map_one]
    calc
      qW P Q s=Wr+((C s - C r)*C ((s-r)⁻¹))*(Ws-Wr) := by
        simp only [qW,P,Q]
        ring
      _=Ws := by rw [hc,one_mul,add_comm,sub_add_cancel]
  let D' := D.gvf P Q hP hQ
  have hd (z :K) (hz :z∈Γ) (h:qW P Q z=(M z hz).decoder) :D'.Q z z=0:= by
    change D.Q z z - D.afu z z (qW P Q z) (qW P Q z)=0
    rw [h,D.cJJ z _ _ (hA.trans (M z hz).dw) (hMS z hz)
      (M z hz).degree (M z hz).lg,sub_self]
  have hzero :=D'.gNo hcard hrs hrA hsA (hd r hrΓ hpr) (hd s hsΓ hps)
  refine ⟨P,Q,hP,hQ,fun z hz=>sub_eq_zero.mp ?_⟩
  let W:=M z hz
  change W.decoder - qW P Q z=0
  apply D'.dU3 hrA hzero z W.support _ (hA.trans W.dw) (hMS z hz)
    (degree_sub_lt W.degree (ajX hP hQ z))
  intro i hi
  rw [b3K,eval_sub,W.lg i hi]
  rfl
end
end P6_2
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P6_2
noncomputable section
open Polynomial gR ProximityPrize.Benchmark
open P6 (e9 k blockLength)
open aBc (K I node qW)
theorem cby {u:e9} {A:ℕ} (Γ:Finset K)
    (M : ∀ z∈Γ,P6.a9J A u z) {P Q:K[X]} (hP:P.degree<k)
    (hQ:Q.degree<k) (h : ∀ z (hz :z∈Γ),(M z hz).decoder=qW P Q z) :
    Γ.card≤blockLength - A+1 := by
  classical
  by_cases hΓ:Γ.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hΓ]
  obtain ⟨r,hr⟩:=hΓ
  let S:=(M r hr).support
  let nonjoint (i:I) :=P.eval (node i)≠u 0 i∨Q.eval (node i)≠u 1 i
  have lg {z :K} (hz :z∈Γ) {i:I} (hi:i∈(M z hz).support) :
      P.eval (node i)+z*Q.eval (node i)=u 0 i+z*u 1 i:= by
    simpa only [h z hz,qW,eval_add,eval_mul,eval_C] using (M z hz).lg i hi
  have unique {z t:K} (hz :z∈Γ) (ht:t∈Γ) {i:I}
      (hi:i∈(M z hz).support) (hj:i∈(M t ht).support) (hn:nonjoint i) :z=t:= by
    by_contra hne
    have h₁:=lg hz hi
    have h₂:=lg ht hj
    have hw: (z-t)*(Q.eval (node i) - u 1 i)=0:= by linear_combination h₁ - h₂
    have he :=sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (sub_ne_zero.mpr hne))
    rw [he,add_right_cancel_iff] at h₁
    exact hn.elim (fun hbad=>hbad h₁) (fun hbad=>hbad he)
  have witness (z : ↥(Γ.erase r)) :
      ∃ i∈(M z.val (Finset.mem_erase.mp z.property).2).support,nonjoint i:= by
    let W:=M z.val (Finset.mem_erase.mp z.property).2
    by_contra hw
    apply W.nonjoint
    refine ⟨⟨P,hP,?_⟩,⟨Q,hQ,?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i,hi,Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i,hi,Or.inr hn⟩
  choose f hf hn using witness
  let g : ↥(Γ.erase r) → ↥((Finset.univ :Finset I) \ S) := fun z =>
    ⟨f z,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hi =>
      (Finset.mem_erase.mp z.property).1 (unique (Finset.mem_erase.mp z.property).2 hr (hf z) hi (hn z))⟩⟩
  have hg:Function.Injective g:= by
    intro z t hzt
    have he :f z=f t:=congrArg Subtype.val hzt
    apply Subtype.ext
    have ht:=hf t
    rw [← he] at ht
    exact unique (Finset.mem_erase.mp z.property).2 (Finset.mem_erase.mp t.property).2 (hf z) ht (hn z)
  have hcard:=Finset.card_le_card_of_injective hg
  have he :=Finset.card_erase_add_one hr
  have hS:A≤S.card:=(M r hr).dw
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,IRSProfile.card_index] at hcard
  change Γ.card≤262144 - A+1
  omega
theorem proof :P6.c2 := by
  intro u hu T R D B _ hp hn Γ hΓ hnormal
  classical
  obtain ⟨data⟩:=eMz B hp hn
  obtain ⟨hcard,hA,_⟩:=P6.dd8 D hu
  have hd: (Finset.univ :Finset I).card=P6.blockLength:= by
    rw [Finset.card_univ,IRSProfile.card_index]
  have hret:k+3*D.height≤(Finset.univ \ P6.pJ R).card:= by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),hd]
    exact hcard
  let M (z :K) (hz :z∈Γ) :=Classical.choice (P6.aCl u Γ hΓ z hz)
  have hMS (z :K) (hz :z∈Γ) :
      (M z hz).support⊆Finset.univ \ P6.pJ R:= by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun he =>
      D.deleted_error z (hnormal z hz) (M z hz) i he ((M z hz).lg i hi)⟩
  rcases eKY data Γ hret hA M hMS with hsmall | ⟨P,Q,hP,hQ,h⟩
  · exact hsmall.trans (by decide)
  · exact cby Γ M hP hQ h
end
end P6_2
end
