import ProximityPrize.SubmissionLower.ZZ0RELd
set_option Elab.async false
open _root_ renaming Finset.range→aU,Finset.range_mono→mD,Finset.sum_congr→lz,MvPolynomial.X→c9,Nat.mul_le_mul_left→nI,Nat.sub_add_cancel→n5,Nat.sub_le_sub_right→nX,P5_8.Moments→lI,P5_8.small→cy,Submodule→nq,min_le_left→lV,min_le_right→lJ
section
set_option autoImplicit true
namespace P5_8
noncomputable section
open i4 Finset PolynomialDifferential
open scoped BigOperators
private theorem lower_q (j:Jet) :Jet.q ⟨j.c,j.b,j.a-1⟩≤j.q:= by
 change j.a - 1+j.b+j.c≤j.a+j.b+j.c
 omega
theorem small_shape :Rz small:= by
 have hm:=b8U (B:=83) (J:=25) (C:=11) (by decide) (by decide)
 refine ⟨by decide,by decide,by decide,by decide,by decide,
  fun j hj=>(hm j).mp (mem_filter.mp hj).1,?_⟩
 intro j hj _
 obtain ⟨hbox,htail⟩:=mem_filter.mp hj
 obtain ⟨hq,hv,hc⟩:=(hm j).mp hbox
 apply mem_filter.mpr
 refine ⟨(hm _).mpr ⟨(lower_q j).trans hq,hv,hc⟩,?_⟩
 have hmono:=Nat.div_le_div_right (nX (lower_q j) 76) (c:=2)
 exact htail.trans (Nat.sub_le_sub_left hmono 25)
private theorem fullBox_shape (m B J C:ℕ) (hm:0< m) (hc:0<C)
  (hJC:2*C≤J) (hBJ:J≤B) (hp:max N (B*(B-1))<p) :
  Rz ⟨m,B,J,C,aH1 B J C⟩:= by
 have hmem:=b8U hBJ hJC
 refine ⟨hm,hc,hJC,hBJ,hp,fun j hj=>(hmem j).mp hj,?_⟩
 intro j hj _
 obtain ⟨hq,hv,ht⟩:=(hmem j).mp hj
 exact (hmem _).mpr ⟨(lower_q j).trans hq,hv,ht⟩
theorem donor_shape :Rz bo8 :=
 fullBox_shape 4600 6251 1959 979 (by decide) (by decide) (by decide) (by decide) (by decide)
end
end P5_8
end
section
set_option autoImplicit true
namespace P5_8_1
open ju (total)
abbrev source :=cy
def aAa (q u h:ℕ) :=u+2*q+h+1-86
def bvg (q u h:ℕ) :=min (q+1 - h) (u+2*(q-h)+1 - 25)
def a8b (q u h:ℕ) :=bvg q u h-aAa q u h
def ayp (u b:ℕ) :=(26-(u+b))/2
def bnz (q b:ℕ) :=min 12 (min (q-b+1) (min ((25-b)/2+1) (26-(q-76)/2-b)))
def bC1 (q u b:ℕ) :=bnz q b-ayp u b
abbrev af (q u:ℕ) :=(h:Fin (q+1))×Fin (a8b q u h)
abbrev qB (q u:ℕ) :=(b:Fin (min q 25+1))×Fin (bC1 q u b)
def ee (q u h i:ℕ) :i4.Jet :=
 let d:=aAa q u h+i
 ⟨q-(h+d),d,h⟩
def rowJet (q u:ℕ) (r :af q u) :i4.Jet:=ee q u r.1 r.2
def bny (q u b i:ℕ) :i4.Jet :=
 let c:=ayp u b+i
 ⟨c,b,q-(b+c)⟩
def bYa (q u:ℕ) (s :qB q u) :i4.Jet:=bny q u s.1 s.2
def Bs (q u:ℕ) :Matrix (af q u) (qB q u) (ZMod i4.p) :=
 fun r s=>i4.alu (rowJet q u r) (bYa q u s)
def rows (q u:ℕ) :=total (a8b q u) (q+1)
def cols (q u:ℕ) :=total (bC1 q u) (min q 25+1)
def b9S (q u:ℕ) :=min (rows q u) (cols q u)
open i4 MvPolynomial
abbrev F:=ZMod p
abbrev lK:=MvPolynomial (Fin 3) F
abbrev Orders :=ℕ×ℕ
abbrev Flags :=Orders×Orders×Orders
def sourceOrders (f :Flags) (e :Fin 3 →₀ ℕ) :Prop :=
 f.1.1≤e 1+e 2∧f.1.2≤e 1+2*e 2 ∧
 f.2.1.1≤e 0+e 1∧f.2.1.2≤2*e 0+e 1
def targetOrders (f :Flags) (e :Fin 3 →₀ ℕ) :Prop :=
 f.2.2.1≤e 0+e 2∧f.2.2.2≤2*e 0+e 2
noncomputable def contactChange :lK →ₐ[F] lK :=
 aeval ![c9 0+MvPolynomial.X 1-MvPolynomial.X 2,c9 1,c9 2]
noncomputable def flagSpace (d:ℕ) (f :Flags) :nq F lK :=
 (restrictSupport F {e | e.degree=d∧sourceOrders f e}) ⊓
   (restrictSupport F {e | targetOrders f e}).comap contactChange.toLinearMap
def iO (q:ℕ) :=min q (25-(q-76)/2)
def blockFlags (q u:ℕ) :Flags :=
 let d:=iO q
 ((0,25-u),(d-11,2*d-25),(0,86-q-u))
def triangle (n:ℕ) :=n*(n+1)/2
def cost (a :Orders) :ℕ :=
 let b:=max a.1 ((a.2+1)/2)
 triangle b+triangle (a.2-b)
def rawLower (d:ℕ) (f :Flags) :ℕ :=
 triangle (d+1)-(cost f.1+cost f.2.1+cost f.2.2)
def factorOrders :Fin 6→Flags
 | 0=>((1,2),(0,0),(1,1))
 | 1=>((1,1),(1,1),(0,0))
 | 2=>((0,0),(1,1),(1,1))
 | 3=>((0,0),(1,2),(0,0))
 | 4=>((0,0),(0,0),(1,2))
 | 5=>((1,1),(1,2),(1,2))
def yE (i:Fin 6) :ℕ:=if i=5 then 2 else 1
noncomputable def factorForm:Fin 6→lK
 | 0=>MvPolynomial.X 2
 | 1=>MvPolynomial.X 1
 | 2=>MvPolynomial.X 0-MvPolynomial.X 1
 | 3=>MvPolynomial.X 0
 | 4=>MvPolynomial.X 0-MvPolynomial.X 1+MvPolynomial.X 2
 | 5=>(MvPolynomial.X 0-MvPolynomial.X 1)*MvPolynomial.X 1+MvPolynomial.X 0*MvPolynomial.X 2
def remove (f :Flags) (i:Fin 6) (k :ℕ) :Flags :=
 let a :=factorOrders i
 let sub (x y :Orders) :Orders :=(x.1-k*y.1,x.2-k*y.2)
 (sub f.1 a.1,sub f.2.1 a.2.1,sub f.2.2 a.2.2)
abbrev Steps :=List (Fin 6×ℕ)
def flagLower (d:ℕ) (f :Flags) :Steps→ℕ
  | []=>rawLower d f
  | (i,k)::xs=>if k*yE i≤d then
      max (rawLower d f) (flagLower (d-k*yE i) (remove f i k) xs)
    else rawLower d f
end P5_8_1
end
section
set_option autoImplicit true
namespace P5_8_1
open i4 Finset
open scoped BigOperators
private def bbW (c:ℕ) :=aU (25 - 2*c+1)
private def E0 (c b:ℕ) :=min 83 (127 - 2*(b+c))+1-(b+c)
private theorem support_eq :
  P5_8.small.E=(aU 12).sigma fun c=>(bbW c).sigma fun b=>aU (E0 c b) := by
 apply Finset.ext
 intro j
 rcases j with ⟨c,b,a⟩
 change (⟨c,b,a⟩:Jet)∈(aH1 83 25 11).filter
  (fun j=>j.b+j.c≤25-(j.q-76)/2)↔_
 rw [Finset.mem_filter,i4.b8U (by decide) (by decide)]
 simp only [bbW,E0,mem_sigma,mem_range,
  Jet.q,Jet.v,Jet.a,Jet.b,Jet.c]
 omega
private def po (c:ℕ) := ∑ b∈bbW c,E0 c b
private def awL (c:ℕ) := ∑ b∈bbW c,
 (E0 c b*(E0 c b - 1)/2+E0 c b*(b+c))
private def aoi (c:ℕ) := ∑ b∈bbW c,E0 c b*(b+2*c)
private theorem bVY:P5_8.small.E.card = ∑ c∈aU 12,po c:= by
 simp only [support_eq,card_sigma,card_range,po]
private theorem dAo: (∑ j∈P5_8.small.E,j.q) = ∑ c∈aU 12,awL c:= by
 simp only [support_eq,sum_sigma,awL,Jet.q,Jet.a,Jet.b,Jet.c]
 apply lz rfl
 intro c _
 apply lz rfl
 intro b _
 simp only [Nat.add_assoc,sum_add_distrib,sum_range_id,sum_const,card_range,smul_eq_mul,Nat.mul_add]
private theorem a1U: (∑ j∈P5_8.small.E,j.v) = ∑ c∈aU 12,aoi c:= by
 simp only [support_eq,sum_sigma,aoi,Jet.v,Jet.b,Jet.c,sum_const,card_range,smul_eq_mul]
private def Acc (c t s v :ℕ) :Prop :=
 (∑ i∈aU c,po i)=t ∧
 (∑ i∈aU c,awL i)=s∧(∑ i∈aU c,aoi i)=v
private theorem step {c t s v x y z :ℕ} (h:Acc c t s v)
  (ht:po c=x) (hs :awL c=y) (hv :aoi c=z) :
  Acc (c+1) (t+x) (s+y) (v+z) := by
 unfold Acc at h ⊢
 simp only [sum_range_succ,h.1,h.2.1,h.2.2,ht,hs,hv,and_self]
local notation "az" prev "," a "," b "," c=>step prev (x :=a) (y :=b) (z :=c) rfl rfl rfl
private theorem r0:Acc 0 0 0 0:=⟨rfl,rfl,rfl⟩
private theorem r1 :Acc 1 1847 87062 21483:=az r0,1847,87062,21483
private theorem r2 :Acc 2 3557 167935 43351 :=az r1,1710,80873,21868
private theorem r3:Acc 3 5128 242438 65224 :=az r2,1571,74503,21873
private theorem r4 :Acc 4 6558 310388 86724 :=az r3,1430,67950,21500
private theorem r5:Acc 5 7845 371600 107475:=az r4,1287,61212,20751
private theorem r6:Acc 6 8989 426056 127155:=az r5,1144,54456,19680
private theorem r7:Acc 7 9990 473740 145446:=az r6,1001,47684,18291
private theorem r8:Acc 8 10848 514638 162034 :=az r7,858,40898,16588
private theorem r9:Acc 9 11563 548738 176609:=az r8,715, 34100,14575
private theorem dz :Acc 10 12135 576030 188865:=az r9,572,27292,12256
private theorem dD:Acc 11 12564 596506 198500:=az dz,429,20476,9635
private theorem dK:Acc 12 12850 610160 205216:=az dD,286,13654,6716
theorem bsK:lI cy 12850 610160 205216:= by
 unfold lI
 rw [bVY,dAo,a1U]
 exact dK
end P5_8_1
end
section
set_option autoImplicit true
namespace P5_8_2
open i4 Finset MvPolynomial
abbrev F:=ZMod i4.p
abbrev lK:=MvPolynomial (Fin 3) F
abbrev Orders :=ℤ×ℤ
abbrev Flags :=Fin 3→Orders
noncomputable section
def bqh (i:Fin 3) :lK →ₐ[F] lK :=
  let h:lK:=c9 0
  let u:lK:=c9 1
  let v :lK:=c9 2
  aeval (if i=0 then ![h-u,u,v]
    else if i=1 then ![v-u,u,h] else ![v-u,h,u])
def flagSpace (i:Fin 3) (a :Orders) :nq F lK :=
  (AddMonoidAlgebra.supported F F {e :Fin 3 →₀ ℕ |
    a.1≤(e 1 :ℤ)+e 2∧a.2≤(e 1 :ℤ)+2*e 2}).comap
    (bqh i).toLinearMap
def planeSpace (d:ℕ) (a :Flags) :nq F lK :=
 homogeneousSubmodule (Fin 3) F d ⊓ ⨅ i,flagSpace i (a i)
end
def normalize (a :Orders) :Orders :=
 let u:=max 0 (max a.1 ((a.2+1)/2))
 (u,max u a.2)
def tri (n:ℕ) :ℕ:=n*(n+1)/2
def yC (a :Orders) :ℕ :=
 let a :=normalize a
 tri a.1.toNat+tri (a.2 - a.1).toNat
def expected (d:ℕ) (a :Flags) :ℕ :=
 tri (d+1)-(yC (a 0)+yC (a 1)+yC (a 2))
def yE (j:Fin 6) :ℕ:=if j=5 then 2 else 1
def factorFlags (j:Fin 6) :Flags :=
  ![![(1,2),(0,0),(1,1)],![(1,1),(1,1),(0,0)],![(0,0),(1,1),(1,1)],
    ![(0,0),(1,2),(0,0)],![(0,0),(0,0),(1,2)],![(1,1),(1,2),(1,2)]] j
abbrev Multiplicities :=Fin 6→ℕ
def cost (m:Multiplicities) :ℕ := ∑ j,m j*yE j
def wD (a :Flags) (m:Multiplicities) :Flags := fun i =>
 ((a i).1 - ∑ j,(m j:ℤ)*(factorFlags j i).1,
  (a i).2 - ∑ j,(m j:ℤ)*(factorFlags j i).2)
def deg (q:ℕ) :ℕ:=min q 1959
def offset (u:ℕ) :ℤ:=(u:ℤ)-(1959:ℕ)
def initialFlags (q u:ℕ) :Flags :=
  ![(0,-offset u),((deg q:ℤ)-979,2*(deg q:ℤ) - 1959),
    (0,4600-(q:ℤ) - offset u)]
def m5 (q u:ℕ) (m:Multiplicities) :ℕ :=
 if cost m≤deg q then expected (deg q - cost m) (wD (initialFlags q u) m) else 0
end P5_8_2
end
section
namespace P5_8_5
noncomputable section
open i4 aFz P5_8 MvPolynomial
def jetCaps (p:BL 2) :Jn :=
 ⟨p.totalDegree,p.weightedTotalDegree Fin.val,p.degreeOf (Fin.last 2)⟩
def aEl (I:Ideal (BL 2)) (u:Jn) (m:ℕ) :
    nq nU (BL 2 ⧸ I) :=
  (GS (m*u.B) (m*u.J) (m*u.C)).map (Ideal.Quotient.mkₐ nU I).toLinearMap
instance (I:Ideal (BL 2)) (u:Jn) (m:ℕ) :
  Module.Finite nU (aEl I u m) := by
 unfold aEl
 infer_instance
def boxDifference (u a b:Jn) (m:ℚ) :ℚ :=
  let B:=m*u.B
  let J:=m*u.J
  let C:=m*u.C
  anJ B J C-anJ (B-a.B) (J-a.J) (C-a.C) -
    anJ (B - b.B) (J - b.J) (C - b.C) +
    anJ (B-a.B - b.B) (J-a.J - b.J) (C-a.C - b.C)
end
end P5_8_5
end
section
set_option autoImplicit true
namespace P5_8_6
open P5_8 Finset
open scoped BigOperators
private def row (B J c:ℕ) :ℕ :=
 ∑ b∈aU (J+1 - 2*c),(B+1-(c+b))
private theorem row_cut (B J c:ℕ) :
  row B J c = ∑ b∈aU (min (J+1-2*c) (B+1-c)),(B+1-c-b) := by
 unfold row
 simp only [Nat.sub_sub]
 symm
 refine sum_subset (mD (lV ..)) ?_
 intro b hb hm
 rw [mem_range] at hb hm
 omega
private theorem sum_desc (n x v :ℕ) (h:v*(n-1)≤x) :
    2*(∑ i∈aU n,(x-v*i))=n*(2*x-v*(n-1)) := by
  have hs : (∑ i∈aU n,(x-v*i))+v*(∑ i∈aU n,i)=n*x := by
    rw [mul_sum,← sum_add_distrib]
    calc
      _ = ∑ i∈aU n,x := by
        apply lz rfl
        intro i hi
        have hi' : i≤n-1 := by have :=mem_range.mp hi; omega
        exact n5 ((nI v hi').trans h)
      _ = _:= by simp
  have ht:=congrArg (fun a :ℕ=>2*a) hs
  rw [Nat.mul_add,show 2*(v*(∑ i∈range n,i))=v*((∑ i∈range n,i)*2) by ring,
    sum_range_id_mul_two] at ht
  have hsum:n*(2*x-v*(n-1))+v*(n*(n-1))=2*(n*x) := calc
    _=n*((2*x-v*(n-1))+v*(n-1)) := by ring
    _ = _:= by rw [n5 (h.trans (by omega))]; ring
  omega
private theorem row_total (B J c:ℕ) (h:B+c≤J) (hc:c≤B) :
  row B J c=(B+2-c).choose 2 := by
 rw [row_cut,min_eq_right (by omega),Nat.choose_two_right]
 have hd:=sum_desc (B+1-c) (B+1-c) 1 (by omega)
 rw [one_mul,show 2*(B+1-c)-(B+1-c-1)=B+2-c by omega] at hd
 simp only [one_mul] at hd
 rw [show B+2-c-1=B+1-c by omega,Nat.mul_comm (B+2-c)]
 omega
private theorem row_index (B J c:ℕ) (h:J≤B+c) (hc:2*c≤J) :
  2*row B J c=(J+1-2*c)*(2*B+2-J) := by
 rw [row_cut,min_eq_left (by omega)]
 have hd:=sum_desc (J+1-2*c) (B+1-c) 1 (by omega)
 simpa only [one_mul,show 2*(B+1-c)-(J+1-2*c-1)=2*B+2-J by omega] using hd
private theorem tetra_choose (n:ℕ) :tetra n=n.choose 3:= by
 rw [Nat.choose_eq_descFactorial_div_factorial]
 simp only [tetra,Nat.descFactorial_succ,Nat.descFactorial_zero,mul_one]
 change n*(n-1)*(n-2)/6=((n-2)*((n-1)*(n-0)))/6
 rw [Nat.sub_zero]
 congr 1
 ring
private theorem sum_choose (x d:ℕ) (h:d≤x) :
   (∑ i∈aU d,(x-i).choose 2)=(x+1).choose 3-(x+1-d).choose 3:= by
 induction d with
 | zero=>simp
 | succ d ih =>
   rw [sum_range_succ,ih (by omega)]
   have he :x+1-d=(x-d)+1 := by omega
   have he' : x+1-(d+1)=x-d:= by omega
   have hs : (x+1-d).choose 3=(x-d).choose 2+(x+1-(d+1)).choose 3:= by
     rw [he,he',Nat.choose_succ_succ']
   have hm: (x+1-d).choose 3≤(x+1).choose 3:=Nat.choose_le_choose _ (Nat.sub_le ..)
   omega
private theorem sum_index (B J z d:ℕ) (hz :2*z≤J) (hd:d≤z+1)
   (hi : ∀ i,i<z+1-d→J≤B+(d+i)) :
   (∑ i∈aU (z+1-d),row B J (d+i)) =
     (z+1-d)*(J+1-d-z)*(2*B+2-J)/2 := by
 let r :=z+1-d
 change (∑ i∈aU r,row B J (d+i))=r*(J+1-d-z)*(2*B+2-J)/2
 have hs :2*(∑ i∈aU r,row B J (d+i)) =
     (∑ i∈aU r,(J+1-2*d-2*i))*(2*B+2-J) := by
   rw [mul_sum,sum_mul]
   apply lz rfl
   intro i hm
   have he :i<z+1-d:=mem_range.mp hm
   rw [row_index B J (d+i) (hi i he) (by omega),show J+1-2*(d+i)=J+1-2*d-2*i by omega]
 have hh: (∑ i∈aU r,(J+1-2*d-2*i))=r*(J+1-d-z) := by
   by_cases hd' : d≤z
   · have hs' := sum_desc r (J+1-2*d) 2 (by dsimp [r]; omega)
     rw [show 2*(J+1-2*d)-2*(r-1)=2*(J+1-d-z) by dsimp [r]; omega] at hs'
     rw [← Nat.mul_assoc,Nat.mul_comm r 2,Nat.mul_assoc] at hs'
     omega
   · have hr :r=0:= by dsimp [r]; omega
     simp [hr]
 rw [hh] at hs
 omega
private theorem box_formula (B J C:ℕ) :
    aMt ⟨B,J,C⟩ = ∑ c∈aU (C+1),row B J c:= by
  let z :=min B (min (J/2) C)
  let d:=min (z+1) (J+1-B)
  have hzB:z≤B:=lV ..
  have hzJ:2*z≤J:= by
    have :z≤J/2 :=(lJ ..).trans (lV ..)
    omega
  have hzC:z≤C:=(lJ ..).trans (lJ ..)
  have hd:d≤z+1 :=lV ..
  have hdJ:d≤J+1-B:=lJ ..
  have hcut: (∑ c∈aU (z+1),row B J c) = ∑ c∈aU (C+1),row B J c:= by
    refine sum_subset (mD (by omega)) ?_
    intro c hc hcz
    have hzc:z<c:= by rw [mem_range] at hcz; omega
    by_cases hcB:B<c
    · simp only [row]
      exact sum_eq_zero fun b _=> by omega
    · have hcJ:J+1-2*c=0:= by
        have :=mem_range.mp hc
        dsimp [z] at hzc
        omega
      simp [row,hcJ]
  have hhead: (∑ c∈aU d,row B J c)=tetra (B+3) - tetra (B+3-d) := calc
    _ = ∑ c∈aU d,(B+2-c).choose 2 := by
      apply lz rfl
      intro c hc
      have :=mem_range.mp hc
      exact row_total B J c (by omega) (by omega)
    _ = _:= by rw [sum_choose _ _ (by omega),tetra_choose,tetra_choose]
  have htail:=sum_index B J z d hzJ hd (by
    intro i hi
    have hlt:d<z+1 := by omega
    have he :d=J+1-B:=min_eq_right (by dsimp [d] at hlt; omega)
    omega)
  change tetra (B+3) - tetra (B+3-d)+(z+1-d)*(J+1-d-z)*(2*B+2-J)/2= _
  rw [← hhead,← htail,← sum_range_add,show d+(z+1-d)=z+1 by omega]
  exact hcut
theorem bmt {B J C B' J' C' : ℕ} (hB:B≤B') (hJ:J≤J') (hC:C≤C') :
  aMt ⟨B,J,C⟩≤aMt ⟨B',J',C'⟩:= by
 rw [box_formula,box_formula]
 apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset (mD (by omega)))
 intro c _
 unfold row
 apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset (mD (by omega)))
 intro b _
 exact nX (Nat.add_le_add_right hB 1) _
end P5_8_6
end
