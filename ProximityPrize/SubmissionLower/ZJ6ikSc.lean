import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.Zc9uAjc
import ProximityPrize.SubmissionLower.ZNc08Oa
set_option Elab.async false
section
set_option autoImplicit true
namespace P6_6_4
noncomputable section
open aR jA Polynomial
open scoped Polynomial BigOperators
open private cfq from ProximityPrize.SubmissionLower.CS
private def weight (d i:ℕ) :ℕ:=d - 7062*i
private def power (w:ℕ) :ℕ:=(48757+w)/48758
private theorem a2J {k :Type*} [CommRing k]
    (P:k[X][X]) (d e i j:ℕ) (hij:j≤ i)
    (hP : ∀ i l:ℕ,7062*i+48758*l<d→(P.coeff i).coeff l=0) :
    (Polynomial.X:k[X])^power (weight (d+e) i - weight e j)∣P.coeff (i - j) := by
  have hweight:weight (d+e) i≤weight e j+weight d (i - j) := by
    unfold weight
    omega
  apply X_pow_dvd_iff.mpr
  intro l hl
  apply hP
  unfold power at hl
  have hsmall:48758*l<weight (d+e) i - weight e j:= by omega
  unfold weight at hweight hsmall
  omega
private def columnWeight {m n:ℕ} (j:Fin (m+n)) :ℕ :=
  j.addCases (fun j:Fin m=>weight Cj j) (fun j:Fin n=>weight Fw j)
private theorem cr3 {k :Type*} [CommRing k]
    (F G:k[X][X]) (m n:ℕ)
    (hF : ∀ i l:ℕ,7062*i+48758*l<Cj→(F.coeff i).coeff l=0)
    (hG : ∀ i l:ℕ,7062*i+48758*l<Fw→(G.coeff i).coeff l=0)
    (i j:Fin (m+n)) :
    (Polynomial.X:k[X])^power (weight (Cj+Fw) i - columnWeight j) ∣
      sylvester F G m n i j:= by
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester,Matrix.of_apply,Fin.addCases_left,columnWeight,Set.mem_Icc]
    split_ifs with h
    · simpa only [add_comm Fw Cj] using
        a2J G Fw Cj i j h.1 hG
    · exact dvd_zero _
  | right j =>
    simp only [sylvester,Matrix.of_apply,Fin.addCases_right,columnWeight,Set.mem_Icc]
    split_ifs with h
    · exact a2J F Cj Fw i j h.1 hF
    · exact dvd_zero _
private theorem b0v {k :Type*} [CommRing k] {N D:ℕ}
    (M:Matrix (Fin N) (Fin N) k[X]) (row col:Fin N→ℕ)
    (hM : ∀ i j,(Polynomial.X:k[X])^power (row i - col j)∣M i j)
    (hbudget: (∑ j,col j)+48758*D ≤(∑ i,row i)+48757) :
    (Polynomial.X:k[X])^D ∣M.det:= by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  let a :Fin N→ℕ:= fun j=>power (row (σ j) - col j)
  have hprod: (Polynomial.X:k[X])^(∑ j,a j) ∣ ∏ j,M (σ j) j:= by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _=>hM (σ j) j)
  have hsum: (∑ i,row i)≤(∑ j,col j)+48758*(∑ j,a j) := by
    rw [← Equiv.sum_comp σ row,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [a,power]
    omega
  have hD:D ≤ ∑ j,a j:= by omega
  exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hD).trans hprod) _
private theorem a8V {d t N :ℕ} (ht:t≤N) (hend:d≤7062*t)
    (hbefore : ∀ i<t,7062*i≤d) :
    (∑ i:Fin N,weight d i)=t*d - 7062*(t*(t - 1)/2) := by
  rw [Fin.sum_univ_eq_sum_range]
  have htrim: (∑ i∈Finset.range t,weight d i) = ∑ i∈Finset.range N,weight d i:= by
    apply Finset.sum_subset (Finset.range_mono ht)
    intro i _ hi
    simp only [Finset.mem_range,not_lt] at hi
    unfold weight
    omega
  rw [← htrim]
  have hsum: (∑ i∈Finset.range t,weight d i)+7062*(∑ i∈Finset.range t,i) =
      t*d:= by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    calc
      _ = ∑ _i∈Finset.range t,d:= by
        apply Finset.sum_congr rfl
        intro i hi
        have h:=hbefore i (Finset.mem_range.mp hi)
        unfold weight
        omega
      _ = _:= by simp [Nat.mul_comm]
  rw [Finset.sum_range_id] at hsum
  omega
private theorem bVz :
    (∑ j:Fin (40000+40000),columnWeight (m:=40000) (n:=40000) j)+48758*34529 ≤
      (∑ i:Fin (40000+40000),weight (Cj+Fw) i)+48757:= by
  have hF: (∑ i:Fin 40000,weight Cj i)=0x6d10b590:= by
    rw [a8V (t:=720) (by decide) (by decide)
      (by intro i hi; simp only [Cj]; omega)]
    decide
  have hG: (∑ i:Fin 40000,weight Fw i)=0x172ed44c:= by
    rw [a8V (t:=332) (by decide) (by decide)
      (by intro i hi; simp only [Fw]; omega)]
    decide
  have hFG: (∑ i:Fin (40000+40000),weight (Cj+Fw) i) =
      0xe89825aa := by
    rw [a8V (t:=1051) (by decide) (by decide)
      (by intro i hi; simp only [Cj,Fw]; omega)]
    decide
  rw [Fin.sum_univ_add,hFG]
  simp only [columnWeight,Fin.addCases_left,Fin.addCases_right,hF,hG]
  decide
private theorem cfo
    (F G:iP[X][X]) (z :iP) {m n D:ℕ} (hF:F.natDegree≤ m) (hG:G.natDegree≤n)
    (hFO : ∀ i l:ℕ,7062*i+48758*l<Cj →
      ((F.taylor (C z)).coeff i).coeff l=0)
    (hGO : ∀ i l:ℕ,7062*i+48758*l<Fw →
      ((G.taylor (C z)).coeff i).coeff l=0)
    (hbudget: (∑ j:Fin (m+n),columnWeight (m:=m) (n:=n) j)+48758*D ≤
      (∑ i:Fin (m+n),weight (Cj+Fw) i)+48757) :
    (Polynomial.X:iP[X])^D ∣resultant F G m n:= by
  rw [← cfq F G (C z) hF hG]
  unfold resultant
  exact b0v
    (sylvester (F.taylor (C z)) (G.taylor (C z)) m n)
    (fun i=>weight (Cj+Fw) i)
    (columnWeight (m:=m) (n:=n))
    (cr3 _ _ m n hFO hGO) hbudget
theorem b7Q (F G:iP[X][X]) (z :iP)
    (hF:F.natDegree≤40000) (hG:G.natDegree≤40000)
    (hFO : ∀ i j,7062*i+48758*j<Cj →
      ((F.taylor (Polynomial.C z)).coeff i).coeff j=0)
    (hGO : ∀ i j,7062*i+48758*j<Fw →
      ((G.taylor (Polynomial.C z)).coeff i).coeff j=0) :
    (Polynomial.X:iP[X])^34529∣Polynomial.resultant F G 40000 40000:= by
  exact cfo F G z (m:=40000) (n:=40000) (D:=34529)
    hF hG hFO hGO bVz
open private BZ bgD b7S caz from ProximityPrize.SubmissionLower.CS
set_option maxRecDepth 4000
private theorem br0 (F:ko) (z :iP) (y v :Fin 3→iP)
    (d:ℕ) (hF:NT F z y d) :
    ∀ i j,7062*i+48758*j<d →
      ((((qN F).map ((BZ v).comp (jA.translate y))).taylor (C z)).coeff i).coeff j=0:= by
  intro i j h
  change ((((qN F).map ((BZ v).comp (jA.translate y))).comp
    (Polynomial.X+C (C z))).coeff i).coeff j=0
  rw [b7S,coeff_map,bgD]
  suffices hc:MvPolynomial.homogeneousComponent j
      ((qN (jA.translate (ED z y) F)).coeff i)=0 by
    rw [hc,map_zero]
  apply MvPolynomial.homogeneousComponent_eq_zero'
  intro a ha hj
  have hmem:a.optionElim i∈(jA.translate (ED z y) F).support := by
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    exact ha
  have hb:=hF _ hmem
  have hweight:Dl (a.optionElim i)=7062*i+48758*j:= by
    change 7062*a.optionElim i none+48758*(a.optionElim i).some.degree= _
    rw [Finsupp.optionElim_apply_none,Finsupp.some_optionElim,hj]
  rw [hweight] at hb
  exact (Nat.not_lt_of_ge hb) h
private theorem b7P (F G:ko) (y v :Fin 3→iP) :
    resultant ((qN F).map ((BZ v).comp (jA.translate y)))
      ((qN G).map ((BZ v).comp (jA.translate y))) 40000 40000 =
        BZ v (jA.translate y (YI F G)) := by
  unfold YI
  rw [resultant_map_map,RingHom.comp_apply]
theorem aVW {F:ko} {z :iP} {y :Fin 3→iP}
    {d:ℕ} (a :ao[X]) (h:NT F z y d) :
    NT (pad F a) z y d:= by
  classical
  intro m hm
  rw [pad,map_mul] at hm
  obtain ⟨u,hu,v,_,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  exact (h u hu).trans (by rw [aOR]; exact Nat.le_add_right _ _)
theorem cfp (F G:ko) (z :iP)
    (y :Fin 3→iP) (hF: (qN F).natDegree≤40000)
    (hG: (qN G).natDegree≤40000) (h:aqw F G z y) :
    Qu (YI F G) y 34529:= by
  apply caz
  intro v
  rw [← b7P F G y v]
  exact b7Q _ _ z (natDegree_map_le.trans hF) (natDegree_map_le.trans hG)
    (br0 F z y v _ h.1) (br0 G z y v _ h.2)
end
end P6_6_4
end
section
set_option autoImplicit true
namespace qKVHaka
open aR (Shape)
open jA (jK Jn gY)
open NR (Bank ay8)
def apR (b:Bank) (F:jK) :Prop :=
  Jn b.box F∧gY F≤40000
def azR (a :Shape) :ℕ :=
  ∑ q∈Finset.range (a.b+1),(a.b+a.j - q)*ay8 a q*(40001+(a.b - q))
def cut:Bank→ℕ
  | .first=>P6_6_4.ajA
  | .second=>P6_6_4.E3
def aAv :Bank→ℕ
  | .first=>0x9075d5531df4
  | .second=>P6_6_4.RF
theorem bZs (b:Bank) :131071*b.box.b≤ cut b+1 := by
  cases b <;> decide
def aEw (b:Bank) :ℕ:=cut b+1 - 131071*b.box.b
def width (b:Bank) (h q k l:ℕ) :ℕ :=
  aEw b+131071*(b.box.b - q)+(l+2*k)+(2300+(b.box.b - q))*h
open aw8 (ama a1U)
open Finset
open scoped BigOperators
open private ajS a5Q slice auf iL extra cT3 bVk from ProximityPrize.SubmissionLower.A2
private def az0 (b:Bank) :ℕ:=ajS b.box.b (aEw b) 1 131071 0
private theorem djv (b:Bank) (h:ℕ) :
    ama b.box.b (width b h)=az0 b+iL b.box.b*h:= by
  simp only [width,az0,ajS,iL,ama,sum_mul,← sum_add_distrib]
  refine sum_congr rfl fun q _=>sum_congr rfl fun k _=>sum_congr rfl fun l _ => ?_
  ring
private theorem c4C (b:Bank) :azR b.box=40001*iL b.box.b+extra b.box.b:= by
  have hb:b.box=⟨b.box.b,2300,1150⟩:= by cases b <;> rfl
  have hgrade (q:ℕ) :ay8 b.box q=ay8 ⟨b.box.b,2300,1150⟩ q :=
    congrArg (fun a=>ay8 a q) hb
  calc
    _=ama b.box.b (fun q _ _=>(2300+(b.box.b - q))*(40001+(b.box.b - q))) := by
      rw [cT3,azR]
      apply sum_congr rfl
      intro q hq
      have hq' := mem_range.mp hq
      have he :b.box.b+b.box.j - q=2300+(b.box.b - q) := by
        rw [a1U]
        omega
      rw [hgrade,he]
      ring
    _ = _:= by
      simp only [iL,extra,ajS,ama,mul_sum,← sum_add_distrib]
      refine sum_congr rfl fun q _=>sum_congr rfl fun k _=>sum_congr rfl fun l _ => ?_
      ring
local notation "slice₁" => slice 6789 4213788 1 131071 0
private theorem ebK:az0 .first=0x2705febfb16331ec:= by
  change ajS 6789 4213788 1 131071 0= _
  refine a5Q 6789 4213788 1 131071 0 _ (by decide) ?_
  change auf (slice₁) 1151= _
  have h0:slice₁ 0=0x9d395960ab20df0:= by decide
  have h1 :slice₁ 1=0x9d156b65bcb13b0:= by decide
  have h2 :slice₁ 2=0x9cf17e0c7035fe0:= by decide
  have h3:slice₁ 3=0x9ccd9154a1af5e0:= by decide
  have h4 :slice₁ 4=0x9ca9a53e2d1d910 := by decide
  unfold auf
  rw [h0,h1,h2,h3,h4]
  decide
local notation "slice₂" => slice 6820 2890499 1 131071 0
private theorem gnh:az0 .second=0x274f6fa506a2371b:= by
  change ajS 6820 2890499 1 131071 0= _
  refine a5Q 6820 2890499 1 131071 0 _ (by decide) ?_
  change auf (slice₂) 1151= _
  have h0:slice₂ 0=0x9e5f3d8b4936650:= by decide
  have h1 :slice₂ 1=0x9e3b0e2b7255520:= by decide
  have h2 :slice₂ 2=0x9e16df6d3d644a0:= by decide
  have h3:slice₂ 3=0x9df2b1508663830:= by decide
  have h4 :slice₂ 4=0x9dce83d52953330:= by decide
  unfold auf
  rw [h0,h1,h2,h3,h4]
  decide
private theorem Ly (b:Bank) :
    aAv b+262144*(40001*b.avF)+2354*extra b.box.b ≤
      40001*az0 b:= by
  obtain ⟨_,_,hfirst,hsecond⟩:=bVk
  cases b
  · rw [ebK,show extra Bank.first.box.b= _ from hfirst]
    exact (by decide : (0x9075d5531df4 :ℕ)+262144*(40001*0x9bab8f5dfb7) +
      2354*0x1cc973f372d9cdc≤40001*0x2705febfb16331ec)
  · rw [gnh,show extra Bank.second.box.b= _ from hsecond]
    exact (by decide : (0x2c77ff4cc20b4ad69d:ℕ)+262144*(40001*0x9bac59312df) +
      2354*0x1d32fca954a0ef7≤40001*0x274f6fa506a2371b)
theorem budget (b:Bank) (h:ℕ) (hh:h≤2354) :
    aAv b+262144*(40001*b.avF)+h*azR b.box ≤
      40001*ama b.box.b (width b h) := by
  have he :=Ly b
  have hm:=Nat.mul_le_mul_right (extra b.box.b) hh
  rw [c4C,djv,Nat.mul_add,Nat.mul_add]
  have hc:h*(40001*iL b.box.b)=40001*(iL b.box.b*h) := by ring
  omega
end qKVHaka
end
section
set_option autoImplicit true
namespace qIkXmGe
noncomputable section
open K1 aR
open jA hiding Ga
open P6_6_4 (Ga)
open bAl (bxL)
open acZ (OV bI3 a88)
open scoped BigOperators
def am0 (R:ko) :Prop :=
  Jn Ga R∧gY R≤40000
def bBt:Submodule iP ko :=
  OV Ga ⊓ MvPolynomial.restrictWeightedDegree (Pi.single (none :mA) 1) 40000
theorem bsu {R:ko} : R∈bBt↔am0 R:= by
  classical
  simp only [bBt,Submodule.mem_inf,bI3,am0,
    MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
    MvPolynomial.weightedTotalDegree_piSingle,gY]
theorem ctu {F:jK} (hc:Jn Ga F)
    (hs :gY F≤40000) :am0 (bC F) :=
  ⟨a88 hc,(bxL F).trans_le hs⟩
def avl {Γ s} (w:I→K) (P:jF Γ s) (L:kH P)
    (t:ℕ) :Submodule iP ko :=
  Submodule.span iP {R | ∃ F,P6_6_4.Source w P L Ga t F∧bC F=R}
theorem b7k {Γ s} {w:I→K} {P:jF Γ s} {L:kH P}
    {t:ℕ} {R:ko} (hR:R∈avl w P L t) :am0 R:= by
  apply bsu.mp
  apply (Submodule.span_le.mpr ?_) hR
  rintro _ ⟨F,hF,rfl⟩
  exact bsu.mpr (ctu hF.1.1 hF.2)
def Vx (a :ℕ) :ℕ:=40001*5671*(1151-a)^2
def amz (moving:Bool) :ℕ:=if moving then 7062 else 48758
def aDA (e t:ℕ) :ℕ:=1+(P6_6_4.E3 - t)/e
end
end qIkXmGe
end
section
set_option autoImplicit true
namespace P6_7_3
noncomputable section
open Polynomial
open P6 (e9 I K p twist jG gJ dw)
open P5_7 (Qn midAgreement)
open P5_7_1 (Ls TopRow TopCaps atTop topConjugate topLift)
open cu (FX Shape Jet vP ku triangle j9)
open DP (jF zG aKF ad0 VY)
open gT (Ambient IZ)
open pI (xN)
open qQ (zI N5 oU)
open scoped BigOperators Classical
abbrev lo:=gJ.graph.lo
abbrev hi:=gJ.graph.hi
abbrev degree :=131071+hi
abbrev introFee :ℕ:=0x46c92041c1d74
abbrev prefixFee :ℕ:=0x31c42a8f2b0c2a0
abbrev retainedFee :ℕ:=0xbcab0a6ad19bc
structure Input where
  u:e9
  del:Finset I
  M:jG u del
  Γ:Finset K
  F:P1.bje dw M Γ
  kA:Qn lo hi M.iF
  noShift:M.shift∉Γ
  H :cu.L[X]
  bY:P6_7.YQ M F H
abbrev Input.h (x :Input) :=x.M.iF.toNat
abbrev Input.word (x :Input) (i:I) :cu.L:=algebraMap K cu.L (x.M.word i)
structure Poles (x :Input) where
  D:jF x.h
  crt:zG D
  first:D.block 0=x.H
  second:D.block 1=x.H.map (frobenius cu.L p)
  offset :D.offset = ![j9 x.M.Q,(j9 x.M.Q).map (frobenius cu.L p)]
  constant:D.constant = ![j9 (x.M.factor*x.M.A₀),
    (j9 (x.M.factor*x.M.A₀)).map (frobenius cu.L p)]
  slope :D.slope = ![j9 (x.M.factor*x.M.A₁),
    (j9 (x.M.factor*x.M.A₁)).map (frobenius cu.L p)]
  nodes : ∀ i j,(D.block i).eval (ad0 j)≠0
  marks : ∀ γ∈x.Γ,aKF D (x.M.label γ) (x.F.scalar γ)
abbrev Poles.rows {x :Input} (P:Poles x) :vP:=VY P.crt x.word
def stages :List Ls :=
  [⟨0,⟨83,115,25,1025⟩,⟨812,1131,235,42181⟩⟩,
   ⟨1,⟨83,115,25,1422⟩,⟨880,1226,255,46350⟩⟩,
   ⟨2,⟨121,168,38,967⟩,⟨982,1368,284,50558⟩⟩,
   ⟨4,⟨106,147,32,1754⟩,⟨1139,1588,330,58763⟩⟩,
   ⟨6,⟨98,136,30,26346⟩,⟨1303,1816,377,67265⟩⟩,
   ⟨10,⟨123,171,38,20020⟩,⟨1590,2217,461,83937⟩⟩,
   ⟨16,⟨165,229,50,10868⟩,⟨2164,3017,627,108324⟩⟩,
   ⟨24,⟨277,384,86,3307⟩,⟨2287,3189,663,154367⟩⟩]
def introductions :List (ℕ×Shape) :=
  [(5,⟨115,159,35,1798⟩),(6,⟨103,143,31,5971⟩),(10,⟨137,190,41,3982⟩),
   (8,⟨151,210,46,1739⟩),(13,⟨200,277,61,2077⟩),(13,⟨158,218,48,4435⟩),
   (16,⟨200,277,61,2963⟩),(20,⟨207,287,63,5245⟩),(20,⟨256,354,81,2731⟩),
   (1,⟨83,115,25,1422⟩),(4,⟨106,147,32,1754⟩),(24,⟨235,327,71,5959⟩),
   (24,⟨233,324,70,6401⟩)]
def movingOrder :List ℕ:=[2,4,5,6]
abbrev anchor :=stages[0]
abbrev IntroIndex :=Fin (introductions.length+1)
abbrev afa :=Fin stages.length
def gw:List (ℕ×ℕ) :=
  [(3611,162841),(3595,163174),(3579,163552),(3563,163977),(3546,164311),(3530,164766),(3513,165204),(3496,165626),
   (3479,166109),(3461,166559),(3444,167096),(3426,167631),(3408,168177),(3389,168710),(3370,169288),(3351,169914),
   (3332,170607),(3312,171271),(3292,172009),(3272,172819),(3251,173619),(3229,174445),(3207,175333),(3185,176347),
   (3162,177402),(3139,178584),(3115,179826),(3090,181158),(3064,182602),(3037,184193)] ++
  [3010,2982,2953,2923,2893,2861,2829,2795,2761,2725,2687,2648,2608,2565,
   2521,2476,2428,2379,2327,2274,2219,2163,2104,2043,1981,1916,1850,1782,
   1712,1640,1566,1491,1414,1334,1253,1171,1086,1000,911,821,730,636,
   541,444,346,245,143,40].map (fun v=>(v,185000))
abbrev aKj:=Fin gw.length
abbrev Test:=Option aKj
abbrev cV (i:aKj) :=gw.get i
def terminal:Shape :=⟨2100,2927,619,185000⟩
def Lc:Test→Shape
  | none=>terminal
  | some i => { terminal with U:=min (cV i).2 terminal.U }
def ordinateThreshold:Test→ℕ
  | none=>gw.length+1
  | some i=>i.val+1
def apo:Test→ℕ
  | none=>0
  | some i=>(cV i).1+1
def cutoff (s :Shape) :ℕ:=s.m*dw - 1
def buffer (h r :ℕ) (s :Shape) :=cutoff s - 2*h*r
def j3 (h:ℕ) (s :Shape) :ℕ :=
  triangle s.U*0xf8eab0e80000+2*h*((s.U+1)*0x1cccacb1996 - 0x47c4a7d1ca8f0)
def bbk (h:ℕ) (s :Shape) (rows :vP) :Prop :=
  triangle s.U*ku s (fun q j=>s.m*dw+j-q*(131071-h)) ≤
    j3 h s + ∑ W∈Finset.range (s.m*dw),Module.finrank FX (rows s W)
abbrev ZN :=P5_7_1.jointGainAt dw
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
structure TopPair (x :Input) where
  cheap:TopRow
  strong:TopRow
  cheap_ne :cheap≠0
  strong_ne :strong≠0
  cheap_caps :TopCaps x.h 64 87 27 12 640 cheap
  strong_caps :TopCaps x.h 120 164 50 19 3037 strong
  no_moving : ∀ Q:MvPolynomial (Fin 4) FX,Irreducible Q →
    0<Q.degreeOf 3→Q∣topLift cheap→Q∣topLift strong→Q.degreeOf 0=0
  necessary : ∀ γ∈x.Γ,
    atTop cheap (x.M.label γ) (x.F.scalar γ)=0 ∧
    atTop strong (x.M.label γ) (x.F.scalar γ)=0 ∧
    atTop (topConjugate cheap) (twist (x.M.label γ)) (x.F.scalar γ)=0 ∧
    atTop (topConjugate strong) (twist (x.M.label γ)) (x.F.scalar γ)=0
abbrev wD:=P5_7_1.wD
abbrev bgK:=P5_7_1.bgK
abbrev aOm:=P5_7_1.aOm
def introCap (i:ℕ) :Fin 3→ℕ :=
  ((introductions.take i).foldl (fun v (r,s) j=>min (v j) (bgK s j/(r+1)))
    (bgK anchor.free))
def lineFee (b j u:ℕ) :ℕ :=
  let t:=2*degree-3
  let a :=1+t*(b-1)
  let v :=min a (t*(j-1)+degree)
  let U:=t*u
  let kK:=u*(2*a*v-v*v)+2*U*(b*v+j*(a-v))
  let other :=u*(2*a+v)+U*(2*b+j)+b*v+j*a+u+b+j
  let q:=midAgreement-degree
  (2*(P6.blockLength-midAgreement)*(kK+other)+q-1)/q+b+u+1
structure OriginCover (x :Input) (anchorRow :Jet) where
  factors :Finset Jet
  origin :Jet→ IntroIndex
  cut:Jet→Jet
  line :Jet→Bool
  lineMarks :Jet→Finset K
  parents :Jet→Finset (Ideal Ambient)
  gH :Finset K
  paid_bound:gH.card≤ introFee
  nested : ∀ i≤ introductions.length,∀ j,
    (∑ f∈factors.filter (fun f=>i≤(origin f).val),wD f j)≤ introCap i j
  proper : ∀ f∈factors,Irreducible f∧f∣anchorRow ∧ ¬ f∣cut f
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
def agA (rows :vP) (s :Shape) (q:zI) :Prop :=
  ∀ P∈rows s (cutoff s),P∈q.asIdeal
structure Prefix (x :Input) (rows :vP) where
  book :Finset K
  book_bound:book.card≤prefixFee
  parents :Finset zI
  geometric : ∀ q∈parents,N5 q
  terminal_pass : ∀ q∈parents,agA rows terminal q
  Eh : ∀ γ∈x.Γ,γ∈book ∨ ∃ q∈parents,P6_7.axy x.M x.F q γ
end
end P6_7_3
end
