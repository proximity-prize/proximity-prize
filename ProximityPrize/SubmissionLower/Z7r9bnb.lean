import ProximityPrize.SubmissionLower.Z3aw2hc
import ProximityPrize.SubmissionLower.Z7T9FDe
import ProximityPrize.SubmissionLower.ZEe4bHc
set_option Elab.async false
section
set_option autoImplicit true
namespace qoRVxvd
open aR (ao)
open scoped BigOperators Polynomial
noncomputable section
local notation "T" => (Polynomial.X:ao[X])
private def probe :Poly →ₐ[ao] ao[X] :=
  MvPolynomial.aeval ![1+T^13,1,T^14]
private theorem probe_witness (q n i h:ℕ) (hi:i+(h-n)≤n) :
    ∃ p:ao[X],p.coeff 0=1∧probe (witness q n i h)=T^(13*n+i)*p:= by
  let r :=h-n
  let s :=r₁ q n i h
  let a :=a₀ q n i h
  refine ⟨(1+T^13)^a*(1+T)^s*(1+T+T^14)^(r-s),?_,?_⟩
  · change Polynomial.constantCoeff _=1
    simp only [map_mul,map_pow,map_add,map_one]
    simp
  have hA:probe (MvPolynomial.X 0)=1+T^13:= by simp [probe]
  have hV:probe (MvPolynomial.X 1)=1 := by simp [probe]
  have hW:probe (MvPolynomial.X 2)=T^14 := by simp [probe]
  have hD: (1+T^13)-1=T^13:= by ring
  have hS:T^13+T^14=T^13*(1+T) := by ring
  have hU:1*T^13+(1+T^13)*T^14=T^13*(1+T+T^14) := by ring
  have hs :s≤ r :=min_le_left _ _
  have he :13*(n-i-r)+14*i+13*s+13*(r-s)=13*n+i:= by omega
  change probe (witness q n i h)=T^(13*n+i)*_
  simp only [witness,map_mul,map_pow,map_add,map_sub,hA,hV,hW,hD,hS,hU]
  rw [← he]
  simp only [one_pow,one_mul,mul_pow,← pow_mul,pow_add]
  ring
private theorem independent_of_coeff {ι:Type} {v :ι→ao[X]} {k :ι→ℕ}
    (hk :Function.Injective k) (hv : ∀ i,(v i).coeff (k i)=1)
    (hz : ∀ i j:ι,k i<k j→(v j).coeff (k i)=0) :
    LinearIndependent ao v := by
  classical
  rw [linearIndependent_iff']
  intro s g he i hi
  by_contra hgi
  obtain ⟨j,hj,hm⟩:=(s.filter fun j=>g j≠0).exists_min_image k
    ⟨i,Finset.mem_filter.mpr ⟨hi,hgi⟩⟩
  have hj' := Finset.mem_filter.mp hj
  have hc:=congrArg (Polynomial.lcoeff ao (k j)) he
  simp only [map_sum,map_smul,map_zero,Polynomial.lcoeff_apply] at hc
  rw [Finset.sum_eq_single_of_mem j hj'.1] at hc
  · exact hj'.2 (by simpa [hv j] using hc)
  · intro l hl hne
    by_cases hgl:g l=0
    · simp [hgl]
    · have hlt:=(hm l (Finset.mem_filter.mpr ⟨hl,hgl⟩)).lt_of_ne (hk.ne hne.symm)
      simp [hz j l hlt]
theorem witnessIndependent {q d h:ℕ} (hq:q≤27) (hd:d≤q) :
    LinearIndependent ao
      (fun j:Index q d h=>witness q j.1 (lo q d j.1+j.2.val) h) := by
  let i (j:Index q d h) :=lo q d j.1+j.2.val
  let k (j:Index q d h) :=13*j.1.val+i j
  have hi (j:Index q d h) :i j+(h-j.1.val)≤j.1.val∧i j≤12 := by
    have hj:=(witness_bounds hq hd j).1
    change i j+(h-j.1.val)<stop j.1 at hj
    unfold stop at hj
    omega
  have hk :Function.Injective k := by
    intro j l hkl
    have hj:=(hi j).2
    have hl:=(hi l).2
    change 13*j.1.val+i j=13*l.1.val+i l at hkl
    have he :j.1=l.1 :=Fin.ext (by omega)
    have hi' : i j=i l:= by
      have :=congrArg Fin.val he
      omega
    refine Sigma.ext he ((Fin.heq_ext_iff
      (congrArg (fun n:jJ q d=>width q d n - Bp q d h n) he)).2 ?_)
    have hl' := congrArg (fun n:jJ q d=>lo q d n) he
    dsimp [i] at hi'
    omega
  apply LinearIndependent.of_comp probe.toLinearMap
  apply independent_of_coeff (k :=k) hk
  · intro j
    obtain ⟨p,hp,he⟩:=probe_witness q j.1 (i j) h (hi j).1
    change (probe (witness q j.1 (i j) h)).coeff (k j)=1
    rw [he,Polynomial.coeff_X_pow_mul']
    change (if k j≤k j then p.coeff (k j-k j) else 0)=1
    simp [hp]
  · intro j l hj
    obtain ⟨p,_,he⟩:=probe_witness q l.1 (i l) h (hi l).1
    change (probe (witness q l.1 (i l) h)).coeff (k j)=0
    rw [he,Polynomial.coeff_X_pow_mul']
    exact ite_eq_right (not_le_of_gt hj)
end
end qoRVxvd
end
section
set_option autoImplicit true
set_option maxHeartbeats 500000
namespace qoRVxvd
open aR (ao)
open MvPolynomial
open scoped BigOperators
noncomputable section
local notation "A" => (MvPolynomial.X 0:Poly)
local notation "V" => (MvPolynomial.X 1 :Poly)
local notation "W" => (MvPolynomial.X 2 :Poly)
local notation "O" => restrictWeightedOrder (R:=ao)
local notation "x" => (MvPolynomial.X 1 :Target)
local notation "y" => (MvPolynomial.X 0:Target)
private theorem aeT (q n i h:ℕ) (v :Fin 3→ℕ) :
    let r :=h-n
    let s :=r₁ q n i h
    let a :=a₀ q n i h
    let m:=min (v 0) (v 1)
    witness q n i h∈O v
      ((q-n-a-(r-s))*v 1+(n-i-r)*m+i*v 2+a*v 0 +
        s*min m (v 2)+(r-s)*min (v 1+m) (v 0+v 2)) := by
  dsimp only
  have hx (j:Fin 3) :MvPolynomial.X j∈O v (v j) :=
    X_mem_restrictWeightedOrder v j le_rfl
  have hd:A-V∈O v (min (v 0) (v 1)) :=
    sub_mem (restrictWeightedOrder_anti _ (min_le_left _ _) (hx 0))
      (restrictWeightedOrder_anti _ (min_le_right _ _) (hx 1))
  have hs :A-V+W∈O v (min (min (v 0) (v 1)) (v 2)) :=
    add_mem (restrictWeightedOrder_anti _ (min_le_left _ _) hd)
      (restrictWeightedOrder_anti _ (min_le_right _ _) (hx 2))
  have ht:V*(A-V)+A*W∈O v (min (v 1+min (v 0) (v 1)) (v 0+v 2)) :=
    add_mem (restrictWeightedOrder_anti _ (min_le_left _ _) (mul_mem_restrictWeightedOrder (hx 1) hd))
      (restrictWeightedOrder_anti _ (min_le_right _ _) (mul_mem_restrictWeightedOrder (hx 0) (hx 2)))
  unfold witness
  exact mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder
      (mul_mem_restrictWeightedOrder
        (mul_mem_restrictWeightedOrder
          (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder (hx 1) _)
            (pow_mem_restrictWeightedOrder hd _)) (pow_mem_restrictWeightedOrder (hx 2) _))
        (pow_mem_restrictWeightedOrder (hx 0) _)) (pow_mem_restrictWeightedOrder hs _))
    (pow_mem_restrictWeightedOrder ht _)
private theorem source_degree (q n i h:ℕ) (hi:i+(h-n)≤n)
    (hq:n+a₀ q n i h+(h-n-r₁ q n i h)≤q) :
    (witness q n i h).IsWeightedHomogeneous (fun _=>(1 :ℕ)) q:= by
  have hx (j:Fin 3) : (MvPolynomial.X j:Poly).IsWeightedHomogeneous (fun _=>(1 :ℕ)) 1 :=
    isWeightedHomogeneous_X ao _ j
  have hd:=(hx 0).sub (hx 1)
  have hf :=((hx 1).mul hd).add ((hx 0).mul (hx 2))
  have hp:=((((((hx 1).pow (q-n-a₀ q n i h-(h-n-r₁ q n i h))).mul
    (hd.pow (n-i-(h-n)))).mul ((hx 2).pow i)).mul ((hx 0).pow (a₀ q n i h))).mul
    ((hd.add (hx 2)).pow (r₁ q n i h))).mul (hf.pow (h-n-r₁ q n i h))
  simp only [Nat.nsmul_eq_mul,Nat.mul_one] at hp
  have hr :r₁ q n i h≤h-n:=min_le_left _ _
  convert hp using 1 <;> first | rfl | omega
theorem witnessSource {q d h:ℕ} (hq:q≤27) (hd:d≤q) (j:Index q d h) :
    witness q j.1 (lo q d j.1+j.2.val) h∈Source q d:= by
  obtain ⟨hi,hqa,hw⟩:=witness_bounds hq hd j
  let n:=j.1.val
  let i:=lo q d n+j.2.val
  have hi' : i+(h-n)≤n∧i+(h-n)≤12 := by
    change i+(h-n)<stop n at hi
    unfold stop at hi
    omega
  have hg:=source_degree q n i h hi'.1 hqa
  have h₁:=aeT q n i h (![0,1,1] :Fin 3→ℕ)
  have h₂:=aeT q n i h (![2,1,0] :Fin 3→ℕ)
  have h₃:=aeT q n i h (![1,1,0] :Fin 3→ℕ)
  change n+a₀ q n i h+(h-n-r₁ q n i h)≤q at hqa
  change n+a₀ q n i h≤q-d+i at hw
  refine (mem_restrictSupport_iff ao).mpr fun e he => ?_
  have e₀:=hg (mem_support_iff.mp he)
  have e₁:=mem_restrictWeightedOrder.mp h₁ e he
  have e₂:=mem_restrictWeightedOrder.mp h₂ e he
  have e₃:=mem_restrictWeightedOrder.mp h₃ e he
  change e 0+e 1+e 2=q∧d≤e 1+e 2∧e 1+2*e 2≤27∧e 2≤12
  simp [Finsupp.weight_eq_sum,Fin.sum_univ_three,smul_eq_mul,Nat.mul_comm] at e₀ e₁ e₂ e₃
  have ha :i+r₁ q n i h≤(27-q)+a₀ q n i h:= by unfold a₀ α; omega
  have hr :r₁ q n i h≤h-n:=min_le_left _ _
  omega
private theorem chart_witness (q n i h:ℕ) :
    bY (witness q n i h) =
      (1+x)^(q-n-a₀ q n i h-(h-n-r₁ q n i h)) *
      (-x)^(n-i-(h-n))*(x+y)^i*y^(r₁ q n i h)*(y-x^2)^(h-n-r₁ q n i h) := by
  have ha :bY A=1 := by simp [bY]
  have hv :bY V=1+x := by simp [bY]
  have hw:bY W=x+y := by simp [bY]
  have hd: (1 :Target)-(1+x) = -x := by ring
  have hs : -x+(x+y)=y := by ring
  have hp: (1+x)*(-x)+1*(x+y)=y-x^2 := by ring
  simp only [witness,map_mul,map_pow,map_add,map_sub,ha,hv,hw,hp,hs,hd,one_pow,mul_one]
theorem witnessOrder {q d h:ℕ} (hq:q≤27) (hd:d≤q) (j:Index q d h) :
    bY (witness q j.1 (lo q d j.1+j.2.val) h)∈O wt h:= by
  let n:=j.1.val
  let i:=lo q d n+j.2.val
  have hi:=(witness_bounds hq hd j).1
  change i+(h-n)<stop n at hi
  unfold stop at hi
  have hr :r₁ q n i h≤h-n:=min_le_left _ _
  have hx :x∈O wt 1 :=X_mem_restrictWeightedOrder _ _ (by decide)
  have hy :y∈O wt 2 :=X_mem_restrictWeightedOrder _ _ (by decide)
  have hv :1+x∈O wt 0:= by simp
  have hw:x+y∈O wt 1 :=add_mem hx (restrictWeightedOrder_anti _ (by decide) hy)
  have hz :y-x^2∈O wt 2 :=sub_mem hy (pow_mem_restrictWeightedOrder hx 2)
  rw [chart_witness]
  apply restrictWeightedOrder_anti wt _ (mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder
      (mul_mem_restrictWeightedOrder
        (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder hv _)
          (pow_mem_restrictWeightedOrder (neg_mem hx) _)) (pow_mem_restrictWeightedOrder hw _))
      (pow_mem_restrictWeightedOrder hy _)) (pow_mem_restrictWeightedOrder hz _))
  change h≤_ *0+(n-i-(h-n))*1+i*1+r₁ q n i h*2+(h-n-r₁ q n i h)*2
  omega
end
end qoRVxvd
end
section
set_option autoImplicit true
namespace qYzmxYc
open Finset
open aR (Shape)
open NR (ay8)
open qlc9qed (Bank)

open scoped BigOperators
private theorem tops_stable (a :Shape) {q:ℕ} (hq:a.j≤q) :
    tops a q=tops a a.j:= by
  unfold tops
  omega
private theorem mids_stable (a :Shape) {q c:ℕ} (hq:a.j≤q)
    (hc:c∈range (tops a a.j)) :mids a q c=mids a a.j c:= by
  have hc:=mem_range.mp hc
  unfold mids tops at *
  omega
private theorem stable_sum (a :Shape) {q:ℕ} (hq:a.j≤q)
    (f :ℕ→ℕ→ℕ) :
    (∑ c∈range (tops a q),f c (mids a q c)) =
      ∑ c∈range (tops a a.j),f c (mids a a.j c) := by
  rw [tops_stable a hq]
  exact sum_congr rfl fun c hc=>congrArg (f c) (mids_stable a hq hc)
private theorem cols_zero (a :Shape) (k :ℕ) (hk :a.j<k) :
    cols a a.j k=0:= by
  apply sum_eq_zero
  intro c hc
  have hc:=mem_range.mp hc
  unfold tops at hc
  unfold mids
  omega
private theorem partial_stable (a :Shape) {q:ℕ} (hq:a.j≤q) :
    partialDebit a q=partialDebit a a.j:= by
  unfold partialDebit
  have hc (k) :cols a q k=cols a a.j k :=
    stable_sum a hq (fun c n=>n-(k - c))
  have hr (d) :rows a q d=rows a a.j d :=
    stable_sum a hq (fun c n=>min n (d - 2*c))
  simp only [hc,hr]
  rw [show range q=range (q-a.j+a.j) by rw [Nat.sub_add_cancel hq],sum_range_add]
  have hz : (∑ w∈range (q-a.j),∑ d∈range a.j,
      min (cols a a.j (q - w)) (rows a a.j (a.j - d)))=0:= by
    apply sum_eq_zero
    intro w hw
    have hh:=mem_range.mp hw
    simp [cols_zero a (q - w) (by omega)]
  change _ = ∑ w∈range a.j,∑ d∈range a.j,
    min (cols a a.j (a.j - w)) (rows a a.j (a.j - d))
  rw [hz,zero_add]
  apply sum_congr rfl
  intro w hw
  have hw:=mem_range.mp hw
  rw [show q-(q-a.j+w)=a.j - w by omega]
private abbrev box :Shape :=Bank.strong.box
private def stable (q:ℕ) :ℕ :=
  (3202 - 2*q)*((214 - q)*640)+(16000*(164 - q)+594590)+364568
private theorem stable_eq (q:ℕ) (hq:50≤q) :j3 box 3037 q=stable q:= by
  change box.j≤q at hq
  unfold j3
  rw [partial_stable box hq]
  have ht:ay8 box q=640:= by
    unfold ay8
    exact (stable_sum box hq (fun _ n=>n)).trans (by rfl)
  rw [ht]
  have hm:reflected box q=16000*(164 - q)+594590:= by
    unfold reflected
    rw [stable_sum box hq (fun c n =>
      ∑ b∈range n,(b+c)*(box.b - q+(b+2*c)))]
    simp only [Nat.mul_add,sum_add_distrib,← sum_mul]
    rfl
  rw [hm,show partialDebit box box.j=364568 by rfl]
  rfl
private def ay (f :ℕ→ℕ) :ℕ→List ℕ→Prop
  | _,[]=>True
  | i,x :: xs=>f i=x∧ay f (i+1) xs
private theorem checked_sum (f :ℕ→ℕ) (i:ℕ) (xs :List ℕ) (h:ay f i xs) :
    (∑ j∈range xs.length,f (i+j))=xs.sum:= by
  induction xs generalizing i with
  | nil=>rfl
  | cons x xs ih =>
    rw [show (x :: xs).length=1 + xs.length by simp [Nat.add_comm],sum_range_add]
    simp only [sum_range_one,Nat.add_zero,List.sum_cons]
    rw [h.1,← ih _ h.2]
    simp only [Nat.add_assoc]
set_option maxRecDepth 12000
set_option maxHeartbeats 1700000
private theorem zLw0 :j3 box 3037 0=685228:= by rfl
private theorem zLw1 :j3 box 3037 1=2045228:= by rfl
private theorem zLw2 :j3 box 3037 2=4069562:= by rfl
private theorem zLw3 :j3 box 3037 3=6747811:= by rfl
private theorem zLw4 :j3 box 3037 4=10069573:= by rfl
private theorem zLw5 :j3 box 3037 5=14024465:= by rfl
private theorem zLw6 :j3 box 3037 6=18602121:= by rfl
private theorem zLw7 :j3 box 3037 7=23792195:= by rfl
private theorem zLw8 :j3 box 3037 8=29584358:= by rfl
private theorem zLw9 :j3 box 3037 9=35968298:= by rfl
private theorem zLw10 :j3 box 3037 10=42933724:= by rfl
private theorem zLw11 :j3 box 3037 11=50470360:= by rfl
private theorem zLw12 :j3 box 3037 12=58567951:= by rfl
private theorem zLw13 :j3 box 3037 13=67216256:= by rfl
private theorem zLw14 :j3 box 3037 14=76405059:= by rfl
private theorem zLw15 :j3 box 3037 15=86124154:= by rfl
private theorem zLw16 :j3 box 3037 16=96363359:= by rfl
private theorem zLw17 :j3 box 3037 17=0x662683d:= by rfl
private theorem zLw18 :j3 box 3037 18=0x70e0d6f:= by rfl
private theorem zLw19 :j3 box 3037 19=0x7c12b65:= by rfl
private theorem zLw20 :j3 box 3037 20=0x8722e1c:= by rfl
private theorem zLw21 :j3 box 3037 21=0x9211670:= by rfl
private theorem zLw22 :j3 box 3037 22=0x9cde536:= by rfl
private theorem zLw23 :j3 box 3037 23=0xa789b3b:= by rfl
private theorem zLw24 :j3 box 3037 24=0xb21394e:= by rfl
private theorem zLw25 :j3 box 3037 25=0xbc7c039:= by rfl
private theorem zLw26 :j3 box 3037 26=0xc6c30c9:= by rfl
private theorem zLw27 :j3 box 3037 27=0xd0e8bc7:= by rfl
private theorem zLw28 :j3 box 3037 28=0xdaed1fc:= by rfl
private theorem zLw29 :j3 box 3037 29=0xe4d0432:= by rfl
private theorem zLw30 :j3 box 3037 30=0xee92331:= by rfl
private theorem zLw31 :j3 box 3037 31=0xf832fc1:= by rfl
private theorem zLw32 :j3 box 3037 32=0x10125aba:= by rfl
private theorem zLw33 :j3 box 3037 33=0x1096cce8:= by rfl
private theorem zLw34 :j3 box 3037 34=0x1110aef6:= by rfl
private theorem zLw35 :j3 box 3037 35=0x1180297b:= by rfl
private theorem zLw36 :j3 box 3037 36=0x11e564e4:= by rfl
private theorem zLw37 :j3 box 3037 37=0x1240898e:= by rfl
private theorem zLw38 :j3 box 3037 38=0x1291bfd6:= by rfl
private theorem zLw39 :j3 box 3037 39=0x12d92ffc:= by rfl
private theorem zLw40 :j3 box 3037 40=0x1317020c:= by rfl
private theorem zLw41 :j3 box 3037 41=0x134b5e2c:= by rfl
private theorem zLw42 :j3 box 3037 42=0x13766c42:= by rfl
private theorem zLw43 :j3 box 3037 43=0x13985449:= by rfl
private theorem zLw44 :j3 box 3037 44=0x13b13dec:= by rfl
private theorem zLw45 :j3 box 3037 45=0x13c150f9:= by rfl
private theorem zLw46 :j3 box 3037 46=0x13c8b50d:= by rfl
private theorem zLw47 :j3 box 3037 47=0x13c79194:= by rfl
private theorem zLw48 :j3 box 3037 48=0x13be0e02:= by rfl
private theorem zLw49 :j3 box 3037 49=0x13ac51a9:= by rfl
private theorem low: (∑ q∈range 50,j3 box 3037 q)=0x21baceb56:= by
  let xs :List ℕ:=[
    685228,2045228,4069562,6747811,10069573,14024465,18602121, 23792195,
    29584358,35968298,42933724,50470360,58567951,67216256,76405059,86124154,
    96363359,0x662683d,0x70e0d6f,0x7c12b65,0x8722e1c,0x9211670,0x9cde536,0xa789b3b,
    0xb21394e,0xbc7c039,0xc6c30c9,0xd0e8bc7,0xdaed1fc,0xe4d0432,0xee92331,0xf832fc1,
    0x10125aba,0x1096cce8,0x1110aef6,0x1180297b,0x11e564e4,0x1240898e,0x1291bfd6,0x12d92ffc,
    0x1317020c,0x134b5e2c,0x13766c42,0x13985449,0x13b13dec,0x13c150f9,0x13c8b50d,0x13c79194,
    0x13be0e02,0x13ac51a9]
  have hc:ay (j3 box 3037) 0 xs := by
    repeat' apply And.intro
    exacts [zLw0,zLw1,zLw2,zLw3,zLw4,zLw5,zLw6,zLw7,zLw8,zLw9,zLw10,zLw11,zLw12,zLw13,zLw14,zLw15,zLw16,zLw17,zLw18,zLw19,zLw20,zLw21,zLw22,zLw23,zLw24,zLw25,zLw26,zLw27,zLw28,zLw29,zLw30,zLw31,zLw32,zLw33,zLw34,zLw35,zLw36,zLw37,zLw38,zLw39,zLw40,zLw41,zLw42,zLw43,zLw44,zLw45,zLw46,zLw47,zLw48,zLw49,True.intro]
  have hl:xs.length=50:=rfl
  have hs :xs.sum=0x21baceb56:=rfl
  have he :=checked_sum (j3 box 3037) 0 xs hc
  simpa only [hl,hs,Nat.zero_add] using he
private def tail (n:ℕ) :ℕ := ∑ d∈range n,stable (50+d)
private theorem block (q n r :ℕ) {s :ℕ} (hs :tail q=s)
    (hr : (∑ d∈range n,stable (50+(q+d)))=r) :tail (q+n)=s+r := by
  unfold tail
  rw [sum_range_add,show (∑ d∈range q,stable (50+d))=s from hs,hr]
private theorem t0:tail 0=0:=rfl
local notation "block!" h "," idx "," len "," v=>block idx len v h rfl
private theorem t1 :tail 16=0x1296f9f60:=block! t0,0,16,0x1296f9f60
private theorem t2 :tail 32=0x231bcbec0:=block! t1,16,16,0x1084d1f60
private theorem t3:tail 48=0x319875e20:=block! t2,32,16,0xe7ca9f60
private theorem t4 :tail 64=0x3e16f7d80:=block! t3,48,16,0xc7e81f60
private theorem t5:tail 80=0x48a151ce0:=block! t4,64,16,0xa8a59f60
private theorem t6:tail 96=0x514183c40:=block! t5,80,16,0x8a031f60
private theorem t7:tail 112=0x58018dba0:=block! t6,96,16,0x6c009f60
private theorem t8:tail 115=0x5910eaf42 :=block! t7,112,3,0x10f5d3a2
end qYzmxYc
end
