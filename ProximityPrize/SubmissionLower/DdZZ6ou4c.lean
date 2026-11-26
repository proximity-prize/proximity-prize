import ProximityPrize.SubmissionLower.DdZRlaVZc
import ProximityPrize.SubmissionLower.DdZDBuLfd
import ProximityPrize.SubmissionLower.DdZdwiBha
import ProximityPrize.SubmissionLower.DdZvOdgMc
import ProximityPrize.SubmissionLower.DdZW31ykd
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Fin.sum_univ_succ → zCS, Int.reduceAdd → z10, Int.reduceDiv → zS8, Int.reduceMod → z6y, Int.reduceSub → zci, MvPolynomial.eval → zY9, Nat.add_le_add_left → z3b, Nat.sub_le_sub_right → zIu, Polynomial → zM1, Polynomial.C → z1z, Polynomial.coeff_C → zFI, RingHom.injective → zyB, Submodule.subset_span → zBO
section
set_option autoImplicit true
namespace P6_8_2
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative gR
open aR (ao embed extend af jet Z8 wU)
open i4 (K Node node N gap close)
open P5_8 (bo8 Equation)
open P5_8_3 (rows)

open anj (line bdm bfX)
open bzr (cX8)
open qC8CERb (coeffForm specialize Yw shift_jetDerivative coeff_iterate_zero atJet_eq_const)

























































































































end
end P6_8_2
end
section
set_option autoImplicit true
namespace P6_8_2
noncomputable section
open i4 PolynomialDifferential MvPolynomial Finset ReedSolomon.HiddenDerivative
open ProximityPrize.Benchmark UniqueFactorizationMonoid
open P5_8 (Equation small smallCaps bo8 donorCaps donor_shape Jn caps Gq)
open P5_8_3 (rows nativeBand dM powerCaps layerBound layerCost mem_nativeBand actual_caps initial_caps repair_band c54)

open scoped Polynomial BigOperators
open P5_8_3 (mem_rows derivative_band initial_mul)
open P5_8_3 (cofactor_eq group_cutoffs)
open qmRQvQa (matrix_dimension)
open qmRQvQa (S6 telescope caps_pow)
set_option maxHeartbeats 500000
set_option maxRecDepth 1800




















































































































































end
end P6_8_2
end
section
set_option autoImplicit true
namespace P6_8_1
open Finset P5_8_2 qxVnKgd
def aoV (a b c d y :ℤ) :ℤ:=a+b*y+c*y^2+d*(y%2)
def prim (a b c d y :ℤ) :ℤ :=
  6*a*y+3*b*y*(y-1)+c*y*(y-1)*(2*y-1)+6*d*(y/2)
def delta (a b c d l u:ℤ) :ℤ:=prim a b c d u - prim a b c d l
private theorem prim_step (a b c d y :ℤ) :
    prim a b c d (y+1)=prim a b c d y+6*aoV a b c d y := by
  unfold prim aoV
  rw [show (y+1)/2=y/2+y%2 by omega]
  ring
private theorem prim_sum (a b c d l:ℤ) (n:ℕ) :
    6*(∑ i∈range n,aoV a b c d (l+i))=delta a b c d l (l+n) := by
  induction n with
  | zero=>simp [delta]
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,Nat.cast_succ,← add_assoc]
    simp only [delta,prim_step]
    ring
theorem inner (f :ℤ→ℤ) {l u:ℤ} (a b c d:ℤ) (hlu:l≤u+1)
    (hf : ∀ y∈Icc l u,4*f y=aoV a b c d y) :
    24*(∑ y∈Icc l u,f y)=delta a b c d l (u+1) := by
  have h:=prim_sum a b c d l (u+1-l).toNat
  rw [← sum_Icc_shift,← sum_congr rfl hf,← mul_sum,
    Int.toNat_of_nonneg (show 0≤u+1-l by omega),
    show l+(u+1-l)=u+1 by ring] at h
  linear_combination h
theorem four_H {x :ℤ} (hx :0≤x) :4*H x=x*(x+2)+x%2 := by
  generalize hq:x/2=q
  have hq' : 0≤q:= by omega
  rcases (show x=2*q∨x=2*q+1 by omega) with rfl | rfl
  · rw [H_even hq',show (2*q)%2=0 by omega]
    ring
  · rw [H_odd hq',show (2*q+1)%2=1 by omega]
    ring
def kA (f :ℤ→ℤ) (l:ℤ) (n:ℕ) :ℤ := ∑ i∈range n,f (l+i)
theorem band_split (f :ℤ→ℤ) (l:ℤ) (m n:ℕ) :
    kA f l (m+n)=kA f l m+kA f (l+m) n:= by
  unfold kA
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Nat.cast_add,← add_assoc]
private theorem gvP (f :ℕ→ℤ) (n:ℕ) :
    (∑ i∈range n,f i) =
      (∑ i∈range ((n+3)/4),f (4*i))+(∑ i∈range ((n+2)/4),f (4*i+1)) +
      (∑ i∈range ((n+1)/4),f (4*i+2))+(∑ i∈range (n/4),f (4*i+3)) := by
  have h :
      (∑ x∈(univ :Finset (Fin 4)).sigma (fun r=>range ((n+3-r.val)/4)),
        f (4*x.2+x.1.val)) = ∑ i∈range n,f i:= by
    refine sum_bij (fun x _=>4*x.2+x.1.val) ?_ ?_ ?_ (fun _ _=>rfl)
    · rintro ⟨r,i⟩ hi
      have hr :=r.isLt
      have hi:=mem_range.mp (mem_sigma.mp hi).2
      exact mem_range.mpr (by dsimp at *; omega)
    · rintro ⟨r,i⟩ _ ⟨s,j⟩ _ hij
      have hr :=r.isLt
      have hs :=s.isLt
      change 4*i+r.val = 4*j+s.val at hij
      have hrs :r=s :=Fin.ext (by omega)
      have hij' : i=j:= by omega
      subst s
      subst j
      rfl
    · intro i hi
      have hi:=mem_range.mp hi
      refine ⟨⟨⟨i%4,by omega⟩,i/4⟩,mem_sigma.mpr ⟨mem_univ _,mem_range.mpr ?_⟩,?_⟩
      · dsimp
        omega
      · dsimp
        omega
  rw [sum_sigma,zCS,zCS,zCS,
    zCS,Fin.sum_univ_zero,add_zero] at h
  rw [← h]
  have h0: (n+3-0)/4=(n+3)/4 := by omega
  have h1 : (n+3-1)/4=(n+2)/4 := by omega
  have h2 : (n+3-2)/4=(n+1)/4 := by omega
  have h3: (n+3-3)/4=n/4 := by omega
  change (∑ i∈range ((n+3-0)/4),f (4*i+0)) +
      ((∑ i∈range ((n+3-1)/4),f (4*i+1)) +
        ((∑ i∈range ((n+3-2)/4),f (4*i+2))+(∑ i∈range ((n+3-3)/4),f (4*i+3))))= _
  rw [h0,h1,h2,h3]
  simp only [add_zero,add_assoc]
theorem quarter (f :ℕ→ℤ) (n:ℕ) (a b c d value :ℤ)
    (hv :sumFormula a b c d n=288*value)
    (hf : ∀ i∈range n,24*f i=poly a b c d i) :
    (∑ i∈range n,f i)=value := by
  have h:=gvl a b c d n
  rw [← sum_congr rfl hf,← mul_sum,hv] at h
  omega
theorem band_value (f :ℤ→ℤ) (l:ℤ) (n:ℕ) {v0 v1 v2 v3 v :ℤ}
    (h0: (∑ i∈range ((n+3)/4),f (l+0+4*(i:ℤ)))=v0)
    (h1 : (∑ i∈range ((n+2)/4),f (l+1+4*(i:ℤ)))=v1)
    (h2 : (∑ i∈range ((n+1)/4),f (l+2+4*(i:ℤ)))=v2)
    (h3: (∑ i∈range (n/4),f (l+3+4*(i:ℤ)))=v3)
    (hv :v0+v1+v2+v3=v) :kA f l n=v := by
  rw [kA,gvP]
  have hs (i r :ℕ) :l+(↑(4*i+r) :ℤ)=l+r+4*(i:ℤ) := by
    push_cast
    ring
  simp only [hs,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,add_zero] at h0 ⊢
  rw [h0,h1,h2,h3,hv]
end P6_8_1
end
section
set_option autoImplicit true
namespace P6_8_1
open Finset qxVnKgd
def II (x :ℤ) :ℤ := ∑ y∈Icc 1 x,low x x y
def lI (x :ℤ) :ℤ := ∑ y∈Icc (max 0 (2*x-1959)) (x-1),low x y y
def pG (x :ℤ) :ℤ :=
  ∑ y∈Icc (max 1 (x-1651)) (min (3919-2*x) ((3919-x)/2)),high x y 0 0
def one (x y :ℤ) :ℤ:=high x y (2*x+y-3919) 0
def uW (x :ℤ) :ℤ := ∑ y∈Icc (max (3920-2*x) (x-1651)) ((3919-x)/2),one x y
def y5 (x :ℤ) :ℤ := ∑ y∈Icc (3920-2*x) ((3919-x)/2),one x y
theorem low0 (x r :ℤ) (hx :0≤x) (hr :max 0 (x-979)=r) :
    24*II x=delta (2*(x+1)*(x+2)-4*r^2) (-2) (-1) (-1) 1 (x+1) := by
  unfold II
  apply inner _ _ _ _ _ (by omega)
  intro y hy
  have hy :=mem_Icc.mp hy
  unfold low aoV
  rw [hr]
  linear_combination 2*twice_T (by omega :0≤x+1) - four_H (by omega :0≤y)
theorem cYR (x r l:ℤ) (hx :0≤x∧x≤1958)
    (hr :max 0 (x-979)=r) (hl:max 0 (2*x-1959)=l) :
    24*lI x=delta (4-4*r^2) 4 1 (-1) l x := by
  unfold lI
  rw [hl]
  have h₀:0≤l:= by omega
  have h₁:l≤x-1+1 := by omega
  have h:=inner (fun y=>low x y y) (4-4*r^2) 4 1 (-1) h₁ ?_
  · rw [sub_add_cancel] at h
    exact h
  · intro y hy
    have hy :=mem_Icc.mp hy
    unfold low aoV
    rw [hr]
    linear_combination 2*twice_T (by omega :0≤y+1) - four_H (by omega :0≤y)
theorem high3 (x l u:ℤ) (hx :1≤x∧x≤1856)
    (hl:max 1 (x-1651)=l) (hu:min (3919-2*x) ((3919-x)/2)=u) :
    24*pG x=delta (3845520-x*(x+2)-x%2) (-2) (-1) (-1) l (u+1) := by
  unfold pG
  rw [hl,hu]
  have h₀:1≤l:= by omega
  apply inner _ _ _ _ _ (by omega)
  intro y hy
  have hy :=mem_Icc.mp hy
  unfold high aoV
  dsimp
  simp only [sub_zero]
  linear_combination -four_H (by omega :0≤x) - four_H (by omega :0≤y)
def oneA (x :ℤ) :ℤ :=
  let n:=4899-2*x
  let v :=7838-3*x
  let w:=3919-2*x
  4*n*(n+1)-v*(v+2)-w*(w+2)-x%2-1
def oneB (x :ℤ) :ℤ:=4*(7838-3*x)-8*(4899-2*x)
private theorem high_one (x l:ℤ) (hx :1307≤x∧x≤1959)
    (hl:3920-2*x≤l) (hu:l≤(3919-x)/2+1) :
    24*(∑ y∈Icc l ((3919-x)/2),one x y) =
      delta (oneA x) (oneB x) 0 0 l ((3919-x)/2+1) := by
  apply inner _ _ _ _ _ hu
  intro y hy
  have hy :=mem_Icc.mp hy
  have hp:x-2*(2*x+y-3919)-0=7838-3*x-2*y := by ring
  have ho:y-(2*x+y-3919)-0=3919-2*x := by ring
  unfold one high oneA oneB aoV
  dsimp
  rw [hp,ho]
  have h:=four_H (by omega :0≤7838-3*x-2*y)
  have h' := four_H (by omega :0≤3919-2*x)
  rw [show (7838-3*x-2*y)%2=x%2 by omega] at h
  rw [show (3919-2*x)%2=1 by omega] at h'
  linear_combination -h-h'
theorem high4 (x l:ℤ) (hx :1307≤x∧x≤1959)
    (hl:max (3920-2*x) (x-1651)=l) :
    24*uW x=delta (oneA x) (oneB x) 0 0 l ((3919-x)/2+1) := by
  unfold uW
  rw [hl]
  exact high_one x l hx (by omega) (by omega)
theorem high5 (x :ℤ) (hx :1307≤x∧x≤1959) :
    24*y5 x=delta (oneA x) (oneB x) 0 0 (3920-2*x) ((3919-x)/2+1) :=
  high_one x _ hx (by omega) (by omega)
theorem half0 (a i:ℤ) : (a+4*i)/2=a/2+2*i:= by omega
theorem half1 (a i:ℤ) : (a+4*i+1)/2=(a+1)/2+2*i:= by omega
theorem half2 (a i:ℤ) : (2*(a+4*i)-1959)/2=a+4*i-980:= by omega
theorem half4 (a i:ℤ) : (a+4*i-1651)/2=(a-1651)/2+2*i:= by omega
theorem half5 (a i:ℤ) : (3919-2*(a+4*i)+1)/2=1960-(a+4*i) := by omega
theorem half6 (a i:ℤ) : (3919-(a+4*i))/2=(3919-a)/2-2*i:= by omega
theorem parity4 (a i:ℤ) : (a+4*i)%2=a%2 := by omega
end P6_8_1
end
section
set_option autoImplicit true
namespace P6_8_1
open Finset P5_8_2 qxVnKgd
private theorem half_neg2 (a i:ℤ) : (a-2*i+1)/2=(a+1)/2-i:= by omega
local notation "part!" a "," b "," c "," d "," v=>quarter _ _ a b c d v (by decide)
private theorem b0:kA II 0 980=0x166827d66a := by
  have h (x :ℤ) (hx :0≤x∧x≤979) :=low0 x 0 hx.1 (by omega)
  refine band_value _ _ _
    ((part! 0,56,432,640,0x591458846) ?_)
    ((part! 48,392,912,640,0x5971ac344) ?_)
    ((part! 216,968,1392,640,0x59cf4929f) ?_)
    ((part! 552,1784,1872,640,0x5a2d2f841) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half1,z10,zci,zS8]
    ring
private theorem b1 :kA II 980 979=0xd21942f432 := by
  have h (x :ℤ) (hx :980≤x∧x≤1958) :=low0 x (x-979) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x2328a0668,0x6dee738,93744,(-896),0x3485baac61) ?_)
    ((part! 0x23441d708,0x6df9da8,93072,(-896),0x34929a6b79) ?_)
    ((part! 0x235f9d520,0x6e052c8,92400,(-896),0x349f75981e) ?_)
    ((part! 0x237b20050,0x6e10698,91728,(-896),0x346178443a) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half1,z10,zci,zS8]
    ring
private theorem b2 :kA lI 0 980=0x47e0a569f := by
  have h (x :ℤ) (hx :0≤x∧x≤979) :=cYR x 0 0 (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0,40,144,128,0x11dc0dfd2) ?_)
    ((part! 24,136,240,128,0x11eec11e7) ?_)
    ((part! 72,280,336,128,0x120182e75) ?_)
    ((part! 168,472,432,128,0x121453671) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half0,z10,zci,zS8]
    ring
private theorem b3:kA lI 980 979=0xd70c1c767:= by
  have h (x :ℤ) (hx :980≤x∧x≤1958) :=cYR x (x-979) (2*x-1959) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x70b694f8,22932056,(-281904),640,0x35df2291f) ?_)
    ((part! 0x710dcac8,22791224,(-281424),640,0x35cc6f615) ?_)
    ((part! 0x71647728,22650632,(-280944),640,0x35b9ad79d) ?_)
    ((part! 0x71ba9a60,22510280,(-280464),640,0x35a6dd096) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,half0,half2,z10,zS8]
    ring
private theorem b4 :kA pG 1 1306=0x12a8abab70c:= by
  have h (x :ℤ) (hx :1≤x∧x≤1306) :=high3 x 1 ((3919-x)/2) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x703dd3e88,(-211540),(-234924),208,0x4ac33f2f40) ?_)
    ((part! 0x703dc2b30,(-352420),(-234708),208,0x4ab6c3adfe) ?_)
    ((part! 0x703dabc10,(-446308),(-234612),208,0x4a8e9602af) ?_)
    ((part! 0x703d895c0,(-586972),(-234396),208,0x4a8221d71f) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,parity4,half6,half_neg2,z10,zci,zS8,z6y]
    ring
private theorem b5:kA pG 1307 346=0x1a3a90fab7:= by
  have h (x :ℤ) (hx :1307≤x∧x≤1652) :=high3 x 1 (3919-2*x) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x2da670bf8,(-0x61b77b0),(-124704),1792,0x69b34cc95) ?_)
    ((part! 0x2d8e02e40,(-0x61c6a20),(-123360),1792,0x695d0a210) ?_)
    ((part! 0x2d758d738,(-0x61d5990),(-122016),1792,0x687707450) ?_)
    ((part! 0x2d5d18198,(-0x61e46c0),(-120672),1792,0x6821b17c2) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,parity4,half5,z10,zci,zS8,z6y]
    ring
private theorem b6:kA pG 1653 204=0x2dffb44aa := by
  have h (x :ℤ) (hx :1653≤x∧x≤1856) :=high3 x (x-1651) (3919-2*x) (by omega) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0xd73d4f68,(-0x6941688),658224,2304,0xbb5ff91e) ?_)
    ((part! 0xd598f8e0,(-0x68f0f88),659952,2304,0xb91cfdc5) ?_)
    ((part! 0xd3f5c810,(-0x68a0498),661680,2304,0xb6dd43c1) ?_)
    ((part! 0xd253f6b8,(-0x684f6d8),663408,2304,0xb4a10a06) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,parity4,half4,half5,z10,zci,zS8,z6y]
    ring
private theorem b7:kA uW 1307 551=0x4d06eb1da := by
  have h (x :ℤ) (hx :1307≤x∧x≤1857) :=high4 x (3920-2*x) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 2558448,15366360,93840,(-1152),0x133eb0237) ?_)
    ((part! 5132544,15428736,92928,(-1152),0x1344d4c20) ?_)
    ((part! 10264944,15459336,92112,(-1152),0x13505f5a9) ?_)
    ((part! 12870000,15520800,91200,(-1152),0x133306dda) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,oneA,oneB,parity4,half6,zero_mul,add_zero,z10,zci,zS8,z6y]
    ring
private theorem b8:kA uW 1858 102=0x6213ca59:= by
  have h (x :ℤ) (hx :1858≤x∧x≤1959) :=high4 x (x-1651) (by omega) (by omega)
  refine band_value _ _ _
    ((part! 0x3499f140,(-49102608),627168,(-2304),0x195a63a6) ?_)
    ((part! 0x33df9d88,(-48791832),625488,(-2304),0x18cad95f) ?_)
    ((part! 0x3325b510,(-48477168),623712,(-2304),0x183c3a9e) ?_)
    ((part! 0x326dbeb0,(-48168072),622032,(-2304),0x17b252b6) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,oneA,oneB,parity4,half6,zero_mul,add_zero,z10,zci,zS8,z6y]
    ring
private theorem b9:kA y5 1307 653=0x54dcf32e1 := by
  have h (x :ℤ) (hx :1307≤x∧x≤1959) :=high5 x hx
  refine band_value _ _ _
    ((part! 2558448,15366360,93840,(-1152),0x1538a0882) ?_)
    ((part! 5132544,15428736,92928,(-1152),0x1535bbca0) ?_)
    ((part! 10264944,15459336,92112,(-1152),0x1538a6f05) ?_)
    ((part! 12870000,15520800,91200,(-1152),0x1535efeba) ?_)
    (by decide)
  all_goals
    intro i hi
    have hi:=mem_range.mp hi
    rw [h] <;> try omega
    simp only [delta,prim,poly,oneA,oneB,parity4,half6,zero_mul,add_zero,z10,zci,zS8,z6y]
    ring
theorem total1 :qxVnKgd.c1 := by
  change (0xe8816aca9c:ℤ) ≤ ∑ x∈(Icc (0:ℤ) 1958).sigma (fun q=>Icc 1 q),score 0 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (0:ℤ) 1958,II x
  rw [sum_Icc_shift]
  change _≤kA II 0 (980+979)
  rw [band_split II 0 980 979,show (0 + ↑(980:ℕ) :ℤ)=980 by decide,b0,b1] <;> decide
theorem total2 :qxVnKgd.c2 := by
  change (0x11eecc1e06:ℤ) ≤ ∑ x∈(Icc (0:ℤ) 1958).sigma (fun q=>Icc (max 0 (2*q-1959)) (q-1)),score 1 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (0:ℤ) 1958,lI x
  rw [sum_Icc_shift]
  change _≤kA lI 0 (980+979)
  rw [band_split lI 0 980 979,show (0 + ↑(980:ℕ) :ℤ)=980 by decide,b2,b3] <;> decide
theorem total3:qxVnKgd.c3:= by
  change (0x147a546f66d:ℤ) ≤ ∑ x∈(Icc (1:ℤ) 1856).sigma (fun p=>Icc (max 1 (p-1651)) (min (3919-2*p) ((3919-p)/2))),score 3 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (1:ℤ) 1856,pG x
  rw [sum_Icc_shift]
  change _≤kA pG 1 (1306+(346+204))
  rw [band_split pG 1 1306 (346+204),show (1 + ↑(1306:ℕ) :ℤ)=1307 by decide,
    band_split pG 1307 346 204,show (1307 + ↑(346:ℕ) :ℤ)=1653 by decide,b4,b5,b6] <;> decide
theorem total4 :qxVnKgd.c4 := by
  change (0x532827c33:ℤ) ≤ ∑ x∈(Icc (1307:ℤ) 1959).sigma (fun p=>Icc (max (3920-2*p) (p-1651)) ((3919-p)/2)),score 4 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (1307:ℤ) 1959,uW x
  rw [sum_Icc_shift]
  change _≤kA uW 1307 (551+102)
  rw [band_split uW 1307 551 102,show (1307 + ↑(551:ℕ) :ℤ)=1858 by decide,b7,b8] <;> decide
theorem total5:qxVnKgd.c5:= by
  change (0x54dcf32e1 :ℤ) ≤ ∑ x∈(Icc (1307:ℤ) 1959).sigma (fun p=>Icc (3920-2*p) ((3919-p)/2)),score 5 x
  rw [sum_sigma]
  change _ ≤ ∑ x∈Icc (1307:ℤ) 1959,y5 x
  rw [sum_Icc_shift]
  change _≤kA y5 1307 653
  rw [b9]
end P6_8_1
end
section
set_option autoImplicit true
namespace P6_8_1
theorem proof :P6_8.c1 :=
  qxVnKgd.of_children total1 total2 total3 total4 total5
end P6_8_1
end
