import ProximityPrize.SubmissionLower.ZPuXYRc
set_option Elab.async false
section
set_option autoImplicit true
namespace P6_7_2
noncomputable section
open Polynomial
open P6 (jG e9 I K p twist dw)
open P6_7 (YQ axy RectTail)
open cu (L FX Jet Equation Shape vP ku)
open P5_7_1 (TopRow topLift topConjugate atTop)
open DP (jF zG aKF ad0 Source Fg complete U4 VY)
open qQ (zI N5 aeH)
open scoped BigOperators
structure Input (b:RectTail) where
  u:e9
  del:Finset I
  M:jG u del
  Γ:Finset K
  F:P1.bje dw M Γ
  kA:P5_7.Qn b.kA.lo b.kA.hi M.iF
  noShift:M.shift∉Γ
  H :L[X]
  bY:YQ M F H
abbrev Input.h {b:RectTail} (x :Input b) :=x.M.iF.toNat
abbrev Input.word {b:RectTail} (x :Input b) (i:I) :L:=algebraMap K L (x.M.word i)
structure Poles {b:RectTail} (x :Input b) where
  D:jF x.h
  crt:zG D
  first:D.block 0=x.H
  second:D.block 1=x.H.map (frobenius L p)
  nodes : ∀ i k,(D.block i).eval (ad0 k)≠0
  marks : ∀ γ∈x.Γ,aKF D (x.M.label γ) (x.F.scalar γ)
abbrev Poles.rows {b:RectTail} {x :Input b} (P:Poles x) :vP:=VY P.crt x.word
def cutoff (h r :ℕ) (s :Shape) :ℕ:=s.m*dw - 1 - 2*h*r
structure Picks {b:RectTail} (h:ℕ) (rows :vP) where
  freeRow :Ls→Jet
  movingRow :Ls→Jet
  auxRow :Aux→Jet
  free_ne : ∀ i,freeRow i≠0
  moving_ne : ∀ i,movingRow i≠0
  aux_ne : ∀ i,auxRow i≠0
  free_mem : ∀ i,freeRow i∈rows (free b i) (cutoff h (dI i) (free b i))
  moving_mem : ∀ i,movingRow i∈rows (moving b i) (cutoff h (dI i) (moving b i))
  aux_mem : ∀ i,auxRow i∈rows (auxiliary b i) (cutoff h (auxReserve i) (auxiliary b i))
  no_moving : ∀ i,aeH (freeRow i) (movingRow i)
  shared:auxRow 9=freeRow 1∧auxRow 10=freeRow 3
def TopCaps (h m B J C U:ℕ) (P:TopRow) :Prop :=
  ∀ a∈P.support,
    a 1+a 2+a 3≤B∧a 2+2*a 3≤J∧a 3≤C∧a 0≤U ∧
    (P.coeff a).natDegree+(131071+h)*(a 1+a 2+a 3) ≤
      m*dw-1+(B+J)*h+a 2+2*a 3
structure TopPair {b:RectTail} (x :Input b) where
  cheap:TopRow
  strong:TopRow
  cheap_ne :cheap≠0
  strong_ne :strong≠0
  cheap_caps :TopCaps x.h 64 87 27 12 (cheapWidth b) cheap
  strong_caps :TopCaps x.h 120 164 50 19 (strongWidth b) strong
  no_moving : ∀ Q:MvPolynomial (Fin 4) FX,Irreducible Q →
    0<Q.degreeOf 3→Q∣topLift cheap→Q∣topLift strong→Q.degreeOf 0=0
  necessary : ∀ γ∈x.Γ,
    atTop cheap (x.M.label γ) (x.F.scalar γ)=0 ∧
    atTop strong (x.M.label γ) (x.F.scalar γ)=0 ∧
    atTop (topConjugate cheap) (twist (x.M.label γ)) (x.F.scalar γ)=0 ∧
    atTop (topConjugate strong) (twist (x.M.label γ)) (x.F.scalar γ)=0
def sk.seedSpace (r :sk) :Submodule L Source where
  carrier := {P | ∀ j i a e,(r.z<e 0∨r.t<e 1)→Fg P j i a e=0}
  zero_mem' := by simp [Fg]
  add_mem' := by
    intro P Q hP hQ j i a e he
    have hp:=hP j i a e he
    have hq:=hQ j i a e he
    simp [Fg] at hp hq ⊢
    simp [hp,hq]
  smul_mem' := by
    intro c P hP j i a e he
    have hp:=hP j i a e he
    unfold Fg at hp ⊢
    simp [Polynomial.coeff_smul,hp]
def rectShape (b:RectTail) (r :sk) :Shape :=
  { (Bs b).terminal with U:=r.z+r.t }
def rectCutoff (b:RectTail) (h:ℕ) :ℕ :=
  cutoff h (Bs b).dI (Bs b).terminal
def rectRows {b:RectTail} {x :Input b} (P:Poles x) (r :sk) (W:ℕ) :
    Submodule FX Jet :=
  Submodule.span FX (U4 ''
    ((complete P.crt x.word (rectShape b r) W ⊓ r.seedSpace :Submodule L Source) :Set Source))
def Subrect (b:RectTail) (r :sk) :Prop :=
  let s :=(Bs b).terminal
  s.B≤ r.z∧s.B≤ r.t∧r.z≤ s.U∧r.t≤ s.U
def TerminalPass {b:RectTail} {x :Input b} (P:Poles x) (q:zI) :Prop :=
  ∀ G∈rectRows P (full b) (rectCutoff b x.h),G∈q.asIdeal
abbrev retainedFee (b:RectTail) :ℕ:=(Bs b).retainedFee
def prefixFee (b:RectTail) :ℕ:=b.kA.regular - retainedFee b
structure Prefix {b:RectTail} {x :Input b} (P:Poles x) where
  book :Finset K
  book_bound:book.card≤prefixFee b
  parents :Finset zI
  geometric : ∀ q∈parents,N5 q
  free_pass : ∀ q∈parents,∀ i:Ls,i≠0 →
    ∀ G∈P.rows (free b i) (cutoff x.h 0 (free b i)),G∈q.asIdeal
  terminal_pass : ∀ q∈parents,TerminalPass P q
  Eh : ∀ γ∈x.Γ,γ∈book ∨ ∃ q∈parents,axy x.M x.F q γ
def localPhysical (s :Shape) :ℕ :=
  ku s fun q j=>s.m+min q s.J-(q+2*j)
def poleExtra (s :Shape) :ℕ :=
  let eta := fun q j=>s.B+s.J+2*j-(q+min q s.J)
  ku s (fun q j=>eta q j*(2*s.B+j+1-2*q)) -
    (s.B+1)*ku s eta
def rectDebit (b:RectTail) (h:ℕ) (r :sk) :ℕ :=
  let s :=(Bs b).terminal
  (r.z+1)*(r.t+1)*262144*localPhysical s+h*poleExtra s*(r.z+r.t+2)
def amv (b:RectTail) (h q j:ℕ) :ℕ :=
  rectCutoff b h+1+j - q*(131071-h)
def rectVolume (b:RectTail) (h:ℕ) (r :sk) :ℕ :=
  (r.z+1)*(r.t+1)*ku (Bs b).terminal (amv b h)
def rankSum {b:RectTail} {x :Input b} (P:Poles x) (r :sk) :ℕ :=
  ∑ W∈Finset.range (rectCutoff b x.h+1),Module.finrank FX (rectRows P r W)
def seedStock (r :sk) (kd:Fin 2) (v :ℕ) :ℕ :=
  if kd=0 then (r.t+1)*(r.z+1-v) else (r.z+1)*(r.t+1-v)
def ZN (b:RectTail) (h:ℕ) (r :sk) (kd:Fin 2) (E v :ℕ) :ℕ :=
  ku (Bs b).terminal fun q j =>
    let g:=(q-j)/E
    let w:=amv b h q j
    let c:= fun a=>seedStock r kd (a*v)
    (∑ a∈Finset.range g,(c a-c (a+1))*(w-2*h*(j+a))) +
      c g*(w-2*h*(j+g))
def AxisBound (f :Equation) (i:Fin 2) (v :ℕ) :Prop :=
  ∀ l,(f.coeff l).degreeOf i≤v
end
end P6_7_2
end
section
set_option autoImplicit true
namespace qO6e97d
open Finset
open P6 (dw p)
open P6_7 (RectTail)
open P6_7_2 (Ls Aux Bs free moving auxiliary dI auxReserve)
open cu (Shape ku triangle)
open DP (bga)
open qZyoMPc (aP4 scaledDebit_eq)
open czX (a8x dei)
open private bid from ProximityPrize.SubmissionLower.CN
open private row aJm level df7 df3 bhM dgC cck from ProximityPrize.SubmissionLower.E7
def count (h r :ℕ) (s :Shape) :ℕ:=s.m*dw - 2*h*r
def amv (h r :ℕ) (s :Shape) (q j:ℕ) :ℕ :=
  count h r s+j - q*(131071-h)
def aL4 (h r :ℕ) (s :Shape) :Prop :=
  s.B*(131071-h)<count h r s
def O3 (h r :ℕ) (s :Shape) (mode :ℕ) :ℕ :=
  triangle s.U*ku s (fun q j=>amv h r s q j - mode*(2*h*j))
def DG (s :Shape) :ℕ:=(aP4 s.B s.J s.U/2880).toNat
def j3 (h:ℕ) (s :Shape) :ℕ:=bga s+2*h*DG s
theorem pole_excess (s :Shape) (hj:s.J≤ s.B) (hu:s.B≤ s.U) :
    P5_7_4.poleRank s≤triangle s.U*agU.arY s+DG s := by
  apply qZyoMPc.bound s _ hj hu
  unfold DG
  rw [scaledDebit_eq s hj hu,Int.mul_ediv_cancel_left _ (by decide : (2880:ℤ)≠0)]
  omega
private theorem scaled_excess (s :Shape) (hj:s.J≤ s.B) (hu:s.B≤ s.U)
    (hn:0≤aP4 s.B s.J s.U) :
    aP4 s.B s.J s.U=2880*(DG s :ℤ) := by
  rw [scaledDebit_eq s hj hu] at hn ⊢
  unfold DG
  rw [scaledDebit_eq s hj hu,Int.mul_ediv_cancel_left _ (by decide : (2880:ℤ)≠0)]
  omega
structure Tested (h r :ℕ) (s :Shape) (mode :ℕ) :Prop where
  jet_le :s.J≤ s.B
  aH4 :s.B≤ s.U
  seed_lt:s.U<p
  width :aL4 h r s
  x5:j3 h s<O3 h r s mode
private theorem cA5: (dw:ℤ)=179827:=rfl
private def cut (s :Shape) (r lo mode :ℕ) :ℕ :=
  min (s.B+1) ((count lo r s - 1-(2*mode*lo-1)*s.J)/(131071-lo)+1)
private def csU (s :Shape) (r lo mode q:ℕ) :ℕ :=
  min (min q s.J+1) ((amv lo r s q 0 - 1)/(2*mode*lo-1)+1)
private def support (s :Shape) (r lo mode q:ℕ) :ℕ :=
  if q<cut s r lo mode then min q s.J+1 else csU s r lo mode q
private def total (s :Shape) (r lo mode :ℕ) (x y z :ℤ) :ℤ :=
  let k :=cut s r lo mode
  aJm x y z s.J+level x y z s.J (k-s.J) +
    6*bhM (fun q=>row x y z q (csU s r lo mode q)) k (s.B+1-k)
private theorem asB (s :Shape) (r lo mode :ℕ) (x y z :ℤ)
    (hj:s.J≤ cut s r lo mode) :
    total s r lo mode x y z=6*(∑ q∈range (s.B+1),row x y z q (support s r lo mode q)) := by
  let k :=cut s r lo mode
  let f := fun q=>row x y z q (support s r lo mode q)
  have hk :k≤ s.B+1 :=min_le_left _ _
  have hsplit :=sum_range_add f k (s.B+1-k)
  have hprefix :=sum_range_add f s.J (k-s.J)
  rw [Nat.add_sub_of_le hk] at hsplit
  rw [Nat.add_sub_of_le hj] at hprefix
  change _=6*(∑ q∈range (s.B+1),f q)
  rw [hsplit,hprefix,mul_add,mul_add]
  have hfirst: (∑ q∈range s.J,f q) = ∑ q∈range s.J,row x y z q (q+1) := by
    apply sum_congr rfl
    intro q hq
    have hq' := mem_range.mp hq
    simp only [f,support,ite_eq_left (hq'.trans_le hj),min_eq_left hq'.le]
  have hmiddle : (∑ i∈range (k-s.J),f (s.J+i)) =
      ∑ i∈range (k-s.J),row x y z (s.J+i) (s.J+1) := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have hlt:s.J+i<cut s r lo mode := by change s.J+i<k; omega
    simp only [f,support,ite_eq_left hlt,min_eq_right (Nat.le_add_right _ _)]
  have hlast : (∑ i∈range (s.B+1-k),f (k+i)) =
      ∑ i∈range (s.B+1-k),row x y z (k+i) (csU s r lo mode (k+i)) := by
    apply sum_congr rfl
    intro i _
    have hge :cut s r lo mode≤k+i:=Nat.le_add_right k i
    simp only [f,support,ite_eq_right (not_lt_of_ge hge)]
  rw [hfirst,hmiddle,hlast,df7,df3]
  dsimp only [total]
  rw [dgC]
private def origin (s :Shape) (r :ℕ) (h:ℤ) :ℤ:=(s.m:ℤ)*dw - 2*h*r
private def aso (s :Shape) (r :ℕ) (h:ℤ) (mode q j:ℕ) :ℤ :=
  origin s r h-(131071-h)*q+(1-2*mode*h)*j
private def b7r (s :Shape) (r lo mode :ℕ) :ℤ :=
  total s r lo mode (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo)
private def cpY (s :Shape) (r lo mode :ℕ) :ℤ :=
  total s r lo mode (-4*(r :ℤ)) 2 (-2*(mode :ℤ))
private theorem gq1 (s :Shape) (r h mode q j:ℕ) (hh:h≤131071) :
    aso s r h mode q j≤((amv h r s q j - mode*(2*h*j) :ℕ) :ℤ) := by
  have cast_sub_le (a b:ℕ) : (a :ℤ)-b≤((a-b:ℕ) :ℤ) := by omega
  have hcut:=cast_sub_le (s.m*dw) (2*h*r)
  have hraw:=cast_sub_le (count h r s+j) (q*(131071-h))
  have hloss :=cast_sub_le (amv h r s q j) (mode*(2*h*j))
  change _≤(count h r s :ℤ) at hcut
  change _≤(amv h r s q j:ℤ) at hraw
  push_cast [Nat.cast_sub hh] at hcut hraw hloss
  unfold aso origin
  rw [cA5]
  nlinarith only [hcut,hraw,hloss]
private theorem fZn (s :Shape) (r lo h mode q n:ℕ) :
    row (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo) q n +
      ((h:ℤ)-lo)*row (-4*(r :ℤ)) 2 (-2*(mode :ℤ)) q n =
    2*(∑ j∈range n,aso s r h mode q j) := by
  change _=2*(∑ j∈range n,(origin s r h-(131071-(h:ℤ))*q+(1-2*(mode :ℤ)*h)*j))
  rw [bid]
  unfold row origin
  ring
private theorem gxx (s :Shape) (r lo h mode :ℕ) (hh:h≤131071)
    (hj:s.J≤ cut s r lo mode) :
    b7r s r lo mode+((h:ℤ)-lo)*cpY s r lo mode ≤
      12*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
  let f := fun q=>row (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo) q
    (support s r lo mode q)
  let g:= fun q=>row (-4*(r :ℤ)) 2 (-2*(mode :ℤ)) q (support s r lo mode q)
  have hsum: (∑ q∈range (s.B+1),f q)+((h:ℤ)-lo)*(∑ q∈range (s.B+1),g q) ≤
      2*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
    unfold ku
    push_cast [Nat.cast_sum]
    rw [mul_sum,← sum_add_distrib,mul_sum]
    apply sum_le_sum
    intro q _
    rw [show f q+((h:ℤ)-lo)*g q= _ from fZn s r lo h mode q (support s r lo mode q)]
    have hsub:range (support s r lo mode q)⊆range (min q s.J+1) := by
      apply range_mono
      unfold support
      split
      · rfl
      · exact min_le_left _ _
    apply mul_le_mul_of_nonneg_left _ (by decide : (0:ℤ)≤2)
    calc
      _ ≤ ∑ j∈range (support s r lo mode q),((amv h r s q j - mode*(2*h*j) :ℕ) :ℤ) :=
        sum_le_sum fun j _=>gq1 s r h mode q j hh
      _≤_:=sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>Int.natCast_nonneg _)
  unfold b7r cpY
  rw [asB _ _ _ _ _ _ _ hj,asB _ _ _ _ _ _ _ hj]
  have hz :=mul_le_mul_of_nonneg_left hsum (by decide : (0:ℤ)≤6)
  dsimp only [f,g] at hz
  nlinarith only [hz]
private def biN (s :Shape) (r :ℕ) (h:ℤ) :ℤ :=
  origin s r h-(131071-h)*s.B
private theorem gMy (s :Shape) (r h:ℕ) (hh:h≤131071)
    (hw:0<biN s r h) :aL4 h r s := by
  have hn:0≤(131071-(h:ℤ))*(s.B:ℤ) := by
    exact mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hh)) (Int.natCast_nonneg _)
  unfold biN origin at hw
  have hbuf :2*h*r≤ s.m*dw:= by
    have hz :2*(h:ℤ)*r≤(s.m:ℤ)*dw:= by nlinarith only [hn,hw]
    exact_mod_cast hz
  unfold aL4 count
  apply Int.ofNat_lt.mp
  push_cast [Nat.cast_sub hh,Nat.cast_sub hbuf]
  rw [cA5] at hw
  nlinarith only [hw]
private def cXb (s :Shape) (r lo mode :ℕ) :ℤ :=
  120*(triangle s.U:ℤ) *
    (b7r s r lo mode - 2*(262144*a8x (s.m-2*s.J) s.J:ℕ)) -
    (lo:ℤ)*aP4 s.B s.J s.U
private def deC (s :Shape) (r lo mode :ℕ) :ℤ :=
  120*(triangle s.U:ℤ)*cpY s r lo mode-aP4 s.B s.J s.U
private structure Check (lo hi:ℕ) (s :Shape) (r mode :ℕ) :Prop where
  height:hi≤131071
  support :s.J≤ cut s r lo mode
  mult:2*s.J≤ s.m
  cV:s.m+s.J≤ s.B+1
  width :s.B≤ s.U
  char :s.U<p
  pole :decide (0≤aP4 s.B s.J s.U)=true
  rawLo:decide (0<biN s r lo)=true
  rawHi:decide (0<biN s r hi)=true
  signLo:decide (0<cXb s r lo mode)=true
  signHi:decide (0<cXb s r lo mode+((hi:ℤ)-lo)*deC s r lo mode)=true
private theorem test {lo hi h:ℕ} {s :Shape} {r mode :ℕ} (hl:lo≤h) (hu:h≤hi)
    (hc:Check lo hi s r mode) :Tested h r s mode := by
  obtain ⟨hk,hj,hm,hB,hU,hp,hD,hw₀,hw₁,hz₀,hz₁⟩:=hc
  have hl' : (lo:ℤ)≤h:=Int.ofNat_le.mpr hl
  have hu' : (h:ℤ)≤hi:=Int.ofNat_le.mpr hu
  have hh:=hu.trans hk
  have he (t:ℤ) :biN s r t =
      biN s r lo+(t-lo)*((s.B:ℤ)-2*r) := by
    unfold biN origin
    ring
  have hw:=cck hl' hu' (of_decide_eq_true hw₀) (he hi ▸ of_decide_eq_true hw₁)
  have hJ:s.J≤ s.B:= by omega
  refine ⟨hJ,hU,hp,gMy _ _ _ hh ((he h).symm ▸ hw),?_⟩
  have hz :=cck hl' hu' (of_decide_eq_true hz₀) (of_decide_eq_true hz₁)
  have hs :=mul_le_mul_of_nonneg_left (gxx _ _ _ _ _ hh hj)
    (Int.natCast_nonneg (triangle s.U))
  unfold cXb deC at hz
  rw [← dei s hm hB,scaled_excess s hJ hU (of_decide_eq_true hD)] at hz
  have hphys :bga s=triangle s.U*agU.ad1 s := by
    unfold bga agU.ad1
    rw [Nat.mul_assoc]
  unfold j3 O3
  rw [hphys]
  apply Int.ofNat_lt.mp
  push_cast at hz ⊢
  nlinarith only [hz,hs]
section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option quotPrecheck false in
local notation "checks!" =>
  ⟨by decide,by decide,by decide,by decide,by decide,by decide,(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel),(by decide +kernel)⟩
private theorem free_check (b:RectTail) (i:Ls) :
    Check b.kA.lo (Bs b).hi (free b i) (dI i) 0:= by
  cases b <;> fin_cases i <;> (conv=>congr <;> cbv) <;> exact checks!
private theorem moving_check (b:RectTail) (i:Ls) :
    Check b.kA.lo (Bs b).hi (moving b i) (dI i) 1 := by
  cases b <;> fin_cases i <;> (conv=>congr <;> cbv) <;> exact checks!
private theorem aux_check (b:RectTail) (i:Aux) :
    Check b.kA.lo (Bs b).hi (auxiliary b i) (auxReserve i) 0:= by
  cases b <;> fin_cases i <;> (conv=>congr <;> cbv) <;> exact checks!
end
theorem free_test (b:RectTail) (i:Ls) {h:ℕ} (hl:b.kA.lo≤h)
    (hu:h≤(Bs b).hi) :Tested h (dI i) (free b i) 0 :=
  test hl hu (free_check b i)
theorem moving_test (b:RectTail) (i:Ls) {h:ℕ} (hl:b.kA.lo≤h)
    (hu:h≤(Bs b).hi) :Tested h (dI i) (moving b i) 1 :=
  test hl hu (moving_check b i)
theorem aux_test (b:RectTail) (i:Aux) {h:ℕ} (hl:b.kA.lo≤h)
    (hu:h≤(Bs b).hi) :Tested h (auxReserve i) (auxiliary b i) 0 :=
  test hl hu (aux_check b i)
end qO6e97d
end
