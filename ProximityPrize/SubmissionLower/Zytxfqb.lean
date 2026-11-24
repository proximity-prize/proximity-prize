import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZLt6kU
set_option Elab.async false
section
set_option autoImplicit true
namespace qpECY2d
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
private def d0_0:=s2! 11702 2444 2444 43 8 0x869a5f6e480cf9d714c90131268779201a358d8b2402093244e48022437b0c90019db9af92000794ffb240
private def d0_1 :=s2! 11702 2444 4492 44 8 0xc16fd415300b5358f55300a7c9aa95300992c25d5300895d0115300785c3c553006639cb3cc2954264b1b240
private def d0_2 :=s2! 11702 2444 6540 44 8 0xf8477a15300f59a3555300f1bb5095300ecaacbd5300e668a715300def4e255300d64f7d95300cc7878d5300
private def d0_3:=s2! 11702 2444 8588 44 8 0xe2b72015300e996db55300ef44f695300f3c171d5300f70c4d15300f9258855300fa0d2395300f9c31ed5300
private def d0_4 :=s2! 11702 2444 10636 44 8 0x8647218b24693c8bb450a6a13e33c4414ae85b3cdd63bb47f315300c6ee2e55300d162c995300daa5c4d5300
private def d0_5:=s2! 11702 2444 12684 43 8 0x4d0d44488c0c14dfddd181d7ead91657464c6894d0ba47a8b052a37ade72c70f35d002c467678d9d5c8764
private def d0_6:=s2! 11702 2444 14732 41 8 0x8e9535c81e12b7d18047275648c054d71054604d2f6ec2303ccec4ad182bcf75fc8c1db30b51460
private def r0:=j2! 11702 2444 0x1c69affdd747b [d0_0,d0_1,d0_2,d0_3,d0_4,d0_5,d0_6]
def dataL:Array aqm := #[
  r0
]
end qpECY2d
end
section
set_option autoImplicit true
namespace qKlO94b
open Finset qBZoH8d
open cu (Shape triangle)
open agU (Xq)
def C (s :Shape) (t n:ℕ) :ℕ := ∑ q∈range n,paddedColumns s t q
def R (s :Shape) (t n:ℕ) :ℕ := ∑ q∈range n,Xq s.B s.J t q
def tail (s :Shape) (t k l:ℕ) :ℕ :=
  min (R s t (k+1)) (C s t (k+1) - C s t l)
private theorem bVH (s :Shape) (t u k :ℕ) :
    xR s t u k=tail s t (min k s.B) (k-u) := by
  have hh:k-u≤ min k s.B+1∨min k s.B+1<k-u:= by omega
  unfold xR tail C R
  rcases hh with h | h
  · have he :=sum_Ico_consecutive (paddedColumns s t) (Nat.zero_le (k-u)) h
    rw [Nat.Ico_zero_eq_range,Nat.Ico_zero_eq_range] at he
    rw [show ∑ q∈Ico (k-u) (min k s.B+1),paddedColumns s t q =
         (∑ q∈range (min k s.B+1),paddedColumns s t q) -
           ∑ q∈range (k-u),paddedColumns s t q by omega,min_comm]
  · rw [Ico_eq_empty_of_le h.le,sum_empty,zero_min,Nat.sub_eq_zero_of_le,_root_.min_zero]
    exact sum_le_sum_of_subset (range_mono h.le)
private theorem zero_start (s :Shape) (t k :ℕ) :
    tail s t k 0=R s t (k+1) := by
  unfold tail C
  simp only [range_zero,sum_empty,Nat.sub_zero]
  apply min_eq_left
  exact sum_le_sum fun q _ =>
    (min_le_left ..).trans
      (Nat.sub_le_sub_right (Nat.add_le_add_right (min_le_min_left _ (min_le_left ..)) 1) _)
private theorem split_window (s :Shape) (t u:ℕ) :
    (∑ k∈range (s.B+u+1),xR s t u k) =
      (∑ k∈range (u+1),R s t (min k s.B+1)) +
      ∑ j∈range s.B,tail s t (min (u+(j+1)) s.B) (j+1) := by
  rw [show s.B+u+1=(u+1)+s.B by omega,sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro k hk
    rw [bVH,Nat.sub_eq_zero_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk)),zero_start]
  · apply sum_congr rfl
    intro j _
    rw [bVH,show u+1+j=u+(j+1) by omega,Nat.add_sub_cancel_left]
private theorem rectangle_zero (s :Shape) (t U:ℕ) :
    (∑ u∈range (U+1),∑ k∈range (u+1),R s t (min k s.B+1)) =
      ∑ k∈range (U+1),(U+1-k)*R s t (min k s.B+1) := by
  simpa only [Nat.Ico_zero_eq_range,sum_const,Nat.card_Ico,Nat.nsmul_eq_mul] using
    (sum_Ico_Ico_comm 0 (U+1) (fun k _=>R s t (min k s.B+1))).symm
private theorem cHX (s :Shape) (t U l:ℕ) (hl:l≤ s.B)
    (hU:s.B≤U) :
    (∑ u∈range (U+1),tail s t (min (u+l) s.B) l) =
      (∑ k∈Ico l s.B,tail s t k l)+(U+1-s.B+l)*tail s t s.B l:= by
  have h:s.B-l≤U+1 := by omega
  have hs :=sum_range_add (fun u=>tail s t (min (u+l) s.B) l) (s.B-l) (U+1-(s.B-l))
  rw [Nat.add_sub_of_le h] at hs
  rw [hs,sum_Ico_eq_sum_range]
  congr 1
  · apply sum_congr rfl
    intro u hu
    have hu' := mem_range.mp hu
    rw [min_eq_left (show u+l≤ s.B by omega),Nat.add_comm]
  · have hh: (∑ u∈range (U+1-(s.B-l)),tail s t (min (s.B-l+u+l) s.B) l) =
          ∑ _u∈range (U+1-(s.B-l)),tail s t s.B l:= by
      apply sum_congr rfl
      intro u _
      rw [min_eq_right (show s.B≤ s.B-l+u+l by omega)]
    simpa only [sum_const,card_range,Nat.nsmul_eq_mul,
      show U+1-(s.B-l)=U+1-s.B+l by omega] using hh
private theorem zero_total (s :Shape) (t:ℕ) (hU:s.B≤ s.U) :
    (∑ k∈range (s.U+1),(s.U+1-k)*R s t (min k s.B+1)) =
      (∑ k∈range s.B,(s.U+1-s.B+(s.B-k))*R s t (k+1)) +
        triangle (s.U-s.B)*R s t (s.B+1) := by
  have hs :=sum_range_add (fun k=>(s.U+1-k)*R s t (min k s.B+1)) s.B (s.U+1-s.B)
  rw [Nat.add_sub_of_le (show s.B≤ s.U+1 by omega)] at hs
  rw [hs]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    rw [min_eq_left hk'.le,show s.U+1-k=s.U+1-s.B+(s.B-k) by omega]
  · let n:=s.U+1-s.B
    have he :n=s.U-s.B+1 := by dsimp [n]; omega
    have hf (k :ℕ) :s.U+1-(s.B+k)=n-k := by dsimp [n]; omega
    simp only [hf,min_eq_right (Nat.le_add_right s.B _),← sum_mul]
    congr 1
    rw [show (∑ k∈range n,(n-k)) = ∑ k∈range n,(k+1) by
      calc
        _ = ∑ k∈range n,(n-1-k+1) :=sum_congr rfl fun k hk=> by
          have :=mem_range.mp hk
          omega
        _ = _:=sum_range_reflect (fun k=>k+1) n]
    have hn:=sum_range_succ' (fun k :ℕ=>k) n
    simp only [add_zero] at hn
    rw [← hn,sum_range_id,Nat.add_sub_cancel,triangle,he,Nat.mul_comm]
def mid (s :Shape) (t:ℕ) :ℕ :=
  ∑ k∈range s.B,(R s t (k+1)+tail s t s.B (k+1))
def extra (s :Shape) (t:ℕ) :ℕ :=
  ∑ k∈range s.B,((s.B-k)*R s t (k+1)+(k+1)*tail s t s.B (k+1) +
    ∑ j∈range k,tail s t k (j+1))
private theorem offset_rank (s :Shape) (t:ℕ) (hU:s.B≤ s.U) :
    (∑ r∈range (s.U+1),∑ k∈range (s.B+(s.U-r)+1),xR s t (s.U-r) k) =
      triangle (s.U-s.B)*R s t (s.B+1)+(s.U+1-s.B)*mid s t+extra s t:= by
  rw [show (∑ r∈range (s.U+1),∑ k∈range (s.B+(s.U-r)+1),xR s t (s.U-r) k) =
    ∑ u∈range (s.U+1),∑ k∈range (s.B+u+1),xR s t u k by
    simpa only [Nat.add_sub_cancel] using
      sum_range_reflect (fun u => ∑ k∈range (s.B+u+1),xR s t u k) (s.U+1)]
  simp only [split_window,sum_add_distrib]
  rw [rectangle_zero,zero_total s t hU,sum_comm (γ:=ℕ)]
  have he :
      (∑ j∈range s.B,∑ u∈range (s.U+1),tail s t (min (u+(j+1)) s.B) (j+1)) =
        (∑ k∈range s.B,∑ j∈range k,tail s t k (j+1)) +
          ∑ j∈range s.B,(s.U+1-s.B+(j+1))*tail s t s.B (j+1) := by
    calc
      _=(∑ j∈range s.B,∑ k∈Ico (j+1) s.B,tail s t k (j+1)) +
            ∑ j∈range s.B,(s.U+1-s.B+(j+1))*tail s t s.B (j+1) := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j hj=>cHX s t s.U (j+1) (mem_range.mp hj) hU
      _ = _:= by
        congr 1
        simpa only [Nat.Ico_zero_eq_range] using
          sum_Ico_Ico_comm' 0 s.B (fun j k=>tail s t k (j+1))
  rw [he]
  simp only [mid,extra,add_mul,mul_add,mul_sum,sum_add_distrib]
  ac_rfl
theorem rank_eq (s :Shape) (hU:s.B≤ s.U) :
    paddedRank s =
      triangle (s.U-s.B)*(∑ t∈range (s.B+2*s.J),R s t (s.B+1)) +
      (s.U+1-s.B)*(∑ t∈range (s.B+2*s.J),mid s t) +
      ∑ t∈range (s.B+2*s.J),extra s t:= by
  simp only [paddedRank,offset_rank s _ hU,sum_add_distrib,mul_sum]
end qKlO94b
end
section
set_option autoImplicit true
namespace qKlO94b
open Finset jQ
open cu (Shape triangle)
open agU (Xq)
open qBZoH8d (paddedColumns paddedRank)
open private fSV fSX eLv from ProximityPrize.SubmissionLower.Z1sUWDe
def col (J t n:ℕ) :ℕ:=(buF n (J-t) - buF n (J+1))/6
def weight (J t n:ℕ) :ℕ:=(bK1 n (J-t) - bK1 n (J+1))/6
def piv (B J t n:ℕ) :ℕ:=bKt B J t (buF n)/6
private theorem col_ramp (s :Shape) (t q:ℕ) :
    paddedColumns s t q+Fu (s.J+1) q=Fu (s.J-t) q:= by
  unfold paddedColumns Fu
  omega
private theorem col_eval (s :Shape) (t n:ℕ) :col s.J t n=C s t n:= by
  unfold col C
  rw [← fSV,← fSV,← Nat.mul_sub_left_distrib,Nat.mul_div_cancel_left _ (by decide)]
  have he : (∑ q∈range n,paddedColumns s t q)+(∑ q∈range n,Fu (s.J+1) q) =
      (∑ q∈range n,Fu (s.J-t) q) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun q _=>col_ramp s t q
  rw [← he,Nat.add_sub_cancel]
private theorem weight_eval (s :Shape) (t n:ℕ) :
    weight s.J t n = ∑ q∈range n,q*paddedColumns s t q:= by
  unfold weight
  rw [← fSX,← fSX,← Nat.mul_sub_left_distrib,Nat.mul_div_cancel_left _ (by decide)]
  have he :=sum_congr (s₁:=range n) rfl (fun q _ =>
    congrArg (q * ·) (col_ramp s t q))
  simp only [Nat.mul_add,sum_add_distrib] at he
  omega
private theorem piv_eval (s :Shape) (t n:ℕ) :piv s.B s.J t n=R s t n:= by
  unfold piv bKt R
  simp only [← fSV,← Nat.mul_add,← Nat.mul_sub_left_distrib,
    Nat.mul_div_cancel_left _ (by decide :0<6)]
  have he :=sum_congr (s₁:=range n) rfl (fun q _=>eLv s.B s.J t q)
  simp only [sum_add_distrib] at he
  omega
private def colTotal (J t n:ℕ) :ℕ:=n*col J t n - weight J t n
private theorem colTotal_eval (s :Shape) (t n:ℕ) :
    colTotal s.J t n = ∑ i∈range n,C s t (i+1) := by
  unfold colTotal
  rw [col_eval,weight_eval]
  have he :
      (∑ i∈range n,C s t (i+1)) = ∑ q∈range n,(n-q)*paddedColumns s t q:= by
    unfold C
    simpa only [Nat.Ico_zero_eq_range,sum_const,Nat.card_Ico,Nat.nsmul_eq_mul] using
      (sum_Ico_Ico_comm 0 n (fun q _=>paddedColumns s t q)).symm
  rw [he]
  have h:=sum_congr (s₁:=range n) rfl (fun q hq=> calc
    (n-q)*paddedColumns s t q+q*paddedColumns s t q =
        (n-q+q)*paddedColumns s t q:=(Nat.add_mul ..).symm
    _=n*paddedColumns s t q:= by rw [Nat.sub_add_cancel (mem_range.mp hq).le])
  rw [sum_add_distrib,← mul_sum] at h
  unfold C
  omega
private def stretch (J t D:ℕ) :ℕ :=
  let a :=J-t
  let w:=J+1-a
  let N :=w*(w+1)/2
  if D =0 then a else
    if D ≤N then a+cud D 8 0 (w+1) else a+w+(D-N)/w
private def zo (J t k c r gd:ℕ) :ℕ :=
  let a :=min k (stretch J t (c-r))
  a*r+((k-a)*c-(gd - colTotal J t a))
private theorem early_bound (s :Shape) (t k :ℕ) :
    (∑ j∈range k,tail s t k (j+1)) ≤
      zo s.J t k (C s t (k+1)) (R s t (k+1)) (∑ j∈range k,C s t (j+1)) := by
  let c:=C s t (k+1)
  let r :=R s t (k+1)
  let a :=min k (stretch s.J t (c-r))
  have ha :a≤k :=min_le_left _ _
  unfold zo
  simp only [colTotal_eval]
  change _≤a*r+((k-a)*c -
    ((∑ j∈range k,C s t (j+1)) - ∑ j∈range a,C s t (j+1)))
  have hs (f :ℕ→ℕ) : (∑ j∈range k,f j) =
      (∑ j∈range a,f j) + ∑ j∈range (k-a),f (a+j) := by
    simpa only [Nat.add_sub_of_le ha] using sum_range_add f a (k-a)
  rw [hs (fun j=>tail s t k (j+1)),hs (fun j=>C s t (j+1)),Nat.add_sub_cancel_left]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _j∈range a,r :=sum_le_sum fun _ _=>min_le_left _ _
      _ = _:= by simp
  · apply Nat.le_sub_of_add_le
    rw [← sum_add_distrib]
    calc
      _ ≤ ∑ _j∈range (k-a),c:= by
        apply sum_le_sum
        intro j hj
        have hj' := mem_range.mp hj
        have hsmall:C s t (a+j+1)≤ c:=sum_le_sum_of_subset
          (range_mono (show a+j+1≤k+1 by omega))
        have hmin:tail s t k (a+j+1)≤ c - C s t (a+j+1) :=min_le_right _ _
        omega
      _ = _:= by simp
def totalPiv (B J t:ℕ) :ℕ:=piv B J t (B+1)
private def lastTail (B J t l:ℕ) :ℕ :=
  min (totalPiv B J t) (col J t (B+1) - col J t l)
def middle (B J t:ℕ) :ℕ :=
  m8 (fun k=>piv B J t (k+1)+lastTail B J t (k+1)) B
private structure bi9 where
  cols :ℕ
  rows :ℕ
  gd:ℕ
  edgeSum:ℕ
private def step (B J t k :ℕ) (x :bi9) :bi9 :=
  let c:=x.cols+(min k J+1-(J-t))
  let r :=x.rows+Xq B J t k
  let l:=min (totalPiv B J t) (col J t (B+1)-c)
  ⟨c,r,x.gd+c,x.edgeSum+((B-k)*r+(k+1)*l+zo J t k c r x.gd)⟩
private def run (B J t n:ℕ) :bi9 :=
  Nat.rec ⟨0,0,0,0⟩ (step B J t) n
def remainder (B J t:ℕ) :ℕ:=(run B J t B).edgeSum
private theorem run_ok (s :Shape) (t n:ℕ) :
    let x :=run s.B s.J t n
    x.cols=C s t n∧x.rows=R s t n ∧
      x.gd=(∑ k∈range n,C s t (k+1)) ∧
      (∑ k∈range n,((s.B-k)*R s t (k+1)+(k+1)*tail s t s.B (k+1) +
        ∑ j∈range k,tail s t k (j+1)))≤x.edgeSum:= by
  dsimp only
  induction n with
  | zero=>simp [run,C,R]
  | succ n ih =>
    rw [show run s.B s.J t (n+1)=step s.B s.J t n (run s.B s.J t n) from rfl]
    have hc:C s t (n+1)=C s t n+(min n s.J+1-(s.J-t)) := by
      simp only [C,sum_range_succ,paddedColumns]
    have hr :R s t (n+1)=R s t n+Xq s.B s.J t n:= by
      simp only [R,sum_range_succ]
    simp only [step,ih.1,ih.2.1,ih.2.2.1,← hc,← hr,totalPiv,piv_eval,col_eval]
    refine ⟨True.intro,True.intro,(sum_range_succ _ _).symm,?_⟩
    rw [sum_range_succ]
    exact Nat.add_le_add ih.2.2.2 (Nat.add_le_add_left (early_bound s t n) _)
private theorem lastTail_eq (s :Shape) (t l:ℕ) :lastTail s.B s.J t l=tail s t s.B l:= by
  simp only [lastTail,totalPiv,col_eval,piv_eval,tail]
theorem middle_eq (s :Shape) (t:ℕ) :middle s.B s.J t=mid s t:= by
  simp only [middle,aNC,piv_eval,lastTail_eq,mid]
theorem remainder_le (s :Shape) (t:ℕ) :extra s t≤ remainder s.B s.J t:= by
  exact (run_ok s t s.B).2.2.2
theorem rank_le (s :Shape) (hU:s.B≤ s.U)
    (r m e :ℕ)
    (hr :m8 (totalPiv s.B s.J) (s.B+2*s.J)=r)
    (hm:m8 (middle s.B s.J) (s.B+2*s.J)=m)
    (he :m8 (remainder s.B s.J) (s.B+2*s.J)=e) :
    paddedRank s≤triangle (s.U-s.B)*r+(s.U+1-s.B)*m+e := by
  simp only [aNC,totalPiv,piv_eval] at hr
  simp only [aNC,middle_eq] at hm
  rw [rank_eq s hU,hr,hm,← he,aNC]
  exact Nat.add_le_add_left (sum_le_sum (fun t _=>remainder_le s t)) _
end qKlO94b
end
section
set_option autoImplicit true
namespace qKlO94b
open cu (Shape triangle)
open jQ (m8 d3l)
open qBZoH8d (paddedRank)
structure Totals where
  r :ℕ
  m:ℕ
  e :ℕ
def Totals.plus (a b:Totals) :Totals :=⟨a.r+b.r,a.m+b.m,a.e+b.e⟩
def block (B J start len:ℕ) :Totals :=
  ⟨m8 (fun t=>totalPiv B J (start+t)) len,
    m8 (fun t=>middle B J (start+t)) len,
    m8 (fun t=>remainder B J (start+t)) len⟩
private theorem block_add (B J start n m:ℕ) :
    block B J start (n+m)=(block B J start n).plus (block B J (start+n) m) := by
  simp only [block,Totals.plus,Totals.mk.injEq]
  have h (f :ℕ→ℕ) :
      m8 (fun t=>f (start+t)) (n+m) =
        m8 (fun t=>f (start+t)) n+m8 (fun t=>f (start+n+t)) m :=
    d3l rfl (by simp only [Nat.add_assoc]) rfl rfl
  exact ⟨h _,h _,h _⟩
theorem join {B J start n m:ℕ} {x y :Totals}
    (hx :block B J start n=x) (hy :block B J (start+n) m=y) :
    block B J start (n+m)=x.plus y :=
  (block_add B J start n m).trans (congrArg₂ Totals.plus hx hy)
def unpack (x :ℕ) :Totals :=
  ⟨x % 2^20,(x >>> 20) % 2^30,(x >>> 50) % 2^40⟩
def sumPacked:ℕ→ℕ→Totals
  | _,0=>⟨0,0,0⟩
  | x,n+1=>(unpack x).plus (sumPacked (x >>> 90) n)
structure cL (B J:ℕ) where
  v :Totals
  hr :m8 (totalPiv B J) (B+2*J)=v.r
  hm:m8 (middle B J) (B+2*J)=v.m
  he :m8 (remainder B J) (B+2*J)=v.e
def cL.ofEq {B J:ℕ} {v :Totals} (h:block B J 0 (B+2*J)=v) :cL B J where
  v :=v
  hr := by simpa only [block,zero_add] using congrArg Totals.r h
  hm:= by simpa only [block,zero_add] using congrArg Totals.m h
  he := by simpa only [block,zero_add] using congrArg Totals.e h
def cL.cap {B J:ℕ} (r :cL B J) (U:ℕ) :ℕ :=
  triangle (U-B)*r.v.r+(U+1-B)*r.v.m+r.v.e
theorem cL.bound (s :Shape) (hU:s.B≤ s.U) (r :cL s.B s.J) :
    paddedRank s≤ r.cap s.U :=
  rank_le s hU _ _ _ r.hr r.hm r.he
end qKlO94b
end
