import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.ZGAUtmc
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
namespace q33KzTa
open aR (Shape)
open P6_6
open P6_6_8
open AJ (CL bOw)
open scoped BigOperators
abbrev Test (v :Shape) :Prop :=
  FirstTest v (Cj v)∧0<sharedOrder v∧sharedOrder v≤Cj v ∧
    dot (Lw v) (firstCaps v (Cj v))≤Cj v*laterCap v.t
def block (v :Shape) (i n:ℕ) :ℕ :=
  CL (fun d=>stock (v.scale (i+d+1))) n
theorem block_add (v :Shape) (i m n:ℕ) :
    block v i (m+n)=block v i m+block v (i+m) n:= by
  simp only [block,bOw,Finset.sum_range_add,Nat.add_assoc]
private def slope (j i n:ℕ) :ℕ :=
  CL (fun d=>(i+d+1)*cV (1710-(i+d+1)*j) (570-(i+d+1))) n
def tu (j n a s :ℕ) :Prop :=
  block ⟨0,j,1⟩ 0 n=a∧slope j 0 n=s
theorem base_zero (j:ℕ) :tu j 0 0 0:=⟨rfl,rfl⟩
theorem base_next {j n a s k x y :ℕ} (h:tu j n a s)
    (hx :block ⟨0,j,1⟩ n k=x) (hy :slope j n k=y) :
    tu j (n+k) (a + x) (s+y) := by
  have hs :slope j 0 (n+k)=slope j 0 n+slope j n k := by
    simp only [slope,bOw,Finset.sum_range_add,Nat.zero_add]
  exact ⟨by rw [block_add,Nat.zero_add,h.1,hx],hs.trans (congrArg₂ (· + ·) h.2 hy)⟩
private theorem block_affine {b j n:ℕ} (hj:0<j) (h:AffineFits b j n) :
    block ⟨b,j,1⟩ 0 n+b*slope j 0 n=block ⟨0,j,1⟩ 0 n:= by
  simp only [block,slope,bOw,Nat.zero_add,Finset.mul_sum,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Nat.mul_assoc,Nat.mul_comm b (d+1)]
  simpa only [stock_eq,Shape.scale,Nat.mul_zero,Nat.mul_one] using
    entry_affine hj h (Nat.succ_le_of_lt (Finset.mem_range.mp hd))
theorem prefix_at {b j n k a s m l:ℕ} (h:tu j n a s) (hn:n+k=l - 1)
    (hj:0<j) (hf :AffineFits b j n) (hm:block ⟨b,j,1⟩ n k=m)
    (hb:a - b*s+m<gG) :
    (∑ d∈Finset.range (l - 1),Gq ((⟨b,j,1⟩:Shape).scale (d+1)))<gG:= by
  have he :=block_affine hj hf
  rw [h.1,h.2] at he
  have hfirst:block ⟨b,j,1⟩ 0 n=a - b*s := by omega
  have hsum:block ⟨b,j,1⟩ 0 (l - 1)<gG:= by
    rwa [← hn,block_add,Nat.zero_add,hfirst,hm]
  simpa only [block,bOw,Nat.zero_add,stock_eq] using hsum
theorem join_tail {v :Shape} {n k m x y :ℕ} (hx :block v n k=x)
    (hy :block v (n+k) m=y) :block v n (k+m)=x+y := by
  rw [block_add,hx,hy]
theorem prefix_from {u v :Shape} {l:ℕ} (h:Test u) (hl:Cj u=l)
    (hbox :u.b≤v.b∧u.j≤v.j∧u.t≤v.t) :
    (∑ d∈Finset.range (l - 1),Gq (v.scale (d+1)))<gG:= by
  have ht:=h.1.2.2.2
  rw [hl] at ht
  exact (Finset.sum_le_sum fun d _=>dNb (Q5 hbox (d+1))).trans_lt ht
theorem row {v :Shape} {l q:ℕ}
    (hL:Cj v=l)
    (hl:0<l∧l≤ack)
    (hf : (v.scale l).b≤4025∧(v.scale l).j≤1710∧(v.scale l).t≤570)
    (he :0<sharedOrder v∧sharedOrder v≤l)
    (hm: (∑ d∈Finset.range (l - 1),Gq (v.scale (d+1)))<gG)
    (hq:dot (Lw v) (firstCaps v l)=q)
    (hb:q≤l*laterCap v.t) :Test v := by
  unfold Test
  rw [hL,hq]
  exact ⟨⟨hl.1,hl.2,hf,hm⟩,he.1,he.2,hb⟩
theorem empty_prefix :
    (∑ d∈Finset.range (55 - 1),Gq (oL.scale (d+1)))<gG:= by
  have h (d:ℕ) :oL.scale (d+1)=oL:= by
    simp [Shape.scale,FI.oL]
  simp only [h,empty_stock,Finset.sum_const,Finset.card_range,Nat.nsmul_eq_mul]
  decide
end q33KzTa
