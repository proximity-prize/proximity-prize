import ProximityPrize.SubmissionLower.R6966ProofPadeCutoff

set_option Elab.async false

namespace Research6966.SpreadBucket
open Finset
open K1_14 (Shape shapeSum)
open KoalaRect (rectDebit rectPower area)
open PadeCutoff (capacity excluded)

private theorem order_iff {A h W k:ℕ} {s:Shape} (hp:0<h) (hw:W<s.m*A) :
    rectPower A h s W=k+1 ↔
      s.m*A-2*h*(k+1)≤W ∧ W<s.m*A-2*h*k := by
  have a:=K1_14_4.power_threshold (s.m*A) (2*h) W 0 k hw (by omega)
  have b:=K1_14_4.power_threshold (s.m*A) (2*h) W 0 (k+1) hw (by omega)
  simp only [Nat.zero_add,Nat.sub_zero] at a b
  unfold rectPower
  omega

/-- There are at most two height units of cutoff for each Hasse order.
The cost function is indexed by positive orders. -/
theorem sum_by_order {s:Shape} {A h K scale:ℕ} (hp:0<h) (F cost:ℕ→ℕ)
    (live:∀ W<s.m*A,rectPower A h s W≤K →
      F W≤scale*cost (rectPower A h s W))
    (tail:∀ W<s.m*A,K<rectPower A h s W → F W=0) :
    ∑ W∈range (s.m*A),F W ≤ scale*(2*h)*(∑ k∈range K,cost (k+1)) := by
  let N:=s.m*A
  let power:=rectPower A h s
  have atW (W:ℕ) (hw:W<N) : F W ≤
      ∑ k∈range K, if power W=k+1 then scale*cost (k+1) else 0 := by
    by_cases high:K<power W
    · rw [tail W hw high];exact Nat.zero_le _
    · have one:0<power W:=Nat.add_pos_left Nat.one_pos _
      rw [sum_eq_single (power W-1)]
      · rw [Nat.sub_add_cancel one,if_pos rfl]
        exact live W hw (Nat.le_of_not_gt high)
      · intro j _ ne
        rw [if_neg (by omega)]
      · intro absent
        exact False.elim (absent (mem_range.mpr (by omega)))
  have count (k:ℕ) :
      (∑ W∈range N, if power W=k+1 then scale*cost (k+1) else 0) ≤
        (2*h)*(scale*cost (k+1)) := by
    rw [←sum_filter]
    have same : (range N).filter (fun W=>power W=k+1)=Ico (N-2*h*(k+1)) (N-2*h*k) := by
      ext W
      simp only [mem_filter,mem_range,mem_Ico]
      constructor
      · rintro ⟨hw,eq⟩
        exact (order_iff hp hw).mp eq
      · intro bounds
        have hw:W<N:=bounds.2.trans_le (Nat.sub_le ..)
        exact ⟨hw,(order_iff hp hw).mpr bounds⟩
    rw [same,sum_const,Nat.card_Ico,nsmul_eq_mul]
    apply Nat.mul_le_mul_right
    change N-2*h*k-(N-2*h*(k+1))≤2*h
    rw [Nat.mul_succ]
    omega
  calc
    _ ≤ ∑ W∈range N, ∑ k∈range K, if power W=k+1 then scale*cost (k+1) else 0 :=
      sum_le_sum fun W hw=>atW W (mem_range.mp hw)
    _ = _ := sum_comm
    _ ≤ ∑ k∈range K,(2*h)*(scale*cost (k+1)) := sum_le_sum fun k _=>count k
    _ = _ := by simp only [←mul_sum];ring

theorem sum_capacity {s:Shape} {A h e a n K:ℕ} {U:Fin 2→ℕ}
    (hp:0<h) (cost:ℕ→ℕ)
    (live:∀ W<s.m*A,rectPower A h s W≤K →
      capacity A h e a n s U W≤area U*cost (rectPower A h s W))
    (tail:∀ W<s.m*A,K<rectPower A h s W → capacity A h e a n s U W=0) :
    ∑ W∈range (s.m*A),capacity A h e a n s U W ≤
      area U*(2*h)*(∑ k∈range K,cost (k+1)) := sum_by_order hp _ cost live tail

def raw (s:Shape) (A h:ℕ) := shapeSum s (fun q j=>s.m*A+j-q*(131071-h))
def slope (s:Shape) := shapeSum s (fun q _=>q)

theorem raw_affine {s:Shape} {A lo h:ℕ} (left:lo≤h) (endH:h≤131071)
    (full:s.B*(131071-lo)≤s.m*A) : raw s A h=raw s A lo+(h-lo)*slope s := by
  unfold raw slope shapeSum
  simp only [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro j _
  have bound: q*(131071-lo)≤s.m*A:=(Nat.mul_le_mul_right _ (by have:=mem_range.mp hq;omega)).trans full
  have steps : (131071-h)+(h-lo)=131071-lo := by omega
  have e : q*(131071-h)+(h-lo)*q=q*(131071-lo) := by
    rw [Nat.mul_comm (h-lo) q,←Nat.mul_add,steps]
  omega

theorem affine_pos {C V B P lo hi h:ℕ} (left:lo≤h) (right:h≤hi)
    (first:P+lo*B<C) (last:P+hi*B<C+(hi-lo)*V) : P+h*B<C+(h-lo)*V := by
  have split1 : h*B=lo*B+(h-lo)*B := by rw [←Nat.add_mul,show lo+(h-lo)=h by omega]
  have split2 : hi*B=h*B+(hi-h)*B := by rw [←Nat.add_mul,show h+(hi-h)=hi by omega]
  have split3 : (hi-lo)*V=(h-lo)*V+(hi-h)*V := by rw [←Nat.add_mul,show (h-lo)+(hi-h)=hi-lo by omega]
  rcases le_total B V with b|v
  · have := Nat.mul_le_mul_left (h-lo) b
    omega
  · have := Nat.mul_le_mul_left (hi-h) v
    omega

/-- A capacity bound shared by a whole height interval needs two scalar
rank comparisons, since the full physical bank is affine throughout it. -/
theorem excluded_of_endpoints {s:Shape} {A e a n nodes moment lo hi h sum:ℕ} {U:Fin 2→ℕ}
    (left:lo≤h) (right:h≤hi) (lastHeight:hi≤131071) (full:s.B*(131071-lo)≤s.m*A)
    (cap:∑ W∈range (s.m*A),capacity A h e a n s U W≤area U*(2*h)*sum)
    (first:rectDebit lo nodes moment U+area U*(2*lo)*sum<area U*raw s A lo)
    (last:rectDebit hi nodes moment U+area U*(2*hi)*sum<area U*raw s A hi) :
    excluded A h e a n s U nodes moment := by
  let B:=(U 0+U 1+2)*moment+2*area U*sum
  have charge (t:ℕ) : rectDebit t nodes moment U+area U*(2*t)*sum=area U*nodes+t*B := by
    unfold rectDebit B;ring
  have supply (t:ℕ) (l:lo≤t) (r:t≤hi) : area U*raw s A t =
      area U*raw s A lo+(t-lo)*(area U*slope s) := by
    rw [raw_affine l (r.trans lastHeight) full];ring
  rw [charge] at first
  rw [charge,supply hi (left.trans right) le_rfl] at last
  have core:=affine_pos left right first last
  unfold excluded
  apply (Nat.add_le_add_left cap _).trans_lt
  change rectDebit h nodes moment U+area U*(2*h)*sum<area U*raw s A h
  rwa [charge,supply h left right]

#print axioms sum_capacity
#print axioms excluded_of_endpoints
end Research6966.SpreadBucket
