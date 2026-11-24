import ProximityPrize.SubmissionLower.ZTFKldb
set_option Elab.async false
set_option autoImplicit true
namespace qYzmxYc
open Finset
open aR (Shape ao)
open NR (ay8)
open aFN (Slot)
open qzLARrc (derivativeIndex flagMatrix flagRank windowBudget)
open scoped BigOperators
abbrev tops (a :Shape) (q:ℕ) :=min q (min a.t (a.j/2))+1
abbrev mids (a :Shape) (q c:ℕ) :=min (q - c) (a.j - 2*c)+1
def cols (a :Shape) (q k :ℕ) :ℕ :=
  ∑ c∈range (tops a q),(mids a q c-(k - c))
def rows (a :Shape) (q d:ℕ) :ℕ :=
  ∑ c∈range (tops a q),min (mids a q c) (d - 2*c)
def reflected (a :Shape) (q:ℕ) :ℕ :=
  ∑ c∈range (tops a q),∑ b∈range (mids a q c),
    (b+c)*(a.b - q+(b+2*c))
def partialDebit (a :Shape) (q:ℕ) :ℕ :=
  ∑ w∈range q,∑ d∈range a.j,min (cols a q (q - w)) (rows a q (a.j - d))
def j3 (a :Shape) (U q:ℕ) :ℕ :=
  (U + a.b+1 - 2*q)*((a.b+a.j - q)*ay8 a q) +
    reflected a q+partialDebit a q
theorem dga {M:Type*} [AddCommMonoid M] (a :Shape) (q:ℕ) (f :ℕ→ℕ→M) :
    (∑ s :Slot a q,f s.1.val s.2.val) =
      ∑ c∈range (tops a q),∑ b∈range (mids a q c),f c b:= by
  rw [Fintype.sum_sigma]
  simp only [Fin.sum_univ_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun c => ∑ b∈range (mids a q c),f c b) _
private theorem dFD (n lo hi:ℕ) :
    ((range n).filter fun i=>lo≤ i∧i<hi).card=min n hi-lo:= by
  have h: (range n).filter (fun i=>lo≤ i∧i<hi)=Ico lo (min n hi) := by
    ext i
    simp only [mem_filter,mem_range,mem_Ico,Nat.lt_min]
    tauto
  rw [h,Nat.card_Ico]
theorem gxl (n lo hi:ℕ) :
    (∑ i∈range n,if lo≤ i∧i<hi then 1 else 0)=min n hi-lo:= by
  rw [← dFD,card_eq_sum_ones,sum_filter]
private theorem sum_indicator {ι:Type*} [Fintype ι] (p:ι→Prop) [DecidablePred p] :
    ((univ :Finset ι).filter p).card = ∑ s :ι,if p s then 1 else 0:= by
  rw [card_eq_sum_ones,sum_filter]
private theorem slot_idx {a :Shape} {q:ℕ} (s :Slot a q) :
    derivativeIndex s≤a.j:= by
  have hc:=s.1.isLt
  have hb:=s.2.isLt
  simp only [Nat.lt_succ_iff,le_min_iff] at hc hb
  unfold derivativeIndex
  omega
private theorem card_rows (a :Shape) (q d:ℕ) :
    ((univ :Finset (Slot a q)).filter fun s=>derivativeIndex s<d).card=rows a q d:= by
  rw [sum_indicator]
  unfold derivativeIndex rows
  rw [dga a q (fun c b=>if b+2*c<d then 1 else 0)]
  apply sum_congr rfl
  intro c _
  rw [← Nat.sub_zero (min (mids a q c) (d - 2*c)),← gxl]
  apply sum_congr rfl
  intro b _
  have h: (b+2*c<d)↔(0≤b∧b<d - 2*c) := by omega
  simp only [h]
private theorem card_cols (a :Shape) (q w:ℕ) :
    ((univ :Finset (Slot a q)).filter fun s=>q - s.1.val - s.2.val≤w).card =
      cols a q (q - w) := by
  rw [sum_indicator,dga a q (fun c b=>if q - c - b≤w then 1 else 0)]
  unfold cols
  apply sum_congr rfl
  intro c _
  rw [← Nat.min_self (mids a q c),
    ← gxl (mids a q c) (q - w - c) (mids a q c)]
  rw [Nat.min_self]
  apply sum_congr rfl
  intro b hb
  have hb:=mem_range.mp hb
  have h: (q - c - b≤w)↔(q - w - c≤b∧b< mids a q c) := by omega
  simp only [h]
private theorem rank_rows {ι:Type*} [Fintype ι] (M:Matrix ι ι ao)
    (p:ι→Prop) [DecidablePred p] (hz : ∀ r s,¬p r→M r s=0) :
    M.rank≤((univ :Finset ι).filter p).card:= by
  apply Matrix.rank_le_card_of_support_subset
  intro r hr
  exact mem_filter.mpr ⟨mem_univ _,by
    by_contra h
    apply hr
    funext s
    exact hz r s h⟩
private theorem rank_cols {ι:Type*} [Fintype ι] (M:Matrix ι ι ao)
    (p:ι→Prop) [DecidablePred p] (hz : ∀ r s,¬p s→M r s=0) :
    M.rank≤((univ :Finset ι).filter p).card:= by
  rw [← Matrix.rank_transpose M]
  exact rank_rows M.transpose p (fun r s h=>hz s r h)
private theorem full_le (a :Shape) (q:ℕ) (hq:q≤a.b) :
    (∑ i∈range (a.b+2*a.j),flagRank a q ((i:ℤ)-a.j) q) ≤
      (a.b+a.j - q)*ay8 a q:= by
  let UD (i:ℕ) (s :Slot a q) :=
    a.j - derivativeIndex s≤ i∧i<a.b+2*a.j - q - derivativeIndex s
  calc
    _ ≤ ∑ i∈range (a.b+2*a.j),
        ((univ :Finset (Slot a q)).filter (UD i)).card:= by
      apply sum_le_sum
      intro i _
      by_cases hi:i<a.j
      · apply rank_cols
        intro r s hs
        have hidx :=slot_idx s
        unfold flagMatrix
        split
        next h =>
          have h:=h.2.1
          exfalso
          apply hs
          dsimp [UD]
          omega
        next=>rfl
      · apply rank_rows
        intro r s hr
        unfold flagMatrix
        split
        next h =>
          have h:=h.2.2.1
          exfalso
          apply hr
          dsimp [UD]
          omega
        next=>rfl
    _ = _:= by
      simp only [sum_indicator]
      rw [sum_comm]
      have h (s :Slot a q) :
          (∑ i∈range (a.b+2*a.j),if UD i s then 1 else 0) =
            a.b+a.j - q:= by
        have hidx :=slot_idx s
        dsimp [UD]
        rw [gxl,min_eq_right (by omega)]
        omega
      simp only [h,sum_const,nsmul_eq_mul]
      rw [mul_comm]
      congr 1
      rw [card_eq_sum_ones,dga a q (fun _ _=>(1 :ℕ))]
      simp [ay8]
private theorem eNL (a :Shape) (q:ℕ) (hq:q≤a.b) :
    (∑ i∈range (a.b+a.j - q),∑ w∈range q,
        flagRank a q ((i:ℤ)-a.j) w)≤ reflected a q:= by
  let UD (i w:ℕ) (s :Slot a q) :=
    a.j - derivativeIndex s≤ i∧q - s.1.val - s.2.val≤w
  calc
    _ ≤ ∑ i∈range (a.b+a.j - q),∑ w∈range q,
        ((univ :Finset (Slot a q)).filter (UD i w)).card:= by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro w _
      apply rank_cols
      intro r s hs
      unfold flagMatrix
      split
      next h =>
        obtain ⟨hw,hi,_⟩:=h
        exfalso
        apply hs
        dsimp [UD]
        omega
      next=>rfl
    _ = _:= by
      simp only [sum_indicator]
      rw [sum_comm]
      have h (w:ℕ) :
          (∑ i∈range (a.b+a.j - q),∑ s :Slot a q,
              if UD i w s then 1 else 0) =
            ∑ s :Slot a q,if q - s.1.val - s.2.val≤w then
              a.b - q+derivativeIndex s else 0:= by
        rw [sum_comm]
        apply sum_congr rfl
        intro s _
        have hidx :=slot_idx s
        by_cases hw:q - s.1.val - s.2.val≤w
        · simp only [UD,hw,and_true,ite_true]
          calc
            _ = ∑ i∈range (a.b+a.j - q),
                if a.j - derivativeIndex s≤ i∧i<a.b+a.j - q then 1 else 0:= by
                  apply sum_congr rfl
                  intro i hi
                  simp [mem_range.mp hi]
            _ = _:= by rw [gxl,Nat.min_self]; omega
        · simp only [UD,hw,and_false,ite_false,sum_const_zero]
      simp only [h]
      rw [sum_comm]
      unfold reflected
      simp only [derivativeIndex]
      rw [dga a q (fun c b =>
        ∑ w∈range q,if q - c - b≤w then a.b - q+(b+2*c) else 0)]
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro b hb
      have hc:=mem_range.mp hc
      have hb:=mem_range.mp hb
      have hbc:b+c≤q:= by
        simp only [tops,mids,Nat.lt_succ_iff,le_min_iff] at hc hb
        omega
      have hsum: (∑ w∈range q,if q - c - b≤w then 1 else 0)=b+c:= by
        calc
          _ = ∑ w∈range q,if q - c - b≤w∧w<q then 1 else 0:= by
            apply sum_congr rfl
            intro w hw
            simp [mem_range.mp hw]
          _ = _:= by rw [gxl,Nat.min_self]; omega
      have hf (w:ℕ) :
          (if q - c - b≤w then a.b - q+(b+2*c) else 0) =
            (if q - c - b≤w then 1 else 0)*(a.b - q+(b+2*c)) := by
        split <;> simp_all
      simp only [hf,← sum_mul,hsum]
private theorem shifted_le (a :Shape) (q:ℕ) (hq:q≤a.b) (d w:ℕ) :
    flagRank a q (((a.b+a.j - q+d:ℕ) :ℤ)-a.j) w ≤
      min (cols a q (q - w)) (rows a q (a.j - d)) := by
  apply le_min
  · rw [← card_cols]
    apply rank_cols
    intro r s hs
    exact ite_eq_right (fun h=>hs h.1)
  · rw [← card_rows]
    apply rank_rows
    intro r s hr
    refine ite_eq_right (fun h=>hr ?_)
    have h:=h.2.2.1
    omega
theorem aCw (a :Shape) (U:ℕ) :
    windowBudget a U ≤ ∑ q∈range (a.b+1),j3 a U q:= by
  unfold windowBudget
  apply sum_le_sum
  intro q hq
  have hq:q≤a.b:=Nat.lt_succ_iff.mp (mem_range.mp hq)
  rw [sum_add_distrib,← mul_sum]
  unfold j3
  refine (Nat.add_le_add (Nat.mul_le_mul_left _ (full_le a q hq)) ?_).trans_eq
    (Nat.add_assoc _ _ _).symm
  have hlen:a.b+2*a.j=(a.b+a.j - q)+(a.j+q) := by omega
  rw [hlen,sum_range_add]
  apply Nat.add_le_add (eNL a q hq)
  rw [sum_range_add]
  have hz : (∑ d∈range q,∑ w∈range q,
      flagRank a q (((a.b+a.j - q+(a.j+d) :ℕ) :ℤ)-a.j) w)=0:= by
    apply sum_eq_zero
    intro d _
    apply sum_eq_zero
    intro w _
    have h:=shifted_le a q hq (a.j+d) w
    simp [rows] at h
    exact h
  rw [hz,Nat.add_zero]
  unfold partialDebit
  rw [sum_comm (s :=range q) (t:=range a.j)]
  exact sum_le_sum fun d _=>sum_le_sum fun w _=>shifted_le a q hq d w
end qYzmxYc
