import ProximityPrize.SubmissionLower.R6966ProofPadeCutoff

set_option Elab.async false

-- merged module R6966ProofSpreadStrip
section Merged_R6966ProofSpreadStrip

namespace Research6966.SpreadStrip
open Finset PadeRank

private theorem widths (b j : ℕ) :
    (positions b j).card = ∑ i ∈ range j, (b-i) := by
  classical
  unfold positions
  rw [card_filter,sum_product]
  apply sum_congr rfl
  intro i _
  change (∑ x ∈ range b, if i+x<b then 1 else 0)=b-i
  rw [← card_filter]
  have eq : (range b).filter (fun x => i+x<b)=range (b-i) := by
    ext x
    simp only [mem_filter,mem_range]
    omega
  rw [eq,card_range]

/-- Exact new symbols on restriction to a primitive slope graph. Both
shape bounds are exclusive; the last slope grades can have fewer columns. -/
theorem slice (b j a : ℕ) :
    (positions (b+1) (j+1)).card - (positions ((b+1)-(a+1)) j).card =
      (b+1) + ∑ i ∈ range (min b j), min a (b-i) := by
  rw [widths,widths,sum_range_succ']
  simp only [Nat.sub_zero,Nat.succ_sub_succ_eq_sub]
  have e : (∑ i ∈ range j, (b-i)) =
      (∑ i ∈ range j, (b-a-i)) + ∑ i ∈ range j, min a (b-i) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    omega
  have f : (∑ i ∈ range j, min a (b-i))=∑ i ∈ range (min b j), min a (b-i) := by
    symm; apply sum_subset (range_mono (Nat.min_le_right ..))
    intro i hi cut
    simp only [mem_range,lt_min_iff] at *
    omega
  omega

private theorem deficits (b j a : ℕ) :
    (∑ i ∈ range (min b j), (a-(b-i))) ≤ ∑ i ∈ range a, i := by
  classical
  let s := (range (min b j)).filter (fun i => 0<a-(b-i))
  let f := fun i : ℕ => a-(b-i)
  have eq : (∑ i ∈ s, f i)=∑ i ∈ range (min b j), f i := by
    apply sum_subset (filter_subset ..)
    intro i hi outside
    simp only [mem_filter,hi,true_and,not_lt] at outside
    change a-(b-i)=0
    omega
  rw [←eq]
  have inj : Set.InjOn f ↑s := by
    intro i hi k hk same
    simp only [s,Finset.mem_coe,mem_filter,mem_range,lt_min_iff] at hi hk
    dsimp [f] at same
    omega
  have sub : s.image f⊆range a := by
    intro i hi
    obtain ⟨k,hk,rfl⟩:=mem_image.mp hi
    simp only [s,mem_filter,mem_range,lt_min_iff] at hk
    simp only [mem_range,f]
    omega
  have im : (∑ i ∈ s.image f, i)=∑ i ∈ s, f i := sum_image (f:=id) inj
  rw [← im]
  exact sum_le_sum_of_subset_of_nonneg sub (by intros; omega)

theorem slice_with_tail (b j a : ℕ) :
    b+1 + a*min b j ≤ (positions (b+1) (j+1)).card -
      (positions ((b+1)-(a+1)) j).card + ∑ i ∈ range a, i := by
  rw [slice]
  have e : (∑ i ∈ range (min b j), min a (b-i)) +
      (∑ i ∈ range (min b j), (a-(b-i)))=a*min b j := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ _ ∈ range (min b j), a := sum_congr rfl fun i _ => by omega
      _ = _ := by simp [Nat.mul_comm]
  have d:=deficits b j a
  omega

theorem slice_full {b j a:ℕ} (room:j+a≤b+1) :
    (positions (b+1) (j+1)).card - (positions ((b+1)-(a+1)) j).card =
      b+1+a*min b j := by
  rw [slice]
  congr 1
  calc
    _=∑ _ ∈ range (min b j), a := by
      apply sum_congr rfl
      intro i hi
      simp only [mem_range,lt_min_iff] at hi
      omega
    _=_ := by simp [Nat.mul_comm]

end Research6966.SpreadStrip

end Merged_R6966ProofSpreadStrip

-- merged module R6966ProofSpreadLines
section Merged_R6966ProofSpreadLines

namespace Research6966.SpreadLines
open Finset

def affine (b s n : ℕ) := n*b-s*(n*(n-1)/2)

private theorem affine_sum (b s n:ℕ) (last:s*(n-1)≤b) :
    (∑ i∈range n,(b-s*i))=affine b s n := by
  have e : (∑ i∈range n,(b-s*i)) + ∑ i∈range n,s*i = n*b := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ _∈range n,b := by
        apply sum_congr rfl
        intro i hi
        exact Nat.sub_add_cancel ((Nat.mul_le_mul_left s (by have := mem_range.mp hi; omega)).trans last)
      _ = _ := by simp
  rw [←mul_sum,Finset.sum_range_id] at e
  unfold affine
  omega

private theorem between {b s c t i last:ℕ} (first:b≤c)
    (endPt:b+t*last≤c+s*last) (hi:i≤last) : b+t*i≤c+s*i := by
  by_cases h:t≤s
  · exact Nat.add_le_add first (Nat.mul_le_mul_right i h)
  · have eq : t=s+(t-s) := by omega
    have e (k:ℕ) : t*k=s*k+(t-s)*k := calc
      t*k = (s+(t-s))*k := congrArg (·*k) eq
      _=_ := Nat.add_mul ..
    rw [e last] at endPt
    rw [e i]
    have := Nat.mul_le_mul_left (t-s) hi
    omega

def segment (b s c t n : ℕ) : ℕ :=
  if s*(n-1)≤b ∧ t*(n-1)≤c ∧ b≤c ∧ b+t*(n-1)≤c+s*(n-1)
  then affine b s n else 0

private theorem segment_le (b s c t n:ℕ) :
    segment b s c t n≤∑ i∈range n,min (b-s*i) (c-t*i) := by
  unfold segment
  split
  · rename_i ok
    rw [←affine_sum b s n ok.1]
    apply sum_le_sum
    intro i hi
    have hh:i≤n-1:=by have := mem_range.mp hi;omega
    have ordered:=between ok.2.2.1 ok.2.2.2 hh
    have low: s*i≤b:=(Nat.mul_le_mul_left _ hh).trans ok.1
    have high:t*i≤c:=(Nat.mul_le_mul_left _ hh).trans ok.2.1
    omega
  · exact Nat.zero_le _

/-- An unchecked proposed crossing is safe because both selected lines
are tested at both ends of their own segment. -/
def splitLower (b s c t n pivot:ℕ) : ℕ :=
  let k:=min n pivot
  segment c t b s k + segment (b-s*k) s (c-t*k) t (n-k)

theorem split_le (b s c t n pivot:ℕ) :
    splitLower b s c t n pivot ≤ ∑ i∈range n,min (b-s*i) (c-t*i) := by
  let k:=min n pivot
  have add : k+(n-k)=n := by dsimp [k];omega
  calc
    _ ≤ (∑ i∈range k,min (c-t*i) (b-s*i)) +
          ∑ i∈range (n-k),min ((b-s*k)-s*i) ((c-t*k)-t*i) :=
      Nat.add_le_add (segment_le ..) (segment_le ..)
    _ = ∑ i∈range (k+(n-k)),min (b-s*i) (c-t*i) := by
      rw [sum_range_add]
      congr 1
      · exact sum_congr rfl fun _ _ => min_comm ..
      · exact sum_congr rfl fun _ _ => by simp only [Nat.mul_add,Nat.sub_sub]
    _ = _ := by rw [add]

def minSum (b s c t n:ℕ) : ℕ :=
  if s=t then segment (min b c) s (max b c) t n
  else if t<s then splitLower b s c t n ((b-c+(s-t)-1)/(s-t))
  else splitLower c t b s n ((c-b+(t-s)-1)/(t-s))

theorem minSum_le (b s c t n:ℕ) :
    minSum b s c t n ≤ ∑ i∈range n,min (b-s*i) (c-t*i) := by
  unfold minSum
  split
  · rename_i eq
    subst t
    rcases le_total b c with h|h
    · simpa [min_eq_left h,max_eq_right h] using segment_le b s c s n
    · simp only [min_eq_right h,max_eq_left h]
      simpa only [min_comm] using segment_le c s b s n
  · split
    · exact split_le ..
    · simpa only [min_comm] using split_le c t b s n ((c-b+(t-s)-1)/(t-s))

end Research6966.SpreadLines

end Merged_R6966ProofSpreadLines

-- merged module R6966ProofSpreadGain
section Merged_R6966ProofSpreadGain

namespace Research6966.SpreadGain
open Finset PadeRank
set_option maxHeartbeats 1100000

def count (a B J k : ℕ) : ℕ := min k (min (J+1) (B/a+1))

def full (a B J m : ℕ) : ℕ := min m ((B-J)/(a-1))

def pivot (a B J m : ℕ) : ℕ := if J ≤ B then min m ((B-J)/(a-1)+1) else 0

def loss (a : ℕ) : ℕ := (a-1)*(a-2)/2

def lower (B J a n k : ℕ) : ℕ :=
  let m := count a B J k
  if a = 1 then SpreadLines.minSum (B+1) 1 (n*k) n m else
    let f := full a B J m
    let p := pivot a B J m
    let first := SpreadLines.minSum (B+(a-1)*J+1) (2*a-1) (n*k) n p
    let tail := SpreadLines.minSum (a*(B-a*p)+1) (a*a) (n*(k-p)) n (m-p)
    first+(tail-(m-p)*loss a)-(p-f)*loss a

private def slot (a n k b j i : ℕ) : ℕ :=
  let B := b-a*i
  let J := j-i
  if B = 0 ∨ J = 0 then 0 else
    (positions B J).card-(positions (B-a) (J-1)).card-imageAllowance B J a n (k-i)

private theorem gain_sum (a n k b j : ℕ) :
    gain a n k b j = ∑ i ∈ range k, slot a n k b j i := by
  induction k generalizing b j with
  | zero => simp [gain]
  | succ k ih =>
    rw [gain]
    by_cases zero : b=0 ∨ j=0
    · rw [ite_eq_left zero]
      symm
      apply sum_eq_zero
      intro i _
      rcases zero with zb | zj
      · simp [slot,zb]
      · simp [slot,zj]
    · rw [ite_eq_right zero, ih, sum_range_succ']
      have next (i : ℕ) : slot a n (k+1) b j (i+1) = slot a n k (b-a) (j-1) i := by
        have hb : b-a*(i+1)=(b-a)-a*i := by rw [Nat.mul_add,Nat.mul_one,Nat.sub_sub,Nat.add_comm (a*i)]
        have hj : j-(i+1)=(j-1)-i := by omega
        have hk : k+1-(i+1)=k-i := by omega
        simp only [slot,hb,hj,hk]
      rw [show (∑ i ∈ range k, slot a n (k+1) b j (i+1)) = ∑ i ∈ range k, slot a n k (b-a) (j-1) i from
        sum_congr rfl (fun i _ => next i)]
      simp only [slot,Nat.mul_zero,Nat.sub_zero,ite_eq_right zero]
      exact Nat.add_comm _ _

private def width (a b j : ℕ) : ℕ := b+1+(a-1)*min b j

private def strip (a b j : ℕ) : ℕ :=
  (positions (b+1) (j+1)).card - (positions (b+1-a) j).card

private theorem full_strip (a b j : ℕ) (ap : 0 < a)
    (room : a=1 ∨ j+(a-1)≤b+1) : strip a b j = width a b j := by
  have aa : a-1+1=a := Nat.sub_add_cancel ap
  rcases room with one | fits
  · subst a
    simpa [strip,width] using SpreadStrip.slice b j 0
  · simpa only [strip,width,aa] using (SpreadStrip.slice_full (b:=b) (j:=j) (a:=a-1) fits)

private theorem all_strips (a b j : ℕ) (ap : 0 < a) : width a b j ≤ strip a b j+loss a := by
  have aa : a-1+1=a := Nat.sub_add_cancel ap
  have estimate := SpreadStrip.slice_with_tail b j (a-1)
  rw [sum_range_id, Nat.sub_sub, show 1+1=2 by decide, aa] at estimate
  exact estimate

private theorem width_mono (a j : ℕ) {lo hi : ℕ} (le : lo ≤ hi) :
    width a lo j ≤ width a hi j :=
  Nat.add_le_add (Nat.succ_le_succ le) (Nat.mul_le_mul_left _ (min_le_min le le_rfl))

private theorem slot_at (a n k B J i : ℕ) (ib : a*i ≤ B) (ij : i ≤ J) :
    slot a n k (B+1) (J+1) i =
      strip a (B-a*i) (J-i) - (width a (B-a*i) (J-i)-n*(k-i)) := by
  have b : B+1-a*i=(B-a*i)+1 := by omega
  have j : J+1-i=(J-i)+1 := by omega
  unfold slot
  dsimp only
  rw [b,j]
  simp only [Nat.add_one_ne_zero,false_or,ite_false,imageAllowance,strip,width,Nat.add_sub_cancel]

private theorem slot_lower (a n k BL B J i L c : ℕ) (le : BL ≤ B) (valid : a*i ≤ BL) (ij : i ≤ J)
    (cap : c ≤ width a (BL-a*i) (J-i))
    (budget : width a (B-a*i) (J-i) ≤ strip a (B-a*i) (J-i)+L) :
    min c (n*(k-i)) ≤ slot a n k (B+1) (J+1) i+L := by
  have actual := cap.trans (width_mono a (J-i) (Nat.sub_le_sub_right le _))
  rw [slot_at a n k B J i (valid.trans le) ij]
  omega

private theorem counting {a B J k i : ℕ} (ap : 0 < a) (inRange : i < count a B J k) :
    i ≤ J ∧ i < k ∧ a*i ≤ B := by
  unfold count at inRange
  rw [lt_min_iff,lt_min_iff] at inRange
  obtain ⟨ik,ij,ib⟩ := inRange
  have b := (Nat.le_div_iff_mul_le ap).mp (Nat.lt_succ_iff.mp ib)
  exact ⟨Nat.lt_succ_iff.mp ij,ik,by simpa only [Nat.mul_comm i a] using b⟩

private theorem first_width {a B J m i : ℕ} (ap : 1 < a) (im : i < pivot a B J m)
    (ib : a*i≤B) (ij : i≤J) :
    width a (B-a*i) (J-i) = B+(a-1)*J+1-(2*a-1)*i := by
  have a₁ : 0<a-1 := by omega
  have ok : J≤B := by by_contra no; simp only [pivot,ite_eq_right no,Nat.not_lt_zero] at im
  have t : i≤(B-J)/(a-1) := by
    rw [pivot,ite_eq_left ok,lt_min_iff] at im
    omega
  have jfits := (Nat.le_div_iff_mul_le a₁).mp t
  have split : (a-1)*i+i=a*i := by rw [← Nat.succ_mul]; congr 1; omega
  rw [Nat.mul_comm i (a-1)] at jfits
  have jle : J-i≤B-a*i := by omega
  unfold width
  rw [min_eq_right jle]
  have cap : (a-1)*(J-i)+(a-1)*i=(a-1)*J := by rw [← Nat.mul_add,Nat.sub_add_cancel ij]
  have line : a*i+(a-1)*i=(2*a-1)*i := by rw [← Nat.add_mul]; congr 1; omega
  omega

private theorem first_room {a B J m i : ℕ} (ap : 1 < a) (im : i < full a B J m)
    (ib : a*i≤B) (ij : i≤J) : J-i+(a-1)≤B-a*i+1 := by
  have a₁ : 0<a-1 := by omega
  have ok : J≤B := by
    by_contra no
    simp only [full,Nat.sub_eq_zero_of_le (show B≤J by omega),Nat.zero_div,_root_.min_zero,Nat.not_lt_zero] at im
  have t : i+1≤(B-J)/(a-1) := by
    rw [full,lt_min_iff] at im
    omega
  have jfits := (Nat.le_div_iff_mul_le a₁).mp t
  rw [Nat.mul_comm (i+1),Nat.mul_add,Nat.mul_one] at jfits
  have split : (a-1)*i+i=a*i := by rw [← Nat.succ_mul]; congr 1; omega
  omega

private theorem tail_width {a B J m i : ℕ} (ap : 1 < a) (im : i < m)
    (ip : pivot a B J m ≤ i) :
    width a (B-a*i) (J-i) = a*(B-a*i)+1 := by
  have a₁ : 0<a-1 := by omega
  have split : (a-1)*i+i=a*i := by rw [← Nat.succ_mul]; congr 1; omega
  have ble : B-a*i ≤ J-i := by
    by_cases room : J≤B
    · rw [pivot,ite_eq_left room] at ip
      have below : (B-J)/(a-1) < i := by omega
      have cap := (Nat.div_lt_iff_lt_mul a₁).mp below
      rw [Nat.mul_comm i (a-1)] at cap
      omega
    · omega
  unfold width
  rw [min_eq_left ble]
  have eq := congrArg (fun x => x*(B-a*i)) (Nat.sub_add_cancel (show 1≤a by omega) : a-1+1=a)
  rw [Nat.add_mul,Nat.one_mul] at eq
  omega

/-- The cost of suppressing the graph in its retained descendants. The
estimate may use a smaller degree box than the one in the actual bank. -/
theorem lower_le (BL B J a n k : ℕ) (ap : 0 < a) (boxLe : BL ≤ B) :
    lower BL J a n k ≤ gain a n k (B+1) (J+1) := by
  classical
  let m := count a BL J k
  have mk : m≤k := min_le_left _ _
  let g (i : ℕ) := slot a n k (B+1) (J+1) i
  have take : (∑ i ∈ range m, g i) ≤ gain a n k (B+1) (J+1) := by
    rw [gain_sum]
    exact sum_le_sum_of_subset_of_nonneg (range_mono mk) (by intros; exact Nat.zero_le _)
  unfold lower
  dsimp only
  have boxAt (i : ℕ) (mem : i < m) := counting ap mem
  by_cases one : a=1
  · rw [ite_eq_left one]
    refine (SpreadLines.minSum_le ..).trans ((sum_le_sum (fun i mem => ?_)).trans take)
    obtain ⟨jle,ik,bfit⟩ := boxAt i (mem_range.mp mem)
    have cap : BL+1-1*i ≤ width a (BL-a*i) (J-i) := by
      rw [one]
      simp only [width,Nat.sub_self,Nat.zero_mul,Nat.add_zero,Nat.one_mul]
      omega
    have full := full_strip a (B-a*i) (J-i) ap (Or.inl one)
    have rel := slot_lower a n k BL B J i 0 _ boxLe bfit jle cap (by rw [full,Nat.add_zero])
    rwa [Nat.mul_sub_left_distrib,Nat.add_zero] at rel
  · rw [ite_eq_right one]
    have ag : 1<a := by omega
    let f := full a BL J m
    let p := pivot a BL J m
    let δ := loss a
    have pm : p≤m := by unfold p pivot; split <;> omega
    have fp : f≤p := by
      by_cases room : J≤BL
      · simpa only [p,pivot,ite_eq_left room,f,full] using
          (min_le_min (le_rfl : m≤m) (Nat.le_succ ((BL-J)/(a-1))))
      · have no : BL-J=0 := by omega
        simp only [p,pivot,ite_eq_right room,f,full,no,Nat.zero_div,_root_.min_zero]
        exact le_rfl
    have first :
        SpreadLines.minSum (BL+(a-1)*J+1) (2*a-1) (n*k) n p ≤ (∑ i ∈ range p,g i)+(p-f)*δ := by
      have penalty : (∑ i ∈ range p, if i<f then 0 else δ)=(p-f)*δ := by
        rw [← sum_range_add_sum_Ico (fun i => if i<f then 0 else δ) fp]
        rw [sum_eq_zero (fun i hi => ite_eq_left (mem_range.mp hi)),Nat.zero_add]
        calc
          _ = ∑ _i ∈ Ico f p,δ := sum_congr rfl (fun i hi => ite_eq_right (Nat.not_lt.mpr (mem_Ico.mp hi).1))
          _ = _ := by simp [Nat.card_Ico]
      refine (SpreadLines.minSum_le ..).trans ?_
      rw [← penalty,← sum_add_distrib]
      apply sum_le_sum
      intro i hi
      obtain ⟨jle,ik,bfit⟩ := boxAt i ((mem_range.mp hi).trans_le pm)
      have cap := (first_width ag (mem_range.mp hi) bfit jle).ge
      rw [← Nat.mul_sub_left_distrib]
      by_cases inside : i<f
      · rw [ite_eq_left inside]
        have room := first_room ag inside bfit jle
        have widened : J-i+(a-1)≤B-a*i+1 := room.trans (Nat.succ_le_succ (Nat.sub_le_sub_right boxLe _))
        exact slot_lower a n k BL B J i _ _ boxLe bfit jle cap (by rw [full_strip a _ _ ap (Or.inr widened),Nat.add_zero])
      · rw [ite_eq_right inside]
        exact slot_lower a n k BL B J i _ _ boxLe bfit jle cap (all_strips a _ _ ap)
    have tail :
        SpreadLines.minSum (a*(BL-a*p)+1) (a*a) (n*(k-p)) n (m-p) ≤
          (∑ i ∈ range (m-p),g (p+i))+(m-p)*δ := by
      refine (SpreadLines.minSum_le ..).trans ?_
      rw [← show (∑ _ ∈ range (m-p),δ)=(m-p)*δ by simp,← sum_add_distrib]
      apply sum_le_sum
      intro i hi
      have ind : p+i < m := by have := mem_range.mp hi; omega
      obtain ⟨jle,ik,bfit⟩ := boxAt (p+i) ind
      have cap : a*(BL-a*p)+1-a*a*i ≤ width a (BL-a*(p+i)) (J-(p+i)) := by
        rw [tail_width ag ind (Nat.le_add_right p i)]
        have eq : a*(BL-a*(p+i))=a*(BL-a*p)-a*a*i := by
          rw [Nat.mul_add,← Nat.sub_sub,Nat.mul_sub_left_distrib,Nat.mul_assoc]
        have bounded : a*a*i≤a*(BL-a*p) := by
          rw [Nat.mul_assoc]
          apply Nat.mul_le_mul_left
          rw [Nat.mul_add] at bfit
          omega
        omega
      rw [← Nat.mul_sub_left_distrib,Nat.sub_sub]
      exact slot_lower a n k BL B J (p+i) _ _ boxLe bfit jle cap (all_strips a _ _ ap)
    have combine := sum_range_add g p (m-p)
    rw [Nat.add_sub_of_le pm] at combine
    have bank := take
    change SpreadLines.minSum (BL+(a-1)*J+1) (2*a-1) (n*k) n p+
      (SpreadLines.minSum (a*(BL-a*p)+1) (a*a) (n*(k-p)) n (m-p)-(m-p)*δ)-(p-f)*δ ≤ _
    omega

end Research6966.SpreadGain

end Merged_R6966ProofSpreadGain
