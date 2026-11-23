import ProximityPrize.SubmissionLower.Final50Price

set_option Elab.async false
set_option maxHeartbeats 1200000

namespace KoalaAllocationWeight
open K1_13 (Shape)
open K1_13_8 (Valid)
open scoped BigOperators

def fullCharge (b j t:ℕ):Prop:=137≤b ∨ 54≤j ∨ 14≤t

instance (b j t:ℕ):Decidable (fullCharge b j t):=by unfold fullCharge; infer_instance

def indexWeight (b j : ℕ) : ℕ :=
  if j≤3 then 3 else if j≤4 then 10 else if j≤51 then min b 137+4*j
  else if j≤52 then 351 else if j≤53 then 358 else 361

def weight (b j t:ℕ):ℕ:=if fullCharge b j t then 361 else indexWeight b j

theorem mono {b j t B J T : ℕ} (hb : b ≤ B) (hj : j ≤ J) (ht : t ≤ T) :
    weight b j t≤weight B J T:=by
  have hm:min b 137≤min B 137:=min_le_min_right _ hb
  have hB:min B 137≤137:=min_le_right _ _
  have hb' : min b 137≤137:=min_le_right _ _
  by_cases hfull:fullCharge B J T
  · by_cases hsmall : fullCharge b j t
    · simpa only [weight,if_pos hsmall,if_pos hfull] using (le_refl (361:ℕ))
    · simp only [weight, if_neg hsmall, if_pos hfull]
      unfold indexWeight
      split_ifs <;> omega
  · have hsmall : ¬ fullCharge b j t := by
      intro h
      apply hfull
      rcases h with h | h | h
      · exact Or.inl (h.trans hb)
      · exact Or.inr (Or.inl (h.trans hj))
      · exact Or.inr (Or.inr (h.trans ht))
    simp only [weight,if_neg hsmall,if_neg hfull]
    unfold indexWeight
    split_ifs <;> omega

/-- A member charged the full allowance is the only member in the priced set. -/
theorem singleton_of_fullCharge {n : ℕ} {a : Fin n → Shape} {s : Finset (Fin n)} {i : Fin n}
    (hv : ∀ k,Valid (a k)) (hb:(∑ k,(a k).b)≤137)
    (hj:(∑ k,(a k).j)≤56) (ht:(∑ k,(a k).t)≤14)
    (hi:i ∈ s) (hfull:fullCharge (a i).b (a i).j (a i).t):s = {i} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, ?_⟩
  intro k _
  by_contra hne
  have pair (f : Fin n → ℕ) : f i+f k ≤ ∑ q, f q := by
    rw [← Finset.sum_pair (Ne.symm hne)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hb' := (pair fun q => (a q).b).trans hb
  have hj' := (pair fun q => (a q).j).trans hj
  have ht' := (pair fun q => (a q).t).trans ht
  obtain ⟨hkt,hkj,hkb⟩:=hv k
  rcases hfull with h | h | h <;> omega

theorem sum_bound {n : ℕ} (a : Fin n → Shape) (s : Finset (Fin n))
    (hv : ∀ i,Valid (a i)) (hb:(∑ i,(a i).b)≤137)
    (hj:(∑ i,(a i).j)≤56) (ht:(∑ i,(a i).t)≤14) :
    (∑ i ∈ s,weight (a i).b (a i).j (a i).t)≤361:=by
  classical
  have part (f : Fin n → ℕ) : ∑ k ∈ s, f k ≤ ∑ k, f k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have idx (k : Fin n) : 3 ≤ (a k).j := by
    have h:=(hv k).1
    have h' := (hv k).2.1
    omega
  by_cases hall : ∃ i ∈ s,fullCharge (a i).b (a i).j (a i).t
  · obtain ⟨i, hi, hfull⟩ := hall
    have he:=singleton_of_fullCharge hv hb hj ht hi hfull
    simp [he,weight,hfull]
  · have noFull (i : Fin n) (hi : i ∈ s) : ¬ fullCharge (a i).b (a i).j (a i).t :=
      fun h => hall ⟨i,hi,h⟩
    by_cases hhigh : ∃ i ∈ s,52≤(a i).j
    · obtain ⟨i,hi,hij⟩ := hhigh
      have hlt : (a i).j < 54 := by
        by_contra! h
        exact noFull i hi (Or.inr (Or.inl h))
      let u:=s.erase i
      have hrem : (∑ k ∈ u, (a k).j) + (a i).j ≤ 56 := by
        change (∑ k ∈ s.erase i,(a k).j)+(a i).j≤56
        rw [Finset.sum_erase_add _ _ hi]
        exact (part _).trans hj
      have hmin : 3*u.card ≤ ∑ k ∈ u, (a k).j := by
        calc
          _ = ∑ _k ∈ u,(3:ℕ):=by simp [Nat.mul_comm]
          _≤_:=Finset.sum_le_sum fun k _ => idx k
      have hu:u.card≤1:=by omega
      let limit:=if (a i).j=52 then 10 else 3
      have hsmall (k : Fin n) (hk : k ∈ u) : weight (a k).b (a k).j (a k).t ≤ limit := by
        have hjk : (a k).j ≤ ∑ q ∈ u, (a q).j :=
          Finset.single_le_sum (fun q _ => Nat.zero_le (a q).j) hk
        have hk0:k ∈ s:=Finset.mem_of_mem_erase hk
        have hz:=idx k
        rw [weight,if_neg (noFull k hk0)]
        dsimp [limit,indexWeight]
        split_ifs <;> omega
      have htail : (∑ k ∈ u, weight (a k).b (a k).j (a k).t) ≤ limit := by
        rw [← Nat.one_mul limit]
        refine (Finset.sum_le_sum hsmall).trans ?_
        simpa using Nat.mul_le_mul_right limit hu
      have head : limit + weight (a i).b (a i).j (a i).t = 361 := by
        rw [weight,if_neg (noFull i hi)]
        dsimp [limit,indexWeight]
        split_ifs <;> omega
      rw [← Finset.sum_erase_add _ _ hi]
      exact (Nat.add_le_add_right htail _).trans head.le
    · have hw (i : Fin n) (hi : i ∈ s) : weight (a i).b (a i).j (a i).t ≤ (a i).b+4*(a i).j := by
        have hlow : (a i).j ≤ 51 := by
          by_contra! h
          exact hhigh ⟨i,hi,by omega⟩
        have hidx:=idx i
        have hm:=min_le_left (a i).b 137
        rw [weight,if_neg (noFull i hi)]
        unfold indexWeight
        split_ifs <;> omega
      refine (Finset.sum_le_sum hw).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact Nat.add_le_add ((part _).trans hb) (Nat.mul_le_mul_left 4 ((part _).trans hj))

theorem sum_le {top n : ℕ} (htop : top ≤ 14) (a : Fin n → Shape)
    (hf:Final50Price.Fits top a) (s:Finset (Fin n)) :
    (∑ i ∈ s,weight (a i).b (a i).j (a i).t)≤361 :=
  sum_bound a s hf.1 hf.2.1 hf.2.2.1 (hf.2.2.2.trans htop)

#print axioms sum_le
end KoalaAllocationWeight
