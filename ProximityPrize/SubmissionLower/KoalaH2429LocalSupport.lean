import ProximityPrize.SubmissionLower.KoalaH2430ContactData

set_option autoImplicit false

namespace KoalaH2429LocalSupport
open K1_14 (Shape)
open P1_7_4 (pairMinSeed pairMinOrdinate sharedBound dotQ Mass)
open KoalaH2430Contact

structure Data where
  free : Shape
  moving : Shape
  reserve : ℕ
  history : Mass
  weight : Mass
  cap : ℚ
  tree : Tree

private def threshold (q : ℕ) (k : Fin 3) : ℕ := (q / 128^k.val) % 128

private def atBound (S : Data) (q : ℕ) (k : Fin 3) (x z : ℕ) : ℚ :=
  sharedBound S.free S.moving x z (threshold q k) (S.reserve+1) true ⟨k, by omega⟩

private def elbow (S : Data) : ℕ := min (S.free.B-S.free.J) (S.moving.B-S.moving.J)
private def between (S : Data) (c d : ℕ) : ℕ := min d (max c (elbow S))

private def boxBound (S : Data) (a b c d q : ℕ) : Mass :=
  ![max (atBound S q 0 0 c)
      (max (atBound S q 0 0 (between S c d)) (atBound S q 0 0 d)),
    max (atBound S q 1 a 0) (atBound S q 1 b 0),
    max (max (atBound S q 2 a c) (atBound S q 2 a d))
      (max (atBound S q 2 b c) (atBound S q 2 b d)),
    0]

private def leaf (S : Data) (a b c d q : ℕ) : Prop :=
  b≤pairMinSeed S.free S.moving ∧ d≤pairMinOrdinate S.free S.moving ∧
  (∀ k : Fin 3, 0<threshold q k ∧ threshold q k≤S.reserve+1) ∧
  dotQ S.weight (fun k => (⌊min (S.history k) (boxBound S a b c d q k)⌋ : ℤ)) ≤ S.cap

private instance (S : Data) (a b c d q : ℕ) : Decidable (leaf S a b c d q) := by
  unfold leaf
  infer_instance

def Checked (S : Data) : Prop :=
  S.free.J≤S.free.B ∧ S.moving.J≤S.moving.B ∧ S.weight 3=0 ∧
  (∀ k, 0≤S.weight k) ∧
  S.tree.Checked (leaf S) 0 (pairMinSeed S.free S.moving) 0 (pairMinOrdinate S.free S.moving)

instance (S : Data) : Decidable (Checked S) := by
  unfold Checked
  infer_instance

private theorem seedBound_box (S : Data) {a b c d q x z : ℕ}
    (hs : S.free.J≤S.free.B) (ht : S.moving.J≤S.moving.B)
    (hd : d≤pairMinOrdinate S.free S.moving) (hcz : c≤z) (hzd : z≤d) :
    atBound S q 0 x z≤boxBound S a b c d q 0 := by
  have hC : atBound S q 0 0 c≤boxBound S a b c d q 0 := le_max_left _ _
  have hD : atBound S q 0 0 d≤boxBound S a b c d q 0 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hM : atBound S q 0 0 (between S c d)≤boxBound S a b c d q 0 :=
    (le_max_left _ _).trans (le_max_right _ _)
  by_cases hleft : d≤elbow S
  · exact seed_box S.free S.moving hcz hzd hd hs ht (Or.inl hleft) hC hD
  by_cases hright : elbow S≤c
  · exact seed_box S.free S.moving hcz hzd hd hs ht (Or.inr hright) hC hD
  have he : between S c d = elbow S := by
    unfold between
    rw [max_eq_right (by omega), min_eq_right (by omega)]
  rw [he] at hM
  by_cases hz : z≤elbow S
  · exact seed_box S.free S.moving hcz hz (by omega) hs ht (Or.inl le_rfl) hC hM
  · exact seed_box S.free S.moving (Nat.le_of_lt (Nat.lt_of_not_ge hz)) hzd hd hs ht
      (Or.inr le_rfl) hM hD

/-- Charge actual natural coordinate mass using the same partition for all three coordinates. -/
theorem count (S : Data) (ok : Checked S) {x z : ℕ}
    (hx : x≤pairMinSeed S.free S.moving) (hz : z≤pairMinOrdinate S.free S.moving)
    (m : Fin 4 → ℕ) (hist : ∀ k, (m k : ℚ)≤S.history k)
    (test : ∀ r, 0<r → r≤S.reserve+1 → ∀ k,
       (m k : ℚ)≤sharedBound S.free S.moving x z r (S.reserve+1) true k) :
    dotQ S.weight (fun k => m k) ≤ S.cap := by
  obtain ⟨hs,ht,hzero,hn,check⟩ := ok
  obtain ⟨a,b,c,d,q,hleaf,hax,hxb,hcz,hzd⟩ :=
    S.tree.locate check (Nat.zero_le x) hx (Nat.zero_le z) hz
  obtain ⟨hb,hd,hr,hbill⟩ := hleaf
  have h0 : (m 0 : ℚ)≤boxBound S a b c d q 0 :=
    (test _ (hr 0).1 (hr 0).2 0).trans (seedBound_box S hs ht hd hcz hzd)
  have h1 : (m 1 : ℚ)≤boxBound S a b c d q 1 :=
    (test _ (hr 1).1 (hr 1).2 1).trans
      (ordinate_box S.free S.moving hax hxb hb hs ht (le_max_left _ _) (le_max_right _ _))
  have h2 : (m 2 : ℚ)≤boxBound S a b c d q 2 := by
    apply (test _ (hr 2).1 (hr 2).2 2).trans
    apply P1_7_4_2.shared_mixed_box S.free S.moving hax hxb hb hcz hzd hd
    intro x' hx' z' hz'
    rcases hx' with rfl | rfl <;> rcases hz' with rfl | rfl
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hfloor (k : Fin 4) (hk : (m k : ℚ)≤boxBound S a b c d q k) :
      (m k : ℚ) ≤ (⌊min (S.history k) (boxBound S a b c d q k)⌋ : ℤ) := by
    have hm : (m k : ℤ) ≤ ⌊min (S.history k) (boxBound S a b c d q k)⌋ :=
      Int.le_floor.mpr (by exact_mod_cast le_min (hist k) hk)
    exact_mod_cast hm
  apply le_trans _ hbill
  unfold dotQ
  apply Finset.sum_le_sum
  intro k _
  fin_cases k
  · exact mul_le_mul_of_nonneg_left (hfloor 0 h0) (hn 0)
  · exact mul_le_mul_of_nonneg_left (hfloor 1 h1) (hn 1)
  · exact mul_le_mul_of_nonneg_left (hfloor 2 h2) (hn 2)
  · change S.weight (3 : Fin 4) * _ ≤ S.weight (3 : Fin 4) * _
    simpa only [hzero,zero_mul] using (le_refl (0 : ℚ))

end KoalaH2429LocalSupport
