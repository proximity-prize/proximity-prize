import ProximityPrize.SubmissionLower.RelativeWeightIntervals
namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open RCN100
set_option autoImplicit false

theorem hinge_tangent (D x c : ℕ) (h : D ≤ x) :
    (D-c)+((D+1-c)-(D-c))*(x-D) ≤ x-c := by
  by_cases hc : c ≤ D
  · have h1 : (D+1-c)-(D-c) = 1 := by omega
    rw [h1, one_mul]
    omega
  · have h1 : (D+1-c)-(D-c) = 0 := by omega
    rw [h1, zero_mul]
    omega

theorem hinge_chord (a x b c : ℕ) (hax : a ≤ x) (hxb : x ≤ b) :
    (b-a)*(x-c) ≤ (b-x)*(a-c)+(x-a)*(b-c) := by
  rcases Nat.lt_or_ge a c with hac | hca
  swap
  ·
    have hba : b-a = (b-x)+(x-a) := by omega
    have hx : x-c = (x-a)+(a-c) := by omega
    have hb : b-c = (b-x)+(x-a)+(a-c) := by omega
    rw [hba, hx, hb]
    apply le_of_eq
    ring
  rcases Nat.lt_or_ge x c with hxc | hcx
  swap
  ·
    have ha : a-c = 0 := by omega
    rw [ha, Nat.mul_zero, Nat.zero_add]
    have hb : b-c = (b-x)+(x-c) := by omega
    have hxa : x-a = (x-c)+(c-a) := by omega
    have hba : b-a = (b-x)+(x-c)+(c-a) := by omega
    rw [hb, hxa, hba]
    nlinarith [Nat.zero_le ((b-x)*(c-a))]
  · have hx : x-c = 0 := by omega
    rw [hx, Nat.mul_zero]
    exact Nat.zero_le _

theorem coefficientCount_eq_hinges (D w L s : ℕ) :
    coefficientCount D w L s =
      ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (s+1),
        (L+1-i-j)*(D-(w*i+(w-1)*j)) := by
  unfold coefficientCount
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.sub_sub, Nat.sub_sub]

def countSlopeAt (D w L s : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (s+1),
    (L+1-i-j)*((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))

theorem coefficientCount_tangent (D x w L s : ℕ) (h : D ≤ x) :
    coefficientCount D w L s+countSlopeAt D w L s*(x-D) ≤ coefficientCount x w L s := by
  rw [coefficientCount_eq_hinges, coefficientCount_eq_hinges, countSlopeAt,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have ht := hinge_tangent D x (w*i+(w-1)*j) h
  calc (L+1-i-j)*(D-(w*i+(w-1)*j))+
        (L+1-i-j)*((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))*(x-D)
      = (L+1-i-j)*((D-(w*i+(w-1)*j))+
          ((D+1-(w*i+(w-1)*j))-(D-(w*i+(w-1)*j)))*(x-D)) := by ring
    _ ≤ (L+1-i-j)*(x-(w*i+(w-1)*j)) := Nat.mul_le_mul_left _ ht

theorem coefficientCount_chord (a x b w L s : ℕ) (hax : a ≤ x) (hxb : x ≤ b) :
    (b-a)*coefficientCount x w L s ≤
      (b-x)*coefficientCount a w L s+(x-a)*coefficientCount b w L s := by
  rw [coefficientCount_eq_hinges, coefficientCount_eq_hinges, coefficientCount_eq_hinges,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hc := hinge_chord a x b (w*i+(w-1)*j) hax hxb
  calc (b-a)*((L+1-i-j)*(x-(w*i+(w-1)*j)))
      = (L+1-i-j)*((b-a)*(x-(w*i+(w-1)*j))) := by ring
    _ ≤ (L+1-i-j)*((b-x)*(a-(w*i+(w-1)*j))+(x-a)*(b-(w*i+(w-1)*j))) :=
        Nat.mul_le_mul_left _ hc
    _ = (b-x)*((L+1-i-j)*(a-(w*i+(w-1)*j)))+(x-a)*((L+1-i-j)*(b-(w*i+(w-1)*j))) := by ring

theorem wide_rows_core (w L s T R K beta Dhi Ehi H t : ℕ) (ht : t ≤ H)
    (hHi : coefficientCount Ehi w (L-T) (s-R)+K < coefficientCount Dhi w L s)
    (hLo : coefficientCount (Ehi+(beta+1)*H) w (L-T) (s-R)+K <
      coefficientCount Dhi w L s+countSlopeAt Dhi w L s*(beta*H)) :
    coefficientCount (Ehi+(beta+1)*t) w (L-T) (s-R)+K < coefficientCount (Dhi+beta*t) w L s := by
  set G2 := fun E => coefficientCount E w (L-T) (s-R) with hG2
  set g1 := coefficientCount Dhi w L s
  set m := countSlopeAt Dhi w L s
  have htan := coefficientCount_tangent Dhi (Dhi+beta*t) w L s (Nat.le_add_right _ _)
  rw [Nat.add_sub_cancel_left] at htan
  rcases Nat.eq_zero_or_pos H with hH | hH
  · have : t = 0 := by omega
    subst this
    simpa using hHi

  have hch := coefficientCount_chord Ehi (Ehi+(beta+1)*t) (Ehi+(beta+1)*H) w (L-T) (s-R)
    (Nat.le_add_right _ _) (by have := Nat.mul_le_mul_left (beta+1) ht; omega)
  have e1 : Ehi+(beta+1)*H-Ehi = (beta+1)*H := by omega
  have e2 : Ehi+(beta+1)*H-(Ehi+(beta+1)*t) = (beta+1)*(H-t) := by
    rw [Nat.mul_sub]; omega
  have e3 : Ehi+(beta+1)*t-Ehi = (beta+1)*t := by omega
  rw [e1, e2, e3] at hch
  have hch' : H*G2 (Ehi+(beta+1)*t) ≤ (H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H) := by
    have hpos : 0 < beta+1 := Nat.succ_pos _
    have : (beta+1)*(H*G2 (Ehi+(beta+1)*t)) ≤ (beta+1)*((H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)) := by
      calc (beta+1)*(H*G2 (Ehi+(beta+1)*t)) = (beta+1)*H*G2 (Ehi+(beta+1)*t) := by ring
        _ ≤ (beta+1)*(H-t)*G2 Ehi+(beta+1)*t*G2 (Ehi+(beta+1)*H) := hch
        _ = (beta+1)*((H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)) := by ring
    exact Nat.le_of_mul_le_mul_left this hpos

  have hsum : H*(G2 (Ehi+(beta+1)*t)+K) < H*(g1+m*(beta*t)) := by
    have hsplit : H = (H-t)+t := by omega
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hch' ⊢
      have := Nat.mul_lt_mul_of_pos_left hHi hH
      nlinarith [hch']
    · have hA : (H-t)*(G2 Ehi+K) ≤ (H-t)*g1 := Nat.mul_le_mul_left _ hHi.le
      have hB : t*(G2 (Ehi+(beta+1)*H)+K) < t*(g1+m*(beta*H)) := Nat.mul_lt_mul_of_pos_left hLo h0
      have hC : t*(m*(beta*H)) = H*(m*(beta*t)) := by ring
      calc H*(G2 (Ehi+(beta+1)*t)+K) = H*G2 (Ehi+(beta+1)*t)+H*K := by ring
        _ ≤ (H-t)*G2 Ehi+t*G2 (Ehi+(beta+1)*H)+((H-t)+t)*K := by
            rw [← hsplit]; exact Nat.add_le_add_right hch' _
        _ = (H-t)*(G2 Ehi+K)+t*(G2 (Ehi+(beta+1)*H)+K) := by ring
        _ < (H-t)*g1+t*(g1+m*(beta*H)) := Nat.add_lt_add_of_le_of_lt hA hB
        _ = ((H-t)+t)*g1+t*(m*(beta*H)) := by ring
        _ = H*(g1+m*(beta*t)) := by rw [← hsplit, hC]; ring
  have hfin : G2 (Ehi+(beta+1)*t)+K < g1+m*(beta*t) := Nat.lt_of_mul_lt_mul_left hsum
  exact lt_of_lt_of_le hfin htan

end ProximityPrize.SubmissionLower.RelativeBounded6814
