import ProximityPrize.SubmissionLower.Koala6844VirtualHighBounds



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

private theorem add_sub_one_le_mul
    {j J delay μ : ℕ} (hj : 1 ≤ j) (hJ : j ≤ J)
    (hdelay : delay ≤ μ) (hμ : 1 ≤ μ) :
    j + delay - 1 ≤ μ * J := by
  have hbound := Nat.mul_le_mul_right (J-1) hμ
  have hexpand : μ * J = μ * (J-1) + μ := by
    conv_lhs => rw [show J = (J-1)+1 by omega]
    rw [Nat.mul_add, Nat.mul_one]
  omega

theorem tailRectangle_delay_le (f : Rectangle) (j J delay μ : ℕ)
    (hvalue : 1 ≤ f.value) (hj : 1 ≤ j) (hJ : j ≤ J)
    (hdelay : delay ≤ μ) (hμ : 1 ≤ μ) :
    (tailRectangle (j+delay) f).value ≤ μ * (tailRectangle (J+1) f).value ∧
    (tailRectangle (j+delay) f).first ≤ μ * (tailRectangle (J+1) f).first ∧
    (tailRectangle (j+delay) f).second ≤ μ * (tailRectangle (J+1) f).second := by
  obtain ⟨y,b,c⟩ := f
  change 1 ≤ y at hvalue
  have numeral : ∀ n : ℕ, 1 ≤ n →
      tailRectangle n ⟨y,b,c⟩ =
        ⟨(n-1)*(2*(y-1))+y, (n-1)*(2*b)+(b+10000), (n-1)*(2*c)+(c+10000)⟩ := by
    intro n hn
    have htwon : 2*n-1 = 2*(n-1)+1 := by omega
    have hv : 1+(2*n-1)*(y-1) = (n-1)*(2*(y-1))+y := by
      calc
        _ = (n-1)*(2*(y-1)) + (1+(y-1)) := by rw [htwon]; ring
        _ = _ := by rw [show 1+(y-1)=y by omega]
    have hs (k : ℕ) : (2*n-1)*k+10000 = (n-1)*(2*k)+(k+10000) := by
      rw [htwon]
      ring
    change Rectangle.mk (1+(2*n-1)*(y-1)) ((2*n-1)*b+10000) ((2*n-1)*c+10000) = _
    rw [hv, hs, hs]
  rw [numeral (j+delay) (by omega), numeral (J+1) (by omega)]
  simp only [Nat.add_sub_cancel]
  have hindex := add_sub_one_le_mul hj hJ hdelay hμ
  have value (a d : ℕ) : (j+delay-1)*a+d ≤ μ*(J*a+d) := by
    rw [Nat.mul_add, ← Nat.mul_assoc]
    exact Nat.add_le_add (Nat.mul_le_mul_right a hindex)
      (by simpa using Nat.mul_le_mul_right d hμ)
  exact ⟨value _ _, value _ _, value _ _⟩

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
