import ProximityPrize.SubmissionLower.UpperBranch8

/-! The rectangular diagonal is from the public kaankolcu 69.50 note,
submission f9161583-1b70-4048-8a65-bae6ee236fe4. The fee uses a single Taylor
cut and ordinary node incidence on every curve. -/

set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Rect51Fee

def graphDegree (e v₀ v₁ b c : ℕ) : ℕ :=
  2*(e*b*c+(v₀*c+v₁*b)*(3*e-3)+v₀*v₁*(2*e-4))

private def ambient (h t a b : ℚ) : ℚ := t*(h+t)*a*b

/-- The mixed coefficient of the root and tangent rows on the chosen diagonal. -/
theorem mixedGraph (e v₀ v₁ b c : ℚ) :
    let p := fun x y z : ℚ =>
      ambient ((e-3)*x+e*y+(e-2)*z) (x+z) (b*x+v₀*(y+z)) (c*x+v₁*(y+z))
    ((p 2 1 1-p 2 0 1-p 2 1 0+p 2 0 0) -
      2*(p 1 1 1-p 1 0 1-p 1 1 0+p 1 0 0) +
      (p 0 1 1-p 0 0 1-p 0 1 0+p 0 0 0))/2 =
      e*b*c+(v₀*c+v₁*b)*(3*e-3)+v₀*v₁*(2*e-4) := by
  dsimp [ambient]
  ring

/-- Scale the usual shortened-node charge without needing a second Taylor cut. -/
theorem scaled_node_charge {A n d L s r k δ count : ℕ}
    (hAn : A≤n) (hd : d<A) (hL : L≤A) (hs : s≤d)
    (hr : r≤L-s) (hc : (A-s)*count≤(n-s)*(r+k)*δ) :
    (A*(A-d))*count ≤ (n*(A-d)*L + A*(n-d)*k)*δ := by
  have hMu := Nat.mul_le_mul_left A (P1_7_8.mu_cross hAn hd.le hs)
  have hLam := Nat.mul_le_mul_left (A-d) (P1_7_8.lambda_cross hAn hL (hs.trans hd.le))
  have hr' := Nat.mul_le_mul_left (A*(A-d)*(n-s)) hr
  have hLam' : A*(A-d)*(n-s)*r ≤ (A-s)*(n*(A-d)*L) := by
    exact hr'.trans (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hLam)
  have hMu' : A*(A-d)*(n-s)*k ≤ (A-s)*(A*(n-d)*k) := by
    exact (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
      Nat.mul_le_mul_right k hMu)
  apply Nat.le_of_mul_le_mul_left _ (Nat.sub_pos_of_lt (hs.trans_lt hd))
  calc
    _ = A*(A-d)*((A-s)*count) := by ring
    _ ≤ A*(A-d)*((n-s)*(r+k)*δ) := Nat.mul_le_mul_left _ hc
    _ = (A*(A-d)*(n-s)*r + A*(A-d)*(n-s)*k)*δ := by ring
    _ ≤ ((A-s)*(n*(A-d)*L)+(A-s)*(A*(n-d)*k))*δ :=
      Nat.mul_le_mul_right _ (Nat.add_le_add hLam' hMu')
    _ = _ := by ring

#print axioms scaled_node_charge
end Rect51Fee
