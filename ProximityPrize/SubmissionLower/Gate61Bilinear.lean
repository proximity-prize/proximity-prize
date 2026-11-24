import ProximityPrize.SubmissionLower.Gate61Tilted

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace Gate61Bilinear

open Low6960Prices K1_13

def Nt (B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 : ℤ) : ℤ :=
  (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4)) * x1 * y2
  + (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4)) * x1 * y3
  + (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4)) * x2 * y1
  + (480*(-4*B1*h1*h2 + 4*B1*h1*k*t - 2*B1*h1*k + 4*B1*h1*t + 2*B1*h1 + 4*B1*h2*k*t - 2*B1*h2*k + 4*B1*h2 + 4*B1*k^2*t + 4*B1*k*t + 8*B1*k + 4*B1 + 6*J2*h1*h2 - 6*J2*h1*k*t + 3*J2*h1*k - 6*J2*h1*t - 3*J2*h1 - 6*J2*h2*k*t + 3*J2*h2*k - 6*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 12*J2*k - 6*J2 - 4*h1*h2*t - 2*h1*h2 + 7*h1*k*t^2 - 4*h1*k*t + 7*h1*t^2 + 2*h1 + 7*h2*k*t^2 - 4*h2*k*t + 4*h2*t + 2*h2 + 7*k^2*t^2 + 7*k*t^2 + 8*k*t + 4*t - 12)) * x2 * y2
  + (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4)) * x2 * y3
  + (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4)) * x3 * y1
  + (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4)) * x3 * y2
  + (480*(-12*B1*J2*h1*k - 12*B1*J2*h1 - 12*B1*J2*h2*k - 12*B1*J2*k^2 - 12*B1*J2*k - 12*B1*h1*h2 + 36*B1*h1*k*t - 12*B1*h1*k + 36*B1*h1*t + 36*B1*h2*k*t - 12*B1*h2*k + 12*B1*h2 + 36*B1*k^2*t + 36*B1*k*t + 24*B1*k + 12*B1 + 7*J2^2*h1*k + 7*J2^2*h1 + 7*J2^2*h2*k + 7*J2^2*k^2 + 7*J2^2*k + 8*J2*h1*h2 - 30*J2*h1*k*t + 8*J2*h1*k - 30*J2*h1*t - 30*J2*h2*k*t + 8*J2*h2*k - 8*J2*h2 - 30*J2*k^2*t - 30*J2*k*t - 16*J2*k - 8*J2 - 12*h1*h2*t + 4*h1*h2 + 27*h1*k*t^2 - 12*h1*k*t + 27*h1*t^2 - 4*h1 + 27*h2*k*t^2 - 12*h2*k*t + 12*h2*t - 4*h2 + 27*k^2*t^2 + 27*k*t^2 + 24*k*t + 12*t + 4)) * x3 * y3

theorem sub5 (c0 c1 c2 c3 c4 : BentCap) : [c0,c1,c2,c3,c4].sublists = [[], [c0], [c1], [c0, c1], [c2], [c0, c2], [c1, c2], [c0, c1, c2], [c3], [c0, c3], [c1, c3], [c0, c1, c3], [c2, c3], [c0, c2, c3], [c1, c2, c3], [c0, c1, c2, c3], [c4], [c0, c4], [c1, c4], [c0, c1, c4], [c2, c4], [c0, c2, c4], [c1, c2, c4], [c0, c1, c2, c4], [c3, c4], [c0, c3, c4], [c1, c3, c4], [c0, c1, c3, c4], [c2, c3, c4], [c0, c2, c3, c4], [c1, c2, c3, c4], [c0, c1, c2, c3, c4]] := by rfl

def mixZ (caps : List BentCap) : ℤ :=
  caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) * bentIntegral s.1.b s.1.j s.1.t s.2) 0

theorem ambientMix_eq (caps : List BentCap) : ambientMix caps = (mixZ caps).toNat := rfl

theorem mixZ_tilted (B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 : ℕ) :
    mixZ [(⟨x1,x2,x3⟩, 0), (⟨y1,y2,y3⟩, 0), (⟨B1+1, J2+3, t+1⟩, 1),
      (⟨1 + k*B1, 4 + k*J2, 2 + k*t⟩, h1), (⟨1 + (k+1)*B1, 4 + (k+1)*J2, 2 + (k+1)*t⟩, h2)] =
      Nt B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 := by
  unfold mixZ
  rw [sub5]
  simp only [List.foldl_cons, List.foldl_nil, addBent, Shape.plus, List.length_cons, List.length_nil]
  unfold bentIntegral Nt
  push_cast
  ring

theorem tiltedPair_formula (p q1 q2 : Shape) (hb : p.j + 1 ≤ p.b) (hj : 2 ≤ p.j) (k h1 h2 : ℕ)
    (hk : Low6960Prices.taylorLength - 4 = k) (hh1 : (bentLift k p).2 = h1) (hh2 : (bentLift (k + 1) p).2 = h2) :
    Gate61.tiltedPair p q1 q2 =
      (Nt ((p.b - 1 : ℕ) : ℤ) ((p.j - 2 : ℕ) : ℤ) p.t k h1 h2 q1.b q1.j q1.t q2.b q2.j q2.t).toNat := by
  obtain ⟨b, j, t⟩ := p
  obtain ⟨x1, x2, x3⟩ := q1
  obtain ⟨y1, y2, y3⟩ := q2
  simp only at hb hj hh1 hh2 ⊢
  obtain ⟨B1, rfl⟩ : ∃ B1, b = B1 + 1 := ⟨b - 1, by omega⟩
  obtain ⟨J2, rfl⟩ : ∃ J2, j = J2 + 2 := ⟨j - 2, by omega⟩
  have hk1 : Low6960Prices.taylorLength - 3 = k + 1 := by
    have : 4 ≤ Low6960Prices.taylorLength := by decide
    omega
  unfold Gate61.tiltedPair
  rw [hk, hk1, ambientMix_eq]
  have hg : bentGraph ⟨B1 + 1, J2 + 2, t⟩ = (⟨B1 + 1, J2 + 3, t + 1⟩, 1) := by
    simp [bentGraph]
    omega
  have hl1 : bentLift k ⟨B1 + 1, J2 + 2, t⟩ = (⟨1 + k * B1, 4 + k * J2, 2 + k * t⟩, h1) := by
    rw [← hh1]; simp [bentLift]
  have hl2 : bentLift (k + 1) ⟨B1 + 1, J2 + 2, t⟩ =
      (⟨1 + (k + 1) * B1, 4 + (k + 1) * J2, 2 + (k + 1) * t⟩, h2) := by
    rw [← hh2]; simp [bentLift]
  rw [hg, hl1, hl2, mixZ_tilted]
  simp

end Gate61Bilinear
