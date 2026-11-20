import ProximityPrize.SubmissionLower.ProjectivePole

namespace ProjectivePole
open scoped BigOperators

/-- Pull the active seed basis back along the actual fractional-linear centre.
The coefficients in this expansion belong to F even when x, y live over a
larger ring. This lets the normalized chart rank bound descend over F. -/
theorem active_seed_basis {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (a b c : F) (x y : R) (d i : ℕ) (hi : i ≤ d)
    (hx : algebraMap F R a * x =
      (algebraMap F R b + algebraMap F R c*x)*y) :
    algebraMap F R ((a*b)^d) * x^i =
      (algebraMap F R b + algebraMap F R c*x)^d *
      ∑ k ∈ Finset.range (d-i+1),
        algebraMap F R (((d-i).choose k : F) * b^i * (-c)^k * a^(d-i-k)) * y^(i+k) := by
  let f := algebraMap F R
  let D := f b + f c * x
  have H := homogeneous_reexpansion (f a) (f b) (f c) x d i hi
  rw [map_pow,map_mul]
  refine H.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hi' : i+k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hs : i+k+(d-i-k) = d := by omega
  change _ = D^d * (f _ * y^(i+k))
  change f a*x = D*y at hx
  change ((d-i).choose k : R)*(f b)^i*(-f c)^k*(f a)^(d-i-k)*(f a*x)^(i+k)*D^(d-i-k) = _
  rw [hx,mul_pow]
  simp only [map_mul,map_pow,map_neg,map_natCast]
  have hD : D^(i+k)*D^(d-i-k) = D^d := by rw [← pow_add,hs]
  rw [← hD]
  ring

/-- On every source monomial the chart pullback has a single denominator
weight depending on the passive seed degree. All powers in the new active
coordinate lie in the original cutoff. -/
theorem actual_monomial_image {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (a b c : F) (active centre passive x T V : R) (d i u t q j : ℕ) (hi : i ≤ d)
    (hx : algebraMap F R a * active =
      (algebraMap F R b + algebraMap F R c*active)*centre) :
    algebraMap F R ((a*b)^d) *
      (passive^u * x^t * (centre+x*T)^(q-j) * (T+x*V)^j * active^i) =
      passive^u * (algebraMap F R b + algebraMap F R c * active)^d *
      ∑ k ∈ Finset.range (d-i+1), algebraMap F R
        (((d-i).choose k : F)*b^i*(-c)^k*a^(d-i-k)) *
        (x^t*(centre+x*T)^(q-j)*(T+x*V)^j*centre^(i+k)) := by
  let m := x^t*(centre+x*T)^(q-j)*(T+x*V)^j
  let D := (algebraMap F R b + algebraMap F R c * active)^d
  let coeff (k : ℕ) := algebraMap F R (((d-i).choose k : F)*b^i*(-c)^k*a^(d-i-k))
  have hsum : ∑ k ∈ Finset.range (d-i+1), coeff k * (m*centre^(i+k)) =
      m * ∑ k ∈ Finset.range (d-i+1), coeff k * centre^(i+k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have H : algebraMap F R ((a*b)^d) * active^i =
      D * ∑ k ∈ Finset.range (d-i+1), coeff k * centre^(i+k) :=
    active_seed_basis a b c active centre d i hi hx
  change algebraMap F R ((a*b)^d) * _ = passive^u*D*∑ k ∈ Finset.range (d-i+1), coeff k * (m*centre^(i+k))
  rw [hsum, show algebraMap F R ((a*b)^d) * (passive^u*x^t*(centre+x*T)^(q-j)*(T+x*V)^j*active^i)
      = passive^u*m*(algebraMap F R ((a*b)^d)*active^i) by dsimp [m]; ring, H]
  ring

end ProjectivePole
