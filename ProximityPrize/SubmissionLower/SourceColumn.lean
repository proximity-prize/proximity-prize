import ProximityPrize.SubmissionLower.SeedSlice
import ProximityPrize.SubmissionLower.PoleImage

namespace SourceColumn
noncomputable section
open PoleBlocks PoleFamily PoleTruncation PoleImage MvPolynomial
open scoped BigOperators

theorem single_passive {F : Type*} [Field F] {U B J : ℕ} (c : Sigma (@Columns U B J)) (u : Fin (U+1)) :
    passivePolynomial (Pi.single c (1:F)) u =
      if c.1.1 = u then chartMonomial F (colInput c) else 0 := by
  classical
  unfold passivePolynomial
  rw [Finset.sum_eq_single c]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

theorem image_column {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    {U B J : ℕ} (x : R) (ev : MvPolynomial (Fin 4) F →ₐ[F] R)
    (weight : Fin (U+1) → R) (c : Sigma (@Columns U B J)) :
    Ideal.Quotient.mk (CutIdeal x (B+J)) (weight c.1.1 * ev (chartMonomial F (colInput c))) ∈
      (postcompose U B J x ev weight).range := by
  classical
  refine ⟨Pi.single c 1, ?_⟩
  rw [postcompose_apply]
  congr 1
  rw [Finset.sum_eq_single c.1.1]
  · simp [single_passive]
  · intro k _ hk
    simp [single_passive, Ne.symm hk]
  · simp

/-- The image of every admissible true source monomial belongs to the
bounded normalized image.  All coefficients used to take the span are in F. -/
theorem original_column {F R : Type*} [Field F] [CommRing R] [Algebra F R]
    (U B J : ℕ) (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (active centre passive x T V : R)
    (hz : algebraMap F R a * active = (algebraMap F R b + algebraMap F R c * active)*centre)
    (u : Fin (U+1)) (t q j i : ℕ) (hq : q ≤ B) (hj : j ≤ J) (hjq : j ≤ q) (hi : i ≤ U-u.val) :
    let ev : MvPolynomial (Fin 4) F →ₐ[F] R := aeval ![x,T,V,centre]
    let weight := fun v : Fin (U+1) => passive^v.val*(algebraMap F R b + algebraMap F R c*active)^(U-v.val)
    Ideal.Quotient.mk (CutIdeal x (B+J))
        (passive^u.val * x^t * (centre+x*T)^(q-j) * (T+x*V)^j * active^i) ∈
      (postcompose U B J x ev weight).range := by
  classical
  dsimp only
  let ev : MvPolynomial (Fin 4) F →ₐ[F] R := aeval ![x,T,V,centre]
  let weight := fun v : Fin (U+1) => passive^v.val*(algebraMap F R b + algebraMap F R c*active)^(U-v.val)
  let d := U-u.val
  let π := Ideal.Quotient.mkₐ F (CutIdeal x (B+J))
  let S := (postcompose U B J x ev weight).range
  let original := passive^u.val * x^t * (centre+x*T)^(q-j) * (T+x*V)^j * active^i
  change π original ∈ S
  by_cases ht : t < B+J
  · have htgt := ProjectivePole.actual_monomial_image a b c active centre passive x T V d i u.val t q j hi hz
    let coeff := fun k : ℕ => ((d-i).choose k : F)*b^i*(-c)^k*a^(d-i-k)
    let m := fun k : ℕ => x^t*(centre+x*T)^(q-j)*(T+x*V)^j*centre^(i+k)
    change algebraMap F R ((a*b)^d) * original =
      weight u * ∑ k ∈ Finset.range (d-i+1), algebraMap F R (coeff k) * m k at htgt
    apply (S.smul_mem_iff (pow_ne_zero d (mul_ne_zero ha hb))).mp
    rw [show (a*b)^d • π original = π ((a*b)^d • original) from (map_smul π _ _).symm,
      Algebra.smul_def, htgt, Finset.mul_sum, map_sum]
    apply Submodule.sum_mem
    intro k hk
    have hik : i+k ≤ d := by have := Finset.mem_range.mp hk; omega
    let input : Input := ⟨t,q,j,i+k,hjq⟩
    obtain ⟨col, hu, hc⟩ := column_exists u input hik hq hj ht
    have hcol := image_column x ev weight col
    rw [hu, hc] at hcol
    have hid : ev (chartMonomial F input) = m k := by
      simp [chartMonomial, input, ev, m]
    rw [hid] at hcol
    have hscalar : weight u * (algebraMap F R (coeff k) * m k) =
        coeff k • (weight u * m k) := by rw [Algebra.smul_def]; ring
    rw [hscalar, map_smul]
    exact S.smul_mem _ hcol
  · have hdiv : x^(B+J) ∣ original := by
      refine ⟨passive^u.val*x^(t-(B+J))*(centre+x*T)^(q-j)*(T+x*V)^j*active^i,?_⟩
      dsimp [original]
      rw [show x^t = x^(B+J)*x^(t-(B+J)) from by rw [←pow_add,Nat.add_sub_of_le (by omega)]]
      ring
    have hzero : π original = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    rw [hzero]
    exact S.zero_mem
end
end SourceColumn
