import ProximityPrize.SubmissionLower.Rect51HilbertCover

set_option autoImplicit false
set_option Elab.async false

namespace Rect51Point
noncomputable section
open HighCore82706Tangent_3 (JetRing seedVar)
open HighCore82706Tangent_3_2 (SeedTranscendental)
open K1_14 (FX)
open Rect51Hilbert MvPolynomial
open scoped BigOperators

structure Probe (Q : Ideal JetRing) where
  coeff : Fin 4 → ℚ
  nonnegative : ∀ i, 0 ≤ coeff i
  offset : ℚ
  threshold : ℕ
  profile : ∀ h t b c : ℕ, threshold ≤ h → threshold ≤ t →
    threshold ≤ b → threshold ≤ c →
    (hilbert Q h t b c : ℚ) = (h : ℚ)*coeff 0 + (t : ℚ)*coeff 1 +
      (b : ℚ)*coeff 2 + (c : ℚ)*coeff 3 + offset

private def slope (p : HilbertPoly) (i : Fin 4) : ℚ :=
  p.coeff (Finsupp.single i 1)

private theorem slope_nonneg {p : HilbertPoly} (hp : p.totalDegree ≤ 1)
    (hpos : NonnegativeTop p) (i : Fin 4) : 0 ≤ slope p i := by
  by_cases h : p.totalDegree = 1
  · apply hpos
    exact (Finsupp.degree_single i 1).trans h.symm
  · have hd : p.totalDegree < (Finsupp.single i 1).degree := by
      rw [Finsupp.degree_single]
      omega
    rw [slope, MvPolynomial.coeff_eq_zero_of_totalDegree_lt hd]
private theorem eval_affine {p : HilbertPoly} (hp : p.totalDegree ≤ 1) (h t b c : ℕ) :
    evalHilbert p h t b c = p.coeff 0 + slope p 0 * h + slope p 1 * t + slope p 2 * b + slope p 3 * c := by
  classical
  have hlinear : p = C (p.coeff 0) + C (slope p 0) * MvPolynomial.X 0 +
      C (slope p 1) * MvPolynomial.X 1 + C (slope p 2) * MvPolynomial.X 2 + C (slope p 3) * MvPolynomial.X 3 := by
    ext m
    by_cases hm : m.degree ≤ 1
    · rcases show m.degree = 0 ∨ m.degree = 1 by omega with hz | ho
      · rw [(Finsupp.degree_eq_zero_iff m).mp hz]
        simp [C_mul_X_eq_monomial, Finsupp.single_eq_zero]
      · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp ho
        fin_cases i <;> simp [slope, C_mul_X_eq_monomial, Finsupp.single_eq_zero,
          Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), eq_comm]
    · rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt (hp.trans_lt (Nat.lt_of_not_ge hm))]
      have hz : 0 ≠ m := by
        rintro rfl
        exact hm (by simp)
      have hi (i : Fin 4) : Finsupp.single i 1 ≠ m := by
        rintro rfl
        exact hm (by simp)
      simp [C_mul_X_eq_monomial, hz, hi]
  unfold evalHilbert
  conv_lhs => rw [hlinear]
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

def Probe.ofProfile {Q : Ideal JetRing} {p : HilbertPoly}
    (hp : IsProfile Q p) (hd : p.totalDegree ≤ 1) (hn : NonnegativeTop p) : Probe Q := by
  let N := Classical.choose hp
  have hN := Classical.choose_spec hp
  refine ⟨slope p, slope_nonneg hd hn, p.coeff 0, N, ?_⟩
  intro h t b c hh ht hb hc
  rw [hN h t b c hh ht hb hc, eval_affine hd]
  ring

def Probe.mass {Q : Ideal JetRing} (T : Probe Q) (h t b c : ℕ) : ℚ :=
  (h : ℚ)*T.coeff 0 + (t : ℚ)*T.coeff 1 + (b : ℚ)*T.coeff 2 + (c : ℚ)*T.coeff 3

private theorem slope_le {u v a b : ℚ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → (n : ℚ)*u + a ≤ (n : ℚ)*v + b) : u ≤ v := by
  by_contra! hv
  have hpos : 0 < u-v := sub_pos.mpr hv
  obtain ⟨n, hn⟩ := exists_nat_gt ((b-a)/(u-v))
  let m := max n N
  have hm : (b-a)/(u-v) < (m : ℚ) := hn.trans_le (by exact_mod_cast le_max_left n N)
  have hstrict := (div_lt_iff₀ hpos).mp hm
  have hh := h m (le_max_right n N)
  nlinarith only [hstrict, hh]

theorem probe_sums {ι : Type} [Fintype ι] {I : Ideal JetRing}
    (P : ι → Ideal JetRing) (T : ∀ i, Probe (P i))
    (hdim : ∃ k, ∀ h t b c, (∑ i, hilbert (P i) h t b c) ≤ hilbert I (h+k) (t+k) (b+k) (c+k))
    (w : Fin 4 → ℚ) {N : ℕ} {offset : ℚ}
    (hbudget : ∀ h t b c : ℕ, N ≤ h → N ≤ t → N ≤ b → N ≤ c →
      (hilbert I h t b c : ℚ) ≤ (h : ℚ)*w 0 + (t : ℚ)*w 1 + (b : ℚ)*w 2 + (c : ℚ)*w 3 + offset)
    (h t b c : ℕ) :
    (∑ i, (T i).mass h t b c) ≤ (h : ℚ)*w 0 + (t : ℚ)*w 1 + (b : ℚ)*w 2 + (c : ℚ)*w 3 := by
  classical
  obtain ⟨k, hk⟩ := hdim
  let M := max N (Finset.univ.sup fun i => (T i).threshold)
  have hM (i : ι) : (T i).threshold ≤ M :=
    (Finset.le_sup (f := fun i => (T i).threshold) (Finset.mem_univ i)).trans (le_max_right _ _)
  refine slope_le (N := 0)
    (a := ∑ i, ((T i).mass M M M M + (T i).offset))
    (b := ((M+k : ℕ) : ℚ)*(w 0+w 1+w 2+w 3) + offset) ?_
  intro n _
  have hh (x : ℕ) : M ≤ n*x+M := Nat.le_add_left _ _
  have hs (x : ℕ) : N ≤ n*x+M+k :=
    (le_max_left _ _).trans ((hh x).trans (Nat.le_add_right _ _))
  have he (i : ι) : (hilbert (P i) (n*h+M) (n*t+M) (n*b+M) (n*c+M) : ℚ) =
      (n : ℚ)*(T i).mass h t b c + ((T i).mass M M M M + (T i).offset) := by
    rw [(T i).profile _ _ _ _ ((hM i).trans (hh h)) ((hM i).trans (hh t))
      ((hM i).trans (hh b)) ((hM i).trans (hh c))]
    unfold Probe.mass
    push_cast
    ring
  have hsum : (∑ i, (hilbert (P i) (n*h+M) (n*t+M) (n*b+M) (n*c+M) : ℚ)) ≤
      (hilbert I (n*h+M+k) (n*t+M+k) (n*b+M+k) (n*c+M+k) : ℚ) := by
    exact_mod_cast hk (n*h+M) (n*t+M) (n*b+M) (n*c+M)
  have ha := hsum.trans (hbudget _ _ _ _ (hs h) (hs t) (hs b) (hs c))
  simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum] at ha
  push_cast at ha ⊢
  simp only [Finset.sum_add_distrib]
  nlinarith only [ha]

private theorem seed_pow_mem (P : Ideal JetRing) (i : Fin 2) (h t b c j : ℕ)
    (hj : j ≤ if i = 0 then b else c) :
    (Ideal.Quotient.mk P (seedVar i)) ^ j ∈ gradedPiece P (nefDegree h t b c) := by
  let u := if i = 0 then j else 0
  let v := if i = 0 then 0 else j
  let q : Cox := MvPolynomial.X h₀ ^ (h+2*t) * MvPolynomial.X v₀ ^ t *
    MvPolynomial.X (seed₀ 1) ^ u * MvPolynomial.X (seed₀ 0) ^ (b-u) *
    MvPolynomial.X (seed₁ 1) ^ v * MvPolynomial.X (seed₁ 0) ^ (c-v)
  refine Submodule.mem_map.mpr ⟨q, ?_, ?_⟩
  · have hw := (((((isWeightedHomogeneous_X FX coxWeight h₀).pow (h+2*t)).mul
        ((isWeightedHomogeneous_X FX coxWeight v₀).pow t)).mul
        ((isWeightedHomogeneous_X FX coxWeight (seed₀ 1)).pow u)).mul
        ((isWeightedHomogeneous_X FX coxWeight (seed₀ 0)).pow (b-u))).mul
        ((isWeightedHomogeneous_X FX coxWeight (seed₁ 1)).pow v)
    have hd : (h+2*t) • coxWeight h₀ + t • coxWeight v₀ +
        u • coxWeight (seed₀ 1) + (b-u) • coxWeight (seed₀ 0) +
        v • coxWeight (seed₁ 1) + (c-v) • coxWeight (seed₁ 0) = nefDegree h t b c := by
      change ((h+2*t)*1+t*0+u*0+(b-u)*0+v*0+(c-v)*0,
        (h+2*t)*0+t*1+u*0+(b-u)*0+v*0+(c-v)*0,
        (h+2*t)*0+t*0+u*1+(b-u)*1+v*0+(c-v)*0,
        (h+2*t)*0+t*0+u*0+(b-u)*0+v*1+(c-v)*1) = (h+2*t,t,b,c)
      have hu : u ≤ b := by fin_cases i <;> simp_all [u]
      have hv : v ≤ c := by fin_cases i <;> simp_all [v]
      simp [Nat.add_sub_of_le hu, Nat.add_sub_of_le hv]
    exact hd ▸ hw.mul ((isWeightedHomogeneous_X FX coxWeight (seed₁ 0)).pow (c-v))
  · change Ideal.Quotient.mk P (dehom q) = _
    rw [← map_pow]
    congr 1
    fin_cases i <;> simp [q, u, v, dehom, affineCoord, h₀, v₀, seed₀, seed₁]

private theorem seed_bound {P : Ideal JetRing} (i : Fin 2) (hi : Transcendental FX (Ideal.Quotient.mk P (seedVar i))) (h t b c : ℕ) :
    (if i = 0 then b else c) + 1 ≤ hilbert P h t b c := by
  let z := Ideal.Quotient.mk P (seedVar i)
  let F : Polynomial FX →ₐ[FX] JetRing ⧸ P := Polynomial.aeval z
  have hF : Function.Injective F := transcendental_iff_injective.mp hi
  have hpow : LinearIndependent FX (fun j : ℕ => z ^ j) := by
    have he : (F.toLinearMap ∘ (Polynomial.basisMonomials FX : ℕ → Polynomial FX)) =
        fun j => z ^ j := by
      funext j
      simp only [Function.comp_apply, Polynomial.coe_basisMonomials,
        Polynomial.monomial_one_right_eq_X_pow, AlgHom.toLinearMap_apply, F,
        Polynomial.aeval_X_pow]
    rw [← he]
    exact (Polynomial.basisMonomials FX).linearIndependent.map' F.toLinearMap
      (LinearMap.ker_eq_bot.mpr hF)
  let d := nefDegree h t b c
  let f (j : Fin ((if i = 0 then b else c)+1)) : gradedPiece P d :=
    ⟨z ^ j.val, seed_pow_mem P i h t b c j.val (Nat.le_of_lt_succ j.isLt)⟩
  have hf : LinearIndependent FX f := LinearIndependent.of_comp (gradedPiece P d).subtype
    (hpow.comp Fin.val Fin.val_injective)
  simpa [hilbert, d] using hf.fintype_card_le_finrank
theorem Probe.seed_positive {Q : Ideal JetRing} (T : Probe Q)
    (hseed : SeedTranscendental Q) : 0 < T.coeff 2 + T.coeff 3 := by
  obtain ⟨i, hi⟩ := hseed
  let N := T.threshold
  have h₂ := T.nonnegative 2
  have h₃ := T.nonnegative 3
  by_contra! hsum
  have hz₂ : T.coeff 2 = 0 := by linarith
  have hz₃ : T.coeff 3 = 0 := by linarith
  let n := N + hilbert Q N N N N
  have hn : N ≤ n := Nat.le_add_right _ _
  have hsame : (hilbert Q N N n n : ℚ) = (hilbert Q N N N N : ℚ) := by
    rw [T.profile N N n n le_rfl le_rfl hn hn, T.profile N N N N le_rfl le_rfl le_rfl le_rfl,
      hz₂, hz₃]
    simp
  have hsame' : hilbert Q N N n n = hilbert Q N N N N := by exact_mod_cast hsame
  have hlarge := seed_bound i hi N N n n
  simp only [ite_self, hsame'] at hlarge
  dsimp [n] at hlarge
  omega

theorem Probe.mass_positive {Q : Ideal JetRing} (T : Probe Q)
    (hseed : SeedTranscendental Q) (h t b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    0 < T.mass h t b c := by
  have hp := T.seed_positive hseed
  have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hc' : (1 : ℚ) ≤ c := by exact_mod_cast hc
  have h₀ := mul_nonneg (Nat.cast_nonneg h) (T.nonnegative 0)
  have h₁ := mul_nonneg (Nat.cast_nonneg t) (T.nonnegative 1)
  have h₂ := mul_le_mul_of_nonneg_right hb' (T.nonnegative 2)
  have h₃ := mul_le_mul_of_nonneg_right hc' (T.nonnegative 3)
  unfold Probe.mass
  linarith

theorem Probe.mass_nat {Q : Ideal JetRing} (T : Probe Q) (h t b c : ℕ) :
    ∃ n : ℕ, (n : ℚ) = T.mass h t b c := by
  let N := T.threshold
  let u := hilbert Q N N N N
  let v := hilbert Q (N+h) (N+t) (N+b) (N+c)
  have hval : (v : ℚ) = (u : ℚ) + T.mass h t b c := by
    dsimp only [u, v]
    rw [T.profile _ _ _ _ (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      (Nat.le_add_right _ _) (Nat.le_add_right _ _), T.profile N N N N le_rfl le_rfl le_rfl le_rfl]
    unfold Probe.mass
    push_cast
    ring
  have hn : 0 ≤ T.mass h t b c := by
    unfold Probe.mass
    exact add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (T.nonnegative 0))
      (mul_nonneg (Nat.cast_nonneg _) (T.nonnegative 1)))
      (mul_nonneg (Nat.cast_nonneg _) (T.nonnegative 2)))
      (mul_nonneg (Nat.cast_nonneg _) (T.nonnegative 3))
  have huv : u ≤ v := by exact_mod_cast (show (u : ℚ) ≤ (v : ℚ) by linarith)
  exact ⟨v-u, by rw [Nat.cast_sub huv, hval, add_sub_cancel_left]⟩

end
end Rect51Point

#print axioms Rect51Point.Probe.ofProfile
#print axioms Rect51Point.Probe.mass_positive
#print axioms Rect51Point.Probe.mass_nat
#print axioms Rect51Point.probe_sums
