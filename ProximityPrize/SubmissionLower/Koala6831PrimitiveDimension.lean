import ProximityPrize.SubmissionLower.Koala6831Primitive

namespace ProximityPrize.SubmissionLower.Koala6831Comparison

open Polynomial
open scoped BigOperators Classical

noncomputable section

variable {K I : Type*} [Field K]

def primitiveBadNodes [Fintype I] (x : I ↪ K) (u v : Fin 2 → I → K)
    (q : SymbolicRow (SeedRing K)) : Finset I :=
  Finset.univ.filter fun i => q.atNode (seedNode x i) (affineSeedWord u v 0 i)
    (affineSeedWord u v 1 i) ≠ 0

def primitiveExcess (w : ℕ) (q : SymbolicRow (SeedRing K)) : ℕ :=
  max (q.beta.natDegree - w) (max q.first.natDegree q.second.natDegree)

private theorem row_eq_of_piece_eq {R : Type*} [CommRing R] {q r : SymbolicRow R}
    (hβ : q.beta = r.beta) (h₀ : q.first = r.first) (h₁ : q.second = r.second) : q = r := by
  cases q
  cases r
  simp_all

private def firstPieceLinear {A a d : ℕ} (x : I ↪ K) (u v : Fin 2 → I → K) :
    ComparisonSpace A a d x u v →ₗ[K] SeedCoefficients K where
  toFun θ := (rankRow θ.1).first
  map_add' θ η := by
    simp [rankRow, symbolicRow, specialize, specializePiece, add_mul, Finset.sum_add_distrib]
  map_smul' s θ := by
    simp [rankRow, symbolicRow, specialize, specializePiece, Polynomial.smul_monomial,
      MvPolynomial.smul_eq_C_mul, Finset.smul_sum, mul_assoc]

private theorem badNodeLocator_ne_zero (x : I ↪ K) (bad : Finset I) :
    badNodeLocator (seedNode x) bad ≠ 0 := by
  unfold badNodeLocator
  exact (Polynomial.monic_multisetProd_X_sub_C _).ne_zero

private theorem locator_dvd_multiplier [Fintype I] {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (θ : ComparisonSpace A a d x u v) (m : SeedCoefficients K)
    (hm : RowFactors q (rankRow θ.1) m) :
    badNodeLocator (seedNode x) (primitiveBadNodes x u v q) ∣ m := by
  apply badNodeLocator_dvd_of_vanishing
  intro i hi
  exact multiplier_eval_eq_zero_of_bad_node q (rankRow θ.1) m (seedNode x i)
    (affineSeedWord u v 0 i) (affineSeedWord u v 1 i) hm.beta hm.first hm.second
    (rankRow_atNode_zero x u v θ i) (Finset.mem_filter.mp hi).2

private theorem quotient_mul_divides_first [Fintype I] {A a d : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (h : ∀ θ : ComparisonSpace A a d x u v, ∃ m, RowFactors q (rankRow θ.1) m)
    (θ : ComparisonSpace A a d x u v) :
    badNodeLocator (seedNode x) (primitiveBadNodes x u v q) * q.first ∣
      firstPieceLinear (A := A) (a := a) (d := d) x u v θ := by
  obtain ⟨m, hm⟩ := h θ
  obtain ⟨f, hf⟩ := locator_dvd_multiplier x u v q θ m hm
  refine ⟨f, ?_⟩
  change (rankRow θ.1).first = _
  rw [hm.first, hf]
  ac_rfl

theorem comparisonSpace_finrank_le_primitiveBox [Fintype I] {A a d w : ℕ}
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) (ha : 0 < a) (hA : a + w = A)
    (h : ∀ θ : ComparisonSpace A a d x u v, ∃ m, RowFactors q (rankRow θ.1) m) :
    Module.finrank K (ComparisonSpace A a d x u v) ≤
      (a - (primitiveExcess w q + (primitiveBadNodes x u v q).card)) * (d + 1) * (d + 1) := by
  let bad := primitiveBadNodes x u v q
  let D := badNodeLocator (seedNode x) bad
  have hD : D ≠ 0 := badNodeLocator_ne_zero x bad
  let L := firstPieceLinear (A := A) (a := a) (d := d) x u v
  let f := divideMultiplierLinear L (D * q.first) (mul_ne_zero hD h₀)
    (quotient_mul_divides_first x u v q h)
  have factors (v' : ComparisonSpace A a d x u v) : RowFactors q (rankRow v'.1) (D * f v') := by
    obtain ⟨m, hm⟩ := h v'
    have he := divideMultiplierLinear_spec L (D * q.first) (mul_ne_zero hD h₀)
      (quotient_mul_divides_first x u v q h) v'
    change (rankRow v'.1).first = (D * q.first) * f v' at he
    have hm' : m = D * f v' := by
      apply mul_right_cancel₀ h₀
      rw [← hm.first, he]
      ac_rfl
    simpa only [hm'] using hm
  have hinj : Function.Injective f := by
    intro v' t' he
    apply Subtype.ext
    apply rankRow_injective A a d
    apply row_eq_of_piece_eq
    · rw [(factors v').beta, (factors t').beta, he]
    · rw [(factors v').first, (factors t').first, he]
    · rw [(factors v').second, (factors t').second, he]
  apply finrank_le_of_multiplierBox f hinj
  intro θ
  let fθ := f θ
  change InMultiplierBox (a - (primitiveExcess w q + bad.card)) (d + 1) (d + 1) fθ
  by_cases hf : fθ = 0
  · simp [hf, InMultiplierBox]
  have hb := rankRow_degrees θ.1
  have hF : RowFactors q (rankRow θ.1) (D * fθ) := factors θ
  have hid : D.natDegree = bad.card := badNodeLocator_natDegree (seedNode x) bad
  have hnonzero : D * fθ ≠ 0 := mul_ne_zero hD hf
  have hdf : (D * fθ).natDegree = bad.card + fθ.natDegree := by
    rw [Polynomial.natDegree_mul hD hf, hid]
  have hα₀ : fθ.natDegree + bad.card + q.first.natDegree ≤ a - 1 := by
    have hh := hb.2.1
    rw [hF.first, Polynomial.natDegree_mul hnonzero h₀, hdf] at hh
    omega
  have hα₁ : fθ.natDegree + bad.card + q.second.natDegree ≤ a - 1 := by
    have hh := hb.2.2
    rw [hF.second, Polynomial.natDegree_mul hnonzero h₁, hdf] at hh
    omega
  have hβ : fθ.natDegree + bad.card + (q.beta.natDegree - w) ≤ a - 1 := by
    by_cases hz : q.beta = 0
    · simp [hz]
      omega
    · have hh := hb.1
      rw [hF.beta, Polynomial.natDegree_mul hnonzero hz, hdf] at hh
      omega
  have hx : fθ.natDegree < a - (primitiveExcess w q + bad.card) := by
    unfold primitiveExcess
    omega
  have hp₀ : (rankRow θ.1).first = fθ * (D * q.first) := by rw [hF.first]; ac_rfl
  have hp₁ : (rankRow θ.1).second = fθ * (D * q.second) := by rw [hF.second]; ac_rfl
  have hd₀ := multiplier_seed_coeff_degree_le fθ _ _ (0 : Fin 2) d hp₀
    (hp₀ ▸ mul_ne_zero hf (mul_ne_zero hD h₀))
    (fun n => (symbolicRow_seed_degree_bounds θ.1 n).2.1.1)
  have hd₁ := multiplier_seed_coeff_degree_le fθ _ _ (1 : Fin 2) d hp₁
    (hp₁ ▸ mul_ne_zero hf (mul_ne_zero hD h₁))
    (fun n => (symbolicRow_seed_degree_bounds θ.1 n).2.2.2)
  refine ⟨fun n hn => Polynomial.coeff_eq_zero_of_natDegree_lt (hx.trans_le hn), fun n => ?_⟩
  exact ⟨Nat.lt_succ_of_le (hd₀ n), Nat.lt_succ_of_le (hd₁ n)⟩

theorem primitive_excess_add_badCard_le_31059 [Fintype I]
    (x : I ↪ K) (u v : Fin 2 → I → K) (q : SymbolicRow (SeedRing K))
    (h₀ : q.first ≠ 0) (h₁ : q.second ≠ 0) (hcard : Fintype.card I = 262144)
    (h : ∀ θ : ComparisonSpace 181078 50007 62150 x u v, ∃ m, RowFactors q (rankRow θ.1) m) :
    primitiveExcess 131071 q + (primitiveBadNodes x u v q).card ≤ 31059 := by
  have hlo := comparisonSpace_finrank_lower_bound 181078 50007 62150 81066 x u v hcard
  have hhi := comparisonSpace_finrank_le_primitiveBox x u v q h₀ h₁ (by decide)
    (w := 131071) (by decide) h
  have hbound := hlo.trans hhi
  norm_num at hbound
  omega

end

end ProximityPrize.SubmissionLower.Koala6831Comparison

/- Modified for this joint-incidence adaptation of Lucieno’s PR 618, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
