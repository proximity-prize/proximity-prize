import ProximityPrize.SubmissionLower.Koala6831IntrinsicSelectedComponents
import ProximityPrize.SubmissionLower.Koala6831IntrinsicLongLiteral


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial RCN002 RCN004 RCN005 RCN013 RCN022 RCN042 RCN135 RCN136 RCN137 RCN264 RCN344
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {Ω : Type} [Field Ω]

def frobeniusSlice (Ω : Type) [Field Ω] (p : ℕ) : MvPolynomial (Fin 3) Ω :=
  MvPolynomial.X 2 - MvPolynomial.X 1 ^ p

theorem frobeniusSlice_y_degree (p : ℕ) : (frobeniusSlice Ω p).degreeOf 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  apply max_le
  · simp [MvPolynomial.degreeOf_X]
  · exact (MvPolynomial.degreeOf_pow_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])

theorem frobeniusSlice_z₁_degree_le (p : ℕ) : (frobeniusSlice Ω p).degreeOf 2 ≤ 1 := by
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  apply max_le
  · simp [MvPolynomial.degreeOf_X]
  · exact (MvPolynomial.degreeOf_pow_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])

theorem frobeniusSlice_nonzero (p : ℕ) : frobeniusSlice Ω p ≠ 0 := by
  intro h
  have hX : (MvPolynomial.X 2 : MvPolynomial (Fin 3) Ω) = MvPolynomial.X 1 ^ p :=
    sub_eq_zero.mp h
  have hz : (MvPolynomial.X 1 ^ p : MvPolynomial (Fin 3) Ω).degreeOf 2 ≤ 0 :=
    (MvPolynomial.degreeOf_pow_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])
  rw [← hX, MvPolynomial.degreeOf_X] at hz
  simp at hz

theorem frobeniusSlice_coordinate (p : ℕ) (C : Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime]
    (hC : frobeniusSlice Ω p ∈ C) :
    coordinate Ω C 2 = coordinate Ω C 1 ^ p := by
  have hz : MvPolynomial.aeval (coordinate Ω C) (frobeniusSlice Ω p) = 0 := by
    change frobeniusSlice Ω p ∈ RingHom.ker (MvPolynomial.aeval (coordinate Ω C)).toRingHom
    rwa [aeval_coordinate_ker]
  simpa only [frobeniusSlice, map_sub, map_pow, MvPolynomial.aeval_X, sub_eq_zero] using hz

theorem frobeniusSlice_selected_zero {K : Type} [Field K] (p : ℕ) (selected : K → Polynomial K) (g : K) :
    MvPolynomial.eval (selectedGraphPoint p selected g) (frobeniusSlice (GenericField K) p) = 0 := by
  simp only [frobeniusSlice, map_sub, map_pow, MvPolynomial.eval_X]
  change (polynomialEmbedding K).comp Polynomial.C (g ^ p) -
    ((polynomialEmbedding K).comp Polynomial.C g) ^ p = 0
  rw [map_pow, sub_self]

variable [IsAlgClosed Ω]

theorem frobeniusSlice_seed_transcendental (p : ℕ)
    (G H : MvPolynomial (Fin 3) Ω)
    (C : RegularComponent Ω G (frobeniusSlice Ω p) H)
    (hG : MvPolynomial.pderiv 0 G ∉ C.1) :
    Transcendental Ω (coordinate Ω C.1 1) := by
  obtain hZ₀ | hZ₁ := seed_transcendental_of_separant C.1 G
    (regularComponent_G_mem Ω G _ H C) hG (regularComponent_ne_point Ω G _ H C)
  · exact hZ₀
  · intro hAlg
    apply hZ₁
    rw [frobeniusSlice_coordinate p C.1 (regularComponent_T_mem Ω G _ H C)]
    exact hAlg.pow _

theorem frobeniusSlice_projection_budget (p : ℕ) [CharP Ω p]
    (G H : MvPolynomial (Fin 3) Ω) (hG : Irreducible G)
    (hGy : G.degreeOf 0 < p) (hGz : G.degreeOf 2 < p)
    (hreg : ∀ C : RegularComponent Ω G (frobeniusSlice Ω p) H, MvPolynomial.pderiv 0 G ∉ C.1)
    (hpositive : 0 < G.degreeOf 0) :
    let C := RegularComponent Ω G (frobeniusSlice Ω p) H
    letI : ∀ c : C, Algebra (RatFunc Ω) (CoordinateField Ω c.1) :=
      fun c => rationalBaseAlgebra Ω c.1 1 (frobeniusSlice_seed_transcendental p G H c (hreg c))
    (∀ c : C, FiniteDimensional (RatFunc Ω) (CoordinateField Ω c.1) ∧
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω c.1)) ∧
    (∑ c : C, Module.finrank (RatFunc Ω) (CoordinateField Ω c.1)) ≤ G.degreeOf 0 := by
  classical
  let order := Equiv.swap (0 : Fin 3) 1
  let T := frobeniusSlice Ω p
  let C := RegularComponent Ω G T H
  let ideal (c : C) := c.1
  have ht (c : C) : Transcendental Ω (coordinate Ω (ideal c) (order 0)) :=
    frobeniusSlice_seed_transcendental p G H c (hreg c)
  have hproper : ¬ G ∣ T := by
    intro hd
    have h := coordinate_degree_le_of_dvd 0 G T hd (frobeniusSlice_nonzero p)
    rw [frobeniusSlice_y_degree] at h
    exact (not_lt_of_ge h) hpositive
  have hdeg : originalMixedDegree Ω order G T ≤ G.degreeOf 0 := by
    change T.degreeOf 0 * G.degreeOf 2 + G.degreeOf 0 * T.degreeOf 2 ≤ _
    rw [frobeniusSlice_y_degree, Nat.zero_mul, Nat.zero_add]
    exact (Nat.mul_le_mul_left _ (frobeniusSlice_z₁_degree_le p)).trans_eq (Nat.mul_one _)
  obtain ⟨hfields, hsum⟩ := original_finite_separable_sum_finrank_bound Ω order ideal ht
    Subtype.val_injective p G T hG (fun c => regularComponent_G_mem Ω G T H c)
    (fun c => regularComponent_T_mem Ω G T H c) hproper hGy hGz (hdeg.trans_lt hGy)
  exact ⟨hfields, hsum.trans hdeg⟩

theorem frobeniusSlice_seed_cover {K : Type} [Field K] (p : ℕ)
    (F : Carrier K) (G : MvPolynomial (Fin 3) (GenericField K))
    (seeds : Finset K) (selected : K → Polynomial K)
    (hG : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint p selected g) G = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) (implicitRegularity F) ≠ 0) :
    let E := GenericField K
    let H := surfaceMap (polynomialEmbedding K) (implicitRegularity F)
    seeds.card ≤ ∑ C : RegularComponent E G (frobeniusSlice E p) H,
      (componentSeeds E G (frobeniusSlice E p) H seeds (selectedGraphPoint p selected) C).card := by
  refine card_le_sum_componentSeeds _ G (frobeniusSlice _ p) _ seeds (selectedGraphPoint p selected) hG
    (fun g _ => frobeniusSlice_selected_zero p selected g) ?_
  intro g hg
  change MvPolynomial.eval (polynomialGraphSurfacePoint (polynomialEmbedding K) (selected g) g (g ^ p))
    (surfaceMap (polynomialEmbedding K) (implicitRegularity F)) ≠ 0
  rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
  exact hreg g hg

private theorem poleOrder_pow {E : Type} [Field E]
    (v : Valuation E (WithZero (Multiplicative ℤ))) (x : E) (p : ℕ) :
    RCN187.poleOrder v (x ^ p) = (p : ℤ) * RCN187.poleOrder v x := by
  simp only [RCN187.poleOrder, map_pow, WithZero.log_pow, nsmul_eq_mul]
  by_cases h : 0 ≤ (v x).log
  · rw [max_eq_right h, max_eq_right (mul_nonneg (Int.natCast_nonneg _) h)]
  · rw [max_eq_left (le_of_not_ge h), mul_zero]
    exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (le_of_not_ge h))

theorem frobeniusSlice_component_poles (p : ℕ)
    (C : Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime] (hC : frobeniusSlice Ω p ∈ C)
    (hx : Transcendental Ω (coordinate Ω C 1))
    (hfinite : letI := rationalBaseAlgebra Ω C 1 hx
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω C))
    (hsep : letI := rationalBaseAlgebra Ω C 1 hx
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C))
    (W : Finset (Place Ω (CoordinateField Ω C))) :
    letI := rationalBaseAlgebra Ω C 1 hx
    let d := Module.finrank (RatFunc Ω) (CoordinateField Ω C)
    (∑ v ∈ W, RCN187.poleOrder v.val (coordinate Ω C 1)) ≤ (d : ℤ) ∧
      (∑ v ∈ W, RCN187.poleOrder v.val (coordinate Ω C 2)) ≤ (p : ℤ) * d := by
  let E := CoordinateField Ω C
  let x := coordinate Ω C 1
  letI := rationalBaseAlgebra Ω C 1 hx
  let d := Module.finrank (RatFunc Ω) E
  have hgate (ht : Transcendental Ω x) :
      (letI := (elementEmbedding Ω E x ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) E) ∧
      (letI := (elementEmbedding Ω E x ht).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) E) :=
    ⟨hfinite, hsep⟩
  have hz : (∑ v ∈ W, RCN187.poleOrder v.val x) ≤ (d : ℤ) := by
    have h := finite_sum_coordinate_pole_le_degree Ω E (coordinateOfGate x hgate) W
    rw [coordinateOfGate_value, coordinateOfGate_degree_of_transcendental x hgate hx] at h
    exact h
  refine ⟨hz, ?_⟩
  rw [frobeniusSlice_coordinate p C hC]
  simp only [poleOrder_pow, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg _)

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
