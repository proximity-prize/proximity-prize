import ProximityPrize.Benchmark.TargetLower
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots

namespace ProximityPrize.SubmissionLower.Koala6831Comparison

open Polynomial
open scoped BigOperators

noncomputable section

variable {K I : Type*} [CommRing K]

abbrev SeedIndex (b c : ℕ) := Fin b × Fin c

abbrev CoefficientIndex (h b c : ℕ) := Fin h × SeedIndex b c

abbrev RowIndex (A a d : ℕ) :=
  CoefficientIndex A (d + 2) (d + 2) ⊕
    (CoefficientIndex a (d + 1) (d + 2) ⊕ CoefficientIndex a (d + 2) (d + 1))

abbrev TargetIndex (I : Type*) (d : ℕ) := I × SeedIndex (d + 2) (d + 2)

private def emit {b c : ℕ} (j : SeedIndex b c) (v : K) (t : SeedIndex b c) : K :=
  if t = j then v else 0

private def betaConstraint {A d : ℕ} (x : K)
    (j : CoefficientIndex A (d + 2) (d + 2)) (t : SeedIndex (d + 2) (d + 2)) : K :=
  emit j.2 (x ^ j.1.val) t

private def firstConstraint {a d : ℕ} (x u v : K)
    (j : CoefficientIndex a (d + 1) (d + 2)) (t : SeedIndex (d + 2) (d + 2)) : K :=
  emit (j.2.1.castSucc, j.2.2) (x ^ j.1.val * u) t +
    emit (j.2.1.succ, j.2.2) (x ^ j.1.val * v) t

private def secondConstraint {a d : ℕ} (x u v : K)
    (j : CoefficientIndex a (d + 2) (d + 1)) (t : SeedIndex (d + 2) (d + 2)) : K :=
  emit (j.2.1, j.2.2.castSucc) (x ^ j.1.val * u) t +
    emit (j.2.1, j.2.2.succ) (x ^ j.1.val * v) t

def constraintMap (A a d : ℕ) (x : I → K) (u v : Fin 2 → I → K) :
    (RowIndex A a d → K) →ₗ[K] (TargetIndex I d → K) where
  toFun θ point :=
    (∑ j : CoefficientIndex A (d + 2) (d + 2),
      θ (.inl j) * betaConstraint (x point.1) j point.2) +
    (∑ j : CoefficientIndex a (d + 1) (d + 2),
      θ (.inr (.inl j)) * firstConstraint (x point.1) (u 0 point.1) (v 0 point.1) j point.2) +
    (∑ j : CoefficientIndex a (d + 2) (d + 1),
      θ (.inr (.inr j)) * secondConstraint (x point.1) (u 1 point.1) (v 1 point.1) j point.2)
  map_add' θ η := by
    funext point
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    abel
  map_smul' scalar θ := by
    funext point
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add]

abbrev ComparisonSpace (A a d : ℕ) (x : I → K) (u v : Fin 2 → I → K) :=
  (constraintMap A a d x u v).ker

theorem comparisonSpace_finrank_lower_bound {F : Type*} [Field F] [Fintype I]
    (A a d e : ℕ) (x : I → F) (u v : Fin 2 → I → F)
    (hcard : Fintype.card I = A + e) :
    (d + 2) * (2 * (d + 1) * a - e * (d + 2)) ≤
      Module.finrank F (ComparisonSpace A a d x u v) := by
  let f := constraintMap A a d x u v
  have hnull := f.finrank_range_add_finrank_ker
  have hdom : Module.finrank F (RowIndex A a d → F) =
      A * (d + 2) * (d + 2) + (d + 2) * (2 * (d + 1) * a) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [RowIndex, CoefficientIndex, SeedIndex, Fintype.card_sum,
      Fintype.card_prod, Fintype.card_fin]
    ring
  have htarget : Module.finrank F (TargetIndex I d → F) =
      A * (d + 2) * (d + 2) + (d + 2) * (e * (d + 2)) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [TargetIndex, SeedIndex, Fintype.card_prod, Fintype.card_fin, hcard]
    ring
  have hrange := f.range.finrank_le
  rw [hdom] at hnull
  rw [htarget] at hrange
  change _ ≤ Module.finrank F f.ker
  rw [Nat.mul_sub]
  omega

theorem exists_nonzero_comparison_row {F : Type*} [Field F] [Fintype I]
    (A a d e : ℕ) (x : I → F) (u v : Fin 2 → I → F)
    (hcard : Fintype.card I = A + e)
    (hgate : 0 < (d + 2) * (2 * (d + 1) * a - e * (d + 2))) :
    ∃ θ : ComparisonSpace A a d x u v, θ.1 ≠ 0 := by
  have hdim := hgate.trans_le (comparisonSpace_finrank_lower_bound A a d e x u v hcard)
  obtain ⟨θ, hθ⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  exact ⟨θ, fun h => hθ (Subtype.ext h)⟩

theorem exists_koalabear_comparison_rows {F : Type*} [Field F] [Fintype I]
    (x : I → F) (u v : Fin 2 → I → F) (hcard : Fintype.card I = 262144) :
    (∃ θ : ComparisonSpace 181078 50007 4 x u v, θ.1 ≠ 0) ∧
      (∃ θ : ComparisonSpace 181078 50007 200 x u v, θ.1 ≠ 0) := by
  constructor
  · exact exists_nonzero_comparison_row 181078 50007 4 81066 x u v hcard (by decide)
  · exact exists_nonzero_comparison_row 181078 50007 200 81066 x u v hcard (by decide)

private def seedMonomial {b c : ℕ} (z : K × K) (j : SeedIndex b c) : K :=
  z.1 ^ j.1.val * z.2 ^ j.2.val

private theorem sum_weighted_emit {b c : ℕ} (z : K × K)
    (j : SeedIndex b c) (value coefficient : K) :
    (∑ t : SeedIndex b c, coefficient * emit j value t * seedMonomial z t) =
      coefficient * value * seedMonomial z j := by
  simp [emit, mul_ite, ite_mul]

private theorem sum_weighted_columns
    {C : Type*} [Fintype C] {b c : ℕ} (z : K × K)
    (f w : C → K) (s : C → SeedIndex b c) :
    (∑ t : SeedIndex b c, (∑ j, f j * emit (s j) (w j) t) * seedMonomial z t) =
      ∑ j, f j * w j * seedMonomial z (s j) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact sum_weighted_emit z (s j) (w j) (f j)

def specializePiece {h b c : ℕ}
    (coefficients : CoefficientIndex h b c → K) (z : K × K) : Polynomial K :=
  ∑ j : CoefficientIndex h b c,
    monomial j.1.val (coefficients j * seedMonomial z j.2)

private theorem specializePiece_eval {h b c : ℕ}
    (coefficients : CoefficientIndex h b c → K) (z : K × K) (x : K) :
    (specializePiece coefficients z).eval x =
      ∑ j : CoefficientIndex h b c, coefficients j * x ^ j.1.val * seedMonomial z j.2 := by
  change (Polynomial.evalRingHom x) (specializePiece coefficients z) = _
  unfold specializePiece
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (monomial _ _).eval x = _
  rw [eval_monomial]
  ring

private theorem specializePiece_natDegree_le {h b c : ℕ}
    (coefficients : CoefficientIndex h b c → K) (z : K × K) :
    (specializePiece coefficients z).natDegree ≤ h - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  refine (Polynomial.natDegree_monomial_le
    (coefficients j * seedMonomial z j.2)).trans ?_
  have hj := j.1.isLt
  omega

structure SpecializedRow (K : Type*) [CommRing K] where
  beta : Polynomial K
  first : Polynomial K
  second : Polynomial K

def specialize {A a d : ℕ} (θ : RowIndex A a d → K) (z : K × K) :
    SpecializedRow K where
  beta := specializePiece (fun j => θ (.inl j)) z
  first := specializePiece (fun j => θ (.inr (.inl j))) z
  second := specializePiece (fun j => θ (.inr (.inr j))) z

theorem specialize_degrees {A a d : ℕ} (θ : RowIndex A a d → K) (z : K × K) :
    let q := specialize θ z
    q.beta.natDegree ≤ A - 1 ∧ q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
  ⟨specializePiece_natDegree_le _ _, specializePiece_natDegree_le _ _,
    specializePiece_natDegree_le _ _⟩

private theorem first_total {a d : ℕ} (z : K × K) (x u v : K)
    (f : CoefficientIndex a (d + 1) (d + 2) → K) :
    (∑ t : SeedIndex (d + 2) (d + 2),
      (∑ j, f j * firstConstraint x u v j t) * seedMonomial z t) =
      (specializePiece f z).eval x * (u + z.1 * v) := by
  conv_lhs =>
    simp only [firstConstraint, mul_add, Finset.sum_add_distrib, add_mul]
  rw [sum_weighted_columns, sum_weighted_columns, specializePiece_eval, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [seedMonomial, Fin.val_castSucc, Fin.val_succ, pow_succ]
  ring

private theorem second_total {a d : ℕ} (z : K × K) (x u v : K)
    (f : CoefficientIndex a (d + 2) (d + 1) → K) :
    (∑ t : SeedIndex (d + 2) (d + 2),
      (∑ j, f j * secondConstraint x u v j t) * seedMonomial z t) =
      (specializePiece f z).eval x * (u + z.2 * v) := by
  conv_lhs =>
    simp only [secondConstraint, mul_add, Finset.sum_add_distrib, add_mul]
  rw [sum_weighted_columns, sum_weighted_columns, specializePiece_eval, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [seedMonomial, Fin.val_castSucc, Fin.val_succ, pow_succ]
  ring

theorem specialize_eval_received_eq_zero {A a d : ℕ}
    (x : I → K) (u v : Fin 2 → I → K)
    (θ : ComparisonSpace A a d x u v) (z : K × K) (i : I) :
    let q := specialize θ.1 z
    q.beta.eval (x i) +
      q.first.eval (x i) * (u 0 i + z.1 * v 0 i) +
      q.second.eval (x i) * (u 1 i + z.2 * v 1 i) = 0 := by
  have hker : constraintMap A a d x u v θ.1 = 0 := LinearMap.mem_ker.mp θ.2
  have hzero :
      (∑ t : SeedIndex (d + 2) (d + 2),
        constraintMap A a d x u v θ.1 (i, t) * seedMonomial z t) = 0 := by
    simp [hker]
  change
      (∑ t : SeedIndex (d + 2) (d + 2),
        ((∑ j, θ.1 (.inl j) * betaConstraint (x i) j t) +
          (∑ j, θ.1 (.inr (.inl j)) * firstConstraint (x i) (u 0 i) (v 0 i) j t) +
          (∑ j, θ.1 (.inr (.inr j)) * secondConstraint (x i) (u 1 i) (v 1 i) j t)) *
            seedMonomial z t) = 0 at hzero
  simp only [add_mul, Finset.sum_add_distrib] at hzero
  rw [first_total, second_total] at hzero
  have hbeta :
      (∑ t : SeedIndex (d + 2) (d + 2),
        (∑ j, θ.1 (.inl j) * betaConstraint (x i) j t) * seedMonomial z t) =
          (specialize θ.1 z).beta.eval (x i) := by
    unfold betaConstraint
    rw [sum_weighted_columns]
    exact (specializePiece_eval _ _ _).symm
  rw [hbeta] at hzero
  exact hzero

private theorem constraintMap_baseChange {R : Type*} [CommRing R]
    (φ : K →+* R) {A a d : ℕ} (x : I → K) (u v : Fin 2 → I → K)
    (θ : RowIndex A a d → K) (t : TargetIndex I d) :
    constraintMap A a d (φ ∘ x) (fun j i => φ (u j i)) (fun j i => φ (v j i))
        (fun j => φ (θ j)) t =
      φ (constraintMap A a d x u v θ t) := by
  have mapEmit (i j : SeedIndex (d + 2) (d + 2)) (v : K) :
      φ (emit i v j) = emit i (φ v) j := by
    by_cases h : j = i <;> simp [emit, h]
  simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    betaConstraint, firstConstraint, secondConstraint, map_add, map_mul, map_sum, map_pow,
    mapEmit]

abbrev SeedRing (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K

def symbolicRow {A a d : ℕ} (θ : RowIndex A a d → K) : SpecializedRow (SeedRing K) :=
  specialize (fun j => MvPolynomial.C (θ j)) (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))

private theorem symbolicPiece_map_seedEval {h b c : ℕ}
    (θ : CoefficientIndex h b c → K) (f : Fin 2 → K) :
    (specializePiece (fun j => MvPolynomial.C (θ j))
        (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).map (MvPolynomial.eval f) =
      specializePiece θ (f 0, f 1) := by
  simp [specializePiece, seedMonomial, Polynomial.map_sum, Polynomial.map_monomial,
    MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem symbolicRow_map_seedEval {A a d : ℕ} (θ : RowIndex A a d → K) (f : Fin 2 → K) :
    let q := symbolicRow θ
    let p := specialize θ (f 0, f 1)
    q.beta.map (MvPolynomial.eval f) = p.beta ∧ q.first.map (MvPolynomial.eval f) = p.first ∧
      q.second.map (MvPolynomial.eval f) = p.second :=
  ⟨symbolicPiece_map_seedEval _ f, symbolicPiece_map_seedEval _ f,
    symbolicPiece_map_seedEval _ f⟩

theorem symbolicRow_eval_received_eq_zero {A a d : ℕ}
    (x : I → K) (u v : Fin 2 → I → K) (θ : ComparisonSpace A a d x u v) (i : I) :
    let q := symbolicRow θ.1
    q.beta.eval (MvPolynomial.C (x i)) +
      q.first.eval (MvPolynomial.C (x i)) *
        (MvPolynomial.C (u 0 i) + MvPolynomial.X 0 * MvPolynomial.C (v 0 i)) +
      q.second.eval (MvPolynomial.C (x i)) *
        (MvPolynomial.C (u 1 i) + MvPolynomial.X 1 * MvPolynomial.C (v 1 i)) = 0 := by
  let C : K →+* SeedRing K := MvPolynomial.C
  have h : constraintMap A a d (C ∘ x) (fun j i => C (u j i)) (fun j i => C (v j i))
      (fun j => C (θ.1 j)) = 0 := by
    funext t
    rw [constraintMap_baseChange]
    simp [LinearMap.mem_ker.mp θ.2]
  let lifted : ComparisonSpace A a d (C ∘ x) (fun j i => C (u j i)) (fun j i => C (v j i)) :=
    ⟨fun j => C (θ.1 j), LinearMap.mem_ker.mpr h⟩
  exact specialize_eval_received_eq_zero (C ∘ x) _ _ lifted (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)) i

private def seedExponent {b c : ℕ} (j : SeedIndex b c) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j.1.val + Finsupp.single 1 j.2.val

private theorem seedExponent_injective {b c : ℕ} :
    Function.Injective (seedExponent : SeedIndex b c → Fin 2 →₀ ℕ) := by
  intro j k h
  have h₀ := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  have h₁ := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  have hOne : (1 : Fin 2) ≠ 0 := by decide
  have hZero : (0 : Fin 2) ≠ 1 := Ne.symm hOne
  apply Prod.ext
  · apply Fin.ext
    simpa [seedExponent, Finsupp.single_apply, hOne, hZero] using h₀
  · apply Fin.ext
    simpa [seedExponent, Finsupp.single_apply, hOne, hZero] using h₁

private theorem symbolicMonomial {b c : ℕ} (z : SeedIndex b c) (v : K) :
    MvPolynomial.C v * seedMonomial (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)) z =
      MvPolynomial.monomial (seedExponent z) v := by
  simp [seedMonomial, seedExponent, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial]

private theorem symbolicPiece_coeff {h b c : ℕ}
    (θ : CoefficientIndex h b c → K) (j : CoefficientIndex h b c) :
    ((specializePiece (fun k => MvPolynomial.C (θ k))
        (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).coeff j.1.val).coeff
      (seedExponent j.2) = θ j := by
  classical
  rw [specializePiece, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro k _ hkj
    by_cases hx : k.1 = j.1
    · have hseed : seedExponent k.2 ≠ seedExponent j.2 := by
        intro he
        exact hkj (Prod.ext hx (seedExponent_injective he))
      simp [hx, symbolicMonomial, MvPolynomial.coeff_monomial, hseed]
    · have hval : k.1.val ≠ j.1.val := fun he => hx (Fin.ext he)
      simp [Polynomial.coeff_monomial, hval]
  · simp
  · simp [symbolicMonomial, MvPolynomial.coeff_monomial]

private theorem symbolicPiece_seed_degree_bounds {h b c : ℕ}
    (θ : CoefficientIndex h b c → K) (n : ℕ) :
    let P := (specializePiece (fun j => MvPolynomial.C (θ j))
      (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).coeff n
    P.degreeOf 0 ≤ b - 1 ∧ P.degreeOf 1 ≤ c - 1 := by
  let P := (specializePiece (fun j => MvPolynomial.C (θ j))
    (MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2))).coeff n
  have hOne : (1 : Fin 2) ≠ 0 := by decide
  have hZero : (0 : Fin 2) ≠ 1 := Ne.symm hOne
  have supported {m : Fin 2 →₀ ℕ} (hm : m ∈ P.support) :
      ∃ j : CoefficientIndex h b c, seedExponent j.2 = m := by
    by_contra hNone
    apply (MvPolynomial.mem_support_iff.mp hm)
    unfold P specializePiece
    rw [Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro j _
    have hne : seedExponent j.2 ≠ m := fun he => hNone ⟨j, he⟩
    by_cases hn : j.1.val = n
    · simp [hn, symbolicMonomial, MvPolynomial.coeff_monomial, hne]
    · simp [Polynomial.coeff_monomial, hn]
  constructor
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    obtain ⟨j, rfl⟩ := supported hm
    have hj := j.2.1.isLt
    simp [seedExponent, hZero]
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    obtain ⟨j, rfl⟩ := supported hm
    have hj := j.2.2.isLt
    simp [seedExponent, hOne]
    omega

theorem symbolicRow_seed_degree_bounds {A a d : ℕ} (θ : RowIndex A a d → K) (n : ℕ) :
    let q := symbolicRow θ
    ((q.beta.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.beta.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.first.coeff n).degreeOf 0 ≤ d ∧ (q.first.coeff n).degreeOf 1 ≤ d + 1) ∧
      ((q.second.coeff n).degreeOf 0 ≤ d + 1 ∧ (q.second.coeff n).degreeOf 1 ≤ d) :=
  ⟨symbolicPiece_seed_degree_bounds _ n, symbolicPiece_seed_degree_bounds _ n,
    symbolicPiece_seed_degree_bounds _ n⟩

theorem symbolicRow_injective (A a d : ℕ) :
    Function.Injective (symbolicRow : (RowIndex A a d → K) → SpecializedRow (SeedRing K)) := by
  intro θ η heq
  funext j
  rcases j with j | j
  · have h := congrArg (fun q : SpecializedRow (SeedRing K) =>
        (q.beta.coeff j.1.val).coeff (seedExponent j.2)) heq
    simpa only [symbolicRow, specialize, symbolicPiece_coeff] using h
  · rcases j with j | j
    · have h := congrArg (fun q : SpecializedRow (SeedRing K) =>
          (q.first.coeff j.1.val).coeff (seedExponent j.2)) heq
      simpa only [symbolicRow, specialize, symbolicPiece_coeff] using h
    · have h := congrArg (fun q : SpecializedRow (SeedRing K) =>
          (q.second.coeff j.1.val).coeff (seedExponent j.2)) heq
      simpa only [symbolicRow, specialize, symbolicPiece_coeff] using h

theorem specialize_selected_eq_zero [IsDomain K] {A a d w : ℕ}
    (x : I ↪ K) (U : Fin 2 → I → K) (σ : K →+* K)
    (hfixed : ∀ i, σ (x i) = x i) (haPos : 0 < a) (ha : a + w = A)
    (θ : ComparisonSpace A a d x (fun j i => if j = 0 then U 0 i else σ (U 0 i))
      (fun j i => if j = 0 then U 1 i else σ (U 1 i)))
    (γ : K) (P : Polynomial K) (hP : P.natDegree ≤ w)
    (S : Finset I) (hS : A ≤ S.card)
    (hagree : ∀ i ∈ S, P.eval (x i) = U 0 i + γ * U 1 i) :
    let q := specialize θ.1 (γ, σ γ)
    q.beta + q.first * P + q.second * P.map σ = 0 := by
  classical
  let q := specialize θ.1 (γ, σ γ)
  let Q := q.beta + q.first * P + q.second * P.map σ
  change Q = 0
  have hdegrees : q.beta.natDegree ≤ A - 1 ∧
      q.first.natDegree ≤ a - 1 ∧ q.second.natDegree ≤ a - 1 :=
    specialize_degrees θ.1 (γ, σ γ)
  obtain ⟨hb, h0, h1⟩ := hdegrees
  have h0w : (q.first * P).natDegree ≤ A - 1 := calc
    _ ≤ q.first.natDegree + P.natDegree := Polynomial.natDegree_mul_le
    _ ≤ A - 1 := by omega
  have hmap : (P.map σ).natDegree ≤ w := Polynomial.natDegree_map_le.trans hP
  have h1w : (q.second * P.map σ).natDegree ≤ A - 1 := calc
    _ ≤ q.second.natDegree + (P.map σ).natDegree := Polynomial.natDegree_mul_le
    _ ≤ A - 1 := by omega
  have hQ : Q.natDegree ≤ A - 1 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le hb h0w)) h1w)
  have hroots : ∀ i ∈ S, Q.eval (x i) = 0 := by
    intro i hi
    have hOne : (1 : Fin 2) ≠ 0 := by decide
    have h : q.beta.eval (x i) +
        q.first.eval (x i) * (U 0 i + γ * U 1 i) +
        q.second.eval (x i) * (σ (U 0 i) + σ γ * σ (U 1 i)) = 0 := by
      simpa [q, hOne] using
        specialize_eval_received_eq_zero x _ _ θ (γ, σ γ) i
    have hconjugate : (P.map σ).eval (x i) = σ (P.eval (x i)) := by
      calc
        (P.map σ).eval (x i) = (P.map σ).eval (σ (x i)) := by rw [hfixed i]
        _ = σ (P.eval (x i)) := by rw [Polynomial.eval_map_apply]
    simpa only [Q, Polynomial.eval_add, Polynomial.eval_mul, hconjugate,
      hagree i hi, map_add, map_mul] using h
  by_contra hne
  have hcount : (S.image x).card ≤ Q.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact (Polynomial.mem_roots hne).mpr (hroots i hi)
  rw [Finset.card_image_of_injective _ x.injective] at hcount
  omega

end

end ProximityPrize.SubmissionLower.Koala6831Comparison

/- Modified for this joint-incidence adaptation of Lucieno’s PR 618, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
