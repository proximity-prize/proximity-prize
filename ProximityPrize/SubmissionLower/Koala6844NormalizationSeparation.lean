import ProximityPrize.SubmissionLower.Koala6844Primitive
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring



section SeparationPart0

namespace ProximityPrize.SubmissionLower.Koala6844Separation

open Polynomial
open Koala6844CoefficientSystem (coefficientPolynomial)
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def regroup : (MvPolynomial (Fin 2) K)[X] →+* MvPolynomial (Fin 2) K[X] :=
  Polynomial.eval₂RingHom (MvPolynomial.map Polynomial.C) (MvPolynomial.C Polynomial.X)

@[simp] theorem regroup_C (P : MvPolynomial (Fin 2) K) :
    regroup (Polynomial.C P) = MvPolynomial.map Polynomial.C P := by simp [regroup]

@[simp] theorem regroup_X :
    regroup (Polynomial.X : (MvPolynomial (Fin 2) K)[X]) = MvPolynomial.C Polynomial.X := by
  simp [regroup]

theorem coeff_regroup_eq (P : (MvPolynomial (Fin 2) K)[X]) (m : Fin 2 →₀ ℕ) (cap : ℕ)
    (hP : P.natDegree ≤ cap) :
    (regroup P).coeff m = coefficientPolynomial P m cap := by
  change (P.eval₂ (MvPolynomial.map Polynomial.C) (MvPolynomial.C Polynomial.X)).coeff m = _
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hP), MvPolynomial.coeff_sum]
  unfold coefficientPolynomial
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_pow, mul_comm (MvPolynomial.map Polynomial.C (P.coeff i)), MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, mul_comm, Polynomial.C_mul_X_pow_eq_monomial]

private theorem coeff_coefficientPolynomial (P : (MvPolynomial (Fin 2) K)[X])
    (m : Fin 2 →₀ ℕ) (cap i : ℕ) (hP : P.natDegree ≤ cap) :
    (coefficientPolynomial P m cap).coeff i = (P.coeff i).coeff m := by
  unfold coefficientPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  by_cases hi : i ≤ cap
  · simp [hi]
  · have hzero : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_of_not_ge hi))
    simp [hi, hzero]

theorem regroup_injective : Function.Injective (regroup (K := K)) := by
  intro P Q h
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  have he := congrArg (fun f : MvPolynomial (Fin 2) K[X] ↦ (f.coeff m).coeff i) h
  have hP : P.natDegree ≤ max P.natDegree Q.natDegree := le_max_left _ _
  have hQ : Q.natDegree ≤ max P.natDegree Q.natDegree := le_max_right _ _
  simpa only [coeff_regroup_eq P m _ hP, coeff_regroup_eq Q m _ hQ,
    coeff_coefficientPolynomial P m _ i hP, coeff_coefficientPolynomial Q m _ i hQ] using he

theorem regroup_surjective : Function.Surjective (regroup (K := K)) := by
  have hconst : regroup.comp (Polynomial.mapRingHom (MvPolynomial.C :
      K →+* MvPolynomial (Fin 2) K)) = MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  intro P
  induction P using MvPolynomial.induction_on with
  | C t =>
      exact ⟨t.map MvPolynomial.C, DFunLike.congr_fun hconst t⟩
  | add P Q hP hQ =>
      obtain ⟨p, rfl⟩ := hP
      obtain ⟨q, rfl⟩ := hQ
      exact ⟨p + q, map_add _ _ _⟩
  | mul_X P i hP =>
      obtain ⟨p, rfl⟩ := hP
      refine ⟨p * Polynomial.C (MvPolynomial.X i), ?_⟩
      rw [map_mul, regroup_C, MvPolynomial.map_X]

theorem primitive_regroup (beta first second : (MvPolynomial (Fin 2) K)[X])
    (h : ∀ D, D ∣ beta → D ∣ first → D ∣ second → IsUnit D) :
    ∀ D, D ∣ regroup beta → D ∣ regroup first → D ∣ regroup second → IsUnit D := by
  intro D hβ h₁ h₂
  obtain ⟨d, rfl⟩ := regroup_surjective D
  have lift (x : (MvPolynomial (Fin 2) K)[X]) (hx : regroup d ∣ regroup x) : d ∣ x := by
    obtain ⟨q, hq⟩ := hx
    obtain ⟨p, rfl⟩ := regroup_surjective q
    exact ⟨p, regroup_injective (hq.trans (map_mul _ _ _).symm)⟩
  exact (h d (lift _ hβ) (lift _ h₁) (lift _ h₂)).map regroup

theorem map_eval_regroup (P : (MvPolynomial (Fin 2) K)[X]) (x : K) :
    MvPolynomial.map (Polynomial.evalRingHom x) (regroup P) = P.eval (MvPolynomial.C x) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_map, coeff_regroup_eq P m P.natDegree le_rfl]
  exact Koala6844CoefficientSystem.eval_coefficientPolynomial P m P.natDegree x le_rfl

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart0


section SeparationPart1

namespace ProximityPrize.SubmissionLower.Koala6844Separation

open scoped BigOperators Matrix

variable {F ι : Type*} [Field F]

private theorem row_span_of_independent_columns {m : ℕ} (M : ι → Fin m → F)
    (h : LinearIndependent F (fun j i ↦ M i j)) :
    Submodule.span F (Set.range M) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨f, hne, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  let b := Pi.basisFun F (Fin m)
  let z (j : Fin m) : F := f (b j)
  have hrepr (v : Fin m → F) : (∑ j, z j * v j) = f v := by
    have he := congrArg f (b.sum_repr v)
    simpa [z, b, map_sum, map_smul, smul_eq_mul, mul_comm] using he
  have hsum : ∑ j, z j • (fun i ↦ M i j) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [hrepr]
    exact hker (Submodule.subset_span ⟨i, rfl⟩)
  have hz (j : Fin m) := Fintype.linearIndependent_iff.mp h z hsum j
  apply hne
  apply LinearMap.ext
  intro v
  simp only [LinearMap.zero_apply, ← hrepr, hz, zero_mul, Finset.sum_const_zero]

theorem exists_nonzero_minor_of_independent_columns {m : ℕ}
    (cols : Fin m → ι → F) (h : LinearIndependent F cols) :
    ∃ keys : Fin m → ι, (Matrix.of fun i j ↦ cols j (keys i)).det ≠ 0 := by
  classical
  let row (i : ι) (j : Fin m) := cols j i
  have hspan := row_span_of_independent_columns row h
  obtain ⟨s, select, _, hs, hli⟩ := exists_linearIndependent' F row
  have : Finite s := hli.finite
  let _ : Fintype s := Fintype.ofFinite s
  let b : Module.Basis s F (Fin m → F) := Module.Basis.mk hli (by rw [hs, hspan])
  have hcard : Fintype.card (Fin m) = Fintype.card s :=
    (Module.finrank_eq_card_basis (Pi.basisFun F (Fin m))).symm.trans
      (Module.finrank_eq_card_basis b)
  let e := Fintype.equivOfCardEq hcard
  refine ⟨select ∘ e, ?_⟩
  let N : Matrix (Fin m) (Fin m) F := Matrix.of fun i j ↦ cols j (select (e i))
  have hN : LinearIndependent F N.row := hli.comp e e.injective
  exact (Matrix.isUnit_iff_isUnit_det N).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hN)
    |>.ne_zero

theorem exists_relation_of_singular_minors {m : ℕ}
    (cols : Fin m → ι → F)
    (h : ∀ keys : Fin m → ι, (Matrix.of fun i j ↦ cols j (keys i)).det = 0) :
    ∃ v : Fin m → F, v ≠ 0 ∧ ∑ j, v j • cols j = 0 := by
  classical
  have hnot : ¬ LinearIndependent F cols := fun hind ↦ by
    obtain ⟨keys, hk⟩ := exists_nonzero_minor_of_independent_columns cols hind
    exact hk (h keys)
  rw [Fintype.linearIndependent_iff] at hnot
  push Not at hnot
  obtain ⟨v, hv, i, hi⟩ := hnot
  exact ⟨v, fun he ↦ hi (by rw [he, Pi.zero_apply]), hv⟩

theorem mem_span_of_singular_augmented_minors {m : ℕ}
    (cols : Fin (m + 1) → ι → F) (rhs : ι → F) (slot : Fin (m + 1))
    (hind : LinearIndependent F (cols ∘ slot.succAbove))
    (h : ∀ keys : Fin (m + 1) → ι,
      ((Matrix.of fun i j ↦ cols j (keys i)).updateCol slot (fun i ↦ rhs (keys i))).det = 0) :
    rhs ∈ Submodule.span F (Set.range (cols ∘ slot.succAbove)) := by
  classical
  by_contra hout
  have hv := (hind.option hout).comp (finSuccEquiv' slot) (Equiv.injective _)
  obtain ⟨keys, hkeys⟩ := exists_nonzero_minor_of_independent_columns _ hv
  apply hkeys
  convert h keys using 2
  ext i j
  refine Fin.succAboveCases slot ?_ (fun k ↦ ?_) j
  · simp
  · simp [Fin.succAbove_ne]

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart1


section SeparationPart2

namespace ProximityPrize.SubmissionLower.Koala6844Separation

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

abbrev Seeds (R : Type*) [CommSemiring R] := MvPolynomial (Fin 2) R

noncomputable def seedColumns (a b : Seeds F) : Fin 4 → Seeds F := ![a, MvPolynomial.X 0 * a, b, MvPolynomial.X 1 * b]

private theorem first_two_independent {a : Seeds F} (ha : a ≠ 0) :
    LinearIndependent F (![a, MvPolynomial.X 0 * a] : Fin 2 → Seeds F) := by
  refine (LinearIndependent.pair_iff' ha).mpr fun t ht ↦ ?_
  rw [smul_eq_C_mul] at ht
  have he : (MvPolynomial.C t : Seeds F) = MvPolynomial.X 0 := mul_right_cancel₀ ha ht
  have hz : t = 0 := by simpa using congrArg (eval (fun _ ↦ 0)) he
  exact (X_ne_zero (R := F) (0 : Fin 2)) (by simpa [hz] using he.symm)

private theorem range_first_two (a : Seeds F) :
    Set.range (![a, MvPolynomial.X 0 * a] : Fin 2 → Seeds F) = {a, MvPolynomial.X 0 * a} := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem exists_independent_triple {a b : Seeds F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ slot : Fin 4, LinearIndependent F (seedColumns a b ∘ slot.succAbove) := by
  have hind := first_two_independent ha
  let W := Submodule.span F (Set.range (![a, MvPolynomial.X 0 * a] : Fin 2 → Seeds F))
  by_cases hbm : b ∈ W
  · have hb1 : MvPolynomial.X 1 * b ∉ W := by
      intro hb1
      dsimp only [W] at hbm hb1
      rw [range_first_two] at hbm hb1
      obtain ⟨u, v, h⟩ := Submodule.mem_span_pair.mp hbm
      obtain ⟨s, t, h'⟩ := Submodule.mem_span_pair.mp hb1
      simp only [smul_eq_C_mul] at h h'
      have hL : (MvPolynomial.C u + MvPolynomial.C v * MvPolynomial.X 0) * a = b := by linear_combination h
      have hR : (MvPolynomial.C s + MvPolynomial.C t * MvPolynomial.X 0) * a = MvPolynomial.X 1 * b := by linear_combination h'
      have he : (MvPolynomial.X 1 * (MvPolynomial.C u + MvPolynomial.C v * MvPolynomial.X 0) : Seeds F) = MvPolynomial.C s + MvPolynomial.C t * MvPolynomial.X 0 := by
        apply mul_right_cancel₀ ha
        rw [mul_assoc, hL, hR]
      let erase : Seeds F →+* Seeds F :=
        MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦ if i = 1 then 0 else MvPolynomial.X i)
      have hzero : (MvPolynomial.C s + MvPolynomial.C t * MvPolynomial.X 0 : Seeds F) = 0 := by
        have he' := congrArg erase he
        symm
        simpa [erase, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
          show (0 : Fin 2) ≠ 1 by decide] using he'
      rw [hzero] at he
      rcases mul_eq_zero.mp he with hx | hh
      · exact (X_ne_zero (R := F) (1 : Fin 2)) hx
      · exact hb (by rw [← hL, hh, zero_mul])
    refine ⟨2, ?_⟩
    have he : seedColumns a b ∘ (2 : Fin 4).succAbove =
        Fin.snoc (![a, MvPolynomial.X 0 * a] : Fin 2 → Seeds F) (MvPolynomial.X 1 * b) := by
      funext j
      fin_cases j <;> rfl
    rw [he]
    exact hind.finSnoc hb1
  · refine ⟨3, ?_⟩
    have he : seedColumns a b ∘ (3 : Fin 4).succAbove =
        Fin.snoc (![a, MvPolynomial.X 0 * a] : Fin 2 → Seeds F) b := by
      funext j
      fin_cases j <;> rfl
    rw [he]
    exact hind.finSnoc hbm

noncomputable def coefficients : Seeds F →ₗ[F] ((Fin 2 →₀ ℕ) → F) :=
  LinearMap.pi fun key ↦ MvPolynomial.lcoeff F key

theorem coefficients_injective : Function.Injective (coefficients (F := F)) := by
  intro f g h
  apply MvPolynomial.ext
  exact fun key ↦ congrFun h key

theorem exists_affine_relation {a b : Seeds F} (v : Fin 4 → F)
    (hv : v ≠ 0) (hs : ∑ j, v j • seedColumns a b j = 0) :
    (v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0) ∧
      (MvPolynomial.C (v 0) + MvPolynomial.C (v 1) * MvPolynomial.X 0) * a + (MvPolynomial.C (v 2) + MvPolynomial.C (v 3) * MvPolynomial.X 1) * b = 0 := by
  constructor
  · by_contra! hz
    apply hv
    funext j
    fin_cases j
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2
  · simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      seedColumns, Matrix.cons_val_zero, Matrix.cons_val_succ, smul_eq_C_mul] at hs
    change MvPolynomial.C (v 0) * a + (MvPolynomial.C (v 1) * (MvPolynomial.X 0 * a) +
      (MvPolynomial.C (v 2) * b + MvPolynomial.C (v 3) * (MvPolynomial.X 1 * b))) = 0 at hs
    linear_combination hs

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart2


section SeparationPart3

namespace ProximityPrize.SubmissionLower.Koala6844Separation

open Polynomial
open Koala6844Comparison (SymbolicRow)
open Koala6844CoefficientSystem (coefficientPolynomial matrix_node_equation)
open scoped BigOperators Matrix Polynomial

set_option maxHeartbeats 5000000

variable {K I : Type*} [Field K]

abbrev NodeField (K : Type*) [Field K] := FractionRing K[X]

noncomputable def asRational : (Seeds K)[X] →+* Seeds (NodeField K) :=
  (MvPolynomial.map (algebraMap K[X] (NodeField K))).comp regroup

theorem asRational_injective : Function.Injective (asRational (K := K)) :=
  (MvPolynomial.map_injective _ (IsFractionRing.injective _ _)).comp regroup_injective

private theorem columns_degree (q : SymbolicRow (Seeds K)) (δ : ℕ)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ) :
    ∀ j, (Koala6844RankFour.columns q j).natDegree ≤ δ := by
  intro j
  fin_cases j
  · exact hfirst
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hfirst
  · exact hsecond
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hsecond

private theorem columns_asRational (q : SymbolicRow (Seeds K)) (j : Fin 4) :
    asRational (Koala6844RankFour.columns q j) =
      seedColumns (asRational q.first) (asRational q.second) j := by
  have hX (i : Fin 2) :
      asRational (Polynomial.C (MvPolynomial.X i : Seeds K)) = MvPolynomial.X i := by
    simp [asRational]
  fin_cases j
  · rfl
  · change asRational (Polynomial.C (MvPolynomial.X 0) * q.first) = _
    rw [map_mul, hX]
    rfl
  · rfl
  · change asRational (Polynomial.C (MvPolynomial.X 1) * q.second) = _
    rw [map_mul, hX]
    rfl

private theorem coeff_asRational (P : (Seeds K)[X]) (key : Fin 2 →₀ ℕ) (cap : ℕ)
    (hP : P.natDegree ≤ cap) :
    (asRational P).coeff key = algebraMap K[X] (NodeField K) (coefficientPolynomial P key cap) := by
  change (MvPolynomial.map (algebraMap K[X] (NodeField K)) (regroup P)).coeff key = _
  rw [MvPolynomial.coeff_map, coeff_regroup_eq _ _ _ hP]

theorem rational_relation_and_span (domain : I ↪ K) (nodes : Finset I)
    (q : SymbolicRow (Seeds K)) (word : I → Fin 4 → K) (w δ : ℕ)
    (hfirst0 : q.first ≠ 0) (hsecond0 : q.second ≠ 0)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ)
    (hbeta : q.beta.natDegree ≤ w + δ) (hcard : w + 4 * δ < nodes.card)
    (hgood : ∀ i ∈ nodes,
      q.atNode (MvPolynomial.C (domain i))
        (MvPolynomial.C (word i 0) + MvPolynomial.X 0 * MvPolynomial.C (word i 1))
        (MvPolynomial.C (word i 2) + MvPolynomial.X 1 * MvPolynomial.C (word i 3)) = 0)
    (hsingular : ∀ keys : Fin 4 → (Fin 2 →₀ ℕ), (Koala6844RankFour.matrix q keys δ).det = 0) :
    let cols := seedColumns (asRational q.first) (asRational q.second)
    (∃ v : Fin 4 → NodeField K, v ≠ 0 ∧ ∑ j, v j • cols j = 0) ∧
      asRational q.beta ∈ Submodule.span (NodeField K) (Set.range cols) := by
  classical
  let φ := algebraMap K[X] (NodeField K)
  let cols := seedColumns (asRational q.first) (asRational q.second)
  let cs := coefficients ∘ cols
  have hcols := columns_degree q δ hfirst hsecond
  have hentry (j : Fin 4) (key : Fin 2 →₀ ℕ) :
      cs j key = φ (coefficientPolynomial (Koala6844RankFour.columns q j) key δ) := by
    change (seedColumns (asRational q.first) (asRational q.second) j).coeff key = _
    rw [← columns_asRational q j, coeff_asRational _ _ _ (hcols j)]
  have hneg : (-q.beta).natDegree ≤ w + δ := by simpa using hbeta
  let rhs := coefficients (asRational (-q.beta))
  have hr (key : Fin 2 →₀ ℕ) :
      rhs key = φ (coefficientPolynomial (-q.beta) key (w + δ)) :=
    coeff_asRational _ _ _ hneg
  have hm (keys : Fin 4 → (Fin 2 →₀ ℕ)) :
      φ.mapMatrix (Koala6844RankFour.matrix q keys δ) =
        Matrix.of (fun i j ↦ cs j (keys i)) := by
    ext i j
    exact (hentry j (keys i)).symm
  have hcs (keys : Fin 4 → (Fin 2 →₀ ℕ)) :
      (Matrix.of fun i j ↦ cs j (keys i)).det = 0 := by
    rw [← hm, ← RingHom.map_det, hsingular keys, map_zero]
  have haug (keys : Fin 4 → (Fin 2 →₀ ℕ)) (slot : Fin 4) :
      ((Matrix.of fun i j ↦ cs j (keys i)).updateCol slot (fun i ↦ rhs (keys i))).det = 0 := by
    let right (i : Fin 4) := coefficientPolynomial (-q.beta) (keys i) (w + δ)
    have haug0 : ((Koala6844RankFour.matrix q keys δ).updateCol slot right).det = 0 := by
      apply Koala6844Cramer.augmented_minor_eq_zero domain nodes _ right word w δ slot
        (hsingular keys)
      · exact fun _ _ ↦ Koala6844CoefficientSystem.coefficientPolynomial_degree _ _ _
      · exact fun _ ↦ Koala6844CoefficientSystem.coefficientPolynomial_degree _ _ _
      · exact hcard
      · intro i hi
        exact matrix_node_equation (Koala6844RankFour.columns q) (-q.beta) keys w δ (domain i)
          (word i) hcols hneg (Koala6844RankFour.equation_of_good_node q (domain i) (word i)
            (hgood i hi))
    have he : φ.mapMatrix ((Koala6844RankFour.matrix q keys δ).updateCol slot right) =
        (Matrix.of fun i j ↦ cs j (keys i)).updateCol slot (fun i ↦ rhs (keys i)) := by
      rw [RingHom.mapMatrix_apply, Matrix.map_updateCol, ← RingHom.mapMatrix_apply, hm]
      congr 1
      funext i
      exact (hr (keys i)).symm
    rw [← he, ← RingHom.map_det, haug0, map_zero]
  obtain ⟨v, hv, hsum⟩ := exists_relation_of_singular_minors cs hcs
  have hvsum : ∑ j, v j • cols j = 0 := by
    apply coefficients_injective
    simpa only [map_sum, map_smul, map_zero, cs, Function.comp_apply] using hsum
  have hn₀ : asRational q.first ≠ 0 :=
    fun he ↦ hfirst0 (asRational_injective (he.trans (map_zero _).symm))
  have hn₁ : asRational q.second ≠ 0 :=
    fun he ↦ hsecond0 (asRational_injective (he.trans (map_zero _).symm))
  obtain ⟨slot, hslot⟩ := exists_independent_triple hn₀ hn₁
  have hslot' : LinearIndependent (NodeField K) (cs ∘ slot.succAbove) :=
    hslot.map' coefficients (LinearMap.ker_eq_bot.mpr coefficients_injective)
  have hmem := mem_span_of_singular_augmented_minors cs rhs slot hslot'
    (fun keys ↦ haug keys slot)
  have hmem' : rhs ∈ (Submodule.span (NodeField K) (Set.range (cols ∘ slot.succAbove))).map
      coefficients := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact hmem
  obtain ⟨z, hz, he⟩ := hmem'
  have hz' : z = asRational (-q.beta) := coefficients_injective he
  have hmFull : asRational (-q.beta) ∈ Submodule.span (NodeField K) (Set.range cols) := by
    rw [← hz']
    apply Submodule.span_mono _ hz
    rintro y ⟨j, rfl⟩
    exact ⟨slot.succAbove j, rfl⟩
  exact ⟨⟨v, hv, hvsum⟩, by simpa only [map_neg, neg_neg] using Submodule.neg_mem _ hmFull⟩

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart3


section SeparationPart4

namespace ProximityPrize.SubmissionLower.Koala6844Separation

variable {R S : Type*} [CommRing R] [CommRing S]

def wedge (A B : Fin 2 → R) (β : Fin 2 → Fin 2 → R) : R :=
  A 1 * (β 0 0 * B 1 - β 0 1 * B 0) -
    A 0 * (β 1 0 * B 1 - β 1 1 * B 0)

theorem wedge_eq_zero_of_decomposition (A B C D : Fin 2 → R)
    (β : Fin 2 → Fin 2 → R) (h : ∀ i j, β i j = C i * B j + A i * D j) :
    wedge A B β = 0 := by
  simp only [wedge, h]
  ring

theorem exists_integral_decomposition (A B : Fin 2 → R) (β : Fin 2 → Fin 2 → R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : wedge A B β = 0) :
    ∃ C D : Fin 2 → R, ∀ i j, β i j = C i * B j + A i * D j := by
  obtain ⟨a₀, a₁, ha⟩ := hA
  obtain ⟨b₀, b₁, hb⟩ := hB
  let u (i : Fin 2) := β i 0 * B 1 - β i 1 * B 0
  let s := a₀ * u 0 + a₁ * u 1
  have hw : A 1 * u 0 - A 0 * u 1 = 0 := h
  have hu (i : Fin 2) : u i = A i * s := by
    fin_cases i
    · change u 0 = A 0 * s
      dsimp only [s]
      linear_combination a₁ * hw - u 0 * ha
    · change u 1 = A 1 * s
      dsimp only [s]
      linear_combination -a₀ * hw - u 1 * ha
  let C (i : Fin 2) := β i 0 * b₀ + β i 1 * b₁
  let D (j : Fin 2) := if j = 0 then s * b₁ else -(s * b₀)
  refine ⟨C, D, fun i j ↦ ?_⟩
  have hui : β i 0 * B 1 - β i 1 * B 0 = A i * s := hu i
  fin_cases j
  · change β i 0 = C i * B 0 + A i * D 0
    simp only [C, D, ite_eq_left rfl]
    linear_combination b₁ * hui - β i 0 * hb
  · change β i 1 = C i * B 1 + A i * D 1
    simp only [C, D, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    linear_combination -b₀ * hui - β i 1 * hb


theorem exists_scalar_of_tensor_zero (A B C D : Fin 2 → R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : ∀ i j, C i * B j + A i * D j = 0) :
    ∃ t : R, (∀ i, C i = t * A i) ∧ ∀ j, D j = -(t * B j) := by
  obtain ⟨a₀, a₁, ha⟩ := hA
  obtain ⟨b₀, b₁, hb⟩ := hB
  let t := -(D 0 * b₀ + D 1 * b₁)
  have hC (i : Fin 2) : C i = t * A i := by
    dsimp only [t]
    linear_combination b₀ * h i 0 + b₁ * h i 1 - C i * hb
  refine ⟨t, hC, fun j ↦ ?_⟩
  have h0 : A 0 * (D j + t * B j) = 0 := by
    linear_combination h 0 j - B j * hC 0
  have h1 : A 1 * (D j + t * B j) = 0 := by
    linear_combination h 1 j - B j * hC 1
  linear_combination a₀ * h0 + a₁ * h1 - (D j + t * B j) * ha

theorem fixed_word (A B C D U V : Fin 2 → R) (d₀ d₁ : R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : ∀ i j, (d₀ * U i + C i) * B j + A i * (D j - d₁ * V j) = 0) :
    ∃ u : R, (∀ i, d₀ * U i + C i = u * A i) ∧
      ∀ j, d₁ * V j - D j = u * B j := by
  obtain ⟨u, hU, hV⟩ := exists_scalar_of_tensor_zero A B (fun i ↦ d₀ * U i + C i)
    (fun j ↦ D j - d₁ * V j) hA hB h
  exact ⟨u, hU, fun j ↦ by linear_combination -(hV j)⟩

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart4


section SeparationPart5

namespace ProximityPrize.SubmissionLower.Koala6844Separation

open Polynomial

variable {K : Type*} [Field K]

def pairDegree (A : Fin 2 → K[X]) : ℕ := max (A 0).natDegree (A 1).natDegree

theorem natDegree_le_pairDegree (A : Fin 2 → K[X]) (i : Fin 2) :
    (A i).natDegree ≤ pairDegree A := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

private theorem pairDegree_le_iff (A : Fin 2 → K[X]) (n : ℕ) :
    pairDegree A ≤ n ↔ ∀ i, (A i).natDegree ≤ n := by
  constructor
  · exact fun h i ↦ (natDegree_le_pairDegree A i).trans h
  · exact fun h ↦ max_le (h 0) (h 1)

private theorem coprime_of_nonzero_pair {a b : K} (h : a ≠ 0 ∨ b ≠ 0) :
    IsCoprime a b := by
  rcases h with ha | hb
  · exact ⟨a⁻¹, 0, by simp [ha]⟩
  · exact ⟨0, b⁻¹, by simp [hb]⟩

private theorem pair_top_coprime (A : Fin 2 → K[X]) (hn : A 0 ≠ 0 ∨ A 1 ≠ 0) :
    IsCoprime ((A 0).coeff (pairDegree A)) ((A 1).coeff (pairDegree A)) := by
  apply coprime_of_nonzero_pair
  by_cases h : (A 0).natDegree ≤ (A 1).natDegree
  · have he : pairDegree A = (A 1).natDegree := max_eq_right h
    by_cases h1 : A 1 = 0
    · have h0 : A 0 ≠ 0 := hn.resolve_right (fun h ↦ h h1)
      have hh : (A 0).natDegree = (A 1).natDegree := by simpa [h1] using h
      exact Or.inl (by simpa only [he, ← hh, leadingCoeff] using leadingCoeff_ne_zero.mpr h0)
    · exact Or.inr (by simpa only [he, leadingCoeff] using leadingCoeff_ne_zero.mpr h1)
  · have hh : (A 1).natDegree < (A 0).natDegree := Nat.lt_of_not_ge h
    have he : pairDegree A = (A 0).natDegree := max_eq_left hh.le
    have h0 : A 0 ≠ 0 := by
      intro h0
      simp [h0] at hh
    exact Or.inl (by simpa only [he, leadingCoeff] using leadingCoeff_ne_zero.mpr h0)

private theorem degree_drop_of_top_cancel {P F : K[X]} {r a q : ℕ} {t : K}
    (hr : 0 < r) (hqa : q + a = r) (hP : P.natDegree ≤ r) (hF : F.natDegree ≤ a)
    (hcoeff : P.coeff r = t * F.coeff a) :
    (P - monomial q t * F).natDegree < r := by
  have hq : (monomial q t).natDegree ≤ q := natDegree_monomial_le _
  have hbound : (P - monomial q t * F).natDegree ≤ r :=
    (natDegree_sub_le _ _).trans (max_le hP (hqa ▸ natDegree_mul_le_of_le hq hF))
  have htop : (monomial q t * F).coeff r = t * F.coeff a := by
    rw [← hqa, coeff_mul_add_eq_of_natDegree_le hq hF, coeff_monomial]
    simp
  have hzero : (P - monomial q t * F).coeff r = 0 := by rw [coeff_sub, hcoeff, htop, sub_self]
  by_contra hc
  have heq := Nat.le_antisymm hbound (Nat.le_of_not_gt hc)
  have hpzero : P - monomial q t * F = 0 := leadingCoeff_eq_zero.mp (by
    unfold leadingCoeff
    rw [heq]
    exact hzero)
  exact hc (by simpa [hpzero] using hr)

theorem exists_decomposition_with_degree (A B : Fin 2 → K[X]) (β : Fin 2 → Fin 2 → K[X])
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (lim : ℕ) (hlim : pairDegree A + pairDegree B ≤ lim)
    (hβ : ∀ i j, (β i j).natDegree ≤ lim) (hw : wedge A B β = 0) :
    ∃ C D : Fin 2 → K[X], pairDegree B + pairDegree C ≤ lim ∧
      pairDegree A + pairDegree D ≤ lim ∧ ∀ i j, β i j = C i * B j + A i * D j := by
  obtain ⟨C, D, hCD⟩ := exists_integral_decomposition A B β hA hB hw
  have hAn : A 0 ≠ 0 ∨ A 1 ≠ 0 := by
    by_contra! hn
    obtain ⟨u, v, h⟩ := hA
    simp [hn.1, hn.2] at h
  have hBn : B 0 ≠ 0 ∨ B 1 ≠ 0 := by
    by_contra! hn
    obtain ⟨u, v, h⟩ := hB
    simp [hn.1, hn.2] at h
  let a := pairDegree A
  let b := pairDegree B
  have hnormalize (n : ℕ) : ∀ C D : Fin 2 → K[X],
      (∀ i j, β i j = C i * B j + A i * D j) →
      b + pairDegree C ≤ n → a + pairDegree D ≤ n →
      ∃ C' D' : Fin 2 → K[X], b + pairDegree C' ≤ lim ∧
        a + pairDegree D' ≤ lim ∧ ∀ i j, β i j = C' i * B j + A i * D' j := by
    induction n with
    | zero =>
        intro C D h hC hD
        exact ⟨C, D, hC.trans (Nat.zero_le _), hD.trans (Nat.zero_le _), h⟩
    | succ n ih =>
        intro C D h hC hD
        by_cases hl : n.succ ≤ lim
        · exact ⟨C, D, hC.trans hl, hD.trans hl, h⟩
        let c := n.succ - b
        let d := n.succ - a
        let shift := n.succ - (a + b)
        have hab : a + b ≤ lim := hlim
        have hrc : c + b = n.succ := by dsimp [c]; omega
        have hsd : a + d = n.succ := by dsimp [d]; omega
        have hc : ∀ i, (C i).natDegree ≤ c := (pairDegree_le_iff _ _).mp (by dsimp [c]; omega)
        have hd : ∀ i, (D i).natDegree ≤ d := (pairDegree_le_iff _ _).mp (by dsimp [d]; omega)
        have ha : ∀ i, (A i).natDegree ≤ a := natDegree_le_pairDegree A
        have hb : ∀ j, (B j).natDegree ≤ b := natDegree_le_pairDegree B
        have htop (i j : Fin 2) :
            (C i).coeff c * (B j).coeff b + (A i).coeff a * (D j).coeff d = 0 := by
          have hzero := coeff_eq_zero_of_natDegree_lt ((hβ i j).trans_lt (Nat.lt_of_not_ge hl))
          rw [h i j, coeff_add] at hzero
          have hCtop : (C i * B j).coeff n.succ = (C i).coeff c * (B j).coeff b := by
            rw [← hrc, coeff_mul_add_eq_of_natDegree_le (hc i) (hb j)]
          have hDtop : (A i * D j).coeff n.succ = (A i).coeff a * (D j).coeff d := by
            rw [← hsd, coeff_mul_add_eq_of_natDegree_le (ha i) (hd j)]
          rwa [hCtop, hDtop] at hzero
        obtain ⟨t, hCt, hDt⟩ := exists_scalar_of_tensor_zero
          (fun i ↦ (A i).coeff a) (fun i ↦ (B i).coeff b)
          (fun i ↦ (C i).coeff c) (fun i ↦ (D i).coeff d)
          (pair_top_coprime A hAn) (pair_top_coprime B hBn) htop
        let C' (i : Fin 2) := C i - monomial shift t * A i
        let D' (j : Fin 2) := D j - monomial shift (-t) * B j
        have hC' (i : Fin 2) : (C' i).natDegree < c :=
          degree_drop_of_top_cancel (by dsimp [c]; omega) (by dsimp [shift,c]; omega)
            (hc i) (ha i) (hCt i)
        have hD' (j : Fin 2) : (D' j).natDegree < d :=
          degree_drop_of_top_cancel (by dsimp [d]; omega) (by dsimp [shift,d]; omega)
            (hd j) (hb j) (by simpa only [neg_mul] using hDt j)
        have hCd : b + pairDegree C' ≤ n := by
          have hdeg := (pairDegree_le_iff C' (c - 1)).mpr fun i ↦ by have hi := hC' i; omega
          have hcpos : 0 < c := by dsimp [c]; omega
          omega
        have hDd : a + pairDegree D' ≤ n := by
          have hdeg := (pairDegree_le_iff D' (d - 1)).mpr fun i ↦ by have hi := hD' i; omega
          have hdpos : 0 < d := by dsimp [d]; omega
          omega
        apply ih C' D' (fun i j ↦ ?_) hCd hDd
        rw [h i j]
        dsimp only [C', D']
        rw [monomial_neg]
        ring
  exact hnormalize (max (b + pairDegree C) (a + pairDegree D)) C D hCD
    (le_max_left _ _) (le_max_right _ _)

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart5


section SeparationPart6

namespace ProximityPrize.SubmissionLower.Koala6844SeparationFactors

open MvPolynomial
open scoped Polynomial nonZeroDivisors

variable {F : Type*} [Field F]

abbrev SeedPolynomial (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R

noncomputable def affine {R : Type*} [CommRing R] (i : Fin 2) (c d : R) :
    SeedPolynomial R := MvPolynomial.C c + MvPolynomial.C d * MvPolynomial.X i

theorem affine_eq_zero_iff (i : Fin 2) (c d : F) : affine i c d = 0 ↔ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hc : c = 0 := by
      simpa [affine] using congrArg (MvPolynomial.eval fun _ : Fin 2 ↦ (0 : F)) h
    have hd : d = 0 := by
      simpa [affine, hc] using congrArg (MvPolynomial.eval fun _ : Fin 2 ↦ (1 : F)) h
    exact ⟨hc, hd⟩
  · rintro ⟨rfl, rfl⟩
    simp [affine]

private theorem affine_left_dvd_of_relation (a₀ a₁ b₀ b₁ : F)
    (first second : SeedPolynomial F) (hA : affine 0 a₀ a₁ ≠ 0)
    (hB : affine 1 b₀ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * first + affine 1 b₀ b₁ * second = 0) :
    affine 0 a₀ a₁ ∣ second := by
  by_cases h₁ : a₁ = 0
  · have h₀ : a₀ ≠ 0 := fun ha ↦ hA ((affine_eq_zero_iff _ _ _).mpr ⟨ha, h₁⟩)
    refine ⟨MvPolynomial.C a₀⁻¹ * second, ?_⟩
    simp only [affine, h₁, map_zero, zero_mul, add_zero]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h₀, map_one, one_mul]
  · let e := finSuccEquiv F 1
    let r : MvPolynomial (Fin 1) F := MvPolynomial.C (-a₀ / a₁)
    let cF : F →+* (MvPolynomial (Fin 1) F)[X] := Polynomial.C.comp MvPolynomial.C
    have ha : e (affine 0 a₀ a₁) = Polynomial.C (MvPolynomial.C a₁) * (Polynomial.X - Polynomial.C r) := by
      simp only [e, affine, map_add, map_mul,
        finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply]
      rw [mul_sub, ← map_mul, ← map_mul, mul_div_cancel₀ _ h₁]
      simp [add_comm]
    have hb : e (affine 1 b₀ b₁) = Polynomial.C (MvPolynomial.C b₀ + MvPolynomial.C b₁ * MvPolynomial.X 0) := by
      have h' : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
      have hx : e (MvPolynomial.X (1 : Fin 2)) = Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
        rw [h']
        exact finSuccEquiv_X_succ
      have hc (c : F) : e (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
        rw [show e (MvPolynomial.C c) = finSuccEquiv F 1 (MvPolynomial.C c) from rfl, finSuccEquiv_apply, eval₂Hom_C]
        rfl
      simp only [affine, map_add, map_mul, hx, hc]
    have hb₀ : MvPolynomial.C b₀ + MvPolynomial.C b₁ * (MvPolynomial.X 0 : MvPolynomial (Fin 1) F) ≠ 0 := by
      intro hz
      apply hB
      apply e.injective
      simp [hb, hz]
    have hroot : Polynomial.IsRoot (e second) r := by
      have hrel := congrArg (fun t ↦ (e t).eval r) rel
      simp only [map_add, map_mul, map_zero, ha, hb, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_zero,
        sub_self, mul_zero, zero_mul, zero_add] at hrel
      exact (mul_eq_zero.mp hrel).resolve_left hb₀
    obtain ⟨D, hD⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    have hinv : cF a₁ * cF a₁⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h₁, map_one]
    refine ⟨e.symm (cF a₁⁻¹ * D), e.injective ?_⟩
    rw [map_mul, ha, AlgEquiv.apply_symm_apply, hD]
    calc
      (Polynomial.X - Polynomial.C r) * D =
          (cF a₁ * cF a₁⁻¹) * ((Polynomial.X - Polynomial.C r) * D) := by rw [hinv, one_mul]
      _ = (cF a₁ * (Polynomial.X - Polynomial.C r)) * (cF a₁⁻¹ * D) := by ac_rfl

theorem factor_of_relation (a₀ a₁ b₀ b₁ : F) (first second : SeedPolynomial F)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hnonzero : a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ b₀ ≠ 0 ∨ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * first + affine 1 b₀ b₁ * second = 0) :
    ∃ G : SeedPolynomial F, G ≠ 0 ∧
      first = affine 1 b₀ b₁ * G ∧ second = -(affine 0 a₀ a₁ * G) := by
  have impossible (hA : affine 0 a₀ a₁ = 0) (hB : affine 1 b₀ b₁ = 0) : False := by
    rcases (affine_eq_zero_iff _ _ _).mp hA with ⟨rfl, rfl⟩
    rcases (affine_eq_zero_iff _ _ _).mp hB with ⟨rfl, rfl⟩
    simp at hnonzero
  have hA : affine 0 a₀ a₁ ≠ 0 := by
    intro hz
    apply impossible hz
    rw [hz, zero_mul, zero_add] at rel
    exact (mul_eq_zero.mp rel).resolve_right hsecond
  have hB : affine 1 b₀ b₁ ≠ 0 := by
    intro hz
    refine impossible ?_ hz
    rw [hz, zero_mul, add_zero] at rel
    exact (mul_eq_zero.mp rel).resolve_right hfirst
  obtain ⟨D, hD⟩ := affine_left_dvd_of_relation a₀ a₁ b₀ b₁ first second hA hB rel
  have hfirst' : first = affine 1 b₀ b₁ * (-D) := by
    apply mul_left_cancel₀ hA
    calc
      _ = -(affine 1 b₀ b₁ * second) := eq_neg_of_add_eq_zero_left rel
      _ = _ := by rw [hD]; ring
  refine ⟨-D, ?_, hfirst', ?_⟩
  · intro h
    exact hfirst (by simpa [h] using hfirst')
  · simpa using hD

theorem separate_of_primitive_relation (a₀ a₁ b₀ b₁ : F)
    (beta first second left right : SeedPolynomial F)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hnonzero : a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ b₀ ≠ 0 ∨ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * first + affine 1 b₀ b₁ * second = 0)
    (hbeta : beta = left * first + right * second)
    (hprimitive : ∀ G : SeedPolynomial F, G ∣ beta → G ∣ first → G ∣ second → IsUnit G) :
    ∃ c : F, c ≠ 0 ∧ first = affine 1 b₀ b₁ * MvPolynomial.C c ∧
      second = -(affine 0 a₀ a₁ * MvPolynomial.C c) := by
  obtain ⟨G, hG, h₁, h₂⟩ := factor_of_relation a₀ a₁ b₀ b₁ first second
    hfirst hsecond hnonzero rel
  have hd₁ : G ∣ first := by rw [h₁]; exact dvd_mul_left _ _
  have hd₂ : G ∣ second := by rw [h₂, dvd_neg]; exact dvd_mul_left _ _
  have hdβ : G ∣ beta := by
    rw [hbeta]
    exact dvd_add (dvd_mul_of_dvd_right hd₁ left) (dvd_mul_of_dvd_right hd₂ right)
  obtain ⟨c, hc, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp (hprimitive G hdβ hd₁ hd₂)
  exact ⟨c, hc.ne_zero, h₁, h₂⟩

section Integral

variable {R : Type*} [CommRing R] [IsDomain R] [Algebra R F] [IsFractionRing R F]

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable abbrev fractionMap : SeedPolynomial R →+* SeedPolynomial F :=
  MvPolynomial.map (algebraMap R F)

omit [IsDomain R] in
private theorem fractionMap_injective :
    Function.Injective (fractionMap (R := R) (F := F)) :=
  MvPolynomial.map_injective _ (IsFractionRing.injective R F)

private theorem clear_denominator (P : SeedPolynomial F) :
    ∃ (N : SeedPolynomial R) (d : R), d ≠ 0 ∧
      P * fractionMap (MvPolynomial.C d) = fractionMap N := by
  obtain ⟨⟨N, m⟩, h⟩ := IsLocalization.surj
    ((nonZeroDivisors R).map (MvPolynomial.C (σ := Fin 2))) P
  obtain ⟨d, hd, hdm⟩ := m.property
  refine ⟨N, d, nonZeroDivisors.ne_zero hd, ?_⟩
  simpa only [MvPolynomial.algebraMap_def, ← hdm] using h

private theorem clear_fraction_divisibility {H P : SeedPolynomial R}
    (h : fractionMap (F := F) H ∣ fractionMap P) :
    ∃ d : R, d ≠ 0 ∧ H ∣ MvPolynomial.C d * P := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨N, d, hd, hN⟩ := clear_denominator (R := R) Q
  refine ⟨d, hd, N, fractionMap_injective (F := F) ?_⟩
  simp only [map_mul, hQ, ← hN, mul_left_comm, mul_comm]

set_option maxHeartbeats 1200000 in
theorem primitive_fractionMap [GCDMonoid (SeedPolynomial R)]
    {beta first second : SeedPolynomial R}
    (hprimitive : ∀ D : SeedPolynomial R, D ∣ beta → D ∣ first → D ∣ second → IsUnit D)
    (G : SeedPolynomial F) (hβ : G ∣ fractionMap beta)
    (h₁ : G ∣ fractionMap first) (h₂ : G ∣ fractionMap second) : IsUnit G := by
  obtain ⟨H, m, hm, hH⟩ := clear_denominator (R := R) G
  have hmUnit : IsUnit (fractionMap (F := F) (MvPolynomial.C m)) := by
    rw [fractionMap, MvPolynomial.map_C]
    apply IsUnit.map MvPolynomial.C
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hm
  have hHG : fractionMap H ∣ G := by
    rw [← hH]
    simpa using mul_dvd_mul (dvd_refl G) (isUnit_iff_dvd_one.mp hmUnit)
  obtain ⟨dβ, hdβ, h'β⟩ := clear_fraction_divisibility (hHG.trans hβ)
  obtain ⟨d₁, hd₁, h'₁⟩ := clear_fraction_divisibility (hHG.trans h₁)
  obtain ⟨d₂, hd₂, h'₂⟩ := clear_fraction_divisibility (hHG.trans h₂)
  let d := dβ * d₁ * d₂
  have hd : d ≠ 0 := mul_ne_zero (mul_ne_zero hdβ hd₁) hd₂
  have scale (P : SeedPolynomial R) (q r s : R) (hdiv : H ∣ MvPolynomial.C q * P) :
      H ∣ MvPolynomial.C (q * r * s) * P := by
    calc
      H ∣ MvPolynomial.C (r * s) * (MvPolynomial.C q * P) := dvd_mul_of_dvd_right hdiv _
      _ = _ := by simp only [map_mul, mul_left_comm, mul_comm]
  obtain ⟨H', D', hH', hD', hcoprime⟩ := extract_gcd H (MvPolynomial.C d)
  let M := gcd H (MvPolynomial.C d)
  have hCd : (MvPolynomial.C d : SeedPolynomial R) ≠ 0 := by simpa using hd
  have hM : M ≠ 0 := gcd_ne_zero_of_right hCd
  have cancel {P : SeedPolynomial R} (h : H ∣ MvPolynomial.C d * P) : H' ∣ P := by
    have hscaled : M * H' ∣ M * (D' * P) := by
      calc
        M * H' = H := hH'.symm
        _ ∣ MvPolynomial.C d * P := h
        _ = (M * D') * P := congrArg (· * P) hD'
        _ = _ := mul_assoc _ _ _
    exact (gcd_isUnit_iff_isRelPrime.mp hcoprime).dvd_of_dvd_mul_left
      ((mul_dvd_mul_iff_left hM).mp hscaled)
  have hH'Unit : IsUnit H' := hprimitive H'
    (cancel (scale beta dβ d₁ d₂ h'β))
    (cancel (by simpa only [d, mul_left_comm, mul_comm, mul_assoc] using scale first d₁ dβ d₂ h'₁))
    (cancel (by simpa only [d, mul_left_comm, mul_comm, mul_assoc] using scale second d₂ dβ d₁ h'₂))
  obtain ⟨c, _, hc⟩ := (dvd_C_iff_exists hd).mp (gcd_dvd_right H (MvPolynomial.C d))
  have hc₀ : c ≠ 0 := by
    intro hz
    apply hM
    exact hc.trans (by simp [hz])
  have hMUnit : IsUnit (fractionMap (F := F) M) := by
    rw [show M = MvPolynomial.C c from hc, fractionMap, MvPolynomial.map_C]
    apply IsUnit.map MvPolynomial.C
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hc₀
  have hHUnit : IsUnit (fractionMap (F := F) H) := by
    rw [hH', map_mul]
    exact hMUnit.mul (hH'Unit.map fractionMap)
  exact isUnit_of_mul_isUnit_left (hH.symm ▸ hHUnit)

omit [IsDomain R] in
theorem coeff_affine_zero (i : Fin 2) (c d : R) :
    (affine i c d).coeff 0 = c := by simp [affine, coeff_X]

omit [IsDomain R] in
theorem coeff_affine_one (i : Fin 2) (c d : R) :
    (affine i c d).coeff (Finsupp.single i 1) = d := by
  have hi : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro h
    simpa using congrArg (fun x : Fin 2 →₀ ℕ ↦ x i) h
  simp [affine, coeff_X, hi]

omit [IsDomain R] in
private theorem affine_of_fractionMap_eq_affine (i : Fin 2)
    {P : SeedPolynomial R} {a b : F} (h : fractionMap P = affine i a b) :
    P = affine i (P.coeff 0) (P.coeff (Finsupp.single i 1)) := by
  have h₀ := congrArg (fun Q : SeedPolynomial F ↦ Q.coeff 0) h
  have h₁ := congrArg (fun Q : SeedPolynomial F ↦ Q.coeff (Finsupp.single i 1)) h
  simp only [fractionMap, coeff_map, coeff_affine_zero] at h₀
  simp only [fractionMap, coeff_map, coeff_affine_one] at h₁
  apply fractionMap_injective (F := F)
  simpa only [fractionMap, affine, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, h₀, h₁]
    using h

private theorem affine_mul_C {i : Fin 2} (a b c : F) :
    affine i a b * MvPolynomial.C c = affine i (a * c) (b * c) := by
  simp only [affine, map_mul]
  ring

omit [IsDomain R] in
private theorem normalize_affine [GCDMonoid R] [IsBezout R]
    (i : Fin 2) (a b : R) (h : affine i a b ≠ 0) :
    ∃ (A : Fin 2 → R) (d : R), d ≠ 0 ∧ IsCoprime (A 0) (A 1) ∧
      affine i a b = MvPolynomial.C d * affine i (A 0) (A 1) := by
  obtain ⟨a', b', ha, hb, hcoprime⟩ := extract_gcd a b
  have hg : gcd a b ≠ 0 := by
    intro hz
    apply h
    have ha₀ : a = 0 := by rw [ha, hz, zero_mul]
    have hb₀ : b = 0 := by rw [hb, hz, zero_mul]
    simp [affine, ha₀, hb₀]
  refine ⟨![a', b'], gcd a b, hg, ?_, ?_⟩
  · simpa using (gcd_isUnit_iff_isRelPrime.mp hcoprime).isCoprime
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, affine, mul_add, ← mul_assoc, ← map_mul]
    rw [← ha, ← hb]

theorem integral_separation [GCDMonoid R] [IsBezout R] [GCDMonoid (SeedPolynomial R)]
    (a₀ a₁ b₀ b₁ : F) (beta first second : SeedPolynomial R) (left right : SeedPolynomial F)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0)
    (hnonzero : a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ b₀ ≠ 0 ∨ b₁ ≠ 0)
    (rel : affine 0 a₀ a₁ * fractionMap first + affine 1 b₀ b₁ * fractionMap second = 0)
    (hbeta : fractionMap beta = left * fractionMap first + right * fractionMap second)
    (hprimitive : ∀ D : SeedPolynomial R, D ∣ beta → D ∣ first → D ∣ second → IsUnit D) :
    ∃ (A B : Fin 2 → R) (d₀ d₁ : R), d₀ ≠ 0 ∧ d₁ ≠ 0 ∧
      IsCoprime (A 0) (A 1) ∧ IsCoprime (B 0) (B 1) ∧
      first = MvPolynomial.C d₀ * affine 1 (B 0) (B 1) ∧ second = -(MvPolynomial.C d₁ * affine 0 (A 0) (A 1)) := by
  have hfirst' : fractionMap (F := F) first ≠ 0 :=
    fun h ↦ hfirst (fractionMap_injective (F := F) (by simpa using h))
  have hsecond' : fractionMap (F := F) second ≠ 0 :=
    fun h ↦ hsecond (fractionMap_injective (F := F) (by simpa using h))
  obtain ⟨c, _, h₁, h₂⟩ := separate_of_primitive_relation a₀ a₁ b₀ b₁
    (fractionMap beta) (fractionMap first) (fractionMap second) left right
    hfirst' hsecond' hnonzero rel hbeta (primitive_fractionMap hprimitive)
  have h₁' := affine_of_fractionMap_eq_affine 1 (h₁.trans (affine_mul_C _ _ _))
  have h₂' := affine_of_fractionMap_eq_affine 0
    (show fractionMap (-second) = affine 0 (a₀ * c) (a₁ * c) by
      rw [map_neg, h₂, neg_neg, affine_mul_C])
  obtain ⟨B, d₀, hd₀, hB, he₀⟩ := normalize_affine 1 _ _ (h₁' ▸ hfirst)
  obtain ⟨A, d₁, hd₁, hA, he₁⟩ := normalize_affine 0 _ _
    (h₂' ▸ (neg_ne_zero.mpr hsecond))
  refine ⟨A, B, d₀, d₁, hd₀, hd₁, hA, hB, h₁'.trans he₀, ?_⟩
  simpa only [neg_neg] using congrArg Neg.neg (h₂'.trans he₁)

end Integral

end ProximityPrize.SubmissionLower.Koala6844SeparationFactors
end SeparationPart6


section SeparationPart7

namespace ProximityPrize.SubmissionLower.Koala6844Separation

open Koala6844SeparationFactors (affine)
open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def corner (i j : Fin 2) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.val + Finsupp.single 1 j.val

@[simp] private theorem corner_apply_zero (i j : Fin 2) : corner i j 0 = i.val := by
  simp [corner]

@[simp] private theorem corner_apply_one (i j : Fin 2) : corner i j 1 = j.val := by
  simp [corner]

private theorem corner_eq_corner {i j i' j' : Fin 2} :
    corner i j = corner i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨Fin.ext (by simpa using congrArg (· 0) h),
      Fin.ext (by simpa using congrArg (· 1) h)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

noncomputable def biform (β : Fin 2 → Fin 2 → R) : MvPolynomial (Fin 2) R :=
  ∑ i, ∑ j, MvPolynomial.monomial (corner i j) (β i j)

@[simp] theorem coeff_biform (β : Fin 2 → Fin 2 → R) (i j : Fin 2) :
    (biform β).coeff (corner i j) = β i j := by
  classical
  fin_cases i <;> fin_cases j <;> simp [biform, MvPolynomial.coeff_monomial, corner_eq_corner]

@[simp] theorem map_biform (φ : R →+* S) (β : Fin 2 → Fin 2 → R) :
    MvPolynomial.map φ (biform β) = biform (fun i j ↦ φ (β i j)) := by
  simp only [biform, map_sum, MvPolynomial.map_monomial]

theorem biform_add (β γ : Fin 2 → Fin 2 → R) :
    biform (fun i j ↦ β i j + γ i j) = biform β + biform γ := by
  simp only [biform, map_add, Finset.sum_add_distrib]

@[simp] theorem map_affine (φ : R →+* S) (i : Fin 2) (a b : R) :
    MvPolynomial.map φ (affine i a b) = affine i (φ a) (φ b) := by
  simp only [affine, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem affine_eq_sum (i : Fin 2) (A : Fin 2 → R) :
    affine i (A 0) (A 1) = ∑ j : Fin 2, MvPolynomial.monomial (Finsupp.single i j.val) (A j) := by
  rw [Fin.sum_univ_two]
  simp [affine, MvPolynomial.C_apply, MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
    -MvPolynomial.monomial_zero']

theorem biform_mul_affine (A B : Fin 2 → R) :
    biform (fun i j ↦ A i * B j) = affine 0 (A 0) (A 1) * affine 1 (B 0) (B 1) := by
  rw [affine_eq_sum 0 A, affine_eq_sum 1 B, Finset.sum_mul]
  simp only [biform, corner, Finset.mul_sum, MvPolynomial.monomial_mul_monomial]

private theorem biform_decomposition (A B C D : Fin 2 → R) :
    biform (fun i j ↦ C i * B j + A i * D j) =
      affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
        affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1) := by
  rw [biform_add, biform_mul_affine, biform_mul_affine]

theorem exists_biaffine_decomposition_with_degree {K : Type*} [Field K]
    (φ : K[X] →+* S) (hφ : Function.Injective φ) (A B : Fin 2 → K[X])
    (beta : MvPolynomial (Fin 2) K[X]) (hA : IsCoprime (A 0) (A 1))
    (hB : IsCoprime (B 0) (B 1)) (lim : ℕ) (hlim : pairDegree A + pairDegree B ≤ lim)
    (hβ : ∀ i j, (beta.coeff (corner i j)).natDegree ≤ lim)
    (h : ∃ C D : Fin 2 → S, MvPolynomial.map φ beta =
      affine 0 (C 0) (C 1) * affine 1 (φ (B 0)) (φ (B 1)) +
        affine 0 (φ (A 0)) (φ (A 1)) * affine 1 (D 0) (D 1)) :
    ∃ C D : Fin 2 → K[X], pairDegree B + pairDegree C ≤ lim ∧
      pairDegree A + pairDegree D ≤ lim ∧
      beta = affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
        affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1) := by
  obtain ⟨C, D, h⟩ := h
  have he := biform_decomposition (φ ∘ A) (φ ∘ B) C D
  simp only [Function.comp_apply] at he
  rw [← he] at h
  let β (i j : Fin 2) := beta.coeff (corner i j)
  have hcoeff (i j : Fin 2) : φ (β i j) = C i * φ (B j) + φ (A i) * D j := by
    have heq := congrArg (fun q : MvPolynomial (Fin 2) S ↦ q.coeff (corner i j)) h
    simpa only [MvPolynomial.coeff_map, coeff_biform, β, Function.comp_apply] using heq
  have hshape : beta = biform β := by
    apply MvPolynomial.map_injective φ hφ
    rw [h, map_biform]
    exact congrArg biform (funext fun i ↦ funext fun j ↦ (hcoeff i j).symm)
  have hw : wedge A B β = 0 := by
    apply hφ
    rw [map_zero]
    simpa only [wedge, map_mul, map_sub, Function.comp_apply] using
      wedge_eq_zero_of_decomposition (φ ∘ A) (φ ∘ B) C D (fun i j ↦ φ (β i j)) hcoeff
  obtain ⟨C', D', hC', hD', hCD⟩ :=
    exists_decomposition_with_degree A B β hA hB lim hlim hβ hw
  refine ⟨C', D', hC', hD', ?_⟩
  rw [← biform_decomposition A B C' D', hshape]
  exact congrArg biform (funext fun i ↦ funext fun j ↦ hCD i j)

theorem fixed_word_of_affine_identity (A B C D U V : Fin 2 → R) (d₀ d₁ : R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : (affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
          affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1)) +
        (MvPolynomial.C d₀ * affine 1 (B 0) (B 1)) * affine 0 (U 0) (U 1) +
        (-(MvPolynomial.C d₁ * affine 0 (A 0) (A 1))) * affine 1 (V 0) (V 1) = 0) :
    ∃ u : R, (∀ i, d₀ * U i + C i = u * A i) ∧
      ∀ j, d₁ * V j - D j = u * B j := by
  let C' (i : Fin 2) := d₀ * U i + C i
  let D' (j : Fin 2) := D j - d₁ * V j
  have h' : affine 0 (C' 0) (C' 1) * affine 1 (B 0) (B 1) +
      affine 0 (A 0) (A 1) * affine 1 (D' 0) (D' 1) = 0 := by
    dsimp only [C', D']
    simp only [affine, map_add, map_sub, map_mul] at h ⊢
    linear_combination h
  rw [← biform_decomposition A B C' D'] at h'
  apply fixed_word A B C D U V d₀ d₁ hA hB
  intro i j
  have hcoeff := congrArg (fun P : MvPolynomial (Fin 2) R ↦ P.coeff (corner i j)) h'
  simpa only [coeff_biform, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, C', D'] using hcoeff

theorem fixed_word_at_node {K : Type*} [Field K] (x : K)
    (A B C D : Fin 2 → K[X]) (d₀ d₁ : K[X]) (U V : Fin 2 → K)
    (beta first second : MvPolynomial (Fin 2) K[X])
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (hbeta : beta = affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
      affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1))
    (hfirst : first = MvPolynomial.C d₀ * affine 1 (B 0) (B 1))
    (hsecond : second = -(MvPolynomial.C d₁ * affine 0 (A 0) (A 1)))
    (hnode : MvPolynomial.map (Polynomial.evalRingHom x) beta +
      MvPolynomial.map (Polynomial.evalRingHom x) first * affine 0 (U 0) (U 1) +
      MvPolynomial.map (Polynomial.evalRingHom x) second * affine 1 (V 0) (V 1) = 0) :
    ∃ u : K, (∀ i, d₀.eval x * U i + (C i).eval x = u * (A i).eval x) ∧
      ∀ j, d₁.eval x * V j - (D j).eval x = u * (B j).eval x := by
  let e := Polynomial.evalRingHom x
  exact fixed_word_of_affine_identity (e ∘ A) (e ∘ B) (e ∘ C) (e ∘ D) U V (e d₀) (e d₁)
    (hA.map e) (hB.map e) (by
      simpa only [e, Function.comp_apply, hbeta, hfirst, hsecond, map_affine,
        map_add, map_mul, map_neg, MvPolynomial.map_C] using hnode)

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart7


section SeparationPart8

namespace ProximityPrize.SubmissionLower.Koala6844Separation

open Polynomial
open Koala6844Comparison (SymbolicRow)
open Koala6844SeparationFactors (affine coeff_affine_zero coeff_affine_one integral_separation)
open scoped BigOperators Matrix Polynomial

set_option maxHeartbeats 5000000

variable {K I : Type*} [Field K]

structure NormalForm (q : SymbolicRow (Seeds K)) (w δ : ℕ) where
  A : Fin 2 → K[X]
  B : Fin 2 → K[X]
  C : Fin 2 → K[X]
  D : Fin 2 → K[X]
  d₀ : K[X]
  d₁ : K[X]
  d₀_ne : d₀ ≠ 0
  d₁_ne : d₁ ≠ 0
  A_coprime : IsCoprime (A 0) (A 1)
  B_coprime : IsCoprime (B 0) (B 1)
  first_eq : regroup q.first = MvPolynomial.C d₀ * affine 1 (B 0) (B 1)
  second_eq : regroup q.second = -(MvPolynomial.C d₁ * affine 0 (A 0) (A 1))
  beta_eq : regroup q.beta = affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
    affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1)
  first_degree : d₀.natDegree + pairDegree B ≤ δ
  second_degree : d₁.natDegree + pairDegree A ≤ δ
  left_degree : pairDegree B + pairDegree C ≤ w + δ
  right_degree : pairDegree A + pairDegree D ≤ w + δ

private theorem degree_of_integral_factor (P : (Seeds K)[X]) (i : Fin 2)
    (A : Fin 2 → K[X]) (d : K[X]) (δ : ℕ) (hd : d ≠ 0)
    (hA : IsCoprime (A 0) (A 1)) (hP : P.natDegree ≤ δ)
    (he : regroup P = MvPolynomial.C d * affine i (A 0) (A 1)) :
    d.natDegree + pairDegree A ≤ δ := by
  have bound (j : Fin 2) : (d * A j).natDegree ≤ δ := by
    let key := Finsupp.single i j.val
    have hkey := coeff_regroup_eq P key δ hP
    have hdeg := Koala6844CoefficientSystem.coefficientPolynomial_degree P key δ
    rw [← hkey, he, MvPolynomial.coeff_C_mul] at hdeg
    fin_cases j
    · change (d * A 0).natDegree ≤ δ
      simpa only [key, Fin.val_zero, Finsupp.single_zero, coeff_affine_zero] using hdeg
    · change (d * A 1).natDegree ≤ δ
      simpa only [key, show (1 : Fin 2).val = 1 by decide, coeff_affine_one] using hdeg
  have hn : A 0 ≠ 0 ∨ A 1 ≠ 0 := by
    by_contra! hz
    obtain ⟨u, v, hu⟩ := hA
    simp [hz.1, hz.2] at hu
  unfold pairDegree
  rcases hn with hne | hne
  · have b₀ := bound (0 : Fin 2)
    rw [Polynomial.natDegree_mul hd hne] at b₀
    have b₁ : d.natDegree + (A 1).natDegree ≤ δ := by
      by_cases hz : A 1 = 0
      · simp only [hz, natDegree_zero, Nat.add_zero]
        omega
      · simpa only [natDegree_mul hd hz] using bound (1 : Fin 2)
    omega
  · have b₁ := bound (1 : Fin 2)
    rw [Polynomial.natDegree_mul hd hne] at b₁
    have b₀ : d.natDegree + (A 0).natDegree ≤ δ := by
      by_cases hz : A 0 = 0
      · simp only [hz, natDegree_zero, Nat.add_zero]
        omega
      · simpa only [natDegree_mul hd hz] using bound (0 : Fin 2)
    omega

theorem normalForm_of_singular (domain : I ↪ K) (nodes : Finset I)
    (q : SymbolicRow (Seeds K)) (word : I → Fin 4 → K) (w δ : ℕ)
    (hfirst0 : q.first ≠ 0) (hsecond0 : q.second ≠ 0)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ)
    (hbeta : q.beta.natDegree ≤ w + δ) (hsmall : δ ≤ w) (hcard : w + 4 * δ < nodes.card)
    (hgood : ∀ i ∈ nodes,
      q.atNode (MvPolynomial.C (domain i))
        (MvPolynomial.C (word i 0) + MvPolynomial.X 0 * MvPolynomial.C (word i 1))
        (MvPolynomial.C (word i 2) + MvPolynomial.X 1 * MvPolynomial.C (word i 3)) = 0)
    (hsingular : ∀ keys : Fin 4 → (Fin 2 →₀ ℕ), (Koala6844RankFour.matrix q keys δ).det = 0)
    (hprimitive : ∀ P, P ∣ q.beta → P ∣ q.first → P ∣ q.second → IsUnit P) :
    Nonempty (NormalForm q w δ) := by
  classical
  let _ : GCDMonoid (Seeds K[X]) := UniqueFactorizationMonoid.toGCDMonoid _
  obtain ⟨⟨v, hv, hrel⟩, hspan⟩ := rational_relation_and_span domain nodes q word w δ
    hfirst0 hsecond0 hfirst hsecond hbeta hcard hgood hsingular
  obtain ⟨hv', hrelation⟩ := exists_affine_relation v hv hrel
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hspan
  have hbetaF : asRational q.beta =
      affine 0 (u 0) (u 1) * asRational q.first + affine 1 (u 2) (u 3) * asRational q.second := by
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      seedColumns, Matrix.cons_val_zero, Matrix.cons_val_succ, MvPolynomial.smul_eq_C_mul] at hu
    change MvPolynomial.C (u 0) * asRational q.first +
      (MvPolynomial.C (u 1) * (MvPolynomial.X 0 * asRational q.first) +
        (MvPolynomial.C (u 2) * asRational q.second +
          MvPolynomial.C (u 3) * (MvPolynomial.X 1 * asRational q.second))) = asRational q.beta at hu
    unfold affine
    linear_combination -hu
  have hp := primitive_regroup q.beta q.first q.second hprimitive
  have hf0 : regroup q.first ≠ 0 :=
    fun h ↦ hfirst0 (regroup_injective (by simpa using h))
  have hf1 : regroup q.second ≠ 0 :=
    fun h ↦ hsecond0 (regroup_injective (by simpa using h))
  obtain ⟨A, B, d₀, d₁, hd₀, hd₁, hA, hB, h₀, h₁⟩ := integral_separation
    (v 0) (v 1) (v 2) (v 3) (regroup q.beta) (regroup q.first) (regroup q.second)
    (affine 0 (u 0) (u 1)) (affine 1 (u 2) (u 3)) hf0 hf1 hv' hrelation hbetaF hp
  have hdeg₀ := degree_of_integral_factor q.first 1 B d₀ δ hd₀ hB hfirst h₀
  have hdeg₁ := degree_of_integral_factor (-q.second) 0 A d₁ δ hd₁ hA
    (by simpa using hsecond) (by rw [map_neg, h₁, neg_neg])
  let φ := algebraMap K[X] (NodeField K)
  have hfirstF : asRational q.first = MvPolynomial.C (φ d₀) * affine 1 (φ (B 0)) (φ (B 1)) := by
    change MvPolynomial.map φ (regroup q.first) = _
    rw [h₀, map_mul, MvPolynomial.map_C, map_affine]
  have hsecondF : asRational q.second = -(MvPolynomial.C (φ d₁) * affine 0 (φ (A 0)) (φ (A 1))) := by
    change MvPolynomial.map φ (regroup q.second) = _
    rw [h₁, map_neg, map_mul, MvPolynomial.map_C, map_affine]
  have hlim : pairDegree A + pairDegree B ≤ w + δ := by omega
  have hcb (i j : Fin 2) : ((regroup q.beta).coeff (corner i j)).natDegree ≤ w + δ := by
    rw [coeff_regroup_eq _ _ _ hbeta]
    exact Koala6844CoefficientSystem.coefficientPolynomial_degree _ _ _
  obtain ⟨C', D', hC', hD', hβ⟩ := exists_biaffine_decomposition_with_degree φ
    (IsFractionRing.injective _ _) A B (regroup q.beta) hA hB (w + δ) hlim hcb (by
      refine ⟨![u 0 * φ d₀, u 1 * φ d₀], ![-(u 2 * φ d₁), -(u 3 * φ d₁)], ?_⟩
      change asRational q.beta = _
      rw [hbetaF, hfirstF, hsecondF]
      simp only [affine, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_neg]
      ring)
  exact ⟨⟨A, B, C', D', d₀, d₁, hd₀, hd₁, hA, hB, h₀, h₁, hβ, hdeg₀, hdeg₁, hC', hD'⟩⟩

theorem NormalForm.fixedWord {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (x : K) (U V : Fin 2 → K)
    (h : q.atNode (MvPolynomial.C x) (affine 0 (U 0) (U 1)) (affine 1 (V 0) (V 1)) = 0) :
    ∃ u : K, (∀ i, N.d₀.eval x * U i + (N.C i).eval x = u * (N.A i).eval x) ∧
      ∀ j, N.d₁.eval x * V j - (N.D j).eval x = u * (N.B j).eval x := by
  exact fixed_word_at_node x N.A N.B N.C N.D N.d₀ N.d₁ U V (regroup q.beta) (regroup q.first)
    (regroup q.second) N.A_coprime N.B_coprime N.beta_eq N.first_eq N.second_eq (by
      simpa only [map_eval_regroup, SymbolicRow.atNode] using h)

end ProximityPrize.SubmissionLower.Koala6844Separation
end SeparationPart8
