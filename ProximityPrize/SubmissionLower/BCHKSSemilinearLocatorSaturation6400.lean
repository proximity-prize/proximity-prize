import ProximityPrize.SubmissionLower.BCHKSSemilinearPolynomialDescent6400
import ProximityPrize.SubmissionLower.BCHKSLagrangeFixedMap6400

/-!
# Simple-root saturation for the score-64 semilinear operator

For `S(Q) = A*Q + B*sigma(Q)`, equal cyclic norms supply explicit
Hilbert--90 elements in the homogeneous kernel of `S`.  At a fixed field
node where both `A` and `B` are nonzero, one such element is nonzero.

Consequently a fixed simple nodal factor can be cancelled from an identity

`L * R = S(W)`.

Indeed, subtract a fixed-field scalar multiple of the homogeneous element so
that `W` vanishes at the node, divide by the corresponding linear factor,
and cancel it from both sides.  Induction cancels an arbitrary squarefree
nodal locator.  This is the saturation statement needed for the reduced
rank-one owner equation; it uses no ordinary Hensel or simple-root lifting
in the challenge variable.
-/

open scoped BigOperators

namespace ProximityPrize.SubmissionLower
namespace BCHKSSemilinearLocatorSaturation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSInhomogeneousCyclicCompatibility6400
open BCHKSHilbert90FiniteSeeds6400
open BCHKSScalarCyclicCompatibilityExact6400
open BCHKSSemilinearPolynomialDescent6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

@[simp]
theorem koalaFrobeniusConjugate_map_one6400
    (P : IRSProfile.Field[X]) (n : Nat) :
    (koalaFrobeniusConjugate n P).map
        koalaSexticFrobenius.toRingHom =
      koalaFrobeniusConjugate (n + 1) P := by
  rfl

@[simp]
theorem koalaFrobeniusConjugate_zero_apply6400
    (P : IRSProfile.Field[X]) :
    koalaFrobeniusConjugate 0 P = P := by
  rfl

@[simp]
theorem koalaScalarConjugate6400_zero_apply
    (t : IRSProfile.Field) :
    koalaScalarConjugate6400 (0 : Fin 6) t = t := by
  have h := koalaFrobeniusMonoidCharacter6400_eq_iterate
    (0 : Fin 6) t
  change koalaScalarConjugate6400 (0 : Fin 6) t =
    (koalaSexticFrobenius^[0]) t at h
  simpa only [Function.iterate_zero_apply] using h

@[simp]
theorem koalaFrobeniusAlgCharacter6400_zero_apply_local
    (t : IRSProfile.Field) :
    koalaFrobeniusAlgCharacter6400 (0 : Fin 6) t = t := by
  change koalaScalarConjugate6400 (0 : Fin 6) t = t
  exact koalaScalarConjugate6400_zero_apply t

/-- An explicit adjugate column for the homogeneous six-cycle operator.
The alternating signs account for the `+ B*sigma(Q)` convention. -/
noncomputable def koalaHomogeneousHilbert90Kernel6400
    (A B : IRSProfile.Field[X]) (t : IRSProfile.Field) :
    IRSProfile.Field[X] :=
  koalaFrobeniusConjugate 1 A *
      koalaFrobeniusConjugate 2 A *
      koalaFrobeniusConjugate 3 A *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 0 (Polynomial.C t) -
    koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 2 A *
      koalaFrobeniusConjugate 3 A *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 1 (Polynomial.C t) +
    koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 3 A *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 2 (Polynomial.C t) -
    koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 2 B *
      koalaFrobeniusConjugate 4 A *
      koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 3 (Polynomial.C t) +
    koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 2 B *
      koalaFrobeniusConjugate 3 B *
      koalaFrobeniusConjugate 5 A *
      koalaFrobeniusConjugate 4 (Polynomial.C t) -
    koalaFrobeniusConjugate 0 B *
      koalaFrobeniusConjugate 1 B *
      koalaFrobeniusConjugate 2 B *
      koalaFrobeniusConjugate 3 B *
      koalaFrobeniusConjugate 4 B *
      koalaFrobeniusConjugate 5 (Polynomial.C t)

/-- The adjugate column is a homogeneous solution up to the norm
difference. -/
theorem koalaHomogeneousHilbert90Kernel_semilinear6400
    (A B : IRSProfile.Field[X]) (t : IRSProfile.Field) :
    koalaPolynomialSemilinear6400 A B
        (koalaHomogeneousHilbert90Kernel6400 A B t) =
      (koalaCyclicNormSix A - koalaCyclicNormSix B) *
        Polynomial.C t := by
  simp only [koalaPolynomialSemilinear6400,
    koalaHomogeneousHilbert90Kernel6400,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    koalaFrobeniusConjugate_map_one6400]
  norm_num
  rw [koalaFrobeniusConjugate_six A,
    koalaFrobeniusConjugate_six (Polynomial.C t)]
  simp only [koalaCyclicNormSix,
    koalaFrobeniusConjugate_zero_apply6400]
  ring

theorem koalaHomogeneousHilbert90Kernel_semilinear_eq_zero6400
    (A B : IRSProfile.Field[X]) (t : IRSProfile.Field)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B) :
    koalaPolynomialSemilinear6400 A B
        (koalaHomogeneousHilbert90Kernel6400 A B t) = 0 := by
  rw [koalaHomogeneousHilbert90Kernel_semilinear6400, hnorm,
    sub_self, zero_mul]

/-- The six polynomial coefficients of the same homogeneous adjugate
column, packaged for the existing Frobenius-character linear map. -/
noncomputable def koalaHomogeneousHilbert90Coefficient6400
    (A B : IRSProfile.Field[X]) (i : Fin 6) : IRSProfile.Field[X] :=
  match i.1 with
  | 0 =>
      koalaFrobeniusConjugate 1 A * koalaFrobeniusConjugate 2 A *
        koalaFrobeniusConjugate 3 A * koalaFrobeniusConjugate 4 A *
        koalaFrobeniusConjugate 5 A
  | 1 =>
      -(koalaFrobeniusConjugate 0 B * koalaFrobeniusConjugate 2 A *
        koalaFrobeniusConjugate 3 A * koalaFrobeniusConjugate 4 A *
        koalaFrobeniusConjugate 5 A)
  | 2 =>
      koalaFrobeniusConjugate 0 B * koalaFrobeniusConjugate 1 B *
        koalaFrobeniusConjugate 3 A * koalaFrobeniusConjugate 4 A *
        koalaFrobeniusConjugate 5 A
  | 3 =>
      -(koalaFrobeniusConjugate 0 B * koalaFrobeniusConjugate 1 B *
        koalaFrobeniusConjugate 2 B * koalaFrobeniusConjugate 4 A *
        koalaFrobeniusConjugate 5 A)
  | 4 =>
      koalaFrobeniusConjugate 0 B * koalaFrobeniusConjugate 1 B *
        koalaFrobeniusConjugate 2 B * koalaFrobeniusConjugate 3 B *
        koalaFrobeniusConjugate 5 A
  | _ =>
      -(koalaFrobeniusConjugate 0 B * koalaFrobeniusConjugate 1 B *
        koalaFrobeniusConjugate 2 B * koalaFrobeniusConjugate 3 B *
        koalaFrobeniusConjugate 4 B)

noncomputable def koalaHomogeneousHilbert90EvalLinear6400
    (A B : IRSProfile.Field[X]) (x : IRSProfile.Field) :
    IRSProfile.Field →ₗ[KoalaBear.Field] IRSProfile.Field :=
  koalaFrobeniusCombinationLinear6400 fun i =>
    (koalaHomogeneousHilbert90Coefficient6400 A B i).eval x

theorem koalaHomogeneousHilbert90EvalLinear_apply6400
    (A B : IRSProfile.Field[X]) (x t : IRSProfile.Field) :
    koalaHomogeneousHilbert90EvalLinear6400 A B x t =
      (koalaHomogeneousHilbert90Kernel6400 A B t).eval x := by
  change (∑ i : Fin 6,
      (koalaHomogeneousHilbert90Coefficient6400 A B i).eval x *
        koalaFrobeniusAlgCharacter6400 i t) = _
  rw [Fin.sum_univ_six]
  norm_num [koalaHomogeneousHilbert90Coefficient6400,
    koalaHomogeneousHilbert90Kernel6400,
    koalaFrobeniusConjugate_C_scalar6400,
    koalaScalarConjugate6400]
  ring

theorem koalaSexticFrobenius_iterate_ne_zero6400
    (a : IRSProfile.Field) (ha : a ≠ 0) (n : Nat) :
    (koalaSexticFrobenius^[n]) a ≠ 0 := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (_root_.map_ne_zero (f := koalaSexticFrobenius)).mpr ih

theorem koalaHomogeneousHilbert90EvalLinear_ne_zero6400
    (A B : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hfixed : koalaSexticFrobenius x = x)
    (hAeval : A.eval x ≠ 0) :
    koalaHomogeneousHilbert90EvalLinear6400 A B x ≠ 0 := by
  have hconjugate (n : Nat) :
      (koalaFrobeniusConjugate n A).eval x ≠ 0 := by
    rw [koalaFrobeniusConjugate_eval_of_fixed A x hfixed n]
    exact koalaSexticFrobenius_iterate_ne_zero6400 (A.eval x) hAeval n
  have hcoefficient :
      (koalaHomogeneousHilbert90Coefficient6400 A B (0 : Fin 6)).eval x ≠ 0 := by
    norm_num [koalaHomogeneousHilbert90Coefficient6400]
    exact ⟨⟨⟨⟨hconjugate 1, hconjugate 2⟩,
      hconjugate 3⟩, hconjugate 4⟩, hconjugate 5⟩
  obtain ⟨t, ht⟩ :=
    exists_koalaFrobeniusCharacterCombination_ne_zero6400
      (fun i =>
        (koalaHomogeneousHilbert90Coefficient6400 A B i).eval x)
      ⟨0, hcoefficient⟩
  intro hzero
  have hvalue := LinearMap.congr_fun hzero t
  apply ht
  change (∑ i : Fin 6,
      (koalaHomogeneousHilbert90Coefficient6400 A B i).eval x *
        koalaFrobeniusAlgCharacter6400 i t) = 0 at hvalue
  have hcoerce (i : Fin 6) :
      koalaFrobeniusMonoidCharacter6400 i t =
        koalaFrobeniusAlgCharacter6400 i t := rfl
  simpa only [hcoerce] using hvalue

theorem exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero6400
    (A B : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hfixed : koalaSexticFrobenius x = x)
    (hAeval : A.eval x ≠ 0) :
    ∃ t : IRSProfile.Field,
      (koalaHomogeneousHilbert90Kernel6400 A B t).eval x ≠ 0 := by
  have hlinear := koalaHomogeneousHilbert90EvalLinear_ne_zero6400
    A B x hfixed hAeval
  by_contra hall
  push Not at hall
  apply hlinear
  apply LinearMap.ext
  intro t
  rw [LinearMap.zero_apply,
    koalaHomogeneousHilbert90EvalLinear_apply6400]
  exact hall t

theorem koalaPolynomialSemilinear6400_sub
    (A B Q₀ Q₁ : IRSProfile.Field[X]) :
    koalaPolynomialSemilinear6400 A B (Q₀ - Q₁) =
      koalaPolynomialSemilinear6400 A B Q₀ -
        koalaPolynomialSemilinear6400 A B Q₁ := by
  simp only [koalaPolynomialSemilinear6400, Polynomial.map_sub]
  ring

theorem koalaPolynomialSemilinear6400_mul_fixed
    (A B G Q : IRSProfile.Field[X])
    (hfixed : G.map koalaSexticFrobenius.toRingHom = G) :
    koalaPolynomialSemilinear6400 A B (G * Q) =
      G * koalaPolynomialSemilinear6400 A B Q := by
  simp only [koalaPolynomialSemilinear6400, Polynomial.map_mul, hfixed]
  ring

theorem koalaCyclicNormSix_eval_ne_zero_of_fixed6400
    (P : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hfixed : koalaSexticFrobenius x = x)
    (hPeval : P.eval x ≠ 0) :
    (koalaCyclicNormSix P).eval x ≠ 0 := by
  have hconjugate (n : Nat) :
      (koalaFrobeniusConjugate n P).eval x ≠ 0 := by
    rw [koalaFrobeniusConjugate_eval_of_fixed P x hfixed n]
    exact koalaSexticFrobenius_iterate_ne_zero6400 (P.eval x) hPeval n
  simp only [koalaCyclicNormSix, Polynomial.eval_mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (hconjugate 0) (hconjugate 1))
    (hconjugate 2)) (hconjugate 3)) (hconjugate 4))
    (hconjugate 5)

/-- At a fixed node, equal cyclic norms and absence of a simultaneous zero
upgrade to nonvanishing of both semilinear coefficients. -/
theorem eval_pair_ne_zero_of_norm_eq6400
    (A B : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hfixed : koalaSexticFrobenius x = x)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hnotBoth : ¬(A.eval x = 0 ∧ B.eval x = 0)) :
    A.eval x ≠ 0 ∧ B.eval x ≠ 0 := by
  constructor
  · intro hAzero
    have hBne : B.eval x ≠ 0 := fun hBzero => hnotBoth ⟨hAzero, hBzero⟩
    have hBnorm := koalaCyclicNormSix_eval_ne_zero_of_fixed6400
      B x hfixed hBne
    apply hBnorm
    rw [← hnorm]
    simp only [koalaCyclicNormSix, Polynomial.eval_mul]
    change A.eval x * _ * _ * _ * _ * _ = 0
    rw [hAzero, zero_mul, zero_mul, zero_mul, zero_mul, zero_mul]
  · intro hBzero
    have hAne : A.eval x ≠ 0 := fun hAzero => hnotBoth ⟨hAzero, hBzero⟩
    have hAnorm := koalaCyclicNormSix_eval_ne_zero_of_fixed6400
      A x hfixed hAne
    apply hAnorm
    rw [hnorm]
    simp only [koalaCyclicNormSix, Polynomial.eval_mul]
    change B.eval x * _ * _ * _ * _ * _ = 0
    rw [hBzero, zero_mul, zero_mul, zero_mul, zero_mul, zero_mul]

/-- A squarefree nodal locator annihilating a semilinear cokernel class can
be cancelled completely whenever both coefficients are nonzero at every
node.  The proof cancels one linear factor at a time. -/
theorem exists_semilinear_of_nodal_mul_eq_semilinear6400
    {I : Type} [DecidableEq I]
    (v : I → IRSProfile.Field)
    (hfixed : ∀ i, koalaSexticFrobenius (v i) = v i)
    (G : Finset I)
    (A B R W : IRSProfile.Field[X])
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hAeval : ∀ i ∈ G, A.eval (v i) ≠ 0)
    (hBeval : ∀ i ∈ G, B.eval (v i) ≠ 0)
    (hfactor :
      Lagrange.nodal G v * R =
        koalaPolynomialSemilinear6400 A B W) :
    ∃ Q : IRSProfile.Field[X],
      R = koalaPolynomialSemilinear6400 A B Q := by
  classical
  induction G using Finset.induction_on generalizing W with
  | empty =>
      refine ⟨W, ?_⟩
      simpa only [Lagrange.nodal_empty, one_mul] using hfactor
  | @insert i G hi ih =>
      let x := v i
      have hAi : A.eval x ≠ 0 := hAeval i (Finset.mem_insert_self i G)
      have hBi : B.eval x ≠ 0 := hBeval i (Finset.mem_insert_self i G)
      obtain ⟨t, ht⟩ :=
        exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero6400
          A B x (hfixed i) hAi
      let H := koalaHomogeneousHilbert90Kernel6400 A B t
      have hHsemi : koalaPolynomialSemilinear6400 A B H = 0 := by
        simpa only [H] using
          koalaHomogeneousHilbert90Kernel_semilinear_eq_zero6400
            A B t hnorm
      have hWscalar :
          A.eval x * W.eval x +
            B.eval x * koalaSexticFrobenius (W.eval x) = 0 := by
        have heval := congrArg (fun P : IRSProfile.Field[X] => P.eval x)
          hfactor
        rw [Polynomial.eval_mul,
          Lagrange.eval_nodal_at_node (Finset.mem_insert_self i G),
          zero_mul, koalaPolynomialSemilinear6400,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
          polynomial_map_eval_of_fixed_locator
            koalaSexticFrobenius W x (hfixed i)] at heval
        exact heval.symm
      have hHscalar :
          A.eval x * H.eval x +
            B.eval x * koalaSexticFrobenius (H.eval x) = 0 := by
        have heval := congrArg (fun P : IRSProfile.Field[X] => P.eval x)
          hHsemi
        rw [koalaPolynomialSemilinear6400,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
          polynomial_map_eval_of_fixed_locator
            koalaSexticFrobenius H x (hfixed i),
          Polynomial.eval_zero] at heval
        exact heval
      let c := W.eval x / H.eval x
      have hcFixed : koalaSexticFrobenius c = c := by
        have hcrossProduct :
            B.eval x *
                (koalaSexticFrobenius (W.eval x) * H.eval x -
                  W.eval x * koalaSexticFrobenius (H.eval x)) = 0 := by
          linear_combination hWscalar * H.eval x - hHscalar * W.eval x
        have hcross :
            koalaSexticFrobenius (W.eval x) * H.eval x =
              W.eval x * koalaSexticFrobenius (H.eval x) := by
          exact sub_eq_zero.mp
            ((mul_eq_zero.mp hcrossProduct).resolve_left hBi)
        dsimp only [c]
        rw [map_div₀]
        exact (div_eq_div_iff
          ((_root_.map_ne_zero (f := koalaSexticFrobenius)).mpr ht) ht).2
            hcross
      let U := Polynomial.C c * H
      have hCfixed :
          (Polynomial.C c).map koalaSexticFrobenius.toRingHom =
            Polynomial.C c := by
        rw [Polynomial.map_C]
        exact congrArg Polynomial.C hcFixed
      have hUsemi : koalaPolynomialSemilinear6400 A B U = 0 := by
        rw [show U = Polynomial.C c * H from rfl,
          koalaPolynomialSemilinear6400_mul_fixed A B
            (Polynomial.C c) H hCfixed,
          hHsemi, mul_zero]
      have hroot : (W - U).eval x = 0 := by
        simp only [U, c, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C]
        rw [div_mul_cancel₀ (W.eval x) ht, sub_self]
      obtain ⟨W₁, hW₁⟩ :=
        (Polynomial.dvd_iff_isRoot.mpr
          (Polynomial.IsRoot.def.mpr hroot))
      have hlinearFixed :
          (Polynomial.X - Polynomial.C x).map
              koalaSexticFrobenius.toRingHom =
            Polynomial.X - Polynomial.C x := by
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        change Polynomial.X - Polynomial.C (koalaSexticFrobenius x) =
          Polynomial.X - Polynomial.C x
        rw [show koalaSexticFrobenius x = x by
          simpa only [x] using hfixed i]
      have hreduced :
          Lagrange.nodal G v * R =
            koalaPolynomialSemilinear6400 A B W₁ := by
        apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero x)
        calc
          (Polynomial.X - Polynomial.C x) *
                (Lagrange.nodal G v * R) =
              Lagrange.nodal (insert i G) v * R := by
                dsimp only [x]
                rw [Lagrange.nodal_insert_eq_nodal hi]
                ring
          _ = koalaPolynomialSemilinear6400 A B W := hfactor
          _ = koalaPolynomialSemilinear6400 A B (W - U) := by
                rw [koalaPolynomialSemilinear6400_sub, hUsemi, sub_zero]
          _ = koalaPolynomialSemilinear6400 A B
                ((Polynomial.X - Polynomial.C x) * W₁) := by
                rw [← hW₁]
          _ = (Polynomial.X - Polynomial.C x) *
                koalaPolynomialSemilinear6400 A B W₁ :=
              koalaPolynomialSemilinear6400_mul_fixed A B
                (Polynomial.X - Polynomial.C x) W₁ hlinearFixed
      apply ih W₁
      · intro j hj
        exact hAeval j (Finset.mem_insert_of_mem hj)
      · intro j hj
        exact hBeval j (Finset.mem_insert_of_mem hj)
      · exact hreduced

/-- Coprimality supplies the nodewise nonvanishing hypotheses automatically.
Thus a coprime equal-norm semilinear cokernel has no squarefree nodal
torsion. -/
theorem exists_semilinear_of_isCoprime_nodal_mul_eq6400
    {I : Type} [DecidableEq I]
    (v : I → IRSProfile.Field)
    (hfixed : ∀ i, koalaSexticFrobenius (v i) = v i)
    (G : Finset I)
    (A B R W : IRSProfile.Field[X])
    (hcoprime : IsCoprime A B)
    (hnorm : koalaCyclicNormSix A = koalaCyclicNormSix B)
    (hfactor :
      Lagrange.nodal G v * R =
        koalaPolynomialSemilinear6400 A B W) :
    ∃ Q : IRSProfile.Field[X],
      R = koalaPolynomialSemilinear6400 A B Q := by
  apply exists_semilinear_of_nodal_mul_eq_semilinear6400
    v hfixed G A B R W hnorm
  · intro i hi
    exact (eval_pair_ne_zero_of_norm_eq6400 A B (v i) (hfixed i) hnorm
      (not_both_eval_eq_zero_of_isCoprime A B hcoprime (v i))).1
  · intro i hi
    exact (eval_pair_ne_zero_of_norm_eq6400 A B (v i) (hfixed i) hnorm
      (not_both_eval_eq_zero_of_isCoprime A B hcoprime (v i))).2
  · exact hfactor

end BCHKSSemilinearLocatorSaturation6400
end ProximityPrize.SubmissionLower
