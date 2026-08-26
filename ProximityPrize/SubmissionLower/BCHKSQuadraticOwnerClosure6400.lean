import ProximityPrize.SubmissionLower.BCHKSQuadraticKernel6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSQuadraticOwnerClosure6400

open Polynomial
open BCHKSQuadraticBranchAlgebra6400
open BCHKSQuadraticKernel6400

set_option maxHeartbeats 2000000

/-!
Algebraic closure of the minimum-weight quadratic-owner case.

For a quadratic of `(X+kY)` weight at most `2k`, its leading coefficient is
constant in `X`, its linear coefficient has `X` degree at most `k`, and its
constant coefficient has `X` degree at most `2k`.  Consequently the
discriminant has `X` degree at most `2k`.  The theorem at the end combines
this observation with the integral parity-kernel construction: every
polynomial-root specialization is controlled either by two global signs or
by one nonzero resultant, apart from the two explicit specialization-drop
sets.
-/

/-- The `X`-degree bound for the discriminant of a minimum-weight
quadratic. -/
theorem quadraticDiscriminant_natDegree_le_two_mul
    {F : Type*} [Field F]
    (c a b : Polynomial (Polynomial F)) (k : ℕ)
    (hc : c.natDegree = 0)
    (ha : a.natDegree ≤ k)
    (hb : b.natDegree ≤ 2 * k) :
    (quadraticDiscriminant c a b).natDegree ≤ 2 * k := by
  have ha2 : (a ^ 2).natDegree ≤ 2 * k := by
    calc
      (a ^ 2).natDegree ≤ 2 * a.natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * k := Nat.mul_le_mul_left 2 ha
  have h4c : (4 * c).natDegree ≤ c.natDegree := by
    change (Polynomial.C (4 : Polynomial F) * c).natDegree ≤ c.natDegree
    exact Polynomial.natDegree_C_mul_le _ _
  have hcb : (4 * c * b).natDegree ≤ 2 * k := by
    calc
      (4 * c * b).natDegree ≤ (4 * c).natDegree + b.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ c.natDegree + b.natDegree := Nat.add_le_add_right h4c _
      _ ≤ 2 * k := by omega
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le ha2 hcb)

/-- Weight-sensitive form.  A quadratic of `(X+kY)` weight at most `w`
has discriminant `X` degree at most `2*(w-k)`. -/
theorem quadraticDiscriminant_natDegree_le_two_mul_weight_sub
    {F : Type*} [Field F]
    (c a b : Polynomial (Polynomial F)) (k w : ℕ)
    (hc : c.natDegree + 2 * k ≤ w)
    (ha : a.natDegree + k ≤ w)
    (hb : b.natDegree ≤ w) :
    (quadraticDiscriminant c a b).natDegree ≤ 2 * (w - k) := by
  have hkw : k ≤ w := by omega
  have ha2 : (a ^ 2).natDegree ≤ 2 * (w - k) := by
    calc
      (a ^ 2).natDegree ≤ 2 * a.natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * (w - k) := by omega
  have h4c : (4 * c).natDegree ≤ c.natDegree := by
    change (Polynomial.C (4 : Polynomial F) * c).natDegree ≤ c.natDegree
    exact Polynomial.natDegree_C_mul_le _ _
  have hcb : (4 * c * b).natDegree ≤ 2 * (w - k) := by
    calc
      (4 * c * b).natDegree ≤ (4 * c).natDegree + b.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ c.natDegree + b.natDegree := Nat.add_le_add_right h4c _
      _ ≤ 2 * (w - k) := by omega
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le ha2 hcb)

private theorem bivariate_degreeX_sub_le
    {F : Type*} [Field F]
    (P Q : Polynomial (Polynomial F)) :
    Polynomial.Bivariate.degreeX (P - Q) ≤
      max (Polynomial.Bivariate.degreeX P)
        (Polynomial.Bivariate.degreeX Q) := by
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  calc
    ((P - Q).coeff i).natDegree =
        (P.coeff i - Q.coeff i).natDegree := by rw [Polynomial.coeff_sub]
    _ ≤ max (P.coeff i).natDegree (Q.coeff i).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ max (P.support.sup fun j ↦ (P.coeff j).natDegree)
        (Q.support.sup fun j ↦ (Q.coeff j).natDegree) := by
      exact max_le_max
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX P i)
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX Q i)

private theorem bivariate_degreeX_pow_two_le
    {F : Type*} [Field F]
    (P : Polynomial (Polynomial F)) :
    Polynomial.Bivariate.degreeX (P ^ 2) ≤
      2 * Polynomial.Bivariate.degreeX P := by
  rw [pow_two]
  exact (Polynomial.Bivariate.degreeX_mul_le P P).trans (by omega)

private theorem bivariate_degreeX_four_mul_le
    {F : Type*} [Field F]
    (P : Polynomial (Polynomial F)) :
    Polynomial.Bivariate.degreeX (4 * P) ≤
      Polynomial.Bivariate.degreeX P := by
  change Polynomial.Bivariate.degreeX
      (Polynomial.C (4 : Polynomial F) * P) ≤
    Polynomial.Bivariate.degreeX P
  calc
    Polynomial.Bivariate.degreeX
        (Polynomial.C (4 : Polynomial F) * P) ≤
      Polynomial.Bivariate.degreeX (Polynomial.C (4 : Polynomial F)) +
        Polynomial.Bivariate.degreeX P :=
      Polynomial.Bivariate.degreeX_mul_le _ _
    _ = Polynomial.Bivariate.degreeX P := by
      unfold Polynomial.Bivariate.degreeX
      by_cases hfour : (4 : Polynomial F) = 0
      · simp [hfour]
      · rw [Polynomial.support_C hfour]
        simp

/-- The `Z`-degree bound inherited from a strict `Y+Z` cap. -/
theorem quadraticDiscriminant_degreeX_le_two_mul_sub_one
    {F : Type*} [Field F]
    (c a b : Polynomial (Polynomial F)) (d : ℕ)
    (hd : 1 ≤ d)
    (hc : Polynomial.Bivariate.degreeX c + 2 ≤ d)
    (ha : Polynomial.Bivariate.degreeX a + 1 ≤ d)
    (hb : Polynomial.Bivariate.degreeX b ≤ d) :
    Polynomial.Bivariate.degreeX (quadraticDiscriminant c a b) ≤
      2 * (d - 1) := by
  have ha2 : Polynomial.Bivariate.degreeX (a ^ 2) ≤ 2 * (d - 1) := by
    exact (bivariate_degreeX_pow_two_le a).trans (by omega)
  have h4cb : Polynomial.Bivariate.degreeX (4 * c * b) ≤
      2 * (d - 1) := by
    calc
      Polynomial.Bivariate.degreeX (4 * c * b) ≤
          Polynomial.Bivariate.degreeX (4 * c) +
            Polynomial.Bivariate.degreeX b :=
        Polynomial.Bivariate.degreeX_mul_le _ _
      _ ≤ Polynomial.Bivariate.degreeX c +
            Polynomial.Bivariate.degreeX b :=
        Nat.add_le_add_right (bivariate_degreeX_four_mul_le c) _
      _ ≤ 2 * (d - 1) := by omega
  exact (bivariate_degreeX_sub_le (a ^ 2) (4 * c * b)).trans
    (max_le ha2 h4cb)

/-- Exact algebraic dichotomy for a minimum-weight quadratic owner.

The first branch supplies one global square root of the discriminant and
records the two coherent signs both for challenge polynomial roots and for
the fixed identity-coordinate roots.  The second branch supplies the
primitive squarefree parity kernel and a single nonzero resultant.  Every
polynomial-root specialization then lies in exactly the advertised union:
the discriminant specializes to zero, the kernel loses positive `X` degree,
or the resultant vanishes.
-/
theorem minimumWeight_quadratic_owner_dichotomy
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    (p : ℕ) [CharP F p]
    (c a b : Polynomial (Polynomial F))
    (k d : ℕ)
    (I : Finset ι) (omega : ι → F) (U : ι → Polynomial F)
    (hDelta : quadraticDiscriminant c a b ≠ 0)
    (hcX : c.natDegree = 0)
    (haX : a.natDegree ≤ k)
    (hbX : b.natDegree ≤ 2 * k)
    (hd : 1 ≤ d)
    (hcZ : Polynomial.Bivariate.degreeX c + 2 ≤ d)
    (haZ : Polynomial.Bivariate.degreeX a + 1 ≤ d)
    (hbZ : Polynomial.Bivariate.degreeX b ≤ d)
    (hchar : 2 * k < p)
    (homega : Function.Injective omega)
    (hI : k + 1 ≤ I.card)
    (hidentity : ∀ i ∈ I,
      c.eval (Polynomial.C (omega i)) * (U i) ^ 2 +
          a.eval (Polynomial.C (omega i)) * U i +
          b.eval (Polynomial.C (omega i)) = 0) :
    (∃ H : Polynomial (Polynomial F),
      quadraticDiscriminant c a b = H ^ 2 ∧
      (∀ z P,
        c.map (Polynomial.evalRingHom z) * P ^ 2 +
              a.map (Polynomial.evalRingHom z) * P +
              b.map (Polynomial.evalRingHom z) = 0 →
          a.map (Polynomial.evalRingHom z) +
                2 * c.map (Polynomial.evalRingHom z) * P =
              H.map (Polynomial.evalRingHom z) ∨
          a.map (Polynomial.evalRingHom z) +
                2 * c.map (Polynomial.evalRingHom z) * P =
              -H.map (Polynomial.evalRingHom z)) ∧
      (∀ i ∈ I,
        a.eval (Polynomial.C (omega i)) +
              2 * c.eval (Polynomial.C (omega i)) * U i =
            H.eval (Polynomial.C (omega i)) ∨
        a.eval (Polynomial.C (omega i)) +
              2 * c.eval (Polynomial.C (omega i)) * U i =
            -H.eval (Polynomial.C (omega i)))) ∨
    (∃ B : Polynomial (Polynomial F), ∃ s : Polynomial F,
      ∃ S : Polynomial (Polynomial F),
        Squarefree s ∧ Squarefree S ∧ S.IsPrimitive ∧
        quadraticDiscriminant c a b =
          B ^ 2 * (Polynomial.C s * S) ∧
        0 < S.natDegree ∧ S.natDegree ≤ 2 * k ∧
        Polynomial.Bivariate.degreeX S ≤ 2 * d ∧
        s.natDegree ≤ 2 * d ∧
        parityKernelResultant S ≠ 0 ∧
        (parityKernelResultant S).natDegree ≤
          S.natDegree * (2 * d) + (S.natDegree - 1) * (2 * d) ∧
        ∀ z P,
          c.map (Polynomial.evalRingHom z) * P ^ 2 +
                a.map (Polynomial.evalRingHom z) * P +
                b.map (Polynomial.evalRingHom z) = 0 →
            (quadraticDiscriminant c a b).map
                (Polynomial.evalRingHom z) = 0 ∨
            (S.map (Polynomial.evalRingHom z)).natDegree = 0 ∨
            Polynomial.eval z (parityKernelResultant S) = 0) := by
  let Delta : Polynomial (Polynomial F) := quadraticDiscriminant c a b
  have hDeltaX : Delta.natDegree ≤ 2 * k := by
    exact quadraticDiscriminant_natDegree_le_two_mul c a b k hcX haX hbX
  have hDeltaZ : Polynomial.Bivariate.degreeX Delta ≤ 2 * d := by
    have hsharp := quadraticDiscriminant_degreeX_le_two_mul_sub_one
      c a b d hd hcZ haZ hbZ
    exact hsharp.trans (Nat.mul_le_mul_left 2 (Nat.sub_le d 1))
  obtain ⟨B, s, S, hs, hS, hprim, hdecomp, hSdeg, hSZ, hsdeg,
      hkernel, hresdeg⟩ :=
    exists_parity_kernel_resultant_dichotomy
      p Delta k d hDelta hDeltaX hDeltaZ hchar
  by_cases hSzero : S.natDegree = 0
  · left
    let D : ι → Polynomial F := fun i ↦
      a.eval (Polynomial.C (omega i)) +
        2 * c.eval (Polynomial.C (omega i)) * U i
    have hidSquare : ∀ i ∈ I,
        Delta.eval (Polynomial.C (omega i)) = (D i) ^ 2 := by
      intro i hi
      dsimp [Delta, D]
      simpa [quadraticDiscriminant, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow] using
        (quadraticDiscriminant_eq_square_of_root
          (c.eval (Polynomial.C (omega i)))
          (a.eval (Polynomial.C (omega i)))
          (b.eval (Polynomial.C (omega i))) (U i) (hidentity i hi))
    obtain ⟨H, hH⟩ :=
      global_square_of_constant_parity_kernel_on_identities
        Delta B S s I omega D k hDelta hdecomp hSzero hDeltaX
          homega hI hidSquare
    refine ⟨H, hH, ?_, ?_⟩
    · intro z P hroot
      exact specialized_quadratic_root_has_global_sign c a b H z P hH hroot
    · intro i hi
      apply quadratic_root_has_global_sign
        (c.eval (Polynomial.C (omega i)))
        (a.eval (Polynomial.C (omega i)))
        (b.eval (Polynomial.C (omega i))) (U i)
        (H.eval (Polynomial.C (omega i))) (hidentity i hi)
      have hmapped := congrArg
        (Polynomial.evalRingHom (Polynomial.C (omega i))) hH
      dsimp [Delta] at hmapped
      simpa [quadraticDiscriminant, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow] using hmapped
  · right
    have hres : parityKernelResultant S ≠ 0 :=
      hkernel.resolve_left hSzero
    have hSpos : 0 < S.natDegree := Nat.pos_of_ne_zero hSzero
    refine ⟨B, s, S, hs, hS, hprim, hdecomp, hSpos, hSdeg, hSZ,
      hsdeg, hres, hresdeg, ?_⟩
    intro z P hroot
    let W : Polynomial F :=
      a.map (Polynomial.evalRingHom z) +
        2 * c.map (Polynomial.evalRingHom z) * P
    have hSquare : Delta.map (Polynomial.evalRingHom z) = W ^ 2 := by
      dsimp [Delta, W]
      simpa [quadraticDiscriminant] using
        (quadraticDiscriminant_eq_square_of_root
          (c.map (Polynomial.evalRingHom z))
          (a.map (Polynomial.evalRingHom z))
          (b.map (Polynomial.evalRingHom z)) P hroot)
    by_cases hDeltaZ0 : Delta.map (Polynomial.evalRingHom z) = 0
    · exact Or.inl hDeltaZ0
    by_cases hSdrop : (S.map (Polynomial.evalRingHom z)).natDegree = 0
    · exact Or.inr (Or.inl hSdrop)
    · exact Or.inr (Or.inr
        (parity_kernel_square_specialization_is_resultant_root
          Delta B s S z W hdecomp hSquare hDeltaZ0
            (Nat.pos_of_ne_zero hSdrop)))

/-- Weight-sensitive quadratic-owner dichotomy.  Unlike the preceding
minimum-weight wrapper, this theorem does not ask for more identity
coordinates than the square factor's `X` degree.

In the constant-kernel case, either the square factor is nonzero at one
identity coordinate, which globalizes the discriminant square, or it
vanishes at every identity coordinate.  In the latter case every identity
slice has zero discriminant and hence a unique received root whenever its
quadratic leading coefficient does not vanish. -/
theorem boundedX_quadratic_owner_dichotomy
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    (p : ℕ) [CharP F p]
    (c a b : Polynomial (Polynomial F))
    (xMargin d : ℕ)
    (I : Finset ι) (omega : ι → F) (U : ι → Polynomial F)
    (hDelta : quadraticDiscriminant c a b ≠ 0)
    (hDeltaX : (quadraticDiscriminant c a b).natDegree ≤ 2 * xMargin)
    (hd : 1 ≤ d)
    (hcZ : Polynomial.Bivariate.degreeX c + 2 ≤ d)
    (haZ : Polynomial.Bivariate.degreeX a + 1 ≤ d)
    (hbZ : Polynomial.Bivariate.degreeX b ≤ d)
    (hchar : 2 * xMargin < p)
    (htwo : (2 : F) ≠ 0)
    (hidentity : ∀ i ∈ I,
      c.eval (Polynomial.C (omega i)) * (U i) ^ 2 +
          a.eval (Polynomial.C (omega i)) * U i +
          b.eval (Polynomial.C (omega i)) = 0) :
    (∃ H : Polynomial (Polynomial F),
      quadraticDiscriminant c a b = H ^ 2 ∧
      ∀ z P,
        c.map (Polynomial.evalRingHom z) * P ^ 2 +
              a.map (Polynomial.evalRingHom z) * P +
              b.map (Polynomial.evalRingHom z) = 0 →
          a.map (Polynomial.evalRingHom z) +
                2 * c.map (Polynomial.evalRingHom z) * P =
              H.map (Polynomial.evalRingHom z) ∨
          a.map (Polynomial.evalRingHom z) +
                2 * c.map (Polynomial.evalRingHom z) * P =
              -H.map (Polynomial.evalRingHom z)) ∨
    ((∀ i ∈ I,
        (quadraticDiscriminant c a b).eval
          (Polynomial.C (omega i)) = 0) ∧
      ∀ i ∈ I, ∀ z v,
        Polynomial.eval z (c.eval (Polynomial.C (omega i))) * v ^ 2 +
              Polynomial.eval z (a.eval (Polynomial.C (omega i))) * v +
              Polynomial.eval z (b.eval (Polynomial.C (omega i))) = 0 →
        Polynomial.eval z (c.eval (Polynomial.C (omega i))) ≠ 0 →
        v = Polynomial.eval z (U i)) ∨
    (∃ B : Polynomial (Polynomial F), ∃ s : Polynomial F,
      ∃ S : Polynomial (Polynomial F),
        Squarefree s ∧ Squarefree S ∧ S.IsPrimitive ∧
        quadraticDiscriminant c a b =
          B ^ 2 * (Polynomial.C s * S) ∧
        0 < S.natDegree ∧ S.natDegree ≤ 2 * xMargin ∧
        Polynomial.Bivariate.degreeX S ≤ 2 * d ∧
        s.natDegree ≤ 2 * d ∧
        parityKernelResultant S ≠ 0 ∧
        (parityKernelResultant S).natDegree ≤
          S.natDegree * (2 * d) + (S.natDegree - 1) * (2 * d) ∧
        ∀ z P,
          c.map (Polynomial.evalRingHom z) * P ^ 2 +
                a.map (Polynomial.evalRingHom z) * P +
                b.map (Polynomial.evalRingHom z) = 0 →
            (quadraticDiscriminant c a b).map
                (Polynomial.evalRingHom z) = 0 ∨
            (S.map (Polynomial.evalRingHom z)).natDegree = 0 ∨
            Polynomial.eval z (parityKernelResultant S) = 0) := by
  let Delta : Polynomial (Polynomial F) := quadraticDiscriminant c a b
  have hDeltaZ : Polynomial.Bivariate.degreeX Delta ≤ 2 * d := by
    have hsharp := quadraticDiscriminant_degreeX_le_two_mul_sub_one
      c a b d hd hcZ haZ hbZ
    exact hsharp.trans (Nat.mul_le_mul_left 2 (Nat.sub_le d 1))
  obtain ⟨B, s, S, hs, hS, hprim, hdecomp, hSdeg, hSZ, hsdeg,
      hkernel, hresdeg⟩ :=
    exists_parity_kernel_resultant_dichotomy
      p Delta xMargin d hDelta hDeltaX hDeltaZ hchar
  by_cases hSzero : S.natDegree = 0
  · let D : ι → Polynomial F := fun i ↦
      a.eval (Polynomial.C (omega i)) +
        2 * c.eval (Polynomial.C (omega i)) * U i
    have hidSquare : ∀ i ∈ I,
        Delta.eval (Polynomial.C (omega i)) = (D i) ^ 2 := by
      intro i hi
      dsimp [Delta, D]
      simpa [quadraticDiscriminant, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow] using
        (quadraticDiscriminant_eq_square_of_root
          (c.eval (Polynomial.C (omega i)))
          (a.eval (Polynomial.C (omega i)))
          (b.eval (Polynomial.C (omega i))) (U i) (hidentity i hi))
    by_cases hBsome : ∃ i ∈ I, B.eval (Polynomial.C (omega i)) ≠ 0
    · left
      obtain ⟨i, hi, hBi⟩ := hBsome
      obtain ⟨H, hH⟩ := global_square_of_constant_parity_kernel
        Delta B S s (Polynomial.C (omega i)) (D i)
          hdecomp hSzero hBi (hidSquare i hi)
      refine ⟨H, hH, ?_⟩
      intro z P hroot
      exact specialized_quadratic_root_has_global_sign c a b H z P hH hroot
    · right
      left
      have hBzero : ∀ i ∈ I,
          B.eval (Polynomial.C (omega i)) = 0 := by
        intro i hi
        by_contra hne
        exact hBsome ⟨i, hi, hne⟩
      have hDeltaIdentity : ∀ i ∈ I,
          Delta.eval (Polynomial.C (omega i)) = 0 := by
        intro i hi
        rw [hdecomp, Polynomial.eval_mul, Polynomial.eval_pow, hBzero i hi,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
      refine ⟨?_, ?_⟩
      · simpa [Delta] using hDeltaIdentity
      · intro i hi z v hv hcz
        let ci : F := Polynomial.eval z (c.eval (Polynomial.C (omega i)))
        let ai : F := Polynomial.eval z (a.eval (Polynomial.C (omega i)))
        let bi : F := Polynomial.eval z (b.eval (Polynomial.C (omega i)))
        let ui : F := Polynomial.eval z (U i)
        have hu : ci * ui ^ 2 + ai * ui + bi = 0 := by
          have hmapped := congrArg (Polynomial.evalRingHom z) (hidentity i hi)
          simpa [ci, ai, bi, ui, map_add, map_mul, map_pow] using hmapped
        have hdisc : quadraticDiscriminant ci ai bi = 0 := by
          have hmapped := congrArg (Polynomial.evalRingHom z)
            (hDeltaIdentity i hi)
          simpa [Delta, ci, ai, bi, quadraticDiscriminant,
            Polynomial.eval_sub, Polynomial.eval_mul,
            Polynomial.eval_pow] using hmapped
        have hvsign : ai + 2 * ci * v = 0 := by
          apply (sq_eq_zero_iff.mp ?_)
          rw [← quadraticDiscriminant_eq_square_of_root ci ai bi v hv]
          exact hdisc
        have husign : ai + 2 * ci * ui = 0 := by
          apply (sq_eq_zero_iff.mp ?_)
          rw [← quadraticDiscriminant_eq_square_of_root ci ai bi ui hu]
          exact hdisc
        exact eq_of_quadratic_roots_same_sign_of_nondegenerate
          ci ai bi v ui 0 htwo hv hu hvsign husign (Or.inr hcz)
  · right
    right
    have hres : parityKernelResultant S ≠ 0 :=
      hkernel.resolve_left hSzero
    have hSpos : 0 < S.natDegree := Nat.pos_of_ne_zero hSzero
    refine ⟨B, s, S, hs, hS, hprim, hdecomp, hSpos, hSdeg, hSZ,
      hsdeg, hres, hresdeg, ?_⟩
    intro z P hroot
    let W : Polynomial F :=
      a.map (Polynomial.evalRingHom z) +
        2 * c.map (Polynomial.evalRingHom z) * P
    have hSquare : Delta.map (Polynomial.evalRingHom z) = W ^ 2 := by
      dsimp [Delta, W]
      simpa [quadraticDiscriminant] using
        (quadraticDiscriminant_eq_square_of_root
          (c.map (Polynomial.evalRingHom z))
          (a.map (Polynomial.evalRingHom z))
          (b.map (Polynomial.evalRingHom z)) P hroot)
    by_cases hDeltaZ0 : Delta.map (Polynomial.evalRingHom z) = 0
    · exact Or.inl hDeltaZ0
    by_cases hSdrop : (S.map (Polynomial.evalRingHom z)).natDegree = 0
    · exact Or.inr (Or.inl hSdrop)
    · exact Or.inr (Or.inr
        (parity_kernel_square_specialization_is_resultant_root
          Delta B s S z W hdecomp hSquare hDeltaZ0
            (Nat.pos_of_ne_zero hSdrop)))

/-- Per-factor form of the weight-sensitive parity-resultant ledger. -/
theorem parityKernelResultant_degree_bound_of_margin
    (r d xMargin : ℕ) (hr : r ≤ 2 * xMargin) :
    r * (2 * d) + (r - 1) * (2 * d) ≤
      (4 * xMargin - 1) * (2 * d) := by
  have hrpred : r - 1 ≤ 2 * xMargin - 1 := Nat.sub_le_sub_right hr 1
  calc
    r * (2 * d) + (r - 1) * (2 * d) ≤
        (2 * xMargin) * (2 * d) +
          (2 * xMargin - 1) * (2 * d) := by gcongr
    _ = ((2 * xMargin) + (2 * xMargin - 1)) * (2 * d) := by
      rw [Nat.add_mul]
    _ = (4 * xMargin - 1) * (2 * d) := by
      congr 1
      omega

/-- Aggregation over all residual quadratic owners.  Only the additive
distinct-factor `Z` mass appears. -/
theorem parityKernelResultant_sum_bound_of_margin
    {γ : Type*} (T : Finset γ) (d obstruction : γ → ℕ)
    (xMargin totalZ : ℕ)
    (hmass : (∑ q ∈ T, d q) ≤ totalZ)
    (hobs : ∀ q ∈ T,
      obstruction q ≤ (4 * xMargin - 1) * (2 * d q)) :
    (∑ q ∈ T, obstruction q) ≤
      (4 * xMargin - 1) * 2 * totalZ := by
  calc
    (∑ q ∈ T, obstruction q) ≤
        ∑ q ∈ T, (4 * xMargin - 1) * (2 * d q) :=
      Finset.sum_le_sum hobs
    _ = ((4 * xMargin - 1) * 2) * (∑ q ∈ T, d q) := by
      simp_rw [mul_assoc, Finset.mul_sum]
    _ ≤ ((4 * xMargin - 1) * 2) * totalZ :=
      Nat.mul_le_mul_left _ hmass
    _ = (4 * xMargin - 1) * 2 * totalZ := by ring

end BCHKSQuadraticOwnerClosure6400
end ProximityPrize.SubmissionLower
