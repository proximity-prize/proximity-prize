import ProximityPrize.SubmissionLower.BCHKSUniversalNumerator

namespace ProximityPrize.SubmissionLower.UniversalNumerator

open Polynomial

noncomputable section

/-- Add the symbolic root as the zeroth coefficient to the positive-index
universal numerator recurrence.  The raw recurrence intentionally stores zero
at index zero; affine interpolation needs the actual constant Taylor term. -/
def rootedNumerators {A : Type*} [CommRing A]
    (root : A) (Rshift : A[X][X]) (s : A) (d : ℕ) (n : ℕ) : A :=
  if n = 0 then root else numerators Rshift s d n

@[simp] theorem rootedNumerators_zero {A : Type*} [CommRing A]
    (root : A) (Rshift : A[X][X]) (s : A) (d : ℕ) :
    rootedNumerators root Rshift s d 0 = root := by
  simp [rootedNumerators]

theorem rootedNumerators_of_pos {A : Type*} [CommRing A]
    (root : A) (Rshift : A[X][X]) (s : A) (d n : ℕ) (hn : 0 < n) :
    rootedNumerators root Rshift s d n = numerators Rshift s d n := by
  simp [rootedNumerators, Nat.ne_of_gt hn]

theorem rootedNumerators_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (root : A) (Rshift : A[X][X]) (s : A) (d n : ℕ) :
    f (rootedNumerators root Rshift s d n) =
      rootedNumerators (f root) (Rshift.map (Polynomial.mapRingHom f))
        (f s) d n := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [rootedNumerators, hn, if_false]
    exact numerators_map f Rshift s d n

/-- The rooted sequence specializes to the complete Taylor sequence,
including the constant term. -/
theorem rootedNumerators_eq_slope_pow_mul_root_coeff
    {L : Type*} [Field L]
    (root : L) (Rshift : L[X][X]) (V : L[X]) (s : L) (hs : s ≠ 0) (d : ℕ)
    (hV0 : V.coeff 0 = 0)
    (hdeg : Rshift.natDegree ≤ d)
    (hslope : ProximityPrize.SubmissionLower.FiniteHensel.ySlope
      Rshift 0 0 = s)
    (hExact : Rshift.eval V = 0) :
    ∀ n, rootedNumerators root Rshift s d n =
      s ^ FiniteHenselWeight.denominatorExponent n *
        (if n = 0 then root else V.coeff n) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [FiniteHenselWeight.denominatorExponent]
  · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [rootedNumerators_of_pos _ _ _ _ _ (Nat.pos_of_ne_zero hn)]
    simpa [FiniteHenselWeight.denominatorExponent, hn] using
      numerators_eq_slope_pow_mul_root_coeff Rshift V s hs d
        hV0 hdeg hslope hExact n hnpos

/-- Bounded form of the course-of-values representation.  Finite Hensel
lifting only supplies residual vanishing through its requested order. -/
theorem numerators_eq_slope_pow_mul_coeff_up_to
    {L : Type*} [Field L]
    (Rshift : L[X][X]) (s : L) (hs : s ≠ 0) (d N : ℕ)
    (c : ℕ → L) (hc0 : c 0 = 0)
    (hdeg : Rshift.natDegree ≤ d)
    (hslope : ProximityPrize.SubmissionLower.FiniteHensel.ySlope
      Rshift 0 0 = s)
    (hvanish : ∀ n, 1 ≤ n → n ≤ N →
      (ProximityPrize.SubmissionLower.FiniteHensel.residual
        Rshift 0 c n).coeff n = 0) :
    ∀ n, 1 ≤ n → n ≤ N →
      numerators Rshift s d n = s ^ (2 * n - 1) * c n := by
  intro n hn hnN
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [numerators_succ]
      apply numeratorStep_eq_slope_pow_mul_coeff
        Rshift s hs d (t + 1)
          (fun i => if i ≤ t then numerators Rshift s d i else 0)
          c (by omega) hc0 hdeg hslope (hvanish (t + 1) (by omega) hnN)
      intro i hi0 hit
      have hit' : i ≤ t := by omega
      rw [if_pos hit']
      exact ih i (by omega) hi0 (by omega)

/-- Outer-variable degree bound for the complete rooted sequence. -/
theorem rootedNumerators_natDegree_le
    {F : Type*} [Field F]
    (root : F[X]) (Rshift : F[X][X][X]) (s : F[X]) (d : ℕ)
    (hd : 0 < d)
    (hroot : root.natDegree ≤ 1)
    (hcoeff : ∀ n b a, b ≤ d → a ≤ n →
      ((Rshift.coeff b).coeff a).natDegree ≤ d)
    (hs : s.natDegree ≤ d - 1) :
    ∀ n, (rootedNumerators root Rshift s d n).natDegree ≤
      if n = 0 then 1 else FiniteHenselWeight.denominatorExponent n * d := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hroot
  · rw [rootedNumerators_of_pos _ _ _ _ _ (Nat.pos_of_ne_zero hn), if_neg hn]
    simpa [FiniteHenselWeight.denominatorExponent] using
      numerators_natDegree_le Rshift s d hd hcoeff hs n (Nat.pos_of_ne_zero hn)

/-- Coefficient-variable degree bound for the complete rooted sequence. -/
theorem rootedNumerators_degreeX_le
    {F : Type*} [Field F]
    (root : F[X][X]) (Rshift : F[X][X][X][X]) (s : F[X][X])
    (d D : ℕ)
    (hroot : Polynomial.Bivariate.degreeX root ≤ 0)
    (hcoeff : ∀ n b a, b ≤ d → a ≤ n →
      Polynomial.Bivariate.degreeX ((Rshift.coeff b).coeff a) ≤ D)
    (hs : Polynomial.Bivariate.degreeX s ≤ D) :
    ∀ n, Polynomial.Bivariate.degreeX
      (rootedNumerators root Rshift s d n) ≤
        if n = 0 then 0 else FiniteHenselWeight.denominatorExponent n * D := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hroot
  · rw [rootedNumerators_of_pos _ _ _ _ _ (Nat.pos_of_ne_zero hn), if_neg hn]
    simpa [FiniteHenselWeight.denominatorExponent] using
      numerators_degreeX_le Rshift s d D hcoeff hs n (Nat.pos_of_ne_zero hn)

end

end ProximityPrize.SubmissionLower.UniversalNumerator
