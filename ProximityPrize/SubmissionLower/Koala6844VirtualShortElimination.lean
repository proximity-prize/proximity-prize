import ProximityPrize.SubmissionLower.Koala6844VirtualShortClear
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open MvPolynomial

noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K]

def asSeed (n : ℕ) :
    MvPolynomial (Fin (n+1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  (renameEquiv K (Equiv.swap (0 : Fin (n+1)) (Fin.last n))).trans
    (finSuccEquiv K n)

theorem asSeed_natDegree (n : ℕ) (P : MvPolynomial (Fin (n+1)) K) :
    (asSeed n P).natDegree = P.degreeOf (Fin.last n) := by
  change (finSuccEquiv K n (rename (Equiv.swap (0 : Fin (n+1)) (Fin.last n)) P)).natDegree = _
  rw [MvPolynomial.natDegree_finSuccEquiv]
  have h := MvPolynomial.degreeOf_rename_of_injective (p := P)
    (Equiv.swap (0 : Fin (n+1)) (Fin.last n)).injective (Fin.last n)
  rwa [Equiv.swap_apply_right] at h

theorem asSeed_constant (n : ℕ) (P : MvPolynomial (Fin (n+1)) K)
    (hP : ∀ e ∈ P.support, e (Fin.last n) = 0) :
    ∃ c : MvPolynomial (Fin n) K, asSeed n P = Polynomial.C c := by
  refine ⟨(asSeed n P).coeff 0, Polynomial.eq_C_of_natDegree_le_zero ?_⟩
  rw [asSeed_natDegree, MvPolynomial.degreeOf_eq_sup]
  exact Finset.sup_le (fun e he => Nat.le_of_eq (hP e he))

theorem clearAux_ne_zero_mv {n : ℕ} (A B : MvPolynomial (Fin (n+1)) K)
    (a₀ a₁ b₀ b₁ : MvPolynomial (Fin n) K) (q : ℕ)
    (hA : asSeed n A = Polynomial.C a₀ + Polynomial.C a₁ * Polynomial.X)
    (hB : asSeed n B = Polynomial.C b₀ + Polynomial.C b₁ * Polynomial.X)
    (ha : a₁ ≠ 0) (hc : a₁*b₀ ≠ a₀*b₁)
    (P : Polynomial (MvPolynomial (Fin (n+1)) K))
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ q)
    (hseed : ∀ j, 0 < j → ∀ e ∈ (P.coeff j).support, e (Fin.last n) = 0) :
    clearAux A B q P ≠ 0 := by
  let R := MvPolynomial (Fin n) K
  let φ := (asSeed (K := K) n).toRingHom
  have hφ : Function.Injective φ := (asSeed (K := K) n).injective
  have hP' : P.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hP
  have hconst (j : ℕ) (hj : 0 < j) : ∃ c : R, (P.map φ).coeff j = Polynomial.C c := by
    rw [Polynomial.coeff_map]
    exact asSeed_constant n (P.coeff j) (hseed j hj)
  have hn := clearAux_ne_zero_of_affine (algebraMap R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R)) a₀ a₁ b₀ b₁ ha hc
    (P.map φ) q hP' (Polynomial.natDegree_map_le.trans hdegree) hconst
  intro hz
  have hm := congrArg φ hz
  rw [clearAux_map, map_zero] at hm
  change clearAux (asSeed n A) (asSeed n B) q (P.map φ) = 0 at hm
  rw [hA, hB] at hm
  exact hn hm

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
