import ProximityPrize.SubmissionLower.Koala6844VirtualHighGlobalBox
import ProximityPrize.SubmissionLower.Koala6844VirtualHighRootContacts
import ProximityPrize.SubmissionLower.Koala6844VirtualHighGermDegrees
import Mathlib.Algebra.MvPolynomial.Equiv


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial
open scoped Classical

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

def sourceRectangle (y b c : ℕ) : Fin 3 → ℕ := ![y,b,c]

def sourceTaylor (a : K) : MvPolynomial (Fin 4) K →ₗ[K] GermCarrier K :=
  ((Polynomial.taylor (MvPolynomial.C a)).restrictScalars K).comp
    (MvPolynomial.finSuccEquiv K 3).toLinearMap

theorem sourceTaylor_apply (a : K) (F : MvPolynomial (Fin 4) K) :
    sourceTaylor a F = Polynomial.taylor (MvPolynomial.C a) (MvPolynomial.finSuccEquiv K 3 F) :=
  rfl

private theorem source_unshifted_coeff_degree_le (D w y b c : ℕ)
    (F : globalBox K D w y b c) (j : Fin 3) (n : ℕ) :
    ((MvPolynomial.finSuccEquiv K 3 F.val).coeff n).degreeOf j ≤ sourceRectangle y b c j := by
  apply (MvPolynomial.degreeOf_coeff_finSuccEquiv F.val j n).trans
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have h := (mem_globalBox K D w y b c F.val).mp F.property e he
  fin_cases j
  · change e 1 ≤ y
    exact h.2.1
  · change e 2 ≤ b
    exact h.2.2.1
  · change e 3 ≤ c
    exact h.2.2.2

theorem taylor_coeff_degree_le (a : K) (F : GermCarrier K) (j : Fin 3) (cap : ℕ)
    (h : ∀ n, (F.coeff n).degreeOf j ≤ cap) (n : ℕ) :
    ((Polynomial.taylor (MvPolynomial.C a) F).coeff n).degreeOf j ≤ cap := by
  classical
  have hsum :
      (Polynomial.taylor (MvPolynomial.C a) F).coeff n =
        ∑ k ∈ F.support, (Polynomial.taylor (MvPolynomial.C a)
          (Polynomial.monomial k (F.coeff k))).coeff n := by
    calc
      (Polynomial.taylor (MvPolynomial.C a) F).coeff n =
          (Polynomial.taylor (MvPolynomial.C a)
            (∑ k ∈ F.support, Polynomial.monomial k (F.coeff k))).coeff n := by
        exact congrArg (fun P : GermCarrier K => (Polynomial.taylor (MvPolynomial.C a) P).coeff n)
          (Polynomial.sum_monomial_eq F).symm
      _ = _ := by rw [map_sum, Polynomial.finsetSum_coeff]
  rw [hsum]
  exact (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => by
    rw [Polynomial.taylor_monomial, Polynomial.coeff_C_mul]
    have he : ((Polynomial.X : GermCarrier K) + Polynomial.C (MvPolynomial.C a)) ^ k =
        (((Polynomial.X : Polynomial K) + Polynomial.C a) ^ k).map MvPolynomial.C := by
      simp
    rw [he, Polynomial.coeff_map]
    exact (MvPolynomial.degreeOf_mul_C_le _ _ _).trans (h k))

theorem source_taylor_coeff_degree_le (D w y b c : ℕ)
    (F : globalBox K D w y b c) (a : K) (j : Fin 3) (n : ℕ) :
    ((sourceTaylor a F.val).coeff n).degreeOf j ≤ sourceRectangle y b c j := by
  rw [sourceTaylor_apply]
  exact taylor_coeff_degree_le a _ j _ (source_unshifted_coeff_degree_le D w y b c F j) n

def sourceJet (a : K) (D w y b c L : ℕ) :
    globalBox K D w y b c →ₗ[K] RectangleJet (K := K) L (sourceRectangle y b c) :=
  LinearMap.pi fun i =>
    ((LinearMap.proj i).comp ((rawJet (K := K) L).comp
      ((sourceTaylor a).comp (globalBox K D w y b c).subtype))).codRestrict _
      (fun F => (mem_rectangleBox K).mpr (fun j => source_taylor_coeff_degree_le D w y b c F a j i))

@[simp] theorem sourceJet_coeff (a : K) (D w y b c L : ℕ)
    (F : globalBox K D w y b c) (i : Fin L) :
    (sourceJet a D w y b c L F i).val = (sourceTaylor a F.val).coeff i := rfl

def sourceContact (a : K) (D w y b c l m : ℕ) (q : GermCarrier K) :
    globalBox K D w y b c →ₗ[K]
      (RectangleJet (K := K) (l*m) (sourceRectangle y b c) ⧸
        virtualContactSpace (K := K) (l*m) l m (Polynomial.taylor (MvPolynomial.C a) q)
          (sourceRectangle y b c)) :=
  (virtualContactSpace (K := K) (l*m) l m (Polynomial.taylor (MvPolynomial.C a) q)
    (sourceRectangle y b c)).mkQ.comp (sourceJet a D w y b c (l*m))

theorem mem_local_of_sourceContact_eq_zero
    (a : K) (D w y b c l m : ℕ) (q : GermCarrier K) (F : globalBox K D w y b c)
    (h : sourceContact a D w y b c l m q F = 0) :
    MvPolynomial.finSuccEquiv K 3 F.val ∈
      Ideal.span ({((Polynomial.X : GermCarrier K) - Polynomial.C (MvPolynomial.C a)) ^ l, q} :
        Set (GermCarrier K)) ^ m := by
  let qt := Polynomial.taylor (MvPolynomial.C a) q
  have hm : sourceJet a D w y b c (l*m) F ∈
      virtualContactSpace (K := K) (l*m) l m qt (sourceRectangle y b c) :=
    Submodule.Quotient.mk_eq_zero _ |>.mp h
  obtain ⟨G, hG, hs⟩ := hm
  have he : rawJet (K := K) (l*m) (sourceTaylor a F.val) = rawJet (K := K) (l*m) G := by
    funext i
    exact (congrFun hs i).symm
  have hh := mem_virtualIdeal_of_equal_rawJet l m qt (sourceTaylor a F.val) G hG he
  exact mem_germ_ideal_of_taylor_mem (MvPolynomial.C a) l m q _ hh

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
