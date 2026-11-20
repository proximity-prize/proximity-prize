import Mathlib.RingTheory.MvPolynomial.Basic
import ProximityPrize.SubmissionLower.Koala6844VirtualHighTriangular



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators
open Polynomial

noncomputable section

set_option maxHeartbeats 1800000

section RectangularBox

variable (K : Type*) [Field K]

abbrev SeedValue := MvPolynomial (Fin 3) K

private def exponentSet (cap : Fin 3 → ℕ) : Set (Fin 3 →₀ ℕ) :=
  {n | ∀ j, n j ≤ cap j}

private def exponentEquiv (cap : Fin 3 → ℕ) :
    exponentSet cap ≃ ((j : Fin 3) → Fin (cap j + 1)) where
  toFun d j := ⟨d.val j, Nat.lt_succ_of_le (d.property j)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun j => (f j).val),
    fun j => by simpa only [Finsupp.coe_equivFunOnFinite_symm] using
      Nat.le_of_lt_succ (f j).isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext j
    simp
  right_inv f := by
    funext j
    apply Fin.ext
    simp

noncomputable instance (cap : Fin 3 → ℕ) : Fintype (exponentSet cap) :=
  Fintype.ofEquiv _ (exponentEquiv cap).symm

private abbrev coeffEquiv := (MvPolynomial.basisMonomials (Fin 3) K).repr

def rectangleBox (cap : Fin 3 → ℕ) : Submodule K (SeedValue K) :=
  (Finsupp.supported K K (exponentSet cap)).comap (coeffEquiv K).toLinearMap

theorem mem_rectangleBox {cap : Fin 3 → ℕ} {F : SeedValue K} :
    F ∈ rectangleBox K cap ↔ ∀ j, F.degreeOf j ≤ cap j := by
  change coeffEquiv K F ∈ Finsupp.supported K K (exponentSet cap) ↔ _
  rw [Finsupp.mem_supported]
  change (↑F.support : Set (Fin 3 →₀ ℕ)) ⊆ exponentSet cap ↔ _
  constructor
  · intro hs j
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro n hn
    exact (hs hn) j
  · intro h n hn j
    exact MvPolynomial.degreeOf_le_iff.mp (h j) n hn

private def boxEquiv (cap : Fin 3 → ℕ) : rectangleBox K cap ≃ₗ[K]
    (exponentSet cap →₀ K) :=
  ((coeffEquiv K).ofSubmodule' _).trans
    (Finsupp.supportedEquivFinsupp (R := K) (M := K) (exponentSet cap))

instance (cap : Fin 3 → ℕ) : Module.Finite K (rectangleBox K cap) :=
  Module.Finite.equiv (boxEquiv K cap).symm

theorem finrank_rectangleBox (cap : Fin 3 → ℕ) :
    Module.finrank K (rectangleBox K cap) = ∏ j : Fin 3, (cap j + 1) := by
  rw [(boxEquiv K cap).finrank_eq,
    Module.finrank_finsupp_self, Fintype.card_congr (exponentEquiv cap), Fintype.card_pi]
  simp

end RectangularBox

section LocalVirtualGerm

variable {K : Type*} [Field K]
variable (L : ℕ)

abbrev RectangleJet (cap : Fin 3 → ℕ) := Fin L → rectangleBox K cap

def forgetJet (cap : Fin 3 → ℕ) : RectangleJet (K := K) L cap →ₗ[K] (Fin L → SeedValue K) :=
  LinearMap.pi fun i => (rectangleBox K cap).subtype.comp (LinearMap.proj i)

def rawJet : Polynomial (SeedValue K) →ₗ[K] (Fin L → SeedValue K) :=
  LinearMap.pi fun i => (Polynomial.lcoeff (SeedValue K) (i : ℕ)).restrictScalars K

def virtualIdeal (l m : ℕ) (q : Polynomial (SeedValue K)) : Ideal (Polynomial (SeedValue K)) :=
  Ideal.span ({X ^ l,q} : Set (Polynomial (SeedValue K))) ^ m

def virtualContactSpace (l m : ℕ) (q : Polynomial (SeedValue K)) (cap : Fin 3 → ℕ) :
    Submodule K (RectangleJet (K := K) L cap) :=
  ((virtualIdeal l m q).restrictScalars K |>.map (rawJet (K := K) L)).comap (forgetJet L cap)

private theorem degreeOf_coeff_mul_le (j : Fin 3)
    {P Q : Polynomial (SeedValue K)} {a b : ℕ}
    (hp : ∀ n, (P.coeff n).degreeOf j ≤ a) (hq : ∀ n, (Q.coeff n).degreeOf j ≤ b)
    (n : ℕ) : ((P * Q).coeff n).degreeOf j ≤ a + b := by
  rw [Polynomial.coeff_mul]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro ij _
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (hp _) (hq _))

private theorem degreeOf_coeff_pow_le (j : Fin 3) (P : Polynomial (SeedValue K))
    (a r : ℕ) (hp : ∀ n, (P.coeff n).degreeOf j ≤ a) :
    ∀ n, ((P ^ r).coeff n).degreeOf j ≤ r * a := by
  induction r with
  | zero =>
    intro n
    simp only [pow_zero, zero_mul, Polynomial.coeff_one]
    split <;> simp
  | succ r ih =>
    intro n
    rw [pow_succ, Nat.succ_mul]
    exact degreeOf_coeff_mul_le j ih hp n

private theorem degreeOf_layer_le {q : Polynomial (SeedValue K)} (cap widths : Fin 3 → ℕ)
    (i n r : ℕ) (f : rectangleBox K (fun j => cap j - r * widths j))
    (bounded : ∀ j, r * widths j ≤ cap j)
    (qBound : ∀ n j, (q.coeff n).degreeOf j ≤ widths j)
    (j : Fin 3) :
    (((X ^ i * q ^ r).coeff n) * f.val).degreeOf j ≤ cap j := by
  have hp : ((X ^ i * q^r).coeff n).degreeOf j ≤ r * widths j := by
    rw [Polynomial.coeff_X_pow_mul']
    split
    · exact degreeOf_coeff_pow_le j q (widths j) r (fun u => qBound u j) _
    · simp
  exact ((MvPolynomial.degreeOf_mul_le _ _ _).trans
    (Nat.add_le_add hp ((mem_rectangleBox K).mp f.property j))).trans_eq
    (Nat.add_sub_of_le (bounded j))

private theorem triangular_in_rectangle
    (cap widths : Fin 3 → ℕ) (q : Polynomial (SeedValue K)) (order : Fin L → ℕ)
    (bounded : ∀ i j, order i * widths j ≤ cap j)
    (qBound : ∀ n j, (q.coeff n).degreeOf j ≤ widths j)
    (f : (i : Fin L) → rectangleBox K (fun j => cap j - order i * widths j)) (i : Fin L) :
    triangularMultiplication (K := K) q order (fun i => (f i).val) i ∈ rectangleBox K cap := by
  apply (mem_rectangleBox K).mpr
  intro j
  let term (u : Fin L) : SeedValue K := (X ^ (u : ℕ) * q ^ order u).coeff i * (f u).val
  change (∑ u : Fin L, term u).degreeOf j ≤ cap j
  have degree := MvPolynomial.degreeOf_sum_le j (Finset.univ : Finset (Fin L)) term
  exact degree.trans (Finset.sup_le fun u _ =>
    degreeOf_layer_le cap widths u i (order u) (f u) (bounded u) qBound j)

theorem finrank_virtualContactSpace_ge
    (l m : ℕ) (cap widths : Fin 3 → ℕ) (q : Polynomial (SeedValue K))
    (q0 : q.coeff 0 ≠ 0) (order : Fin L → ℕ)
    (valid : ∀ i, order i ≤ m ∧ l * (m - order i) ≤ (i : ℕ))
    (bounded : ∀ i j, order i * widths j ≤ cap j)
    (qBound : ∀ n j, (q.coeff n).degreeOf j ≤ widths j) :
    (∑ i : Fin L, ∏ j : Fin 3, (cap j - order i * widths j + 1)) ≤
      Module.finrank K (virtualContactSpace (K := K) L l m q cap) := by
  let slice (i : Fin L) := rectangleBox K (fun j => cap j - order i * widths j)
  let forget : ((i : Fin L) → slice i) →ₗ[K] (Fin L → SeedValue K) :=
    LinearMap.pi fun i => (slice i).subtype.comp (LinearMap.proj i)
  let raw := (triangularMultiplication (K := K) q order).comp forget
  let intoBox : ((i : Fin L) → slice i) →ₗ[K] RectangleJet (K := K) L cap :=
    LinearMap.pi fun i => ((LinearMap.proj i).comp raw).codRestrict _
      (fun f => triangular_in_rectangle L cap widths q order bounded qBound f i)
  have contact (f : (i : Fin L) → slice i) :
      intoBox f ∈ virtualContactSpace (K := K) L l m q cap := by
    refine ⟨∑ i : Fin L, X ^ (i : ℕ) * q ^ order i * C ((f i).val),
      sum_mem_virtual_contact l m q order valid (fun i => (f i).val), ?_⟩
    funext i
    exact (triangularMultiplication_apply (K := K) q order (fun i => (f i).val) i).symm
  let mapped := intoBox.codRestrict _ contact
  have hinj : Function.Injective mapped := by
    intro f g same
    have equal : raw f = raw g := congrArg (fun t => forgetJet L cap t.val) same
    have forgotten := triangularMultiplication_injective (K := K) q q0 order equal
    funext i
    exact Subtype.ext (congrFun forgotten i)
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at h
  simpa only [slice, finrank_rectangleBox] using h

theorem quotient_rank_le
    (l m : ℕ) (cap widths : Fin 3 → ℕ) (q : Polynomial (SeedValue K))
    (q0 : q.coeff 0 ≠ 0) (order : Fin L → ℕ)
    (valid : ∀ i, order i ≤ m ∧ l * (m - order i) ≤ (i : ℕ))
    (bounded : ∀ i j, order i * widths j ≤ cap j)
    (qBound : ∀ n j, (q.coeff n).degreeOf j ≤ widths j) :
    Module.finrank K (RectangleJet (K := K) L cap ⧸
      virtualContactSpace (K := K) L l m q cap) ≤
      L * (∏ j : Fin 3, (cap j + 1)) -
        (∑ i : Fin L, ∏ j : Fin 3, (cap j - order i * widths j + 1)) := by
  have low := finrank_virtualContactSpace_ge L l m cap widths q q0 order valid bounded qBound
  have whole := (virtualContactSpace (K := K) L l m q cap).finrank_quotient_add_finrank
  have hbox : Module.finrank K (RectangleJet (K := K) L cap) =
      L * (∏ j : Fin 3, (cap j + 1)) := by
    rw [Module.finrank_pi_fintype]
    simp only [finrank_rectangleBox, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin, Nat.cast_id]
  rw [hbox] at whole
  omega

theorem mem_virtualIdeal_of_equal_rawJet (l m : ℕ) (q F G : Polynomial (SeedValue K))
    (hg : G ∈ virtualIdeal l m q)
    (same : rawJet (K := K) (l*m) F = rawJet (K := K) (l*m) G) :
    F ∈ virtualIdeal l m q := by
  let base := Ideal.span ({X ^ l,q} : Set (Polynomial (SeedValue K)))
  have hd : X ^ (l*m) ∣ F - G := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro n hn
    rw [Polynomial.coeff_sub]
    exact sub_eq_zero.mpr (congrFun same ⟨n,hn⟩)
  have gen : X ^ l ∈ base := Ideal.subset_span (by simp)
  have hp : X ^ (l*m) ∈ virtualIdeal l m q := by
    rw [pow_mul]
    exact Ideal.pow_mem_pow gen _
  obtain ⟨Q, hQ⟩ := hd
  have diff : F - G ∈ virtualIdeal l m q := by rw [hQ]; exact Ideal.mul_mem_right _ _ hp
  rw [← sub_add_cancel F G]
  exact Ideal.add_mem _ diff hg

end LocalVirtualGerm

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
