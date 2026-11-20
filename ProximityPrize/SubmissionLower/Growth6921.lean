import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Front6921
set_option Elab.async false

/- Profile transport of Dadon's PR 627. -/
section Port_K1_6_2Aux1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace K21_6_2

open Polynomial Matrix Finset
open FrobeniusLocator
open scoped BigOperators

private def unitColumns {R row col : Type*} [Zero R] [One R] [DecidableEq row]
    (rows : col → row) : Matrix row col R :=
  fun i j => (Pi.single (rows j) 1 : row → R) i

private theorem transpose_mul_unitColumns {R row col pick : Type*}
    [CommRing R] [Fintype row] [DecidableEq row]
    (W : Matrix row col R) (rows : pick → row) :
    W.transpose * unitColumns rows = (W.submatrix rows id).transpose := by
  ext i j
  change W.transpose.mulVec (Pi.single (rows j) 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl

variable {E : Type*} [Field E] {r s : ℕ}

/-- With a nonzero kernel minor, adjoining the corresponding coordinate
columns gives a square matrix with trivial kernel. -/
private theorem augmentation_det_ne_zero
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hWC : W.transpose * C = 0)
    (hC : ∀ a, C.mulVec a = 0 → a = 0)
    (rows : Fin s → (Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns rows)).det ≠ 0 := by
  let A := Matrix.fromCols C (unitColumns rows)
  have hker : ∀ v, A.mulVec v = 0 → v = 0 := by
    intro v hv
    have hz := congrArg W.transpose.mulVec hv
    change W.transpose.mulVec ((Matrix.fromCols C (unitColumns rows)).mulVec v) =
      W.transpose.mulVec 0 at hz
    rw [Matrix.mulVec_zero, Matrix.fromCols_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hWC, Matrix.zero_mulVec,
      zero_add, transpose_mul_unitColumns] at hz
    have hs : v ∘ Sum.inr = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero (by simpa only [Matrix.det_transpose] using hminor) hz
    change (Matrix.fromCols C (unitColumns rows)).mulVec v = 0 at hv
    rw [Matrix.fromCols_mulVec, hs, Matrix.mulVec_zero, add_zero] at hv
    have hr := hC _ hv
    funext i
    cases i with
    | inl i => exact congrFun hr i
    | inr i => exact congrFun hs i
  have hinj : Function.Injective A.mulVec := by
    intro u v huv
    exact sub_eq_zero.mp (hker (u - v) (by rw [Matrix.mulVec_sub, huv, sub_self]))
  exact ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

/-- Unit-column augmentations encode signed complementary minors. Over
the field they are proportional to the minors of the annihilator. -/
private theorem augmented_minor_cross
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hWC : W.transpose * C = 0)
    (hC : ∀ a, C.mulVec a = 0 → a = 0)
    (rows : Fin s → (Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns rows)).det ≠ 0 ∧
    ∀ pick : Fin s → (Fin r ⊕ Fin s),
      (Matrix.fromCols C (unitColumns pick)).det * (W.submatrix rows id).det =
        (Matrix.fromCols C (unitColumns rows)).det * (W.submatrix pick id).det := by
  let A := Matrix.fromCols C (unitColumns rows)
  have hA := augmentation_det_ne_zero C W hWC hC rows hminor
  refine ⟨hA, ?_⟩
  intro pick
  let B := Matrix.fromCols C (unitColumns pick)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  let T := A⁻¹ * B
  let J : Matrix (Fin r ⊕ Fin s) (Fin r) E := Matrix.fromRows 1 0
  have hAJ : A * J = C := by
    simp only [A, J, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hfirst : T.submatrix id Sum.inl = J := by
    change A⁻¹ * C = J
    rw [← hAJ, Matrix.nonsing_inv_mul_cancel_left A J hunit]
  let D := T.submatrix Sum.inr Sum.inr
  have hT : T = Matrix.fromBlocks 1 (T.submatrix Sum.inl Sum.inr) 0 D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inl i)) j
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inr i)) j
      | inr j => rfl
  have hAT : A * T = B := Matrix.mul_nonsing_inv_cancel_left A B hunit
  have hWaug (I : Fin s → (Fin r ⊕ Fin s)) :
      W.transpose * Matrix.fromCols C (unitColumns I) =
        Matrix.fromCols 0 (W.submatrix I id).transpose := by
    rw [Matrix.mul_fromCols, hWC, transpose_mul_unitColumns]
  have hbottom : (W.submatrix rows id).transpose * D = (W.submatrix pick id).transpose := by
    have hh : (W.transpose * A) * T = W.transpose * B := by rw [Matrix.mul_assoc, hAT]
    change (W.transpose * Matrix.fromCols C (unitColumns rows)) * T =
      W.transpose * Matrix.fromCols C (unitColumns pick) at hh
    rw [hWaug, hWaug, hT, Matrix.fromCols_mul_fromBlocks, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, Matrix.zero_mul, zero_add] at hh
    exact congrArg (fun M : Matrix (Fin s) (Fin r ⊕ Fin s) E => M.submatrix id Sum.inr) hh
  have hdetD : (W.submatrix rows id).det * D.det = (W.submatrix pick id).det := by
    simpa only [Matrix.det_mul, Matrix.det_transpose] using congrArg Matrix.det hbottom
  have hdetT : T.det = D.det := by
    rw [hT, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have hdetB : B.det = A.det * D.det := by
    rw [← hAT, Matrix.det_mul, hdetT]
  change B.det * (W.submatrix rows id).det = A.det * (W.submatrix pick id).det
  rw [hdetB, ← hdetD]
  ring

variable {F : Type*} [Field F]

/-- Each adjoined constant column saves one from the total row budget. -/
private theorem augmented_det_degree
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X])
    (d : (Fin r ⊕ Fin s) → ℕ) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (C i j).natDegree ≤ d i)
    (rows : Fin s → (Fin r ⊕ Fin s)) :
    (Matrix.fromCols C (unitColumns rows)).det.natDegree ≤ (∑ i, d i) - s := by
  classical
  let A := Matrix.fromCols C (unitColumns rows : Matrix _ _ F[X])
  change A.det.natDegree ≤ _
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hsign : (Equiv.Perm.sign σ • ∏ j, A (σ j) j).natDegree =
      (∏ j, A (σ j) j).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
  rw [hsign]
  let saving : (Fin r ⊕ Fin s) → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hpoint (j : Fin r ⊕ Fin s) : (A (σ j) j).natDegree + saving j ≤ d (σ j) := by
    cases j with
    | inl j => simpa [A, saving] using hdegree (σ (Sum.inl j)) j
    | inr j =>
      change ((Pi.single (rows j) 1 : Fin r ⊕ Fin s → F[X])
        (σ (Sum.inr j))).natDegree + 1 ≤
        d (σ (Sum.inr j))
      simp only [Pi.single_apply]
      split_ifs <;> simpa only [Polynomial.natDegree_one, Polynomial.natDegree_zero, zero_add]
        using hpositive (σ (Sum.inr j))
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hsaving : (∑ j, saving j) = s := by simp [saving, Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib, hsaving, Equiv.sum_comp σ d] at hsum
  have hprod := Polynomial.natDegree_prod_le Finset.univ (fun j => A (σ j) j)
  omega

private theorem map_augmentation (φ : F[X] →+* E)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X]) (rows : Fin s → (Fin r ⊕ Fin s)) :
    φ (Matrix.fromCols C (unitColumns rows)).det =
      (Matrix.fromCols (C.map φ) (unitColumns rows)).det := by
  rw [φ.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  cases j with
  | inl j => rfl
  | inr j =>
    change φ ((Pi.single (rows j) 1 : Fin r ⊕ Fin s → F[X]) i) =
      (Pi.single (rows j) 1 : Fin r ⊕ Fin s → E) i
    simp only [Pi.single_apply]
    split_ifs <;> simp

/-- Bézout converts fraction-field proportionality into polynomial
divisibility by the primitive minor. -/
theorem primitive_minor_degree (φ : F[X] →+* E) (hφ : Function.Injective φ)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X])
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) F[X])
    (hWC : (W.map φ).transpose * (C.map φ) = 0)
    (hC : ∀ a, (C.map φ).mulVec a = 0 → a = 0)
    (hprim : PrimitiveVector.IsPrimitive
      (fun I : Fin s → (Fin r ⊕ Fin s) => (W.submatrix I id).det))
    (d : (Fin r ⊕ Fin s) → ℕ) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (C i j).natDegree ≤ d i)
    (rows : Fin s → (Fin r ⊕ Fin s)) :
    (W.submatrix rows id).det.natDegree ≤ (∑ i, d i) - s := by
  classical
  let P (I : Fin s → (Fin r ⊕ Fin s)) := (W.submatrix I id).det
  let A (I : Fin s → (Fin r ⊕ Fin s)) := (Matrix.fromCols C (unitColumns I)).det
  change (P rows).natDegree ≤ _
  by_cases hP : P rows = 0
  · simp [hP]
  have hmap (I : Fin s → (Fin r ⊕ Fin s)) : φ (P I) = ((W.map φ).submatrix I id).det :=
    φ.map_det (W.submatrix I id)
  have hW : ((W.map φ).submatrix rows id).det ≠ 0 := by
    rw [← hmap]
    exact fun hz => hP (hφ (hz.trans (map_zero φ).symm))
  obtain ⟨hAfield, hcrossField⟩ := augmented_minor_cross (C.map φ) (W.map φ) hWC hC rows hW
  have hA : A rows ≠ 0 := by
    intro hz
    apply hAfield
    rw [← map_augmentation φ C rows]
    exact (congrArg φ hz).trans (map_zero φ)
  have hcross (I : Fin s → (Fin r ⊕ Fin s)) : A I * P rows = A rows * P I := by
    apply hφ
    simpa only [map_mul, hmap, A, map_augmentation] using hcrossField I
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout P).mp hprim
  let q := ∑ I, a I * A I
  have hfactor : A rows = q * P rows := by
    calc
      A rows = (∑ I, a I * P I) * A rows := by rw [ha, one_mul]
      _ = q * P rows := by
        dsimp only [q]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro I _
        rw [mul_assoc, mul_comm (P I), ← hcross I, ← mul_assoc]
  have hq : q ≠ 0 := by
    intro hz
    exact hA (by rw [hfactor, hz, zero_mul])
  have hbound := augmented_det_degree C d hpositive hdegree rows
  change (A rows).natDegree ≤ _ at hbound
  rw [hfactor, Polynomial.natDegree_mul hq hP] at hbound
  omega

end K21_6_2
end Port_K1_6_2Aux1

section Port_K1_6Defs
set_option autoImplicit true
namespace K21_6
noncomputable section

open Polynomial Matrix

/-- The columns are the first (s) shifts of the pair in the outer variable. -/
def shifts {A : Type} [CommRing A] (P : Fin 2 → A[X]) (L s : ℕ) :
    Matrix (Fin 2 × Fin L) (Fin s) A :=
  fun i j => (P i.1 * Polynomial.X ^ j.val).coeff i.2.val

/-- Coefficients in the inner variable, with the outer degree cutoff retained. -/
def pairCoordinates {F : Type} [Field F] (P : Fin 2 → F[X][X]) (h : ℕ) :
    Fin 2 × Fin (h + 1) → F[X] :=
  fun i => (P i.1).coeff i.2.val

/-- All full-column minors, indexed by row selections. -/
def maximalMinors {A row : Type} [CommRing A] {s : ℕ}
    (W : Matrix row (Fin s) A) (rows : Fin s → row) : A :=
  (W.submatrix rows id).det

end
end K21_6
end Port_K1_6Defs

section Port_K1_6Aux1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_6

open K21 Polynomial Matrix
open FrobeniusLocator ProximityPrize.Benchmark

private theorem map_syndrome {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (f : F →+* E)
    (x w : ι → F) (j : ℕ) :
    f (syndrome x w j) = syndrome (fun i => f (x i)) (fun i => f (w i)) j := by
  simp only [syndrome, weight, map_sum, map_mul, map_pow, map_inv₀, map_prod, map_sub]

private theorem generic_stacked_moment {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (p : ℕ) [ExpChar F p]
    (node u v : ι → F) (hfixed : ∀ i, node i ^ p = node i)
    (φ : F[X] →+* E) (L t : ℕ) (b : Fin 2) (l : Fin L) (j : Fin (t + 1)) :
    let f := φ.comp Polynomial.C
    let z := φ Polynomial.X
    φ (stacked p node u v L t (b, l) j) =
      syndrome (fun i => f (node i)) (fun i =>
        if b = 0 then f (u i) + z * f (v i)
        else f (u i ^ p) + z ^ p * f (v i ^ p)) (l.val + j.val) := by
  let f := φ.comp Polynomial.C
  let z := φ Polynomial.X
  let x := fun i => f (node i)
  dsimp only
  by_cases hb : b = 0
  · simp only [stacked, hankel, hb, ite_true, map_add, map_mul]
    change f (syndrome node u _) + z * f (syndrome node v _) = _
    rw [map_syndrome, map_syndrome]
    simpa only [one_mul] using
      (Principal.syndrome_linear x (fun i => f (u i)) (fun i => f (v i))
        1 z (l.val + j.val)).symm
  · simp only [stacked, hb, ite_false]
    rw [φ.map_add, φ.map_mul, φ.map_pow Polynomial.X]
    change f (syndrome node u _ ^ p) + z ^ p * f (syndrome node v _ ^ p) = _
    rw [← syndrome_frobenius p node hfixed, ← syndrome_frobenius p node hfixed,
      map_syndrome, map_syndrome]
    simpa only [one_mul] using
      (Principal.syndrome_linear x (fun i => f (u i ^ p)) (fun i => f (v i ^ p))
        1 (z ^ p) (l.val + j.val)).symm

private theorem certificate_shifts_annihilate_generic {F E ι : Type} [Field F] [Field E]
    [Fintype ι] [DecidableEq ι] (p : ℕ) [ExpChar F p]
    (node u v : ι → F) (hx : Function.Injective node) (hfixed : ∀ i, node i ^ p = node i)
    (φ : F[X] →+* E) (hφ : Function.Injective φ)
    (k h L t s : ℕ) (hL : h + s = L + 1) (hsize : k + (L + 1) + t ≤ Fintype.card ι)
    (R : Strata.PolynomialRelationCertificate p node u v k h)
    (P : Fin 2 → F[X][X])
    (hP : ∀ b, P b = Principal.assemble (fun j => R.coefficients (b, j))) :
    (shifts P (L + 1) s).transpose * stacked p node u v (L + 1) t = 0 := by
  classical
  let f : F →+* E := φ.comp Polynomial.C
  let x : ι → E := fun i => f (node i)
  let z : E := φ Polynomial.X
  let w : Fin 2 → ι → E := fun b i =>
    if b = 0 then f (u i) + z * f (v i)
    else f (u i ^ p) + z ^ p * f (v i ^ p)
  have hMoment (b : Fin 2) (l : Fin (L + 1)) (j : Fin (t + 1)) :
      φ (stacked p node u v (L + 1) t (b, l) j) = syndrome x (w b) (l.val + j.val) :=
    generic_stacked_moment p node u v hfixed φ (L + 1) t b l j
  have hDegree (b : Fin 2) : (P b).natDegree ≤ h := by
    rw [hP]
    exact R.x_degree b
  have hNode (i : ι) :
      ((P 0).map φ).eval (x i) * w 0 i + ((P 1).map φ).eval (x i) * w 1 i =
        (R.output.map φ).eval (x i) := by
    have he := congrArg φ (R.nodes i)
    simpa only [hP, x, f, RingHom.comp_apply, z, w,
      zero_ne_one, one_ne_zero, ite_true, ite_false, map_add, map_mul, map_pow,
      eval_map_apply] using he
  apply Matrix.ext
  intro d j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, shifts]
  apply hφ
  let A (b : Fin 2) : E[X] := (P b).map φ * Polynomial.X ^ d.val
  have hA (b : Fin 2) : (A b).natDegree ≤ L := by
    have hd : ((P b).map φ).natDegree ≤ h := natDegree_map_le.trans (hDegree b)
    have ha := natDegree_mul_le (p := (P b).map φ) (q := (Polynomial.X : E[X]) ^ d.val)
    rw [natDegree_X_pow] at ha
    have := d.isLt
    dsimp only [A]
    omega
  have hOut (i : ι) : (A 0).eval (x i) * w 0 i + (A 1).eval (x i) * w 1 i =
      ((R.output.map φ) * Polynomial.X ^ d.val).eval (x i) := by
    simp only [A, eval_mul, eval_pow, eval_X]
    rw [← hNode i]
    ring
  have hOutDegree : ((R.output.map φ) * Polynomial.X ^ d.val).degree < ((k + L : ℕ) : WithBot ℕ) := by
    have hR : (R.output.map φ).degree < ((k + h : ℕ) : WithBot ℕ) := degree_map_le.trans_lt R.output_degree
    have hd := Strata.degree_mul_lt_add (Polynomial.X ^ d.val : E[X])
      (R.output.map φ) d.val (k + h) (by simp) hR
    rw [mul_comm] at hd
    refine hd.trans_le ?_
    exact_mod_cast (show k + h + d.val ≤ k + L by have := d.isLt; omega)
  rw [map_sum, map_zero, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [map_mul, hMoment, ← coeff_map, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X]
  change (∑ l : Fin (L + 1), (A 0).coeff l.val * syndrome x (w 0) (l.val + j.val)) +
    (∑ l : Fin (L + 1), (A 1).coeff l.val * syndrome x (w 1) (l.val + j.val)) = 0
  rw [← Strata.syndrome_polynomial_multiple x (w 0) (A 0) _ _ (hA 0),
    ← Strata.syndrome_polynomial_multiple x (w 1) (A 1) _ _ (hA 1)]
  have hLin := Principal.syndrome_linear x
    (fun i => (A 0).eval (x i) * w 0 i) (fun i => (A 1).eval (x i) * w 1 i) 1 1 j.val
  simp only [one_mul] at hLin
  rw [← hLin]
  simp_rw [hOut]
  apply Strata.syndrome_eval_zero x (f.injective.comp hx) _ (k + L) _ hOutDegree
  have := j.isLt
  omega

/-- Each prescribed shift satisfies every complementary moment equation. -/
theorem certificate_shifts_annihilate {u : Words} {T : TwoActive u} (R : Relation T)
    (s : ℕ) (hL : T.height + s = 49067) :
    (shifts (fun b => Principal.assemble (fun j => R.coefficients (b, j))) 49067 s).transpose *
      twoBlock u = 0 := by
  have hsize : 131072 + (49066 + 1) + 82005 ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
  exact certificate_shifts_annihilate_generic p node (u 0) (u 1) IRSProfile.domain.injective
    Native.native_domain_fixed (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
    131072 T.height 49066 82005 s hL hsize R _ (fun _ => rfl)

end K21_6
end Port_K1_6Aux1

section Port_K1_6Aux2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_6

open K21 Polynomial
open FrobeniusLocator ProximityPrize.Benchmark

/-- Clear denominators and remove seed content before applying Gauss's lemma. -/
private theorem lift_common_divisor {G : Frac[X]} {U V : Bivar} (hG : G ≠ 0)
    (hU : G ∣ extendSeed U) (hV : G ∣ extendSeed V) :
    ∃ D : Bivar, D ≠ 0 ∧ G.natDegree ≤ D.natDegree ∧ D ∣ U ∧ D ∣ V := by
  let φ : K[X] →+* Frac := algebraMap K[X] Frac
  have hφ : Function.Injective φ := IsFractionRing.injective K[X] Frac
  let Q : Bivar := IsLocalization.integerNormalization (nonZeroDivisors K[X]) G
  let D := Q.primPart
  obtain ⟨a, ha, hQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors K[X]) G
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hscale : C (φ Q.content) * D.map φ = C (φ a) * G := by
    calc
      C (φ Q.content) * D.map φ = Q.map φ := by
        rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q.eq_C_content_mul_primPart]
      _ = C (φ a) * G := by
        simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hQ
  have hscale0 : C (φ a) * G ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (fun hz => ha0 (hφ (hz.trans (map_zero φ).symm)))) hG
  have hDmap : D.map φ ≠ 0 := by
    intro hz
    exact hscale0 (by rw [← hscale, hz, mul_zero])
  have hcontent : φ Q.content ≠ 0 := by
    intro hz
    exact hscale0 (by rw [← hscale, hz, map_zero, zero_mul])
  have hD : D ≠ 0 := fun hz => hDmap (by rw [hz, Polynomial.map_zero])
  have hGtoD : G ∣ D.map φ := by
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontent)).dvd_mul_left.mp
    rw [hscale]
    exact dvd_mul_left _ _
  have hDtoG : D.map φ ∣ G := by
    have ha' : φ a ≠ 0 := fun hz => ha0 (hφ (hz.trans (map_zero φ).symm))
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha')).dvd_mul_left.mp
    rw [← hscale]
    exact dvd_mul_left _ _
  have hdeg := natDegree_le_of_dvd hGtoD hDmap
  rw [natDegree_map_eq_of_injective hφ] at hdeg
  exact ⟨D, hD, hdeg,
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hU),
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hV)⟩

private theorem specialize_factor {D P A : Bivar} {γ : K} (hD : D ≠ 0)
    (hP : P = D * A) (hγ : atSlope P γ ≠ 0) :
    atSlope P γ = atSlope D γ * atSlope A γ ∧
      (atSlope P γ).natDegree + D.natDegree ≤ P.natDegree + (atSlope D γ).natDegree := by
  have heq : atSlope P γ = atSlope D γ * atSlope A γ := by rw [hP, atSlope, Polynomial.map_mul]; rfl
  have hDγ : atSlope D γ ≠ 0 := by
    intro hz
    exact hγ (by rw [heq, hz, zero_mul])
  have hAγ : atSlope A γ ≠ 0 := by
    intro hz
    exact hγ (by rw [heq, hz, mul_zero])
  have hA : A ≠ 0 := fun hz => hAγ (by rw [hz, atSlope, Polynomial.map_zero])
  refine ⟨heq, ?_⟩
  have hdeg : (atSlope A γ).natDegree ≤ A.natDegree := natDegree_map_le
  rw [heq, natDegree_mul hDγ hAγ, hP, natDegree_mul hD hA]
  omega

private theorem eval_atSlope (P : Bivar) (γ x : K) :
    (atSlope P γ).eval x = (P.eval (C x)).eval γ := by
  simpa only [atSlope, coe_evalRingHom, eval_C] using
    (Polynomial.eval_map_apply (evalRingHom γ) (C x) (p := P))

private theorem root_outside_of_dvd_locator {F ι : Type} [Field F] [Fintype ι]
    [DecidableEq ι] (x : ι → F) (hx : Function.Injective x) (errors fixed : Finset ι) (D : F[X])
    (hD : D ∣ locator x errors) (hdeg : fixed.card < D.natDegree) :
    ∃ i ∉ fixed, D.eval (x i) = 0 := by
  classical
  let S := Finset.univ.filter (fun i : ι => D.eval (x i) = 0)
  have hcard : D.natDegree = S.card := Principal.divisor_domain_roots x hx errors D hD
  have hNot : ¬ S ⊆ fixed := fun h => by
    have := Finset.card_le_card h
    omega
  obtain ⟨i, hiS, hiFixed⟩ := Finset.not_subset.mp hNot
  exact ⟨i, hiFixed, (Finset.mem_filter.mp hiS).2⟩

/-- Saturation preserves the common divisor degree and splits that many distinct
domain roots. More roots than fixed nodes gives a new common zero. -/
theorem moving_has_new_node {u : Words} {T : TwoActive u} (R : Relation T)
    (hMoving : MovingGCD R) {γ : K} {M : BadMark u γ} (hSat : SaturatedAt R M) :
    ∃ i ∉ fixedNodes R,
      (atSlope (leftU R) γ).eval (node i) = 0 ∧ (atSlope (leftV R) γ).eval (node i) = 0 := by
  classical
  obtain ⟨G, hG, hGU, hGV, hg⟩ := hMoving.2
  obtain ⟨D, hD, hd, hDU, hDV⟩ := lift_common_divisor hG hGU hGV
  obtain ⟨A, hA⟩ := hDU
  obtain ⟨B, hB⟩ := hDV
  obtain ⟨hAU, hAUdeg⟩ := specialize_factor hD hA hSat.U_ne
  obtain ⟨hBV, hBVdeg⟩ := specialize_factor hD hB hSat.V_ne
  have hdeg : D.natDegree ≤ (atSlope D γ).natDegree := by
    have hU := R.x_degree 0
    have hV := R.x_degree 1
    change (leftU R).natDegree ≤ T.height at hU
    change (leftV R).natDegree ≤ T.height at hV
    have hMax := hSat.degree_eq
    rcases le_total (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree with h | h
    · rw [max_eq_right h] at hMax
      omega
    · rw [max_eq_left h] at hMax
      omega
  obtain ⟨errors, _, hGCD⟩ := hSat.gcd_errors
  have hDvd := hGCD.2.2.2 (atSlope D γ) ⟨atSlope A γ, hAU⟩ ⟨atSlope B γ, hBV⟩
  have hCard : (fixedNodes R).card < (atSlope D γ).natDegree := by omega
  obtain ⟨i, hiFixed, hi⟩ := root_outside_of_dvd_locator (F := K) (ι := I)
    node IRSProfile.domain.injective errors (fixedNodes R) (atSlope D γ) hDvd hCard
  exact ⟨i, hiFixed, by rw [hAU, eval_mul, hi, zero_mul], by rw [hBV, eval_mul, hi, zero_mul]⟩

private theorem common_node_count {F ι : Type} [Field F] [Fintype ι]
    (U V : ι → F[X]) (H : ℕ) (Γ : Finset F)
    (hU : ∀ i, (U i).natDegree ≤ H) (hV : ∀ i, (V i).natDegree ≤ H)
    (hNew : ∀ γ ∈ Γ, ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0) :
    Γ.card ≤ Fintype.card ι * H := by
  classical
  let Q (i : ι) := if U i = 0 then V i else U i
  have hCover : Γ ⊆ (Finset.univ : Finset ι).biUnion (fun i => (Q i).roots.toFinset) := by
    intro γ hγ
    obtain ⟨i, hNZ, hu, hv⟩ := hNew γ hγ
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [Multiset.mem_toFinset]
    by_cases h : U i = 0
    · rw [show Q i = V i by simp [Q, h]]
      exact (mem_roots (fun hz => hNZ ⟨h, hz⟩)).mpr hv
    · rw [show Q i = U i by simp [Q, h]]
      exact (mem_roots h).mpr hu
  refine (Finset.card_le_card hCover).trans
    ((Finset.card_biUnion_le_card_mul _ _ H ?_).trans_eq (by rw [Finset.card_univ]))
  intro i _
  refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
  change (if U i = 0 then V i else U i).natDegree ≤ H
  split_ifs
  · exact hV i
  · exact hU i

-- Transport the bound with symbolic factors so checking it does not enumerate the index type.
private theorem k16Aux2_count_bound {c n n' H b : ℕ}
    (hn : n = n') (hc : c ≤ n * H) (hb : n' * H = b) : c ≤ b :=
  hb ▸ hn ▸ hc

/-- Cover the marked slopes by one nonzero seed polynomial per nonfixed node. -/
theorem normal_growth_count {u : Words} {T : TwoActive u} (R : Relation T)
    (hHeight : ∀ i, (R.coefficients i).natDegree ≤ 6479539670)
    (hMoving : MovingGCD R) (hSat : NormalSaturation R) (Γ : Finset K)
    (hBad : BadFamily u Γ) (hNormal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1698572447252480 := by
  classical
  let U (i : I) := (leftU R).eval (C (node i))
  let V (i : I) := (leftV R).eval (C (node i))
  have hU (i) : (U i).natDegree ≤ 6479539670 := by
    dsimp only [U, leftU]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (0, j)) _
  have hV (i) : (V i).natDegree ≤ 6479539670 := by
    dsimp only [V, leftV]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (1, j)) _
  have hNew (γ : K) (hγ : γ ∈ Γ) :
      ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0 := by
    refine (K21.bad_mark u Γ hBad γ hγ).elim (fun M => ?_)
    obtain ⟨i, hi, hu, hv⟩ := moving_has_new_node R hMoving (hSat γ (hNormal γ hγ) M)
    rw [eval_atSlope] at hu hv
    have hNZ : ¬ (U i = 0 ∧ V i = 0) := by
      simpa only [fixedNodes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact ⟨i, hNZ, hu, hv⟩
  exact k16Aux2_count_bound (c := Γ.card) (n := Fintype.card I) (n' := 262144)
    (H := 6479539670) (b := 1698572447252480) IRSProfile.card_index
    (common_node_count U V 6479539670 Γ hU hV hNew) rfl

end K21_6
end Port_K1_6Aux2

section Port_K1_6Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K21_6

open K21 Polynomial Matrix
open FrobeniusLocator

/-- Primitivity and maximal seed degree of the full-column shift minors. -/
def c1 : Prop :=
  ∀ (F : Type) [Field F] (h L s : ℕ) (P : Fin 2 → F[X][X]),
    h + s = L → 0 < s →
    (∀ b, (P b).natDegree ≤ h) →
    PrimitiveVector.IsPrimitive (pairCoordinates P h) →
    PrimitiveVector.IsPrimitive (maximalMinors (shifts P L s)) ∧
    ∃ H : ℕ, (∀ b j, ((P b).coeff j).natDegree ≤ H) ∧
      ∃ rows : Fin s → (Fin 2 × Fin L),
        (maximalMinors (shifts P L s) rows).natDegree = s * H

/-- Complementary minors bound the height of a primitive Plücker tuple. -/
def c2 : Prop :=
  ∀ (F : Type) [Field F] (L w s p : ℕ)
    (M : Matrix (Fin 2 × Fin L) (Fin w) F[X]) (W : Matrix (Fin 2 × Fin L) (Fin s) F[X]),
    1 ≤ p →
    GenericLayer.genericRank M + s = 2 * L →
    W.transpose * M = 0 →
    (∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p) →
    PrimitiveVector.IsPrimitive (maximalMinors W) →
    ∀ rows : Fin s → (Fin 2 × Fin L), (maximalMinors W rows).natDegree ≤ L * (p + 1) - s

theorem of_children (h1 : c1) (h2 : c2) : K21.c6 := by
  intro u front T R moving saturated Γ bad normal
  let P (b : Fin 2) : Bivar := Principal.assemble (fun j => R.coefficients (b, j))
  let s := 49067 - T.height
  have hsDef : s = 49067 - T.height := rfl
  have hP : ∀ b, (P b).natDegree ≤ T.height := R.x_degree
  have hBalance : 49067 + T.height + nullity u = 82006 ∧ T.height ≤ 32932 ∧ T.height < 49067 :=
    Native6921Balance (nullity u) T.a T.b T.c
      T.top T.degreeSum T.nullitySum (by have := front.1; omega)
  have hSum : T.height + s = 49067 := by omega
  have hs : 16135 ≤ s := by omega
  have hRank : GenericLayer.genericRank (twoBlock u) + s = 2 * 49067 := by
    change stackRank u + s = _
    rw [K21.actual_stackRank u]
    omega
  have hCoordinates : pairCoordinates P T.height = R.coefficients := by
    funext i
    exact Principal.assemble_coeff (fun j => R.coefficients (i.1, j)) i.2
  have hPrim : PrimitiveVector.IsPrimitive (pairCoordinates P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hKernel := certificate_shifts_annihilate R s hSum
  obtain ⟨hMinors, H, hH, rows, hRows⟩ :=
    h1 K T.height 49067 s P hSum (by omega) hP hPrim
  have hBound := h2 K 49067 82006 s p (twoBlock u) (shifts P 49067 s)
    (by norm_num [Native.p]) hRank hKernel
    (stacked_entry_natDegree p node (u 0) (u 1) 49067 82005) hMinors rows
  rw [hRows] at hBound
  have hProduct : 16135 * H ≤ s * H := Nat.mul_le_mul_right H hs
  have hCeiling : 49067 * (p + 1) = 104547372597078 := by norm_num [Native.p]
  have hCap : H ≤ 6479539670 := by omega
  apply normal_growth_count R _ moving saturated Γ bad normal
  intro i
  rw [← hCoordinates]
  exact (hH i.1 i.2.val).trans hCap

end K21_6
end Port_K1_6Split

section Port_K1_6_1Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace K21_6_1
noncomputable section

open Polynomial Matrix FrobeniusLocator K21_6

/-- Consecutive rows beginning at the highest surviving coefficient of one block
give an upper triangular minor after an entrywise zero-preserving map. -/
private theorem exists_shift_minor {R E : Type} [CommRing R] [Field E]
    (P : Fin 2 → R[X]) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (f : R → E) (hf : f 0 = 0) (b : Fin 2) (j : Fin (h + 1))
    (hj : f ((P b).coeff j.val) ≠ 0) :
    ∃ rows : Fin s → Fin 2 × Fin (h + s),
      maximalMinors ((shifts P (h + s) s).map f) rows ≠ 0 := by
  classical
  let S := (Finset.range (h + 1)).filter (fun d => f ((P b).coeff d) ≠ 0)
  have hS : S.Nonempty := ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hj⟩⟩
  let d := S.max' hS
  have hd : d ∈ S := S.max'_mem hS
  have hdle : d ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
  have hdne : f ((P b).coeff d) ≠ 0 := (Finset.mem_filter.mp hd).2
  have hlarge : ∀ k, d < k → f ((P b).coeff k) = 0 := by
    intro k hk
    by_cases hkh : k < h + 1
    · by_contra hne
      exact (not_le_of_gt hk) (S.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkh, hne⟩))
    · have hk' : (P b).natDegree < k := (hdegree b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', hf]
  let rows (i : Fin s) : Fin 2 × Fin (h + s) := (b, ⟨d + i.val, by omega⟩)
  let A := ((shifts P (h + s) s).map f).submatrix rows id
  have htri : A.IsUpperTriangular := by
    intro i j hij
    change j.val < i.val at hij
    change f ((P b * Polynomial.X ^ j.val).coeff (d + i.val)) = 0
    rw [Polynomial.coeff_mul_X_pow', ite_eq_left (by omega)]
    exact hlarge _ (by omega)
  have hdiag (i : Fin s) : A i i = f ((P b).coeff d) := by
    change f ((P b * Polynomial.X ^ i.val).coeff (d + i.val)) = _
    rw [Polynomial.coeff_mul_X_pow]
  refine ⟨rows, ?_⟩
  change A.det ≠ 0
  rw [Matrix.det_of_isUpperTriangular htri]
  simp only [hdiag, Fin.prod_const]
  exact pow_ne_zero _ hdne

/-- Every maximal quotient of the seed ring retains a nonzero shift minor. -/
private theorem primitive_shift_minors {F : Type} [Field F]
    (P : Fin 2 → F[X][X]) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (hprimitive : PrimitiveVector.IsPrimitive (pairCoordinates P h)) :
    PrimitiveVector.IsPrimitive (maximalMinors (shifts P (h + s) s)) := by
  classical
  let W := shifts P (h + s) s
  let I := Ideal.span (Set.range (maximalMinors W))
  change I = ⊤
  by_contra hI
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let : M.IsMaximal := hM
  let : Field (F[X] ⧸ M) := Ideal.Quotient.field M
  let φ := Ideal.Quotient.mk M
  have hsurvives : ∃ i, φ (pairCoordinates P h i) ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout _).mp hprimitive
    have heq := congrArg φ ha
    simp only [map_sum, map_mul, hn, mul_zero, Finset.sum_const_zero, map_one] at heq
    exact zero_ne_one heq
  obtain ⟨⟨b, j⟩, hj⟩ := hsurvives
  obtain ⟨rows, hrows⟩ := exists_shift_minor P h s hdegree φ (map_zero φ) b j hj
  have hz : φ (maximalMinors W rows) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hIM (Ideal.subset_span (Set.mem_range_self rows)))
  apply hrows
  have heq := φ.map_det (W.submatrix rows id)
  rw [RingHom.mapMatrix_apply] at heq
  exact heq.symm.trans hz

/-- Under a uniform degree bound, the coefficient at the determinant's
degree bound is the determinant of the corresponding entry coefficients. -/
private theorem coeff_det_uniform {F : Type*} [Field F] {s : ℕ}
    (A : Matrix (Fin s) (Fin s) F[X]) (H : ℕ) (hdegree : ∀ i j, (A i j).natDegree ≤ H) :
    A.det.coeff (s * H) = (A.map (fun q => q.coeff H)).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul]
  congr 1
  simpa only [Finset.card_univ, Fintype.card_fin, Matrix.map_apply] using
    Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin s))
      (fun i => A (σ i) i) H (fun i _ => hdegree (σ i) i)

private theorem shift_minors_height {F : Type} [Field F]
    (P : Fin 2 → F[X][X]) (h s : ℕ) (hdegree : ∀ b, (P b).natDegree ≤ h)
    (hprimitive : PrimitiveVector.IsPrimitive (pairCoordinates P h)) :
    ∃ H : ℕ, (∀ b j, ((P b).coeff j).natDegree ≤ H) ∧
      ∃ rows : Fin s → Fin 2 × Fin (h + s),
        (maximalMinors (shifts P (h + s) s) rows).natDegree = s * H := by
  classical
  let q := pairCoordinates P h
  let S := (Finset.univ : Finset (Fin 2 × Fin (h + 1))).filter (fun i => q i ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := PrimitiveVector.exists_eval_ne_zero q hprimitive 0
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro hz
    exact hi (by rw [hz, Polynomial.eval_zero])
  let H := S.sup (fun i => (q i).natDegree)
  have hbound : ∀ b j, ((P b).coeff j).natDegree ≤ H := by
    intro b j
    by_cases hj : j < h + 1
    · let i : Fin 2 × Fin (h + 1) := (b, ⟨j, hj⟩)
      change (q i).natDegree ≤ H
      by_cases hi : q i = 0
      · simp [hi]
      · exact Finset.le_sup (s := S) (f := fun k => (q k).natDegree)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · have hj' : (P b).natDegree < j := (hdegree b).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj']
      simp
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup S hS (fun k => (q k).natDegree)
  have htop : (q i).coeff H ≠ 0 := by
    change H = (q i).natDegree at hmax
    rw [hmax, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (Finset.mem_filter.mp hi).2
  obtain ⟨rows, hrows⟩ := exists_shift_minor P h s hdegree (fun p => p.coeff H)
    (Polynomial.coeff_zero _) i.1 i.2 htop
  let A := (shifts P (h + s) s).submatrix rows id
  have hA (i j : Fin s) : (A i j).natDegree ≤ H := by
    change ((P (rows i).1 * Polynomial.X ^ j.val).coeff (rows i).2.val).natDegree ≤ H
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs
    · exact hbound _ _
    · simp
  have hcoeff : A.det.coeff (s * H) ≠ 0 := by
    rw [coeff_det_uniform A H hA]
    exact hrows
  have hupper : A.det.natDegree ≤ s * H := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      FrobeniusLocator.natDegree_det_le_row_sum A (fun _ => H) hA
  exact ⟨H, hbound, rows, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hupper hcoeff⟩

theorem proof : K21_6.c1 := by
  intro F inst h L s P hL _ hdegree hprimitive
  subst L
  exact ⟨primitive_shift_minors P h s hdegree hprimitive,
    shift_minors_height P h s hdegree hprimitive⟩

end
end K21_6_1
end Port_K1_6_1Proof

section Port_K1_6_2Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace K21_6_2

open Polynomial Matrix
open FrobeniusLocator
open scoped BigOperators

theorem proof : K21_6.c2 := by
  intro F _ L w s p M W hp hrank hkernel hdegree hprim rows
  classical
  let E := GenericLayer.GenericField F
  let φ := algebraMap F[X] E
  have hφ : Function.Injective φ := IsFractionRing.injective F[X] E
  let r := GenericLayer.genericRank M
  obtain ⟨B⟩ := GenericLayer.exists_generic_basis M
  have hcard : Fintype.card (Fin r ⊕ Fin s) = Fintype.card (Fin 2 × Fin L) := by
    simpa [Fintype.card_sum, Fintype.card_prod, r] using hrank
  let e : (Fin r ⊕ Fin s) ≃ (Fin 2 × Fin L) := Fintype.equivOfCardEq hcard
  let C := M.submatrix e B.cols
  let V := W.submatrix e id
  have hC : ∀ a, (C.map φ).mulVec a = 0 → a = 0 := by
    have hdet : ((M.submatrix B.rows B.cols).map φ).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← φ.map_det]
      exact fun hz => B.minor_ne (hφ (hz.trans (map_zero φ).symm))
    intro a ha
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have hi := congrFun ha (e.symm (B.rows i))
    simpa only [C, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.apply_symm_apply, Pi.zero_apply] using hi
  have hVC : (V.map φ).transpose * (C.map φ) = 0 := by
    ext i j
    have hij := congrArg φ (congrFun (congrFun hkernel i) (B.cols j))
    change (∑ k : Fin r ⊕ Fin s, φ (W (e k) i) * φ (M (e k) (B.cols j))) = 0
    rw [Equiv.sum_comp e (fun k => φ (W k i) * φ (M k (B.cols j)))]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      map_sum, map_mul, map_zero] using hij
  have hminor (I : Fin s → (Fin r ⊕ Fin s)) :
      (V.submatrix I id).det = K21_6.maximalMinors W (e ∘ I) := rfl
  have hminor' (J : Fin s → (Fin 2 × Fin L)) :
      (V.submatrix (e.symm ∘ J) id).det = K21_6.maximalMinors W J := by
    rw [hminor]
    congr 1
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have hprimV : PrimitiveVector.IsPrimitive
      (fun I : Fin s → (Fin r ⊕ Fin s) => (V.submatrix I id).det) := by
    have hrange : Set.range (fun I : Fin s → (Fin r ⊕ Fin s) => (V.submatrix I id).det) =
        Set.range (K21_6.maximalMinors W) := by
      ext z
      constructor
      · rintro ⟨I, rfl⟩
        exact ⟨e ∘ I, (hminor I).symm⟩
      · rintro ⟨J, rfl⟩
        exact ⟨e.symm ∘ J, hminor' J⟩
    unfold PrimitiveVector.IsPrimitive at hprim ⊢
    rwa [hrange]
  let d (i : Fin r ⊕ Fin s) := if (e i).1 = 0 then 1 else p
  have hpositive : ∀ i, 1 ≤ d i := by
    intro i
    dsimp [d]
    split_ifs <;> omega
  have hsum : (∑ i, d i) = L * (p + 1) := by
    dsimp [d]
    rw [Equiv.sum_comp e (fun i : Fin 2 × Fin L => if i.1 = 0 then 1 else p)]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, Nat.mul_add, Nat.add_comm]
  have hbound := primitive_minor_degree φ hφ C V hVC hC hprimV d hpositive
    (fun i j => hdegree (e i) (B.cols j)) (e.symm ∘ rows)
  rwa [hminor', hsum] at hbound

end K21_6_2
end Port_K1_6_2Proof
