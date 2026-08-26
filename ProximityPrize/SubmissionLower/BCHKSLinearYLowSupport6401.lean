import ProximityPrize.SubmissionLower.BCHKSLinearYInterpolation6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusCubicMassLedger6401
import ProximityPrize.SubmissionLower.BCHKSMixedHermiteRowSpan6400

/-!
# Linear-in-Y routing of low-support owners at score 64.01

The score-64.01 interpolation polynomial is linear in `Y`.  Write it as
`A(X,Z) + B(X,Z)Y`.  An owner with error support at most `65536` has at
least `196608` agreements, whereas the specialized expression
`A_z + B_z P_z` has degree at most `196607`; it therefore vanishes
identically.

The remaining algebra has two branches.

* If the augmented coefficient columns `B, XB, ..., X^131071 B, A` are
  generically independent over `F(Z)`, a square minor is a nonzero
  polynomial in `Z` of degree at most
  `65537 + 131072 * 65536 = 8590000129`.  Every low-support owner is a root.
* If they are dependent, `-A/B` is a degree-`131071` polynomial over
  `F(Z)`.  At all but at most `65536` domain coordinates, the interpolation
  identities show that its value is `u0 + Z*u1`.  Polynomial uniqueness over
  `F(Z)` then makes the quotient affine in `Z`.

This file supplies the root-counting, low-support vanishing, extension-field
affine uniqueness, and degree-descent pieces.  The concrete augmented-minor
construction is exposed through a small matrix interface so it can be fed by
either a coefficient-column proof or a future pseudo-division proof.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSLinearYLowSupport6401

open Polynomial
open BCHKSSubstitutionVanish
open BCHKSFrobeniusCubicMassLedger6401
open BCHKSFrobeniusProjectiveSectionLine6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

/-! ## Concrete support and degree ledger -/

def lowSupportThreshold6401 : Nat := 65536
def lowSupportAgreementFloor6401 : Nat := 262144 - lowSupportThreshold6401
def linearYSpecializedDegreeCap6401 : Nat := 196607
def linearYQuotientDegreeCap6401 : Nat := 131071
def linearYAugmentedColumnCount6401 : Nat := 131073
def linearYBParameterDegreeCap6401 : Nat := 65536
def linearYAParameterDegreeCap6401 : Nat := 65537
def linearYMinorDegreeCap6401 : Nat :=
  linearYAParameterDegreeCap6401 +
    (linearYAugmentedColumnCount6401 - 1) *
      linearYBParameterDegreeCap6401

def linearYAugmentedColumnCap6401
    (c : Fin linearYAugmentedColumnCount6401) : Nat :=
  if (c : Nat) < linearYAugmentedColumnCount6401 - 1 then
    linearYBParameterDegreeCap6401
  else linearYAParameterDegreeCap6401

theorem lowSupport_ledger_exact6401 :
    lowSupportAgreementFloor6401 = 196608 ∧
      linearYSpecializedDegreeCap6401 < lowSupportAgreementFloor6401 ∧
      linearYMinorDegreeCap6401 = 8590000129 := by
  native_decide

theorem linearYAugmentedColumnCap_sum_exact6401 :
    ∑ c : Fin linearYAugmentedColumnCount6401,
        linearYAugmentedColumnCap6401 c = linearYMinorDegreeCap6401 := by
  native_decide

/-! ## Too many agreement roots force the specialized linear-Y relation -/

theorem specializedLinearY_eq_zero_of_lowSupport
    {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (alpha : I ↪ F) (agreements : Finset I)
    (A B P : F[X])
    (hA : A.natDegree ≤ 196607)
    (hB : B.natDegree ≤ 65536)
    (hP : P.natDegree ≤ 131071)
    (hcard : 196608 ≤ agreements.card)
    (hroot : ∀ i ∈ agreements,
      A.eval (alpha i) + B.eval (alpha i) * P.eval (alpha i) = 0) :
    A + B * P = 0 := by
  let R := A + B * P
  have hRdegree : R.natDegree ≤ 196607 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le hA
    exact Polynomial.natDegree_mul_le.trans (by omega)
  let roots : Finset F := agreements.map alpha
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R roots
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simpa [R, Polynomial.eval_add, Polynomial.eval_mul] using hroot i hi
  · rw [Finset.card_map]
    omega

/-! ## A square polynomial minor charges every singular specialization -/

theorem polynomialMinor_rootCap
    {F J : Type*} [Field F] [DecidableEq F]
    [Fintype J] [DecidableEq J]
    (M : Matrix J J F[X]) (columnCap : J → Nat)
    (hentry : ∀ i j, (M i j).natDegree ≤ columnCap j)
    (hdet : M.det ≠ 0)
    (S : Finset F)
    (hsingular : ∀ z ∈ S,
      (M.map (Polynomial.evalRingHom z)).det = 0) :
    S.card ≤ ∑ j, columnCap j := by
  have hdegree : M.det.natDegree ≤ ∑ j, columnCap j := by
    rw [← Matrix.det_transpose]
    apply BCHKSGaoSpecializationCore6400.natDegree_det_le_sum_rowCaps
    intro j i
    simpa using hentry i j
  let roots : Finset F := S
  have hsubset : roots ⊆ M.det.roots.toFinset := by
    intro z hz
    have hzdet := hsingular z hz
    have heval : Polynomial.eval z M.det = 0 := by
      exact (RingHom.map_det (Polynomial.evalRingHom z) M).trans hzdet
    exact Multiset.mem_toFinset.mpr
      (Polynomial.mem_roots hdet |>.2 heval)
  calc
    S.card = roots.card := rfl
    _ ≤ M.det.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ M.det.roots.card := Multiset.toFinset_card_le _
    _ ≤ M.det.natDegree := Polynomial.card_roots' M.det
    _ ≤ ∑ j, columnCap j := hdegree

/-- Generic independence of the augmented coefficient columns selects one
nonzero square minor.  If every owner supplies a nonzero coefficient vector
annihilated by the specialized full matrix, the selected determinant charges
all owners at the sum of the column parameter-degree caps.

The orientation is intentional: rows of the generic transpose are the
augmented columns, so `exists_columns_det_ne_zero_of_rows_linearIndependent`
selects coefficient positions. -/
theorem ownerFamily_card_le_of_genericAugmentedColumns
    {F Rows Cols : Type*} [Field F] [DecidableEq F]
    [Fintype Rows] [DecidableEq Rows]
    [Fintype Cols] [DecidableEq Cols]
    (M : Matrix Rows Cols F[X]) (columnCap : Cols → Nat)
    (hentry : ∀ r c, (M r c).natDegree ≤ columnCap c)
    (hgeneric : LinearIndependent (RatFunc F)
      ((M.transpose.map (algebraMap F[X] (RatFunc F))).row))
    (S : Finset F) (kernel : F → Cols → F)
    (hkernel : ∀ z ∈ S, ∀ r,
      ∑ c, Polynomial.eval z (M r c) * kernel z c = 0)
    (hnonzero : ∀ z ∈ S, ∃ c, kernel z c ≠ 0) :
    S.card ≤ ∑ c, columnCap c := by
  classical
  obtain ⟨rows, hminor⟩ :=
    BCHKSMixedHermiteRowSpan6400.exists_columns_det_ne_zero_of_rows_linearIndependent
      (M.transpose.map (algebraMap F[X] (RatFunc F))) hgeneric
  let N : Matrix Cols Cols F[X] := M.submatrix rows _root_.id
  have hminorEq :
      ((M.transpose.map (algebraMap F[X] (RatFunc F))).submatrix
        _root_.id rows) =
      (N.map (algebraMap F[X] (RatFunc F))).transpose := by
    ext i j
    rfl
  have hNdet : N.det ≠ 0 := by
    intro hzero
    apply hminor
    rw [hminorEq, Matrix.det_transpose]
    calc
      (N.map (algebraMap F[X] (RatFunc F))).det =
          algebraMap F[X] (RatFunc F) N.det :=
        (RingHom.map_det (algebraMap F[X] (RatFunc F)) N).symm
      _ = 0 := by rw [hzero, map_zero]
  apply polynomialMinor_rootCap N columnCap
  · intro i j
    exact hentry (rows i) j
  · exact hNdet
  · intro z hz
    obtain ⟨c, hc⟩ := hnonzero z hz
    apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
        (v := kernel z) (i := c)
    · funext i
      simpa [N, Matrix.mulVec, dotProduct] using hkernel z hz (rows i)
    · exact mem_nonZeroDivisors_of_ne_zero hc

/-- Exact score-64.01 specialization of the generic augmented-column minor
cap. -/
theorem ownerFamily_card_le_linearYMinorCap6401
    {F Rows : Type*} [Field F] [DecidableEq F]
    [Fintype Rows] [DecidableEq Rows]
    (M : Matrix Rows (Fin linearYAugmentedColumnCount6401) F[X])
    (hentry : ∀ r c,
      (M r c).natDegree ≤ linearYAugmentedColumnCap6401 c)
    (hgeneric : LinearIndependent (RatFunc F)
      ((M.transpose.map (algebraMap F[X] (RatFunc F))).row))
    (S : Finset F)
    (kernel : F → Fin linearYAugmentedColumnCount6401 → F)
    (hkernel : ∀ z ∈ S, ∀ r,
      ∑ c, Polynomial.eval z (M r c) * kernel z c = 0)
    (hnonzero : ∀ z ∈ S, ∃ c, kernel z c ≠ 0) :
    S.card ≤ linearYMinorDegreeCap6401 := by
  rw [← linearYAugmentedColumnCap_sum_exact6401]
  exact ownerFamily_card_le_of_genericAugmentedColumns M
    linearYAugmentedColumnCap6401 hentry hgeneric S kernel hkernel hnonzero

/-! ## The concrete augmented-column dichotomy -/

/-- Multiplication by a nonzero polynomial preserves the independence of a
finite initial segment of the monomial basis.  This is the elementary module
fact behind the linear-`Y` augmented-column dichotomy. -/
theorem linearIndependent_X_pow_mul
    {K : Type*} [Field K] (B : K[X]) (hB : B ≠ 0) (N : Nat) :
    LinearIndependent K (fun j : Fin N =>
      (Polynomial.X : K[X]) ^ (j : Nat) * B) := by
  have hmono : LinearIndependent K (fun j : Fin N =>
      (Polynomial.X : K[X]) ^ (j : Nat)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hj := congrArg
      (fun P : K[X] => P.coeff (j : Nat)) hc
    simpa [Polynomial.coeff_X_pow, ← Fin.ext_iff] using hj
  have hker : LinearMap.ker (LinearMap.mulRight K B) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro P Q hPQ
    exact mul_right_cancel₀ hB (by simpa using hPQ)
  have hmap := hmono.map' (LinearMap.mulRight K B) hker
  simpa [Function.comp_def] using hmap

/-- The augmented family `A, B, XB, ..., X^(N-1)B` is independent exactly
when `B` is nonzero and `A` is not in the span of the shifted `B` columns.
The `Option` orientation agrees with `linearIndependent_option'`: `none` is
the exceptional `A` column and `some j` is the `j`th shifted `B` column. -/
theorem linearIndependent_augmented_iff
    {K : Type*} [Field K] (A B : K[X]) (N : Nat) (hB : B ≠ 0) :
    LinearIndependent K (fun o : Option (Fin N) =>
      Option.casesOn' o A
        (fun j => (Polynomial.X : K[X]) ^ (j : Nat) * B)) ↔
      A ∉ Submodule.span K
        (Set.range (fun j : Fin N =>
          (Polynomial.X : K[X]) ^ (j : Nat) * B)) := by
  rw [linearIndependent_option']
  simp only [linearIndependent_X_pow_mul B hB N, true_and]

/-- Failure of augmented independence produces an actual bounded polynomial
quotient: `A = P*B` with `deg P < N`.  This is division-free and therefore
works verbatim over the rational function field `F(Z)`. -/
theorem exists_bounded_quotient_of_augmented_dependent
    {K : Type*} [Field K] (A B : K[X]) (N : Nat) (hB : B ≠ 0)
    (hN : 0 < N)
    (hdep : ¬ LinearIndependent K (fun o : Option (Fin N) =>
      Option.casesOn' o A
        (fun j => (Polynomial.X : K[X]) ^ (j : Nat) * B))) :
    ∃ P : K[X], P.natDegree < N ∧ A = P * B := by
  have hspan : A ∈ Submodule.span K
      (Set.range (fun j : Fin N =>
        (Polynomial.X : K[X]) ^ (j : Nat) * B)) := by
    by_contra hnot
    exact hdep ((linearIndependent_augmented_iff A B N hB).2 hnot)
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  let P : K[X] := ∑ j : Fin N,
    Polynomial.C (c j) * (Polynomial.X : K[X]) ^ (j : Nat)
  refine ⟨P, ?_, ?_⟩
  · have hle : P.natDegree ≤ N - 1 := by
      dsimp only [P]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j hj
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.le_pred_of_lt (Fin.is_lt j))
    omega
  · rw [← hc]
    simp only [P, Finset.sum_mul, smul_eq_C_mul, mul_assoc]

/-- A polynomial of degree below `D` is determined by its first `D`
coefficients.  Consequently coefficient truncation preserves linear
independence for any family uniformly bounded by `D-1`. -/
theorem linearIndependent_coefficients_of_degree_lt
    {K Cols : Type*} [Field K] [Fintype Cols]
    (v : Cols → K[X]) (D : Nat)
    (hdeg : ∀ c, v c = 0 ∨ (v c).natDegree < D)
    (hli : LinearIndependent K v) :
    LinearIndependent K (fun c : Cols => fun r : Fin D =>
      (v c).coeff (r : Nat)) := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg c
  apply hli g
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_sum, Polynomial.coeff_smul,
    Polynomial.coeff_zero]
  by_cases hn : n < D
  · let r : Fin D := ⟨n, hn⟩
    have hr := congrFun hg r
    simpa [r, Pi.zero_apply] using hr
  ·
    change Polynomial.lcoeff K n (∑ i, g i • v i) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rcases hdeg j with hjzero | hjdeg
    · simp [hjzero]
    · have hcoeff : (v j).coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le hjdeg (Nat.le_of_not_gt hn))
      simp [Polynomial.lcoeff, hcoeff]

/-- The actual augmented family attached to `A(X,Z)+B(X,Z)Y`.  The outer
polynomial variable is `X`; the coefficients are polynomials in `Z`. -/
noncomputable def linearYAugmented
    {F : Type*} [Field F] (A B : F[X][X]) (N : Nat) :
    Option (Fin N) → F[X][X]
  | none => A
  | some j => (Polynomial.X : F[X][X]) ^ (j : Nat) * B

/-- First-`D` coefficient matrix of the augmented family. -/
noncomputable def linearYAugmentedCoefficientMatrix
    {F : Type*} [Field F] (A B : F[X][X]) (N D : Nat) :
    Matrix (Fin D) (Option (Fin N)) F[X] :=
  fun r c => (linearYAugmented A B N c).coeff (r : Nat)

/-- Mapping the coefficient matrix to `F(Z)` preserves generic column
independence whenever the augmented polynomials are independent and all have
`X`-degree below the truncation length. -/
theorem linearYAugmentedCoefficientMatrix_generic
    {F : Type*} [Field F]
    (A B : F[X][X]) (N D : Nat)
    (hdegree : ∀ c : Option (Fin N),
      linearYAugmented A B N c = 0 ∨
        (linearYAugmented A B N c).natDegree < D)
    (hli : LinearIndependent (RatFunc F) (fun c : Option (Fin N) =>
      (linearYAugmented A B N c).map
        (algebraMap F[X] (RatFunc F)))) :
    LinearIndependent (RatFunc F)
      (((linearYAugmentedCoefficientMatrix A B N D).transpose.map
        (algebraMap F[X] (RatFunc F))).row) := by
  have hcoeff := linearIndependent_coefficients_of_degree_lt
    (v := fun c : Option (Fin N) =>
      (linearYAugmented A B N c).map
        (algebraMap F[X] (RatFunc F))) D (fun c => by
          rcases hdegree c with hc | hc
          · exact Or.inl (by simp [hc])
          · exact Or.inr (Polynomial.natDegree_map_le.trans_lt hc)) hli
  change LinearIndependent (RatFunc F) (fun c : Option (Fin N) =>
    fun r : Fin D => algebraMap F[X] (RatFunc F)
      ((linearYAugmented A B N c).coeff (r : Nat)))
  simpa only [Polynomial.coeff_map] using hcoeff

/-- The coefficient matrix has the advertised per-column parameter-degree
caps as soon as `A` and every shifted `B` coefficient does. -/
theorem linearYAugmentedCoefficientMatrix_entryCap
    {F : Type*} [Field F]
    (A B : F[X][X]) (N D : Nat) (cap : Option (Fin N) → Nat)
    (hcap : ∀ r c,
      ((linearYAugmented A B N c).coeff r).natDegree ≤ cap c) :
    ∀ r c, (linearYAugmentedCoefficientMatrix A B N D r c).natDegree ≤ cap c := by
  intro r c
  exact hcap (r : Nat) c

/-- The coefficient vector of a degree-`<N` owner is a nonzero kernel vector
of the specialized augmented matrix whenever `A_z+B_z P=0`. -/
theorem linearYAugmentedCoefficientMatrix_ownerKernel
    {F : Type*} [Field F]
    (A B : F[X][X]) (N D : Nat) (z : F) (P : F[X])
    (hP : P.natDegree < N)
    (hzero : A.map (Polynomial.evalRingHom z) +
      B.map (Polynomial.evalRingHom z) * P = 0) :
    (∀ r : Fin D,
      ∑ c : Option (Fin N),
        Polynomial.eval z
            (linearYAugmentedCoefficientMatrix A B N D r c) *
          Option.casesOn' c 1 (fun j => P.coeff (j : Nat)) = 0) ∧
      (∃ c : Option (Fin N),
        Option.casesOn' c 1 (fun j => P.coeff (j : Nat)) ≠ 0) := by
  classical
  have hPsum :
      (∑ j : Fin N, Polynomial.C (P.coeff (j : Nat)) *
        (Polynomial.X : F[X]) ^ (j : Nat)) = P := by
    calc
      (∑ j : Fin N, Polynomial.C (P.coeff (j : Nat)) *
          (Polynomial.X : F[X]) ^ (j : Nat)) =
          ∑ j ∈ Finset.range N,
            Polynomial.C (P.coeff j) * (Polynomial.X : F[X]) ^ j :=
        Fin.sum_univ_eq_sum_range
          (fun j => Polynomial.C (P.coeff j) *
            (Polynomial.X : F[X]) ^ j) N
      _ = P := (P.as_sum_range_C_mul_X_pow' hP).symm
  constructor
  · intro r
    let e : F[X] →+* F := Polynomial.evalRingHom z
    let Az : F[X] := A.map e
    let Bz : F[X] := B.map e
    have hshift (j : Fin N) :
        (((Polynomial.X : F[X][X]) ^ (j : Nat) * B).map e) =
          (Polynomial.X : F[X]) ^ (j : Nat) * Bz := by
      simp [Bz, e]
    have hmul :
        (∑ j : Fin N,
          Polynomial.C (P.coeff (j : Nat)) *
            (((Polynomial.X : F[X][X]) ^ (j : Nat) * B).map e)) =
          P * Bz := by
      calc
        (∑ j : Fin N,
            Polynomial.C (P.coeff (j : Nat)) *
              (((Polynomial.X : F[X][X]) ^ (j : Nat) * B).map e)) =
            (∑ j : Fin N,
              Polynomial.C (P.coeff (j : Nat)) *
                (Polynomial.X : F[X]) ^ (j : Nat)) * Bz := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [hshift]
          ring
        _ = P * Bz := by rw [hPsum]
    have hpolyzero :
        Az + ∑ j : Fin N,
          Polynomial.C (P.coeff (j : Nat)) *
            (((Polynomial.X : F[X][X]) ^ (j : Nat) * B).map e) = 0 := by
      rw [hmul]
      simpa [Az, Bz, e, mul_comm] using hzero
    have hcoeff := congrArg (Polynomial.lcoeff F (r : Nat)) hpolyzero
    have heval (R : F[X]) : Polynomial.evalRingHom z R = Polynomial.eval z R := rfl
    rw [Fintype.sum_option]
    simpa only [linearYAugmentedCoefficientMatrix, linearYAugmented, Az, e,
      Option.casesOn'_none, Option.casesOn'_some, mul_one, one_mul,
      map_add, map_sum, Polynomial.lcoeff_apply,
      Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_map,
      Polynomial.coeff_zero, heval, mul_comm] using hcoeff
  · exact ⟨none, one_ne_zero⟩

/-- Fully concrete determinant branch for a linear-`Y` pair.  There is no
matrix or kernel hypothesis left: both are manufactured from the augmented
polynomial columns. -/
theorem ownerFamily_card_le_of_linearYAugmentedIndependent
    {F : Type*} [Field F] [DecidableEq F]
    (A B : F[X][X]) (N D : Nat) (cap : Option (Fin N) → Nat)
    (hdegree : ∀ c : Option (Fin N),
      linearYAugmented A B N c = 0 ∨
        (linearYAugmented A B N c).natDegree < D)
    (hentry : ∀ r c,
      ((linearYAugmented A B N c).coeff r).natDegree ≤ cap c)
    (hindependent : LinearIndependent (RatFunc F)
      (fun c : Option (Fin N) =>
        (linearYAugmented A B N c).map
          (algebraMap F[X] (RatFunc F))))
    (S : Finset F) (P : F → F[X])
    (hP : ∀ z ∈ S, (P z).natDegree < N)
    (hzero : ∀ z ∈ S,
      A.map (Polynomial.evalRingHom z) +
        B.map (Polynomial.evalRingHom z) * P z = 0) :
    S.card ≤ ∑ c, cap c := by
  let M := linearYAugmentedCoefficientMatrix A B N D
  exact ownerFamily_card_le_of_genericAugmentedColumns M cap
    (linearYAugmentedCoefficientMatrix_entryCap A B N D cap hentry)
    (linearYAugmentedCoefficientMatrix_generic A B N D hdegree hindependent)
    S (fun z c => Option.casesOn' c 1
      (fun j => (P z).coeff (j : Nat)))
    (fun z hz => (linearYAugmentedCoefficientMatrix_ownerKernel
      A B N D z (P z) (hP z hz) (hzero z hz)).1)
    (fun z hz => (linearYAugmentedCoefficientMatrix_ownerKernel
      A B N D z (P z) (hP z hz) (hzero z hz)).2)


/-! ## Affine uniqueness over an extension field -/

theorem lagrange_natDegree_le_of_card_eq_succ
    {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (E : Finset I) (alpha : I → F) (U : I → F) (k : Nat)
    (hinj : Set.InjOn alpha (E : Set I)) (hcard : E.card = k + 1) :
    (Lagrange.interpolate E alpha U).natDegree ≤ k := by
  classical
  let p := Lagrange.interpolate E alpha U
  change p.natDegree ≤ k
  by_cases hp : p = 0
  · rw [hp]
    simp
  · have hdeg : p.degree < (E.card : WithBot Nat) :=
      Lagrange.degree_interpolate_lt U hinj
    have hnat : p.natDegree < E.card :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg
    simpa [hcard] using hnat

/-- A degree-`D` polynomial over any extension field which evaluates to an
affine function of one fixed extension element on `D+1` ground-field nodes
is itself the corresponding affine combination of two ground-field
polynomials. -/
theorem extensionPolynomial_eq_affine_of_many_evals
    {F L I : Type*} [Field F] [Field L]
    [DecidableEq F] [DecidableEq I]
    (embed : F →+* L) (hembed : Function.Injective embed)
    (theta : L) (gamma : L[X]) (D : Nat)
    (nodes : Finset I) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (hnodes : D + 1 ≤ nodes.card)
    (hgamma : gamma.natDegree ≤ D)
    (heval : ∀ i ∈ nodes,
      gamma.eval (embed (alpha i)) =
        embed (u₀ i) + theta * embed (u₁ i)) :
    ∃ p₀ p₁ : F[X],
      p₀.natDegree ≤ D ∧ p₁.natDegree ≤ D ∧
      gamma = p₀.map embed + Polynomial.C theta * p₁.map embed := by
  classical
  obtain ⟨E, hEnodes, hEcard⟩ := Finset.exists_subset_card_eq hnodes
  let p₀ : F[X] := Lagrange.interpolate E alpha u₀
  let p₁ : F[X] := Lagrange.interpolate E alpha u₁
  have hinj : Set.InjOn (alpha : I → F) (E : Set I) :=
    alpha.injective.injOn
  have hp₀ : p₀.natDegree ≤ D :=
    lagrange_natDegree_le_of_card_eq_succ E alpha u₀ D hinj hEcard
  have hp₁ : p₁.natDegree ≤ D :=
    lagrange_natDegree_le_of_card_eq_succ E alpha u₁ D hinj hEcard
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  let rhs : L[X] := p₀.map embed + Polynomial.C theta * p₁.map embed
  have hrhs : rhs.natDegree ≤ D := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_map_le.trans hp₀
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_map_le.trans hp₁)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq gamma rhs
    (f := fun i : E => embed (alpha i))
  · exact hembed.comp (alpha.injective.comp Subtype.val_injective)
  · intro i
    have hiNodes : (i : I) ∈ nodes := hEnodes i.property
    have hp₀eval : p₀.eval (alpha i) = u₀ i :=
      Lagrange.eval_interpolate_at_node u₀ hinj i.property
    have hp₁eval : p₁.eval (alpha i) = u₁ i :=
      Lagrange.eval_interpolate_at_node u₁ hinj i.property
    rw [heval i hiNodes]
    simp [rhs, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_map, hp₀eval, hp₁eval]
  · rw [Fintype.card_coe, hEcard]
    exact max_lt (hgamma.trans_lt (Nat.lt_succ_self D))
      (hrhs.trans_lt (Nat.lt_succ_self D))

/-- Function-field form used by the global-divisor branch of the linear-Y
interpolant. -/
theorem ratFuncPolynomial_eq_affine_of_many_evals
    {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (gamma : (RatFunc F)[X]) (D : Nat)
    (nodes : Finset I) (alpha : I ↪ F) (u₀ u₁ : I → F)
    (hnodes : D + 1 ≤ nodes.card)
    (hgamma : gamma.natDegree ≤ D)
    (heval : ∀ i ∈ nodes,
      gamma.eval (algebraMap F (RatFunc F) (alpha i)) =
        algebraMap F (RatFunc F) (u₀ i) +
          RatFunc.X * algebraMap F (RatFunc F) (u₁ i)) :
    ∃ p₀ p₁ : F[X],
      p₀.natDegree ≤ D ∧ p₁.natDegree ≤ D ∧
      gamma = p₀.map (algebraMap F (RatFunc F)) +
        Polynomial.C RatFunc.X *
          p₁.map (algebraMap F (RatFunc F)) := by
  exact extensionPolynomial_eq_affine_of_many_evals
    (algebraMap F (RatFunc F)) (algebraMap F (RatFunc F)).injective
    RatFunc.X gamma D nodes alpha u₀ u₁ hnodes hgamma heval

/-! ## Two bounded specializations descend the affine coefficient degrees -/

theorem affineCoefficient_degreeCaps_of_two_specializations
    {F : Type*} [Field F]
    (p₀ p₁ Pz Pw : F[X]) (z w : F) (D : Nat)
    (hzw : z ≠ w)
    (hz : Pz = p₀ + Polynomial.C z * p₁)
    (hw : Pw = p₀ + Polynomial.C w * p₁)
    (hPz : Pz.natDegree ≤ D) (hPw : Pw.natDegree ≤ D) :
    p₀.natDegree ≤ D ∧ p₁.natDegree ≤ D := by
  have hsub : Pw - Pz = Polynomial.C (w - z) * p₁ := by
    rw [hz, hw]
    simp only [map_sub]
    ring
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  have hp₁eq : p₁ = Polynomial.C ((w - z)⁻¹) * (Pw - Pz) := by
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hwz)
    rw [hsub]
    simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ hwz, map_one,
      one_mul]
  have hp₁ : p₁.natDegree ≤ D := by
    rw [hp₁eq]
    calc
      (Polynomial.C ((w - z)⁻¹) * (Pw - Pz)).natDegree ≤
          (Polynomial.C ((w - z)⁻¹)).natDegree +
            (Pw - Pz).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + D := Nat.add_le_add (by simp)
        ((Polynomial.natDegree_sub_le _ _).trans (max_le hPw hPz))
      _ = D := Nat.zero_add D
  have hp₀eq : p₀ = Pz - Polynomial.C z * p₁ := by
    rw [hz]
    ring
  refine ⟨?_, hp₁⟩
  rw [hp₀eq]
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le hPz (Polynomial.natDegree_C_mul_le _ _ |>.trans hp₁))

end BCHKSLinearYLowSupport6401
end ProximityPrize.SubmissionLower
