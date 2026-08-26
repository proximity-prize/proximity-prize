import ProximityPrize.SubmissionLower.BCHKSFrobeniusRectangularHankelAudit6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusSixLanePencilNoGo6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusRectangularHankelAudit6401
open BCHKSTwoFrobeniusModuleAudit6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
abbrev SixLaneRow (rows : Nat) := Fin 6 × Fin rows
def pencilLowIndex (rows p : Nat) (r : Fin rows) : Fin (rows + p) :=
  ⟨r.1, by omega⟩
def pencilHighIndex (rows p : Nat) (r : Fin rows) : Fin (rows + p) :=
  ⟨p + r.1, by omega⟩
def sixLanePencilCoefficientMatrix
    {F : Type*} [Field F] (rows p : Nat) (c : Fin 6 → F) :
    Matrix (SixLaneRow rows) (Fin (rows + p)) F :=
  fun lr k =>
    (if k = pencilLowIndex rows p lr.2 then c lr.1 else 0) +
      (if k = pencilHighIndex rows p lr.2 then 1 else 0)
theorem sixLanePencilCoefficientMatrix_mulVec
    {F : Type*} [Field F] (rows p : Nat) (c : Fin 6 → F)
    (x : Fin (rows + p) → F) (lane : Fin 6) (r : Fin rows) :
    (sixLanePencilCoefficientMatrix rows p c).mulVec x (lane, r) =
      c lane * x (pencilLowIndex rows p r) +
        x (pencilHighIndex rows p r) := by
  classical
  simp only [sixLanePencilCoefficientMatrix, Matrix.mulVec, dotProduct,
    add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
theorem sixLanePencilCoefficientMatrix_mulVec_eq_zero_imp
    {F : Type*} [Field F] (rows p : Nat) (hp : p ≤ rows)
    (c : Fin 6 → F) (hc : c 0 ≠ c 1)
    (x : Fin (rows + p) → F)
    (hx : (sixLanePencilCoefficientMatrix rows p c).mulVec x = 0) :
    x = 0 := by
  classical
  have hlow : ∀ r : Fin rows, x (pencilLowIndex rows p r) = 0 := by
    intro r
    have h0 := congrFun hx ((0 : Fin 6), r)
    have h1 := congrFun hx ((1 : Fin 6), r)
    rw [sixLanePencilCoefficientMatrix_mulVec] at h0 h1
    simp only [Pi.zero_apply] at h0 h1
    have hprod : (c 0 - c 1) * x (pencilLowIndex rows p r) = 0 := by
      linear_combination h0 - h1
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hc)
  have hhigh : ∀ r : Fin rows, x (pencilHighIndex rows p r) = 0 := by
    intro r
    have h0 := congrFun hx ((0 : Fin 6), r)
    rw [sixLanePencilCoefficientMatrix_mulVec, hlow r,
      mul_zero, zero_add, Pi.zero_apply] at h0
    exact h0
  funext k
  by_cases hk : k.1 < rows
  · let r : Fin rows := ⟨k.1, hk⟩
    have hr := hlow r
    simpa [pencilLowIndex, r] using hr
  · have hpk : p ≤ k.1 := hp.trans (Nat.le_of_not_gt hk)
    let r : Fin rows := ⟨k.1 - p, by omega⟩
    have hr := hhigh r
    have hidx : pencilHighIndex rows p r = k := by
      apply Fin.ext
      simp [pencilHighIndex, r]
      omega
    simpa [hidx] using hr
theorem sixLanePencilCoefficientMatrix_rank_eq
    {F : Type*} [Field F] (rows p : Nat) (hp : p ≤ rows)
    (c : Fin 6 → F) (hc : c 0 ≠ c 1) :
    (sixLanePencilCoefficientMatrix rows p c).rank = rows + p := by
  let C := sixLanePencilCoefficientMatrix rows p c
  have hinj : Function.Injective C.mulVec := by
    intro x y hxy
    have hsub : C.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp
      (sixLanePencilCoefficientMatrix_mulVec_eq_zero_imp rows p hp c hc
        (x - y) hsub)
  have hker : LinearMap.ker C.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot_of_injective hinj
  have hnull :=
    BCHKSGaoSpecializationCore6400.rank_add_finrank_ker_mulVecLin C
  rw [hker] at hnull
  simpa [C] using hnull
def sixLaneSupportLeftFactor
    {F : Type*} [Field F] {s : Nat}
    (rows : Nat) (alpha : Fin s → F)
    (d : Fin 6 → Fin s → F) :
    Matrix (SixLaneRow rows) (Fin s) F :=
  fun lr i => d lr.1 i * alpha i ^ lr.2.1
def sixLaneSupportSyndromeMatrix
    {F : Type*} [Field F] {s : Nat}
    (rows cols : Nat) (alpha : Fin s → F)
    (d : Fin 6 → Fin s → F) :
    Matrix (SixLaneRow rows) (Fin cols) F :=
  fun lr j => supportSyndrome alpha (d lr.1) (lr.2.1 + j.1)
theorem sixLaneSupportSyndromeMatrix_factorization
    {F : Type*} [Field F] {s : Nat}
    (rows cols : Nat) (alpha : Fin s → F)
    (d : Fin 6 → Fin s → F) :
    sixLaneSupportSyndromeMatrix rows cols alpha d =
      sixLaneSupportLeftFactor rows alpha d *
        rectangularSyndromeRightVandermonde cols alpha := by
  classical
  ext lr j
  simp only [sixLaneSupportSyndromeMatrix, sixLaneSupportLeftFactor,
    rectangularSyndromeRightVandermonde, Matrix.mul_apply,
    supportSyndrome]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring
theorem sixLaneSupportSyndromeMatrix_rank_eq_leftFactor
    {F : Type*} [Field F] {s rows cols : Nat}
    (alpha : Fin s ↪ F) (d : Fin 6 → Fin s → F)
    (hcols : s ≤ cols) :
    (sixLaneSupportSyndromeMatrix rows cols alpha d).rank =
      (sixLaneSupportLeftFactor rows alpha d).rank := by
  classical
  rw [sixLaneSupportSyndromeMatrix_factorization]
  apply Nat.le_antisymm
  · exact Matrix.rank_mul_le_left _ _
  · let col : Fin s → Fin cols := Fin.castLE hcols
    let L := sixLaneSupportLeftFactor rows (alpha : Fin s → F) d
    let V := rectangularSyndromeRightVandermonde cols (alpha : Fin s → F)
    have hVsub : V.submatrix id col =
        Matrix.vandermonde (alpha : Fin s → F) := by
      ext i j
      rfl
    have hsub : (L * V).submatrix id col =
        L * Matrix.vandermonde (alpha : Fin s → F) := by
      rw [Matrix.submatrix_mul L V id (Equiv.refl (Fin s)) col
        (Equiv.refl (Fin s)).bijective]
      simp only [Equiv.coe_refl, Matrix.submatrix_id_id, hVsub]
    have hdet : IsUnit
        (Matrix.vandermonde (alpha : Fin s → F)).det :=
      isUnit_iff_ne_zero.mpr
        (Matrix.det_vandermonde_ne_zero_iff.mpr alpha.injective)
    have hrankSub : ((L * V).submatrix id col).rank = L.rank := by
      rw [hsub]
      exact Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet
    exact (le_of_eq hrankSub.symm).trans
      (Matrix.rank_submatrix_le (L * V) id col)
def sixLanePencilProfile
    {F : Type*} [Field F] {s : Nat}
    (alpha beta : Fin s → F) (p : Nat) (c : Fin 6 → F) :
    Fin 6 → Fin s → F :=
  fun lane i => beta i * (alpha i ^ p + c lane)
theorem sixLanePencilLeftFactor_factorization
    {F : Type*} [Field F] {s rows p : Nat}
    (alpha beta : Fin s → F) (c : Fin 6 → F) :
    sixLaneSupportLeftFactor rows alpha
        (sixLanePencilProfile alpha beta p c) =
      sixLanePencilCoefficientMatrix rows p c *
        syndromeLeftVandermonde (rows := rows + p) alpha *
          Matrix.diagonal beta := by
  classical
  ext lr i
  rw [Matrix.mul_diagonal]
  change beta i * (alpha i ^ p + c lr.1) * alpha i ^ lr.2.1 =
    ((sixLanePencilCoefficientMatrix rows p c).mulVec
      (fun k : Fin (rows + p) => alpha i ^ k.1)) lr * beta i
  rw [sixLanePencilCoefficientMatrix_mulVec]
  simp [pencilLowIndex, pencilHighIndex, pow_add]
  ring
theorem sixLanePencilCore_rank_eq
    {F : Type*} [Field F] {s rows p : Nat}
    (alpha : Fin s ↪ F) (hp : p ≤ rows) (hsize : rows + p ≤ s)
    (c : Fin 6 → F) (hc : c 0 ≠ c 1) :
    (sixLanePencilCoefficientMatrix rows p c *
      syndromeLeftVandermonde (rows := rows + p) alpha).rank = rows + p := by
  classical
  let C := sixLanePencilCoefficientMatrix rows p c
  let V := syndromeLeftVandermonde (rows := rows + p) (alpha : Fin s → F)
  let col : Fin (rows + p) → Fin s := Fin.castLE hsize
  have hVsub : V.submatrix id col =
      (Matrix.vandermonde
        (fun j : Fin (rows + p) => alpha (col j))).transpose := by
    ext i j
    simp [V, syndromeLeftVandermonde, Matrix.vandermonde]
  have hsub : (C * V).submatrix id col =
      C * (Matrix.vandermonde
        (fun j : Fin (rows + p) => alpha (col j))).transpose := by
    rw [Matrix.submatrix_mul C V id (Equiv.refl (Fin (rows + p))) col
      (Equiv.refl (Fin (rows + p))).bijective]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id, hVsub]
  have hdet : IsUnit
      (Matrix.vandermonde
        (fun j : Fin (rows + p) => alpha (col j))).transpose.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr
      (alpha.injective.comp (Fin.castLE_injective hsize)))
  have hrankSub : ((C * V).submatrix id col).rank = rows + p := by
    rw [hsub, Matrix.rank_mul_eq_left_of_isUnit_det _ C hdet,
      sixLanePencilCoefficientMatrix_rank_eq rows p hp c hc]
  apply Nat.le_antisymm
  · exact (Matrix.rank_mul_le_left C V).trans <| by
      simpa [C] using Matrix.rank_le_card_width C
  · exact (le_of_eq hrankSub.symm).trans
      (Matrix.rank_submatrix_le (C * V) id col)
theorem sixLanePencilLeftFactor_rank_eq
    {F : Type*} [Field F] {s rows p : Nat}
    (alpha : Fin s ↪ F) (beta : Fin s → F)
    (hbeta : ∀ i, beta i ≠ 0)
    (hp : p ≤ rows) (hsize : rows + p ≤ s)
    (c : Fin 6 → F) (hc : c 0 ≠ c 1) :
    (sixLaneSupportLeftFactor rows alpha
      (sixLanePencilProfile alpha beta p c)).rank = rows + p := by
  classical
  rw [sixLanePencilLeftFactor_factorization]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det]
  · exact sixLanePencilCore_rank_eq alpha hp hsize c hc
  · rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i hi => hbeta i)
theorem sixLanePencilSyndrome_rank_eq
    {F : Type*} [Field F] {s rows p : Nat}
    (alpha : Fin s ↪ F) (beta : Fin s → F)
    (hbeta : ∀ i, beta i ≠ 0)
    (hp : p ≤ rows) (hsize : rows + p ≤ s)
    (c : Fin 6 → F) (hc : c 0 ≠ c 1) :
    (sixLaneSupportSyndromeMatrix rows s alpha
      (sixLanePencilProfile alpha beta p c)).rank = rows + p := by
  classical
  rw [sixLaneSupportSyndromeMatrix_factorization]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det]
  · exact sixLanePencilLeftFactor_rank_eq alpha beta hbeta hp hsize c hc
  · change IsUnit (Matrix.vandermonde (alpha : Fin s → F)).det
    exact isUnit_iff_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr alpha.injective)
theorem sixLanePencilRectangularSyndrome_rank_eq
    {F : Type*} [Field F] {s rows cols p : Nat}
    (alpha : Fin s ↪ F) (beta : Fin s → F)
    (hbeta : ∀ i, beta i ≠ 0)
    (hp : p ≤ rows) (hsize : rows + p ≤ s) (hcols : s ≤ cols)
    (c : Fin 6 → F) (hc : c 0 ≠ c 1) :
    (sixLaneSupportSyndromeMatrix rows cols alpha
      (sixLanePencilProfile alpha beta p c)).rank = rows + p := by
  rw [sixLaneSupportSyndromeMatrix_rank_eq_leftFactor alpha _ hcols]
  exact sixLanePencilLeftFactor_rank_eq alpha beta hbeta hp hsize c hc
def sixFrobeniusOrbit
    {F : Type*} [Field F] (sigma : F →+* F) (x : F) : Fin 6 → F :=
  ![x, sigma x, sigma (sigma x), sigma (sigma (sigma x)),
    sigma (sigma (sigma (sigma x))),
    sigma (sigma (sigma (sigma (sigma x))))]
def sixFrobeniusErrorProfile
    {F : Type*} [Field F] {s : Nat}
    (sigma : F →+* F) (beta E : Fin s → F) :
    Fin 6 → Fin s → F :=
  fun lane i => beta i * sixFrobeniusOrbit sigma (E i) lane
theorem sixFrobenius_pencil_profile
    {F : Type*} [Field F] {s : Nat}
    (sigma : F →+* F) (alpha : Fin s → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (beta : Fin s → F) (p : Nat) (lambda : F) :
    sixFrobeniusErrorProfile sigma beta
        (fun i => alpha i ^ p + lambda) =
      sixLanePencilProfile alpha beta p (sixFrobeniusOrbit sigma lambda) := by
  funext lane i
  fin_cases lane <;> simp [sixFrobeniusErrorProfile, sixFrobeniusOrbit,
    sixLanePencilProfile, hfixed, map_add, map_pow]
theorem fixed_pow_add_nonfixed_ne_zero
    {F : Type*} [Field F] (sigma : F →+* F)
    (alpha : F) (hfixed : sigma alpha = alpha)
    (p : Nat) (lambda : F) (hlambda : lambda ≠ sigma lambda) :
    alpha ^ p + lambda ≠ 0 := by
  intro hzero
  have hlam : lambda = -(alpha ^ p) :=
    eq_neg_of_add_eq_zero_right hzero
  have hsigma : sigma lambda = lambda := by
    calc
      sigma lambda = sigma (-(alpha ^ p)) := by rw [hlam]
      _ = -(sigma alpha ^ p) := by simp
      _ = -(alpha ^ p) := by rw [hfixed]
      _ = lambda := hlam.symm
  exact hlambda hsigma.symm
theorem sixFrobeniusPencil_syndrome_rank_eq
    {F : Type*} [Field F] {s rows p : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (beta : Fin s → F) (hbeta : ∀ i, beta i ≠ 0)
    (hp : p ≤ rows) (hsize : rows + p ≤ s)
    (lambda : F) (hlambda : lambda ≠ sigma lambda) :
    (sixLaneSupportSyndromeMatrix rows s alpha
      (sixFrobeniusErrorProfile sigma beta
        (fun i => alpha i ^ p + lambda))).rank = rows + p := by
  rw [sixFrobenius_pencil_profile sigma alpha hfixed beta p lambda]
  apply sixLanePencilSyndrome_rank_eq alpha beta hbeta hp hsize
  simpa [sixFrobeniusOrbit] using hlambda
theorem sixFrobeniusPencil_exactSupport_counterprofile
    {F : Type*} [Field F] {s rows p : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (beta : Fin s → F) (hbeta : ∀ i, beta i ≠ 0)
    (hp : p ≤ rows) (hsize : rows + p ≤ s)
    (lambda : F) (hlambda : lambda ≠ sigma lambda)
    (herror : ∀ i, alpha i ^ p + lambda ≠ 0) :
    (∀ i, alpha i ^ p + lambda ≠ 0) ∧
      (sixLaneSupportSyndromeMatrix rows s alpha
        (sixFrobeniusErrorProfile sigma beta
          (fun i => alpha i ^ p + lambda))).rank = rows + p := by
  exact ⟨herror,
    sixFrobeniusPencil_syndrome_rank_eq sigma alpha hfixed beta hbeta
      hp hsize lambda hlambda⟩
theorem sixFrobeniusPencil_rectangular_exactSupport_counterprofile
    {F : Type*} [Field F] {s rows cols p : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (beta : Fin s → F) (hbeta : ∀ i, beta i ≠ 0)
    (hp : p ≤ rows) (hsize : rows + p ≤ s) (hcols : s ≤ cols)
    (lambda : F) (hlambda : lambda ≠ sigma lambda)
    (herror : ∀ i, alpha i ^ p + lambda ≠ 0) :
    (∀ i, alpha i ^ p + lambda ≠ 0) ∧
      (sixLaneSupportSyndromeMatrix rows cols alpha
        (sixFrobeniusErrorProfile sigma beta
          (fun i => alpha i ^ p + lambda))).rank = rows + p := by
  refine ⟨herror, ?_⟩
  rw [sixFrobenius_pencil_profile sigma alpha hfixed beta p lambda]
  apply sixLanePencilRectangularSyndrome_rank_eq alpha beta hbeta hp hsize hcols
  simpa [sixFrobeniusOrbit] using hlambda
theorem sixFrobeniusPencil_rectangular_counterprofile
    {F : Type*} [Field F] {s rows cols p : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (beta : Fin s → F) (hbeta : ∀ i, beta i ≠ 0)
    (hp : p ≤ rows) (hsize : rows + p ≤ s) (hcols : s ≤ cols)
    (lambda : F) (hlambda : lambda ≠ sigma lambda) :
    (∀ i, alpha i ^ p + lambda ≠ 0) ∧
      (sixLaneSupportSyndromeMatrix rows cols alpha
        (sixFrobeniusErrorProfile sigma beta
          (fun i => alpha i ^ p + lambda))).rank = rows + p := by
  apply sixFrobeniusPencil_rectangular_exactSupport_counterprofile
    sigma alpha hfixed beta hbeta hp hsize hcols lambda hlambda
  intro i
  exact fixed_pow_add_nonfixed_ne_zero sigma (alpha i) (hfixed i)
    p lambda hlambda
noncomputable def pencilPrimitive (F : Type*) [Field F] (p : Nat) (lambda : F) :
    Polynomial F := (Polynomial.X : Polynomial F) ^ p + Polynomial.C lambda
theorem pencilPrimitive_natDegree
    {F : Type*} [Field F] (p : Nat) (lambda : F) :
    (pencilPrimitive F p lambda).natDegree = p := by
  exact Polynomial.natDegree_X_pow_add_C
theorem pencilPrimitive_eval
    {F : Type*} [Field F] (p : Nat) (lambda alpha : F) :
    (pencilPrimitive F p lambda).eval alpha = alpha ^ p + lambda := by
  simp [pencilPrimitive]
theorem pencilPrimitive_map
    {F : Type*} [Field F] (sigma : F →+* F)
    (p : Nat) (lambda : F) :
    (pencilPrimitive F p lambda).map sigma =
      pencilPrimitive F p (sigma lambda) := by
  simp [pencilPrimitive]
theorem pencilPrimitive_sub
    {F : Type*} [Field F] (p : Nat) (lambda mu : F) :
    pencilPrimitive F p lambda - pencilPrimitive F p mu =
      Polynomial.C (lambda - mu) := by
  simp [pencilPrimitive]
theorem pencilPrimitive_isCoprime
    {F : Type*} [Field F] (p : Nat) (lambda mu : F)
    (h : lambda ≠ mu) :
    IsCoprime (pencilPrimitive F p lambda) (pencilPrimitive F p mu) := by
  let a : F := (lambda - mu)⁻¹
  refine ⟨Polynomial.C a, -(Polynomial.C a), ?_⟩
  calc
    Polynomial.C a * pencilPrimitive F p lambda +
        -(Polynomial.C a) * pencilPrimitive F p mu =
      Polynomial.C a *
        (pencilPrimitive F p lambda - pencilPrimitive F p mu) := by
        ring
    _ = Polynomial.C a * Polynomial.C (lambda - mu) := by
      rw [pencilPrimitive_sub]
    _ = 1 := by
      rw [← Polynomial.C_mul]
      simp [a, sub_ne_zero.mpr h]
theorem sixFrobeniusPencil_primitivePair
    {F : Type*} [Field F] (sigma : F →+* F)
    (p : Nat) (lambda : F) (hlambda : lambda ≠ sigma lambda) :
    (pencilPrimitive F p lambda).natDegree = p ∧
      (pencilPrimitive F p (sigma lambda)).natDegree = p ∧
      IsCoprime (pencilPrimitive F p lambda)
        (pencilPrimitive F p (sigma lambda)) := by
  exact ⟨pencilPrimitive_natDegree p lambda,
    pencilPrimitive_natDegree p (sigma lambda),
    pencilPrimitive_isCoprime p lambda (sigma lambda) hlambda⟩
theorem sixFrobeniusPencil_failureRelation
    {F ι : Type*} [Field F] (sigma : F →+* F)
    (alpha : ι → F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (p : Nat) (lambda : F) :
    TwoLaneFailureRelation sigma alpha (fun i ↦ alpha i ^ p + lambda)
      (pencilPrimitive F p lambda)
      (pencilPrimitive F p (sigma lambda)) := by
  intro i
  rw [pencilPrimitive_eval, pencilPrimitive_eval]
  simp only [map_add, map_pow, hfixed]
  ring
theorem benchmark_p10000_failureRelation6401
    {F ι : Type*} [Field F] (sigma : F →+* F)
    (alpha : ι → F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (lambda : F) :
    TwoLaneFailureRelation sigma alpha (fun i ↦ alpha i ^ 10000 + lambda)
        (pencilPrimitive F 10000 lambda)
        (pencilPrimitive F 10000 (sigma lambda)) ∧
      (pencilPrimitive F 10000 lambda).natDegree < keySecondLaneRows6401 ∧
      (pencilPrimitive F 10000 (sigma lambda)).natDegree <
        keySecondLaneRows6401 := by
  refine ⟨sixFrobeniusPencil_failureRelation sigma alpha hfixed 10000 lambda,
    ?_, ?_⟩ <;>
    rw [pencilPrimitive_natDegree] <;>
    norm_num [keySecondLaneRows6401, keyErrors6401, keyFirstLaneRows6401,
      keyRedundancy6401, n6401, ownerDegreeCap6401, bchksErrors6401]
theorem sixLane_counterprofile_parameters6401 :
    let p := 10000
    let delta := 1
    let rows := keyFirstLaneRows6401
    let support := rows + p + delta
    4501 < p ∧ p ≤ rows ∧ support ≤ keyErrors6401 ∧
      support - (rows + p) = delta := by
  norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
    n6401, ownerDegreeCap6401, bchksErrors6401]
theorem benchmark_sixFrobenius_p10000_counterprofile6401
    {F : Type*} [Field F]
    (sigma : F →+* F)
    (alpha : Fin 64283 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (lambda : F) (hlambda : lambda ≠ sigma lambda) :
    (∀ i, alpha i ^ 10000 + lambda ≠ 0) ∧
      (sixLaneSupportSyndromeMatrix keyFirstLaneRows6401 keyErrors6401 alpha
        (sixFrobeniusErrorProfile sigma (syndromeWeight alpha)
          (fun i => alpha i ^ 10000 + lambda))).rank = 64282 := by
  have h := sixFrobeniusPencil_rectangular_counterprofile sigma alpha hfixed
    (syndromeWeight alpha) (fun i ↦ syndromeWeight_ne_zero alpha i)
    (p := 10000) (rows := keyFirstLaneRows6401) (cols := keyErrors6401)
    (by norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
      n6401, ownerDegreeCap6401, bchksErrors6401])
    (by norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
      n6401, ownerDegreeCap6401, bchksErrors6401])
    (by norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
      n6401, ownerDegreeCap6401, bchksErrors6401])
    lambda hlambda
  simpa [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
    n6401, ownerDegreeCap6401, bchksErrors6401] using h
end BCHKSFrobeniusSixLanePencilNoGo6401
end ProximityPrize.SubmissionLower
