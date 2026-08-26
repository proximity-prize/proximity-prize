import ProximityPrize.SubmissionLower.BCHKSFrobeniusGenericRankFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusGraphInjectivity6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTwoFrobeniusModuleAudit6401
noncomputable def frobeniusGraphEval
    {F : Type*} [Field F] (q : Nat) (P : F[X][X]) : F[X] :=
  Polynomial.eval₂ (RingHom.id F[X]) (Polynomial.X ^ q) P
theorem frobeniusGraphEval_eq_zero_imp_eq_zero
    {F : Type*} [Field F] (q : Nat) (P : F[X][X])
    (hcoeff : ∀ j, (P.coeff j).natDegree < q)
    (hzero : frobeniusGraphEval q P = 0) : P = 0 := by
  by_contra hP
  let J := P.natDegree
  let a := P.coeff J
  let N := a.natDegree + q * J
  have ha : a ≠ 0 := by
    dsimp [a, J]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  have hJmem : J ∈ Finset.range (P.natDegree + 1) := by
    simp [J]
  have hlow : ∀ j ∈ Finset.range (P.natDegree + 1), j ≠ J →
      ((P.coeff j) * Polynomial.X ^ (q * j)).coeff N = 0 := by
    intro j hj hjne
    have hjlt : j < J := by
      simp only [Finset.mem_range] at hj
      dsimp [J] at hjne ⊢
      omega
    by_cases hcj : P.coeff j = 0
    · simp [hcj]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Polynomial.natDegree_mul_X_pow (q * j) hcj]
      have hd := hcoeff j
      have hj1 : j + 1 ≤ J := by omega
      dsimp [N]
      calc
        (P.coeff j).natDegree + q * j < q + q * j :=
          Nat.add_lt_add_right hd (q * j)
        _ = q * (j + 1) := by ring
        _ ≤ q * J := Nat.mul_le_mul_left q hj1
        _ ≤ a.natDegree + q * J := Nat.le_add_left _ _
  have hmain : ((P.coeff J) * Polynomial.X ^ (q * J)).coeff N =
      a.leadingCoeff := by
    dsimp [N, a]
    rw [Polynomial.coeff_mul_X_pow, Polynomial.coeff_natDegree]
  have hevalcoeff : (frobeniusGraphEval q P).coeff N =
      a.leadingCoeff := by
    rw [frobeniusGraphEval, Polynomial.eval₂_eq_sum_range]
    simp only [← pow_mul, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single J]
    · exact hmain
    · intro j hj hjne
      exact hlow j hj hjne
    · intro hnot
      exact (hnot hJmem).elim
  rw [hzero, Polynomial.coeff_zero] at hevalcoeff
  exact (Polynomial.leadingCoeff_ne_zero.mpr ha) hevalcoeff.symm
theorem frobeniusGraphEval_eq_zero_iff
    {F : Type*} [Field F] (q : Nat) (P : F[X][X])
    (hcoeff : ∀ j, (P.coeff j).natDegree < q) :
    frobeniusGraphEval q P = 0 ↔ P = 0 := by
  constructor
  · exact frobeniusGraphEval_eq_zero_imp_eq_zero q P hcoeff
  · rintro rfl
    simp [frobeniusGraphEval]
theorem benchmark_rows_lt_frobeniusBase6401 :
    keyFirstLaneRows6401 < q6401 ∧ keyErrors6401 < q6401 := by
  native_decide
noncomputable def frobeniusGraphRingHom
    {F : Type*} [Field F] (q : Nat) : F[X][X] →+* F[X] :=
  Polynomial.eval₂RingHom (RingHom.id F[X]) (Polynomial.X ^ q)
noncomputable def frobeniusSyndromeW
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) (j : Nat) : F[X][X] :=
  (frobeniusSyndromeZ sigma 1 alpha u₀ u₁ j).map Polynomial.C
theorem frobeniusSyndromeW_graph
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (q : Nat) (alpha u₀ u₁ : iota → F) (j : Nat) :
    frobeniusGraphRingHom q (frobeniusSyndromeW sigma alpha u₀ u₁ j) =
      frobeniusSyndromeZ sigma q alpha u₀ u₁ j := by
  classical
  simp [frobeniusGraphRingHom, frobeniusSyndromeW,
    frobeniusSyndromeZ, Polynomial.C_mul_X_pow_eq_monomial]
noncomputable def fullTwoLaneKeyMatrixZW6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) :
    Matrix FullTwoLaneKeyRow6401 (Fin keyErrors6401) F[X][X]
  | Sum.inl a, col => Polynomial.C
      (affineSyndromeZ alpha u₀ u₁ (a.1 + col.1))
  | Sum.inr a, col =>
      frobeniusSyndromeW sigma alpha u₀ u₁ (a.1 + col.1)
theorem fullTwoLaneKeyMatrixZW_graph6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) :
    (fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁).map
        (frobeniusGraphRingHom q6401) =
      fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁ := by
  apply Matrix.ext
  intro row col
  cases row with
  | inl a =>
      simp [fullTwoLaneKeyMatrixZW6401, frobeniusGraphRingHom,
        fullTwoLaneKeyMatrixZ6401]
  | inr a =>
      exact frobeniusSyndromeW_graph sigma q6401 alpha u₀ u₁ _
def BivariateCoeffDegreeLE
    {F : Type*} [Field F] (P : F[X][X]) (D : Nat) : Prop :=
  ∀ j, (P.coeff j).natDegree ≤ D
theorem BivariateCoeffDegreeLE_add
    {F : Type*} [Field F] {P Q : F[X][X]} {D E : Nat}
    (hP : BivariateCoeffDegreeLE P D)
    (hQ : BivariateCoeffDegreeLE Q E) :
    BivariateCoeffDegreeLE (P + Q) (max D E) := by
  intro j
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le
    ((hP j).trans (Nat.le_max_left _ _))
    ((hQ j).trans (Nat.le_max_right _ _)))
theorem BivariateCoeffDegreeLE_mul
    {F : Type*} [Field F] {P Q : F[X][X]} {D E : Nat}
    (hP : BivariateCoeffDegreeLE P D)
    (hQ : BivariateCoeffDegreeLE Q E) :
    BivariateCoeffDegreeLE (P * Q) (D + E) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (hP ij.1) (hQ ij.2))
theorem BivariateCoeffDegreeLE_smul
    {F : Type*} [Field F] {P : F[X][X]} {D : Nat}
    (s : ℤˣ) (hP : BivariateCoeffDegreeLE P D) :
    BivariateCoeffDegreeLE (s • P) D := by
  intro j
  rw [Polynomial.coeff_smul]
  exact (Polynomial.natDegree_smul_le _ _).trans (hP j)
theorem BivariateCoeffDegreeLE_sum
    {F I : Type*} [Field F] [Fintype I]
    (f : I → F[X][X]) (D : Nat)
    (hf : ∀ i, BivariateCoeffDegreeLE (f i) D) :
    BivariateCoeffDegreeLE (∑ i, f i) D := by
  intro j
  simp only [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact hf i j
theorem BivariateCoeffDegreeLE_prod
    {F I : Type*} [Field F] [DecidableEq I]
    (s : Finset I) (f : I → F[X][X]) (cap : I → Nat)
    (hf : ∀ i ∈ s, BivariateCoeffDegreeLE (f i) (cap i)) :
    BivariateCoeffDegreeLE (∏ i ∈ s, f i) (∑ i ∈ s, cap i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro j
      simp only [Finset.prod_empty, Finset.sum_empty]
      rw [Polynomial.coeff_one]
      split_ifs <;> simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      apply BivariateCoeffDegreeLE_mul
      · exact hf a (Finset.mem_insert_self _ _)
      · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
theorem bivariateCoeffDegree_det_le_sum_rowCaps
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (M : Matrix I I F[X][X]) (rowCap : I → Nat)
    (hentry : ∀ i j, BivariateCoeffDegreeLE (M i j) (rowCap i)) :
    BivariateCoeffDegreeLE M.det (∑ i, rowCap i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply BivariateCoeffDegreeLE_sum
  intro perm
  apply BivariateCoeffDegreeLE_smul
  apply BivariateCoeffDegreeLE_prod
  intro i hi
  simpa using hentry i (perm i)
def independentZRowCap6401 : FullTwoLaneKeyRow6401 → Nat
  | Sum.inl _ => 1
  | Sum.inr _ => 0
theorem fullTwoLaneKeyMatrixZW_entry_coeffDegree6401
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F) :
    ∀ row col, BivariateCoeffDegreeLE
      (fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁ row col)
      (independentZRowCap6401 row) := by
  intro row col
  cases row with
  | inl a =>
      intro j
      by_cases hj : j = 0
      · subst j
        simpa [fullTwoLaneKeyMatrixZW6401, independentZRowCap6401] using
          affineSyndromeZ_natDegree_le_one alpha u₀ u₁ (a.1 + col.1)
      · rw [show fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁
            (Sum.inl a) col = Polynomial.C
              (affineSyndromeZ alpha u₀ u₁ (a.1 + col.1)) by rfl,
          Polynomial.coeff_C, if_neg hj]
        simp
  | inr a =>
      intro j
      by_cases hj₀ : j = 0
      · subst j
        simp [fullTwoLaneKeyMatrixZW6401, independentZRowCap6401,
          frobeniusSyndromeW, frobeniusSyndromeZ]
      · by_cases hj₁ : j = 1
        · subst j
          simp [fullTwoLaneKeyMatrixZW6401, independentZRowCap6401,
            frobeniusSyndromeW, frobeniusSyndromeZ]
        · have h₁j : 1 ≠ j := Ne.symm hj₁
          simp [fullTwoLaneKeyMatrixZW6401, independentZRowCap6401,
            frobeniusSyndromeW, frobeniusSyndromeZ,
            Polynomial.coeff_C, Polynomial.coeff_monomial, hj₀, h₁j]
theorem fullTwoLane_minor_graph6401
    {F iota I : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    [Fintype I] [DecidableEq I]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F)
    (rows : I → FullTwoLaneKeyRow6401) (cols : I → Fin keyErrors6401) :
    frobeniusGraphRingHom q6401
      ((fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁).submatrix
        rows cols).det =
      ((fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).submatrix
        rows cols).det := by
  rw [RingHom.map_det]
  congr 1
  exact congrArg (fun M => M.submatrix rows cols)
    (fullTwoLaneKeyMatrixZW_graph6401 sigma alpha u₀ u₁)
theorem fullTwoLane_independentMinor_eq_zero_of_graphMinor_eq_zero6401
    {F iota I : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    [Fintype I] [DecidableEq I]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F)
    (rows : I → FullTwoLaneKeyRow6401) (cols : I → Fin keyErrors6401)
    (hcoeff : ∀ j,
      (((fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁).submatrix
        rows cols).det.coeff j).natDegree < q6401)
    (hzero :
      ((fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).submatrix
        rows cols).det = 0) :
    ((fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁).submatrix
      rows cols).det = 0 := by
  apply frobeniusGraphEval_eq_zero_imp_eq_zero q6401 _ hcoeff
  change frobeniusGraphRingHom q6401
    ((fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁).submatrix
      rows cols).det = 0
  rw [fullTwoLane_minor_graph6401 sigma alpha u₀ u₁ rows cols, hzero]
theorem fullTwoLane_independentMinor_eq_zero_automatic6401
    {F iota I : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    [Fintype I] [DecidableEq I]
    (sigma : F →+* F) (alpha u₀ u₁ : iota → F)
    (rows : I → FullTwoLaneKeyRow6401) (cols : I → Fin keyErrors6401)
    (hsize : Fintype.card I ≤ keyErrors6401)
    (hzero :
      ((fullTwoLaneKeyMatrixZ6401 sigma alpha u₀ u₁).submatrix
        rows cols).det = 0) :
    ((fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁).submatrix
      rows cols).det = 0 := by
  apply fullTwoLane_independentMinor_eq_zero_of_graphMinor_eq_zero6401
    sigma alpha u₀ u₁ rows cols
  · let cap : I → Nat := fun i => independentZRowCap6401 (rows i)
    have hdet := bivariateCoeffDegree_det_le_sum_rowCaps
      ((fullTwoLaneKeyMatrixZW6401 sigma alpha u₀ u₁).submatrix
        rows cols) cap (by
          intro i j
          exact fullTwoLaneKeyMatrixZW_entry_coeffDegree6401
            sigma alpha u₀ u₁ (rows i) (cols j))
    have hcap : (∑ i, cap i) < q6401 := by
      calc
        (∑ i, cap i) ≤ ∑ _i : I, 1 := by
          apply Finset.sum_le_sum
          intro i hi
          cases hrow : rows i <;>
            simp [cap, hrow, independentZRowCap6401]
        _ = Fintype.card I := by simp
        _ ≤ keyErrors6401 := hsize
        _ < q6401 := benchmark_rows_lt_frobeniusBase6401.2
    exact fun j => (hdet j).trans_lt hcap
  · exact hzero
theorem finrank_sup_le_add_of_anchor
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (B T U : Submodule K V) (m h : Nat)
    (hBT : B ≤ T)
    (hBdim : Module.finrank K B = m)
    (hcross : Module.finrank K (U ⊔ B : Submodule K V) ≤ m + h) :
    Module.finrank K (T ⊔ U : Submodule K V) ≤
      Module.finrank K T + h := by
  have hUB := Submodule.finrank_sup_add_finrank_inf_eq U B
  have hTU := Submodule.finrank_sup_add_finrank_inf_eq T U
  have hinf : U ⊓ B ≤ T ⊓ U := by
    intro x hx
    exact ⟨hBT hx.2, hx.1⟩
  have hdimInf : Module.finrank K (U ⊓ B : Submodule K V) ≤
      Module.finrank K (T ⊓ U : Submodule K V) :=
    Submodule.finrank_mono hinf
  omega
theorem fourFibres_finrank_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (R₀ R₁ S₀ S₁ : Submodule K V) (m h : Nat)
    (hR₀ : Module.finrank K R₀ = m)
    (hS₀ : Module.finrank K S₀ = m)
    (hcross00 : Module.finrank K (R₀ ⊔ S₀ : Submodule K V) ≤ m + h)
    (hcross10 : Module.finrank K (R₁ ⊔ S₀ : Submodule K V) ≤ m + h)
    (hcross01 : Module.finrank K (R₀ ⊔ S₁ : Submodule K V) ≤ m + h) :
    Module.finrank K
      (R₀ ⊔ S₀ ⊔ R₁ ⊔ S₁ : Submodule K V) ≤ m + 3 * h := by
  have h₁ := finrank_sup_le_add_of_anchor S₀ (R₀ ⊔ S₀) R₁ m h
    le_sup_right hS₀ hcross10
  have h₂ := finrank_sup_le_add_of_anchor R₀
    ((R₀ ⊔ S₀) ⊔ R₁) S₁ m h
    (le_trans le_sup_left le_sup_left) hR₀ (by
      rw [sup_comm]
      exact hcross01)
  omega
theorem twoFibres_oneAnchor_finrank_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (R₀ R₁ S : Submodule K V) (m h : Nat)
    (hR₀ : Module.finrank K R₀ = m)
    (hR₁ : Module.finrank K R₁ = m)
    (hS : Module.finrank K S = m)
    (hcross0 : Module.finrank K (R₀ ⊔ S : Submodule K V) ≤ m + h)
    (hcross1 : Module.finrank K (R₁ ⊔ S : Submodule K V) ≤ m + h) :
    Module.finrank K (R₀ ⊔ R₁ : Submodule K V) ≤ m + 2 * h := by
  have hdim₀ := Submodule.finrank_sup_add_finrank_inf_eq R₀ S
  have hdim₁ := Submodule.finrank_sup_add_finrank_inf_eq R₁ S
  have hinter₀ : m - h ≤ Module.finrank K (R₀ ⊓ S : Submodule K V) := by
    omega
  have hinter₁ : m - h ≤ Module.finrank K (R₁ ⊓ S : Submodule K V) := by
    omega
  have hsupS : (R₀ ⊓ S) ⊔ (R₁ ⊓ S) ≤ S := by
    exact sup_le inf_le_right inf_le_right
  have hsupSdim : Module.finrank K
      ((R₀ ⊓ S) ⊔ (R₁ ⊓ S) : Submodule K V) ≤ m := by
    rw [← hS]
    exact Submodule.finrank_mono hsupS
  have hdimIntersections := Submodule.finrank_sup_add_finrank_inf_eq
    (R₀ ⊓ S) (R₁ ⊓ S)
  have htriple : m - 2 * h ≤ Module.finrank K
      ((R₀ ⊓ S) ⊓ (R₁ ⊓ S) : Submodule K V) := by
    omega
  have htriple_le : (R₀ ⊓ S) ⊓ (R₁ ⊓ S) ≤ R₀ ⊓ R₁ := by
    intro x hx
    exact ⟨hx.1.1, hx.2.1⟩
  have hRinter : m - 2 * h ≤
      Module.finrank K (R₀ ⊓ R₁ : Submodule K V) :=
    htriple.trans (Submodule.finrank_mono htriple_le)
  have hdimR := Submodule.finrank_sup_add_finrank_inf_eq R₀ R₁
  omega
end BCHKSFrobeniusGraphInjectivity6401
end ProximityPrize.SubmissionLower
