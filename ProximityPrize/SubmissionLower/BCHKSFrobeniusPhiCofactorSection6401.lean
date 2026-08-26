import ProximityPrize.SubmissionLower.BCHKSFrobeniusEndpointCommonKernel6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusDeltaOneCofactor6401
import ProximityPrize.SubmissionLower.BCHKSGaoPositiveCharacteristicCore6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusPhiCofactorSection6401
open Polynomial
open scoped BigOperators
open BCHKSFrobeniusDeltaOneCofactor6401
open BCHKSGaoPositiveCharacteristicCore6400
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section AbstractGlobalCramer
variable {F Row : Type*} [Fintype Row] [DecidableEq Row]
def pivotMinor6401 (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) F)
    (row : Fin h → Row) : Matrix (Fin h) (Fin h) F :=
  K.submatrix row Sum.inl
def pivotExtra6401 (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) F)
    (row : Fin h → Row) : Fin h → F :=
  fun i ↦ K (row i) (Sum.inr ())
noncomputable def globalCramerVector6401
    [CommRing F]
    (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) F)
    (row : Fin h → Row) : Fin h ⊕ Unit → F
  | Sum.inl j => (pivotMinor6401 h K row).cramer
      (pivotExtra6401 h K row) j
  | Sum.inr _ => -(pivotMinor6401 h K row).det
theorem selectedRows_mulVec_globalCramerVector6401
    [CommRing F]
    (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) F)
    (row : Fin h → Row) :
    (K.submatrix row id).mulVec (globalCramerVector6401 h K row) = 0 := by
  classical
  funext i
  have hcr := congrFun (Matrix.mulVec_cramer
    (pivotMinor6401 h K row) (pivotExtra6401 h K row)) i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix, id_eq,
    Pi.zero_apply, Fintype.sum_sum_type, globalCramerVector6401,
    Finset.univ_unique, Finset.sum_singleton]
  change (pivotMinor6401 h K row).mulVec
      ((pivotMinor6401 h K row).cramer (pivotExtra6401 h K row)) i +
        K (row i) (Sum.inr ()) * (-(pivotMinor6401 h K row).det) = 0
  rw [hcr]
  simp only [pivotExtra6401, Pi.smul_apply, smul_eq_mul]
  ring
theorem mulVec_globalCramerVector_eq_zero_of_rank_le6401
    [Field F]
    (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) F)
    (row : Fin h → Row) (hrow : Function.Injective row)
    (hrank : K.rank ≤ h)
    (hdet : (pivotMinor6401 h K row).det ≠ 0) :
    K.mulVec (globalCramerVector6401 h K row) = 0 := by
  classical
  let A := pivotMinor6401 h K row
  let selected : Fin h → (Fin h ⊕ Unit → F) :=
    fun i ↦ K.row (row i)
  let restrictPivot : (Fin h ⊕ Unit → F) →ₗ[F] (Fin h → F) :=
    LinearMap.funLeft F F Sum.inl
  have hArows : LinearIndependent F A.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hrestrict : (fun i ↦ restrictPivot (selected i)) = A.row := by
    funext i j
    rfl
  have hselected : LinearIndependent F selected := by
    apply LinearIndependent.of_comp restrictPivot
    change LinearIndependent F (fun i ↦ restrictPivot (selected i))
    rw [hrestrict]
    exact hArows
  let S : Submodule F (Fin h ⊕ Unit → F) :=
    Submodule.span F (Set.range selected)
  let T : Submodule F (Fin h ⊕ Unit → F) :=
    Submodule.span F (Set.range K.row)
  have hST : S ≤ T := by
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨row i, rfl⟩
  have hSdim : Module.finrank F S = h := by
    have hs := linearIndependent_iff_card_eq_finrank_span.mp hselected
    simpa only [S, Set.finrank, Fintype.card_fin] using hs.symm
  have hTdim : Module.finrank F T ≤ h := by
    rw [← K.rank_eq_finrank_span_row]
    exact hrank
  have hSTeq : S = T := by
    apply Submodule.eq_of_le_of_finrank_le hST
    rw [hSdim]
    exact hTdim
  let ell : (Fin h ⊕ Unit → F) →ₗ[F] F :=
    { toFun := fun x ↦ dotProduct x (globalCramerVector6401 h K row)
      map_add' := by
        intro x y
        simp [dotProduct, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [RingHom.id_apply]
        ring }
  have hselectedKer : ∀ i, selected i ∈ LinearMap.ker ell := by
    intro i
    rw [LinearMap.mem_ker]
    have hs := congrFun (selectedRows_mulVec_globalCramerVector6401
      h K row) i
    exact hs
  have hSker : S ≤ LinearMap.ker ell := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hselectedKer i
  funext i
  have hrowT : K.row i ∈ T := Submodule.subset_span ⟨i, rfl⟩
  have hrowS : K.row i ∈ S := by rw [hSTeq]; exact hrowT
  have hzero := LinearMap.mem_ker.mp (hSker hrowS)
  exact hzero
theorem globalCramerVector_ne_zero6401
    [CommRing F]
    (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) F)
    (row : Fin h → Row)
    (hdet : (pivotMinor6401 h K row).det ≠ 0) :
    globalCramerVector6401 h K row ≠ 0 := by
  intro hz
  have hlast := congrFun hz (Sum.inr ())
  exact hdet (neg_eq_zero.mp (by
    simpa [globalCramerVector6401] using hlast))
theorem map_pivotMinor6401
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) :
    (pivotMinor6401 h K row).map f =
      pivotMinor6401 h (K.map f) row := by
  rfl
theorem map_pivotExtra6401
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) :
    (fun i ↦ f (pivotExtra6401 h K row i)) =
      pivotExtra6401 h (K.map f) row := by
  rfl
theorem map_pivotMinor_det6401
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) :
    f (pivotMinor6401 h K row).det =
      (pivotMinor6401 h (K.map f) row).det := by
  rw [RingHom.map_det]
  exact congrArg Matrix.det (map_pivotMinor6401 f h K row)
theorem map_cramer6401
    {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I]
    (f : R →+* S) (A : Matrix I I R) (b : I → R) (j : I) :
    f (A.cramer b j) = (A.map f).cramer (fun i ↦ f (b i)) j := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, RingHom.map_det,
    show f.mapMatrix (A.updateCol j b) =
      (A.map f).updateCol j (fun i ↦ f (b i)) by
        change (A.updateCol j b).map f = _
        rw [Matrix.map_updateCol]
        rfl]
theorem map_globalCramerVector6401
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) :
    (fun c ↦ f (globalCramerVector6401 h K row c)) =
      globalCramerVector6401 h (K.map f) row := by
  funext c
  cases c with
  | inl j =>
      simp only [globalCramerVector6401]
      rw [map_cramer6401]
      simpa only [map_pivotMinor6401, map_pivotExtra6401]
  | inr u =>
      cases u
      simp only [globalCramerVector6401, map_neg]
      rw [map_pivotMinor_det6401]
theorem mulVec_globalCramerVector_eq_zero_of_fractionRank_le6401
    {R : Type*} [CommRing R] [IsDomain R]
    (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) (hrow : Function.Injective row)
    (hrank : (K.map (algebraMap R (FractionRing R))).rank ≤ h)
    (hdet : (pivotMinor6401 h K row).det ≠ 0) :
    K.mulVec (globalCramerVector6401 h K row) = 0 := by
  classical
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hf : Function.Injective f := IsFractionRing.injective R (FractionRing R)
  have hdetMap :
      (pivotMinor6401 h (K.map f) row).det ≠ 0 := by
    have hm : f (pivotMinor6401 h K row).det ≠ 0 := by
      simpa only [map_zero] using hf.ne hdet
    rwa [map_pivotMinor_det6401] at hm
  have hzero := mulVec_globalCramerVector_eq_zero_of_rank_le6401
    h (K.map f) row hrow hrank hdetMap
  funext i
  apply hf
  have hi := congrFun hzero i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, map_zero] at hi ⊢
  rw [map_sum]
  simp only [map_mul]
  calc
    (∑ x, f (K i x) * f (globalCramerVector6401 h K row x)) =
        ∑ x, (K.map f) i x *
          globalCramerVector6401 h (K.map f) row x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← congrFun (map_globalCramerVector6401 f h K row) x]
      rfl
    _ = 0 := hi
theorem globalCramerVector_natDegree_le6401
    {R : Type*} [CommRing R]
    (h d : Nat) (K : Matrix Row (Fin h ⊕ Unit) R[X])
    (row : Fin h → Row)
    (hentry : ∀ i c, (K (row i) c).natDegree ≤ d)
    (c : Fin h ⊕ Unit) :
    (globalCramerVector6401 h K row c).natDegree ≤ h * d := by
  classical
  cases c with
  | inl j =>
      simp only [globalCramerVector6401, Matrix.cramer_apply]
      calc
        ((pivotMinor6401 h K row).updateCol j
            (pivotExtra6401 h K row)).det.natDegree
            ≤ ∑ _ : Fin h, d := by
          apply natDegree_det_le_sum_rowCaps_commRing
          intro i k
          by_cases hk : k = j
          · subst k
            simpa [pivotExtra6401] using hentry i (Sum.inr ())
          · simpa [pivotMinor6401, Matrix.updateCol, hk] using
              hentry i (Sum.inl k)
        _ = h * d := by simp
  | inr u =>
      cases u
      simp only [globalCramerVector6401, Polynomial.natDegree_neg]
      calc
        (pivotMinor6401 h K row).det.natDegree
            ≤ ∑ _ : Fin h, d := by
          apply natDegree_det_le_sum_rowCaps_commRing
          intro i j
          simpa [pivotMinor6401] using hentry i (Sum.inl j)
        _ = h * d := by simp
theorem globalCramerVector_degreeX_le6401
    {Kfield : Type*} [Field Kfield]
    (h d : Nat)
    (K : Matrix Row (Fin h ⊕ Unit)
      (Polynomial (Polynomial Kfield)))
    (row : Fin h → Row)
    (hentry : ∀ i c,
      Polynomial.Bivariate.degreeX (K (row i) c) ≤ d)
    (c : Fin h ⊕ Unit) :
    Polynomial.Bivariate.degreeX
        (globalCramerVector6401 h K row c) ≤ h * d := by
  classical
  cases c with
  | inl j =>
      simp only [globalCramerVector6401, Matrix.cramer_apply]
      calc
        Polynomial.Bivariate.degreeX
            ((pivotMinor6401 h K row).updateCol j
              (pivotExtra6401 h K row)).det
            ≤ ∑ _ : Fin h, d := by
          apply coefficientDegree_det_le_sum_rowCaps
          intro i k
          by_cases hk : k = j
          · subst k
            simpa [pivotExtra6401] using hentry i (Sum.inr ())
          · simpa [pivotMinor6401, Matrix.updateCol, hk] using
              hentry i (Sum.inl k)
        _ = h * d := by simp
  | inr u =>
      cases u
      simp only [globalCramerVector6401, degreeX_neg]
      calc
        Polynomial.Bivariate.degreeX (pivotMinor6401 h K row).det
            ≤ ∑ _ : Fin h, d := by
          apply coefficientDegree_det_le_sum_rowCaps
          intro i j
          simpa [pivotMinor6401] using hentry i (Sum.inl j)
        _ = h * d := by simp
theorem globalCramerVector_Phi_bidegree6401
    {Kfield : Type*} [Field Kfield]
    (h : Nat)
    (K : Matrix Row (Fin h ⊕ Unit)
      (Polynomial (Polynomial Kfield)))
    (row : Fin h → Row)
    (hW : ∀ i c, (K (row i) c).natDegree ≤ 1)
    (hZ : ∀ i c,
      Polynomial.Bivariate.degreeX (K (row i) c) ≤ 65536)
    (c : Fin h ⊕ Unit) :
    (globalCramerVector6401 h K row c).natDegree ≤ h ∧
      Polynomial.Bivariate.degreeX
        (globalCramerVector6401 h K row c) ≤ h * 65536 := by
  constructor
  · simpa using globalCramerVector_natDegree_le6401 h 1 K row hW c
  · exact globalCramerVector_degreeX_le6401 h 65536 K row hZ c
noncomputable def embeddedCramerPolynomial6401
    {R : Type*} [CommRing R]
    (shifts h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) (col : Fin h ⊕ Unit ↪ Fin shifts) : R[X] :=
  ∑ c, Polynomial.monomial (col c).1
    (globalCramerVector6401 h K row c)
theorem embeddedCramerPolynomial_coeff6401
    {R : Type*} [CommRing R]
    (shifts h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) (col : Fin h ⊕ Unit ↪ Fin shifts)
    (c : Fin h ⊕ Unit) :
    (embeddedCramerPolynomial6401 shifts h K row col).coeff (col c).1 =
      globalCramerVector6401 h K row c := by
  classical
  simp only [embeddedCramerPolynomial6401]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Fintype.sum_eq_single c]
  · simp
  · intro d hdc
    rw [if_neg]
    intro heq
    exact hdc (col.injective (Fin.ext heq))
theorem embeddedCramerPolynomial_degree_lt6401
    {R : Type*} [CommRing R]
    (shifts h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) (col : Fin h ⊕ Unit ↪ Fin shifts) :
    (embeddedCramerPolynomial6401 shifts h K row col).degree < shifts := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  classical
  simp only [embeddedCramerPolynomial6401]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro c hc
  rw [if_neg]
  intro heq
  have hlt := (col c).isLt
  omega
theorem embeddedCramerPolynomial_ne_zero6401
    {R : Type*} [CommRing R]
    (shifts h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) (col : Fin h ⊕ Unit ↪ Fin shifts)
    (hdet : (pivotMinor6401 h K row).det ≠ 0) :
    embeddedCramerPolynomial6401 shifts h K row col ≠ 0 := by
  intro hz
  have hc := embeddedCramerPolynomial_coeff6401
    shifts h K row col (Sum.inr ())
  rw [hz, Polynomial.coeff_zero] at hc
  exact hdet (neg_eq_zero.mp (by
    simpa [globalCramerVector6401] using hc.symm))
theorem embeddedCramerPolynomial_natDegree_lt6401
    {R : Type*} [CommRing R]
    (shifts h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row) (col : Fin h ⊕ Unit ↪ Fin shifts)
    (hdet : (pivotMinor6401 h K row).det ≠ 0) :
    (embeddedCramerPolynomial6401 shifts h K row col).natDegree < shifts := by
  rw [Polynomial.natDegree_lt_iff_degree_lt
    (embeddedCramerPolynomial_ne_zero6401 shifts h K row col hdet)]
  exact embeddedCramerPolynomial_degree_lt6401 shifts h K row col
theorem PhiCofactor_shiftBudget6401
    {R : Type*} [CommRing R]
    (h : Nat) (K : Matrix Row (Fin h ⊕ Unit) R)
    (row : Fin h → Row)
    (col : Fin h ⊕ Unit ↪ Fin 11254)
    (hdet : (pivotMinor6401 h K row).det ≠ 0)
    (B : R[X]) (hB : B.natDegree ≤ 65536) :
    (embeddedCramerPolynomial6401 11254 h K row col).natDegree ≤ 11253 ∧
      (embeddedCramerPolynomial6401 11254 h K row col * B).natDegree <
        76790 := by
  have hRlt := embeddedCramerPolynomial_natDegree_lt6401
    11254 h K row col hdet
  constructor
  · omega
  · apply lt_of_le_of_lt Polynomial.natDegree_mul_le
    omega
end AbstractGlobalCramer
end BCHKSFrobeniusPhiCofactorSection6401
end ProximityPrize.SubmissionLower
