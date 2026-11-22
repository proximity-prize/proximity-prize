import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.Fast051
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_6
open K1 Polynomial Matrix
open FrobeniusLocator
def c1 : Prop :=
  ∀ (F : Type) [Field F] (h L s : ℕ) (P : Fin 2 → F[X][X]),
    h + s = L → 0 < s →
    (∀ b, (P b).natDegree ≤ h) →
    PrimitiveVector.IsPrimitive (pairCoordinates P h) →
    PrimitiveVector.IsPrimitive (maximalMinors (shifts P L s)) ∧
    ∃ H : ℕ, (∀ b j, ((P b).coeff j).natDegree ≤ H) ∧
      ∃ rows : Fin s → (Fin 2 × Fin L),
        (maximalMinors (shifts P L s) rows).natDegree = s * H
def c2 : Prop :=
  ∀ (F : Type) [Field F] (L w s p : ℕ)
    (M : Matrix (Fin 2 × Fin L) (Fin w) F[X]) (W : Matrix (Fin 2 × Fin L) (Fin s) F[X]),
    1 ≤ p →
    GenericLayer.genericRank M + s = 2 * L →
    W.transpose * M = 0 →
    (∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p) →
    PrimitiveVector.IsPrimitive (maximalMinors W) →
    ∀ rows : Fin s → (Fin 2 × Fin L), (maximalMinors W rows).natDegree ≤ L * (p + 1) - s
theorem of_children (h1 : c1) (h2 : c2) : K1.c6 := by
  intro u front T R moving saturated Γ bad normal
  let P (b : Fin 2) : Bivar := Principal.assemble (fun j => R.coefficients (b, j))
  let s := 49193 - T.height
  have hsDef : s = 49193 - T.height := rfl
  have hP : ∀ b, (P b).natDegree ≤ T.height := R.x_degree
  have hBalance : 49193 + T.height + nullity u = 81880 ∧ T.height ≤ 32680 ∧ T.height < 49193 :=
    Strata.native_minimal_relation_degree (nullity u) T.a T.b T.c
      T.top T.degreeSum T.nullitySum (by have := front.1; omega)
  have hSum : T.height + s = 49193 := by omega
  have hs : 16513 ≤ s := by omega
  have hRank : GenericLayer.genericRank (twoBlock u) + s = 2 * 49193 := by
    change stackRank u + s = _
    rw [K1.actual_stackRank u]
    omega
  have hCoordinates : pairCoordinates P T.height = R.coefficients := by
    funext i
    exact Principal.assemble_coeff (fun j => R.coefficients (i.1, j)) i.2
  have hPrim : PrimitiveVector.IsPrimitive (pairCoordinates P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hKernel := certificate_shifts_annihilate R s hSum
  obtain ⟨hMinors, H, hH, rows, hRows⟩ :=
    h1 K T.height 49193 s P hSum (by omega) hP hPrim
  have hBound := h2 K 49193 81880 s p (twoBlock u) (shifts P 49193 s)
    (by norm_num [Native.p]) hRank hKernel
    (stacked_entry_natDegree p node (u 0) (u 1) 49193 81879) hMinors rows
  rw [hRows] at hBound
  have hProduct : 16513 * H ≤ s * H := Nat.mul_le_mul_right H hs
  have hCeiling : 49193 * (p + 1) = 104815841607762 := by norm_num [Native.p]
  have hCap : H ≤ 6347474207 := by omega
  apply normal_growth_count R _ moving saturated Γ bad normal
  intro i
  rw [← hCoordinates]
  exact (hH i.1 i.2.val).trans hCap
end K1_6
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_6_1
noncomputable section
open Polynomial Matrix FrobeniusLocator K1_6
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
theorem shift_minors_height {F : Type} [Field F]
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
theorem proof : K1_6.c1 := by
  intro F inst h L s P hL _ hdegree hprimitive
  subst L
  exact ⟨primitive_shift_minors P h s hdegree hprimitive,
    shift_minors_height P h s hdegree hprimitive⟩
end
end K1_6_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_6_2
open Polynomial Matrix
open FrobeniusLocator
open scoped BigOperators
theorem proof : K1_6.c2 := by
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
      (V.submatrix I id).det = K1_6.maximalMinors W (e ∘ I) := rfl
  have hminor' (J : Fin s → (Fin 2 × Fin L)) :
      (V.submatrix (e.symm ∘ J) id).det = K1_6.maximalMinors W J := by
    rw [hminor]
    congr 1
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have hprimV : PrimitiveVector.IsPrimitive
      (fun I : Fin s → (Fin r ⊕ Fin s) => (V.submatrix I id).det) := by
    have hrange : Set.range (fun I : Fin s → (Fin r ⊕ Fin s) => (V.submatrix I id).det) =
        Set.range (K1_6.maximalMinors W) := by
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
end K1_6_2
end
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000
open private activeNatCount_eq sumRange_prefix sumRange_congr sumToCap_eq innerSlice_eq from ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
def budgetGRamp₁ (x : ℕ) : ℕ := x * (x+1) / 2
def budgetGRamp₂ (x : ℕ) : ℕ := ((x+1)/2) * (x/2+1)
theorem budgetGRamp₁Step (x : ℕ) :
    budgetGRamp₁ x = x + budgetGRamp₁ (x-1) := by
  cases x with
  | zero => rfl
  | succ x =>
    change (x+1)*(x+1+1)/2 = (x+1) + x*(x+1)/2
    rw [show (x+1)*(x+1+1) = x*(x+1) + 2*(x+1) by ring]
    omega
theorem budgetGRamp₂Step (x : ℕ) :
    budgetGRamp₂ x = x + budgetGRamp₂ (x-2) := by
  obtain _ | _ | x := x
  · rfl
  · rfl
  · change ((x+2+1)/2) * ((x+2)/2+1) = x+2 + ((x+1)/2)*(x/2+1)
    rw [show (x+2+1)/2 = (x+1)/2+1 by omega, show (x+2)/2 = x/2+1 by omega]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
private theorem sumStep (f : ℕ → ℕ) (n a b : ℕ)
    (ha : sumRange n f = a) (hb : f n = b) :
    sumRange (n + 1) f = a + b :=
  (show sumRange (n + 1) f = sumRange n f + f n from rfl).trans (congrArg₂ Nat.add ha hb)
private def gradeFrom (i : ℕ) : ℕ := fastGrade (i + 90)
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
theorem jetIndex_formula (m : Fin 4 →₀ ℕ) :
    m.weight jetIndex = m 1 + 2 * m 2 + 3 * m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, jetIndex, Nat.mul_comm]
theorem targetOrder_formula (m : Fin 4 →₀ ℕ) :
    m.weight targetOrder = 3 * m 0 + m 2 + 2 * m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, targetOrder, Nat.mul_comm]
theorem degree_formula (m : Fin 4 →₀ ℕ) :
    m.degree = m 0 + m 1 + m 2 + m 3 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_four]
theorem sumRange_eq_fin (n : ℕ) (f : ℕ → ℕ) : sumRange n f = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range f, sumRange_eq_sum]
theorem bandSpace_finite (d : ℕ) (lo hi : ℤ) (top : ℕ) :
    Module.Finite Geom (bandSpace d lo hi top) :=
  restrictSupport_finite ((Finsupp.finite_of_degree_le d).subset fun _ h => Nat.le_of_eq h.1)
private def exponents (a b c f : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c, f]
@[simp] private theorem exponents_apply (a b c f : ℕ) (j : Fin 4) :
    exponents a b c f j = ![a, b, c, f] j := by simp [exponents]
theorem exponents_coords (m : Fin 4 →₀ ℕ) :
    exponents (m 0) (m 1) (m 2) (m 3) = m := by
  ext i
  fin_cases i <;> simp
theorem interval_iff (lo hi : ℤ) (j : ℕ) :
    j < intervalSize lo hi ↔ lo + (j : ℤ) ≤ hi := by
  unfold intervalSize
  omega
abbrev BandSlots (d : ℕ) (lo hi : ℤ) (top : ℕ) :=
  Σ f : Fin (min d top + 1),
    Σ c : Fin (min (d - f.val) ((hi - 3 * f.val) / 2).toNat + 1),
      Fin (intervalSize (max 0 (lo - 2 * c.val - 3 * f.val))
        (min ((d : ℤ) - f.val - c.val) (hi - 2 * c.val - 3 * f.val)))
def bandEncoding (d : ℕ) (lo hi : ℤ) (top : ℕ) (p : BandSlots d lo hi top) :
    {m : Fin 4 →₀ ℕ // BandExponent d lo hi top m} := by
  obtain ⟨f, c, j⟩ := p
  let lower : ℤ := max 0 (lo - 2 * c.val - 3 * f.val)
  let upper : ℤ := min ((d : ℤ) - f.val - c.val) (hi - 2 * c.val - 3 * f.val)
  let b := lower.toNat + j.val
  have h0 : 0 ≤ lower := le_max_left _ _
  have hj : lower + (j.val : ℤ) ≤ upper := (interval_iff _ _ _).mp j.isLt
  have hb : (b : ℤ) = lower + (j.val : ℤ) := by dsimp [b]; omega
  have hlow := le_max_right (0 : ℤ) (lo - 2 * c.val - 3 * f.val)
  have hf := f.isLt
  have h : b + c.val + f.val ≤ d := by dsimp [upper] at hj; omega
  refine ⟨exponents (d - (b + c.val + f.val)) b c f, ?_⟩
  simp only [BandExponent, degree_formula, jetIndex_formula, exponents_apply]
  change d - (b + c.val + f.val) + b + c.val + f.val = d ∧
    lo ≤ (b + 2 * c.val + 3 * f.val : ℕ) ∧
    (b + 2 * c.val + 3 * f.val : ℕ) ≤ hi ∧ f.val ≤ top
  dsimp only [upper] at hj
  change lo - 2 * c.val - 3 * f.val ≤ lower at hlow
  omega
theorem bandEncoding_bijective (d : ℕ) (lo hi : ℤ) (top : ℕ) :
    Function.Bijective (bandEncoding d lo hi top) := by
  constructor
  · rintro ⟨⟨f, hf⟩, ⟨c, hc⟩, ⟨j, hj⟩⟩ ⟨⟨f', hf'⟩, ⟨c', hc'⟩, ⟨j', hj'⟩⟩ h
    have ef : f = f' := by
      simpa [bandEncoding] using congrArg (fun m => m.val 3) h
    have ec : c = c' := by
      simpa [bandEncoding] using congrArg (fun m => m.val 2) h
    subst f'
    subst c'
    have ej : j = j' := by
      simpa [bandEncoding] using congrArg (fun m => m.val 1) h
    subst j'
    rfl
  · intro m
    obtain ⟨hd, hl, hu, htop⟩ := m.property
    let a := m.val 0
    let b := m.val 1
    let c := m.val 2
    let f := m.val 3
    change f ≤ top at htop
    rw [degree_formula] at hd
    change a + b + c + f = d at hd
    rw [jetIndex_formula] at hl hu
    change lo ≤ (b + 2 * c + 3 * f : ℕ) at hl
    change (b + 2 * c + 3 * f : ℕ) ≤ hi at hu
    have hf : f < min d top + 1 := by omega
    have hc : c < min (d - f) ((hi - 3 * f) / 2).toNat + 1 := by omega
    let lower : ℤ := max 0 (lo - 2 * c - 3 * f)
    let upper : ℤ := min ((d : ℤ) - f - c) (hi - 2 * c - 3 * f)
    let j := b - lower.toNat
    have h0 : 0 ≤ lower := le_max_left _ _
    have hb : lower.toNat + j = b := by
      dsimp [lower, j]
      omega
    have hj : j < intervalSize lower upper := (interval_iff _ _ _).mpr (by
      dsimp [upper] at *
      omega)
    refine ⟨⟨⟨f, hf⟩, ⟨c, hc⟩, ⟨j, hj⟩⟩, Subtype.ext ?_⟩
    change exponents (d - (lower.toNat + j + c + f)) (lower.toNat + j) c f = m.val
    rw [hb, show d - (b + c + f) = a by omega]
    exact exponents_coords m.val
theorem finrank_bandSpace (d : ℕ) (lo hi : ℤ) (top : ℕ) :
    Module.finrank Geom (bandSpace d lo hi top) = bandCount d lo hi top := by
  let e := Equiv.ofBijective (bandEncoding d lo hi top) (bandEncoding_bijective d lo hi top)
  let b := basisRestrictSupport Geom {m | BandExponent d lo hi top m}
  calc
    _ = Fintype.card (BandSlots d lo hi top) := Module.finrank_eq_card_basis (b.reindex e.symm)
    _ = _ := by simp only [BandSlots, bandCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin]
def TargetExponent (d : ℕ) (lo order : ℤ) (m : Fin 4 →₀ ℕ) : Prop :=
  m.degree = d ∧ lo ≤ (m.weight jetIndex : ℤ) ∧ (m.weight targetOrder : ℤ) < order
def targetSpace (d : ℕ) (lo order : ℤ) : Submodule Geom Form :=
  restrictSupport Geom {m | TargetExponent d lo order m}
abbrev TargetSlots (d : ℕ) (lo order : ℤ) :=
  Σ a : Fin (d + 1), Σ f : Fin (d - a.val + 1),
    Fin (intervalSize (max 0 (lo - d + a.val - 2 * f.val))
      (min ((d : ℤ) - a.val - f.val) (order - 1 - 3 * a.val - 2 * f.val)))
def targetEncoding (d : ℕ) (lo order : ℤ) (p : TargetSlots d lo order) :
    {m : Fin 4 →₀ ℕ // TargetExponent d lo order m} := by
  obtain ⟨a, f, j⟩ := p
  let lower : ℤ := max 0 (lo - d + a.val - 2 * f.val)
  let upper : ℤ := min ((d : ℤ) - a.val - f.val) (order - 1 - 3 * a.val - 2 * f.val)
  let c := lower.toNat + j.val
  have h0 : 0 ≤ lower := le_max_left _ _
  have hj : lower + (j.val : ℤ) ≤ upper := (interval_iff _ _ _).mp j.isLt
  have hc : (c : ℤ) = lower + j.val := by dsimp [c]; omega
  have hlow := le_max_right (0 : ℤ) (lo - d + a.val - 2 * f.val)
  have h : a.val + c + f.val ≤ d := by dsimp [upper] at hj; omega
  refine ⟨exponents a (d - (a.val + c + f.val)) c f, ?_⟩
  simp only [TargetExponent, degree_formula, jetIndex_formula, targetOrder_formula, exponents_apply]
  change a.val + (d - (a.val + c + f.val)) + c + f.val = d ∧
    lo ≤ (d - (a.val + c + f.val) + 2 * c + 3 * f.val : ℕ) ∧
    (3 * a.val + c + 2 * f.val : ℕ) < order
  dsimp only [upper] at hj
  change lo - d + a.val - 2 * f.val ≤ lower at hlow
  omega
theorem targetEncoding_bijective (d : ℕ) (lo order : ℤ) :
    Function.Bijective (targetEncoding d lo order) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨f, hf⟩, ⟨j, hj⟩⟩ ⟨⟨a', ha'⟩, ⟨f', hf'⟩, ⟨j', hj'⟩⟩ h
    have ea : a = a' := by
      simpa [targetEncoding] using congrArg (fun m => m.val 0) h
    have ef : f = f' := by
      simpa [targetEncoding] using congrArg (fun m => m.val 3) h
    subst a'
    subst f'
    have ej : j = j' := by
      simpa [targetEncoding] using congrArg (fun m => m.val 2) h
    subst j'
    rfl
  · intro m
    obtain ⟨hd, hl, ho⟩ := m.property
    let a := m.val 0
    let b := m.val 1
    let c := m.val 2
    let f := m.val 3
    rw [degree_formula] at hd
    change a + b + c + f = d at hd
    rw [jetIndex_formula] at hl
    change lo ≤ (b + 2 * c + 3 * f : ℕ) at hl
    rw [targetOrder_formula] at ho
    change (3 * a + c + 2 * f : ℕ) < order at ho
    have ha : a < d + 1 := by omega
    have hf : f < d - a + 1 := by omega
    let lower : ℤ := max 0 (lo - d + a - 2 * f)
    let upper : ℤ := min ((d : ℤ) - a - f) (order - 1 - 3 * a - 2 * f)
    let j := c - lower.toNat
    have h0 : 0 ≤ lower := le_max_left _ _
    have hc : lower.toNat + j = c := by
      dsimp [lower, j]
      omega
    have hj : j < intervalSize lower upper := (interval_iff _ _ _).mpr (by
      dsimp [upper] at *
      omega)
    refine ⟨⟨⟨a, ha⟩, ⟨f, hf⟩, ⟨j, hj⟩⟩, Subtype.ext ?_⟩
    change exponents a (d - (a + (lower.toNat + j) + f)) (lower.toNat + j) f = m.val
    rw [hc, show d - (a + c + f) = b by omega]
    exact exponents_coords m.val
theorem targetSpace_finite (d : ℕ) (lo order : ℤ) :
    Module.Finite Geom (targetSpace d lo order) :=
  restrictSupport_finite ((Finsupp.finite_of_degree_le d).subset fun _ h => Nat.le_of_eq h.1)
theorem finrank_targetSpace (d : ℕ) (lo order : ℤ) :
    Module.finrank Geom (targetSpace d lo order) = targetCount d lo order := by
  let e := Equiv.ofBijective (targetEncoding d lo order) (targetEncoding_bijective d lo order)
  let b := basisRestrictSupport Geom {m | TargetExponent d lo order m}
  calc
    _ = Fintype.card (TargetSlots d lo order) := Module.finrank_eq_card_basis (b.reindex e.symm)
    _ = _ := by simp only [TargetSlots, targetCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin]
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
noncomputable section
set_option maxHeartbeats 1000000
@[simp] theorem backShift_X_zero : backShift (MvPolynomial.X 0) = valueForm := by
  simp [backShift]
theorem backShift_X_of_ne (j : Fin 4) (h : j ≠ 0) :
    backShift (MvPolynomial.X j) = MvPolynomial.X j := by
  simp [backShift, h]
theorem backShift_homogeneous {Q : Form} {d : ℕ}
    (hQ : Q.IsWeightedHomogeneous (fun _ => (1 : ℕ)) d) :
    (backShift Q).IsWeightedHomogeneous (fun _ => (1 : ℕ)) d := by
  apply hQ.bind₁
  intro i
  split_ifs
  · let h := isWeightedHomogeneous_X Geom (fun _ : Fin 4 => (1 : ℕ))
    exact (((h 0).add (h 1)).sub (h 2)).add (h 3)
  · exact isWeightedHomogeneous_X _ _ _
theorem backShift_index_order {Q : Form} {n : ℕ}
    (hQ : Q ∈ restrictWeightedOrder jetIndex n) :
    backShift Q ∈ restrictWeightedOrder jetIndex n := by
  apply bind₁_mem_restrictWeightedOrder _ hQ
  intro j
  split_ifs with h
  · subst j
    change valueForm ∈ restrictWeightedOrder jetIndex 0
    simp
  · exact X_mem_restrictWeightedOrder _ _ le_rfl
theorem coefficient_of_filter {p : (Fin 4 →₀ ℕ) → Prop} [DecidablePred p]
    {Q : Form} {e : Fin 4 →₀ ℕ} (h : e ∈ (filterSupport p Q).support) :
    p e ∧ e ∈ Q.support := by
  have hne := MvPolynomial.mem_support_iff.mp h
  rw [coeff_filterSupport] at hne
  by_cases he : p e
  · simpa [he, MvPolynomial.mem_support_iff] using hne
  · simp [he] at hne
theorem rank_block_le_active (s : ℕ) (g : ℤ) (hg : g < 90 - (s : ℤ)) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) ≤
      bandCount (residualDegree s) (-g) (activeIndex g) 10 := by
  let d := residualDegree s
  let B := bandSpace d (-g) 48 10
  let A := bandSpace d (-g) (activeIndex g) 10
  let cut := (90 - g).toNat
  let retain := fun e : Fin 4 →₀ ℕ => e.weight jetIndex < cut
  let project : B →ₗ[Geom] A := ((filterSupport retain).domRestrict B).codRestrict A (by
    intro Q
    apply (mem_restrictSupport_iff Geom).mpr
    intro e he
    have ⟨hret, hQ⟩ := coefficient_of_filter he
    obtain ⟨hdeg, hlo, hhi, htop⟩ := Q.property hQ
    refine ⟨hdeg, hlo, ?_, htop⟩
    dsimp [activeIndex]
    change e.weight jetIndex < cut at hret
    dsimp [cut] at hret
    omega)
  let trunc := weightedTruncation (R := Geom) targetOrder (orderCutoff s g).toNat
  let restricted := (trunc.comp backShift.toLinearMap).domRestrict A
  have fac : blockMap s g = restricted.comp project := by
    apply LinearMap.ext
    intro Q
    let P := filterSupport retain (Q : Form)
    let H := filterSupport (fun e => ¬retain e) (Q : Form)
    change trunc (backShift (Q : Form)) = trunc (backShift P)
    have hsplit : P + H = (Q : Form) := filterSupport_add_filterSupport_not _ _
    have hH : H.IsWeightedHomogeneous (fun _ => (1 : ℕ)) d := by
      intro e he
      have hmem : e ∈ H.support := MvPolynomial.mem_support_iff.mpr he
      obtain ⟨_, hq⟩ := coefficient_of_filter hmem
      rw [← Finsupp.degree_eq_weight_one]
      exact (Q.property hq).1
    have hI : H ∈ restrictWeightedOrder jetIndex cut := by
      refine mem_restrictWeightedOrder.mpr fun e he => ?_
      exact Nat.le_of_not_lt (coefficient_of_filter he).1
    have hh := backShift_homogeneous hH
    have hj := backShift_index_order hI
    have hkill : trunc (backShift H) = 0 := by
      apply (weightedTruncation_eq_zero_iff _ _ _).mpr
      refine mem_restrictWeightedOrder.mpr fun e he => ?_
      have hdeg := hh (MvPolynomial.mem_support_iff.mp he)
      rw [← Finsupp.degree_eq_weight_one, degree_formula] at hdeg
      have heI := mem_restrictWeightedOrder.mp hj e he
      rw [jetIndex_formula] at heI
      rw [targetOrder_formula]
      have hd : d ≤ s := min_le_left _ _
      dsimp [cut, orderCutoff] at *
      omega
    rw [← hsplit, map_add, map_add, hkill, add_zero]
  have : Module.Finite Geom A := bandSpace_finite _ _ _ _
  calc
    _ = Module.finrank Geom (LinearMap.range (restricted.comp project)) := by rw [fac]
    _ ≤ Module.finrank Geom (LinearMap.range restricted) :=
      LinearMap.finrank_range_comp_le_left restricted project
    _ ≤ Module.finrank Geom A := LinearMap.finrank_range_le restricted
    _ = _ := finrank_bandSpace _ _ _ _
theorem factorial_cast_ne_zero {n : ℕ} (hn : n ≤ 48) : (n.factorial : Geom) ≠ 0 := by
  have : CharP Geom 2130706433 :=
    charP_of_injective_algebraMap
      (R := K1.K) (A := Geom) (algebraMap K1.K Geom).injective 2130706433
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    refine mul_ne_zero ?_ (ih (by omega))
    intro h
    have hd := (CharP.cast_eq_zero_iff Geom 2130706433 (n + 1)).mp h
    have := Nat.le_of_dvd (Nat.succ_pos n) hd
    omega
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
open scoped Pointwise BigOperators
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
theorem bandSpace_mul {d e a b : ℕ} {lo hi low high : ℤ} {P Q : Form}
    (hp : P ∈ bandSpace d lo hi a) (hq : Q ∈ bandSpace e low high b) :
    P * Q ∈ bandSpace (d + e) (lo + low) (hi + high) (a + b) := by
  classical
  apply (mem_restrictSupport_iff Geom).mpr
  intro m hm
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  obtain ⟨hdu, hlu, hhu, htu⟩ := (mem_restrictSupport_iff Geom).mp hp hu
  obtain ⟨hdv, hlv, hhv, htv⟩ := (mem_restrictSupport_iff Geom).mp hq hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [map_add, hdu, hdv]
  · simpa only [map_add, Nat.cast_add] using add_le_add hlu hlv
  · simpa only [map_add, Nat.cast_add] using add_le_add hhu hhv
  · exact Nat.add_le_add htu htv
private theorem bandSpace_pow {d f : ℕ} {lo hi : ℤ} {P : Form}
    (hP : P ∈ bandSpace d lo hi f) (n : ℕ) :
    P ^ n ∈ bandSpace (n * d) (n * lo) (n * hi) (n * f) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    rw [← MvPolynomial.C_1, ← monomial_zero']
    apply (monomial_mem_restrictSupport Geom).mpr
    exact Or.inl (by simp [BandExponent])
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul, Nat.succ_mul, Nat.cast_succ, add_mul, add_mul,
      one_mul, one_mul]
    exact bandSpace_mul ih hP
private abbrev x₀ : Form := MvPolynomial.X 0
private abbrev x₁ : Form := MvPolynomial.X 1
private abbrev x₂ : Form := MvPolynomial.X 2
private abbrev x₃ : Form := MvPolynomial.X 3
private abbrev quad : Form := x₀ * x₁ - x₁ ^ 2 + x₀ * x₂
private abbrev cubic : Form := x₀ ^ 2 * x₃ + x₀ ^ 2 * x₂ - 2 * x₀ * x₁ * x₂ - x₀ * x₁ ^ 2 + x₁ ^ 3
private theorem monomial_band (a b c f : ℕ) {d top : ℕ} {lo hi : ℤ}
    (hd : a + b + c + f = d) (hlo : lo ≤ (b + 2 * c + 3 * f : ℕ))
    (hhi : (b + 2 * c + 3 * f : ℕ) ≤ hi) (hf : f ≤ top) :
    x₀ ^ a * x₁ ^ b * x₂ ^ c * x₃ ^ f ∈ bandSpace d lo hi top := by
  let u : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![a, b, c, f]
  have hval (i : Fin 4) : u i = ![a, b, c, f] i := by simp [u]
  have he : BandExponent d lo hi top u := by
    simpa [BandExponent, degree_formula, jetIndex_formula, hval] using ⟨hd, hlo, hhi, hf⟩
  have hm : monomial u (1 : Geom) ∈ bandSpace d lo hi top :=
    (monomial_mem_restrictSupport Geom).mpr (Or.inl he)
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four,
    MvPolynomial.C_1, one_mul] at hm
  simpa [hval] using hm
theorem x₀_band : x₀ ∈ bandSpace 1 0 0 0 := by
  simpa using monomial_band 1 0 0 0 (d := 1) (lo := 0) (hi := 0) (top := 0)
    (by decide) (by decide) (by decide) (by decide)
theorem x₂_band : x₂ ∈ bandSpace 1 2 2 0 := by
  simpa using monomial_band 0 0 1 0 (d := 1) (lo := 2) (hi := 2) (top := 0)
    (by decide) (by decide) (by decide) (by decide)
theorem quad_band : quad ∈ bandSpace 2 1 2 0 := by
  have hm (a b c : ℕ) (h : a + b + c = 2) (hl : 1 ≤ b + 2 * c) (hh : b + 2 * c ≤ 2) :
      x₀ ^ a * x₁ ^ b * x₂ ^ c ∈ bandSpace 2 1 2 0 := by
    simpa using monomial_band a b c 0 (d := 2) (lo := 1) (hi := 2) (top := 0)
      (by simpa using h) (by exact_mod_cast hl) (by exact_mod_cast hh) (by decide)
  exact add_mem
    (sub_mem (by simpa using hm 1 1 0 (by decide) (by decide) (by decide))
      (by simpa using hm 0 2 0 (by decide) (by decide) (by decide)))
    (by simpa using hm 1 0 1 (by decide) (by decide) (by decide))
theorem cubic_band : cubic ∈ bandSpace 3 2 3 1 := by
  have hm (a b c f : ℕ) (h : a + b + c + f = 3) (hl : 2 ≤ b + 2*c + 3*f)
      (hh : b + 2*c + 3*f ≤ 3) (hf : f ≤ 1) :
      x₀ ^ a * x₁ ^ b * x₂ ^ c * x₃ ^ f ∈ bandSpace 3 2 3 1 :=
    monomial_band a b c f h (by exact_mod_cast hl) (by exact_mod_cast hh) hf
  have h12 : x₀ * x₁ * x₂ ∈ bandSpace 3 2 3 1 := by
    simpa using hm 1 1 1 0 (by decide) (by decide) (by decide) (by decide)
  have h2 : 2 * x₀ * x₁ * x₂ ∈ bandSpace 3 2 3 1 := by
    simpa [two_mul, add_mul] using add_mem h12 h12
  have h001 : x₀ ^ 2 * x₃ ∈ bandSpace 3 2 3 1 := by
    simpa using hm 2 0 0 1 (by decide) (by decide) (by decide) (by decide)
  have h010 : x₀ ^ 2 * x₂ ∈ bandSpace 3 2 3 1 := by
    simpa using hm 2 0 1 0 (by decide) (by decide) (by decide) (by decide)
  have h020 : x₀ * x₁ ^ 2 ∈ bandSpace 3 2 3 1 := by
    simpa using hm 1 2 0 0 (by decide) (by decide) (by decide) (by decide)
  have h030 : x₁ ^ 3 ∈ bandSpace 3 2 3 1 := by
    simpa using hm 0 3 0 0 (by decide) (by decide) (by decide) (by decide)
  exact add_mem (sub_mem (sub_mem (add_mem h001 h010) h2) h020) h030
theorem flagFactor_mem_band (v : FactorPowers) :
    flagFactor v ∈ bandSpace v.degree v.minIndex v.maxIndex v.maxTop := by
  have h := bandSpace_mul (bandSpace_mul (bandSpace_mul
    (bandSpace_pow x₀_band v.value) (bandSpace_pow x₂_band v.jetTwo))
    (bandSpace_pow quad_band v.quad)) (bandSpace_pow cubic_band v.cubic)
  have hd : v.value * 1 + v.jetTwo * 1 + v.quad * 2 + v.cubic * 3 = v.degree := by
    unfold FactorPowers.degree
    omega
  have hl : (v.value : ℤ) * 0 + (v.jetTwo : ℤ) * 2 + (v.quad : ℤ) * 1 + (v.cubic : ℤ) * 2 =
      (v.minIndex : ℤ) := by
    unfold FactorPowers.minIndex
    push_cast
    ring
  have hh : (v.value : ℤ) * 0 + (v.jetTwo : ℤ) * 2 + (v.quad : ℤ) * 2 + (v.cubic : ℤ) * 3 =
      (v.maxIndex : ℤ) := by
    unfold FactorPowers.maxIndex
    push_cast
    ring
  have ht : v.value * 0 + v.jetTwo * 0 + v.quad * 0 + v.cubic * 1 = v.maxTop := by
    simp [FactorPowers.maxTop]
  rw [hd, hl, hh, ht] at h
  exact h
def evaluateAtJetOne : Form →ₐ[Geom] Geom :=
  MvPolynomial.aeval (fun j : Fin 4 => if j = 1 then 1 else 0)
theorem quad_ne_zero : quad ≠ 0 := by
  intro h
  have he := congrArg evaluateAtJetOne h
  simp [evaluateAtJetOne] at he
theorem cubic_ne_zero : cubic ≠ 0 := by
  intro h
  have he := congrArg evaluateAtJetOne h
  simp [evaluateAtJetOne] at he
theorem flagFactor_ne_zero (v : FactorPowers) : flagFactor v ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero _))
    (pow_ne_zero _ (MvPolynomial.X_ne_zero _))) (pow_ne_zero _ quad_ne_zero)) (pow_ne_zero _ cubic_ne_zero)
private theorem capX (i : Fin 4) :
    MvPolynomial.X (R := Geom) i ∈ restrictWeightedOrder targetOrder (targetOrder i) :=
  X_mem_restrictWeightedOrder _ _ le_rfl
theorem shift_quad_order : backShift quad ∈ restrictWeightedOrder targetOrder 2 := by
  have h : backShift quad = x₁ * (x₀ + x₃) + ((x₀ + x₃) - x₂) * x₂ := by
    simp only [map_add, map_sub, map_mul, backShift_X_zero, backShift_X_of_ne 1 (by decide),
      backShift_X_of_ne 2 (by decide), pow_two]
    unfold valueForm
    ring
  rw [h]
  have ha : x₀ + x₃ ∈ restrictWeightedOrder targetOrder 2 :=
    add_mem (restrictWeightedOrder_anti _ (by decide) (capX 0)) (capX 3)
  have hb : (x₀ + x₃) - x₂ ∈ restrictWeightedOrder targetOrder 1 :=
    sub_mem (restrictWeightedOrder_anti _ (by decide) ha) (capX 2)
  exact add_mem (mul_mem_restrictWeightedOrder (capX 1) ha)
    (mul_mem_restrictWeightedOrder hb (capX 2))
theorem shift_cubic_order : backShift cubic ∈ restrictWeightedOrder targetOrder 3 := by
  let U := x₀ + x₃ - x₂
  have h : backShift cubic = -(x₁ ^ 2 * x₀) + 2 * (x₁ * U * x₃) + U ^ 2 * (x₃ + x₂) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, backShift_X_zero,
      backShift_X_of_ne 1 (by decide), backShift_X_of_ne 2 (by decide), backShift_X_of_ne 3 (by decide)]
    unfold valueForm U
    ring
  rw [h]
  have hU : U ∈ restrictWeightedOrder targetOrder 1 :=
    sub_mem (add_mem (restrictWeightedOrder_anti _ (by decide) (capX 0))
      (restrictWeightedOrder_anti _ (by decide) (capX 3))) (capX 2)
  have hmiddle : x₁ * U * x₃ ∈ restrictWeightedOrder targetOrder 3 :=
    mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder (capX 1) hU) (capX 3)
  have hlast : x₃ + x₂ ∈ restrictWeightedOrder targetOrder 1 :=
    add_mem (restrictWeightedOrder_anti _ (by decide) (capX 3)) (capX 2)
  exact add_mem
    (add_mem (neg_mem (mul_mem_restrictWeightedOrder
      (pow_mem_restrictWeightedOrder (capX 1) 2) (capX 0)))
      (by simpa [two_mul] using add_mem hmiddle hmiddle))
    (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder hU 2) hlast)
theorem flagFactor_target_order (v : FactorPowers) :
    backShift (flagFactor v) ∈ restrictWeightedOrder targetOrder v.minOrder := by
  have h₀ : backShift x₀ ∈ restrictWeightedOrder targetOrder 0 := by simp
  have h₂ : backShift x₂ ∈ restrictWeightedOrder targetOrder 1 := by
    rw [backShift_X_of_ne 2 (by decide)]
    exact capX 2
  have h := mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder
      (mul_mem_restrictWeightedOrder (pow_mem_restrictWeightedOrder h₀ v.value)
        (pow_mem_restrictWeightedOrder h₂ v.jetTwo))
      (pow_mem_restrictWeightedOrder shift_quad_order v.quad))
    (pow_mem_restrictWeightedOrder shift_cubic_order v.cubic)
  have ho : v.value * 0 + v.jetTwo * 1 + v.quad * 2 + v.cubic * 3 = v.minOrder := by
    unfold FactorPowers.minOrder
    omega
  rw [ho] at h
  simp only [flagFactor, map_pow, map_mul]
  exact h
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
noncomputable section
set_option maxHeartbeats 1800000
private def smallContact (d : ℕ) (lo hi : ℤ) (top : ℕ) (order : ℤ) :
    bandSpace d lo hi top →ₗ[Geom] targetSpace d lo order :=
  (((weightedTruncation targetOrder order.toNat).comp backShift.toLinearMap).domRestrict
    (bandSpace d lo hi top)).codRestrict (targetSpace d lo order) (by
      intro P
      have hP := (mem_restrictSupport_iff Geom).mp P.property
      have hdeg : (P : Form).IsWeightedHomogeneous (fun _ => (1 : ℕ)) d := by
        intro m hm
        rw [← Finsupp.degree_eq_weight_one]
        exact (hP (MvPolynomial.mem_support_iff.mpr hm)).1
      have horder : (P : Form) ∈ restrictWeightedOrder jetIndex lo.toNat := by
        refine mem_restrictWeightedOrder.mpr fun m hm => ?_
        have := (hP hm).2.1
        omega
      have hdeg' := backShift_homogeneous hdeg
      have horder' := backShift_index_order horder
      apply (mem_restrictSupport_iff Geom).mpr
      intro e he
      have hc := MvPolynomial.mem_support_iff.mp he
      change (weightedTruncation targetOrder order.toNat (backShift P)).coeff e ≠ 0 at hc
      rw [coeff_weightedTruncation] at hc
      by_cases hb : e.weight targetOrder < order.toNat
      · have hcoeff : (backShift P).coeff e ≠ 0 := by simpa [hb] using hc
        have hd := hdeg' hcoeff
        rw [← Finsupp.degree_eq_weight_one] at hd
        have hi := mem_restrictWeightedOrder.mp horder' e (MvPolynomial.mem_support_iff.mpr hcoeff)
        exact ⟨hd, by omega, by omega⟩
      · simp [hb] at hc)
private theorem smallContact_order {d : ℕ} {lo hi : ℤ} {top : ℕ} {order : ℤ}
    (Q : LinearMap.ker (smallContact d lo hi top order)) :
    backShift (Q : Form) ∈ restrictWeightedOrder targetOrder order.toNat := by
  apply (weightedTruncation_eq_zero_iff _ _ _).mp
  have h := LinearMap.mem_ker.mp Q.property
  exact congrArg (fun P : targetSpace d lo order => (P : Form)) h
theorem rank_block_le_flag (s : ℕ) (g : ℤ) (v : FactorPowers) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) ≤ flagBound s g v := by
  let d := residualDegree s
  let B := bandSpace d (-g) 48 10
  have hB : Module.Finite Geom B := bandSpace_finite _ _ _ _
  have hBdim : Module.finrank Geom B = bandCount d (-g) 48 10 := finrank_bandSpace _ _ _ _
  unfold flagBound
  dsimp only
  by_cases h : v.degree ≤ d ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10
  · rw [ite_eq_left h]
    let d' := d - v.degree
    let lo' := -g - (v.minIndex : ℤ)
    let hi' := 48 - (v.maxIndex : ℤ)
    let top' := 10 - v.maxTop
    let order' := orderCutoff s g - (v.minOrder : ℤ)
    let W := bandSpace d' lo' hi' top'
    let Target := targetSpace d' lo' order'
    let small : W →ₗ[Geom] Target := smallContact d' lo' hi' top' order'
    let V := LinearMap.ker small
    have hW : Module.Finite Geom W := bandSpace_finite _ _ _ _
    have hTarget : Module.Finite Geom Target := targetSpace_finite _ _ _
    have hdim : Module.finrank Geom W = bandCount d' lo' hi' top' := finrank_bandSpace _ _ _ _
    have hTdim : Module.finrank Geom Target = targetCount d' lo' order' := finrank_targetSpace _ _ _
    have hsmall : Module.finrank Geom (LinearMap.range small) ≤ Module.finrank Geom Target :=
      Submodule.finrank_le _
    have hsum := small.finrank_range_add_finrank_ker
    have hK : bandCount d' lo' hi' top' - targetCount d' lo' order' ≤
        Module.finrank Geom V := by
      change Module.finrank Geom (LinearMap.range small) + Module.finrank Geom V =
        Module.finrank Geom W at hsum
      omega
    let multiply : W →ₗ[Geom] B :=
      ((LinearMap.mulLeft Geom (flagFactor v)).domRestrict W).codRestrict B (by
        intro Q
        have hm := bandSpace_mul (flagFactor_mem_band v) Q.property
        have hd : v.degree + d' = d := by dsimp [d']; omega
        have hl : (v.minIndex : ℤ) + lo' = -g := by dsimp [lo']; omega
        have hh : (v.maxIndex : ℤ) + hi' = 48 := by dsimp [hi']; omega
        have ht : v.maxTop + top' = 10 := by dsimp [top']; omega
        change flagFactor v * (Q : Form) ∈ bandSpace d (-g) 48 10
        simpa only [hd, hl, hh, ht] using hm)
    let embed : V →ₗ[Geom] LinearMap.ker (blockMap s g) :=
      (multiply.domRestrict V).codRestrict (LinearMap.ker (blockMap s g)) (by
        intro Q
        apply LinearMap.mem_ker.mpr
        change weightedTruncation targetOrder (orderCutoff s g).toNat
          (backShift (flagFactor v * (Q : Form))) = 0
        rw [map_mul]
        apply (weightedTruncation_eq_zero_iff _ _ _).mpr
        have hcut : (orderCutoff s g).toNat ≤ v.minOrder + order'.toNat := by
          dsimp [order']; omega
        exact restrictWeightedOrder_anti _ hcut
          (mul_mem_restrictWeightedOrder (flagFactor_target_order v)
            (smallContact_order (d := d') (lo := lo') (hi := hi') (top := top') (order := order') Q)))
    have hinj : Function.Injective embed := by
      intro P Q he
      have he' : flagFactor v * (P : Form) = flagFactor v * (Q : Form) :=
        congrArg (fun P : LinearMap.ker (blockMap s g) => (P : Form)) he
      exact Subtype.ext (Subtype.ext (mul_left_cancel₀ (flagFactor_ne_zero v) he'))
    have hr := LinearMap.finrank_range_le_sub_of_injective_ker (W := V) (blockMap s g) embed hinj
    change _ ≤ bandCount d (-g) 48 10 - (bandCount d' lo' hi' top' - targetCount d' lo' order')
    change Module.finrank Geom (LinearMap.range (blockMap s g)) ≤
      Module.finrank Geom B - Module.finrank Geom V at hr
    omega
  · rw [ite_eq_right h, ← hBdim]
    exact LinearMap.finrank_range_le (blockMap s g)
end
end K1_13_1_1
end
section
namespace K1_13_1_1
open K1_13 MvPolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
theorem coeff_projectJet (j : Fin 4) (k : ℕ) (P : Form) (e : Fin 4 →₀ ℕ) :
    (projectJet j k P).coeff e = if e j = k then P.coeff e else 0 :=
  coeff_filterSupport _ _ _
theorem support_projectJet {j : Fin 4} {k : ℕ} {P : Form} {e : Fin 4 →₀ ℕ}
    (he : e ∈ (projectJet j k P).support) : e j = k ∧ e ∈ P.support := by
  have hc := MvPolynomial.mem_support_iff.mp he
  rw [coeff_projectJet] at hc
  by_cases h : e j = k
  · simpa [h, MvPolynomial.mem_support_iff] using hc
  · simp [h] at hc
theorem rank_le_projected_sum {V : Type*} [AddCommGroup V] [Module Geom V]
    (j : Fin 4) (n : ℕ) (φ : V →ₗ[Geom] Form)
    (hb : ∀ v e, e ∈ (φ v).support → e j < n) :
    Module.finrank Geom (LinearMap.range φ) ≤
      ∑ b : Fin n, Module.finrank Geom (LinearMap.range ((projectJet j b).comp φ)) := by
  let π : LinearMap.range φ →ₗ[Geom] (Fin n → Form) :=
    LinearMap.pi fun b : Fin n => (projectJet j b).comp (LinearMap.range φ).subtype
  have hinj : Function.Injective π := by
    intro Q R h
    apply Subtype.ext
    ext e
    by_cases he : e j < n
    · let b : Fin n := ⟨e j, he⟩
      have heq := congrArg (fun f : Fin n → Form => (f b).coeff e) h
      change (projectJet j (e j) Q).coeff e = (projectJet j (e j) R).coeff e at heq
      simpa [coeff_projectJet] using heq
    · obtain ⟨v, hv⟩ := Q.property
      obtain ⟨w, hw⟩ := R.property
      rw [← hv, ← hw]
      have hzero (v : V) : (φ v).coeff e = 0 := by
        by_contra hne
        exact he (hb v e (MvPolynomial.mem_support_iff.mpr hne))
      rw [hzero, hzero]
  let collect := LinearMap.pi fun b : Fin n => (projectJet j b).comp φ
  have hrange : LinearMap.range π = LinearMap.range collect := by
    ext z
    change (∃ Q, π Q = z) ↔ ∃ v, collect v = z
    constructor
    · rintro ⟨Q, rfl⟩
      obtain ⟨v, hv⟩ := Q.property
      refine ⟨v, ?_⟩
      funext b
      change projectJet j b (φ v) = projectJet j b (Q : Form)
      rw [hv]
    · rintro ⟨v, rfl⟩
      exact ⟨φ.rangeRestrict v, rfl⟩
  calc
    _ = Module.finrank Geom (LinearMap.range π) := (LinearMap.finrank_range_of_inj hinj).symm
    _ = Module.finrank Geom (LinearMap.range collect) := by rw [hrange]
    _ ≤ _ := LinearMap.finrank_range_pi_le_sum _
theorem degree_of_mem_blockMap {s : ℕ} {g : ℤ}
    (Q : bandSpace (residualDegree s) (-g) 48 10) {e : Fin 4 →₀ ℕ}
    (he : e ∈ (blockMap s g Q).support) : e.degree = residualDegree s := by
  have hQ : (Q : Form).IsWeightedHomogeneous (fun _ => (1 : ℕ)) (residualDegree s) := by
    intro e he
    rw [← Finsupp.degree_eq_weight_one]
    exact (Q.property (MvPolynomial.mem_support_iff.mpr he)).1
  have h := (backShift_homogeneous hQ).weightedTruncation targetOrder (orderCutoff s g).toNat
  have hc := h (MvPolynomial.mem_support_iff.mp he)
  rwa [← Finsupp.degree_eq_weight_one] at hc
theorem rank_block_le_pascal (s : ℕ) (g : ℤ) (hg : g < 90 - (s : ℤ))
    (hline : ∀ (b c : ℕ), b + c ≤ residualDegree s →
      Module.finrank Geom (LinearMap.range
        ((projectJet 2 c).comp ((projectJet 1 b).comp (blockMap s g)))) ≤
        lineBound (residualDegree s) (-g) (orderCutoff s g) b c)
    (hpair : ∀ b ≤ residualDegree s,
      Module.finrank Geom (LinearMap.range ((projectJet 1 b).comp (blockMap s g))) ≤
        pairBound (residualDegree s) (-g) b) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) ≤ pascalBound s g := by
  let d := residualDegree s
  refine le_min (rank_block_le_active s g hg) ?_
  have h : Module.finrank Geom (LinearMap.range (blockMap s g)) ≤
      ∑ b : Fin (d + 1),
        Module.finrank Geom (LinearMap.range ((projectJet 1 b).comp (blockMap s g))) :=
    rank_le_projected_sum 1 (d + 1) (blockMap s g) (fun Q e he => by
      have := degree_of_mem_blockMap Q he
      exact Nat.lt_succ_of_le ((Finsupp.le_degree 1 e).trans_eq this))
  refine h.trans ?_
  rw [sumRange_eq_fin]
  refine Finset.sum_le_sum fun b _ => le_min (hpair b (Nat.le_of_lt_succ b.isLt)) ?_
  have hs :=
    rank_le_projected_sum 2 (d - b.val + 1) ((projectJet 1 b).comp (blockMap s g))
      (fun Q e he => by
        have ⟨hb, he'⟩ := support_projectJet he
        have hd := degree_of_mem_blockMap Q he'
        rw [degree_formula] at hd
        omega)
  refine hs.trans ?_
  rw [sumRange_eq_fin]
  exact Finset.sum_le_sum fun c _ => hline b c (by have := b.isLt; have := c.isLt; omega)
end
end K1_13_1_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_13_6_1_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem genericCutLength_sliceIdeal (surface : Ideal GeoJets) (a h : Shape) :
    genericCutLength (sliceIdeal surface h) a = surfaceDegree surface a h := by
  classical
  let H₀ := MvPolynomial (SectionIndex h) GeoField
  let H := SectionField h
  let B := MvPolynomial (PairSectionIndex a h) GeoField
  let N := MvPolynomial (SectionIndex a) H₀
  let S := MvPolynomial (SectionIndex a) H
  let F := PairSectionField a h
  let T := CutField H a
  let M : Submonoid N := (nonZeroDivisors H₀).map MvPolynomial.C
  have : IsLocalization M S := MvPolynomial.isLocalization (nonZeroDivisors H₀) H
  have hcomap : (nonZeroDivisors S).comap (algebraMap N S) = nonZeroDivisors N := by
    have hinj : Function.Injective (algebraMap N S) :=
      MvPolynomial.map_injective _ (IsFractionRing.injective H₀ H)
    ext z
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _ hinj]
  have : IsFractionRing N T := by
    change IsLocalization (nonZeroDivisors N) T
    rw [← hcomap]
    exact IsLocalization.localization_localization_isLocalization_of_has_all_units M
      (nonZeroDivisors S) T (fun _ hu => hu.mem_nonZeroDivisors)
  let s : B ≃+* N := (sumAlgEquiv GeoField (SectionIndex a) (SectionIndex h)).toRingEquiv
  let e : F ≃+* T := IsFractionRing.ringEquivOfRingEquiv s
  let r := MvPolynomial.mapEquiv (Fin 4) e
  let mapF : GeoJets →+* MvPolynomial (Fin 4) F := MvPolynomial.map (algebraMap GeoField F)
  let mapT : SectionJets h →+* MvPolynomial (Fin 4) T := MvPolynomial.map (algebraMap H T)
  have ebase (x : B) :
      e (algebraMap B F x) = algebraMap S T (algebraMap N S (s x)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap s x
  have eC (c : GeoField) :
      e (algebraMap GeoField F c) = algebraMap H T (algebraMap GeoField H c) := by
    change e (algebraMap B F (MvPolynomial.C c)) = _
    rw [ebase]
    change algebraMap S T (algebraMap N S (sumAlgEquiv _ _ _ (MvPolynomial.C c))) = _
    rw [sumAlgEquiv_C_inl, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rfl
  have eX₁ (m : SectionIndex a) :
      e (algebraMap B F (MvPolynomial.X (Sum.inl m))) = algebraMap S T (MvPolynomial.X m) := by
    rw [ebase]
    change algebraMap S T (algebraMap N S (sumAlgEquiv _ _ _ (MvPolynomial.X (Sum.inl m)))) = _
    rw [sumAlgEquiv_X_inl, MvPolynomial.algebraMap_def, MvPolynomial.map_X]
  have eX₂ (m : SectionIndex h) :
      e (algebraMap B F (MvPolynomial.X (Sum.inr m))) = algebraMap H T (algebraMap H₀ H (MvPolynomial.X m)) := by
    rw [ebase]
    change algebraMap S T (algebraMap N S (sumAlgEquiv _ _ _ (MvPolynomial.X (Sum.inr m)))) = _
    rw [sumAlgEquiv_X_inr, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rfl
  have hr₀ : r.toRingHom.comp mapF = mapT.comp (sliceMap h) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [r, mapF, mapT, sliceMap, eC]
      rfl
    · intro i
      simp [r, mapF, mapT, sliceMap]
  have hr₁ : r.toRingHom (sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h)) =
      cutPolynomial H a := by
    simp [r, sectionWith, cutPolynomial]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact congrArg (fun c : T => MvPolynomial.C c * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val)
      (eX₁ m)
  have hr₂ : r.toRingHom (sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)) =
      mapT (genericSection h) := by
    simp [r, mapT, sectionWith, genericSection]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact congrArg (fun c : T => MvPolynomial.C c * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val)
      (eX₂ m)
  let J := surface.map mapF ⊔
    Ideal.span {sectionWith a (Sum.inl : SectionIndex a → PairSectionIndex a h),
      sectionWith h (Sum.inr : SectionIndex h → PairSectionIndex a h)}
  let J' := (sliceIdeal surface h).map mapT ⊔ Ideal.span {cutPolynomial H a}
  have hJ : J' = J.map r.toRingHom := by
    simp only [J, J', sliceIdeal, Ideal.span_insert, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, Ideal.map_map, hr₀, hr₁, hr₂]
    let baseIdeal := surface.map (mapT.comp (sliceMap h))
    let first := Ideal.span {cutPolynomial H a}
    let second := Ideal.span {mapT (genericSection h)}
    change (baseIdeal ⊔ second) ⊔ first = baseIdeal ⊔ (first ⊔ second)
    calc
      _ = baseIdeal ⊔ (second ⊔ first) := sup_assoc _ _ _
      _ = _ := congrArg (baseIdeal ⊔ ·) (sup_comm _ _)
  let j := Ideal.quotientEquiv J J' r hJ
  have hc : (algebraMap T (MvPolynomial (Fin 4) T ⧸ J')).comp e.toRingHom =
      j.toRingHom.comp (algebraMap F (MvPolynomial (Fin 4) F ⧸ J)) := by
    apply RingHom.ext
    intro c
    change Ideal.Quotient.mk J' (MvPolynomial.C (e c)) = j (Ideal.Quotient.mk J (MvPolynomial.C c))
    rw [show j (Ideal.Quotient.mk J (MvPolynomial.C c)) = Ideal.Quotient.mk J' (r (MvPolynomial.C c)) from rfl]
    simp [r]
  exact (Algebra.finrank_eq_of_equiv_equiv e j hc).symm
end
end K1_13_6_1_4_1
end
section
namespace K1_13_6_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
abbrev JetPoint := Fin 4 → GeoField
abbrev GeoJets5 := MvPolynomial (Fin 5) GeoField
def actualPoint (S : Geom[X]) : JetPoint := fun i => genericCoeffs (jet S i)
structure Branch (f Q : Row 4) (l : ℕ) where
  surface : Ideal GeoJets
  r : ℕ
  base : (intersectionIdeal f Q).IsMinimalPrime surface
  high : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface base.isPrime
  chart : CanonicalChart f surface r
  invariant : Invariant ((separant^[r]) f) surface
  proper : toGeneric (membershipTest ((separant^[r]) f)) ∉ surface
  curve : Ideal GeoJets
  divisor : (divisorIdeal surface (membershipTest ((separant^[r]) f))).IsMinimalPrime curve
  regularCurve : toGeneric (separant ((separant^[r]) f)) ∉ curve
  terminal :
    cycleLength (divisorIdeal surface (membershipTest ((separant^[r]) f))) curve
      divisor.isPrime ≠ 1 ∨ toGeneric (nextTest ((separant^[r]) f)) ∉ curve
namespace Branch
variable {f Q : Row 4} {l : ℕ} (b : Branch f Q l)
def g : Row 4 := (separant^[b.r]) f
def sigma : GeoJets := toGeneric (separant b.g)
def member : GeoJets := toGeneric (membershipTest b.g)
def next : GeoJets := toGeneric (nextTest b.g)
def Simple : Prop := cycleLength (divisorIdeal b.surface (membershipTest b.g))
  b.curve b.divisor.isPrime = 1
def weight : ℕ := by classical exact if b.Simple then 1 else 2
def Contains (p : JetPoint) : Prop :=
  b.curve ≤ RingHom.ker (MvPolynomial.eval p) ∧ MvPolynomial.eval p b.sigma ≠ 0
def graph : GeoJets5 :=
  MvPolynomial.rename Fin.castSucc (toGeneric (partialFlow b.g)) +
    MvPolynomial.C (4 : GeoField) * MvPolynomial.rename Fin.castSucc b.sigma *
      MvPolynomial.X (Fin.last 4)
abbrev Local := Localization.Away b.sigma
def localMap : GeoJets →+* b.Local := algebraMap GeoJets b.Local
def onGraph : GeoJets5 →+* b.Local :=
  MvPolynomial.eval₂Hom (b.localMap.comp MvPolynomial.C)
    (Fin.lastCases
      (b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma)
      (fun i => b.localMap (MvPolynomial.X i)))
def localCurve : Ideal b.Local := b.curve.map b.localMap
def regularEval (p : JetPoint) (h : b.Contains p) : b.Local →+* GeoField :=
  IsLocalization.Away.lift b.sigma (isUnit_iff_ne_zero.mpr h.2)
def liftedEval (p : JetPoint) (h : b.Contains p) : GeoJets5 →+* GeoField :=
  (b.regularEval p h).comp b.onGraph
end Branch
def OldBox {n : ℕ} (old : Fin 4 → Fin n) (p : Shape)
    (D : MvPolynomial (Fin n) GeoField) : Prop :=
  ∀ m ∈ D.support,
    (∑ i : Fin 4, m (old i)) ≤ p.b ∧
    (∑ i : Fin 4, i.val * m (old i)) ≤ p.j ∧ m (old 3) ≤ p.t
abbrev Box4 := OldBox (id : Fin 4 → Fin 4)
def Box5 (p : Shape) (d : ℕ) (D : GeoJets5) : Prop :=
  OldBox Fin.castSucc p D ∧ ∀ m ∈ D.support, m (Fin.last 4) ≤ d
def graphBox (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
def budget4 (p : Shape) : ℕ :=
  mixed32 p cutterBox (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
def budget5 (p : Shape) : ℕ :=
  let a := liftedChart (taylorLength + 1) p
  let b := liftedChart (taylorLength + 2) p
  mixed32 p cutterBox a b + (taylorLength + 1) * mixed32 p cutterBox (graphBox p) b +
    (taylorLength + 2) * mixed32 p cutterBox (graphBox p) a
def Slice4 {f Q l} (b : Branch f Q l) (T : Finset JetPoint) : Prop :=
  T.card ≤ 1 ∨ ∃ D, Box4 (chart (taylorLength + 2) (shape f).chamber) D ∧
    D ∉ b.curve ∧ ∀ p ∈ T, MvPolynomial.eval p D = 0
def Slice5 {f Q l} (b : Branch f Q l) (T : Finset JetPoint) : Prop :=
  T.card ≤ 1 ∨ ∃ D, Box5 (liftedChart (taylorLength + 2) (shape f).chamber)
      (taylorLength + 2) D ∧ b.onGraph D ∉ b.localCurve ∧
    ∀ p ∈ T, ∀ h : b.Contains p, b.liftedEval p h D = 0
def Chart4 {f Q l} (b : Branch f Q l) : Prop :=
  let p := (shape f).chamber
  Box4 (chart (taylorLength + 1) p) b.member ∧
    Box4 (chart (taylorLength + 2) p) b.next ∧
    ∀ x a : K, ∃ D, Box4 (chart (taylorLength + 2) p) D ∧
      ∀ S : K[X], S.natDegree ≤ 133671 → b.Contains (actualPoint (extend S)) →
        (MvPolynomial.eval (actualPoint (extend S)) D = 0 ↔ S.eval x = a)
def Chart5 {f Q l} (b : Branch f Q l) : Prop :=
  let p := (shape f).chamber
  Box5 (graphBox p) 1 b.graph ∧
    ∃ E H,
      Box5 (liftedChart (taylorLength + 1) p) (taylorLength + 1) E ∧
      Associated (b.onGraph E) (b.localMap b.member) ∧
      Box5 (liftedChart (taylorLength + 2) p) (taylorLength + 2) H ∧
      Associated (b.onGraph H) (b.localMap b.next) ∧
      ∀ x a : K, ∃ D, Box5 (liftedChart (taylorLength + 2) p) (taylorLength + 2) D ∧
        ∀ S : K[X], S.natDegree ≤ 133671 → ∀ h : b.Contains (actualPoint (extend S)),
          (b.liftedEval (actualPoint (extend S)) h D = 0 ↔ S.eval x = a)
end
end K1_13_6_2
end
section
namespace K1_13_6_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
private theorem genericCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
theorem actualPoint_injective : Function.Injective actualPoint := by
  intro S T h
  have h₀ := congrFun h (0 : Fin 4)
  exact genericCoeffs_injective (by simpa [actualPoint, jet, hasseDeriv_zero'] using h₀)
theorem eval_actualPoint (S : Geom[X]) (P : Row 4) :
    MvPolynomial.eval (actualPoint S) (toGeneric P) = genericCoeffs (atJet P S) := by
  rw [toGeneric, MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet S) P = _
  rw [← MvPolynomial.eval₂_comp]
  rfl
theorem branch_of_mixed {f Q l S} (h : MixedMark f Q l S) :
    ∃ b : Branch f Q l, b.Contains (actualPoint S) := by
  obtain ⟨surf, r, hz, hE, C, hC, hP, hterminal⟩ := h
  have hr : MvPolynomial.eval (actualPoint S) (toGeneric (separant ((separant^[r]) f))) ≠ 0 := by
    rw [eval_actualPoint]
    exact fun hzero => hz.regular (genericCoeffs_injective (by simpa using hzero))
  have hc : toGeneric (separant ((separant^[r]) f)) ∉ C := fun hmem => hr (hP hmem)
  let b : Branch f Q l :=
    ⟨surf, r, hz.base, hz.high, hz.chart, hz.invariant, hE, C, hC, hc, hterminal⟩
  exact ⟨b, hP, hr⟩
namespace Branch
variable {f Q : Row 4} {l : ℕ}
theorem eq_of_surface_curve {b c : Branch f Q l} (hs : b.surface = c.surface)
    (hc : b.curve = c.curve) : b = c := by
  have order (d e : Branch f Q l) (h : d.surface = e.surface) : ¬ d.r < e.r := by
    intro hlt
    have hmem := e.chart.2.1 (d.r + 1) (by omega)
    rw [← h, Function.iterate_succ_apply'] at hmem
    exact d.chart.2.2 hmem
  have hr : b.r = c.r := Nat.le_antisymm (Nat.le_of_not_gt (order c b hs.symm))
    (Nat.le_of_not_gt (order b c hs))
  cases b
  cases c
  cases hs
  cases hr
  cases hc
  rfl
theorem next_proper (b : Branch f Q l) (h : b.Simple) : b.next ∉ b.curve :=
  b.terminal.resolve_left (fun hne => hne h)
theorem next_actual (b : Branch f Q l) {S : Geom[X]} (h : b.Contains (actualPoint S))
    (hd : S.natDegree ≤ 133671) : MvPolynomial.eval (actualPoint S) b.next = 0 := by
  have hs : b.surface ≤ b.curve := le_trans le_sup_left b.divisor.le
  have hg : toGeneric b.g ∈ b.surface := b.chart.2.1 b.r le_rfl
  have hzero : MvPolynomial.eval (actualPoint S) (toGeneric b.g) = 0 := h.1 (hs hg)
  rw [eval_actualPoint] at hzero
  have he : atJet b.g S = 0 := genericCoeffs_injective (by simpa using hzero)
  rw [next, eval_actualPoint, (eval_membership_tests _ _ he hd).2, map_zero]
theorem localMap_mem_localCurve_iff (b : Branch f Q l) (P : GeoJets) :
    b.localMap P ∈ b.localCurve ↔ P ∈ b.curve := by
  change algebraMap GeoJets b.Local P ∈ b.curve.map (algebraMap GeoJets b.Local) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers b.sigma) b.Local]
  constructor
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    exact (b.divisor.isPrime.mem_or_mem hm).resolve_left
      (fun hpow => b.regularCurve (b.divisor.isPrime.mem_of_pow_mem n hpow))
  · intro hP
    exact ⟨1, (Submonoid.powers b.sigma).one_mem, by simpa using hP⟩
theorem regularEval_localMap (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) (P : GeoJets) :
    b.regularEval p h (b.localMap P) = MvPolynomial.eval p P := by
  exact IsLocalization.Away.lift_eq b.sigma _ _
theorem lifted_proper_of_nonzero (b : Branch f Q l) (p : JetPoint) (h : b.Contains p)
    {D : GeoJets5} (hn : b.liftedEval p h D ≠ 0) : b.onGraph D ∉ b.localCurve := by
  have hk : b.localCurve ≤ RingHom.ker (b.regularEval p h) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change b.regularEval p h (b.localMap P) = 0
    rw [regularEval_localMap]
    exact h.1 hP
  exact fun hm => hn (hk hm)
theorem lifted_proper_of_associated (b : Branch f Q l) {D : GeoJets5} {P : GeoJets}
    (hD : Associated (b.onGraph D) (b.localMap P)) (hP : P ∉ b.curve) :
    b.onGraph D ∉ b.localCurve := by
  intro hmem
  exact hP ((b.localMap_mem_localCurve_iff _).mp (b.localCurve.mem_of_dvd hD.dvd hmem))
theorem lifted_zero_of_associated (b : Branch f Q l) {D : GeoJets5} {P : GeoJets}
    (hD : Associated (b.onGraph D) (b.localMap P)) {p : JetPoint} (h : b.Contains p)
    (hP : MvPolynomial.eval p P = 0) : b.liftedEval p h D = 0 := by
  obtain ⟨u, hu⟩ := hD
  have hm := congrArg (b.regularEval p h) hu
  rw [map_mul, regularEval_localMap, hP, mul_eq_zero] at hm
  exact hm.resolve_right (IsUnit.ne_zero (IsUnit.map (b.regularEval p h) u.isUnit))
end Branch
def Demand (A : Finset K) (s : K → K[X]) (T : Finset K) : Prop := by
  classical
  exact T.card = 1 ∨ ∃ x a, (∃ γ ∈ A, (s γ).eval x ≠ a) ∧
    T = A.filter (fun γ => (s γ).eval x = a)
theorem maximal_demand (A : Finset K) (s : K → K[X]) (hA : A.Nonempty) :
    ∃ T ⊆ A, 0 < T.card ∧ CurveSections A s T.card ∧ Demand A s T := by
  classical
  let candidates := A.powerset.filter (Demand A s)
  obtain ⟨γ, hγ⟩ := hA
  have hsingle : {γ} ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hγ),
      Or.inl (Finset.card_singleton γ)⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨_, hsingle⟩
  have hpositive : 1 ≤ T.card := by simpa using hmax _ hsingle
  refine ⟨T, Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1, hpositive, ?_,
    (Finset.mem_filter.mp hT).2⟩
  intro x a ha
  exact hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
    Or.inr ⟨x, a, ha, rfl⟩⟩)
end
end K1_13_6_2
end
section
namespace K1_13_6_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
def c1 : Prop :=
  ∀ f Q l, SmallFactor f → ∀ b : Branch f Q l, Chart4 b
def c2 : Prop :=
  ∀ f Q l, SmallFactor f → ∀ b : Branch f Q l, Chart5 b
def c3 : Prop :=
  ∀ f Q l, SmallFactor f → ¬ f ∣ Q → InBox (shape Q) cutterBox → 0 < l →
    ∀ (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint),
      (∀ b ∈ F, Box4 (chart (taylorLength + 1) (shape f).chamber) b.member ∧
        (∀ p ∈ T b, b.Contains p) ∧ Slice4 b (T b)) →
      32 * l * (∑ b ∈ F, b.weight * (T b).card) ≤ budget4 (shape f).chamber
def c4 : Prop :=
  ∀ f Q l, SmallFactor f → ¬ f ∣ Q → InBox (shape Q) cutterBox → 0 < l →
    ∀ (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint),
      (∀ b ∈ F, Box5 (graphBox (shape f).chamber) 1 b.graph ∧
        (∃ E, Box5 (liftedChart (taylorLength + 1) (shape f).chamber) (taylorLength + 1) E ∧
          Associated (b.onGraph E) (b.localMap b.member)) ∧
        (∀ p ∈ T b, b.Contains p) ∧ Slice5 b (T b)) →
      32 * l * (∑ b ∈ F, b.weight * (T b).card) ≤ budget5 (shape f).chamber
theorem of_children (h4chart : c1) (h5chart : c2) (h4budget : c3) (h5budget : c4) :
    K1_13_6.c2 := by
  classical
  intro Γ s f Q l input
  let point (γ : K) := actualPoint (extend (s γ))
  let marked := Γ.filter (fun γ => MixedMark f Q l (extend (s γ)))
  let assign (γ : marked) : Branch f Q l :=
    Classical.choose (branch_of_mixed (Finset.mem_filter.mp γ.property).2)
  let branches := marked.attach.image assign
  let labels (b : Branch f Q l) :=
    marked.filter (fun γ => ∃ h : γ ∈ marked, assign ⟨γ, h⟩ = b)
  have label_sub (b : Branch f Q l) : labels b ⊆ Γ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have contains_label (b : Branch f Q l) (γ : K) (hγ : γ ∈ labels b) :
      b.Contains (point γ) := by
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hγ).2
    exact Classical.choose_spec (branch_of_mixed (Finset.mem_filter.mp h).2)
  have labels_nonempty (b : Branch f Q l) (hb : b ∈ branches) : (labels b).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨γ.val, Finset.mem_filter.mpr ⟨γ.property, γ.property, rfl⟩⟩
  have available (b : Branch f Q l) : ∃ T ⊆ labels b,
      (b.Simple → T = labels b) ∧
      (b ∈ branches → ¬ b.Simple → 0 < T.card ∧ CurveSections (labels b) s T.card ∧
        Demand (labels b) s T) := by
    by_cases hs : b.Simple
    · exact ⟨labels b, Finset.Subset.rfl, fun _ => rfl, fun _ hn => (hn hs).elim⟩
    by_cases hb : b ∈ branches
    · obtain ⟨T, hsub, hd⟩ := maximal_demand (labels b) s (labels_nonempty b hb)
      exact ⟨T, hsub, fun h => (hs h).elim, fun _ _ => hd⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => (hs h).elim, fun h _ => (hb h).elim⟩
  choose demanded demand_sub demand_simple demand_multiple using available
  let points (b : Branch f Q l) := (demanded b).image point
  have points_card (b : Branch f Q l) : (points b).card = (demanded b).card := by
    apply Finset.card_image_of_injOn
    intro γ hγ δ hδ heq
    exact input.distinct (label_sub b (demand_sub b hγ)) (label_sub b (demand_sub b hδ))
      (Polynomial.map_injective embed embed.injective (actualPoint_injective heq))
  have points_on (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) : b.Contains p := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    exact contains_label b γ (demand_sub b hγ)
  have points_next (b : Branch f Q l) (p : JetPoint) (hp : p ∈ points b) :
      MvPolynomial.eval p b.next = 0 := by
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    apply b.next_actual (contains_label b γ (demand_sub b hγ))
    simpa only [Polynomial.natDegree_map] using input.degree γ (label_sub b (demand_sub b hγ))
  have fitQ : InBox (shape Q) cutterBox :=
    ⟨input.box.1.trans (by decide), input.box.2⟩
  have bound4 := h4budget f Q l input.small input.proper fitQ input.positive branches points
    (by
      intro b hb
      obtain ⟨hmember, hnext, hvalue⟩ := h4chart f Q l input.small b
      refine ⟨hmember, points_on b, ?_⟩
      by_cases hs : b.Simple
      · exact Or.inr ⟨b.next, hnext, b.next_proper hs, points_next b⟩
      rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
      · exact Or.inl (by rw [points_card, hone])
      obtain ⟨D, hD, hEval⟩ := hvalue x a
      obtain ⟨δ, hδ, hδvalue⟩ := hwit
      have hδon := contains_label b δ hδ
      have hproper : D ∉ b.curve := fun hmem =>
        hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp (hδon.1 hmem))
      refine Or.inr ⟨D, hD, hproper, ?_⟩
      intro p hp
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
      have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
      exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ)))
        (contains_label b γ (demand_sub b hγ))).mpr hvalueγ)
  have bound5 := h5budget f Q l input.small input.proper fitQ input.positive branches points
    (by
      intro b hb
      obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := h5chart f Q l input.small b
      refine ⟨hgraph, ⟨E, hE, hEeq⟩, points_on b, ?_⟩
      by_cases hs : b.Simple
      · exact Or.inr ⟨H, hH, b.lifted_proper_of_associated hHeq (b.next_proper hs),
          fun p hp hon => b.lifted_zero_of_associated hHeq hon (points_next b p hp)⟩
      rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
      · exact Or.inl (by rw [points_card, hone])
      obtain ⟨D, hD, hEval⟩ := hvalue x a
      obtain ⟨δ, hδ, hδvalue⟩ := hwit
      have hδon := contains_label b δ hδ
      refine Or.inr ⟨D, hD, b.lifted_proper_of_nonzero (point δ) hδon ?_, ?_⟩
      · exact fun hzero => hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp hzero)
      · intro p hp hon
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
        have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
        exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ)
  let simple := branches.filter Branch.Simple
  let multiple := branches.filter (fun b => ¬ b.Simple)
  let e := multiple.equivFin
  let C : Pieces Γ :=
    { n := multiple.card
      piece := fun i => labels (e.symm i).val
      subset := fun i => label_sub (e.symm i).val
      degree := fun i => (demanded (e.symm i).val).card }
  let B := simple.biUnion labels
  have hmultiple (i : Fin C.n) := Finset.mem_filter.mp (e.symm i).property
  refine ⟨C, B,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).2.1,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).1, ?_, ?_⟩
  · intro γ hγ hm
    have hmark : γ ∈ marked := Finset.mem_filter.mpr ⟨hγ, hm⟩
    let b := assign ⟨γ, hmark⟩
    have hb : b ∈ branches := Finset.mem_image.mpr ⟨_, Finset.mem_attach _ _, rfl⟩
    have hlabel : γ ∈ labels b := Finset.mem_filter.mpr ⟨hmark, hmark, rfl⟩
    by_cases hs : b.Simple
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, hlabel⟩)
    have hbm : b ∈ multiple := Finset.mem_filter.mpr ⟨hb, hs⟩
    apply Finset.mem_union_left _
    refine Finset.mem_biUnion.mpr ⟨e ⟨b, hbm⟩, Finset.mem_univ _, ?_⟩
    change γ ∈ labels (e.symm (e ⟨b, hbm⟩)).val
    simpa only [Equiv.symm_apply_apply] using hlabel
  · have htotal : C.total = ∑ b ∈ multiple, (demanded b).card := by
      calc
        C.total = ∑ b : multiple, (demanded b.val).card :=
          Equiv.sum_comp e.symm (fun b : multiple => (demanded b.val).card)
        _ = _ := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach multiple (fun b => (demanded b).card)
    have hsimple : (∑ b ∈ simple, b.weight * (points b).card) =
        ∑ b ∈ simple, (labels b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, demand_simple b hs, Branch.weight, ite_eq_left hs, one_mul]
    have hmult : (∑ b ∈ multiple, b.weight * (points b).card) = 2 * C.total := by
      rw [htotal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, Branch.weight, ite_eq_right hs]
    have hpart : (∑ b ∈ simple, b.weight * (points b).card) +
        (∑ b ∈ multiple, b.weight * (points b).card) =
        ∑ b ∈ branches, b.weight * (points b).card :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hB : B.card ≤ ∑ b ∈ simple, (labels b).card := Finset.card_biUnion_le
    have hpay : 2 * C.total + B.card ≤ ∑ b ∈ branches, b.weight * (points b).card := by
      rw [← hpart, hsimple, hmult, Nat.add_comm (∑ b ∈ simple, (labels b).card)]
      exact Nat.add_le_add_left hB _
    change _ ≤ min (budget4 (shape f).chamber) (budget5 (shape f).chamber)
    exact (Nat.mul_le_mul_left (32 * l) hpay).trans (le_min bound4 bound5)
end
end K1_13_6_2
end
section
namespace K1_13_6_2_3
noncomputable section
open K1_13 K1_13_6
open scoped BigOperators
def ChamberBox (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j ∧ 0 < p.t
def capExponents (p : Shape) : Set (Fin 4 →₀ ℕ) :=
  {m | m.degree ≤ 2 * p.b ∧ (∑ i : Fin 4, i.val * m i) ≤ 2 * p.j ∧ m 3 ≤ 2 * p.t}
instance (p : Shape) : Finite (capExponents p) :=
  ((Finsupp.finite_of_degree_le (2 * p.b)).subset fun _ hm => hm.1).to_subtype
abbrev dimension (J : Ideal GeoJets) := (MvPolynomial.affineHilbertPolynomial J).natDegree
def capCoeff (J : Ideal GeoJets) (d : ℕ) (p : Shape) : ℚ :=
  (MvPolynomial.affineHilbertPolynomial
    (J.comap (MvPolynomial.monomialMap GeoField (capExponents p)).toRingHom)).coeff d
def polarize (H : Shape → ℚ) : List Shape → Shape → ℚ
  | [] => H
  | p :: rest => fun x => polarize H rest (x.plus p) - polarize H rest x
def mixedDegree (J : Ideal GeoJets) (boxes : List Shape) : ℚ :=
  polarize (capCoeff J boxes.length) boxes ⟨3, 3, 1⟩ / 2 ^ boxes.length
def localWeight (J P : Ideal GeoJets) : ℕ := by
  classical
  exact if hp : P.IsPrime then (cycleLength J P hp).toNat else 0
def pointIdeal (x : K1_13_6_2.JetPoint) : Ideal GeoJets := RingHom.ker (MvPolynomial.eval x)
end
end K1_13_6_2_3
end
section
namespace K1_13_6_2_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
lemma anchor_box {f : Row 4} (hf : SmallFactor f) : ChamberBox (shape f).chamber :=
  ⟨(K1_13_7_1.shape_chamber f).1, (K1_13_7_1.shape_chamber f).2, hf.2.1⟩
lemma chart_box (L : ℕ) (p : Shape) (hL : 0 < L) : ChamberBox (chart L p) := by
  refine ⟨(K1_13_7_1.chart_chamber L p).1, (K1_13_7_1.chart_chamber L p).2, ?_⟩
  unfold chart
  have h : 3 ≤ 2 * L * (p.j - 3) + L + 3 := by omega
  exact lt_min (by omega) (Nat.div_pos h (by decide))
lemma cutter_box : ChamberBox cutterBox := ⟨by decide, by decide, by decide⟩
lemma generic_box {P : Row 4} {p : Shape} (hP : InBox (shape P) p) : Box4 p (toGeneric P) := by
  intro m hm
  have hm' := MvPolynomial.support_map_subset genericCoeffs P hm
  have hb := (MvPolynomial.le_totalDegree hm').trans hP.1
  have hj := (Finset.le_sup (f := fun m : Fin 4 →₀ ℕ => m.sum fun i a => i.val * a) hm').trans hP.2.1
  refine ⟨?_, ?_, (MvPolynomial.monomial_le_degreeOf 3 hm').trans hP.2.2⟩
  · simpa [Finsupp.degree_apply, Finsupp.sum_fintype] using hb
  · simpa [Finsupp.sum_fintype] using hj
lemma regular_cut {J : Ideal GeoJets} (hJ : J.IsPrime) {D : GeoJets} (hD : D ∉ J) :
    IsLeftRegular (Ideal.Quotient.mk J D) := by
  have := hJ
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)
lemma cut_dimension {J : Ideal GeoJets} {D : GeoJets} (hD : IsLeftRegular (Ideal.Quotient.mk J D)) :
    dimension (J ⊔ Ideal.span {D}) ≤ dimension J - 1 :=
  (MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hD le_rfl).1
lemma dimension_bot : dimension (⊥ : Ideal GeoJets) = 4 := by
  simp [MvPolynomial.natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card]
lemma pair_regular (f Q : Row 4) (h : IsRelPrime (toGeneric f) (toGeneric Q)) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {toGeneric f}) (toGeneric Q)) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h.dvd_of_dvd_mul_left hx))
lemma intersection_eq (f Q : Row 4) :
    intersectionIdeal f Q = Ideal.span {toGeneric f} ⊔ Ideal.span {toGeneric Q} := by
  rw [intersectionIdeal, ← Ideal.span_union]
  rfl
lemma surface_dimension {f Q : Row 4} (hf : toGeneric f ≠ 0)
    (hproper : IsRelPrime (toGeneric f) (toGeneric Q))
    {S : Ideal GeoJets} (hZ : (intersectionIdeal f Q).IsMinimalPrime S) : dimension S = 2 := by
  have := hZ.isPrime
  rw [intersection_eq] at hZ
  obtain ⟨P, hP, hPZ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hZ.le)
  have := hP.isPrime
  have hPdim := MvPolynomial.natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hf hP
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hPdim
  have hPle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP
  have hPbot : P ≠ ⊥ := by
    intro heq
    exact hf (Ideal.mem_bot.mp (heq ▸ hP.le (Ideal.mem_span_singleton_self (toGeneric f))))
  have hPheight : P.height = 1 := le_antisymm hPle (by
    simpa [Ideal.height_bot] using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hPbot))
  obtain ⟨a, ha⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPheight).principal
  change P = Ideal.span {a} at ha
  have hQ : toGeneric Q ∉ P := by
    intro hQ
    have hfa : a ∣ toGeneric f := Ideal.mem_span_singleton.mp (ha ▸ hP.le (Ideal.mem_span_singleton_self _))
    have hQa : a ∣ toGeneric Q := Ideal.mem_span_singleton.mp (ha ▸ hQ)
    exact Ideal.IsPrime.ne_top' (ha.trans (Ideal.span_singleton_eq_top.mpr (hproper hfa hQa)))
  have hmin : S ∈ (P ⊔ Ideal.span {toGeneric Q}).minimalPrimes := by
    refine ⟨⟨hZ.isPrime, sup_le hPZ (le_sup_right.trans hZ.le)⟩, fun U hU hUZ => ?_⟩
    exact hZ.2 ⟨hU.1, sup_le (hP.le.trans (le_sup_left.trans hU.2)) (le_sup_right.trans hU.2)⟩ hUZ
  have h := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hQ hmin
  change dimension S + 1 = dimension P at h
  change dimension P + 1 = 4 at hPdim
  omega
lemma curve_dimension {f Q l} (b : Branch f Q l) (h : dimension b.surface = 2) :
    dimension b.curve = 1 := by
  have := b.base.isPrime
  have hdim := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one b.proper b.divisor
  change dimension b.curve + 1 = dimension b.surface at hdim
  omega
lemma positive_length {J P : Ideal GeoJets} (hP : J.IsMinimalPrime P) :
    0 < cycleLength J P hP.isPrime ∧ cycleLength J P hP.isPrime ≠ ⊤ := by
  have := hP.isPrime
  let A := Localization.AtPrime P
  let L := J.map (algebraMap GeoJets A)
  change 0 < Module.length A (A ⧸ L) ∧ Module.length A (A ⧸ L) ≠ ⊤
  have hmin : IsLocalRing.maximalIdeal A ∈ L.minimalPrimes := by
    rw [show L = J.map (algebraMap GeoJets A) from rfl,
      IsLocalization.minimalPrimes_map P.primeCompl A, Set.mem_preimage,
      IsLocalization.AtPrime.under_maximalIdeal A P]
    exact hP
  have hL : L ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hmin.le))
  have : Nontrivial (A ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hL
  have : IsArtinianRing (A ⧸ L) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing L hmin
  exact ⟨Module.length_pos, Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_quotient L,
        isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := L))⟩)⟩
lemma weight_cast {J P : Ideal GeoJets} (hP : J.IsMinimalPrime P) :
    (localWeight J P : ℕ∞) = cycleLength J P hP.isPrime := by
  rw [localWeight, dite_eq_left hP.isPrime, ENat.natCast_toNat (positive_length hP).2]
lemma weight_pos {J P : Ideal GeoJets} (hP : J.IsMinimalPrime P) : 0 < localWeight J P := by
  exact ENat.natCast_lt_natCast.mp ((weight_cast hP).symm ▸ (positive_length hP).1)
lemma branch_weight_le {f Q l} (b : Branch f Q l) :
    b.weight ≤ localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve := by
  have hcast : (localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve : ℕ∞) =
      cycleLength (divisorIdeal b.surface (membershipTest b.g)) b.curve b.divisor.isPrime :=
    weight_cast b.divisor
  have hpos : 0 < localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve := weight_pos b.divisor
  by_cases hs : b.Simple
  · simpa [Branch.weight, hs] using (Nat.succ_le_of_lt hpos)
  · rw [Branch.weight, ite_eq_right hs]
    have hne : localWeight (divisorIdeal b.surface (membershipTest b.g)) b.curve ≠ 1 := by
      intro h
      apply hs
      exact hcast.symm.trans (by rw [h]; norm_num)
    omega
lemma same_member {f Q l} {b c : Branch f Q l} (h : b.surface = c.surface) : b.member = c.member := by
  have order (d e : Branch f Q l) (heq : d.surface = e.surface) : ¬ d.r < e.r := by
    intro hlt
    have hmem := e.chart.2.1 (d.r + 1) (by omega)
    rw [← heq, Function.iterate_succ_apply'] at hmem
    exact d.chart.2.2 hmem
  have hr : b.r = c.r := Nat.le_antisymm (Nat.le_of_not_gt (order c b h.symm))
    (Nat.le_of_not_gt (order b c h))
  simp only [Branch.member, Branch.g, hr]
lemma point_injective : Function.Injective pointIdeal := by
  intro x y heq
  funext i
  have hm : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    simp [pointIdeal, RingHom.mem_ker]
  rw [heq] at hm
  exact (sub_eq_zero.mp (by simpa [pointIdeal, RingHom.mem_ker] using hm)).symm
lemma aeval_surjective (x : JetPoint) :
    Function.Surjective (MvPolynomial.aeval x : GeoJets →ₐ[GeoField] GeoField) :=
  fun a => ⟨MvPolynomial.C a, by simp⟩
lemma point_prime (x : JetPoint) : (pointIdeal x).IsPrime := RingHom.ker_isPrime _
lemma point_dimension (x : JetPoint) : dimension (pointIdeal x) = 0 := by
  let φ : GeoJets →ₐ[GeoField] GeoField := MvPolynomial.aeval x
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := φ) (aeval_surjective x)
  have : Module.Finite GeoField (GeoJets ⧸ pointIdeal x) := Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.surjective
  exact MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff.mpr inferInstance
lemma point_degree (x : JetPoint) : mixedDegree (pointIdeal x) [] = 1 := by
  let φ := MvPolynomial.monomialMap GeoField (capExponents ⟨3, 3, 1⟩)
  have hsφ : Function.Surjective φ := by
    apply MvPolynomial.monomialMap_surjective
    intro i
    fin_cases i <;> simp [capExponents, Fin.sum_univ_four]
  let ψ := (MvPolynomial.aeval x).comp φ
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := ψ) ((aeval_surjective x).comp hsφ)
  have : Module.Finite GeoField (_ ⧸ RingHom.ker ψ) :=
    Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.surjective
  change (MvPolynomial.affineHilbertPolynomial (RingHom.ker ψ)).coeff 0 / (2 : ℚ) ^ 0 = 1
  rw [MvPolynomial.affineHilbertPolynomial_eq_C_finrank, Polynomial.coeff_C_zero,
    e.toLinearEquiv.finrank_eq, Module.finrank_self]
  norm_num
lemma point_proper_section {C : Ideal GeoJets} (hC : dimension C = 1) {p : Shape}
    (hp : ChamberBox p) (x : JetPoint) (hx : C ≤ pointIdeal x) :
    ∃ D : GeoJets, Box4 p D ∧ D ∉ C ∧ MvPolynomial.eval x D = 0 := by
  have h : ∃ i : Fin 4, MvPolynomial.X i - MvPolynomial.C (x i) ∉ C := by
    by_contra! hall
    let constants := (Ideal.Quotient.mk C).comp MvPolynomial.C
    have heq : constants.comp (MvPolynomial.eval x) = Ideal.Quotient.mk C := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [constants]
      · intro i
        have hi := Ideal.Quotient.eq_zero_iff_mem.mpr (hall i)
        rw [map_sub, sub_eq_zero] at hi
        simpa [constants] using hi.symm
    have hincl : pointIdeal x ≤ C := by
      intro D hD
      have hz : MvPolynomial.eval x D = 0 := hD
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← DFunLike.congr_fun heq D, RingHom.comp_apply, hz, map_zero]
    have hd := point_dimension x
    rw [le_antisymm hx hincl, hd] at hC
    omega
  obtain ⟨i, hi⟩ := h
  refine ⟨MvPolynomial.X i - MvPolynomial.C (x i), ?_, hi, by simp⟩
  intro m hm
  have hm' := MvPolynomial.support_sub (Fin 4) (MvPolynomial.X i) (MvPolynomial.C (x i)) hm
  rw [Finset.mem_union] at hm'
  obtain hX | hConst := hm'
  · rw [MvPolynomial.support_X] at hX
    have he := Finset.mem_singleton.mp hX
    subst m
    have hb : 1 ≤ p.b := by have := hp.1; have := hp.2.1; have := hp.2.2; omega
    have hj : i.val ≤ p.j := by have := i.isLt; have := hp.2.1; have := hp.2.2; omega
    refine ⟨?_, ?_, ?_⟩
    · simpa [Finsupp.single_apply] using hb
    · simpa [Finsupp.single_apply] using hj
    · simp only [id_eq, Finsupp.single_apply]
      split <;> have := hp.2.2 <;> omega
  · have he : m = 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hConst) (by simp [MvPolynomial.coeff_C, Ne.symm h])
    subst m
    simp
end
end K1_13_6_2_3
end
section
namespace K1_13_6_2_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
def c1 : Prop :=
  ∀ p : Shape, ChamberBox p →
    capCoeff (⊥ : Ideal GeoJets) 4 p = 16 * (volume32 p : ℚ) / 32
def c2 : Prop :=
  ∀ (J : Ideal GeoJets) (p : Shape) (boxes : List Shape),
    ChamberBox p → (∀ q ∈ boxes, ChamberBox q) → dimension J ≤ boxes.length + 1 →
    ∀ D : GeoJets, Box4 p D → IsLeftRegular (Ideal.Quotient.mk J D) →
      mixedDegree (J ⊔ Ideal.span {D}) boxes ≤ mixedDegree J (p :: boxes)
def c3 : Prop :=
  ∀ (J : Ideal GeoJets) (boxes : List Shape),
    (∀ q ∈ boxes, ChamberBox q) → dimension J ≤ boxes.length →
    ∀ S : Finset (Ideal GeoJets), (∀ P ∈ S, J.IsMinimalPrime P) →
      (∑ P ∈ S, (localWeight J P : ℚ) * mixedDegree P boxes) ≤ mixedDegree J boxes
private lemma chamber_plus {x y : Shape} (hx : ChamberBox x) (hy : ChamberBox y) :
    ChamberBox (x.plus y) := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy
  refine ⟨Nat.add_le_add hx₁ hy₁, ?_, Nat.add_pos_left hx₃ _⟩
  change 3 * (x.t + y.t) ≤ x.j + y.j
  omega
private lemma polarize_congr {A B : Shape → ℚ} (h : ∀ p, ChamberBox p → A p = B p)
    {boxes : List Shape} (hboxes : ∀ q ∈ boxes, ChamberBox q) {p : Shape}
    (hp : ChamberBox p) : polarize A boxes p = polarize B boxes p := by
  induction boxes generalizing p with
  | nil => exact h p hp
  | cons q boxes ih =>
    have hq := hboxes q List.mem_cons_self
    have hr := fun r hr => hboxes r (List.mem_cons_of_mem _ hr)
    simp only [polarize, ih hr (chamber_plus hp hq), ih hr hp]
private lemma ambient_degree (h : c1) {p q r s : Shape}
    (hp : ChamberBox p) (hq : ChamberBox q) (hr : ChamberBox r) (hs : ChamberBox s) :
    mixedDegree (⊥ : Ideal GeoJets) [p,q,r,s] ≤ (mixed32 p q r s : ℚ) / 32 := by
  have hb : ChamberBox ⟨3, 3, 1⟩ := ⟨by decide, by decide, by decide⟩
  have hboxes : ∀ u ∈ [p,q,r,s], ChamberBox u := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
    · exact hs
  unfold mixedDegree
  change polarize (capCoeff ⊥ 4) [p,q,r,s] ⟨3,3,1⟩ / (2 : ℚ)^4 ≤ _
  rw [polarize_congr h hboxes hb]
  let n := difference (difference (difference (difference volume32 p) q) r) s ⟨0,0,0⟩
  have hpoly : polarize (fun x => 16 * (volume32 x : ℚ) / 32) [p,q,r,s] ⟨3,3,1⟩ /
      (2 : ℚ)^4 = (n : ℚ) / 32 := by
    simp only [n, polarize, difference, volume32, Shape.plus]
    push_cast
    ring
  rw [hpoly]
  have hn : n ≤ (n.toNat : ℤ) := by omega
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast hn
lemma point_minimal {J : Ideal GeoJets} (hJ : dimension J = 0)
    (x : JetPoint) (hx : J ≤ pointIdeal x) : J.IsMinimalPrime (pointIdeal x) := by
  have : Module.Finite GeoField (GeoJets ⧸ J) :=
    MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff.mp hJ
  have : IsArtinianRing (GeoJets ⧸ J) := IsArtinianRing.of_finite GeoField _
  have : Ring.KrullDimLE 0 (GeoJets ⧸ J) := isArtinianRing_iff_krullDimLE_zero.mp ‹_›
  have hp := point_prime x
  change pointIdeal x ∈ J.minimalPrimes
  rw [Ideal.minimalPrimes_eq_comap]
  refine ⟨(pointIdeal x).map (Ideal.Quotient.mk J), ?_, Ideal.comap_map_mk hx⟩
  have := Ideal.isPrime_map_quotientMk_of_isPrime hx
  exact Ideal.mem_minimalPrimes_of_krullDimLE_zero _
lemma proper_slice_card (h2 : c2) (h3 : c3) {C : Ideal GeoJets} (hC : C.IsPrime)
    (hdim : dimension C = 1) {s : Shape} (hs : ChamberBox s)
    {D : GeoJets} (hD : Box4 s D) (hproper : D ∉ C) (T : Finset JetPoint)
    (hT : ∀ x ∈ T, C ≤ pointIdeal x ∧ MvPolynomial.eval x D = 0) :
    (T.card : ℚ) ≤ mixedDegree C [s] := by
  classical
  let J := C ⊔ Ideal.span {D}
  have hreg := regular_cut hC hproper
  have hJ : dimension J = 0 := by
    have hdrop := cut_dimension hreg
    change dimension J ≤ dimension C - 1 at hdrop
    omega
  have hmin (x : JetPoint) (hx : x ∈ T) : J.IsMinimalPrime (pointIdeal x) :=
    point_minimal hJ x (sup_le (hT x hx).1 ((pointIdeal x).span_singleton_le_iff_mem.mpr (hT x hx).2))
  calc
    (T.card : ℚ) = ∑ _x ∈ T, (1 : ℚ) := by simp
    _ ≤ ∑ x ∈ T, (localWeight J (pointIdeal x) : ℚ) * mixedDegree (pointIdeal x) [] := by
      apply Finset.sum_le_sum
      intro x hx
      rw [point_degree, mul_one]
      exact_mod_cast Nat.succ_le_of_lt (weight_pos (hmin x hx))
    _ = ∑ P ∈ T.image pointIdeal, (localWeight J P : ℚ) * mixedDegree P [] :=
      (Finset.sum_image (f := fun P => (localWeight J P : ℚ) * mixedDegree P [])
        point_injective.injOn).symm
    _ ≤ mixedDegree J [] := h3 J [] (by simp) (by simp [hJ]) _ (by
      intro P hP
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
      exact hmin x hx)
    _ ≤ mixedDegree C [s] := h2 C s [] hs (by simp) (by simp [hdim]) D hD hreg
lemma slice_card (h2 : c2) (h3 : c3) {f Q l} (b : Branch f Q l)
    (hdim : dimension b.curve = 1) (T : Finset JetPoint)
    (hT : ∀ x ∈ T, b.Contains x) (hS : Slice4 b T) :
    (T.card : ℚ) ≤ mixedDegree b.curve [chart (taylorLength + 2) (shape f).chamber] := by
  classical
  let s := chart (taylorLength + 2) (shape f).chamber
  have hs : ChamberBox s := chart_box _ _ (by decide)
  rcases hS with hone | ⟨D, hD, hproper, hzero⟩
  · by_cases hemp : T = ∅
    · rw [hemp]
      simpa using h3 b.curve [s] (by simpa using hs) (by simp [hdim]) ∅ (by simp)
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hsingle : T = {x} := by
        symm
        apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hx)
        simpa using hone
      obtain ⟨D, hD, hproper, hzero⟩ := point_proper_section hdim hs x (hT x hx).1
      exact proper_slice_card h2 h3 b.divisor.isPrime hdim hs hD hproper T (by
        intro y hy
        have hxy : y = x := by simpa [hsingle] using hy
        exact ⟨(hT y hy).1, by rw [hxy]; exact hzero⟩)
  · exact proper_slice_card h2 h3 b.divisor.isPrime hdim hs hD hproper T
      (fun x hx => ⟨(hT x hx).1, hzero x hx⟩)
lemma surface_slice_sum (h2 : c2) (h3 : c3) {f Q l} (ref : Branch f Q l)
    (hdim : dimension ref.surface = 2) (F : Finset (Branch f Q l))
    (T : Branch f Q l → Finset JetPoint) (hF : ∀ b ∈ F, b.surface = ref.surface)
    (hmember : Box4 (chart (taylorLength + 1) (shape f).chamber) ref.member)
    (hT : ∀ b ∈ F, (∀ x ∈ T b, b.Contains x) ∧ Slice4 b (T b)) :
    (∑ b ∈ F, ((b.weight * (T b).card : ℕ) : ℚ)) ≤
      mixedDegree ref.surface [chart (taylorLength + 1) (shape f).chamber,
        chart (taylorLength + 2) (shape f).chamber] := by
  classical
  let p := chart (taylorLength + 1) (shape f).chamber
  let s := chart (taylorLength + 2) (shape f).chamber
  have hp : ChamberBox p := chart_box _ _ (by decide)
  have hs : ChamberBox s := chart_box _ _ (by decide)
  let J := ref.surface ⊔ Ideal.span {ref.member}
  have hcut (b) (hb : b ∈ F) : divisorIdeal b.surface (membershipTest b.g) = J := by
    change b.surface ⊔ Ideal.span {b.member} = J
    rw [hF b hb, same_member (hF b hb)]
  have hreg := regular_cut ref.base.isPrime ref.proper
  have hJdim : dimension J ≤ 1 := (cut_dimension hreg).trans (by simp [hdim])
  calc
    _ ≤ ∑ b ∈ F, (localWeight J b.curve : ℚ) * mixedDegree b.curve [s] := by
      apply Finset.sum_le_sum
      intro b hb
      have hdimB := curve_dimension b ((hF b hb).symm ▸ hdim)
      have hS := slice_card h2 h3 b hdimB (T b) (hT b hb).1 (hT b hb).2
      have hW := (hcut b hb) ▸ branch_weight_le b
      push_cast
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hW) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _))
    _ = ∑ P ∈ F.image Branch.curve, (localWeight J P : ℚ) * mixedDegree P [s] :=
      (Finset.sum_image (f := fun P => (localWeight J P : ℚ) * mixedDegree P [s]) (fun b hb c hc heq =>
        Branch.eq_of_surface_curve ((hF b hb).trans (hF c hc).symm) heq)).symm
    _ ≤ mixedDegree J [s] := h3 J [s] (by simpa using hs) (by simpa using hJdim) _ (by
      intro P hP
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
      exact hcut b hb ▸ b.divisor)
    _ ≤ mixedDegree ref.surface [p,s] :=
      h2 ref.surface p [s] hp (by simpa using hs) (by simp [hdim]) ref.member hmember hreg
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_2.c3 := by
  classical
  intro f Q l hf hproper hQ _ F T hT
  let p := (shape f).chamber
  let r := chart (taylorLength + 1) p
  let s := chart (taylorLength + 2) p
  have hp : ChamberBox p := anchor_box hf
  have hr : ChamberBox r := chart_box _ _ (by decide)
  have hs : ChamberBox s := chart_box _ _ (by decide)
  have hboxes : ∀ q ∈ [r,s], ChamberBox q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact hq.elim (fun h => h ▸ hr) (fun h => h ▸ hs)
  let J := intersectionIdeal f Q
  let H : Ideal GeoJets := Ideal.span {toGeneric f}
  have hpair := K1_13_7_1.proper_generic f Q hf.1 hproper
  have hf0 : toGeneric f ≠ 0 := by
    intro hz
    exact hf.1.ne_zero (K1_13_7_1.toGeneric_injective (hz.trans (map_zero _).symm))
  have hregF : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (toGeneric f)) :=
    regular_cut (by infer_instance) (by simpa using hf0)
  have hregQ := pair_regular f Q hpair
  have hH : dimension H ≤ 3 := by
    simpa [H, dimension_bot] using cut_dimension hregF
  have hJ : dimension J ≤ 2 := by
    rw [show J = H ⊔ Ideal.span {toGeneric Q} from intersection_eq f Q]
    have hdrop : dimension (H ⊔ Ideal.span {toGeneric Q}) ≤ dimension H - 1 := cut_dimension hregQ
    exact hdrop.trans (by omega)
  let surfaces := F.image Branch.surface
  let fiber (P : Ideal GeoJets) := F.filter (fun b => b.surface = P)
  let cost (b : Branch f Q l) : ℚ := ((b.weight * (T b).card : ℕ) : ℚ)
  have hsurface (P : Ideal GeoJets) (hP : P ∈ surfaces) :
      J.IsMinimalPrime P ∧ l ≤ localWeight J P ∧
      (∑ b ∈ fiber P, cost b) ≤ mixedDegree P [r,s] := by
    obtain ⟨ref, href, rfl⟩ := Finset.mem_image.mp hP
    have hl : (l : ℕ∞) ≤ (localWeight J ref.surface : ℕ∞) := by
      rw [weight_cast ref.base]
      exact ref.high
    refine ⟨ref.base, ENat.natCast_le_natCast.mp hl, ?_⟩
    exact surface_slice_sum h2 h3 ref (surface_dimension hf0 hpair ref.base) _ T
      (fun _ hb => (Finset.mem_filter.mp hb).2) (hT ref href).1
      (fun b hb => (hT b (Finset.mem_filter.mp hb).1).2)
  have hcalc : (l : ℚ) * (∑ b ∈ F, cost b) ≤ (budget4 p : ℚ) / 32 := by
    calc
      _ = ∑ P ∈ surfaces, (l : ℚ) * ∑ b ∈ fiber P, cost b := by
        rw [← Finset.mul_sum]
        congr 1
        exact (Finset.sum_fiberwise_of_maps_to (fun _ hb => Finset.mem_image_of_mem _ hb) cost).symm
      _ ≤ ∑ P ∈ surfaces, (localWeight J P : ℚ) * mixedDegree P [r,s] := by
        apply Finset.sum_le_sum
        intro P hP
        obtain ⟨_, hl, hsum⟩ := hsurface P hP
        have hnonneg : 0 ≤ ∑ b ∈ fiber P, cost b := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hnonneg).trans
          (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
      _ ≤ mixedDegree J [r,s] := h3 J [r,s] hboxes (by simpa using hJ) surfaces
        (fun P hP => (hsurface P hP).1)
      _ ≤ mixedDegree H [cutterBox,r,s] := by
        rw [show J = H ⊔ Ideal.span {toGeneric Q} from intersection_eq f Q]
        exact h2 H cutterBox [r,s] cutter_box hboxes (by simpa using hH) _ (generic_box hQ) hregQ
      _ ≤ mixedDegree (⊥ : Ideal GeoJets) [p,cutterBox,r,s] := by
        rw [show H = (⊥ : Ideal GeoJets) ⊔ Ideal.span {toGeneric f} by simp [H]]
        apply h2 _ p [cutterBox,r,s] hp _ (by simp) _ _ hregF
        · intro q hq
          exact (List.mem_cons.mp hq).elim (fun h => h ▸ cutter_box) (hboxes q)
        · exact generic_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
      _ ≤ _ := ambient_degree h1 hp cutter_box hr hs
  have hfinal := (le_div_iff₀ (by norm_num : (0 : ℚ) < 32)).mp hcalc
  rw [mul_comm _ (32 : ℚ), ← mul_assoc] at hfinal
  dsimp only [cost, p] at hfinal
  exact_mod_cast hfinal
end
end K1_13_6_2_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_1
open K1_13 K1_13_6_2_3
open scoped Pointwise
theorem cap_coords (p : Shape) (e : Fin 4 →₀ ℕ) :
    e ∈ capExponents p ↔
      e 0 + e 1 + e 2 + e 3 ≤ 2 * p.b ∧
      e 1 + 2 * e 2 + 3 * e 3 ≤ 2 * p.j ∧ e 3 ≤ 2 * p.t := by
  unfold capExponents
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_four, add_assoc]
theorem zero_mem_cap (p : Shape) : 0 ∈ capExponents p := by
  simp [cap_coords]
theorem cap_add {p q : Shape} (hp : ChamberBox p) (hq : ChamberBox q) :
    capExponents p + capExponents q = capExponents (p.plus q) := by
  ext e
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [cap_coords, Shape.plus, Finsupp.add_apply] at *
    omega
  · intro he
    obtain ⟨hpb, hpj, _⟩ := hp
    obtain ⟨hqb, hqj, _⟩ := hq
    rw [cap_coords] at he
    simp only [Shape.plus] at he
    let z := min (e 3) (2 * p.t)
    let z' := e 3 - z
    have hz : z + z' = e 3 ∧ z ≤ 2 * p.t ∧ z' ≤ 2 * q.t := by dsimp [z, z']; omega
    let w := 2 * p.j - 3 * z
    let w' := 2 * q.j - 3 * z'
    have hw : w + 3 * z = 2 * p.j ∧ w' + 3 * z' = 2 * q.j := by
      dsimp [w, w']
      omega
    have hhalf : (w + w') / 2 = w / 2 + w' / 2 := by
      by_cases h : e 3 ≤ 2 * p.t
      · have hz' : z' = 0 := by dsimp [z, z']; omega
        omega
      · have hze : z = 2 * p.t := min_eq_right (by omega)
        omega
    let y := min (e 2) (w / 2)
    let y' := e 2 - y
    have hy : y + y' = e 2 ∧ 2 * y ≤ w ∧ 2 * y' ≤ w' := by dsimp [y, y']; omega
    let x := min (e 1) (w - 2 * y)
    let x' := e 1 - x
    have hx : x + x' = e 1 ∧ x + 2 * y ≤ w ∧ x' + 2 * y' ≤ w' := by
      dsimp [x, x']
      omega
    let u := min (e 0) (2 * p.b - (x + y + z))
    let u' := e 0 - u
    have hu : u + u' = e 0 ∧ u + x + y + z ≤ 2 * p.b ∧
        u' + x' + y' + z' ≤ 2 * q.b := by
      dsimp [u, u']
      omega
    let a : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u, x, y, z]
    let b : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u', x', y', z']
    refine ⟨a, (cap_coords p a).mpr ?_, b, (cap_coords q b).mpr ?_, ?_⟩
    · change u + x + y + z ≤ 2 * p.b ∧ x + 2 * y + 3 * z ≤ 2 * p.j ∧ z ≤ 2 * p.t
      omega
    · change u' + x' + y' + z' ≤ 2 * q.b ∧ x' + 2 * y' + 3 * z' ≤ 2 * q.j ∧ z' ≤ 2 * q.t
      omega
    · ext i
      fin_cases i
      · exact hu.1
      · exact hx.1
      · exact hy.1
      · exact hz.1
theorem nsmul_cap (p : Shape) (hp : ChamberBox p) (n : ℕ) :
    n • capExponents p = capExponents (p.scale n) := by
  induction n with
  | zero =>
      rw [zero_smul]
      ext e
      simp only [Set.mem_zero, cap_coords, Shape.scale, zero_mul, mul_zero]
      constructor
      · rintro rfl
        simp
      · rintro ⟨h, _, _⟩
        ext i
        fin_cases i
        · change e 0 = 0; omega
        · change e 1 = 0; omega
        · change e 2 = 0; omega
        · change e 3 = 0; omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Shape.scale]
      have hscaled : ChamberBox (p.scale n) := by
        obtain ⟨hb, hj, ht⟩ := hp
        refine ⟨Nat.mul_le_mul_left n hb, ?_, Nat.mul_pos (Nat.pos_of_ne_zero hn) ht⟩
        change 3 * (n * p.t) ≤ n * p.j
        rw [Nat.mul_left_comm 3 n]
        exact Nat.mul_le_mul_left n hj
      rw [succ_nsmul, ih, cap_add hscaled hp]
      congr 1
      cases p
      simp [Shape.plus, Shape.scale, Nat.succ_mul]
end K1_13_6_2_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_1
open K1_13 K1_13_6_2_3 Finset
open scoped BigOperators
noncomputable section
private def slices (b j t : ℕ) :=
  Σ z : Fin (2 * t + 1), Σ y : Fin ((2 * j - 3 * z.val) / 2 + 1),
    Σ x : Fin (2 * j - 3 * z.val - 2 * y.val + 1),
      Fin (2 * b - (z.val + y.val + x.val) + 1)
def cap_slices (p : Shape) (hp : ChamberBox p) :
    capExponents p ≃ slices p.b p.j p.t where
  toFun e := by
    have he := (cap_coords p e.val).mp e.property
    have hb := he.1
    have hj := he.2.1
    have ht := he.2.2
    let z : Fin (2 * p.t + 1) := ⟨e.val 3, by omega⟩
    let y : Fin ((2 * p.j - 3 * z.val) / 2 + 1) := ⟨e.val 2, by dsimp [z]; omega⟩
    let x : Fin (2 * p.j - 3 * z.val - 2 * y.val + 1) := ⟨e.val 1, by dsimp [z, y]; omega⟩
    exact ⟨z, y, x, ⟨e.val 0, by dsimp [z, y, x]; omega⟩⟩
  invFun a := by
    rcases a with ⟨z, y, x, u⟩
    have hz := z.isLt
    have hy := y.isLt
    have hx := x.isLt
    have hu := u.isLt
    have hb := hp.1
    have hj := hp.2.1
    refine ⟨Finsupp.equivFunOnFinite.symm ![u.val, x.val, y.val, z.val], (cap_coords p _).mpr ?_⟩
    change u.val + x.val + y.val + z.val ≤ 2 * p.b ∧
      x.val + 2 * y.val + 3 * z.val ≤ 2 * p.j ∧ z.val ≤ 2 * p.t
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv a := by
    rcases a with ⟨⟨z, hz⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨u, hu⟩⟩
    rfl
private theorem sum_affine (a d : ℚ) (n : ℕ) :
    (∑ x ∈ range n, (a + d * (x : ℚ))) = n * a + d * n * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
private def slice (W C : ℕ) : ℚ :=
  ((C : ℚ) + 1 - (W : ℚ) / 2) *
    ((W / 2 : ℕ) + (1 : ℚ)) * ((W / 2 : ℕ) + (1 : ℚ) + (W % 2 : ℕ))
theorem slice_count (W C : ℕ) (h : W ≤ C) :
    (∑ y ∈ range (W / 2 + 1), ∑ x ∈ range (W - 2 * y + 1),
      ((C - (y + x) + 1 : ℕ) : ℚ)) = slice W C := by
  calc
    _ = ∑ y ∈ range (W / 2 + 1),
        (((C : ℚ) + 1 - (W : ℚ) / 2) * ((W : ℚ) + 1 - 2 * (y : ℚ))) := by
      apply sum_congr rfl
      intro y hy
      have hy' := mem_range.mp hy
      calc
        _ = ∑ x ∈ range (W - 2 * y + 1), ((C : ℚ) - y + 1 + (-1) * (x : ℚ)) := by
          apply sum_congr rfl
          intro x hx
          have hx' := mem_range.mp hx
          have hxy : y + x ≤ C := by omega
          push_cast [Nat.cast_sub hxy]
          ring
        _ = _ := by
          rw [sum_affine]
          have h2y : 2 * y ≤ W := by omega
          push_cast [Nat.cast_sub h2y]
          ring
    _ = _ := by
      rw [← mul_sum]
      have hlin (y : ℕ) : (W : ℚ) + 1 - 2 * (y : ℚ) = (W : ℚ) + 1 + (-2) * (y : ℚ) := by
        ring
      simp_rw [hlin]
      rw [sum_affine]
      have hW : (W : ℚ) = 2 * ((W / 2 : ℕ) : ℚ) + ((W % 2 : ℕ) : ℚ) := by
        exact_mod_cast (show W = 2 * (W / 2) + W % 2 by omega)
      unfold slice
      push_cast
      rw [hW]
      ring
theorem cap_count (p : Shape) (hp : ChamberBox p) :
    ((capExponents p).ncard : ℚ) =
      ∑ z ∈ range (2 * p.t + 1), slice (2 * p.j - 3 * z) (2 * p.b - z) := by
  classical
  let : Fintype (slices p.b p.j p.t) := by unfold slices; infer_instance
  rw [← Nat.card_coe_set_eq, Nat.card_congr (cap_slices p hp), Nat.card_eq_fintype_card]
  change (Fintype.card (Σ z : Fin (2 * p.t + 1), Σ y : Fin ((2 * p.j - 3 * z.val) / 2 + 1),
    Σ x : Fin (2 * p.j - 3 * z.val - 2 * y.val + 1),
      Fin (2 * p.b - (z.val + y.val + x.val) + 1)) : ℚ) = _
  simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  rw [Fin.sum_univ_eq_sum_range (fun z => ∑ y : Fin ((2 * p.j - 3 * z) / 2 + 1),
    ∑ x : Fin (2 * p.j - 3 * z - 2 * y.val + 1), ((2 * p.b - (z + y.val + x.val) + 1 : ℕ) : ℚ))]
  apply sum_congr rfl
  intro z _
  have hW : 2 * p.j - 3 * z ≤ 2 * p.b - z := by have := hp.1; omega
  rw [← slice_count _ _ hW]
  rw [Fin.sum_univ_eq_sum_range (fun y => ∑ x : Fin (2 * p.j - 3 * z - 2 * y + 1),
    ((2 * p.b - (z + y + x.val) + 1 : ℕ) : ℚ))]
  apply sum_congr rfl
  intro y _
  rw [Fin.sum_univ_eq_sum_range (fun x => ((2 * p.b - (z + y + x) + 1 : ℕ) : ℚ))]
  simp only [Nat.sub_sub, Nat.add_assoc]
private def evenSlice (b j i : ℚ) : ℚ := (j - 3 * i + 1) ^ 2 * (2 * b + 1 - j + i)
private def oddSlice (b j i : ℚ) : ℚ :=
  (j - 3 * i - 1) * (j - 3 * i) * (2 * b + 3 / 2 - j + i)
theorem slice_even (b j i : ℕ) (hi : 3 * i ≤ j) (hb : j ≤ b) :
    slice (2 * j - 3 * (2 * i)) (2 * b - 2 * i) = evenSlice b j i := by
  have hW : 2 * j - 3 * (2 * i) = 2 * (j - 3 * i) := by omega
  have hC : 2 * i ≤ 2 * b := by omega
  rw [hW]
  simp only [slice, evenSlice, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
    Nat.mul_mod_right, Nat.cast_zero, add_zero]
  push_cast [Nat.cast_sub hi, Nat.cast_sub hC]
  ring
theorem slice_odd (b j i : ℕ) (hi : 3 * i + 3 ≤ j) (hb : j ≤ b) :
    slice (2 * j - 3 * (2 * i + 1)) (2 * b - (2 * i + 1)) = oddSlice b j i := by
  have hW : 3 * (2 * i + 1) ≤ 2 * j := by omega
  have hC : 2 * i + 1 ≤ 2 * b := by omega
  have hdiv : (2 * j - 3 * (2 * i + 1)) / 2 = j - (3 * i + 2) := by omega
  have hmod : (2 * j - 3 * (2 * i + 1)) % 2 = 1 := by omega
  simp only [slice, oddSlice, hdiv, hmod]
  push_cast [Nat.cast_sub hW, Nat.cast_sub hC, Nat.cast_sub (show 3 * i + 2 ≤ j by omega)]
  ring
private theorem sum_pair (f : ℕ → ℚ) (n : ℕ) :
    (∑ z ∈ range (2 * n), f z) = ∑ i ∈ range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, show 2 * n + 2 = (2 * n + 1) + 1 by omega]
    rw [sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring
private def pair (b j i : ℚ) : ℚ := evenSlice b j i + oddSlice b j i
private def pairedSum (b j n : ℚ) : ℚ :=
  let f := pair b j
  n * f 0 + n * (n - 1) / 2 * (f 1 - f 0) +
    n * (n - 1) * (n - 2) / 6 * (f 2 - 2 * f 1 + f 0) +
    n * (n - 1) * (n - 2) * (n - 3) / 24 * (f 3 - 3 * f 2 + 3 * f 1 - f 0)
theorem paired_sum (b j : ℚ) (n : ℕ) :
    (∑ i ∈ range n, pair b j i) = pairedSum b j n := by
  induction n with
  | zero => simp [pairedSum]
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    dsimp [pairedSum, pair, evenSlice, oddSlice]
    ring
theorem count_formula (p : Shape) (hp : ChamberBox p) :
    ((capExponents p).ncard : ℚ) = pairedSum p.b p.j p.t + evenSlice p.b p.j p.t := by
  rw [cap_count p hp, sum_range_succ, sum_pair, slice_even _ _ _ hp.2.1 hp.1, ← paired_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  rw [slice_even _ _ _ (by have := hp.2.1; omega) hp.1,
    slice_odd _ _ _ (by have := hp.2.1; omega) hp.1]
  rfl
def latticePolynomial (p : Shape) : Polynomial ℚ :=
  let b : ℚ := p.b
  let j : ℚ := p.j
  let t : ℚ := p.t
  Polynomial.C (16 * (volume32 p : ℚ) / 32) * Polynomial.X ^ 4 +
    Polynomial.C (2*b*j^2 + 2*b*j*t - 3*b*t^2 - j^3 + (3/2)*j^2*t -
      (11/2)*j*t^2 + (13/2)*t^3) * Polynomial.X ^ 3 +
    Polynomial.C (4*b*j - b*t - j^2 + 2*j*t - (5/2)*t^2) * Polynomial.X ^ 2 +
    Polynomial.C (2*b + j - t/2) * Polynomial.X ^ 1 + Polynomial.C 1
theorem latticePolynomial_coeff (p : Shape) :
    (latticePolynomial p).coeff 4 = 16 * (volume32 p : ℚ) / 32 := by
  simp only [latticePolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  norm_num
theorem latticePolynomial_eval (p : Shape) (hp : ChamberBox p) (n : ℕ) (hn : 0 < n) :
    (latticePolynomial p).eval (n : ℚ) = ((capExponents (p.scale n)).ncard : ℚ) := by
  have hscaled : ChamberBox (p.scale n) := by
    obtain ⟨hb, hj, ht⟩ := hp
    refine ⟨Nat.mul_le_mul_left n hb, ?_, Nat.mul_pos hn ht⟩
    change 3 * (n * p.t) ≤ n * p.j
    rw [Nat.mul_left_comm 3 n]
    exact Nat.mul_le_mul_left n hj
  rw [count_formula _ hscaled]
  simp only [latticePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, pairedSum, pair, evenSlice, oddSlice, Shape.scale, volume32]
  push_cast
  ring
end
end K1_13_6_2_3_1
end
section
namespace K1_13_6_2_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_6_2 K1_13_7_1
open scoped BigOperators
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem topPartial_bound (w : Fin 4 → ℕ) (P : Row 4) :
    W w (separant P) ≤ W w P - w 3 :=
  weightedTotalDegree_pderiv_le_sub w 3 P
private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]
private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj
private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem flow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) :
    W w (flowNumerator g P) ≤ d + (B - w 3) + Δ := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (partialFlow_bound w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h : w 3 ≤ d
    · have hp := (topPartial_bound w P).trans (Nat.sub_le_sub_right hP (w 3))
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (partialFlow_bound w Δ hshift g hg) hp).trans (by omega))
    · rw [separant, pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero, weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem step_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (hP : W w P ≤ d) (a : ℕ) :
    W w (clearedStep g a P) ≤ d + (2 * (B - w 3) + Δ) := by
  have hsep := (topPartial_bound w g).trans (Nat.sub_le_sub_right hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add hsep (flow_bound w Δ hshift hB hg hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [← map_natCast (MvPolynomial.C : Geom[X] →+* Row 4)]
    exact (Nat.add_le_add ((weight_const_mul_le _ _ _).trans (flow_bound w Δ hshift hB hg hsep))
      hP).trans (by omega)
theorem jet_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) {g : Row 4} {B : ℕ}
    (hB : w 3 ≤ B) (hg : W w g ≤ B) (n : ℕ) :
    W w (jetNumerator g n) ≤ w 0 + n * (2 * (B - w 3) + Δ) := by
  induction n with
  | zero => simpa only [jetNumerator, zero_mul, add_zero] using weight_X_le (R := Geom[X]) w 0
  | succ n ih =>
    simpa only [jetNumerator, Nat.add_mul, one_mul, Nat.add_assoc] using
      step_bound w Δ hshift hB hg ih (2 * n)
private theorem iterate_bound (w : Fin 4 → ℕ) (f : Row 4) (r : ℕ) :
    W w ((separant^[r]) f) ≤ W w f := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (weightedTotalDegree_pderiv_le w 3 _).trans ih
theorem branch_box {f Q l} (b : Branch f Q l) : InBox (shape b.g) (shape f).chamber := by
  refine ⟨?_, ?_, ?_⟩
  · change b.g.totalDegree ≤ max f.totalDegree (indexDegree f)
    exact (by simpa only [Branch.g, weightedTotalDegree_one] using iterate_bound 1 f b.r :
      b.g.totalDegree ≤ f.totalDegree).trans (le_max_left _ _)
  · simpa only [Shape.chamber, shape, indexDegree_eq, Branch.g] using iterate_bound Fin.val f b.r
  · simpa only [Shape.chamber, shape, Branch.g, weightedTotalDegree_piSingle] using
      iterate_bound (Pi.single 3 1) f b.r
theorem oldBox_of_fits {P : GeoJets} {p : Shape} (h : GeoFits P p) : Box4 p P := by
  intro m hm
  have h₁ := le_weightedTotalDegree (1 : Fin 4 → ℕ) hm
  have h₂ := (le_weightedTotalDegree Fin.val hm).trans h.2.1
  have h₃ := (le_weightedTotalDegree (Pi.single (3 : Fin 4) (1 : ℕ)) hm).trans
    (by simpa only [weightedTotalDegree_piSingle] using h.2.2)
  rw [weightedTotalDegree_one] at h₁
  refine ⟨?_, ?_, ?_⟩
  · have ht := h₁.trans h.1
    rw [Finsupp.weight_eq_sum] at ht
    simpa only [id_eq, Pi.one_apply, smul_eq_mul, mul_one] using ht
  · rw [Finsupp.weight_eq_sum] at h₂
    simpa only [id_eq, smul_eq_mul, Nat.mul_comm] using h₂
  · simpa only [id_eq, Finsupp.weight_single_one_apply] using h₃
private def topWeight : Fin 4 → ℕ := Pi.single 3 1
theorem fits_chart_of_weights (P : Row 4) (p : Shape) (L : ℕ)
    (hb : W 1 P ≤ 1 + 2 * L * (p.b - 1))
    (hj : W Fin.val P ≤ 2 * L * (p.j - 3) + L + 3)
    (ht : W topWeight P ≤ 2 * L * (p.t - 1) + L + 1) :
    GeoFits (toGeneric P) (chart L p) := by
  apply toGeneric_fits
  refine ⟨?_, ?_, ?_⟩
  · change P.totalDegree ≤ max _ _
    exact (by simpa only [weightedTotalDegree_one] using hb :
      P.totalDegree ≤ 1 + 2 * L * (p.b - 1)).trans (le_max_left _ _)
  · change indexDegree P ≤ _
    rwa [indexDegree_eq]
  · change P.degreeOf 3 ≤ min _ _
    apply le_min
    · simpa only [topWeight, weightedTotalDegree_piSingle] using ht
    · have h := (top_le_index P).trans hj
      omega
theorem three_weights {g P : Row 4} {p : Shape} {L : ℕ} (hB : InBox (shape g) p)
    (hp : Chamber p) (ht : 0 < p.t)
    (bound : ∀ (w : Fin 4 → ℕ) (Δ d₀ B : ℕ),
      (∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) → (∀ i, w i ≤ d₀) →
      w 3 ≤ B → W w g ≤ B → W w P ≤ d₀ + 2 * L * (B - w 3) + L * Δ) :
    GeoFits (toGeneric P) (chart L p) := by
  have hb : 1 ≤ p.b := by have := hp.1; have := hp.2; omega
  have hj : 3 ≤ p.j := by have := hp.2; omega
  have h₁ : W 1 g ≤ p.b := by simpa only [shape, weightedTotalDegree_one] using hB.1
  have h₂ : W Fin.val g ≤ p.j := by simpa only [shape, indexDegree_eq] using hB.2.1
  have h₃ : W topWeight g ≤ p.t := by
    simpa only [topWeight, shape, weightedTotalDegree_piSingle] using hB.2.2
  have hshift : ∀ i : Fin 3, topWeight i.succ ≤ topWeight i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  have hw : ∀ i, topWeight i ≤ 1 := by
    intro i
    fin_cases i <;> decide
  have hw3 : topWeight 3 = 1 := by decide
  apply fits_chart_of_weights
  · have h := bound 1 0 1 p.b (fun _ => by simp) (fun _ => le_rfl) hb h₁
    simpa only [Pi.one_apply, mul_zero, add_zero] using h
  · have h := bound Fin.val 1 3 p.j (fun _ => by rfl)
      (fun j : Fin 4 => Nat.le_of_lt_succ j.isLt) hj h₂
    change W Fin.val P ≤ 3 + 2 * L * (p.j - 3) + L * 1 at h
    simpa only [mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
  · have h := bound topWeight 1 1 p.t hshift hw (hw3.symm ▸ ht) h₃
    simpa only [hw3, mul_one, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using h
theorem separant_pow_bound (w : Fin 4 → ℕ) {g : Row 4} {B : ℕ} (hg : W w g ≤ B) (a : ℕ) :
    W w (separant g ^ a) ≤ a * (B - w 3) :=
  (weightedTotalDegree_pow_le _ _ _).trans
    (Nat.mul_le_mul_left _ ((topPartial_bound w g).trans (Nat.sub_le_sub_right hg _)))
theorem jet_fits {g : Row 4} {p : Shape} (hB : InBox (shape g) p) (hp : Chamber p)
    (ht : 0 < p.t) {n L : ℕ} (hn : n ≤ L) :
    GeoFits (toGeneric (jetNumerator g n)) (chart L p) := by
  apply three_weights hB hp ht
  intro w Δ d₀ B hshift hw hwB hg
  calc
    _ ≤ w 0 + n * (2 * (B - w 3) + Δ) := jet_bound w Δ hshift hwB hg n
    _ ≤ d₀ + L * (2 * (B - w 3) + Δ) :=
      Nat.add_le_add (hw 0) (Nat.mul_le_mul_right _ hn)
    _ = _ := by ring
end
end K1_13_6_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_1
open K1_13 K1_13_6 K1_13_6_2_3 MvPolynomial
open scoped Pointwise
noncomputable section
private theorem monomial_preimage (S : Set (Fin 4 →₀ ℕ)) (n : ℕ) (e : Fin 4 →₀ ℕ)
    (he : e ∈ n • S) :
    ∃ P : MvPolynomial S GeoField, P.totalDegree ≤ n ∧
      monomialMap GeoField S P = monomial e 1 := by
  induction n generalizing e with
  | zero =>
      simp only [zero_smul, Set.mem_zero] at he
      subst e
      exact ⟨1, by simp, by simp⟩
  | succ n ih =>
      rw [succ_nsmul] at he
      obtain ⟨a, ha, b, hb, rfl⟩ := he
      obtain ⟨P, hn, hP⟩ := ih a ha
      refine ⟨P * MvPolynomial.X ⟨b, hb⟩, (totalDegree_mul _ _).trans ?_, ?_⟩
      · simpa only [totalDegree_X] using Nat.add_le_add_right hn 1
      · rw [map_mul, hP, monomialMap_X, monomial_mul_monomial, mul_one]
private theorem cap_surjective (p : Shape) (hp : ChamberBox p) :
    Function.Surjective (monomialMap GeoField (capExponents p)) := by
  apply monomialMap_surjective
  intro i
  have ⟨hb, hj, ht⟩ := hp
  fin_cases i <;> norm_num [cap_coords, Finsupp.single_apply] <;> omega
theorem cap_hilbert_count (p : Shape) (hp : ChamberBox p) (n : ℕ) :
    affineHilbertFunction
        ((⊥ : Ideal GeoJets).comap (monomialMap GeoField (capExponents p)).toRingHom) n =
      (capExponents (p.scale n)).ncard := by
  classical
  let φ := monomialMap GeoField (capExponents p)
  let I := RingHom.ker φ.toRingHom
  let g : (MvPolynomial (capExponents p) GeoField ⧸ I) ≃ₐ[GeoField] GeoJets :=
    Ideal.quotientKerAlgEquivOfSurjective (f := φ) (cap_surjective p hp)
  have hg (P : MvPolynomial (capExponents p) GeoField) : g (Ideal.Quotient.mk I P) = φ P :=
    Ideal.quotientKerAlgEquivOfSurjective_mk (f := φ) (cap_surjective p hp) P
  let M := restrictSupport GeoField (capExponents (p.scale n))
  have hmap : (quotientDegreeLE I n).map g.toLinearEquiv.toLinearMap = M := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hv
      change g (Ideal.Quotient.mk I P) ∈ M
      rw [hg]
      dsimp [M]
      rw [← nsmul_cap p hp n]
      exact monomialMap_mem_restrictSupport_nsmul (zero_mem_cap p) hP
    · dsimp [M]
      rw [restrictSupport_eq_span, Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      rw [← nsmul_cap p hp n] at he
      obtain ⟨P, hN, hP⟩ := monomial_preimage _ n e he
      refine ⟨Ideal.Quotient.mk I P, mk_mem_quotientDegreeLE hN, ?_⟩
      change g (Ideal.Quotient.mk I P) = monomial e 1
      rw [hg]
      exact hP
  change affineHilbertFunction I n = _
  calc
    _ = Module.finrank GeoField ((quotientDegreeLE I n).map g.toLinearEquiv.toLinearMap) :=
      (g.toLinearEquiv.finrank_map_eq _).symm
    _ = Module.finrank GeoField M := by rw [hmap]
    _ = _ := by
      rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _), Nat.card_coe_set_eq]
theorem proof : K1_13_6_2_3.c1 := by
  intro p hp
  let I := (⊥ : Ideal GeoJets).comap (monomialMap GeoField (capExponents p)).toRingHom
  have hP : affineHilbertPolynomial I = latticePolynomial p := by
    apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
    filter_upwards [eventually_eval_affineHilbertPolynomial I, Filter.eventually_ge_atTop 1]
      with n hn hn₁
    rw [hn, cap_hilbert_count p hp n, latticePolynomial_eval p hp n hn₁]
  change (affineHilbertPolynomial I).coeff 4 = _
  rw [hP, latticePolynomial_coeff]
end
end K1_13_6_2_3_1
end
section
namespace K1_13_6_2_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
abbrev Exponent := Fin 5 →₀ ℕ
abbrev Boxes := Fin 5 → Shape × ℕ
def boxes (p : Shape) (i : Fin 5) : Shape × ℕ :=
  if i = 0 then (p, 0) else
  if i = 1 then (cutterBox, 0) else
  if i = 2 then (graphBox p, 1) else
  if i = 3 then (liftedChart (taylorLength + 1) p, taylorLength + 1)
  else (liftedChart (taylorLength + 2) p, taylorLength + 2)
def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j
def Allowed (a : Shape × ℕ) (m : Exponent) : Prop :=
  (∑ i : Fin 4, m i.castSucc) ≤ a.1.b ∧
  (∑ i : Fin 4, i.val * m i.castSucc) ≤ a.1.j ∧
  m (Fin.castSucc (3 : Fin 4)) ≤ a.1.t ∧ m (Fin.last 4) ≤ a.2
def latticePoints (a : Shape × ℕ) : Set Exponent :=
  {m | Allowed (a.1.scale 2, 2 * a.2) m}
instance latticePointsFinite (a : Shape × ℕ) : Finite (latticePoints a) := by
  apply Set.Finite.to_subtype
  refine (Finsupp.finite_of_degree_le (2 * a.1.b + 2 * a.2)).subset ?_
  intro m hm
  change m.degree ≤ _
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc]
  exact Nat.add_le_add hm.1 hm.2.2.2
def Admissible (B : Boxes) : Prop :=
  (∀ i, Chamber (B i).1) ∧ (∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ latticePoints (B i))
def diagonalExponents (B : Boxes) (t : Fin 5 → ℕ) : Set Exponent :=
  {m | ∃ u : (i : Fin 5) → Fin (t i) → Exponent,
    (∀ i j, u i j ∈ latticePoints (B i)) ∧ m = ∑ i, ∑ j, u i j}
instance diagonalExponentsFinite (B : Boxes) (t : Fin 5 → ℕ) :
    Finite (diagonalExponents B t) := by
  let addExponents (u : (i : Fin 5) → Fin (t i) → latticePoints (B i)) : Exponent :=
    ∑ i, ∑ j, (u i j).val
  have heq : diagonalExponents B t = Set.range addExponents := by
    ext m
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i j => ⟨u i j, hu i j⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨fun i j => (u i j).val, fun i j => (u i j).property, rfl⟩
  rw [heq]
  exact (Set.finite_range _).to_subtype
def mixedDegree (B : Boxes) (P : Ideal GeoJets5) (I : Finset (Fin 5)) : ℚ :=
  (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
    (MvPolynomial.affineHilbertPolynomial (Ideal.comap
      (MvPolynomial.monomialMap GeoField (diagonalExponents B (fun i => if i ∈ J then 2 else 1)))
      P)).coeff I.card) / (2 : ℚ) ^ I.card
def OfDim (P : Ideal GeoJets5) (d : ℕ) : Prop :=
  ringKrullDim (GeoJets5 ⧸ P) = ((d : ℕ∞) : WithBot ℕ∞)
def DimLE (P : Ideal GeoJets5) (d : ℕ) : Prop :=
  ringKrullDim (GeoJets5 ⧸ P) ≤ ((d : ℕ∞) : WithBot ℕ∞)
def sectionIdeal (P : Ideal GeoJets5) (D : GeoJets5) : Ideal GeoJets5 :=
  P ⊔ Ideal.span {D}
def LengthAt (J P : Ideal GeoJets5) (hp : P.IsPrime) : ℕ∞ :=
  letI := hp
  let A := Localization.AtPrime P
  Module.length A (A ⧸ J.map (algebraMap GeoJets5 A))
structure Component (P : Ideal GeoJets5) (D : GeoJets5) (C : Ideal GeoJets5) (w : ℕ) : Prop where
  minimal : (sectionIdeal P D).IsMinimalPrime C
  length_le : (w : ℕ∞) ≤ LengthAt (sectionIdeal P D) C minimal.isPrime
def ProperCutComparison : Prop :=
  ∀ (B : Boxes), Admissible B →
    ∀ (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5),
      i ∉ I → DimLE P (I.card + 1) →
      ∀ (D : GeoJets5), Box5 (B i).1 (B i).2 D → IsLeftRegular (Ideal.Quotient.mk P D) →
        mixedDegree B (sectionIdeal P D) I ≤ mixedDegree B P (insert i I)
def CycleComparison : Prop :=
  ∀ (B : Boxes), Admissible B →
    ∀ (J : Ideal GeoJets5) (I : Finset (Fin 5)), DimLE J I.card →
      ∀ {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ),
        Set.InjOn C (S : Set ι) →
        (∀ a ∈ S, ∃ h : J.IsMinimalPrime (C a), (w a : ℕ∞) ≤ LengthAt J (C a) h.isPrime) →
        (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B J I
def DivisorBound : Prop :=
  ∀ (B : Boxes), Admissible B →
    ∀ (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5),
      P.IsPrime → i ∉ I → OfDim P (I.card + 1) →
      ∀ (D : GeoJets5), Box5 (B i).1 (B i).2 D → D ∉ P →
        ∀ {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ),
          Set.InjOn C (S : Set ι) → (∀ a ∈ S, Component P D (C a) (w a)) →
          (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B P (insert i I)
def oldEmbedding : GeoJets →+* GeoJets5 :=
  (MvPolynomial.rename Fin.castSucc).toRingHom
def cylinder (P : Ideal GeoJets) : Ideal GeoJets5 := P.map oldEmbedding
def graphLift {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) : Ideal GeoJets5 :=
  (P.map b.localMap).comap b.onGraph
def pointIdeal (z : Fin 5 → GeoField) : Ideal GeoJets5 :=
  RingHom.ker (MvPolynomial.eval z)
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_4
noncomputable section
open K1_13_6 K1_13_6_2
open scoped BigOperators
theorem box5_iff {a : K1_13.Shape × ℕ} {D : GeoJets5} :
    Box5 a.1 a.2 D ↔ ∀ m ∈ D.support, Allowed a m := by
  constructor
  · intro h m hm
    exact ⟨(h.1 m hm).1, (h.1 m hm).2.1, (h.1 m hm).2.2, h.2 m hm⟩
  · intro h
    exact ⟨fun m hm => ⟨(h m hm).1, (h m hm).2.1, (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2⟩
theorem allowed_zero (a : K1_13.Shape × ℕ) : Allowed a 0 := by
  simp [Allowed]
theorem allowed_coordinate {a : K1_13.Shape × ℕ}
    (h : 1 ≤ a.1.b ∧ 3 ≤ a.1.j ∧ 1 ≤ a.1.t ∧ 1 ≤ a.2) (i : Fin 5) :
    Allowed a (Finsupp.single i 1) := by
  obtain ⟨hb, hj, ht, hd⟩ := h
  let m : Exponent := Finsupp.single i 1
  have hold : (∑ j : Fin 4, m j.castSucc) ≤ 1 := calc
    _ ≤ ∑ j : Fin 5, m j := by
      rw [Fin.sum_univ_castSucc (n := 4)]
      exact Nat.le_add_right _ _
    _ = 1 := by
      rw [← Finsupp.degree_eq_sum]
      exact Finsupp.degree_single i 1
  have hindex : (∑ j : Fin 4, j.val * m j.castSucc) ≤ 3 := calc
    _ ≤ ∑ j : Fin 4, 3 * m j.castSucc := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ 3 := by rw [← Finset.mul_sum]; omega
  have hsingle (j : Fin 5) : m j ≤ 1 := by
    simp only [m, Finsupp.single_apply]
    split <;> decide
  exact ⟨hold.trans hb, hindex.trans hj, (hsingle _).trans ht, (hsingle _).trans hd⟩
theorem constant_box (a : K1_13.Shape × ℕ) (s : GeoField) :
    Box5 a.1 a.2 (MvPolynomial.C s) := by
  classical
  apply box5_iff.mpr
  intro m hm
  by_cases hs : s = 0
  · simp [hs] at hm
  · rw [MvPolynomial.support_C, ite_eq_right hs, Finset.mem_singleton] at hm
    exact hm ▸ allowed_zero a
theorem coordinate_box {a : K1_13.Shape × ℕ}
    (h : 1 ≤ a.1.b ∧ 3 ≤ a.1.j ∧ 1 ≤ a.1.t ∧ 1 ≤ a.2)
    (z : Fin 5 → GeoField) (i : Fin 5) :
    Box5 a.1 a.2 (MvPolynomial.X i - MvPolynomial.C (z i)) := by
  apply box5_iff.mpr
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ hm) with hX | hC
  · rw [MvPolynomial.support_X, Finset.mem_singleton] at hX
    exact hX ▸ allowed_coordinate h i
  · exact box5_iff.mp (constant_box a (z i)) m hC
theorem eval_surjective (z : Fin 5 → GeoField) :
    Function.Surjective (MvPolynomial.eval z) :=
  fun a => ⟨MvPolynomial.C a, MvPolynomial.eval_C _⟩
private theorem pointIdeal_injective : Function.Injective pointIdeal := by
  intro x y h
  funext i
  have hx : MvPolynomial.X i - MvPolynomial.C (x i) ∈ pointIdeal x := by
    simp [pointIdeal, RingHom.mem_ker]
  have hy := RingHom.mem_ker.mp (h ▸ hx : _ ∈ pointIdeal y)
  rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] at hy
  exact hy.symm
theorem point_degree (B : Boxes) (z : Fin 5 → GeoField) :
    mixedDegree B (pointIdeal z) ∅ = 1 := by
  let A := diagonalExponents B (fun _ => 1)
  let φ := (MvPolynomial.aeval z).comp (MvPolynomial.monomialMap GeoField A)
  have hφ : Function.Surjective φ := fun a => ⟨MvPolynomial.C a, φ.commutes a⟩
  have heq : (pointIdeal z).comap (MvPolynomial.monomialMap GeoField A) = RingHom.ker φ := rfl
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  let := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  unfold mixedDegree
  simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, tsub_self,
    pow_zero, one_mul, div_one]
  change (MvPolynomial.affineHilbertPolynomial
    ((pointIdeal z).comap (MvPolynomial.monomialMap GeoField A))).coeff 0 = 1
  rw [heq, MvPolynomial.affineHilbertPolynomial_eq_C_finrank, Polynomial.coeff_C_zero,
    e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one]
theorem one_le_length {J C : Ideal GeoJets5} (h : J.IsMinimalPrime C) :
    (1 : ℕ∞) ≤ LengthAt J C h.isPrime := by
  let := h.isPrime
  let A := Localization.AtPrime C
  have hne : J.map (algebraMap GeoJets5 A) ≠ ⊤ := by
    have hle := Ideal.map_mono (f := algebraMap GeoJets5 A) h.le
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal C A] at hle
    exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hle
  let : Nontrivial (A ⧸ J.map (algebraMap GeoJets5 A)) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact Order.one_le_iff_ne_zero.mpr Module.length_pos.ne'
theorem point_component {C : Ideal GeoJets5} (hprime : C.IsPrime) (hdim : OfDim C 1)
    {z : Fin 5 → GeoField} (hz : C ≤ pointIdeal z) {D : GeoJets5} (hproper : D ∉ C)
    (hD : MvPolynomial.eval z D = 0) : Component C D (pointIdeal z) 1 := by
  let := hprime
  let : (pointIdeal z).IsPrime := RingHom.ker_isPrime (MvPolynomial.eval z)
  let : Ring.KrullDimLE 1 (GeoJets5 ⧸ C) := Ring.krullDimLE_iff.mpr (le_of_eq hdim)
  have hmin : (sectionIdeal C D).IsMinimalPrime (pointIdeal z) := by
    refine ⟨⟨RingHom.ker_isPrime _, sup_le hz ((Ideal.span_singleton_le_iff_mem _).mpr hD)⟩, ?_⟩
    intro P hP hPle
    have := hP.1
    have hCP : C ≤ P := le_sup_left.trans hP.2
    have hDJ : D ∈ sectionIdeal C D :=
      (le_sup_right : Ideal.span {D} ≤ sectionIdeal C D) (Ideal.subset_span (by simp))
    have hDP : D ∈ P := hP.2 hDJ
    let π := Ideal.Quotient.mk C
    have hne : P.map π ≠ ⊥ := by
      intro h
      have hmem := Ideal.mem_map_of_mem π hDP
      rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
      exact hproper hmem
    have hmax : (P.map π).IsMaximal :=
      (Ideal.isPrime_map_quotientMk_of_isPrime hCP).isMaximal_of_ne_bot hne
    have htop := (Ideal.isPrime_map_quotientMk_of_isPrime
      (p := pointIdeal z) hz).ne_top
    have hEq := hmax.eq_of_le htop (Ideal.map_mono (f := π) hPle)
    have hEq' := congrArg (Ideal.comap π) hEq
    rw [Ideal.comap_map_mk hCP, Ideal.comap_map_mk hz] at hEq'
    exact hEq'.ge
  exact ⟨hmin, one_le_length hmin⟩
private theorem exists_coordinate_cut {C : Ideal GeoJets5} {z : Fin 5 → GeoField}
    (h : C < pointIdeal z) :
    ∃ i : Fin 5, MvPolynomial.X i - MvPolynomial.C (z i) ∉ C := by
  by_contra! hmem
  let π := Ideal.Quotient.mk C
  have hmaps : π = π.comp (MvPolynomial.C.comp (MvPolynomial.eval z)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      have heq := Ideal.Quotient.eq_zero_iff_mem.mpr (hmem i)
      rw [map_sub, sub_eq_zero] at heq
      simpa using heq
  apply not_le_of_gt h
  intro D hD
  have hz : MvPolynomial.eval z D = 0 := RingHom.mem_ker.mp hD
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π D = 0
  calc
    π D = π (MvPolynomial.C (MvPolynomial.eval z D)) := RingHom.congr_fun hmaps D
    _ = 0 := by rw [hz, map_zero, map_zero]
theorem point_bound (H : DivisorBound)
    (B : Boxes) (hB : Admissible B)
    (ha : 1 ≤ (B 4).1.b ∧ 3 ≤ (B 4).1.j ∧ 1 ≤ (B 4).1.t ∧ 1 ≤ (B 4).2)
    (C : Ideal GeoJets5) (hprime : C.IsPrime) (hdim : OfDim C 1)
    (U : Finset (Fin 5 → GeoField)) (hU : ∀ z ∈ U, C ≤ pointIdeal z)
    (hslice : U.card ≤ 1 ∨ ∃ D, Box5 (B 4).1 (B 4).2 D ∧ D ∉ C ∧
      ∀ z ∈ U, MvPolynomial.eval z D = 0) :
    (U.card : ℚ) ≤ mixedDegree B C {4} := by
  classical
  have cut_bound (D : GeoJets5) (hB' : Box5 (B 4).1 (B 4).2 D) (hproper : D ∉ C)
      (hD : ∀ z ∈ U, MvPolynomial.eval z D = 0) : (U.card : ℚ) ≤ mixedDegree B C {4} := by
    have hb := H B hB C ∅ 4 hprime (by simp) hdim D hB' hproper U pointIdeal (fun _ => 1)
      pointIdeal_injective.injOn (fun z hz => point_component hprime hdim (hU z hz) hproper (hD z hz))
    simpa [point_degree] using hb
  rcases hslice with hone | ⟨D, hD, hp, hz⟩
  · by_cases hempty : U = ∅
    · apply cut_bound (MvPolynomial.C 1) (constant_box (B 4) 1)
      · rw [map_one]
        exact (Ideal.ne_top_iff_one C).mp hprime.ne_top
      · simp [hempty]
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hlt : C < pointIdeal z := by
      refine lt_of_le_of_ne (hU z hz) ?_
      intro h
      rw [h, OfDim, pointIdeal] at hdim
      have e := (MvPolynomial.eval z).quotientKerEquivOfSurjective (eval_surjective z)
      rw [e.ringKrullDim, ringKrullDim_eq_zero_of_field] at hdim
      exact (by decide : (0 : WithBot ℕ∞) ≠ 1) hdim
    obtain ⟨i, hi⟩ := exists_coordinate_cut hlt
    apply cut_bound _ (coordinate_box ha z i) hi
    intro y hy
    have hyz := Finset.card_le_one.mp hone y hy z hz
    subst y
    simp
  · exact cut_bound D hD hp hz
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
abbrev lift4 : Row 4 →ₐ[Geom[X]] Row 5 := MvPolynomial.rename Fin.castSucc
abbrev generic5 : Row 5 →+* GeoJets5 := MvPolynomial.map genericCoeffs
def coefficientDerivative5 (P : Row 5) : Row 5 :=
  ∑ m ∈ P.support, MvPolynomial.monomial m (derivative (P.coeff m))
def fixedFlow (P : Row 5) : Row 5 :=
  coefficientDerivative5 P +
    ∑ i : Fin 4, MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) *
      MvPolynomial.X i.succ * MvPolynomial.pderiv i.castSucc P
def rawGraph (g : Row 4) : Row 5 :=
  lift4 (partialFlow g) +
    MvPolynomial.C (4 : Geom[X]) * lift4 (separant g) * MvPolynomial.X (Fin.last 4)
def fifthFlow (g : Row 4) : Row 5 :=
  MvPolynomial.C (Polynomial.C (-(4 : Geom)⁻¹)) * fixedFlow (rawGraph g)
def numerator (g : Row 4) : ℕ → Row 5
  | 0 => MvPolynomial.C (24 : Geom[X]) * MvPolynomial.X (Fin.last 4)
  | k+1 =>
    let S := lift4 (separant g)
    let P := numerator g k
    S * fixedFlow P + fifthFlow g * MvPolynomial.pderiv (Fin.last 4) P -
      (k : Row 5) * fixedFlow S * P
def denominator (g : Row 4) (k : ℕ) : Row 5 := lift4 (separant g) ^ k
def padded (g : Row 4) (k i : ℕ) : Row 5 :=
  if hi : i < 4 then
    MvPolynomial.C (Polynomial.C (i.factorial : Geom)) *
      lift4 (MvPolynomial.X ⟨i, hi⟩) * denominator g k
  else numerator g (i - 4) * denominator g (k - (i - 4))
theorem padded_last (g : Row 4) (k : ℕ) : padded g k (k + 4) = numerator g k := by
  rw [padded, dite_eq_right (by omega : ¬ k + 4 < 4)]
  simp [denominator]
theorem generic_rawGraph {f Q l} (b : Branch f Q l) :
    generic5 (rawGraph b.g) = b.graph := by
  simp [rawGraph, Branch.graph, Branch.sigma, toGeneric, MvPolynomial.map_rename, map_ofNat]
end
end K1_13_6_2_2
end
section
namespace K1_13_6_2_2
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
def c1 : Prop :=
  ∀ f Q l, SmallFactor f → ∀ b : Branch f Q l,
    let p := (shape f).chamber
    Box5 (graphBox p) 1 b.graph ∧
      ∀ k : ℕ, Box5 (liftedChart (k + 5) p) (k + 5) (generic5 (denominator b.g k)) ∧
        ∀ i ≤ k + 4, Box5 (liftedChart (k + 5) p) (k + 5) (generic5 (padded b.g k i))
def c2 : Prop :=
  ∀ f Q l, ∀ (b : Branch f Q l) (k : ℕ),
    b.onGraph (generic5 (numerator b.g k)) * b.localMap b.sigma ^ (k + 8) =
      b.localMap (toGeneric (jetNumerator b.g (k + 4)))
variable {f Q : Row 4} {l : ℕ}
@[simp] private theorem onGraph_C (b : Branch f Q l) (a : GeoField) :
    b.onGraph (MvPolynomial.C a) = b.localMap (MvPolynomial.C a) := by
  simp [Branch.onGraph]
theorem onGraph_lift4 (b : Branch f Q l) (P : Row 4) :
    b.onGraph (generic5 (lift4 P)) = b.localMap (toGeneric P) := by
  let lift := (MvPolynomial.rename Fin.castSucc : GeoJets →ₐ[GeoField] GeoJets5).toRingHom
  have h : b.onGraph.comp lift = b.localMap := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lift]
    · intro i
      simp [lift, Branch.onGraph]
  rw [MvPolynomial.map_rename]
  exact DFunLike.congr_fun h (toGeneric P)
theorem denominator_onGraph (b : Branch f Q l) (k : ℕ) :
    b.onGraph (generic5 (denominator b.g k)) = b.localMap b.sigma ^ k := by
  simp only [denominator, map_pow, onGraph_lift4, Branch.sigma]
theorem numerator_associated (h : c2) (b : Branch f Q l) (k : ℕ) :
    Associated (b.onGraph (generic5 (numerator b.g k)))
      (b.localMap (toGeneric (jetNumerator b.g (k+4)))) := by
  rw [← h f Q l b k]
  exact associated_mul_unit_right _ _ (IsLocalization.Away.algebraMap_pow_isUnit b.sigma (k+8))
theorem eval_const (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) (a : GeoField) :
    b.liftedEval p h (MvPolynomial.C a) = a := by
  simp [Branch.liftedEval, b.regularEval_localMap]
private theorem eval_denominator (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) (k : ℕ) :
    b.liftedEval p h (generic5 (denominator b.g k)) = MvPolynomial.eval p b.sigma ^ k := by
  simp [Branch.liftedEval, denominator_onGraph, b.regularEval_localMap]
private abbrev ordinary (T : Geom[X]) (i : ℕ) : GeoField :=
  genericCoeffs ((derivative (R := Geom))^[i] T)
private theorem ordinary_eq_hasse (T : Geom[X]) (i : ℕ) :
    (derivative (R := Geom))^[i] T =
      Polynomial.C (i.factorial : Geom) * hasseDeriv i T := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
theorem eval_padded (h2 : c2) (b : Branch f Q l) {T : Geom[X]}
    (h : b.Contains (actualPoint T)) (k i : ℕ) (hi : i ≤ k + 4) :
    b.liftedEval (actualPoint T) h (generic5 (padded b.g k i)) =
      ordinary T i * MvPolynomial.eval (actualPoint T) b.sigma ^ k := by
  by_cases hi4 : i < 4
  · rw [padded, dite_eq_left hi4]
    simp only [map_mul, MvPolynomial.map_C, eval_const, eval_denominator]
    have he : b.liftedEval (actualPoint T) h (generic5 (lift4 (MvPolynomial.X ⟨i, hi4⟩))) =
        genericCoeffs (hasseDeriv i T) := by
      change b.regularEval (actualPoint T) h (b.onGraph (generic5 (lift4 (MvPolynomial.X _)))) = _
      rw [onGraph_lift4, b.regularEval_localMap]
      simp [toGeneric, actualPoint, jet]
    rw [he]
    unfold ordinary
    rw [ordinary_eq_hasse, map_mul]
  · rw [padded, dite_eq_right hi4]
    simp only [map_mul, eval_denominator]
    let j := i - 4
    have hj : j + 4 = i := by dsimp only [j]; omega
    have hjk : j ≤ k := by omega
    have hg : atJet b.g T = 0 := K1_13_6_1.mem_markIdeal.mp
      (h.1 ((le_trans le_sup_left b.divisor.le) (b.chart.2.1 b.r le_rfl)))
    let s := MvPolynomial.eval (actualPoint T) b.sigma
    let e := b.regularEval (actualPoint T) h
    have he := congrArg e (h2 f Q l b j)
    simp only [map_mul, map_pow, e, b.regularEval_localMap] at he
    change b.liftedEval (actualPoint T) h (generic5 (numerator b.g j)) * s ^ (j+8) =
      MvPolynomial.eval (actualPoint T) (toGeneric (jetNumerator b.g (j+4))) at he
    have hEval (P : Row 4) :
        MvPolynomial.eval (actualPoint T) (toGeneric P) = genericCoeffs (atJet P T) :=
      (MvPolynomial.map_eval genericCoeffs (jet T) P).symm
    rw [hEval, eval_jetNumerator _ _ hg, map_mul, map_pow, hj] at he
    have hs : genericCoeffs (atJet (separant b.g) T) = s := (hEval _).symm
    rw [hs, show 2*i = j + (j+8) by omega, pow_add s j (j+8)] at he
    have hnum : b.liftedEval (actualPoint T) h (generic5 (numerator b.g j)) =
        ordinary T i * s ^ j := by
      apply mul_right_cancel₀ (pow_ne_zero (j+8) h.2)
      exact he.trans (show s ^ j * s ^ (j+8) * ordinary T i =
        (ordinary T i * s ^ j) * s ^ (j+8) by ac_rfl)
    change b.liftedEval (actualPoint T) h (generic5 (numerator b.g j)) * s ^ (k-j) =
      ordinary T i * s ^ k
    rw [hnum, mul_assoc, ← pow_add, Nat.add_sub_of_le hjk]
private abbrev const : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
private abbrev centre : GeoField := genericCoeffs Polynomial.X
private def taylorScalar (x : Geom) (i : ℕ) : GeoField :=
  (i.factorial : GeoField)⁻¹ * (const x - centre)^i
private theorem factorial_ne_zero {i : ℕ} (hi : i < K1.p) : (i.factorial : GeoField) ≠ 0 := by
  let e := const.comp K1_13.embed
  let : CharP GeoField K1.p := charP_of_injective_ringHom e.injective K1.p
  induction i with
  | zero => simp
  | succ i ih =>
    have he : ((i+1 : ℕ) : GeoField) ≠ 0 := by
      intro hz
      exact (not_le_of_gt hi) (Nat.le_of_dvd (Nat.succ_pos i)
        ((CharP.cast_eq_zero_iff GeoField K1.p (i+1)).mp hz))
    simpa only [Nat.factorial_succ, Nat.cast_mul] using
      mul_ne_zero he (ih (Nat.lt_of_succ_lt hi))
private theorem eval_taylor (T : Geom[X]) (hT : T.natDegree < taylorLength) (x : Geom) :
    (∑ i ∈ Finset.range taylorLength, taylorScalar x i * ordinary T i) = const (T.eval x) := by
  have hd : (Polynomial.taylor centre (T.map const)).natDegree < taylorLength := by
    rw [Polynomial.natDegree_taylor]
    exact Polynomial.natDegree_map_le.trans_lt hT
  rw [← Polynomial.eval_map_apply const x, ← Polynomial.taylor_eval_sub centre,
    Polynomial.eval_eq_sum_range' hd]
  apply Finset.sum_congr rfl
  intro i hi
  have hcent (P : Geom[X]) : (P.map const).eval centre = genericCoeffs P := by
    rw [Polynomial.eval_map]
    simpa only [Polynomial.eval₂_C_X] using
      (Polynomial.hom_eval₂ P Polynomial.C genericCoeffs Polynomial.X).symm
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, hcent]
  have hord : ordinary T i = (i.factorial : GeoField) * genericCoeffs (hasseDeriv i T) := by
    unfold ordinary
    rw [ordinary_eq_hasse, map_mul, Polynomial.C_eq_natCast, map_natCast]
  have hn : i < K1.p :=
    (Finset.mem_range.mp hi).trans (by decide : taylorLength < K1.p)
  rw [hord, taylorScalar]
  calc
    _ = ((i.factorial : GeoField)⁻¹ * (i.factorial : GeoField)) *
          (genericCoeffs (hasseDeriv i T) * (const x - centre)^i) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (factorial_ne_zero hn), one_mul]
theorem box_C_mul {p : Shape} {d : ℕ} {P : GeoJets5} (hP : Box5 p d P)
    (a : GeoField) : Box5 p d (MvPolynomial.C a * P) := by
  have hsub : (MvPolynomial.C a * P).support ⊆ P.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)
  exact ⟨fun m hm => hP.1 m (hsub hm), fun m hm => hP.2 m (hsub hm)⟩
theorem box_sum {α : Type*} {p : Shape} {d : ℕ} (I : Finset α) (P : α → GeoJets5)
    (hP : ∀ i ∈ I, Box5 p d (P i)) : Box5 p d (∑ i ∈ I, P i) := by
  classical
  have hsub m (hm : m ∈ (∑ i ∈ I, P i).support) : ∃ i ∈ I, m ∈ (P i).support :=
    Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  constructor
  · intro m hm
    obtain ⟨i, hi, hmi⟩ := hsub m hm
    exact (hP i hi).1 m hmi
  · intro m hm
    obtain ⟨i, hi, hmi⟩ := hsub m hm
    exact (hP i hi).2 m hmi
theorem box_sub {p : Shape} {d : ℕ} {A B : GeoJets5}
    (hA : Box5 p d A) (hB : Box5 p d B) : Box5 p d (A - B) := by
  classical
  have hsub := MvPolynomial.support_sub (Fin 5) A B
  constructor
  · intro m hm
    rcases Finset.mem_union.mp (hsub hm) with ha | hb
    · exact hA.1 m ha
    · exact hB.1 m hb
  · intro m hm
    rcases Finset.mem_union.mp (hsub hm) with ha | hb
    · exact hA.2 m ha
    · exact hB.2 m hb
private def valuePolynomial (g : Row 4) (k : ℕ) (x a : K) : GeoJets5 :=
  (∑ i ∈ Finset.range taylorLength, MvPolynomial.C (taylorScalar (embed x) i) *
      generic5 (padded g k i)) -
    MvPolynomial.C (const (embed a)) * generic5 (denominator g k)
theorem value_section (h2 : c2) (b : Branch f Q l) (k : ℕ)
    (hk : taylorLength ≤ k + 5) (x a : K) :
    ∀ S : K[X], S.natDegree ≤ 133671 → ∀ h : b.Contains (actualPoint (extend S)),
      b.liftedEval (actualPoint (extend S)) h (valuePolynomial b.g k x a) = 0 ↔ S.eval x = a := by
  intro S hS h
  let p := actualPoint (extend S)
  let e := b.liftedEval p h
  let s := MvPolynomial.eval p b.sigma
  have hsum :
      (∑ i ∈ Finset.range taylorLength,
        e (MvPolynomial.C (taylorScalar (embed x) i) * generic5 (padded b.g k i))) =
        const ((extend S).eval (embed x)) * s^k := by
    have hdeg : (extend S).natDegree < taylorLength := by
      rw [Polynomial.natDegree_map]
      exact Nat.lt_succ_of_le hS
    rw [← eval_taylor (extend S) hdeg (embed x), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hki : i ≤ k + 4 := by have := Finset.mem_range.mp hi; omega
    simp only [map_mul, e, eval_const, p, eval_padded h2 b h k i hki, s, mul_assoc]
  change e (valuePolynomial b.g k x a) = 0 ↔ _
  unfold valuePolynomial
  rw [map_sub, map_sum, hsum, map_mul, eval_const, eval_denominator]
  change const ((extend S).eval (embed x)) * s^k - const (embed a) * s^k = 0 ↔ _
  rw [Polynomial.eval_map_apply, ← sub_mul, mul_eq_zero,
    or_iff_left (pow_ne_zero k h.2), sub_eq_zero]
  exact ⟨fun he => embed.injective (const.injective he), fun he => congrArg (const.comp embed) he⟩
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2.c2 := by
  intro f Q l hf b
  obtain ⟨hg, hbox⟩ := h1 f Q l hf b
  let k := taylorLength - 4
  have hE := (hbox k).2 (k+4) le_rfl
  have hH := (hbox (k+1)).2 ((k+1)+4) le_rfl
  rw [padded_last] at hE hH
  have hm := numerator_associated h2 b k
  have hn := numerator_associated h2 b (k+1)
  refine ⟨hg, generic5 (numerator b.g k), generic5 (numerator b.g (k+1)), hE, hm, hH, hn, ?_⟩
  intro x a
  refine ⟨valuePolynomial b.g (k+1) x a, ?_, value_section h2 b (k+1) (by decide) x a⟩
  unfold valuePolynomial
  apply box_sub
  · apply box_sum
    intro i hi
    have hki : i ≤ k + 1 + 4 := by
      have := Finset.mem_range.mp hi
      dsimp only [k]
      omega
    exact box_C_mul ((hbox (k+1)).2 i hki) _
  · exact box_C_mul (hbox (k+1)).1 _
end
end K1_13_6_2_2
end
section
namespace K1_13_6_2_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3
open scoped BigOperators
def step {ι : Type} [DecidableEq ι] (i : ι) : ι → ℕ := Pi.single i 1
def Graded {ι σ : Type} [Fintype ι] [DecidableEq ι] (slot : σ → ι)
    (I : Ideal (MvPolynomial σ GeoField)) : Prop :=
  ∀ f ∈ I, ∀ a : ι → ℕ, MvPolynomial.weightedHomogeneousComponent (step ∘ slot) a f ∈ I
def hilbert {ι σ : Type} [DecidableEq ι] (slot : σ → ι)
    (I : Ideal (MvPolynomial σ GeoField)) (a : ι → ℕ) : ℚ :=
  (Module.finrank GeoField
    ((MvPolynomial.weightedHomogeneousSubmodule GeoField (step ∘ slot) a).map
      (Ideal.Quotient.mkₐ GeoField I).toLinearMap) : ℕ)
def deltas {ι : Type} [DecidableEq ι] : List ι → ((ι → ℕ) → ℚ) → (ι → ℕ) → ℚ
  | [], H => H
  | i :: rest, H => fun a => deltas rest H (a + step i) - deltas rest H a
def outside {σ : Type} (A : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
  {e | ∀ b ∈ A, ¬ b ≤ e}
def sliceCount {ι σ : Type} [DecidableEq ι] (slot : σ → ι)
    (A : Finset (σ →₀ ℕ)) (a : ι → ℕ) : ℚ :=
  ({e | e ∈ outside A ∧ Finsupp.weight (step ∘ slot) e = a}.ncard : ℕ)
abbrev CapVar {ι : Type} (shapes : ι → Shape) := (i : ι) × capExponents (shapes i)
def capSlot {ι : Type} (shapes : ι → Shape) : CapVar shapes → ι := Sigma.fst
def capMap {ι : Type} (shapes : ι → Shape) (J : Ideal GeoJets) :
    MvPolynomial (CapVar shapes) GeoField →ₐ[GeoField] MvPolynomial ι (GeoJets ⧸ J) :=
  MvPolynomial.aeval fun v =>
    MvPolynomial.monomial (Finsupp.single v.1 1)
      (Ideal.Quotient.mk J (MvPolynomial.monomial v.2.val 1))
def capIdeal {ι : Type} (shapes : ι → Shape) (J : Ideal GeoJets) :
    Ideal (MvPolynomial (CapVar shapes) GeoField) :=
  RingHom.ker (capMap shapes J).toRingHom
def shapeSum {ι : Type} [Fintype ι] (shapes : ι → Shape) (a : ι → ℕ) : Shape :=
  ⟨∑ i, a i * (shapes i).b, ∑ i, a i * (shapes i).j, ∑ i, a i * (shapes i).t⟩
def productExponents {ι : Type} [DecidableEq ι] (shapes : ι → Shape) (a : ι → ℕ) :
    Set (Fin 4 →₀ ℕ) :=
  {m | ∃ e : CapVar shapes →₀ ℕ,
    Finsupp.weight (step ∘ capSlot shapes) e = a ∧
    Finsupp.weight (fun v : CapVar shapes => v.2.val) e = m}
def supportRank (J : Ideal GeoJets) (A : Set (Fin 4 →₀ ℕ)) : ℕ :=
  Module.finrank GeoField
    ((MvPolynomial.restrictSupport GeoField A).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap)
abbrev cut (J : Ideal GeoJets) (D : GeoJets) : Ideal GeoJets := J ⊔ Ideal.span {D}
end
end K1_13_6_2_3_2
end
section
namespace K1_13_6_2_4
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators
theorem cylinder_injective : Function.Injective cylinder := by
  let retr : GeoJets5 →ₐ[GeoField] GeoJets :=
    MvPolynomial.killCompl (Fin.castSucc_injective 4)
  have hr : retr.toRingHom.comp oldEmbedding = RingHom.id GeoJets :=
    congrArg AlgHom.toRingHom (MvPolynomial.killCompl_comp_rename (Fin.castSucc_injective 4))
  intro P Q h
  have hh := congrArg (Ideal.map retr.toRingHom) h
  simpa only [cylinder, Ideal.map_map, hr, Ideal.map_id] using hh
theorem ambient_dim : DimLE (⊥ : Ideal GeoJets5) 5 := by
  unfold DimLE
  rw [(RingEquiv.quotientBot GeoJets5).ringKrullDim]
  change ringKrullDim (MvPolynomial (Fin 5) GeoField) ≤ _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_eq_fintype_card, Fintype.card_fin, WithBot.coe_natCast]
theorem old_section_box {P : Row 4} {p : Shape} (hP : InBox (shape P) p) :
    Box5 p 0 (oldEmbedding (toGeneric P)) := by
  apply (box5_iff (a := (p, 0))).mpr
  intro m hm
  change m ∈ (MvPolynomial.rename Fin.castSucc (toGeneric P)).support at hm
  rw [MvPolynomial.support_rename_of_injective (Fin.castSucc_injective 4)] at hm
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
  have haP := MvPolynomial.support_map_subset genericCoeffs P ha
  unfold Allowed
  simp only [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective 4)]
  have hlast : Fin.last 4 ∉ Set.range (Fin.castSucc : Fin 4 → Fin 5) := by
    rintro ⟨i, hi⟩
    exact Fin.castSucc_ne_last i hi
  refine ⟨?_, ?_, (MvPolynomial.monomial_le_degreeOf _ haP).trans hP.2.2,
    le_of_eq (Finsupp.mapDomain_of_notMem_range _ _ hlast)⟩
  · have hdegree := MvPolynomial.le_totalDegree haP
    change a.degree ≤ P.totalDegree at hdegree
    rw [Finsupp.degree_eq_sum] at hdegree
    exact hdegree.trans hP.1
  · have hindex : a.sum (fun i n => i.val * n) ≤ (shape P).j :=
      Finset.le_sup (f := fun m => m.sum (fun i n => i.val * n)) haP
    rw [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)] at hindex
    exact hindex.trans hP.2.1
theorem anchor_section_regular {f : Row 4} (hf : SmallFactor f) :
    IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5) (oldEmbedding (toGeneric f))) := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)
  have hf5 : oldEmbedding (toGeneric f) ≠ 0 :=
    (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      ((MvPolynomial.map_injective _ hinj).ne hf.1.ne_zero)
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact hf5)
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_4
noncomputable section
open K1_13_6 K1_13_6_2
theorem chart_index_eq {f Q l} {b c : Branch f Q l} (h : b.surface = c.surface) :
    b.r = c.r := by
  have order (d e : Branch f Q l) (he : d.surface = e.surface) : ¬ d.r < e.r := by
    intro hlt
    have hmem := e.chart.2.1 (d.r + 1) (by omega)
    rw [← he, Function.iterate_succ_apply'] at hmem
    exact d.chart.2.2 hmem
  exact Nat.le_antisymm (Nat.le_of_not_gt (order c b h.symm)) (Nat.le_of_not_gt (order b c h))
theorem graphLift_same_chart {f Q l} {b c : Branch f Q l} (h : b.r = c.r)
    (P : Ideal GeoJets) : graphLift b P = graphLift c P := by
  cases b
  cases c
  cases h
  rfl
theorem membership_same_chart {f Q l} {b c : Branch f Q l} (h : b.r = c.r) (D : GeoJets5) :
    Associated (b.onGraph D) (b.localMap b.member) ↔
      Associated (c.onGraph D) (c.localMap c.member) := by
  cases b
  cases c
  cases h
  rfl
theorem graph_on_old {f Q l} (b : Branch f Q l) :
    b.onGraph.comp oldEmbedding = b.localMap := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [oldEmbedding, Branch.onGraph]
  · intro i
    simp [oldEmbedding, Branch.onGraph]
theorem graphLift_comap {f Q l} (b : Branch f Q l) (P : Ideal GeoJets)
    (hP : P.IsPrime) (hregular : b.sigma ∉ P) :
    (graphLift b P).comap oldEmbedding = P := by
  rw [graphLift, Ideal.comap_comap, graph_on_old]
  ext D
  change algebraMap GeoJets b.Local D ∈ P.map (algebraMap GeoJets b.Local) ↔ D ∈ P
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers b.sigma) b.Local]
  constructor
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    exact (hP.mem_or_mem hm).resolve_left (fun hpow => hregular (hP.mem_of_pow_mem n hpow))
  · intro hD
    exact ⟨1, (Submonoid.powers b.sigma).one_mem, by simpa using hD⟩
theorem member_proper_on_graph {f Q l} (b : Branch f Q l) {E : GeoJets5}
    (hE : Associated (b.onGraph E) (b.localMap b.member)) :
    E ∉ graphLift b b.surface := by
  intro hmem
  have hlocal : b.localMap b.member ∈ b.surface.map b.localMap :=
    (b.surface.map b.localMap).mem_of_dvd hE.dvd hmem
  have hold : oldEmbedding b.member ∈ graphLift b b.surface := by
    change b.onGraph (oldEmbedding b.member) ∈ b.surface.map b.localMap
    rw [show b.onGraph (oldEmbedding b.member) = b.localMap b.member from
      RingHom.congr_fun (graph_on_old b) _]
    exact hlocal
  have hcont := graphLift_comap b b.surface b.base.isPrime b.chart.2.2
  exact b.proper (hcont ▸ hold)
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_2
open scoped BigOperators nonZeroDivisors
def c1 : Prop := ProperCutComparison
def c2 : Prop := CycleComparison
def c3 : Prop :=
  ∀ p : Shape, Chamber p →
    32 * mixedDegree (boxes p) ⊥ Finset.univ ≤ (budget5 p : ℚ)
def c4 : Prop :=
  ∀ (f Q : Row 4), SmallFactor f → ¬ f ∣ Q →
    let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
    let J := sectionIdeal A (oldEmbedding (toGeneric Q))
    IsLeftRegular (Ideal.Quotient.mk A (oldEmbedding (toGeneric Q))) ∧
    ∀ P : Ideal GeoJets, ∀ h : (intersectionIdeal f Q).IsMinimalPrime P,
      OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P),
          cycleLength (intersectionIdeal f Q) P h.isPrime ≤ LengthAt J (cylinder P) hc.isPrime
def c5 : Prop :=
  ∀ {f Q l} (b : Branch f Q l) (E : GeoJets5),
    (cylinder b.surface).IsPrime → OfDim (cylinder b.surface) 3 →
    Associated (b.onGraph E) (b.localMap b.member) →
    b.graph ∉ cylinder b.surface ∧
    Component (cylinder b.surface) b.graph (graphLift b b.surface) 1 ∧
    OfDim (graphLift b b.surface) 2 ∧
    ∀ c : Branch f Q l, c.surface = b.surface →
      Component (graphLift b b.surface) E (graphLift c c.curve) c.weight ∧
      OfDim (graphLift c c.curve) 1
theorem dim_le_after_section {P : Ideal GeoJets5} {D : GeoJets5} {d : ℕ}
    (hr : IsLeftRegular (Ideal.Quotient.mk P D)) (h : DimLE P (d + 1)) :
    DimLE (sectionIdeal P D) d := by
  have hle : P ≤ sectionIdeal P D := le_sup_left
  let π := Ideal.Quotient.factor hle
  have hπ : π (Ideal.Quotient.mk P D) = 0 := by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (le_sup_right : Ideal.span {D} ≤ sectionIdeal P D) (Ideal.subset_span (by simp))
  have hnd : Ideal.Quotient.mk P D ∈ (GeoJets5 ⧸ P)⁰ :=
    mem_nonZeroDivisors_iff_left.mpr fun a ha => hr (ha.trans (mul_zero _).symm)
  have hd := ringKrullDim_succ_le_of_surjective π (Ideal.Quotient.factor_surjective hle) hnd hπ
  unfold DimLE at h ⊢
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  exact hd.trans (by simpa only [Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one] using h)
theorem divisor_bound (hcut : ProperCutComparison) (hcycle : CycleComparison) :
    DivisorBound := by
  intro B hB P I i hP hi hd D hD hprop ι S C w hinj hcomp
  let := hP
  have hr : IsLeftRegular (Ideal.Quotient.mk P D) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hprop)
  have hdle : DimLE P (I.card + 1) := le_of_eq hd
  exact (hcycle B hB (sectionIdeal P D) I (dim_le_after_section hr hdle) S C w hinj
    (fun a ha => ⟨(hcomp a ha).minimal, (hcomp a ha).length_le⟩)).trans
    (hcut B hB P I i hi hdle D hD hr)
theorem last_caps (p : Shape) :
    1 ≤ (boxes p 4).1.b ∧ 3 ≤ (boxes p 4).1.j ∧ 1 ≤ (boxes p 4).1.t ∧ 1 ≤ (boxes p 4).2 := by
  let H := 4 + (taylorLength + 2 - 5) * (p.j - 2)
  change 1 ≤ max _ H ∧ 3 ≤ H ∧ 1 ≤ min _ (H / 3) ∧ 1 ≤ taylorLength + 2
  have hH : 4 ≤ H := Nat.le_add_right _ _
  refine ⟨(by omega : 1 ≤ H).trans (le_max_right _ _), by omega, le_min ?_ (by omega), by decide⟩
  omega
private theorem chart_chamber (L : ℕ) (p : Shape) : Chamber (liftedChart L p) := by
  let H := 4 + (L - 5) * (p.j - 2)
  change H ≤ max _ H ∧ 3 * min _ (H / 3) ≤ H
  refine ⟨le_max_right _ _, ?_⟩
  have h := min_le_right (2 + (L - 5) * p.t) (H / 3)
  omega
theorem boxes_admissible (p : Shape) (h : Chamber p) : Admissible (boxes p) := by
  constructor
  · intro i
    fin_cases i
    · exact h
    · change 1650 ≤ 4013 ∧ 3 * 550 ≤ (1650 : ℕ)
      decide
    · change p.j + 1 ≤ max p.b (p.j + 1) ∧
        3 * min (p.t + 1) ((p.j + 1) / 3) ≤ p.j + 1
      have ht := min_le_right (p.t + 1) ((p.j + 1) / 3)
      exact ⟨le_max_right _ _, by omega⟩
    · exact chart_chamber _ _
    · exact chart_chamber _ _
  · intro v
    refine ⟨4, ?_⟩
    obtain ⟨hb, hj, ht, hd⟩ := last_caps p
    change Allowed ((boxes p 4).1.scale 2, 2 * (boxes p 4).2) (Finsupp.single v 1)
    apply allowed_coordinate
    change 1 ≤ 2 * (boxes p 4).1.b ∧ 3 ≤ 2 * (boxes p 4).1.j ∧
      1 ≤ 2 * (boxes p 4).1.t ∧ 1 ≤ 2 * (boxes p 4).2
    omega
private def liftedPoint {f Q l} (b : Branch f Q l) (p : JetPoint) : Fin 5 → GeoField := by
  classical
  exact if h : b.Contains p then fun i => b.liftedEval p h (MvPolynomial.X i)
    else Fin.lastCases 0 p
theorem eval_liftedPoint {f Q l} (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) :
    MvPolynomial.eval (liftedPoint b p) = b.liftedEval p h := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [Branch.liftedEval, Branch.onGraph, Branch.regularEval_localMap]
  · intro i
    simp [liftedPoint, h]
theorem liftedPoint_old {f Q l} (b : Branch f Q l) (p : JetPoint) (h : b.Contains p)
    (i : Fin 4) : liftedPoint b p i.castSucc = p i := by
  simp [liftedPoint, h, Branch.liftedEval, Branch.onGraph, Branch.regularEval_localMap]
theorem liftedPoint_mem {f Q l} (b : Branch f Q l) (p : JetPoint) (h : b.Contains p) :
    graphLift b b.curve ≤ pointIdeal (liftedPoint b p) := by
  have hk : b.localCurve ≤ RingHom.ker (b.regularEval p h) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change b.regularEval p h (b.localMap P) = 0
    rw [Branch.regularEval_localMap]
    exact h.1 hP
  intro D hD
  change MvPolynomial.eval (liftedPoint b p) D = 0
  rw [eval_liftedPoint b p h]
  exact hk hD
theorem bound_marks {f Q l} (hdiv : DivisorBound) {p : Shape}
    (hB : Admissible (boxes p)) (b : Branch f Q l) (T : Finset JetPoint)
    (hp : p = (shape f).chamber) (hT : ∀ y ∈ T, b.Contains y) (hSlice : Slice5 b T)
    (hprime : (graphLift b b.curve).IsPrime) (hdim : OfDim (graphLift b b.curve) 1) :
    (T.card : ℚ) ≤ mixedDegree (boxes p) (graphLift b b.curve) {4} := by
  classical
  subst p
  let U := T.image (liftedPoint b)
  have hcard : U.card = T.card := Finset.card_image_of_injOn (by
    intro x hx y hy he
    funext i
    have hz := congrFun he i.castSucc
    rwa [liftedPoint_old b x (hT x hx), liftedPoint_old b y (hT y hy)] at hz)
  rw [← hcard]
  apply point_bound hdiv _ hB (last_caps _) _ hprime hdim U
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact liftedPoint_mem b y (hT y hy)
  · rcases hSlice with hsingle | ⟨D, hD, hproper, hvanish⟩
    · exact Or.inl (hcard ▸ hsingle)
    · refine Or.inr ⟨D, hD, hproper, ?_⟩
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      rw [eval_liftedPoint b y (hT y hy)]
      exact hvanish y hy (hT y hy)
theorem initial_bound (h1 : c1) (h2 : c2) (h4 : c4)
    (f Q : Row 4) (l : ℕ) (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    (hQbox : InBox (shape Q) cutterBox) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (l : ℚ) * (∑ P ∈ S, mixedDegree (boxes (shape f).chamber) (cylinder P) {2, 3, 4}) ≤
        mixedDegree (boxes (shape f).chamber) ⊥ Finset.univ := by
  classical
  let p := (shape f).chamber
  let B := boxes p
  have hB := boxes_admissible p (K1_13_7_1.shape_chamber f)
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
  let J := sectionIdeal A (oldEmbedding (toGeneric Q))
  obtain ⟨hregQ, hAlgebra⟩ := h4 f Q hf hQ
  have hregf := anchor_section_regular hf
  have hboxf : Box5 p 0 (oldEmbedding (toGeneric f)) :=
    old_section_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (l : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := h2 B hB J {2, 3, 4} hJdim S cylinder (fun _ => l) cylinder_injective.injOn
    (fun P hP => (hgeom P hP).2.2)
  have hcutQ := h1 B hB A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric Q)) (old_section_box hQbox) hregQ
  have hcutf := h1 B hB ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric f)) hboxf hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  rw [Finset.mul_sum]
  exact hs.trans (hcutQ.trans hcutf)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_13_6_2.c4 := by
  classical
  have hdiv := divisor_bound h1 h2
  intro f Q l hf hproper hQ hl F T hF
  let p := (shape f).chamber
  have hp : Chamber p := K1_13_7_1.shape_chamber f
  let B := boxes p
  have hB : Admissible B := boxes_admissible p hp
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound h1 h2 h4 f Q l hf hproper hQ S (by
    intro P hP
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨b.base, b.high⟩)
  have hfibre (P : Ideal GeoJets) (hP : P ∈ S) :
      (∑ c ∈ fibre P, charge c) ≤ mixedDegree B (cylinder P) {2, 3, 4} := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    let G := graphLift b b.surface
    let C (c : Branch f Q l) := graphLift c c.curve
    obtain ⟨hboxG, ⟨E, hboxE, hE⟩, _, _⟩ := hF b hb
    obtain ⟨hZprime, hZdim⟩ := hZ _ hP
    obtain ⟨hproperG, hG, hGdim, hC⟩ := h5 b E hZprime hZdim hE
    have hproperE := member_proper_on_graph b hE
    have inj : Set.InjOn C (fibre b.surface : Set (Branch f Q l)) := by
      intro c hc d hd he
      have hcs := (Finset.mem_filter.mp hc).2
      have hds := (Finset.mem_filter.mp hd).2
      apply Branch.eq_of_surface_curve (hcs.trans hds.symm)
      rw [← graphLift_comap c c.curve c.divisor.isPrime c.regularCurve,
        ← graphLift_comap d d.curve d.divisor.isPrime d.regularCurve]
      exact congrArg (Ideal.comap oldEmbedding) he
    have hmarks : (∑ c ∈ fibre b.surface, charge c) ≤
        ∑ c ∈ fibre b.surface, (c.weight : ℚ) * mixedDegree B (C c) {4} := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨hcF, hcs⟩ := Finset.mem_filter.mp hc
      obtain ⟨_, _, hon, hslice⟩ := hF c hcF
      obtain ⟨hcomp, hdim⟩ := hC c hcs
      exact mul_le_mul_of_nonneg_left
        (bound_marks hdiv hB c (T c) rfl hon hslice hcomp.minimal.isPrime hdim)
        (Nat.cast_nonneg _)
    have hEbound := hdiv B hB G {4} 3 hG.minimal.isPrime (by decide) hGdim E hboxE hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := hdiv B hB (cylinder b.surface) {3, 4} 2 hZprime (by decide) hZdim
      b.graph hboxG hproperG {G} id (fun _ => 1) (fun _ _ _ _ h => h) (by
        intro P hP
        obtain rfl := Finset.mem_singleton.mp hP
        exact hG)
    have hGbound' : mixedDegree B G {3, 4} ≤ mixedDegree B (cylinder b.surface) {2, 3, 4} := by
      simpa only [Finset.sum_singleton, Nat.cast_one, one_mul, id_eq] using hGbound
    exact hmarks.trans (hEbound.trans hGbound')
  have hcharge : (∑ c ∈ F, charge c) ≤ ∑ P ∈ S, mixedDegree B (cylinder P) {2, 3, 4} := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
      (fun b hb => Finset.mem_image_of_mem Branch.surface hb) charge]
    exact Finset.sum_le_sum hfibre
  have htotal := (mul_le_mul_of_nonneg_left hcharge (Nat.cast_nonneg l)).trans hsumZ
  have hr : 32 * ((l : ℚ) * (∑ b ∈ F, charge b)) ≤ (budget5 p : ℚ) :=
    (mul_le_mul_of_nonneg_left htotal (by norm_num)).trans (h3 p hp)
  apply (Nat.cast_le (α := ℚ)).mp
  push_cast
  simpa only [charge, mul_assoc] using hr
end
end K1_13_6_2_4
end
section
namespace K1_13_6_2_3_2
noncomputable section
open K1_13_6 MvPolynomial
theorem standard_rank {ι σ : Type} [Fintype ι] [DecidableEq ι]
    (slot : σ → ι) (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ GeoField))
    (hI : Graded slot I) (a : ι → ℕ) :
    hilbert slot I a =
      ({e | e ∈ m.standardExponents I ∧ Finsupp.weight (step ∘ slot) e = a}.ncard : ℕ) := by
  classical
  let w := step ∘ slot
  let E : Set (σ →₀ ℕ) := {e | e ∈ m.standardExponents I ∧ Finsupp.weight w e = a}
  let S := restrictSupport GeoField E
  let T := weightedHomogeneousSubmodule GeoField w a
  let mk := (Ideal.Quotient.mkₐ GeoField I).toLinearMap
  have hST : S ≤ T := by
    intro f hf e he
    exact (hf (mem_support_iff.mpr he)).2
  let φ : S →ₗ[GeoField] T.map mk := (mk.domRestrict S).codRestrict (T.map mk)
    (fun f => Submodule.mem_map.mpr ⟨f, hST f.2, rfl⟩)
  have hinj : Function.Injective φ := by
    intro f g hfg
    have heq : mk f = mk g := congrArg Subtype.val hfg
    apply Subtype.ext
    exact m.eq_of_mem_standardSpace_of_sub_mem
      (fun e he => (f.2 he).1) (fun e he => (g.2 he).1) (Ideal.Quotient.eq.mp heq)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨f, hf, heq⟩ := Submodule.mem_map.mp x.2
    obtain ⟨q, hq, hfq, _⟩ := m.exists_mem_standardSpace_sub_mem I f
    let q' := weightedHomogeneousComponent w a q
    have hq' : q' ∈ S := by
      intro e he
      have hc := mem_support_iff.mp he
      change (weightedHomogeneousComponent w a q).coeff e ≠ 0 at hc
      rw [coeff_weightedHomogeneousComponent] at hc
      by_cases ha : Finsupp.weight w e = a
      · rw [ite_eq_left ha] at hc
        exact ⟨hq (mem_support_iff.mpr hc), ha⟩
      · simp [ha] at hc
    have hproj : weightedHomogeneousComponent w a f = f :=
      IsWeightedHomogeneous.weightedHomogeneousComponent_same hf
    have hsub : f - q' ∈ I := by
      have h := hI (f - q) hfq a
      change weightedHomogeneousComponent w a (f - q) ∈ I at h
      rw [map_sub, hproj] at h
      exact h
    exact ⟨⟨q', hq'⟩, Subtype.ext ((Ideal.Quotient.eq.mpr hsub).symm.trans heq)⟩
  have heq := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  change ((Module.finrank GeoField (T.map mk) : ℕ) : ℚ) = (E.ncard : ℕ)
  rw [← heq, Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField E), Nat.card_coe_set_eq]
end
end K1_13_6_2_3_2
end
section
namespace K1_13_6_2_2_2
noncomputable section
open K1_13 MvPolynomial
open scoped Polynomial
abbrev Dual (A : Type*) [CommRing A] := TrivSqZeroExt A A
def coefficientJet {A : Type*} [CommRing A] (e : Geom[X] →+* A) : Geom[X] →+* Dual A where
  toFun c := (e c, e (Polynomial.derivative c))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' c d := by
    apply TrivSqZeroExt.ext
    · change e (c + d) = e c + e d
      exact map_add _ _ _
    · change e (Polynomial.derivative (c + d)) =
        e (Polynomial.derivative c) + e (Polynomial.derivative d)
      simp only [map_add]
  map_mul' c d := by
    apply TrivSqZeroExt.ext
    · change e (c * d) = e c * e d
      exact map_mul _ _ _
    · change e (Polynomial.derivative (c * d)) =
        e c * e (Polynomial.derivative d) + e (Polynomial.derivative c) * e d
      rw [Polynomial.derivative_mul, map_add, map_mul, map_mul, add_comm]
def coefficientDiff {n : ℕ} (P : Row n) : Row n :=
  ∑ m ∈ P.support, monomial m (Polynomial.derivative (P.coeff m))
@[simp] private theorem coeff_coefficientDiff {n : ℕ} (P : Row n) (m : Fin n →₀ ℕ) :
    (coefficientDiff P).coeff m = Polynomial.derivative (P.coeff m) := by
  classical
  rw [coefficientDiff, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm, map_zero]
theorem coefficientDiff_C {n : ℕ} (c : Geom[X]) :
    coefficientDiff (C c : Row n) = C (Polynomial.derivative c) := by
  classical
  ext m
  rw [coeff_coefficientDiff]
  by_cases hm : 0 = m <;> simp [coeff_C, hm]
theorem coefficientDiff_add {n : ℕ} (P Q : Row n) :
    coefficientDiff (P + Q) = coefficientDiff P + coefficientDiff Q := by
  ext m
  simp
theorem coefficientDiff_mul_X {n : ℕ} (P : Row n) (j : Fin n) :
    coefficientDiff (P * MvPolynomial.X j) = coefficientDiff P * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_coefficientDiff, coeff_mul_X', coeff_mul_X']
  split_ifs <;> simp
theorem dual_chain {n : ℕ} {A : Type*} [CommRing A]
    (e : Row n →+* A) (j : Row n →+* Dual A)
    (hfst : ∀ P, (j P).fst = e P)
    (hC : ∀ c, (j (C c)).snd = e (C (Polynomial.derivative c))) (P : Row n) :
    (j P).snd = e (coefficientDiff P) + ∑ i, (j (MvPolynomial.X i)).snd * e (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [hC, coefficientDiff_C]
  | add P Q hP hQ =>
    simp only [map_add, TrivSqZeroExt.snd_add, coefficientDiff_add, hP, hQ,
      mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P l ih =>
    rw [map_mul]
    change (j P).fst * (j (MvPolynomial.X l)).snd + (j P).snd * (j (MvPolynomial.X l)).fst = _
    rw [hfst, hfst, ih, coefficientDiff_mul_X, map_mul]
    simp only [pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    have left : (∑ i, (j (MvPolynomial.X i)).snd * (e (pderiv i P) * e (MvPolynomial.X l))) =
        (∑ i, (j (MvPolynomial.X i)).snd * e (pderiv i P)) * e (MvPolynomial.X l) := by
      simp only [Finset.sum_mul, mul_assoc]
    have right : (∑ i, (j (MvPolynomial.X i)).snd * (e P * e (pderiv i (MvPolynomial.X l)))) =
        (j (MvPolynomial.X l)).snd * e P := by
      simp [pderiv_X, Pi.single_apply, mul_ite]
    rw [left, right]
    ring
end
end K1_13_6_2_2_2
end
section
namespace K1_13_6_2_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 Filter
def c1 : Prop :=
  ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (A B : Finset (σ →₀ ℕ)), outside B ⊆ outside A →
    let H := fun a => sliceCount slot A a - sliceCount slot B a
    (∃ P : MvPolynomial ι ℚ, ∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) ∧
    ∀ used : List ι, ∀ᶠ a in atTop, 0 ≤ deltas used H a
def c2 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape),
    (∀ i, ChamberBox (shapes i)) → ∀ a : ι → ℕ,
      productExponents shapes a = capExponents (shapeSum shapes a)
def c3 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets),
    Graded (capSlot shapes) (capIdeal shapes J) ∧ ∀ a : ι → ℕ,
      hilbert (capSlot shapes) (capIdeal shapes J) a = (supportRank J (productExponents shapes a) : ℚ)
def c4 : Prop :=
  ∀ (J : Ideal GeoJets) (p : Shape) (n : ℕ),
    MvPolynomial.affineHilbertFunction
      (J.comap (MvPolynomial.monomialMap GeoField (capExponents p)).toRingHom) n =
    supportRank J (productExponents (fun _ : Unit => p) (fun _ => n))
def c5 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets)
    (base : ι) (used : List ι),
    (∀ i, ChamberBox (shapes i)) → base ∉ used → used.Nodup → dimension J ≤ used.length →
    (∀ q : Shape, ChamberBox q → ∀ n,
      MvPolynomial.affineHilbertFunction
        (J.comap (MvPolynomial.monomialMap GeoField (capExponents q)).toRingHom) n =
      supportRank J (capExponents (q.scale n))) →
    let H := fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ)
    ∀ P : MvPolynomial ι ℚ, (∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) →
      ∀ᶠ a in atTop,
        deltas used H a = polarize (capCoeff J used.length) (used.map shapes) (shapes base)
def c6 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (i : ι)
    (J : Ideal GeoJets) (D : GeoJets),
    Box4 (shapes i) D → IsLeftRegular (Ideal.Quotient.mk J D) →
    let slot := capSlot shapes
    let I := capIdeal shapes J
    let I₁ := capIdeal shapes (cut J D)
    let I₂ := capIdeal shapes (cut J (D ^ 2))
    Graded slot I → Graded slot I₂ →
    ∃ B C : Ideal (MvPolynomial (CapVar shapes) GeoField),
      Graded slot B ∧ Graded slot C ∧ B ≤ I₂ ∧ C ≤ I₁ ∧
      (∀ a : ι → ℕ, hilbert slot B (a + step i) + hilbert slot I a = hilbert slot I (a + step i)) ∧
      ∀ a : ι → ℕ, hilbert slot C (a + step i) + hilbert slot I₁ a = hilbert slot I₂ (a + step i)
private lemma deltas_sub {ι : Type} [DecidableEq ι] (used : List ι)
    (H G : (ι → ℕ) → ℚ) (a : ι → ℕ) :
    deltas used (fun b => H b - G b) a = deltas used H a - deltas used G a := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih]; ring
private lemma deltas_shift {ι : Type} [DecidableEq ι] (used : List ι)
    (H : (ι → ℕ) → ℚ) (a v : ι → ℕ) :
    deltas used (fun b => H (b + v)) a = deltas used H (a + v) := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih, add_right_comm a (step i) v]
private lemma eventually_shift {ι : Type} {Q : (ι → ℕ) → Prop} (v : ι → ℕ)
    (h : ∀ᶠ a in atTop, Q a) : ∀ᶠ a in atTop, Q (a + v) := by
  obtain ⟨u, hu⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨u, fun a ha => hu (a + v) (ha.trans (le_add_of_nonneg_right zero_le))⟩
private lemma spend {ι : Type} [DecidableEq ι] (used : List ι) (v : ι → ℕ)
    (B C G H : (ι → ℕ) → ℚ) (heq : ∀ a, B (a + v) + H a = G (a + v))
    (hpos : ∀ᶠ a in atTop, 0 ≤ deltas used (fun b => B b - C b) a) :
    ∀ᶠ a in atTop, deltas used C (a + v) ≤ deltas used G (a + v) - deltas used H a := by
  have hid : (fun a => B (a + v)) = fun a => G (a + v) - H a := by
    funext a
    linarith [heq a]
  filter_upwards [eventually_shift v hpos] with a ha
  rw [deltas_sub] at ha
  rw [← deltas_shift used B, hid, deltas_sub, deltas_shift] at ha
  linarith
private lemma graded_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (slot : σ → ι) :
    Graded slot (⊤ : Ideal (MvPolynomial σ GeoField)) := by
  intro f hf a
  exact Submodule.mem_top
private lemma hilbert_top {ι σ : Type} [DecidableEq ι] (slot : σ → ι) (a : ι → ℕ) :
    hilbert slot (⊤ : Ideal (MvPolynomial σ GeoField)) a = 0 := by
  have : Subsingleton (MvPolynomial σ GeoField ⧸ (⊤ : Ideal (MvPolynomial σ GeoField))) :=
    (Ideal.Quotient.subsingleton_iff).2 rfl
  simp [hilbert, Module.finrank_eq_zero_of_subsingleton]
private theorem hilbert_difference (h1 : c1)
    {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (I K : Ideal (MvPolynomial σ GeoField))
    (hI : Graded slot I) (hK : Graded slot K) (hle : I ≤ K) :
    let H := fun a => hilbert slot I a - hilbert slot K a
    (∃ P : MvPolynomial ι ℚ, ∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) ∧
    ∀ used : List ι, ∀ᶠ a in atTop, 0 ≤ deltas used H a := by
  classical
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff I
  obtain ⟨B, hB⟩ := m.exists_finset_standardExponents_iff K
  have hAB : outside B ⊆ outside A := by
    intro e he
    exact (hA e).mp (fun f hf => (hB e).mpr he f (hle hf))
  have eqI : hilbert slot I = sliceCount slot A := by
    funext a
    rw [standard_rank slot m I hI a]
    simp only [sliceCount, hA, outside, Set.mem_ofPred_eq]
  have eqK : hilbert slot K = sliceCount slot B := by
    funext a
    rw [standard_rank slot m K hK a]
    simp only [sliceCount, hB, outside, Set.mem_ofPred_eq]
  rw [eqI, eqK]
  exact h1 slot A B hAB
theorem read_cap (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets)
    (base : ι) (used : List ι) (hsh : ∀ i, ChamberBox (shapes i))
    (hb : base ∉ used) (hn : used.Nodup) (hd : dimension J ≤ used.length) :
    ∀ᶠ a in atTop, deltas used (hilbert (capSlot shapes) (capIdeal shapes J)) a =
      polarize (capCoeff J used.length) (used.map shapes) (shapes base) := by
  let slot := capSlot shapes
  let I := capIdeal shapes J
  have hI := (h3 shapes J).1
  have hall := (hilbert_difference h1 slot I ⊤ hI (graded_top slot) le_top).1
  rw [show (fun a => hilbert slot I a - hilbert slot ⊤ a) = hilbert slot I by
    funext a; simp [hilbert_top]] at hall
  obtain ⟨P, hP⟩ := hall
  have hrank : hilbert slot I = fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ) := by
    funext a
    rw [(h3 shapes J).2 a, h2 shapes hsh a]
  rw [hrank] at hP ⊢
  refine h5 shapes J base used hsh hb hn hd (fun q hq n => ?_) P hP
  rw [h4, h2 (fun _ : Unit => q) (fun _ => hq)]
  simp [shapeSum, Shape.scale]
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) :
    K1_13_6_2_3.c2 := by
  classical
  intro J p boxes hp hboxes hdim D hD hreg
  let ι := Option (Option (Fin boxes.length))
  let base : ι := none
  let i : ι := some none
  let emb : Fin boxes.length → ι := fun k => some (some k)
  let rest := (List.finRange boxes.length).map emb
  let shapes : ι → Shape
    | none => ⟨3, 3, 1⟩
    | some none => p
    | some (some k) => boxes.get k
  have hsh (k : ι) : ChamberBox (shapes k) := by
    cases k with
    | none =>
      change ChamberBox ⟨3, 3, 1⟩
      exact ⟨by decide, by decide, by decide⟩
    | some k => cases k with
      | none => exact hp
      | some k => exact hboxes _ (List.get_mem _ _)
  have hbase : base ∉ rest := by simp [base, rest, emb]
  have hi : i ∉ rest := by
    intro h
    obtain ⟨k, _, hk⟩ := List.mem_map.mp h
    change (some (some k) : Option (Option (Fin boxes.length))) = some none at hk
    have hinner : (some k : Option (Fin boxes.length)) = none := Option.some.inj hk
    cases hinner
  have hn : rest.Nodup := (List.nodup_finRange _).map
    (fun _ _ h => Option.some.inj (Option.some.inj h))
  have hbase' : base ∉ i :: rest := by simp [base, i, rest, emb]
  have hn' : (i :: rest).Nodup := List.nodup_cons.mpr ⟨hi, hn⟩
  have hmap : rest.map shapes = boxes := by
    simp [rest, List.map_map, Function.comp_def, emb, shapes]
  have hlen : rest.length = boxes.length := by simp [rest]
  let slot := capSlot shapes
  let I := capIdeal shapes J
  let I₁ := capIdeal shapes (cut J D)
  let I₂ := capIdeal shapes (cut J (D ^ 2))
  have hgraded₂ := (h3 shapes (cut J (D ^ 2))).1
  obtain ⟨B, C, hB, hC, hBI, hCI, heqB, heqC⟩ := h6 shapes i J D hD hreg (h3 shapes J).1 hgraded₂
  have hposB := (hilbert_difference h1 slot B I₂ hB hgraded₂ hBI).2 rest
  have hposC := (hilbert_difference h1 slot C I₁ hC (h3 shapes (cut J D)).1 hCI).2 rest
  have hspendB := spend rest (step i) (hilbert slot B) (hilbert slot I₂) (hilbert slot I)
    (hilbert slot I) heqB hposB
  have hspendC := spend rest (step i) (hilbert slot C) (hilbert slot I₁) (hilbert slot I₂)
    (hilbert slot I₁) heqC hposC
  have hd₁ : dimension (cut J D) ≤ rest.length := by
    have hdrop : dimension (cut J D) ≤ dimension J - 1 := cut_dimension hreg
    omega
  have hd₀ : dimension J ≤ (i :: rest).length := by simpa [hlen] using hdim
  have hr₀ := read_cap h1 h2 h3 h4 h5 shapes J base (i :: rest) hsh hbase' hn' hd₀
  have hr₁ := read_cap h1 h2 h3 h4 h5 shapes (cut J D) base rest hsh hbase hn hd₁
  have hfinal : ∀ᶠ _a in (atTop : Filter (ι → ℕ)),
      2 * polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ ≤
        polarize (capCoeff J (p :: boxes).length) (p :: boxes) ⟨3, 3, 1⟩ := by
    filter_upwards [hspendB, hspendC, hr₀, hr₁, eventually_shift (step i) hr₁] with a hb hc h₀ h₁ h₁'
    rw [List.map_cons, hmap, List.length_cons, hlen] at h₀
    rw [hlen, hmap] at h₁ h₁'
    change deltas rest (hilbert slot I) (a + step i) - deltas rest (hilbert slot I) a =
      polarize (capCoeff J (boxes.length + 1)) (p :: boxes) ⟨3, 3, 1⟩ at h₀
    change deltas rest (hilbert slot I₁) a =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁
    change deltas rest (hilbert slot I₁) (a + step i) =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁'
    simp only [List.length_cons]
    linarith [hb, hc, h₀, h₁, h₁']
  obtain ⟨_, hfinal⟩ := hfinal.exists
  unfold mixedDegree
  rw [List.length_cons, pow_succ, mul_comm ((2 : ℚ)^boxes.length) 2, ← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).2 (by simpa [mul_comm] using hfinal)
end
end K1_13_6_2_3_2
end
section
namespace K1_13_6_2_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_2 MvPolynomial
open scoped Polynomial
abbrev Chart (g : Row 4) := Localization.Away (separant g)
abbrev incl (g : Row 4) : Row 4 →+* Chart g := algebraMap _ _
abbrev S (g : Row 4) : Chart g := incl g (separant g)
abbrev invS (g : Row 4) : Chart g := IsLocalization.Away.invSelf (separant g)
theorem S_mul_invS (g : Row 4) : S g * invS g = 1 :=
  IsLocalization.Away.mul_invSelf _
abbrev constants (g : Row 4) : Geom[X] →+* Chart g := (incl g).comp C
abbrev negQuarter : Geom := -(4 : Geom)⁻¹
theorem negQuarter_mul_four : negQuarter * (4 : Geom) = -1 := by
  let _ : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have h : (4 : Geom) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff Geom K1.p 4).mp hz
    exact (by decide : ¬ 4 % K1.p = 0) (Nat.dvd_iff_mod_eq_zero.mp hd)
  rw [negQuarter, neg_mul, inv_mul_cancel₀ h]
abbrev q (g : Row 4) : Chart g := constants g (Polynomial.C negQuarter)
theorem q_mul_four (g : Row 4) : q g * 4 = -1 := by
  let e := (constants g).comp Polynomial.C
  change e negQuarter * 4 = -1
  calc
    _ = e negQuarter * e 4 := by rw [map_ofNat]
    _ = e (negQuarter * 4) := (map_mul _ _ _).symm
    _ = _ := by rw [negQuarter_mul_four, map_neg, map_one]
def W (g : Row 4) : Chart g := q g * incl g (partialFlow g) * invS g
theorem four_mul_W (g : Row 4) : 4 * W g = -(incl g (partialFlow g) * invS g) := by
  unfold W
  calc
    _ = (q g * 4) * (incl g (partialFlow g) * invS g) := by ring
    _ = _ := by rw [q_mul_four, neg_one_mul]
def graphMap (g : Row 4) : Row 5 →+* Chart g :=
  eval₂Hom (constants g) (Fin.lastCases (W g) (fun i => incl g (MvPolynomial.X i)))
@[simp] theorem graphMap_C (g : Row 4) (a : Geom[X]) :
    graphMap g (C a) = constants g a := eval₂Hom_C _ _ _
@[simp] theorem graphMap_X_last (g : Row 4) :
    graphMap g (MvPolynomial.X (Fin.last 4)) = W g :=
  (eval₂Hom_X' _ _ _).trans Fin.lastCases_last
@[simp] theorem graphMap_X_old (g : Row 4) (i : Fin 4) :
    graphMap g (MvPolynomial.X i.castSucc) = incl g (MvPolynomial.X i) := by simp [graphMap]
@[simp] theorem graphMap_lift (g P : Row 4) : graphMap g (lift4 P) = incl g P := by
  have h : (graphMap g).comp lift4.toRingHom = incl g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  exact DFunLike.congr_fun h P
def oldJet (g : Row 4) : Row 4 →+* Dual (Chart g) :=
  eval₂Hom (coefficientJet (constants g))
    (fun i => (incl g (MvPolynomial.X i),
      Fin.lastCases (4 * W g)
        (fun j : Fin 3 => (j.val + 1 : ℕ) * incl g (MvPolynomial.X j.succ)) i))
theorem oldJet_C (g : Row 4) (a : Geom[X]) :
    oldJet g (C a) = (constants g a, constants g (Polynomial.derivative a)) :=
  eval₂Hom_C _ _ _
theorem oldJet_X (g : Row 4) (i : Fin 4) :
    oldJet g (MvPolynomial.X i) = (incl g (MvPolynomial.X i),
      Fin.lastCases (4 * W g)
        (fun j : Fin 3 => (j.val + 1 : ℕ) * incl g (MvPolynomial.X j.succ)) i) :=
  eval₂Hom_X' _ _ _
theorem oldJet_fst (g P : Row 4) : (oldJet g P).fst = incl g P := by
  have h : (TrivSqZeroExt.fstHom (Chart g) (Chart g) (Chart g)).toRingHom.comp
      (oldJet g) = incl g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (oldJet g (C a)).fst = incl g (C a)
      rw [oldJet_C, TrivSqZeroExt.fst_mk]
      rfl
    · intro i
      change (oldJet g (MvPolynomial.X i)).fst = incl g (MvPolynomial.X i)
      rw [oldJet_X, TrivSqZeroExt.fst_mk]
  exact DFunLike.congr_fun h P
private def localJet (g : Row 4) : Chart g →+* Dual (Chart g) :=
  IsLocalization.Away.lift (separant g) (g := oldJet g)
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
      rw [oldJet_fst]
      exact IsLocalization.Away.algebraMap_isUnit _))
@[simp] private theorem localJet_incl (g P : Row 4) :
    localJet g (incl g P) = oldJet g P := IsLocalization.Away.lift_eq _ _ _
theorem localJet_fst (g : Row 4) (a : Chart g) : (localJet g a).fst = a := by
  have h : (TrivSqZeroExt.fstHom (Chart g) (Chart g) (Chart g)).toRingHom.comp
      (localJet g) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (separant g))
    apply RingHom.ext
    intro P
    change (localJet g (incl g P)).fst = incl g P
    rw [localJet_incl, oldJet_fst]
  exact DFunLike.congr_fun h a
def D (g : Row 4) : Chart g →+ Chart g :=
  (TrivSqZeroExt.sndHom (R := Chart g) (M := Chart g)).toAddMonoidHom.comp
    (localJet g).toAddMonoidHom
theorem D_mul (g : Row 4) (a b : Chart g) : D g (a * b) = a * D g b + D g a * b := by
  change (localJet g (a * b)).snd = _
  rw [map_mul]
  change (localJet g a).fst * D g b + D g a * (localJet g b).fst = _
  rw [localJet_fst, localJet_fst]
@[simp] theorem D_natCast (g : Row 4) (n : ℕ) : D g (n : Chart g) = 0 := by
  have h : D g 1 = 0 := by
    change (localJet g 1).snd = 0
    rw [map_one]
    rfl
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, map_add, ih, h, add_zero]
@[simp] theorem D_X_old (g : Row 4) (i : Fin 3) :
    D g (incl g (MvPolynomial.X i.castSucc)) = (i.val + 1 : ℕ) * incl g (MvPolynomial.X i.succ) := by
  change (localJet g (incl g (MvPolynomial.X i.castSucc))).snd = _
  rw [localJet_incl, oldJet_X, TrivSqZeroExt.snd_mk, Fin.lastCases_castSucc]
@[simp] theorem D_X_last (g : Row 4) :
    D g (incl g (MvPolynomial.X (Fin.last 3))) = 4 * W g := by
  change (localJet g (incl g (MvPolynomial.X (Fin.last 3)))).snd = _
  rw [localJet_incl, oldJet_X, TrivSqZeroExt.snd_mk, Fin.lastCases_last]
theorem D_incl_C (g : Row 4) (c : Geom[X]) :
    D g (constants g c) = constants g (Polynomial.derivative c) := by
  change (localJet g (incl g (C c))).snd = _
  rw [localJet_incl, oldJet_C, TrivSqZeroExt.snd_mk]
theorem D_incl (g P : Row 4) : S g * D g (incl g P) = incl g (flowNumerator g P) := by
  have h := dual_chain (incl g) (oldJet g) (oldJet_fst g) (by
    intro c
    rw [oldJet_C, TrivSqZeroExt.snd_mk]
    rfl) P
  have hs : D g (incl g P) =
      incl g (partialFlow P) + 4 * W g * incl g (separant P) := by
    change (localJet g (incl g P)).snd = _
    rw [localJet_incl, h, Fin.sum_univ_castSucc]
    simp only [oldJet_X, TrivSqZeroExt.snd_mk, Fin.lastCases_castSucc, Fin.lastCases_last,
      partialFlow, separant, map_add, map_sum, map_mul, map_natCast, ← add_assoc]
    rfl
  rw [hs, four_mul_W, flowNumerator, map_sub, map_mul, map_mul, mul_add]
  have hm : S g * (incl g (partialFlow g) * invS g) = incl g (partialFlow g) := by
    rw [← mul_left_comm, S_mul_invS, mul_one]
  linear_combination -incl g (separant P) * hm
theorem D_graphMap_X (g : Row 4) (i : Fin 4) :
    D g (graphMap g (MvPolynomial.X i.castSucc)) = (i.val + 1 : ℕ) * graphMap g (MvPolynomial.X i.succ) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change D g (graphMap g (MvPolynomial.X (Fin.last 3).castSucc)) =
      4 * graphMap g (MvPolynomial.X (Fin.last 4))
    rw [graphMap_X_old, graphMap_X_last, D_X_last]
  · rw [graphMap_X_old, Fin.succ_castSucc, graphMap_X_old, D_X_old]
    rfl
theorem D_graphMap (g : Row 4) (P : Row 5) :
    D g (graphMap g P) = graphMap g (fixedFlow P) +
      D g (W g) * graphMap g (pderiv (Fin.last 4) P) := by
  have h := dual_chain (graphMap g) ((localJet g).comp (graphMap g))
    (fun p => localJet_fst g (graphMap g p)) (by
      intro c
      change D g (graphMap g (C c)) = graphMap g (C (Polynomial.derivative c))
      rw [graphMap_C, graphMap_C, D_incl_C]) P
  change D g (graphMap g P) = graphMap g (coefficientDerivative5 P) +
    ∑ i, D g (graphMap g (MvPolynomial.X i)) * graphMap g (pderiv i P) at h
  rw [h, Fin.sum_univ_castSucc, graphMap_X_last, ← add_assoc]
  simp only [D_graphMap_X, fixedFlow, map_add, map_sum, map_mul, map_natCast]
theorem graph_zero (g : Row 4) : graphMap g (rawGraph g) = 0 := by
  rw [rawGraph, map_add, map_mul, map_mul, graphMap_lift, graphMap_lift, graphMap_X_last,
    graphMap_C, map_ofNat]
  change incl g (partialFlow g) + 4 * S g * W g = 0
  have hm : S g * (incl g (partialFlow g) * invS g) = incl g (partialFlow g) := by
    rw [← mul_left_comm, S_mul_invS, mul_one]
  rw [mul_comm (4 : Chart g) (S g), mul_assoc, four_mul_W, mul_neg, hm, add_neg_cancel]
@[simp] private theorem pderiv_last_lift (P : Row 4) :
    pderiv (Fin.last 4) (lift4 P) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨i, _, hi⟩ := mem_vars_rename Fin.castSucc P hv
  exact Fin.castSucc_ne_last i hi
theorem pderiv_graph (g : Row 4) :
    pderiv (Fin.last 4) (rawGraph g) = C (4 : Geom[X]) * lift4 (separant g) := by
  rw [rawGraph, map_add, pderiv_last_lift, zero_add, pderiv_mul, pderiv_C_mul,
    pderiv_last_lift, mul_zero, zero_mul, pderiv_X_self, mul_one, zero_add]
theorem D_W (g : Row 4) : S g * D g (W g) = graphMap g (fifthFlow g) := by
  have h := congrArg (D g) (graph_zero g)
  rw [map_zero, D_graphMap, pderiv_graph, map_mul, graphMap_C, map_ofNat, graphMap_lift] at h
  change graphMap g (fixedFlow (rawGraph g)) + D g (W g) * (4 * S g) = 0 at h
  rw [fifthFlow, map_mul, graphMap_C]
  change S g * D g (W g) = q g * graphMap g (fixedFlow (rawGraph g))
  linear_combination -q g * h + S g * D g (W g) * q_mul_four g
theorem D_graphMap_sigma (g : Row 4) :
    D g (S g) = graphMap g (fixedFlow (lift4 (separant g))) := by
  simpa only [graphMap_lift, pderiv_last_lift, map_zero, mul_zero, add_zero] using
    D_graphMap g (lift4 (separant g))
theorem lifted_step (g : Row 4) (T : Row 5) (n : ℕ) :
    graphMap g (lift4 (separant g) * fixedFlow T + fifthFlow g * pderiv (Fin.last 4) T -
      (n : Row 5) * fixedFlow (lift4 (separant g)) * T) =
      S g * D g (graphMap g T) - (n : Chart g) * D g (S g) * graphMap g T := by
  simp only [map_sub, map_add, map_mul, map_natCast, graphMap_lift,
    ← D_graphMap_sigma, ← D_W, D_graphMap]
  ring
end
end K1_13_6_2_2_2
end
section
namespace K1_13_6_2_4_3
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
open scoped BigOperators
def sumCap (B : Boxes) (t : Fin 5 → ℕ) : Shape × ℕ :=
  (⟨∑ i, t i * (B i).1.b, ∑ i, t i * (B i).1.j, ∑ i, t i * (B i).1.t⟩,
    ∑ i, t i * (B i).2)
def scaleCap (a : Shape × ℕ) (n : ℕ) : Shape × ℕ :=
  (a.1.scale n, n * a.2)
theorem sumCap_chamber (B : Boxes) (hB : ∀ i, Chamber (B i).1) (t : Fin 5 → ℕ) :
    Chamber (sumCap B t).1 := by
  unfold Chamber sumCap
  dsimp only
  constructor
  · exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hB i).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left (t i) (hB i).2)
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators
theorem dim_le_of_integral_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun chain => ?_
  obtain ⟨q, hq⟩ := hf.comap_surjective hinj chain.head
  have : q.asIdeal.LiesOver chain.head.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hq.symm⟩
  obtain ⟨lifted, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp chain q.asIdeal
  exact le_iSup_of_le lifted (by rw [hlen])
theorem hilbert_degree_le {σ : Type*} [Finite σ] {P : Ideal (MvPolynomial σ GeoField)} {d : ℕ}
    (hd : ringKrullDim (MvPolynomial σ GeoField ⧸ P) ≤ ((d : ℕ∞) : WithBot ℕ∞)) :
    (affineHilbertPolynomial P).natDegree ≤ d := by
  by_cases hP : P = ⊤
  · simp [hP, affineHilbertPolynomial_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hP
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg GeoField (MvPolynomial σ GeoField ⧸ P)
  rw [natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfin hinj, Nat.card_fin]
  have hdim := (dim_le_of_integral_injective g.toRingHom hfin.to_isIntegral hinj).trans hd
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field] using hdim
theorem zero_in_box (a : Shape × ℕ) : (0 : Exponent) ∈ latticePoints a := by
  change Allowed (a.1.scale 2, 2 * a.2) 0
  simp [Allowed]
theorem diagonal_surjective {B : Boxes} (hB : Admissible B) {t : Fin 5 → ℕ}
    (ht : ∀ i, 0 < t i) : Function.Surjective (monomialMap GeoField (diagonalExponents B t)) := by
  classical
  apply monomialMap_surjective
  intro v
  obtain ⟨i, hi⟩ := hB.2 v
  let j₀ : Fin (t i) := ⟨0, ht i⟩
  let u (k : Fin 5) (j : Fin (t k)) : Exponent :=
    if h : k = i then if h ▸ j = j₀ then Finsupp.single v 1 else 0 else 0
  refine ⟨u, ?_, ?_⟩
  · intro k j
    by_cases hk : k = i
    · subst k
      by_cases hj : j = j₀
      · simpa [u, hj] using hi
      · simpa [u, hj] using zero_in_box (B i)
    · simpa [u, hk] using zero_in_box (B k)
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j₀]
      · simp [u]
      · intro j _ hj
        simp [u, hj]
      · simp
    · intro k _ hk
      simp [u, hk]
    · simp
theorem diagonal_degree_le {B : Boxes} (hB : Admissible B) {P : Ideal GeoJets5} {d : ℕ}
    (hP : DimLE P d) {t : Fin 5 → ℕ} (ht : ∀ i, 0 < t i) :
    (affineHilbertPolynomial (P.comap (monomialMap GeoField (diagonalExponents B t)))).natDegree ≤ d := by
  let f := monomialMap GeoField (diagonalExponents B t)
  let g := (Ideal.Quotient.mk P).comp f.toRingHom
  have hg : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp (diagonal_surjective hB ht)
  have hker : RingHom.ker g = P.comap f := by
    ext x
    change Ideal.Quotient.mk P (f x) = 0 ↔ f x ∈ P
    exact Ideal.Quotient.eq_zero_iff_mem
  apply hilbert_degree_le
  rw [← hker, (g.quotientKerEquivOfSurjective hg).ringKrullDim]
  exact hP
end
end K1_13_6_2_4_2
end
section
namespace K1_13_6_2_3_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3
open scoped BigOperators
def c1 : Prop :=
  ∀ (J : Ideal GeoJets) (d : ℕ), dimension J ≤ d →
    ∀ p : Shape, ChamberBox p →
      capCoeff J d p =
        ∑ P ∈ J.minimalPrimesFinset, (localWeight J P : ℚ) * capCoeff P d p
def c2 : Prop :=
  ∀ (P : Ideal GeoJets) (boxes : List Shape), P.IsPrime →
    (∀ q ∈ boxes, ChamberBox q) → dimension P = boxes.length → 2 ≤ boxes.length →
      0 ≤ mixedDegree P boxes
private abbrev baseline : Shape := ⟨3, 3, 1⟩
private lemma baseline_box : ChamberBox baseline := ⟨by decide, by decide, by decide⟩
private lemma chamber_plus {p q : Shape} (hp : ChamberBox p) (hq : ChamberBox q) :
    ChamberBox (p.plus q) := by
  obtain ⟨hp₁, hp₂, hp₃⟩ := hp
  obtain ⟨hq₁, hq₂, hq₃⟩ := hq
  refine ⟨Nat.add_le_add hp₁ hq₁, ?_, Nat.add_pos_left hp₃ _⟩
  change 3 * (p.t + q.t) ≤ p.j + q.j
  omega
private lemma polarize_congr {H G : Shape → ℚ} (h : ∀ p, ChamberBox p → H p = G p)
    {boxes : List Shape} (hboxes : ∀ q ∈ boxes, ChamberBox q) {p : Shape}
    (hp : ChamberBox p) : polarize H boxes p = polarize G boxes p := by
  induction boxes generalizing p with
  | nil => exact h p hp
  | cons q boxes ih =>
    have hq := hboxes q List.mem_cons_self
    have hr := fun r hr => hboxes r (List.mem_cons_of_mem _ hr)
    simp only [polarize, ih hr (chamber_plus hp hq), ih hr hp]
lemma polarize_sum {ι : Type*} (S : Finset ι) (w : ι → ℚ) (H : ι → Shape → ℚ)
    (boxes : List Shape) (p : Shape) :
    polarize (fun x => ∑ i ∈ S, w i * H i x) boxes p =
      ∑ i ∈ S, w i * polarize (H i) boxes p := by
  induction boxes generalizing p with
  | nil => rfl
  | cons q boxes ih =>
    simp only [polarize, ih, ← Finset.sum_sub_distrib, mul_sub]
private lemma polarize_zero (boxes : List Shape) (p : Shape) :
    polarize (fun _ => 0) boxes p = 0 := by
  induction boxes generalizing p with
  | nil => rfl
  | cons q boxes ih => simp only [polarize, ih, sub_self]
private abbrev capMap (p : Shape) := MvPolynomial.monomialMap GeoField (capExponents p)
private lemma capMap_surjective {p : Shape} (hp : ChamberBox p) :
    Function.Surjective (capMap p) := by
  obtain ⟨hb, hj, ht⟩ := hp
  apply MvPolynomial.monomialMap_surjective
  intro i
  fin_cases i <;> simp [capExponents, Fin.sum_univ_four] <;> omega
private lemma cap_dimension (J : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) :
    (MvPolynomial.affineHilbertPolynomial (J.comap (capMap p).toRingHom)).natDegree =
      dimension J :=
  MvPolynomial.natDegree_affineHilbertPolynomial_comap_of_surjective
    (capMap p) (capMap_surjective hp) J
lemma mixed_zero_of_lt {J : Ideal GeoJets} {boxes : List Shape}
    (hboxes : ∀ p ∈ boxes, ChamberBox p) (hd : dimension J < boxes.length) :
    mixedDegree J boxes = 0 := by
  have hz (p : Shape) (hp : ChamberBox p) : capCoeff J boxes.length p = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((cap_dimension J hp).trans_lt hd)
  unfold mixedDegree
  rw [polarize_congr hz hboxes baseline_box, polarize_zero, zero_div]
private lemma capCoeff_le_of_subset (J : Ideal GeoJets) {p q : Shape}
    (hp : ChamberBox p) (hq : ChamberBox q) (hsub : capExponents p ⊆ capExponents q)
    {d : ℕ} (hd : dimension J ≤ d) :
    capCoeff J d p ≤ capCoeff J d q := by
  let incl (i : capExponents p) : capExponents q := ⟨i.val, hsub i.property⟩
  let f := MvPolynomial.rename (R := GeoField) incl
  have hf : (capMap q).comp f = capMap p := by
    ext i
    simp [f, incl, MvPolynomial.monomialMap_X]
  let I := J.comap (capMap p).toRingHom
  let K := J.comap (capMap q).toRingHom
  have heq : K.comap f.toRingHom = I := by
    change (J.comap (capMap q).toRingHom).comap f.toRingHom = _
    rw [Ideal.comap_comap]
    change J.comap ((capMap q).comp f).toRingHom = I
    rw [hf]
  let g := Ideal.quotientMapₐ K f heq.ge
  have hg : Function.Injective g := Ideal.quotientMap_injective' (H := heq.ge) heq.le
  have hgen (i : capExponents p) :
      g (Ideal.Quotient.mk I (MvPolynomial.X i)) ∈ MvPolynomial.quotientDegreeLE K 1 := by
    rw [show g (Ideal.Quotient.mk I (MvPolynomial.X i)) =
        Ideal.Quotient.mk K (MvPolynomial.X (incl i)) by
          change Ideal.quotientMap K f.toRingHom heq.ge
            (Ideal.Quotient.mk I (MvPolynomial.X i)) = _
          rw [Ideal.quotientMap_mk]
          change Ideal.Quotient.mk K (MvPolynomial.rename incl (MvPolynomial.X i)) = _
          rw [MvPolynomial.rename_X]]
    exact MvPolynomial.mk_X_mem_quotientDegreeLE K _
  change (MvPolynomial.affineHilbertPolynomial I).coeff d ≤
    (MvPolynomial.affineHilbertPolynomial K).coeff d
  refine Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    ((cap_dimension J hp).trans_le hd) ((cap_dimension J hq).trans_le hd) ?_
  filter_upwards [MvPolynomial.eventually_eval_affineHilbertPolynomial I,
    MvPolynomial.eventually_eval_affineHilbertPolynomial K] with n hI hK
  rw [hI, hK]
  exact_mod_cast (by simpa only [one_mul] using
    MvPolynomial.affineHilbertFunction_le_of_injective g hg hgen n :
      MvPolynomial.affineHilbertFunction I n ≤ MvPolynomial.affineHilbertFunction K n)
private lemma mixed_nonneg (h2 : c2) {P : Ideal GeoJets} (hP : P.IsPrime)
    {boxes : List Shape} (hboxes : ∀ q ∈ boxes, ChamberBox q)
    (hd : dimension P ≤ boxes.length) :
    0 ≤ mixedDegree P boxes := by
  rcases hd.lt_or_eq with hlt | heq
  · rw [mixed_zero_of_lt hboxes hlt]
  · cases boxes with
    | nil =>
      change 0 ≤ capCoeff P 0 baseline / (2 : ℚ) ^ 0
      apply div_nonneg _ (by norm_num)
      exact Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg
        ((cap_dimension P baseline_box).trans_le heq.le)
        (MvPolynomial.eventually_eval_affineHilbertPolynomial_nonneg _)
    | cons p boxes =>
      cases boxes with
      | nil =>
        have hp := hboxes p List.mem_cons_self
        have hsub : capExponents baseline ⊆ capExponents (baseline.plus p) := by
          intro m hm
          exact ⟨hm.1.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)),
            hm.2.1.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)),
            hm.2.2.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _))⟩
        change 0 ≤ (capCoeff P 1 (baseline.plus p) - capCoeff P 1 baseline) / (2 : ℚ) ^ 1
        exact div_nonneg (sub_nonneg.mpr
          (capCoeff_le_of_subset P baseline_box (chamber_plus baseline_box hp) hsub heq.le))
          (by norm_num)
      | cons q boxes =>
        exact h2 P (p :: q :: boxes) hP hboxes heq (by simp)
lemma mixed_cycle (h1 : c1) (J : Ideal GeoJets) (boxes : List Shape)
    (hboxes : ∀ q ∈ boxes, ChamberBox q) (hd : dimension J ≤ boxes.length) :
    mixedDegree J boxes =
      ∑ P ∈ J.minimalPrimesFinset, (localWeight J P : ℚ) * mixedDegree P boxes := by
  unfold mixedDegree
  rw [polarize_congr (h1 J boxes.length hd) hboxes baseline_box,
    polarize_sum, Finset.sum_div]
  simp only [mul_div_assoc]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2_3.c3 := by
  classical
  intro J boxes hboxes hd S hS
  rw [mixed_cycle h1 J boxes hboxes hd]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun P hP => Ideal.mem_minimalPrimesFinset.mpr (hS P hP)) ?_
  intro P hP _
  have hmin : J.IsMinimalPrime P := Ideal.mem_minimalPrimesFinset.mp hP
  have hdim := (MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hmin.le).trans hd
  exact mul_nonneg (Nat.cast_nonneg _) (mixed_nonneg h2 hmin.isPrime hboxes hdim)
end
end K1_13_6_2_3_3
end
section
namespace K1_13_6_2_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
open scoped BigOperators
def capPlus (x y : Shape × ℕ) : Shape × ℕ := (x.1.plus y.1, x.2 + y.2)
def volumeProduct (x : Shape × ℕ) : ℚ := (volume32 x.1 : ℚ) * x.2
def diagonal (J : Finset (Fin 5)) (i : Fin 5) : ℕ := if i ∈ J then 2 else 1
theorem diagonal_sum_insert (w : Fin 5 → ℕ) {i : Fin 5} {J : Finset (Fin 5)}
    (hi : i ∉ J) :
    (∑ k, diagonal (insert i J) k * w k) =
      (∑ k, diagonal J k * w k) + w i := by
  calc
    _ = ∑ k, (diagonal J k * w k + if k = i then w i else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = i
      · subst k
        simp [diagonal, hi, two_mul]
      · simp [diagonal, h]
    _ = _ := by simp [Finset.sum_add_distrib]
theorem sumCap_insert (B : Boxes) {i : Fin 5} {J : Finset (Fin 5)} (hi : i ∉ J) :
    sumCap B (diagonal (insert i J)) = capPlus (sumCap B (diagonal J)) (B i) := by
  simp only [sumCap, capPlus, Shape.plus, diagonal_sum_insert _ hi]
private def alt (B : Boxes) (s : Finset (Fin 5)) (F : Shape × ℕ → ℚ) : ℚ :=
  ∑ J ∈ s.powerset, (-1 : ℚ) ^ (s.card - J.card) * F (sumCap B (diagonal J))
private def capDiff (a : Shape × ℕ) (F : Shape × ℕ → ℚ) (x : Shape × ℕ) : ℚ :=
  F (capPlus x a) - F x
private theorem alt_empty (B : Boxes) (F : Shape × ℕ → ℚ) :
    alt B ∅ F = F (sumCap B (diagonal ∅)) := by
  simp [alt]
private theorem alt_insert (B : Boxes) {s : Finset (Fin 5)} {i : Fin 5}
    (hi : i ∉ s) (F : Shape × ℕ → ℚ) :
    alt B (insert i s) F = alt B s (capDiff (B i) F) := by
  have hJ (J) (hJ : J ∈ s.powerset) : i ∉ J :=
    Finset.notMem_of_mem_powerset_of_notMem hJ hi
  have hdisj : Disjoint s.powerset (s.powerset.image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro J hJs hJi
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hJi
    exact hJ _ hJs (Finset.mem_insert_self _ _)
  have hinj : Set.InjOn (insert i) (s.powerset : Set (Finset (Fin 5))) :=
    fun J hJs T hTs h => by
      simpa [Finset.erase_insert (hJ J hJs), Finset.erase_insert (hJ T hTs)] using
        congrArg (fun U : Finset (Fin 5) => U.erase i) h
  unfold alt
  rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJs
  have hcard := Finset.card_le_card (Finset.mem_powerset.mp hJs)
  have hstep : s.card + 1 - J.card = s.card - J.card + 1 := by omega
  rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem (hJ J hJs), hstep,
    pow_succ, sumCap_insert B (hJ J hJs)]
  simp only [Nat.add_sub_add_right, capDiff]
  ring
def signed4 (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩
private theorem signed4_le (p q r s : Shape) : (signed4 p q r s : ℚ) ≤ mixed32 p q r s := by
  have h : signed4 p q r s ≤ ((signed4 p q r s).toNat : ℤ) := by omega
  exact_mod_cast h
def shapeVolume (x : Shape) : ℚ := (volume32 x : ℚ)
def shapeShift (a : Shape) (F : Shape → ℚ) (x : Shape) : ℚ := F (x.plus a)
def shapeDiff (a : Shape) (F : Shape → ℚ) (x : Shape) : ℚ := F (x.plus a) - F x
theorem shapeDiff_shift (a b : Shape) (F : Shape → ℚ) :
    shapeDiff b (shapeShift a F) = shapeShift a (shapeDiff b F) := by
  funext x
  have h : (x.plus b).plus a = (x.plus a).plus b := by
    simp [Shape.plus, Nat.add_comm, Nat.add_left_comm]
  simp only [shapeDiff, shapeShift, h]
def constantInterval (F : Shape → ℚ) (x : Shape × ℕ) : ℚ := F x.1
def linearInterval (F : Shape → ℚ) (x : Shape × ℕ) : ℚ := F x.1 * x.2
theorem capDiff_add (a : Shape × ℕ) (F G : Shape × ℕ → ℚ) :
    capDiff a (fun x => F x + G x) = fun x => capDiff a F x + capDiff a G x := by
  funext x
  unfold capDiff
  ring
theorem capDiff_smul (a : Shape × ℕ) (d : ℚ) (F : Shape × ℕ → ℚ) :
    capDiff a (fun x => d * F x) = fun x => d * capDiff a F x := by
  funext x
  unfold capDiff
  ring
theorem capDiff_constantInterval (a : Shape) (d : ℕ) (F : Shape → ℚ) :
    capDiff (a, d) (constantInterval F) = constantInterval (shapeDiff a F) := rfl
theorem capDiff_linearInterval (a : Shape) (d : ℕ) (F : Shape → ℚ) :
    capDiff (a, d) (linearInterval F) =
      fun x => linearInterval (shapeDiff a F) x + (d : ℚ) * constantInterval (shapeShift a F) x := by
  funext x
  simp only [capDiff, linearInterval, capPlus, Nat.cast_add, constantInterval, shapeDiff, shapeShift]
  ring
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 4096 in
theorem fourth_difference (p q r s : Shape) :
    shapeDiff s (shapeDiff r (shapeDiff q (shapeDiff p shapeVolume))) =
      fun _ => (signed4 p q r s : ℚ) := by
  funext x
  simp only [shapeDiff, shapeVolume, signed4, difference, volume32, Shape.plus]
  push_cast
  ring
private theorem five_differences (p q g a b : Shape) (d e : ℕ) (x : Shape × ℕ) :
    capDiff (b, e) (capDiff (a, d) (capDiff (g, 1) (capDiff (q, 0)
      (capDiff (p, 0) volumeProduct)))) x =
      (signed4 p q a b : ℚ) + (d : ℚ) * (signed4 p q g b : ℚ) +
        (e : ℚ) * (signed4 p q g a : ℚ) := by
  change capDiff (b, e) (capDiff (a, d) (capDiff (g, 1) (capDiff (q, 0)
    (capDiff (p, 0) (linearInterval shapeVolume))))) x = _
  simp only [capDiff_linearInterval, capDiff_add, capDiff_smul, capDiff_constantInterval,
    Nat.cast_zero, zero_mul, add_zero, shapeDiff_shift, fourth_difference]
  simp only [linearInterval, constantInterval, shapeShift, shapeDiff, sub_self, zero_mul,
    zero_add, Nat.cast_one, one_mul]
  ring
theorem polarized_budget (p : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      volumeProduct (sumCap (boxes p) (diagonal J))) ≤ (budget5 p : ℚ) := by
  change alt (boxes p) Finset.univ volumeProduct ≤ _
  have hu : (Finset.univ : Finset (Fin 5)) = insert 0 (insert 1 (insert 2 (insert 3 (insert 4 ∅)))) := by
    decide
  rw [hu, alt_insert _ (by decide), alt_insert _ (by decide), alt_insert _ (by decide),
    alt_insert _ (by decide), alt_insert _ (by decide), alt_empty]
  let a := liftedChart (taylorLength + 1) p
  let b := liftedChart (taylorLength + 2) p
  change capDiff (b, taylorLength + 2) (capDiff (a, taylorLength + 1)
    (capDiff (graphBox p, 1) (capDiff (cutterBox, 0) (capDiff (p, 0) volumeProduct)))) _ ≤ _
  rw [five_differences]
  change _ ≤ ((mixed32 p cutterBox a b + (taylorLength + 1) * mixed32 p cutterBox (graphBox p) b +
    (taylorLength + 2) * mixed32 p cutterBox (graphBox p) a : ℕ) : ℚ)
  push_cast
  gcongr <;> apply signed4_le
end
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped Polynomial
abbrev Grade := Exponent
abbrev Form := MvPolynomial (Fin 5) ℚ
abbrev Generator (B : Boxes) := (i : Fin 5) × latticePoints (B i)
abbrev SlotRing (B : Boxes) := MvPolynomial (Generator B) GeoField
instance (B : Boxes) : Finite (Generator B) := by
  infer_instance
def unitGrade (i : Fin 5) : Grade := Finsupp.single i 1
def squarefree (I : Finset (Fin 5)) : Grade := ∑ i ∈ I, unitGrade i
def slotWeight {σ : Type} (slot : σ → Fin 5) (v : σ) : Grade := unitGrade (slot v)
abbrev piece {σ : Type} (slot : σ → Fin 5) :=
  weightedHomogeneousSubmodule GeoField (slotWeight slot)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def gradedHilbert {σ : Type} (slot : σ → Fin 5) (J : Ideal (MvPolynomial σ GeoField))
    (t : Grade) : ℕ :=
  Module.finrank GeoField ((piece slot t).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap)
def slot (B : Boxes) : Generator B → Fin 5 := Sigma.fst
def taggedMap (B : Boxes) : SlotRing B →ₐ[GeoField] GeoJets5 :=
  aeval fun v => monomial v.2.val 1
def gradedIdeal (B : Boxes) (P : Ideal GeoJets5) : Ideal (SlotRing B) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).toIdeal
def diagonalIdeal (B : Boxes) (P : Ideal GeoJets5) (t : Grade) :=
  P.comap (monomialMap GeoField (diagonalExponents B t))
def outside {σ : Type} (A : Finset (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
  {a | ∀ b ∈ A, ¬ b ≤ a}
def sliceCount {σ : Type} (s : σ → Fin 5) (A : Finset (σ →₀ ℕ)) (t : Grade) : ℕ :=
  {a ∈ outside A | Finsupp.weight (slotWeight s) a = t}.ncard
def Represents (p : Form) (h : Grade → ℚ) : Prop :=
  ∃ N : ℕ, ∀ t : Grade, (∀ j, N ≤ t j) → eval (fun j => (t j : ℚ)) p = h t
def TopNonnegative (p : Form) : Prop :=
  ∀ a : Grade, p.totalDegree ≤ a.degree → 0 ≤ p.coeff a
def line (t : Grade) : Form →+* ℚ[X] :=
  eval₂Hom Polynomial.C (fun j => Polynomial.C (t j : ℚ) * Polynomial.X)
def positiveDiagonal (J : Finset (Fin 5)) : Grade :=
  Finsupp.equivFunOnFinite.symm fun i => if i ∈ J then 2 else 1
end
end K1_13_6_2_4_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem gradedIdeal_homogeneous (B : Boxes) (P : Ideal GeoJets5) :
    (gradedIdeal B P).IsHomogeneous (piece (slot B)) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).isHomogeneous
theorem gradedIdeal_mono (B : Boxes) {P Q : Ideal GeoJets5} (h : P ≤ Q) :
    gradedIdeal B P ≤ gradedIdeal B Q :=
  Ideal.homogeneousCore_mono _ (Ideal.comap_mono h)
theorem mem_gradedIdeal_of_grade {B : Boxes} {P : Ideal GeoJets5} {a : SlotRing B}
    {t : Grade} (ha : a ∈ piece (slot B) t) :
    a ∈ gradedIdeal B P ↔ taggedMap B a ∈ P := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (piece (slot B)) (P.comap (taggedMap B)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t, ha⟩ h
theorem component_mul_of_grade {σ : Type} (s : σ → Fin 5)
    {g : MvPolynomial σ GeoField} {e : Grade} (hg : g ∈ piece s e)
    (a : MvPolynomial σ GeoField) (t : Grade) :
    weightedHomogeneousComponent (slotWeight s) (t + e) (a * g) =
      weightedHomogeneousComponent (slotWeight s) t a * g := by
  induction a using MvPolynomial.induction_on' with
  | monomial b r =>
    have hb := isWeightedHomogeneous_monomial (slotWeight s) b r rfl
    have hg' : g.IsWeightedHomogeneous (slotWeight s) e := hg
    simp only [weightedHomogeneousComponent_of_mem (hb.mul hg'),
      weightedHomogeneousComponent_of_mem hb, add_right_cancel_iff]
    split <;> simp_all
  | add a b ha hb => simp [add_mul, ha, hb]
private theorem homogeneous_colon {σ : Type} (s : σ → Fin 5)
    {J : Ideal (MvPolynomial σ GeoField)} (hJ : J.IsHomogeneous (piece s))
    {g : MvPolynomial σ GeoField} {e : Grade} (hg : g ∈ piece s e) :
    (J.colon {g}).IsHomogeneous (piece s) := by
  intro t a ha
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at ha ⊢
  have hp : (DirectSum.decompose (piece s) a t : MvPolynomial σ GeoField) =
      weightedHomogeneousComponent (slotWeight s) t a :=
    weightedDecomposition.decompose'_apply GeoField (slotWeight s) a t
  rw [hp, ← component_mul_of_grade s hg a t]
  exact weightedHomogeneousComponent_mem_of_mem _ _ hJ ha _
theorem gradedIdeal_colon {B : Boxes} {P Q : Ideal GeoJets5} {g : SlotRing B}
    {e : Grade} (hg : g ∈ piece (slot B) e)
    (h : ∀ a : GeoJets5, a * taggedMap B g ∈ P ↔ a ∈ Q) :
    (gradedIdeal B P).colon {g} = gradedIdeal B Q := by
  ext a
  rw [mem_iff_weightedHomogeneousComponent_mem _ _
      (homogeneous_colon (slot B) (gradedIdeal_homogeneous B P) hg),
    mem_iff_weightedHomogeneousComponent_mem _ _ (gradedIdeal_homogeneous B Q)]
  apply forall_congr'
  intro t
  let z := weightedHomogeneousComponent (slotWeight (slot B)) t a
  have hz : z ∈ piece (slot B) t := weightedHomogeneousComponent_mem _ _ _
  have hg' : g.IsWeightedHomogeneous (slotWeight (slot B)) e := hg
  have hzg : z * g ∈ piece (slot B) (t + e) :=
    (weightedHomogeneousComponent_isWeightedHomogeneous t a).mul hg'
  change z ∈ (gradedIdeal B P).colon {g} ↔ z ∈ gradedIdeal B Q
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_gradedIdeal_of_grade hzg,
    mem_gradedIdeal_of_grade hz, map_mul, h]
theorem allowed_scaled {a : Shape × ℕ} {m : Exponent} (h : Allowed a m) :
    m ∈ latticePoints a := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  change Allowed (a.1.scale 2, 2 * a.2) m
  simp only [Allowed, Shape.scale]
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem allowed_add_scaled {a : Shape × ℕ} {m n : Exponent}
    (hm : Allowed a m) (hn : Allowed a n) : m + n ∈ latticePoints a := by
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := hm
  obtain ⟨hn₁, hn₂, hn₃, hn₄⟩ := hn
  change Allowed (a.1.scale 2, 2 * a.2) (m + n)
  simp only [Allowed, Shape.scale, Finsupp.add_apply, Nat.mul_add, Finset.sum_add_distrib]
  exact ⟨by omega, by omega, by omega, by omega⟩
private theorem exists_slot_lift (B : Boxes) (i : Fin 5) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ latticePoints (B i)) :
    ∃ g : SlotRing B, g ∈ piece (slot B) (unitGrade i) ∧ taggedMap B g = D := by
  classical
  let gen (m : D.support) : Generator B := ⟨i, ⟨m, hD m m.property⟩⟩
  refine ⟨∑ m : D.support, C (D.coeff m) * MvPolynomial.X (gen m), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro m _
    have hc : (C (D.coeff m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) 0 :=
      isWeightedHomogeneous_C _ _
    have hx : (MvPolynomial.X (gen m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) (unitGrade i) :=
      isWeightedHomogeneous_X GeoField (slotWeight (slot B)) (gen m)
    rw [mem_weightedHomogeneousSubmodule]
    simpa only [zero_add] using hc.mul hx
  · simp only [map_sum, map_mul, taggedMap, aeval_C, algebraMap_eq, aeval_X,
      C_mul_monomial, mul_one, gen]
    rw [Finset.sum_coe_sort D.support (fun m => monomial m (D.coeff m))]
    exact D.support_sum_monomial_coeff
private theorem regular_colon {P : Ideal GeoJets5} {D : GeoJets5}
    (h : IsLeftRegular (Ideal.Quotient.mk P D)) (a : GeoJets5) :
    a * D ∈ P ↔ a ∈ P := by
  constructor
  · intro ha
    rw [← Ideal.Quotient.eq_zero_iff_mem] at ha ⊢
    apply h
    change Ideal.Quotient.mk P D * Ideal.Quotient.mk P a = Ideal.Quotient.mk P D * 0
    rw [mul_zero, mul_comm, ← map_mul, ha]
  · exact P.mul_mem_right D
private theorem square_colon {P : Ideal GeoJets5} {D : GeoJets5}
    (h : IsLeftRegular (Ideal.Quotient.mk P D)) (a : GeoJets5) :
    a * D ∈ sectionIdeal P (D ^ 2) ↔ a ∈ sectionIdeal P D := by
  constructor
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy
    have he : (a - c * D) * D = x := by
      rw [sub_mul, ← hxy, ← hc]
      ring
    have hm : a - c * D ∈ P := (regular_colon h _).mp (by rw [he]; exact hx)
    exact Submodule.mem_sup.mpr
      ⟨a - c * D, hm, c * D, Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩, sub_add_cancel _ _⟩
  · intro ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact Submodule.mem_sup.mpr ⟨x * D, P.mul_mem_right D hx, c * D * D,
      Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩, by rw [← add_mul, hxy]⟩
theorem exists_regular_lifts (B : Boxes) (P : Ideal GeoJets5) (i : Fin 5) (D : GeoJets5)
    (hD : Box5 (B i).1 (B i).2 D) (hr : IsLeftRegular (Ideal.Quotient.mk P D)) :
    ∃ f g : SlotRing B,
      f ∈ piece (slot B) (unitGrade i) ∧ g ∈ piece (slot B) (unitGrade i) ∧
      (gradedIdeal B P).colon {f} = gradedIdeal B P ∧
      gradedIdeal B P ⊔ Ideal.span {f} ≤ gradedIdeal B (sectionIdeal P (D ^ 2)) ∧
      (gradedIdeal B (sectionIdeal P (D ^ 2))).colon {g} = gradedIdeal B (sectionIdeal P D) ∧
      gradedIdeal B (sectionIdeal P (D ^ 2)) ⊔ Ideal.span {g} ≤ gradedIdeal B (sectionIdeal P D) := by
  classical
  have hs (m : Exponent) (hm : m ∈ D.support) : Allowed (B i) m :=
    ⟨(hD.1 m hm).1, (hD.1 m hm).2.1, (hD.1 m hm).2.2, hD.2 m hm⟩
  have hs₂ (m : Exponent) (hm : m ∈ (D ^ 2).support) : m ∈ latticePoints (B i) := by
    rw [pow_two] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul D D hm)
    exact allowed_add_scaled (hs a ha) (hs b hb)
  obtain ⟨f, hf, hfmap⟩ := exists_slot_lift B i (D ^ 2) hs₂
  obtain ⟨g, hg, hgmap⟩ := exists_slot_lift B i D (fun m hm => allowed_scaled (hs m hm))
  refine ⟨f, g, hf, hg, ?_, ?_, ?_, ?_⟩
  · apply gradedIdeal_colon hf
    intro a
    rw [hfmap]
    have h : IsLeftRegular (Ideal.Quotient.mk P (D ^ 2)) := by
      rw [map_pow]
      exact IsLeftRegular.pow 2 hr
    exact regular_colon h a
  · refine sup_le (gradedIdeal_mono B le_sup_left) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    rw [mem_gradedIdeal_of_grade hf, hfmap]
    exact (le_sup_right : Ideal.span {D ^ 2} ≤ sectionIdeal P (D ^ 2))
      (Ideal.mem_span_singleton_self _)
  · apply gradedIdeal_colon hg
    intro a
    rw [hgmap]
    exact square_colon hr a
  · refine sup_le (gradedIdeal_mono B (sup_le le_sup_left ?_))
      ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mem_span_singleton'.mpr ⟨D, (pow_two D).symm⟩)).trans le_sup_right
    · rw [mem_gradedIdeal_of_grade hg, hgmap]
      exact (le_sup_right : Ideal.span {D} ≤ sectionIdeal P D) (Ideal.mem_span_singleton_self _)
end
end K1_13_6_2_4_1
end
section
namespace K1_13_6_2_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators Pointwise
theorem zero_mem_latticePoints (a : Shape × ℕ) : 0 ∈ latticePoints a := by
  simp [latticePoints, Allowed]
theorem zero_mem_diagonalExponents (B : Boxes) (t : Fin 5 → ℕ) :
    0 ∈ diagonalExponents B t :=
  ⟨fun _ _ => 0, fun i _ => zero_mem_latticePoints (B i), by simp⟩
theorem nsmul_monomial_preimage {S : Set Exponent} {n : ℕ} {m : Exponent}
    (hm : m ∈ n • S) :
    ∃ P : MvPolynomial S GeoField,
      P.totalDegree ≤ n ∧ monomialMap GeoField S P = monomial m 1 := by
  induction n generalizing m with
  | zero =>
    rw [zero_smul, Set.mem_zero] at hm
    subst m
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul'] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := hm
    obtain ⟨P, hdeg, hP⟩ := ih hb
    refine ⟨MvPolynomial.X ⟨a, ha⟩ * P, ?_, ?_⟩
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_X]; omega)
    · rw [map_mul, monomialMap_X, hP, monomial_mul_monomial, one_mul]
theorem monomial_hilbert_count (S : Set Exponent) (h0 : 0 ∈ S) (n : ℕ) :
    affineHilbertFunction (Ideal.comap (monomialMap GeoField S) ⊥) n = (n • S).ncard := by
  classical
  let φ := monomialMap GeoField S
  let j := Ideal.kerLiftAlg φ
  let V := quotientDegreeLE (RingHom.ker φ) n
  have hmap : V.map j.toLinearMap = restrictSupport GeoField (n • S) := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hv
      exact monomialMap_mem_restrictSupport_nsmul h0 hP
    · rw [restrictSupport_eq_span, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨P, hP, hφ⟩ := nsmul_monomial_preimage hm
      exact ⟨_, mk_mem_quotientDegreeLE hP, hφ⟩
  rw [← RingHom.ker_eq_comap_bot]
  change Module.finrank GeoField V = _
  calc
    _ = Module.finrank GeoField (V.map j.toLinearMap) :=
      (Submodule.equivMapOfInjective _ (Ideal.kerLiftAlg_injective φ) V).finrank_eq
    _ = _ := by
      rw [hmap, Module.finrank_eq_nat_card_basis (basisRestrictSupport GeoField _),
        Nat.card_coe_set_eq]
private def exponentEquiv : Exponent ≃ (Fin 4 →₀ ℕ) × ℕ :=
  Finsupp.equivFunOnFinite.trans
    ((Fin.snocEquiv (fun _ : Fin 5 => ℕ)).symm.trans
      ((Equiv.prodComm ℕ (Fin 4 → ℕ)).trans
        (Equiv.prodCongr Finsupp.equivFunOnFinite.symm (Equiv.refl ℕ))))
theorem lattice_count (a : Shape × ℕ) :
    (latticePoints a).ncard = (K1_13_6_2_3.capExponents a.1).ncard * (2 * a.2 + 1) := by
  classical
  let e : latticePoints a ≃ K1_13_6_2_3.capExponents a.1 × Fin (2 * a.2 + 1) :=
    { toFun := fun m => ⟨⟨(exponentEquiv m).1, by
        simpa [exponentEquiv, K1_13_6_2_3.capExponents, Finsupp.degree_eq_sum, Fin.init,
          Shape.scale]
          using And.intro m.property.1 (And.intro m.property.2.1 m.property.2.2.1)⟩,
        ⟨(exponentEquiv m).2, Nat.lt_succ_of_le m.property.2.2.2⟩⟩
      invFun := fun x => ⟨exponentEquiv.symm (x.1, x.2), by
        have hx := x.1.property
        change (x.1.val.degree ≤ _) ∧ _ at hx
        simp only [Finsupp.degree_eq_sum] at hx
        change (∑ i : Fin 4, Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) i.castSucc) ≤ 2 * a.1.b ∧
          (∑ i : Fin 4, i.val * Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) i.castSucc) ≤ 2 * a.1.j ∧
          Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) (Fin.castSucc (3 : Fin 4)) ≤ 2 * a.1.t ∧
          Fin.snoc (α := fun _ => ℕ) x.1.val (x.2 : ℕ) (Fin.last 4) ≤ 2 * a.2
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
          And.intro hx.1 (And.intro hx.2.1 (And.intro hx.2.2 (Nat.le_of_lt_succ x.2.isLt)))⟩
      left_inv := fun m => Subtype.ext (exponentEquiv.symm_apply_apply m)
      right_inv := fun x => Prod.ext
        (Subtype.ext (congrArg Prod.fst (exponentEquiv.apply_symm_apply (x.1, (x.2 : ℕ)))))
        (Fin.ext (congrArg Prod.snd (exponentEquiv.apply_symm_apply (x.1, (x.2 : ℕ))))) }
  simpa only [Nat.card_coe_set_eq, Nat.card_prod, Nat.card_fin] using Nat.card_congr e
end
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3
open scoped BigOperators
def sumShape {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ) : Shape :=
  ⟨∑ i, w i * (boxes i).b, ∑ i, w i * (boxes i).j, ∑ i, w i * (boxes i).t⟩
def capPiece (P : Ideal GeoJets) (p : Shape) : Submodule GeoField (GeoJets ⧸ P) :=
  (MvPolynomial.restrictSupport GeoField (capExponents p)).map
    (Ideal.Quotient.mkₐ GeoField P).toLinearMap
def standardCount {k m : ℕ} (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (w : Fin k → ℕ) : ℕ :=
  {e : Fin m →₀ ℕ | (∀ b ∈ bad, ¬ b ≤ e) ∧
    ∀ i, ∑ j ∈ Finset.univ.filter (fun j => slot j = i), e j = w i}.ncard
end
end K1_13_6_2_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_1 MvPolynomial Polynomial Filter
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ (P : Ideal GeoJets) (k : ℕ) (boxes : Fin k → Shape),
    P.IsPrime → (∀ i, ChamberBox (boxes i)) →
    ∃ (m : ℕ) (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ)),
      ∀ w, Module.finrank GeoField (capPiece P (sumShape boxes w)) = standardCount slot bad w
def c2 : Prop :=
  ∀ (k m : ℕ) (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ)),
    ∃ (T r : ℕ) (f : Fin r → Fin k → ℕ → ℚ),
      (∀ a i, Monotone (f a i)) ∧ (∀ a i n, 0 ≤ f a i n) ∧
      ∀ (w : Fin k → ℕ), (∀ i, T ≤ w i) →
        (standardCount slot bad w : ℚ) = ∑ a, ∏ i, f a i (w i)
private def shift {k : ℕ} (w : Fin k → ℕ) (i : Fin k) (n : ℕ) : Fin k → ℕ :=
  Function.update w i (w i + n)
private def diff {k : ℕ} (F : (Fin k → ℕ) → ℚ) (dirs : List (Fin k)) (n : ℕ)
    (w : Fin k → ℕ) : ℚ :=
  match dirs with
  | [] => F w
  | i :: rest => diff F rest n (shift w i n) - diff F rest n w
private theorem le_shift {k : ℕ} (w : Fin k → ℕ) (i : Fin k) (n : ℕ) (j : Fin k) :
    w j ≤ shift w i n j := by
  by_cases h : j = i
  · subst j
    simp [shift]
  · simp [shift, Function.update_of_ne h]
theorem diff_congr {k : ℕ} {F G : (Fin k → ℕ) → ℚ} {T : ℕ}
    (h : ∀ w, (∀ i, T ≤ w i) → F w = G w)
    (dirs : List (Fin k)) (n : ℕ) (w : Fin k → ℕ) (hw : ∀ i, T ≤ w i) :
    diff F dirs n w = diff G dirs n w := by
  induction dirs generalizing w with
  | nil => exact h w hw
  | cons i rest ih =>
    rw [diff, diff, ih w hw, ih (shift w i n) (fun j => (hw j).trans (le_shift w i n j))]
theorem diff_sum {k r : ℕ} (F : Fin r → (Fin k → ℕ) → ℚ)
    (dirs : List (Fin k)) (n : ℕ) (w : Fin k → ℕ) :
    diff (fun v => ∑ a, F a v) dirs n w = ∑ a, diff (F a) dirs n w := by
  induction dirs generalizing w with
  | nil => rfl
  | cons i rest ih =>
    simp only [diff, ih, Finset.sum_sub_distrib]
theorem diff_prod {k : ℕ} (f : Fin k → ℕ → ℚ) (dirs : List (Fin k))
    (hd : dirs.Nodup) (n : ℕ) (w : Fin k → ℕ) :
    diff (fun v => ∏ i, f i (v i)) dirs n w =
      ∏ i, if i ∈ dirs then f i (w i + n) - f i (w i) else f i (w i) := by
  induction dirs generalizing w with
  | nil => simp [diff]
  | cons i rest ih =>
    obtain ⟨hi, hr⟩ := List.nodup_cons.mp hd
    simp only [diff, ih hr]
    let g (v : Fin k → ℕ) (j : Fin k) :=
      if j ∈ rest then f j (v j + n) - f j (v j) else f j (v j)
    let s := (Finset.univ : Finset (Fin k)).erase i
    have hs : ∏ j ∈ s, g (shift w i n) j = ∏ j ∈ s, g w j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [g, shift, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    let h (j : Fin k) :=
      if j ∈ i :: rest then f j (w j + n) - f j (w j) else f j (w j)
    have hh : ∏ j ∈ s, h j = ∏ j ∈ s, g w j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [h, g, Finset.ne_of_mem_erase hj]
    change (∏ j, g (shift w i n) j) - (∏ j, g w j) = ∏ j, h j
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    change g (shift w i n) i * (∏ j ∈ s, g (shift w i n) j) -
      g w i * (∏ j ∈ s, g w j) = h i * (∏ j ∈ s, h j)
    rw [hs, hh, ← sub_mul]
    simp [g, h, shift, hi]
theorem standard_diff_nonneg (h : c2) {k m : ℕ}
    (slot : Fin m → Fin k) (bad : Finset (Fin m →₀ ℕ))
    (dirs : List (Fin k)) (hd : dirs.Nodup) :
    ∃ T : ℕ, ∀ n (w : Fin k → ℕ), (∀ i, T ≤ w i) →
      0 ≤ diff (fun v => (standardCount slot bad v : ℚ)) dirs n w := by
  obtain ⟨T, r, f, hmono, hnonneg, hcount⟩ := h k m slot bad
  refine ⟨T, fun n w hw => ?_⟩
  rw [diff_congr hcount dirs n w hw, diff_sum]
  apply Finset.sum_nonneg
  intro a _
  rw [diff_prod (f a) dirs hd n w]
  apply Finset.prod_nonneg
  intro i _
  split
  · exact sub_nonneg.mpr (hmono a i (Nat.le_add_right _ _))
  · exact hnonneg a i (w i)
private abbrev capMap (p : Shape) := monomialMap GeoField (capExponents p)
private abbrev capIdeal (P : Ideal GeoJets) (p : Shape) := P.comap (capMap p).toRingHom
private lemma cap_dimension (P : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) :
    (affineHilbertPolynomial (capIdeal P p)).natDegree = dimension P := by
  have hsurj : Function.Surjective (capMap p) := by
    apply monomialMap_surjective
    obtain ⟨hb, hj, ht⟩ := hp
    intro i
    fin_cases i <;> norm_num [cap_coords, Finsupp.single_apply] <;> omega
  exact natDegree_affineHilbertPolynomial_comap_of_surjective (capMap p) hsurj P
private lemma monomial_preimage (S : Set (Fin 4 →₀ ℕ)) (n : ℕ) (e : Fin 4 →₀ ℕ)
    (he : e ∈ n • S) :
    ∃ f : MvPolynomial S GeoField, f.totalDegree ≤ n ∧ monomialMap GeoField S f = monomial e 1 := by
  induction n generalizing e with
  | zero =>
    rw [zero_smul, Set.mem_zero] at he
    subst e
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at he
    obtain ⟨a, ha, b, hb, rfl⟩ := he
    obtain ⟨f, hn, hf⟩ := ih a ha
    refine ⟨f * MvPolynomial.X ⟨b, hb⟩, (totalDegree_mul _ _).trans ?_, ?_⟩
    · simpa only [totalDegree_X] using Nat.add_le_add_right hn 1
    · rw [map_mul, hf, monomialMap_X, MvPolynomial.monomial_mul_monomial, mul_one]
theorem capPiece_scale (P : Ideal GeoJets) {p : Shape} (hp : ChamberBox p) (n : ℕ) :
    Module.finrank GeoField (capPiece P (p.scale n)) = affineHilbertFunction (capIdeal P p) n := by
  let I := capIdeal P p
  let g := Ideal.quotientMapₐ P (capMap p) (le_rfl : I ≤ capIdeal P p)
  have hg : Function.Injective g := Ideal.quotientMap_injective
  let V := quotientDegreeLE I n
  have hmap : V.map g.toLinearMap = capPiece P (p.scale n) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨f, hf, rfl⟩ := mem_quotientDegreeLE.mp hx
      change Ideal.Quotient.mk P (capMap p f) ∈ capPiece P (p.scale n)
      refine ⟨capMap p f, ?_, rfl⟩
      rw [← nsmul_cap p hp n]
      exact monomialMap_mem_restrictSupport_nsmul (zero_mem_cap p) hf
    · unfold capPiece
      rw [Submodule.map_le_iff_le_comap, restrictSupport_eq_span, Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      rw [← nsmul_cap p hp n] at he
      obtain ⟨f, hf, hφ⟩ := monomial_preimage _ n e he
      have hmk : Ideal.Quotient.mk I f ∈ V := mk_mem_quotientDegreeLE hf
      exact ⟨Ideal.Quotient.mk I f, hmk, by
        change Ideal.Quotient.mk P (capMap p f) = Ideal.Quotient.mk P (monomial e 1)
        rw [hφ]⟩
  rw [← hmap]
  exact (Submodule.equivMapOfInjective _ hg V).finrank_eq.symm
lemma capPiece_mono (P : Ideal GeoJets) {p q : Shape} (h : InBox p q) :
    Module.finrank GeoField (capPiece P p) ≤ Module.finrank GeoField (capPiece P q) := by
  have := restrictSupport_finite (R := GeoField) (Set.toFinite (capExponents q))
  have : Module.Finite GeoField (capPiece P q) := by unfold capPiece; infer_instance
  apply Submodule.finrank_mono
  apply Submodule.map_mono
  apply restrictSupport_mono
  intro e he
  exact ⟨he.1.trans (Nat.mul_le_mul_left 2 h.1),
    he.2.1.trans (Nat.mul_le_mul_left 2 h.2.1), he.2.2.trans (Nat.mul_le_mul_left 2 h.2.2)⟩
private lemma sumShape_chamber {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ)
    (hb : ∀ i, ChamberBox (boxes i)) (hw : ∃ i, 0 < w i) : ChamberBox (sumShape boxes w) := by
  obtain ⟨i, hi⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · change (∑ j, w j * (boxes j).j) ≤ ∑ j, w j * (boxes j).b
    exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left (w j) (hb j).1)
  · change 3 * (∑ j, w j * (boxes j).t) ≤ ∑ j, w j * (boxes j).j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ (hb j).2.1
  · change 0 < ∑ j, w j * (boxes j).t
    exact (Nat.mul_pos hi (hb i).2.2).trans_le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (w j * (boxes j).t)) (Finset.mem_univ i))
lemma sumShape_shift {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ) (i : Fin k) :
    sumShape boxes (shift w i 1) = (sumShape boxes w).plus (boxes i) := by
  have h (a : Fin k → ℕ) :
      (∑ j, shift w i 1 j * a j) = (∑ j, w j * a j) + a i := by
    calc
      _ = ∑ j, (w j * a j + if j = i then a i else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp [shift, Nat.add_mul]
        · simp [shift, hj]
      _ = _ := by simp [Finset.sum_add_distrib]
  simp only [sumShape, Shape.plus, h]
lemma sumShape_ray {k : ℕ} (boxes : Fin k → Shape) (w : Fin k → ℕ) (N T : ℕ) :
    sumShape boxes (fun i => N * w i + T) =
      ((sumShape boxes w).scale N).plus (sumShape boxes (fun _ => T)) := by
  simp only [sumShape, Shape.scale, Shape.plus, Nat.add_mul, Finset.sum_add_distrib,
    Nat.mul_assoc, Finset.mul_sum]
lemma cast_ray_shift {k : ℕ} (w : Fin k → ℕ) (i : Fin k) (N T : ℕ) :
    shift (fun j => N * w j + T) i N = fun j => N * shift w i 1 j + T := by
  funext j
  by_cases h : j = i
  · subst j
    simp [shift, Nat.mul_add, Nat.add_right_comm]
  · simp [shift, Function.update_of_ne h]
lemma capPiece_ray_bounds {k : ℕ} (P : Ideal GeoJets) (boxes : Fin k → Shape)
    (w : Fin k → ℕ) (hp : ChamberBox (sumShape boxes w)) (T : ℕ) :
    ∃ C : ℕ, ∀ N,
      affineHilbertFunction (capIdeal P (sumShape boxes w)) N ≤
        Module.finrank GeoField (capPiece P (sumShape boxes (fun i => N * w i + T))) ∧
      Module.finrank GeoField (capPiece P (sumShape boxes (fun i => N * w i + T))) ≤
        affineHilbertFunction (capIdeal P (sumShape boxes w)) (N + C) := by
  let p := sumShape boxes w
  let q := sumShape boxes (fun _ => T)
  let C := q.b + q.j + q.t
  have hbox : InBox q (p.scale C) := by
    obtain ⟨hb, hj, ht⟩ := hp
    have hj' : 0 < p.j := by change 3 * p.t ≤ p.j at hj; change 0 < p.t at ht; omega
    have hb' : 0 < p.b := hj'.trans_le hb
    exact ⟨(show q.b ≤ C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right _ hb'),
      (show q.j ≤ C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right _ hj'),
      (show q.t ≤ C by dsimp [C]; omega).trans (Nat.le_mul_of_pos_right _ ht)⟩
  refine ⟨C, fun N => ?_⟩
  rw [← capPiece_scale P hp N, ← capPiece_scale P hp (N + C), sumShape_ray]
  constructor
  · exact capPiece_mono P ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · apply capPiece_mono P
    obtain ⟨hb, hj, ht⟩ := hbox
    exact ⟨by simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hb (N * p.b),
      by simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hj (N * p.j),
      by simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left ht (N * p.t)⟩
theorem diff_bounds {k : ℕ} (P : Ideal GeoJets) (boxes : Fin k → Shape)
    (hb : ∀ i, ChamberBox (boxes i)) (d T : ℕ) (hd : dimension P ≤ d)
    (dirs : List (Fin k)) (w : Fin k → ℕ) (hw : ∃ i, 0 < w i) :
    ∃ L U : ℚ[X], L.natDegree ≤ d ∧ U.natDegree ≤ d ∧
      L.coeff d = diff (fun v => capCoeff P d (sumShape boxes v)) dirs 1 w ∧
      U.coeff d = diff (fun v => capCoeff P d (sumShape boxes v)) dirs 1 w ∧
      ∀ᶠ N : ℕ in atTop,
        L.eval (N : ℚ) ≤ diff (fun v => (Module.finrank GeoField (capPiece P (sumShape boxes v)) : ℚ))
          dirs N (fun i => N * w i + T) ∧
        diff (fun v => (Module.finrank GeoField (capPiece P (sumShape boxes v)) : ℚ))
          dirs N (fun i => N * w i + T) ≤ U.eval (N : ℚ) := by
  induction dirs generalizing w with
  | nil =>
    let p := sumShape boxes w
    let I := capIdeal P p
    let L := affineHilbertPolynomial I
    have hp := sumShape_chamber boxes w hb hw
    have hL : L.natDegree ≤ d := (cap_dimension P hp).trans_le hd
    obtain ⟨C, hC⟩ := capPiece_ray_bounds P boxes w hp T
    refine ⟨L, taylor (C : ℚ) L, hL, (natDegree_taylor _ _).trans_le hL, rfl,
      coeff_taylor_of_natDegree_le _ hL, ?_⟩
    obtain ⟨N₀, hN₀⟩ := exists_eval_affineHilbertPolynomial I
    filter_upwards [eventually_ge_atTop N₀] with N hN
    change (affineHilbertPolynomial I).eval (N : ℚ) ≤ _ ∧
      _ ≤ (taylor (C : ℚ) (affineHilbertPolynomial I)).eval (N : ℚ)
    rw [taylor_eval, ← Nat.cast_add, hN₀ N hN, hN₀ (N + C) (hN.trans (Nat.le_add_right _ _))]
    simp only [diff]
    exact ⟨by exact_mod_cast (hC N).1, by exact_mod_cast (hC N).2⟩
  | cons i dirs ih =>
    have hwi : ∃ j, 0 < shift w i 1 j := by
      obtain ⟨j, hj⟩ := hw
      exact ⟨j, hj.trans_le (le_shift w i 1 j)⟩
    obtain ⟨L₁, U₁, hL₁, hU₁, hcL₁, hcU₁, he₁⟩ := ih (shift w i 1) hwi
    obtain ⟨L₀, U₀, hL₀, hU₀, hcL₀, hcU₀, he₀⟩ := ih w hw
    refine ⟨L₁ - U₀, U₁ - L₀, (natDegree_sub_le _ _).trans (max_le hL₁ hU₀),
      (natDegree_sub_le _ _).trans (max_le hU₁ hL₀), ?_, ?_, ?_⟩
    · rw [Polynomial.coeff_sub, hcL₁, hcU₀, diff]
    · rw [Polynomial.coeff_sub, hcU₁, hcL₀, diff]
    · filter_upwards [he₁, he₀] with N a b
      simp only [diff, cast_ray_shift, Polynomial.eval_sub]
      exact ⟨sub_le_sub a.1 b.2, sub_le_sub a.2 b.1⟩
lemma diff_polarize {k : ℕ} (boxes : Fin k → Shape) (H : Shape → ℚ)
    (dirs : List (Fin k)) (w : Fin k → ℕ) :
    diff (fun v => H (sumShape boxes v)) dirs 1 w =
      polarize H (dirs.map boxes) (sumShape boxes w) := by
  induction dirs generalizing w with
  | nil => rfl
  | cons i rest ih =>
    simp only [diff, ih, List.map_cons, polarize, sumShape_shift]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2_3_3.c2 := by
  intro P boxes hp hb hd _
  let p : Shape := ⟨3, 3, 1⟩
  let B : Fin (boxes.length + 1) → Shape := Fin.cons p boxes.get
  let dirs : List (Fin (boxes.length + 1)) := List.ofFn (fun i : Fin boxes.length => i.succ)
  let w : Fin (boxes.length + 1) → ℕ := Pi.single 0 1
  have hB (i : Fin (boxes.length + 1)) : ChamberBox (B i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change ChamberBox p
      exact ⟨by decide, by decide, by decide⟩
    · exact hb _ (List.get_mem _ _)
  have hdirs : dirs.Nodup := List.nodup_ofFn_ofInjective (Fin.succ_injective _)
  have hmap : dirs.map B = boxes := by
    rw [List.map_ofFn]
    exact List.ofFn_get boxes
  have hw : ∃ i, 0 < w i := ⟨0, by simp [w]⟩
  have hbase : sumShape B w = p := by
    simp [sumShape, w, Pi.single_apply, Finset.sum_ite_eq', B]
  obtain ⟨m, slot, bad, hcount⟩ := h1 P _ B hp hB
  obtain ⟨T, hpos⟩ := standard_diff_nonneg h2 slot bad dirs hdirs
  obtain ⟨_, U, _, hU, _, hc, hu⟩ := diff_bounds P B hB boxes.length T hd.le dirs w hw
  have hnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ U.eval (N : ℚ) := by
    filter_upwards [hu] with N hN
    refine le_trans ?_ hN.2
    rw [diff_congr (T := 0) (fun v _ => by rw [hcount]) dirs N _ (fun _ => Nat.zero_le _)]
    exact hpos N _ (fun _ => Nat.le_add_left _ _)
  have hcoeff := coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg hU hnonneg
  rw [hc, diff_polarize, hmap, hbase] at hcoeff
  exact div_nonneg hcoeff (by positivity)
end
end K1_13_6_2_3_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_2
open K1_13 K1_13_6_2_3 K1_13_6_2_3_1 K1_13_6_2_3_2
open scoped BigOperators Pointwise
private theorem slot_degree_ne_zero {ι : Type} [DecidableEq ι] (shapes : ι → Shape)
    (e : CapVar shapes →₀ ℕ) (i : ι) :
    Finsupp.weight (step ∘ capSlot shapes) e i ≠ 0 ↔
      ∃ v : CapVar shapes, v.1 = i ∧ e v ≠ 0 := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Function.comp_apply,
    capSlot, step, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Nat.cast_id]
  rw [← Nat.pos_iff_ne_zero, Finset.sum_pos_iff]
  constructor
  · rintro ⟨v, _, hv⟩
    by_cases hvi : v.1 = i
    · exact ⟨v, hvi, Nat.ne_of_gt (by simpa [hvi] using hv)⟩
    · rw [Pi.single_eq_of_ne (Ne.symm hvi)] at hv
      simp at hv
  · rintro ⟨v, hvi, hv⟩
    exact ⟨v, Finsupp.mem_support_iff.mpr hv, by simpa [hvi] using Nat.pos_of_ne_zero hv⟩
private theorem productExponents_zero {ι : Type} [DecidableEq ι] (shapes : ι → Shape) :
    productExponents shapes 0 = 0 := by
  ext m
  simp only [Set.mem_zero, productExponents, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, hdeg, hexp⟩
    have he : e = 0 := by
      ext v
      rw [Finsupp.zero_apply]
      by_contra hv
      have hslot := (slot_degree_ne_zero shapes e v.1).mpr ⟨v, rfl, hv⟩
      simp [hdeg] at hslot
    simpa [he] using hexp.symm
  · rintro rfl
    exact ⟨0, map_zero _, map_zero _⟩
private theorem productExponents_add_step {ι : Type} [DecidableEq ι] (shapes : ι → Shape)
    (a : ι → ℕ) (i : ι) :
    productExponents shapes (a + step i) =
      productExponents shapes a + capExponents (shapes i) := by
  ext m
  constructor
  · rintro ⟨e, hdeg, hexp⟩
    have hne : Finsupp.weight (step ∘ capSlot shapes) e i ≠ 0 := by
      simp [hdeg, step]
    obtain ⟨v, hvi, hv⟩ := (slot_degree_ne_zero shapes e i).mp hne
    let e' := e - Finsupp.single v 1
    have hdeg' : Finsupp.weight (step ∘ capSlot shapes) e' + step i = a + step i := by
      have h := Finsupp.weight_sub_single_add (w := step ∘ capSlot shapes) hv
      calc
        _ = Finsupp.weight (step ∘ capSlot shapes) e := by
          simpa only [e', Function.comp_apply, capSlot, hvi] using h
        _ = _ := hdeg
    refine ⟨Finsupp.weight (fun u : CapVar shapes => u.2.val) e',
      ⟨e', add_right_cancel hdeg', rfl⟩, v.2.val, ?_, ?_⟩
    · simpa only [hvi] using v.2.property
    · exact (Finsupp.weight_sub_single_add hv).trans hexp
  · rintro ⟨m', ⟨e, hdeg, hexp⟩, w, hw, rfl⟩
    let v : CapVar shapes := ⟨i, ⟨w, hw⟩⟩
    refine ⟨e + Finsupp.single v 1, ?_, ?_⟩
    · rw [map_add, Finsupp.weight_single, one_smul, hdeg] <;> rfl
    · simp only [map_add, Finsupp.weight_single, one_smul, hexp, v]
private theorem capExponents_zero : capExponents ⟨0, 0, 0⟩ = 0 := by
  ext m
  simp only [cap_coords, Set.mem_zero, Nat.mul_zero]
  constructor
  · intro hm
    have h := hm.1
    ext k
    fin_cases k
    · change m 0 = 0; omega
    · change m 1 = 0; omega
    · change m 2 = 0; omega
    · change m 3 = 0; omega
  · rintro rfl
    simp
theorem sum_add_step_mul {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (i : ι) (f : ι → ℕ) :
    (∑ k, (a + step i) k * f k) = (∑ k, a k * f k) + f i := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_eq_single i]
  · simp [step]
  · intro k hki
    simp [step, Pi.single_eq_of_ne hki]
theorem shapeSum_add_step {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape)
    (a : ι → ℕ) (i : ι) :
    shapeSum shapes (a + step i) = (shapeSum shapes a).plus (shapes i) := by
  simp only [shapeSum, Shape.plus, sum_add_step_mul]
theorem exists_nonzero_slot {ι : Type} (a : ι → ℕ) (ha : a ≠ 0) :
    ∃ i, a i ≠ 0 := by
  by_contra! h
  exact ha (funext h)
theorem chamber_shapeSum {ι : Type} [Fintype ι] (shapes : ι → Shape)
    (hsh : ∀ i, ChamberBox (shapes i)) (a : ι → ℕ) (ha : a ≠ 0) :
    ChamberBox (shapeSum shapes a) := by
  refine ⟨Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left (a i) (hsh i).1, ?_, ?_⟩
  · dsimp [shapeSum]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Nat.mul_left_comm 3 (a i)]
    exact Nat.mul_le_mul_left (a i) (hsh i).2.1
  · obtain ⟨i, hi⟩ := exists_nonzero_slot a ha
    exact (Nat.mul_pos (Nat.pos_of_ne_zero hi) (hsh i).2.2).trans_le
      (Finset.single_le_sum (f := fun k => a k * (shapes k).t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
theorem proof : K1_13_6_2_3_2.c2 := by
  intro ι _ _ shapes hsh a
  induction a using WellFounded.induction (measure (fun b : ι → ℕ => ∑ i, b i)).wf with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha, productExponents_zero]
      simpa [shapeSum] using capExponents_zero.symm
    · obtain ⟨i, hi⟩ := exists_nonzero_slot a ha
      let b := a - step i
      have hab : b + step i = a := by
        funext k
        change a k - step i k + step i k = a k
        apply Nat.sub_add_cancel
        by_cases hki : k = i
        · subst k
          simpa [step] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [step, Pi.single_eq_of_ne hki]
      have hsum : (∑ k, a k) = (∑ k, b k) + 1 := by
        rw [← hab]
        simpa only [Nat.mul_one] using sum_add_step_mul b i (fun _ => 1)
      have hlt : (∑ k, b k) < ∑ k, a k := by omega
      rw [← hab, productExponents_add_step, shapeSum_add_step]
      by_cases hb : b = 0
      · rw [hb, productExponents_zero, zero_add]
        cases shapes i
        simp [shapeSum, Shape.plus]
      · rw [ih b hlt, cap_add (chamber_shapeSum shapes hsh b hb) (hsh i)]
end K1_13_6_2_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_5
noncomputable section
open MvPolynomial Filter
open scoped BigOperators
variable {ι : Type}
def ray (P : MvPolynomial ι ℚ) (u v : ι → ℕ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun i => Polynomial.C (v i : ℚ) * Polynomial.X +
    Polynomial.C (u i : ℚ)) P
theorem ray_eval (P : MvPolynomial ι ℚ) (u v : ι → ℕ) (n : ℕ) :
    (ray P u v).eval (n : ℚ) = MvPolynomial.eval (fun i => ((u i + n * v i : ℕ) : ℚ)) P := by
  let φ : Polynomial ℚ →ₐ[ℚ] ℚ := Polynomial.aeval (n : ℚ)
  change φ (ray P u v) = _
  rw [ray, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
  have he : (fun i => φ (Polynomial.C (v i : ℚ) * Polynomial.X +
      Polynomial.C (u i : ℚ))) = (fun i => ((u i + n * v i : ℕ) : ℚ)) := by
    funext i
    simp [φ, Polynomial.aeval_def, mul_comm, add_comm]
  rw [he]
theorem prod_top (f : ι → Polynomial ℚ) (e : ι →₀ ℕ)
    (h : ∀ i, (f i).natDegree ≤ 1) (s : Finset ι) :
    (∏ i ∈ s, f i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
    (∏ i ∈ s, f i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (f i).coeff 1 ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have hpow : ((f i) ^ e i).natDegree ≤ e i := by
      simpa using Polynomial.natDegree_pow_le_of_le (e i) (h i)
    refine ⟨(Polynomial.natDegree_mul_le).trans (Nat.add_le_add hpow ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpow ih.1, ih.2]
    rw [show (f i ^ e i).coeff (e i) = (f i).coeff 1 ^ e i by
      simpa only [mul_one] using Polynomial.coeff_pow_of_natDegree_le (m := e i) (h i)]
theorem affine_top (f : ι → Polynomial ℚ) (h : ∀ i, (f i).natDegree ≤ 1)
    (P : MvPolynomial ι ℚ) (d : ℕ) (hd : P.totalDegree ≤ d) :
    (MvPolynomial.aeval f P).coeff d =
      MvPolynomial.eval (fun i => (f i).coeff 1) (homogeneousComponent d P) := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff]
  rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hle : e.degree ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  rw [MvPolynomial.aeval_monomial, ← Polynomial.C_eq_algebraMap, Polynomial.coeff_C_mul]
  by_cases hEq : e.degree = d
  · rw [ite_eq_left hEq, ← hEq, Finsupp.degree_apply, MvPolynomial.eval_monomial]
    congr 1
    exact (prod_top f e h e.support).2
  · rw [ite_eq_right hEq, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    exact (prod_top f e h e.support).1.trans_lt (lt_of_le_of_ne hle hEq)
theorem ray_top (P : MvPolynomial ι ℚ) (u v : ι → ℕ) {d : ℕ} (hd : P.totalDegree ≤ d) :
    (ray P u v).coeff d = MvPolynomial.eval (fun i => (v i : ℚ)) (homogeneousComponent d P) := by
  unfold ray
  rw [affine_top _ (fun i => ?_) P d hd]
  · simp [Polynomial.coeff_add]
  · apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (by simpa using Polynomial.natDegree_C_mul_X_pow_le (v i : ℚ) 1) (by simp)
theorem totalDegree_le_of_ray_degree (P : MvPolynomial ι ℚ) (u : ι → ℕ) (d : ℕ)
    (h : ∀ v : ι → ℕ, (∀ i, 0 < v i) → (ray P u v).natDegree ≤ d) :
    P.totalDegree ≤ d := by
  classical
  by_contra! hd
  let f (n : ℕ) : ℚ := ((n + 1 : ℕ) : ℚ)
  have hf : Function.Injective f := by
    intro m n hmn
    change ((m + 1 : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) at hmn
    have hmn' : m + 1 = n + 1 := by exact_mod_cast hmn
    omega
  have hvanish : homogeneousComponent P.totalDegree P = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range f)
      (fun _ => Set.infinite_range_of_injective hf)
    intro x hx
    choose w hw using fun i : ι => hx i (Set.mem_univ i)
    let v : ι → ℕ := fun i => w i + 1
    have hv : (fun i => (v i : ℚ)) = x := _root_.funext hw
    rw [← hv, ← ray_top P u v le_rfl, map_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((h v (fun i => Nat.succ_pos (w i))).trans_lt hd)
  have hlt : P.totalDegree < P.totalDegree := by
    change P.support.sup (fun e => e.degree) < P.totalDegree
    refine (Finset.sup_lt_iff (Nat.zero_lt_of_lt hd)).2 fun e he' => ?_
    have hz := congrArg (fun Q : MvPolynomial ι ℚ => Q.coeff e) hvanish
    by_contra! heq
    have hEq : e.degree = P.totalDegree := le_antisymm (MvPolynomial.le_totalDegree he') heq
    rw [coeff_homogeneousComponent, ite_eq_left hEq, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hz
    exact MvPolynomial.mem_support_iff.mp he' hz
  exact (lt_irrefl _ hlt)
end
end K1_13_6_2_3_2_5
end
section
namespace K1_13_6_2_3_2_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial
open scoped BigOperators
theorem weight_mapDomain {α β : Type} (f : α → β) (w : β → Fin 4 →₀ ℕ)
    (e : α →₀ ℕ) : Finsupp.weight w (e.mapDomain f) = Finsupp.weight (w ∘ f) e := by
  simp only [Finsupp.weight_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_smul _ _) (fun _ _ _ => add_smul ..)
theorem unit_weight (p : Shape) (e : CapVar (fun _ : Unit => p) →₀ ℕ) :
    Finsupp.weight (step ∘ capSlot (fun _ : Unit => p)) e = fun _ => e.degree := by
  have h : step ∘ capSlot (fun _ : Unit => p) = fun _ _ => (1 : ℕ) := by
    funext v i
    obtain ⟨⟨⟩, v⟩ := v
    cases i
    simp [capSlot, step]
  rw [h, Finsupp.weight_apply, Finsupp.degree_apply]
  funext i
  simp [Finsupp.sum, Finset.sum_apply]
theorem monomialMap_monomial_one (p : Shape) (e : capExponents p →₀ ℕ) :
    monomialMap GeoField (capExponents p) (monomial e 1) =
      monomial (Finsupp.weight Subtype.val e) 1 := by
  rw [monomialMap, aeval_monomial, map_one, one_mul, Finsupp.weight_apply]
  simp only [Finsupp.prod, Finsupp.sum, monomial_pow, one_pow]
  let M := monomialOneHom GeoField (Fin 4)
  change (∏ i ∈ e.support, M (Multiplicative.ofAdd (e i • i.val))) =
    M (Multiplicative.ofAdd (∑ i ∈ e.support, e i • i.val))
  rw [ofAdd_sum, map_prod]
theorem image_weight_degreeLE (p : Shape) (n : ℕ) :
    Finsupp.weight (fun i : capExponents p => i.val) '' {e | e.degree ≤ n} =
      productExponents (fun _ : Unit => p) (fun _ => n) := by
  classical
  let tag : capExponents p → CapVar (fun _ : Unit => p) := fun i => ⟨(), i⟩
  let untag : CapVar (fun _ : Unit => p) → capExponents p := fun v => v.2
  let zeroVar : CapVar (fun _ : Unit => p) := ⟨(), ⟨0, by simp [capExponents]⟩⟩
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    change e.degree ≤ n at he
    refine ⟨e.mapDomain tag + Finsupp.single zeroVar (n - e.degree), ?_, ?_⟩
    · rw [unit_weight, map_add, Finsupp.degree_mapDomain, Finsupp.degree_single,
        Nat.add_sub_of_le he]
    · rw [map_add, weight_mapDomain, Finsupp.weight_single]
      change Finsupp.weight (fun i : capExponents p => i.val) e + (n - e.degree) •
        (0 : Fin 4 →₀ ℕ) = Finsupp.weight (fun i : capExponents p => i.val) e
      rw [smul_zero, add_zero]
  · rintro ⟨e, hdegree, rfl⟩
    refine ⟨e.mapDomain untag, ?_, weight_mapDomain untag Subtype.val e⟩
    change (e.mapDomain untag).degree ≤ n
    rw [Finsupp.degree_mapDomain]
    rw [unit_weight] at hdegree
    exact (congrFun hdegree ()).le
theorem map_restrictTotalDegree (p : Shape) (n : ℕ) :
    (restrictTotalDegree (capExponents p) GeoField n).map
      (monomialMap GeoField (capExponents p)).toLinearMap =
      restrictSupport GeoField (productExponents (fun _ : Unit => p) (fun _ => n)) := by
  classical
  let D : Set (capExponents p →₀ ℕ) := {e | e.degree ≤ n}
  let A := productExponents (fun _ : Unit => p) (fun _ => n)
  let f := (monomialMap GeoField (capExponents p)).toLinearMap
  change (restrictSupport GeoField D).map f = restrictSupport GeoField A
  have hgens : (fun e => f (monomial e 1)) '' D = (fun m => monomial m (1 : GeoField)) '' A := by
    rw [show A = Finsupp.weight Subtype.val '' D from (image_weight_degreeLE p n).symm,
      Set.image_image]
    apply Set.image_congr'
    intro e
    change monomialMap GeoField (capExponents p) (monomial e 1) =
      monomial (Finsupp.weight Subtype.val e) 1
    exact monomialMap_monomial_one p e
  rw [restrictSupport_eq_span GeoField D, restrictSupport_eq_span GeoField A,
    Submodule.map_span, Set.image_image, hgens]
theorem proof : K1_13_6_2_3_2.c4 := by
  intro J p n
  let f := monomialMap GeoField (capExponents p)
  let I := J.comap f.toRingHom
  let g : MvPolynomial (capExponents p) GeoField ⧸ I →ₐ[GeoField] GeoJets ⧸ J :=
    Ideal.quotientMapₐ J f le_rfl
  let L := g.toLinearMap.domRestrict (quotientDegreeLE I n)
  have hL : Function.Injective L := by
    intro x y hxy
    exact Subtype.ext (Ideal.quotientMap_injective (I := J) (f := f.toRingHom) hxy)
  have hcomp : g.comp (Ideal.Quotient.mkₐ GeoField I) = (Ideal.Quotient.mkₐ GeoField J).comp f :=
    Ideal.quotient_map_comp_mkₐ J f le_rfl
  have hmap : (restrictTotalDegree (capExponents p) GeoField n).map f.toLinearMap =
      restrictSupport GeoField (productExponents (fun _ : Unit => p) (fun _ => n)) :=
    map_restrictTotalDegree p n
  have hrange : LinearMap.range L =
      (restrictSupport GeoField (productExponents (fun _ : Unit => p) (fun _ => n))).map
        (Ideal.Quotient.mkₐ GeoField J).toLinearMap := by
    dsimp only [L]
    rw [LinearMap.range_domRestrict, quotientDegreeLE, ← Submodule.map_comp,
      ← AlgHom.comp_toLinearMap, hcomp, AlgHom.comp_toLinearMap, Submodule.map_comp, hmap]
  change Module.finrank GeoField (quotientDegreeLE I n) = _
  rw [← LinearMap.finrank_range_of_inj hL, hrange, supportRank]
end
end K1_13_6_2_3_2_4
end
section
set_option autoImplicit false
namespace K1_13_6_2_3_2_5
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial Filter
open scoped BigOperators
variable {ι : Type} [Fintype ι]
theorem shapeSum_add (shapes : ι → Shape) (a b : ι → ℕ) :
    shapeSum shapes (a + b) = (shapeSum shapes a).plus (shapeSum shapes b) := by
  simp [shapeSum, Shape.plus, Pi.add_apply, add_mul, Finset.sum_add_distrib]
theorem shapeSum_step [DecidableEq ι] (shapes : ι → Shape) (i : ι) :
    shapeSum shapes (step i) = shapes i := by
  simp [shapeSum, step, Pi.single_apply, ite_mul]
private theorem shapeSum_scale (shapes : ι → Shape) (n : ℕ) (v : ι → ℕ) :
    shapeSum shapes (fun i => n * v i) = (shapeSum shapes v).scale n := by
  simp [shapeSum, Shape.scale, mul_assoc, Finset.mul_sum]
private theorem shapeSum_chamber (shapes : ι → Shape) (hs : ∀ i, ChamberBox (shapes i))
    (v : ι → ℕ) (base : ι) (hv : 0 < v base) : ChamberBox (shapeSum shapes v) := by
  refine ⟨Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hs i).1), ?_, ?_⟩
  · change 3 * (∑ i, v i * (shapes i).t) ≤ ∑ i, v i * (shapes i).j
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [Nat.mul_left_comm 3]
      exact Nat.mul_le_mul_left _ (hs i).2.1
  · exact (Nat.mul_pos hv (hs base).2.2).trans_le
      (Finset.single_le_sum (f := fun i => v i * (shapes i).t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ base))
private theorem cap_surjective (p : Shape) (hp : ChamberBox p) :
    Function.Surjective (monomialMap GeoField (capExponents p)) := by
  apply monomialMap_surjective
  intro i
  have ⟨hb, hj, ht⟩ := hp
  fin_cases i <;>
    norm_num [K1_13_6_2_3_1.cap_coords, Finsupp.single_apply] <;> omega
private theorem supportRank_le (J : Ideal GeoJets) {p q : Shape} (h : InBox p q) :
    supportRank J (capExponents p) ≤ supportRank J (capExponents q) := by
  have hsub : capExponents p ⊆ capExponents q := fun _ he =>
    ⟨he.1.trans (Nat.mul_le_mul_left _ h.1), he.2.1.trans (Nat.mul_le_mul_left _ h.2.1),
      he.2.2.trans (Nat.mul_le_mul_left _ h.2.2)⟩
  have : Module.Finite GeoField (restrictSupport GeoField (capExponents q)) :=
    Module.Finite.of_basis (basisRestrictSupport GeoField _)
  exact Submodule.finrank_mono (Submodule.map_mono (restrictSupport_mono GeoField hsub))
private theorem shape_bounds (p q : Shape) (hq : ChamberBox q) :
    ∃ C : ℕ, ∀ n, InBox (q.scale n) (p.plus (q.scale n)) ∧
      InBox (p.plus (q.scale n)) (q.scale (n + C)) := by
  let C := p.b + p.j + p.t
  have ⟨hb, hj, ht⟩ := hq
  have bound (a b : ℕ) (ha : a ≤ C) (hpos : 0 < b) (n : ℕ) :
      a + n * b ≤ (n + C) * b := by
    rw [Nat.add_mul, add_comm a]
    exact Nat.add_le_add_left (ha.trans (Nat.le_mul_of_pos_right _ hpos)) _
  refine ⟨C, fun n => ⟨⟨Nat.le_add_left _ _, Nat.le_add_left _ _, Nat.le_add_left _ _⟩,
    ⟨bound p.b q.b (by dsimp [C]; omega) (by omega) n,
     bound p.j q.j (by dsimp [C]; omega) (by omega) n,
     bound p.t q.t (by dsimp [C]; omega) ht n⟩⟩⟩
theorem ray_compare (shapes : ι → Shape) (J : Ideal GeoJets) (base : ι)
    (hs : ∀ i, ChamberBox (shapes i))
    (hfil : ∀ q : Shape, ChamberBox q → ∀ n,
      affineHilbertFunction
        (J.comap (monomialMap GeoField (capExponents q)).toRingHom) n =
      supportRank J (capExponents (q.scale n)))
    (P : MvPolynomial ι ℚ) (u : ι → ℕ)
    (hu : ∀ a ≥ u, MvPolynomial.eval (fun i => (a i : ℚ)) P =
      (supportRank J (capExponents (shapeSum shapes a)) : ℚ))
    (v : ι → ℕ) (hv : 0 < v base) (d : ℕ) (hd : dimension J ≤ d) :
    (ray P u v).natDegree ≤ dimension J ∧
    (ray P u v).coeff d = capCoeff J d (shapeSum shapes v) := by
  let q := shapeSum shapes v
  have hq : ChamberBox q := shapeSum_chamber shapes hs v base hv
  let I := J.comap (monomialMap GeoField (capExponents q)).toRingHom
  let Q := affineHilbertPolynomial I
  have hQ : Q.natDegree = dimension J :=
    natDegree_affineHilbertPolynomial_comap_of_surjective _ (cap_surjective q hq) J
  obtain ⟨C, hC⟩ := shape_bounds (shapeSum shapes u) q hq
  have hR (n : ℕ) : (ray P u v).eval (n : ℚ) =
      (supportRank J (capExponents ((shapeSum shapes u).plus (q.scale n))) : ℚ) := by
    rw [ray_eval]
    change MvPolynomial.eval (fun i => (((u + fun j => n * v j) i : ℕ) : ℚ)) P = _
    rw [hu (u + fun i => n * v i) (fun i => Nat.le_add_right _ _), shapeSum_add, shapeSum_scale]
  have hshift : Tendsto (fun n : ℕ => n + C) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n C) tendsto_id
  have hlo : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ (ray P u v).eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I] with n hn
    rw [show Q.eval (n : ℚ) = (affineHilbertFunction I n : ℚ) from hn, hfil q hq n, hR]
    exact_mod_cast supportRank_le J (hC n).1
  have hhi : ∀ᶠ n : ℕ in atTop,
      (ray P u v).eval (n : ℚ) ≤ (Polynomial.taylor (C : ℚ) Q).eval (n : ℚ) := by
    filter_upwards [hshift.eventually (eventually_eval_affineHilbertPolynomial I)] with n hn
    rw [Polynomial.taylor_eval, ← Nat.cast_add, show Q.eval ((n + C : ℕ) : ℚ) =
      (affineHilbertFunction I (n + C) : ℚ) from hn, hfil q hq (n + C), hR]
    exact_mod_cast supportRank_le J (hC n).2
  have hT : (Polynomial.taylor (C : ℚ) Q).natDegree = dimension J :=
    (Polynomial.natDegree_taylor Q _).trans hQ
  have hdeg : (ray P u v).natDegree ≤ dimension J :=
    (Polynomial.natDegree_le_of_eventually_eval_natCast_le
      (Eventually.of_forall fun n => by rw [hR]; positivity) hhi).1.trans_eq hT
  have hl := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hQ.trans_le hd) (hdeg.trans hd) hlo
  have hh := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hdeg.trans hd) (hT.trans_le hd) hhi
  rw [Polynomial.coeff_taylor_of_natDegree_le _ (hQ.trans_le hd)] at hh
  exact ⟨hdeg, le_antisymm hh hl⟩
end
end K1_13_6_2_3_2_5
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
theorem eq_of_grid {p q : Form} {N : ℕ}
    (h : ∀ t : Grade, (∀ j, N ≤ t j) →
        eval (fun j => (t j : ℚ)) p = eval (fun j => (t j : ℚ)) q) : p = q := by
  let s : Fin 5 → Set ℚ := fun _ => Set.range fun n : ℕ => ((N + n : ℕ) : ℚ)
  refine MvPolynomial.funext_set s (fun _ => Set.infinite_range_of_injective ?_) ?_
  · intro a b hab
    exact Nat.add_left_cancel (Nat.cast_injective hab)
  · intro x hx
    choose n hn using fun j => hx j (Set.mem_univ j)
    let t : Grade := Finsupp.equivFunOnFinite.symm fun j => N + n j
    have hx' : (fun j => (t j : ℚ)) = x := funext hn
    rw [← hx']
    exact h t (fun j => Nat.le_add_right N (n j))
theorem Represents.unique {p q : Form} {h : Grade → ℚ}
    (hp : Represents p h) (hq : Represents q h) : p = q := by
  obtain ⟨N, hN⟩ := hp
  obtain ⟨M, hM⟩ := hq
  exact eq_of_grid (N := max N M) (fun t ht =>
    (hN t (fun j => (le_max_left N M).trans (ht j))).trans
      (hM t (fun j => (le_max_right N M).trans (ht j))).symm)
theorem squarefree_apply (I : Finset (Fin 5)) (i : Fin 5) :
    squarefree I i = if i ∈ I then 1 else 0 := by
  classical
  simp [squarefree, unitGrade, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
theorem squarefree_degree (I : Finset (Fin 5)) : (squarefree I).degree = I.card := by
  classical
  simp [Finsupp.degree_eq_sum, squarefree_apply]
theorem squarefree_insert {I : Finset (Fin 5)} {i : Fin 5} (hi : i ∉ I) :
    squarefree (insert i I) = squarefree I + unitGrade i := by
  simp [squarefree, Finset.sum_insert hi, add_comm]
theorem line_eval (p : Form) (t : Grade) (N : ℕ) :
    (line t p).eval (N : ℚ) = eval (fun j => ((N • t) j : ℚ)) p := by
  let L := (Polynomial.evalRingHom (N : ℚ)).comp (line t)
  let R := eval (fun j => ((N • t) j : ℚ))
  have h : L = R := by
    ext j
    · simp [L, R, line]
    · simp [L, R, line, Finsupp.smul_apply, Nat.cast_mul, mul_comm]
  exact DFunLike.congr_fun h p
theorem line_of_diagonal_agreement (B : Boxes) (P : Ideal GeoJets5) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (t : Grade) (ht : ∀ j, 0 < t j)
    (hdiag : ∀ N, gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
      affineHilbertFunction (diagonalIdeal B P t) N) :
    line t p = affineHilbertPolynomial (diagonalIdeal B P t) := by
  obtain ⟨N₀, hN₀⟩ := hp
  refine eq_affineHilbertPolynomial_of_eval_eq (N₀ := N₀) fun N hN => ?_
  rw [line_eval, hN₀ _ (fun j => hN.trans (Nat.le_mul_of_pos_right N (ht j)))]
  exact congrArg (fun n : ℕ => (n : ℚ)) (hdiag N)
theorem line_monomial (t a : Grade) (r : ℚ) :
    line t (monomial a r) =
      Polynomial.C (eval (fun j => (t j : ℚ)) (monomial a r)) * Polynomial.X ^ a.degree := by
  simp only [line, eval₂Hom_monomial, eval_monomial, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply]
  rw [← mul_assoc, ← map_mul]
theorem line_coeff (p : Form) (t : Grade) (d : ℕ) :
    (line t p).coeff d = eval (fun j => (t j : ℚ)) (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    rw [line_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases h : a.degree = d
    · subst d
      simp [homogeneousComponent_eq_self (isHomogeneous_monomial r rfl)]
    · simp [Ne.symm h, homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
  | add p q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]
theorem totalDegree_le_of_lines {p : Form} {d : ℕ}
    (h : ∀ t : Grade, (∀ j, 0 < t j) → (line t p).natDegree ≤ d) :
    p.totalDegree ≤ d := by
  refine Finset.sup_le fun a ha => ?_
  by_contra! hda
  have hh : homogeneousComponent a.degree p = 0 := by
    refine eq_of_grid (N := 1) fun t ht => ?_
    rw [map_zero, ← line_coeff]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((h t ht).trans_lt hda)
  have hcoeff := congrArg (fun q : Form => q.coeff a) hh
  simp [coeff_homogeneousComponent, Finsupp.degree_apply] at hcoeff
  exact (mem_support_iff.mp ha) hcoeff
theorem positiveDiagonal_apply (J : Finset (Fin 5)) (j : Fin 5) :
    positiveDiagonal J j = if j ∈ J then 2 else 1 := rfl
theorem cube_prod (I : Finset (Fin 5)) (f : Fin 5 → ℚ) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) * ∏ j ∈ J, f j) =
      ∏ j ∈ I, (f j - 1) := by
  classical
  rw [Finset.prod_sub f (fun _ => (1 : ℚ))]
  refine Finset.sum_bij (fun J _ => I \ J) ?_ ?_ ?_ ?_
  · intro J hJ
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro J hJ K hK h
    simpa [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hJ),
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hK)] using
      congrArg (fun U => I \ U) h
  · intro J hJ
    exact ⟨I \ J, Finset.mem_powerset.mpr Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hJ)⟩
  · intro J hJ
    simp [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hJ),
      Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hJ)]
theorem cube_monomial (I : Finset (Fin 5)) (a : Grade) (r : ℚ) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
      eval (fun j => (positiveDiagonal J j : ℚ)) (monomial a r)) =
      r * ∏ j ∈ I, ((2 : ℚ) ^ a j - 1) := by
  rw [← cube_prod, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [eval_monomial, Finsupp.prod_pow]
  have he (j : Fin 5) : ((positiveDiagonal J j : ℕ) : ℚ) ^ a j =
      if j ∈ J then (2 : ℚ) ^ a j else 1 := by
    by_cases h : j ∈ J <;> simp [positiveDiagonal_apply, h]
  simp_rw [he]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  ring
theorem cube_monomial_top (I : Finset (Fin 5)) {a : Grade} (ha : a.degree = I.card)
    (r : ℚ) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
      eval (fun j => (positiveDiagonal J j : ℚ)) (monomial a r)) =
      (monomial a r).coeff (squarefree I) := by
  classical
  rw [cube_monomial]
  by_cases h : squarefree I ≤ a
  · have he : squarefree I = a := by
      obtain ⟨b, hab⟩ := le_iff_exists_add.mp h
      have hd := congrArg Finsupp.degree hab
      rw [ha, map_add, squarefree_degree] at hd
      have hb : b.degree = 0 := by omega
      rw [hab, (Finsupp.degree_eq_zero_iff _).mp hb, add_zero]
    subst a
    rw [show (∏ j ∈ I, ((2 : ℚ) ^ squarefree I j - 1)) = 1 from
      Finset.prod_eq_one (fun j hj => by norm_num [squarefree_apply, hj])]
    simp
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hm : j ∈ I ∧ a j = 0 := by
      by_cases hi : j ∈ I <;> simp [squarefree_apply, hi] at hj ⊢
      exact hj
    rw [Finset.prod_eq_zero hm.1 (by simp [hm.2]), mul_zero, coeff_monomial]
    exact (ite_eq_right (fun he => h he.ge)).symm
theorem cube_extract (I : Finset (Fin 5)) (p : Form) :
    (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
      (line (positiveDiagonal J) p).coeff I.card) = p.coeff (squarefree I) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    simp_rw [line_coeff, homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    by_cases h : I.card = a.degree
    · simpa only [ite_eq_left h] using cube_monomial_top I h.symm r
    · have hne : a ≠ squarefree I := fun h' => h (by rw [h', squarefree_degree])
      simp [h, coeff_monomial, hne]
  | add p q hp hq =>
    simp [map_add, Polynomial.coeff_add, mul_add, Finset.sum_add_distrib, hp, hq]
end
end K1_13_6_2_4_1
end
section
namespace K1_13_6_2_3_2_6
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 K1_13_6_2_3_2 MvPolynomial
def rawCapMap {ι : Type} (shapes : ι → Shape) :
    MvPolynomial (CapVar shapes) GeoField →ₐ[GeoField] MvPolynomial ι GeoJets :=
  aeval fun v => monomial (Finsupp.single v.1 1) (monomial v.2.val 1)
theorem mem_capIdeal {ι : Type} (shapes : ι → Shape) (J : Ideal GeoJets)
    (f : MvPolynomial (CapVar shapes) GeoField) :
    f ∈ capIdeal shapes J ↔ ∀ e, (rawCapMap shapes f).coeff e ∈ J := by
  have hmap : capMap shapes J = (mapAlgHom (Ideal.Quotient.mkₐ GeoField J)).comp
      (rawCapMap shapes) := by
    apply algHom_ext
    intro v
    simp only [capMap, rawCapMap, AlgHom.comp_apply, aeval_X, mapAlgHom_apply, map_monomial]
    rfl
  change capMap shapes J f = 0 ↔ _
  rw [hmap, AlgHom.comp_apply, mapAlgHom_apply]
  constructor
  · intro h e
    have he := congrArg (fun q : MvPolynomial ι (GeoJets ⧸ J) => q.coeff e) h
    rw [coeff_map] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using he)
  · intro h
    ext e
    rw [coeff_map]
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (h e)
theorem box_support {p : Shape} {D : GeoJets} (hD : Box4 p D) :
    ∀ e ∈ D.support, e ∈ capExponents p := by
  intro e he
  obtain ⟨hb, hj, ht⟩ := hD e he
  simp only [id_eq] at hb hj ht
  change e.degree ≤ 2 * p.b ∧ _ ∧ _
  rw [Finsupp.degree_eq_sum]
  exact ⟨by omega, by omega, by omega⟩
theorem box_sq_support {p : Shape} {D : GeoJets} (hD : Box4 p D) :
    ∀ e ∈ (D ^ 2).support, e ∈ capExponents p := by
  intro e he
  rw [MvPolynomial.mem_support_iff, pow_two, coeff_mul] at he
  obtain ⟨⟨u, v⟩, huv, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hu : D.coeff u ≠ 0 := fun h => hc (by simp [h])
  have hv : D.coeff v ≠ 0 := fun h => hc (by simp [h])
  obtain ⟨hub, huj, hut⟩ := hD u (MvPolynomial.mem_support_iff.mpr hu)
  obtain ⟨hvb, hvj, hvt⟩ := hD v (MvPolynomial.mem_support_iff.mpr hv)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
  rw [← huv]
  simp only [capExponents, Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Finsupp.add_apply,
    mul_add, Finset.sum_add_distrib]
  simp only [id_eq] at hub huj hut hvb hvj hvt
  exact ⟨by omega, by omega, by omega⟩
theorem exists_lift {ι : Type} [DecidableEq ι] (shapes : ι → Shape) (i : ι)
    (D : GeoJets) (hD : ∀ e ∈ D.support, e ∈ capExponents (shapes i)) :
    ∃ L : MvPolynomial (CapVar shapes) GeoField,
      IsWeightedHomogeneous (step ∘ capSlot shapes) L (step i) ∧
      rawCapMap shapes L = monomial (Finsupp.single i 1) D := by
  classical
  let v (e : ↥D.support) : CapVar shapes := ⟨i, ⟨e, hD e e.2⟩⟩
  let L : MvPolynomial (CapVar shapes) GeoField :=
    ∑ e ∈ D.support.attach, D.coeff e • MvPolynomial.X (v e)
  refine ⟨L, ?_, ?_⟩
  · change L ∈ weightedHomogeneousSubmodule GeoField (step ∘ capSlot shapes) (step i)
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.smul_mem _ _ (isWeightedHomogeneous_X GeoField (step ∘ capSlot shapes) (v e))
  · simp only [L, map_sum, map_smul, rawCapMap, aeval_X, v, smul_monomial, smul_eq_mul, mul_one]
    rw [← map_sum (monomial (Finsupp.single i 1))]
    congr 1
    rw [Finset.sum_attach D.support (fun e => monomial e (D.coeff e))]
    exact D.as_sum.symm
theorem capIdeal_mono {ι : Type} (shapes : ι → Shape) {J K : Ideal GeoJets}
    (h : J ≤ K) : capIdeal shapes J ≤ capIdeal shapes K := by
  intro f hf
  exact (mem_capIdeal shapes K f).mpr fun e => h ((mem_capIdeal shapes J f).mp hf e)
theorem lift_mem {ι : Type} {shapes : ι → Shape} {i : ι} {D : GeoJets}
    {J : Ideal GeoJets} {L : MvPolynomial (CapVar shapes) GeoField}
    (hL : rawCapMap shapes L = monomial (Finsupp.single i 1) D)
    (hD : D ∈ J) : L ∈ capIdeal shapes J := by
  classical
  rw [mem_capIdeal, hL]
  intro e
  rw [coeff_monomial]
  split_ifs
  · exact hD
  · exact J.zero_mem
theorem lift_mul_mem_iff {ι : Type} {shapes : ι → Shape} {i : ι} {D : GeoJets}
    {J K : Ideal GeoJets} {L : MvPolynomial (CapVar shapes) GeoField}
    (hL : rawCapMap shapes L = monomial (Finsupp.single i 1) D)
    (hD : ∀ x, D * x ∈ J ↔ x ∈ K) (f : MvPolynomial (CapVar shapes) GeoField) :
    L * f ∈ capIdeal shapes J ↔ f ∈ capIdeal shapes K := by
  classical
  rw [mem_capIdeal, mem_capIdeal, map_mul, hL]
  constructor
  · intro h e
    apply (hD _).mp
    rw [← coeff_monomial_mul e (Finsupp.single i 1) D (rawCapMap shapes f)]
    exact h _
  · intro h e
    rw [coeff_monomial_mul']
    split_ifs
    · exact (hD _).mpr (h _)
    · exact J.zero_mem
theorem mem_cut_iff (J : Ideal GeoJets) (D x : GeoJets) :
    x ∈ cut J D ↔ ∃ r : GeoJets ⧸ J, Ideal.Quotient.mk J x = Ideal.Quotient.mk J D * r := by
  rw [show cut J D = Ideal.span {D} ⊔ J from sup_comm _ _, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨r, b, hb, rfl⟩
    exact ⟨Ideal.Quotient.mk J r, by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hb, mul_comm]⟩
  · rintro ⟨r, hr⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨a, x - a * D, Ideal.Quotient.eq.mp ?_, by abel⟩
    rw [map_mul, mul_comm]
    exact hr
theorem square_mul_mem_iff (J : Ideal GeoJets) (D : GeoJets)
    (hD : IsLeftRegular (Ideal.Quotient.mk J D)) (x : GeoJets) :
    D ^ 2 * x ∈ J ↔ x ∈ J := by
  simp only [← Ideal.Quotient.eq_zero_iff_mem, map_mul, pow_two]
  exact (hD.mul hD).mul_left_eq_zero_iff
theorem cut_square_mul_mem_iff (J : Ideal GeoJets) (D : GeoJets)
    (hD : IsLeftRegular (Ideal.Quotient.mk J D)) (x : GeoJets) :
    D * x ∈ cut J (D ^ 2) ↔ x ∈ cut J D := by
  simp only [mem_cut_iff, map_mul, pow_two, mul_assoc]
  exact exists_congr fun _ => Function.Injective.eq_iff hD
end
end K1_13_6_2_3_2_6
end
section
namespace K1_13_6_2_4_5
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4
private theorem four_ne_zero : (4 : GeoField) ≠ 0 := by
  let e := (genericCoeffs.comp Polynomial.C).comp K1_13.embed
  let : CharP GeoField K1.p := charP_of_injective_ringHom e.injective K1.p
  intro hz
  have hd := (CharP.cast_eq_zero_iff GeoField K1.p 4).mp (by simpa using hz)
  exact (not_le_of_gt (show 4 < K1.p by decide)) (Nat.le_of_dvd (by decide) hd)
private theorem graph_eq {f Q l} (b : Branch f Q l) :
    b.graph = oldEmbedding (toGeneric (partialFlow b.g)) +
      oldEmbedding (MvPolynomial.C (4 : GeoField) * b.sigma) * MvPolynomial.X (Fin.last 4) := by
  simp [Branch.graph, oldEmbedding]
private theorem graph_old {f Q l} (b : Branch f Q l) (D : GeoJets) :
    b.onGraph (oldEmbedding D) = b.localMap D :=
  RingHom.congr_fun (graph_on_old b) D
private theorem onGraph_graph {f Q l} (b : Branch f Q l) : b.onGraph b.graph = 0 := by
  rw [graph_eq, map_add, map_mul, graph_old, graph_old, map_mul]
  have hx : b.onGraph (MvPolynomial.X (Fin.last 4)) =
      b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹) * toGeneric (partialFlow b.g)) *
        IsLocalization.Away.invSelf b.sigma := by
    rw [Branch.onGraph, MvPolynomial.eval₂Hom_X', Fin.lastCases_last]
  have hσ : b.localMap b.sigma * IsLocalization.Away.invSelf b.sigma = 1 :=
    IsLocalization.Away.mul_invSelf b.sigma
  have h4 : b.localMap (MvPolynomial.C (4 : GeoField)) *
      b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹)) = -1 := by
    rw [← map_mul, ← map_mul, mul_neg, mul_inv_cancel₀ four_ne_zero, map_neg, map_one, map_neg, map_one]
  rw [hx, map_mul]
  calc
    _ = b.localMap (toGeneric (partialFlow b.g)) +
        (b.localMap (MvPolynomial.C (4 : GeoField)) *
          b.localMap (MvPolynomial.C (-(4 : GeoField)⁻¹))) *
        (b.localMap b.sigma * IsLocalization.Away.invSelf b.sigma) *
        b.localMap (toGeneric (partialFlow b.g)) := by ac_rfl
    _ = 0 := by rw [h4, hσ, mul_one, neg_one_mul, add_neg_cancel]
private theorem factor_onGraph {f Q l} (b : Branch f Q l) {A : Type*} [CommRing A]
    (k : GeoJets5 →+* A) (hs : IsUnit (k (oldEmbedding b.sigma))) (hg : k b.graph = 0) :
    k = (IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs).comp b.onGraph := by
  let φ : b.Local →+* A := IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs
  let ψ := φ.comp b.onGraph
  have hold (D : GeoJets) : ψ (oldEmbedding D) = k (oldEmbedding D) := by
    change φ (b.onGraph (oldEmbedding D)) = _
    rw [graph_old]
    exact IsLocalization.Away.lift_eq b.sigma hs D
  have hψ : ψ b.graph = 0 := by simp [ψ, onGraph_graph]
  change k = ψ
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [oldEmbedding] using (hold (MvPolynomial.C a)).symm
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [graph_eq, map_add, map_mul] at hg hψ
      rw [hold, hold] at hψ
      have hμ : IsUnit (k (oldEmbedding (MvPolynomial.C (4 : GeoField) * b.sigma))) := by
        rw [map_mul, map_mul]
        exact ((isUnit_iff_ne_zero.mpr four_ne_zero).map
          (k.comp (oldEmbedding.comp MvPolynomial.C))).mul hs
      exact hμ.mul_right_inj.mp (add_left_cancel (hg.trans hψ.symm))
    · simpa [oldEmbedding] using (hold (MvPolynomial.X j)).symm
private theorem graphLift_prime {f Q l} (b : Branch f Q l) (P : Ideal GeoJets)
    (hP : P.IsPrime) (hs : b.sigma ∉ P) : (graphLift b P).IsPrime := by
  have hdis : Disjoint (↑(Submonoid.powers b.sigma) : Set GeoJets) P := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨n, rfl⟩ hn
    exact hs (hP.mem_of_pow_mem n hn)
  let : (P.map b.localMap).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers b.sigma) b.Local P hP hdis
  exact Ideal.comap_isPrime b.onGraph _
private theorem graphLift_contains_graph {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) :
    b.graph ∈ graphLift b P := by
  change b.onGraph b.graph ∈ P.map b.localMap
  rw [onGraph_graph]
  exact Ideal.zero_mem _
private theorem cylinder_le_graphLift {f Q l} (b : Branch f Q l) (P : Ideal GeoJets) :
    cylinder P ≤ graphLift b P := by
  rw [cylinder, Ideal.map_le_iff_le_comap, graphLift, Ideal.comap_comap, graph_on_old]
  exact Ideal.le_comap_map
private theorem prime_eq_graphLift {f Q l} (b : Branch f Q l) (T : Ideal GeoJets5)
    (hT : T.IsPrime) (hs : oldEmbedding b.sigma ∉ T) (hg : b.graph ∈ T) :
    T = graphLift b (T.comap oldEmbedding) := by
  let := hT
  let A := FractionRing (GeoJets5 ⧸ T)
  let k := (algebraMap (GeoJets5 ⧸ T) A).comp (Ideal.Quotient.mk T)
  have hk (x : GeoJets5) : k x = 0 ↔ x ∈ T := by
    change algebraMap (GeoJets5 ⧸ T) A (Ideal.Quotient.mk T x) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  have hs' : IsUnit (k (oldEmbedding b.sigma)) := isUnit_iff_ne_zero.mpr (mt (hk _).mp hs)
  let φ : b.Local →+* A := IsLocalization.Away.lift b.sigma (g := k.comp oldEmbedding) hs'
  have hφ : φ.comp b.localMap = k.comp oldEmbedding :=
    IsLocalization.Away.lift_comp b.sigma hs'
  have hker : (RingHom.ker φ).comap b.localMap = T.comap oldEmbedding := by
    ext x
    change φ (b.localMap x) = 0 ↔ oldEmbedding x ∈ T
    rw [show φ (b.localMap x) = k (oldEmbedding x) from RingHom.congr_fun hφ x, hk]
  rw [graphLift, ← hker]
  have he : ((RingHom.ker φ).comap b.localMap).map b.localMap =
      RingHom.ker φ := IsLocalization.map_under (Submonoid.powers b.sigma) b.Local _
  rw [he]
  ext D
  change D ∈ T ↔ φ (b.onGraph D) = 0
  exact (hk D).symm.trans (Iff.of_eq (congrArg (fun j : GeoJets5 →+* A => j D = 0)
    (factor_onGraph b k hs' ((hk _).mpr hg))))
private def substituteLast (x : GeoJets) : GeoJets5 →+* GeoJets :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.lastCases x MvPolynomial.X)
private theorem substituteLast_old (x : GeoJets) :
    (substituteLast x).comp oldEmbedding = RingHom.id GeoJets := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [substituteLast, oldEmbedding]
  · intro i
    simp [substituteLast, oldEmbedding]
theorem graph_proper {f Q l} (b : Branch f Q l) :
    b.graph ∉ cylinder b.surface := by
  intro h
  have hm (x : GeoJets) : substituteLast x b.graph ∈ b.surface := by
    have hle : cylinder b.surface ≤ b.surface.comap (substituteLast x) := by
      rw [cylinder, Ideal.map_le_iff_le_comap, Ideal.comap_comap, substituteLast_old, Ideal.comap_id]
    exact hle h
  have evalGraph (x : GeoJets) : substituteLast x b.graph =
      toGeneric (partialFlow b.g) + (MvPolynomial.C (4 : GeoField) * b.sigma) * x := by
    have ho (D : GeoJets) : substituteLast x (oldEmbedding D) = D :=
      RingHom.congr_fun (substituteLast_old x) D
    rw [graph_eq, map_add, map_mul, ho, ho]
    rw [substituteLast, MvPolynomial.eval₂Hom_X', Fin.lastCases_last]
  have h0 := hm 0
  have h1 := hm 1
  rw [evalGraph, mul_zero, add_zero] at h0
  rw [evalGraph, mul_one] at h1
  have hσ : MvPolynomial.C (4 : GeoField) * b.sigma ∈ b.surface :=
    (b.surface.add_mem_iff_right h0).mp h1
  have hu : IsUnit (MvPolynomial.C (4 : GeoField) : GeoJets) :=
    (isUnit_iff_ne_zero.mpr four_ne_zero).map MvPolynomial.C
  exact b.chart.2.2 ((b.base.isPrime.mem_or_mem hσ).resolve_left
    (fun hc => b.base.isPrime.ne_top (b.surface.eq_top_of_isUnit_mem hc hu)))
theorem graph_minimal {f Q l} (b : Branch f Q l) :
    (sectionIdeal (cylinder b.surface) b.graph).IsMinimalPrime (graphLift b b.surface) := by
  refine ⟨⟨graphLift_prime b b.surface b.base.isPrime b.chart.2.2,
    sup_le (cylinder_le_graphLift b _) ((Ideal.span_singleton_le_iff_mem _).mpr
      (graphLift_contains_graph b _))⟩, ?_⟩
  intro T hT hTG
  have hs : oldEmbedding b.sigma ∉ T := by
    intro h
    have hm : b.sigma ∈ (graphLift b b.surface).comap oldEmbedding := hTG h
    rw [graphLift_comap b b.surface b.base.isPrime b.chart.2.2] at hm
    exact b.chart.2.2 hm
  have hg : b.graph ∈ T := hT.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hb : b.surface ≤ T.comap oldEmbedding :=
    Ideal.map_le_iff_le_comap.mp (le_sup_left.trans hT.2)
  rw [prime_eq_graphLift b T hT.1 hs hg]
  exact Ideal.comap_mono (Ideal.map_mono hb)
theorem member_minimal {f Q l} (b : Branch f Q l) {E : GeoJets5}
    (hE : Associated (b.onGraph E) (b.localMap b.member)) :
    (sectionIdeal (graphLift b b.surface) E).IsMinimalPrime (graphLift b b.curve) := by
  have hSC : b.surface ≤ b.curve := le_sup_left.trans b.divisor.le
  have hm : b.member ∈ b.curve := b.divisor.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine ⟨⟨graphLift_prime b b.curve b.divisor.isPrime b.regularCurve,
    sup_le (Ideal.comap_mono (Ideal.map_mono hSC)) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩, ?_⟩
  · change b.onGraph E ∈ b.curve.map b.localMap
    exact (b.curve.map b.localMap).mem_of_dvd hE.dvd' (Ideal.mem_map_of_mem _ hm)
  · intro T hT hTC
    let P := T.comap oldEmbedding
    have hP : P.IsPrime := by
      let := hT.1
      exact Ideal.comap_isPrime oldEmbedding _
    have hPC : P ≤ b.curve := by
      have hle := Ideal.comap_mono (f := oldEmbedding) hTC
      rwa [graphLift_comap b b.curve b.divisor.isPrime b.regularCurve] at hle
    have hS : b.surface ≤ P :=
      Ideal.map_le_iff_le_comap.mp ((cylinder_le_graphLift b _).trans (le_sup_left.trans hT.2))
    have hreg : b.sigma ∉ P := fun h => b.regularCurve (hPC h)
    have hEq : T = graphLift b P := prime_eq_graphLift b T hT.1 hreg
      (hT.2 (Ideal.mem_sup_left (graphLift_contains_graph b _)))
    have hEmem : E ∈ T := hT.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [hEq] at hEmem
    have hold : oldEmbedding b.member ∈ graphLift b P := by
      change b.onGraph (oldEmbedding b.member) ∈ P.map b.localMap
      rw [graph_old]
      exact (P.map b.localMap).mem_of_dvd hE.dvd hEmem
    have hmP : b.member ∈ P := by
      have hh : b.member ∈ (graphLift b P).comap oldEmbedding := hold
      rwa [graphLift_comap b P hP hreg] at hh
    have hCP : b.curve ≤ P :=
      b.divisor.2 ⟨hP, sup_le hS ((Ideal.span_singleton_le_iff_mem _).mpr hmP)⟩ hPC
    rw [hEq]
    exact Ideal.comap_mono (Ideal.map_mono hCP)
end
end K1_13_6_2_4_5
end
section
namespace K1_13_6_2_4_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
open scoped BigOperators Pointwise
def c1 : Prop :=
  ∀ (B : Boxes), (∀ i, Chamber (B i).1) → ∀ (t : Fin 5 → ℕ) (n : ℕ),
    n • diagonalExponents B t = latticePoints (scaleCap (sumCap B t) n)
def c2 : Prop :=
  ∀ p : Shape, Chamber p →
    ∃ H : Polynomial ℚ, H.natDegree ≤ 4 ∧
      H.coeff 4 = (volume32 p : ℚ) / 2 ∧
      ∀ n : ℕ, H.eval (n : ℚ) = (K1_13_6_2_3.capExponents (p.scale n)).ncard
private theorem diagonal_coeff (h1 : c1) (h2 : c2)
    (B : Boxes) (hB : ∀ i, Chamber (B i).1) (t : Fin 5 → ℕ) :
    (affineHilbertPolynomial (Ideal.comap (monomialMap GeoField (diagonalExponents B t))
      ⊥)).coeff 5 = volumeProduct (sumCap B t) := by
  let a := sumCap B t
  obtain ⟨H, hdeg, hcoeff, hH⟩ := h2 a.1 (sumCap_chamber B hB t)
  let F := H * (Polynomial.C (2 * (a.2 : ℚ)) * Polynomial.X + 1)
  have heq : F = affineHilbertPolynomial
      (Ideal.comap (monomialMap GeoField (diagonalExponents B t)) ⊥) := by
    apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := 0)
    intro n _
    rw [monomial_hilbert_count _ (zero_mem_diagonalExponents B t), h1 B hB t n,
      lattice_count]
    simp only [F, scaleCap, a, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, hH, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    ring
  rw [← heq]
  have h5 := Polynomial.coeff_eq_zero_of_natDegree_lt (p := H) (n := 5) (by omega)
  simp only [F, mul_add, mul_one, Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C, h5, add_zero, hcoeff, volumeProduct, a]
  ring
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_2_4.c3 := by
  intro p hp
  have hB := (boxes_admissible p hp).1
  unfold mixedDegree
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℚ) ^ 5 = 32 by norm_num, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num)]
  change (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (diagonalExponents (boxes p) (diagonal J))) ⊥)).coeff 5) ≤ _
  simp only [diagonal_coeff h1 h2 (boxes p) hB]
  exact polarized_budget p
end
end K1_13_6_2_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
theorem diagonal_degree_le (B : Boxes) (P : Ideal GeoJets5) (t : Grade) {d : ℕ}
    (hd : DimLE P d) : (affineHilbertPolynomial (diagonalIdeal B P t)).natDegree ≤ d := by
  let f := monomialMap GeoField (diagonalExponents B t)
  let φ := Ideal.quotientMapₐ P f le_rfl
  exact (natDegree_affineHilbertPolynomial_le_of_injective φ Ideal.quotientMap_injective).trans
    (K1_13_6_2_4_2.hilbert_degree_le hd)
theorem gradedIdeal_degree_le (B : Boxes) (P : Ideal GeoJets5) {d : ℕ} (hd : DimLE P d)
    {p : Form} (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    p.totalDegree ≤ d := by
  apply totalDegree_le_of_lines
  intro t ht
  rw [line_of_diagonal_agreement B P hp t ht (hdiag t ht)]
  exact diagonal_degree_le B P t hd
theorem mixedDegree_eq (B : Boxes) (P : Ideal GeoJets5) (I : Finset (Fin 5)) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    mixedDegree B P I = p.coeff (squarefree I) / (2 : ℚ) ^ I.card := by
  unfold mixedDegree
  rw [← cube_extract I p]
  congr 1
  refine Finset.sum_congr rfl fun J _ => ?_
  have ht (j : Fin 5) : 0 < positiveDiagonal J j := by
    rw [positiveDiagonal_apply]
    split <;> decide
  have he := line_of_diagonal_agreement B P hp (positiveDiagonal J) ht
    (hdiag (positiveDiagonal J) ht)
  rw [he]
  rfl
end
end K1_13_6_2_4_1
end
section
namespace K1_13_6_1_2
noncomputable section
open K1_13
open scoped BigOperators
def multiOrder {n : ℕ} (a : Fin n →₀ ℕ) : ℕ :=
  a.sum (fun _ k => k)
def hassePartial {n : ℕ} {A : Type*} [CommSemiring A]
    (a : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) A) : MvPolynomial (Fin n) A :=
  ∑ m ∈ P.support, MvPolynomial.monomial (m - a) (P.coeff m * ∏ i : Fin n, ((m i).choose (a i) : A))
def VanishesTo {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (f : R) (d : ℕ) : Prop :=
  let L := Localization.AtPrime p
  algebraMap R L f ∈ IsLocalRing.maximalIdeal L ^ d
end
end K1_13_6_1_2
end
