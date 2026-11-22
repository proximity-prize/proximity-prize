import ProximityPrize.SubmissionLower.UpperBranch1


namespace KoalaRect
noncomputable section
open Polynomial K1_14 K1_14_1 K1_14_1_7
open K1 (I)
open scoped BigOperators
open private centerCoeff centerCoeff_eval from ProximityPrize.SubmissionLower.Fast065

def rectShaped {F : Type} [Field F] (U : Fin 2 → ℕ) (P : TrueSource F) : Prop :=
  ∀ j i a e, sourceCoeff P j i a e ≠ 0 → ∀ z, e z ≤ U z

def seedSupport {F : Type} [Field F] (U : Fin 2 → ℕ) : Submodule F (TrueSource F) where
  carrier := {P | rectShaped U P}
  zero_mem' := by simp [rectShaped, sourceCoeff]
  add_mem' := by
    intro P Q hP hQ j i a e hne z
    by_contra hb
    have hP0 : sourceCoeff P j i a e = 0 := by
      by_contra hz
      exact hb (hP j i a e hz z)
    have hQ0 : sourceCoeff Q j i a e = 0 := by
      by_contra hz
      exact hb (hQ j i a e hz z)
    apply hne
    change ((((P + Q).coeff j).coeff i).coeff a).coeff e = 0
    simp only [Polynomial.coeff_add, AddMonoidAlgebra.coeff_add]
    change sourceCoeff P j i a e + sourceCoeff Q j i a e = 0
    rw [hP0, hQ0, add_zero]
  smul_mem' := by
    intro c P hP j i a e hne z
    apply hP j i a e _ z
    intro hz
    apply hne
    simp [sourceCoeff, Polynomial.coeff_smul, show (((P.coeff j).coeff i).coeff a).coeff e = 0 from hz]

abbrev rectAmbient (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  ambient h s W ⊓ seedSupport U

abbrev rectContacted (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  contacted h word s W ⊓ seedSupport U

abbrev rectComplete {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule L Source :=
  complete Crt word s W ⊓ seedSupport U

def rectEvaluated {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Submodule FX Jet :=
  Submodule.span FX (centerEval '' (rectComplete Crt word s W U : Set Source))

theorem rectEvaluated_le {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : rectEvaluated Crt word s W U ≤ evaluated Crt word s W :=
  Submodule.span_mono (Set.image_mono inf_le_left)

theorem rectEvaluated_axis {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s : Shape} {W : ℕ} {U : Fin 2 → ℕ} {P : Jet} (hP : P ∈ rectEvaluated Crt word s W U)
    (j i : ℕ) (z : Fin 2) : ((P.coeff j).coeff i).degreeOf z ≤ U z := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_le
  intro e he
  by_contra hb
  have hsub : rectEvaluated Crt word s W U ≤ LinearMap.ker (centerCoeff j i e) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q, hQ, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply centerCoeff_eval
    intro a
    by_contra hz
    exact hb (hQ.2 j i a e hz z)
  exact (MvPolynomial.mem_support_iff.mp he) (LinearMap.mem_ker.mp (hsub hP))

abbrev AxisIndex (U : Fin 2 → ℕ) := ∀ z : Fin 2, Fin (U z + 1)

def axisExponent {U : Fin 2 → ℕ} (e : AxisIndex U) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun z => (e z).val)

@[simp] theorem axisExponent_apply {U : Fin 2 → ℕ} (e : AxisIndex U) (z : Fin 2) :
    axisExponent e z = (e z).val := by simp [axisExponent]

def area (U : Fin 2 → ℕ) := (U 0 + 1) * (U 1 + 1)

theorem axis_card (U : Fin 2 → ℕ) : Fintype.card (AxisIndex U) = area U := by
  simp [AxisIndex, Fintype.card_pi, Fin.prod_univ_two, area]

theorem exists_axisIndex {U : Fin 2 → ℕ} (e : Fin 2 →₀ ℕ) (he : ∀ z, e z ≤ U z) :
    ∃ a : AxisIndex U, axisExponent a = e :=
  ⟨fun z => ⟨e z, Nat.lt_succ_of_le (he z)⟩, by ext z; simp⟩

theorem axisExponent_injective (U : Fin 2 → ℕ) : Function.Injective (axisExponent (U := U)) := by
  intro a b h
  funext z
  apply Fin.ext
  simpa using congrArg (fun e : Fin 2 →₀ ℕ => e z) h

open private trueWidth lt_trueWidth_iff trueWidth_eq_add seedWeight_eq Exponents monomialAt
  coeffAt_monomialAt from ProximityPrize.SubmissionLower.Fast065

private abbrev RectIndex (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :=
  Σ q : Fin (s.B + 1), Σ j : Fin (min q.val s.J + 1),
    Fin (trueWidth h s W q.val j.val) × AxisIndex U

private def rectExponents {h : ℕ} {s : Shape} {W : ℕ} {U : Fin 2 → ℕ}
    (k : RectIndex h s W U) : Exponents :=
  (k.2.1.val, k.1.val - k.2.1.val, k.2.2.1.val, axisExponent k.2.2.2)

private theorem rectExponents_injective (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Function.Injective (rectExponents (h := h) (s := s) (W := W) (U := U)) := by
  rintro ⟨q, j, a, b⟩ ⟨q', j', a', b'⟩ he
  obtain ⟨hj, hi, ha, hb⟩ : j.val = j'.val ∧ q.val - j.val = q'.val - j'.val ∧
      a.val = a'.val ∧ axisExponent b = axisExponent b' := by simpa [rectExponents] using he
  have hqj := (Nat.le_of_lt_succ j.isLt).trans (min_le_left _ _)
  have hq'j' := (Nat.le_of_lt_succ j'.isLt).trans (min_le_left _ _)
  have hq : q = q' := Fin.ext (by omega)
  subst q'
  have hje : j = j' := Fin.ext hj
  subst j'
  have hae : a = a' := Fin.ext ha
  subst a'
  have hbe := axisExponent_injective U hb
  subst b'
  rfl

private theorem rectExponents_exists {h : ℕ} {s : Shape} {W j i a : ℕ}
    {U : Fin 2 → ℕ} {e : Fin 2 →₀ ℕ} (hE : trueEligible h s W j i a e)
    (hU : ∀ z, e z ≤ U z) : ∃ k : RectIndex h s W U, rectExponents k = (j, i, a, e) := by
  obtain ⟨hq, hj, _, ha⟩ := hE
  obtain ⟨b, hb⟩ := exists_axisIndex e hU
  let q : Fin (s.B + 1) := ⟨i + j, by omega⟩
  let v : Fin (min q.val s.J + 1) := ⟨j, Nat.lt_succ_of_le (le_min (by dsimp [q]; omega) hj)⟩
  let x : Fin (trueWidth h s W q.val v.val) := ⟨a, (lt_trueWidth_iff h s W _ _ _).mpr ha⟩
  exact ⟨⟨q, v, x, b⟩, by simp [rectExponents, q, v, x, hb]⟩

private def rectMonomial {h : ℕ} {s : Shape} {W : ℕ} {U : Fin 2 → ℕ}
    (hbox : U 0 + U 1 ≤ s.U) (k : RectIndex h s W U) : rectAmbient h s W U := by
  refine ⟨monomialAt (rectExponents k), ?_, ?_⟩
  · intro j i a e he
    rw [coeffAt_monomialAt (rectExponents k) (j,i,a,e), ite_eq_right]
    intro hEq
    apply he
    change trueEligible h s W (j,i,a,e).1 (j,i,a,e).2.1 (j,i,a,e).2.2.1 (j,i,a,e).2.2.2
    rw [← hEq]
    rcases k with ⟨q, v, x, b⟩
    have hq := q.isLt
    have hv := v.isLt
    have hvq := min_le_left q.val s.J
    have hvJ := min_le_right q.val s.J
    have hvq' : q.val - v.val + v.val = q.val := by omega
    have hboxv := Nat.add_le_add (Nat.le_of_lt_succ (b 0).isLt) (Nat.le_of_lt_succ (b 1).isLt)
    simp only [rectExponents, trueEligible, hvq', seedWeight_eq, axisExponent_apply]
    exact ⟨by omega, by omega, hboxv.trans hbox, (lt_trueWidth_iff h s W _ _ _).mp x.isLt⟩
  · intro j i a e hz z
    change coeffAt _ j i a e ≠ 0 at hz
    rw [coeffAt_monomialAt (rectExponents k) (j,i,a,e)] at hz
    split_ifs at hz with he
    · change (j,i,a,e).2.2.2 z ≤ U z
      rw [← he]
      exact Nat.le_of_lt_succ (k.2.2.2 z).isLt
    · exact (hz rfl).elim

private def rectCoordinates (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    rectAmbient h s W U →ₗ[L] (RectIndex h s W U → L) where
  toFun P k := coeffAt P (rectExponents k).1 (rectExponents k).2.1
    (rectExponents k).2.2.1 (rectExponents k).2.2.2
  map_add' P Q := by funext k; simp [coeffAt]
  map_smul' c P := by funext k; simp [coeffAt, Polynomial.coeff_smul]

private def rectCoordinateEquiv (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hbox : U 0 + U 1 ≤ s.U) : rectAmbient h s W U ≃ₗ[L] (RectIndex h s W U → L) := by
  classical
  refine LinearEquiv.ofBijective (rectCoordinates h s W U) ⟨?_, ?_⟩
  · intro P Q hPQ
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro a
    apply MvPolynomial.ext
    intro e
    change coeffAt P j i a e = coeffAt Q j i a e
    by_cases he : trueEligible h s W j i a e
    · by_cases hb : ∀ z, e z ≤ U z
      · obtain ⟨k, hk⟩ := rectExponents_exists he hb
        have hval := congrFun hPQ k
        change coeffAt P (rectExponents k).1 (rectExponents k).2.1 (rectExponents k).2.2.1
          (rectExponents k).2.2.2 = coeffAt Q (rectExponents k).1 (rectExponents k).2.1
            (rectExponents k).2.2.1 (rectExponents k).2.2.2 at hval
        simpa only [hk] using hval
      · have hzero (R : rectAmbient h s W U) : coeffAt R j i a e = 0 := by
          by_contra hne
          exact hb (R.property.2 j i a e hne)
        rw [hzero P, hzero Q]
    · exact (P.property.1 j i a e he).trans (Q.property.1 j i a e he).symm
  · intro f
    refine ⟨∑ k, f k • rectMonomial hbox k, ?_⟩
    funext d
    have hmono (k : RectIndex h s W U) : rectCoordinates h s W U (rectMonomial hbox k) d =
        if k = d then 1 else 0 := by
      change coeffAt (monomialAt (rectExponents k)) (rectExponents d).1 (rectExponents d).2.1
        (rectExponents d).2.2.1 (rectExponents d).2.2.2 = _
      simp only [coeffAt_monomialAt, (rectExponents_injective h s W U).eq_iff]
    rw [map_sum]
    simp [Finset.sum_apply, hmono, mul_ite]

theorem rectAmbient_finrank (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hbox : U 0 + U 1 ≤ s.U) :
    Module.finrank L (rectAmbient h s W U) = area U * shapeSum s (trueWidth h s W) := by
  rw [(rectCoordinateEquiv h s W U hbox).finrank_eq, Module.finrank_pi]
  unfold RectIndex shapeSum
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, axis_card, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  exact Nat.mul_comm _ _

end
end KoalaRect
