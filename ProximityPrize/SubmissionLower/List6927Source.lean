import ProximityPrize.SubmissionLower.Fast013

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

namespace List6927Source

noncomputable section
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

abbrev Jet := (s : Fin 68) × (e2 : Fin (min s.val 9 + 1)) ×
  Fin (min (s.val - e2.val) (20 - 2 * e2.val) + 1)

def e1 (j : Jet) : ℕ := j.2.2.val
def e2 (j : Jet) : ℕ := j.2.1.val
def e0 (j : Jet) : ℕ := j.1.val - e2 j - e1 j
def width (j : Jet) : ℕ := 49 * 180139 - 131072 * j.1.val + e1 j + 2 * e2 j
abbrev SourceIndex := (j : Jet) × Fin (width j)

def columns (i : SourceIndex) : SourceColumn 2 where
  x := i.2.val
  y₀ := e0 i.1
  higher := ![e1 i.1, e2 i.1]

theorem jet_total (j : Jet) : e0 j + e1 j + e2 j = j.1.val := by
  have h2 := j.2.1.isLt
  have h1 := j.2.2.isLt
  simp only [e0, e1, e2]
  omega

theorem jet_order (j : Jet) : e1 j + 2 * e2 j ≤ 20 := by
  have h1 := j.2.2.isLt
  simp only [e1, e2]
  omega

theorem width_lower (j : Jet) : 44987 ≤ width j := by
  have hs := j.1.isLt
  unfold width
  omega

theorem source_weight_lt (i : SourceIndex) :
    i.2.val + 131072 * e0 i.1 + 131071 * e1 i.1 + 131070 * e2 i.1 < 49 * 180139 := by
  have hs := i.1.1.isLt
  have ht := jet_total i.1
  have hx := i.2.isLt
  unfold width at hx
  omega

theorem columns_injective : Function.Injective columns := by
  rintro ⟨⟨sa, ea, fa⟩, xa⟩ ⟨⟨sb, eb, fb⟩, xb⟩ heq
  have hx := congrArg SourceColumn.x heq
  have h0 := congrArg SourceColumn.y₀ heq
  have h1 := congrArg (fun c : SourceColumn 2 ↦ c.higher 0) heq
  have h2 := congrArg (fun c : SourceColumn 2 ↦ c.higher 1) heq
  have hta := jet_total (⟨sa, ea, fa⟩ : Jet)
  have htb := jet_total (⟨sb, eb, fb⟩ : Jet)
  simp only [columns, e0, e1, e2, Matrix.cons_val_zero, Matrix.cons_val_one] at hx h0 h1 h2 hta htb
  have hs : sa = sb := Fin.ext (by omega)
  subst sb
  have he : ea = eb := Fin.ext h2
  subst eb
  have hf : fa = fb := Fin.ext h1
  subst fb
  have hxx : xa = xb := Fin.ext hx
  subst xb
  rfl

theorem columns_y0_le (i : SourceIndex) : (columns i).y₀ ≤ 67 := by
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  change e0 i.1 ≤ 67
  omega

theorem columns_total_le (i : SourceIndex) : totalJetDegree (columns i).exponent ≤ 67 := by
  rw [SourceColumn.totalJetDegree_exponent]
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  simp [columns, Fin.sum_univ_two]
  omega

theorem columns_weight_lt (i : SourceIndex) :
    Finsupp.weight (differentialWeight 131072) (columns i).exponent < 49 * 180139 := by
  simpa [SourceColumn.weight_exponent, columns, differentialWeight, Fin.sum_univ_two,
    Nat.add_assoc, Nat.mul_comm] using
    source_weight_lt i

def sourceTotal : ℕ := ∑ j : Jet, width j

theorem jet_count : Fintype.card Jet = 6960 := by decide +kernel
theorem source_total : sourceTotal = 26471237490 := by decide +kernel

/-- Cardinality is a sum over7194 jet triples, never an enumeration of the
26471237490-dimensional full source index. -/
theorem source_card : Fintype.card SourceIndex = 26471237490 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact source_total


theorem jet_top (j : Jet) : e2 j ≤ 9 := by
  have h := j.2.1.isLt
  unfold e2
  omega

def Eligible (x a b c : ℕ) : Prop :=
  a + b + c ≤ 67 ∧ b + 2 * c ≤ 20 ∧ c ≤ 9 ∧
    x + 131072 * a + 131071 * b + 131070 * c < 49 * 180139

theorem columns_eligible (i : SourceIndex) :
    Eligible (columns i).x (columns i).y₀ ((columns i).higher 0) ((columns i).higher 1) := by
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  have ho := jet_order i.1
  have hw := source_weight_lt i
  have htop := jet_top i.1
  simp only [Eligible, columns, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- Every monomial in the stated finite weighted support has an index in the
actual Sigma-Fin source family; no monomials are lost by the indexing scheme. -/
theorem index_of_eligible (x a b c : ℕ) (h : Eligible x a b c) :
    ∃ i : SourceIndex, columns i = { x := x, y₀ := a, higher := ![b,c] } := by
  obtain ⟨htotal, horder, htop, hweight⟩ := h
  let s : Fin 68 := ⟨a + b + c, by omega⟩
  let f2 : Fin (min s.val 9 + 1) := ⟨c, by dsimp [s]; omega⟩
  let f1 : Fin (min (s.val - f2.val) (20 - 2 * f2.val) + 1) :=
    ⟨b, by dsimp [s, f2]; omega⟩
  let j : Jet := ⟨s, f2, f1⟩
  have h0 : e0 j = a := by dsimp [e0, e1, e2, j, s, f1, f2]; omega
  have h1 : e1 j = b := rfl
  have h2 : e2 j = c := rfl
  have hx : x < width j := by dsimp [width, e1, e2, j, s, f1, f2]; omega
  refine ⟨⟨j, ⟨x, hx⟩⟩, ?_⟩
  change { x := x, y₀ := e0 j, higher := ![e1 j,e2 j] } =
    ({ x := x, y₀ := a, higher := ![b,c] } : SourceColumn 2)
  rw [h0, h1, h2]


section Translation
variable {F : Type*} [Field F]
def sourceOrderWeight : JetVariable 2 → ℕ
  | none => 0
  | some j => j.val

def sourceTopWeight : JetVariable 2 → ℕ :=
  fun i => i.elim 0 (Pi.single (2 : Fin 3) (1 : ℕ))

def sourceSpan (F : Type*) [Field F] : Submodule F (DifferentialPolynomial F 2) :=
  Submodule.span F (Set.range fun i : SourceIndex ↦ (columns i).polynomial)

def sourceBand (F : Type*) [Field F] : Submodule F (DifferentialPolynomial F 2) :=
  restrictWeightAtMost (R := F) (differentialWeight 131072) 8826810 ⊓
    (restrictWeightAtMost (R := F) jetDegreeWeight 67 ⊓
      (restrictWeightAtMost (R := F) sourceOrderWeight 20 ⊓
        restrictWeightAtMost (R := F) sourceTopWeight 9))

theorem column_mem_band (i : SourceIndex) : (columns i).polynomial ∈ sourceBand F := by
  classical
  have hs : ∀ u ∈ ((columns i).polynomial : DifferentialPolynomial F 2).support,
      u = (columns i).exponent := by
    intro u hu
    exact Finset.mem_singleton.mp (support_monomial_subset hu)
  refine ⟨?_,?_,?_,?_⟩
  · apply mem_restrictWeightAtMost.mpr
    intro u hu
    rw [hs u hu]
    have h := columns_weight_lt i
    omega
  · apply mem_restrictWeightAtMost.mpr
    intro u hu
    rw [hs u hu]
    exact columns_total_le i
  · apply mem_restrictWeightAtMost.mpr
    intro u hu
    rw [hs u hu]
    simpa [SourceColumn.weight_exponent, columns, sourceOrderWeight, Fin.sum_univ_two,
      Nat.mul_comm] using jet_order i.1

  · apply mem_restrictWeightAtMost.mpr
    intro u hu
    rw [hs u hu]
    simpa [SourceColumn.weight_exponent, columns, sourceTopWeight, Fin.sum_univ_two]
      using jet_top i.1

theorem sourceSpan_le_band : sourceSpan F ≤ sourceBand F := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact column_mem_band i

theorem mem_sourceSpan_of_band (Q : DifferentialPolynomial F 2) (hQ : Q ∈ sourceBand F) :
    Q ∈ sourceSpan F := by
  classical
  rw [Q.as_sum]
  apply Submodule.sum_mem
  intro u hu
  let c := SourceColumn.ofExponent u
  have he : c.exponent = u := SourceColumn.exponent_ofExponent u
  have hr := mem_restrictWeightAtMost.mp hQ.1 u hu
  have ht := mem_restrictWeightAtMost.mp hQ.2.1 u hu
  have ho := mem_restrictWeightAtMost.mp hQ.2.2.1 u hu
  have htop := mem_restrictWeightAtMost.mp hQ.2.2.2 u hu
  rw [← he] at hr ht ho htop
  have heligible : Eligible c.x c.y₀ (c.higher 0) (c.higher 1) := by
    simp [SourceColumn.weight_exponent, differentialWeight, jetDegreeWeight,
      sourceOrderWeight, sourceTopWeight, Fin.sum_univ_succ, Nat.mul_comm] at hr ht ho htop
    unfold Eligible
    omega
  obtain ⟨i,hi⟩ := index_of_eligible c.x c.y₀ (c.higher 0) (c.higher 1) heligible
  have hc : ({x := c.x, y₀ := c.y₀, higher := ![c.higher 0,c.higher 1]} : SourceColumn 2) = c := by
    apply SourceColumn.exponent_injective
    ext v
    rcases v with _ | j
    · simp
    · fin_cases j <;> simp [SourceColumn.exponent, Fin.sum_univ_two]
  have hexp : (columns i).exponent = u := by rw [hi, hc]; exact he
  have hgen : ((columns i).polynomial : DifferentialPolynomial F 2) ∈ sourceSpan F :=
    Submodule.subset_span ⟨i,rfl⟩
  have hmono : monomial u (Q.coeff u) = Q.coeff u • (columns i).polynomial := by
    simp [SourceColumn.polynomial, hexp, smul_monomial, smul_eq_mul]
  rw [hmono]
  exact (sourceSpan F).smul_mem _ hgen

/-- Point translation genuinely preserves the full finite source span. -/
theorem sourceSpan_translation (center received : F) (Q : DifferentialPolynomial F 2)
    (hQ : Q ∈ sourceSpan F) : globalPointTranslation center received Q ∈ sourceSpan F := by
  apply mem_sourceSpan_of_band
  have hb := sourceSpan_le_band hQ
  refine ⟨?_,?_,?_,?_⟩
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.1
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.2.1
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.2.2.1
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _) (by exact Nat.zero_le _)
      center received hb.2.2.2

def pointMatrix (m : ℕ) (center received : F) : Matrix (LowContactIndex 2 m) SourceIndex F :=
  fun row i ↦ localConstraintCoordinatesAt m center received (columns i).polynomial row

theorem coordinates_translation (m : ℕ) (center received : F) (Q : DifferentialPolynomial F 2) :
    localConstraintCoordinatesAt m center received Q =
      localConstraintCoordinatesAt m 0 0 (globalPointTranslation center received Q) := by
  have he : unscaledLocalSubstitution 2 0 0 (globalPointTranslation center received Q) =
      unscaledLocalSubstitution 2 center received Q := by
    change ((unscaledLocalSubstitution 2 0 0).comp (globalPointTranslation center received)) Q = _
    rw [unscaledLocalSubstitution_comp_globalPointTranslation]
    simp
  ext row
  change (unscaledLocalSubstitution 2 center received Q).coeff row.val =
    (unscaledLocalSubstitution 2 0 0 (globalPointTranslation center received Q)).coeff row.val
  rw [he]

/-- Local rank at arbitrary center/value is at most the origin rank, with
the actual source family and coefficient maps, over every coefficient field. -/
theorem point_rank_le_origin (m : ℕ) (center received : F) :
    (pointMatrix m center received).rank ≤ (pointMatrix (F := F) m 0 0).rank := by
  classical
  let L := localConstraintCoordinatesAt (R := F) (d := 2) m 0 0
  have hmap : (sourceSpan F).map L =
      Submodule.span F (Set.range (pointMatrix (F := F) m 0 0).col) := by
    rw [sourceSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan : Submodule.span F (Set.range (pointMatrix m center received).col) ≤
      Submodule.span F (Set.range (pointMatrix (F := F) m 0 0).col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [← hmap]
    refine ⟨globalPointTranslation center received (columns i).polynomial,
      sourceSpan_translation center received _ (Submodule.subset_span ⟨i,rfl⟩), ?_⟩
    exact (coordinates_translation m center received (columns i).polynomial).symm
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (pointMatrix (F := F) m 0 0).col)
  exact Submodule.finrank_mono hspan

end Translation

section Grading
open Sol1.C42 (sourceBalance localBalance origin_constraint_balance)
variable {R : Type*} [CommRing R]
theorem column_balance (i : SourceIndex) :
    ((columns i).polynomial : DifferentialPolynomial R 2).IsWeightedHomogeneous sourceBalance
      ((i.2.val : ℤ) - e1 i.1 - 2 * e2 i.1) := by
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  have h := sourceMonomial_isWeightedHomogeneous (R := R) sourceBalance
    (columns i).x (columns i).y₀ (columns i).higher
  convert h using 1
  simp [sourceBalance, columns, Fin.sum_univ_two]
  ring

/-- Actual low-contact coefficients vanish off the source g block. -/
theorem origin_coefficient_zero_of_balance_ne
    (m : ℕ) (i : SourceIndex) (row : LocalVariable 2 →₀ ℕ)
    (hne : row.weight localBalance ≠ (i.2.val : ℤ) - e1 i.1 - 2 * e2 i.1) :
    (localConstraintAt (R := R) m 0 0 (columns i).polynomial).coeff row = 0 :=
  (origin_constraint_balance m (column_balance i)).coeff_eq_zero row hne

theorem column_jet_homogeneous (i : SourceIndex) :
    ((columns i).polynomial : DifferentialPolynomial R 2).IsWeightedHomogeneous
      jetDegreeWeight i.1.1.val := by
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  have h := sourceMonomial_isWeightedHomogeneous_jetDegreeWeight (R := R)
    (columns i).x (columns i).y₀ (columns i).higher
  have hdegree : (columns i).y₀ + ∑ j, (columns i).higher j = i.1.1.val := by
    simpa [columns, Fin.sum_univ_two, Nat.add_assoc] using jet_total i.1
  rw [hdegree] at h
  exact h

theorem origin_coefficient_zero_of_jet_ne
    (m : ℕ) (i : SourceIndex) (row : LocalVariable 2 →₀ ℕ)
    (hne : row.weight (localJetDegreeWeight 2) ≠ i.1.1.val) :
    (localConstraintAt (R := R) m 0 0 (columns i).polynomial).coeff row = 0 :=
  (localConstraintAt_isWeightedHomogeneous 0 (column_jet_homogeneous i)).coeff_eq_zero row hne

/-- High global X powers are actually killed by the origin contact map. -/
theorem origin_high_X_zero (m : ℕ) (i : SourceIndex) (hlarge : m ≤ (columns i).x) :
    localConstraintAt (R := R) m 0 0 (columns i).polynomial = 0 := by
  have hsource : (MvPolynomial.X (none : JetVariable 2) : DifferentialPolynomial R 2) ^ (columns i).x ∣
      (columns i).polynomial := by
    rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hmap := map_dvd (unscaledLocalSubstitution 2 (0 : R) 0).toRingHom hsource
  change unscaledLocalSubstitution 2 0 0
      ((MvPolynomial.X (none : JetVariable 2)) ^ (columns i).x) ∣
    unscaledLocalSubstitution 2 0 0 (columns i).polynomial at hmap
  simp only [map_pow, unscaledLocalSubstitution_X, MvPolynomial.C_0, zero_add] at hmap
  obtain ⟨G, hG⟩ := hmap
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, weightedTruncation_eq_zero_iff, hG]
  have hT := pow_mem_restrictWeightedOrder (R := R)
    (X_mem_restrictWeightedOrder (localContactWeight 2) (localT 2) le_rfl) (columns i).x
  have hrest : G ∈ restrictWeightedOrder (localContactWeight 2) 0 := by simp
  refine restrictWeightedOrder_anti _ ?_ (mul_mem_restrictWeightedOrder hT hrest)
  simpa only [localContactWeight_T, add_zero, one_mul, mul_one] using hlarge

end Grading

theorem columns_weight147 (i : SourceIndex) :
    Finsupp.weight (Astra7.jetWeight 1 4 3) (columns i).exponent ≤ 147 := by
  rw [SourceColumn.weight_exponent]
  have ht := jet_total i.1
  have ho := jet_order i.1
  have hs := i.1.1.isLt
  simp only [columns, Astra7.jetWeight, Option.elim_none, Option.elim_some,
    smul_eq_mul, mul_zero, zero_add, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one, Fin.val_succ]
  omega

end
end List6927Source
