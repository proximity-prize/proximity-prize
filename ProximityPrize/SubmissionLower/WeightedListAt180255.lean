import ProximityPrize.SubmissionLower.Fast013
set_option Elab.async false

/-! Weighted list chain at the 6916 agreement A = 180255 (UNBUILT).
Copied from 12b4b15d (Fast002/008/010/012/013 sections) by research/proximity-6916/port_weighted_list.py:
literals by meaning (180265->180255, 49193->49183 = A-k+1, 49194->49184, 81879->81889),
namespaces Sol1.C42/C52/C57 -> Sol1A.*, Astra7 -> Astra7A, non-ported references qualified to the
official declarations, recomputed facts (list_constants_at.py, which first reproduces every
official value): weightedListCap = 31924061854636696, source total 27309691024 (surplus 15257744).
`chartBound 2 1 4 148 131073 262146 = 36962583` is A-free (Fast012.lean:38). The value of
`dimensionSensitiveIncidenceProduct` (ArkLib, not vendored) at A = 180255 is the inferred
131072/49183, 131073/49184 pattern; `incidence_one/two` check it by norm_num. -/

section PackSource_C42ConsumerArithmetic
set_option autoImplicit true
/-! Exact native arithmetic for the WRITTEN C40 consumer.
These identities do not assert that the consumer inequality has been proved. -/
namespace Sol1A.C42

def listCap : ℕ := 123986085283480091
def I1 : ℚ := 131072 / 49183
def I2 : ℚ := I1 * (131073 / 49184)
def b (v : ℕ) : ℕ := 1 + 2 * 131073 * (v - 1)
def firstOrderCharge (h : ℕ) : ℚ := I1 * h * b h + (h : ℚ) * (h - 1)
def secondOrderCharge (nu : ℕ) : ℚ := I2 * nu * (b nu : ℚ) ^ 2 + firstOrderCharge (nu ^ 2)

theorem consumer_exact : secondOrderCharge 64 =
    (9372637731148505796448256 : ℚ) / 75594271 := by
  norm_num [secondOrderCharge, firstOrderCharge, I2, I1, b]

theorem consumer_le_cap : secondOrderCharge 64 ≤ (listCap : ℚ) := by
  rw [consumer_exact]
  norm_num [listCap]

theorem cap_sub_one_lt_consumer : (listCap : ℚ) - 1 < secondOrderCharge 64 := by
  rw [consumer_exact]
  norm_num [listCap]

theorem listCap_lt_seven_n_cubed : listCap < 7 * 262144 ^ 3 := by norm_num [listCap]
theorem listCap_gap : listCap + 2114704282893797 = 7 * 262144 ^ 3 := by norm_num [listCap]
theorem characteristic_guard : max (131072 : ℕ) (64 ^ 2) < 2130706433 := by norm_num
theorem complete_local_X_blocks : (48 : ℕ) * 180255 - 131072 * 64 = 263632 := by norm_num
theorem complete_local_X_blocks_ge : (48 : ℕ) ≤ 48 * 180255 - 131072 * 64 := by norm_num
theorem radius_agreement_sum : (81889 : ℕ) + 180255 = 262144 := by norm_num

theorem integer_count_le_cap {M : ℕ} (h : (M : ℚ) ≤ secondOrderCharge 64) : M ≤ listCap := by
  exact_mod_cast h.trans consumer_le_cap


end Sol1A.C42
end PackSource_C42ConsumerArithmetic

section PackSource_C42SourceArithmetic
set_option autoImplicit true
/-! Exact finite source indexing and closed combinatorial arithmetic for C42.
The closed block formulas are not, by themselves, a proof about the polynomial
constraint map's support or rank; that remaining bridge is kept separate. -/

namespace Sol1A.C42

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
open ReedSolomon.HiddenDerivative PolynomialDifferential

abbrev Jet := (s : Fin 65) × (e2 : Fin (min s.val 10 + 1)) ×
  Fin (min (s.val - e2.val) (21 - 2 * e2.val) + 1)

def e1 (j : Jet) : ℕ := j.2.2.val
def e2 (j : Jet) : ℕ := j.2.1.val
def e0 (j : Jet) : ℕ := j.1.val - e2 j - e1 j
def width (j : Jet) : ℕ := 48 * 180255 - 131072 * j.1.val + e1 j + 2 * e2 j
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

theorem jet_order (j : Jet) : e1 j + 2 * e2 j ≤ 21 := by
  have h1 := j.2.2.isLt
  simp only [e1, e2]
  omega

theorem width_lower (j : Jet) : 263632 ≤ width j := by
  have hs := j.1.isLt
  unfold width
  omega

theorem source_weight_lt (i : SourceIndex) :
    i.2.val + 131072 * e0 i.1 + 131071 * e1 i.1 + 131070 * e2 i.1 < 48 * 180255 := by
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

theorem columns_y0_le (i : SourceIndex) : (columns i).y₀ ≤ 64 := by
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  change e0 i.1 ≤ 64
  omega

theorem columns_total_le (i : SourceIndex) : totalJetDegree (columns i).exponent ≤ 64 := by
  rw [SourceColumn.totalJetDegree_exponent]
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  simp [columns, Fin.sum_univ_two]
  omega

theorem columns_weight_lt (i : SourceIndex) :
    Finsupp.weight (differentialWeight 131072) (columns i).exponent < 48 * 180255 := by
  simpa [SourceColumn.weight_exponent, columns, differentialWeight, Fin.sum_univ_two,
    Nat.add_assoc, Nat.mul_comm] using
    source_weight_lt i

def sourceTotal : ℕ := ∑ j : Jet, width j

theorem jet_count : Fintype.card Jet = 7194 := by decide +kernel
theorem source_total : sourceTotal = 27309691024 := by decide +kernel

/-- Cardinality is a sum over7194 jet triples, never an enumeration of the
27309691024-dimensional full source index. -/
theorem source_card : Fintype.card SourceIndex = 27309691024 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact source_total


end Sol1A.C42
end PackSource_C42SourceArithmetic

section PackSource_C42SourceClosure
set_option autoImplicit true
/-! Exact source-family coverage/downward closure and the elementary
bounded-derivative-weight interval lemmas behind the closed row formula.
No actual coefficient-map rank bound is asserted here. -/
namespace Sol1A.C42

open ReedSolomon.HiddenDerivative

def Eligible (x a b c : ℕ) : Prop :=
  a + b + c ≤ 64 ∧ b + 2 * c ≤ 21 ∧
    x + 131072 * a + 131071 * b + 131070 * c < 48 * 180255

theorem columns_eligible (i : SourceIndex) :
    Eligible (columns i).x (columns i).y₀ ((columns i).higher 0) ((columns i).higher 1) := by
  have ht := jet_total i.1
  have hs := i.1.1.isLt
  have ho := jet_order i.1
  have hw := source_weight_lt i
  simp only [Eligible, columns, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- Every monomial in the stated finite weighted support has an index in the
actual Sigma-Fin source family; no monomials are lost by the indexing scheme. -/
theorem index_of_eligible (x a b c : ℕ) (h : Eligible x a b c) :
    ∃ i : SourceIndex, columns i = { x := x, y₀ := a, higher := ![b,c] } := by
  obtain ⟨htotal, horder, hweight⟩ := h
  let s : Fin 65 := ⟨a + b + c, by omega⟩
  let f2 : Fin (min s.val 10 + 1) := ⟨c, by dsimp [s]; omega⟩
  let f1 : Fin (min (s.val - f2.val) (21 - 2 * f2.val) + 1) :=
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

theorem eligible_lower_X {x a b c x' : ℕ} (h : Eligible x a b c) (hx : x' ≤ x) :
    Eligible x' a b c := by unfold Eligible at *; omega

theorem eligible_lower_Y0 {x a b c a' : ℕ} (h : Eligible x a b c) (ha : a' ≤ a) :
    Eligible x a' b c := by unfold Eligible at *; omega

/-- The complete interval supplied by [0,c]+2[0,d] when c>=1. -/
theorem bounded_jet_weight_iff (c d w : ℕ) (hc : 1 ≤ c) :
    (∃ a b : ℕ, a ≤ c ∧ b ≤ d ∧ a + 2 * b = w) ↔ w ≤ c + 2 * d := by
  constructor
  · rintro ⟨a,b,ha,hb,heq⟩
    omega
  · intro hw
    by_cases hsmall : w ≤ 2 * d
    · refine ⟨w % 2, w / 2, ?_, ?_, ?_⟩ <;> omega
    · refine ⟨w - 2 * d, d, ?_, le_rfl, ?_⟩ <;> omega

theorem bounded_even_weight_iff (d w : ℕ) :
    (∃ b : ℕ, b ≤ d ∧ 2 * b = w) ↔ w % 2 = 0 ∧ w ≤ 2 * d := by
  constructor
  · rintro ⟨b,hb,heq⟩
    omega
  · rintro ⟨heven,hw⟩
    exact ⟨w / 2, by omega, by omega⟩

/-- Nonempty intersection with the reachable derivative-weight interval. -/
theorem derivative_interval_iff (c d lo hi : ℕ) (hc : 1 ≤ c) :
    (∃ a b : ℕ, a ≤ c ∧ b ≤ d ∧ lo ≤ a + 2 * b ∧ a + 2 * b ≤ hi) ↔
      lo ≤ hi ∧ lo ≤ c + 2 * d := by
  constructor
  · rintro ⟨a,b,ha,hb,hl,hh⟩
    omega
  · rintro ⟨hlh,hl⟩
    obtain ⟨a,b,ha,hb,heq⟩ := (bounded_jet_weight_iff c d lo hc).mpr hl
    exact ⟨a,b,ha,hb,by omega,by omega⟩

/-- The c=0 parity exception uses the first even integer above lo. -/
theorem even_interval_iff (d lo hi : ℕ) :
    (∃ b : ℕ, b ≤ d ∧ lo ≤ 2 * b ∧ 2 * b ≤ hi) ↔
      2 * ((lo + 1) / 2) ≤ min hi (2 * d) := by
  constructor
  · rintro ⟨b,hb,hlo,hhi⟩
    omega
  · intro h
    exact ⟨(lo + 1) / 2, by omega, by omega, by omega⟩

def ReachableDerivativeChoice (c f : ℕ) (g : ℤ) : Prop :=
  ∃ a d : ℕ, a ≤ c ∧ d ≤ f ∧ 0 ≤ g + a + 2 * d ∧
    g + a + 2 * d < 48 ∧ a + 2 * d ≤ 21

/-- When c>=1, the original bounded source derivative exponents exist
exactly under the interval criterion used by the row-count formula. -/
theorem reachable_derivative_choice_iff (c f : ℕ) (g : ℤ) (hc : 1 ≤ c) :
    ReachableDerivativeChoice c f g ↔
      max 0 (-g) ≤ min 21 (47 - g) ∧ max 0 (-g) ≤ (c : ℤ) + 2 * f := by
  constructor
  · rintro ⟨a,d,ha,hd,hzero,hsmall,hord⟩
    omega
  · rintro ⟨hinterval,hbound⟩
    let lo : ℤ := max 0 (-g)
    let hi : ℤ := min 21 (47 - g)
    have hlo : 0 ≤ lo := by dsimp [lo]; omega
    have hhi : 0 ≤ hi := by dsimp [lo,hi] at *; omega
    have hnat : lo.toNat ≤ hi.toNat ∧ lo.toNat ≤ c + 2 * f := by
      dsimp [lo,hi] at *
      omega
    obtain ⟨a,d,ha,hd,hl,hu⟩ := (derivative_interval_iff c f lo.toNat hi.toNat hc).mpr hnat
    refine ⟨a,d,ha,hd,?_,?_,?_⟩ <;> dsimp [lo,hi] at * <;> omega

/-- The c=0 boundary is exactly the even-weight exception. -/
theorem reachable_even_choice_iff (f : ℕ) (g : ℤ) :
    ReachableDerivativeChoice 0 f g ↔
      max 0 (-g) ≤ min 21 (47 - g) ∧
        2 * ((max 0 (-g) + 1) / 2) ≤ min (min 21 (47 - g)) (2 * (f : ℤ)) := by
  constructor
  · rintro ⟨a,d,ha,hd,hzero,hsmall,hord⟩
    omega
  · rintro ⟨hinterval,hbound⟩
    let lo : ℤ := max 0 (-g)
    let hi : ℤ := min 21 (47 - g)
    have hlo : 0 ≤ lo := by dsimp [lo]; omega
    have hhi : 0 ≤ hi := by dsimp [lo,hi] at *; omega
    have hnat : 2 * ((lo.toNat + 1) / 2) ≤ min hi.toNat (2 * f) := by
      dsimp [lo,hi] at *
      omega
    obtain ⟨d,hd,hl,hu⟩ := (even_interval_iff f lo.toNat hi.toNat).mpr hnat
    refine ⟨0,d,by omega,hd,?_,?_,?_⟩ <;> dsimp [lo,hi] at * <;> omega


end Sol1A.C42
end PackSource_C42SourceClosure

section PackSource_C42OriginGrading
set_option autoImplicit true
/-! Actual origin coefficient-map preservation of the second block grading g.
Together with the pinned total-jet grading this gives the off-block zeros;
full finite support/reindexing and uniform-rank transport remain separate. -/
namespace Sol1A.C42

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
variable {R : Type*} [CommRing R]

def sourceBalance : JetVariable 2 → ℤ
  | none => 1
  | some j => -(j.val : ℤ)

def localBalance : LocalVariable 2 → ℤ
  | none => 1
  | some none => -1
  | some (some j) => -((j.val : ℤ) + 1)

theorem localCorrection_balance :
    (localCorrection (R := R) 2).IsWeightedHomogeneous localBalance 0 := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hC := isWeightedHomogeneous_C localBalance ((-1 : R) ^ j.val)
  have hT := (isWeightedHomogeneous_X R localBalance (localT 2)).pow (j.val + 1)
  have hY := isWeightedHomogeneous_X R localBalance (localY j)
  simpa [localBalance, localT, localY, nsmul_eq_mul] using (hC.mul hT).mul hY

theorem origin_image_balance (v : JetVariable 2) :
    (unscaledLocalImage 2 (0 : R) 0 v).IsWeightedHomogeneous localBalance (sourceBalance v) := by
  have hX := isWeightedHomogeneous_X R localBalance
  rcases v with _ | j
  · simpa [unscaledLocalImage, sourceBalance, localBalance, localT] using hX (localT 2)
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · have hTE : (X (localT 2) * X (localE 2) : LocalPolynomial R 2).IsWeightedHomogeneous
          localBalance 0 := by
        simpa [localBalance, localT, localE, localAux] using (hX (localT 2)).mul (hX (localE 2))
      simpa [unscaledLocalImage, sourceBalance] using localCorrection_balance.add hTE
    · simpa [unscaledLocalImage, sourceBalance, localBalance, localY] using hX (localY i)

theorem origin_substitution_balance {Q : DifferentialPolynomial R 2} {g : ℤ}
    (hQ : Q.IsWeightedHomogeneous sourceBalance g) :
    (unscaledLocalSubstitution 2 0 0 Q).IsWeightedHomogeneous localBalance g :=
  hQ.bind₁ origin_image_balance

theorem origin_constraint_balance (m : ℕ) {Q : DifferentialPolynomial R 2} {g : ℤ}
    (hQ : Q.IsWeightedHomogeneous sourceBalance g) :
    (localConstraintAt m 0 0 Q).IsWeightedHomogeneous localBalance g :=
  (origin_substitution_balance hQ).weightedTruncation _ m

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
  have hsource : (X (none : JetVariable 2) : DifferentialPolynomial R 2) ^ (columns i).x ∣
      (columns i).polynomial := by
    rw [SourceColumn.polynomial_eq_sourceMonomial, sourceMonomial]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hmap := map_dvd (unscaledLocalSubstitution 2 (0 : R) 0).toRingHom hsource
  change unscaledLocalSubstitution 2 0 0
      ((X (none : JetVariable 2)) ^ (columns i).x) ∣
    unscaledLocalSubstitution 2 0 0 (columns i).polynomial at hmap
  simp only [map_pow, unscaledLocalSubstitution_X, C_0, zero_add] at hmap
  obtain ⟨G, hG⟩ := hmap
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, weightedTruncation_eq_zero_iff, hG]
  have hT := pow_mem_restrictWeightedOrder (R := R)
    (X_mem_restrictWeightedOrder (localContactWeight 2) (localT 2) le_rfl) (columns i).x
  have hrest : G ∈ restrictWeightedOrder (localContactWeight 2) 0 := by simp
  refine restrictWeightedOrder_anti _ ?_ (mul_mem_restrictWeightedOrder hT hrest)
  simpa only [localContactWeight_T, add_zero, one_mul, mul_one] using hlarge


end Sol1A.C42
end PackSource_C42OriginGrading

section PackSource_C42TranslationRank
set_option autoImplicit true
/-! Uniform point-rank transport on the ACTUAL C42 source span.
This does not prove the numerical origin rank bound. -/
namespace Sol1A.C42

noncomputable section
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
variable {F : Type*} [Field F]

def sourceOrderWeight : JetVariable 2 → ℕ
  | none => 0
  | some j => j.val

def sourceSpan (F : Type*) [Field F] : Submodule F (DifferentialPolynomial F 2) :=
  Submodule.span F (Set.range fun i : SourceIndex ↦ (columns i).polynomial)

def sourceBand (F : Type*) [Field F] : Submodule F (DifferentialPolynomial F 2) :=
  restrictWeightAtMost (R := F) (differentialWeight 131072) 8652239 ⊓
    (restrictWeightAtMost (R := F) jetDegreeWeight 64 ⊓
      restrictWeightAtMost (R := F) sourceOrderWeight 21)

theorem column_mem_band (i : SourceIndex) : (columns i).polynomial ∈ sourceBand F := by
  classical
  have hs : ∀ u ∈ ((columns i).polynomial : DifferentialPolynomial F 2).support,
      u = (columns i).exponent := by
    intro u hu
    exact Finset.mem_singleton.mp (support_monomial_subset hu)
  refine ⟨?_,?_,?_⟩
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
  have ho := mem_restrictWeightAtMost.mp hQ.2.2 u hu
  rw [← he] at hr ht ho
  have heligible : Eligible c.x c.y₀ (c.higher 0) (c.higher 1) := by
    simp [SourceColumn.weight_exponent, differentialWeight, jetDegreeWeight,
      sourceOrderWeight, Fin.sum_univ_succ, Nat.mul_comm] at hr ht ho
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
  refine ⟨?_,?_,?_⟩
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.1
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.2.1
  · exact globalPointTranslation_mem_restrictWeightAtMost (by exact Nat.zero_le _)
      (by exact Nat.zero_le _) center received hb.2.2

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


end
end Sol1A.C42
end PackSource_C42TranslationRank

section PackSource_C52FiniteOrigin
set_option autoImplicit true
namespace Sol1A.C52
open scoped BigOperators
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1A.C42
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Block := Fin 65 × Fin 69
def balance (q : Block) : ℤ := (q.2.val : ℤ) - 21
abbrev ColFiber (q : Block) :=
  (e : Fin (min q.1.val 10 + 1)) ×
    {a : Fin (min (q.1.val - e.val) (21 - 2 * e.val) + 1) //
      0 ≤ balance q + a.val + 2 * e.val ∧ balance q + a.val + 2 * e.val < 48}
abbrev Col := (q : Block) × ColFiber q

abbrev RowFiber (q : Block) :=
  (b : Fin (q.1.val + 1)) × {f : Fin (q.1.val - b.val + 1) //
    (b.val : ℤ) ≤ balance q + q.1.val + f.val ∧
      balance q + q.1.val + f.val + 2 * b.val < 48}
abbrev Row := (q : Block) × RowFiber q

theorem colFiber_card (q : Block) : Fintype.card (ColFiber q) = Sol1.C42.columnCount q.1.val (balance q) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_subtype]
  rw [← Sol1.C42.sourceBlockFiberCount_eq]
  unfold Sol1.C42.sourceBlockFiberCount
  let f : ℕ → ℕ := fun e ↦ (Finset.univ.filter fun a :
    Fin (min (q.1.val - e) (21 - 2 * e) + 1) ↦
      0 ≤ balance q + a.val + 2 * e ∧ balance q + a.val + 2 * e < 48).card
  change (∑ e : Fin (min q.1.val 10 + 1), f e.val) =
    ∑ e ∈ Finset.range (min q.1.val 10 + 1), f e
  exact Fin.sum_univ_eq_sum_range f _

theorem rowFiber_card (q : Block) : Fintype.card (RowFiber q) =
    Sol1.C52.rowCountEnvelope q.1.val (balance q) := by
  classical
  rw [Fintype.card_sigma]
  unfold Sol1.C52.rowCountEnvelope
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter fun f : Fin (q.1.val - b.val + 1) ↦
      (b.val : ℤ) ≤ balance q + q.1.val + f.val ∧
        balance q + q.1.val + f.val + 2 * b.val < 48) =
      (Finset.univ.filter fun f : Fin (q.1.val - b.val + 1) ↦
        max 0 (-(balance q)) - q.1.val + b.val ≤ (f.val : ℤ) ∧
          (f.val : ℤ) ≤ 48 - balance q - q.1.val - 1 - 2 * b.val) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hb := b.isLt
    have hh := f.isLt
    omega
  rw [hf, Sol1.C42.fin_interval_card]
  have hb := b.isLt
  have hh : ((q.1.val - b.val + 1 : ℕ) : ℤ) - 1 = (q.1.val : ℤ) - b.val := by omega
  rw [hh]

def colOriginal (j : Col) : SourceIndex :=
  let jet : Jet := ⟨j.1.1, j.2.1, j.2.2.1⟩
  ⟨jet, ⟨(balance j.1 + j.2.2.1.val + 2 * j.2.1.val).toNat, by
    have hp := j.2.2.2
    have hw := width_lower jet
    omega⟩⟩

def rowExponent (i : Row) : LocalVariable 2 →₀ ℕ :=
  Finsupp.single (localT 2) (balance i.1 + i.1.1.val + i.2.2.1.val).toNat +
  Finsupp.single (localE 2) i.2.1.val +
  Finsupp.single (localY (0 : Fin 2)) (i.1.1.val - i.2.1.val - i.2.2.1.val) +
  Finsupp.single (localY (1 : Fin 2)) i.2.2.1.val

theorem rowExponent_contact (i : Row) : localContactOrder 2 (rowExponent i) < 48 := by
  have hp := i.2.2.2
  rw [localContactOrder_eq]
  simp [rowExponent, localT, localE, localAux, localY]
  omega

def rowOriginal (i : Row) : LowContactIndex 2 48 := ⟨rowExponent i, rowExponent_contact i⟩

theorem rowExponent_jet (i : Row) :
    (rowExponent i).weight (localJetDegreeWeight 2) = i.1.1.val := by
  have hb := i.2.1.isLt
  have hf := i.2.2.1.isLt
  simp only [rowExponent, map_add, Finsupp.weight_single, localJetDegreeWeight,
    localT, localE, localAux, localY, nsmul_eq_mul, Nat.cast_id, mul_zero, mul_one, zero_add]
  omega

theorem rowExponent_balance (i : Row) : (rowExponent i).weight localBalance = balance i.1 := by
  have hb := i.2.1.isLt
  have hf := i.2.2.1.isLt
  have hp := i.2.2.2
  simp only [rowExponent, map_add, Finsupp.weight_single, localBalance,
    localT, localE, localAux, localY, nsmul_eq_mul]
  omega


theorem row_jet_formula (u : LocalVariable 2 →₀ ℕ) :
    u.weight (localJetDegreeWeight 2) =
      u (localE 2) + u (localY (0 : Fin 2)) + u (localY (1 : Fin 2)) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_two,
    localJetDegreeWeight, localE, localAux, localY, Nat.add_assoc]

theorem row_balance_formula (u : LocalVariable 2 →₀ ℕ) :
    u.weight localBalance = (u (localT 2) : ℤ) - u (localE 2) -
      u (localY (0 : Fin 2)) - 2 * u (localY (1 : Fin 2)) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_two,
    localBalance, localT, localE, localAux, localY]
  ring

theorem colOriginal_grade (j : Col) : (colOriginal j).1.1 = j.1.1 := rfl

theorem colOriginal_balance (j : Col) :
    ((colOriginal j).2.val : ℤ) - e1 (colOriginal j).1 - 2 * e2 (colOriginal j).1 =
      balance j.1 := by
  have hp := j.2.2.2
  simp only [colOriginal, e1, e2]
  omega

theorem low_column_represented (i : SourceIndex) (hx : i.2.val < 48) :
    ∃ j : Col, colOriginal j = i := by
  rcases i with ⟨⟨s,e,a⟩,x⟩
  change x.val < 48 at hx
  have ho := jet_order (⟨s,e,a⟩ : Jet)
  simp only [e1, e2] at ho
  let gi : Fin 69 := ⟨((x.val : ℤ) - a.val - 2 * e.val + 21).toNat, by omega⟩
  let q : Block := ⟨s,gi⟩
  have hgi : balance q = (x.val : ℤ) - a.val - 2 * e.val := by
    dsimp [balance,q,gi]
    omega
  let j : Col := ⟨q,e,⟨a,by rw [hgi]; omega⟩⟩
  refine ⟨j, ?_⟩
  dsimp only [colOriginal, j, q]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Fin.ext
  change (balance q + a.val + 2 * e.val).toNat = x.val
  rw [hgi]
  omega

variable {F : Type*} [Field F]

theorem point_entry_constraint (r : LowContactIndex 2 48) (j : SourceIndex) :
    pointMatrix (F := F) 48 0 0 r j =
      (localConstraintAt 48 0 0 (columns j).polynomial).coeff r.val := by
  change (unscaledLocalSubstitution 2 (0 : F) 0 (columns j).polynomial).coeff r.val = _
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coeff_projectLowContact, ite_eq_left r.property]

theorem high_column_zero (j : SourceIndex) (hx : 48 ≤ j.2.val) :
    (pointMatrix (F := F) 48 0 0).col j = 0 := by
  ext r
  rw [Matrix.col_apply, point_entry_constraint, origin_high_X_zero 48 j hx]
  simp

/-- Every actual nonzero coefficient has a representative in the finite envelope. -/
theorem nonzero_row_represented (r : LowContactIndex 2 48) (j : SourceIndex)
    (hne : pointMatrix (F := F) 48 0 0 r j ≠ 0) :
    ∃ i : Row, rowOriginal i = r := by
  have hx : j.2.val < 48 := by
    by_contra hh
    have hz := high_column_zero (F := F) j (by omega)
    exact hne (congrFun hz r)
  have hs : r.val.weight (localJetDegreeWeight 2) = j.1.1.val := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_jet_ne 48 j r.val hh))
  have hg : r.val.weight localBalance = (j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_balance_ne 48 j r.val hh))
  have he : r.val (localE 2) ≤ r.val (localT 2) := by
    apply localE_le_localT_of_mem_support (0 : F) 0 (columns j).polynomial
    exact mem_support_iff.mpr hne
  have ht := r.property
  rw [localContactOrder_eq] at ht
  have hsj := row_jet_formula r.val
  have hgj := row_balance_formula r.val
  have ho := jet_order j.1
  let gi : Fin 69 := ⟨((j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 + 21).toNat, by omega⟩
  let q : Block := ⟨j.1.1,gi⟩
  have hq : balance q = (j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 := by
    dsimp [balance,q,gi]
    omega
  let b : Fin (q.1.val + 1) := ⟨r.val (localE 2), by dsimp [q]; omega⟩
  let f : Fin (q.1.val - b.val + 1) := ⟨r.val (localY (1 : Fin 2)), by dsimp [q,b]; omega⟩
  have hT : balance q + q.1.val + f.val = (r.val (localT 2) : ℤ) := by
    change balance q + j.1.1.val + (r.val (localY (1 : Fin 2)) : ℤ) = _
    rw [hq]
    omega
  let i : Row := ⟨q,b,⟨f,by rw [hT]; dsimp [b]; omega⟩⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  ext v
  rcases v with _ | (_ | v)
  · change rowExponent i (localT 2) = r.val (localT 2)
    have heval : rowExponent i (localT 2) =
        (balance q + q.1.val + f.val).toNat := by
      simp [rowExponent, localT, localE, localAux, localY, i]
    rw [heval, hT]
    simp
  · change rowExponent i (localE 2) = r.val (localE 2)
    simp [rowExponent, localT, localE, localAux, localY, i,b]
  · fin_cases v
    · change rowExponent i (localY (0 : Fin 2)) = r.val (localY (0 : Fin 2))
      have heval : rowExponent i (localY (0 : Fin 2)) =
          j.1.1.val - r.val (localE 2) - r.val (localY (1 : Fin 2)) := by
        simp [rowExponent, localT, localE, localAux, localY, i,b,f,q]
      rw [heval]
      omega
    · change rowExponent i (localY (1 : Fin 2)) = r.val (localY (1 : Fin 2))
      simp [rowExponent, localT, localE, localAux, localY, i,b,f]

end
end Sol1A.C52
end PackSource_C52FiniteOrigin

section PackSource_C52OriginRank
set_option autoImplicit true
namespace Sol1A.C52
open scoped BigOperators Matrix
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1A.C42
noncomputable section
variable {F : Type*} [Field F]
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finiteMatrix : Matrix Row Col F :=
  (pointMatrix 48 (0 : F) 0).submatrix rowOriginal colOriginal

/-- Actual origin coefficients vanish between different s,g blocks. -/
theorem finiteMatrix_offblock (i : Row) (j : Col) (hne : i.1 ≠ j.1) :
    finiteMatrix (F := F) i j = 0 := by
  rw [finiteMatrix, Matrix.submatrix_apply, point_entry_constraint]
  by_cases hs : i.1.1 = j.1.1
  · apply origin_coefficient_zero_of_balance_ne
    dsimp only [rowOriginal]
    rw [rowExponent_balance, colOriginal_balance]
    intro hbalance
    apply hne
    apply Prod.ext hs
    apply Fin.ext
    unfold balance at hbalance
    omega
  · apply origin_coefficient_zero_of_jet_ne
    dsimp only [rowOriginal]
    rw [rowExponent_jet, colOriginal_grade]
    exact fun h ↦ hs (Fin.ext h)

/-- The finite semantic block matrix has the exact static C42 rank allowance. -/
theorem finiteMatrix_rank : (finiteMatrix (F := F)).rank ≤ Sol1.C42.blockUpper := by
  classical
  apply (Sol1.C52.rank_le_sum_min_dependent (finiteMatrix (F := F)) finiteMatrix_offblock).trans
  simp_rw [rowFiber_card, colFiber_card]
  rw [Fintype.sum_prod_type]
  change (∑ s : Fin 65, ∑ gi : Fin 69,
    min (Sol1.C52.rowCountEnvelope s.val ((gi.val : ℤ) - 21))
      (Sol1.C42.columnCount s.val ((gi.val : ℤ) - 21))) ≤ Sol1.C42.blockUpper
  simp_rw [min_comm]
  exact Sol1.C52.envelope_upper_eq_block.le

/-- Restrict the actual origin columns to X<48 without increasing the rank. -/
theorem origin_rank_le_low_columns :
    (pointMatrix (F := F) 48 0 0).rank ≤
      ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal).rank := by
  apply Sol1.C52.rank_le_col_representatives
  intro j
  by_cases hx : j.2.val < 48
  · obtain ⟨c,hc⟩ := low_column_represented j hx
    exact Or.inr ⟨c,by rw [hc]⟩
  · exact Or.inl (high_column_zero j (by omega))

/-- Every nonzero low-column row is represented by the finite target envelope. -/
theorem low_columns_rank_le_finite :
    ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal).rank ≤
      (finiteMatrix (F := F)).rank := by
  classical
  apply Sol1.C52.rank_le_row_representatives
  intro r
  by_cases hz : ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal) r = 0
  · exact Or.inl hz
  · right
    obtain ⟨c,hc⟩ := Function.ne_iff.mp hz
    have hc' : pointMatrix (F := F) 48 0 0 r (colOriginal c) ≠ 0 := hc
    obtain ⟨i,hi⟩ := nonzero_row_represented r (colOriginal c) hc'
    refine ⟨i, ?_⟩
    exact congrArg (fun r : LowContactIndex 2 48 ↦
      ((pointMatrix (F := F) 48 0 0).submatrix id colOriginal) r) hi.symm

/-- Kernel-checked static origin rank, valid over every coefficient field. -/
theorem origin_rank : (pointMatrix (F := F) 48 0 0).rank ≤ Sol1.C42.blockUpper :=
  origin_rank_le_low_columns.trans (low_columns_rank_le_finite.trans finiteMatrix_rank)

end
end Sol1A.C52
end PackSource_C52OriginRank

section PackSource_WeightedRegularList
set_option autoImplicit true
namespace Astra7A
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

/-- Weighted regular-list bound over the original field, with the entire
algebraic-closure chart construction and finite covering degree discharged. -/
theorem weighted_regular_polynomial_card {r n k A : ℕ}
    (a b V : ℕ) (ha : 0 < a) (hV : a+b*r ≤ V)
    (hchar : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : F) ≠ 0)
    (Q : DifferentialPolynomial F r)
    (hQ : Q.weightedTotalDegree (Astra7.jetWeight a b (r+1)) ≤ V)
    (hrk : r < k) (hkA : k ≤ A)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hbin : ∀ i, r < i → i < k → (i.choose r : F) ≠ 0)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P=0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i => P.eval (domain i)=received i).card) :
    ((S.card * ∏ j : Fin (r+1), (a+b*j.val) : ℕ) : ℚ) ≤ V *
      ((((n-k+1)*Astra7.chartBound r a b V k (2*k) : ℕ) : ℚ) / ((A-k+1 : ℕ) : ℚ)) ^ r := by
  classical
  let E := AlgebraicClosure F
  let f : F →+* E := algebraMap F E
  have hbinE : ∀ i, r < i → i < k → (i.choose r : E) ≠ 0 := by
    intro i hir hik hz
    apply hbin i hir hik
    exact f.injective (by simpa using hz)
  have hcharE : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : E) ≠ 0 := by
    intro j hz
    apply hchar j
    apply f.injective
    rw [map_natCast,map_zero]
    exact hz
  obtain ⟨center,J,hcard,hJ⟩ := exists_regular_solution_jet_family_of_exponent f Q k k (2*k)
    (taylorExponentSufficient_two_mul r k) le_rfl S domain received hdegree hsol hsep hbinE hagree
  let QE := MvPolynomial.map f Q
  have hQE : QE.weightedTotalDegree (Astra7.jetWeight a b (r+1)) ≤ V := by
    apply Finset.sup_le
    intro m hm
    exact (le_weightedTotalDegree _ (MvPolynomial.support_map_subset f Q hm)).trans hQ
  let domainE : Fin n ↪ E := domain.trans ⟨f,f.injective⟩
  have hA : ∀ jet ∈ J, A ≤ {i | aeval jet
      (taylorAgreementEquation center QE k (2*k) (domainE i) (f (received i)))=0}.ncard := by
    intro jet hjet
    have heq : {i | aeval jet (taylorAgreementEquation center QE k (2*k)
        (domainE i) (f (received i)))=0} =
        ((Finset.univ.filter fun i => aeval jet (taylorAgreementEquation center QE k (2*k)
          (f (domain i)) (f (received i)))=0 : Finset (Fin n)) : Set (Fin n)) := by
      ext i
      simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
      rfl
    rw [heq,Set.ncard_coe_finset]
    exact (hJ jet hjet).2.2.2
  have hh := Astra7.weighted_regular_jets_card a b V ha hV hcharE center QE hQE hrk hkA domainE
    (fun i => f (received i)) J (fun jet hjet => ⟨(hJ jet hjet).1,(hJ jet hjet).2.1⟩) hA
  rwa [hcard] at hh

theorem native_choose_two [CharP F 2130706433] (i : ℕ) (hi : 2 < i) (hik : i < 131073) :
    (i.choose 2 : F) ≠ 0 := by
  have hh := natCast_choose_ne_zero_of_ringChar (F := F) (D := 131072) (s := 2)
    (Or.inr (by rw [ringChar.eq F 2130706433]; norm_num)) (i-2) (by omega) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using hh

def weightedRegularCap : ℚ := (148 : ℚ) / 45 *
  (((131072 : ℚ)*36962583)/49183)^2

theorem regular64_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2)
    (hQ : Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148)
    (S : Finset (Polynomial F))
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 2)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180255) :
    (S.card : ℚ) ≤ weightedRegularCap := by
  classical
  have hchar : ∀ j : Fin 3, ((1+4*j.val : ℕ) : F) ≠ 0 := by
    intro j hz
    have hdvd := (CharP.cast_eq_zero_iff F 2130706433 (1+4*j.val)).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have hh := weighted_regular_polynomial_card (r := 2) (n := 262144) (k := 131073) (A := 180255)
    1 4 148 (by decide) (by decide) hchar Q hQ
    (by decide) (by decide) domain received native_choose_two S
    (fun P hP => (hS P hP).2.1) (fun P hP => (hS P hP).1) hsep
    (fun P hP => by
      simpa [ReedSolomon.closePolynomialSet,ReedSolomon.polynomialAgreementSet] using
        (hS P hP).2.2)
  norm_num [Astra7.chartBound,Fin.prod_univ_succ] at hh
  dsimp [weightedRegularCap]
  linarith

end
end Astra7A
end PackSource_WeightedRegularList

section PackSource_C57CountingPrimitives
set_option autoImplicit true
namespace Sol1A.C57
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E]

/-- The pinned order-zero conversion is injective. -/
theorem orderZeroAsPolynomial_injective :
    Function.Injective (orderZeroAsPolynomial (F := E)) := by
  intro Q R h
  apply (MvPolynomial.renameEquiv E orderZeroVariableEquiv).injective
  apply (MvPolynomial.finSuccEquiv E 1).injective
  apply Polynomial.map_injective (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingHom
    (MvPolynomial.uniqueAlgEquiv E (Fin 1)).injective
  exact h

theorem orderZeroAsPolynomial_degree (Q : DifferentialPolynomial E 0) :
    (orderZeroAsPolynomial Q).natDegree = jetTotalDegree Q := by
  have hleft : orderZeroOfPolynomial (orderZeroAsPolynomial Q) = Q := by
    apply orderZeroAsPolynomial_injective
    exact orderZeroAsPolynomial_orderZeroOfPolynomial _
  simpa only [hleft] using (orderZeroOfPolynomial_jetTotalDegree (orderZeroAsPolynomial Q)).symm

/-- The entire ordinary polynomial root family of a nonzero order-zero equation. -/
theorem order_zero_card_le (Q : DifferentialPolynomial E 0) (hQ : Q ≠ 0)
    (S : Finset E[X]) (hroot : ∀ P ∈ S, differentialSpecialization Q P = 0) :
    S.card ≤ jetTotalDegree Q := by
  have hP : orderZeroAsPolynomial Q ≠ 0 := by
    intro hz
    apply hQ
    apply orderZeroAsPolynomial_injective
    simpa only [orderZeroAsPolynomial, map_zero, Polynomial.map_zero] using hz
  have h := Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hP
    (x := id) (s := S) Function.injective_id.injOn
    (fun P hP ↦ (orderZeroAsPolynomial_eval Q P).trans (hroot P hP))
  exact h.trans_eq (orderZeroAsPolynomial_degree Q)

section Native
variable [CharP E 2130706433]

/-- Native dimension-sensitive regular branch, uniformly at any order d<=2. -/
theorem regular_top_card_le (d : ℕ) (hd : d ≤ 2)
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E d) (nu : ℕ)
    (hhighest : highestActiveJet Q = some (Fin.last d)) (hweight : jetTotalDegree Q ≤ nu)
    (S : Finset E[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last d)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180255) :
    (S.card : ℚ) ≤ dimensionSensitiveIncidenceProduct 262144 180255 131073 1 d * nu *
      ((1 + 2 * 131073 * (nu - 1) : ℕ) : ℚ) ^ d := by
  have hactual := finite_actualStage_regularSolutions_card_le_dimensionSensitive Q (Fin.last d)
    hhighest 131073 131073 (by omega) le_rfl domain received (by norm_num) (by norm_num)
    (fun r hr ↦ Sol1.C40Primitives.native_binomial_guard r (hr.trans hd)) S hsep hS
  exact hactual.trans (directJetStageCharge_le_weight_order (Q, Fin.last d)
    262144 180255 131073 131073 nu d (by norm_num) hweight (by simp))

end Native

/-- A positive top degree makes the top variable the computed highest active jet. -/
theorem highestActiveJet_last_of_pos {d : ℕ} (Q : DifferentialPolynomial E d)
    (hpos : 0 < jetDegree Q (Fin.last d)) : highestActiveJet Q = some (Fin.last d) := by
  cases hh : highestActiveJet Q with
  | none =>
    exact False.elim (((highestActiveJet_eq_none_iff Q).mp hh) _ hpos)
  | some j =>
    have hj := isHighestActiveJet_of_highestActiveJet_eq_some hh
    have heq : j = Fin.last d := by
      by_contra hne
      have hlt : j < Fin.last d := lt_of_le_of_ne (Fin.le_last j) hne
      exact hj.2 _ hlt hpos
    exact congrArg some heq

end
end Sol1A.C57
end PackSource_C57CountingPrimitives

section PackSource_C57FirstOrderConsumer
set_option autoImplicit true
namespace Sol1A.C57
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1A.C42
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E] [CharP E 2130706433]

theorem incidence_one : dimensionSensitiveIncidenceProduct 262144 180255 131073 1 1 = I1 := by
  norm_num [dimensionSensitiveIncidenceProduct, I1]
theorem incidence_two : dimensionSensitiveIncidenceProduct 262144 180255 131073 1 2 = I2 := by
  norm_num [dimensionSensitiveIncidenceProduct, I2, I1]

theorem cast_mul_pred (h : ℕ) : ((h * (h - 1) : ℕ) : ℚ) = (h : ℚ) * (h - 1) := by
  cases h with
  | zero => norm_num
  | succ h => simp [Nat.cast_add, Nat.cast_mul]

theorem firstOrderCharge_ge (h : ℕ) : (h : ℚ) ≤ firstOrderCharge h := by
  have hi : (1 : ℚ) ≤ I1 := by norm_num [I1]
  have hI : 0 ≤ I1 := by norm_num [I1]
  have hb : (1 : ℚ) ≤ (b h : ℚ) := by
    exact_mod_cast (by unfold b; omega : 1 ≤ b h)
  have hprod : 0 ≤ (h : ℚ) * (h - 1) := by
    rw [← cast_mul_pred]
    positivity
  have h1 : (h : ℚ) ≤ I1 * h := by nlinarith [Nat.cast_nonneg (α := ℚ) h]
  have h2 : I1 * h ≤ I1 * h * b h :=
    le_mul_of_one_le_right (mul_nonneg hI (Nat.cast_nonneg _)) hb
  exact (h1.trans h2).trans (le_add_of_nonneg_right hprod)

/-- Sharp whole first-order fixed-word consumer, including every singular/lower-order root. -/
theorem first_order_card_le
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E 1) (hQ : Q ≠ 0) (h : ℕ) (hbound : h ≤ 4096)
    (hweight : jetTotalDegree Q ≤ h) (S : Finset E[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180255) :
    (S.card : ℚ) ≤ firstOrderCharge h := by
  classical
  let G := Sol1.C57.regularPart 0 Q
  have hsplit := Sol1.C57.split_weight 0 Q
  have hGweight : jetTotalDegree G ≤ h := by dsimp [G]; omega
  have hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last 1) < ringChar E := by
    right
    rw [ringChar.eq E 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 1)
    omega
  by_cases hb : jetDegree G (Fin.last 1) = 0
  · have hGone : G = 1 := Sol1.C57.regular_eq_one_of_degree_zero 0 Q hb
    have hlow : ∀ P ∈ S, differentialSpecialization (Sol1.C57.lowerPart 0 Q) P = 0 := by
      intro P hP
      rcases Sol1.C57.root_split 0 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P = 0 at hr
        rw [hGone] at hr
        have hz : (1 : E[X]) = 0 := by
          simpa only [differentialSpecialization, map_one] using hr
        exact (one_ne_zero hz).elim
    have hc := order_zero_card_le (Sol1.C57.lowerPart 0 Q) (Sol1.C57.lower_ne_zero 0 Q) S hlow
    have hch : S.card ≤ h := by omega
    exact (by exact_mod_cast hch : (S.card : ℚ) ≤ h).trans (firstOrderCharge_ge h)
  · have hbpos : 0 < jetDegree G (Fin.last 1) := by omega
    let good : E[X] → Prop := fun P ↦ differentialSpecialization G P = 0 ∧
      differentialSpecialization (separant G (Fin.last 1)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P ↦ ¬ good P
    have hreg : (regular.card : ℚ) ≤ I1 * h * b h := by
      have hx := regular_top_card_le 1 (by norm_num) domain received G h
        (highestActiveJet_last_of_pos G hbpos) hGweight regular
        (by intro P hP; exact ((Finset.mem_filter.mp hP).2).2)
        (by
          intro P hP
          have hp := Finset.mem_filter.mp hP
          exact ⟨hp.2.1,(hS P hp.1).2⟩)
      simpa only [incidence_one, pow_one, b] using hx
    let R := Sol1.C57.exceptionalEquation 0 Q
    have hR : R ≠ 0 := Sol1.C57.exceptional_ne_zero 0 Q hchar
    have hRweight : jetTotalDegree R ≤ h * (h - 1) :=
      Sol1.C57.exceptional_weight_sharp 0 Q h hweight
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 1)))
    have hexc : exceptional.card ≤ h * (h - 1) := by
      apply (order_zero_card_le R hR exceptional ?_).trans hRweight
      intro P hP
      have hp := Finset.mem_filter.mp hP
      rcases Sol1.C57.root_regular_or_exceptional 0 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hcard : regular.card + exceptional.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ) = (regular.card : ℚ) + exceptional.card := by exact_mod_cast hcard.symm
      _ ≤ I1 * h * b h + ((h * (h - 1) : ℕ) : ℚ) :=
        add_le_add hreg (by exact_mod_cast hexc)
      _ = firstOrderCharge h := by rw [cast_mul_pred]; rfl

end
end Sol1A.C57
end PackSource_C57FirstOrderConsumer

section PackSource_C42SurplusAt
set_option autoImplicit true
namespace Sol1A.C42

theorem source_surplus : sourceTotal - 262144 * Sol1.C42.blockUpper = 15257744 := by
  rw [source_total, Sol1.C42.block_upper]

theorem strict_source_surplus : 262144 * Sol1.C42.blockUpper < Fintype.card SourceIndex := by
  rw [Sol1.C42.block_upper, source_card]
  norm_num


end Sol1A.C42
end PackSource_C42SurplusAt

section PackSource_C42RankTransportAt
set_option autoImplicit true
namespace Sol1A.C42
noncomputable section
set_option maxRecDepth 10000
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
universe u

open Classical in
def GlobalBlockRankGate (domain : Fin 262144 ↪ E) (received : Fin 262144 → E) : Prop :=
  ((supportedLocalConstraintMatrix 48 (fun i ↦ Polynomial.C (domain i))
      (fun i ↦ Polynomial.C (received i)) columns).map
    (algebraMap (Polynomial E) (FractionRing (Polynomial E)))).rank ≤ 262144 * Sol1.C42.blockUpper

theorem constraint_matrix_map {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (centers received : Fin 262144 → R) :
    (localConstraintMatrix 48 centers received columns).map phi =
      localConstraintMatrix 48 (fun i ↦ phi (centers i)) (fun i ↦ phi (received i)) columns := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]

-- Keep the finite cardinality and the summand symbolic during simplification.
private theorem rankTransport_sum_const (n bound : ℕ) :
    (∑ _i : Fin n, bound) = n * bound := by
  simp

open Classical in
/-- Uniformity and the global sum of local ranks are now proved. Only the
single origin rank bound is assumed, over the relevant coefficient field. -/
theorem global_block_rank_of_origin {E : Type*} [Field E]
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (horigin : (pointMatrix (F := FractionRing (Polynomial E)) 48 0 0).rank ≤ Sol1.C42.blockUpper) :
    GlobalBlockRankGate domain received := by
  classical
  let F := FractionRing (Polynomial E)
  let phi : Polynomial E →+* F := algebraMap (Polynomial E) F
  change ((supportedLocalConstraintMatrix 48 (fun i ↦ C (domain i))
    (fun i ↦ C (received i)) columns).map phi).rank ≤ 262144 * Sol1.C42.blockUpper
  rw [rank_map_supportedLocalConstraintMatrix, constraint_matrix_map]
  apply (Matrix.rank_prod_rows_le_sum _).trans
  calc
    (∑ i : Fin 262144, Matrix.rank (fun row j ↦
      localConstraintMatrix 48 (fun k ↦ phi (C (domain k)))
        (fun k ↦ phi (C (received k))) columns (i,row) j)) ≤
        ∑ _i : Fin 262144, Sol1.C42.blockUpper := by
      apply Finset.sum_le_sum
      intro i _
      change (pointMatrix 48 (phi (C (domain i))) (phi (C (received i)))).rank ≤ Sol1.C42.blockUpper
      exact (point_rank_le_origin 48 (phi (C (domain i))) (phi (C (received i)))).trans horigin
    _ = 262144 * Sol1.C42.blockUpper := rankTransport_sum_const 262144 Sol1.C42.blockUpper


end
end Sol1A.C42
end PackSource_C42RankTransportAt

section PackSource_WeightedSource
set_option autoImplicit true
namespace Astra7A
universe u
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1A.C42
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem generic_source_support {R E κ : Type*} [CommSemiring R] [CommSemiring E] [Fintype κ]
    {d : ℕ} (psi : R →+* E) (cols : κ → SourceColumn d) (v : κ → R)
    (u : JetVariable d →₀ ℕ)
    (hu : u ∈ (MvPolynomial.map psi (SourceColumn.interpolant cols v)).support) :
    ∃ j : κ, u=(cols j).exponent := by
  classical
  have hs := MvPolynomial.support_map_subset psi (SourceColumn.interpolant cols v) hu
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
  exact ⟨j,by simpa [SourceColumn.interpolant] using MvPolynomial.support_monomial_subset hj⟩

theorem generic_source_weight_le {R E κ : Type*} [CommSemiring R] [CommSemiring E] [Fintype κ]
    {d : ℕ} (psi : R →+* E) (cols : κ → SourceColumn d) (v : κ → R)
    (w : JetVariable d → ℕ) (B : ℕ) (hB : ∀ j, Finsupp.weight w (cols j).exponent ≤ B) :
    (MvPolynomial.map psi (SourceColumn.interpolant cols v)).weightedTotalDegree w ≤ B := by
  apply Finset.sup_le
  intro u hu
  obtain ⟨j,rfl⟩ := generic_source_support psi cols v u hu
  exact hB j

theorem generic_source_weight_lt {R E κ : Type*} [CommSemiring R] [CommSemiring E] [Fintype κ]
    {d : ℕ} (psi : R →+* E) (cols : κ → SourceColumn d) (v : κ → R)
    (w : JetVariable d → ℕ) (B : ℕ) (hpos : 0 < B)
    (hB : ∀ j, Finsupp.weight w (cols j).exponent < B) :
    (MvPolynomial.map psi (SourceColumn.interpolant cols v)).weightedTotalDegree w < B := by
  rw [MvPolynomial.weightedTotalDegree,Finset.sup_lt_iff hpos]
  intro u hu
  obtain ⟨j,rfl⟩ := generic_source_support psi cols v u hu
  exact hB j

theorem columns_weight148 (i : SourceIndex) :
    Finsupp.weight (Astra7.jetWeight 1 4 3) (columns i).exponent ≤ 148 := by
  rw [SourceColumn.weight_exponent]
  have ht := jet_total i.1
  have ho := jet_order i.1
  have hs := i.1.1.isLt
  simp only [columns,Astra7.jetWeight,Option.elim_none,Option.elim_some,
    smul_eq_mul,mul_zero,zero_add,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Fin.val_zero,Fin.val_one,
    Fin.val_succ,Fin.val_castSucc]
  omega

/-- The original, already certified C42 source, retaining its derivative-index
information as weighted degree 148 for jet weights (1,5,9). -/
theorem weighted_uniform_annihilator {F : Type u} [Field F]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    ∃ Q : DifferentialPolynomial F 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 64 ∧
      Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148 ∧
      ∀ P ∈ ReedSolomon.closePolynomialSet domain received 131073 180255,
        differentialSpecialization Q P=0 := by
  classical
  let K := FractionRing (Polynomial F)
  let phi : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hphi : Function.Injective phi := IsFractionRing.injective (Polynomial F) K
  have hglobal := global_block_rank_of_origin domain received (Sol1A.C52.origin_rank (F := K))
  have hrank : ((localConstraintMatrix 48 (fun i => Polynomial.C (domain i))
      (fun i => Polynomial.C (received i)) columns).map phi).rank ≤ 262144*Sol1.C42.blockUpper := by
    rw [← rank_map_supportedLocalConstraintMatrix phi 48
      (fun i => Polynomial.C (domain i)) (fun i => Polynomial.C (received i)) columns]
    exact hglobal
  obtain ⟨v,_,hvdegree,hspan,_,hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le.{u,0,0,u,u} 48 0 64 (fun i => domain i)
      (fun i => Polynomial.C (received i)) (by intro i; simp) columns
      columns_injective columns_y0_le phi hphi hrank strict_source_surplus
  let Qs : DifferentialPolynomial (Polynomial F) 2 := SourceColumn.interpolant columns v
  let psi : Polynomial F →+* F := Polynomial.evalRingHom 0
  let Q : DifferentialPolynomial F 2 := MvPolynomial.map psi Qs
  have hQ0 : Q ≠ 0 := by
    exact SourceColumn.map_interpolant_ne_zero columns_injective psi
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan psi)
  have hjet : jetTotalDegree Q ≤ 64 :=
    SourceColumn.map_interpolant_jetTotalDegree_le psi columns columns_total_le v
  have hwt : Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148 :=
    generic_source_weight_le psi columns v (Astra7.jetWeight 1 4 3) 148 columns_weight148
  refine ⟨Q,hQ0,hjet,hwt,?_⟩
  intro P hP
  have hPdegree : P.natDegree ≤ 131072 := by
    by_cases hz : P=0
    · simp [hz]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP.1
      omega
  have hQweight : differentialWeightedDegree 131072 Q < 48*180255 :=
    generic_source_weight_lt psi columns v (differentialWeight 131072) (48*180255)
      (by decide) columns_weight_lt
  have hlocal : ∀ i, SatisfiesLocalConstraints 48 (domain i) (received i) Q := by
    intro i
    have hh := SatisfiesLocalConstraints.map psi 48 (Polynomial.C (domain i))
      (Polynomial.C (received i)) Qs (hconstraints i)
    simpa [psi,Q] using hh
  let indices := ReedSolomon.polynomialAgreementSet domain received P
  apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    domain received indices hQweight (fun i _ => hlocal i) P hPdegree
    domain.injective.injOn hP.2
  intro i hi
  exact (Finset.mem_filter.mp hi).2

end
end Astra7A
end PackSource_WeightedSource

section PackSource_WeightedFullList
set_option autoImplicit true
namespace Astra7A
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1A.C42 Sol1A.C57
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F]

theorem regularPart_dvd (d : ℕ) (Q : DifferentialPolynomial F (d+1)) : Sol1.C57.regularPart d Q ∣ Q := by
  obtain ⟨R,hR⟩ := radicalPrimPart_dvd_self none (Sol1.C57.topReindex d Q)
  refine ⟨(Sol1.C57.topReindex d).symm R,?_⟩
  have hh := congrArg (Sol1.C57.topReindex d).symm hR
  simpa [Sol1.C57.regularPart] using hh

def weightedFullCharge : ℚ := weightedRegularCap+firstOrderCharge 4032
def weightedListCap : ℕ := 31924061854636696
def weightedMCAAllowance : ℕ := 243056666256758391

theorem weighted_budget_exact :
    weightedFullCharge=(386116338715956056424231232 : ℚ)/12094837445 ∧
    weightedFullCharge ≤ weightedListCap ∧
    (weightedListCap : ℚ)-1 < weightedFullCharge ∧
    weightedListCap+weightedMCAAllowance=274980728111395087 ∧
    123986085283480091-weightedListCap=92062023428843395 := by
  norm_num [weightedFullCharge,weightedRegularCap,firstOrderCharge,I1,b,
    weightedListCap,weightedMCAAllowance]

/-- All regular, singular, and lower-order branches are included. -/
theorem weighted_second_order_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2) (hQ : Q ≠ 0) (hjet : jetTotalDegree Q ≤ 64)
    (hwt : Q.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180255) :
    (S.card : ℚ) ≤ weightedFullCharge := by
  classical
  let G := Sol1.C57.regularPart 1 Q
  have hsplit := Sol1.C57.split_weight 1 Q
  have hGjet : jetTotalDegree G ≤ 64 := by dsimp [G]; omega
  have hGwt : G.weightedTotalDegree (Astra7.jetWeight 1 4 3) ≤ 148 :=
    (weightedTotalDegree_le_of_dvd (Astra7.jetWeight 1 4 3) (regularPart_dvd 1 Q) hQ).trans hwt
  have hchar : ringChar F=0 ∨ jetDegree Q (Fin.last 2) < ringChar F := by
    right
    rw [ringChar.eq F 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 2)
    omega
  have hcost : 0 ≤ weightedRegularCap := by unfold weightedRegularCap; positivity
  by_cases hb : jetDegree G (Fin.last 2)=0
  · have hGone : G=1 := Sol1.C57.regular_eq_one_of_degree_zero 1 Q hb
    have hlow : ∀ P ∈ S, P ∈ directJetAgreementSolutions (Sol1.C57.lowerPart 1 Q)
        domain received 131073 180255 := by
      intro P hP
      refine ⟨?_,(hS P hP).2⟩
      rcases Sol1.C57.root_split 1 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P=0 at hr
        rw [hGone] at hr
        have hz : (1 : F[X])=0 := by
          simpa only [differentialSpecialization,map_one] using hr
        exact (one_ne_zero hz).elim
    have hlowjet : jetTotalDegree (Sol1.C57.lowerPart 1 Q) ≤ 4032 := by omega
    have hc := first_order_card_le domain received (Sol1.C57.lowerPart 1 Q) (Sol1.C57.lower_ne_zero 1 Q)
      4032 (by decide) hlowjet S hlow
    exact hc.trans (le_add_of_nonneg_left hcost)
  · have hbpos : 0 < jetDegree G (Fin.last 2) := by omega
    let good : F[X] → Prop := fun P => differentialSpecialization G P=0 ∧
      differentialSpecialization (separant G (Fin.last 2)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P => ¬good P
    have hr : (regular.card : ℚ) ≤ weightedRegularCap := by
      apply regular64_card domain received G hGwt regular
      · intro P hP
        exact ((Finset.mem_filter.mp hP).2).2
      · intro P hP
        have hp := Finset.mem_filter.mp hP
        exact ⟨hp.2.1,(hS P hp.1).2⟩
    let R := Sol1.C57.exceptionalEquation 1 Q
    have hR : R ≠ 0 := Sol1.C57.exceptional_ne_zero 1 Q hchar
    have hRjet : jetTotalDegree R ≤ 4032 := by
      have hh := Sol1.C57.exceptional_weight_sharp 1 Q 64 hjet
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 2)))
      exact hh
    have he : (exceptional.card : ℚ) ≤ firstOrderCharge 4032 := by
      apply first_order_card_le domain received R hR 4032 (by decide) hRjet exceptional
      intro P hP
      have hp := Finset.mem_filter.mp hP
      refine ⟨?_,(hS P hp.1).2⟩
      rcases Sol1.C57.root_regular_or_exceptional 1 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hc : regular.card+exceptional.card=S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ)=(regular.card : ℚ)+exceptional.card := by exact_mod_cast hc.symm
      _ ≤ weightedRegularCap+firstOrderCharge 4032 := add_le_add hr he
      _ = weightedFullCharge := rfl

theorem weighted_complete_list [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    (ReedSolomon.closePolynomialSet domain received 131073 180255).Finite ∧
      (ReedSolomon.closePolynomialSet domain received 131073 180255).ncard ≤ weightedListCap := by
  classical
  obtain ⟨Q,hQ,hjet,hwt,hsound⟩ := weighted_uniform_annihilator domain received
  have hf : ∀ S : Finset F[X],
      (S : Set F[X]) ⊆ ReedSolomon.closePolynomialSet domain received 131073 180255 →
      S.card ≤ weightedListCap := by
    intro S hS
    have hh := weighted_second_order_card domain received Q hQ hjet hwt S
      (fun P hP => ⟨hsound P (hS hP),hS hP⟩)
    exact_mod_cast hh.trans weighted_budget_exact.2.1
  have hfin : (ReedSolomon.closePolynomialSet domain received 131073 180255).Finite := by
    by_contra hi
    obtain ⟨S,hS,hcard⟩ := Set.Infinite.exists_subset_card_eq hi (weightedListCap+1)
    have hh := hf S hS
    omega
  refine ⟨hfin,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hf hfin.toFinset (fun P hP => hfin.mem_toFinset.mp hP)

local instance : DecidableEq Sol1.C42.NativeK := Classical.decEq _

theorem native_weighted_complete_list (received : Sol1.C42.NativeIndex → Sol1.C42.NativeK) :
    (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180255).Finite ∧
      (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180255).ncard ≤
        weightedListCap := by
  let := Sol1.C42.native_charP
  exact weighted_complete_list ProximityPrize.Benchmark.IRSProfile.domain received

end
end Astra7A
end PackSource_WeightedFullList
