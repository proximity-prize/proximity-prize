import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import ProximityPrize.SubmissionLower.A6966FinalRankReceiptGroup50
import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.FrontBranch12
import ProximityPrize.SubmissionLower.R6960Anchor6966Columns
import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.StructuralListPrice

section Merged6967_R6960Anchor6966Dimension
set_option Elab.async false

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Anchor6966Dimension
open A6966FinalAnchorSpace Anchor6966Columns
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

/- Count the abscissa powers using the monomial parametrization in P0_9_1. -/
private abbrev Exponent := JetVariable 3 →₀ ℕ
private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 142 (gradeLimit (a + b + c))
private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)
private def firstWidth (a b c : ℕ) : ℕ :=
  106 * 179759 - 133387 * gradeCeiling a b c + 2 * indexWeight a b c
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133387 * j
private noncomputable def exponent (x v a b c : ℕ) : Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v, a, b, c]).optionElim x
@[simp] private theorem exponent_none (x v a b c : ℕ) : exponent x v a b c none = x := by
  simp [exponent]
@[simp] private theorem exponent_some (x v a b c : ℕ) (i : Fin 4) :
    exponent x v a b c (some i) = ![v, a, b, c] i := by
  simp [exponent]
private theorem exponent_coordinates (u : Exponent) :
    exponent (u none) (u (some 0)) (u (some 1)) (u (some 2)) (u (some 3)) = u := by
  ext i
  cases i with
  | none => simp
  | some i => fin_cases i <;> simp
private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]
private theorem eligible_exponent (x v a b c : ℕ) :
    ColumnEligible (exponent x v a b c) ↔
      c ≤ 15 ∧ indexWeight a b c ≤ 58 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133387 * (v + (a + b + c)) < 106 * 179759 + 2 * indexWeight a b c := by
  unfold ColumnEligible jdeg jidx jdiff gradeCeiling indexWeight
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  simp only [exponent_none, Matrix.cons_val_one]
  have ht : ![v,a,b,c] (2 : Fin 4) = b := rfl
  have hf : ![v,a,b,c] (3 : Fin 4) = c := rfl
  rw [ht,hf,show ![a,b,c] (0 : Fin 3) = a by rfl]
  change (v + a + b + c ≤ 142 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 58 ∧
    c ≤ 15 ∧ v + a + b + c ≤ gradeLimit (a + b + c) ∧
    x + 133387 * (v + a + b + c) < 106 * 179759 + 2 * (v * 0 + a * 1 + b * 2 + c * 3)) ↔ _
  omega
private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133387 * (gradeCeiling a b c - j) < 106 * 179759 + 2 * indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 142 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega
private abbrev Slot :=
  Σ c : Fin 16, Σ b : Fin ((58 - 3 * c.val) / 2 + 1),
    Σ a : Fin (58 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)
private abbrev Eligible := {u : Exponent // ColumnEligible u}
private theorem slot_bounds (c b a j x : ℕ) :
    (c < 16 ∧ b < (58 - 3 * c) / 2 + 1 ∧ a < 58 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 15 ∧ indexWeight a b c ≤ 58 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
      x < abscissaWidth a b c j) := by
  unfold indexWeight gradeSlots
  omega
private noncomputable def slotExponent (q : Slot) : Eligible := by
  rcases q with ⟨c, b, a, j, x⟩
  refine ⟨exponent x (gradeCeiling a b c - j - (a.val + b.val + c.val)) a b c, ?_⟩
  obtain ⟨hc, hi, hj, hx⟩ := (slot_bounds c b a j x).mp
    ⟨c.isLt, b.isLt, a.isLt, j.isLt, x.isLt⟩
  have hg : gradeCeiling a b c - j - (a.val + b.val + c.val) + (a.val + b.val + c.val) =
      gradeCeiling a b c - j := by omega
  rw [eligible_exponent, hg]
  exact ⟨hc, hi, by omega, (width_iff a b c j x (by omega)).mp hx⟩
private theorem slotExponent_injective : Function.Injective slotExponent := by
  rintro ⟨⟨c, hc⟩, ⟨b, hb⟩, ⟨a, ha⟩, ⟨j, hj⟩, ⟨x, hx⟩⟩
    ⟨⟨c', hc'⟩, ⟨b', hb'⟩, ⟨a', ha'⟩, ⟨j', hj'⟩, ⟨x', hx'⟩⟩ h
  have ec : c = c' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 3)) h
  have eb : b = b' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 2)) h
  have ea : a = a' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 1)) h
  have ex : x = x' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val none) h
  subst c'
  subst b'
  subst a'
  subst x'
  have ev : gradeCeiling a b c - j - (a + b + c) =
      gradeCeiling a b c - j' - (a + b + c) := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 0)) h
  have ej : j = j' := by
    change j < gradeSlots a b c at hj
    change j' < gradeSlots a b c at hj'
    unfold gradeSlots at hj hj'
    omega
  subst j'
  rfl
private theorem slotExponent_surjective : Function.Surjective slotExponent := by
  intro u
  let x := u.val none
  let v := u.val (some 0)
  let a := u.val (some 1)
  let b := u.val (some 2)
  let c := u.val (some 3)
  have he : exponent x v a b c = u.val := exponent_coordinates u.val
  obtain ⟨hc, hi, hg, hx⟩ := (eligible_exponent x v a b c).mp (he.symm ▸ u.property)
  let j := gradeCeiling a b c - (v + (a + b + c))
  have hj : j ≤ gradeCeiling a b c := Nat.sub_le _ _
  have hj' : gradeCeiling a b c - j = v + (a + b + c) := by
    dsimp [j]
    omega
  obtain ⟨hc', hb', ha', hj'', hx'⟩ := (slot_bounds c b a j x).mpr
    ⟨hc, hi, by dsimp [j]; omega, (width_iff a b c j x hj).mpr (hj'.symm ▸ hx)⟩
  refine ⟨⟨⟨c, hc'⟩, ⟨b, hb'⟩, ⟨a, ha'⟩, ⟨j, hj''⟩, ⟨x, hx'⟩⟩, Subtype.ext ?_⟩
  change exponent x (gradeCeiling a b c - j - (a + b + c)) a b c = u.val
  have hv : gradeCeiling a b c - j - (a + b + c) = v := by omega
  rwa [hv]
private def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n
private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]
private theorem sumRange_eq_fin (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range, sumRange_eq]
private def tripleCount (a b c : ℕ) : ℕ :=
  let n := gradeSlots a b c
  n * firstWidth a b c + 133387 * (n * (n - 1) / 2)
private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]
private def rowCount (b c : ℕ) : ℕ :=
  sumRange (fun a => tripleCount a b c) (58 - 3 * c - 2 * b + 1)
private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => rowCount b c) ((58 - 3 * c) / 2 + 1)
private theorem slot_card : Fintype.card Slot = sumRange sliceCount 16 := by
  simp only [Slot, sliceCount, rowCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]
private def totals : List ℕ := [792230142621, 720519901367, 652047739428, 586022117319, 523426464468, 463454055133, 407104038729, 353554369870, 303820051345, 257063584737, 214315959596, 174724091087, 139335088908, 107280360880, 79625029008, 55488328392]

private theorem slice_value (i : Fin 16) : sliceCount i = totals[i.val]! := by
  fin_cases i <;> decide +kernel

private theorem totalCount : sumRange sliceCount 16 = 5830011322888 := by
  rw [sumRange_eq_fin]
  calc
    _ = ∑ c : Fin 16, totals[c.val]! := Finset.sum_congr rfl fun c _ => slice_value c
    _ = _ := by rw [← sumRange_eq_fin]; decide +kernel


theorem eligible_card : Nonempty (Eligible ≃ Fin 5830011322888) := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  exact ⟨e.symm.trans ((Fintype.equivFin Slot).trans (finCongr (slot_card.trans totalCount)))⟩

#print axioms eligible_card
end Anchor6966Dimension

end Merged6967_R6960Anchor6966Dimension

section Merged6967_R6960Front6960List
set_option Elab.async false






set_option Elab.async false

-- merged module ShortenChartJet
section Merged_ShortenChartJet

set_option Elab.async false
set_option maxRecDepth 5000
namespace ShortenChart
noncomputable section
open CJ0 CJ0_3 PolynomialDifferential MvPolynomial
open scoped BigOperators Polynomial
open CJ0_3 (eval_at_center)

section Affine

variable {R : Type*} [CommRing R]

/-- The first three coefficients of `g + l · u` in power-series coordinates. -/
def triangular (g l u : Fin 3 → R) : Fin 3 → R :=
  ![g 0 + l 0 * u 0,
    g 1 + l 1 * u 0 + l 0 * u 1,
    g 2 + l 2 * u 0 + l 1 * u 1 + l 0 * u 2]

theorem map_triangular {A : Type*} [CommRing A] (φ : R →+* A)
    (g l u : Fin 3 → R) (i : Fin 3) :
    φ (triangular g l u i) = triangular (φ ∘ g) (φ ∘ l) (φ ∘ u) i := by
  fin_cases i <;> simp [triangular]

def affineVars (g l : Fin 3 → R) : Fin 3 → MvPolynomial (Fin 3) R :=
  triangular (C ∘ g) (C ∘ l) MvPolynomial.X

def affineMap (g l : Fin 3 → R) : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  MvPolynomial.aeval (affineVars g l)

theorem eval_affine (g l u : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    MvPolynomial.eval u (affineMap g l P) = MvPolynomial.eval (triangular g l u) P := by
  change MvPolynomial.aeval u (MvPolynomial.aeval (affineVars g l) P) =
    MvPolynomial.aeval (triangular g l u) P
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun i => MvPolynomial.aeval u (affineVars g l i)) = triangular g l u := by
    funext i
    simpa only [affineVars, MvPolynomial.aeval_eq_eval, Function.comp_def,
      MvPolynomial.eval_C, MvPolynomial.eval_X] using
      map_triangular (MvPolynomial.eval u) (C ∘ g) (C ∘ l) MvPolynomial.X i
  rw [he]

theorem map_affine {A : Type*} [CommRing A] (φ : R →+* A)
    (g l : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    MvPolynomial.map φ (affineMap g l P) = affineMap (φ ∘ g) (φ ∘ l) (MvPolynomial.map φ P) := by
  let F := (MvPolynomial.map φ).comp (affineMap g l).toRingHom
  let H := (affineMap (φ ∘ g) (φ ∘ l)).toRingHom.comp (MvPolynomial.map φ)
  have heq : F = H := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [F, H, affineMap, MvPolynomial.algebraMap_eq]
    · intro i
      simpa only [F, H, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        affineMap, aeval_X, affineVars, Function.comp_def, MvPolynomial.map_C, MvPolynomial.map_X] using
        map_triangular (MvPolynomial.map φ) (C ∘ g) (C ∘ l) MvPolynomial.X i
  exact DFunLike.congr_fun heq P

private theorem weight_sum (w : Fin 3 → ℕ) {P Q : MvPolynomial (Fin 3) R} {b : ℕ}
    (hp : P.weightedTotalDegree w ≤ b) (hq : Q.weightedTotalDegree w ≤ b) :
    (P + Q).weightedTotalDegree w ≤ b :=
  (show (P + Q).weightedTotalDegree w ≤ max (P.weightedTotalDegree w) (Q.weightedTotalDegree w)
    from AddMonoidAlgebra.supDegree_add_le).trans (max_le hp hq)

private theorem weight_C_mul (w : Fin 3 → ℕ) (a : R)
    {P : MvPolynomial (Fin 3) R} {b : ℕ} (hp : P.weightedTotalDegree w ≤ b) :
    (C a * P).weightedTotalDegree w ≤ b :=
  (weightedTotalDegree_mul_le _ _ _).trans (by simpa only [weightedTotalDegree_C, zero_add] using hp)

private theorem weight_X [Nontrivial R] (w : Fin 3 → ℕ) (i : Fin 3) :
    (MvPolynomial.X i : MvPolynomial (Fin 3) R).weightedTotalDegree w = w i := by
  classical
  rw [show MvPolynomial.X i = (monomial (Finsupp.single i 1) 1 : MvPolynomial (Fin 3) R) from rfl]
  simp [weightedTotalDegree_monomial, Finsupp.weight_single]

private theorem triangular_weight (w : Fin 3 → ℕ) (hw : Monotone w) (g l : Fin 3 → R)
    (u : Fin 3 → MvPolynomial (Fin 3) R) (hu : ∀ i, (u i).weightedTotalDegree w ≤ w i)
    (i : Fin 3) :
    (triangular (C ∘ g) (C ∘ l) u i).weightedTotalDegree w ≤ w i := by
  have hC (a : R) (b : ℕ) : (C a : MvPolynomial (Fin 3) R).weightedTotalDegree w ≤ b := by simp
  have hu' (i j : Fin 3) (h : i ≤ j) : (u i).weightedTotalDegree w ≤ w j := (hu i).trans (hw h)
  fin_cases i
  · exact weight_sum w (hC _ _) (weight_C_mul w _ (hu 0))
  · exact weight_sum w (weight_sum w (hC _ _) (weight_C_mul w _ (hu' 0 1 (by decide))))
      (weight_C_mul w _ (hu 1))
  · exact weight_sum w
      (weight_sum w (weight_sum w (hC _ _) (weight_C_mul w _ (hu' 0 2 (by decide))))
        (weight_C_mul w _ (hu' 1 2 (by decide))))
      (weight_C_mul w _ (hu 2))

theorem affine_weight [Nontrivial R] (w : Fin 3 → ℕ) (hw : Monotone w)
    (g l : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    (affineMap g l P).weightedTotalDegree w ≤ P.weightedTotalDegree w :=
  weightedTotalDegree_aeval_le_of_le w w _ _ <|
    triangular_weight w hw g l MvPolynomial.X (fun i => (weight_X (R := R) w i).le)

private theorem pderiv_affineVar (g l : Fin 3 → R) (i : Fin 3) :
    pderiv (Fin.last 2) (affineMap g l (MvPolynomial.X i)) =
      C (l 0) * affineMap g l (pderiv (Fin.last 2) (MvPolynomial.X i)) := by
  change pderiv (Fin.last 2) (MvPolynomial.aeval (affineVars g l) (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]
  fin_cases i <;> simp [affineVars, triangular, affineMap, pderiv_X,
    show Fin.last 2 = (2 : Fin 3) from rfl]

theorem pderiv_affine (g l : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    pderiv (Fin.last 2) (affineMap g l P) = C (l 0) * affineMap g l (pderiv (Fin.last 2) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [affineMap, MvPolynomial.algebraMap_eq]
  | add P Q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X P i ih =>
    rw [map_mul, pderiv_mul, ih, pderiv_affineVar, pderiv_mul, map_add, map_mul, map_mul]
    ring

end Affine

section Inverse
variable {F : Type*} [Field F]

def inverseScale (l : Fin 3 → F) : Fin 3 → F :=
  ![(l 0)⁻¹, -(l 1) * ((l 0)⁻¹)^2,
    (l 1)^2 * ((l 0)⁻¹)^3 - l 2 * ((l 0)⁻¹)^2]

def inverseJet (g l u : Fin 3 → F) : Fin 3 → F :=
  triangular 0 (inverseScale l) (fun i => u i - g i)

theorem triangular_inverse (g l u : Fin 3 → F) (hl : l 0 ≠ 0) :
    triangular g l (inverseJet g l u) = u := by
  funext i
  fin_cases i <;> simp [triangular, inverseJet, inverseScale] <;> field_simp [hl] <;> ring

theorem inverse_triangular (g l u : Fin 3 → F) (hl : l 0 ≠ 0) :
    inverseJet g l (triangular g l u) = u := by
  funext i
  fin_cases i <;> simp [triangular, inverseJet, inverseScale] <;> field_simp [hl] <;> ring

def inverseVars (g l : Fin 3 → F) : Fin 3 → MvPolynomial (Fin 3) F :=
  triangular (C ∘ 0) (C ∘ inverseScale l) (fun i => MvPolynomial.X i - C (g i))

def inverseMap (g l : Fin 3 → F) : MvPolynomial (Fin 3) F →ₐ[F] MvPolynomial (Fin 3) F :=
  MvPolynomial.aeval (inverseVars g l)

theorem eval_inverse (g l u : Fin 3 → F) (P : MvPolynomial (Fin 3) F) :
    MvPolynomial.eval u (inverseMap g l P) = MvPolynomial.eval (inverseJet g l u) P := by
  change MvPolynomial.aeval u (MvPolynomial.aeval (inverseVars g l) P) =
    MvPolynomial.aeval (inverseJet g l u) P
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun i => MvPolynomial.aeval u (inverseVars g l i)) = inverseJet g l u := by
    funext i
    fin_cases i <;> simp [inverseVars, inverseJet, triangular, MvPolynomial.aeval_eq_eval]
  rw [he]

theorem inverse_weight (w : Fin 3 → ℕ) (hw : Monotone w)
    (g l : Fin 3 → F) (P : MvPolynomial (Fin 3) F) :
    (inverseMap g l P).weightedTotalDegree w ≤ P.weightedTotalDegree w := by
  refine weightedTotalDegree_aeval_le_of_le w w _ _
    (triangular_weight w hw 0 (inverseScale l) _ ?_)
  intro i
  change (MvPolynomial.X i - C (g i) : MvPolynomial (Fin 3) F).weightedTotalDegree w ≤ w i
  rw [sub_eq_add_neg, ← map_neg (C : F →+* MvPolynomial (Fin 3) F)]
  exact weight_sum w (weight_X w i).le ((weightedTotalDegree_C w (-g i)).le.trans (Nat.zero_le _))

end Inverse

def derivatives {R : Type*} [CommRing R] (g : (Polynomial R)) (i : Fin 3) : (Polynomial R) :=
  Polynomial.hasseDeriv i.val g

theorem derivatives_affine {R : Type*} [CommRing R] (g L h : (Polynomial R)) :
    derivatives (g + L * h) = triangular (derivatives g) (derivatives L) (derivatives h) := by
  funext i
  have h₂ : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  fin_cases i <;> simp [derivatives, triangular, Polynomial.hasseDeriv_mul, h₂] <;> ring

def transform (g L : (Polynomial K)) (G : Equation) : Equation :=
  (MvPolynomial.optionEquivRight K (Fin 3)).symm
    (affineMap (derivatives g) (derivatives L) (MvPolynomial.optionEquivRight K (Fin 3) G))

private theorem spec_of_flatten {R : Type*} [CommRing R]
    (Q : MvPolynomial (Fin 3) (Polynomial R)) (h : (Polynomial R)) :
    differentialSpecialization ((MvPolynomial.optionEquivRight R (Fin 3)).symm Q) h =
      MvPolynomial.eval (derivatives h) Q := by
  let x : Option (Fin 3) → (Polynomial R) := fun i => i.elim Polynomial.X (derivatives h)
  have he : differentialSpecializationHom h = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    cases i with
    | none => exact differentialSpecialization_x h
    | some i => exact differentialSpecialization_jet i h
  rw [differentialSpecialization, he, MvPolynomial.aeval_optionEquivRight_symm]
  rw [show x none = Polynomial.X from rfl, Polynomial.aeval_X_left,
    show (AlgHom.id R (Polynomial R)).toRingHom = RingHom.id (Polynomial R) from rfl, MvPolynomial.map_id]
  rfl

theorem transform_spec (g L h : (Polynomial K)) (G : Equation) :
    differentialSpecialization (transform g L G) h =
      differentialSpecialization G (g + L * h) := by
  conv_rhs => rw [← (MvPolynomial.optionEquivRight K (Fin 3)).symm_apply_apply G]
  rw [transform, spec_of_flatten, eval_affine, spec_of_flatten, derivatives_affine]

theorem nativeJet_derivatives (g : (Polynomial K)) (i : Fin 3) :
    nativeJet g i = centerMap (derivatives g i) := by
  change (Polynomial.hasseDeriv i.val (g.map embed)).eval center = _
  rw [Polynomial.hasseDeriv_map, eval_at_center]
  rfl

theorem nativeJet_eq (g : (Polynomial K)) : nativeJet g = centerMap ∘ derivatives g :=
  funext (nativeJet_derivatives g)

theorem nativeJet_affine (g L h : (Polynomial K)) :
    nativeJet (g + L * h) = triangular (nativeJet g) (nativeJet L) (nativeJet h) := by
  funext i
  simp only [nativeJet_eq, Function.comp_apply, derivatives_affine]
  exact map_triangular centerMap _ _ _ i

theorem nativeJet_zero_ne {L : (Polynomial K)} (hL : L ≠ 0) : nativeJet L 0 ≠ 0 := by
  rw [nativeJet_derivatives]
  exact map_ne_zero_iff centerMap centerMap_injective |>.mpr (by simpa [derivatives] using hL)

theorem transform_initial (g L : (Polynomial K)) (G : Equation) :
    initial (transform g L G) = affineMap (nativeJet g) (nativeJet L) (initial G) := by
  rw [initial_eq_map, transform, AlgEquiv.apply_symm_apply, map_affine, ← initial_eq_map]
  simp only [nativeJet_eq]

theorem transform_initialSep (g L : (Polynomial K)) (G : Equation) :
    initialSep (transform g L G) =
      C (nativeJet L 0) * affineMap (nativeJet g) (nativeJet L) (initialSep G) := by
  rw [show initialSep (transform g L G) = pderiv (Fin.last 2) (initial (transform g L G)) from
    (pderiv_last_initialJetEquation _ _).symm, transform_initial, pderiv_affine,
    show pderiv (Fin.last 2) (initial G) = initialSep G from pderiv_last_initialJetEquation _ _]

theorem transform_weight (g L : (Polynomial K)) (G : Equation) (w : Fin 3 → ℕ) (hw : Monotone w) :
    (transform g L G).weightedTotalDegree (fun j => j.elim 0 w) ≤
      G.weightedTotalDegree (fun j => j.elim 0 w) := by
  rw [← weightedTotalDegree_optionEquivRight, ← weightedTotalDegree_optionEquivRight]
  rw [transform, AlgEquiv.apply_symm_apply]
  exact affine_weight w hw _ _ _

#print axioms transform_initialSep
end
end ShortenChart

end Merged_ShortenChartJet

-- merged module ShortenChart
section Merged_ShortenChart

set_option Elab.async false
set_option maxRecDepth 8000
namespace ShortenChart
noncomputable section
open CJ0 CJ0_3 PolynomialDifferential MvPolynomial
open StructuralList (ShortBand InBand exponent totalCap indexCap topCap)
open scoped Polynomial BigOperators
open CJ0_3 (lifted_total lifted_top lifted_weight indexWeight_eq coeffWeight_eq totalWeight_eq degreeOf_top_of_index readJet_eq)
open CJ0_3_2 (commonTaylor_top)

private theorem exponent_sufficient (length : ℕ) :
    TaylorExponentSufficient 2 length (exponent length) := by
  intro l
  have hl := l.isLt
  unfold exponent
  omega

private theorem top_monotone : Monotone (Pi.single (Fin.last 2) (1 : ℕ)) := by
  intro i j hij
  by_cases hi : i = Fin.last 2
  · have hj : j = Fin.last 2 := le_antisymm (Fin.le_last j) (hi ▸ hij)
    rw [hi, hj]
  · have hi₂ : i ≠ (2 : Fin 3) := hi
    have hw : (Pi.single (Fin.last 2) (1 : ℕ) : Fin 3 → ℕ) i = 0 := by simp [hi₂]
    rw [hw]
    exact Nat.zero_le _

private theorem lift_total {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : (Polynomial K)) :
    jetTotalDegree (lifted (transform g L G)) ≤ s.B := by
  rw [lifted_total]
  have h := transform_weight g L G 1 (fun _ _ _ => le_rfl)
  rw [totalWeight_eq] at h
  exact h.trans hG.2.1

private theorem lift_index {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : (Polynomial K)) :
    (lifted (transform g L G)).weightedTotalDegree (Astra7.jetWeight 0 1 3) ≤ s.J := by
  rw [lifted_weight, indexWeight_eq]
  exact (transform_weight g L G Fin.val (fun _ _ h => h)).trans hG.2.2.1

private theorem lift_top {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : (Polynomial K)) :
    (lifted (transform g L G)).degreeOf (some (Fin.last 2)) ≤ s.C := by
  change jetDegree (lifted (transform g L G)) (Fin.last 2) ≤ s.C
  rw [lifted_top]
  have hw := transform_weight g L G (Pi.single (Fin.last 2) 1) top_monotone
  have he : (fun v : Option (Fin 3) => v.elim 0 (Pi.single (Fin.last 2) 1)) =
      Pi.single (some (Fin.last 2)) (1 : ℕ) := by
    funext v
    cases v <;> simp [Pi.single_apply]
  rw [he, weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hw
  exact hw.trans hG.2.2.2

private def basisPolynomial (L : (Polynomial K)) (j : ℕ) : (Polynomial Geo) :=
  L.map embed * (Polynomial.X - Polynomial.C center) ^ j

private def rawDenominator (length : ℕ) (G : Equation) : InitialRing 2 :=
  initialSep G ^ exponent length

private def rawNumerator (length : ℕ) (g L : (Polynomial K)) (G : Equation)
    (i : Fin k) : InitialRing 2 :=
  C ((g.map embed).coeff i.val) * rawDenominator length G +
    ∑ l : Fin length, C ((basisPolynomial L l.val).coeff i.val) *
      commonTaylorNumerator center (lifted G) (exponent length) l.val

def chart (length : ℕ) (g L : (Polynomial K)) (G : Equation) (E : InitialRing 2) : Chart 2 :=
  ⟨E, inverseMap (nativeJet g) (nativeJet L) (rawDenominator length (transform g L G)),
    fun i => inverseMap (nativeJet g) (nativeJet L) (rawNumerator length g L (transform g L G) i)⟩

private theorem rawDenominator_band (s : Source) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) :
    InBand s length (rawDenominator length (transform g L G)) := by
  let Q := lifted (transform g L G)
  have hb : (initialJetSeparant center Q).totalDegree ≤ s.B - 1 :=
    (totalDegree_initialJetSeparant_le center Q).trans
      (Nat.sub_le_sub_right (lift_total hG g L) 1)
  have hi : (initialJetSeparant center Q).weightedTotalDegree Fin.val ≤ s.J - 2 := by
    simpa only [coeffWeight_eq, zero_add, one_mul] using
      (Astra7.initialSeparant_weight 0 1 center Q).trans (Nat.sub_le_sub_right (lift_index hG g L) (0 + 1 * 2))
  have ht : (initialJetSeparant center Q).degreeOf (Fin.last 2) ≤ s.C - 1 :=
    (degreeOf_initialJetSeparant_le center Q).trans (Nat.sub_le_sub_right (lift_top hG g L) 1)
  have hindex : (initialJetSeparant center Q ^ exponent length).weightedTotalDegree Fin.val ≤ indexCap s length :=
    ((weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hi)).trans (by
      unfold indexCap
      omega)
  refine ⟨((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hb)).trans (by unfold totalCap; omega),
    hindex, le_min ?_ (degreeOf_top_of_index hindex)⟩
  exact ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ ht)).trans (by omega)

private theorem rawCentered_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) (l : Fin length) :
    InBand s length (commonTaylorNumerator center (lifted (transform g L G)) (exponent length) l.val) := by
  let Q := lifted (transform g L G)
  have hlK := l.isLt
  have hJ := hs.index_top
  have hC := hs.top_pos
  have hi := Astra7.commonTaylor_weight 0 1 s.J length (exponent length) center Q
    (exponent_sufficient length) (by omega) (lift_index hG g L) l
  have hindex : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
      indexCap s length := by
    have h : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
        exponent length * (s.J - 2) + l.val := by
      simpa only [coeffWeight_eq, zero_add, one_mul, add_zero] using hi
    exact h.trans (by unfold indexCap; omega)
  refine ⟨?_, hindex, le_min ?_ (degreeOf_top_of_index hindex)⟩
  · exact (totalDegree_commonTaylorNumerator_le center Q (exponent_sufficient length l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (lift_total hG g L) 1)) 1)
  · have hl : l.val - 1 ≤ length - 2 := by omega
    apply (commonTaylor_top center Q hs.top_pos (lift_top hG g L) (exponent_sufficient length) l).trans
    rw [Nat.add_sub_assoc (by omega : 2 ≤ length)]
    exact Nat.add_le_add_left hl _

private theorem rawNumerator_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) (i : Fin k) :
    InBand s length (rawNumerator length g L (transform g L G) i) := by
  let V := CJ0_4.bandSpace (totalCap s length) (indexCap s length) (topCap s length)
  have hmem {P : InitialRing 2} (hp : InBand s length P) : P ∈ V := CJ0_4.mem_bandSpace.mpr hp
  have hc (a : Geo) {P : InitialRing 2} (hp : InBand s length P) : C a * P ∈ V := by
    rw [← MvPolynomial.smul_eq_C_mul]
    exact V.smul_mem _ (hmem hp)
  suffices h : rawNumerator length g L (transform g L G) i ∈ V from CJ0_4.mem_bandSpace.mp h
  unfold rawNumerator
  exact V.add_mem (hc _ (rawDenominator_band s length hK g L G hG))
    (V.sum_mem fun l _ => hc _ (rawCentered_band s hs length hK g L G hG l))

private theorem inverse_band (s : Source) (length : ℕ) (g L : (Polynomial K)) {P : InitialRing 2}
    (hp : InBand s length P) : InBand s length (inverseMap (nativeJet g) (nativeJet L) P) := by
  have hb := inverse_weight (1 : Fin 3 → ℕ) (fun _ _ _ => le_rfl) (nativeJet g) (nativeJet L) P
  have hi := inverse_weight Fin.val (fun _ _ h => h) (nativeJet g) (nativeJet L) P
  have ht := inverse_weight (Pi.single (Fin.last 2) 1) top_monotone (nativeJet g) (nativeJet L) P
  simp only [weightedTotalDegree_one] at hb
  simp only [weightedTotalDegree_piSingle] at ht
  exact ⟨hb.trans hp.1, hi.trans hp.2.1, ht.trans hp.2.2⟩

theorem chart_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : (Polynomial K)) (G : Equation) (hG : OrderTwo s G) (E : InitialRing 2) :
    ShortBand s length (chart length g L G E) :=
  ⟨inverse_band s length g L (rawDenominator_band s length hK g L G hG),
    fun i => inverse_band s length g L (rawNumerator_band s hs length hK g L G hG i)⟩

private theorem denominator_eval (length : ℕ) (g L : (Polynomial K)) (G : Equation) (E : InitialRing 2)
    (u : Fin 3 → Geo) (hL : L ≠ 0) :
    MvPolynomial.eval u (chart length g L G E).denominator =
      (nativeJet L 0 * MvPolynomial.eval u (initialSep G)) ^ exponent length := by
  change MvPolynomial.eval u (inverseMap (nativeJet g) (nativeJet L)
    (rawDenominator length (transform g L G))) = _
  rw [eval_inverse, rawDenominator, map_pow, transform_initialSep, map_mul, MvPolynomial.eval_C,
    eval_affine, triangular_inverse _ _ _ (nativeJet_zero_ne hL)]

private theorem denominator_regular (length : ℕ) (g L : (Polynomial K)) (G : Equation) (E : InitialRing 2)
    (hL : L ≠ 0) (hE : Irreducible E) (hreg : ¬ E ∣ initialSep G) :
    ¬ E ∣ (chart length g L G E).denominator := by
  have he : (chart length g L G E).denominator =
      C (nativeJet L 0 ^ exponent length) * (initialSep G) ^ exponent length := by
    apply MvPolynomial.funext
    intro u
    rw [denominator_eval length g L G E u hL, map_mul, MvPolynomial.eval_C, map_pow, mul_pow]
  rw [he]
  have hu : IsUnit (C (nativeJet L 0 ^ exponent length) : InitialRing 2) :=
    ((isUnit_iff_ne_zero).mpr (pow_ne_zero _ (nativeJet_zero_ne hL))).map C
  intro h
  have hh := (hE.prime.dvd_or_dvd h).resolve_left (fun hd => hE.not_isUnit (isUnit_of_dvd_unit hd hu))
  exact hreg (hE.prime.dvd_of_dvd_pow hh)

private theorem reconstruct_basis (length : ℕ) (L : (Polynomial K)) (G : Equation) (u : Fin 3 → Geo) :
    L.map embed * rationalTaylorPolynomial center (lifted G) length u =
      ∑ l : Fin length, Polynomial.C (rationalTaylorCoefficient center (lifted G) u l.val) *
        basisPolynomial L l.val := by
  rw [rationalTaylorPolynomial, Polynomial.centeredCoefficientPrefix, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_monomial, map_neg, ← sub_eq_add_neg]
  unfold basisPolynomial
  ring

private theorem raw_output (length : ℕ) (g L : (Polynomial K)) (G : Equation)
    (u : Fin 3 → Geo) (hsep : MvPolynomial.eval u (initialSep G) ≠ 0) (i : Fin k) :
    MvPolynomial.eval u (rawNumerator length g L G i) / MvPolynomial.eval u (rawDenominator length G) =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted G) length u).coeff i.val := by
  have hpow : MvPolynomial.eval u (initialSep G) ^ exponent length ≠ 0 := pow_ne_zero _ hsep
  rw [reconstruct_basis, Polynomial.coeff_add, Polynomial.finsetSum_coeff, rawNumerator,
    map_add, add_div, map_mul, MvPolynomial.eval_C, rawDenominator, map_pow, mul_div_cancel_right₀ _ hpow,
    map_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.coeff_C_mul, map_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval (f := u),
    aeval_commonTaylorNumerator center (lifted G) u (exponent_sufficient length l) hsep]
  change _ * (MvPolynomial.eval u (initialSep G) ^ exponent length * _) /
    MvPolynomial.eval u (initialSep G) ^ exponent length = _
  field_simp

private theorem chart_output (length : ℕ) (hK : 3 ≤ length) (g L : (Polynomial K)) (G : Equation)
    (E : InitialRing 2) (u : Fin 3 → Geo) (hu : MvPolynomial.eval u (chart length g L G E).denominator ≠ 0)
    (i : Fin k) :
    (chart length g L G E).output u i =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted (transform g L G))
        length (inverseJet (nativeJet g) (nativeJet L) u)).coeff i.val := by
  let v := inverseJet (nativeJet g) (nativeJet L) u
  have hv : MvPolynomial.eval v (initialSep (transform g L G)) ≠ 0 := by
    intro hh
    apply hu
    change MvPolynomial.eval u (inverseMap (nativeJet g) (nativeJet L)
      (rawDenominator length (transform g L G))) = 0
    rw [eval_inverse, rawDenominator, map_pow, hh, zero_pow]
    unfold exponent
    omega
  rw [Chart.output, chart, eval_inverse, eval_inverse]
  exact raw_output length g L (transform g L G) v hv i

private theorem geoJet_affine (g L h : (Polynomial Geo)) :
    polynomialJet (d := 2) center (g + L * h) =
      triangular (polynomialJet center g) (polynomialJet center L) (polynomialJet center h) := by
  funext i
  change Polynomial.evalRingHom center (derivatives (g + L * h) i) =
    triangular (Polynomial.evalRingHom center ∘ derivatives g)
      (Polynomial.evalRingHom center ∘ derivatives L) (Polynomial.evalRingHom center ∘ derivatives h) i
  rw [derivatives_affine]
  exact map_triangular (Polynomial.evalRingHom center) _ _ _ i

private theorem natDegree_lt {F : Type*} [Field F] {P : (Polynomial F)} {b : ℕ} (hb : 0 < b)
    (hp : P.degree < b) : P.natDegree < b := by
  by_cases hz : P = 0
  · simpa [hz] using hb
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp

private theorem reconstruction_degree (length : ℕ) (hK : 3 ≤ length) (g L : (Polynomial K))
    (hg : g.degree < k) (hsum : L.natDegree + length ≤ k) (G : Equation) (u : Fin 3 → Geo) :
    (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted G) length u).degree < k := by
  let U := rationalTaylorPolynomial center (lifted G) length u
  have hU : U.natDegree < length :=
    natDegree_lt (by omega) (Polynomial.degree_centeredCoefficientPrefix_lt _ _ _)
  have hg' : (g.map embed).natDegree < k :=
    Polynomial.natDegree_map_le.trans_lt (natDegree_lt (by decide) hg)
  have hm : (L.map embed * U).natDegree < k :=
    (Polynomial.natDegree_mul_le).trans_lt ((Nat.add_lt_add_of_le_of_lt Polynomial.natDegree_map_le hU).trans_le hsum)
  have hh : (g.map embed + L.map embed * U).natDegree < k :=
    (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hg' hm)
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hh)

theorem chart_ok (length : ℕ) (hK : 3 ≤ length) (g L : (Polynomial K)) (hL : L ≠ 0)
    (hg : g.degree < k) (hsum : L.natDegree + length ≤ k) (G : Equation)
    (E : InitialRing 2) (hE : Irreducible E) (hreg : ¬ E ∣ initialSep G) :
    ChartOK (chart length g L G E) := by
  refine ⟨hE, denominator_regular length g L G E hL hE hreg, ?_⟩
  intro u hu j
  let v := inverseJet (nativeJet g) (nativeJet L) u
  let U := rationalTaylorPolynomial center (lifted (transform g L G)) length v
  let P := g.map embed + L.map embed * U
  have hcoeff : (chart length g L G E).output u = (fun i : Fin k => P.coeff i.val) := by
    funext i
    exact chart_output length hK g L G E u hu.2 i
  rw [hcoeff, show readJet (fun i : Fin k => P.coeff i.val) j.val =
    (polynomialJet (d := 2) center P) j from readJet_eq P
      (reconstruction_degree length hK g L hg hsum (transform g L G) v) j.val]
  have hU : polynomialJet (d := 2) center U = v :=
    polynomialJet_rationalTaylorPolynomial center (lifted (transform g L G)) (by omega) v
  change (polynomialJet (d := 2) center (g.map embed + L.map embed * U)) j = u j
  rw [geoJet_affine, hU]
  exact congrFun (triangular_inverse (nativeJet g) (nativeJet L) u (nativeJet_zero_ne hL)) j

private theorem chart_contains (length : ℕ) (hK : 3 ≤ length) (hk : length ≤ k)
    (g L : (Polynomial K)) (hL : L ≠ 0) (G : Equation) (E : InitialRing 2)
    {f h : (Polynomial K)} (hh : h.degree < length) (hf : f = g + L * h)
    (hsol : differentialSpecialization G f = 0) (hE : MvPolynomial.eval (nativeJet f) E = 0)
    (hsep : MvPolynomial.eval (nativeJet f) (initialSep G) ≠ 0) :
    coeffPoint f ∈ (chart length g L G E).imageSet := by
  have hL0 := nativeJet_zero_ne hL
  have hu : MvPolynomial.eval (nativeJet f) (chart length g L G E).denominator ≠ 0 := by
    rw [denominator_eval length g L G E _ hL]
    exact pow_ne_zero _ (mul_ne_zero hL0 hsep)
  have hv : inverseJet (nativeJet g) (nativeJet L) (nativeJet f) = nativeJet h := by
    rw [hf, nativeJet_affine]
    exact inverse_triangular _ _ _ hL0
  have hs : MvPolynomial.eval (nativeJet h) (initialSep (transform g L G)) ≠ 0 := by
    rw [transform_initialSep, map_mul, MvPolynomial.eval_C, eval_affine, ← nativeJet_affine, ← hf]
    exact mul_ne_zero hL0 hsep
  have hsol' : differentialSpecialization (lifted (transform g L G)) (h.map embed) = 0 := by
    rw [lifted, ← map_differentialSpecialization, transform_spec, ← hf, hsol, Polynomial.map_zero]
  have hsep' : jetEvaluation (separant (lifted (transform g L G)) (Fin.last 2)) center (nativeJet h) ≠ 0 := by
    simpa only [initialSep, ← MvPolynomial.aeval_eq_eval, aeval_initialJetSeparant] using hs
  let : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hbin (i : ℕ) (hlo : 2 < i) (hhi : i < length) : (i.choose 2 : Geo) ≠ 0 :=
    Sol1.C40Primitives.native_binomial_guard 2 le_rfl i hlo (Nat.lt_succ_of_lt (hhi.trans_le hk))
  have hrec := rationalTaylorPolynomial_polynomialJet center (lifted (transform g L G))
    (h.map embed) hsol' hsep' (Polynomial.degree_map_le.trans_lt hh) hbin
  refine ⟨nativeJet f, ⟨hE, hu⟩, ?_⟩
  funext i
  rw [chart_output length hK g L G E _ hu, hv, nativeJet, hrec,
    ← Polynomial.map_mul, ← Polynomial.map_add, ← hf, Polynomial.coeff_map]
  rfl

/-- Shortening the quotient chart by the number of common agreement positions bounds the
numerator and denominator while retaining the original jet coordinates. -/
theorem shortenChart (s : Source) (hs : ShapeOK s) (G : Equation) (hG : OrderTwo s G)
    (E : InitialRing 2) (hE : Irreducible E) (_hEdvd : E ∣ initial G)
    (hreg : ¬ E ∣ initialSep G) (S : Finset Node) (hS : S.card + 3 ≤ k) (w : Node → K) :
    ∃ T : Chart 2, ChartOK T ∧ T.equation = E ∧ ShortBand s (k - S.card) T ∧
      ∀ f : (Polynomial K), f.degree < k → differentialSpecialization G f = 0 →
        MvPolynomial.eval (nativeJet f) E = 0 → MvPolynomial.eval (nativeJet f) (initialSep G) ≠ 0 →
        (∀ i ∈ S, f.eval (node i) = w i) → coeffPoint f ∈ T.imageSet := by
  classical
  let g := Lagrange.interpolate S node w
  let L := FrobeniusLocator.locator node S
  let length := k - S.card
  have hK : 3 ≤ length := by dsimp [length]; omega
  have hk : length ≤ k := Nat.sub_le _ _
  have hL := (FrobeniusLocator.locator_monic node S).ne_zero
  have hLn : L.natDegree = S.card := FrobeniusLocator.locator_natDegree _ _
  have hx : Function.Injective node := ProximityPrize.Benchmark.IRSProfile.domain.injective
  have hg : g.degree < k := (Lagrange.degree_interpolate_lt w hx.injOn).trans_le
    (by exact_mod_cast (show S.card ≤ k by omega))
  have hsum : L.natDegree + length ≤ k := by rw [hLn]; dsimp [length]; omega
  refine ⟨chart length g L G E, chart_ok length hK g L hL hg hsum G E hE hreg, rfl,
    chart_band s hs length hK g L G hG E, ?_⟩
  intro f hf hroot hEroot hsep hits
  have hdiv : L ∣ f - g := FrobeniusLocator.Strata.locator_dvd_of_eval_zero node hx S _ (fun i hi => by
    rw [Polynomial.eval_sub, hits i hi, show g.eval (node i) = w i from
      Lagrange.eval_interpolate_at_node w hx.injOn hi, sub_self])
  have hd : (f - g).degree < k := (Polynomial.degree_sub_le _ _).trans_lt (max_lt hf hg)
  have hdN : (f - g).natDegree ≤ N := by
    have hh := natDegree_lt (by decide) hd
    change _ < 131072 at hh
    change _ ≤ 131071
    omega
  have hS' : S.card ≤ N := by
    change _ ≤ 131072 at hS
    change _ ≤ 131071
    omega
  obtain ⟨h, hdeg, he⟩ :=
    FrobeniusLocator.Strata.bounded_locator_quotient node S (f - g) N hS' hdN hdiv
  have hf' : f = g + L * h := by rw [← he]; ring
  have hlen : N - S.card + 1 = length := by
    dsimp [length]
    change _ ≤ 131072 at hS
    change 131071 - S.card + 1 = 131072 - S.card
    omega
  rw [hlen] at hdeg
  exact chart_contains length hK hk g L hL G E hdeg hf' hroot hEroot hsep

#print axioms shortenChart
end
end ShortenChart

end Merged_ShortenChart

-- merged module R6960Front6960List
section Merged_R6960Front6960List

set_option Elab.async false
set_option maxRecDepth 18000

namespace Front6960ListBank
noncomputable section
open Finset
open CJ0 (ShapeOK mem_fullBox Jet fullBox Surplus AgreementOK SilentTail)
open scoped BigOperators

theorem native_shape : ShapeOK source := by
  have hmem := mem_fullBox (B := 78) (J := 24) (C := 10) (by decide) (by decide)
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun j hj => (hmem j).mp hj, ?_⟩
  intro j hj hpos
  obtain ⟨hq, hv, hc⟩ := (hmem j).mp hj
  apply (hmem _).mpr
  refine ⟨?_, hv, hc⟩
  change j.a-1 + j.b + j.c ≤ 78
  unfold Jet.q at hq
  omega
private def runLength (c b : ℕ) := 78 - (b+c) + 1
private def bRange (c : ℕ) := range (24 - 2*c + 1)
private def countRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (runLength c b * (runLength c b - 1) / 2 + runLength c b * (b+c))
private def indexRow (c : ℕ) := ∑ b ∈ bRange c, runLength c b * (b+2*c)
private theorem box_count : source.E.card = ∑ c ∈ range 11, countRow c := by
  simp only [source, fullBox, card_sigma, card_range, countRow, bRange, runLength]
private theorem box_total : (∑ j ∈ source.E, j.q) = ∑ c ∈ range 11, totalRow c := by
  simp only [source, fullBox, sum_sigma, totalRow, bRange, runLength, Jet.q, Jet.a, Jet.b, Jet.c]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range, smul_eq_mul, Nat.mul_add]
private theorem box_index : (∑ j ∈ source.E, j.v) = ∑ c ∈ range 11, indexRow c := by
  simp only [source, fullBox, sum_sigma, indexRow, bRange, runLength, Jet.v, Jet.b, Jet.c,
    sum_const, card_range, smul_eq_mul]
private theorem row0 : countRow 0 = 1675 ∧ totalRow 0 = 74725 ∧ indexRow 0 = 18800 := by decide +kernel
private theorem row1 : countRow 1 = 1541 ∧ totalRow 1 = 68839 ∧ indexRow 1 = 19021 := by decide +kernel
private theorem row2 : countRow 2 = 1407 ∧ totalRow 2 = 62930 ∧ indexRow 2 = 18928 := by decide +kernel
private theorem row3 : countRow 3 = 1273 ∧ totalRow 3 = 57000 ∧ indexRow 3 = 18525 := by decide +kernel
private theorem row4 : countRow 4 = 1139 ∧ totalRow 4 = 51051 ∧ indexRow 4 = 17816 := by decide +kernel
private theorem row5 : countRow 5 = 1005 ∧ totalRow 5 = 45085 ∧ indexRow 5 = 16805 := by decide +kernel
private theorem row6 : countRow 6 = 871 ∧ totalRow 6 = 39104 ∧ indexRow 6 = 15496 := by decide +kernel
private theorem row7 : countRow 7 = 737 ∧ totalRow 7 = 33110 ∧ indexRow 7 = 13893 := by decide +kernel
private theorem row8 : countRow 8 = 603 ∧ totalRow 8 = 27105 ∧ indexRow 8 = 12000 := by decide +kernel
private theorem row9 : countRow 9 = 469 ∧ totalRow 9 = 21091 ∧ indexRow 9 = 9821 := by decide +kernel
private theorem row10 : countRow 10 = 335 ∧ totalRow 10 = 15070 ∧ indexRow 10 = 7360 := by decide +kernel
private theorem sum_rows (f : ℕ → ℕ) : (∑ i ∈ range 11, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by simp only [sum_range_succ, sum_range_zero, zero_add]
theorem moments : source.E.card = 11055 ∧ (∑ j ∈ source.E, j.q) = 495110 ∧
    (∑ j ∈ source.E, j.v) = 168465 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [box_count, sum_rows, row0.1, row1.1, row2.1, row3.1, row4.1, row5.1, row6.1, row7.1, row8.1, row9.1, row10.1]
  · rw [box_total, sum_rows, row0.2.1, row1.2.1, row2.2.1, row3.2.1, row4.2.1, row5.2.1, row6.2.1, row7.2.1, row8.2.1, row9.2.1, row10.2.1]
  · rw [box_index, sum_rows, row0.2.2, row1.2.2, row2.2.2, row3.2.2, row4.2.2, row5.2.2, row6.2.2, row7.2.2, row8.2.2, row9.2.2, row10.2.2]

theorem surplus : Surplus 179818 source 184686 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide +kernel : 262144*184686+131071*495110 < 57*179818*11055+168465)

private theorem list_price : StructuralList.tariff 179818 source = 8609338830670119 := by decide +kernel

theorem scalar_list : CJ0.ScalarList 179818 8609338830670119 := by
  have agr : AgreementOK 179818 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 79 := by
    intro j hj hcut
    have hq : j.q ≤ 78 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_shortening ShortenChart.shortenChart
    179818 source 184686 agr (by decide) native_shape (by decide) (by decide) surplus
    (Or.inr ⟨79, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list
end
end Front6960ListBank

end Merged_R6960Front6960List

end Merged6967_R6960Front6960List

section Merged6967_R6960Front6960Rank3
set_option Elab.async false


set_option Elab.async false
set_option autoImplicit true
section
namespace Front6960_3
noncomputable section
open Front6960 Polynomial
open P1_3 (Bank cutDegree)
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : (Polynomial K) :=
  B.a * (B.β l).map twist
def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : (Polynomial K) :=
  -(B.b * B.α j)
abbrev sourceCutoff : ℕ := 4 * agreement - 1
def quotientSurplus (bank : Bank) (n h : ℕ) : Prop :=
  n * (K1_10.jetDim 4 bank.first bank.second -
      K1_10.jetDim 3 (bank.first - 1) (bank.second - 1)) <
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4
        (bank.first - 1) (bank.second - 1)
def incidenceRatio : ℚ :=
  (((blockLength - (k - 1)) * cutDegree : ℕ) : ℚ) / ((agreement - (k - 1) : ℕ) : ℚ)
def regularPrice : ℕ := ⌈((210 : ℕ) : ℚ) * incidenceRatio ^ 2⌉₊
end
end Front6960_3
end
section
namespace Front6960_3
noncomputable section
open Front6960 Polynomial ProximityPrize.Benchmark FrobeniusLocator
open P1_3 (Adjugate Plane)
open P0_6 (amp_le primitive_lift contraction_degree)
theorem adjugate_of_plane {u : Words} {T : TwoActive u} {R : Relation T} {D : Reduction u T R}
    (B : RankThree u T R D) (hnp : Nonparallel B)
    (W : Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (hroom : k + 3 * D.height + (fixedNodes R).card ≤ blockLength) :
    Nonempty (Adjugate u (fixedNodes R) D.height) := by
  change 131072 + 3 * D.height + (fixedNodes R).card ≤ 262144 at hroom
  let A := B.α
  let V := fun j => (B.β j).map twist
  let s := amplitudeDegree (A 0) (A 1)
  let t := amplitudeDegree (V 0) (V 1)
  have htw (P : (Polynomial K)) : (P.map twist).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective twist.injective _
  have ht : t = amplitudeDegree (B.β 0) (B.β 1) := by simp only [t, V, amplitudeDegree, htw]
  have ha : B.a.natDegree + t ≤ D.height := ht ▸ B.first_degree
  have hb : B.b.natDegree + s ≤ D.height := B.second_degree
  have hv : IsCoprime (V 0) (V 1) := B.β_primitive.map (mapRingHom twist)
  have hout (j l : Fin 2) : (W.output j l).natDegree < 131072 + D.height := by
    by_cases hz : W.output j l = 0
    · simp [hz]
    · exact (natDegree_lt_iff_degree_lt hz).mpr (W.output_degree j l)
  let L := fun l => A 0 * W.output 1 l - A 1 * W.output 0 l
  let N := fun j => V 1 * W.output j 0 - V 0 * W.output j 1
  let w := fun i => B.a.eval (node i) * ((A 0).eval (node i) * u 1 i - (A 1).eval (node i) * u 0 i)
  let z := fun i => B.b.eval (node i) * ((V 0).eval (node i) * (u 1 i)^p - (V 1).eval (node i) * (u 0 i)^p)
  have hn (i : I) (hi : i ∉ fixedNodes R) (j l : Fin 2) :
      (W.output j l).eval (node i) =
        B.a.eval (node i) * (V l).eval (node i) * u j i -
        B.b.eval (node i) * (A j).eval (node i) * (u l i)^p := by
    rw [← W.nodes i hi]
    simp only [leftCoeff, rightCoeff, eval_mul, eval_neg, A, V]
    ring
  obtain ⟨P, hP, heP⟩ := primitive_lift (fixedNodes R) V L w (131072 + D.height + s) hv
    (fun l => contraction_degree (amp_le A 0) (amp_le A 1) (hout 1 l) (hout 0 l))
    (by intro i hi j; simp only [L, w, eval_sub, eval_mul, hn i hi]; ring)
    (by change t < _; omega) (by change _ + t + _ ≤ _; omega)
  obtain ⟨Q, hQ, heQ⟩ := primitive_lift (fixedNodes R) A N z (131072 + D.height + t) B.α_primitive
    (fun j => contraction_degree (amp_le V 1) (amp_le V 0) (hout j 0) (hout j 1))
    (by intro i hi j; simp only [N, z, eval_sub, eval_mul, hn i hi]; ring)
    (by change s < _; omega) (by change _ + s + _ ≤ _; omega)
  change P.natDegree + t < 131072 + D.height + s at hP
  change Q.natDegree + s < 131072 + D.height + t at hQ
  let σ := RingEquiv.ofBijective twist ⟨twist.injective, Finite.surjective_of_injective twist.injective⟩
  let τ := σ.symm.toRingHom
  have hundo (x : K) : τ (twist x) = x := σ.symm_apply_apply x
  have hfixed (i : I) : τ (node i) = node i := by
    have hh : twist (node i) = node i := Native.native_domain_fixed i
    simpa only [hh] using hundo (node i)
  have hmap (F : (Polynomial K)) (i : I) : (F.map τ).eval (node i) = τ (F.eval (node i)) :=
    Strata.eval_coefficient_map τ _ _ (hfixed i)
  have hβ (l : Fin 2) (i : I) : (V l).eval (node i) = twist ((B.β l).eval (node i)) :=
    Strata.eval_coefficient_map twist _ _ (Native.native_domain_fixed i)
  let b := B.b.map τ
  let Q' := Q.map τ
  have heQ' (i : I) (hi : i ∉ fixedNodes R) : Q'.eval (node i) = b.eval (node i) *
      ((B.β 0).eval (node i) * u 1 i - (B.β 1).eval (node i) * u 0 i) := by
    rw [show Q'.eval (node i) = τ (Q.eval (node i)) from hmap Q i, heQ i hi]
    change τ (B.b.eval (node i) * ((V 0).eval (node i) * twist (u 1 i) -
      (V 1).eval (node i) * twist (u 0 i))) = _
    simp only [b, hmap, hβ, map_mul, map_sub, hundo]
  let det := A 0 * B.β 1 - A 1 * B.β 0
  let denom := B.a * b * det
  let num := fun j => b * B.β j * P - B.a * A j * Q'
  have hb' : b.natDegree = B.b.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hQ' : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hvdeg (j : Fin 2) : (B.β j).natDegree ≤ t := ht ▸ amp_le B.β j
  have hadeg (j : Fin 2) : (A j).natDegree ≤ s := amp_le A j
  have ddet : det.natDegree ≤ s + t := (natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 0) (hvdeg 1)))
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 1) (hvdeg 0))))
  refine ⟨⟨denom, mul_ne_zero (mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff τ.injective).mpr B.b_ne)) hnp,
    ?_, num, ?_, ?_⟩⟩
  · calc
      denom.natDegree ≤ B.a.natDegree + b.natDegree + det.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
      _ ≤ 2 * D.height := by omega
  · intro j
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show (num j).natDegree < 131072 + 2 * D.height from by
      apply (natDegree_sub_le _ _).trans_lt
      apply max_lt
      · have := hvdeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega)
      · have := hadeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega))
  · intro i hi j
    fin_cases j
    · change denom.eval (node i) * u 0 i = (num 0).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
    · change denom.eval (node i) * u 1 i = (num 1).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
end
end Front6960_3
end
section
namespace Front6960_3
noncomputable section
open Front6960
open P1_3 (Bank)
open scoped BigOperators
open P1_3 (jet_quotient)
open P0_6 (sum_rows ceil_sq_div_eq)
private theorem source_st : K1_10.sourceDim sourceCutoff 5 20 17 = 1980273442 := by
  let rows : Fin 6 → ℕ := ![812952651, 547908600, 339148214, 183717540, 78138341, 18408096]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1980273442 := by decide
private theorem source_ts : K1_10.sourceDim sourceCutoff 5 17 20 = 1980273442 := by
  let rows : Fin 6 → ℕ := ![823693176, 548867355, 335619008, 179421330, 75223232, 17449341]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 6, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 1980273442 := by decide
private theorem multiple_st : K1_10.sourceDim 563827 4 19 16 = 992329821 := by
  let rows : Fin 5 → ℕ := ![478743200, 290637034, 152129916, 60063703, 10755968]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 992329821 := by decide
private theorem multiple_ts : K1_10.sourceDim 563827 4 16 19 = 992329821 := by
  let rows : Fin 5 → ℕ := ![483861650, 290087872, 149807955, 58290904, 10281440]
  unfold K1_10.sourceDim
  calc
    _ = ∑ i : Fin 5, rows i := by
      refine sum_rows _ rows ?_
      intro i
      fin_cases i <;> decide
    _ = 992329821 := by decide
private theorem source_corner (bank : Bank) :
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second = 1980273442 := by
  cases bank
  · exact source_st
  · exact source_ts
private theorem multiple_corner (bank : Bank) :
    K1_10.sourceDim 563827 4 (bank.first - 1) (bank.second - 1) = 992329821 := by
  cases bank
  · exact multiple_st
  · exact multiple_ts
theorem minimum_surplus (bank : Bank) :
    K1_10.sourceDim sourceCutoff 5 bank.first bank.second -
      K1_10.sourceDim 563827 4 (bank.first - 1) (bank.second - 1) =
      blockLength * 3765 + 971461 := by
  rw [source_corner, multiple_corner]
  decide
theorem bank_surplus (bank : Bank) (n h : ℕ) (hn : n ≤ blockLength) (hh : 24373 ≤ h) :
    quotientSurplus bank n h := by
  let s := bank.first - 1
  let t := bank.second - 1
  have hm : K1_10.sourceDim (sourceCutoff - (k - 1) - h) 4 s t ≤
      K1_10.sourceDim 563827 4 s t := by
    have hcut : sourceCutoff - (k - 1) - 24373 = 563827 := by decide
    rw [← hcut]
    unfold K1_10.sourceDim
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.sub_le_sub_left hh _) _) _))
  unfold quotientSurplus
  rw [jet_quotient]
  have hd := minimum_surplus bank
  have hs : n * 3765 ≤ blockLength * 3765 := Nat.mul_le_mul_right _ hn
  calc
    n * 3765 ≤ blockLength * 3765 := hs
    _ < blockLength * 3765 + 971461 := Nat.lt_add_of_pos_right (by decide)
    _ = _ := hd.symm
    _ ≤ _ := Nat.sub_le_sub_left hm _
theorem regularPrice_exact : regularPrice = 175383076967335670 := by
  unfold regularPrice incidenceRatio
  exact ceil_sq_div_eq 0x147ffafff86 48747 210 175383076967335670
    (by decide) (by decide) (by decide) (by decide)
theorem bank_price_le (bank : Bank) : regularPrice + bank.graphFee ≤ 250000000000000000 := by
  rw [regularPrice_exact]
  cases bank <;> decide
end
end Front6960_3
end
section
namespace Front6960_3
noncomputable section
open Front6960 FrobeniusLocator ProximityPrize.Benchmark Polynomial
open P1_3 (Adjugate)
open P0_6 (natDegree_lt_of_degree_lt_pos)
theorem mark_disjoint {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {γ : K} (hn : Normal u γ) (M : BadMark u γ) :
    Disjoint M.support (fixedNodes R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hfix
  exact D.deleted_error γ hn M i hfix (M.hits i hi)
theorem no_small_normal {u : Words} (T : TwoActive u) {R : Relation T}
    (D : Reduction u T R) (J : Adjugate u (fixedNodes R) D.height)
    (hsmall : 2 * D.height < Front6960.L) {γ : K} (hn : Normal u γ) (M : BadMark u γ) : False := by
  classical
  let F := J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder
  have hfit : Front6960.k + 2 * D.height < Front6960.agreement := by
    have hsum : Front6960.k + Front6960.L = Front6960.agreement := by decide
    omega
  have hdeg : F.natDegree < Front6960.agreement := by
    have hj (j : Fin 2) : (J.numer j).natDegree < Front6960.k + 2 * D.height :=
      natDegree_lt_of_degree_lt_pos (by
        have hk : 0 < Front6960.k := by decide
        omega) (J.numer_degree j)
    have hP : M.decoder.natDegree < Front6960.k := natDegree_lt_of_degree_lt_pos (by decide) M.degree
    have hnum := (natDegree_add_le (J.numer 0) (C γ * J.numer 1)).trans
      (max_le_max_left _ (natDegree_C_mul_le γ (J.numer 1)))
    have hprod := natDegree_mul_le (p := J.denom) (q := M.decoder)
    have hsub := natDegree_sub_le (J.numer 0 + C γ * J.numer 1) (J.denom * M.decoder)
    change (J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder).natDegree < Front6960.agreement
    have := J.denom_degree
    apply hsub.trans_lt
    apply max_lt
    · exact hnum.trans_lt (max_lt (by have := hj 0; omega) (by have := hj 1; omega))
    · exact hprod.trans_lt (by omega)
  have hF : F = 0 := by
    by_contra hf
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective F hf M.support
      (by
        intro i hi
        have hd : i ∉ fixedNodes R := fun h => (Finset.disjoint_left.mp (mark_disjoint D hn M)) hi h
        simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd, M.hits i hi]
        ring)
    have := M.agreement
    omega
  let zeros := Finset.univ.filter (fun i : I => J.denom.eval (node i) = 0)
  let E := fixedNodes R ∪ zeros
  have hZ : zeros.card ≤ J.denom.natDegree := Strata.root_nodes_card_le node
    IRSProfile.domain.injective _ J.nonzero zeros (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hE : E.card ≤ (fixedNodes R).card + 2 * D.height := (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (hZ.trans J.denom_degree) _)
  have hoff (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    have hd : i ∉ fixedNodes R := fun h => hi (Finset.mem_union_left _ h)
    have hz : J.denom.eval (node i) ≠ 0 :=
      fun h => hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hf : F.eval (node i) = 0 := by rw [hF, eval_zero]
    simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd] at hf
    apply mul_left_cancel₀ hz
    linear_combination hf
  have hbal := relation_height_balance T
  have hheight := D.height_eq
  have hs := actual_stackRank u
  have hcard : Front6960.k + Front6960.L + Front6960.t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have hfix (b : Fin 2) (i : I) : iterateFrobenius K p b.val (node i) = node i := by
    fin_cases b
    · exact iterateFrobenius_zero_apply K p _
    · exact (iterateFrobenius_one_apply K p _).trans (Native.native_domain_fixed i)
  change ((stacked p node (u 0) (u 1) Front6960.L Front6960.t).map (evalRingHom γ)).rank = stackRank u at hn
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval,
    Strata.conjugateHankel_error_rank _ node _ IRSProfile.domain.injective hfix M.decoder
      Front6960.k Front6960.L Front6960.t M.degree hcard E (by omega) hoff] at hn
  have hr := Matrix.rank_le_card_width (Strata.conjugateErrors
    (fun b : Fin 2 => iterateFrobenius K p b.val) (fun i : E => node i.val)
    (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) Front6960.L)
  rw [Fintype.card_coe, hn] at hr
  have hsize : 2 * D.height + (fixedNodes R).card < stackRank u := by
    omega
  omega
end
end Front6960_3
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front6960_3
noncomputable section
open Front6960 Polynomial FrobeniusLocator
open P1_3 (Plane)
open P0_6 (column column_ne column_bound column_dvd firstColumn_normal threeU_fun tight_pair outputs slice_bound nodes_of_columns relationOn_fun)
private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))
private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring
theorem plane_of_rankThree {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} (B : RankThree u T R D) :
    Nonempty (Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) := by
  let U := leftCoeff B
  let V := rightCoeff B
  have amp_ne (v : Fin 2 → (Polynomial K)) (hv : IsCoprime (v 0) (v 1)) : ∃ j, v j ≠ 0 := by
    by_contra! hz
    obtain ⟨a,b,hab⟩ := hv
    simp [hz] at hab
  obtain ⟨l,hl⟩ := amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩ := amp_ne B.α B.α_primitive
  have hU : ∃ l, U l ≠ 0 :=
    ⟨l, mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hl)⟩
  have hV : ∃ j, V j ≠ 0 := ⟨j, neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu : amplitudeDegree (U 0) (U 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply Nat.add_le_add_left
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv : amplitudeDegree (V 0) (V 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      simp only [V, rightCoeff, natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply Nat.add_le_add_left
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ := algebraMap (Polynomial K) Frac
  have hinj : Function.Injective φ := IsFractionRing.injective (Polynomial K) Frac
  have hd (P : Bivar) : (extendSeed P).natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hn {P : Bivar} (hp : P ≠ 0) : extendSeed P ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hdir := B.same_direction
  rw [sameDirection, left_eq, right_eq] at hdir
  have he := congrArg (Polynomial.map φ) hdir
  simp only [Polynomial.map_mul] at he
  have hdom := max_le_max (column_bound p U) (column_bound 1 V)
  obtain ⟨htight,hcp⟩ := tight_pair (extendSeed D.U) (extendSeed D.V)
    (extendSeed (column p U)) (extendSeed (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (column_ne (by decide : p ≠ 0) hU)) D.coprime he
    (by simp only [hd, D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd, D.max_degree] at htight
  refine ⟨⟨outputs p B.output, hU, hV, ?_, ?_, ?_, ?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit := hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (column_dvd p U f hfU))
      ((mapRingHom φ).map_dvd (column_dvd 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map Polynomial.C).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective Polynomial.C_injective] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht : B.output.natDegree < P0.k + D.height := by
      by_cases hz : B.output = 0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (slice_bound B.output _).trans_lt ht
  · apply nodes_of_columns p (by decide) u (fixedNodes R) U V B.output
    have h := B.nodes
    rwa [relationOn_fun, left_eq, right_eq] at h
end
end Front6960_3
end
section
namespace Front6960_3
noncomputable section
open Front6960 Polynomial
open P1_3 (Bank Plane ScalarSource)
def c1 : Prop :=
  ∀ bank u deleted h U V, Plane u deleted h U V → 24373 ≤ h →
    h + deleted.card ≤ heightCap → quotientSurplus bank (blockLength - deleted.card) h →
    ∃ A : ScalarSource bank, ∀ γ (M : BadMark u γ), Disjoint M.support deleted →
      A.atDecoder γ M.decoder = 0
def c2 : Prop :=
  ∀ bank u (A : ScalarSource bank) (Γ : Finset K),
    (∀ γ ∈ Γ, A.atLabel γ ≠ 0 ∧ ∃ M : BadMark u γ, A.atDecoder γ M.decoder = 0) →
    Γ.card ≤ regularPrice
private theorem zero_specializations {bank : Bank} (A : ScalarSource bank) (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, A.atLabel γ = 0) : Γ.card ≤ bank.graphFee := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr A.nonzero
  have hlt : bank.first + 5 < p := by cases bank <;> decide
  apply K1_10.frobenius_coefficient_exception_count p (bank.first + 5) bank.second
    (by decide) (A.poly.coeff e) (MvPolynomial.mem_support_iff.mp he)
    (A.s_degree e he) hlt (A.t_degree e he) Γ
  intro γ hγ
  have hh := congrArg (fun P : MvPolynomial (Fin 2) K => P.coeff e) (hΓ γ hγ)
  simpa only [ScalarSource.atLabel, MvPolynomial.coeff_map,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hh
private theorem count_with_bank (h1 : c1) (h2 : c2) (bank : Bank) : Front6960.c3 := by
  classical
  intro u hu T R D B _hsat hnp Γ hΓ hn
  obtain ⟨W⟩ := plane_of_rankThree B
  have hh : D.height + (fixedNodes R).card ≤ heightCap :=
    D.height_eq ▸ relation_height_le hu T
  by_cases hsmall : 2 * D.height < L
  · have hshort := (shortened_guards D hu).1
    have hcap : heightCap ≤ blockLength := by decide
    have hroom : k + 3 * D.height + (fixedNodes R).card ≤ blockLength := by omega
    obtain ⟨J⟩ := adjugate_of_plane B hnp W hroom
    have hempty : Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
      exact no_small_normal T D J hsmall (hn γ hγ) M)
    simp [hempty]
  have hmin : 24373 ≤ D.height := by
    change ¬ 2 * D.height < 48746 at hsmall
    omega
  obtain ⟨A, hA⟩ := h1 bank u _ D.height _ _ W hmin hh
    (bank_surplus bank _ _ (Nat.sub_le _ _) hmin)
  let good := Γ.filter (fun γ => A.atLabel γ ≠ 0)
  let exc := Γ.filter (fun γ => ¬ A.atLabel γ ≠ 0)
  have hexc : exc.card ≤ bank.graphFee := zero_specializations A exc (by
    intro γ hγ
    exact not_ne_iff.mp (Finset.mem_filter.mp hγ).2)
  have hgood : good.card ≤ regularPrice := h2 bank u A good (by
    intro γ hγ
    obtain ⟨hγΓ, hnonzero⟩ := Finset.mem_filter.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact ⟨hnonzero, M, hA γ M (mark_disjoint D (hn γ hγΓ) M)⟩)
  have hsum : good.card + exc.card = Γ.card :=
    Finset.card_filter_add_card_filter_not (s := Γ) (p := fun γ => A.atLabel γ ≠ 0)
  exact hsum ▸ (Nat.add_le_add hgood hexc).trans (bank_price_le bank)
theorem of_children (h1 : c1) (h2 : c2) : Front6960.c3 :=
  count_with_bank h1 h2 .ts
end
end Front6960_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Front6960_3_1
noncomputable section
open MvPolynomial K1_11
open K1_10_1 (Contacts relationBounds)
open Front6960_3 (sourceCutoff)
open P1_3_1 (Multipliers)
open P1_3_1 (localMultiply LocalSpace local_finrank)
open P0_6_1 (exists_kernel_outside)
abbrev Source (F : Type*) [Field F] (bank : P1_3.Bank) :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
variable (bank : P1_3.Bank) (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
private def nodeMap (i : Fin N) : Source F bank →ₗ[F] LocalSpace bank C hdeg i :=
  (LinearMap.range (localMultiply bank C hdeg i)).mkQ.comp
    (sourceToJet sourceCutoff 131071 5 bank.first bank.second 3 (C.x i) (C.first i) (C.firstSlope i)
      (C.second i) (C.secondSlope i))
include hdeg in
theorem quotientSource (hL : L ≠ 0) (hh : h ≤ 33579) (hs : Front6960_3.quotientSurplus bank N h) :
    ∃ G : Source F bank, ¬ L ∣ G.val ∧ ∀ i, ∃ R : Multipliers F bank,
      C.shifted i G.val - C.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ j, relationBounds h j ≤ sourceBounds sourceCutoff 5 bank.first bank.second j := by
    have hcapacity : 131071 + 33579 ≤ sourceCutoff := by decide
    intro j
    cases bank <;> fin_cases j <;> simp [relationBounds, sourceBounds, P1_3.Bank.first, P1_3.Bank.second] <;> omega
  have hshift : (fun j => sourceBounds sourceCutoff 5 bank.first bank.second j - relationBounds h j) =
      sourceBounds (sourceCutoff - 131071 - h) 4 (bank.first - 1) (bank.second - 1) := by
    funext j
    fin_cases j <;> simp [sourceBounds, relationBounds, Nat.sub_sub]
    omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds sourceCutoff 5 bank.first bank.second)
    (relationBounds h) L hL hdeg hfit
  have hmult : Module.finrank F (LinearMap.range mult) =
      V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) := by
    rw [LinearMap.finrank_range_of_inj (filteredMul_injective _ _ _ L hL hdeg hfit),
      hshift, source_filtered_finrank]
  let (i : Fin N) : Module.Free F (LocalSpace bank C hdeg i) := Module.Free.of_divisionRing F _
  let : Module F (∀ i : Fin N, LocalSpace bank C hdeg i) := Pi.module _ _ _
  have hlocal : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) =
      N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) := by
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank bank C hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace bank C hdeg i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F bank) := by
    rw [hlocal, hmult, source_filtered_finrank]
    change N * (J 4 bank.first bank.second - J 3 (bank.first - 1) (bank.second - 1)) <
      V sourceCutoff 131071 5 bank.first bank.second -
        V (sourceCutoff - 131071 - h) 131071 4 (bank.first - 1) (bank.second - 1) at hs
    omega
  have hk := P0_6_1.exists_kernel_outside (G := ∀ i : Fin N, LocalSpace bank C hdeg i)
    (LinearMap.pi (nodeMap bank C hdeg)) (LinearMap.range mult) hdim
  obtain ⟨G, hG, hnot⟩ := hk
  refine ⟨G, (mem_filteredMul_range_iff _ _ _ L hL hdeg hfit G).not.mp hnot, ?_⟩
  intro i
  have hi : nodeMap bank C hdeg i G = 0 := congrFun hG i
  obtain ⟨R, hR⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm
end
end Front6960_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Front6960_3_1
noncomputable section
open MvPolynomial K1_11
open Front6960 (K I Words node p blockLength agreement twist heightCap BadMark)
open P1_3 (Plane)
open Front6960_3 (sourceCutoff)
open P1_3_1 (toScalarSource toScalarSource_atDecoder)
open K1_10_1 (Contacts denominator numerator planeRelation planeRelation_view relationBounds)
open P0_6_1 (coeff_bounds denominator_ne relation_eval)
open K1_11 (scalar_total_weight_le)
private theorem mark_degree {u : Words} {γ : K} (M : BadMark u γ) :
    M.decoder.natDegree ≤ 131071 := by
  apply Polynomial.natDegree_le_of_degree_le
  exact Order.le_of_lt_succ (show M.decoder.degree < (131072 : ℕ) from M.degree)
private theorem correctOn_mark {u : Words} {deleted : Finset I} (P : Puncture deleted)
    {γ : K} (M : BadMark u γ) :
    correctOn u P M.decoder (M.decoder.map twist) γ (γ ^ p) (indexedSupport P M.support) := by
  intro i hi
  have h := M.hits (P.index i) ((mem_indexedSupport P M.support i).mp hi)
  refine ⟨h, ?_⟩
  change (M.decoder.map twist).eval (node (P.index i)) =
    u 0 (P.index i) ^ p + γ ^ p * u 1 (P.index i) ^ p
  rw [FrobeniusLocator.Strata.eval_coefficient_map twist M.decoder _
    (FrobeniusLocator.Native.native_domain_fixed (P.index i)), h]
  simp only [map_add, map_mul, P0.twist, frobenius_def]
private theorem relation_at_decoder {u : Words} {deleted : Finset I} {h : ℕ}
    {U V : Fin 2 → Polynomial K} (W : Plane u deleted h U V) (P : Puncture deleted)
    (hdeg : (planeRelation U V W.output).weightedTotalDegree (sourceWeights 131071 0) ≤ 131071 + h)
    (hh : h ≤ 33579) (Q Q' : Polynomial K) (hq : Q.natDegree ≤ 131071)
    (hq' : Q'.natDegree ≤ 131071) (s t : K) (S : Finset (Fin P.N)) (hS : agreement ≤ S.card)
    (hc : correctOn u P Q Q' s t S) :
    aeval (decoderImages Q Q' s t) (planeRelation U V W.output) = 0 := by
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 1
  · intro j hj
    rw [pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, relation_eval]
    have hi : P.index j ∉ deleted := (P.retained _).mp ⟨j, rfl⟩
    have hcj := hc j hj
    change Q.eval (node (P.index j)) = u 0 (P.index j) + s * u 1 (P.index j) ∧
      Q'.eval (node (P.index j)) = u 0 (P.index j) ^ p + t * u 1 (P.index j) ^ p at hcj
    simp only [Puncture.nodes, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, hcj.1, hcj.2]
    linear_combination W.nodes _ hi 0 0 + s * W.nodes _ hi 1 0 +
      t * W.nodes _ hi 0 1 + (s * t) * W.nodes _ hi 1 1
  · have hd := decoder_eval_degree 131071 (131071 + h) _ hdeg Q Q' hq hq' s t
    have hcapacity : 131071 + 33579 < agreement := by decide
    omega
theorem proof : Front6960_3.c1 := by
  intro bank u deleted h U V W _ hh hs
  have hheight : h ≤ 33579 := by
    have hh' : h + deleted.card ≤ heightCap := hh
    change h + deleted.card ≤ 33579 at hh'
    omega
  let P := nativePuncture deleted
  let L := planeRelation U V W.output
  let a := numerator U W.output
  let b := denominator V
  have hb : b ≠ 0 := denominator_ne W.V_ne
  have hview : polynomialView L = Polynomial.C b * Polynomial.X - Polynomial.C a :=
    planeRelation_view U V W.output
  have hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j :=
    K1_10_1_1.proof u deleted h U V W
  have hl : L ≠ 0 := by
    intro hz
    have hpos := hdeg 1
    simp [hz, relationBounds, weightedTotalDegree] at hpos
  let C : Contacts P.N L :=
    ⟨P.nodes, fun i => u 0 (P.index i), fun i => u 1 (P.index i),
      fun i => u 0 (P.index i) ^ p, fun i => u 1 (P.index i) ^ p,
      fun i => K1_10_1_2.proof u deleted h U V W (P.index i) ((P.retained _).mp ⟨i, rfl⟩)⟩
  have hN : P.N = blockLength - deleted.card := by
    have hsize : P.N + deleted.card = blockLength := P.size
    omega
  obtain ⟨G, hnot, hcontacts⟩ := quotientSource bank C hdeg hl hheight (hN ▸ hs)
  let Q := scalarEliminant 5 G.val a b
  have hne : Q ≠ 0 := scalarEliminant_ne_zero sourceCutoff 131071 5 bank.first bank.second
    G.val L G.property hnot a b hb hview (K1_10_1_3.proof u deleted h U V W)
  have hLsource : L ∈ filtered (sourceWeights 131071) (sourceBounds (131071 + h) 1 1 1) := by
    apply (mem_filtered _ _ _).mpr
    intro j
    rw [hdeg j]
    rfl
  obtain ⟨haY, hbY, haS, hbS, haT, hbT⟩ := coeff_bounds L a b _ hLsource hview hb
  obtain ⟨hY, hS, hT⟩ := polynomialView_source_coefficients
    sourceCutoff 131071 5 bank.first bank.second G.val G.property
  have hy : Q.weightedTotalDegree scalarWeightY ≤ 5 :=
    clearedEval_weight_bound scalarWeightY 5 5 1 1 0 (polynomialView G.val) a b
      (by simpa using hY) haY hbY (by decide)
  have hs' : Q.weightedTotalDegree scalarWeightYS ≤ bank.first + 5 :=
    clearedEval_weight_bound scalarWeightYS 5 bank.first 0 1 1 (polynomialView G.val) a b
      (by simpa using hS) haS hbS (by decide)
  have ht' : Q.weightedTotalDegree scalarWeightT ≤ bank.second :=
    clearedEval_weight_bound scalarWeightT 5 bank.second 1 1 0 (polynomialView G.val) a b
      (by simpa using hT) haT hbT (by decide)
  have htotal : Q.weightedTotalDegree scalarWeightTotal ≤ 42 :=
    (scalar_total_weight_le Q _ _ hs' ht').trans (by cases bank <;> decide)
  refine ⟨toScalarSource Q hne hy hs' ht' htotal, ?_⟩
  intro γ M hdis
  rw [toScalarSource_atDecoder]
  let S := indexedSupport P M.support
  have hS' : agreement ≤ S.card := by
    rw [indexedSupport_card P M.support
      (fun i hi hid => Finset.disjoint_left.mp hdis hi hid)]
    exact M.agreement
  have hd := mark_degree M
  have hd' : (M.decoder.map twist).natDegree ≤ 131071 := Polynomial.natDegree_map_le.trans hd
  have hcorrect := correctOn_mark P M
  have hrel := relation_at_decoder W P (le_of_eq (hdeg 0)) hheight
    _ _ hd hd' γ (γ ^ p) S hS' hcorrect
  apply scalarEliminant_annihilates sourceCutoff 131071 5 bank.first bank.second
    G.val L G.property a b hview M.decoder (M.decoder.map twist) γ (γ ^ p) hrel
  apply eq_zero_of_many_contacts S P.nodes nodes_injective 4
  · intro i hi
    obtain ⟨R, hR⟩ := hcontacts i
    exact decoder_contact_multiplicity 4 _ _ _ _ _ γ (γ ^ p) _ _ G.val L R.val
      (hcorrect i hi).1 (hcorrect i hi).2 hrel hR
  · have hdG := decoder_eval_degree 131071 sourceCutoff G.val
      ((mem_filtered _ _ _).mp G.property 0) _ _ hd hd' γ (γ ^ p)
    have hcut : sourceCutoff < 4 * agreement := by decide
    omega
end
end Front6960_3_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace Front6960_3_2
noncomputable section
open Front6960 Polynomial MvPolynomial ProximityPrize.Benchmark
open P1_3 (cutDegree)
open P1_3_2 (nodeCut_degree)
open Front6960_3 (incidenceRatio)
open K1_10_2 (GenericRow point surface_count_with_terminal RegularRoot
  derivativeOrder toGeneric atTrajectory)
open scoped Polynomial
open P1_3_2 (assign_charts)
open K1_10_2_2 (nodeCut eval_nodeCut)
open K1_10_2 (derivativeOrder_degree eval_toGeneric)
private abbrev Marks (u : Words) (Γ : Finset K) := ∀ γ ∈ Γ, BadMark u γ
private structure TaylorCuts {u : Words} {Γ : Finset K} (F : Marks u Γ) where
  equation : I → GenericRow
  degree : ∀ i, (equation i).totalDegree ≤ cutDegree
  agrees : ∀ γ (hγ : γ ∈ Γ) i,
    MvPolynomial.eval (point γ (F γ hγ).decoder) (equation i) = 0 ↔
      (F γ hγ).decoder.eval (node i) = u 0 i + γ * u 1 i
private theorem pencil_count {u : Words} (Γ : Finset K) (F : Marks u Γ)
    (P Q : (Polynomial K)) (hP : P.degree < 131072) (hQ : Q.degree < 131072)
    (hpencil : ∀ γ (hγ : γ ∈ Γ), (F γ hγ).decoder = P + Polynomial.C γ * Q) :
    Γ.card ≤ 82327 := by
  classical
  rcases Γ.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
  · simp
  let S := (F r hr).support
  let mismatch (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {γ : K} (hγ : γ ∈ Γ) {i : I} (hi : i ∈ (F γ hγ).support) :
      P.eval (node i) + γ * Q.eval (node i) = u 0 i + γ * u 1 i := by
    simpa only [hpencil γ hγ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      using (F γ hγ).hits i hi
  have unique {γ δ : K} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) {i : I}
      (hi : i ∈ (F γ hγ).support) (hj : i ∈ (F δ hδ).support) (hm : mismatch i) :
      γ = δ := by
    by_contra hne
    have hγi := hits hγ hi
    have hδi := hits hδ hj
    have h := show (γ - δ) * (Q.eval (node i) - u 1 i) = 0 by
      linear_combination hγi - hδi
    have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at hγi
    exact hm.elim (fun hbad => hbad hγi) (fun hbad => hbad he)
  have witness (γ : ↥(Γ.erase r)) :
      ∃ i ∈ (F γ.val (Finset.mem_erase.mp γ.property).2).support, mismatch i := by
    let M := F γ.val (Finset.mem_erase.mp γ.property).2
    by_contra hw
    apply M.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose index hindex hmismatch using witness
  let f : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun γ =>
    ⟨index γ, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp γ.property).1
        (unique (Finset.mem_erase.mp γ.property).2 hr (hindex γ) hi (hmismatch γ))⟩⟩
  have hf : Function.Injective f := by
    intro γ δ h
    have he : index γ = index δ := congrArg Subtype.val h
    have hδ := hindex δ
    rw [← he] at hδ
    exact Subtype.ext (unique (Finset.mem_erase.mp γ.property).2
      (Finset.mem_erase.mp δ.property).2 (hindex γ) hδ (hmismatch γ))
  have hcard := Finset.card_le_card_of_injective hf
  have he := Finset.card_erase_add_one hr
  have hS : 179818 ≤ S.card := (F r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index] at hcard
  omega
private theorem persistent_count {u : Words} {Γ : Finset K} {F : Marks u Γ}
    (C : TaylorCuts F) (J : Ideal GenericRow) (W : Finset K) (hW : W ⊆ Γ)
    (hzero : ∀ γ (hγ : γ ∈ W), point γ (F γ (hW hγ)).decoder ∈ zeroLocus Frac J)
    (hpersistent : 131072 ≤ {i | C.equation i ∈ J}.ncard) :
    W.card ≤ 82327 := by
  classical
  let keep := Finset.univ.filter fun i => C.equation i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersistent.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P := Lagrange.interpolate S node (u 0)
  let Q := Lagrange.interpolate S node (u 1)
  have hinj : Set.InjOn node (S : Set I) := node.injective.injOn
  have hP : P.degree < (131072 : ℕ) := by
    simpa only [P, hcard] using Lagrange.degree_interpolate_lt (u 0) hinj
  have hQ : Q.degree < (131072 : ℕ) := by
    simpa only [Q, hcard] using Lagrange.degree_interpolate_lt (u 1) hinj
  apply pencil_count W (fun γ hγ => F γ (hW hγ)) P Q hP hQ
  intro γ hγ
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact (F γ (hW hγ)).degree
  · rw [hcard]
    have hm : (Polynomial.C γ * Q).degree ≤ Q.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) Q.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hP (hm.trans_lt hQ))
  · intro i hi
    have hcut := (Finset.mem_filter.mp (hS hi)).2
    have hz := hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (C.agrees γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])
private theorem terminal_price_le : (82327 : ℚ) ≤ incidenceRatio := by
  change ((82327 : ℕ) : ℚ) ≤ ((0x147ffafff86 : ℕ) : ℚ) / ((48747 : ℕ) : ℚ)
  apply (le_div_iff₀ (by positivity)).mpr
  exact_mod_cast (show (82327 : ℕ) * 48747 ≤ 0x147ffafff86 by decide)
private theorem node_incidence (m : ℕ) (hm : m < 131072) :
    (((Fintype.card I - m) * cutDegree : ℕ) : ℚ) ≤
      incidenceRatio * ((179818 - m : ℕ) : ℚ) := by
  rw [IRSProfile.card_index, Nat.cast_mul]
  have hn : (262144 - m) * 48747 ≤ 131073 * (179818 - m) := by omega
  have hq : ((262144 - m : ℕ) : ℚ) * 48747 ≤ 131073 * ((179818 - m : ℕ) : ℚ) := by
    exact_mod_cast hn
  change ((262144 - m : ℕ) : ℚ) * (cutDegree : ℚ) ≤
    (((131073 : ℕ) * cutDegree : ℕ) : ℚ) / 48747 * ((179818 - m : ℕ) : ℚ)
  rw [Nat.cast_mul, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (((262144 - m : ℕ) : ℚ) * 48747) * (cutDegree : ℚ) := by ring
    _ ≤ (131073 * ((179818 - m : ℕ) : ℚ)) * (cutDegree : ℚ) :=
      mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring
private theorem count_chart {u : Words} {Γ : Finset K} (F : Marks u Γ) (C : TaylorCuts F)
    (g s : GenericRow) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ 42)
    (hroot : ∀ γ (hγ : γ ∈ Γ), MvPolynomial.eval (point γ (F γ hγ).decoder) g = 0 ∧
      MvPolynomial.eval (point γ (F γ hγ).decoder) s ≠ 0) :
    (Γ.card : ℚ) ≤ 42 * incidenceRatio ^ 2 := by
  classical
  let x : Γ → (Fin 3 → Frac) := fun γ => point γ (F γ γ.property).decoder
  have hinj : Function.Injective x := by
    intro γ δ h
    apply Subtype.ext
    apply Polynomial.C_injective
    apply IsFractionRing.injective (Polynomial K) Frac
    exact congrFun h 1
  let S := Γ.attach.image x
  have hcard : S.card = Γ.card := by
    simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [← hcard]
  refine surface_count_with_terminal g s hg C.equation (L := 131072) (A := 179818)
    (by decide) hdeg C.degree ((by norm_num : (1 : ℚ) ≤ 82327).trans terminal_price_le)
    node_incidence S
    (fun y hy => ?_) (fun y hy => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    exact hroot γ γ.property
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    let M := F γ γ.property
    have hsub : (M.support : Set I) ⊆ {i | aeval (x γ) (C.equation i) = 0} :=
      fun i hi => (C.agrees γ γ.property i).mpr (M.hits i hi)
    exact M.agreement.trans (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub)
  · let W := Γ.attach.filter fun γ => x γ ∈ zeroLocus Frac J
    let V := W.image (fun γ : Γ => (γ : K))
    have hV : V ⊆ Γ := fun γ hγ => by
      obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ
      exact δ.property
    have hV0 : ∀ γ (hγ : γ ∈ V), point γ (F γ (hV hγ)).decoder ∈ zeroLocus Frac J := by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ
      exact (Finset.mem_filter.mp hδ).2
    have hcount := persistent_count C J V hV hV0 hJ
    have hW : W.card = V.card := (Finset.card_image_of_injective W Subtype.val_injective).symm
    have he : (S : Set (Fin 3 → Frac)) ∩ zeroLocus Frac J = (W.image x : Finset _) := by
      ext y
      simp only [S, W, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨γ, hγ, rfl⟩, h⟩
        exact ⟨γ, ⟨hγ, h⟩, rfl⟩
      · rintro ⟨γ, ⟨hγ, h⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, h⟩
    rw [he, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, hW]
    exact (by exact_mod_cast hcount : (V.card : ℚ) ≤ 82327).trans terminal_price_le
theorem proof : Front6960_3.c2 := by
  classical
  intro bank u A Γ hΓ
  let F : Marks u Γ := fun γ hγ => Classical.choose (hΓ γ hγ).2
  have hF (γ : K) (hγ : γ ∈ Γ) :
      A.atLabel γ ≠ 0 ∧ A.atDecoder γ (F γ hγ).decoder = 0 :=
    ⟨(hΓ γ hγ).1, Classical.choose_spec (hΓ γ hγ).2⟩
  obtain ⟨g, hg, hassign⟩ := assign_charts A Γ (fun γ hγ => (F γ hγ).decoder) hF
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, RegularRoot (derivativeOrder g j) γ (F γ hγ).decoder
  have hsub (j : Fin 5) : charts j ⊆ Γ := Finset.filter_subset _ _
  have hcover : Γ ⊆ Finset.univ.biUnion charts := by
    intro γ hγ
    obtain ⟨j, hj⟩ := hassign γ hγ
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  have hchart (j : Fin 5) : ((charts j).card : ℚ) ≤ 42 * incidenceRatio ^ 2 := by
    rcases (charts j).eq_empty_or_nonempty with hempty | ⟨γ₀, hγ₀⟩
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    let G := derivativeOrder g j
    let M : Marks u (charts j) := fun γ hγ => F γ (hsub j hγ)
    have hregular (γ : K) (hγ : γ ∈ charts j) : RegularRoot G γ (M γ hγ).decoder := by
      obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hγ).2
      exact hr
    have hG : G.totalDegree ≤ 42 := (derivativeOrder_degree g j).trans hg
    let C : TaylorCuts M :=
      ⟨nodeCut u G, nodeCut_degree u G hG, fun γ hγ i =>
        eval_nodeCut u G γ (M γ hγ).decoder (hregular γ hγ) (M γ hγ).degree i⟩
    have hinj := IsFractionRing.injective (Polynomial K) Frac
    have hGne : G ≠ 0 := by
      intro h
      exact (hregular γ₀ hγ₀).2 (by simp [h, atTrajectory])
    have hgne : toGeneric G ≠ 0 := by
      intro h
      exact hGne (MvPolynomial.map_injective (algebraMap (Polynomial K) Frac) hinj
        (by simpa [toGeneric] using h))
    have hgd : (toGeneric G).totalDegree ≤ 42 := by
      simpa only [toGeneric, totalDegree, support_map_of_injective G hinj] using hG
    apply count_chart M C (toGeneric G) (toGeneric (MvPolynomial.pderiv 0 G)) hgne hgd
    intro γ hγ
    obtain ⟨hr, hs⟩ := hregular γ hγ
    rw [K1_10_2.eval_toGeneric, K1_10_2.eval_toGeneric, hr, map_zero]
    exact ⟨rfl, by simpa only [map_zero] using hinj.ne hs⟩
  have hnat : Γ.card ≤ ∑ j : Fin 5, (charts j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrat : (Γ.card : ℚ) ≤ 5 * 42 * incidenceRatio ^ 2 := by
    calc
      (Γ.card : ℚ) ≤ ∑ j : Fin 5, ((charts j).card : ℚ) := by exact_mod_cast hnat
      _ ≤ ∑ _j : Fin 5, (42 * incidenceRatio ^ 2 : ℚ) :=
        Finset.sum_le_sum fun j _ => hchart j
      _ = _ := by simp; ring
  have hrounded : (Γ.card : ℚ) ≤ (Front6960_3.regularPrice : ℚ) := by
    unfold Front6960_3.regularPrice
    apply hrat.trans
    rw [show (5 : ℚ) * 42 = ((210 : ℕ) : ℚ) by norm_num]
    exact Nat.le_ceil _
  exact_mod_cast hrounded
end
end Front6960_3_2
end

end Merged6967_R6960Front6960Rank3
