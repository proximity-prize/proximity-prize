import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BCHKSBridge

/-!
# From the selected-polynomial counting theorem to the stock alignment target

Model label: gpt-5.

The sole counting input says that a selected family with no base-field
polynomial pencil containing more than e+1 selections has at most B seeds.
It quantifies over actual degree-bounded polynomials agreeing on the caller's
original supports. It does not assume affine-line alignment, an interpolant,
a geometric component cover, or a replacement support.

Projected RS membership constructs the selected polynomials. Contraposition
produces an actual large polynomial pencil and thus the stock alignment
predicate. The elementary stock incidence theorem then gives both received
rows on one ORIGINAL supplied support. The score-64 alignment theorem remains
conditional on this explicit, still-to-be-assembled counting input. No final
protocol claim is proved here.
-/

namespace ProximityPrize.SubmissionLower.ContactAlignmentBridge

open ProximityPrize.Benchmark

noncomputable section

variable {ι K : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

def pencilSeeds (seeds : Finset K) (selected : K → Polynomial K)
    (P₀ P₁ : Polynomial K) : Finset K := by
  classical
  exact seeds.filter (fun γ => selected γ = P₀ + Polynomial.C γ * P₁)

/-- Exact uniform selected-family theorem to be supplied by the counting
pipeline. The no-large-pencil premise concerns actual polynomial equality. -/
def SelectedNoLargePencilBound (domain : ι ↪ K) (w e B : ℕ) : Prop :=
  ∀ (U : Fin 2 → ι → K) (seeds : Finset K) (A : K → Finset ι)
    (selected : K → Polynomial K),
    (∀ γ ∈ seeds, (selected γ).natDegree ≤ w) →
    (∀ γ ∈ seeds, Fintype.card ι - e ≤ (A γ).card) →
    (∀ γ ∈ seeds, ∀ i ∈ A γ,
      (selected γ).eval (domain i) = U 0 i + γ * U 1 i) →
    (∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (pencilSeeds seeds selected P₀ P₁).card ≤ e + 1) →
    seeds.card ≤ B

theorem degree_lt_succ_of_natDegree_le (P : Polynomial K) (w : ℕ)
    (hdegree : P.natDegree ≤ w) : P.degree < ((w + 1 : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne P 0 with hzero | hnonzero
  · simp [hzero]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hnonzero]
    omega

/-- The codeword and polynomial are chosen from projected-code membership;
the original support A(γ) is never enlarged, shrunk, or replaced. -/
theorem exists_selected_polynomials
    (domain : ι ↪ K) (w : ℕ) (U : Fin 2 → ι → K)
    (seeds : Finset K) (A : K → Finset ι)
    (hprojected : ∀ γ ∈ seeds,
      LinearCode.projectedWord (fun i => U 0 i + γ * U 1 i) (A γ) ∈
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w + 1)) (A γ)) :
    ∃ selected : K → Polynomial K,
      (∀ γ ∈ seeds, (selected γ).natDegree ≤ w) ∧
      (∀ γ ∈ seeds, ∀ i ∈ A γ,
        (selected γ).eval (domain i) = U 0 i + γ * U 1 i) := by
  classical
  have hexists (γ : K) (hγ : γ ∈ seeds) : ∃ P : Polynomial K,
      P.natDegree ≤ w ∧ ∀ i ∈ A γ, P.eval (domain i) = U 0 i + γ * U 1 i := by
    have hc := hprojected γ hγ
    rw [LinearCode.mem_projectedCodeSubmod_iff] at hc
    obtain ⟨c, hcode, hvalue⟩ := hc
    change c ∈ ReedSolomon.code domain (w + 1) at hcode
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcode
    obtain ⟨P, hdegree, rfl⟩ := hcode
    refine ⟨P, ?_, ?_⟩
    · rcases eq_or_ne P 0 with hzero | hnonzero
      · simp [hzero]
      · have hd : P.natDegree < w + 1 :=
          (Polynomial.natDegree_lt_iff_degree_lt hnonzero).mpr hdegree
        omega
    · intro i hi
      have hh := congrFun hvalue ⟨i, hi⟩
      simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints] using hh.symm
  let selected : K → Polynomial K := fun γ =>
    if hγ : γ ∈ seeds then Classical.choose (hexists γ hγ) else 0
  have hspec (γ : K) (hγ : γ ∈ seeds) :
      (selected γ).natDegree ≤ w ∧
        ∀ i ∈ A γ, (selected γ).eval (domain i) = U 0 i + γ * U 1 i := by
    simpa only [selected, dif_pos hγ] using Classical.choose_spec (hexists γ hγ)
  exact ⟨selected, fun γ hγ => (hspec γ hγ).1, fun γ hγ => (hspec γ hγ).2⟩

theorem exists_large_pencil_of_selected_count
    (domain : ι ↪ K) (w e B : ℕ)
    (hcount : SelectedNoLargePencilBound domain w e B)
    (U : Fin 2 → ι → K) (seeds : Finset K) (A : K → Finset ι)
    (selected : K → Polynomial K) (hlarge : B < seeds.card)
    (hdegree : ∀ γ ∈ seeds, (selected γ).natDegree ≤ w)
    (hcard : ∀ γ ∈ seeds, Fintype.card ι - e ≤ (A γ).card)
    (hagreement : ∀ γ ∈ seeds, ∀ i ∈ A γ,
      (selected γ).eval (domain i) = U 0 i + γ * U 1 i) :
    ∃ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w ∧ P₁.natDegree ≤ w ∧
      e + 1 < (pencilSeeds seeds selected P₀ P₁).card := by
  by_contra hno
  have hsmall : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (pencilSeeds seeds selected P₀ P₁).card ≤ e + 1 := by
    intro P₀ P₁ h₀ h₁
    apply Nat.le_of_not_gt
    intro hh
    exact hno ⟨P₀, P₁, h₀, h₁, hh⟩
  have hh := hcount U seeds A selected hdegree hcard hagreement hsmall
  omega

/-- Actual selected-polynomial counting implies the unmodified stock
affine-line alignment predicate for the RS code. -/
theorem alignmentBound_of_selected_count
    (domain : ι ↪ K) (w e B : ℕ)
    (hcount : SelectedNoLargePencilBound domain w e B) :
    AffineLineAlignmentBound (ReedSolomon.code domain (w + 1)) e B := by
  classical
  intro U seeds A hlarge hcard hprojected
  obtain ⟨selected, hdegree, hagreement⟩ := exists_selected_polynomials domain w U seeds A hprojected
  obtain ⟨P₀, P₁, h₀, h₁, hTcard⟩ := exists_large_pencil_of_selected_count
    domain w e B hcount U seeds A selected hlarge hdegree hcard hagreement
  let T := pencilSeeds seeds selected P₀ P₁
  have hTsub : T ⊆ seeds := Finset.filter_subset _ _
  let rows : Fin 2 → ι → K :=
    ![ReedSolomon.evalOnPoints domain P₀, ReedSolomon.evalOnPoints domain P₁]
  refine ⟨rows, ?_, T, hTsub, hTcard, ?_⟩
  · intro j
    fin_cases j
    · change ReedSolomon.evalOnPoints domain P₀ ∈ ReedSolomon.code domain (w + 1)
      exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
        (degree_lt_succ_of_natDegree_le P₀ w h₀)
    · change ReedSolomon.evalOnPoints domain P₁ ∈ ReedSolomon.code domain (w + 1)
      exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
        (degree_lt_succ_of_natDegree_le P₁ w h₁)
  · intro γ hγ i hi
    have hpoly : selected γ = P₀ + Polynomial.C γ * P₁ := (Finset.mem_filter.mp hγ).2
    have heval := congrArg (Polynomial.eval (domain i)) hpoly
    have hword := hagreement γ (hTsub hγ) i hi
    simpa [rows, ReedSolomon.evalOnPoints] using hword.symm.trans heval

/-- Explicit stock incidence finish on one of the caller's ORIGINAL
agreement supports, with both original received rows explained there. -/
theorem exists_original_support_of_selected_count
    (domain : ι ↪ K) (w e B : ℕ)
    (hcount : SelectedNoLargePencilBound domain w e B)
    (U : Fin 2 → ι → K) (seeds : Finset K) (A : K → Finset ι)
    (hlarge : B < seeds.card)
    (hcard : ∀ γ ∈ seeds, Fintype.card ι - e ≤ (A γ).card)
    (hprojected : ∀ γ ∈ seeds,
      LinearCode.projectedWord (fun i => U 0 i + γ * U 1 i) (A γ) ∈
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w + 1)) (A γ)) :
    ∃ γ ∈ seeds, ∀ j : Fin 2,
      LinearCode.projectedWord (U j) (A γ) ∈
        LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w + 1)) (A γ) := by
  classical
  obtain ⟨rows, hrows, T, hTsub, hTcard, hEq⟩ :=
    alignmentBound_of_selected_count domain w e B hcount U seeds A hlarge hcard hprojected
  obtain ⟨γ, hγ, hcommon⟩ := ProximityPrize.SubmissionLower.exists_common_affine_set
    U rows T A e hTcard (fun z hz => hcard z (hTsub hz)) hEq
  refine ⟨γ, hTsub hγ, fun j => ?_⟩
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  refine ⟨rows j, hrows j, ?_⟩
  funext i
  simp only [LinearCode.projectedWord]
  obtain ⟨h₀, h₁⟩ := hcommon i.1 i.2
  fin_cases j
  · exact h₀
  · exact h₁

def SelectedNoLargePencilBound6400 : Prop :=
  SelectedNoLargePencilBound IRSProfile.domain 131071 76780 274980728111352763

theorem alignmentBound6400_of_selected_count
    (hcount : SelectedNoLargePencilBound6400) :
    AffineLineAlignmentBound IRSProfile.baseCode 76780 274980728111352763 := by
  change AffineLineAlignmentBound (ReedSolomon.code IRSProfile.domain (131071 + 1))
    76780 274980728111352763
  exact alignmentBound_of_selected_count IRSProfile.domain 131071 76780
    274980728111352763 hcount

#print axioms exists_selected_polynomials
#print axioms exists_large_pencil_of_selected_count
#print axioms alignmentBound_of_selected_count
#print axioms exists_original_support_of_selected_count
#print axioms alignmentBound6400_of_selected_count

end
end ProximityPrize.SubmissionLower.ContactAlignmentBridge
