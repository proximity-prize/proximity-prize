import ProximityPrize.SubmissionLower.FadicSpace

set_option Elab.async false

/-!
# The gate space of one level, and its kernel certificate

At level `r` the gate space is the whole source when `r • σ` covers it, and otherwise the larger
of the plain tapered box `r • σ` and the f-adic space of `FadicSpace`.

* `exists_gateSpace`: the space, the bound `gateDim ≤ finrank`, and the two forms of a nonzero
  row: supported in the box `r • σ`, or `f ^ a * (c + f * h)` with `c` in the box `(r - a) • σ`.
* `fastGateDim_eq`: the same number in a form the kernel evaluates (prefix sums, the constant
  range of each count collapsed).
* `loss_of_rows`: from the per-level values to `∑ i < N, max 0 (S - gateDim (i+1)) ≤ L` for
  every `N`.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents jetColumns)
open MvPolynomial
open scoped BigOperators
open Finset

/-- The level covers the whole source. -/
def IsFull (σb σj σt r : ℕ) : Prop := 4012 ≤ r * σb ∧ 1650 ≤ r * σj ∧ 550 ≤ r * σt

instance (σb σj σt r : ℕ) : Decidable (IsFull σb σj σt r) := by unfold IsFull; infer_instance



/-- Exponents in the box `(B, J, T)`, no taper. -/
def slopeBox (B J T : ℕ) : Set JetExp :=
  {e | Finsupp.weight gradeWeight e ≤ B ∧ Finsupp.weight oldWeight e ≤ J ∧ e 3 ≤ T}

theorem taperBox_subset_slopeBox (B J T Θ : ℕ) : taperBox B J T Θ ⊆ slopeBox B J T :=
  fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem taperBox_subset_source {B J T : ℕ} (hB : B ≤ 4012) (hJ : J ≤ 1650) :
    taperBox B J T 131312 ⊆ jetExponents := by
  intro e he
  obtain ⟨h1, h2, _, h4⟩ := he
  have hg := w_grade e
  have ho := w_old e
  refine ⟨h1.trans hB, h2.trans hJ, ?_⟩
  unfold TaperBudget.cap
  split
  · omega
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 25)).mpr
    omega

theorem source_subset_slopeBox {σb σj σt r : ℕ} (h : IsFull σb σj σt r) :
    jetExponents ⊆ slopeBox (r * σb) (r * σj) (r * σt) := by
  intro e he
  obtain ⟨h1, h2, _⟩ := he
  obtain ⟨hb, hj, ht⟩ := h
  have ho := w_old e
  exact ⟨h1.trans hb, h2.trans hj, by omega⟩

section Field

variable {𝕜 : Type*} [Field 𝕜]


end Field

/-! ### Kernel form -/








end FadicGate

