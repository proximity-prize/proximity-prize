import ProximityPrize.SubmissionBinaryLower.P64C6Counts

/-!
# Constructing a flat auxiliary with the required degree caps

The exact coefficient boxes instantiate the kernel. The returned cofactors
are in the original coordinates, using the kernel's additive convention.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Auxiliary

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Boxes P64C6Weights
  P64C6Flat P64C6Counts

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

theorem exists_auxiliary (R : Tri) (hR : R ≠ 0) (D W q e h d : ℕ)
    (hRw : WtLE 0 q 1 d R) (hde : d ≤ e)
    (x : ι → F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q) (s : ι → ℕ)
    (hdim : (∑ i, (conditions (s i) q e).card) < (auxiliary D W q e h).card +
      ∑ i, (conditions (s i - lineOrd R (x i) (y i)) q (e - d)).card) :
    ∃ (H : Tri) (G : ι → Tri), H ≠ 0 ∧
      P64Caps.Weighted.weightedSupportDegree H D ≤ W ∧ H.natDegree < h ∧
      WtLE 0 q 1 e H ∧ ∀ i, OrdGE (H + R * G i) (x i) (y i) (s i) := by
  classical
  let C : ι → Finset (ℕ × ℕ × ℕ) := fun i =>
    conditions (s i - lineOrd R (x i) (y i)) q (e - d)
  let T : ι → Finset (ℕ × ℕ × ℕ) := fun i => conditions (s i) q e
  have hshift : ∀ i, WtLE 0 q 1 d (lineShift R (x i) (y i)) :=
    fun i => lineShift_weight R (x i) (y i) q d hRw (hy i)
  have huniq : ∀ i (c : C i → F),
      extr3 (T i) (lineShift R (x i) (y i) * comb3 (C i) c) = 0 → c = 0 := by
    intro i c hc
    apply cofactor_unique (lineShift R (x i) (y i))
      ((lineShift_eq_zero_iff R (x i) (y i)).not.mpr hR) (s i) q d (e - d)
      (hshift i) (C i) (T i) ?_ ?_ ?_ c hc
    · rintro ⟨a, b, l⟩ hp
      exact ((mem_conditions _ q (e - d) a b l).mp hp).1
    · rintro ⟨a, b, l⟩ hp
      exact ((mem_conditions _ q (e - d) a b l).mp hp).2
    · intro a b l hab hbl
      apply (mem_conditions (s i) q e a b l).mpr
      exact ⟨hab, by simpa [Nat.add_sub_of_le hde] using hbl⟩
  obtain ⟨c, g, hc, hg⟩ := exists_flat_coefficients R (auxiliary D W q e h) C T x y hdim huniq
  let H := comb3 (auxiliary D W q e h) c
  let G₀ : ι → Tri := fun i => comb3 (C i) (g i)
  let G : ι → Tri := fun i => shiftHom (-(Polynomial.C (x i))) (-(y i)) (G₀ i)
  have hH : H ≠ 0 := by
    intro hz
    apply hc
    apply comb3_injective (auxiliary D W q e h)
    simpa [H] using hz
  have hcaps := auxiliary_caps D W q e h hH (comb3_mem_supp (auxiliary D W q e h) c)
  refine ⟨H, G, hH, hcaps.1, hcaps.2.1, hcaps.2.2, ?_⟩
  intro i
  have hG₀w : WtLE 0 q 1 (e - d) (G₀ i) := by
    apply weight_of_supp (comb3_mem_supp (C i) (g i))
    rintro ⟨a, b, l⟩ hp
    simpa using ((mem_conditions _ q (e - d) a b l).mp hp).2
  have hpw : WtLE 0 q 1 e (lineShift R (x i) (y i) * G₀ i) := by
    simpa [Nat.add_sub_of_le hde] using (hshift i).mul hG₀w
  have hh := order_of_constraints (lineShift H (x i) (y i) + lineShift R (x i) (y i) * G₀ i)
    (s i) q e (weight_add (lineShift_weight H (x i) (y i) q e hcaps.2.2 (hy i)) hpw) (hg i)
  have hGshift : lineShift (G i) (x i) (y i) = G₀ i :=
    shiftHom_inverse (Polynomial.C (x i)) (y i) (G₀ i)
  have heq : lineShift (H + R * G i) (x i) (y i) =
      lineShift H (x i) (y i) + lineShift R (x i) (y i) * G₀ i := by
    rw [show lineShift (H + R * G i) (x i) (y i) =
      lineShift H (x i) (y i) + lineShift (R * G i) (x i) (y i) from
      (shiftHom (Polynomial.C (x i)) (y i)).map_add H (R * G i)]
    rw [lineShift_mul, hGshift]
  intro a b hab
  rw [heq]
  exact hh a b hab

/-- A symbolic upper bound on the net conditions suffices for the strict dimension inequality. -/
theorem dimension_of_net_bound (D W q e h d : ℕ) (s μ : ι → ℕ)
    (hμ : ∀ i, μ i ≤ s i) (he : ∀ i, q * s i + d ≤ e)
    (hnum : (∑ i, netUpper6 (s i) q d (μ i) e) <
      6 * (h : ℤ) * (W - h * D : ℕ) * (e - q * h : ℕ)) :
    (∑ i, (conditions (s i) q e).card) < (auxiliary D W q e h).card +
      ∑ i, (conditions (s i - μ i) q (e - d)).card := by
  have hn := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    net_count_le (s i) q d (μ i) e (hμ i) (he i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hn
  have hl := auxiliary_lower D W q e h
  have hl' : (h : ℤ) * (W - h * D : ℕ) * (e - q * h : ℕ) ≤
      (auxiliary D W q e h).card := by exact_mod_cast hl
  have hx : (∑ i, ((conditions (s i) q e).card : ℤ)) <
      (auxiliary D W q e h).card + ∑ i, ((conditions (s i - μ i) q (e - d)).card : ℤ) := by
    linarith
  exact_mod_cast hx

end P64C6Auxiliary
end ProximityPrize.SubmissionBinaryLower
