import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 8000

namespace CurveListRectangularRoots
open CJ0 CJ0_3 PolynomialDifferential Finset
open scoped Polynomial BigOperators

def curveFactor (A : ℕ) : ℚ := (errors A : ℚ) / gap A

theorem first_order_price {A w s Q₁} (hA : AgreementOK A) (hs : ShapeOK s) (hQ₁ : OrderOne s Q₁)
    (T : Finset K[X]) (hT : (T : Set K[X]) ⊆ close A w)
    (hroot : ∀ f ∈ T, differentialSpecialization Q₁ f = 0) :
    (T.card : ℚ) ≤ curveFactor A * R₁ s + (H s : ℚ)^2 := by
  classical
  obtain ⟨F₁,hF₁,hcover₁⟩ := CJ0_6.proof s hs Q₁ hQ₁
  obtain ⟨G,hG,hGdeg,hordinary⟩ := CJ0_8.proof s hs Q₁ hQ₁
  let T₁ := T.filter (RegularRoot Q₁)
  let T₀ := T.filter fun f => ¬ RegularRoot Q₁ f
  have h₁ (f : K[X]) (hf : f ∈ T₁) := hT (mem_filter.mp hf).1
  have p₁' := family_capacity (fun f hf => h₁ f hf) hA (Or.inl rfl) F₁ (CJ0_7.proof s hs F₁ hF₁)
    (fun f hf => hcover₁ f (h₁ f hf).1 (mem_filter.mp hf).2)
  have hd : (0 : ℚ) < gap A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
  have p₁ : (T₁.card : ℚ) ≤ curveFactor A * R₁ s + H s := by
    apply le_of_mul_le_mul_left _ hd
    unfold curveFactor
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
    simp only [one_mul] at p₁'
    have hcount : (F₁.count : ℚ) ≤ H s := by exact_mod_cast hF₁.count
    exact p₁'.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hd.le))
  have p₀ : T₀.card ≤ H s*(H s-1) := by
    refine (Polynomial.card_le_degree_of_subset_roots (p := G) ?_).trans hGdeg
    intro f hf
    obtain ⟨hr',hsing₁⟩ := mem_filter.mp (show f ∈ T₀ from hf)
    exact (Polynomial.mem_roots hG).mpr (hordinary f (hT hr').1 (hroot f hr') hsing₁)
  have hp₀ : (H s : ℚ)+T₀.card ≤ (H s : ℚ)^2 := by
    have he : H s+H s*(H s-1) = H s^2 := by
      generalize H s = z
      cases z with
      | zero => decide
      | succ q => simp only [Nat.succ_sub_one]; ring
    exact_mod_cast (Nat.add_le_add_left p₀ (H s)).trans_eq he
  rw [← show T₁.card + T₀.card = T.card from card_filter_add_card_filter_not .., Nat.cast_add]
  linarith only [p₁,hp₀]

end CurveListRectangularRoots
