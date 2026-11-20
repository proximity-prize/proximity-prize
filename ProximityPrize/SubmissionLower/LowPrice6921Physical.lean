import ProximityPrize.SubmissionLower.LowPrice6921Incidence
import ProximityPrize.SubmissionLower.LowPrice6921Geometry
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace LowPrice6921

noncomputable section

open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators

private theorem le_ceil {n d count : ℕ} (hd : 0 < d) (h : count*d ≤ n) :
    count ≤ ceilDiv n d := by
  unfold ceilDiv
  exact (Nat.le_div_iff_mul_le hd).mpr (by omega)

private theorem price_formula (x : Shape) (l : ℕ) :
    physicalPrice x l =
      ceilDiv (ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 +
        ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594) l +
      2 * (133671 * x.b * cutterBox.b) +
      ceilDiv (81879 * auxCurves32 x + 2*46594 * auxPoints32 x) (32*46594) := by
  simp only [physicalPrice, auxCurves32, auxPoints32, membershipDegree, Nat.mul_assoc]

theorem physical_count_from_sections (w : I → K) {Γ s} (hm : LowFat6921.Messages w Γ s)
    (f Q : Row 4) (l : ℕ) (hl : 0 < l) (A C D F : Pieces Γ) (AB CB : Finset K)
    (hA : A.curves s)
    (haCover : ∀ γ ∈ Γ, ¬ HighMark f Q l (extend (s γ)) → γ ∈ A.union ∪ AB)
    (haCurves : 32 * A.total ≤ auxCurves32 (shape f))
    (haPoints : 32 * (AB.card + A.n) ≤ 2 * auxPoints32 (shape f))
    (hC : C.curves s) (hcPos : ∀ i, 0 < C.degree i)
    (hcCover : ∀ γ ∈ Γ, MixedMark f Q l (extend (s γ)) → γ ∈ C.union ∪ CB)
    (hcBudget : 32 * l * (2 * C.total + CB.card) ≤ surfaceNumerator32 (shape f).chamber cutterBox)
    (hD : D.curves s) (hF : F.surfaces s) (hdPos : ∀ i, 0 < D.degree i)
    (hfPos : ∀ i, 0 < F.degree i)
    (hdCover : ∀ γ ∈ Γ, ContinuedMark f Q l (extend (s γ)) → γ ∈ D.union ∪ F.union)
    (hdBudget : l * D.total ≤ membershipDegree (shape f))
    (hfBudget : 2 * F.total ≤ 133671 * (shape f).b * cutterBox.b) :
    Γ.card ≤ physicalPrice (shape f) l := by
  classical
  let aux := A.union.card + AB.card
  let mixed := C.union.card + CB.card
  have cover : Γ ⊆ (A.union ∪ AB) ∪ (C.union ∪ CB) ∪ D.union ∪ F.union := by
    intro γ hγ
    by_cases hh : HighMark f Q l (extend (s γ))
    · have hdeg : (extend (s γ)).natDegree ≤ 133671 := by
        simpa only [Polynomial.natDegree_map] using hm.old_degree γ hγ
      rcases highMark_cases hdeg hh with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (hcCover γ hγ h)))
      · rcases Finset.mem_union.mp (hdCover γ hγ h) with hd | hf
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hd)
        · exact Finset.mem_union_right _ hf
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (haCover γ hγ hh)))
  have card : Γ.card ≤ aux + mixed + D.union.card + F.union.card := by
    refine (Finset.card_le_card cover).trans ?_
    calc
      _ ≤ (((A.union ∪ AB) ∪ (C.union ∪ CB)) ∪ D.union).card + F.union.card :=
        Finset.card_union_le _ _
      _ ≤ ((A.union ∪ AB) ∪ (C.union ∪ CB)).card + D.union.card + F.union.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (A.union ∪ AB).card + (C.union ∪ CB).card + D.union.card + F.union.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ ≤ _ := by
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)) _) _
  let x := shape f
  have aux_bound : aux ≤
      ceilDiv (81879 * auxCurves32 x + 2*46594 * auxPoints32 x) (32*46594) := by
    apply le_ceil (by decide)
    have hA' := piece_curve_capacity A hm hA
    change 32 * A.total ≤ auxCurves32 x at haCurves
    change 32 * (AB.card + A.n) ≤ 2 * auxPoints32 x at haPoints
    dsimp only [aux]
    omega
  have mixed_bound : l * mixed ≤ ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 := by
    apply le_ceil (by decide)
    have hC' := Nat.add_le_add_right (piece_curve_capacity_integral C hm hC hcPos) CB.card
    have h := (Nat.mul_le_mul_left (32*l) hC').trans hcBudget
    simpa only [mixed, x, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have curve_bound : l * D.union.card ≤
      ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594 := by
    apply le_ceil (by decide)
    have hD' := Nat.mul_le_mul_left l (piece_curve_capacity_integral D hm hD hdPos)
    change l * D.total ≤ membershipDegree x at hdBudget
    have hD'' : l * D.union.card ≤ 2 * membershipDegree x := by
      rw [Nat.mul_left_comm] at hD'
      omega
    omega
  have main_bound : mixed + D.union.card ≤
      ceilDiv (ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 +
        ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594) l := by
    apply le_ceil hl
    rw [Nat.add_mul, Nat.mul_comm mixed l, Nat.mul_comm D.union.card l]
    exact Nat.add_le_add mixed_bound curve_bound
  have surface_bound : F.union.card ≤ 2*(133671*x.b*cutterBox.b) := by
    have hF' := piece_surface_capacity F hm hF hfPos
    change 2 * F.total ≤ 133671*x.b*cutterBox.b at hfBudget
    omega
  rw [price_formula]
  change Γ.card ≤
    ceilDiv (ceilDiv (surfaceNumerator32 x.chamber cutterBox) 32 +
      ceilDiv ((81879 + 2*46594) * membershipDegree x) 46594) l +
    2*(133671*x.b*cutterBox.b) +
    ceilDiv (81879 * auxCurves32 x + 2*46594 * auxPoints32 x) (32*46594)
  omega

theorem physical_count (w : I → K) {Γ s} (hm : LowFat6921.Messages w Γ s)
    (f : Row 4) (hf : SmallFactor f) (hOn : ∀ γ ∈ Γ, OnFactor f (extend (s γ)))
    (l : ℕ) (hl : 0 < l) (hCut : ProperCut f Γ s l) :
    Γ.card ≤ physicalPrice (shape f) l := by
  classical
  have h1 := Geometry.K1_13_6_1
  have h2 := Geometry.K1_13_6_2
  have h3 := Geometry.K1_13_6_3
  obtain ⟨Q, hproper, hbox, hweight, horder⟩ := hCut
  have input : CutInput Γ s f Q l := ⟨hm.distinct, hm.old_degree, hf, hOn, hl,
    hproper, hbox, hweight, horder⟩
  obtain ⟨A, AB, hA, haCover, haCurves, haPoints⟩ := h1 Γ s f Q l input
  obtain ⟨C, CB, hC, hcPos, hcCover, hcBudget⟩ := h2 Γ s f Q l input
  obtain ⟨D, F, hD, hF, hdPos, hfPos, hdCover, hdBudget, hfBudget⟩ := h3 Γ s f Q l input
  exact physical_count_from_sections w hm f Q l hl A C D F AB CB hA haCover haCurves haPoints
    hC hcPos hcCover hcBudget hD hF hdPos hfPos hdCover hdBudget hfBudget

end
end LowPrice6921
