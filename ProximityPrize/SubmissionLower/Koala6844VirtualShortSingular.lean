import ProximityPrize.SubmissionLower.Koala6844VirtualShortResultant


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open RCN081 RCN156 RCN234 RCN313 RCN137 RCN267
open scoped Classical Matrix BigOperators

noncomputable section

set_option maxHeartbeats 2000000

variable {K : Type} [Field K]

theorem slope_degree_le_weight (F : MvPolynomial (Fin 4) K) (w : Fin 4 → ℕ) (hw : w 2 = 1) :
    F.degreeOf 2 ≤ wt w F := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree w hd
  rw [weight_fin4,hw,mul_one] at h
  exact (show d 2 ≤ d 0*w 0+d 1*w 1+d 2+d 3*w 3 by omega).trans h

def singularMiddle (r y : ℕ) : ℕ := 184*y + (828-184)*r
def singularTotal (r t : ℕ) : ℕ := 184*t + (43753-184)*r
def singularPrice (r y t : ℕ) : ℕ := singularTotal r t + 2130706433 * singularMiddle r y

private theorem pad_cut (r s y u : ℕ) (hs : s ≤ 184) (hy : r ≤ y) (hu : 184 ≤ u) :
    s*y+r*u-r*s ≤ 184*y+(u-184)*r := by
  have first : s*y+r*u-r*s = s*(y-r)+r*u := by
    rw [Nat.mul_comm r s, Nat.add_comm (s*y), Nat.add_sub_assoc (Nat.mul_le_mul_left s hy),
      ← Nat.mul_sub_left_distrib, Nat.add_comm]
  have final : 184*(y-r)+r*u = 184*y+(u-184)*r := by
    have decomposeY : 184*(y-r)+184*r = 184*y := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hy]
    have decomposeU : r*u = 184*r + (u-184)*r := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hu, Nat.mul_comm]
    rw [decomposeU, ← Nat.add_assoc, decomposeY]
  rw [first, ← final]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) _

theorem singular_germ_cut [CharP K 2130706433] (F : MvPolynomial (Fin 4) K)
    (hF : Irreducible F) (hr : 0 < F.degreeOf 2) (hrCap : F.degreeOf 2 ≤ 185)
    (hy : wt residualYSWeights F ≤ 829) (ht : wt residualTotalWeights F ≤ 43754) :
    ∃ J : MvPolynomial (Fin 3) K, J ≠ 0 ∧
      J.degreeOf 1 ≤ singularMiddle (F.degreeOf 2) (wt residualYSWeights F) ∧
      J.weightedTotalDegree ![0,1,1] ≤ singularTotal (F.degreeOf 2) (wt residualTotalWeights F) ∧
      ∀ (P : Polynomial K) (g : K), RCN319.specialization K P g F = 0 →
        RCN319.specialization K P g (MvPolynomial.pderiv 2 F) = 0 →
        MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,P,Polynomial.C g] J = 0 := by
  let G := MvPolynomial.pderiv 2 F
  have hGne : G ≠ 0 := by
    intro hz
    exact (Nat.ne_of_gt hr) ((pderiv_zero_iff_degree_zero_below_char 2 F 2130706433 (by omega)).mp hz)
  have hGr : G.degreeOf 2 ≤ F.degreeOf 2 - 1 := pderiv_same_degree_bound 2 F _ le_rfl
  have hproper : ¬ F ∣ G := by
    intro hd
    have h := coordinate_degree_le_of_dvd 2 F G hd hGne
    omega
  have hGy : wt residualYSWeights G ≤ 828 := wt_pderiv_le residualYSWeights F 2 829 hy
  have hGt : wt residualTotalWeights G ≤ 43753 := wt_pderiv_le residualTotalWeights F 2 43754 ht
  obtain ⟨J, hJ, hJy, hJt, hvanish⟩ :=
    exists_weighted_R_resultant F G hF hr hproper _ 828 _ 43753 le_rfl hGy le_rfl hGt
  have hsy : F.degreeOf 2 ≤ wt residualYSWeights F := slope_degree_le_weight F _ rfl
  have hst : F.degreeOf 2 ≤ wt residualTotalWeights F := slope_degree_le_weight F _ rfl
  exact ⟨J,hJ,hJy.trans (pad_cut _ _ _ _ (by omega) hsy (by decide)),
    hJt.trans (pad_cut _ _ _ _ (by omega) hst (by decide)),hvanish⟩

theorem slope_weight_eq_degree (F : MvPolynomial (Fin 4) K) :
    wt residualSWeights F = F.degreeOf 2 := by
  simp [wt, MvPolynomial.weightedTotalDegree, MvPolynomial.degreeOf_eq_sup,
    weight_fin4, residualSWeights]

theorem card_biUnion_le_short_singular (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    {Seed : Type} [DecidableEq Seed]
    (factors : Finset (MvPolynomial (Fin 4) K))
    (points : MvPolynomial (Fin 4) K → Finset Seed)
    (hproduct : (∏ F ∈ factors, F) ∣ H)
    (hr : wt residualSWeights H ≤ 185) (hy : wt residualYSWeights H ≤ 829)
    (ht : wt residualTotalWeights H ≤ 43754)
    (hcount : ∀ F ∈ factors, (points F).card ≤
      singularPrice (F.degreeOf 2) (wt residualYSWeights F) (wt residualTotalWeights F)) :
    (factors.biUnion points).card ≤ singularPrice 185 829 43754 := by
  have sy := (RCN293.sum_weighted_degrees_le_of_prod_dvd
    residualYSWeights factors id H hH hproduct).trans hy
  have st := (RCN293.sum_weighted_degrees_le_of_prod_dvd
    residualTotalWeights factors id H hH hproduct).trans ht
  have sr := (RCN293.sum_weighted_degrees_le_of_prod_dvd
    residualSWeights factors id H hH hproduct).trans hr
  simp only [id_eq] at sy st sr
  change (∑ F ∈ factors, wt residualSWeights F) ≤ 185 at sr
  simp only [slope_weight_eq_degree] at sr
  calc
    _ ≤ ∑ F ∈ factors, (points F).card := Finset.card_biUnion_le
    _ ≤ ∑ F ∈ factors,
        singularPrice (F.degreeOf 2) (wt residualYSWeights F) (wt residualTotalWeights F) :=
      Finset.sum_le_sum hcount
    _ ≤ _ := by
      simp only [singularPrice,singularMiddle,singularTotal,Finset.sum_add_distrib,← Finset.mul_sum]
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ st) (Nat.mul_le_mul_left _ sr))
        (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ sy) (Nat.mul_le_mul_left _ sr)))

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
