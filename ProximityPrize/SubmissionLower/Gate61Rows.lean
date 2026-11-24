import ProximityPrize.SubmissionLower.R6960Low6960VariableSelect
import ProximityPrize.SubmissionLower.Gate61Tilted
import ProximityPrize.SubmissionLower.Gate61Shape
import ProximityPrize.SubmissionLower.Gate61CertCF
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew

-- merged module Gate61Flat
section Merged_Gate61Flat

set_option autoImplicit false
set_option Elab.async false

namespace Gate61Flat

open Low6960SharedRational (toGeometric FractionJet)
open K1_13_6 (GenericField GeoField GeoJets)
open K1_13_5_4_4 (regular_cut_of_flat_map)
open K1_13_6_2_4_4 (relPrime_of_regular)

theorem pair_regular_fraction {F G : FractionJet} (hrel : IsRelPrime F G) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {F}) G) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (hrel.dvd_of_dvd_mul_left hx))

theorem isRelPrime_toGeometric {G₁ G₂ : FractionJet} (h₁ : G₁ ≠ 0)
    (hrel : IsRelPrime G₁ G₂) : IsRelPrime (toGeometric G₁) (toGeometric G₂) := by
  have hreg := pair_regular_fraction hrel
  have hf : IsSMulRegular (FractionJet) G₁ := by
    intro x y hxy
    exact mul_left_cancel₀ h₁ hxy
  have hflat : (algebraMap GenericField GeoField).Flat := by
    letI : Algebra GenericField GeoField := (algebraMap GenericField GeoField).toAlgebra
    have h : Module.Flat GenericField GeoField := inferInstance
    exact h
  have h2 := regular_cut_of_flat_map (algebraMap GenericField GeoField) hflat hf hreg
  have hne : toGeometric G₁ ≠ 0 := by
    intro h
    apply h₁
    exact MvPolynomial.map_injective _ (algebraMap GenericField GeoField).injective
      (h.trans (map_zero _).symm)
  exact relPrime_of_regular hne h2

end Gate61Flat

end Merged_Gate61Flat

-- merged module Gate61Clear
section Merged_Gate61Clear

set_option autoImplicit false
set_option Elab.async false

namespace Gate61Clear

open Low6960SharedRational (FractionJet toGeometric toFraction clear_denominators fraction_geometric)
open K1_13 (Row shape Geom)
open scoped Polynomial
open K1_13_6 (GeoJets GeoField toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6960SharedPrice (coord)
open Low6960SharedChooseCut (weight_coord)

theorem clear_row (A0 : FractionJet) :
    ∃ A0' : Row 4, A0'.support = A0.support ∧ ∃ u : GeoField, u ≠ 0 ∧
      toGeneric A0' = MvPolynomial.C u * toGeometric A0 := by
  obtain ⟨d, Q, hd, hS, hQ⟩ := clear_denominators A0
  have hinj : Function.Injective
      ((algebraMap K1_13_6.GenericField GeoField).comp (algebraMap (Polynomial Geom) K1_13_6.GenericField)) :=
    (algebraMap K1_13_6.GenericField GeoField).injective.comp
      (IsFractionRing.injective (Polynomial Geom) K1_13_6.GenericField)
  refine ⟨Q, hS, (algebraMap K1_13_6.GenericField GeoField) (algebraMap (Polynomial Geom) K1_13_6.GenericField d),
    ?_, ?_⟩
  · intro h
    apply hd
    apply hinj
    simpa using h
  · rw [← fraction_geometric, hQ, map_mul]
    simp [toGeometric]

theorem coord_eq_shp (A0' : Row 4) (A0 : FractionJet) (h : A0'.support = A0.support) (i : Fin 3) :
    coord (shape A0') i = Gate61Shape.shp i A0 := by
  rw [weight_coord]
  unfold Gate61Shape.shp MvPolynomial.weightedTotalDegree
  rw [h]
  fin_cases i <;> rfl

theorem vanishesTo_C_mul (P : Ideal GeoJets) [P.IsPrime] {u : GeoField} (hu : u ≠ 0) {B0 : GeoJets} {n : ℕ} :
    VanishesTo P (MvPolynomial.C u * B0) n ↔ VanishesTo P B0 n := by
  constructor
  · intro h
    have hu' : MvPolynomial.C u⁻¹ * (MvPolynomial.C u * B0) = B0 := by
      rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hu, MvPolynomial.C_1, one_mul]
    rw [← hu']
    unfold VanishesTo at *
    change algebraMap GeoJets (Localization.AtPrime P) _ ∈ _ at h ⊢
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ h
  · intro h
    unfold VanishesTo at *
    change algebraMap GeoJets (Localization.AtPrime P) _ ∈ _ at h ⊢
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ h

theorem isRelPrime_C_mul_right {u : GeoField} (hu : u ≠ 0) {A0 B0 : GeoJets} (h : IsRelPrime A0 B0) :
    IsRelPrime A0 (MvPolynomial.C u * B0) := by
  intro d hd1 hd2
  have hc : IsUnit (MvPolynomial.C u : GeoJets) := (Ne.isUnit hu).map MvPolynomial.C
  exact h hd1 ((hc.dvd_mul_left).mp hd2)

theorem isRelPrime_C_mul_left {u : GeoField} (hu : u ≠ 0) {A0 B0 : GeoJets} (h : IsRelPrime A0 B0) :
    IsRelPrime (MvPolynomial.C u * A0) B0 := by
  intro d hd1 hd2
  have hc : IsUnit (MvPolynomial.C u : GeoJets) := (Ne.isUnit hu).map MvPolynomial.C
  exact h ((hc.dvd_mul_left).mp hd1) hd2

end Gate61Clear

end Merged_Gate61Clear

-- merged module Gate61Rows
section Merged_Gate61Rows

set_option autoImplicit false
set_option Elab.async false

namespace Gate61Rows

open Low6960SharedRational (FractionJet toGeometric toFraction fraction_geometric)
open K1_13 (Row shape Geom)
open K1_13_6 (GeoJets GeoField GenericField toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6960SharedPrice (coord)
open scoped Polynomial

theorem shp_pow {F : Type*} [Field F] {p : MvPolynomial (Fin 4) F} (hp : p ≠ 0) (a : ℕ) (i : Fin 3) :
    Gate61Shape.shp i (p ^ a) = a * Gate61Shape.shp i p := by
  induction a with
  | zero =>
    simp [Gate61Shape.shp, MvPolynomial.weightedTotalDegree]
  | succ a ih =>
    rw [pow_succ, Gate61Shape.shp_mul (pow_ne_zero _ hp) hp, ih]; ring

theorem support_toFraction (f : Row 4) : (toFraction f).support = f.support :=
  MvPolynomial.support_map_of_injective f (IsFractionRing.injective (Polynomial Geom) GenericField)

theorem shp_toFraction (f : Row 4) (i : Fin 3) :
    Gate61Shape.shp i (toFraction f) = coord (shape f) i :=
  (Gate61Clear.coord_eq_shp f (toFraction f) (support_toFraction f).symm i).symm

theorem toFraction_ne_zero {f : Row 4} (hf : f ≠ 0) : toFraction f ≠ 0 := by
  intro h
  apply hf
  exact MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial Geom) GenericField)
    (h.trans (map_zero _).symm)

theorem toFraction_not_unit {f : Row 4} (hdeg : 0 < f.totalDegree) : ¬ IsUnit (toFraction f) := by
  rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
  have : (toFraction f).totalDegree = f.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [support_toFraction]
  omega

theorem isRelPrime_scaled {a b : FractionJet} (ha : a ≠ 0) (hrel : IsRelPrime a b) {a' b' : Row 4} {ua ub : GeoField}
    (hua : ua ≠ 0) (hub : ub ≠ 0) (ha' : toGeneric a' = MvPolynomial.C ua * toGeometric a)
    (hb' : toGeneric b' = MvPolynomial.C ub * toGeometric b) :
    IsRelPrime (toGeneric a') (toGeneric b') := by
  have h := Gate61Flat.isRelPrime_toGeometric ha hrel
  rw [ha', hb']
  exact Gate61Clear.isRelPrime_C_mul_left hua (Gate61Clear.isRelPrime_C_mul_right hub h)

theorem clear_frac (X0 : FractionJet) :
    ∃ X' : Row 4, X'.support = X0.support ∧ ∃ c : GenericField, c ≠ 0 ∧
      toFraction X' = MvPolynomial.C c * X0 := by
  obtain ⟨d, Q, hd, hS, hQ⟩ := Low6960SharedRational.clear_denominators X0
  refine ⟨Q, hS, algebraMap (Polynomial Geom) GenericField d, ?_, hQ⟩
  intro h
  exact hd ((IsFractionRing.injective (Polynomial Geom) GenericField) (h.trans (map_zero _).symm))

theorem toGeneric_clear {X' : Row 4} {X0 : FractionJet} {c : GenericField}
    (h : toFraction X' = MvPolynomial.C c * X0) :
    toGeneric X' = MvPolynomial.C (algebraMap GenericField GeoField c) * toGeometric X0 := by
  rw [← fraction_geometric, h, map_mul]
  simp [toGeometric]

theorem algebraMap_ne_zero {c : GenericField} (hc : c ≠ 0) : algebraMap GenericField GeoField c ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap GenericField GeoField).injective).mpr hc

set_option maxHeartbeats 1600000 in
theorem rows_from_subspace [Infinite GenericField] (f : Row 4) (hfirr : Irreducible f)
    (hdeg : 0 < f.totalDegree) (U : Submodule GenericField FractionJet) (hU : U ≠ ⊥) (r : ℕ)
    (S : Finset (Ideal GeoJets)) (hS : ∀ P ∈ S, P.IsPrime)
    (hcontact : ∀ Q ∈ U, ∀ (P : Ideal GeoJets) (hP : P ∈ S),
      @VanishesTo _ _ P (hS P hP) (toGeometric Q) r)
    (B : Fin 3 → ℕ) (hB : ∀ Q ∈ U, ∀ i, Gate61Shape.shp i Q ≤ B i) :
    ∃ (a : ℕ) (H G₁ G₂ : Row 4), H ≠ 0 ∧ G₁ ≠ 0 ∧
      IsRelPrime (toGeneric f) (toGeneric H) ∧ IsRelPrime (toGeneric f) (toGeneric G₁) ∧
      IsRelPrime (toGeneric H) (toGeneric G₁) ∧ IsRelPrime (toGeneric G₁) (toGeneric G₂) ∧
      (∀ (P : Ideal GeoJets) (hP : P ∈ S), @VanishesTo _ _ P (hS P hP)
        ((toGeneric f) ^ a * (toGeneric H * toGeneric G₁)) r) ∧
      (∀ (P : Ideal GeoJets) (hP : P ∈ S), @VanishesTo _ _ P (hS P hP)
        ((toGeneric f) ^ a * (toGeneric H * toGeneric G₂)) r) ∧
      (∀ i, coord (shape G₁) i ≤ B i - (a * coord (shape f) i + coord (shape H) i)) ∧
      (∀ i, coord (shape G₂) i ≤ B i - (a * coord (shape f) i + coord (shape H) i)) ∧
      Module.finrank GenericField U ≤
        Gate61Shape.free (fun i => B i - (a * coord (shape f) i + coord (shape H) i)) ∧
      (∀ i, a * coord (shape f) i + coord (shape H) i ≤ B i) ∧
      (coord (shape H) 2 ≤ coord (shape H) 0 ∧ 3 * coord (shape H) 2 ≤ coord (shape H) 1 ∧
        coord (shape H) 1 ≤ 2 * coord (shape H) 0 + coord (shape H) 2) := by
  classical
  have hf0 : f ≠ 0 := hfirr.ne_zero
  have hfF0 := toFraction_ne_zero hf0
  have hfFn := toFraction_not_unit hdeg
  obtain ⟨g0, hg0, V', hV', hdiv, hno⟩ := Gate61Gcd.gcd_split U hU
  obtain ⟨a, h', hgh, hnd⟩ := Gate61Gcd.split_power_nonunit (toFraction f) g0 hfFn hg0
  have hh0 : h' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgh
    exact hg0 hgh
  have hT0 : toFraction f * h' ≠ 0 := mul_ne_zero hfF0 hh0
  have hTn : ¬ IsUnit (toFraction f * h') := fun h => hfFn (isUnit_of_mul_isUnit_left h)
  obtain ⟨G1, hG1, G2, hG2, hG10, hrelT1, hrel12⟩ := Gate61Gcd.two_general V' hno hT0 hTn
  have hmem : ∀ G, G ∈ V' → g0 * G ∈ U := fun G hG => by rw [hV'] at hG; exact hG
  obtain ⟨H, hHs, cH, hcH, hHf⟩ := clear_frac h'
  obtain ⟨K1, hK1s, c1, hc1, hK1f⟩ := clear_frac G1
  obtain ⟨K2, hK2s, c2, hc2, hK2f⟩ := clear_frac G2
  have hH0 : H ≠ 0 := by
    intro h; apply hh0
    have := congrArg MvPolynomial.support h
    rw [hHs, MvPolynomial.support_zero] at this
    exact MvPolynomial.support_eq_empty.mp this
  have hK10 : K1 ≠ 0 := by
    intro h; apply hG10
    have := congrArg MvPolynomial.support h
    rw [hK1s, MvPolynomial.support_zero] at this
    exact MvPolynomial.support_eq_empty.mp this
  have eH := toGeneric_clear hHf
  have e1 := toGeneric_clear hK1f
  have e2 := toGeneric_clear hK2f
  have ef : toGeneric f = MvPolynomial.C (1 : GeoField) * toGeometric (toFraction f) := by
    rw [fraction_geometric]; simp
  have hfG1 : IsRelPrime (toFraction f) G1 := hrelT1.of_mul_left_left
  have hhG1 : IsRelPrime h' G1 := hrelT1.of_mul_left_right
  have hnotdvd : ¬ f ∣ H := by
    intro ⟨w, hw⟩
    apply hnd
    have h1 : toFraction f ∣ MvPolynomial.C cH * h' := by
      rw [← hHf]
      exact ⟨toFraction w, by rw [hw]; simp [toFraction, map_mul]⟩
    have hu : IsUnit (MvPolynomial.C cH : FractionJet) := (Ne.isUnit hcH).map MvPolynomial.C
    exact (hu.dvd_mul_left).mp h1
  have hgfrac : toGeometric g0 = (toGeneric f) ^ a * toGeometric h' := by
    rw [hgh, map_mul, map_pow, fraction_geometric]
  have shp_g0 : ∀ i, Gate61Shape.shp i g0 = a * coord (shape f) i + coord (shape H) i := by
    intro i
    rw [hgh, Gate61Shape.shp_mul (pow_ne_zero a hfF0) hh0, shp_pow hfF0, shp_toFraction,
      ← Gate61Clear.coord_eq_shp H h' hHs i]
  have contact_of : ∀ (G : FractionJet) (K : Row 4) (c : GenericField), G ∈ V' →
      toFraction K = MvPolynomial.C c * G → c ≠ 0 →
      ∀ (P : Ideal GeoJets) (hP : P ∈ S), @VanishesTo _ _ P (hS P hP)
        ((toGeneric f) ^ a * (toGeneric H * toGeneric K)) r := by
    intro G K c hG hKf hc P hP
    haveI := hS P hP
    have hq := hcontact (g0 * G) (hmem G hG) P hP
    have eK := toGeneric_clear hKf
    have hrew : (toGeneric f) ^ a * (toGeneric H * toGeneric K) =
        MvPolynomial.C (algebraMap GenericField GeoField cH * algebraMap GenericField GeoField c) *
          toGeometric (g0 * G) := by
      rw [eH, eK, show toGeometric (g0 * G) = toGeometric g0 * toGeometric G from map_mul _ _ _, hgfrac,
        MvPolynomial.C_mul]; ring
    rw [hrew]
    exact (Gate61Clear.vanishesTo_C_mul P
      (mul_ne_zero (algebraMap_ne_zero hcH) (algebraMap_ne_zero hc))).mpr hq
  have shape_of : ∀ (G : FractionJet) (K : Row 4), G ∈ V' → K.support = G.support → ∀ i,
      coord (shape K) i ≤ B i - (a * coord (shape f) i + coord (shape H) i) := by
    intro G K hG hKs i
    rw [Gate61Clear.coord_eq_shp K G hKs i]
    by_cases hG0 : G = 0
    · subst hG0; simp [Gate61Shape.shp, MvPolynomial.weightedTotalDegree]
    · have h1 := hB (g0 * G) (hmem G hG) i
      rw [Gate61Shape.shp_mul hg0 hG0, shp_g0] at h1
      omega
  have fitsx : ∀ i, a * coord (shape f) i + coord (shape H) i ≤ B i := by
    intro i
    have h1 := hB (g0 * G1) (hmem G1 hG1) i
    rw [Gate61Shape.shp_mul hg0 hG10, shp_g0] at h1
    omega
  have validH : coord (shape H) 2 ≤ coord (shape H) 0 ∧ 3 * coord (shape H) 2 ≤ coord (shape H) 1 ∧
      coord (shape H) 1 ≤ 2 * coord (shape H) 0 + coord (shape H) 2 := by
    have := Gate61Shape.shp_valid hh0
    rw [Gate61Clear.coord_eq_shp H h' hHs 0, Gate61Clear.coord_eq_shp H h' hHs 1,
      Gate61Clear.coord_eq_shp H h' hHs 2]
    exact this
  refine ⟨a, H, K1, K2, hH0, hK10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fitsx, validH⟩
  · exact K1_13_7_1.proper_generic f H hfirr hnotdvd
  · exact isRelPrime_scaled hfF0 hfG1 one_ne_zero (algebraMap_ne_zero hc1) ef e1
  · exact isRelPrime_scaled hh0 hhG1 (algebraMap_ne_zero hcH) (algebraMap_ne_zero hc1) eH e1
  · exact isRelPrime_scaled hG10 hrel12 (algebraMap_ne_zero hc1) (algebraMap_ne_zero hc2) e1 e2
  · exact contact_of G1 K1 c1 hG1 hK1f hc1
  · exact contact_of G2 K2 c2 hG2 hK2f hc2
  · exact shape_of G1 K1 hG1 hK1s
  · exact shape_of G2 K2 hG2 hK2s
  · have := Gate61Shape.dim_le_free U g0 hg0 hdiv B hB
    simpa only [shp_g0] using this

end Gate61Rows

end Merged_Gate61Rows
