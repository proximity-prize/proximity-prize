import ProximityPrize.SubmissionLower.CommonShearFamilyPrototype
import ProximityPrize.SubmissionLower.Y
import ProximityPrize.SubmissionLower.BW

namespace ProximityPrize.SubmissionLower.CommonShearConsumerPrototype

open scoped Classical BigOperators
open RCN001 RCN002 RCN003 RCN005 RCN006 RCN007 RCN022 RCN023 RCN045 RCN051
  RCN067 RCN068 RCN081 RCN093 RCN135 RCN136 RCN137 RCN138 RCN169 RCN170
  RCN172 RCN174 RCN231 RCN238 RCN243 RCN264 RCN319 RCN344 RCN370 RCN372
open CommonShearFamilyPrototype

noncomputable section

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2000000

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)
variable {ι : Type*}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω
local instance : DecidableEq ι := Classical.decEq ι

/-- A proper-cut seed bound obtained from one common shear across all regular
components.  Only the original `Y` and `Z` characteristic gates are needed:
the `R` projection is replaced by the common `R + a Z` coordinate. -/
theorem proper_cut_seed_bound_of_common_global_shear
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedY : coordinateMixedDegree Ω G T 0 < p)
    (hmixedZ : coordinateMixedDegree Ω G T 2 < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
        (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
    (hcapY : 1 ≤ cap 0) (hcapR : 1 ≤ cap 1) :
    Γ.card * (a - w) ≤
      (nodes.card - w) *
        (∑ i, adaptiveShearCap cap i * coordinateMixedDegree Ω G T i) +
      (e + 1) * (a - w) * coordinateMixedDegree Ω G T 2 := by
  classical
  let H := regularitySurface φ F
  let Component := RegularComponent Ω G T H
  have hgeom :=
    regularComponents_finite_and_degree_budget_charfree φ F G T hG hproper
  have hsepY : ∀ C : Component,
      ∀ hY : Transcendental Ω (coordinate Ω C.1 0),
        letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
          rationalBaseAlgebra Ω C.1 0 hY
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) := by
    intro C hY
    exact (finite_separable_at_of_original_coordinate_gate Ω C.1 0 hY p G T
      hG (regularComponent_G_mem Ω G T H C)
      (regularComponent_T_mem Ω G T H C) hproper hGdegree hmixedY).2
  have hsepZ : ∀ C : Component,
      ∀ hZ : Transcendental Ω (coordinate Ω C.1 2),
        letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
          rationalBaseAlgebra Ω C.1 2 hZ
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) := by
    intro C hZ
    exact (finite_separable_at_of_original_coordinate_gate Ω C.1 2 hZ p G T
      hG (regularComponent_G_mem Ω G T H C)
      (regularComponent_T_mem Ω G T H C) hproper hGdegree hmixedZ).2
  obtain ⟨shear, hshear, dS, hSbudget, hfiber⟩ :=
    exists_common_global_shear_family φ
      (Q := fun C : Component => C.1) Subtype.val_injective hgeom.1
      (fun C => regularComponent_ne_point Ω G T H C)
      hsepY hsepZ G T hG
      (regularComponent_G_mem Ω G T H)
      (regularComponent_T_mem Ω G T H) hproper F selected
      (fun C : Component =>
        componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
      p w hchar
      (fun C γ hγ => hdegree γ
        (componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C hγ))
      (fun C γ hγ => hsolution γ
        (componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C hγ))
      (fun C γ hγ => hregular γ
        (componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C hγ))
      (fun C γ hγ => componentSeeds_on_prime Ω G T H Γ
        (selectedPoint φ selected) C γ hγ)
      cap hcapY hcapR
  exact proper_cut_seed_bound_of_global_shear_sum φ F G T hG hdiv hproper
    selected Γ nodes x u₀ u₁ hinj p w a e hw hchar hwa han hdegree
    hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
    (coordinateMixedDegree Ω G T) hcap hgeom.1 hgeom.2 dS hSbudget hfiber

/-- Generic implicit-pair incidence bound using the common global shear.  It
removes the old mixed `R` characteristic premise `2 * jY * jZ < p`; the exact
price is the `2 * w` contribution to the `Z` coefficient below. -/
theorem implicit_pair_seed_bound_common_global_shear
    (A G : MvPolynomial (Fin 4) K) (hG : Irreducible G)
    (hGR : G.degreeOf 2 = 1) (hproper : ¬ G ∣ A)
    (implicitD w jY jZ p n a e : ℕ)
    (hAbox : A ∈ globalCoefficientBox K implicitD w jZ 0)
    (hGbox : G ∈ globalCoefficientBox K implicitD w jZ 1)
    (hjY : (implicitD - 1) / w = jY)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n) [CharP K p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a) (han : a ≤ n)
    (hjYsmall : jY < p) (hjZsmall : jZ < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolutionA : ∀ γ ∈ Γ, specialization K (selected γ) γ A = 0)
    (hsolutionG : ∀ γ ∈ Γ, specialization K (selected γ) γ G = 0)
    (hregular : ∀ γ ∈ Γ,
      specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    Γ.card * (a - w) ≤
      (n - w) *
        ((1 + 2 * w * jY) * pairYCost ⟨A, G⟩ +
          w * pairRCost ⟨A, G⟩ +
          (2 * w * jZ + 1 + 2 * w) * pairZCost ⟨A, G⟩) +
      (e + 1) * (a - w) * pairZCost ⟨A, G⟩ := by
  classical
  let φ := polynomialEmbedding K
  let factors := surfaceFactors φ G
  let seedsFor := fun g : MvPolynomial (Fin 3) (GenericField K) =>
    Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g = 0)
  let surfaceCap : RCN051.DegreeVector := ⟨jY, 1, jZ⟩
  let cutCap : RCN051.DegreeVector := ⟨jY, 0, jZ⟩
  let agreementCap : RCN051.DegreeVector :=
    ⟨1 + 2 * w * jY, w, 2 * w * jZ + 1⟩
  have hsub (g) : seedsFor g ⊆ Γ := Finset.filter_subset _ _
  have hAGcaps := degree_bounds_of_mem_box A implicitD w jZ 0 hw hAbox
  have hGGcaps := degree_bounds_of_mem_box G implicitD w jZ 1 hw hGbox
  have hAY : A.degreeOf 1 ≤ jY := hAGcaps.1.trans_eq hjY
  have hGY : G.degreeOf 1 ≤ jY := hGGcaps.1.trans_eq hjY
  have hAR : A.degreeOf 2 = 0 := Nat.eq_zero_of_le_zero hAGcaps.2.1
  have hAcaps : HasCaps (surfaceMap φ A) cutCap := by
    intro i
    fin_cases i
    · exact (surfaceMap_degreeOf_le φ A 0).trans hAY
    · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
    · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
  have hFzero : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G) = 0 := by
    intro γ hγ
    rw [RCN170.canonical_selectedPoint_surface_evaluation,
      hsolutionG γ hγ, map_zero]
  have hAzero : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A) = 0 := by
    intro γ hγ
    rw [RCN170.canonical_selectedPoint_surface_evaluation,
      hsolutionA γ hγ, map_zero]
  have hcover : Γ ⊆ factors.biUnion seedsFor := by
    intro γ hγ
    obtain ⟨g, hg, hz⟩ := exists_surfaceFactor_zero φ
      (polynomialEmbedding_injective K) G hG.ne_zero
      (selectedPoint φ selected γ) (hFzero γ hγ)
    exact Finset.mem_biUnion.mpr
      ⟨g, hg, Finset.mem_filter.mpr ⟨hγ, hz⟩⟩
  have hcard : Γ.card ≤ ∑ g ∈ factors, (seedsFor g).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsingle (g : MvPolynomial (Fin 3) (GenericField K)) (hg : g ∈ factors) :
      (seedsFor g).card * (a - w) ≤
        (n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            capAt (RCN170.geometricPairCost A g) i) +
        (e + 1) * (a - w) *
          capAt (RCN170.geometricPairCost A g) 2 := by
    obtain ⟨hgi, hdiv⟩ := surfaceFactors_spec φ G g hg
    have hfacdegree (i : Fin 3) : g.degreeOf i ≤ G.degreeOf i.succ :=
      (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
        (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G
          hG.ne_zero)).trans (surfaceMap_degreeOf_le φ G i)
    have hgcaps : HasCaps g surfaceCap := by
      intro i
      fin_cases i
      · exact (hfacdegree 0).trans hGY
      · exact (hfacdegree 1).trans hGGcaps.2.1
      · exact (hfacdegree 2).trans hGGcaps.2.2
    have hsurfaceSmall : ∀ j, capAt surfaceCap j < p := by
      intro j
      fin_cases j
      · simpa [surfaceCap, capAt] using hjYsmall
      · simpa [surfaceCap, capAt] using lt_of_le_of_lt hw hchar
      · simpa [surfaceCap, capAt] using hjZsmall
    have hGdegree : ∀ j : Fin 3, g.degreeOf j < p :=
      fun j => (hgcaps j).trans_lt (hsurfaceSmall j)
    have hmixedYactual : coordinateMixedDegree (GenericField K) g
        (surfaceMap φ A) 0 < p := by
      have hpair := actual_pair_degree_le g (surfaceMap φ A)
        surfaceCap cutCap hgcaps hAcaps 1 2
      have hcapbound :
          capAt cutCap 1 * capAt surfaceCap 2 +
            capAt surfaceCap 1 * capAt cutCap 2 ≤ jZ := by
        simp [surfaceCap, cutCap, capAt]
      exact (hpair.trans hcapbound).trans_lt hjZsmall
    have hmixedZactual : coordinateMixedDegree (GenericField K) g
        (surfaceMap φ A) 2 < p := by
      have hpair := actual_pair_degree_le g (surfaceMap φ A)
        surfaceCap cutCap hgcaps hAcaps 0 1
      have hcapbound :
          capAt cutCap 0 * capAt surfaceCap 1 +
            capAt surfaceCap 0 * capAt cutCap 1 ≤ jY := by
        simp [surfaceCap, cutCap, capAt]
      simpa [coordinateMixedDegree_two] using
        (hpair.trans hcapbound).trans_lt hjYsmall
    have hreg : ∀ γ ∈ seedsFor g,
        MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
          (RCN231.polynomialPoint (φ.comp Polynomial.C)
            (selected γ) γ (φ Polynomial.X))
          (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0 := by
      intro γ hγ
      exact (initialPoint_regular_iff K G (selected γ) γ).mpr
        (hregular γ (hsub g hγ))
    have hcap (i : ι) : HasCaps
        (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)) agreementCap := by
      have h := surface_agreement_caps φ G jY 1 jZ (by decide)
        hGY hGGcaps.2.1 hGGcaps.2.2 w
        (fun j => (j.factorial : K)⁻¹) (x i) (u₀ i) (u₁ i)
      simpa [agreementPolynomial, agreementCaps, agreementCap] using h
    have hcount := proper_cut_seed_bound_of_common_global_shear φ G g
      (surfaceMap φ A) hgi hdiv
      (RCN170.geometric_factor_proper_cut A G hG hGR hproper g hg)
      selected (seedsFor g) nodes x u₀ u₁ hinj p w a e hw hchar hwa
      (by simpa [hnodes] using han) hGdegree hmixedYactual hmixedZactual
      (fun γ hγ => hdegree γ (hsub g hγ))
      (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => hAzero γ (hsub g hγ))
      (fun γ hγ => hagreement γ (hsub g hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e (hsub g) hnoPencil)
      (capAt agreementCap) (fun i _ => hcap i)
      (by simp [agreementCap, capAt]) (by simpa [agreementCap, capAt] using hw)
    rw [hnodes] at hcount
    have hδ (i : Fin 3) :=
      RCN170.coordinateMixedDegree_le_geometricPairCost φ A hAR g i
    exact hcount.trans (Nat.add_le_add
      (Nat.mul_le_mul_left (n - w) (Finset.sum_le_sum
        (fun i _ => Nat.mul_le_mul_left
          (adaptiveShearCap (capAt agreementCap) i) (hδ i))))
      (Nat.mul_le_mul_left ((e + 1) * (a - w)) (hδ 2)))
  have hbudget (i : Fin 3) :
      (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) i) ≤
        capAt (RCN170.pairCost A G) i :=
    RCN170.sum_geometricPairCost_le φ
      (polynomialEmbedding_injective K) A G hG.ne_zero i
  have hfubini :
      (∑ g ∈ factors, ∑ i : Fin 3,
        adaptiveShearCap (capAt agreementCap) i *
          capAt (RCN170.geometricPairCost A g) i) =
      ∑ i : Fin 3, adaptiveShearCap (capAt agreementCap) i *
        (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Γ.card * (a - w) ≤ (∑ g ∈ factors, (seedsFor g).card) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hcard
    _ = ∑ g ∈ factors, (seedsFor g).card * (a - w) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g ∈ factors,
        ((n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            capAt (RCN170.geometricPairCost A g) i) +
          (e + 1) * (a - w) *
            capAt (RCN170.geometricPairCost A g) 2) :=
      Finset.sum_le_sum (fun g hg => hsingle g hg)
    _ = (n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) i)) +
        (e + 1) * (a - w) *
          (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfubini]
    _ ≤ (n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            capAt (RCN170.pairCost A G) i) +
        (e + 1) * (a - w) * capAt (RCN170.pairCost A G) 2 :=
      Nat.add_le_add
        (Nat.mul_le_mul_left (n - w) (Finset.sum_le_sum
          (fun i _ => Nat.mul_le_mul_left
            (adaptiveShearCap (capAt agreementCap) i) (hbudget i))))
        (Nat.mul_le_mul_left ((e + 1) * (a - w)) (hbudget 2))
    _ = (n - w) *
        ((1 + 2 * w * jY) * pairYCost ⟨A, G⟩ +
          w * pairRCost ⟨A, G⟩ +
          (2 * w * jZ + 1 + 2 * w) * pairZCost ⟨A, G⟩) +
        (e + 1) * (a - w) * pairZCost ⟨A, G⟩ := by
      simp [Fin.sum_univ_three, adaptiveShearCap, capAt, agreementCap,
        RCN170.pairCost]

end

end ProximityPrize.SubmissionLower.CommonShearConsumerPrototype
