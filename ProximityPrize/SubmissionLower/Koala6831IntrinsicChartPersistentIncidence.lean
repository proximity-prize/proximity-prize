import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartPersistentCount
import ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped Classical BigOperators
open RCN002 RCN065 RCN135 RCN136 RCN341 RCN344 Koala6831OrdinaryIncidence

noncomputable section

set_option maxHeartbeats 4900000
set_option maxRecDepth 22000

variable {K I : Type} [Field K]

theorem persistent_curve_selected_seed_bound
    (F : Carrier K) (w bound p t z : ℕ) [CharP (GenericField K) p]
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K))) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (d₀ d₁ : ℕ)
    (hd₀ : ∀ W : Finset (Place (GenericField K) (CoordinateField (GenericField K) C)),
      (∑ v ∈ W, RCN346.poleOrder (GenericField K) (CoordinateField (GenericField K) C) v
        (coordinate (GenericField K) C 1)) ≤ (d₀ : ℤ))
    (hd₁ : ∀ W : Finset (Place (GenericField K) (CoordinateField (GenericField K) C)),
      (∑ v ∈ W, RCN346.poleOrder (GenericField K) (CoordinateField (GenericField K) C) v
        (coordinate (GenericField K) C 2)) ≤ (d₁ : ℤ))
    (hF : surfaceMap (polynomialEmbedding K) F ∈ C)
    (hS : surfaceMap (polynomialEmbedding K) (implicitRegularity F) ∉ C)
    (htail : ∀ delay, surfaceMap (polynomialEmbedding K) (tailNumerator F (w + delay)) ∈ C)
    (hbound : 2 ≤ bound) (hw : w + 1 ≤ bound) (hchar : bound < p)
    (hweight : RCN234.wt (![1, w, 0, 0] : Fin 4 → ℕ) F < bound)
    (ht : ∀ d ∈ F.support, d 2 ≤ t) (hz : ∀ d ∈ F.support, d 3 ≤ z)
    (x : I ↪ K) (u₀ u₁ : I → K) (nodes : Finset I) (A e : ℕ)
    (hwA : w < A) (hAn : A ≤ nodes.card)
    (haverage : nodeAverage nodes.card w A ≤ 3)
    (seeds allSeeds : Finset K) (hsub : seeds ⊆ allSeeds)
    (selected : K → Polynomial K) (seed₁ : K → K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hgraph : ∀ g ∈ seeds, graphSpecialize (selected g) g (seed₁ g) F = 0)
    (hreg : ∀ g ∈ seeds, MvPolynomial.eval
      (polynomialGraphSurfacePoint (polynomialEmbedding K) (selected g) g (seed₁ g))
      (surfaceMap (polynomialEmbedding K) (implicitRegularity F)) ≠ 0)
    (hpoint : ∀ g ∈ seeds, C ≤ RingHom.ker
      (MvPolynomial.aeval
        (polynomialGraphSurfacePoint (polynomialEmbedding K) (selected g) g (seed₁ g))).toRingHom)
    (hagreements : ∀ g ∈ seeds, A ≤
      (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds allSeeds selected P₀ P₁).card ≤ e + 1) :
    seeds.card ≤ 3 * ((t + 1) * d₀ + z * d₁) + (e + 1) := by
  classical
  obtain ⟨P, _hP, hroot, hagree⟩ :=
    curve_persistent_uncentered_witness F w bound p C hF hS htail hbound hw hchar hweight
  let Ω := GenericField K
  let φ := polynomialEmbedding K
  let coeff := componentCoefficients φ C
  let cost := (t + 1) * d₀ + z * d₁
  let H := surfaceMap φ (implicitRegularity F)
  let V := fun g => polynomialGraphSurfacePoint φ (selected g) g (seed₁ g)
  let rel := fun g i => (selected g).eval (x i) = u₀ i + g * u₁ i
  let nodeValue := fun i => P.eval (coeff (x i)) - coeff (u₀ i) -
    coeff (u₁ i) * coordinate Ω C 1
  let ids := nodes.filter (fun i => nodeValue i = 0)
  have hV : Function.Injective V := by
    intro g h hgh
    have hh := congrFun hgh (1 : Fin 3)
    exact Polynomial.C_injective ((polynomialEmbedding_injective K) (by exact hh))
  have hraw (g : K) (hg : g ∈ seeds) (i : I) :
      MvPolynomial.eval (V g) (surfaceMap φ (persistentAgreementNumerator F w (x i) (u₀ i) (u₁ i))) = 0 ↔
        rel g i := by
    have heq := persistentAgreementNumerator_selected_zero_iff φ F (selected g) g (seed₁ g)
      (hgraph g hg) (hreg g hg) p w (by omega) (hdegree g hg) (x i) (u₀ i) (u₁ i)
    simpa only [rel, mul_comm] using heq
  by_cases hi : ids.card ≤ w
  · have hfiber (i : I) (hni : i ∈ nodes \ ids) :
        (seeds.filter (fun g => rel g i)).card ≤ cost := by
      have hproper : nodeValue i ≠ 0 := by
        intro hzero
        exact (Finset.mem_sdiff.mp hni).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hni).1, hzero⟩)
      obtain ⟨B, _, hcount⟩ := persistent_curve_regular_agreement_bound F w t z C base d₀ d₁
        hd₀ hd₁ hS ht hz P hroot (x i) (u₀ i) (u₁ i) (hagree (x i) (u₀ i) (u₁ i)) hproper
      let fiber := seeds.filter (fun g => rel g i)
      let points := fiber.image V
      have hpts : points.card ≤ cost := by
        apply hcount
        · intro q hq
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
          exact hpoint g (Finset.mem_filter.mp hg).1
        · intro q hq
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
          exact hreg g (Finset.mem_filter.mp hg).1
        · intro q hq
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
          obtain ⟨hgs, hgi⟩ := Finset.mem_filter.mp hg
          rw [map_mul]
          exact mul_eq_zero.mpr (Or.inr ((hraw g hgs i).2 hgi))
      rwa [Finset.card_image_of_injective _ hV] at hpts
    have havg := incidence_le_shortened_scaled rel seeds nodes ids A w 1 0 cost
      (by decide) (Finset.filter_subset _ _) hi hwA hAn hagreements
      (fun i hi => by simpa only [mul_one, zero_mul, add_zero] using hfiber i hi)
    simp only [Nat.cast_one, Nat.cast_zero, mul_one, zero_mul, zero_add] at havg
    have hrat : (seeds.card : ℚ) ≤ (3 : ℚ) * cost := by
      exact havg.trans (by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left haverage (show (0 : ℚ) ≤ cost from by positivity))
    exact Nat.le_add_right_of_le (by exact_mod_cast hrat)
  · have hident (g : K) (hg : g ∈ seeds) (i : I) (hni : i ∈ ids) : rel g i := by
      have hI : nodeValue i = 0 := (Finset.mem_filter.mp hni).2
      let raw := surfaceMap φ (persistentAgreementNumerator F w (x i) (u₀ i) (u₁ i))
      have hH : coordinateEvaluation Ω C H ≠ 0 := by
        intro hzero
        apply hS
        change H ∈ RingHom.ker (coordinateEvaluation Ω C).toRingHom at hzero
        rwa [coordinateEvaluation_ker] at hzero
      have hzero : coordinateEvaluation Ω C raw / (coordinateEvaluation Ω C H) ^ (2 * w) = 0 :=
        (hagree (x i) (u₀ i) (u₁ i)).trans hI
      have hmem : raw ∈ C := by
        have hfield := (div_eq_zero_iff.mp hzero).resolve_right (pow_ne_zero _ hH)
        change raw ∈ RingHom.ker (coordinateEvaluation Ω C).toRingHom at hfield
        rwa [coordinateEvaluation_ker] at hfield
      exact (hraw g hg i).1 (hpoint g hg hmem)
    obtain ⟨P₀, P₁, h₀, h₁, hline⟩ := RCN147.exists_basefield_affine_pencil_of_identity_nodes
      (RingHom.id K) ids x u₀ u₁ w (by omega) x.injective.injOn
      (fun g : ↥seeds => g.val) (fun g => selected g.val) (fun g => hdegree g.val g.property)
      (fun g i hi => hident g.val g.property i hi)
    have hsize : seeds.card ≤ e + 1 := by
      refine (Finset.card_le_card (t := RCN050.pencilSeeds allSeeds selected P₀ P₁) ?_).trans
        (hpencil P₀ P₁ h₀ h₁)
      intro g hg
      refine Finset.mem_filter.mpr ⟨hsub hg, ?_⟩
      simpa only [Polynomial.map_id] using hline ⟨g, hg⟩
    exact hsize.trans (Nat.le_add_left _ _)

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
