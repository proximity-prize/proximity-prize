import ProximityPrize.SubmissionLower.Koala6844VirtualHighActualResidual
import ProximityPrize.SubmissionLower.Koala6844VirtualHighCount
import ProximityPrize.SubmissionLower.Koala6831IntrinsicSelectedComponents


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
open Koala6831Intrinsic RCN005 RCN007 RCN135 RCN136 RCN137 RCN264

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K : Type} [Field K]

def rawComponentSeeds (F V W : Carrier K) (first p : ℕ)
    (G : MvPolynomial (Fin 3) (GenericField K)) (seeds : Finset K)
    (selected : K → Polynomial K) (C : RawTrimmedComponent F V W first G) : Finset K :=
  componentSeeds (GenericField K) G
    (surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W first))
    (surfaceMap (polynomialEmbedding K) (V * implicitRegularity F))
    seeds (selectedGraphPoint p selected) C

def literalRectangle (G : MvPolynomial (Fin 3) (GenericField K)) : Rectangle :=
  ⟨G.degreeOf 0, G.degreeOf 1, G.degreeOf 2⟩

theorem literalRectangle_coordinate (G : MvPolynomial (Fin 3) (GenericField K)) (i : Fin 3) :
    rectangleCoordinate (literalRectangle G) i = G.degreeOf i := by
  fin_cases i <;> rfl

theorem selected_proper_factor_residual_count
    (F V W : Carrier K) (first J p : ℕ) [CharP K p] (hp : p.Prime)
    [ExpChar (GenericField K) p] [PerfectRing (GenericField K) p]
    (G : MvPolynomial (Fin 3) (GenericField K))
    (hF : Irreducible F) (hG : Irreducible G)
    (hFpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3)
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (properOriginal : ¬ F ∣ rawTrimmedTail F V W first)
    (f : Rectangle) (hy : 1 ≤ f.value) (hfirst : first+1 ≤ J)
    (hFcap : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hVcap : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0)
    (hWcap : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000)
    (seeds : Finset K) (selected trimmed : K → Polynomial K) (scale : K → K)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) (V * implicitRegularity F) ≠ 0)
    (hGzero : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint p selected g) G = 0)
    (htrim : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) W =
      Polynomial.C (scale g) * graphSpecialize (selected g) g (g^p) V * trimmed g)
    (hdeg : ∀ g ∈ seeds, (trimmed g).natDegree ≤ first)
    (persistent : ∀ (C : RawTrimmedComponent F V W first G) μ, 1 ≤ μ →
      (∀ delay, surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (first+delay)) ∈ C.1) →
      (rawComponentSeeds F V W first p G seeds selected C).card ≤
        ∑ i, (μ * rectangleCoordinate (tailRectangle (J+1) f) i) *
          actualCoordinateDegree (GenericField K) C.1 i) :
    seeds.card ≤ mixedDegree (literalRectangle G) (tailRectangle J f) (tailRectangle (J+1) f) := by
  classical
  let Ω := GenericField K
  let φ := polynomialEmbedding K
  let P := selectedGraphPoint p selected
  let T (n : ℕ) := surfaceMap φ (rawTrimmedTail F V W n)
  let H := surfaceMap φ (V * implicitRegularity F)
  let S := rawComponentSeeds F V W first p G seeds selected
  let points (C : RawTrimmedComponent F V W first G) := (S C).image P
  have card (C) : (points C).card = (S C).card :=
    Finset.card_image_of_injective _ (selectedGraphPoint_injective p selected)
  have zero (g) (hg : g ∈ seeds) (n : ℕ) (hn : first ≤ n) :
      MvPolynomial.eval (P g) (T n) = 0 := by
    change MvPolynomial.eval (polynomialGraphSurfacePoint φ (selected g) g (g^p))
      (surfaceMap φ (rawTrimmedTail F V W n)) = 0
    rw [eval_polynomialGraphSurfacePoint,
      graphSpecialize_rawTrimmedTail_eq_zero F V W (selected g) (trimmed g) g (g^p)
        (scale g) n (hroot g hg) (htrim g hg) ((hdeg g hg).trans hn),
      map_zero]
  have regular (g) (hg : g ∈ seeds) : MvPolynomial.eval (P g) H ≠ 0 := by
    change MvPolynomial.eval (polynomialGraphSurfacePoint φ (selected g) g (g^p))
      (surfaceMap φ (V * implicitRegularity F)) ≠ 0
    rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
    exact hreg g hg
  have cover : seeds.card ≤ ∑ C, (points C).card := by
    simp only [card]
    exact card_le_sum_componentSeeds Ω G (T first) H seeds P hGzero
      (fun g hg => zero g hg first le_rfl) regular
  apply cover.trans
  refine sum_actual_residual_points_le_mixedDegree F V W first J p hp G hF hG hFpos
    hdiv properOriginal (literalRectangle G) f hy hfirst hFcap hVcap hWcap
    (fun i => le_of_eq (literalRectangle_coordinate G i).symm) points ?_ ?_ ?_ ?_
  · intro C v hv
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime Ω G (T first) H seeds P C g hg
  · intro C v hv
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
    exact regular g (componentSeeds_subset Ω G (T first) H seeds P C hg)
  · intro C v hv n hn
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
    exact zero g (componentSeeds_subset Ω G (T first) H seeds P C hg) n hn
  · intro C μ hμ hwhole
    rw [card]
    exact persistent C μ hμ hwhole

def geometricFactorSeeds (seeds : Finset K) (selected : K → Polynomial K) (p : ℕ)
    (G : MvPolynomial (Fin 3) (GenericField K)) : Finset K :=
  seeds.filter fun g => MvPolynomial.eval (selectedGraphPoint p selected g) G = 0

theorem selected_geometric_factor_cover
    (F : Carrier K) (hF : F ≠ 0) (p : ℕ)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0) :
    seeds ⊆ (surfaceFactors (polynomialEmbedding K) F).biUnion
      (geometricFactorSeeds seeds selected p) := by
  classical
  let φ := polynomialEmbedding K
  intro g hg
  have hz : MvPolynomial.eval (selectedGraphPoint p selected g) (surfaceMap φ F) = 0 := by
    change MvPolynomial.eval (polynomialGraphSurfacePoint φ (selected g) g (g^p))
      (surfaceMap φ F) = 0
    rw [eval_polynomialGraphSurfacePoint, hroot g hg, map_zero]
  obtain ⟨G, hG, hzG⟩ := exists_surfaceFactor_zero φ
    (polynomialEmbedding_injective K) F hF _ hz
  exact Finset.mem_biUnion.mpr ⟨G, hG, Finset.mem_filter.mpr ⟨hg, hzG⟩⟩

theorem selected_carrier_count_of_geometric_factors
    (F : Carrier K) (hF : F ≠ 0) (p : ℕ)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0)
    (f firstTail laterTail : Rectangle)
    (hFcap : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hcount : ∀ G ∈ surfaceFactors (polynomialEmbedding K) F,
      (geometricFactorSeeds seeds selected p G).card ≤ mixedDegree (literalRectangle G)
        firstTail laterTail) :
    seeds.card ≤ mixedDegree f firstTail laterTail := by
  classical
  let φ := polynomialEmbedding K
  let family := surfaceFactors φ F
  let hits := geometricFactorSeeds seeds selected p
  have cover := selected_geometric_factor_cover F hF p seeds selected hroot
  have budget (i : Fin 3) := surfaceFactors_degree_budget φ
    (polynomialEmbedding_injective K) F hF i
  exact (Finset.card_le_card cover).trans
    (card_biUnion_le_mixedDegree family hits literalRectangle f firstTail laterTail hcount
      ((budget 0).trans hFcap.1) ((budget 1).trans hFcap.2.1) ((budget 2).trans hFcap.2.2))

theorem selected_carrier_invariant_count_of_geometric_factors
    (F : Carrier K) (hF : F ≠ 0) (p : ℕ)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0)
    (cost : ℕ)
    (hcount : ∀ G ∈ surfaceFactors (polynomialEmbedding K) F,
      (geometricFactorSeeds seeds selected p G).card ≤ cost * G.degreeOf 0) :
    seeds.card ≤ cost * F.degreeOf 1 := by
  classical
  let φ := polynomialEmbedding K
  let family := surfaceFactors φ F
  let hits := geometricFactorSeeds seeds selected p
  calc
    _ ≤ (family.biUnion hits).card :=
      Finset.card_le_card (selected_geometric_factor_cover F hF p seeds selected hroot)
    _ ≤ ∑ G ∈ family, (hits G).card := Finset.card_biUnion_le
    _ ≤ ∑ G ∈ family, cost * G.degreeOf 0 := Finset.sum_le_sum hcount
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ (surfaceFactors_degree_budget φ
        (polynomialEmbedding_injective K) F hF 0)


theorem regularComponent_actualDegree_sum_pos
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G T H : MvPolynomial (Fin 3) Ω}
    (p : ℕ) [ExpChar Ω p] [PerfectRing Ω p] (hp : p.Prime)
    (C : RegularComponent Ω G T H) (hG : Irreducible G) (hproper : ¬ G ∣ T) :
    1 ≤ ∑ i, actualCoordinateDegree Ω C.1 i := by
  obtain ⟨base⟩ := regularComponent_exists_separating_literal p hp C hG hproper
  have hdeg : 1 ≤ actualCoordinateDegree Ω C.1 base.index := by
    rw [actualCoordinateDegree_of_transcendental Ω C.1 base.index base.transcendental]
    letI := rationalBaseAlgebra Ω C.1 base.index base.transcendental
    letI := base.finite
    exact Module.finrank_pos
  exact hdeg.trans (Finset.single_le_sum (f := fun i => actualCoordinateDegree Ω C.1 i)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ base.index))

theorem persistent_curve_charge_le_tailRectangle
    (f : Rectangle) (J μ : ℕ) (hJ : 2 ≤ J) (hμ : 1 ≤ μ)
    (degree : Fin 3 → ℕ) (positive : 1 ≤ ∑ i, degree i) :
    4 * ((f.first+1) * degree 1 + f.second * degree 2) + 1 ≤
      ∑ i, (μ * rectangleCoordinate (tailRectangle (J+1) f) i) * degree i := by
  rw [Fin.sum_univ_three] at positive ⊢
  let q := tailRectangle (J+1) f
  change _ ≤ (μ*q.value)*degree 0 + (μ*q.first)*degree 1 + (μ*q.second)*degree 2
  have hcoeff : 4 ≤ 2*(J+1)-1 := by omega
  have hv : 1 ≤ q.value := Nat.le_add_right _ _
  have h₀ : 4*(f.first+1)+1 ≤ q.first := by
    change 4*(f.first+1)+1 ≤ (2*(J+1)-1)*f.first+10000
    calc
      _ = 4*f.first+5 := by ring
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ hcoeff) (by decide)
  have h₁ : 4*f.second+1 ≤ q.second :=
    Nat.add_le_add (Nat.mul_le_mul_right _ hcoeff) (by decide)
  have mulCap {a b : ℕ} (h : a ≤ b) : a ≤ μ*b :=
    h.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right b hμ)
  calc
    _ ≤ 4 * ((f.first+1) * degree 1 + f.second * degree 2) +
        (degree 0 + degree 1 + degree 2) := Nat.add_le_add_left positive _
    _ = 1*degree 0 + (4*(f.first+1)+1)*degree 1 + (4*f.second+1)*degree 2 := by ring
    _ ≤ _ := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_right _ (mulCap hv))
        (Nat.mul_le_mul_right _ (mulCap h₀)))
      (Nat.mul_le_mul_right _ (mulCap h₁))


end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh



