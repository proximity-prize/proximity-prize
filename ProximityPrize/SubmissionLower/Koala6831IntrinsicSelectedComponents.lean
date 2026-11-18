import ProximityPrize.SubmissionLower.Koala6831IntrinsicChartCuts

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open RCN135 RCN136 RCN138 RCN264
open scoped Classical BigOperators Polynomial

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

abbrev FirstTailComponent (F : Carrier K) (w : ℕ) (G : MvPolynomial (Fin 3) (GenericField K)) :=
  RegularComponent (GenericField K) G
    (surfaceMap (polynomialEmbedding K) (tailNumerator F w))
    (surfaceMap (polynomialEmbedding K) (implicitRegularity F))

def selectedGraphPoint (p : ℕ) (selected : K → K[X]) (g : K) : Fin 3 → GenericField K :=
  polynomialGraphSurfacePoint (polynomialEmbedding K) (selected g) g (g ^ p)

theorem selectedGraphPoint_injective (p : ℕ) (selected : K → K[X]) :
    Function.Injective (selectedGraphPoint p selected) := by
  intro g h eq
  exact Polynomial.C_injective (polynomialEmbedding_injective K (congrFun eq (1 : Fin 3)))

def selectedOnComponent (F : Carrier K) (w p : ℕ) (G : MvPolynomial (Fin 3) (GenericField K))
    (seeds : Finset K) (selected : K → K[X]) (C : FirstTailComponent F w G) : Finset K :=
  componentSeeds (GenericField K) G
    (surfaceMap (polynomialEmbedding K) (tailNumerator F w))
    (surfaceMap (polynomialEmbedding K) (implicitRegularity F))
    seeds (selectedGraphPoint p selected) C

def selectedComponentPoints (F : Carrier K) (w p : ℕ) (G : MvPolynomial (Fin 3) (GenericField K))
    (seeds : Finset K) (selected : K → K[X]) (C : FirstTailComponent F w G) :
    Finset (Fin 3 → GenericField K) :=
  (selectedOnComponent F w p G seeds selected C).image (selectedGraphPoint p selected)

theorem selectedComponentPoints_card (F : Carrier K) (w p : ℕ)
    (G : MvPolynomial (Fin 3) (GenericField K)) (seeds : Finset K)
    (selected : K → K[X]) (C : FirstTailComponent F w G) :
    (selectedComponentPoints F w p G seeds selected C).card =
      (selectedOnComponent F w p G seeds selected C).card :=
  Finset.card_image_of_injective _ (selectedGraphPoint_injective p selected)

theorem selectedComponentPoints_spec (F : Carrier K) (w p : ℕ)
    (G : MvPolynomial (Fin 3) (GenericField K)) (seeds : Finset K)
    (selected : K → K[X]) (C : FirstTailComponent F w G)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) F = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) (implicitRegularity F) ≠ 0)
    (v : Fin 3 → GenericField K) (hv : v ∈ selectedComponentPoints F w p G seeds selected C) :
    C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom ∧
      MvPolynomial.aeval v (surfaceMap (polynomialEmbedding K) (implicitRegularity F)) ≠ 0 ∧
      ∀ j, MvPolynomial.aeval v (surfaceMap (polynomialEmbedding K) (tailNumerator F (w + j))) = 0 := by
  classical
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
  have hs : g ∈ seeds := (Finset.mem_filter.mp hg).1
  refine ⟨(Finset.mem_filter.mp hg).2, ?_, ?_⟩
  · change MvPolynomial.eval (polynomialGraphSurfacePoint (polynomialEmbedding K) (selected g) g (g ^ p))
      (surfaceMap (polynomialEmbedding K) (implicitRegularity F)) ≠ 0
    rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
    exact hreg g hs
  · intro j
    exact polynomialGraphSurfacePoint_tail_zero (polynomialEmbedding K) F (selected g) g (g ^ p)
      (hroot g hs) _ ((hdegree g hs).trans (Nat.le_add_right _ _))

theorem selected_card_le_sum_componentPoints (F : Carrier K) (w p : ℕ)
    (G : MvPolynomial (Fin 3) (GenericField K)) (seeds : Finset K) (selected : K → K[X])
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) F = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ p) (implicitRegularity F) ≠ 0)
    (hG : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint p selected g) G = 0) :
    seeds.card ≤ ∑ C : FirstTailComponent F w G, (selectedComponentPoints F w p G seeds selected C).card := by
  simp only [selectedComponentPoints_card]
  refine card_le_sum_componentSeeds _ G _ _ seeds (selectedGraphPoint p selected) hG ?_ ?_
  · intro g hg
    exact polynomialGraphSurfacePoint_tail_zero (polynomialEmbedding K) F (selected g) g (g ^ p)
      (hroot g hg) _ (hdegree g hg)
  · intro g hg
    change MvPolynomial.eval (polynomialGraphSurfacePoint (polynomialEmbedding K) (selected g) g (g ^ p))
      (surfaceMap (polynomialEmbedding K) (implicitRegularity F)) ≠ 0
    rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
    exact hreg g hg

private theorem dvd_clearedImplicit_of_dvd (F A : Carrier K) (hA : F ∣ A) :
    F ∣ clearedImplicit F A := by
  obtain ⟨B, rfl⟩ := hA
  refine ⟨clearedImplicit F B, ?_⟩
  simp only [clearedImplicit, implicitRegularity, MvPolynomial.pderiv_mul]
  ring

theorem dvd_tailNumerator_add (F : Carrier K) (w : ℕ)
    (h : F ∣ tailNumerator F w) (k : ℕ) : F ∣ tailNumerator F (w + k) := by
  induction k with
  | zero => simpa only [Nat.add_zero] using h
  | succ k ih =>
    rw [Nat.add_succ, tailNumerator]
    have hfirst := dvd_clearedImplicit_of_dvd F _ ih
    exact dvd_sub (dvd_mul_of_dvd_right hfirst _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ih _) _)

theorem geometric_dvd_tailNumerator_add (F : Carrier K) (hF : Irreducible F)
    (hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) (w : ℕ)
    (G : MvPolynomial (Fin 3) (GenericField K)) (hG : Irreducible G)
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hfirst : G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F w)) (k : ℕ) :
    G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F (w + k)) := by
  have hdiv' : G ∣ geometricSurfaceMap K (GenericField K) F := by
    rwa [canonical_geometricSurfaceMap]
  have h : F ∣ tailNumerator F w := by
    apply (geometric_factor_dvd_iff K (GenericField K) F _ hF hpos G hG hdiv').mp
    rwa [canonical_geometricSurfaceMap]
  exact hdiv.trans (map_dvd (surfaceMap (polynomialEmbedding K)) (dvd_tailNumerator_add F w h k))

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
