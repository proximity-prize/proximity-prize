import ProximityPrize.SubmissionLower.Koala6844VirtualHighGeometricOrder
import ProximityPrize.SubmissionLower.Koala6844VirtualHighResidualDegrees
import ProximityPrize.SubmissionLower.Koala6844VirtualHighSeparatingLiteral
import ProximityPrize.SubmissionLower.Koala6844VirtualHighTailCaps


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
open Koala6831Intrinsic RCN005 RCN007 RCN135 RCN136 RCN138 RCN219 RCN264

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {K : Type} [Field K]

abbrev RawTrimmedComponent (F V W : Carrier K) (first : ℕ)
    (G : MvPolynomial (Fin 3) (GenericField K)) :=
  RegularComponent (GenericField K) G
    (surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W first))
    (surfaceMap (polynomialEmbedding K) (V * implicitRegularity F))

private theorem tailRectangleCoordinate_mono (f : Rectangle) {a b : ℕ} (hab : a ≤ b)
    (i : Fin 3) :
    rectangleCoordinate (tailRectangle a f) i ≤ rectangleCoordinate (tailRectangle b f) i := by
  have h : 2*a-1 ≤ 2*b-1 := by omega
  fin_cases i
  · change 1 + (2*a-1)*(f.value-1) ≤ 1 + (2*b-1)*(f.value-1)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
  · change (2*a-1)*f.first+10000 ≤ (2*b-1)*f.first+10000
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
  · change (2*a-1)*f.second+10000 ≤ (2*b-1)*f.second+10000
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _

theorem sum_actual_residual_points_le_mixedDegree
    (F V W : Carrier K) (first J p : ℕ) [CharP K p] (hp : p.Prime)
    [ExpChar (GenericField K) p] [PerfectRing (GenericField K) p]
    (G : MvPolynomial (Fin 3) (GenericField K))
    (hF : Irreducible F) (hG : Irreducible G)
    (hFpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3)
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (properOriginal : ¬ F ∣ rawTrimmedTail F V W first)
    (surface f : Rectangle) (hy : 1 ≤ f.value) (hfirst : first+1 ≤ J)
    (hFcap : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hVcap : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0)
    (hWcap : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000)
    (surfaceCap : ∀ i, G.degreeOf i ≤ rectangleCoordinate surface i)
    (points : RawTrimmedComponent F V W first G → Finset (Fin 3 → GenericField K))
    (hpoints : ∀ C v, v ∈ points C → C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hregular : ∀ C v, v ∈ points C →
      MvPolynomial.aeval v (surfaceMap (polynomialEmbedding K) (V * implicitRegularity F)) ≠ 0)
    (hzero : ∀ C v, v ∈ points C → ∀ n, first ≤ n →
      MvPolynomial.aeval v (surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W n)) = 0)
    (persistent : ∀ C μ, 1 ≤ μ →
      (∀ delay, surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (first+delay)) ∈ C.1) →
      (points C).card ≤ ∑ i, (μ * rectangleCoordinate (tailRectangle (J+1) f) i) *
        actualCoordinateDegree (GenericField K) C.1 i) :
    (∑ C, (points C).card) ≤ mixedDegree surface (tailRectangle J f) (tailRectangle (J+1) f) := by
  classical
  let Ω := GenericField K
  let φ := polynomialEmbedding K
  let A := RawTrimmedComponent F V W first G
  let T (n : ℕ) := surfaceMap φ (rawTrimmedTail F V W n)
  let H := surfaceMap φ (V * implicitRegularity F)
  have properGeometric : ¬ G ∣ T first := by
    intro h
    apply properOriginal
    have hdiv' : G ∣ geometricSurfaceMap K (GenericField K) F := by
      rw [canonical_geometricSurfaceMap]
      exact hdiv
    have div := geometric_factor_dvd_iff K (GenericField K) F
      (rawTrimmedTail F V W first) hF hFpos G hG hdiv'
    apply div.mp
    rw [canonical_geometricSurfaceMap]
    exact h
  have hcaps (n : ℕ) (i : Fin 3) :
      (T n).degreeOf i ≤ rectangleCoordinate (tailRectangle (n+1) f) i := by
    obtain ⟨h0, h1, h2⟩ := surface_rawTrimmedTail_degrees φ F V W f n hy hFcap hVcap hWcap
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hfirstCap (i : Fin 3) : (T first).degreeOf i ≤ rectangleCoordinate (tailRectangle J f) i :=
    (hcaps first i).trans (tailRectangleCoordinate_mono f hfirst i)
  choose μ positive primary decisions using
    fun C : A => geometric_order_rawTrimmedTail F V W first p hp G hdiv hF properOriginal C
  refine sum_residual_curve_counts_le_mixedDegree (G := G) (T := T first) (H := H)
    (fun C : A => C) Function.injective_id μ positive primary hG properGeometric
    surface (tailRectangle J f) (tailRectangle (J+1) f) surfaceCap hfirstCap
    (fun C => (points C).card) ?_
  intro C
  rcases decisions C with ⟨delay, _, hdelay, hproper⟩ | hpersistent
  · let tail := T (first+delay)
    obtain ⟨seed⟩ := regularComponent_exists_separating_literal p hp C hG properGeometric
    obtain ⟨hv, h₀, h₁⟩ :=
      tailRectangle_delay_le f (first+1) J delay (μ C) hy (by omega) hfirst hdelay (positive C)
    have lowerCap (i : Fin 3) :
        rectangleCoordinate (tailRectangle (first+delay+1) f) i ≤
          μ C * rectangleCoordinate (tailRectangle (J+1) f) i := by
      rw [show first+delay+1 = first+1+delay by omega]
      fin_cases i
      · exact hv
      · exact h₀
      · exact h₁
    have cap (i : Fin 3) :
        tail.degreeOf i ≤ μ C * rectangleCoordinate (tailRectangle (J+1) f) i :=
      (hcaps (first+delay) i).trans (lowerCap i)
    have count := regular_zero_bound_of_rectangular_poles C.1 seed H tail
      (fun i => μ C * rectangleCoordinate (tailRectangle (J+1) f) i)
      (actualCoordinateDegree Ω C.1) hproper
      (regularComponent_H_not_mem Ω G (T first) H C) cap
      (finite_pole_sum_le_actualCoordinateDegree p hp C.1 seed)
    exact count (points C) (hpoints C) (hregular C)
      (fun v hv => hzero C v hv (first+delay) (by omega))
  · exact persistent C (μ C) (positive C) hpersistent

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

