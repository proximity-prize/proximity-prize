import ProximityPrize.SubmissionLower.Koala6844VirtualHighSelectedResidual
import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantBridge
import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantIncidence


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
open Koala6831Intrinsic Koala6831OrdinaryIncidence RCN002 RCN007 RCN135 RCN136 RCN137 RCN138 RCN264

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2600000

variable {K I : Type} [Field K]

theorem degreeOf_coefficient_map_le {E : Type} [Field E] (embed : K →+* E)
    (F : Carrier K) (i : Fin 4) :
    (MvPolynomial.map embed F).degreeOf i ≤ F.degreeOf i := by
  simp only [MvPolynomial.degreeOf_def]
  exact Multiset.count_le_of_le i (MvPolynomial.degrees_map_le (p := F) (f := embed))

def InvariantTrim.map {E : Type} [Field E] {V W : Carrier K} {first plain : ℕ}
    (trimData : InvariantTrim V W first plain) (embed : K →+* E) :
    InvariantTrim (MvPolynomial.map embed V) (MvPolynomial.map embed W) first plain where
  denominator := MvPolynomial.map embed trimData.denominator
  remainder := MvPolynomial.map embed trimData.remainder
  divisorDegree := trimData.divisorDegree
  shape := by
    simpa only [map_sub, map_mul, MvPolynomial.map_X] using
      congrArg (MvPolynomial.map embed) trimData.shape
  denominator_X := (degreeOf_coefficient_map_le embed _ 0).trans trimData.denominator_X
  denominator_Y := (degreeOf_coefficient_map_le embed _ 1).trans trimData.denominator_Y
  divisor_Y := (degreeOf_coefficient_map_le embed _ 1).trans trimData.divisor_Y
  remainder_Y := (degreeOf_coefficient_map_le embed _ 1).trans trimData.remainder_Y
  divisor_X := (degreeOf_coefficient_map_le embed _ 0).trans trimData.divisor_X
  remainder_X := (degreeOf_coefficient_map_le embed _ 0).trans trimData.remainder_X
  enlargedDegree := trimData.enlargedDegree

theorem selected_trimmed_proper_factor_count
    (F V W : Carrier K) (first plain J bound p : ℕ) [CharP K p] (hp : p.Prime)
    [CharP (GenericField K) p] [ExpChar (GenericField K) p] [PerfectRing (GenericField K) p]
    (trimData : InvariantTrim V W first plain)
    (G : MvPolynomial (Fin 3) (GenericField K))
    (hF : Irreducible F) (hG : Irreducible G)
    (hFpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3)
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (properOriginal : ¬ F ∣ rawTrimmedTail F V W first)
    (f : Rectangle) (hy : 1 ≤ f.value) (hfirst : first+1 ≤ J) (hJ : 2 ≤ J)
    (hFcap : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hVcap : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0)
    (hWcap : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000)
    (hbound : 2 ≤ bound) (hplain : plain+1 ≤ bound) (hchar : bound < p)
    (hweight : RCN234.wt (![1,plain,0,0] : Fin 4 → ℕ) F < bound)
    (x : I ↪ K) (word : I → K) (nodes : Finset I) (agreement : ℕ)
    (hgap : plain < agreement) (hAn : agreement ≤ nodes.card)
    (haverage : nodeAverage nodes.card plain agreement ≤ 4)
    (seeds : Finset K) (selected reduced : K → Polynomial K) (scale : K → K)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) (V * implicitRegularity F) ≠ 0)
    (hdenom : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) trimData.denominator ≠ 0)
    (hGzero : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint p selected g) G = 0)
    (htrim : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) W =
      Polynomial.C (scale g) * graphSpecialize (selected g) g (g^p) V * reduced g)
    (hreduced : ∀ g ∈ seeds, (reduced g).natDegree ≤ first)
    (hselected : ∀ g ∈ seeds, (selected g).natDegree ≤ plain)
    (hagree : ∀ g ∈ seeds, agreement ≤
      (nodes.filter fun i => (selected g).eval (x i) = word i).card)
    (hinj : Set.InjOn selected ↑seeds) :
    seeds.card ≤ mixedDegree (literalRectangle G) (tailRectangle J f) (tailRectangle (J+1) f) := by
  refine selected_proper_factor_residual_count F V W first J p hp G hF hG hFpos hdiv
    properOriginal f hy hfirst hFcap hVcap hWcap seeds selected reduced scale
    hroot hreg hGzero htrim hreduced ?_
  intro C μ hμ later
  let Ω := GenericField K
  let φ := polynomialEmbedding K
  let S := rawComponentSeeds F V W first p G seeds selected C
  let P := selectedGraphPoint p selected
  let degree := actualCoordinateDegree Ω C.1
  change S.card ≤ ∑ i, (μ * rectangleCoordinate (tailRectangle (J+1) f) i) * degree i
  by_cases empty : S = ∅
  · simp [empty]
  have hS : S ⊆ seeds := Finset.filter_subset _ _
  have hpoint (g : K) (hg : g ∈ S) : C.1 ≤ RingHom.ker (MvPolynomial.aeval (P g)).toRingHom :=
    (Finset.mem_filter.mp hg).2
  obtain ⟨g₀, hg₀⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have hD : surfaceMap φ trimData.denominator ∉ C.1 := by
    intro hd
    have hzero := hpoint g₀ hg₀ hd
    change MvPolynomial.eval (polynomialGraphSurfacePoint φ (selected g₀) g₀ (g₀^p))
      (surfaceMap φ trimData.denominator) = 0 at hzero
    rw [eval_polynomialGraphSurfacePoint, polynomialEmbedding_eq_zero_iff] at hzero
    exact hdenom g₀ (hS hg₀) hzero
  have hGR : surfaceMap φ V * surfaceMap φ (implicitRegularity F) ∉ C.1 := by
    intro hm
    exact regularComponent_H_not_mem _ _ _ _ C
      ((congrArg (fun t => t ∈ C.1) (map_mul (surfaceMap φ) V (implicitRegularity F))).mpr hm)
  have hV : surfaceMap φ V ∉ C.1 := fun hm => hGR (Ideal.mul_mem_right _ _ hm)
  have hR : surfaceMap φ (implicitRegularity F) ∉ C.1 :=
    fun hm => hGR (Ideal.mul_mem_left _ _ hm)
  have hFmem : surfaceMap φ F ∈ C.1 :=
    C.1.mem_of_dvd hdiv (regularComponent_G_mem _ _ _ _ C)
  have plainTail := trimData.component_persistence C.1 hFmem hR hV hD later
  have geoProper : ¬ G ∣ surfaceMap φ (rawTrimmedTail F V W first) := by
    intro hd
    apply properOriginal
    have hdF : G ∣ geometricSurfaceMap K (GenericField K) F := by
      rw [canonical_geometricSurfaceMap]
      exact hdiv
    apply (geometric_factor_dvd_iff K (GenericField K) F _ hF hFpos G hG hdF).mp
    rw [canonical_geometricSurfaceMap]
    exact hd
  obtain ⟨base⟩ := regularComponent_exists_separating_literal p hp C hG geoProper
  have inc := persistent_curve_fixed_word_seed_bound F plain bound p f.first f.second C.1
    base (degree 1) (degree 2)
    (finite_pole_sum_le_actualCoordinateDegree p hp C.1 base 1)
    (finite_pole_sum_le_actualCoordinateDegree p hp C.1 base 2)
    hFmem hR plainTail hbound hplain hchar hweight
    (fun d hd => (MvPolynomial.monomial_le_degreeOf 2 hd).trans hFcap.2.1)
    (fun d hd => (MvPolynomial.monomial_le_degreeOf 3 hd).trans hFcap.2.2)
    x word nodes agreement hgap hAn haverage S selected (fun g => g^p)
    (fun g hg => hselected g (hS hg)) (fun g hg => hroot g (hS hg))
    (fun g hg => by
      rw [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
      exact (mul_ne_zero_iff.mp (by rw [← map_mul]; exact hreg g (hS hg))).2)
    hpoint (fun g hg => hagree g (hS hg)) (hinj.mono hS)
  exact inc.trans (persistent_curve_charge_le_tailRectangle f J μ hJ hμ degree
    (regularComponent_actualDegree_sum_pos p hp C hG geoProper))

theorem selected_trimmed_proper_carrier_count
    (F V W : Carrier K) (first plain J bound p : ℕ) [CharP K p] (hp : p.Prime)
    [CharP (GenericField K) p] [ExpChar (GenericField K) p] [PerfectRing (GenericField K) p]
    (trimData : InvariantTrim V W first plain)
    (hF : Irreducible F) (hFpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3)
    (properOriginal : ¬ F ∣ rawTrimmedTail F V W first)
    (f : Rectangle) (hy : 1 ≤ f.value) (hfirst : first+1 ≤ J) (hJ : 2 ≤ J)
    (hFcap : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hVcap : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0)
    (hWcap : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000)
    (hbound : 2 ≤ bound) (hplain : plain+1 ≤ bound) (hchar : bound < p)
    (hweight : RCN234.wt (![1,plain,0,0] : Fin 4 → ℕ) F < bound)
    (x : I ↪ K) (word : I → K) (nodes : Finset I) (agreement : ℕ)
    (hgap : plain < agreement) (hAn : agreement ≤ nodes.card)
    (haverage : nodeAverage nodes.card plain agreement ≤ 4)
    (seeds : Finset K) (selected reduced : K → Polynomial K) (scale : K → K)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0)
    (hreg : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) (V * implicitRegularity F) ≠ 0)
    (hdenom : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) trimData.denominator ≠ 0)
    (htrim : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) W =
      Polynomial.C (scale g) * graphSpecialize (selected g) g (g^p) V * reduced g)
    (hreduced : ∀ g ∈ seeds, (reduced g).natDegree ≤ first)
    (hselected : ∀ g ∈ seeds, (selected g).natDegree ≤ plain)
    (hagree : ∀ g ∈ seeds, agreement ≤
      (nodes.filter fun i => (selected g).eval (x i) = word i).card)
    (hinj : Set.InjOn selected ↑seeds) :
    seeds.card ≤ mixedDegree f (tailRectangle J f) (tailRectangle (J+1) f) := by
  refine selected_carrier_count_of_geometric_factors F hF.ne_zero p seeds selected hroot f
    (tailRectangle J f) (tailRectangle (J+1) f) hFcap ?_
  intro G hG
  obtain ⟨irr, dvd⟩ := surfaceFactors_spec (polynomialEmbedding K) F G hG
  let S := geometricFactorSeeds seeds selected p G
  have hsub : S ⊆ seeds := Finset.filter_subset _ _
  exact selected_trimmed_proper_factor_count F V W first plain J bound p hp trimData G hF irr
    hFpos dvd properOriginal f hy hfirst hJ hFcap hVcap hWcap hbound hplain hchar hweight
    x word nodes agreement hgap hAn haverage S selected reduced scale
    (fun g hg => hroot g (hsub hg)) (fun g hg => hreg g (hsub hg))
    (fun g hg => hdenom g (hsub hg)) (fun g hg => (Finset.mem_filter.mp hg).2)
    (fun g hg => htrim g (hsub hg)) (fun g hg => hreduced g (hsub hg))
    (fun g hg => hselected g (hsub hg)) (fun g hg => hagree g (hsub hg)) (hinj.mono hsub)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh


