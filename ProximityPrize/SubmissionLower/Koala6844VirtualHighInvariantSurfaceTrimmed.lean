import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantSurface
import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantBridge


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic RCN135 RCN136 RCN267 Koala6831OrdinaryIncidence
open scoped Classical

noncomputable section

set_option maxHeartbeats 2000000

variable {K I : Type} [Field K]

theorem persistent_trimmed_geometric_factor_bound
    (F V W : Carrier K) (first w bound p b c : ℕ) [CharP (GenericField K) p]
    (trim : InvariantTrim V W first w)
    (G : MvPolynomial (Fin 3) (GenericField K)) (hirr : Irreducible G)
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F)
    (hyp : G.degreeOf 0 < p) (hzp : G.degreeOf 2 < p)
    (whole : F ∣ rawTrimmedTail F V W first)
    (hbound : 2 ≤ bound) (hw : w+1 ≤ bound) (hchar : bound < p)
    (hweight : RCN234.wt (![1,w,0,0] : Fin 4 → ℕ) F < bound)
    (ht : ∀ d ∈ F.support, d 2 ≤ b) (hz : ∀ d ∈ F.support, d 3 ≤ c)
    (x : I ↪ K) (word : I → K) (nodes : Finset I) (A : ℕ)
    (hwA : w < A) (hAn : A ≤ nodes.card) (haverage : nodeAverage nodes.card w A ≤ 4)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hgraph : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) F = 0)
    (hG : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint p selected g) G = 0)
    (hreg : ∀ g ∈ seeds,
      graphSpecialize (selected g) g (g^p) (V * implicitRegularity F) ≠ 0)
    (hdenom : ∀ g ∈ seeds, graphSpecialize (selected g) g (g^p) trim.denominator ≠ 0)
    (hagree : ∀ g ∈ seeds, A ≤ (nodes.filter fun i => (selected g).eval (x i) = word i).card)
    (hinj : Set.InjOn selected ↑seeds) :
    seeds.card ≤ (4*(b+1+p*c)+1) * G.degreeOf 0 := by
  by_cases hs : seeds.Nonempty
  · obtain ⟨g, hg⟩ := hs
    let φ := polynomialEmbedding K
    let P := selectedGraphPoint p selected g
    have hV (s : K) (hst : s ∈ seeds) :
        graphSpecialize (selected s) s (s^p) V ≠ 0 := by
      intro hfalse
      apply hreg s hst
      rw [map_mul, hfalse, zero_mul]
    have hH (s : K) (hst : s ∈ seeds) :
        graphSpecialize (selected s) s (s^p) (implicitRegularity F) ≠ 0 := by
      intro hfalse
      apply hreg s hst
      rw [map_mul, hfalse, mul_zero]
    have hnon (Q : Carrier K) (hq : graphSpecialize (selected g) g (g^p) Q ≠ 0) :
        MvPolynomial.eval P (surfaceMap φ Q) ≠ 0 := by
      change MvPolynomial.eval (polynomialGraphSurfacePoint φ (selected g) g (g^p))
        (surfaceMap φ Q) ≠ 0
      rwa [eval_polynomialGraphSurfacePoint, ne_eq, polynomialEmbedding_eq_zero_iff]
    have avoid (Q : Carrier K) (hq : graphSpecialize (selected g) g (g^p) Q ≠ 0) :
        ¬ G ∣ surfaceMap φ Q := by
      rintro ⟨q, hqf⟩
      apply hnon Q hq
      rw [hqf, map_mul, hG g hg, zero_mul]
    have hy : 0 < G.degreeOf 0 := by
      by_contra! hzero
      have dG : MvPolynomial.pderiv 0 G = 0 :=
        pderiv_zero_of_degree_zero _ _ (Nat.eq_zero_of_le_zero hzero)
      obtain ⟨Q, hQ⟩ := hdiv
      apply hnon (implicitRegularity F) (hH g hg)
      rw [show surfaceMap φ (implicitRegularity F) = MvPolynomial.pderiv 0 (surfaceMap φ F)
        from (surfaceMap_pderiv φ F 0).symm, hQ, MvPolynomial.pderiv_mul,
        dG, zero_mul, zero_add, map_mul, hG g hg, zero_mul]
    have persist := trim.geometric_factor_persistence G hirr hdiv
      (avoid _ (hH g hg)) (avoid _ (hV g hg)) (avoid _ (hdenom g hg)) whole
    exact persistent_surface_fixed_word_seed_bound F w bound p b c G hirr hdiv hy hyp hzp persist
      hbound hw hchar hweight ht hz x word nodes A hwA hAn haverage seeds selected
      hdegree hgraph hG hH hagree hinj
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    exact Nat.zero_le _

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
