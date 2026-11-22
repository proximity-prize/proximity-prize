import ProximityPrize.SubmissionLower.Peer653High53FamilyCurveTariff

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
noncomputable section
open Polynomial Finset MvPolynomial ProximityPrize.Benchmark
open scoped BigOperators
open Peer653High53 (K I node agreement blockLength)
open K1_14 (FX)
open K1_14_6 (Biform ClosedField rootPoint)
open P1_7_7 (point slice slice_subset slice_on point_injective boxMap BoxRing
  localOrd localSeed ShortCharts WeightedCut CurveScale)
open private zero_dim_count common common_agrees from ProximityPrize.SubmissionLower.UpperBranch7
open private card_le_sum_cover from ProximityPrize.SubmissionLower.Fast055
open private eval_extend extend_mem from ProximityPrize.SubmissionLower.Fast055
private theorem common_bound {word T S d} (hword : FixedWord word T S d)
    {U : Finset K} (hU : U ⊆ T) (hsize : 1 < U.card) :
    (common word U S).card ≤ d := by
  obtain ⟨γ, hγ, η, hη, hne⟩ := one_lt_card.mp hsize
  let P := S γ - S η
  have hp : P ≠ 0 := sub_ne_zero.mpr fun he => hne (hword.distinct (hU hγ) (hU hη) he)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
    P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (hword.degree γ (hU hγ))
      (hword.degree η (hU hη))))
  intro j hj
  change ((S γ) - (S η)).eval (node j) = 0
  rw [Polynomial.eval_sub, common_agrees hγ hj, common_agrees hη hj, sub_self]
private theorem residual_incidence {word T S d} (hword : FixedWord word T S d)
    {U : Finset K} (hU : U ⊆ T) (cap : ℚ)
    (hcap : ∀ j ∉ common word U S, ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ) ≤ cap) :
    ((agreement - (common word U S).card : ℕ) : ℚ) * U.card ≤
      ((blockLength - (common word U S).card : ℕ) : ℚ) * cap := by
  classical
  let sites := common word U S
  let J : Finset I := univ \ sites
  let rel (γ : K) (j : I) := (S γ).eval (node j) = word j
  have hJ : J.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  have hrows (γ : K) (hγ : γ ∈ U) :
      ((agreement - sites.card : ℕ) : ℚ) ≤ (J.bipartiteAbove rel γ).card := by
    obtain ⟨H, hH, heval⟩ := hword.hits γ (hU hγ)
    have hcover : H \ sites ⊆ J.bipartiteAbove rel γ := fun j hj =>
      mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hj).2⟩, heval j (mem_sdiff.mp hj).1⟩
    exact_mod_cast (Nat.sub_le_sub_right hH sites.card).trans
      ((le_card_sdiff _ _).trans (card_le_card hcover))
  have hcols (j : I) (hj : j ∈ J) :
      ((U.bipartiteBelow rel j).card : ℚ) ≤ cap := hcap j (mem_sdiff.mp hj).2
  have he := card_nsmul_le_card_nsmul rel hrows hcols
  rw [nsmul_eq_mul, nsmul_eq_mul, hJ, mul_comm (U.card : ℚ)] at he
  exact he
structure Invoice (d w e v a b D : ℕ) : Prop where
  scale_pos : 0 < D
  ordinate : D ≤ a
  seed : D ≤ b
  degree : d < agreement
  fits : ∀ s ≤ d, D * (blockLength-s) * localOrd d w e s ≤ (agreement-s) * a ∧
    D * (blockLength-s) * localSeed d w v s ≤ (agreement-s) * b
private theorem count_step {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut : WeightedCut) {word T z S} (hword : FixedWord word T S d)
    (hchart : ShortCharts d w e v word T z S)
    {U : Finset K} (hU : U ⊆ T) (hsize : 1 < U.card) (P : Ideal (BoxRing a b))
    (hP : P.IsPrime) (hbase : RingHom.ker (boxMap a b) ≤ P)
    (hdim : 0 < (affineHilbertPolynomial P).natDegree)
    (hpoints : ∀ γ ∈ U, point a b z S γ ∈ zeroLocus ClosedField P)
    {c : ℚ} (hc : 0 < c)
    (hchildren : ∀ (V : Finset K), V ⊆ U → ∀ (Q : Ideal (BoxRing a b)), Q.IsPrime →
      RingHom.ker (boxMap a b) ≤ Q →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, point a b z S γ ∈ zeroLocus ClosedField Q) →
      c * V.card ≤ affineDegree Q) :
    (D : ℚ) * c * U.card ≤ affineDegree P := by
  classical
  let sites := common word U S
  let s := sites.card
  let r := D * (blockLength-s)
  let t := agreement-s
  have hs : s ≤ d := common_bound hword hU hsize
  have ht : 0 < t := Nat.sub_pos_of_lt (hs.trans_lt hInv.degree)
  have hn : 0 < blockLength-s :=
    Nat.sub_pos_of_lt (hs.trans_lt (hInv.degree.trans (by decide)))
  have hr : 0 < r := Nat.mul_pos hInv.scale_pos hn
  have ha := hInv.scale_pos.trans_le hInv.ordinate
  have hb := hInv.scale_pos.trans_le hInv.seed
  let : P.IsPrime := hP
  obtain ⟨cut, hcut_box, hcut_eval⟩ := hchart U hU sites hs
    (fun _ hγ _ hj => common_agrees hγ hj)
  let ι := algebraMap FX ClosedField
  have hsection (j : I) (hj : j ∉ sites) :
      (r : ℚ) * (c * ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ)) ≤
        (t : ℚ) * affineDegree P := by
    let V := U.filter fun γ => (S γ).eval (node j) = word j
    obtain ⟨q, hq⟩ := bidegreeMap_surjective (R := ClosedField) ha hb (MvPolynomial.map ι (cut j))
    have heval (γ : K) (hγ : γ ∈ U) :
        aeval (point a b z S γ) q = 0 ↔ (S γ).eval (node j) = word j := by
      rw [point, aeval_monomialPoint, ← bidegreeMap_eq_monomialMap, hq]
      change MvPolynomial.eval (ι ∘ rootPoint (z γ) (S γ)) (MvPolynomial.map ι (cut j)) = 0 ↔ _
      rw [eval_extend, ← map_zero ι, ι.injective.eq_iff]
      exact hcut_eval γ hγ j
    have hproper : q ∉ P := by
      intro hqP
      apply hj
      exact mem_filter.mpr ⟨mem_univ _, fun γ hγ => (heval γ hγ).mp (hpoints γ hγ q hqP)⟩
    let Qs := (P ⊔ Ideal.span {q}).minimalPrimesFinset
    have hdeg : (r : ℚ) * (∑ Q ∈ Qs, affineDegree Q) ≤ (t : ℚ) * affineDegree P :=
      hcut a b _ _ r t ha hb hr ht (hInv.fits s hs).1 (hInv.fits s hs).2
        P hP hbase hdim q hproper (by rw [hq]; exact extend_mem (hcut_box j))
    have hcover : V.card ≤ ∑ Q ∈ Qs, (slice z S V Q).card := by
      apply card_le_sum_cover
      intro γ hγ
      obtain ⟨hγU, hv⟩ := mem_filter.mp hγ
      have hγP : point a b z S γ ∈ zeroLocus ClosedField (P ⊔ Ideal.span {q}) :=
        mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoints γ hγU, (heval γ hγU).mpr hv⟩
      obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hγP (by simp)
      exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
        mem_filter.mpr ⟨hγ, hγQ⟩⟩
    have hparts (Q : Ideal (BoxRing a b)) (hQ : Q ∈ Qs) :
        c * ((slice z S V Q).card : ℚ) ≤ affineDegree Q := by
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact hchildren _ ((slice_subset Q).trans (filter_subset _ _)) Q hmin.isPrime
        (hbase.trans (le_sup_left.trans hmin.le))
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => slice_on Q hγ)
    have hcoverQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((slice z S V Q).card : ℚ) := by
      exact_mod_cast hcover
    have hsum : c * (V.card : ℚ) ≤ ∑ Q ∈ Qs, affineDegree Q := by
      refine (mul_le_mul_of_nonneg_left hcoverQ hc.le).trans ?_
      rw [mul_sum]
      exact sum_le_sum hparts
    exact (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r)).trans hdeg
  let cap : ℚ := (t : ℚ) * affineDegree P / ((r : ℚ) * c)
  have hrc : 0 < (r : ℚ) * c := mul_pos (Nat.cast_pos.mpr hr) hc
  have hinc := residual_incidence hword hU cap (fun j hj => by
    apply (le_div_iff₀ hrc).mpr
    calc
      _ = (r : ℚ) * (c * ((U.filter fun γ => (S γ).eval (node j) = word j).card : ℚ)) := by ring
      _ ≤ _ := hsection j hj)
  change (t : ℚ) * U.card ≤ ((blockLength-s : ℕ) : ℚ) * cap at hinc
  have hnQ : (0 : ℚ) < ((blockLength-s : ℕ) : ℚ) := Nat.cast_pos.mpr hn
  have htQ : (0 : ℚ) < (t : ℚ) := Nat.cast_pos.mpr ht
  apply le_of_mul_le_mul_left _ (mul_pos hnQ htQ)
  calc
    _ = ((r : ℚ) * c) * ((t : ℚ) * U.card) := by simp only [r, Nat.cast_mul]; ring
    _ ≤ ((r : ℚ) * c) * (((blockLength-s : ℕ) : ℚ) * cap) :=
      mul_le_mul_of_nonneg_left hinc hrc.le
    _ = _ := by dsimp only [cap]; field_simp [hrc.ne']
theorem count_cover {d w e v a b D : ℕ} (hInv : Invoice d w e v a b D)
    (hcut : WeightedCut) (hscale : CurveScale) {word T z S} (hword : FixedWord word T S d)
    (hchart : ShortCharts d w e v word T z S) (hz : Set.InjOn z (T : Set K))
    (Ps : Finset (Ideal (BoxRing a b)))
    (hPs : ∀ P ∈ Ps, P.IsPrime ∧ RingHom.ker (boxMap a b) ≤ P ∧
      (affineHilbertPolynomial P).natDegree = 2)
    (hcover : ∀ γ ∈ T, ∃ P ∈ Ps, point a b z S γ ∈ zeroLocus ClosedField P) :
    (D : ℚ)^2 * T.card ≤ (∑ P ∈ Ps, affineDegree P) + (D : ℚ)^2 * Ps.card := by
  classical
  have hinj := point_injective (hInv.scale_pos.trans_le hInv.ordinate)
    (hInv.scale_pos.trans_le hInv.seed) (S := S) hz
  have curve {U : Finset K} (hU : U ⊆ T) (P : Ideal (BoxRing a b))
      (hP : P.IsPrime) (hbase : RingHom.ker (boxMap a b) ≤ P)
      (hdim : (affineHilbertPolynomial P).natDegree = 1)
      (hpoints : ∀ γ ∈ U, point a b z S γ ∈ zeroLocus ClosedField P) :
      (D : ℚ) * U.card ≤ affineDegree P := by
    by_cases hsize : 1 < U.card
    · simpa only [mul_one] using
        count_step hInv hcut hword hchart hU hsize P hP hbase (by omega) hpoints
          (by norm_num : (0 : ℚ) < 1) (fun V hv Q _ _ hdimQ hpointQ => by
            rw [one_mul]
            exact zero_dim_count (hv.trans hU) hinj Q (by omega) hpointQ)
    · have hu : (U.card : ℚ) ≤ 1 := by exact_mod_cast (show U.card ≤ 1 by omega)
      calc
        _ ≤ (D : ℚ) * 1 := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg D)
        _ ≤ affineDegree P := by
          rw [mul_one]
          exact hscale a b D hInv.scale_pos hInv.ordinate hInv.seed P hP hbase hdim
  have surface (P : Ideal (BoxRing a b)) (hP : P ∈ Ps) :
      (D : ℚ)^2 * ((slice z S T P).card : ℚ) ≤ affineDegree P + (D : ℚ)^2 := by
    obtain ⟨hp, hk, hd⟩ := hPs P hP
    by_cases hsize : 1 < (slice z S T P).card
    · rw [pow_two]
      exact (count_step hInv hcut hword hchart (slice_subset P) hsize P hp hk (by omega)
        (fun _ hγ => slice_on P hγ) (Nat.cast_pos.mpr hInv.scale_pos)
        (fun V hv Q hQ hQk hQd hQV => curve (hv.trans (slice_subset P)) Q hQ hQk (by omega) hQV)).trans
          (le_add_of_nonneg_right (by positivity))
    · have hu : ((slice z S T P).card : ℚ) ≤ 1 := by
        exact_mod_cast (show (slice z S T P).card ≤ 1 by omega)
      calc
        _ ≤ (D : ℚ)^2 * 1 := mul_le_mul_of_nonneg_left hu (by positivity)
        _ ≤ _ := by rw [mul_one]; exact le_add_of_nonneg_left (affineDegree_nonneg P)
  have hsum : T.card ≤ ∑ P ∈ Ps, (slice z S T P).card := by
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨P, hP, hγP⟩ := hcover γ hγ
    exact ⟨P, hP, mem_filter.mpr ⟨hγ, hγP⟩⟩
  have hsumQ : (T.card : ℚ) ≤ ∑ P ∈ Ps, ((slice z S T P).card : ℚ) := by exact_mod_cast hsum
  calc
    _ ≤ (D : ℚ)^2 * ∑ P ∈ Ps, ((slice z S T P).card : ℚ) :=
      mul_le_mul_of_nonneg_left hsumQ (by positivity)
    _ ≤ ∑ P ∈ Ps, (affineDegree P + (D : ℚ)^2) := by
      rw [mul_sum]
      exact sum_le_sum surface
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm (Ps.card : ℚ)]
end
end Peer653High53
end
