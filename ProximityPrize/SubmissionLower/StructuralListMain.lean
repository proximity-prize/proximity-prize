import ProximityPrize.SubmissionLower.StructuralListPrice
import ProximityPrize.SubmissionLower.StructuralListIncidence
import ProximityPrize.SubmissionLower.ScalarCutCapacity

set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

namespace StructuralList

open CJ0 Polynomial PolynomialDifferential Finset
open scoped BigOperators

noncomputable section

/-- A shortened order-two chart using a prescribed set of common evaluations. -/
def ShortenChartClaim : Prop :=
  ∀ (s : Source) (_ : ShapeOK s) (G : CJ0_3.Equation) (_ : OrderTwo s G)
      (E : InitialRing 2) (_ : Irreducible E) (_ : E ∣ CJ0_3.initial G)
      (_ : ¬ E ∣ CJ0_3.initialSep G) (S : Finset Node) (_ : S.card + 3 ≤ k) (w : Node → K),
    ∃ T : Chart 2, ChartOK T ∧ T.equation = E ∧ ShortBand s (k-S.card) T ∧
      ∀ f : K[X], f.degree < k → differentialSpecialization G f = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 →
        MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0 →
        (∀ i∈S, f.eval (node i)=w i) → coeffPoint f ∈ T.imageSet

private theorem factorPrice (shorten : ShortenChartClaim)
    {A w s} (hA : AgreementOK A) (hA₅ : k + 5 ≤ A) (hs : ShapeOK s)
    (hJ : 2 * s.C + 1 ≤ s.J) {G : CJ0_3.Equation} (hG : OrderTwo s G)
    {E : InitialRing 2} (hE : Irreducible E) (hEdvd : E ∣ CJ0_3.initial G)
    (hreg : ¬ E ∣ CJ0_3.initialSep G) (V : Finset K[X])
    (hV : (V : Set K[X]) ⊆ close A w)
    (hroots : ∀ f∈V, differentialSpecialization G f = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    (V.card : ℚ) ≤ baseFactor A * slicePrice A s k E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) + 1 := by
  classical
  by_cases hv : 1 < V.card
  · let S := commonSites w V
    obtain ⟨S', hsubset, hcard⟩ := exists_subset_card_eq (min_le_left S.card (k-3))
    have hshort : S'.card + 3 ≤ k := by rw [hcard]; have := min_le_right S.card (k-3); unfold k at *; omega
    have hL : k - S'.card = shortLength S.card := by
      rw [hcard]; unfold shortLength k; omega
    obtain ⟨T, hT, heq, hband, hcovers⟩ := shorten s hs G hG E hE hEdvd hreg S' hshort w
    rw [hL] at hband
    have hcov (f : K[X]) (hf : f ∈ V) : coeffPoint f ∈ T.imageSet := by
      obtain ⟨h₁, h₂, h₃⟩ := hroots f hf
      exact hcovers f (hV hf).1 h₁ h₂ h₃ (fun i hi => mem_commonSites.mp (hsubset hi) f hf)
    have hc : S.card ≤ N := commonSites_card_le hV hv
    have hS : S.card < A := hc.trans_lt hA.gt_degree
    have hd : (0 : ℚ) < gap A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
    have hdegree := volumeDegree s hs (shortLength S.card) (le_max_left ..) T hT hband
    rw [heq] at hdegree
    let price := slicePrice A s (shortLength S.card) E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2))
    have hprice (i : Node) (hi : i ∉ S) : ((V.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ price := by
      have hmiss : ∃ f∈V, f.eval (node i) ≠ w i := by
        simpa only [S, mem_commonSites, not_forall, exists_prop] using hi
      have cut := ScalarCutCapacity.cutCap T hT hA hV hcov i hmiss
        (totalCap s (shortLength S.card)) hband.denominator.1 (fun i => (hband.numerator i).1)
      rw [heq, Nat.cast_mul] at cut
      have price_mul : (gap A : ℚ) * price =
          (errors A : ℚ) * bandVolume s (shortLength S.card) E.totalDegree
            (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) +
          (gap A : ℚ) * ((totalCap s (shortLength S.card) : ℚ) * E.totalDegree) := by
        dsimp only [price, slicePrice, curveFactor]
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
      apply le_of_mul_le_mul_left _ hd
      rw [price_mul]
      exact cut.trans (add_le_add (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg (errors A))) le_rfl)
    have hh := firstMoment hV hS.le price hprice
    have hu : (0 : ℚ) < (A - S.card : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hS)
    have hpart : (V.card : ℚ) ≤ incidenceFactor A S.card * price := by
      rw [incidenceFactor, div_mul_eq_mul_div, le_div_iff₀ hu, mul_comm (V.card : ℚ)]
      exact hh
    exact hpart.trans ((weighted_price A S.card s hs hJ hA₅ hA.lt_length.le hc ..).trans
      (le_add_of_nonneg_right zero_le_one))
  · have hc : (V.card : ℚ) ≤ 1 := by exact_mod_cast (show V.card ≤ 1 by omega)
    have hp : 0 ≤ baseFactor A * slicePrice A s k E.totalDegree
        (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) := by
      obtain ⟨ht, hi, hz⟩ := volume_nonneg s hs k (by decide)
      have hbf : 0 ≤ baseFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hcf : 0 ≤ curveFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      unfold slicePrice bandVolume
      positivity
    exact hc.trans (le_add_of_nonneg_left hp)

private theorem regularPrice (shorten : ShortenChartClaim)
    {A w s Q} (hA : AgreementOK A) (hA₅ : k + 5 ≤ A) (hs : ShapeOK s)
    (hJ : 2 * s.C + 1 ≤ s.J) (hQ : OrderTwo s Q) (T : Finset K[X])
    (hT : (T : Set K[X]) ⊆ close A w) (hreg : ∀ f∈T, RegularRoot Q f) :
    (T.card : ℚ) ≤ surfacePrice A s + s.B := by
  classical
  obtain ⟨F⟩ := CJ0_3_1.proof Q hQ.1
  let root (i : Fin F.count) (f : K[X]) := differentialSpecialization (F.source i) f = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (F.equation i) = 0 ∧
    MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep (F.source i)) ≠ 0
  let part (i : Fin F.count) := T.filter (root i)
  have hc : T.card ≤ ∑ i, (part i).card := by
    apply (card_le_card (t := univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i, hi⟩ := F.covers f (hreg f hf)
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hf, hi⟩⟩
  let b (i : Fin F.count) := (F.equation i).totalDegree
  let j (i : Fin F.count) := (F.equation i).weightedTotalDegree Fin.val
  let c (i : Fin F.count) := (F.equation i).degreeOf (Fin.last 2)
  have hp (i : Fin F.count) : ((part i).card : ℚ) ≤
      baseFactor A * slicePrice A s k (b i) (j i) (c i) + 1 :=
    factorPrice shorten hA hA₅ hs hJ (CJ0_3.orderTwo_of_dvd hQ (F.source_dvd i))
      (F.irreducible i) (F.component i) (F.regular i) (part i)
      (fun _ hf => hT (mem_filter.mp hf).1) (fun _ hf => (mem_filter.mp hf).2)
  obtain ⟨hb, hj, ht⟩ := CJ0_3.factor_weights hQ F
  have hn : F.count ≤ s.B := (CJ0_3.factor_count F).trans hb
  have hbq : (∑ i, (b i : ℚ)) ≤ s.B := by exact_mod_cast hb
  have hjq : (∑ i, (j i : ℚ)) ≤ s.J := by exact_mod_cast hj
  have hcq : (∑ i, (c i : ℚ)) ≤ s.C := by exact_mod_cast ht
  obtain ⟨hu, hv, hw⟩ := volume_nonneg s hs k (by decide)
  have hsum : (∑ i, bandVolume s k (b i) (j i) (c i)) ≤ R₂ s := by
    rw [← volume_full s hs]
    simp only [bandVolume, sum_add_distrib, ← mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbq hu)
      (mul_le_mul_of_nonneg_left hjq hv)) (mul_le_mul_of_nonneg_left hcq hw)
  have hprice : (∑ i, slicePrice A s k (b i) (j i) (c i)) ≤
      curveFactor A * R₂ s + (s.B : ℚ) * totalCap s k := by
    simp only [slicePrice, sum_add_distrib, ← mul_sum]
    rw [mul_comm (s.B : ℚ)]
    exact add_le_add (mul_le_mul_of_nonneg_left hsum (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_left hbq (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
    _ ≤ ∑ i, (baseFactor A * slicePrice A s k (b i) (j i) (c i) + 1) := sum_le_sum fun i _ => hp i
    _ = baseFactor A * (∑ i, slicePrice A s k (b i) (j i) (c i)) + F.count := by
      simp only [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprice (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Nat.cast_le.mpr hn)

/-- Use the original rank certificate with proper value sections and shortened charts. -/
theorem scalar_list_of_shortening (shorten : ShortenChartClaim)
    (A : ℕ) (s : Source) (R : ℕ) (hA : AgreementOK A) (hA₅ : k+5 ≤ A)
    (hs : ShapeOK s) (hJ : 2*s.C+1 ≤ s.J) (hw : s.m ≤ s.m*A - N*s.B)
    (hsur : Surplus A s R) (hcert : RankCertificate A s R) : ScalarList A (tariff A s) := by
  classical
  intro w
  have horig : originRank A s ≤ R := by
    rcases hcert with h | ⟨cut, hcut, htail, hp⟩
    · exact h
    · exact (CJ0_1.proof A s cut hs hw hcut htail).trans hp
  have hr := (CJ0_2.proof A s hs hw w).trans (Nat.mul_le_mul_left n horig)
  have hdim := source_dimension A s hs hw
  unfold Surplus at hsur
  have hsmall : stackRank A s w < Fintype.card (ColumnIndex A s) := by omega
  obtain ⟨Q, hQ, hwt, hloc⟩ := interpolant hs hw w hsmall
  have hroot := specializes hwt hloc
  obtain ⟨Q₁, hQ₁, hremain₁⟩ := CJ0_5.proof s hs Q hQ
  obtain ⟨F₁, hF₁, hcover₁⟩ := CJ0_6.proof s hs Q₁ hQ₁
  obtain ⟨G, hG, hGdeg, hordinary⟩ := CJ0_8.proof s hs Q₁ hQ₁
  have hfin : (close A w).Finite :=
    ReedSolomon.closePolynomialSet_finite node w (show k ≤ A from hA.gt_degree)
  let T := hfin.toFinset
  have hall (f : K[X]) (hf : f ∈ T) : f ∈ close A w := hfin.mem_toFinset.mp hf
  let T₂ := T.filter (RegularRoot Q)
  let rest := T.filter fun f => ¬ RegularRoot Q f
  let T₁ := rest.filter (RegularRoot Q₁)
  let T₀ := rest.filter fun f => ¬ RegularRoot Q₁ f
  have h₂ (f) (hf : f ∈ T₂) := hall f (mem_filter.mp hf).1
  have hrest (f) (hf : f ∈ rest) := hall f (mem_filter.mp hf).1
  have h₁ (f) (hf : f ∈ T₁) := hrest f (mem_filter.mp hf).1
  have p₂ := regularPrice shorten hA hA₅ hs hJ hQ T₂
    (fun f hf => h₂ f hf) (fun _ hf => (mem_filter.mp hf).2)
  have hprice₁ := family_capacity (fun f hf => h₁ f hf) hA (Or.inl rfl) F₁ (CJ0_7.proof s hs F₁ hF₁)
    (fun f hf => hcover₁ f (h₁ f hf).1 (mem_filter.mp hf).2)
  have hd : (0 : ℚ) < gap A := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hA.gt_degree)
  have p₁ : (T₁.card : ℚ) ≤ curveFactor A * R₁ s + H s := by
    apply le_of_mul_le_mul_left _ hd
    unfold curveFactor
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hd.ne']
    simp only [one_mul] at hprice₁
    have hcount : (F₁.count : ℚ) ≤ H s := by exact_mod_cast hF₁.count
    exact hprice₁.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount hd.le))
  have p₀ : T₀.card ≤ H s*(H s-1) := by
    refine (Polynomial.card_le_degree_of_subset_roots (p := G) ?_).trans hGdeg
    intro f hf
    obtain ⟨hr', hsing₁⟩ := mem_filter.mp (show f ∈ T₀ from hf)
    have hf' := hrest f hr'
    exact (Polynomial.mem_roots hG).mpr (hordinary f hf'.1
      (hremain₁ f hf'.1 (hroot f hf') (mem_filter.mp hr').2) hsing₁)
  have htail : ∀ h : ℕ, h+h*(h-1) = h^2 := by
    intro h
    cases h with
    | zero => rfl
    | succ h => rw [Nat.succ_sub_one]; ring
  have hp₀ : (H s : ℚ) + T₀.card ≤ (H s : ℚ)^2 := by
    exact_mod_cast (Nat.add_le_add_left p₀ (H s)).trans_eq (htail (H s))
  have hpart₂ : T₂.card + rest.card = T.card := card_filter_add_card_filter_not ..
  have hpart₁ : T₁.card + T₀.card = rest.card := card_filter_add_card_filter_not ..
  have hp : (T.card : ℚ) ≤ totalPrice A s := by
    rw [show T.card = T₂.card+T₁.card+T₀.card by omega, Nat.cast_add, Nat.cast_add]
    unfold totalPrice
    linarith only [p₂, p₁, hp₀]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact Nat.cast_le.mp (hp.trans (Nat.le_ceil _))

end

end StructuralList

#print axioms StructuralList.scalar_list_of_shortening
