import ProximityPrize.SubmissionLower.StructuralListPairSections

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

namespace StructuralList

open CJ0 Finset Polynomial PolynomialDifferential
open scoped BigOperators
open private surfaceBound from ProximityPrize.SubmissionLower.ListProofA

noncomputable section

private def volumeA (d e : ℕ) : ℚ := 2 * (e : ℚ) * ((d : ℚ)-e)
private def volumeD (a d e : ℕ) : ℚ := (e : ℚ) * (2*(a : ℚ)-2*d+e)
private def volumeE (a d e : ℕ) : ℚ := ((d : ℚ)-2*e) * (2*(a : ℚ)-d)

def pairVolume (a d e b j c : ℕ) : ℚ :=
  volumeA d e * b + volumeD a d e * j + volumeE a d e * c

private theorem pairVolume_eq (a d e b j c : ℕ) : pairVolume a d e b j c = surfaceBound a d e b j c := rfl

private theorem weights_nonneg (a d e : ℕ) (hda : d ≤ a) (hed : 2*e ≤ d) :
    0 ≤ volumeA d e ∧ 0 ≤ volumeD a d e ∧ 0 ≤ volumeE a d e := by
  have ha : (d : ℚ) ≤ a := by exact_mod_cast hda
  have hd : (2 : ℚ) * e ≤ d := by exact_mod_cast hed
  have h₀ : (0 : ℚ) ≤ e := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (by linarith)
  · exact mul_nonneg h₀ (by linarith)
  · exact mul_nonneg (by linarith) (by linarith)

def pairPrice (A : ℕ) (s : Source) (a d e b j c : ℕ) : ℚ :=
  (baseFactor A * k)^2 * pairVolume a d e b j c + baseFactor A * totalCap s k * b

def pairTotalPrice (A : ℕ) (s : Source) (a d e : ℕ) : ℚ :=
  pairPrice A s a d e s.B s.J s.C + curveFactor A * R₁ s + s.B + (H s : ℚ)^2

def pairTariff (A : ℕ) (s : Source) (a d e : ℕ) : ℕ := ⌈pairTotalPrice A s a d e⌉₊

private theorem pairFactorPrice (shorten : ShortenChartClaim) {A w s} (hA : AgreementOK A)
    (hA₅ : k+5 ≤ A) (hs : ShapeOK s) (hJ : 2*s.C+1 ≤ s.J)
    (a d e : ℕ) (hN : normalizedBand s a d e) (hda : d < a) (hed : 2*e < d) (he : 0 < e)
    {G : CJ0_3.Equation} (hG : OrderTwo s G) {E : InitialRing 2} (hE : Irreducible E)
    (hEdvd : E ∣ CJ0_3.initial G) (hreg : ¬ E ∣ CJ0_3.initialSep G) (V : Finset K[X])
    (hV : (V : Set K[X]) ⊆ close A w)
    (hroots : ∀ f∈V, differentialSpecialization G f = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) E = 0 ∧
      MvPolynomial.eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    (V.card : ℚ) ≤ pairPrice A s a d e E.totalDegree
      (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) + 1 := by
  classical
  obtain ⟨ha, hd, he₀⟩ := weights_nonneg a d e hda.le hed.le
  have hBase : 0 ≤ baseFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  by_cases hsize : 1 < V.card
  · obtain ⟨T, hT, hEq, hBand, hAlign⟩ := localizedChart shorten hs hG hE hEdvd hreg V hV hroots
    let common := (commonSites w V).card
    let length := shortLength common
    let mass := pairVolume a d e E.totalDegree (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2))
    have hmass : 0 ≤ mass := by dsimp only [mass, pairVolume]; positivity
    let cap := baseFactor A*k*(length*mass) + (totalCap s length : ℚ)*E.totalDegree
    have hS : common ≤ N := commonSites_card_le hV hsize
    have hHit : (V.card : ℚ) ≤ incidenceFactor A common * cap := by
      refine firstMomentDiv hV (hS.trans_lt hA.gt_degree) cap ?_
      intro i hi
      have hmiss : ∃ f∈V, f.eval (node i) ≠ w i := by
        simpa only [mem_commonSites, not_forall, exists_prop] using hi
      simpa only [cap, mass, pairVolume_eq] using pairSection shorten hA hA₅ hs hJ a d e hN hda hed he
        hG hE hEdvd hreg V hV hroots T hT hEq hBand hAlign i hmiss
    have hscale := incidenceLength A common hA₅ hA.lt_length.le hS
    have hvol := mul_le_mul_of_nonneg_right hscale (mul_nonneg (mul_nonneg hBase (Nat.cast_nonneg (α := ℚ) k)) hmass)
    have hCap := (bandCapScale s hs length (le_max_left ..) (max_le (by decide) (Nat.sub_le ..)) hJ).1
    have hα : 0 ≤ incidenceFactor A common := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h₁ := mul_le_mul_of_nonneg_left hCap hα
    have h₂ := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg (α := ℚ) (totalCap s k))
    have hsmall : incidenceFactor A common * totalCap s length ≤ baseFactor A * totalCap s k := by
      have h₃ : (k : ℚ) * (incidenceFactor A common * totalCap s length) ≤
          (k : ℚ) * (baseFactor A * totalCap s k) := by nlinarith only [h₁, h₂]
      exact le_of_mul_le_mul_left h₃ (by positivity)
    have hfee := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg (α := ℚ) E.totalDegree)
    refine hHit.trans (le_trans ?_ (le_add_of_nonneg_right zero_le_one))
    change incidenceFactor A common * cap ≤ (baseFactor A*k)^2 * mass + baseFactor A * totalCap s k * E.totalDegree
    dsimp only [cap]
    nlinarith only [hvol, hfee]
  · have hv : (V.card : ℚ) ≤ 1 := by exact_mod_cast (show V.card ≤ 1 by omega)
    have hp : 0 ≤ pairPrice A s a d e E.totalDegree (E.weightedTotalDegree Fin.val) (E.degreeOf (Fin.last 2)) := by
      unfold pairPrice pairVolume
      positivity
    exact hv.trans (le_add_of_nonneg_left hp)

private theorem pairRegularPrice (shorten : ShortenChartClaim)
    {A w s Q} (hA : AgreementOK A) (hA₅ : k + 5 ≤ A) (hs : ShapeOK s)
    (hJ : 2 * s.C + 1 ≤ s.J) (a d e : ℕ) (hN : normalizedBand s a d e)
    (hda : d < a) (hed : 2*e < d) (he : 0 < e) (hQ : OrderTwo s Q) (T : Finset K[X])
    (hT : (T : Set K[X]) ⊆ close A w) (hreg : ∀ f∈T, RegularRoot Q f) :
    (T.card : ℚ) ≤ pairPrice A s a d e s.B s.J s.C + s.B := by
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
      pairPrice A s a d e (b i) (j i) (c i) + 1 :=
    pairFactorPrice shorten hA hA₅ hs hJ a d e hN hda hed he (CJ0_3.orderTwo_of_dvd hQ (F.source_dvd i))
      (F.irreducible i) (F.component i) (F.regular i) (part i)
      (fun _ hf => hT (mem_filter.mp hf).1) (fun _ hf => (mem_filter.mp hf).2)
  obtain ⟨hb, hj, ht⟩ := CJ0_3.factor_weights hQ F
  have hn : F.count ≤ s.B := (CJ0_3.factor_count F).trans hb
  have hbq : (∑ i, (b i : ℚ)) ≤ s.B := by exact_mod_cast hb
  have hjq : (∑ i, (j i : ℚ)) ≤ s.J := by exact_mod_cast hj
  have hcq : (∑ i, (c i : ℚ)) ≤ s.C := by exact_mod_cast ht
  obtain ⟨hu, hv, hw⟩ := weights_nonneg a d e hda.le hed.le
  have hsum : (∑ i, pairVolume a d e (b i) (j i) (c i)) ≤ pairVolume a d e s.B s.J s.C := by
    simp only [pairVolume, sum_add_distrib, ← mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hbq hu)
      (mul_le_mul_of_nonneg_left hjq hv)) (mul_le_mul_of_nonneg_left hcq hw)
  have hprice : (∑ i, pairPrice A s a d e (b i) (j i) (c i)) ≤ pairPrice A s a d e s.B s.J s.C := by
    simp only [pairPrice, sum_add_distrib, ← mul_sum]
    have hBase : 0 ≤ baseFactor A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact add_le_add (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hbq (mul_nonneg hBase (Nat.cast_nonneg _)))
  calc
    _ ≤ ∑ i, ((part i).card : ℚ) := by exact_mod_cast hc
    _ ≤ ∑ i, (pairPrice A s a d e (b i) (j i) (c i) + 1) := sum_le_sum fun i _ => hp i
    _ = (∑ i, pairPrice A s a d e (b i) (j i) (c i)) + F.count := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin]
    _ ≤ _ := add_le_add hprice (Nat.cast_le.mpr hn)

/-- Apply two shortenings with the original rank certificate. -/
theorem scalar_list_of_pair_shortening (shorten : ShortenChartClaim)
    (A : ℕ) (s : Source) (R : ℕ) (hA : AgreementOK A) (hA₅ : k+5 ≤ A)
    (hs : ShapeOK s) (hJ : 2*s.C+1 ≤ s.J) (a d e : ℕ) (hN : normalizedBand s a d e)
    (hda : d < a) (hed : 2*e < d) (he : 0 < e) (hw : s.m ≤ s.m*A - N*s.B)
    (hsur : Surplus A s R) (hcert : RankCertificate A s R) : ScalarList A (pairTariff A s a d e) := by
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
  have p₂ := pairRegularPrice shorten hA hA₅ hs hJ a d e hN hda hed he hQ T₂
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
  have hp : (T.card : ℚ) ≤ pairTotalPrice A s a d e := by
    rw [show T.card = T₂.card+T₁.card+T₀.card by omega, Nat.cast_add, Nat.cast_add]
    unfold pairTotalPrice
    linarith only [p₂, p₁, hp₀]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact Nat.cast_le.mp (hp.trans (Nat.le_ceil _))


end

end StructuralList

#print axioms StructuralList.scalar_list_of_pair_shortening
