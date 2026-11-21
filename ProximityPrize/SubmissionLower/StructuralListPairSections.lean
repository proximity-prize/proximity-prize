import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.StructuralListPairDegree
import ProximityPrize.SubmissionLower.StructuralListPairRecovery

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

namespace StructuralList

open CJ0 CJ0_4 MvPolynomial PolynomialDifferential Finset
open scoped BigOperators Polynomial
open private surfaceBound valueCut valueCut_eval section_count zeroDim_count from ProximityPrize.SubmissionLower.ListProofA
open private pullback pullback_degree eval_pullback from ProximityPrize.SubmissionLower.ScalarCutCapacity
open private curve_degree_nat from ProximityPrize.SubmissionLower.Fast055

noncomputable section

def normalizedBand (s : Source) (a d e : ℕ) : Prop :=
  totalCap s k ≤ k*a ∧ indexCap s k ≤ k*d ∧ topCap s k ≤ k*e

theorem normalized_caps (s : Source) (hs : ShapeOK s) (hJ : 2*s.C+1 ≤ s.J)
    (a d e : ℕ) (hN : normalizedBand s a d e) (L : ℕ) (hL : 3 ≤ L) (hk : L ≤ k) :
    totalCap s L ≤ L*a ∧ indexCap s L ≤ L*d ∧ topCap s L ≤ L*e := by
  obtain ⟨ha, hd, he⟩ := bandCapScale s hs L hL hk hJ
  have compare (x y z : ℕ) (h : (k : ℚ) * x ≤ (L : ℚ)*y) (hz : y ≤ k*z) : x ≤ L*z := by
    have hh := h.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hz) (Nat.cast_nonneg L))
    have h' : (k : ℚ) * x ≤ (k : ℚ) * (L*z : ℕ) := by push_cast at hh ⊢; nlinarith only [hh]
    exact Nat.cast_le.mp (le_of_mul_le_mul_left h' (by positivity))
  exact ⟨compare _ _ _ ha hN.1, compare _ _ _ hd hN.2.1, compare _ _ _ he hN.2.2⟩

theorem normalized_mem (s : Source) (hs : ShapeOK s) (hJ : 2*s.C+1 ≤ s.J)
    (a d e : ℕ) (hN : normalizedBand s a d e) (L : ℕ) (hL : 3 ≤ L) (hk : L ≤ k)
    (p : InitialRing 2) (hp : InBand s L p) : p ∈ bandSpace (L*a) (L*d) (L*e) := by
  obtain ⟨ha, hd, he⟩ := normalized_caps s hs hJ a d e hN L hL hk
  exact (bandSpace_mono ha hd he) (mem_bandSpace.mpr hp)

theorem firstMomentDiv {A w} {V : Finset K[X]} (hV : (V : Set K[X]) ⊆ close A w)
    (hS : (commonSites w V).card < A) (cap : ℚ) (hcap : ∀ i ∉ commonSites w V,
      ((V.filter fun f => f.eval (node i) = w i).card : ℚ) ≤ cap) :
    (V.card : ℚ) ≤ incidenceFactor A (commonSites w V).card * cap := by
  have hpos := Nat.cast_pos (α := ℚ) |>.mpr (Nat.sub_pos_of_lt hS)
  rw [incidenceFactor, div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm (V.card : ℚ)]
  exact firstMoment hV hS.le cap hcap

theorem curveFirstMoment {A w} {V : Finset K[X]} (hA : AgreementOK A)
    (hV : (V : Set K[X]) ⊆ close A w) (hsize : 1 < V.card) (P : Ideal CoeffRing)
    (hp : P.IsPrime) (hd : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ f ∈ V, coeffPoint f ∈ zeroLocus Geo P) :
    (V.card : ℚ) ≤ incidenceFactor A (commonSites w V).card * affineDegree P := by
  apply firstMomentDiv hV ((commonSites_card_le hV hsize).trans_lt hA.gt_degree)
  intro i hi
  have hmiss : ∃ f∈V, f.eval (node i) ≠ w i := by
    simpa only [mem_commonSites, not_forall, exists_prop] using hi
  have hc := section_count hV hp hpoints (node i) (w i) hmiss (c := 1) zero_le_one
    (fun _ hU Q _ hdim hpts => by
      rw [one_mul]
      exact zeroDim_count (fun _ hf => hV (hU hf)) Q (by omega) hpts)
  simpa only [one_mul] using hc

/-- Build the shortened chart and keep track of the input of every actual polynomial solution. -/
theorem localizedChart (shorten : ShortenChartClaim) {A w s} (hs : ShapeOK s)
    {G : CJ0_3.Equation} (hG : OrderTwo s G) {E : InitialRing 2} (hE : Irreducible E)
    (hEdvd : E ∣ CJ0_3.initial G) (hreg : ¬ E ∣ CJ0_3.initialSep G)
    (V : Finset K[X]) (hV : (V : Set K[X]) ⊆ close A w)
    (hroots : ∀ f∈V, differentialSpecialization G f = 0 ∧
      eval (CJ0_3.nativeJet f) E = 0 ∧ eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0) :
    ∃ T : Chart 2, ChartOK T ∧ T.equation = E ∧ ShortBand s (shortLength (commonSites w V).card) T ∧
      ∀ f∈V, CJ0_3.nativeJet f ∈ T.locus ∧ T.output (CJ0_3.nativeJet f) = coeffPoint f := by
  classical
  let S := commonSites w V
  obtain ⟨S', hsub, hcard⟩ := exists_subset_card_eq (min_le_left S.card (k-3))
  have hshort : S'.card + 3 ≤ k := by rw [hcard]; have := min_le_right S.card (k-3); unfold k at *; omega
  have hL : k - S'.card = shortLength S.card := by rw [hcard]; unfold shortLength k; omega
  obtain ⟨T, hT, heq, hband, hcovers⟩ := shorten s hs G hG E hE hEdvd hreg S' hshort w
  rw [hL] at hband
  refine ⟨T, hT, heq, hband, fun f hf => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hroots f hf
  obtain ⟨y, hy, hyf⟩ := hcovers f (hV hf).1 h₁ h₂ h₃
    (fun i hi => mem_commonSites.mp (hsub hi) f hf)
  have hinput := input_eq_nativeJet T hT f (hV hf).1 hy hyf
  rw [hinput] at hy hyf
  exact ⟨hy, hyf⟩

/-- The value cut has the same band as the numerator and common denominator. -/
theorem pullback_band (T : Chart 2) (x b : K) (a d e : ℕ)
    (hD : T.denominator ∈ bandSpace a d e) (hN : ∀ j, T.numerator j ∈ bandSpace a d e) :
    pullback T x b ∈ bandSpace a d e := by
  unfold pullback
  simp_rw [← smul_eq_C_mul]
  apply Submodule.sub_mem
  · exact (bandSpace a d e).sum_mem (fun j _ => (bandSpace a d e).smul_mem _ (hN j))
  · exact (bandSpace a d e).smul_mem _ hD


/-- Bound a section by shortening separately on its source curves. -/
theorem pairSection (shorten : ShortenChartClaim) {A w s} (hA : AgreementOK A) (hA₅ : k+5 ≤ A)
    (hs : ShapeOK s) (hJ : 2*s.C+1 ≤ s.J) (a d e : ℕ) (hN : normalizedBand s a d e)
    (hda : d < a) (hed : 2*e < d) (he : 0 < e)
    {G : CJ0_3.Equation} (hG : OrderTwo s G) {E : InitialRing 2} (hE : Irreducible E)
    (hEdvd : E ∣ CJ0_3.initial G) (hreg : ¬ E ∣ CJ0_3.initialSep G)
    (V : Finset K[X]) (hV : (V : Set K[X]) ⊆ close A w)
    (hroots : ∀ f∈V, differentialSpecialization G f = 0 ∧
      eval (CJ0_3.nativeJet f) E = 0 ∧ eval (CJ0_3.nativeJet f) (CJ0_3.initialSep G) ≠ 0)
    (T : Chart 2) (hT : ChartOK T) (hEq : T.equation = E)
    (hband : ShortBand s (shortLength (commonSites w V).card) T)
    (halign : ∀ f∈V, CJ0_3.nativeJet f ∈ T.locus ∧ T.output (CJ0_3.nativeJet f) = coeffPoint f)
    (i : Node) (hmiss : ∃ f∈V, f.eval (node i) ≠ w i) :
    let L := shortLength (commonSites w V).card
    ((V.filter fun f => f.eval (node i) = w i).card : ℚ) ≤
      baseFactor A * k * (L * surfaceBound a d e E.totalDegree
        (E.weightedTotalDegree Fin.val : ℕ) (E.degreeOf (Fin.last 2))) + totalCap s L * E.totalDegree := by
  classical
  let L := shortLength (commonSites w V).card
  change _ ≤ baseFactor A * k * (L * surfaceBound a d e E.totalDegree
    (E.weightedTotalDegree Fin.val : ℕ) (E.degreeOf (Fin.last 2))) + totalCap s L * E.totalDegree
  let x := node i
  let y := w i
  let Q := pullback T x y
  let J := sourceIdeal T ⊔ Ideal.span {Q}
  let src := J.retainedMinimalPrimes T.denominator
  let hits := V.filter fun f => f.eval x = y
  have hz (f : K[X]) (hf : f ∈ V) : CJ0_3.nativeJet f ∈ zeroLocus Geo (sourceIdeal T) := by
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    exact (Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (halign f hf).1.1)
  have hp : (sourceIdeal T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  let := hp
  have hproper : Q ∉ sourceIdeal T := by
    obtain ⟨f, hf, hn⟩ := hmiss
    intro hQ
    have heval := hz f hf _ hQ
    change eval (CJ0_3.nativeJet f) (pullback T x y) = 0 at heval
    rw [eval_pullback T x y _ (halign f hf).1.2, (halign f hf).2] at heval
    have hcz := (mul_eq_zero.mp heval).resolve_right (halign f hf).1.2
    exact hn ((valueCut_eval (hV hf).1 x y).mp hcz)
  have hpDim : (affineHilbertPolynomial (sourceIdeal T)).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one hT.irreducible.ne_zero hp.ne_top
    rw [Nat.card_fin] at h
    exact Nat.add_right_cancel h
  have hmin (P : Ideal (InitialRing 2)) (hP : P ∈ src) : J.IsMinimalPrime P :=
    (Ideal.mem_retainedMinimalPrimes.mp hP).1
  have hDim (P : Ideal (InitialRing 2)) (hP : P ∈ src) : (affineHilbertPolynomial P).natDegree = 1 := by
    have h := principalCut_natDegree_affineHilbertPolynomial_add_one hproper (hmin P hP)
    omega
  have srcCount : (src.card : ℚ) ≤ (totalCap s L : ℚ) * E.totalDegree := by
    have hs₀ := principalCut_sum_affineDegree_minimalPrimes_le hproper
      (pullback_degree T x y (totalCap s L) hband.denominator.1 (fun j => (hband.numerator j).1))
    rw [show affineDegree (sourceIdeal T) = (T.equation.totalDegree : ℚ) from
      affineDegree_span_singleton hT.irreducible.ne_zero, hEq] at hs₀
    calc
      _ = ∑ P ∈ src, (1 : ℚ) := by simp
      _ ≤ ∑ P ∈ src, affineDegree P := by
        apply sum_le_sum
        intro P hP
        obtain ⟨z, hz, hr⟩ := curve_degree_nat P (hmin P hP).isPrime (hDim P hP)
        rw [hr]
        exact_mod_cast hz
      _ ≤ ∑ P ∈ J.minimalPrimesFinset, affineDegree P :=
        sum_le_sum_of_subset_of_nonneg (Ideal.retainedMinimalPrimes_subset _ _)
          (fun P _ _ => affineDegree_nonneg P)
      _ ≤ _ := hs₀
  let part (P : Ideal (InitialRing 2)) := hits.filter fun f => CJ0_3.nativeJet f ∈ zeroLocus Geo P
  have hc : hits.card ≤ ∑ P ∈ src, (part P).card := by
    apply (card_le_card (t := src.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨hfV, hfA⟩ := mem_filter.mp hf
    have hzQ : eval (CJ0_3.nativeJet f) Q = 0 := by
      unfold Q
      rw [eval_pullback T x y _ (halign f hfV).1.2, (halign f hfV).2]
      have hv : eval (coeffPoint f) (valueCut x y) = 0 := (valueCut_eval (hV hfV).1 x y).mpr hfA
      rw [hv, zero_mul]
    have hzJ : CJ0_3.nativeJet f ∈ zeroLocus Geo J :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hz f hfV, hzQ⟩
    obtain ⟨P, hP, hzP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J T.denominator _ hzJ (halign f hfV).1.2
    exact mem_biUnion.mpr ⟨P, hP, mem_filter.mpr ⟨hf, hzP⟩⟩
  let large := src.filter fun P => 1 < (part P).card
  let small := src.filter fun P => ¬ 1 < (part P).card
  have htot : (hits.card : ℚ) ≤ ∑ P ∈ large, ((part P).card : ℚ) + src.card := by
    have hcq : (hits.card : ℚ) ≤ ∑ P ∈ src, ((part P).card : ℚ) := by exact_mod_cast hc
    rw [← sum_filter_add_sum_filter_not _ (fun P => 1 < (part P).card)] at hcq
    refine hcq.trans (add_le_add le_rfl ?_)
    calc
      _ ≤ ∑ P ∈ small, (1 : ℚ) := by
        apply sum_le_sum
        intro P hP
        exact_mod_cast Nat.le_of_not_gt (mem_filter.mp hP).2
      _ = (small.card : ℚ) := by simp
      _ ≤ src.card := Nat.cast_le.mpr (card_le_card (filter_subset _ _))
  let I := {P // P ∈ large}
  let P (j : I) := j.val
  have hsrc (j : I) : P j ∈ src := (mem_filter.mp j.property).1
  have hsize (j : I) : 1 < (part (P j)).card := (mem_filter.mp j.property).2
  have hsub (j : I) : (part (P j) : Set K[X]) ⊆ close A w :=
    fun f hf => hV (mem_filter.mp (mem_filter.mp hf).1).1
  have hOld (j : I) : sourceIdeal T ≤ P j := le_sup_left.trans (hmin (P j) (hsrc j)).le
  have hIsPrime (j : I) : (P j).IsPrime := (hmin (P j) (hsrc j)).isPrime
  have hPQ (j : I) : Q ∈ P j := (hmin (P j) (hsrc j)).le
    ((show Ideal.span {Q} ≤ J from le_sup_right) (Ideal.mem_span_singleton_self Q))
  have hAnti (j l : I) (hj : j ≠ l) : ¬ P l ≤ P j := by
    intro hle
    have hrev : P j ≤ P l := (hmin (P j) (hsrc j)).2 (hmin (P l) (hsrc l)).1 hle
    exact hj (Subtype.ext (le_antisymm hrev hle))
  choose U hU hUeq hUband hUpoint using fun j : I => localizedChart shorten hs hG hE hEdvd hreg (part (P j)) (hsub j)
    (fun f hf => hroots f (mem_filter.mp (mem_filter.mp hf).1).1)
  let length (j : I) := shortLength (commonSites w (part (P j))).card
  have hLen (j : I) : 3 ≤ length j := le_max_left ..
  have hMax (j : I) : length j ≤ k := max_le (by decide) (Nat.sub_le ..)
  have hD (j : I) : (U j).denominator ∉ P j := by
    have hn : 0 < (part (P j)).card := Nat.zero_lt_one.trans (hsize j)
    obtain ⟨f, hf⟩ := card_pos.mp hn
    exact fun h => (hUpoint j f hf).1.2 ((mem_filter.mp hf).2 _ h)
  have hsrcU (j : I) : sourceIdeal (U j) ≤ P j := by
    simpa only [sourceIdeal, hUeq j, hEq] using hOld j
  have hUDim (j : I) : (affineHilbertPolynomial (componentIdeal (U j) (P j))).natDegree = 1 :=
    (componentDimension (U j) (hU j) (P j) (hIsPrime j) (hsrcU j) (hD j)).trans (hDim (P j) (hsrc j))
  have hMoment (j : I) : ((part (P j)).card : ℚ) ≤ baseFactor A * k *
      (affineDegree (componentIdeal (U j) (P j)) / (length j : ℚ)) := by
    have ht (f : K[X]) (hf : f ∈ part (P j)) : coeffPoint f ∈ zeroLocus Geo (componentIdeal (U j) (P j)) := by
      rw [← (hUpoint j f hf).2]
      exact componentOutput_mem (U j) (P j) _ (mem_filter.mp hf).2 (hUpoint j f hf).1.2
    have h := curveFirstMoment hA (hsub j) (hsize j) _
      (componentGeometry (U j) (P j) (hIsPrime j) (hD j)).1 (hUDim j) ht
    refine h.trans ?_
    have hscl := incidenceLength A (commonSites w (part (P j))).card hA₅ hA.lt_length.le
      (commonSites_card_le (hsub j) (hsize j))
    have hlq : (0 : ℚ) < length j := Nat.cast_pos.mpr (by have := hLen j; omega)
    rw [← mul_div_assoc, le_div_iff₀ hlq]
    have hdeg := affineDegree_nonneg (componentIdeal (U j) (P j))
    nlinarith only [mul_le_mul_of_nonneg_right hscl hdeg]
  have hL : 3 ≤ L := le_max_left ..
  have hLk : L ≤ k := max_le (by decide) (Nat.sub_le ..)
  have hnormT (q : InitialRing 2) (hq : InBand s L q) : q ∈ bandSpace (L*a) (L*d) (L*e) :=
    normalized_mem s hs hJ a d e hN L hL hLk q hq
  have hQ : Q ∈ bandSpace (L*a) (L*d) (L*e) :=
    pullback_band T x y _ _ _ (hnormT _ hband.denominator) (fun j => hnormT _ (hband.numerator j))
  have hnorm (j : I) (q : InitialRing 2) (hq : InBand s (length j) q) :=
    normalized_mem s hs hJ a d e hN (length j) (hLen j) (hMax j) q hq
  have hVolume := jointImageDegrees T hT Q hproper a d e L hda hed he hQ P hIsPrime hOld hPQ hAnti
    U length (fun j => by have := hLen j; omega)
    (fun j => hnorm j _ (hUband j).denominator)
    (fun j l => hnorm j _ ((hUband j).numerator l)) hUDim
  rw [hEq] at hVolume
  have hbase : 0 ≤ baseFactor A * k := mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ P ∈ large, ((part P).card : ℚ) + src.card := htot
    _ = (∑ j : I, ((part (P j)).card : ℚ)) + src.card := by
      rw [Finset.univ_eq_attach]
      congr 1
      exact (Finset.sum_attach large (fun P => ((part P).card : ℚ))).symm
    _ ≤ (∑ j : I, baseFactor A*k*(affineDegree (componentIdeal (U j) (P j)) / (length j : ℚ))) + src.card :=
      add_le_add (sum_le_sum fun j _ => hMoment j) le_rfl
    _ ≤ _ := by
      rw [← mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left hVolume hbase) srcCount

end

end StructuralList
