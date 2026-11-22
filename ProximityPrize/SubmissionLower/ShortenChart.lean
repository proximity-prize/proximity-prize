import ProximityPrize.SubmissionLower.ShortenChartJet
import ProximityPrize.SubmissionLower.StructuralListDefs

set_option Elab.async false
set_option maxRecDepth 8000
namespace ShortenChart
noncomputable section
open CJ0 CJ0_3 PolynomialDifferential MvPolynomial
open StructuralList (ShortBand InBand exponent totalCap indexCap topCap)
open scoped Polynomial BigOperators
open private lifted_total lifted_top lifted_weight indexWeight_eq coeffWeight_eq totalWeight_eq
  degreeOf_top_of_index readJet_eq from ProximityPrize.SubmissionLower.ListProofA
open private commonTaylor_top from ProximityPrize.SubmissionLower.ListProofA

private theorem exponent_sufficient (length : ℕ) :
    TaylorExponentSufficient 2 length (exponent length) := by
  intro l
  have hl := l.isLt
  unfold exponent
  omega

private theorem top_monotone : Monotone (Pi.single (Fin.last 2) (1 : ℕ)) := by
  intro i j hij
  by_cases hi : i = Fin.last 2
  · have hj : j = Fin.last 2 := le_antisymm (Fin.le_last j) (hi ▸ hij)
    rw [hi, hj]
  · have hi₂ : i ≠ (2 : Fin 3) := hi
    have hw : (Pi.single (Fin.last 2) (1 : ℕ) : Fin 3 → ℕ) i = 0 := by simp [hi₂]
    rw [hw]
    exact Nat.zero_le _

private theorem lift_total {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : K[X]) :
    jetTotalDegree (lifted (transform g L G)) ≤ s.B := by
  rw [lifted_total]
  have h := transform_weight g L G 1 (fun _ _ _ => le_rfl)
  rw [totalWeight_eq] at h
  exact h.trans hG.2.1

private theorem lift_index {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : K[X]) :
    (lifted (transform g L G)).weightedTotalDegree (Astra7.jetWeight 0 1 3) ≤ s.J := by
  rw [lifted_weight, indexWeight_eq]
  exact (transform_weight g L G Fin.val (fun _ _ h => h)).trans hG.2.2.1

private theorem lift_top {s : Source} {G : Equation} (hG : OrderTwo s G) (g L : K[X]) :
    (lifted (transform g L G)).degreeOf (some (Fin.last 2)) ≤ s.C := by
  change jetDegree (lifted (transform g L G)) (Fin.last 2) ≤ s.C
  rw [lifted_top]
  have hw := transform_weight g L G (Pi.single (Fin.last 2) 1) top_monotone
  have he : (fun v : Option (Fin 3) => v.elim 0 (Pi.single (Fin.last 2) 1)) =
      Pi.single (some (Fin.last 2)) (1 : ℕ) := by
    funext v
    cases v <;> simp [Pi.single_apply]
  rw [he, weightedTotalDegree_piSingle, weightedTotalDegree_piSingle] at hw
  exact hw.trans hG.2.2.2

private def basisPolynomial (L : K[X]) (j : ℕ) : Geo[X] :=
  L.map embed * (Polynomial.X - Polynomial.C center) ^ j

private def rawDenominator (length : ℕ) (G : Equation) : InitialRing 2 :=
  initialSep G ^ exponent length

private def rawNumerator (length : ℕ) (g L : K[X]) (G : Equation)
    (i : Fin k) : InitialRing 2 :=
  C ((g.map embed).coeff i.val) * rawDenominator length G +
    ∑ l : Fin length, C ((basisPolynomial L l.val).coeff i.val) *
      commonTaylorNumerator center (lifted G) (exponent length) l.val

def chart (length : ℕ) (g L : K[X]) (G : Equation) (E : InitialRing 2) : Chart 2 :=
  ⟨E, inverseMap (nativeJet g) (nativeJet L) (rawDenominator length (transform g L G)),
    fun i => inverseMap (nativeJet g) (nativeJet L) (rawNumerator length g L (transform g L G) i)⟩

private theorem rawDenominator_band (s : Source) (length : ℕ) (hK : 3 ≤ length)
    (g L : K[X]) (G : Equation) (hG : OrderTwo s G) :
    InBand s length (rawDenominator length (transform g L G)) := by
  let Q := lifted (transform g L G)
  have hb : (initialJetSeparant center Q).totalDegree ≤ s.B - 1 :=
    (totalDegree_initialJetSeparant_le center Q).trans
      (Nat.sub_le_sub_right (lift_total hG g L) 1)
  have hi : (initialJetSeparant center Q).weightedTotalDegree Fin.val ≤ s.J - 2 := by
    simpa only [coeffWeight_eq, zero_add, one_mul] using
      (Astra7.initialSeparant_weight 0 1 center Q).trans (Nat.sub_le_sub_right (lift_index hG g L) (0 + 1 * 2))
  have ht : (initialJetSeparant center Q).degreeOf (Fin.last 2) ≤ s.C - 1 :=
    (degreeOf_initialJetSeparant_le center Q).trans (Nat.sub_le_sub_right (lift_top hG g L) 1)
  have hindex : (initialJetSeparant center Q ^ exponent length).weightedTotalDegree Fin.val ≤ indexCap s length :=
    ((weightedTotalDegree_pow_le _ _ _).trans (Nat.mul_le_mul_left _ hi)).trans (by
      unfold indexCap
      omega)
  refine ⟨((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hb)).trans (by unfold totalCap; omega),
    hindex, le_min ?_ (degreeOf_top_of_index hindex)⟩
  exact ((degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left _ ht)).trans (by omega)

private theorem rawCentered_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : K[X]) (G : Equation) (hG : OrderTwo s G) (l : Fin length) :
    InBand s length (commonTaylorNumerator center (lifted (transform g L G)) (exponent length) l.val) := by
  let Q := lifted (transform g L G)
  have hlK := l.isLt
  have hJ := hs.index_top
  have hC := hs.top_pos
  have hi := Astra7.commonTaylor_weight 0 1 s.J length (exponent length) center Q
    (exponent_sufficient length) (by omega) (lift_index hG g L) l
  have hindex : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
      indexCap s length := by
    have h : (commonTaylorNumerator center Q (exponent length) l.val).weightedTotalDegree Fin.val ≤
        exponent length * (s.J - 2) + l.val := by
      simpa only [coeffWeight_eq, zero_add, one_mul, add_zero] using hi
    exact h.trans (by unfold indexCap; omega)
  refine ⟨?_, hindex, le_min ?_ (degreeOf_top_of_index hindex)⟩
  · exact (totalDegree_commonTaylorNumerator_le center Q (exponent_sufficient length l)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (lift_total hG g L) 1)) 1)
  · have hl : l.val - 1 ≤ length - 2 := by omega
    apply (commonTaylor_top center Q hs.top_pos (lift_top hG g L) (exponent_sufficient length) l).trans
    rw [Nat.add_sub_assoc (by omega : 2 ≤ length)]
    exact Nat.add_le_add_left hl _

private theorem rawNumerator_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : K[X]) (G : Equation) (hG : OrderTwo s G) (i : Fin k) :
    InBand s length (rawNumerator length g L (transform g L G) i) := by
  let V := CJ0_4.bandSpace (totalCap s length) (indexCap s length) (topCap s length)
  have hmem {P : InitialRing 2} (hp : InBand s length P) : P ∈ V := CJ0_4.mem_bandSpace.mpr hp
  have hc (a : Geo) {P : InitialRing 2} (hp : InBand s length P) : C a * P ∈ V := by
    rw [← MvPolynomial.smul_eq_C_mul]
    exact V.smul_mem _ (hmem hp)
  suffices h : rawNumerator length g L (transform g L G) i ∈ V from CJ0_4.mem_bandSpace.mp h
  unfold rawNumerator
  exact V.add_mem (hc _ (rawDenominator_band s length hK g L G hG))
    (V.sum_mem fun l _ => hc _ (rawCentered_band s hs length hK g L G hG l))

private theorem inverse_band (s : Source) (length : ℕ) (g L : K[X]) {P : InitialRing 2}
    (hp : InBand s length P) : InBand s length (inverseMap (nativeJet g) (nativeJet L) P) := by
  have hb := inverse_weight (1 : Fin 3 → ℕ) (fun _ _ _ => le_rfl) (nativeJet g) (nativeJet L) P
  have hi := inverse_weight Fin.val (fun _ _ h => h) (nativeJet g) (nativeJet L) P
  have ht := inverse_weight (Pi.single (Fin.last 2) 1) top_monotone (nativeJet g) (nativeJet L) P
  simp only [weightedTotalDegree_one] at hb
  simp only [weightedTotalDegree_piSingle] at ht
  exact ⟨hb.trans hp.1, hi.trans hp.2.1, ht.trans hp.2.2⟩

theorem chart_band (s : Source) (hs : ShapeOK s) (length : ℕ) (hK : 3 ≤ length)
    (g L : K[X]) (G : Equation) (hG : OrderTwo s G) (E : InitialRing 2) :
    ShortBand s length (chart length g L G E) :=
  ⟨inverse_band s length g L (rawDenominator_band s length hK g L G hG),
    fun i => inverse_band s length g L (rawNumerator_band s hs length hK g L G hG i)⟩

private theorem denominator_eval (length : ℕ) (g L : K[X]) (G : Equation) (E : InitialRing 2)
    (u : Fin 3 → Geo) (hL : L ≠ 0) :
    MvPolynomial.eval u (chart length g L G E).denominator =
      (nativeJet L 0 * MvPolynomial.eval u (initialSep G)) ^ exponent length := by
  change MvPolynomial.eval u (inverseMap (nativeJet g) (nativeJet L)
    (rawDenominator length (transform g L G))) = _
  rw [eval_inverse, rawDenominator, map_pow, transform_initialSep, map_mul, MvPolynomial.eval_C,
    eval_affine, triangular_inverse _ _ _ (nativeJet_zero_ne hL)]

private theorem denominator_regular (length : ℕ) (g L : K[X]) (G : Equation) (E : InitialRing 2)
    (hL : L ≠ 0) (hE : Irreducible E) (hreg : ¬ E ∣ initialSep G) :
    ¬ E ∣ (chart length g L G E).denominator := by
  have he : (chart length g L G E).denominator =
      C (nativeJet L 0 ^ exponent length) * (initialSep G) ^ exponent length := by
    apply MvPolynomial.funext
    intro u
    rw [denominator_eval length g L G E u hL, map_mul, MvPolynomial.eval_C, map_pow, mul_pow]
  rw [he]
  have hu : IsUnit (C (nativeJet L 0 ^ exponent length) : InitialRing 2) :=
    ((isUnit_iff_ne_zero).mpr (pow_ne_zero _ (nativeJet_zero_ne hL))).map C
  intro h
  have hh := (hE.prime.dvd_or_dvd h).resolve_left (fun hd => hE.not_isUnit (isUnit_of_dvd_unit hd hu))
  exact hreg (hE.prime.dvd_of_dvd_pow hh)

private theorem reconstruct_basis (length : ℕ) (L : K[X]) (G : Equation) (u : Fin 3 → Geo) :
    L.map embed * rationalTaylorPolynomial center (lifted G) length u =
      ∑ l : Fin length, Polynomial.C (rationalTaylorCoefficient center (lifted G) u l.val) *
        basisPolynomial L l.val := by
  rw [rationalTaylorPolynomial, Polynomial.centeredCoefficientPrefix, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.taylor_monomial, map_neg, ← sub_eq_add_neg]
  unfold basisPolynomial
  ring

private theorem raw_output (length : ℕ) (g L : K[X]) (G : Equation)
    (u : Fin 3 → Geo) (hsep : MvPolynomial.eval u (initialSep G) ≠ 0) (i : Fin k) :
    MvPolynomial.eval u (rawNumerator length g L G i) / MvPolynomial.eval u (rawDenominator length G) =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted G) length u).coeff i.val := by
  have hpow : MvPolynomial.eval u (initialSep G) ^ exponent length ≠ 0 := pow_ne_zero _ hsep
  rw [reconstruct_basis, Polynomial.coeff_add, Polynomial.finsetSum_coeff, rawNumerator,
    map_add, add_div, map_mul, MvPolynomial.eval_C, rawDenominator, map_pow, mul_div_cancel_right₀ _ hpow,
    map_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [Polynomial.coeff_C_mul, map_mul, MvPolynomial.eval_C, ← MvPolynomial.aeval_eq_eval (f := u),
    aeval_commonTaylorNumerator center (lifted G) u (exponent_sufficient length l) hsep]
  change _ * (MvPolynomial.eval u (initialSep G) ^ exponent length * _) /
    MvPolynomial.eval u (initialSep G) ^ exponent length = _
  field_simp

private theorem chart_output (length : ℕ) (hK : 3 ≤ length) (g L : K[X]) (G : Equation)
    (E : InitialRing 2) (u : Fin 3 → Geo) (hu : MvPolynomial.eval u (chart length g L G E).denominator ≠ 0)
    (i : Fin k) :
    (chart length g L G E).output u i =
      (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted (transform g L G))
        length (inverseJet (nativeJet g) (nativeJet L) u)).coeff i.val := by
  let v := inverseJet (nativeJet g) (nativeJet L) u
  have hv : MvPolynomial.eval v (initialSep (transform g L G)) ≠ 0 := by
    intro hh
    apply hu
    change MvPolynomial.eval u (inverseMap (nativeJet g) (nativeJet L)
      (rawDenominator length (transform g L G))) = 0
    rw [eval_inverse, rawDenominator, map_pow, hh, zero_pow]
    unfold exponent
    omega
  rw [Chart.output, chart, eval_inverse, eval_inverse]
  exact raw_output length g L (transform g L G) v hv i

private theorem geoJet_affine (g L h : Geo[X]) :
    polynomialJet (d := 2) center (g + L * h) =
      triangular (polynomialJet center g) (polynomialJet center L) (polynomialJet center h) := by
  funext i
  change Polynomial.evalRingHom center (derivatives (g + L * h) i) =
    triangular (Polynomial.evalRingHom center ∘ derivatives g)
      (Polynomial.evalRingHom center ∘ derivatives L) (Polynomial.evalRingHom center ∘ derivatives h) i
  rw [derivatives_affine]
  exact map_triangular (Polynomial.evalRingHom center) _ _ _ i

private theorem natDegree_lt {F : Type*} [Field F] {P : F[X]} {b : ℕ} (hb : 0 < b)
    (hp : P.degree < b) : P.natDegree < b := by
  by_cases hz : P = 0
  · simpa [hz] using hb
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp

private theorem reconstruction_degree (length : ℕ) (hK : 3 ≤ length) (g L : K[X])
    (hg : g.degree < k) (hsum : L.natDegree + length ≤ k) (G : Equation) (u : Fin 3 → Geo) :
    (g.map embed + L.map embed * rationalTaylorPolynomial center (lifted G) length u).degree < k := by
  let U := rationalTaylorPolynomial center (lifted G) length u
  have hU : U.natDegree < length :=
    natDegree_lt (by omega) (Polynomial.degree_centeredCoefficientPrefix_lt _ _ _)
  have hg' : (g.map embed).natDegree < k :=
    Polynomial.natDegree_map_le.trans_lt (natDegree_lt (by decide) hg)
  have hm : (L.map embed * U).natDegree < k :=
    (Polynomial.natDegree_mul_le).trans_lt ((Nat.add_lt_add_of_le_of_lt Polynomial.natDegree_map_le hU).trans_le hsum)
  have hh : (g.map embed + L.map embed * U).natDegree < k :=
    (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hg' hm)
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hh)

theorem chart_ok (length : ℕ) (hK : 3 ≤ length) (g L : K[X]) (hL : L ≠ 0)
    (hg : g.degree < k) (hsum : L.natDegree + length ≤ k) (G : Equation)
    (E : InitialRing 2) (hE : Irreducible E) (hreg : ¬ E ∣ initialSep G) :
    ChartOK (chart length g L G E) := by
  refine ⟨hE, denominator_regular length g L G E hL hE hreg, ?_⟩
  intro u hu j
  let v := inverseJet (nativeJet g) (nativeJet L) u
  let U := rationalTaylorPolynomial center (lifted (transform g L G)) length v
  let P := g.map embed + L.map embed * U
  have hcoeff : (chart length g L G E).output u = (fun i : Fin k => P.coeff i.val) := by
    funext i
    exact chart_output length hK g L G E u hu.2 i
  rw [hcoeff, show readJet (fun i : Fin k => P.coeff i.val) j.val =
    (polynomialJet (d := 2) center P) j from readJet_eq P
      (reconstruction_degree length hK g L hg hsum (transform g L G) v) j.val]
  have hU : polynomialJet (d := 2) center U = v :=
    polynomialJet_rationalTaylorPolynomial center (lifted (transform g L G)) (by omega) v
  change (polynomialJet (d := 2) center (g.map embed + L.map embed * U)) j = u j
  rw [geoJet_affine, hU]
  exact congrFun (triangular_inverse (nativeJet g) (nativeJet L) u (nativeJet_zero_ne hL)) j

private theorem chart_contains (length : ℕ) (hK : 3 ≤ length) (hk : length ≤ k)
    (g L : K[X]) (hL : L ≠ 0) (G : Equation) (E : InitialRing 2)
    {f h : K[X]} (hh : h.degree < length) (hf : f = g + L * h)
    (hsol : differentialSpecialization G f = 0) (hE : MvPolynomial.eval (nativeJet f) E = 0)
    (hsep : MvPolynomial.eval (nativeJet f) (initialSep G) ≠ 0) :
    coeffPoint f ∈ (chart length g L G E).imageSet := by
  have hL0 := nativeJet_zero_ne hL
  have hu : MvPolynomial.eval (nativeJet f) (chart length g L G E).denominator ≠ 0 := by
    rw [denominator_eval length g L G E _ hL]
    exact pow_ne_zero _ (mul_ne_zero hL0 hsep)
  have hv : inverseJet (nativeJet g) (nativeJet L) (nativeJet f) = nativeJet h := by
    rw [hf, nativeJet_affine]
    exact inverse_triangular _ _ _ hL0
  have hs : MvPolynomial.eval (nativeJet h) (initialSep (transform g L G)) ≠ 0 := by
    rw [transform_initialSep, map_mul, MvPolynomial.eval_C, eval_affine, ← nativeJet_affine, ← hf]
    exact mul_ne_zero hL0 hsep
  have hsol' : differentialSpecialization (lifted (transform g L G)) (h.map embed) = 0 := by
    rw [lifted, ← map_differentialSpecialization, transform_spec, ← hf, hsol, Polynomial.map_zero]
  have hsep' : jetEvaluation (separant (lifted (transform g L G)) (Fin.last 2)) center (nativeJet h) ≠ 0 := by
    simpa only [initialSep, ← MvPolynomial.aeval_eq_eval, aeval_initialJetSeparant] using hs
  let : CharP Geo p := charP_of_injective_ringHom embed.injective p
  have hbin (i : ℕ) (hlo : 2 < i) (hhi : i < length) : (i.choose 2 : Geo) ≠ 0 :=
    Sol1.C40Primitives.native_binomial_guard 2 le_rfl i hlo (Nat.lt_succ_of_lt (hhi.trans_le hk))
  have hrec := rationalTaylorPolynomial_polynomialJet center (lifted (transform g L G))
    (h.map embed) hsol' hsep' (Polynomial.degree_map_le.trans_lt hh) hbin
  refine ⟨nativeJet f, ⟨hE, hu⟩, ?_⟩
  funext i
  rw [chart_output length hK g L G E _ hu, hv, nativeJet, hrec,
    ← Polynomial.map_mul, ← Polynomial.map_add, ← hf, Polynomial.coeff_map]
  rfl

/-- Shortening the quotient chart by the number of common agreement positions bounds the
numerator and denominator while retaining the original jet coordinates. -/
theorem shortenChart (s : Source) (hs : ShapeOK s) (G : Equation) (hG : OrderTwo s G)
    (E : InitialRing 2) (hE : Irreducible E) (_hEdvd : E ∣ initial G)
    (hreg : ¬ E ∣ initialSep G) (S : Finset Node) (hS : S.card + 3 ≤ k) (w : Node → K) :
    ∃ T : Chart 2, ChartOK T ∧ T.equation = E ∧ ShortBand s (k - S.card) T ∧
      ∀ f : K[X], f.degree < k → differentialSpecialization G f = 0 →
        MvPolynomial.eval (nativeJet f) E = 0 → MvPolynomial.eval (nativeJet f) (initialSep G) ≠ 0 →
        (∀ i ∈ S, f.eval (node i) = w i) → coeffPoint f ∈ T.imageSet := by
  classical
  let g := Lagrange.interpolate S node w
  let L := FrobeniusLocator.locator node S
  let length := k - S.card
  have hK : 3 ≤ length := by dsimp [length]; omega
  have hk : length ≤ k := Nat.sub_le _ _
  have hL := (FrobeniusLocator.locator_monic node S).ne_zero
  have hLn : L.natDegree = S.card := FrobeniusLocator.locator_natDegree _ _
  have hx : Function.Injective node := ProximityPrize.Benchmark.IRSProfile.domain.injective
  have hg : g.degree < k := (Lagrange.degree_interpolate_lt w hx.injOn).trans_le
    (by exact_mod_cast (show S.card ≤ k by omega))
  have hsum : L.natDegree + length ≤ k := by rw [hLn]; dsimp [length]; omega
  refine ⟨chart length g L G E, chart_ok length hK g L hL hg hsum G E hE hreg, rfl,
    chart_band s hs length hK g L G hG E, ?_⟩
  intro f hf hroot hEroot hsep hits
  have hdiv : L ∣ f - g := FrobeniusLocator.Strata.locator_dvd_of_eval_zero node hx S _ (fun i hi => by
    rw [Polynomial.eval_sub, hits i hi, show g.eval (node i) = w i from
      Lagrange.eval_interpolate_at_node w hx.injOn hi, sub_self])
  have hd : (f - g).degree < k := (Polynomial.degree_sub_le _ _).trans_lt (max_lt hf hg)
  have hdN : (f - g).natDegree ≤ N := by
    have hh := natDegree_lt (by decide) hd
    change _ < 131072 at hh
    change _ ≤ 131071
    omega
  have hS' : S.card ≤ N := by
    change _ ≤ 131072 at hS
    change _ ≤ 131071
    omega
  obtain ⟨h, hdeg, he⟩ :=
    FrobeniusLocator.Strata.bounded_locator_quotient node S (f - g) N hS' hdN hdiv
  have hf' : f = g + L * h := by rw [← he]; ring
  have hlen : N - S.card + 1 = length := by
    dsimp [length]
    change _ ≤ 131072 at hS
    change 131071 - S.card + 1 = 131072 - S.card
    omega
  rw [hlen] at hdeg
  exact chart_contains length hK hk g L hL G E hdeg hf' hroot hEroot hsep

#print axioms shortenChart
end
end ShortenChart
