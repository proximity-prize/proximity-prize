import ProximityPrize.SubmissionLower.LocatorDerivativeChainJoint
import ProximityPrize.SubmissionLower.LocatorArithmetic

/-!
# Early stopping in the derivative chain

This module stops an irreducible factor's derivative chain once its remaining
`R`-degree is at most a prescribed cap.  The unresolved seeds are then split
once into a regular pair and the existing tight singular family.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeChainPartial

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318
  RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243
open LocatorDerivativeChain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

theorem exists_derivative_degree_le (F : MvPolynomial (Fin 4) K) (r : ℕ) :
    ∃ j, j ≤ chainLength F ∧ (dR j F).degreeOf 2 ≤ r :=
  ⟨chainLength F, le_rfl, by rw [chainLength_spec]; exact Nat.zero_le _⟩

/-- First derivative in the chain whose remaining `R`-degree is at most `r`. -/
def partialLength (F : MvPolynomial (Fin 4) K) (r : ℕ) : ℕ :=
  Nat.find (exists_derivative_degree_le F r)

theorem partialLength_le_chainLength (F : MvPolynomial (Fin 4) K) (r : ℕ) :
    partialLength F r ≤ chainLength F :=
  (Nat.find_spec (exists_derivative_degree_le F r)).1

theorem partialLength_degree_le (F : MvPolynomial (Fin 4) K) (r : ℕ) :
    (dR (partialLength F r) F).degreeOf 2 ≤ r :=
  (Nat.find_spec (exists_derivative_degree_le F r)).2

theorem partialLength_le_degree_sub (F : MvPolynomial (Fin 4) K) (r : ℕ) :
    partialLength F r ≤ F.degreeOf 2 - r := by
  by_cases h : chainLength F ≤ F.degreeOf 2 - r
  · exact (partialLength_le_chainLength F r).trans h
  · apply Nat.find_min'
    refine ⟨by omega, ?_⟩
    exact dR_R_degree_le (F.degreeOf 2 - r) F |>.trans (by omega)

theorem partialLength_pos_of_cap_lt_degree (F : MvPolynomial (Fin 4) K)
    (r : ℕ) (h : r < F.degreeOf 2) : 1 ≤ partialLength F r := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hd := partialLength_degree_le F r
  rw [hz] at hd
  simpa only [dR_zero] using (Nat.not_le_of_lt h hd)

theorem dR_partial_ne_zero (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (p r : ℕ) [CharP K p] (hsmall : F.degreeOf 2 < p) :
    dR (partialLength F r) F ≠ 0 :=
  dR_ne_zero F hF p hsmall _ (partialLength_le_chainLength F r)

/-- The derivative inherits the original weighted and seed bounds, while an
independent degree estimate can sharpen its `R` cap. -/
theorem dR_mem_reduced_box (F : MvPolynomial (Fin 4) K)
    (D w L s r j : ℕ) (hbox : F ∈ globalCoefficientBox K D w L s)
    (hdegree : (dR j F).degreeOf 2 ≤ r) :
    dR j F ∈ globalCoefficientBox K D w L r := by
  intro d hd
  obtain ⟨ht, _hs, hz⟩ := dR_mem_box j F D w L s hbox hd
  have hdr := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd
  exact ⟨ht, hdr.trans hdegree, hz⟩

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Seeds singular on an irreducible factor. -/
def factorSingularSeeds (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ => specialization K (selected γ) γ F = 0 ∧
    specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) F) = 0

def partialRemainderSeeds (F : MvPolynomial (Fin 4) K) (r : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun γ =>
    specialization K (selected γ) γ (dR (partialLength F r) F) = 0 ∧
      specialization K (selected γ) γ F = 0

theorem factorSingularSeeds_partial_cover
    (F : MvPolynomial (Fin 4) K) (r : ℕ) (hr : r < F.degreeOf 2)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    factorSingularSeeds F selected Gamma ⊆
      ((Finset.Ico 1 (partialLength F r)).biUnion fun j =>
        chainSeeds F j selected Gamma) ∪
      partialRemainderSeeds F r selected Gamma := by
  classical
  intro γ hγ
  obtain ⟨hγG, hF0, hF1⟩ := Finset.mem_filter.mp hγ
  have hk : 1 ≤ partialLength F r := partialLength_pos_of_cap_lt_degree F r hr
  rcases chain_split F (selected γ) γ hF0 hF1 (partialLength F r) hk with
    hregular | hall
  · obtain ⟨j, hj1, hjk, hjreg⟩ := hregular
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjk⟩,
      Finset.mem_filter.mpr ⟨hγG, hjreg, hF0⟩⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hγG, hall _ le_rfl, hF0⟩

/-- Bound one high-degree factor after stopping when its remaining slope is at
most `r`.  The first term counts the preceding regular derivative stages; the
last two terms are the regular/singular split at the stopping derivative. -/
theorem factorSingularSeeds_card_le_partial
    (Pc : UnequalParameters) (S : TightParameters)
    (Q F : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hFmem : F ∈ positiveRFactors Q)
    (D w L s r p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hrpos : 1 ≤ r) (hrlt : r < F.degreeOf 2)
    (hcgap : 0 < Pc.gap) (hcY : (D - 1) / w ≤ Pc.leftY)
    (hcR : s ≤ Pc.leftR) (hcZ : L ≤ Pc.leftZ)
    (hcY' : (D - 1) / w ≤ Pc.rightY) (hcR' : s ≤ Pc.rightR)
    (hcZ' : L ≤ Pc.rightZ) (hcleftR : 1 ≤ Pc.leftR)
    (hcleftYSmall : Pc.leftY < p) (hcleftRSmall : Pc.leftR < p)
    (hcleftZSmall : Pc.leftZ < p) (hcmixedYSmall : Pc.mixedCost.y < p)
    (hcmixedRSmall : Pc.mixedCost.r < p) (hcmixedZSmall : Pc.mixedCost.z < p)
    (hSD : S.D = D) (hSw : S.w = w) (hSL : S.L = L) (hSs : S.s = r)
    (hSsmall : S.s < p) (hSchar : S.w < p)
    (hSDw : S.w < S.kappa * S.D) (hSj : 1 ≤ S.algebraicCap)
    (hSY : S.implicitYCap < p) (hSZ : S.algebraicCap < p)
    (hSmixed : 2 * S.implicitYCap * S.algebraicCap < p)
    (hSwa : S.w < S.a) (hSan : S.a ≤ S.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodesC : nodes.card = Pc.n) (hnodesS : nodes.card = S.n)
    (hCw : 1 ≤ Pc.w) (hCchar : Pc.w < p) (hCwa : Pc.w < Pc.a)
    (hCan : Pc.a ≤ Pc.n)
    (hdegreeC : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ Pc.w)
    (hdegreeS : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ S.w)
    (hagreementC : ∀ γ ∈ Gamma, Pc.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementS : ∀ γ ∈ Gamma, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencilC : NoLargeSelectedPencil selected Gamma Pc.w Pc.errors)
    (hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors) :
    (factorSingularSeeds F selected Gamma).card ≤
      partialLength F r * Pc.regularCountCap + S.countCap := by
  classical
  obtain ⟨hFirr, hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hFmem
  have hFsmall : F.degreeOf 2 < p := by
    exact (degreeOf_R_le_of_mem_box F D w L s hFbox).trans_lt hsmall
  let k := partialLength F r
  let J := dR k F
  have hkpos : 1 ≤ k := partialLength_pos_of_cap_lt_degree F r hrlt
  have hkle : k ≤ chainLength F := partialLength_le_chainLength F r
  have hJ : J ≠ 0 := dR_ne_zero F hFirr.ne_zero p hFsmall k hkle
  have hrel : IsRelPrime J F :=
    (hFirr.isRelPrime_iff_not_dvd.mpr
      (irreducible_not_dvd_dR F hFirr p hFpos hFsmall k hkpos hkle)).symm
  have hJboxOriginal : J ∈ globalCoefficientBox K D w L s :=
    dR_mem_box k F D w L s hFbox
  have hJboxReduced : J ∈ globalCoefficientBox K S.D S.w S.L S.s := by
    rw [hSD, hSw, hSL, hSs]
    exact dR_mem_reduced_box F D w L s r k hFbox
      (partialLength_degree_le F r)
  let Delta := partialRemainderSeeds F r selected Gamma
  have hDeltaSub : Delta ⊆ Gamma := Finset.filter_subset _ _
  have hDeltaJ : ∀ γ ∈ Delta, specialization K (selected γ) γ J = 0 := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2.1
  have hDeltaF : ∀ γ ∈ Delta, specialization K (selected γ) γ F = 0 := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2.2
  have hdecomp := card_le_regular_sum_add_singular J F hJ
    S.D S.w S.L S.s p (by simpa [hSs] using hrpos) hSsmall
    (by simpa [hSw] using hw) hSDw hSj hSZ hJboxReduced
    selected Delta hDeltaJ hDeltaF
  have hFcaps := degree_bounds_of_mem_box F D w L s hw hFbox
  have hregular := all_regularPairSeeds_bound Pc J F hJ hrel D w L s p
    hJboxOriginal hw hcY hcR hcZ (hFcaps.1.trans hcY')
    (hFcaps.2.1.trans hcR') (hFcaps.2.2.trans hcZ') hcleftR hcleftYSmall
    hcleftRSmall hcleftZSmall hcmixedYSmall hcmixedRSmall hcmixedZSmall
    selected Delta nodes x u0 u1 hinj hnodesC hCw hCchar hCwa hCan
    (fun γ hγ => hdegreeC γ (hDeltaSub hγ))
    (fun γ hγ => hagreementC γ (hDeltaSub hγ))
    (noLargeSelectedPencil_mono selected Gamma Delta Pc.w Pc.errors
      hDeltaSub hnoPencilC)
  have hregSum := sum_regular_counts_bound Pc J F selected Delta
    (regularVector_budgets Pc J hJ D w L s (by omega) hJboxOriginal hcY hcR hcZ)
    hregular
  have hregCap : (∑ G : RegularIndex J,
      (regularPairSeeds J F selected Delta G).card) ≤ Pc.regularCountCap :=
    Pc.regular_count_le _ hcgap hregSum
  have hsingCap : (singularSeeds J selected Delta).card ≤ S.countCap := by
    exact RCN292.TightParameters.singularSeeds_count_le_countCap
      S J hJ hJboxReduced
      (by simpa [hSs] using hrpos) hSsmall (by simpa [hSw] using hw)
      hSchar hSDw hSj hSY hSZ hSmixed hSwa hSan selected Delta nodes x u0 u1
      hinj hnodesS
      (fun γ hγ => hdegreeS γ (hDeltaSub hγ))
      (fun γ hγ => hagreementS γ (hDeltaSub hγ))
      (noLargeSelectedPencil_mono selected Gamma Delta S.w S.errors
        hDeltaSub hnoPencilS)
  have hDelta : Delta.card ≤ Pc.regularCountCap + S.countCap := by omega
  have hchain : ∀ j ∈ Finset.Ico 1 k,
      (chainSeeds F j selected Gamma).card ≤ Pc.regularCountCap := by
    intro j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Ico.mp hj
    exact chainSeeds_card_le Pc Q F hQ hFmem j hj1
      (hjk.le.trans hkle) D w L s p hsmall hw hbox hcgap hcY hcR hcZ hcY'
      hcR' hcZ' hcleftR hcleftYSmall hcleftRSmall hcleftZSmall
      hcmixedYSmall hcmixedRSmall hcmixedZSmall selected Gamma nodes x u0 u1
      hinj hnodesC hCw hCchar hCwa hCan hdegreeC hagreementC hnoPencilC
  have hchainUnion : ((Finset.Ico 1 k).biUnion fun j =>
      chainSeeds F j selected Gamma).card ≤ (k - 1) * Pc.regularCountCap := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico 1 k, (chainSeeds F j selected Gamma).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.Ico 1 k, Pc.regularCountCap :=
        Finset.sum_le_sum fun j hj => hchain j hj
      _ = (k - 1) * Pc.regularCountCap := by
        simp [Finset.sum_const, Nat.card_Ico]
  have hcover := factorSingularSeeds_partial_cover F r hrlt selected Gamma
  have hcard := Finset.card_le_card hcover
  have hunion := Finset.card_union_le
    ((Finset.Ico 1 k).biUnion fun j => chainSeeds F j selected Gamma) Delta
  dsimp only [k, Delta] at hcard hunion hchainUnion hDelta ⊢
  have hkpos' : 1 ≤ partialLength F r := partialLength_pos_of_cap_lt_degree F r hrlt
  have hsplit : partialLength F r * Pc.regularCountCap + S.countCap =
      (partialLength F r - 1) * Pc.regularCountCap +
        (Pc.regularCountCap + S.countCap) := by
    have hk : partialLength F r = (partialLength F r - 1) + 1 := by omega
    have hmul : partialLength F r * Pc.regularCountCap =
        (partialLength F r - 1) * Pc.regularCountCap +
          Pc.regularCountCap := by
      calc
        partialLength F r * Pc.regularCountCap =
            ((partialLength F r - 1) + 1) * Pc.regularCountCap := by
          exact congrArg (fun z => z * Pc.regularCountCap) hk
        _ = (partialLength F r - 1) * Pc.regularCountCap +
            Pc.regularCountCap := by ring
    rw [hmul]
    omega
  rw [hsplit]
  omega

theorem partial_factor_bound_to_degree_bound
    (F : MvPolynomial (Fin 4) K) (r chainCap singularCap count : ℕ)
    (hcount : count ≤ partialLength F r * chainCap + singularCap) :
    count ≤ (F.degreeOf 2 - r) * chainCap + singularCap := by
  exact hcount.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right chainCap (partialLength_le_degree_sub F r)) _)

/-- The regular factors, singular factors, and the `R`-free product cover all
solutions of a relatively-prime pair.  Unlike `LocatorDerivativeChain.cover`,
this leaves the singular factor sets intact so that each factor may choose its
own stopping depth. -/
theorem residual_factor_cover
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0) :
    Gamma ⊆
      (Finset.univ.biUnion fun F : RegularIndex Q =>
        regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        factorSingularSeeds F selected Gamma) ∪
      rfreeSeeds Q selected Gamma := by
  classical
  intro γ hγ
  obtain ⟨F, hFactive, hFzero⟩ :=
    exists_active_factor_of_solution Q hQ (selected γ) γ (hQsolution γ hγ)
  by_cases hRfree : F.degreeOf 2 = 0
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hγ, ?_⟩
    have hdiv : F ∣ rfreeProduct Q := by
      unfold rfreeProduct
      exact Finset.dvd_prod_of_mem _
        (Finset.mem_filter.mpr ⟨hFactive, hRfree⟩)
    obtain ⟨c, hc⟩ := hdiv
    rw [hc, map_mul, hFzero, zero_mul]
  · have hpos : 0 < F.degreeOf 2 := Nat.pos_of_ne_zero hRfree
    have hFpos : F ∈ positiveRFactors Q := by
      unfold positiveRFactors
      exact Finset.mem_filter.mpr ⟨hFactive, hpos⟩
    by_cases hregular :
        specialization K (selected γ) γ
          (MvPolynomial.pderiv (2 : Fin 4) F) = 0
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨F, hFpos, Finset.mem_filter.mpr ⟨hγ, hFzero, hregular⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨F, hFpos⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hγ, ⟨hFzero, hregular⟩,
          hTsolution γ hγ⟩⟩

/-- The old terminal argument, localized to one positive-`R` factor. -/
theorem factorSingularSeeds_card_le_full
    (F : MvPolynomial (Fin 4) K) (hpos : 0 < F.degreeOf 2)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (chainCap tailCap : ℕ)
    (hchain : ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤ chainCap)
    (htail : (tailSeeds F selected Gamma).card ≤ tailCap) :
    (factorSingularSeeds F selected Gamma).card ≤
      (chainLength F - 1) * chainCap + tailCap := by
  classical
  have hm : 1 ≤ chainLength F := chainLength_pos F hpos
  have hcover : factorSingularSeeds F selected Gamma ⊆
      ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
        chainSeeds F j selected Gamma) ∪ tailSeeds F selected Gamma := by
    intro γ hγ
    obtain ⟨hγG, hF0, hF1⟩ := Finset.mem_filter.mp hγ
    rcases chain_split F (selected γ) γ hF0 hF1 (chainLength F) hm with
      hregular | hall
    · obtain ⟨j, hj1, hjm, hjreg⟩ := hregular
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjm⟩,
        Finset.mem_filter.mpr ⟨hγG, hjreg, hF0⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hγG, hall _ le_rfl⟩
  have hchains : ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
      chainSeeds F j selected Gamma).card ≤
      (chainLength F - 1) * chainCap := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico 1 (chainLength F),
          (chainSeeds F j selected Gamma).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.Ico 1 (chainLength F), chainCap :=
        Finset.sum_le_sum fun j hj => hchain j hj
      _ = (chainLength F - 1) * chainCap := by
        simp [Finset.sum_const, Nat.card_Ico]
  have hcard := Finset.card_le_card hcover
  have hunion := Finset.card_union_le
    ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
      chainSeeds F j selected Gamma) (tailSeeds F selected Gamma)
  omega

theorem full_factor_bound_to_degree_bound
    (F : MvPolynomial (Fin 4) K) (chainCap tailCap count : ℕ)
    (hcount : count ≤ (chainLength F - 1) * chainCap + tailCap) :
    count ≤ (F.degreeOf 2 - 1) * chainCap + tailCap := by
  have hsub : chainLength F - 1 ≤ F.degreeOf 2 - 1 :=
    Nat.sub_le_sub_right (chainLength_le F) 1
  exact hcount.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right chainCap hsub) _)

private theorem high_scalar_bound
    (totalSlope stopCap a b chain residual : ℕ)
    (hab : a + stopCap * b ≤ totalSlope)
    (hb : 1 ≤ b) (hp : residual ≤ stopCap * chain) :
    a * chain + b * residual ≤
      (totalSlope - stopCap) * chain + residual := by
  have hb' : b = (b - 1) + 1 := by omega
  have hbstop : stopCap * b = stopCap * (b - 1) + stopCap := by
    calc
      stopCap * b = stopCap * ((b - 1) + 1) := by rw [← hb']
      _ = stopCap * (b - 1) + stopCap := by ring
  have haAdd : (a + stopCap * (b - 1)) + stopCap ≤ totalSlope := by
    rw [add_assoc, ← hbstop]
    exact hab
  have ha : a + stopCap * (b - 1) ≤ totalSlope - stopCap :=
    Nat.le_sub_of_add_le haAdd
  have hmul : b * residual = (b - 1) * residual + residual := by
    calc
      b * residual = ((b - 1) + 1) * residual := by
        exact congrArg (fun z => z * residual) hb'
      _ = (b - 1) * residual + residual := by ring
  calc
    a * chain + b * residual =
        a * chain + (b - 1) * residual + residual := by
      simpa only [add_assoc] using congrArg (fun z => a * chain + z) hmul
    _ ≤ a * chain + (b - 1) * (stopCap * chain) + residual := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left (b - 1) hp) _) _
    _ = (a + stopCap * (b - 1)) * chain + residual := by ring
    _ ≤ (totalSlope - stopCap) * chain + residual :=
      Nat.add_le_add_right (Nat.mul_le_mul_right chain ha) _

/-- Pure aggregation theorem for fixed-stop accounting.  The final `hlow`
hypothesis is a small scalar certificate for the case where every factor has
degree at most `stopCap`; it is discharged numerically by the benchmark
instance. -/
theorem residual_card_le_fixed_stop
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (totalSlope stopCap regularCap chainCap tailCap partialCap : ℕ)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0)
    (hregular : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F).card ≤ regularCap)
    (hrfree : (rfreeSeeds Q selected Gamma).card ≤ tailCap)
    (hfactorLow : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ stopCap →
      (factorSingularSeeds F selected Gamma).card ≤
        (F.degreeOf 2 - 1) * chainCap + tailCap)
    (hfactorHigh : ∀ F ∈ positiveRFactors Q, stopCap < F.degreeOf 2 →
      (factorSingularSeeds F selected Gamma).card ≤
        (F.degreeOf 2 - stopCap) * chainCap + partialCap)
    (hdegree : (∑ F ∈ positiveRFactors Q, F.degreeOf 2) ≤ totalSlope)
    (htailChain : tailCap ≤ chainCap)
    (hpartialChain : partialCap ≤ stopCap * chainCap)
    (hlow : ∀ a b : ℕ, a + b ≤ totalSlope →
      a ≤ (stopCap - 1) * b →
      a * chainCap + b * tailCap ≤
        (totalSlope - stopCap) * chainCap + partialCap) :
    Gamma.card ≤ regularCap + (totalSlope - stopCap) * chainCap +
      partialCap + tailCap := by
  classical
  let low := (positiveRFactors Q).filter fun F => F.degreeOf 2 ≤ stopCap
  let high := (positiveRFactors Q).filter fun F => stopCap < F.degreeOf 2
  let singularUnion := (positiveRFactors Q).biUnion fun F =>
    factorSingularSeeds F selected Gamma
  have hpartition : positiveRFactors Q = low ∪ high := by
    ext F
    simp only [low, high, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hF
      by_cases hd : F.degreeOf 2 ≤ stopCap
      · exact Or.inl ⟨hF, hd⟩
      · exact Or.inr ⟨hF, by omega⟩
    · intro hF
      rcases hF with ⟨hF, _⟩ | ⟨hF, _⟩ <;> exact hF
  have hdisjoint : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro F hFl hFh
    have hl := (Finset.mem_filter.mp hFl).2
    have hh := (Finset.mem_filter.mp hFh).2
    omega
  have hpositive : singularUnion.card ≤
      (∑ F ∈ low, ((F.degreeOf 2 - 1) * chainCap + tailCap)) +
      (∑ F ∈ high, ((F.degreeOf 2 - stopCap) * chainCap + partialCap)) := by
    calc
      singularUnion.card ≤ ∑ F ∈ positiveRFactors Q,
          (factorSingularSeeds F selected Gamma).card := Finset.card_biUnion_le
      _ = (∑ F ∈ low, (factorSingularSeeds F selected Gamma).card) +
          (∑ F ∈ high, (factorSingularSeeds F selected Gamma).card) := by
        rw [hpartition, Finset.sum_union hdisjoint]
      _ ≤
          (∑ F ∈ low, ((F.degreeOf 2 - 1) * chainCap + tailCap)) +
          (∑ F ∈ high, ((F.degreeOf 2 - stopCap) * chainCap + partialCap)) := by
        apply Nat.add_le_add
        · apply Finset.sum_le_sum
          intro F hF
          have hm := Finset.mem_filter.mp hF
          exact hfactorLow F hm.1 hm.2
        · apply Finset.sum_le_sum
          intro F hF
          have hm := Finset.mem_filter.mp hF
          exact hfactorHigh F hm.1 hm.2
  have hpositiveCap : singularUnion.card ≤
      (totalSlope - stopCap) * chainCap + partialCap := by
    apply hpositive.trans
    by_cases hHighEmpty : high.card = 0
    · rw [Finset.card_eq_zero] at hHighEmpty
      simp only [hHighEmpty, Finset.sum_empty, add_zero]
      have hcostEq :
          (∑ F ∈ low, ((F.degreeOf 2 - 1) * chainCap + tailCap)) =
            (∑ F ∈ low, (F.degreeOf 2 - 1)) * chainCap +
              low.card * tailCap := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp [Finset.sum_const]
      rw [hcostEq]
      apply hlow
      · have hlowDegree :
            (∑ F ∈ low, F.degreeOf 2) ≤ totalSlope := by
          apply le_trans ?_ hdegree
          rw [hpartition, Finset.sum_union hdisjoint, hHighEmpty]
          simp
        have hposLow : ∀ F ∈ low, 1 ≤ F.degreeOf 2 := by
          intro F hF
          exact (positiveRFactors_spec Q F (Finset.mem_filter.mp hF).1).2.2
        have heq : (∑ F ∈ low, (F.degreeOf 2 - 1)) + low.card =
            ∑ F ∈ low, F.degreeOf 2 := by
          calc
            _ = ∑ F ∈ low, ((F.degreeOf 2 - 1) + 1) := by
              rw [Finset.sum_add_distrib]
              simp
            _ = _ := Finset.sum_congr rfl (fun F hF => by
              have := hposLow F hF
              omega)
        rw [heq]
        exact hlowDegree
      · calc
          (∑ F ∈ low, (F.degreeOf 2 - 1)) ≤
              ∑ _F ∈ low, (stopCap - 1) := by
            apply Finset.sum_le_sum
            intro F hF
            have hm := (Finset.mem_filter.mp hF).2
            omega
          _ = (stopCap - 1) * low.card := by
            simp [Finset.sum_const, Nat.mul_comm]
    · have hHighPos : 1 ≤ high.card := Nat.pos_of_ne_zero hHighEmpty
      have hcostEqLow :
          (∑ F ∈ low, ((F.degreeOf 2 - 1) * chainCap + tailCap)) =
            (∑ F ∈ low, (F.degreeOf 2 - 1)) * chainCap +
              low.card * tailCap := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp [Finset.sum_const]
      have hcostEqHigh :
          (∑ F ∈ high, ((F.degreeOf 2 - stopCap) * chainCap + partialCap)) =
            (∑ F ∈ high, (F.degreeOf 2 - stopCap)) * chainCap +
              high.card * partialCap := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp [Finset.sum_const]
      rw [hcostEqLow, hcostEqHigh]
      have hbudget :
          (((∑ F ∈ low, (F.degreeOf 2 - 1)) + low.card) +
            ∑ F ∈ high, (F.degreeOf 2 - stopCap)) +
              stopCap * high.card ≤
              totalSlope := by
        have hposLow : ∀ F ∈ low, 1 ≤ F.degreeOf 2 := by
          intro F hF
          exact (positiveRFactors_spec Q F (Finset.mem_filter.mp hF).1).2.2
        have heqLow :
            (∑ F ∈ low, (F.degreeOf 2 - 1)) + low.card =
              ∑ F ∈ low, F.degreeOf 2 := by
          calc
            _ = ∑ F ∈ low, ((F.degreeOf 2 - 1) + 1) := by
              rw [Finset.sum_add_distrib]
              simp
            _ = _ := Finset.sum_congr rfl (fun F hF => by
              have := hposLow F hF
              omega)
        have heqHigh :
            (∑ F ∈ high, (F.degreeOf 2 - stopCap)) +
                stopCap * high.card =
              ∑ F ∈ high, F.degreeOf 2 := by
          calc
            _ = ∑ F ∈ high, ((F.degreeOf 2 - stopCap) + stopCap) := by
              rw [Finset.sum_add_distrib]
              simp [Finset.sum_const, Nat.mul_comm]
            _ = _ := Finset.sum_congr rfl (fun F hF => by
              have hm := (Finset.mem_filter.mp hF).2
              omega)
        calc
          _ = (∑ F ∈ low, F.degreeOf 2) +
              (∑ F ∈ high, F.degreeOf 2) := by omega
          _ = ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
            rw [hpartition, Finset.sum_union hdisjoint]
          _ ≤ totalSlope := hdegree
      have hlowAbsorb :
          low.card * tailCap ≤ low.card * chainCap :=
        Nat.mul_le_mul_left _ htailChain
      have hmain := high_scalar_bound
        totalSlope stopCap
        ((∑ F ∈ low, (F.degreeOf 2 - 1)) + low.card +
          ∑ F ∈ high, (F.degreeOf 2 - stopCap))
        high.card chainCap partialCap (by omega) hHighPos hpartialChain
      calc
        (∑ F ∈ low, (F.degreeOf 2 - 1)) * chainCap +
              low.card * tailCap +
            ((∑ F ∈ high, (F.degreeOf 2 - stopCap)) * chainCap +
              high.card * partialCap) ≤
            (∑ F ∈ low, (F.degreeOf 2 - 1)) * chainCap +
              low.card * chainCap +
            ((∑ F ∈ high, (F.degreeOf 2 - stopCap)) * chainCap +
              high.card * partialCap) := by
          exact Nat.add_le_add_right
            (Nat.add_le_add_left hlowAbsorb _) _
        _ = ((∑ F ∈ low, (F.degreeOf 2 - 1)) + low.card +
              ∑ F ∈ high, (F.degreeOf 2 - stopCap)) * chainCap +
                high.card * partialCap := by ring
        _ ≤ (totalSlope - stopCap) * chainCap + partialCap := hmain
  have hcover := residual_factor_cover Q T hQ selected Gamma hQsolution hTsolution
  have hcard := Finset.card_le_card hcover
  have h1 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F) ∪ singularUnion)
    (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le
    (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F) singularUnion
  dsimp only [singularUnion] at hcard h1 h2 hpositiveCap
  omega

/-! ### Current target specialization: total slope 25, stopping cap 7 -/

open LocatorArithmetic

theorem partialSingular7_le_chain :
    partialSingular7.countCap ≤ 7 * chainStage.regularCountCap := by
  rw [partialSingular7_exact, chainStage_exact]
  decide

theorem target25_stop7_low_certificate :
    ∀ a b : ℕ, a + b ≤ 25 → a ≤ 6 * b →
      a * chainStage.regularCountCap + b * tailSingular.countCap ≤
        18 * chainStage.regularCountCap + partialSingular7.countCap := by
  intro a b hab ha
  rw [chainStage_exact, tailSingular_exact, partialSingular7_exact]
  omega

/-- Target-ready wrapper around `residual_card_le_fixed_stop`.  Its high-degree
factor premise is supplied by `factorSingularSeeds_card_le_partial` with
`Pc = chainStage`, `S = partialSingular7`, and `r = 7`. -/
theorem residual_card_le_target25_stop7
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (regularCap : ℕ)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0)
    (hregular : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F).card ≤ regularCap)
    (hrfree : (rfreeSeeds Q selected Gamma).card ≤ tailSingular.countCap)
    (hfactorLow : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ 7 →
      (factorSingularSeeds F selected Gamma).card ≤
        (F.degreeOf 2 - 1) * chainStage.regularCountCap +
          tailSingular.countCap)
    (hfactorHigh : ∀ F ∈ positiveRFactors Q, 7 < F.degreeOf 2 →
      (factorSingularSeeds F selected Gamma).card ≤
        (F.degreeOf 2 - 7) * chainStage.regularCountCap +
          partialSingular7.countCap)
    (hdegree : (∑ F ∈ positiveRFactors Q, F.degreeOf 2) ≤ 25) :
    Gamma.card ≤ regularCap + 18 * chainStage.regularCountCap +
      partialSingular7.countCap + tailSingular.countCap := by
  exact residual_card_le_fixed_stop Q T hQ selected Gamma
    25 7 regularCap chainStage.regularCountCap tailSingular.countCap
    partialSingular7.countCap hQsolution hTsolution hregular hrfree
    hfactorLow hfactorHigh hdegree
    (by rw [tailSingular_exact, chainStage_exact]; decide)
    partialSingular7_le_chain target25_stop7_low_certificate

end
end ProximityPrize.SubmissionLower.LocatorDerivativeChainPartial
