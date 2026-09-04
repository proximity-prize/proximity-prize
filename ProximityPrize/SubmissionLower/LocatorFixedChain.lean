import ProximityPrize.SubmissionLower.LocatorDerivativeChain

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedChain. -/
section PackedLocator_LocatorFixedChain
/-!
# Derivative chain on the fixed stage

`LocatorDerivativeChain.residual_chain_count_le` counts the seeds of a
polynomial `Q` by its regular seeds (through a coprime partner `T`), the
derivative-chain pairs `(∂_R^j F, F)` of its positive-slope factors, and the
R-free tails.  On the fixed stage the regular seeds of the common divisor `H`
are already charged by the phase certificate through
`LocatorFixedConsumer.initial_A_regularSeeds_sum_le`, so this file restates that
lemma with `T := Q` and the regular block replaced by a hypothesis: no second
polynomial of the selected pair is needed.  The chain pairs are coprime by the
R-degree drop (`isRelPrime_dR`) and, as in `chainSeeds_card_le`, the
differentiated left factor only needs slope `s - 1`; the tails use
`card_le_regular_sum_add_singular J J`.  The only new mathematics is the
inclusion `regularPairSeeds Q Q ⊆ regularSeeds Q`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135
  RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 RCN140 LocatorDerivativeChain

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- With `T := Q`, the regular pair seeds of `(Q, Q)` are the regular seeds of the
factors of `Q` (RCN140.regularSeeds, the set the grid bounds by `bound`). -/
theorem regularPairSeeds_self_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (F : RegularIndex Q) :
    regularPairSeeds Q Q selected Gamma F ⊆ regularSeeds Q selected Gamma F := by
  intro γ hγ
  simp only [regularPairSeeds, regularSeeds, Finset.mem_filter] at hγ ⊢
  exact ⟨hγ.1, hγ.2.1⟩

/-- `residual_chain_count_le` (`LocatorDerivativeChain`) with `T := Q`: the regular seeds are charged to `bound` by hypothesis (the grid), the chain seeds
to `(s-1)*Pc`, the tails and R-free seeds to `(s+1)*S`.  No coprime partner from the
selected pair is needed: the chain pairs `(∂_R^j F, F)` are coprime by the R-degree drop
(`isRelPrime_dR`), and the tails/rfree parts use `card_le_regular_sum_add_singular J J`. -/
theorem fixed_chain_count_le
    (Pc : UnequalParameters) (S : TightParameters) (bound : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w) (hp : 1 < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hcgap : 0 < Pc.gap) (hcY : (D - 1) / w ≤ Pc.leftY) (hcR : s - 1 ≤ Pc.leftR) (hcZ : L ≤ Pc.leftZ)
    (hcY' : (D - 1) / w ≤ Pc.rightY) (hcR' : s ≤ Pc.rightR) (hcZ' : L ≤ Pc.rightZ)
    (hcleftR : 1 ≤ Pc.leftR) (hcleftYSmall : Pc.leftY < p) (hcleftRSmall : Pc.leftR < p)
    (hcleftZSmall : Pc.leftZ < p) (hcmixedYSmall : Pc.mixedCost.y < p)
    (hcmixedRSmall : Pc.mixedCost.r < p) (hcmixedZSmall : Pc.mixedCost.z < p)
    (hSD : S.D = D) (hSw : S.w = w) (hSL : S.L = L) (hSs : S.s = 1)
    (hSchar : S.w < p) (hSDw : S.w < S.kappa * S.D) (hSj : 1 ≤ S.algebraicCap)
    (hSY : S.implicitYCap < p) (hSZ : S.algebraicCap < p)
    (hSmixed : 2 * S.implicitYCap * S.algebraicCap < p) (hSwa : S.w < S.a) (hSan : S.a ≤ S.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodesC : nodes.card = Pc.n) (hnodesS : nodes.card = S.n)
    (hCw : 1 ≤ Pc.w) (hCchar : Pc.w < p) (hCwa : Pc.w < Pc.a) (hCan : Pc.a ≤ Pc.n)
    (hdegreeC : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ Pc.w)
    (hdegreeS : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ S.w)
    (hagreementC : ∀ γ ∈ Gamma, Pc.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementS : ∀ γ ∈ Gamma, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencilC : NoLargeSelectedPencil selected Gamma Pc.w Pc.errors)
    (hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hregular : (∑ F : RegularIndex Q, (regularSeeds Q selected Gamma F).card) ≤ bound) :
    Gamma.card ≤ bound + (s - 1) * Pc.regularCountCap + (s + 1) * S.countCap := by
  classical
  -- cover with T := Q  (LocatorDerivativeChain.cover)
  have hRcap : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s := fun F hF =>
    degreeOf_R_le_of_mem_box F D w L s (directFactor_data Q F hQ D w L s hbox hF).2.2
  have hcover := cover Q Q hQ p s hsmall hRcap selected Gamma hQsolution hQsolution
  -- regular seeds: the grid
  have hA : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q Q selected Gamma F).card ≤ bound := by
    calc (Finset.univ.biUnion fun F : RegularIndex Q =>
          regularPairSeeds Q Q selected Gamma F).card
        ≤ ∑ F : RegularIndex Q, (regularPairSeeds Q Q selected Gamma F).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ F : RegularIndex Q, (regularSeeds Q selected Gamma F).card :=
          Finset.sum_le_sum fun F _ =>
            Finset.card_le_card (regularPairSeeds_self_subset Q selected Gamma F)
      _ ≤ bound := hregular
  -- chain seeds  (LocatorDerivativeChain.residual_chain_count_le, verbatim)
  have hchain : ∀ F ∈ positiveRFactors Q, ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤ Pc.regularCountCap := by
    intro F hF j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    exact chainSeeds_card_le Pc Q F hQ hF j hj1 hjm.le D w L s p hsmall hw hbox hcgap
      hcY hcR hcZ hcY' hcR' hcZ' hcleftR hcleftYSmall hcleftRSmall hcleftZSmall
      hcmixedYSmall hcmixedRSmall hcmixedZSmall selected Gamma nodes x u0 u1 hinj hnodesC
      hCw hCchar hCwa hCan hdegreeC hagreementC hnoPencilC
  -- tail seeds  (verbatim)
  have htail : ∀ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card ≤ S.countCap := by
    intro F hF
    obtain ⟨hFirr, hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hF
    have hFsmall : F.degreeOf 2 < p := by
      have := degreeOf_R_le_of_mem_box F D w L s hFbox
      omega
    have hJ : dR (chainLength F) F ≠ 0 := dR_ne_zero F hFirr.ne_zero p hFsmall _ le_rfl
    have hJbox : dR (chainLength F) F ∈ globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s (dR_mem_box _ F D w L s hFbox) (chainLength_spec F)
    refine rfree_seed_count_le S _ hJ p hJbox (chainLength_spec F) hSs hp (by omega) hSchar
      hSDw hSj hSY hSZ hSmixed hSwa hSan selected (tailSeeds F selected Gamma) nodes x u0 u1
      hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ; exact hdegreeS γ (tailSeeds_subset F selected Gamma hγ)
    · intro γ hγ; exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ; exact hagreementS γ (tailSeeds_subset F selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (tailSeeds_subset F selected Gamma) hnoPencilS
  -- R-free seeds  (verbatim)
  have hrfree : (rfreeSeeds Q selected Gamma).card ≤ S.countCap := by
    have hJ := rfreeProduct_ne_zero Q hQ
    have hJbox : rfreeProduct Q ∈ globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s
        (mem_globalCoefficientBox_of_dvd _ Q D w L s hQ (rfreeProduct_dvd Q hQ) hbox)
        (rfreeProduct_R_degree Q)
    refine rfree_seed_count_le S _ hJ p hJbox (rfreeProduct_R_degree Q) hSs hp (by omega)
      hSchar hSDw hSj hSY hSZ hSmixed hSwa hSan selected (rfreeSeeds Q selected Gamma) nodes
      x u0 u1 hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ; exact hdegreeS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · intro γ hγ; exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ; exact hagreementS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (rfreeSeeds_subset Q selected Gamma) hnoPencilS
  -- budgets  (verbatim)
  obtain ⟨hsumChain, hcardPos⟩ := sum_chainLength_sub_one_le Q hQ D w L s (by omega) hs hbox
  have hB : ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      (s - 1) * Pc.regularCountCap := by
    calc ((positiveRFactors Q).biUnion fun F =>
          (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card
        ≤ ∑ F ∈ positiveRFactors Q,
            ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ F ∈ positiveRFactors Q, ∑ j ∈ Finset.Ico 1 (chainLength F),
            (chainSeeds F j selected Gamma).card :=
          Finset.sum_le_sum fun F _ => Finset.card_biUnion_le
      _ ≤ ∑ F ∈ positiveRFactors Q, ∑ _j ∈ Finset.Ico 1 (chainLength F), Pc.regularCountCap :=
          Finset.sum_le_sum fun F hF => Finset.sum_le_sum fun j hj => hchain F hF j hj
      _ = ∑ F ∈ positiveRFactors Q, (chainLength F - 1) * Pc.regularCountCap := by
          apply Finset.sum_congr rfl
          intro F _
          simp [Finset.sum_const, Nat.card_Ico]
      _ = (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) * Pc.regularCountCap := by
          rw [Finset.sum_mul]
      _ ≤ (s - 1) * Pc.regularCountCap := Nat.mul_le_mul_right _ hsumChain
  have hC : ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card ≤
      s * S.countCap := by
    calc ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card
        ≤ ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
      _ ≤ ∑ _F ∈ positiveRFactors Q, S.countCap := Finset.sum_le_sum fun F hF => htail F hF
      _ = (positiveRFactors Q).card * S.countCap := by simp [Finset.sum_const]
      _ ≤ s * S.countCap := Nat.mul_le_mul_right _ hcardPos
  have hunion := Finset.card_le_card hcover
  have h1 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q Q selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) ∪
      ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma))
    (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q Q selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma))
    ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma)
  have h3 := Finset.card_union_le
    (Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q Q selected Gamma F)
    ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma)
  have hfinal : (s + 1) * S.countCap = s * S.countCap + S.countCap := by ring
  omega

end

end ProximityPrize.SubmissionLower.LocatorFixedChain
end PackedLocator_LocatorFixedChain

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier54 : True := by trivial
end ProximityPrize.SubmissionLower

