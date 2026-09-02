import ProximityPrize.SubmissionLower.LocatorDerivativeChain

/-!
# Joint terminal accounting for the derivative chain

The original derivative-chain bound separately maximizes the number of
nonterminal chain stages and the number of positive-`R` factors.  Both are
paid from the same `R`-degree budget.  This module keeps that budget joint.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeChainJoint

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318
  RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243
open LocatorDerivativeChain

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- The chain stages and terminal factors consume one common degree budget. -/
theorem sum_chainLength_sub_one_add_card_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s : ℕ) (hw : 0 < w)
    (hbox : Q ∈ globalCoefficientBox K D w L s) :
    (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) +
        (positiveRFactors Q).card ≤ s := by
  classical
  have hbudget := (directFactor_input_budgets Q hQ D w L s hw hbox).2.1
  calc
    (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) +
          (positiveRFactors Q).card =
        ∑ F ∈ positiveRFactors Q, ((chainLength F - 1) + 1) := by
          rw [Finset.sum_add_distrib]
          simp
    _ ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 := by
      apply Finset.sum_le_sum
      intro F hF
      have hpos : 1 ≤ F.degreeOf 2 :=
        (positiveRFactors_spec Q F hF).2.2
      have hlen := chainLength_le F
      omega
    _ ≤ s := hbudget

private theorem joint_scalar_bound
    (a b s chain terminal : ℕ)
    (hab : a + b ≤ s) (hb : 1 ≤ b) (htc : terminal ≤ chain) :
    a * chain + b * terminal ≤ (s - 1) * chain + terminal := by
  have hb_split : b = (b - 1) + 1 := by omega
  have hab' : a + (b - 1) ≤ s - 1 := by omega
  have hbmul : b * terminal = (b - 1) * terminal + terminal := by
    calc
      b * terminal = ((b - 1) + 1) * terminal := by rw [← hb_split]
      _ = (b - 1) * terminal + terminal := by ring
  calc
    a * chain + b * terminal =
        a * chain + (b - 1) * terminal + terminal := by
      simpa only [add_assoc] using congrArg (fun z => a * chain + z) hbmul
    _ ≤ a * chain + (b - 1) * chain + terminal := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left (b - 1) htc) _) _
    _ = (a + (b - 1)) * chain + terminal := by ring
    _ ≤ (s - 1) * chain + terminal := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right chain hab') _

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

/-- `residual_chain_count_le` with the chain-stage and terminal-factor
budgets aggregated jointly.  When the terminal cap is no larger than the
chain cap, the positive-slope part costs only
`(s - 1) * chainCap + terminalCap`; the separate `rfreeProduct` costs one
more terminal cap. -/
theorem residual_chain_count_le_joint
    (P Pc : UnequalParameters) (S : TightParameters)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (D w L s p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w) (hp : 1 < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hgap : 0 < P.gap) (hY : (D - 1) / w ≤ P.leftY)
    (hR : s ≤ P.leftR) (hZ : L ≤ P.leftZ)
    (hTY : T.degreeOf 1 ≤ P.rightY) (hTR : T.degreeOf 2 ≤ P.rightR)
    (hTZ : T.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR) (hleftYSmall : P.leftY < p)
    (hleftRSmall : P.leftR < p) (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p) (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (hcgap : 0 < Pc.gap) (hcY : (D - 1) / w ≤ Pc.leftY)
    (hcR : s ≤ Pc.leftR) (hcZ : L ≤ Pc.leftZ)
    (hcY' : (D - 1) / w ≤ Pc.rightY) (hcR' : s ≤ Pc.rightR)
    (hcZ' : L ≤ Pc.rightZ) (hcleftR : 1 ≤ Pc.leftR)
    (hcleftYSmall : Pc.leftY < p) (hcleftRSmall : Pc.leftR < p)
    (hcleftZSmall : Pc.leftZ < p) (hcmixedYSmall : Pc.mixedCost.y < p)
    (hcmixedRSmall : Pc.mixedCost.r < p) (hcmixedZSmall : Pc.mixedCost.z < p)
    (hSD : S.D = D) (hSw : S.w = w) (hSL : S.L = L) (hSs : S.s = 1)
    (hSchar : S.w < p) (hSDw : S.w < S.kappa * S.D)
    (hSj : 1 ≤ S.algebraicCap) (hSY : S.implicitYCap < p)
    (hSZ : S.algebraicCap < p)
    (hSmixed : 2 * S.implicitYCap * S.algebraicCap < p)
    (hSwa : S.w < S.a) (hSan : S.a ≤ S.n)
    (hterminal : S.countCap ≤ Pc.regularCountCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodesP : nodes.card = P.n) (hnodesC : nodes.card = Pc.n)
    (hnodesS : nodes.card = S.n)
    (hPw : 1 ≤ P.w) (hPchar : P.w < p) (hPwa : P.w < P.a)
    (hPan : P.a ≤ P.n) (hCw : 1 ≤ Pc.w) (hCchar : Pc.w < p)
    (hCwa : Pc.w < Pc.a) (hCan : Pc.a ≤ Pc.n)
    (hdegreeP : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ P.w)
    (hdegreeC : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ Pc.w)
    (hdegreeS : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ S.w)
    (hagreementP : ∀ γ ∈ Gamma, P.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementC : ∀ γ ∈ Gamma, Pc.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementS : ∀ γ ∈ Gamma, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencilP : NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hnoPencilC : NoLargeSelectedPencil selected Gamma Pc.w Pc.errors)
    (hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0) :
    Gamma.card ≤ P.regularCountCap + (s - 1) * Pc.regularCountCap +
      2 * S.countCap := by
  classical
  have hregular := all_regularPairSeeds_bound P Q T hQ hrel D w L s p hbox hw
    hY hR hZ hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u0 u1 hinj
    hnodesP hPw hPchar hPwa hPan hdegreeP hagreementP hnoPencilP
  have hregSum := sum_regular_counts_bound P Q T selected Gamma
    (regularVector_budgets P Q hQ D w L s (by omega) hbox hY hR hZ) hregular
  have hregCap : (∑ F : RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card) ≤ P.regularCountCap :=
    P.regular_count_le _ hgap hregSum
  have hRcap : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s := fun F hF =>
    degreeOf_R_le_of_mem_box F D w L s
      (directFactor_data Q F hQ D w L s hbox hF).2.2
  have hcover := cover Q T hQ p s hsmall hRcap selected Gamma hQsolution hTsolution
  have hchain : ∀ F ∈ positiveRFactors Q,
      ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤ Pc.regularCountCap := by
    intro F hF j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    exact chainSeeds_card_le Pc Q F hQ hF j hj1 hjm.le D w L s p hsmall hw
      hbox hcgap hcY hcR hcZ hcY' hcR' hcZ' hcleftR hcleftYSmall
      hcleftRSmall hcleftZSmall hcmixedYSmall hcmixedRSmall hcmixedZSmall
      selected Gamma nodes x u0 u1 hinj hnodesC hCw hCchar hCwa hCan
      hdegreeC hagreementC hnoPencilC
  have htail : ∀ F ∈ positiveRFactors Q,
      (tailSeeds F selected Gamma).card ≤ S.countCap := by
    intro F hF
    obtain ⟨hFirr, _hFpos, hFbox⟩ := directFactor_data Q F hQ D w L s hbox hF
    have hFsmall : F.degreeOf 2 < p := by
      have := degreeOf_R_le_of_mem_box F D w L s hFbox
      omega
    have hJ : dR (chainLength F) F ≠ 0 :=
      dR_ne_zero F hFirr.ne_zero p hFsmall _ le_rfl
    have hJbox : dR (chainLength F) F ∈
        globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s (dR_mem_box _ F D w L s hFbox)
        (chainLength_spec F)
    refine rfree_seed_count_le S _ hJ p hJbox (chainLength_spec F) hSs hp
      (by omega) hSchar hSDw hSj hSY hSZ hSmixed hSwa hSan selected
      (tailSeeds F selected Gamma) nodes x u0 u1 hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ
      exact hdegreeS γ (tailSeeds_subset F selected Gamma hγ)
    · intro γ hγ
      exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ
      exact hagreementS γ (tailSeeds_subset F selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (tailSeeds_subset F selected Gamma) hnoPencilS
  have hrfree : (rfreeSeeds Q selected Gamma).card ≤ S.countCap := by
    have hJ := rfreeProduct_ne_zero Q hQ
    have hJbox : rfreeProduct Q ∈ globalCoefficientBox K S.D S.w S.L S.s := by
      rw [hSD, hSw, hSL, hSs]
      exact mem_box_slope_one _ D w L s
        (mem_globalCoefficientBox_of_dvd _ Q D w L s hQ
          (rfreeProduct_dvd Q hQ) hbox) (rfreeProduct_R_degree Q)
    refine rfree_seed_count_le S _ hJ p hJbox (rfreeProduct_R_degree Q) hSs hp
      (by omega) hSchar hSDw hSj hSY hSZ hSmixed hSwa hSan selected
      (rfreeSeeds Q selected Gamma) nodes x u0 u1 hinj hnodesS ?_ ?_ ?_ ?_
    · intro γ hγ
      exact hdegreeS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · intro γ hγ
      exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ
      exact hagreementS γ (rfreeSeeds_subset Q selected Gamma hγ)
    · exact noLargeSelectedPencil_mono selected Gamma _ S.w S.errors
        (rfreeSeeds_subset Q selected Gamma) hnoPencilS
  have hA : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F).card ≤ P.regularCountCap :=
    Finset.card_biUnion_le.trans hregCap
  let chainPart := (positiveRFactors Q).biUnion fun F =>
    (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma
  let tailPart :=
    (positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma
  have hChainCard : chainPart.card ≤
      (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) *
        Pc.regularCountCap := by
    calc
      chainPart.card ≤ ∑ F ∈ positiveRFactors Q,
          ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
            chainSeeds F j selected Gamma).card := Finset.card_biUnion_le
      _ ≤ ∑ F ∈ positiveRFactors Q,
          ∑ j ∈ Finset.Ico 1 (chainLength F),
            (chainSeeds F j selected Gamma).card :=
        Finset.sum_le_sum fun F _ => Finset.card_biUnion_le
      _ ≤ ∑ F ∈ positiveRFactors Q,
          ∑ _j ∈ Finset.Ico 1 (chainLength F), Pc.regularCountCap :=
        Finset.sum_le_sum fun F hF =>
          Finset.sum_le_sum fun j hj => hchain F hF j hj
      _ = ∑ F ∈ positiveRFactors Q,
          (chainLength F - 1) * Pc.regularCountCap := by
        apply Finset.sum_congr rfl
        intro F _
        simp [Finset.sum_const, Nat.card_Ico]
      _ = (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) *
          Pc.regularCountCap := by rw [Finset.sum_mul]
  have hTailCard : tailPart.card ≤
      (positiveRFactors Q).card * S.countCap := by
    calc
      tailPart.card ≤ ∑ F ∈ positiveRFactors Q,
          (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
      _ ≤ ∑ _F ∈ positiveRFactors Q, S.countCap :=
        Finset.sum_le_sum fun F hF => htail F hF
      _ = (positiveRFactors Q).card * S.countCap := by
        simp [Finset.sum_const]
  have hBC : (chainPart ∪ tailPart).card ≤
      (s - 1) * Pc.regularCountCap + S.countCap := by
    by_cases hempty : (positiveRFactors Q).card = 0
    · rw [Finset.card_eq_zero] at hempty
      simp [chainPart, tailPart, hempty]
    · have hcardPos : 1 ≤ (positiveRFactors Q).card :=
        Nat.pos_of_ne_zero hempty
      have hjoint := sum_chainLength_sub_one_add_card_le Q hQ D w L s
        (by omega) hbox
      calc
        (chainPart ∪ tailPart).card ≤ chainPart.card + tailPart.card :=
          Finset.card_union_le _ _
        _ ≤
            (∑ F ∈ positiveRFactors Q, (chainLength F - 1)) *
                Pc.regularCountCap +
              (positiveRFactors Q).card * S.countCap :=
          Nat.add_le_add hChainCard hTailCard
        _ ≤ (s - 1) * Pc.regularCountCap + S.countCap :=
          joint_scalar_bound _ _ _ _ _ hjoint hcardPos hterminal
  let regularPart := Finset.univ.biUnion fun F : RegularIndex Q =>
    regularPairSeeds Q T selected Gamma F
  have hcover' : Gamma ⊆
      (regularPart ∪ (chainPart ∪ tailPart)) ∪ rfreeSeeds Q selected Gamma := by
    simpa only [regularPart, chainPart, tailPart, Finset.union_assoc] using hcover
  have hunion := Finset.card_le_card hcover'
  have h1 := Finset.card_union_le
    (regularPart ∪ (chainPart ∪ tailPart)) (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le regularPart (chainPart ∪ tailPart)
  have hA' : regularPart.card ≤ P.regularCountCap := by
    simpa only [regularPart] using hA
  omega

end
end ProximityPrize.SubmissionLower.LocatorDerivativeChainJoint
