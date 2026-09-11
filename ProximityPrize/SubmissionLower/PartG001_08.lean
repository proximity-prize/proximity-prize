import ProximityPrize.SubmissionLower.PartG001_07
section Compact_PackedLocatorTail
section PackedLocator_LocatorFixedChain
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


/-- `residual_chain_count_le` (`LocatorDerivativeChain`) with `T := Q`: the regular seeds are charged to `bound` by hypothesis (the grid), the chain seeds
to `(s-1)*Pc`, the tails and R-free seeds to `(s+1)*S`.  No coprime partner from the
selected pair is needed: the chain pairs `(∂_R^j F, F)` are coprime by the R-degree drop
(`isRelPrime_dR`), and the tails/rfree parts use `card_le_regular_sum_add_singular J J`. -/
theorem fixed_chain_count_le
    (Pc : ℕ → UnequalParameters) (S : TightParameters) (bound : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w) (hp : 1 < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hcmono : Monotone (fun t => (Pc t).regularCountCap))
    (hcgap : ∀ t, 0 < (Pc t).gap) (hcY : ∀ t, (D - 1) / w ≤ (Pc t).leftY)
    (hcR : ∀ t, t ≤ s → t ≤ (Pc t).leftR) (hcZ : ∀ t, L ≤ (Pc t).leftZ)
    (hcY' : ∀ t, (D - 1) / w ≤ (Pc t).rightY) (hcR' : ∀ t, s ≤ (Pc t).rightR)
    (hcZ' : ∀ t, L ≤ (Pc t).rightZ)
    (hcleftR : ∀ t, 1 ≤ (Pc t).leftR) (hcleftYSmall : ∀ t, (Pc t).leftY < p)
    (hcleftRSmall : ∀ t, (Pc t).leftR < p)
    (hcleftZSmall : ∀ t, (Pc t).leftZ < p) (hcmixedYSmall : ∀ t, (Pc t).mixedCost.y < p)
    (hcmixedRSmall : ∀ t, (Pc t).mixedCost.r < p) (hcmixedZSmall : ∀ t, (Pc t).mixedCost.z < p)
    (htailLe : S.countCap ≤ (Pc 1).regularCountCap)
    (hSD : S.D = D) (hSw : S.w = w) (hSL : S.L = L) (hSs : S.s = 1)
    (hSchar : S.w < p) (hSDw : S.w < S.kappa * S.D) (hSj : 1 ≤ S.algebraicCap)
    (hSY : S.implicitYCap < p) (hSZ : S.algebraicCap < p)
    (hSmixed : 2 * S.implicitYCap * S.algebraicCap < p) (hSwa : S.w < S.a) (hSan : S.a ≤ S.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodesC : ∀ t, nodes.card = (Pc t).n) (hnodesS : nodes.card = S.n)
    (hCw : ∀ t, 1 ≤ (Pc t).w) (hCchar : ∀ t, (Pc t).w < p) (hCwa : ∀ t, (Pc t).w < (Pc t).a)
    (hCan : ∀ t, (Pc t).a ≤ (Pc t).n)
    (hdegreeC : ∀ t, ∀ γ ∈ Gamma, (selected γ).natDegree ≤ (Pc t).w)
    (hdegreeS : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ S.w)
    (hagreementC : ∀ t, ∀ γ ∈ Gamma, (Pc t).a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementS : ∀ γ ∈ Gamma, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencilC : ∀ t, NoLargeSelectedPencil selected Gamma (Pc t).w (Pc t).errors)
    (hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hregular : (∑ F : RegularIndex Q, (regularSeeds Q selected Gamma F).card) ≤ bound) :
    Gamma.card ≤ bound
      + ChainAmort.capSum (fun t => (Pc t).regularCountCap) s + 2 * S.countCap := by
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
      (chainSeeds F j selected Gamma).card ≤ (Pc (F.degreeOf 2 - j)).regularCountCap := by
    intro F hF j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    have hFd : F.degreeOf 2 ≤ s :=
      degreeOf_R_le_of_mem_box F D w L s (directFactor_data Q F hQ D w L s hbox hF).2.2
    exact chainSeeds_card_le (Pc (F.degreeOf 2 - j)) Q F hQ hF j hj1 hjm.le D w L s p hsmall hw
      hbox (hcgap _) (hcY _) (hcR _ (by omega)) (hcZ _) (hcY' _) (hcR' _) (hcZ' _) (hcleftR _)
      (hcleftYSmall _) (hcleftRSmall _) (hcleftZSmall _)
      (hcmixedYSmall _) (hcmixedRSmall _) (hcmixedZSmall _)
      selected Gamma nodes x u0 u1 hinj (hnodesC _)
      (hCw _) (hCchar _) (hCwa _) (hCan _) (hdegreeC _) (hagreementC _) (hnoPencilC _)
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
  have hdeg : (∑ F ∈ positiveRFactors Q, F.degreeOf 2) ≤ s :=
    (directFactor_input_budgets Q hQ D w L s (by omega) hbox).2.1
  have hpos1 : ∀ F ∈ positiveRFactors Q, 1 ≤ F.degreeOf 2 :=
    fun F hF => (positiveRFactors_spec Q F hF).2.2
  have hrow : ∀ F ∈ positiveRFactors Q,
      ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card
        + (tailSeeds F selected Gamma).card ≤
      ChainAmort.capSumT (fun t => (Pc t).regularCountCap) S.countCap (F.degreeOf 2) := by
    intro F hF
    have h1 : ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
        chainSeeds F j selected Gamma).card ≤
        ∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card :=
      Finset.card_biUnion_le
    have h2 : ∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card ≤
        ChainAmort.capSum (fun t => (Pc t).regularCountCap) (F.degreeOf 2) :=
      le_trans (Finset.sum_le_sum fun j hj => hchain F hF j hj)
        (ChainAmort.chain_row_le (fun t => (Pc t).regularCountCap)
          (F.degreeOf 2) (chainLength F) (chainLength_le F))
    have h4 := htail F hF
    unfold ChainAmort.capSumT
    omega
  have hsumrow : ∑ F ∈ positiveRFactors Q,
      (((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card
        + (tailSeeds F selected Gamma).card) ≤
      ChainAmort.capSumT (fun t => (Pc t).regularCountCap) S.countCap s :=
    le_trans (Finset.sum_le_sum hrow)
      (ChainAmort.sum_capSumT_le (fun t => (Pc t).regularCountCap) hcmono S.countCap htailLe
        (positiveRFactors Q) (fun F => F.degreeOf 2) s hpos1 hdeg)
  rw [Finset.sum_add_distrib] at hsumrow
  unfold ChainAmort.capSumT at hsumrow
  have hB : ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q,
        ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
          chainSeeds F j selected Gamma).card := Finset.card_biUnion_le
  have hC : ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
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
  omega

/-- Two-group form of `fixed_chain_count_le`: the positive-`R` factors of `Q` are split by
membership in `U`; each group is charged its own amortised chain (`Pc true` / `Pc false`)
at its own total slope (`rB true` / `rB false`), and every factor's tail is charged once. -/
theorem fixed_chain_count_le_split
    (Pc : Bool → ℕ → UnequalParameters) (rB : Bool → ℕ) (S : TightParameters) (bound : ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (U : Finset (MvPolynomial (Fin 4) K)) (hU : U ⊆ positiveRFactors Q)
    (D w L s p : ℕ) [CharP K p]
    (hs : 1 ≤ s) (hsmall : s < p) (hw : 1 ≤ w) (hp : 1 < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hcmono : ∀ b, Monotone (fun t => (Pc b t).regularCountCap))
    (hcgap : ∀ b t, 0 < (Pc b t).gap)
    (hcdeg : ∀ F ∈ positiveRFactors Q, ∀ t, t ≤ F.degreeOf 2 →
      F.degreeOf 1 ≤ (Pc (decide (F ∈ U)) t).leftY ∧
      F.degreeOf 1 ≤ (Pc (decide (F ∈ U)) t).rightY ∧
      F.degreeOf 2 ≤ (Pc (decide (F ∈ U)) t).rightR ∧
      t ≤ (Pc (decide (F ∈ U)) t).leftR)
    (hcZ : ∀ b t, L ≤ (Pc b t).leftZ) (hcZ' : ∀ b t, L ≤ (Pc b t).rightZ)
    (hcleftR : ∀ b t, 1 ≤ (Pc b t).leftR)
    (hcleftYSmall : ∀ b t, (Pc b t).leftY < p) (hcleftRSmall : ∀ b t, (Pc b t).leftR < p)
    (hcleftZSmall : ∀ b t, (Pc b t).leftZ < p)
    (hcmixedYSmall : ∀ b t, (Pc b t).mixedCost.y < p)
    (hcmixedRSmall : ∀ b t, (Pc b t).mixedCost.r < p)
    (hcmixedZSmall : ∀ b t, (Pc b t).mixedCost.z < p)
    (hrU : ∑ F ∈ U, F.degreeOf 2 ≤ rB true)
    (hrR : ∑ F ∈ positiveRFactors Q \ U, F.degreeOf 2 ≤ rB false)
    (hSD : S.D = D) (hSw : S.w = w) (hSL : S.L = L) (hSs : S.s = 1)
    (hSchar : S.w < p) (hSDw : S.w < S.kappa * S.D) (hSj : 1 ≤ S.algebraicCap)
    (hSY : S.implicitYCap < p) (hSZ : S.algebraicCap < p)
    (hSmixed : 2 * S.implicitYCap * S.algebraicCap < p) (hSwa : S.w < S.a) (hSan : S.a ≤ S.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K) (hinj : Set.InjOn x nodes)
    (hnodesC : ∀ b t, nodes.card = (Pc b t).n) (hnodesS : nodes.card = S.n)
    (hCw : ∀ b t, 1 ≤ (Pc b t).w) (hCchar : ∀ b t, (Pc b t).w < p)
    (hCwa : ∀ b t, (Pc b t).w < (Pc b t).a) (hCan : ∀ b t, (Pc b t).a ≤ (Pc b t).n)
    (hdegreeC : ∀ b t, ∀ γ ∈ Gamma, (selected γ).natDegree ≤ (Pc b t).w)
    (hdegreeS : ∀ γ ∈ Gamma, (selected γ).natDegree ≤ S.w)
    (hagreementC : ∀ b t, ∀ γ ∈ Gamma, (Pc b t).a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hagreementS : ∀ γ ∈ Gamma, S.a ≤ (nodes.filter (fun i =>
      (selected γ).eval (x i) = u0 i + γ * u1 i)).card)
    (hnoPencilC : ∀ b t, NoLargeSelectedPencil selected Gamma (Pc b t).w (Pc b t).errors)
    (hnoPencilS : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hregular : (∑ F : RegularIndex Q, (regularSeeds Q selected Gamma F).card) ≤ bound) :
    Gamma.card ≤ bound
      + ChainAmort.capSum (fun t => (Pc true t).regularCountCap) (rB true)
      + ChainAmort.capSum (fun t => (Pc false t).regularCountCap) (rB false)
      + (s + 1) * S.countCap := by
  classical
  have hRcap : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s := fun F hF =>
    degreeOf_R_le_of_mem_box F D w L s (directFactor_data Q F hQ D w L s hbox hF).2.2
  have hcover := cover Q Q hQ p s hsmall hRcap selected Gamma hQsolution hQsolution
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
  have hchain : ∀ F ∈ positiveRFactors Q, ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤
        (Pc (decide (F ∈ U)) (F.degreeOf 2 - j)).regularCountCap := by
    intro F hF j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
    obtain ⟨hY, hY', hR', hL⟩ := hcdeg F hF (F.degreeOf 2 - j) (Nat.sub_le _ _)
    exact chainSeeds_card_le'
      (Pc (decide (F ∈ U)) (F.degreeOf 2 - j)) Q F hQ hF j hj1 hjm.le D w L s p hsmall hw
      hbox (hcgap _ _) hY hL (hcZ _ _) hY' hR' (hcZ' _ _) (hcleftR _ _)
      (hcleftYSmall _ _) (hcleftRSmall _ _) (hcleftZSmall _ _)
      (hcmixedYSmall _ _) (hcmixedRSmall _ _) (hcmixedZSmall _ _)
      selected Gamma nodes x u0 u1 hinj (hnodesC _ _)
      (hCw _ _) (hCchar _ _) (hCwa _ _) (hCan _ _) (hdegreeC _ _) (hagreementC _ _)
      (hnoPencilC _ _)
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
  obtain ⟨_hsumChain, hcardPos⟩ := sum_chainLength_sub_one_le Q hQ D w L s (by omega) hs hbox
  have hrow : ∀ F ∈ positiveRFactors Q,
      ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ChainAmort.capSum (fun t => (Pc (decide (F ∈ U)) t).regularCountCap) (F.degreeOf 2) := by
    intro F hF
    refine le_trans Finset.card_biUnion_le ?_
    exact le_trans (Finset.sum_le_sum fun j hj => hchain F hF j hj)
      (ChainAmort.chain_row_le (fun t => (Pc (decide (F ∈ U)) t).regularCountCap)
        (F.degreeOf 2) (chainLength F) (chainLength_le F))
  have hgroupU : ∑ F ∈ U,
      ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ChainAmort.capSum (fun t => (Pc true t).regularCountCap) (rB true) := by
    refine le_trans (Finset.sum_le_sum fun F hF => ?_)
      (ChainAmort.sum_capSum_le _ (hcmono true) U (fun F => F.degreeOf 2) (rB true) hrU)
    have h := hrow F (hU hF)
    simpa [hF] using h
  have hgroupR : ∑ F ∈ positiveRFactors Q \ U,
      ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ChainAmort.capSum (fun t => (Pc false t).regularCountCap) (rB false) := by
    refine le_trans (Finset.sum_le_sum fun F hF => ?_)
      (ChainAmort.sum_capSum_le _ (hcmono false) _ (fun F => F.degreeOf 2) (rB false) hrR)
    have hFmem := (Finset.mem_sdiff.mp hF).1
    have hFnot := (Finset.mem_sdiff.mp hF).2
    have h := hrow F hFmem
    simpa [hFnot] using h
  have hsumChainCards : ∑ F ∈ positiveRFactors Q,
      ((Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ChainAmort.capSum (fun t => (Pc true t).regularCountCap) (rB true) +
        ChainAmort.capSum (fun t => (Pc false t).regularCountCap) (rB false) := by
    rw [← Finset.sum_sdiff hU]
    omega
  have htails : ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card ≤
      s * S.countCap := by
    calc ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card
        ≤ ∑ _F ∈ positiveRFactors Q, S.countCap := Finset.sum_le_sum htail
      _ = (positiveRFactors Q).card * S.countCap := by simp
      _ ≤ s * S.countCap := Nat.mul_le_mul_right _ hcardPos
  set A := (Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q Q selected Gamma F)
    with hAdef
  set B := ((positiveRFactors Q).biUnion fun F =>
    (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) with hBdef
  set C := ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma) with hCdef
  set Dset := rfreeSeeds Q selected Gamma with hDdef
  have hB : B.card ≤ ∑ F ∈ positiveRFactors Q,
      ((Finset.Ico 1 (chainLength F)).biUnion fun j =>
        chainSeeds F j selected Gamma).card := Finset.card_biUnion_le
  have hC : C.card ≤ ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card :=
    Finset.card_biUnion_le
  have hunion : Gamma.card ≤ (A ∪ B ∪ C ∪ Dset).card := Finset.card_le_card hcover
  calc Gamma.card ≤ (A ∪ B ∪ C ∪ Dset).card := hunion
    _ ≤ (A ∪ B ∪ C).card + Dset.card := Finset.card_union_le _ _
    _ ≤ (A ∪ B).card + C.card + Dset.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ A.card + B.card + C.card + Dset.card := by
        have := Finset.card_union_le A B
        omega
    _ ≤ bound + (ChainAmort.capSum (fun t => (Pc true t).regularCountCap) (rB true) +
          ChainAmort.capSum (fun t => (Pc false t).regularCountCap) (rB false)) +
        s * S.countCap + S.countCap :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hA (hB.trans hsumChainCards))
          (hC.trans htails)) hrfree
    _ = bound + ChainAmort.capSum (fun t => (Pc true t).regularCountCap) (rB true)
          + ChainAmort.capSum (fun t => (Pc false t).regularCountCap) (rB false)
          + (s + 1) * S.countCap := by ring

end

end ProximityPrize.SubmissionLower.LocatorFixedChain
end PackedLocator_LocatorFixedChain

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedConsumer. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1. -/
section PackedLocator_LocatorHybridTailProviderC1
/-
LOCATOR HYBRID TAIL PROVIDER — C1 VARIANT.

Same architecture as `LocatorHybridTailProvider`, with the C1 trade:

  * the FLAG route (charge `mult · weightedCost hybrid`) is restricted to
    components of local multiplicity at least 6, which lets the coordinate drop
    from `cellRational + ⟨0,(w+1)/2,3·((w+1)/2)⟩` all the way to `cellRational`;
  * components of multiplicity 1..5 go through the MOVING engine at cut level
    `w + mult` (the dichotomy's `delay` satisfies `delay ≤ mult`), charging
    `weightedCost (cellRationalAt (w + mult)) + (w + mult) · movingCost`;
  * the moving term's outer factor therefore becomes `w + 5` instead of `w + 1`.

The structure `HybridTailMultiplicityProvider` and `stage_card_le_divisorBound`
are reused unchanged from `LocatorHybridTailProvider`.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

/-! ### 0. Arithmetic helpers -/

/-- `sharp_absorbs_total_C1` in the `(a, b + s)` shape used by the containment proof. -/
theorem sharp_absorbs_total_abs (a B delay mult : ℕ) (hA : 1 ≤ a + B)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * a + 2 * B + 4) * (131072 + delay) ≤
      mult * (131074 * a + 131072 * B + 2 * B + 5) := by
  have h := sharp_absorbs_total_C1 (a + B) delay mult hA hdm hm6
  have e1 : 2 * (a + B) + 4 = 2 * a + 2 * B + 4 := by ring
  have e2 : 131072 * (a + B) + 2 * (a + B) + 5 =
      131074 * a + 131072 * B + 2 * B + 5 := by ring
  rw [e1, e2] at h
  exact h

/-- The rational coordinate grows componentwise with the cut level. -/
theorem cellRationalAt_mono (t y r k l : Nat) (h : k ≤ l) :
    (cellRationalAt t y r k).zOnly ≤ (cellRationalAt t y r l).zOnly ∧
      (cellRationalAt t y r k).yz ≤ (cellRationalAt t y r l).yz ∧
      (cellRationalAt t y r k).all ≤ (cellRationalAt t y r l).all := by
  simp only [cellRationalAt_eq]
  exact ⟨by exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _,
    by exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _,
    by exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _⟩

/-! ### 1. L1 (C1) — the delayed cut lands in `mult • cellRational` for `mult ≥ 6` -/

theorem laterTail_in_hybridFlagC1
    (t y r : Nat) (hr3 : 3 ≤ r) (_hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult : ℕ) (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinateC1 t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  have hs1 : 1 ≤ cellS r := by simp only [cellS]; omega
  have hB1 : 1 ≤ cellB y r + cellS r := by omega
  have hA1 : 1 ≤ cellA t y + (cellB y r + cellS r) := by omega
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (w + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  have hallV : (sharpResidualAgreementFlag (cellSupport t y r)
      (w + 1 + delay)).all = (2 * cellS r + 3) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
  have hysV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * (cellB y r + cellS r) + 4) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have htotV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).zOnly +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * cellA t y + 2 * (cellB y r + cellS r) + 4) *
        (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have hhallV : (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3)) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_all, w]
  have hhysV : (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_yz, nsmul_all, w]
    ring
  have hhtotV : (mult • cellHybridCoordinateC1 t y r).zOnly +
      (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_zOnly, nsmul_yz, nsmul_all, w]
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      sharp_absorbs_all_C1 (cellS r) delay mult hs1 hdm hm6)
  · exact (hysV ▸ hys).trans (hhysV ▸
      sharp_absorbs_ysall_C1 (cellB y r + cellS r) delay mult hB1 hdm hm6)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      sharp_absorbs_total_abs (cellA t y) (cellB y r + cellS r) delay mult
        hA1 hdm hm6)

/-! ### 2. L2 (C1) — the moving count at an arbitrary delay -/

set_option maxHeartbeats 20000000 in
theorem component_moving_card_le_delay
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y) (_hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (delay : ℕ) (hd : 1 ≤ delay)
    (hproper : globalTailCut (polynomialEmbedding K) S.F
      (w + 1 + delay) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + delay) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) := by
  classical
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hR : S.F.degreeOf 2 ≤ cellS r + 2 := by
    have h := Hsupport.coordinate_bounds.2.1
    simpa only [cellSupport, cellS, RCN198.support] using h
  have hYR : wt ![0, 1, 1, 0] S.F ≤ cellB y r + cellS r + 3 := by
    have h := Hsupport.ys_weight
    simpa only [residualYSWeights, cellSupport, cellB, cellS, RCN198.support] using h
  have hAll : wt ![0, 1, 1, 1] S.F ≤ cellA t y + cellB y r + cellS r + 3 := by
    have h := Hsupport.total_weight
    simpa only [residualTotalWeights, cellSupport, cellA, cellB, cellS,
      RCN198.support] using h
  obtain ⟨Bc, cf, heq, hcoeff, hclass⟩ :=
    globalTailCut_certificate (polynomialEmbedding K)
      (cellA t y) (cellB y r) (cellS r) S.F hR hYR hAll
      (w + delay) (by omega)
  rw [show w + delay + 1 = w + 1 + delay from by omega] at heq
  have hHrw : surfaceMap (polynomialEmbedding K) (polyH K S.F) =
      regularitySurface (polynomialEmbedding K) S.F := rfl
  rw [hHrw] at heq
  have hA : filteredCut
      (w + delay) Bc
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)) ∉ C.1 :=
    heq ▸ hproper
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (filteredCut (w + delay) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
      (budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + delay) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost)) :=
    budget.zero_le base (cellA t y) (cellB y r) (cellS r) (w + delay)
      (center (cellA t y) (cellB y r) (cellS r)) Bc cf hHnot hA hcoeff hclass
  let seeds := componentSeeds (GenericField K) S.G
    (globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C
  let pts : Finset (Fin 3 → GenericField K) :=
    seeds.image (selectedPoint (polynomialEmbedding K) S.selected)
  have hprime : ∀ v ∈ pts,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
  have hHne : ∀ v ∈ pts, MvPolynomial.aeval v
      (regularitySurface (polynomialEmbedding K) S.F) ≠ 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    show MvPolynomial.eval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (regularitySurface (polynomialEmbedding K) S.F) ≠ 0
    exact (selectedPoint_evaluation (polynomialEmbedding K) S.selected gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.F)).symm ▸ S.regular gamma hGamma
  have hAzero : ∀ v ∈ pts, MvPolynomial.aeval v
      (filteredCut (w + delay) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F))) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    have hz : MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (globalTailCut (polynomialEmbedding K) S.F
          (w + 1 + delay)) = 0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
        S.selected gamma w (w + 1 + delay)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact heq ▸ hz
  have hbound : pts.card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + delay) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega

/-! ### 3. The C1 provider from a local DVR family -/


end
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
end PackedLocator_LocatorHybridTailProviderC1

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTransportC2. -/
section PackedLocator_LocatorHybridTransportC2
/-
C2 FOUNDATION: transporting the unit family across a congruent cut, and the
moving-budget existence at an ARBITRARY first-tail flag.

C2 replaces the sharp first tail `sharpResidualAgreementFlag (support a b s) (w+1)`
by the reduced one `reducedResidualAgreementFlag (support a b s) (w+1)`, which is
strictly `Below` it (same `yz + all` and total, `all` smaller by `w + 1`).  The
reduced geometry lives over the components of `reducedFirstCut`, so it has to be
transported to the components of `globalTailCut (w+1)`.

`PrimeFlagBudgetFamily.ofCongruentCut` (B1.lean:108) already transports the
budget family, and `RCN335` uses it for the certificate.  What is missing for the
hybrid moving route is the transport of the whole `AdaptiveUnitProjectionFamily`,
because `exists_moving_pole_budget_family` needs the projections themselves in
order to produce a `MovingPoleBudget` whose costs agree with the family's.

§1 supplies that transport.  Every field of `AdaptiveUnitProjectionFamily`
mentions the component only through `C.1`, and `regularComponentEquiv h C` has
`.1 = C.1` definitionally, so the transport is a precomposition.

§2 generalises `RCN085.exists_firstTail_cut_budgets` (J3.lean:13) in the
first-tail flag.  J3 hard-codes the sharp flag purely to state the three
`z / yz / all` sum bounds through `mixed_sharp_le_padded`; the hybrid route uses
only the cost equalities and the moving sum, both of which are flag-agnostic.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridTransportC2
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086 RCN085
open RCN066 RCN135 RCN159 RCN074 RCN237 RCN244 RCN327 RCN263 RCN206 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

/-! ### 1. Transport of a unit family across a congruent cut -/

section Transport
variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
  {G T T' H : MvPolynomial (Fin 3) Omega}

/-- An `AdaptiveUnitProjectionFamily` over the components of `T'` transports to
the components of `T` whenever `G ∣ T - T'`, for any choice of `base`.  All the
structure's fields see the component only through `C.1`, and the equivalence
preserves `C.1` definitionally. -/
def unitFamilyOfCongruentCut (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1) :
    AdaptiveUnitProjectionFamily base p q where
  zProjection C := U.zProjection (regularComponentEquiv h C)
  yzProjection C := U.yzProjection (regularComponentEquiv h C)
  allProjection C := U.allProjection (regularComponentEquiv h C)
  zValue C := U.zValue (regularComponentEquiv h C)
  allTranscendental C := U.allTranscendental (regularComponentEquiv h C)
  zPole_eq C := U.zPole_eq (regularComponentEquiv h C)
  yzPole_eq C := U.yzPole_eq (regularComponentEquiv h C)
  allPole_eq C := U.allPole_eq (regularComponentEquiv h C)
  sum_zDegree_le := by
    refine Eq.trans_le ?_ U.sum_zDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_yzDegree_le := by
    refine Eq.trans_le ?_ U.sum_yzDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_allDegree_le := by
    refine Eq.trans_le ?_ U.sum_allDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)

/-- The transported unit family carries exactly the costs of the transported
budget family, so the hybrid provider can use the two interchangeably. -/
theorem unitFamilyOfCongruentCut_costs (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1)
    (C : RegularComponent Omega G T H) :
    (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.zCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).zCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.yzCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).yzCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.allCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).allCost C := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end Transport

/-! ### 2. Moving budgets at an arbitrary first-tail flag -/

section Budgets
variable {K Ω E : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
  [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E]

/-- `RCN085.exists_firstTail_cut_budgets` with the first-tail flag left free.
Only the cost equalities and the moving sum are produced; the three `z / yz /
all` sum bounds of J3 are exactly the parts that needed the sharp flag, and the
hybrid route never uses them. -/
theorem exists_firstTail_moving_budgets
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Ω) (a b s w : ℕ) (hw : 1 ≤ w)
    (hT : T = globalTailCut φ F (w + 1))
    (hF : ResidualSupportData (support a b s) F) (flag : FlagDegree)
    (hG : G ≠ 0) (hdiv : G ∣ surfaceMap φ F) (hGflag : PolynomialInFlag flag G)
    (base : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      SeparableLiteralCoordinate C.1)
    (tailFlag : FlagDegree)
    (unit : AdaptiveUnitProjectionFamily base flag tailFlag)
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < pchar) :
    ∃ budget : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
      (∀ C, (budget C).zCost = unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost = unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost = unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (∑ C, (budget C).movingCost) ≤ flagMixed flag
        (RCN206.fiberFlag a b s)
        (center a b s + (w + 1) • RCN206.surfaceFlag a b s) := by
  classical
  obtain ⟨coeffs, cflags, heq, hcoeff, hclass⟩ := globalTailCut_certificate
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight w hw
  obtain ⟨hHflag, hGcontact⟩ := surfaceMap_HG_flags
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
  have hderiv : regularitySurface φ F ∈
      Ideal.span ({G, MvPolynomial.pderiv (1 : Fin 3) G} :
        Set (MvPolynomial (Fin 3) Ω)) := by
    rw [regularitySurface, ← RCN267.surfaceMap_pderiv_R]
    exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
  have hT' : T = filteredCut w coeffs (surfaceMap φ (polyH K F))
      (surfaceMap φ (polyG K F)) := hT.trans heq
  clear hT
  subst T
  obtain ⟨budget, hcost, hz, hyz, ha, hm⟩ :=
    exists_moving_pole_budget_family (E := E)
      G (regularitySurface φ F) (surfaceMap φ (polyG K F)) w coeffs
      base flag tailFlag unit hG hderiv hGflag
      a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
      (by convert hmix using 1 <;> ring)
  refine ⟨budget, hcost, hm.trans ?_⟩
  rw [mixed_affine_third, mixed_affine_third]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _

end Budgets

end
end ProximityPrize.SubmissionLower.LocatorHybridTransportC2
end PackedLocator_LocatorHybridTransportC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2. -/
section PackedLocator_LocatorHybridTailProviderC2
/-
LOCATOR HYBRID TAIL PROVIDER — C2 (first-tail flag left free).

C1's provider proof never touches the sharp flag except through the type of its
budget family, so this file re-states it with the first-tail flag `tail1` as a
parameter.  Instantiating `tail1 := cellSharpTail t y r` recovers C1 exactly;
instantiating `tail1 := cellFirstTail t y r` (the REDUCED agreement flag, which
is strictly `Below` the sharp one) is the C2 tightening, worth about 1.29% on
the binding cells.

The C2 instantiation needs the reduced geometry transported to the components of
`globalTailCut (w+1)`; `LocatorHybridTransportC2` supplies the missing piece
(the unit-family transport and the moving budgets at a free first-tail flag),
while `RCN332` already supplies `reducedBudgetFamily`, `reducedBaseOrd` and
`transportedWeightedResultantsGeneral`.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

theorem exists_hybridTailMultiplicityProviderGen_of_localDVR
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (tail1 : FlagDegree)
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag tail1)
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (budget : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C : FirstTailComponent S,
      (budget C).zCost = B.zCost C ∧ (budget C).yzCost = B.yzCost C ∧
        (budget C).allCost = B.allCost C)
    (hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))
    (hgate : stageErrorCap + 1 ≤ (cellHybridCoordinateC1 t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) * B.yzCost C)
    (hresultants : RegularComponentWeightedInertiaResultantCertificate B
      (fun C => localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C)) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := tail1)
      (tailFlag2 := cellHybridCoordinateC1 t y r) S
      (flagMixed flag tail1 (cellHybridCoordinateC1 t y r) +
        (w + 5) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  have hry : r < y := by omega
  have hr2 : 2 ≤ r := by omega
  let S0 := loosenStageGeneral S
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C :=
    loosenStageGeneral_one_le_localMultiplicity S hfirstProper
  have hwcEq : ∀ (C : FirstTailComponent S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [MovingPoleBudget.weightedCost,
      PrimeFlagBudgetFamily.weightedCost, hz, hy', ha]
  have hscale : ∀ (m : ℕ) (f : FlagDegree) (C : FirstTailComponent S),
      B.weightedCost (m • f) C = m * B.weightedCost f C := by
    intro m f C
    simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
      nsmul_all]
    ring
  -- the piecewise cost: flag route at multiplicity ≥ 6, moving route below
  let cost : FirstTailComponent S → ℕ := fun C =>
    if 6 ≤ multiplicity C then
      multiplicity C * B.weightedCost (cellHybridCoordinateC1 t y r) C
    else
      B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C +
        (w + multiplicity C) * (budget C).movingCost
  have hlow : ∀ C : FirstTailComponent S,
      B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C ≤
        multiplicity C * B.weightedCost (cellHybridCoordinateC1 t y r) C := by
    intro C
    have hle := cellRationalAt_le_smul t y r (multiplicity C) (hone C)
    have h := weightedCost_mono B C hle.1 hle.2.1 hle.2.2
    rwa [hscale] at h
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellHybridCoordinateC1 t y r) C +
        (w + 5) * (budget C).movingCost := by
    intro C
    by_cases hm : 6 ≤ multiplicity C
    · simp only [cost, if_pos hm]
      exact Nat.le_add_right _ _
    · simp only [cost, if_neg hm]
      have h2 : (w + multiplicity C) * (budget C).movingCost ≤
          (w + 5) * (budget C).movingCost :=
        Nat.mul_le_mul_right _ (by omega)
      have := hlow C
      omega
  have hbound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      cost C := by
    intro C
    have dichotomy := local_order_tail_dichotomy S0
      (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      by_cases hm : 6 ≤ multiplicity C
      · have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C,
            MvPolynomial.aeval
              (selectedPoint (polynomialEmbedding K) S.selected gamma)
              (globalTailCut (polynomialEmbedding K) S.F
                (w + 1 + delay)) = 0 := by
          intro gamma hgamma
          have hGamma := componentSeeds_subset (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K)
            S.F S.selected gamma w (w + 1 + delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod : PolynomialInFlagMod C.1
            (multiplicity C • cellHybridCoordinateC1 t y r)
            (globalTailCut (polynomialEmbedding K) S.F
              (w + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F
            (w + 1 + delay),
            laterTail_in_hybridFlagC1 t y r hr3 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simp
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        simp only [cost, if_pos hm]
        rw [hscale] at hcount
        exact hcount
      · -- the dichotomy hands back `delay ≤ localMultiplicity …`; restate it
        -- against the local `multiplicity` so the atoms line up
        have hdm' : delay ≤ multiplicity C := hdelayMu
        have hcount := component_moving_card_le_delay t y r hr2 hry hyt
          S C (budget C) (base C) delay hdelay htail
        simp only [hwcEq] at hcount
        have hfold : B.weightedCost
              (center (cellA t y) (cellB y r) (cellS r)) C +
            (w + delay) *
              (B.weightedCost
                (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) C +
                (budget C).movingCost) =
            B.weightedCost (cellRationalAt t y r (w + delay)) C +
              (w + delay) * (budget C).movingCost := by
          simp only [cellRationalAt, PrimeFlagBudgetFamily.weightedCost,
            add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
          ring
        rw [hfold] at hcount
        have hmono := cellRationalAt_mono t y r (w + delay)
          (w + multiplicity C) (by omega)
        have h1 := weightedCost_mono B C hmono.1 hmono.2.1 hmono.2.2
        have h2 : (w + delay) * (budget C).movingCost ≤
            (w + multiplicity C) * (budget C).movingCost :=
          Nat.mul_le_mul_right _ (by omega)
        simp only [cost, if_neg hm]
        exact hcount.trans (Nat.add_le_add h1 h2)
    · have hcount := htangent C htangentBranch
      by_cases hm : 6 ≤ multiplicity C
      · simp only [cost, if_pos hm]
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellHybridCoordinateC1 t y r) C :=
            yzCost_mul_le_weightedCost B (cellHybridCoordinateC1 t y r) C
              (stageErrorCap + 1) hgate
          _ = 1 * B.weightedCost (cellHybridCoordinateC1 t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinateC1 t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      · simp only [cost, if_neg hm]
        have hmono := cellRationalAt_mono t y r (w + 1)
          (w + multiplicity C) (by have := hone C; omega)
        have h1 := weightedCost_mono B C hmono.1 hmono.2.1 hmono.2.2
        rw [cellRationalAt_succ_w] at h1
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellHybridCoordinateC1 t y r) C :=
            yzCost_mul_le_weightedCost B (cellHybridCoordinateC1 t y r) C
              (stageErrorCap + 1) hgate
          _ ≤ B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C :=
            h1
          _ ≤ B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C +
              (w + multiplicity C) * (budget C).movingCost :=
            Nat.le_add_right _ _
  have hsum : (∑ C, cost C) ≤
      flagMixed flag tail1 (cellHybridCoordinateC1 t y r) +
        (w + 5) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    calc (∑ C, cost C) ≤
        ∑ C, (multiplicity C *
            B.weightedCost (cellHybridCoordinateC1 t y r) C +
          (w + 5) * (budget C).movingCost) :=
        Finset.sum_le_sum (fun C _ => hcost_pointwise C)
      _ = (∑ C, multiplicity C *
            B.weightedCost (cellHybridCoordinateC1 t y r) C) +
          (w + 5) * (∑ C, (budget C).movingCost) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ flagMixed flag tail1
            (cellHybridCoordinateC1 t y r) +
          (w + 5) *
            flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) :=
        Nat.add_le_add
          (hresultants.divisor_le B multiplicity)
          (Nat.mul_le_mul_left _ hmovingSum)
  have providerDichotomy := loosenStageGeneral_dichotomy_with_tangent S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := cost
    one_le_multiplicity := hone
    tangentYZGate := hgate
    cost_sum_le := hsum
    componentBound := hbound
    dichotomy := providerDichotomy }⟩


end
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
end PackedLocator_LocatorHybridTailProviderC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2. -/
section PackedLocator_LocatorHybridTailRealizationC2
/-
LOCATOR HYBRID TAIL REALIZATION — C2 VARIANT.

C2 runs the hybrid provider on the REDUCED first tail
`cellFirstTail t y r = reducedResidualAgreementFlag (cellSupport t y r) (w+1)`
instead of the sharp one.  Three pieces come from `RCN332` unchanged:

  reducedBudgetFamily                  the budget family over the T1-components
  reducedBaseOrd                       the separable base, transported
  transportedWeightedResultantsGeneral the certificate at the reduced flag

and the missing fourth — a `MovingPoleBudget` whose costs agree with that budget
family — is built here from `LocatorHybridTransportC2`: the reduced unit family
is transported to the T1-components, and `exists_firstTail_moving_budgets`
consumes it at the reduced first-tail flag.

The provider itself is `exists_hybridTailMultiplicityProviderGen_of_localDVR`,
the C1 proof with the first-tail flag left free.
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTailProviderC2 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 800000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
variable {t y r : Nat}

theorem exists_hybridTailMultiplicityProviderC2_realized
    (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedRed : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 2) * (w + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := cellFirstTail t y r)
      (tailFlag2 := cellHybridCoordinateC1 t y r) S
      (flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r) +
        (w + 5) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  haveI : CharP (AlgebraicClosure (RatFunc (GenericField K))) p :=
    charP_of_injective_algebraMap
      (algebraMap (GenericField K)
        (AlgebraicClosure (RatFunc (GenericField K)))).injective p
  obtain ⟨budget, hcost, hmov⟩ :=
    exists_firstTail_moving_budgets
      (E := AlgebraicClosure (RatFunc (GenericField K)))
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (cellA t y) (cellB y r) (cellS r) w (by norm_num [RCN327.w])
      rfl
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      flag S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
      (reducedBaseOrd S hfirstProper hflagChar hmixedRed)
      (cellFirstTail t y r)
      (unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
        (reducedUnitFamily S hfirstProper hflagChar hmixedRed)
        (reducedBaseOrd S hfirstProper hflagChar hmixedRed))
      p hmix
  have hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    have hcut := cellMovingCut_eq_center_add t y r
    have hfib : cellMovingFiber t y r =
        RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r) := rfl
    rw [hfib, hcut]
    exact hmov
  -- route the cost equalities through `unitFamilyOfCongruentCut_costs` rather
  -- than through a single large defeq check, which overruns `maxRecDepth`
  have hcost' : ∀ C : FirstTailComponent S,
      (budget C).zCost =
        (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).zCost C ∧
      (budget C).yzCost =
        (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C ∧
      (budget C).allCost =
        (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).allCost C := by
    intro C
    obtain ⟨hz, hy, ha⟩ := hcost C
    obtain ⟨ez, ey, ea⟩ := unitFamilyOfCongruentCut_costs
      (ordinary_sub_reducedFirstCut_dvd S)
      (reducedUnitFamily S hfirstProper hflagChar hmixedRed)
      (reducedBaseOrd S hfirstProper hflagChar hmixedRed) C
    refine ⟨hz.trans ez, hy.trans ey, ha.trans ea⟩
  exact exists_hybridTailMultiplicityProviderGen_of_localDVR
    t y r hr3 hb hyt S hfirstProper (cellFirstTail t y r)
    (reducedBudgetFamily S hfirstProper hflagChar hmixedRed)
    (reducedBaseOrd S hfirstProper hflagChar hmixedRed)
    budget hcost' hmovingSum hrationalGate htangent
    (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixedRed)


end
end ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
end PackedLocator_LocatorHybridTailRealizationC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridIdentityC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridGatesC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedHybridC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridRealizeC2. -/

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSourceArithmetic. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSingletonSource. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSelection. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorCaps. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorSelectedCaps. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorCover. -/
section PackedLocator_LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorCover
open RCN259
noncomputable section
variable {R S I:Type*} [CommRing R] [GCDMonoid R]
 [CommRing S] [IsDomain S]
local instance:DecidableEq S:=Classical.decEq S
local instance:DecidableEq I:=Classical.decEq I
theorem quotient_vanish (phi:R →+* S) (a b:R)
    (ha:phi a = 0) (hb:phi b = 0) (hg:phi (gcd12 a b) ≠ 0) :
    phi (quotientA a b) = 0 ∧ phi (quotientB a b) = 0:=by
  rw [a_eq_gcd12_mul_quotientA a b, map_mul] at ha
  rw [b_eq_gcd12_mul_quotientB a b, map_mul] at hb
  exact ⟨(mul_eq_zero.mp ha).resolve_left hg, (mul_eq_zero.mp hb).resolve_left hg⟩
def fixed (phi:I → R →+* S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) = 0)
def residual (phi:I → R →+* S) (seeds:Finset I) (a b:R):Finset I:=by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) ≠ 0)
theorem partition_card (phi:I → R →+* S) (seeds:Finset I) (a b:R) :
    (fixed phi seeds a b).card + (residual phi seeds a b).card = seeds.card:=by
  classical
  simpa only [fixed, residual] using
    Finset.card_filter_add_card_filter_not (s:=seeds)
      (fun i => phi i (gcd12 a b) = 0)
theorem fixed_vanish (phi:I → R →+* S) (seeds:Finset I) (a b:R)
    (i:I) (hi:i ∈ fixed phi seeds a b):phi i (gcd12 a b) = 0:=by
  classical
  have hm:i ∈ seeds ∧ phi i (gcd12 a b) = 0:=by
    simpa only [fixed, Finset.mem_filter] using hi
  exact hm.2
theorem residual_vanish (phi:I → R →+* S) (seeds:Finset I) (a b:R)
    (ha:∀ i ∈ seeds, phi i a = 0) (hb:∀ i ∈ seeds, phi i b = 0)
    (i:I) (hi:i ∈ residual phi seeds a b) :
    phi i (quotientA a b) = 0 ∧ phi i (quotientB a b) = 0:=by
  classical
  have hm:i ∈ seeds ∧ phi i (gcd12 a b) ≠ 0:=by
    simpa only [residual, Finset.mem_filter] using hi
  exact quotient_vanish (phi i) a b (ha i hm.1) (hb i hm.1) hm.2
end
end ProximityPrize.SubmissionLower.LocatorCover
end PackedLocator_LocatorCover

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFixedBridge. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Bridge. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Composition. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptCellCore. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData01. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData02. -/

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData03. -/

end Compact_PackedLocatorTail

