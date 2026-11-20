import ProximityPrize.SubmissionLower.Koala6831OrdinaryCurveBudget

namespace ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

open RCN095 RCN237 RCN264
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4500000

def averagedFlag (n w A y t : ℕ) : FlagDegree :=
  ordinaryFlag (averagedCutNumerator n w A y) (averagedCutNumerator n w A t)

def pencilAugmentedFlag (n w A y t e : ℕ) : FlagDegree :=
  ordinaryFlag (averagedCutNumerator n w A y)
    (averagedCutNumerator n w A t + ((e + 1) * averageDenominator w A))

private theorem cut_flag_cost (length y t cy ca : ℕ) :
    (cutFlag 1 length y t).yz * cy + (cutFlag 1 length y t).all * ca =
      ca + length * ((2 * (t - 1) - 2 * (y - 1)) * cy + 2 * (y - 1) * ca) := by
  simp only [cutFlag, ordinaryFlag, Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib]
  ring

private theorem averaged_cost_le_pencil_augmented (n w A y t e cy ca : ℕ) :
    (averagedFlag n w A y t).yz * cy + (averagedFlag n w A y t).all * ca ≤
      (pencilAugmentedFlag n w A y t e).yz * cy + (pencilAugmentedFlag n w A y t e).all * ca := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_right cy (Nat.sub_le_sub_right (Nat.le_add_right _ _) _)) _

private theorem pencil_fee_le_augmented (n w A y t e cy ca : ℕ) (hyt : y ≤ t) (hcy : 1 ≤ cy) :
    (e + 1) * averageDenominator w A ≤
      (pencilAugmentedFlag n w A y t e).yz * cy + (pencilAugmentedFlag n w A y t e).all * ca := by
  have hmono : averagedCutNumerator n w A y ≤ averagedCutNumerator n w A t := by
    unfold averagedCutNumerator
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hyt 1))) _
  have hfee : (e + 1) * averageDenominator w A ≤ (pencilAugmentedFlag n w A y t e).yz := by
    change _ ≤ averagedCutNumerator n w A t + _ - averagedCutNumerator n w A y
    omega
  calc
    _ ≤ (pencilAugmentedFlag n w A y t e).yz := hfee
    _ = (pencilAugmentedFlag n w A y t e).yz * 1 := (Nat.mul_one _).symm
    _ ≤ (pencilAugmentedFlag n w A y t e).yz * cy := Nat.mul_le_mul_left _ hcy
    _ ≤ _ := Nat.le_add_right _ _

private theorem incidence_after_shortened_cuts {Seed Node : Type}
    (seeds : Finset Seed) (nodes identities : Finset Node) (relation : Seed → Node → Prop)
    (w A y t cy ca : ℕ) (hIN : identities ⊆ nodes) (hI : identities.card ≤ w)
    (hwA : w < A) (hAn : A ≤ nodes.card)
    (hagreement : ∀ g ∈ seeds, A ≤ (nodes.filter (relation g)).card)
    (hcut : ∀ i ∈ nodes \ identities,
      (seeds.filter (fun g => relation g i)).card ≤
        (cutFlag 1 (w - identities.card) y t).yz * cy + (cutFlag 1 (w - identities.card) y t).all * ca) :
    seeds.card * averageDenominator w A ≤
      (averagedFlag nodes.card w A y t).yz * cy + (averagedFlag nodes.card w A y t).all * ca := by
  let slope := (2 * (t - 1) - 2 * (y - 1)) * cy + 2 * (y - 1) * ca
  have h := incidence_le_shortened_scaled relation seeds nodes identities A w 1 slope ca
    (by decide) hIN hI hwA hAn hagreement (by
      intro i hi
      have bound := hcut i hi
      rw [cut_flag_cost, Nat.mul_comm (w - identities.card)] at bound
      simpa only [Nat.mul_one, slope] using bound)
  simp only [Nat.cast_one, mul_one] at h
  have hA : (A : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_le w |>.trans_lt hwA))
  have hAw : (A : ℚ) - w ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hwA))
  let n := nodes.card
  let scaledLength := n * w * (A - w)
  let scaledNodes := (n - w) * A
  have hL : lengthAverage nodes.card w A * (averageDenominator w A : ℚ) = (scaledLength : ℚ) := by
    unfold lengthAverage averageDenominator scaledLength n
    push_cast [Nat.cast_sub hwA.le]
    field_simp
  have hN : nodeAverage nodes.card w A * (averageDenominator w A : ℚ) = (scaledNodes : ℚ) := by
    unfold nodeAverage averageDenominator scaledNodes n
    push_cast [Nat.cast_sub hwA.le, Nat.cast_sub (hwA.le.trans hAn)]
    field_simp
  have scaled := mul_le_mul_of_nonneg_right h (show (0 : ℚ) ≤ averageDenominator w A by positivity)
  rw [add_mul, mul_assoc (slope : ℚ), mul_assoc (ca : ℚ), hL, hN] at scaled
  have hn : seeds.card * averageDenominator w A ≤ slope * scaledLength + ca * scaledNodes := by
    exact_mod_cast scaled
  have hnum (degree : ℕ) :
      averagedCutNumerator n w A degree = scaledNodes + scaledLength * (2 * (degree - 1)) := by
    unfold averagedCutNumerator scaledLength scaledNodes
    ring
  change _ ≤ (averagedCutNumerator n w A t - averagedCutNumerator n w A y) * cy +
    averagedCutNumerator n w A y * ca
  rw [hnum t, hnum y, Nat.add_sub_add_left, ← Nat.mul_sub_left_distrib]
  convert hn using 1
  simp only [slope]
  ring

variable {K Ω I : Type} [Field K] [Field Ω]

private theorem identity_pencil_bound (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds allSeeds : Finset K) (identities : Finset I) (w e : ℕ)
    (hsub : seeds ⊆ allSeeds) (hI : w < identities.card)
    (hdegree : ∀ g ∈ allSeeds, (P g).natDegree ≤ w)
    (hident : ∀ g ∈ seeds, ∀ i ∈ identities, (P g).eval (x i) = u₀ i + g * u₁ i)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds allSeeds P P₀ P₁).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  obtain ⟨P₀, P₁, h₀, h₁, eq⟩ := RCN147.exists_basefield_affine_pencil_of_identity_nodes
    (RingHom.id K) identities x u₀ u₁ w hI x.injective.injOn
    (fun g : ↥seeds => g.val) (fun g => P g.val) (fun g => hdegree g.val (hsub g.property))
    (fun g i hi => hident g.val g.property i hi)
  refine (Finset.card_le_card (t := RCN050.pencilSeeds allSeeds P P₀ P₁) ?_).trans (hpencil P₀ P₁ h₀ h₁)
  intro g hg
  refine Finset.mem_filter.mpr ⟨hsub hg, ?_⟩
  simpa only [Polynomial.map_id] using eq ⟨g, hg⟩

def identityNodes (nodes : Finset I) (full : I → MvPolynomial (Fin 3) Ω)
    (C : Ideal (MvPolynomial (Fin 3) Ω)) : Finset I :=
  nodes.filter (fun i => full i ∈ C)

structure ShortenedAgreementTests (nodes : Finset I) (H : MvPolynomial (Fin 3) Ω) (w y t : ℕ) where
  full : I → MvPolynomial (Fin 3) Ω
  short : Ideal (MvPolynomial (Fin 3) Ω) → I → MvPolynomial (Fin 3) Ω
  correct : ∀ C : Ideal (MvPolynomial (Fin 3) Ω), C.IsPrime → H ∉ C →
    (identityNodes nodes full C).card ≤ w → ∀ i ∈ nodes \ identityNodes nodes full C,
    short C i ∉ C ∧
      PolynomialInFlag (cutFlag 1 (w - (identityNodes nodes full C).card) y t) (short C i) ∧
      ∀ point : Fin 3 → Ω,
        C ≤ RingHom.ker (MvPolynomial.aeval point).toRingHom →
        MvPolynomial.aeval point H ≠ 0 →
        MvPolynomial.aeval point (full i) = 0 → MvPolynomial.aeval point (short C i) = 0

def ShortenedAgreementTests.of_constant_mul {nodes : Finset I} {H : MvPolynomial (Fin 3) Ω}
    {w y t : ℕ} (c : Ω) (hc : c ≠ 0) (test : ShortenedAgreementTests nodes (MvPolynomial.C c * H) w y t) :
    ShortenedAgreementTests nodes H w y t where
  full := test.full
  short := test.short
  correct C hprime hH few i hi := by
    have hscaled : MvPolynomial.C c * H ∉ C := fun mem => hH
      ((C.unit_mul_mem_iff_mem ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C)).mp mem)
    obtain ⟨proper, cap, zero⟩ := test.correct C hprime hscaled few i hi
    refine ⟨proper, cap, fun v hv hreg hfull => zero v hv ?_ hfull⟩
    rw [map_mul, MvPolynomial.aeval_C]
    exact mul_ne_zero hc hreg

private theorem identity_at_point {nodes : Finset I} {full : I → MvPolynomial (Fin 3) Ω}
    {C : Ideal (MvPolynomial (Fin 3) Ω)} {i : I}
    (hi : i ∈ identityNodes nodes full C) (point : Fin 3 → Ω)
    (hC : C ≤ RingHom.ker (MvPolynomial.aeval point).toRingHom) :
    i ∈ nodes ∧ MvPolynomial.aeval point (full i) = 0 := by
  have h := Finset.mem_filter.mp hi
  exact ⟨h.1, hC h.2⟩

variable [IsAlgClosed Ω] [CharP Ω 2130706433]

theorem regular_firstCut_scaled
    (F G T : MvPolynomial (Fin 3) Ω) (left first : FlagDegree)
    (hdiv : G ∣ F) (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hR : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (hGflag : PolynomialInFlag left G) (hTflag : PolynomialInFlag first T)
    (hchar : left.zOnly + left.yz + left.all < 2130706433)
    (hsharp : flagMixed left first unitZFlag < 2130706433)
    (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds allSeeds : Finset K) (nodes : Finset I) (v : K → Fin 3 → Ω)
    (w A e y t : ℕ) (hwA : w < A) (hAn : A ≤ nodes.card) (hyt : y ≤ t)
    (test : ShortenedAgreementTests nodes (MvPolynomial.pderiv (1 : Fin 3) F) w y t)
    (hsub : seeds ⊆ allSeeds) (hinj : Set.InjOn v allSeeds)
    (hdegree : ∀ g ∈ allSeeds, (P g).natDegree ≤ w)
    (hGpoint : ∀ g ∈ seeds, MvPolynomial.aeval (v g) G = 0)
    (hTpoint : ∀ g ∈ seeds, MvPolynomial.aeval (v g) T = 0)
    (hHpoint : ∀ g ∈ seeds, MvPolynomial.aeval (v g) (MvPolynomial.pderiv (1 : Fin 3) F) ≠ 0)
    (hfull : ∀ g ∈ seeds, ∀ i ∈ nodes,
      MvPolynomial.aeval (v g) (test.full i) = 0 ↔ (P g).eval (x i) = u₀ i + g * u₁ i)
    (hagreement : ∀ g ∈ allSeeds, A ≤ (nodes.filter (fun i => (P g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds allSeeds P P₀ P₁).card ≤ e + 1) :
    seeds.card * averageDenominator w A ≤ flagMixed left first (pencilAugmentedFlag nodes.card w A y t e) := by
  classical
  let H := MvPolynomial.pderiv (1 : Fin 3) F
  obtain ⟨B, B_pos⟩ := exists_regular_curve_budgets 2130706433 F G T left first hdiv hG hproper
    hR hGflag hTflag hchar hsharp
  let onCurve (C : RegularComponent Ω G T H) := componentSeeds Ω G T H seeds v C
  let relation := fun (g : K) (i : I) => (P g).eval (x i) = u₀ i + g * u₁ i
  let scaled := pencilAugmentedFlag nodes.card w A y t e
  have count (C : RegularComponent Ω G T H) :
      (onCurve C).card * averageDenominator w A ≤ B.weightedCost scaled C := by
    have curve_sub : onCurve C ⊆ seeds := componentSeeds_subset Ω G T H seeds v C
    have hon (g : K) (hg : g ∈ onCurve C) : C.1 ≤ RingHom.ker (MvPolynomial.aeval (v g)).toRingHom :=
      componentSeeds_on_prime Ω G T H seeds v C g hg
    let identities := identityNodes nodes test.full C.1
    have hIN : identities ⊆ nodes := Finset.filter_subset _ _
    by_cases few : identities.card ≤ w
    · have hc : (onCurve C).card * averageDenominator w A ≤
          (averagedFlag nodes.card w A y t).yz * B.yzCost C + (averagedFlag nodes.card w A y t).all * B.allCost C := by
        apply incidence_after_shortened_cuts (onCurve C) nodes identities relation w A y t _ _ hIN few hwA hAn
          (fun g hg => hagreement g (hsub (curve_sub hg)))
        intro i hi
        obtain ⟨proper, flag, vanishing⟩ := test.correct C.1 inferInstance
          (regularComponent_H_not_mem Ω G T H C) few i hi
        let fiber := (onCurve C).filter (fun g => relation g i)
        have fiber_sub : fiber ⊆ onCurve C := Finset.filter_subset _ _
        have hcount := curve_cut_seed_bound B C fiber v (test.short C.1 i)
          (cutFlag 1 (w - identities.card) y t) flag proper
          (hinj.mono (fiber_sub.trans (curve_sub.trans hsub)))
          (fun g hg => hon g (fiber_sub hg)) (by
            intro g hg
            have hgc := fiber_sub hg
            have agrees := (Finset.mem_filter.mp hg).2
            exact vanishing (v g) (hon g hgc) (hHpoint g (curve_sub hgc))
              ((hfull g (curve_sub hgc) i (Finset.mem_sdiff.mp hi).1).mpr agrees))
        simpa only [fiber, PrimeFlagBudgetFamily.weightedCost, cutFlag, ordinaryFlag,
          zero_mul, zero_add] using hcount
      exact hc.trans (by simpa only [PrimeFlagBudgetFamily.weightedCost, scaled,
        pencilAugmentedFlag, ordinaryFlag, zero_mul, zero_add] using
        averaged_cost_le_pencil_augmented nodes.card w A y t e (B.yzCost C) (B.allCost C))
    · have hp : (onCurve C).card ≤ e + 1 := by
        apply identity_pencil_bound x u₀ u₁ P (onCurve C) allSeeds identities w e
          (curve_sub.trans hsub) (Nat.lt_of_not_ge few) hdegree _ hpencil
        intro g hg i hi
        obtain ⟨hiN, hiZero⟩ := identity_at_point hi (v g) (hon g hg)
        exact (hfull g (curve_sub hg) i hiN).mp hiZero
      have charge := pencil_fee_le_augmented nodes.card w A y t e (B.yzCost C) (B.allCost C) hyt (B_pos C)
      exact (Nat.mul_le_mul_right _ hp).trans (by
        simpa only [PrimeFlagBudgetFamily.weightedCost, scaled, pencilAugmentedFlag, ordinaryFlag,
          zero_mul, zero_add] using charge)
  calc
    _ ≤ (∑ C, (onCurve C).card) * averageDenominator w A :=
      Nat.mul_le_mul_right _ (card_le_sum_componentSeeds Ω G T H seeds v hGpoint hTpoint hHpoint)
    _ = ∑ C, (onCurve C).card * averageDenominator w A := Finset.sum_mul _ _ _
    _ ≤ ∑ C, B.weightedCost scaled C := Finset.sum_le_sum fun C _ => count C
    _ ≤ _ := B.sum_weightedCost_le scaled

theorem regular_surface_seed_count
    (F G : MvPolynomial (Fin 3) Ω) (yG tG y t : ℕ)
    (hdiv : G ∣ F) (hG : Irreducible G)
    (hGflag : PolynomialInFlag (ordinaryFlag yG tG) G)
    (hyG : yG ≤ 19) (htG : tG ≤ 185) (hytG : yG ≤ tG)
    (hy : y ≤ 19) (ht : t ≤ 185) (hyt : y ≤ t)
    (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds allSeeds : Finset K) (nodes : Finset I) (v : K → Fin 3 → Ω)
    (w A e : ℕ) (hw : w ≤ 131071) (hwA : w < A) (hAn : A ≤ nodes.card)
    (test : ShortenedAgreementTests nodes (MvPolynomial.pderiv (1 : Fin 3) F) w y t)
    (hsub : seeds ⊆ allSeeds) (hinj : Set.InjOn v allSeeds)
    (hdegree : ∀ g ∈ allSeeds, (P g).natDegree ≤ w)
    (hGpoint : ∀ g ∈ seeds, MvPolynomial.aeval (v g) G = 0)
    (hHpoint : ∀ g ∈ seeds, MvPolynomial.aeval (v g) (MvPolynomial.pderiv (1 : Fin 3) F) ≠ 0)
    (hfull : ∀ g ∈ seeds, ∀ i ∈ nodes,
      MvPolynomial.aeval (v g) (test.full i) = 0 ↔ (P g).eval (x i) = u₀ i + g * u₁ i)
    (hagreement : ∀ g ∈ allSeeds, A ≤ (nodes.filter (fun i => (P g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds allSeeds P P₀ P₁).card ≤ e + 1) :
    seeds.card ≤ e + 1 + flagMixed (ordinaryFlag yG tG) (averagedFlag nodes.card w A y t)
      (pencilAugmentedFlag nodes.card w A y t e) / averageDenominator w A ^ 2 := by
  classical
  by_cases empty : seeds = ∅
  · simp [empty]
  obtain ⟨g₀, hg₀⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  let ideal : Ideal (MvPolynomial (Fin 3) Ω) := Ideal.span {G}
  let H := MvPolynomial.pderiv (1 : Fin 3) F
  let left := ordinaryFlag yG tG
  let identities := identityNodes nodes test.full ideal
  let relation := fun (g : K) (i : I) => (P g).eval (x i) = u₀ i + g * u₁ i
  have hPrime : ideal.IsPrime := (Ideal.span_singleton_prime hG.ne_zero).mpr hG.prime
  have hon (g : K) (hg : g ∈ seeds) : ideal ≤ RingHom.ker (MvPolynomial.aeval (v g)).toRingHom := by
    apply Ideal.span_le.mpr
    intro polynomial hpolynomial
    have eq : polynomial = G := Set.mem_singleton_iff.mp hpolynomial
    subst polynomial
    exact hGpoint g hg
  have hH_ideal : H ∉ ideal := fun mem => hHpoint g₀ hg₀ (hon g₀ hg₀ mem)
  have hR : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0 := by
    intro zero
    apply hH_ideal
    obtain ⟨Q, hQ⟩ := hdiv
    change MvPolynomial.pderiv (1 : Fin 3) F ∈ Ideal.span {G}
    rw [hQ, MvPolynomial.pderiv_mul, zero, zero_mul, zero_add]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  by_cases few : identities.card ≤ w
  · have hIN : identities ⊆ nodes := Finset.filter_subset _ _
    have hs : 0 < averageDenominator w A := Nat.mul_pos (Nat.zero_le w |>.trans_lt hwA) (Nat.sub_pos_of_lt hwA)
    have scaled := mixed_incidence_le_scaled relation seeds nodes identities left
      (pencilAugmentedFlag nodes.card w A y t e) A w y t (averageDenominator w A) hs
      hIN few hwA hAn (fun g hg => hagreement g (hsub hg)) (by
        intro i hi
        obtain ⟨proper, flag, vanishing⟩ := test.correct ideal hPrime hH_ideal few i hi
        let fiber := seeds.filter (fun g => relation g i)
        have fiber_sub : fiber ⊆ seeds := Finset.filter_subset _ _
        have hflagchar : left.zOnly + left.yz + left.all < 2130706433 := by
          change 0 + (tG - yG) + yG < 2130706433
          rw [Nat.zero_add, Nat.sub_add_cancel hytG]
          omega
        have sharp := koala_ordinary_sharp_projection_gate yG tG y t (w - identities.card)
          hyG htG hytG hy ht ((Nat.sub_le ..).trans hw)
        exact regular_firstCut_scaled F G (test.short ideal i) left
          (cutFlag 1 (w - identities.card) y t) hdiv hG
          (fun hd => proper (Ideal.mem_span_singleton.mpr hd)) hR hGflag flag hflagchar sharp
          x u₀ u₁ P fiber allSeeds nodes v w A e y t hwA hAn hyt test
          (fiber_sub.trans hsub) hinj hdegree
          (fun g hg => hGpoint g (fiber_sub hg))
          (fun g hg => vanishing (v g) (hon g (fiber_sub hg)) (hHpoint g (fiber_sub hg))
            ((hfull g (fiber_sub hg) i (Finset.mem_sdiff.mp hi).1).mpr (Finset.mem_filter.mp hg).2))
          (fun g hg => hHpoint g (fiber_sub hg)) (fun g hg => hfull g (fiber_sub hg)) hagreement hpencil)
    have count : seeds.card ≤ flagMixed left (averagedFlag nodes.card w A y t)
        (pencilAugmentedFlag nodes.card w A y t e) / averageDenominator w A ^ 2 := by
      apply (Nat.le_div_iff_mul_le (pow_pos hs 2)).mpr
      simpa only [averagedFlag, pow_two, ← Nat.mul_assoc] using scaled
    exact count.trans (Nat.le_add_left _ _)
  · have count : seeds.card ≤ e + 1 := by
      apply identity_pencil_bound x u₀ u₁ P seeds allSeeds identities w e hsub
        (Nat.lt_of_not_ge few) hdegree _ hpencil
      intro g hg i hi
      obtain ⟨hiN, hiZero⟩ := identity_at_point hi (v g) (hon g hg)
      exact (hfull g hg i hiN).mp hiZero
    exact count.trans (Nat.le_add_right _ _)

end

end ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence
