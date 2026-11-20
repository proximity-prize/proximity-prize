import ProximityPrize.SubmissionLower.Koala6831OrdinaryCurveCount
import ProximityPrize.SubmissionLower.Koala6831OrdinaryFactors



namespace ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

open RCN095 RCN137 RCN237 MvPolynomial
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4500000

variable {K E Ω I : Type} [Field K] [Field E] [Field Ω]

theorem polynomialIn_ordinaryFlag (G : MvPolynomial (Fin 3) Ω) (y t : ℕ)
    (hy : G.degreeOf 1 ≤ y) (ht : G.totalDegree ≤ t) (hyt : y ≤ t) :
    PolynomialInFlag (ordinaryFlag y t) G := by
  intro d hd
  have hvalue : d 1 ≤ y := (MvPolynomial.degreeOf_le_iff.mp hy) d hd
  have htotal := (MvPolynomial.le_totalDegree hd).trans ht
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at htotal
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Nat.add_zero] at htotal
  rw [← Nat.add_assoc] at htotal
  change d 1 ≤ y ∧ d 0 + d 1 ≤ t - y + y ∧ d 0 + d 1 + d 2 ≤ 0 + (t - y) + y
  rw [Nat.zero_add, Nat.sub_add_cancel hyt]
  exact ⟨hvalue, (Nat.le_add_right _ _).trans htotal, htotal⟩

private theorem sum_surface_prices {S : Type*} [Fintype S]
    (value total : S → ℕ) (y t e D : ℕ) (q r : FlagDegree) (hD : 0 < D)
    (hvalue_total : ∀ s, value s ≤ total s) (hyt : y ≤ t)
    (hvalue : (∑ s, value s) ≤ y) (htotal : (∑ s, total s) ≤ t) :
    (∑ s, ((e + 1) * total s + flagMixed (ordinaryFlag (value s) (total s)) q r / D)) ≤
      (e + 1) * t + flagMixed (ordinaryFlag y t) q r / D := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply Nat.add_le_add (Nat.mul_le_mul_left _ htotal)
  apply (Nat.le_div_iff_mul_le hD).mpr
  rw [Finset.sum_mul]
  refine (Finset.sum_le_sum fun s _ => Nat.div_mul_le_self _ _).trans ?_
  exact ordinary_mixed_sum_le value total y t q r hvalue_total hyt hvalue htotal

omit [Field K] in
private theorem card_le_geometric_factor_sum (F : MvPolynomial (Fin 3) Ω) (hF : F ≠ 0)
    (seeds : Finset K) (v : K → Fin 3 → Ω)
    (hpoint : ∀ g ∈ seeds, MvPolynomial.eval (v g) F = 0) :
    seeds.card ≤ ∑ G : ↥(normalizedFactorSet F), (seeds.filter fun g => MvPolynomial.eval (v g) G = 0).card := by
  classical
  let onFactor (G : ↥(normalizedFactorSet F)) := seeds.filter fun g => MvPolynomial.eval (v g) G = 0
  refine (Finset.card_le_card (t := Finset.univ.biUnion onFactor) ?_).trans Finset.card_biUnion_le
  intro g hg
  obtain ⟨G, hG, hz⟩ := exists_normalizedFactorSet_zero (MvPolynomial.eval (v g)) F hF (hpoint g hg)
  exact Finset.mem_biUnion.mpr ⟨⟨G, hG⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hg, hz⟩⟩

variable [IsAlgClosed Ω] [CharP Ω 2130706433]

theorem regular_geometric_seed_count
    (F : MvPolynomial (Fin 3) Ω) (hF : F ≠ 0) (yF tF y t : ℕ)
    (hy : y ≤ 19) (ht : t ≤ 185) (hyt : y ≤ t)
    (hyF : yF ≤ 19) (htF : tF ≤ 185) (hytF : yF ≤ tF)
    (hFy : F.degreeOf 1 ≤ yF) (hFt : F.totalDegree ≤ tF)
    (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds allSeeds : Finset K) (nodes : Finset I) (v : K → Fin 3 → Ω)
    (w A e : ℕ) (hw : w ≤ 131071) (hwA : w < A) (hAn : A ≤ nodes.card)
    (test : ShortenedAgreementTests nodes (MvPolynomial.pderiv (1 : Fin 3) F) w y t)
    (hsub : seeds ⊆ allSeeds) (hinj : Set.InjOn v allSeeds)
    (hdegree : ∀ g ∈ allSeeds, (P g).natDegree ≤ w)
    (hFpoint : ∀ g ∈ seeds, MvPolynomial.eval (v g) F = 0)
    (hHpoint : ∀ g ∈ seeds, MvPolynomial.eval (v g) (MvPolynomial.pderiv (1 : Fin 3) F) ≠ 0)
    (hfull : ∀ g ∈ seeds, ∀ i ∈ nodes,
      MvPolynomial.aeval (v g) (test.full i) = 0 ↔ (P g).eval (x i) = u₀ i + g * u₁ i)
    (hagreement : ∀ g ∈ allSeeds, A ≤ (nodes.filter (fun i => (P g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds allSeeds P P₀ P₁).card ≤ e + 1) :
    seeds.card ≤ (e + 1) * tF + flagMixed (ordinaryFlag yF tF) (averagedFlag nodes.card w A y t)
      (pencilAugmentedFlag nodes.card w A y t e) / averageDenominator w A ^ 2 := by
  classical
  let Factors := ↥(normalizedFactorSet F)
  let value (G : Factors) := G.1.degreeOf 1
  let total (G : Factors) := G.1.totalDegree
  let onFactor (G : Factors) := seeds.filter fun g => MvPolynomial.eval (v g) G = 0
  let D := averageDenominator w A ^ 2
  let q := averagedFlag nodes.card w A y t
  let r := pencilAugmentedFlag nodes.card w A y t e
  have hD : 0 < D := pow_pos (Nat.mul_pos (Nat.zero_le w |>.trans_lt hwA) (Nat.sub_pos_of_lt hwA)) _
  have hvalue_total (G : Factors) : value G ≤ total G := G.1.degreeOf_le_totalDegree 1
  obtain ⟨ySum, tSum⟩ := Koala6831Ordinary.factor_degree_budgets F hF
  have hySum : (∑ G, value G) ≤ yF := by
    change ∑ G ∈ (normalizedFactorSet F).attach, G.1.degreeOf 1 ≤ yF
    rw [Finset.sum_attach]
    exact ySum.trans hFy
  have htSum : (∑ G, total G) ≤ tF := by
    change ∑ G ∈ (normalizedFactorSet F).attach, G.1.totalDegree ≤ tF
    rw [Finset.sum_attach]
    exact tSum.trans hFt
  have hcount (G : Factors) :
      (onFactor G).card ≤ (e + 1) * total G + flagMixed (ordinaryFlag (value G) (total G)) q r / D := by
    have hG := normalizedFactorSet_spec F G.1 G.2
    have hsingleY : value G ≤ yF := (Finset.single_le_sum (fun J _ => Nat.zero_le (value J))
      (Finset.mem_univ G)).trans hySum
    have hsingleT : total G ≤ tF := (Finset.single_le_sum (fun J _ => Nat.zero_le (total J))
      (Finset.mem_univ G)).trans htSum
    have hfactor_sub : onFactor G ⊆ seeds := Finset.filter_subset _ _
    have hp : 1 ≤ total G := by
      change 0 < G.1.totalDegree
      apply Nat.pos_of_ne_zero
      intro hz
      have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
      have hcn : G.1.coeff 0 ≠ 0 := fun eq => hG.1.ne_zero (by simpa only [eq, map_zero] using hc)
      apply hG.1.not_isUnit
      rw [hc]
      exact (isUnit_iff_ne_zero.mpr hcn).map MvPolynomial.C
    have hc := regular_surface_seed_count F G.1 (value G) (total G) y t
      hG.2 hG.1 (polynomialIn_ordinaryFlag G.1 _ _ le_rfl le_rfl (hvalue_total G))
      (hsingleY.trans hyF) (hsingleT.trans htF)
      (hvalue_total G) hy ht hyt x u₀ u₁ P (onFactor G) allSeeds nodes v w A e hw hwA hAn
      test (hfactor_sub.trans hsub) hinj hdegree
      (fun g hg => (Finset.mem_filter.mp hg).2)
      (fun g hg => hHpoint g (hfactor_sub hg))
      (fun g hg => hfull g (hfactor_sub hg)) hagreement hpencil
    exact hc.trans (Nat.add_le_add_right ((Nat.mul_one (e + 1)).symm.le.trans (Nat.mul_le_mul_left _ hp)) _)
  calc
    _ ≤ ∑ G, (onFactor G).card := card_le_geometric_factor_sum F hF seeds v hFpoint
    _ ≤ ∑ G, ((e + 1) * total G + flagMixed (ordinaryFlag (value G) (total G)) q r / D) :=
      Finset.sum_le_sum fun G _ => hcount G
    _ ≤ _ := sum_surface_prices value total yF tF e D q r hD hvalue_total hytF hySum htSum

open Koala6831Ordinary

def HasOrdinaryAgreementTests (φ : Polynomial K →+* E) (ψ : E →+* Ω) (F : Carrier K)
    (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds : Finset K) (nodes : Finset I) (w y t : ℕ) : Prop :=
  ∀ H ∈ normalizedFactorSet (ordinarySurface φ F), ∃ c : Ω, c ≠ 0 ∧
    ∃ test : ShortenedAgreementTests nodes (MvPolynomial.C c * MvPolynomial.pderiv (1 : Fin 3)
        (MvPolynomial.map ψ H)) w y t,
      ∀ g ∈ seeds, MvPolynomial.eval (ordinaryPoint φ P 2130706433 g) H = 0 →
        MvPolynomial.eval (ordinaryPoint φ P 2130706433 g) (MvPolynomial.pderiv 1 H) ≠ 0 →
        ∀ i ∈ nodes, MvPolynomial.aeval (fun j => ψ (ordinaryPoint φ P 2130706433 g j)) (test.full i) = 0 ↔
          (P g).eval (x i) = u₀ i + g * u₁ i

theorem ordinary_carrier_seed_count [CharP E 2130706433]
    (φ : Polynomial K →+* E) (hφ : Function.Injective φ) (ψ : E →+* Ω) (F : Carrier K) (hF : F ≠ 0)
    (y t : ℕ) (hy : y ≤ 19) (ht : t ≤ 185) (hyt : y ≤ t)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t)
    (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds : Finset K) (nodes : Finset I) (w A e : ℕ)
    (hw : w ≤ 131071) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hdegree : ∀ g ∈ seeds, (P g).natDegree ≤ w)
    (hvanish : ∀ g ∈ seeds, MvPolynomial.aeval
      ![Polynomial.X, P g, Polynomial.C g, Polynomial.C (g ^ 2130706433)] F = 0)
    (hagreement : ∀ g ∈ seeds, A ≤ (nodes.filter (fun i => (P g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (RCN050.pencilSeeds seeds P P₀ P₁).card ≤ e + 1)
    (tests : HasOrdinaryAgreementTests φ ψ F x u₀ u₁ P seeds nodes w y t) :
    seeds.card ≤ ordinaryPrice 2130706433 nodes.card w A e y t := by
  classical
  let Q := ordinarySurface φ F
  let point := ordinaryPoint φ P 2130706433
  let v (g : K) (i : Fin 3) := ψ (point g i)
  have hQ : Q ≠ 0 := fun hz => hF (ordinarySurface_injective φ hφ (by simpa only [map_zero] using hz))
  have bounds := ordinarySurface_degree_caps φ F y t hcap
  have hSylvester : (2 * y - 1) * t < 2130706433 :=
    lt_of_le_of_lt (Nat.mul_le_mul (by omega) ht : (2 * y - 1) * t ≤ (2 * 19 - 1) * 185) (by decide)
  obtain ⟨bad, hbadSub, hbadSize, hcover⟩ := discard_singular_ordinary_seeds 2130706433
    φ hφ F hF y t (by omega) (by omega) hSylvester hcap seeds P hvanish
  let Factors := ↥(normalizedFactorSet Q)
  let value (H : Factors) := H.1.degreeOf 1
  let total (H : Factors) := H.1.totalDegree
  let onFactor (H : Factors) := (seeds \ bad).filter fun g =>
    MvPolynomial.eval (point g) H = 0 ∧ MvPolynomial.eval (point g) (MvPolynomial.pderiv 1 H) ≠ 0
  let D := averageDenominator w A ^ 2
  let q := averagedFlag nodes.card w A y t
  let r := pencilAugmentedFlag nodes.card w A y t e
  have hD : 0 < D := pow_pos (Nat.mul_pos (Nat.zero_le w |>.trans_lt hwA) (Nat.sub_pos_of_lt hwA)) _
  have hvalue_total (H : Factors) : value H ≤ total H := H.1.degreeOf_le_totalDegree 1
  obtain ⟨ySum, tSum⟩ := factor_degree_budgets Q hQ
  have hySum : (∑ H, value H) ≤ y := by
    change ∑ H ∈ (normalizedFactorSet Q).attach, H.1.degreeOf 1 ≤ y
    rw [Finset.sum_attach]
    exact ySum.trans bounds.1
  have htSum : (∑ H, total H) ≤ t := by
    change ∑ H ∈ (normalizedFactorSet Q).attach, H.1.totalDegree ≤ t
    rw [Finset.sum_attach]
    exact tSum.trans bounds.2
  have hinj : Function.Injective v := by
    intro g h eq
    apply ordinaryPoint_injective φ hφ P 2130706433
    funext i
    exact ψ.injective (congrFun eq i)
  have heval (g : K) (B : MvPolynomial (Fin 3) E) :
      MvPolynomial.aeval (v g) (MvPolynomial.map ψ B) = ψ (MvPolynomial.eval (point g) B) := by
    rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map, MvPolynomial.eval₂_comp]
    rfl
  have hcount (H : Factors) :
      (onFactor H).card ≤ (e + 1) * total H + flagMixed (ordinaryFlag (value H) (total H)) q r / D := by
    have hsingleY : value H ≤ y := (Finset.single_le_sum (fun J _ => Nat.zero_le (value J))
      (Finset.mem_univ H)).trans hySum
    have hsingleT : total H ≤ t := (Finset.single_le_sum (fun J _ => Nat.zero_le (total J))
      (Finset.mem_univ H)).trans htSum
    have hH := (normalizedFactorSet_spec Q H.1 H.2).1.ne_zero
    let G := MvPolynomial.map ψ H.1
    have hG : G ≠ 0 := fun hz => hH (MvPolynomial.map_injective ψ ψ.injective (by simpa only [map_zero] using hz))
    have hGy : G.degreeOf 1 ≤ value H := by
      change (MvPolynomial.map ψ H.1).degreeOf 1 ≤ H.1.degreeOf 1
      simp only [MvPolynomial.degreeOf, MvPolynomial.degrees_map_of_injective _ ψ.injective, le_rfl]
    have hGt : G.totalDegree ≤ total H := by
      change (MvPolynomial.map ψ H.1).totalDegree ≤ H.1.totalDegree
      simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective _ ψ.injective, le_rfl]
    obtain ⟨c, hc, test, htest⟩ := tests H.1 H.2
    let actual := test.of_constant_mul c hc
    have hf (g : K) (hg : g ∈ onFactor H) : g ∈ seeds ∧
        MvPolynomial.eval (point g) H = 0 ∧ MvPolynomial.eval (point g) (MvPolynomial.pderiv 1 H.1) ≠ 0 :=
      ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp hg).1).1, (Finset.mem_filter.mp hg).2⟩
    apply regular_geometric_seed_count G hG (value H) (total H) y t hy ht hyt
      (hsingleY.trans hy) (hsingleT.trans ht) (hvalue_total H) hGy hGt
      x u₀ u₁ P (onFactor H) seeds nodes v w A e hw hwA hAn actual
      (fun g hg => (hf g hg).1) hinj.injOn hdegree _ _ _ hagreement hpencil
    · intro g hg
      change MvPolynomial.aeval (v g) (MvPolynomial.map ψ H.1) = 0
      rw [heval, (hf g hg).2.1, map_zero]
    · intro g hg
      change MvPolynomial.aeval (v g) (MvPolynomial.pderiv 1 (MvPolynomial.map ψ H.1)) ≠ 0
      rw [MvPolynomial.pderiv_map, heval]
      exact fun hz => (hf g hg).2.2 (ψ.injective (hz.trans (map_zero ψ).symm))
    · intro g hg i hi
      exact htest g (hf g hg).1 (hf g hg).2.1 (hf g hg).2.2 i hi
  have hfamily : (seeds \ bad).card ≤ ∑ H, (onFactor H).card := by
    refine (Finset.card_le_card (t := Finset.univ.biUnion onFactor) ?_).trans Finset.card_biUnion_le
    intro g hg
    obtain ⟨H, hH, hz, hr⟩ := hcover g hg
    exact Finset.mem_biUnion.mpr ⟨⟨H, hH⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hg, hz, hr⟩⟩
  have hregular : (seeds \ bad).card ≤ (e + 1) * t + flagMixed (ordinaryFlag y t) q r / D :=
    hfamily.trans ((Finset.sum_le_sum fun H _ => hcount H).trans
      (sum_surface_prices value total y t e D q r hD hvalue_total hyt hySum htSum))
  have hpartition : (seeds \ bad).card + bad.card = seeds.card := by
    rw [Finset.card_sdiff_of_subset hbadSub, Nat.sub_add_cancel (Finset.card_le_card hbadSub)]
  rw [← hpartition]
  have charge : (e + 1) * t ≤ (e + 1) * (y + t) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  unfold ordinaryPrice
  have hsum := Nat.add_le_add hregular hbadSize
  change _ ≤ flagMixed (ordinaryFlag y t) q r / D + 2130706433 * (2 * y + 2) * t + (e + 1) * (y + t)
  omega

end

end ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

