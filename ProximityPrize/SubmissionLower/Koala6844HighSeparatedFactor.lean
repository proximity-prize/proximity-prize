import ProximityPrize.SubmissionLower.Koala6844HighSeparatedBudget
import ProximityPrize.SubmissionLower.Koala6844HighSeparatedProper
import ProximityPrize.SubmissionLower.Koala6844HighSeparatedPersistentSurface


namespace ProximityPrize.SubmissionLower.Koala6844HighSeparated

open Koala6831Intrinsic Koala6831OrdinaryIncidence
open RCN135 RCN136 RCN234 RCN264
open scoped Classical BigOperators

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {K I : Type} [Field K] [CharP K 2130706433]

local notation "Ω" => GenericField K
local notation "φ" => polynomialEmbedding K

private theorem sum_partition {A : Type} [Fintype A] (p : A → Prop) (f : A → ℕ) :
    (∑ a, f a) = (∑ a : {a // p a}, f a.1) + ∑ a : {a // ¬ p a}, f a.1 := by
  classical
  have first : (∑ a ∈ (Finset.univ : Finset A).filter p, f a) =
      ∑ a : {a // p a}, f a.1 := by
    simpa only [Finset.subtype_univ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset A)) f (p := p)).symm
  have second : (∑ a ∈ (Finset.univ : Finset A).filter (fun a => ¬ p a), f a) =
      ∑ a : {a // ¬ p a}, f a.1 := by
    simpa only [Finset.subtype_univ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset A)) f (p := fun a => ¬ p a)).symm
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ p f).symm.trans
    (congrArg₂ (· + ·) first second)

theorem long_factor_seed_count_of_persistent_allowance
    (F : Carrier K) (hp : Nat.Prime 2130706433) (hF : Irreducible F)
    (hweight : wt ![1, 131071, 0, 0] F < 4000000)
    (hY : wt ![0, 1, 0, 0] F ≤ 22)
    (hT : wt ![0, 1, 1, 0] F ≤ 200)
    (hZ : wt ![0, 0, 0, 1] F ≤ 162)
    (G : MvPolynomial (Fin 3) Ω) (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F)
    (x : I ↪ K) (u₀ u₁ : I → K) (nodes : Finset I)
    (hAn : 180961 ≤ nodes.card) (haverage : nodeAverage nodes.card 131071 180961 ≤ 3)
    (seeds allSeeds : Finset K) (hsub : seeds ⊆ allSeeds)
    (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hroot : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ 2130706433) F = 0)
    (hreg : ∀ g ∈ seeds,
      graphSpecialize (selected g) g (g ^ 2130706433) (implicitRegularity F) ≠ 0)
    (hzero : ∀ g ∈ seeds, MvPolynomial.eval (selectedGraphPoint 2130706433 selected g) G = 0)
    (hagreements : ∀ g ∈ seeds, 180961 ≤
      (nodes.filter (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (RCN050.pencilSeeds allSeeds selected P₀ P₁).card ≤ 81184)
    (curveAllowance : ¬ G ∣ surfaceMap φ (tailNumerator F 131071) →
      (∑ C : {C : FirstTailComponent F 131071 G // Persistent F 131071 C.1},
        (selectedComponentPoints F 131071 2130706433 G seeds selected C.1).card) ≤
          200000 * ((5505004 * G.degreeOf 2 + G.degreeOf 0 * 42467166) +
             (5505004 * (longMiddleDegree G - G.degreeOf 0) + G.degreeOf 0 * 52166458))) :
    seeds.card ≤ longFactorCharge (G.degreeOf 0) (longMiddleDegree G) (G.degreeOf 2) := by
  classical
  let y := G.degreeOf 0
  let t := longMiddleDegree G
  let z := G.degreeOf 2
  obtain ⟨hy, ht, hz, hyt, hGt⟩ := long_geometric_factor_caps F hF.ne_zero G hdiv hY hT hZ
  have hseed₀ d hd := (long_native_seed_support F hT hZ d hd).1
  have hseed₁ d hd := (long_native_seed_support F hT hZ d hd).2
  by_cases whole : G ∣ surfaceMap φ (tailNumerator F 131071)
  · have hcount := long_persistent_surface_selected_count F hF hweight hseed₀ hseed₁ G
      hG hdiv whole hy hz x u₀ u₁ nodes hAn haverage seeds allSeeds hsub selected hdegree
      hroot hreg hzero hagreements hpencil
    exact hcount.trans (by
      rw [longFactorCharge_eq _ _ _ hyt]
      omega)
  · let A := FirstTailComponent F 131071 G
    let f (c : A) := (selectedComponentPoints F 131071 2130706433 G seeds selected c).card
    have hcover : seeds.card ≤ ∑ c : A, f c :=
      selected_card_le_sum_componentPoints F 131071 2130706433 G seeds selected hdegree hroot hreg hzero
    have hproper := nonpersistent_selected_price F hp hF hY hT hZ G hG hdiv whole
      y t z hyt hy ht hz le_rfl hGt le_rfl seeds selected hdegree hroot hreg
    have hpersist := curveAllowance whole
    rw [sum_partition (fun c : A => Persistent F 131071 c.1) f] at hcover
    apply hcover.trans
    refine (Nat.add_le_add hpersist hproper).trans ?_
    rw [longFactorCharge_eq _ _ _ hyt]
    unfold longProperCurveCost y t z
    omega

end

end ProximityPrize.SubmissionLower.Koala6844HighSeparated
