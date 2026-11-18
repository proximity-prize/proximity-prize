import ProximityPrize.SubmissionLower.Koala6831MovingFoldCount
import ProximityPrize.SubmissionLower.Koala6831MovingTangentRoute

namespace ProximityPrize.SubmissionLower.Koala6831MovingPrimaryRoute

open scoped Classical
open Koala6831Moving Koala6831MovingSources Koala6831MovingFoldCount
open LocatorLowQuotient RCN238 RCN266 RCN313 RCN319

noncomputable section

variable {K Node : Type} [Field K] [CharP K 2130706433]

theorem exists_primary_and_regular_subfamily
    (nodes good : Finset Node) (hgood : good ⊆ nodes) (hnodes : nodes.card = 262144)
    (x : Node ↪ K) (u₀ u₁ : Node → K)
    (Γ : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hgoodAgree : ∀ γ ∈ Γ, ∀ i ∈ nodes,
      (selected γ).eval (x i) = u₀ i + γ * u₁ i → i ∈ good)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81060) :
    ∃ H : MvPolynomial (Fin 4) K, H ≠ 0 ∧
      H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 53188 360 80 ∧
      (∀ i ∈ good, ContactOrderBridge.ContactAtLeast K (x i) (u₀ i) (u₁ i) Stage.primary.multiplicity H) ∧
      ∃ regular : Finset K, regular ⊆ Γ ∧ Γ.card ≤ regular.card + 3084745996799680 ∧
        ∀ γ ∈ regular, ∃ F : RegularIndex H, specialization K (selected γ) γ F.1 = 0 ∧
          specialization K (selected γ) γ (polyH K F.1) ≠ 0 := by
  classical
  let xgood (i : ↥good) := x i.1
  let u₀good (i : ↥good) := u₀ i.1
  let u₁good (i : ↥good) := u₁ i.1
  have hcard : Fintype.card (↥good) ≤ 262144 := by
    rw [Fintype.card_coe, ← hnodes]
    exact Finset.card_le_card hgood
  obtain ⟨v, hv⟩ := Stage.primary.exists_source K xgood u₀good u₁good hcard
  let H := Stage.primary.reconstruct K xgood u₀good u₁good v
  have hbox : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 53188 360 80 :=
    Stage.primary.reconstruct_mem_box K xgood u₀good u₁good v
  have hcontact (i : Node) (hi : i ∈ good) :
      ContactOrderBridge.ContactAtLeast K (x i) (u₀ i) (u₁ i) Stage.primary.multiplicity H :=
    Stage.primary.reconstruct_contact K xgood u₀good u₁good v ⟨i, hi⟩
  have hsolution (γ : K) (hγ : γ ∈ Γ) : specialization K (selected γ) γ H = 0 := by
    let support := nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)
    exact specialization_zero_of_box_and_agreement x u₀ u₁ Stage.primary H (selected γ) γ support hbox
      (fun i hi => hcontact i (hgoodAgree γ hγ i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2))
      (hdegree γ hγ) (hagreement γ hγ) (fun i hi => (Finset.mem_filter.mp hi).2)
  exact ⟨H, hv, hbox, hcontact, exists_primary_regular_seeds H hv hbox Γ selected nodes x u₀ u₁
    x.injective.injOn hnodes hdegree hsolution hagreement hnoPencil⟩

theorem exists_primary_and_transverse_subfamily [Fintype Node]
    (B : FlowData K) (nodes good : Finset Node) (hgood : good ⊆ nodes) (hnodes : nodes.card = 262144)
    (x : Node ↪ K) (u₀ u₁ received : Node → K)
    (Γ : Finset K) (selected normalized : K → Polynomial K)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hgoodAgree : ∀ γ ∈ Γ, ∀ i ∈ nodes,
      (selected γ).eval (x i) = u₀ i + γ * u₁ i → i ∈ good)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81060)
    (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0)
    (hden : ∀ γ ∈ Γ, B.seedDenominator γ ≠ 0)
    (hnorm : ∀ γ ∈ Γ,
      B.d0 * selected γ + B.seedOffset γ = B.seedDenominator γ * normalized γ)
    (hnormDegree : ∀ γ ∈ Γ, (normalized γ).natDegree ≤ TangentList.w)
    (hnormAgree : ∀ γ ∈ Γ, TangentList.agreements ≤
      (nodes.filter (fun i => (normalized γ).eval (x i) = received i)).card) :
    ∃ H : MvPolynomial (Fin 4) K, H ≠ 0 ∧
      H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 53188 360 80 ∧
      (∀ i ∈ good, ContactOrderBridge.ContactAtLeast K (x i) (u₀ i) (u₁ i) Stage.primary.multiplicity H) ∧
      ∃ retained : Finset K, retained ⊆ Γ ∧ Γ.card ≤ retained.card + 7016598644482579 ∧
        ∀ γ ∈ retained, ∃ F : RegularIndex H, specialization K (selected γ) γ F.1 = 0 ∧
          specialization K (selected γ) γ (polyH K F.1) ≠ 0 ∧ ¬ F.1 ∣ B.flow F.1 := by
  classical
  obtain ⟨H, hH, hbox, hcontact, regular, hsub, hcost, hregular⟩ :=
    exists_primary_and_regular_subfamily nodes good hgood hnodes x u₀ u₁ Γ selected
      hdegree hagreement hgoodAgree hnoPencil
  obtain ⟨retained, hret, htangentCost, htangent⟩ :=
    B.screen_tangent_seeds H hH hbox regular selected normalized nodes x received x.injective.injOn
      hnodes hd0 ha (fun γ hγ => hden γ (hsub hγ)) (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => hnorm γ (hsub hγ)) (fun γ hγ => hnormDegree γ (hsub hγ))
      (fun γ hγ => hnormAgree γ (hsub hγ))
      (RCN243.noLargeSelectedPencil_mono selected Γ regular weight 81060 hsub hnoPencil)
  refine ⟨H, hH, hbox, hcontact, retained, hret.trans hsub, ?_, ?_⟩
  · change regular.card ≤ retained.card + 3931852647682899 at htangentCost
    omega
  · intro γ hγ
    obtain ⟨F, hF, hreg⟩ := hregular γ (hret hγ)
    exact ⟨F, hF, hreg, htangent γ hγ F hF⟩

end

end ProximityPrize.SubmissionLower.Koala6831MovingPrimaryRoute
