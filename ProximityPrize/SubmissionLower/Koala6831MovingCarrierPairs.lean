import ProximityPrize.SubmissionLower.Koala6831MovingPairIncidence

namespace ProximityPrize.SubmissionLower.Koala6831MovingCarrierPairs

open scoped Classical BigOperators
open RCN095 RCN130 RCN135 RCN136 RCN137 RCN138 RCN222 RCN238 RCN263 RCN267 RCN275 RCN313 RCN319
open Koala6831MovingPairIncidence

noncomputable section

variable {K : Type} [Field K]

theorem regular_carrier_seed_card_mul_le
    (support : ResidualSupportParameters) (F D : MvPolynomial (Fin 4) K)
    (hF : Irreducible F) (hD : ¬ F ∣ D) (p : ℕ) [CharP K p]
    (hRpos : 0 < F.degreeOf (2 : Fin 4)) (hRsmall : F.degreeOf (2 : Fin 4) < p)
    (hData : ResidualSupportData support F) (right : FlagDegree)
    (hDflag : PolynomialInFlag right (surfaceMap (polynomialEmbedding K) D))
    (selected : K → Polynomial K) (Γ : Finset K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (w A e : ℕ) (hw : 1 ≤ w) (hchar : w < p) (hwA : w < A) (hAn : A ≤ nodes.card)
    (htotal : support.total < p)
    (hmixed : (right.yz + right.all) * support.s + support.ys * right.all < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hpartner : ∀ γ ∈ Γ, specialization K (selected γ) γ D = 0)
    (hregular : ∀ γ ∈ Γ, specialization K (selected γ) γ (polyH K F) ≠ 0)
    (hagreement : ∀ γ ∈ Γ, A ≤ (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    Γ.card * (A * (A - w)) ≤ flagMixed (originalCumulativeFlag F) right
      (scaledPairFlag support nodes.card w A e) := by
  classical
  let E := GenericField K
  let φ := polynomialEmbedding K
  let _ : CharP E p := genericField_charP K p
  let T := surfaceMap φ D
  let seeds := geometricSeeds K F selected Γ
  let left := geometricCumulativeFlag K (F := F)
  let cut := scaledPairFlag support nodes.card w A e
  have hcomp (g : GeometricFactor K F) : (seeds g).card * (A * (A - w)) ≤
      flagMixed (left g) right cut := by
    obtain ⟨hirr, hgdiv⟩ := surfaceFactors_spec φ F g.1 g.2
    have hdivGeo : g.1 ∣ geometricSurfaceMap K E F := by
      change g.1 ∣ geometricSurfaceMap K (GenericField K) F
      rw [canonical_geometricSurfaceMap]
      exact hgdiv
    have hgate := geometric_factor_regular_gate K E F hF p hRpos hRsmall g.1 hirr hdivGeo
    have hproper : ¬ g.1 ∣ T := by
      intro h
      apply hD
      have hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 := by omega
      apply (geometric_factor_dvd_iff K E F D hF hpos g.1 hirr hdivGeo).mp
      change g.1 ∣ geometricSurfaceMap K (GenericField K) D
      rw [canonical_geometricSurfaceMap]
      exact h
    have hcap := geometricCumulativeFlag_le_support F hF.ne_zero hData g
    have hleft : (left g).zOnly + (left g).yz + (left g).all < p := hcap.2.2.trans_lt htotal
    have hmix : (right.yz + right.all) * (left g).all +
        ((left g).yz + (left g).all) * right.all < p :=
      (Nat.add_le_add (Nat.mul_le_mul_left _ hcap.1) (Nat.mul_le_mul_right _ hcap.2.1)).trans_lt hmixed
    obtain ⟨budget, hz⟩ := exists_regular_pair_budget φ F g.1 T p (left g) right hgdiv
      hirr hproper hgate.1 hgate.2.2.2.1 (polynomialIn_surfaceCumulativeFlag g.1)
      hDflag hleft hmix
    have hsub := geometricSeeds_subset K F selected Γ g
    have count := regular_pair_seed_card_le φ (polynomialEmbedding_injective K) support hData
      g.1 T hgdiv (left g) right budget hz selected (seeds g) nodes x u₀ u₁ hx
      p w A e hw hchar hwA hAn (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => hsolution γ (hsub hγ))
      (fun γ hγ => selectedPoint_regular_of_specialization K F selected γ (hregular γ (hsub hγ)))
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => by
        change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
          (surfaceMap (polynomialEmbedding K) D) = 0
        rw [selectedPoint_surface_evaluation K D selected γ, hpartner γ (hsub hγ), map_zero])
      (fun γ hγ => hagreement γ (hsub hγ))
      (RCN243.noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
    exact mul_scale_le_of_pair_bound support nodes.card w A e (seeds g).card
      (left g) right hwA hAn count
  have ⟨hs, hy, ht⟩ := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    Γ.card * (A * (A - w)) ≤ (∑ g, (seeds g).card) * (A * (A - w)) :=
      Nat.mul_le_mul_right _ (card_le_sum_geometricSeeds K F hF.ne_zero selected Γ hsolution)
    _ = ∑ g, (seeds g).card * (A * (A - w)) := Finset.sum_mul _ _ _
    _ ≤ ∑ g, flagMixed (left g) right cut := Finset.sum_le_sum fun g _ => hcomp g
    _ ≤ _ := RCN084.sum_flagMixed_le_of_cumulative left _ _ _ hs hy ht

end

end ProximityPrize.SubmissionLower.Koala6831MovingCarrierPairs
