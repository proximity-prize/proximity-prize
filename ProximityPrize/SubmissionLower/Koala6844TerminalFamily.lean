import ProximityPrize.SubmissionLower.Koala6844TerminalLong
import ProximityPrize.SubmissionLower.Koala6844TerminalDecode
import ProximityPrize.SubmissionLower.Koala6844ReceiptsFactorSum


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical BigOperators
open RCN095 RCN081 RCN140 RCN156 RCN167 RCN234 RCN266
open LocatorBatchProductRoute Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

variable {K I : Type} [Field K]

def countedRegular (H : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (seeds : Finset K) (F : RegularIndex H) : CountedFactor :=
  ⟨physicalFlag F.1,(regularSeeds H selected seeds F).card,physicalFlag_positive H F,
    physicalFlag_ordered F.1⟩

def regularFamily (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (selected : K → Polynomial K) (seeds : Finset K) : List CountedFactor :=
  remaining.toList.map (countedRegular H selected seeds)

private theorem sum_toList {A : Type} (atoms : Finset A) (f : A → Nat) :
    (atoms.toList.map f).sum = ∑ a ∈ atoms, f a := by
  change ((atoms.toList.map f : List Nat) : Multiset Nat).sum = _
  rw [← Multiset.map_coe,Finset.coe_toList]
  rfl

theorem regularFamily_flag (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (selected : K → Polynomial K) (seeds : Finset K) :
    factorFlags (regularFamily H remaining selected seeds) = physicalFlag (regularProduct H remaining) := by
  unfold factorFlags regularFamily countedRegular physicalFlag
  simp only [List.map_map, Function.comp_apply, sum_toList]
  have h (weights : Fin 4 → ℕ) : wt weights (regularProduct H remaining) =
      ∑ F ∈ remaining, wt weights F.1 :=
    RCN071.weightedTotalDegree_prod_eq weights remaining (fun F => F.1)
      (fun F _ => regularFactor_ne_zero H F)
  rw [h,h,h]

theorem regularFamily_count (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (selected : K → Polynomial K) (seeds : Finset K)
    (hcover : seeds ⊆ remaining.biUnion (regularSeeds H selected seeds)) :
    seeds.card ≤ factorCounts (regularFamily H remaining selected seeds) := by
  unfold factorCounts regularFamily countedRegular
  simp only [List.map_map, Function.comp_apply, sum_toList]
  exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le

theorem terminal_regular_family [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (remaining : Finset (RegularIndex H)) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1)
    (outer : Flag) (src : Sources) (price : Nat) (hprice : terminalPrice outer src = some price)
    (hfo : outer.ordered) (hyL : outer.y ≤ src.totalCap) (hLt : src.totalCap+outer.y ≤ outer.t)
    (hR : outer.r ≤ 19) (hY : outer.y ≤ 82) (hL : src.totalCap ≤ 3873)
    (hfit : (physicalFlag (regularProduct H remaining)).cumulativeLE outer)
    (hshape : ∀ j : Fin 3, (shapeAt src j).carrierFlag.ordered)
    (hdiv : ∀ j : Fin 3, 3*(shapeAt src j).k+3 ∣ graphScale)
    (hk : ∀ j : Fin 3, (shapeAt src j).k < 2130706433)
    (nodes : Finset I) (x u₀ u₁ : I → K) (selected : K → Polynomial K) (seeds : Finset K)
    (data : TerminalSeedData nodes x u₀ u₁ selected seeds)
    (hcover : seeds ⊆ remaining.biUnion (regularSeeds H selected seeds))
    (routes : ∀ F ∈ remaining, src.totalCap < (physicalFlag F.1).t →
      ∀ scope : Flag, (physicalFlag F.1).cumulativeLE scope →
        ∀ rate, longRates scope src = some rate → ∀ j : Fin 3,
          Route F.1 (padFlag scope 2) (shapeAt src j) (regularSeeds H selected seeds F) selected) :
    seeds.card ≤ price := by
  have hbudget (F : RegularIndex H) :
      MvPolynomial.weightedTotalDegree (contactWeights 131071) F.1 ≤ D-1 := by
    have hdiv' := (positiveRFactors_spec H F.1 F.2).2.1
    exact (RCN081.weightedTotalDegree_le_of_dvd _ F.1 H hdiv' hH).trans hcontact
  refine (regularFamily_count H remaining selected seeds hcover).trans
    (factorCounts_le_terminal outer src price (regularFamily H remaining selected seeds)
      hprice hfo hyL hLt (by simpa only [regularFamily_flag] using hfit) ?_ ?_)
  · intro a ha hshort r y hr hy hscope
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp ha
    have hordered : (⟨r,y,src.totalCap⟩ : Flag).ordered := ⟨hscope.2.1,hscope.2.2.1⟩
    exact short_regular_payment H F D hD hDchar (hbudget F) ⟨r,y,src.totalCap⟩ hscope.1
      hordered (hscope.2.2.2.1.trans hR) (hscope.2.2.2.2.trans hY) hL ⟨hr,hy,hshort⟩
      nodes x u₀ u₁ selected seeds data
  · intro a ha hlong scope hFfit rate hrate
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp ha
    exact long_regular_payment H F D hD hDchar (hbudget F) scope src rate (longRates_data hrate) hFfit hlong hshape hdiv hk
      nodes x u₀ u₁ selected seeds data (routes F (Finset.mem_toList.mp hF) hlong scope hFfit rate hrate)

end
end ProximityPrize.SubmissionLower.Koala6844Terminal
