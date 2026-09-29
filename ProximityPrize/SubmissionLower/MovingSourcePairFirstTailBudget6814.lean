import ProximityPrize.SubmissionLower.MovingSourcePairFirstChannel6814

/-! The actual old first-tail family receives the new pair moving sum.
Its ordinary pole costs remain the old frame's costs. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairFirstTailBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN002 RCN046 RCN064 RCN074 RCN086 RCN095 RCN135 RCN136 RCN198 RCN199 RCN200 RCN207 RCN208 RCN209 RCN264 RCN313 RCN341 RCN344
open MovingFiberThreeSources6811 MovingSourceMovingDegrees6814 MovingSourcePairMovingDegrees6814
open MovingSourceExtendedPointCount6814

variable {K : Type} [Field K] [CharP K 2130706433]
local notation "Ω" => GenericField K
local notation "Poly" => MvPolynomial (Fin 3) Ω

theorem actual_first_tail_pair_degrees {I : Type} [Fintype I]
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (carrier : Poly) (hcarrierF : carrier∣baseCarrier F)
    (a b s w : ℕ) (hw : 1≤w)
    (hR : F.degreeOf 2≤s+2)
    (hYR : RCN234.wt ![0,1,1,0] F≤b+s+3)
    (hAll : RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (Q A : Poly) (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (scale z u v : ℕ) (hbound : ScaledPointBudget F SZ Q A scale z u v)
    (old : I → RegularComponent Ω carrier (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F))
    (hold : Function.Injective old) (hlead : ∀ i, SZ.leading (polynomialEmbedding K)∉(old i).1)
    (hAnonzero : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i)=
      movingValue (old i).1 (baseH F) (baseG F) Q A) :
    let W := RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)
    scale*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i))≤
      W.zOnly*z+W.yz*u+W.all*v := by
  obtain ⟨coeff,flags,heq,hcoeff,hrel⟩ := exists_filtered_certificate (polynomialEmbedding K) a b s F hR hYR hAll
    (w+1) (by omega) (tailSelector (w+1)) 0 0 0
  have heq' : globalTailCut (polynomialEmbedding K) F (w+1)=filteredCut w coeff (baseH F) (baseG F) := heq
  let old' : I → FactorFamily F carrier w coeff := fun i =>
    ⟨(old i).1,by rw [←heq']; exact (old i).2⟩
  have hi : Function.Injective old' := by
    intro i j h
    exact hold (Subtype.ext (congrArg (fun C : FactorFamily F carrier w coeff => C.1) h))
  obtain ⟨hHflag,hGflag⟩ := RCN201.surfaceMap_HG_flags (polynomialEmbedding K) a b s F hR hYR hAll
  have hcut := targetCut_small_flag F a b s w (RCN198.center a b s) coeff flags hHflag hGflag hcoeff hrel Q A hQ hA
  exact sum_moving_degrees_of_pair_budget F SZ carrier hcarrierF Q A scale z u v hbound
    w coeff _ hcut old' hi hlead hAnonzero projection hvalue

theorem exists_first_tail_pair_budget
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (carrier : Poly) (hcarrierF : carrier∣baseCarrier F)
    (a b s w : ℕ) (hw : 1≤w)
    (hR : F.degreeOf 2≤s+2)
    (hYR : RCN234.wt ![0,1,1,0] F≤b+s+3)
    (hAll : RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (base : ∀ C : RegularComponent Ω carrier (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F),
      SeparableLiteralCoordinate C.1)
    (p tailFlag : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p tailFlag)
    (active : Finset (RegularComponent Ω carrier (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F)))
    (hlead : ∀ C∈active, SZ.leading (polynomialEmbedding K)∉C.1)
    (scale z u v : ℕ)
    (hbound : ∀ Q A : Poly, (2 : Poly)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ScaledPointBudget F SZ Q A scale z u v) :
    let W := RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)
    ∃ budget : ∀ C : RegularComponent Ω carrier (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F),
      MovingPoleBudget C.1 (baseH F) (baseG F),
      (∀ C, (budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C) ∧
      scale*(∑ C∈active, (budget C).movingCost)≤W.zOnly*z+W.yz*u+W.all*v := by
  classical
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩ := exists_separable_moving_coordinates
    carrier (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F) (baseG F) base
  let budget := budgetOfProjections carrier (globalTailCut (polynomialEmbedding K) F (w+1))
    (baseH F) (baseG F) unit projection (fun C nu => (hproj C).2.2.1 nu)
  refine ⟨budget,fun _ => ⟨rfl,rfl,rfl⟩,?_⟩
  by_cases he : active=∅
  · simp [he]
  obtain ⟨C0,hC0⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hAne : A≠0 := by intro hz; exact (hproj C0).1 (hz ▸ C0.1.zero_mem)
  have htwo : (2 : Poly)≠0 := (CharP.cast_eq_zero_iff Poly 2130706433 2).not.mpr (by decide)
  have hb := actual_first_tail_pair_degrees F SZ carrier hcarrierF a b s w hw hR hYR hAll Q A hQ hA
    scale z u v (hbound Q A (mul_ne_zero htwo hAne) hQ hA)
    (fun C : active => C.val) Subtype.val_injective (fun C => hlead C.val C.property)
    (fun C => (hproj C.val).1) (fun C => projection C.val) (fun C => (hproj C.val).2.1)
  change scale*(∑ C∈active, SeparableCoordinate.degree Ω (CoordinateField Ω C.1) (projection C))≤_
  rwa [Finset.sum_coe_sort active (fun C => SeparableCoordinate.degree Ω (CoordinateField Ω C.1) (projection C))] at hb

#print axioms exists_first_tail_pair_budget
end
end ProximityPrize.SubmissionLower.MovingSourcePairFirstTailBudget6814
