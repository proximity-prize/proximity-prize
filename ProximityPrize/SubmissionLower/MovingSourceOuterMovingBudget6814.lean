import ProximityPrize.SubmissionLower.MovingSourceCommonChannelBudget6814
namespace ProximityPrize.SubmissionLower.MovingSourceOuterMovingBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN002 RCN046 RCN064 RCN074 RCN086 RCN095 RCN135 RCN136 RCN198 RCN199 RCN200 RCN207 RCN208 RCN209 RCN264 RCN313 RCN341 RCN344
open MovingFiberThreeSources6811 MovingSourceMovingDegrees6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceExtendedPointCount6814 MovingSourceIndexedMovingDegrees6814 MovingSourceIndexedMovingCoordinates6814

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local notation "Ω" => GenericField K
local notation "Poly" => MvPolynomial (Fin 3) Ω

theorem outer_first_tail_pair_degrees
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (G : I → Poly) (hGF : ∀ i, G i∣baseCarrier F)
    (a b s w : ℕ) (hw : 1≤w) (hR : F.degreeOf 2≤s+2)
    (hYR : RCN234.wt ![0,1,1,0] F≤b+s+3) (hAll : RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (Q A : Poly) (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (scale z u v : ℕ) (hbound : ExtendedPointBudget (RingHom.id Ω) F SZ Q A scale z u v)
    (old : ∀ i, RegularComponent Ω (G i) (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F))
    (hold : Function.Injective (fun i => (old i).1)) (hlead : ∀ i, SZ.leading (polynomialEmbedding K)∉(old i).1)
    (hAnonzero : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i)=
      movingValue (old i).1 (baseH F) (baseG F) Q A) :
    let W := RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)
    scale*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i))≤
      W.zOnly*z+W.yz*u+W.all*v := by
  obtain ⟨coeff,flags,heq,hcoeff,hrel⟩ := exists_filtered_certificate (polynomialEmbedding K)
    a b s F hR hYR hAll (w+1) (by omega) (tailSelector (w+1)) 0 0 0
  have heq' : globalTailCut (polynomialEmbedding K) F (w+1)=filteredCut w coeff (baseH F) (baseG F) := heq
  let old' : ∀ i, ExtendedFactorFamily (RingHom.id Ω) F (G i) w coeff := fun i =>
    ⟨(old i).1,by
      change (old i).1∈regularComponents Ω (G i) (filteredCut w coeff (baseH F) (baseG F)) (baseH F)
      rw [←heq']
      exact (old i).2⟩
  obtain ⟨hHflag,hGflag⟩ := RCN201.surfaceMap_HG_flags (polynomialEmbedding K) a b s F hR hYR hAll
  have hcut := targetCut_small_flag F a b s w (RCN198.center a b s) coeff flags hHflag hGflag hcoeff hrel Q A hQ hA
  exact sum_indexed_moving_degrees (RingHom.id Ω) F SZ G hGF Q A scale z u v hbound
    w coeff _ hcut old' hold hlead hAnonzero projection hvalue

theorem exists_outer_first_tail_pair_budget
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (G : I → Poly) (hGF : ∀ i, G i∣baseCarrier F)
    (a b s w : ℕ) (hw : 1≤w) (hR : F.degreeOf 2≤s+2)
    (hYR : RCN234.wt ![0,1,1,0] F≤b+s+3) (hAll : RCN234.wt ![0,1,1,1] F≤a+b+s+3)
    (base : ∀ i, ∀ C : RegularComponent Ω (G i) (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F),
      SeparableLiteralCoordinate C.1)
    (p : I → FlagDegree) (tailFlag : FlagDegree) (unit : ∀ i, AdaptiveUnitProjectionFamily (base i) (p i) tailFlag)
    (old : ∀ i, RegularComponent Ω (G i) (globalTailCut (polynomialEmbedding K) F (w+1)) (baseH F))
    (hold : Function.Injective (fun i => (old i).1))
    (active : Finset I) (hlead : ∀ i∈active, SZ.leading (polynomialEmbedding K)∉(old i).1)
    (scale z u v : ℕ)
    (hbound : ∀ Q A : Poly, (2 : Poly)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget (RingHom.id Ω) F SZ Q A scale z u v) :
    let W := RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)
    ∃ budget : ∀ i, MovingPoleBudget (old i).1 (baseH F) (baseG F),
      (∀ i, (budget i).zCost=(unit i).toPrimeFlagBudgetFamily.zCost (old i) ∧
        (budget i).yzCost=(unit i).toPrimeFlagBudgetFamily.yzCost (old i) ∧
        (budget i).allCost=(unit i).toPrimeFlagBudgetFamily.allCost (old i)) ∧
      scale*(∑ i∈active, (budget i).movingCost)≤W.zOnly*z+W.yz*u+W.all*v := by
  classical
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩ := exists_indexed_moving_coordinates
    (fun i => (old i).1) (fun i => base i (old i)) (baseH F) (baseG F)
  let budget (i : I) : MovingPoleBudget (old i).1 (baseH F) (baseG F) := {
    zCost := (unit i).toPrimeFlagBudgetFamily.zCost (old i)
    yzCost := (unit i).toPrimeFlagBudgetFamily.yzCost (old i)
    allCost := (unit i).toPrimeFlagBudgetFamily.allCost (old i)
    movingCost := SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)
    zPole := (unit i).toAdaptiveUnitPoleBudget.zPole (old i)
    yzPole := (unit i).toAdaptiveUnitPoleBudget.yzPole (old i)
    allPole := (unit i).toAdaptiveUnitPoleBudget.allPole (old i)
    movingPole := by
      intro U
      calc
        _=∑ nu∈U, RCN187.poleOrder nu.val
            (SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i)) := by
          apply Finset.sum_congr rfl
          intro nu _
          exact ((hproj i).2.2 nu).symm
        _≤_ := SeparableCoordinate.finite_sum_pole_le_degree Ω (CoordinateField Ω (old i).1) (projection i) U }
  refine ⟨budget,fun _ => ⟨rfl,rfl,rfl⟩,?_⟩
  by_cases hempty : active=∅
  · simp [hempty]
  obtain ⟨i0,hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hAne : A≠0 := by intro hz; exact (hproj i0).1 (hz ▸ (old i0).1.zero_mem)
  have htwo : (2 : Poly)≠0 := (CharP.cast_eq_zero_iff Poly 2130706433 2).not.mpr (by decide)
  have hb := outer_first_tail_pair_degrees F SZ (fun i : active => G i.val) (fun i => hGF i.val)
    a b s w hw hR hYR hAll Q A hQ hA scale z u v (hbound Q A (mul_ne_zero htwo hAne) hQ hA)
    (fun i => old i.val) (fun i j hh => Subtype.ext (hold hh))
    (fun i => hlead i.val i.property) (fun i => (hproj i.val).1)
    (fun i => projection i.val) (fun i => (hproj i.val).2.1)
  change scale*(∑ i∈active, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i))≤_
  rwa [Finset.sum_coe_sort active (fun i => SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i))] at hb

end
end ProximityPrize.SubmissionLower.MovingSourceOuterMovingBudget6814
