import ProximityPrize.SubmissionLower.MovingSourceIndexedMovingDegrees6814

/-! One moving budget across ALL assigned slice factors. Ordinary flag
costs are those of the existing slice budgets, while the moving degrees
are summed once using prime injectivity and a common projection. -/
namespace ProximityPrize.SubmissionLower.MovingSourceSliceMovingBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN002 RCN046 RCN064 RCN084 RCN095 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN341 RCN344
open MovingFiberThreeSources6811 MovingSourceExtendedCoefficients6814
open MovingSourceExtendedPointCount6814 MovingSourceExtendedMovingDegrees6814
open MovingSourceIndexedMovingCoordinates6814 MovingSourceIndexedMovingDegrees6814
open MovingSourceSlicePrimeFamily6814 WeightedSliceAssignment6807 SmallSliceBudgets6807

variable {K E : Type} [Field K] [CharP K 2130706433]
  [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta : GenericField K →+* E)
local notation "Poly" => MvPolynomial (Fin 3) E

theorem filteredCut_zero (N H G : Poly) : filteredCut 0 (fun _ => N) H G=N := by
  simp [filteredCut,Fin.sum_univ_one]

theorem targetCut_zero (N Q A : Poly) :
    extendedTargetCut 0 (fun _ => N) Q A=MvPolynomial.map (coefficientEmbedding E) N := by
  simp [extendedTargetCut,eliminatedCut,filteredCut,Fin.sum_univ_one]

theorem exists_slice_moving_budget
    (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (G N : Poly) (hG : G≠0) (hGF : G∣frozenCarrier eta F)
    (hR : frozenH eta F∈Ideal.span ({G,MvPolynomial.pderiv (1 : Fin 3) G} : Set Poly))
    (q : FlagDegree) (hN : PolynomialInFlag q N)
    (B : SliceBudgets G N (frozenH eta F) q)
    (active : Finset (SliceComponent G N (frozenH eta F)))
    (hlead : ∀ a∈active, SZ.leading (codeMap eta)∉a.2.1)
    (scale z u v : ℕ)
    (hbound : ∀ Q A : Poly, (2 : Poly)*A≠0 →
      PolynomialInFlag (2 • unitAllFlag) Q → PolynomialInFlag unitYZFlag A →
      ExtendedPointBudget eta F SZ Q A scale z u v) :
    ∃ moving : ∀ a : active, MovingPoleBudget a.val.2.1 (frozenH eta F) (frozenG eta F),
      (∀ a : active, (moving a).zCost=(B.unit a.val.1).zCost a.val.2 ∧
        (moving a).yzCost=(B.unit a.val.1).yzCost a.val.2 ∧
        (moving a).allCost=(B.unit a.val.1).allCost a.val.2) ∧
      scale*(∑ a : active, (moving a).movingCost)≤q.zOnly*z+q.yz*u+q.all*v := by
  let P (a : active) := a.val.2.1
  let base (a : active) := B.base a.val.1 a.val.2
  obtain ⟨Q,A,projection,hQ,hA,hproj⟩ := exists_indexed_moving_coordinates P base (frozenH eta F) (frozenG eta F)
  let moving (a : active) : MovingPoleBudget (P a) (frozenH eta F) (frozenG eta F) := {
    zCost := (B.unit a.val.1).zCost a.val.2
    yzCost := (B.unit a.val.1).yzCost a.val.2
    allCost := (B.unit a.val.1).allCost a.val.2
    movingCost := SeparableCoordinate.degree E (CoordinateField E (P a)) (projection a)
    zPole := (B.unit a.val.1).zPole a.val.2
    yzPole := (B.unit a.val.1).yzPole a.val.2
    allPole := (B.unit a.val.1).allPole a.val.2
    movingPole := by
      intro W
      calc
        _=∑ nu∈W, RCN346.poleOrder E (CoordinateField E (P a)) nu
            (SeparableCoordinate.value E (CoordinateField E (P a)) (projection a)) := by
          apply Finset.sum_congr rfl
          intro nu _
          exact ((hproj a).2.2 nu).symm
        _≤_ := SeparableCoordinate.finite_sum_pole_le_degree E (CoordinateField E (P a)) (projection a) W }
  refine ⟨moving,fun _ => ⟨rfl,rfl,rfl⟩,?_⟩
  by_cases hactive : Nonempty active
  · let a0 : active := Classical.choice hactive
    have hAne : A≠0 := by intro hz; exact (hproj a0).1 (hz ▸ (P a0).zero_mem)
    have h2 : (2 : Poly)≠0 := (CharP.cast_eq_zero_iff Poly 2130706433 2).not.mpr (by decide)
    let factor (a : active) : Poly := a.val.1.val
    let old (a : active) : ExtendedFactorFamily eta F (factor a) 0 (fun _ => N) :=
      ⟨P a,by simpa only [filteredCut_zero] using a.val.2.property⟩
    have hinj : Function.Injective (fun a : active => (old a).1) := by
      intro a b hab
      apply Subtype.ext
      exact slice_prime_injective G N (frozenH eta F) hG hR hab
    have hcut : PolynomialInFlag q (extendedTargetCut 0 (fun _ => N) Q A) := by
      rw [targetCut_zero]
      exact inFlag_map _ hN
    have hh := sum_indexed_moving_degrees eta F SZ factor
      (fun a => (activeFactors_spec G N a.val.1).2.1.trans hGF)
      Q A scale z u v (hbound Q A (mul_ne_zero h2 hAne) hQ hA)
      0 (fun _ => N) q hcut old hinj (fun a => hlead a.val a.property)
      (fun a => (hproj a).1) projection (fun a => (hproj a).2.1)
    exact hh
  · letI : IsEmpty active := ⟨fun a => hactive ⟨a⟩⟩
    simp

#print axioms exists_slice_moving_budget
end
end ProximityPrize.SubmissionLower.MovingSourceSliceMovingBudget6814
