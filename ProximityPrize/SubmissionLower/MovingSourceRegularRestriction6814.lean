import ProximityPrize.SubmissionLower.MovingSourceHybridCount6814
namespace ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN046 RCN095 RCN264 RCN341 RCN344

variable {K : Type} [Field K]
    {G M R : MvPolynomial (Fin 3) K}

def forgetExtra (L : MvPolynomial (Fin 3) K)
    (C : RegularComponent K G M (R*L)) : RegularComponent K G M R := by
  classical
  exact ⟨C.1,(mem_regularComponents K).mpr ⟨regularComponent_mem K G M (R*L) C,by
    intro hz
    exact regularComponent_H_not_mem K G M (R*L) C (C.1.mul_mem_right L hz)⟩⟩

theorem forgetExtra_injective (L : MvPolynomial (Fin 3) K) :
    Function.Injective (forgetExtra (G:=G) (M:=M) (R:=R) L) := by
  intro C D h
  exact Subtype.ext (congrArg (fun C0 : RegularComponent K G M R => C0.1) h)

theorem extra_not_mem (L : MvPolynomial (Fin 3) K)
    (C : RegularComponent K G M (R*L)) : L∉C.1 := by
  intro hz
  exact regularComponent_H_not_mem K G M (R*L) C (C.1.mul_mem_left R hz)

private theorem sum_pullback_le {I J : Type} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (v : J → ℕ) :
    (∑ i, v (f i))≤∑ j, v j := by
  classical
  letI : DecidableEq J := Classical.decEq J
  calc
    _ = ∑ j ∈ Finset.univ.image f, v j := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def restrict_projection_family [IsAlgClosed K]
    (base : ∀ C : RegularComponent K G M R, SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q)
    (L : MvPolynomial (Fin 3) K) :
    AdaptiveUnitProjectionFamily (fun C => base (forgetExtra L C)) p q where
  zProjection := fun C => unit.zProjection (forgetExtra L C)
  yzProjection := fun C => unit.yzProjection (forgetExtra L C)
  allProjection := fun C => unit.allProjection (forgetExtra L C)
  zValue := fun C => unit.zValue (forgetExtra L C)
  allTranscendental := fun C => unit.allTranscendental (forgetExtra L C)
  zPole_eq := fun C v => unit.zPole_eq (forgetExtra L C) v
  yzPole_eq := fun C v => unit.yzPole_eq (forgetExtra L C) v
  allPole_eq := fun C v => unit.allPole_eq (forgetExtra L C) v
  sum_zDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.zProjection C))).trans unit.sum_zDegree_le
  sum_yzDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C))).trans unit.sum_yzDegree_le
  sum_allDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.allProjection C))).trans unit.sum_allDegree_le

open RCN084 RCN136 RCN207
open MovingFiberThreeSources6811 MovingSourceHybridCount6814

end
end ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
