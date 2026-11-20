import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
namespace H21_2
export _root_.K1_14_2 (UsesSeed)
end H21_2



section High_K1_14_2_1Defs
set_option autoImplicit true
namespace H21_2_1

open H21 H21_2

export _root_.K1_14_2_1 (RowCaps)

/-- Number of cutoffs in the buffered telescope, including cutoff zero. -/
def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m * 180139 - 2 * h * r

def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s + j - q * (131071 - h)

def rawVolume (h r : ℕ) (s : Shape) : ℕ :=
  triangle s.U * shapeSum s (rawWidth h r s)

export _root_.K1_14_2_1 (movingCeiling)

end H21_2_1
end High_K1_14_2_1Defs

section High_K1_14_2_1Selection
set_option autoImplicit true
set_option maxSynthPendingDepth 8

namespace H21_2_1

noncomputable section

open H21 H21_2 Polynomial UniqueFactorizationMonoid

open private divisible from ProximityPrize.SubmissionLower.Fast029

export _root_.K1_14_2_1 (exists_layered)

end
end H21_2_1
end High_K1_14_2_1Selection

section High_K1_14_3Defs
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8

namespace H21_3

noncomputable section

open K21 H21 Polynomial
open scoped BigOperators

export _root_.K1_14_3 (JetPlane)
export _root_.K1_14_3 (Surface)

export _root_.K1_14_3 (fixedEmbedding)

export _root_.K1_14_3 (fixedAt)

def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))

export _root_.K1_14_3 (JetCaps)

export _root_.K1_14_3 (RowCaps)

export _root_.K1_14_3 (cheapShape)

export _root_.K1_14_3 (layeredShape)

export _root_.K1_14_3 (reserve)

export _root_.K1_14_3 (fullShape)

def reserveCutoff (h : ℕ) (s : Shape) (i : Fin 4) : ℕ :=
  s.m * 180139 - 1 - 2*h*reserve i

def contactPower (h : ℕ) (s : Shape) (W : ℕ) : ℕ :=
  1 + (s.m * 180139 - 1 - W) / (2*h)

export _root_.K1_14_3 (SeedShift)

export _root_.K1_14_3 (LeadingFilter)

def RankFloor (h : ℕ) (rows : Banks) (s : Shape) : Prop :=
  ∀ W < s.m*180139,
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q*(131071-h) ≤ W+1+j) →
    triangle s.U * shapeSum s (fun q j => W+1+j - q*(131071-h)) ≤
      sourceDebit h s + ∑ t ∈ Finset.range (W+1), Module.finrank FX (rows s t)

export _root_.K1_14_3 (NoMovingCommon)

structure BufferedPair (h : ℕ) (rows : Banks) (i : Fin 4) where
  cheap : Jet
  layered : Jet
  cheap_ne : cheap ≠ 0
  layered_ne : layered ≠ 0
  cheap_mem : cheap ∈ rows (cheapShape i) (reserveCutoff h (cheapShape i) i)
  layered_mem : layered ∈ rows (layeredShape i) (reserveCutoff h (layeredShape i) i)
  cheap_caps : RowCaps cheap (cheapShape i)
  layered_caps : RowCaps layered (layeredShape i)
  no_moving : NoMovingCommon cheap layered

export _root_.K1_14_3 (SeedField)
export _root_.K1_14_3 (SeedClosure)
export _root_.K1_14_3 (JetField)
export _root_.K1_14_3 (JetClosure)
export _root_.K1_14_3 (FibreJet)

export _root_.K1_14_3 (seedGeneric)

export _root_.K1_14_3 (jetGeneric)

export _root_.K1_14_3 (seedFibreEval)

export _root_.K1_14_3 (OnSeedFibre)

export _root_.K1_14_3 (Parent)
namespace Parent
export _root_.K1_14_3.Parent (casesOn height_two jet_side mk rec recOn seed_side)
end Parent

export _root_.K1_14_3 (fibreRow)

export _root_.K1_14_3 (fibrePoint)

export _root_.K1_14_3 (OrderAt)

def BankVanishes (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (s.m*180139 - 1), P ∈ q.asIdeal

export _root_.K1_14_3 (ClearedSeeds)
export _root_.K1_14_3 (ClearedEquation)

export _root_.K1_14_3 (liftEquation)

export _root_.K1_14_3 (clearedDx)

export _root_.K1_14_3 (ordinaryCutter)

export _root_.K1_14_3 (IsClearing)

export _root_.K1_14_3 (Compatible)

def PassStage {h : ℕ} (rows : Banks) (pairs : ∀ i : Fin 4, BufferedPair h rows i)
    (i : Fin 5) (q : Surface) : Prop :=
  if hi : i.val < 4 then
    let j : Fin 4 := ⟨i.val, hi⟩
    BankVanishes rows (cheapShape j) q ∧ BankVanishes rows (layeredShape j) q ∧
      Compatible (pairs j).cheap (pairs j).layered q
  else BankVanishes rows fullShape q

export _root_.K1_14_3 (cutShape)

export _root_.K1_14_3 (Slice)
namespace Slice
export _root_.K1_14_3.Slice (casesOn ctorElim jets mixed noConfusion ordinate rec recOn seed)
end Slice

export _root_.K1_14_3 (SectionField)
export _root_.K1_14_3 (SectionSeeds)
export _root_.K1_14_3 (SectionJet)

export _root_.K1_14_3 (sectionMap)

export _root_.K1_14_3 (sectionScalar)

export _root_.K1_14_3 (sectionEquations)

export _root_.K1_14_3 (sectionDegree)

export _root_.K1_14_3 (mass)

export _root_.K1_14_3 (MassCap)
namespace MassCap
export _root_.K1_14_3.MassCap (casesOn mixed mk ordinate rec recOn seed)
end MassCap

export _root_.K1_14_3 (seedMassCap)

export _root_.K1_14_3 (ordinateMassCap)

export _root_.K1_14_3 (mixedMassCap)

export _root_.K1_14_3 (cutDegree)

export _root_.K1_14_3 (constantDegree)

export _root_.K1_14_3 (SeedCover)
namespace SeedCover
export _root_.K1_14_3.SeedCover (casesOn curve curve_ne mk noConfusion points rec recOn)
end SeedCover

namespace SeedCover
export _root_.K1_14_3.SeedCover (Covers)
end SeedCover

/-- Initial proper-pair cover with its three fixed-ODE packages. -/
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  masses : MassCap parents 2891 60998 381269
  jetMass : mass parents .jets ≤ 3019828
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 381269 + 812 + 2907
  seedPoints : seeds.points.card ≤ 3019828
  ordinates : Finset FX
  ordinateCount : ordinates.card ≤ 2891
  lowJet : JetPlane
  fixedCheap : JetPlane
  fixedLayered : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedCheap_ne : fixedCheap ≠ 0
  fixedLayered_ne : fixedLayered ≠ 0
  lowJet_caps : JetCaps lowJet 381269 60998
  fixedCheap_caps : JetCaps fixedCheap 63 14
  fixedLayered_caps : JetCaps fixedLayered 118 24
  cover : ∀ γ ∈ Γ,
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    fixedAt lowJet (F.scalar γ) = 0 ∨ fixedAt fixedCheap (F.scalar γ) = 0 ∨
    fixedAt fixedLayered (F.scalar γ) = 0 ∨ ∃ q ∈ parents, MarkOn M F q γ

def odePrice (d b j : ℕ) : ℕ :=
  let T := 2*d - 3
  let a := 1 + T*(b-1)
  let v := min a (T*(j-1)+d)
  let gap := 180139-d
  ((262144-d)*((b-j)*v+j*a) + (gap-1))/gap + b*(b-1)+b

export _root_.K1_14_3 (ProjectedProduct)
namespace ProjectedProduct
export _root_.K1_14_3.ProjectedProduct (casesOn divides_leading mk positive primitive rec recOn separable vanishes)
end ProjectedProduct

end
end H21_3
end High_K1_14_3Defs



section High_K1_14_3_2Defs
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace H21_3_2

noncomputable section

open K21 H21 H21_3 Polynomial
open scoped BigOperators

export _root_.K1_14_3_2 (ordinarySeedDegree)

export _root_.K1_14_3_2 (ProperPair)
namespace ProperPair
export _root_.K1_14_3_2.ProperPair (casesOn left_ne mk no_common rec recOn right_ne)
end ProperPair

export _root_.K1_14_3_2 (markEval)

export _root_.K1_14_3_2 (AtSurface)

export _root_.K1_14_3_2 (TwoDimensional)

export _root_.K1_14_3_2 (ComponentsOn)

export _root_.K1_14_3_2 (PreparedPair)
namespace PreparedPair
export _root_.K1_14_3_2.PreparedPair (casesOn cheap cheap_caps cover fixedCheap fixedCheap_caps fixedCheap_ne fixedLayered fixedLayered_caps fixedLayered_ne layered layered_caps mk noConfusion ordinary ordinary_factors ordinary_seed ordinary_y proper rec recOn seedContent seedContent_degree seedContent_ne)
end PreparedPair

export _root_.K1_14_3_2 (FourMassCap)
namespace FourMassCap
export _root_.K1_14_3_2.FourMassCap (casesOn jets mixed mk ordinate rec recOn seed)
end FourMassCap

export _root_.K1_14_3_2 (SeedDominant)

export _root_.K1_14_3_2 (JetDominant)

export _root_.K1_14_3_2 (totalSectionDegree)

end
end H21_3_2
end High_K1_14_3_2Defs

section High_K1_14_3Count
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace H21_3

noncomputable section

open K21 H21 Polynomial
open scoped BigOperators Classical

export _root_.K1_14_3 (seed_count)

export _root_.K1_14_3 (scalar_atX_injective)

theorem label_injective {u del} (M : AnchorModel u del) : Function.Injective M.label :=
  fun _ _ h => sub_left_inj.mp h

export _root_.K1_14_3 (joinCovers)

export _root_.K1_14_3 (joinCovers_degree)

export _root_.K1_14_3 (joinCovers_points)

export _root_.K1_14_3 (joinCovers_covers)

/-- The degree budgets add over the actual lost parents. -/
theorem combine_cut_covers {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (s : Shape) (lost : Finset Surface)
    (hcut : ∀ q ∈ lost, ∃ C : SeedCover,
      (C.curve.totalDegree : ℚ) ≤ cutDegree s {q} ∧
      (C.points.card : ℚ) ≤ constantDegree s {q} ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → C.Covers (M.label γ)) :
    ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ cutDegree s lost ∧
      (C.points.card : ℚ) ≤ constantDegree s lost ∧
      ∀ γ ∈ Γ, (∃ q ∈ lost, MarkOn M F q γ) → C.Covers (M.label γ) := by
  classical
  let C (q : Surface) : SeedCover :=
    if hq : q ∈ lost then Classical.choose (hcut q hq) else ⟨1, one_ne_zero, ∅⟩
  have hC (q) (hq : q ∈ lost) :
      ((C q).curve.totalDegree : ℚ) ≤ cutDegree s {q} ∧
      ((C q).points.card : ℚ) ≤ constantDegree s {q} ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → (C q).Covers (M.label γ) := by
    simpa only [C, dite_eq_left hq] using Classical.choose_spec (hcut q hq)
  refine ⟨joinCovers lost C, ?_, ?_, ?_⟩
  · calc
      _ ≤ ∑ q ∈ lost, ((C q).curve.totalDegree : ℚ) := by
        exact_mod_cast joinCovers_degree lost C
      _ ≤ ∑ q ∈ lost, cutDegree s {q} := Finset.sum_le_sum (fun q hq => (hC q hq).1)
      _ = _ := by simp [cutDegree, mass, Finset.sum_add_distrib, Finset.mul_sum]
  · calc
      _ ≤ ∑ q ∈ lost, ((C q).points.card : ℚ) := by
        exact_mod_cast joinCovers_points lost C
      _ ≤ ∑ q ∈ lost, constantDegree s {q} := Finset.sum_le_sum (fun q hq => (hC q hq).2.1)
      _ = _ := by simp [constantDegree, mass, Finset.sum_add_distrib, Finset.mul_sum]
  · rintro γ hγ ⟨q, hq, hqγ⟩
    exact joinCovers_covers hq ((hC q hq).2.2 γ hγ hqγ)

export _root_.K1_14_3 (mass_sdiff)

export _root_.K1_14_3 (mass_nonneg)

export _root_.K1_14_3 (moving_loss_bound)

export _root_.K1_14_3 (constant_loss_bound)

theorem endpoint_fees (w : ℤ) (hlo : 3555 ≤ w) :
    (p+1)*(381269+812+2907) + 3019828 + 2891 +
      odePrice (131071 + (band w).endpoint) 381269 60998 +
      odePrice (131071 + (band w).endpoint) 63 14 +
      odePrice (131071 + (band w).endpoint) 118 24 +
      ((p+1)*54375137 + 26769366519) ≤ highPrefix w := by
  have hnot : ¬ w ≤ 3554 := by omega
  unfold band highPrefix
  simp only [hnot, ite_false]
  split_ifs <;> decide

theorem endpoint_range (w : ℤ) (hlo : 3555 ≤ w) (hhi : w ≤ 32932) :
    w ≤ (band w).endpoint ∧ 8249 ≤ (band w).endpoint ∧ (band w).endpoint ≤ 32932 := by
  unfold band
  split_ifs <;> norm_num at * <;> omega

end
end H21_3
end High_K1_14_3Count
