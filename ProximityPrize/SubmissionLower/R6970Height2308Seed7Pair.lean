import ProximityPrize.SubmissionLower.R6970Height2308PointwisePair
import ProximityPrize.SubmissionLower.Bundle6970_6632846eabe9b5ce
import ProximityPrize.SubmissionLower.R6970Height2308Seed7Rescue

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Research6970.Height2308.Seed7

open _root_.Lower6960 _root_.Research6969
open Research6970.Height2313.Lower6960
open Research6970.Height2308
open _root_.Research6969.TransitionPacket (Pair)
open _root_.Research6969.TransitionBanks (bank154)
open Far6969RescueGeometry (Model Family word)
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open PrefixRows (Common)
open Research6966
open Polynomial


abbrev mainBook : JointLedger.Book := ⟨193647081422721663,5339,126333412540560,1836282766952⟩
abbrev rescueBook : JointLedger.Book := ⟨30754142137729235,17346,1522334094943,241867641062⟩

def bounds : RankBoundedNormalBounds _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5.plan _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5.price _root_.Research6970.Height2308.Seed7Rescue.plan _root_.Research6970.Height2308.Seed7Rescue.price
    mainBook rescueBook _root_.Research6970.Height2308.ExactPrimary.Seed07.lossCap where
  main_fee := by rw [_root_.Research6970.Height2308.ExactPrimary.Seed07.fee_eq]
  rescue_fee := le_rfl
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 329
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel

theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j k, (D.block j).eval (nodeL k) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G)
    (caps : RowCaps G (_root_.Research6970.Height2313.Lower6960.Prefix6969Rescue.graphShape 2 7))
    (known : Common (evaluated Crt (word M) _root_.Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape
      (HelperSource.cutoffCount _root_.Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape 179730 M.overhead.toNat 10-1)) G)
    (degree : 2 ≤ jetDegree G) (seed : 7 ≤ seedDegree G)
    (floor : 308251 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G mainBook rescueBook, P.mainGrade=335 ∧ P.rescueGrade=329 :=
  of_rank_pointwise_with_grades F Crt _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5.valid _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5.priced _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5.sources _root_.Research6970.Height2308.Seed7Rescue.sources
    _root_.Research6970.Height2308.Seed7Rescue.priced _root_.Research6970.Height2308.ExactPrimary.Seed07.pointwise bounds (by decide) lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6970.Height2308.Seed7
