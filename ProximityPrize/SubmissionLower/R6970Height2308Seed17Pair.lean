import ProximityPrize.SubmissionLower.R6970Height2308PointwiseDirectPair
import ProximityPrize.SubmissionLower.Bundle6970_6632846eabe9b5ce
import ProximityPrize.SubmissionLower.R6970Height2313NormalPlans01

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Research6970.Height2308.Seed17

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


abbrev mainBook : JointLedger.Book := ⟨181043128054534460,4979,124546966494840,1834670642428⟩
abbrev rescueBook : JointLedger.Book := ⟨11655159682270253,8935,3511151355600,239614962000⟩

def bounds : RankBoundedNormalBounds _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15.plan _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15.price _root_.Research6970.Height2313.Research6969.NormalPrefixData.Seed17.plan (directLedger _root_.Research6970.Height2313.Research6969.NormalPrefixData.Seed17.price)
    mainBook rescueBook _root_.Research6970.Height2308.ExactPrimary.Seed17.lossCap where
  main_fee := by rw [_root_.Research6970.Height2308.ExactPrimary.Seed17.fee_eq]
  rescue_fee := le_rfl
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 292
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel

theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j k, (D.block j).eval (nodeL k) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G)
    (caps : RowCaps G (_root_.Research6970.Height2313.Lower6960.Prefix6969Rescue.graphShape 2 17))
    (known : Common (evaluated Crt (word M) _root_.Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape
      (HelperSource.cutoffCount _root_.Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape 179730 M.overhead.toNat 10-1)) G)
    (degree : 2 ≤ jetDegree G) (seed : 17 ≤ seedDegree G)
    (floor : 307566 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G mainBook rescueBook, P.mainGrade=335 ∧ P.rescueGrade=292 :=
  of_rank_pointwise_with_direct_rescue F Crt _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15.valid _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15.priced _root_.Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15.sources _root_.Research6970.Height2313.Research6969.NormalPrefixData.Seed17.sources
    _root_.Research6970.Height2313.Research6969.NormalPrefixData.Seed17.priced _root_.Research6970.Height2308.ExactPrimary.Seed17.pointwise bounds (by decide) lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6970.Height2308.Seed17
