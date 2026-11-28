import ProximityPrize.SubmissionLower.R6970Height2308PointwisePair
import ProximityPrize.SubmissionLower.R6970Height2308PrimaryExactSeed02
import ProximityPrize.SubmissionLower.R6970Height2308SeedTwoRescue

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Research6970.Height2308.SeedTwo

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


abbrev mainBook : JointLedger.Book := ⟨198354486275453699,4913,109783487471040,1822026209648⟩
abbrev rescueBook : JointLedger.Book := ⟨38879759036669888,23021,499017450260,260421232025⟩

def bounds : RankBoundedNormalBounds _root_.Research6970.Height2308.SeedTwoPrimary.plan _root_.Research6970.Height2308.SeedTwoPrimary.price _root_.Research6970.Height2308.SeedTwoRescue.plan _root_.Research6970.Height2308.SeedTwoRescue.price
    mainBook rescueBook _root_.Research6970.Height2308.ExactPrimary.Seed02.lossCap where
  main_fee := by rw [_root_.Research6970.Height2308.ExactPrimary.Seed02.fee_eq]
  rescue_fee := le_rfl
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 286
  rescueGrade := 337
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel

theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j k, (D.block j).eval (nodeL k) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G)
    (caps : RowCaps G (_root_.Research6970.Height2313.Lower6960.Prefix6969Rescue.graphShape 2 2))
    {U : ℕ} (fit : 9716 ≤ U)
    (known : Common (evaluated Crt (word M) (bank154 U).shape
      (HelperSource.cutoffCount (bank154 U).shape 179730 M.overhead.toNat 10-1)) G)
    (degree : 2 ≤ jetDegree G) (seed : 2 ≤ seedDegree G)
    (floor : 308378 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G mainBook rescueBook, P.mainGrade=286 ∧ P.rescueGrade=337 :=
  of_rank_pointwise_with_grades F Crt _root_.Research6970.Height2308.SeedTwoPrimary.valid _root_.Research6970.Height2308.SeedTwoPrimary.priced (_root_.Research6970.Height2308.SeedTwoPrimary.sources U fit) _root_.Research6970.Height2308.SeedTwoRescue.sources
    _root_.Research6970.Height2308.SeedTwoRescue.priced _root_.Research6970.Height2308.ExactPrimary.Seed02.pointwise bounds (by decide) lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6970.Height2308.SeedTwo
