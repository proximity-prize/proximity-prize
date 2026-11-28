import ProximityPrize.SubmissionLower.R6970Height2308PointwisePair
import ProximityPrize.SubmissionLower.R6970Height2308PrimaryExactSeed03
import ProximityPrize.SubmissionLower.R6970Height2308SeedThreeRescue

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Research6970.Height2308.SeedThree

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


abbrev mainBook : JointLedger.Book := ⟨196881618245884581,4878,109576150771500,1822095353180⟩
abbrev rescueBook : JointLedger.Book := ⟨36413616117674388,22046,714709871655,251265737123⟩

def bounds : RankBoundedNormalBounds _root_.Research6970.Height2308.SeedThreePrimary.plan _root_.Research6970.Height2308.SeedThreePrimary.price _root_.Research6970.Height2308.SeedThreeRescue.plan _root_.Research6970.Height2308.SeedThreeRescue.price
    mainBook rescueBook _root_.Research6970.Height2308.ExactPrimary.Seed03.lossCap where
  main_fee := by rw [_root_.Research6970.Height2308.ExactPrimary.Seed03.fee_eq]
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
    (caps : RowCaps G (_root_.Research6970.Height2313.Lower6960.Prefix6969Rescue.graphShape 2 3))
    {U : ℕ} (fit : 9594 ≤ U)
    (known : Common (evaluated Crt (word M) (bank154 U).shape
      (HelperSource.cutoffCount (bank154 U).shape 179730 M.overhead.toNat 10-1)) G)
    (degree : 2 ≤ jetDegree G) (seed : 3 ≤ seedDegree G)
    (floor : 308364 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G mainBook rescueBook, P.mainGrade=286 ∧ P.rescueGrade=337 :=
  of_rank_pointwise_with_grades F Crt _root_.Research6970.Height2308.SeedThreePrimary.valid _root_.Research6970.Height2308.SeedThreePrimary.priced (_root_.Research6970.Height2308.SeedThreePrimary.sources U fit) _root_.Research6970.Height2308.SeedThreeRescue.sources
    _root_.Research6970.Height2308.SeedThreeRescue.priced _root_.Research6970.Height2308.ExactPrimary.Seed03.pointwise bounds (by decide) lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6970.Height2308.SeedThree
