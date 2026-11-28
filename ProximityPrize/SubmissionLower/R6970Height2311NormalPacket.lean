import ProximityPrize.SubmissionLower.R6970Height2308Seed18Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed17Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed16Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed15Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed14Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed13Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed12Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed11Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed10Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed9Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed8Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed7Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed6Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed5Pair
import ProximityPrize.SubmissionLower.R6970Height2308Seed4Pair
import ProximityPrize.SubmissionLower.R6970Height2308SeedThreePair
import ProximityPrize.SubmissionLower.R6970Height2308SeedTwoPair
import ProximityPrize.SubmissionLower.R6970Height2308SeedOnePair
import ProximityPrize.SubmissionLower.R6970Height2313PairState
import ProximityPrize.SubmissionLower.R6970Height2313PairReduce

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0829
set_option autoImplicit true
namespace Research6969.TransitionPacket.NormalCatalogue
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14 (Equation)
open K1_14_3 (ProjectedProduct SeedField)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Research6966
open _root_.Research6969.TransitionPacket (Pair)
open _root_.Lower6960.Far6969RescueGeometry (Model Family word)
open scoped Classical
set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

abbrev seed (i : Fin 18) : ℕ := i.val+1
def floor (i : Fin 18) : ℕ := ![308385, 308378, 308364, 308344, 308319, 308288, 308251, 308209, 308161, 308107, 308048, 307983, 307912, 307836, 307754, 307664, 307566, 307462] i
abbrev savedMainGrade := Research6970.Height2313.Research6969.BookView.savedMainGrade
abbrev savedRescueGrade := Research6970.Height2313.Research6969.BookView.savedRescueGrade
abbrev mainBook := Research6970.Height2313.Research6969.BookView.mainBook
abbrev rescueBook := Research6970.Height2313.Research6969.BookView.rescueBook


private theorem weaken_grades {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {m r : JointLedger.Book}
    {oldM oldR newM newR : ℕ} (growM : oldM ≤ newM) (growR : oldR ≤ newR)
    (existsPair : ∃ P : Pair F Crt G m r, P.mainGrade=oldM ∧ P.rescueGrade=oldR) :
    ∃ P : Pair F Crt G m r, P.mainGrade=newM ∧ P.rescueGrade=newR := by
  obtain ⟨P, capM, capR⟩ := existsPair
  let Q : Pair F Crt G m r := {
    P with
    mainGrade := newM
    rescueGrade := newR
    mainDegreeCap := P.mainDegreeCap.trans (capM.trans_le growM)
    rescueDegreeCap := P.rescueDegreeCap.trans (capR.trans_le growR)
  }
  exact ⟨Q,rfl,rfl⟩

theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (i : Fin 18)
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j k, (D.block j).eval (nodeL k) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (_root_.Lower6960.Prefix6969Rescue.graphShape 2 (seed i)))
    (known : PrefixRows.Common (evaluated Crt (word M) Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape
      (Research6970.Height2313.Lower6960.Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed_lower : seed i ≤ seedDegree G)
    (physical : floor i ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G (mainBook i) (rescueBook i),
      P.mainGrade=savedMainGrade i ∧ P.rescueGrade=savedRescueGrade i := by
  fin_cases i
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.SeedOne.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps (U := 10281) (by decide) known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.SeedTwo.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps (U := 10281) (by decide) known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.SeedThree.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps (U := 10281) (by decide) known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed4.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed5.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed6.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed7.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed8.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed9.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed10.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed11.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed12.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed13.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed14.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed15.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed16.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed17.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)
  · exact weaken_grades (by decide) (by decide)
      (_root_.Research6970.Height2308.Seed18.packet_with_grades F Crt lo hi noPole residues phys prime slope seeded caps known degree seed_lower physical)

def Reducer : Prop :=
  ∀ {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet}
    (i : Fin 18) (P : Pair F Crt G (mainBook i) (rescueBook i)),
    2308 ≤ M.overhead.toNat → M.overhead.toNat ≤ 2313 →
    Prime G → G.natDegree = 1 → 2 ≤ jetDegree G →
    RowCaps G (Prefix6969Rescue.graphShape 2 (seed i)) →
    Γ.card≤274779381266040419 ∨ ∃ (f : Equation) (H : Pade.Row SeedField),
      ProjectedProduct (P.main∪P.rescue) f ∧ 22≤f.natDegree ∧ H.primitive ∧
      H.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (H.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue))
        (TransitionClassification.content (TransitionClassification.band f.natDegree))

end
end Research6969.TransitionPacket.NormalCatalogue
end Z6969Source0829


end Research6970.Height2313
