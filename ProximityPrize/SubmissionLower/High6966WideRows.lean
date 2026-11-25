import ProximityPrize.SubmissionLower.High6966Main20142
import ProximityPrize.SubmissionLower.High6966WideHelper

set_option Elab.async false

namespace Lower6960.High6966Main20142
open Rescue6966 (Model Family word)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
theorem source_rows {u deleted} {M:Model u deleted} {Γ} (F:Family M Γ)
    {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (lo:2330≤M.overhead.toNat) (hi:M.overhead.toNat≤33677)
    (noPole:∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues:∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (Rows F Crt) :=
  rows F Crt lo hi noPole residues (Wide6966Helper.helper_nonzero Crt (word M) lo hi)
    (fun _ _ g i cop => Wide6966Helper.helper_not_two Crt (word M) lo hi g.1 i.1 cop
      g.2.1 i.2.1 g.2.2.1 i.2.2.1 g.2.2.2 i.2.2.2)
#print axioms source_rows
end Lower6960.High6966Main20142
