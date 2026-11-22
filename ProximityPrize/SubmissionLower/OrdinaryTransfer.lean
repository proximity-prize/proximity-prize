import ProximityPrize.SubmissionLower.Numeric2Aux

set_option Elab.async false
namespace OrdinaryTransfer

/-- The witnesses and their support stay valid at every weaker agreement and height limit. -/
def enlarge {cap larger u del} (M : P1.ModelAt cap u del) (hc : cap ≤ larger) :
    P1.ModelAt larger u del :=
  { M with height_bound := M.height_bound.trans hc }

def lowerMark {cap larger u del A a γ S} (M : P1.ModelAt cap u del)
    (hc : cap ≤ larger) (ha : a ≤ A) (B : P1.MarkAt (A := A) M γ S) :
    P1.MarkAt (A := a) (enlarge M hc) γ S :=
  ⟨{ B.bad with agreement := ha.trans B.bad.agreement }, B.avoids_deleted, B.scalar_fixed,
    B.scalar_degree, B.scalar_hits, B.pole_unit, B.identity⟩

def family {cap larger u del Γ A a} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt A M Γ) (hc : cap ≤ larger) (ha : a ≤ A) :
    P1.FamilyAt a (enlarge M hc) Γ :=
  ⟨F.scalar, fun γ hγ => lowerMark M hc ha (F.mark γ hγ), F.distinct⟩

theorem overhead {cap larger u del} (M : P1.ModelAt cap u del) (hc : cap ≤ larger) :
    (enlarge M hc).overhead = M.overhead := rfl

end OrdinaryTransfer
