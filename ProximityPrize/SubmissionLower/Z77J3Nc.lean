import ProximityPrize.SubmissionLower.ZHSmgre
import ProximityPrize.SubmissionLower.ZUt8KUb
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace q7F2qKe
noncomputable section
open Finset Polynomial
open scoped BigOperators Classical
open P5 (K jG)
open P5_7_2 (A fO)
open cu (Jet)
open gT (Ambient)
open pI (xN dual pN)
open TD (FP)

def c2 :Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje A M Γ),
    P5_7_2.Window b M.iF→FixedTariff F b
def c5:Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Input b M F → ∀ o∈origins b,∀ I:Ideal Ambient,
      xN I→ I.height=2 → ¬ dual I→ Individual b o 0 (fun k=>pN I k) →
      ((Γ.filter (I0 F I)).card:ℚ)≤FP (rankPrice b o) fun k=>pN I k
private theorem card_union_cast (s t:Finset K) : ((s∪t).card:ℚ)≤ s.card+t.card:= by
  exact_mod_cast card_union_le s t
private theorem card_biUnion_cast {α:Type*} (s :Finset α) (m:α→Finset K) :
    ((s.biUnion m).card:ℚ) ≤ ∑ i∈s,((m i).card:ℚ) := by
  exact_mod_cast (card_biUnion_le : (s.biUnion m).card ≤ ∑ i∈s,(m i).card)
private theorem le_ceil (x :ℚ) :x≤(x.ceil.toNat :ℚ) :=
  (show x≤(x.ceil:ℚ) from Rat.le_ceil).trans (by exact_mod_cast Int.self_le_toNat x.ceil)
section
variable {b u del M Γ F} {x : @Input b u del M Γ F} {C:aAT F b x}
variable (R:Timeline C)
private def PN (o:ℕ) (f :Jet) (j:ℕ) (I:Ideal Ambient) :Finset K :=
  if j=0 then Γ.filter (I0 F I) else aHl F (R.cuts o f j I)
end
end
end q7F2qKe
