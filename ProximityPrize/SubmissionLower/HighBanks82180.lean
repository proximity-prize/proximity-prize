import ProximityPrize.SubmissionLower.GoldBranch7N2

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighBanks82180

open Finset
open P3 (HighBand)
open P3_7 (Stage Bank debit stages)
open P3_7_2 (BankCertificate checked of_certificate worstWidth)
open K1_14 (Shape shapeSum triangle)

def count (s : Shape) : ℕ :=
  let j := min s.B s.J
  triangle j + (s.B-j)*(j+1)

def width (h r : ℕ) (s : Shape) (q j mode : ℕ) : ℕ :=
  s.m*179964 - 2*h*r + j - q*(131071-h) - mode*(2*h*j)

def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U * shapeSum s (fun q j => width h r s q j mode)

/-- Pay once per coefficient for the nineteen agreements removed from the cutoff. -/
def adjusted (t : Bank) : Bank :=
  {t with nodeRows := t.nodeRows + count t.shape*(19*t.shape.m)}

def start : HighBand → ℕ
  | .h2274 => 2323
  | .h2294 => 2343
  | .h7773 => 7773

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankCertificate lo s.reserve 0 (adjusted s.free) ∧
    BankCertificate lo s.reserve 1 (adjusted s.moving)
private theorem nil {lo : ℕ} : Checks lo [] := fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf : BankCertificate lo s.reserve 0 (adjusted s.free))
    (hm : BankCertificate lo s.reserve 1 (adjusted s.moving))
    (ht : Checks lo ss) : Checks lo (s::ss) := List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩
set_option quotPrecheck false
local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end HighBanks82180
