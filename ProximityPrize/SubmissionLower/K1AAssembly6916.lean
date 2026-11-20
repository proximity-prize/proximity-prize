import ProximityPrize.SubmissionLower.K1AListAt180255
import ProximityPrize.SubmissionLower.K1AChildren17At180255
import ProximityPrize.SubmissionLower.K1AChild2At180255
import ProximityPrize.SubmissionLower.K1AChildren345At180255
import ProximityPrize.SubmissionLower.K1AChild6At180255
import ProximityPrize.SubmissionLower.K1AChild8At180255
import ProximityPrize.SubmissionLower.K1AChild9At180255
import ProximityPrize.SubmissionLower.K1AChild10At180255
import ProximityPrize.SubmissionLower.K1AChild11At180255
import ProximityPrize.SubmissionLower.K1AChild12At180255
import ProximityPrize.SubmissionLower.K1AChild13At180255
set_option Elab.async false

/-! Budget instance and short-route assembly at the 6916 radius (A = 180255).

Every child whose source exists (c0..c12) is plugged in; the remaining hypotheses are exactly
the open obligations:
* `K1A_13.c1 .. c8` (the A'-ported K1_13 children, 216 leaves in the official tree), and
* `K1A.c14 Bg6916` with `high w = 242917318055663462` (= total - c12 - rankBound, the maximum
  admitted by `Budget.Valid`; ONLY the allowance is checked here — the c14 band paths at A'
  (≤ 234901821509846093 with official highPrefix) are not Lean-proved and highPrefix at A' is
  not re-derived).
The final `ProtocolClaim`/`ScalarMCACap` at radius 81889/262144 still needs a 6916 copy of
`Native.ScalarMCACap6915`/`nativeCap_of_scalarCap`/`protocolClaim6915_of_scalarCap`
(Fast015.lean:644-700) with a new allowance; not written here.
UNBUILT. -/

section PackSource_K1AAssembly6916
set_option autoImplicit true
namespace K1A_6916
noncomputable section
open K1A

def Bg6916 : Budget where
  list := 31924061854636696
  c2 := 181820280647725573
  c3 := 311326
  c4 := 733035456970722
  c5 := 174483549798370
  c6 := 1666641901125632
  c9 := 81890
  c10 := 117080401567220092
  c11 := 98729016819426202
  c12 := 69674100686646
  c13 := 242716246186441406
  high := fun _ => 242917318055663462
  total := 243056666256758391

theorem rankBound_eq : rankBound = 69674100408283 := by decide

theorem valid : Bg6916.Valid where
  c2 := by decide
  c3 := by decide
  typeOne := by decide
  c4 := by decide
  c5 := by decide
  c6 := by rw [rankBound_eq]; decide
  empty := by rw [rankBound_eq]; decide
  c9 := by decide
  c10 := by decide
  c11 := by rw [rankBound_eq]; decide
  cheap := by rw [rankBound_eq]; decide
  list := by rw [rankBound_eq]; decide
  c13 := by rw [rankBound_eq]; decide
  c14 := fun _ _ _ => by rw [rankBound_eq]; decide

theorem c13_6916 (h1 : K1A_13.c1) (h2 : K1A_13.c2) (h3 : K1A_13.c3) (h4 : K1A_13.c4)
    (h5 : K1A_13.c5) (h6 : K1A_13.c6) (h7 : K1A_13.c7) (h8 : K1A_13.c8) : c13 Bg6916 :=
  K1A_13.of_children h1 h2 h3 h4 h5 h6 h7 h8 (by decide)

/-- Short route at A = 180255 with every sourced child plugged in. -/
theorem short_route_6916 (h13 : c13 Bg6916) (h14 : c14 Bg6916)
    (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 243056666256758391 :=
  short_route_bound valid (c0_of_list Bg6916 le_rfl) K1A_1.proof (K1A_2.c2_of Bg6916 le_rfl)
    (K1A_3.c3_of Bg6916 le_rfl) (K1A_4.c4_of Bg6916 le_rfl) (K1A_5.c5_of Bg6916 le_rfl)
    (K1A_6.c6_of Bg6916 le_rfl) K1A_7.proof (K1A_8.of_children K1A_8_1.proof K1A_8_2.proof)
    (K1A_9.c9_of Bg6916 le_rfl) (K1A_10.c10_of Bg6916 le_rfl) (K1A_11.c11_of Bg6916 le_rfl)
    (K1A_12.c12_of Bg6916 le_rfl) h13 h14 u Γ hΓ

theorem short_route_6916_of_c13_children (h1 : K1A_13.c1) (h2 : K1A_13.c2) (h3 : K1A_13.c3)
    (h4 : K1A_13.c4) (h5 : K1A_13.c5) (h6 : K1A_13.c6) (h7 : K1A_13.c7) (h8 : K1A_13.c8)
    (h14 : c14 Bg6916) (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ 243056666256758391 :=
  short_route_6916 (c13_6916 h1 h2 h3 h4 h5 h6 h7 h8) h14 u Γ hΓ

end
end K1A_6916
end PackSource_K1AAssembly6916
