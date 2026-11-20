import ProximityPrize.SubmissionLower.C14BandsAt180255
set_option Elab.async false

/-! Band and height facts needed to assemble `K1_14` (c6 `of_children`, c14 range) for the
6916 radius (A = 180255, e = 81889, L = A - 131072 = 49183). UNBUILT.

* `height_at`: the official height cap is `e + 1 - 7 - L` (Fast006 `native_rank_exception_count`,
  Fast014 `native_minimal_relation_degree`); at A = 180255 it is 32700, which is the last
  endpoint of `bandNew`.
* `bandNew_*`: the four facts `K1_14_6.of_children` extracts from `band` by `decide`
  (Fast055.lean:7948-7962), restated for `bandNew` and A = 180255.
The children `K1_14_6.c1`/`c2` are generic in (d, e, b) and contain no A literal, so they carry
over unchanged; the assembly itself still needs the A-literal port of the K1 definitions. -/

section PackSource_K1_14_AssemblyAt180255
set_option autoImplicit true
namespace K1_14_At

open K1 K1_14

theorem minimal_relation_degree_at (r a b c : ℕ) (hc : c ≤ 131072)
    (hsum : a + b + c = 262146) (hr : r + a + b = 163780) (hr7 : 7 ≤ r) :
    49183 + (131073 - c) + r = 81890 ∧ 131073 - c ≤ 32700 ∧ 131073 - c < 49183 := by
  omega

theorem height_at (r : ℕ) (hr7 : 7 ≤ r) : 81889 + 1 - r - 49183 ≤ 32700 := by omega

theorem bandNew_endpoint (w : ℤ) (hhi : w ≤ 32700) : w ≤ ((bandNew w).endpoint : ℤ) := by
  unfold bandNew
  split_ifs with h1 h2 h3
  · exact h1
  · exact h2
  · exact h3
  · exact hhi

theorem bandNew_degree_lt (w : ℤ) : 131071 + (bandNew w).endpoint < 180255 := by
  unfold bandNew
  split_ifs <;> decide

theorem bandNew_degree_lt_p (w : ℤ) : 131071 + (bandNew w).endpoint < p :=
  (bandNew_degree_lt w).trans (by decide)

theorem bandNew_seed_pos (w : ℤ) : 0 < (bandNew w).seedBound := by
  unfold bandNew
  split_ifs <;> decide

end K1_14_At
end PackSource_K1_14_AssemblyAt180255
