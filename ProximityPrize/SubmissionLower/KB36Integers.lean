/- Apache-2.0. Bome2017. Exact 68.36 score and field-capacity inequalities. -/

namespace Koala6836.ProtocolInt
set_option maxRecDepth 20000
theorem score_root_integer :
    (2 : Nat)^36 * 100000000^100 ≤ 128342590^100 := by
  decide +kernel

theorem score_radius_integer :
    (741531649 : Nat)^128 * (2^68 * 128342590) ≤ 100000000 * 1073741824^128 := by
  decide +kernel

theorem capacity : 2^(128:Nat)*(274980640798883310+87312511777) ≤ 2130706433^6 := by decide +kernel
#print axioms score_root_integer
#print axioms score_radius_integer
#print axioms capacity
end Koala6836.ProtocolInt
