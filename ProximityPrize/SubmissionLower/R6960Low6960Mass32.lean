import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group32

private def m0 : MassCell 32 :=
  ⟨⟨1,3,30⟩,mass_cell 32 1 3 30 212 (by decide)
    (by decide +kernel) [4505854168299, 3823260910383, 3177485012491, 2470853384949, 1873807173669, 1388429167485, 1000684495101, 697369695141, 466112716149, 295372916589, 174441064845, 93439339221, 43321327941, 15872029149, 3707850909, 276611205, 1919, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 32 :=
  ⟨⟨8,8,62⟩,mass_cell 32 8 8 62 178 (by decide)
    (by decide +kernel) [4505854168299, 3823260910383, 3220445335251, 2691032304855, 2228906461755, 1636958777683, 994802287847, 557751582811, 279136472239, 117559460579, 36895747063, 6293225707, 177381184, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 32 :=
  ⟨⟨10,28,79⟩,mass_cell 32 10 28 79 126 (by decide)
    (by decide +kernel) [4505854168299, 3823260910383, 3220445335251, 2691032304855, 2228906461755, 1828212229119, 1327526402882, 415128471789, 50489593713, 246815969, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 32) := [m0, m1, m2]

end Low6960Allocation.Group32
