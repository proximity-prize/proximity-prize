import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group31

private def m0 : MassCell 31 :=
  ⟨⟨1,3,21⟩,mass_cell 31 1 3 21 203 (by decide)
    (by decide +kernel) [4532662882374, 3873008692665, 3115046873319, 2429024708679, 1856625631647, 1385981475567, 1005692686647, 704828323959, 472926059439, 299992177887, 176501576967, 93397767207, 42092871999, 14467627599, 2871383127, 122318529, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 31 :=
  ⟨⟨8,9,57⟩,mass_cell 31 8 9 57 166 (by decide)
    (by decide +kernel) [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2316323663030, 1537285257910, 898533132850, 474145072390, 214743476530, 75499705270, 16134078610, 915876550, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 31 :=
  ⟨⟨72,31,75⟩,mass_cell 31 72 31 75 118 (by decide)
    (by decide +kernel) [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1067841952863, 166265646773, 5350649974, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 31) := [m0, m1, m2]

end Low6960Allocation.Group31
