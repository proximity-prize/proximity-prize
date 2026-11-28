import ProximityPrize.SubmissionLower.R6970Height2308ContentAdapter
import ProximityPrize.SubmissionLower.R6970Height2313AlternateContracts
import ProximityPrize.SubmissionLower.R6970Height2313AlternateNew
import ProximityPrize.SubmissionLower.Bundle6970_7a0ead0a3fc2768d
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.R6970Height2313MeasuredTests03
import ProximityPrize.SubmissionLower.R6970Height2313AlternateReuse

section Pack_R6970Height2308PaidPair100

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3600 : PairRoute.Done (3:Fin 18) ⟨⟨41,49,9,3,23,(some 24)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨41,49,9,3,23,(some 24),0,none,386273,[MeasuredChoices.test896,MeasuredChoices.test898],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p3601 : PairRoute.Done (3:Fin 18) ⟨⟨41,49,9,3,21,(some 22)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 21
    (PairLeaves.paired ⟨41,49,9,3,21,(some 21),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,22,(some 22),0,none,386273,[MeasuredChoices.test882,MeasuredChoices.test884],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p3602 : PairRoute.Done (3:Fin 18) ⟨⟨41,49,9,3,19,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 19
    (PairRoute.axes_of_total (PairRoute.axis 9
    (PairRoute.axis 4
    (PairLeaves.paired ⟨41,49,9,3,19,(some 19),0,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1821,AlternateBanks.test26221]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairRoute.axis 7
    (PairLeaves.paired ⟨41,49,9,3,19,(some 19),5,(some 7),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1826]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,19,(some 19),8,(some 9),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1829]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))))
    (PairRoute.axis 14
    (PairRoute.axis 12
    (PairLeaves.paired ⟨41,49,9,3,19,(some 19),10,(some 12),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AlternateBanks.test26219]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,19,(some 19),13,(some 14),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1834]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))
    (PairLeaves.paired ⟨41,49,9,3,19,(some 19),15,(some 19),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1836]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))))
    (PairLeaves.paired ⟨41,49,9,3,20,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test856],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p3603 : PairRoute.Done (3:Fin 18) ⟨⟨41,49,9,3,17,(some 18)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 17
    (PairRoute.axes_of_total (PairRoute.axis 8
    (PairRoute.axis 4
    (PairLeaves.paired ⟨41,49,9,3,17,(some 17),0,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1821,AlternateBanks.test26221]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,17,(some 17),5,(some 8),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1826]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))
    (PairRoute.axis 13
    (PairRoute.axis 11
    (PairLeaves.paired ⟨41,49,9,3,17,(some 17),9,(some 11),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1830]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,17,(some 17),12,(some 13),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1833]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))
    (PairLeaves.paired ⟨41,49,9,3,17,(some 17),14,(some 17),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1835]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))))
    (PairLeaves.paired ⟨41,49,9,3,18,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test831],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p3604 : PairRoute.Done (3:Fin 18) ⟨⟨41,49,9,3,15,(some 16)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 15
    (PairLeaves.paired ⟨41,49,9,3,15,(some 15),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairRoute.axes_of_total (PairRoute.axis 8
    (PairRoute.axis 4
    (PairLeaves.paired ⟨41,49,9,3,16,(some 16),0,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test807],[AxisChoices.test1821,AlternateBanks.test26221]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,16,(some 16),5,(some 8),386273,[MeasuredChoices.test773,MeasuredChoices.test807],[AxisChoices.test1826]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))
    (PairRoute.axis 12
    (PairRoute.axis 10
    (PairLeaves.paired ⟨41,49,9,3,16,(some 16),9,(some 10),386273,[MeasuredChoices.test773,MeasuredChoices.test807],[AxisChoices.test1830]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,16,(some 16),11,(some 12),386273,[MeasuredChoices.test773,MeasuredChoices.test807],[AlternateBanks.test26225]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))
    (PairLeaves.paired ⟨41,49,9,3,16,(some 16),13,(some 16),386273,[MeasuredChoices.test773,MeasuredChoices.test807],[AxisChoices.test1834]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))))))

theorem p3607 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,61,(some 64)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,61,(some 64),0,none,257515,[MeasuredChoices.test85],[]⟩ ⟨.marked,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p3608 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,59,(some 60)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,59,(some 60),0,none,257515,[MeasuredChoices.test82],[]⟩ ⟨.marked,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p3610 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,58,(some 58)⟩,0,none,283522,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,58,(some 58),0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩ ⟨.marked,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair100

section Pack_R6970Height2308PaidPair101

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3641 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),30,(some 30),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p3642 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),31,(some 31),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1794]⟩ (by decide +kernel) none))

theorem p3659 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),48,(some 48),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p3660 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),49,(some 49),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p3661 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),50,(some 50),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1813]⟩ (by decide +kernel) none))

theorem p3662 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),51,(some 51),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1814]⟩ (by decide +kernel) none))

theorem p3663 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,52,(some 52),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),52,(some 52),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1815]⟩ (by decide +kernel) none))

theorem p3664 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,53,(some 53),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),53,(some 53),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1816]⟩ (by decide +kernel) none))

theorem p3665 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,54,(some 54),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),54,(some 54),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1817]⟩ (by decide +kernel) none))

theorem p3666 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,55,(some 55),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),55,(some 55),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1817]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair101

section Pack_R6970Height2308PaidPair102

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3699 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),30,(some 30),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p3700 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),31,(some 31),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1794]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair102

section Pack_R6970Height2308PaidPair103

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3717 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),48,(some 48),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p3718 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),49,(some 49),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p3719 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),50,(some 50),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1813]⟩ (by decide +kernel) none))

theorem p3720 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),51,(some 51),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1814]⟩ (by decide +kernel) none))

theorem p3721 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,52,(some 52),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),52,(some 52),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1815]⟩ (by decide +kernel) none))

theorem p3722 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,53,(some 53),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),53,(some 53),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1816]⟩ (by decide +kernel) none))

theorem p3723 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,54,(some 54),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),54,(some 54),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1817]⟩ (by decide +kernel) none))

theorem p3724 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,56,(some 56)⟩,55,(some 55),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,56,(some 56),55,(some 55),257515,[MeasuredChoices.test76,MeasuredChoices.test77],[AxisChoices.test1817]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair103

section Pack_R6970Height2308PaidPair104

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3756 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),30,(some 30),257515,[MeasuredChoices.test74],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p3757 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),31,(some 31),257515,[MeasuredChoices.test74],[AxisChoices.test1794]⟩ (by decide +kernel) none))

theorem p3774 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),48,(some 48),257515,[MeasuredChoices.test74],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p3775 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),49,(some 49),257515,[MeasuredChoices.test74],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p3776 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),50,(some 50),257515,[MeasuredChoices.test74],[AxisChoices.test1813]⟩ (by decide +kernel) none))

theorem p3777 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),51,(some 51),257515,[MeasuredChoices.test74],[AxisChoices.test1814]⟩ (by decide +kernel) none))

theorem p3778 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,52,(some 52),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),52,(some 52),257515,[MeasuredChoices.test74],[AxisChoices.test1815]⟩ (by decide +kernel) none))

theorem p3779 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,53,(some 53),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),53,(some 53),257515,[MeasuredChoices.test74],[AxisChoices.test1816]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair104

section Pack_R6970Height2308PaidPair105

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3780 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,54,(some 54),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),54,(some 54),257515,[MeasuredChoices.test74],[AxisChoices.test1817]⟩ (by decide +kernel) none))

theorem p3781 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,55,(some 55)⟩,55,(some 55),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,55,(some 55),55,(some 55),257515,[MeasuredChoices.test74],[AxisChoices.test1817]⟩ (by decide +kernel) none))

theorem p3812 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),30,(some 30),257515,[MeasuredChoices.test73],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p3813 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),31,(some 31),257515,[MeasuredChoices.test73],[AxisChoices.test1794]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair105

section Pack_R6970Height2308PaidPair106

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3830 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),48,(some 48),257515,[MeasuredChoices.test73],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p3831 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),49,(some 49),257515,[MeasuredChoices.test73],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p3832 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),50,(some 50),257515,[MeasuredChoices.test73],[AxisChoices.test1813]⟩ (by decide +kernel) none))

theorem p3833 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),51,(some 51),257515,[MeasuredChoices.test73],[AxisChoices.test1814]⟩ (by decide +kernel) none))

theorem p3834 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,52,(some 52),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),52,(some 52),257515,[MeasuredChoices.test73],[AxisChoices.test1815]⟩ (by decide +kernel) none))

theorem p3835 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,53,(some 53),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),53,(some 53),257515,[MeasuredChoices.test73],[AxisChoices.test1816]⟩ (by decide +kernel) none))

theorem p3836 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,54,(some 54)⟩,54,(some 54),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,54,(some 54),54,(some 54),257515,[MeasuredChoices.test73],[AxisChoices.test1817]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair106

section Pack_R6970Height2308PaidPair107

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3867 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),30,(some 30),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p3868 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),31,(some 31),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1794]⟩ (by decide +kernel) none))

theorem p3885 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),48,(some 48),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p3886 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),49,(some 49),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p3887 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),50,(some 50),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1813]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair107

section Pack_R6970Height2308PaidPair108

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3888 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),51,(some 51),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1814]⟩ (by decide +kernel) none))

theorem p3889 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,52,(some 52),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),52,(some 52),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1815]⟩ (by decide +kernel) none))

theorem p3890 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,53,(some 53)⟩,53,(some 53),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,53,(some 53),53,(some 53),257515,[MeasuredChoices.test70,MeasuredChoices.test71],[AxisChoices.test1816]⟩ (by decide +kernel) none))

theorem p3921 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,(some 52)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,52,(some 52),30,(some 30),257515,[MeasuredChoices.test66,MeasuredChoices.test69],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p3922 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,(some 52)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,52,(some 52),31,(some 31),257515,[MeasuredChoices.test66,MeasuredChoices.test69],[AxisChoices.test1794]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair108

section Pack_R6970Height2308PaidPair109

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3939 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,(some 52)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,52,(some 52),48,(some 48),257515,[MeasuredChoices.test66,MeasuredChoices.test69],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p3940 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,(some 52)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,52,(some 52),49,(some 49),257515,[MeasuredChoices.test66,MeasuredChoices.test69],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p3941 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,(some 52)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,52,(some 52),50,(some 50),257515,[MeasuredChoices.test66,MeasuredChoices.test69],[AxisChoices.test1813]⟩ (by decide +kernel) none))

theorem p3942 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,(some 52)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,52,(some 52),51,(some 51),257515,[MeasuredChoices.test66,MeasuredChoices.test69],[AxisChoices.test1814]⟩ (by decide +kernel) none))

theorem p3943 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,52,(some 52)⟩,52,(some 52),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,52,(some 52),52,(some 52),257515,[MeasuredChoices.test66,MeasuredChoices.test69],[AxisChoices.test1815]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair109

section Pack_R6970Height2308PaidPair110

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3974 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,51,(some 51)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,51,(some 51),30,(some 30),257515,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p3975 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,51,(some 51)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,51,(some 51),31,(some 31),257515,[MeasuredChoices.test66],[AxisChoices.test1794]⟩ (by decide +kernel) none))

theorem p3992 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,51,(some 51)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,51,(some 51),48,(some 48),257515,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p3993 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,51,(some 51)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,51,(some 51),49,(some 49),257515,[MeasuredChoices.test66],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p3994 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,51,(some 51)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,51,(some 51),50,(some 50),257515,[MeasuredChoices.test66],[AxisChoices.test1813]⟩ (by decide +kernel) none))

theorem p3995 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,51,(some 51)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,51,(some 51),51,(some 51),257515,[MeasuredChoices.test66],[AxisChoices.test1814]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair110

section Pack_R6970Height2308PaidPair111

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p3997 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,49,(some 50)⟩,0,none,289917,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,49,(some 50),0,none,289917,[MeasuredChoices.test118],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p3998 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,45,(some 48)⟩,0,none,257319,(some 303874)⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,45,(some 48),0,none,257515,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩ ⟨(.node 29457171958066585),.intersection,.impossible,303874⟩ (by decide +kernel) (some 303874) (by decide)))

theorem p3999 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,45,(some 48)⟩,0,none,303874,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,45,(some 48),0,none,303874,[MeasuredChoices.test174,MeasuredChoices.test175],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4000 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,41,(some 44)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,41,(some 44),0,none,257515,[MeasuredChoices.test50],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4002 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,33,(some 40)⟩,0,none,296579,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,33,(some 40),0,none,296579,[MeasuredChoices.test157],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4008 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,25,(some 26)⟩,0,none,303418,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,25,(some 26),0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4009 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,23,(some 24)⟩,0,none,257319,(some 307280)⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,23,(some 24),0,none,257515,[MeasuredChoices.test29,MeasuredChoices.test30],[]⟩ ⟨(.node 28128048211584585),.intersection,.impossible,307280⟩ (by decide +kernel) (some 307280) (by decide)))

theorem p4010 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,23,(some 24)⟩,0,none,307280,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,23,(some 24),0,none,307280,[MeasuredChoices.test348,MeasuredChoices.test425],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4011 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,2,21,(some 22)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,21,(some 22),0,none,257515,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4016 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,39,(some 40)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,39,(some 40),0,none,386273,[AlternateBanks.test26004],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4017 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,37,(some 38)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,37,(some 38),0,none,386273,[MeasuredChoices.test1080,AlternateBanks.test26001],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4018 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,33,(some 36)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,33,(some 36),0,none,386273,[MeasuredChoices.test1028,MeasuredChoices.test1029],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4022 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,25,(some 26)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,25,(some 26),0,none,386273,[MeasuredChoices.test925,AlternateBanks.test26002],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4023 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,23,(some 24)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,23,(some 24),0,none,386273,[MeasuredChoices.test896,MeasuredChoices.test898],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4024 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,22,(some 22)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,22,(some 22),0,none,386273,[MeasuredChoices.test882,MeasuredChoices.test884],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4025 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,21,(some 21)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,21,(some 21),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4026 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,20,(some 20)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,20,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test856],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4030 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,3,(some 3),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),3,(some 3),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1823,AxisChoices.test1824]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4031 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,4,(some 4),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),4,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1823,AxisChoices.test1825]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair111

section Pack_R6970Height2308PaidPair112

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4033 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,6,(some 6),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),6,(some 6),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1826,AxisChoices.test1827]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4034 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,7,(some 7),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),7,(some 7),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1826,AxisChoices.test1828]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4035 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,8,(some 8),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),8,(some 8),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1829]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4036 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,9,(some 9),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),9,(some 9),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1830]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4037 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,10,(some 10),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),10,(some 10),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AlternateBanks.test26219]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4038 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,11,(some 11),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),11,(some 11),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AlternateBanks.test26225]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4039 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,12,(some 12),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),12,(some 12),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1833]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4040 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,13,(some 13),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),13,(some 13),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1834]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4044 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,19,(some 19)⟩,17,(some 17),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 19),17,(some 17),386273,[MeasuredChoices.test773,MeasuredChoices.test843],[AxisChoices.test1838]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4047 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,18,(some 18)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,18,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test831],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4051 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,3,(some 3),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),3,(some 3),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1823,AxisChoices.test1824]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4052 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,4,(some 4),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),4,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1823,AxisChoices.test1825]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4054 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,6,(some 6),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),6,(some 6),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1826,AxisChoices.test1827]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4055 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,7,(some 7),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),7,(some 7),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1826,AxisChoices.test1828]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4057 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,9,(some 9),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),9,(some 9),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1830]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4058 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,10,(some 10),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),10,(some 10),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AlternateBanks.test26219]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4059 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,11,(some 11),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),11,(some 11),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AlternateBanks.test26225]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4060 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,12,(some 12),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),12,(some 12),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1833]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4061 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,13,(some 13),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),13,(some 13),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1834]⟩ ⟨.separate,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4065 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,17,(some 17)⟩,17,(some 17),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 17),17,(some 17),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1838]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4066 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,16,(some 16)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,16,(some 16),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test807],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4067 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,15,(some 15)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,15,(some 15),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair112

section Pack_R6970Height2308PaidPair113

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4068 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,10,3,13,(some 14)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,13,(some 14),0,none,386273,[MeasuredChoices.test770,MeasuredChoices.test773],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair113

section Pack_R6970Height2308PaidPair114

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows







end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair114

section Pack_R6970Height2308PaidPair115

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows




end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair115

section Pack_R6970Height2308PaidPair116

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows















theorem p4202 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,2,25,(some 28)⟩,0,none,257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.weight 302619
    (PairLeaves.paired ⟨25,27,9,2,25,(some 28),0,none,257515,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩ ⟨(.node 7880313335284333),.intersection,.impossible,302619⟩ (by decide +kernel) (some 302619) (by decide))
    (PairLeaves.paired ⟨25,27,9,2,25,(some 28),0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4211 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,3,(some 3),385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨25,27,9,3,17,(some 20),3,(some 3),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1823,AxisChoices.test1824]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair116

section Pack_R6970Height2308PaidPair117

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4212 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,4,(some 4),385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨25,27,9,3,17,(some 20),4,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1823,AxisChoices.test1825]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4214 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,6,(some 6),385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨25,27,9,3,17,(some 20),6,(some 6),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1826,AxisChoices.test1827]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4215 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,7,(some 7),385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨25,27,9,3,17,(some 20),7,(some 7),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1826,AxisChoices.test1828]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4218 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,10,(some 10),385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨25,27,9,3,17,(some 20),10,(some 10),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AlternateBanks.test26219]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4219 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,11,(some 11),385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨25,27,9,3,17,(some 20),11,(some 11),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AlternateBanks.test26225]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4225 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,17,(some 17),385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨25,27,9,3,17,(some 20),17,(some 17),386273,[MeasuredChoices.test773,MeasuredChoices.test821],[AxisChoices.test1838]⟩ ⟨.markedAxis,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4229 : PairRoute.Done (4:Fin 18) ⟨⟨25,27,9,3,13,(some 16)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 14
    (PairLeaves.paired ⟨25,27,9,3,13,(some 14),0,none,386273,[MeasuredChoices.test770,MeasuredChoices.test773],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairRoute.splitSeed 15
    (PairLeaves.paired ⟨25,27,9,3,15,(some 15),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨25,27,9,3,16,(some 16),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test807],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))))

theorem p4231 : PairRoute.Done (4:Fin 18) ⟨⟨28,32,9,2,25,(some 28)⟩,0,none,257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.weight 302619
    (PairLeaves.paired ⟨28,32,9,2,25,(some 28),0,none,257515,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩ ⟨(.node 7880313335284333),.intersection,.impossible,302619⟩ (by decide +kernel) (some 302619) (by decide))
    (PairLeaves.paired ⟨28,32,9,2,25,(some 28),0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4236 : PairRoute.Done (4:Fin 18) ⟨⟨28,32,9,3,21,(some 24)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 22
    (PairLeaves.paired ⟨28,32,9,3,21,(some 22),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨28,32,9,3,23,(some 24),0,none,386273,[MeasuredChoices.test896,MeasuredChoices.test898],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4237 : PairRoute.Done (4:Fin 18) ⟨⟨28,32,9,3,19,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨28,32,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4238 : PairRoute.Done (4:Fin 18) ⟨⟨28,32,9,3,17,(some 18)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 17
    (PairLeaves.paired ⟨28,32,9,3,17,(some 17),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨28,32,9,3,18,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test831],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4239 : PairRoute.Done (4:Fin 18) ⟨⟨28,32,9,3,13,(some 16)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 14
    (PairLeaves.paired ⟨28,32,9,3,13,(some 14),0,none,386273,[MeasuredChoices.test770,MeasuredChoices.test773],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairRoute.splitSeed 15
    (PairLeaves.paired ⟨28,32,9,3,15,(some 15),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨28,32,9,3,16,(some 16),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test807],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))))

theorem p4241 : PairRoute.Done (4:Fin 18) ⟨⟨33,40,9,2,25,(some 28)⟩,0,none,257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.weight 302619
    (PairLeaves.paired ⟨33,40,9,2,25,(some 28),0,none,257515,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩ ⟨(.node 7880313335284333),.intersection,.impossible,302619⟩ (by decide +kernel) (some 302619) (by decide))
    (PairLeaves.paired ⟨33,40,9,2,25,(some 28),0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair117

section Pack_R6970Height2308PaidPair118

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4249 : PairRoute.Done (4:Fin 18) ⟨⟨33,40,9,3,21,(some 24)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 22
    (PairLeaves.paired ⟨33,40,9,3,21,(some 22),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨33,40,9,3,23,(some 24),0,none,386273,[MeasuredChoices.test896,MeasuredChoices.test898],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4250 : PairRoute.Done (4:Fin 18) ⟨⟨33,40,9,3,19,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨33,40,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4251 : PairRoute.Done (4:Fin 18) ⟨⟨33,40,9,3,17,(some 18)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 17
    (PairLeaves.paired ⟨33,40,9,3,17,(some 17),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨33,40,9,3,18,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test831],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4252 : PairRoute.Done (4:Fin 18) ⟨⟨33,40,9,3,13,(some 16)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 14
    (PairLeaves.paired ⟨33,40,9,3,13,(some 14),0,none,386273,[MeasuredChoices.test770,MeasuredChoices.test773],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨33,40,9,3,15,(some 16),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair118

section Pack_R6970Height2308PaidPair120

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4325 : PairRoute.Done (4:Fin 18) ⟨⟨41,49,9,3,49,(some 64)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 56
    (PairLeaves.paired ⟨41,49,9,3,49,(some 56),0,none,386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[]⟩ ⟨.marked,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,57,(some 64),0,none,386273,[MeasuredChoices.test1144],[]⟩ ⟨.marked,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4326 : PairRoute.Done (4:Fin 18) ⟨⟨41,49,9,3,41,(some 48)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 44
    (PairLeaves.paired ⟨41,49,9,3,41,(some 44),0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,45,(some 48),0,none,386273,[MeasuredChoices.test1139],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4329 : PairRoute.Done (4:Fin 18) ⟨⟨41,49,9,3,21,(some 24)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 22
    (PairLeaves.paired ⟨41,49,9,3,21,(some 22),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,23,(some 24),0,none,386273,[MeasuredChoices.test896,MeasuredChoices.test898],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4330 : PairRoute.Done (4:Fin 18) ⟨⟨41,49,9,3,19,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨41,49,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4331 : PairRoute.Done (4:Fin 18) ⟨⟨41,49,9,3,17,(some 18)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨41,49,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4332 : PairRoute.Done (4:Fin 18) ⟨⟨41,49,9,3,13,(some 16)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 14
    (PairLeaves.paired ⟨41,49,9,3,13,(some 14),0,none,386273,[MeasuredChoices.test770,MeasuredChoices.test773],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,15,(some 16),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair120

section Pack_R6970Height2308PaidPair121

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4366 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),30,(some 30),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p4367 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),31,(some 31),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1794]⟩ (by decide +kernel) none))

theorem p4384 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),48,(some 48),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p4385 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),49,(some 49),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1812]⟩ (by decide +kernel) none))

theorem p4386 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),50,(some 50),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1813]⟩ (by decide +kernel) none))

theorem p4387 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),51,(some 51),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1814]⟩ (by decide +kernel) none))

theorem p4388 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,52,(some 52),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),52,(some 52),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1815]⟩ (by decide +kernel) none))

theorem p4389 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,53,(some 53),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),53,(some 53),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1816]⟩ (by decide +kernel) none))

theorem p4390 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,54,(some 54),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),54,(some 54),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1817]⟩ (by decide +kernel) none))

theorem p4391 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,57,(some 57)⟩,55,(some 55),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨50,63,9,2,57,(some 57),55,(some 55),257515,[MeasuredChoices.test76,MeasuredChoices.test79],[AxisChoices.test1817]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair121

section Pack_R6970Height2308PaidPair122

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4395 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,53,(some 56)⟩,0,none,285209,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,53,(some 56),0,none,285209,[MeasuredChoices.test111],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4396 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,49,(some 52)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,49,(some 52),0,none,257515,[MeasuredChoices.test62],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4397 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,41,(some 48)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,41,(some 48),0,none,257515,[MeasuredChoices.test50],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4401 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,25,(some 28)⟩,0,none,302619,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,25,(some 28),0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4402 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,2,21,(some 24)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,21,(some 24),0,none,257515,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4406 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,3,37,(some 40)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,37,(some 40),0,none,386273,[MeasuredChoices.test1080,AlternateBanks.test26001],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4409 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,3,25,(some 28)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,25,(some 28),0,none,386273,[MeasuredChoices.test925,AlternateBanks.test26002],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4410 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,3,23,(some 24)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,23,(some 24),0,none,386273,[MeasuredChoices.test896,MeasuredChoices.test898],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4411 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,3,21,(some 22)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,21,(some 22),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4412 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,3,19,(some 20)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4413 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,3,17,(some 18)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4414 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,10,3,15,(some 16)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,15,(some 16),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair122

section Pack_R6970Height2308PaidPair123

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4449 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),30,(some 30),257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none)

theorem p4450 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),31,(some 31),257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair123

section Pack_R6970Height2308PaidPair124

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4467 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),48,(some 48),257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none)

theorem p4468 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),49,(some 49),257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩ (by decide +kernel) none)

theorem p4469 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),50,(some 50),257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩ (by decide +kernel) none)

theorem p4470 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),51,(some 51),257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair124

section Pack_R6970Height2308PaidPair125

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4501 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),30,(some 30),257319,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none)

theorem p4502 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),31,(some 31),257319,[MeasuredChoices.test64],[AxisChoices.test1793,AxisChoices.test1794]⟩ (by decide +kernel) none)

theorem p4519 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),48,(some 48),257319,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none)

theorem p4520 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),49,(some 49),257319,[MeasuredChoices.test64],[AxisChoices.test1812]⟩ (by decide +kernel) none)

theorem p4521 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),50,(some 50),257319,[MeasuredChoices.test64],[AxisChoices.test1813]⟩ (by decide +kernel) none)

theorem p4523 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,49,(some 49)⟩,0,none,290650,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,49,(some 49),0,none,290650,[MeasuredChoices.test120],[]⟩ (by decide +kernel) none)

theorem p4524 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,48,(some 48)⟩,0,none,257319,(some 303874)⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,48,(some 48),0,none,257515,[MeasuredChoices.test61],[]⟩ ⟨(.node 29457171958066585),.intersection,.impossible,303874⟩ (by decide +kernel) (some 303874) (by decide)))

theorem p4525 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,48,(some 48)⟩,0,none,303874,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,48,(some 48),0,none,303874,[MeasuredChoices.test191],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4526 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,47,(some 47)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,47,(some 47),0,none,257515,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4527 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,45,(some 46)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,45,(some 46),0,none,257515,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4531 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,37,(some 40)⟩,0,none,296579,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,37,(some 40),0,none,296579,[MeasuredChoices.test158],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4535 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,29,(some 32)⟩,0,none,300842,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,29,(some 32),0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair125

section Pack_R6970Height2308PaidPair126

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4539 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,25,(some 26)⟩,0,none,303418,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,25,(some 26),0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4540 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,23,(some 24)⟩,0,none,257319,(some 307280)⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,23,(some 24),0,none,257515,[MeasuredChoices.test29,MeasuredChoices.test30],[]⟩ ⟨(.node 28128048211584585),.intersection,.impossible,307280⟩ (by decide +kernel) (some 307280) (by decide)))

theorem p4541 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,23,(some 24)⟩,0,none,307280,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,23,(some 24),0,none,307280,[MeasuredChoices.test348,MeasuredChoices.test425],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4542 : PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,21,(some 22)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,21,(some 22),0,none,257515,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4552 : PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 18
    (PairLeaves.paired ⟨25,27,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨25,27,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4561 : PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 18
    (PairLeaves.paired ⟨28,32,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨28,32,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4570 : PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 18
    (PairLeaves.paired ⟨33,40,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨33,40,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair126

section Pack_R6970Height2308PaidPair128

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4621 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,48,(some 48),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),48,(some 48),257515,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none)

theorem p4622 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,49,(some 49),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),49,(some 49),257515,[MeasuredChoices.test62],[AxisChoices.test1812]⟩ (by decide +kernel) none)

theorem p4623 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,50,(some 50),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),50,(some 50),257515,[MeasuredChoices.test62],[AxisChoices.test1813]⟩ (by decide +kernel) none)

theorem p4624 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,51,(some 51),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),51,(some 51),257515,[MeasuredChoices.test62],[AxisChoices.test1814]⟩ (by decide +kernel) none)

theorem p4625 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,52,(some 52),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),52,(some 52),257515,[MeasuredChoices.test62],[AxisChoices.test1815]⟩ (by decide +kernel) none)

theorem p4626 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,53,(some 53),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),53,(some 53),257515,[MeasuredChoices.test62],[AxisChoices.test1816]⟩ (by decide +kernel) none)

theorem p4627 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,54,(some 54),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),54,(some 54),257515,[MeasuredChoices.test62],[AxisChoices.test1817]⟩ (by decide +kernel) none)

theorem p4628 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,(some 64)⟩,55,(some 55),257319,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨41,49,9,2,49,(some 64),55,(some 55),257515,[MeasuredChoices.test62],[AxisChoices.test1817]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair128

section Pack_R6970Height2308PaidPair129

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4646 : PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 18
    (PairLeaves.paired ⟨41,49,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4652 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,2,49,(some 56)⟩,0,none,285209,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨50,63,9,2,49,(some 56),0,none,285209,[MeasuredChoices.test104],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4656 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,2,25,(some 28)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,25,(some 28),0,none,257515,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4661 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,3,33,(some 40)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,33,(some 40),0,none,386273,[MeasuredChoices.test1028,MeasuredChoices.test1029],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4664 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,3,21,(some 24)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,21,(some 24),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4665 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,3,19,(some 20)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4666 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,3,17,(some 18)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4667 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,3,13,(some 16)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,13,(some 16),0,none,386273,[MeasuredChoices.test770,MeasuredChoices.test773],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair129

section Pack_R6970Height2308PaidPair130

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4701 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),30,(some 30),257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none)

theorem p4702 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),31,(some 31),257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair130

section Pack_R6970Height2308PaidPair131

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4719 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),48,(some 48),257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none)

theorem p4720 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),49,(some 49),257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩ (by decide +kernel) none)

theorem p4721 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),50,(some 50),257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩ (by decide +kernel) none)

theorem p4722 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,51,(some 51)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,51,(some 51),51,(some 51),257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair131

section Pack_R6970Height2308PaidPair132

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4753 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),30,(some 30),257319,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none)

theorem p4754 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),31,(some 31),257319,[MeasuredChoices.test64],[AxisChoices.test1793,AxisChoices.test1794]⟩ (by decide +kernel) none)

theorem p4771 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),48,(some 48),257319,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none)

theorem p4772 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),49,(some 49),257319,[MeasuredChoices.test64],[AxisChoices.test1812]⟩ (by decide +kernel) none)

theorem p4773 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,50,(some 50)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,654,9,2,50,(some 50),50,(some 50),257319,[MeasuredChoices.test64],[AxisChoices.test1813]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair132

section Pack_R6970Height2308PaidPair133

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4804 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,49,(some 49)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨64,654,9,2,49,(some 49),30,(some 30),257515,[MeasuredChoices.test62],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p4805 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,49,(some 49)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨64,654,9,2,49,(some 49),31,(some 31),257515,[MeasuredChoices.test62],[AxisChoices.test1794]⟩ (by decide +kernel) none))

theorem p4822 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,49,(some 49)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨64,654,9,2,49,(some 49),48,(some 48),257515,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p4823 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,49,(some 49)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨64,654,9,2,49,(some 49),49,(some 49),257515,[MeasuredChoices.test62],[AxisChoices.test1812]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair133

section Pack_R6970Height2308PaidPair134

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4854 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,48,(some 48)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨64,654,9,2,48,(some 48),30,(some 30),257515,[MeasuredChoices.test61],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none))

theorem p4855 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,48,(some 48)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨64,654,9,2,48,(some 48),31,(some 31),257515,[MeasuredChoices.test61],[AxisChoices.test1794]⟩ (by decide +kernel) none))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair134

section Pack_R6970Height2308PaidPair135

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4872 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,48,(some 48)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.excluded ⟨64,654,9,2,48,(some 48),48,(some 48),257515,[MeasuredChoices.test61],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none))

theorem p4875 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,45,(some 46)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,45,(some 46),0,none,257515,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4877 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,43,(some 44)⟩,0,none,294092,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,43,(some 44),0,none,294092,[MeasuredChoices.test141,MeasuredChoices.test142],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4879 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,41,(some 42)⟩,0,none,295365,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,41,(some 42),0,none,295365,[MeasuredChoices.test124,MeasuredChoices.test144],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4880 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,39,(some 40)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,39,(some 40),0,none,257515,[MeasuredChoices.test47,MeasuredChoices.test48],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4881 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,37,(some 38)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,37,(some 38),0,none,257515,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4883 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,33,(some 36)⟩,0,none,305352,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,33,(some 36),0,none,305352,[MeasuredChoices.test276,MeasuredChoices.test277],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4884 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,31,(some 32)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,31,(some 32),0,none,257515,[MeasuredChoices.test41,MeasuredChoices.test42],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4885 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,29,(some 30)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,29,(some 30),0,none,257515,[MeasuredChoices.test39],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4889 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,25,(some 26)⟩,0,none,303418,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,25,(some 26),0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4891 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,24,(some 24)⟩,0,none,304158,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,24,(some 24),0,none,304158,[MeasuredChoices.test218,AlternateBanks.test26031],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4893 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,23,(some 23)⟩,0,none,305811,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,23,(some 23),0,none,305811,[MeasuredChoices.test300,MeasuredChoices.test312],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p4894 : PairRoute.Done (5:Fin 18) ⟨⟨64,654,12,2,21,(some 22)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,654,9,2,21,(some 22),0,none,257515,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair135

section Pack_R6970Height2308PaidPair137

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4933 : PairRoute.Done (6:Fin 18) ⟨⟨41,49,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 18
    (PairLeaves.paired ⟨41,49,9,3,17,(some 18),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,19,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test843],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4936 : PairRoute.Done (6:Fin 18) ⟨⟨50,63,10,2,57,(some 60)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,57,(some 60),0,none,257515,[MeasuredChoices.test76,MeasuredChoices.test79],[]⟩ ⟨.marked,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4939 : PairRoute.Done (6:Fin 18) ⟨⟨50,63,10,2,25,(some 28)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,2,25,(some 28),0,none,257515,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4947 : PairRoute.Done (6:Fin 18) ⟨⟨50,63,10,3,21,(some 24)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,21,(some 24),0,none,386273,[MeasuredChoices.test869,MeasuredChoices.test871],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p4948 : PairRoute.Done (6:Fin 18) ⟨⟨50,63,10,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair137

section Pack_R6970Height2308PaidPair138

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p4983 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,51,(some 51)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,51,(some 51),30,(some 30),257319,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none)

theorem p4984 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,51,(some 51)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,51,(some 51),31,(some 31),257319,[MeasuredChoices.test66],[AxisChoices.test1793,AxisChoices.test1794]⟩ (by decide +kernel) none)

theorem p5001 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,51,(some 51)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,51,(some 51),48,(some 48),257319,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none)

theorem p5002 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,51,(some 51)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,51,(some 51),49,(some 49),257319,[MeasuredChoices.test66],[AxisChoices.test1812]⟩ (by decide +kernel) none)

theorem p5003 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,51,(some 51)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,51,(some 51),50,(some 50),257319,[MeasuredChoices.test66],[AxisChoices.test1813]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair138

section Pack_R6970Height2308PaidPair139

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p5004 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,51,(some 51)⟩,51,(some 51),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,51,(some 51),51,(some 51),257319,[MeasuredChoices.test66],[AxisChoices.test1813,AxisChoices.test1814]⟩ (by decide +kernel) none)

theorem p5035 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,50,(some 50)⟩,30,(some 30),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,50,(some 50),30,(some 30),257319,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩ (by decide +kernel) none)

theorem p5036 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,50,(some 50)⟩,31,(some 31),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,50,(some 50),31,(some 31),257319,[MeasuredChoices.test64],[AxisChoices.test1793,AxisChoices.test1794]⟩ (by decide +kernel) none)

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair139

section Pack_R6970Height2308PaidPair140

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p5053 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,50,(some 50)⟩,48,(some 48),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,50,(some 50),48,(some 48),257319,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩ (by decide +kernel) none)

theorem p5054 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,50,(some 50)⟩,49,(some 49),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,50,(some 50),49,(some 49),257319,[MeasuredChoices.test64],[AxisChoices.test1812]⟩ (by decide +kernel) none)

theorem p5055 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,50,(some 50)⟩,50,(some 50),257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,50,(some 50),50,(some 50),257319,[MeasuredChoices.test64],[AxisChoices.test1813]⟩ (by decide +kernel) none)

theorem p5057 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,49,(some 49)⟩,0,none,290650,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,706,9,2,49,(some 49),0,none,290650,[MeasuredChoices.test120],[]⟩ (by decide +kernel) none)

theorem p5058 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,47,(some 48)⟩,0,none,257319,(some 303874)⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,706,9,2,47,(some 48),0,none,257515,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩ ⟨(.node 29457171958066585),.intersection,.impossible,303874⟩ (by decide +kernel) (some 303874) (by decide)))

theorem p5059 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,47,(some 48)⟩,0,none,303874,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,706,9,2,47,(some 48),0,none,303874,[MeasuredChoices.test190],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5060 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,45,(some 46)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,706,9,2,45,(some 46),0,none,257515,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5062 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,41,(some 44)⟩,0,none,294092,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,706,9,2,41,(some 44),0,none,294092,[MeasuredChoices.test124,MeasuredChoices.test140],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5064 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,37,(some 40)⟩,0,none,296579,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,706,9,2,37,(some 40),0,none,296579,[MeasuredChoices.test158],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5066 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,33,(some 36)⟩,0,none,298829,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,706,9,2,33,(some 36),0,none,298829,[MeasuredChoices.test161],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5068 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,29,(some 32)⟩,0,none,300842,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,706,9,2,29,(some 32),0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5072 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,25,(some 26)⟩,0,none,303418,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,706,9,2,25,(some 26),0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5073 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,23,(some 24)⟩,0,none,257319,(some 307280)⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,706,9,2,23,(some 24),0,none,257515,[MeasuredChoices.test29,MeasuredChoices.test30],[]⟩ ⟨(.node 28128048211584585),.intersection,.impossible,307280⟩ (by decide +kernel) (some 307280) (by decide)))

theorem p5074 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,23,(some 24)⟩,0,none,307280,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,706,9,2,23,(some 24),0,none,307280,[MeasuredChoices.test348,MeasuredChoices.test425],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5075 : PairRoute.Done (6:Fin 18) ⟨⟨64,706,12,2,21,(some 22)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,706,9,2,21,(some 22),0,none,257515,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair140

section Pack_R6970Height2308PaidPair141

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p5089 : PairRoute.Done (7:Fin 18) ⟨⟨28,32,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨28,32,9,3,17,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5095 : PairRoute.Done (7:Fin 18) ⟨⟨33,40,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨33,40,9,3,17,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5102 : PairRoute.Done (7:Fin 18) ⟨⟨41,49,9,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨41,49,9,3,17,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair141

section Pack_R6970Height2308PaidPair142

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p5112 : PairRoute.Done (7:Fin 18) ⟨⟨50,63,10,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5115 : PairRoute.Done (7:Fin 18) ⟨⟨64,722,12,2,49,(some 52)⟩,0,none,288407,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.excluded ⟨64,722,9,2,49,(some 52),0,none,288407,[MeasuredChoices.test114],[]⟩ (by decide +kernel) none)

theorem p5116 : PairRoute.Done (7:Fin 18) ⟨⟨64,722,12,2,45,(some 48)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,722,9,2,45,(some 48),0,none,257515,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5117 : PairRoute.Done (7:Fin 18) ⟨⟨64,722,12,2,41,(some 44)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,722,9,2,41,(some 44),0,none,257515,[MeasuredChoices.test50],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5118 : PairRoute.Done (7:Fin 18) ⟨⟨64,722,12,2,37,(some 40)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,722,9,2,37,(some 40),0,none,257515,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5119 : PairRoute.Done (7:Fin 18) ⟨⟨64,722,12,2,33,(some 36)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,722,9,2,33,(some 36),0,none,257515,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5123 : PairRoute.Done (7:Fin 18) ⟨⟨64,722,12,2,25,(some 28)⟩,0,none,302619,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,722,9,2,25,(some 28),0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5124 : PairRoute.Done (7:Fin 18) ⟨⟨64,722,12,2,21,(some 24)⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨64,722,9,2,21,(some 24),0,none,257515,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair142

section Pack_R6970Height2308PaidPair143

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p5152 : PairRoute.Done (8:Fin 18) ⟨⟨50,63,10,3,17,(some 20)⟩,0,none,385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,63,9,3,17,(some 20),0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test821],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5155 : PairRoute.Done (8:Fin 18) ⟨⟨64,654,12,2,41,(some 48)⟩,0,none,291368,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (PairLeaves.paired ⟨64,654,9,2,41,(some 48),0,none,291368,[MeasuredChoices.test124,MeasuredChoices.test125],[]⟩ ⟨.surface,.intersection,.impossible,0⟩ (by decide +kernel) none (by decide))

theorem p5165 : PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,25,(some 28)⟩,0,none,514639,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 26
    (PairLeaves.paired ⟨33,40,9,4,25,(some 26),0,none,515031,[MeasuredChoices.test1272,MeasuredChoices.test1273],[]⟩ ⟨.surface,.whole,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨33,40,9,4,27,(some 28),0,none,515031,[MeasuredChoices.test1273,AlternateBanks.test21279],[]⟩ ⟨.surface,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5168 : PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,3,49,(some 56)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 52
    (PairLeaves.three ⟨41,49,9,3,49,(some 52),0,none,386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[]⟩ (by decide +kernel) (by decide) none)
    (PairRoute.splitSeed 54
    (PairLeaves.three ⟨41,49,9,3,53,(some 54),0,none,386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[]⟩ (by decide +kernel) (by decide) none)
    (PairRoute.splitSeed 55
    (PairLeaves.three ⟨41,49,9,3,55,(some 55),0,none,386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[]⟩ (by decide +kernel) (by decide) none)
    (PairRoute.axes_of_total (PairRoute.axis 28
    (PairRoute.axis 14
    (PairRoute.axis 7
    (PairRoute.axis 3
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),0,(some 3),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1821,AlternateBanks.test26221]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairRoute.axis 5
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),4,(some 5),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1823,AxisChoices.test1825]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairRoute.axis 6
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),6,(some 6),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1826,AxisChoices.test1827]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),7,(some 7),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1826,AxisChoices.test1828]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))))
    (PairRoute.axis 11
    (PairRoute.axis 9
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),8,(some 9),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1829]⟩ ⟨.markedAxis,.whole,.impossible,0⟩ (by decide +kernel) none (by decide))
    (PairRoute.axis 10
    (PairLeaves.three ⟨41,49,9,3,56,(some 56),10,(some 10),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AlternateBanks.test26219]⟩ (by decide +kernel) (by decide) none)
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),11,(some 11),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AlternateBanks.test26225]⟩ ⟨.markedAxis,.whole,.impossible,0⟩ (by decide +kernel) none (by decide))))
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),12,(some 14),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1833]⟩ ⟨.markedAxis,.whole,.impossible,0⟩ (by decide +kernel) none (by decide))))
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),15,(some 28),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1836]⟩ ⟨.markedAxis,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))
    (PairLeaves.paired ⟨41,49,9,3,56,(some 56),29,(some 56),386273,[MeasuredChoices.test1142,MeasuredChoices.test1143],[AxisChoices.test1849]⟩ ⟨.markedAxis,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))))))

theorem p5175 : PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,41,(some 44)⟩,0,none,385979,none⟩ :=
  AlternateDispatch.raiseWeight (by decide) (PairRoute.splitSeed 42
    (PairLeaves.three ⟨41,49,9,3,41,(some 42),0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩ (by decide +kernel) (by decide) none)
    (PairLeaves.three ⟨41,49,9,3,43,(some 44),0,none,386273,[MeasuredChoices.test1136,MeasuredChoices.test1137],[]⟩ (by decide +kernel) (by decide) none))

theorem p5179 : PairRoute.Done (1:Fin 18) ⟨⟨50,50,10,3,15,(some 15)⟩,3,(some 3),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,50,9,3,15,(some 15),3,(some 3),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1823,AxisChoices.test1824]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5180 : PairRoute.Done (1:Fin 18) ⟨⟨50,50,10,3,15,(some 15)⟩,4,(some 4),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,50,9,3,15,(some 15),4,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1823,AxisChoices.test1825]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5182 : PairRoute.Done (1:Fin 18) ⟨⟨50,50,10,3,15,(some 15)⟩,6,(some 6),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,50,9,3,15,(some 15),6,(some 6),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1826,AxisChoices.test1827]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5183 : PairRoute.Done (1:Fin 18) ⟨⟨50,50,10,3,15,(some 15)⟩,7,(some 7),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,50,9,3,15,(some 15),7,(some 7),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1826,AxisChoices.test1828]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair143

section Pack_R6970Height2308PaidPair144

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.PaidRows

theorem p5186 : PairRoute.Done (1:Fin 18) ⟨⟨50,50,10,3,15,(some 15)⟩,10,(some 10),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,50,9,3,15,(some 15),10,(some 10),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AlternateBanks.test26219]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5187 : PairRoute.Done (1:Fin 18) ⟨⟨50,50,10,3,15,(some 15)⟩,11,(some 11),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨50,50,9,3,15,(some 15),11,(some 11),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AlternateBanks.test26225]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5195 : PairRoute.Done (1:Fin 18) ⟨⟨51,51,10,3,15,(some 15)⟩,3,(some 3),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨51,51,9,3,15,(some 15),3,(some 3),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1823,AxisChoices.test1824]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5196 : PairRoute.Done (1:Fin 18) ⟨⟨51,51,10,3,15,(some 15)⟩,4,(some 4),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨51,51,9,3,15,(some 15),4,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1823,AxisChoices.test1825]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5198 : PairRoute.Done (1:Fin 18) ⟨⟨51,51,10,3,15,(some 15)⟩,6,(some 6),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨51,51,9,3,15,(some 15),6,(some 6),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1826,AxisChoices.test1827]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5199 : PairRoute.Done (1:Fin 18) ⟨⟨51,51,10,3,15,(some 15)⟩,7,(some 7),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨51,51,9,3,15,(some 15),7,(some 7),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1826,AxisChoices.test1828]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5202 : PairRoute.Done (1:Fin 18) ⟨⟨51,51,10,3,15,(some 15)⟩,10,(some 10),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨51,51,9,3,15,(some 15),10,(some 10),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AlternateBanks.test26219]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5203 : PairRoute.Done (1:Fin 18) ⟨⟨51,51,10,3,15,(some 15)⟩,11,(some 11),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨51,51,9,3,15,(some 15),11,(some 11),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AlternateBanks.test26225]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5211 : PairRoute.Done (1:Fin 18) ⟨⟨52,52,10,3,15,(some 15)⟩,3,(some 3),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨52,52,9,3,15,(some 15),3,(some 3),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1823,AxisChoices.test1824]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5212 : PairRoute.Done (1:Fin 18) ⟨⟨52,52,10,3,15,(some 15)⟩,4,(some 4),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨52,52,9,3,15,(some 15),4,(some 4),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1823,AxisChoices.test1825]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5214 : PairRoute.Done (1:Fin 18) ⟨⟨52,52,10,3,15,(some 15)⟩,6,(some 6),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨52,52,9,3,15,(some 15),6,(some 6),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1826,AxisChoices.test1827]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5215 : PairRoute.Done (1:Fin 18) ⟨⟨52,52,10,3,15,(some 15)⟩,7,(some 7),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨52,52,9,3,15,(some 15),7,(some 7),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AxisChoices.test1826,AxisChoices.test1828]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5218 : PairRoute.Done (1:Fin 18) ⟨⟨52,52,10,3,15,(some 15)⟩,10,(some 10),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨52,52,9,3,15,(some 15),10,(some 10),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AlternateBanks.test26219]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

theorem p5219 : PairRoute.Done (1:Fin 18) ⟨⟨52,52,10,3,15,(some 15)⟩,11,(some 11),385979,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) (PairLeaves.paired ⟨52,52,9,3,15,(some 15),11,(some 11),386273,[MeasuredChoices.test773,MeasuredChoices.test797],[AlternateBanks.test26225]⟩ ⟨.separate,.whole,.impossible,0⟩ (by decide +kernel) none (by decide)))

end Research6970.Height2313.Research6969.PaidRows
end Pack_R6970Height2308PaidPair144
