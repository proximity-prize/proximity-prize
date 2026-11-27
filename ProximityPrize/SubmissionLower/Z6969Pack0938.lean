import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0936
import ProximityPrize.SubmissionLower.Z6969Pack0937
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.HardFit1At100
section Z6969Source2615
set_option autoImplicit true
namespace Research6969.HardFit1At100
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,17,some 20⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell480 PairReceipts.choice480 PairReceipts.check480 (none) (by decide)
theorem case100: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,21,some 24⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell479 PairReceipts.choice479 PairReceipts.check479 (none) (by decide)
theorem case101: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,25,some 28⟩,0,none,257363,some 302619⟩:=PairLeaves.paired PairReceipts.cell477 PairReceipts.choice477 PairReceipts.check477 (some 302619) (by decide)
private theorem leaf3:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,25,some 28⟩,0,none,302619,none⟩:=PairLeaves.paired PairReceipts.cell478 PairReceipts.choice478 PairReceipts.check478 (none) (by decide)
private theorem weight4:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,25,some 28⟩,0,none,257363,none⟩:=PairRoute.weight 302619 leaf2 leaf3
theorem case102: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ weight4
private theorem leaf5:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,29,some 32⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell476 PairReceipts.choice476 PairReceipts.check476 (none) (by decide)
theorem case103: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,29,some 32⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,33,some 40⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell475 PairReceipts.choice475 PairReceipts.check475 (none) (by decide)
theorem case104: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,33,some 40⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,41,some 48⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell474 PairReceipts.choice474 PairReceipts.check474 (none) (by decide)
theorem case105: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,41,some 48⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,49,some 64⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell473 PairReceipts.choice473 PairReceipts.check473 (none) (by decide)
theorem case106: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,49,some 64⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,65,some 96⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell472 PairReceipts.choice472 PairReceipts.check472 (none) (by decide)
theorem case107: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,65,some 96⟩:=PairRoute.start _ leaf9
private theorem leaf10:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,4,some 8⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell629 PairReceipts.choice629 PairReceipts.check629 (none) (by decide)
theorem case108: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,4,some 8⟩:=PairRoute.start _ leaf10
private theorem leaf11:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,9,some 12⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell628 PairReceipts.choice628 PairReceipts.check628 (none) (by decide)
theorem case109: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf11
end Research6969.HardFit1At100
end Z6969Source2615

-- Source: Research6969.PairReceipts025
section Z6969Source2616
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell500:PairCell.Row:=⟨33,40,9,3,21,some 21,6,some 6,386045,[MeasuredChoices.test869],[AxisChoices.test1827]⟩
def choice500:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check500:PairPrices.valid cell500 (0:Fin 18) choice500:=by decide +kernel
def cell501:PairCell.Row:=⟨33,40,9,3,21,some 21,7,some 7,386045,[MeasuredChoices.test869],[AxisChoices.test1828]⟩
def choice501:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check501:PairPrices.valid cell501 (0:Fin 18) choice501:=by decide +kernel
def cell502:PairCell.Row:=⟨33,40,9,3,21,some 21,8,some 8,386045,[MeasuredChoices.test869],[AxisChoices.test1829]⟩
def choice502:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check502:PairPrices.valid cell502 (0:Fin 18) choice502:=by decide +kernel
def cell503:PairCell.Row:=⟨33,40,9,3,21,some 21,9,some 9,386045,[MeasuredChoices.test869],[AxisChoices.test1830]⟩
def choice503:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check503:PairPrices.valid cell503 (0:Fin 18) choice503:=by decide +kernel
def cell504:PairCell.Row:=⟨33,40,9,3,21,some 21,10,some 10,386045,[MeasuredChoices.test869],[AxisChoices.test1831]⟩
def choice504:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check504:PairPrices.valid cell504 (0:Fin 18) choice504:=by decide +kernel
def cell505:PairCell.Row:=⟨33,40,9,3,21,some 21,11,some 11,386045,[MeasuredChoices.test869],[AxisChoices.test1832]⟩
def choice505:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check505:PairPrices.valid cell505 (0:Fin 18) choice505:=by decide +kernel
def cell506:PairCell.Row:=⟨33,40,9,3,21,some 21,12,some 12,386045,[MeasuredChoices.test869],[AxisChoices.test1833]⟩
def choice506:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check506:PairPrices.valid cell506 (0:Fin 18) choice506:=by decide +kernel
def cell507:PairCell.Row:=⟨33,40,9,3,21,some 21,13,some 13,386045,[MeasuredChoices.test869],[AxisChoices.test1834]⟩
def choice507:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check507:PairPrices.valid cell507 (0:Fin 18) choice507:=by decide +kernel
def cell508:PairCell.Row:=⟨33,40,9,3,21,some 21,14,some 14,386045,[MeasuredChoices.test869],[AxisChoices.test1835]⟩
def choice508:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check508:PairPrices.valid cell508 (0:Fin 18) choice508:=by decide +kernel
def cell509:PairCell.Row:=⟨33,40,9,3,21,some 21,15,some 15,386045,[MeasuredChoices.test869],[AxisChoices.test1836]⟩
def choice509:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check509:PairPrices.valid cell509 (0:Fin 18) choice509:=by decide +kernel
def cell510:PairCell.Row:=⟨33,40,9,3,21,some 21,16,some 16,386045,[MeasuredChoices.test869],[AxisChoices.test1837]⟩
def choice510:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check510:PairPrices.valid cell510 (0:Fin 18) choice510:=by decide +kernel
def cell511:PairCell.Row:=⟨33,40,9,3,21,some 21,17,some 17,386045,[MeasuredChoices.test869],[AxisChoices.test1838]⟩
def choice511:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check511:PairPrices.valid cell511 (0:Fin 18) choice511:=by decide +kernel
def cell512:PairCell.Row:=⟨33,40,9,3,21,some 21,18,some 18,386045,[MeasuredChoices.test869],[AxisChoices.test1839]⟩
def choice512:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check512:PairPrices.valid cell512 (0:Fin 18) choice512:=by decide +kernel
def cell513:PairCell.Row:=⟨33,40,9,3,21,some 21,19,some 19,386045,[MeasuredChoices.test869],[AxisChoices.test1840]⟩
def choice513:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check513:PairPrices.valid cell513 (0:Fin 18) choice513:=by decide +kernel
def cell514:PairCell.Row:=⟨33,40,9,3,21,some 21,20,some 20,386045,[MeasuredChoices.test869],[AxisChoices.test1841]⟩
def choice514:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check514:PairPrices.valid cell514 (0:Fin 18) choice514:=by decide +kernel
def cell515:PairCell.Row:=⟨33,40,9,3,21,some 21,21,some 21,386045,[MeasuredChoices.test869],[AxisChoices.test1842]⟩
def choice515:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check515:PairPrices.valid cell515 (0:Fin 18) choice515:=by decide +kernel
def cell516:PairCell.Row:=⟨33,40,9,3,20,some 20,0,some 0,386045,[MeasuredChoices.test856],[AxisChoices.test1821]⟩
def choice516:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check516:PairPrices.valid cell516 (0:Fin 18) choice516:=by decide +kernel
def cell517:PairCell.Row:=⟨33,40,9,3,20,some 20,1,some 1,386045,[MeasuredChoices.test856],[AxisChoices.test1822]⟩
def choice517:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check517:PairPrices.valid cell517 (0:Fin 18) choice517:=by decide +kernel
def cell518:PairCell.Row:=⟨33,40,9,3,20,some 20,2,some 2,386045,[MeasuredChoices.test856],[AxisChoices.test1823]⟩
def choice518:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check518:PairPrices.valid cell518 (0:Fin 18) choice518:=by decide +kernel
def cell519:PairCell.Row:=⟨33,40,9,3,20,some 20,3,some 3,386045,[MeasuredChoices.test856],[AxisChoices.test1824]⟩
def choice519:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check519:PairPrices.valid cell519 (0:Fin 18) choice519:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2616

-- Source: Research6969.PairReceipts026
section Z6969Source2617
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell520:PairCell.Row:=⟨33,40,9,3,20,some 20,4,some 4,386045,[MeasuredChoices.test856],[AxisChoices.test1825]⟩
def choice520:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check520:PairPrices.valid cell520 (0:Fin 18) choice520:=by decide +kernel
def cell521:PairCell.Row:=⟨33,40,9,3,20,some 20,5,some 5,386045,[MeasuredChoices.test856],[AxisChoices.test1826]⟩
def choice521:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check521:PairPrices.valid cell521 (0:Fin 18) choice521:=by decide +kernel
def cell522:PairCell.Row:=⟨33,40,9,3,20,some 20,6,some 6,386045,[MeasuredChoices.test856],[AxisChoices.test1827]⟩
def choice522:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check522:PairPrices.valid cell522 (0:Fin 18) choice522:=by decide +kernel
def cell523:PairCell.Row:=⟨33,40,9,3,20,some 20,7,some 7,386045,[MeasuredChoices.test856],[AxisChoices.test1828]⟩
def choice523:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check523:PairPrices.valid cell523 (0:Fin 18) choice523:=by decide +kernel
def cell524:PairCell.Row:=⟨33,40,9,3,20,some 20,8,some 8,386045,[MeasuredChoices.test856],[AxisChoices.test1829]⟩
def choice524:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check524:PairPrices.valid cell524 (0:Fin 18) choice524:=by decide +kernel
def cell525:PairCell.Row:=⟨33,40,9,3,20,some 20,9,some 9,386045,[MeasuredChoices.test856],[AxisChoices.test1830]⟩
def choice525:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check525:PairPrices.valid cell525 (0:Fin 18) choice525:=by decide +kernel
def cell526:PairCell.Row:=⟨33,40,9,3,20,some 20,10,some 10,386045,[MeasuredChoices.test856],[AxisChoices.test1831]⟩
def choice526:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check526:PairPrices.valid cell526 (0:Fin 18) choice526:=by decide +kernel
def cell527:PairCell.Row:=⟨33,40,9,3,20,some 20,11,some 11,386045,[MeasuredChoices.test856],[AxisChoices.test1832]⟩
def choice527:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check527:PairPrices.valid cell527 (0:Fin 18) choice527:=by decide +kernel
def cell528:PairCell.Row:=⟨33,40,9,3,20,some 20,12,some 12,386045,[MeasuredChoices.test856],[AxisChoices.test1833]⟩
def choice528:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check528:PairPrices.valid cell528 (0:Fin 18) choice528:=by decide +kernel
def cell529:PairCell.Row:=⟨33,40,9,3,20,some 20,13,some 13,386045,[MeasuredChoices.test856],[AxisChoices.test1834]⟩
def choice529:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check529:PairPrices.valid cell529 (0:Fin 18) choice529:=by decide +kernel
def cell530:PairCell.Row:=⟨33,40,9,3,20,some 20,14,some 14,386045,[MeasuredChoices.test856],[AxisChoices.test1835]⟩
def choice530:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check530:PairPrices.valid cell530 (0:Fin 18) choice530:=by decide +kernel
def cell531:PairCell.Row:=⟨33,40,9,3,20,some 20,15,some 15,386045,[MeasuredChoices.test856],[AxisChoices.test1836]⟩
def choice531:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check531:PairPrices.valid cell531 (0:Fin 18) choice531:=by decide +kernel
def cell532:PairCell.Row:=⟨33,40,9,3,20,some 20,16,some 16,386045,[MeasuredChoices.test856],[AxisChoices.test1837]⟩
def choice532:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check532:PairPrices.valid cell532 (0:Fin 18) choice532:=by decide +kernel
def cell533:PairCell.Row:=⟨33,40,9,3,20,some 20,17,some 17,386045,[MeasuredChoices.test856],[AxisChoices.test1838]⟩
def choice533:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check533:PairPrices.valid cell533 (0:Fin 18) choice533:=by decide +kernel
def cell534:PairCell.Row:=⟨33,40,9,3,20,some 20,18,some 18,386045,[MeasuredChoices.test856],[AxisChoices.test1839]⟩
def choice534:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check534:PairPrices.valid cell534 (0:Fin 18) choice534:=by decide +kernel
def cell535:PairCell.Row:=⟨33,40,9,3,20,some 20,19,some 19,386045,[MeasuredChoices.test856],[AxisChoices.test1840]⟩
def choice535:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check535:PairPrices.valid cell535 (0:Fin 18) choice535:=by decide +kernel
def cell536:PairCell.Row:=⟨33,40,9,3,20,some 20,20,some 20,386045,[MeasuredChoices.test856],[AxisChoices.test1841]⟩
def choice536:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check536:PairPrices.valid cell536 (0:Fin 18) choice536:=by decide +kernel
def cell537:PairCell.Row:=⟨33,40,9,3,19,some 19,0,some 0,386045,[MeasuredChoices.test843],[AxisChoices.test1821]⟩
def choice537:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check537:PairPrices.valid cell537 (0:Fin 18) choice537:=by decide +kernel
def cell538:PairCell.Row:=⟨33,40,9,3,19,some 19,1,some 1,386045,[MeasuredChoices.test843],[AxisChoices.test1822]⟩
def choice538:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check538:PairPrices.valid cell538 (0:Fin 18) choice538:=by decide +kernel
def cell539:PairCell.Row:=⟨33,40,9,3,19,some 19,2,some 2,386045,[MeasuredChoices.test843],[AxisChoices.test1823]⟩
def choice539:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check539:PairPrices.valid cell539 (0:Fin 18) choice539:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2617

-- Source: Research6969.PairReceipts027
section Z6969Source2618
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell540:PairCell.Row:=⟨33,40,9,3,19,some 19,3,some 3,386045,[MeasuredChoices.test843],[AxisChoices.test1824]⟩
def choice540:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check540:PairPrices.valid cell540 (0:Fin 18) choice540:=by decide +kernel
def cell541:PairCell.Row:=⟨33,40,9,3,19,some 19,4,some 4,386045,[MeasuredChoices.test843],[AxisChoices.test1825]⟩
def choice541:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check541:PairPrices.valid cell541 (0:Fin 18) choice541:=by decide +kernel
def cell542:PairCell.Row:=⟨33,40,9,3,19,some 19,5,some 5,386045,[MeasuredChoices.test843],[AxisChoices.test1826]⟩
def choice542:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check542:PairPrices.valid cell542 (0:Fin 18) choice542:=by decide +kernel
def cell543:PairCell.Row:=⟨33,40,9,3,19,some 19,6,some 6,386045,[MeasuredChoices.test843],[AxisChoices.test1827]⟩
def choice543:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check543:PairPrices.valid cell543 (0:Fin 18) choice543:=by decide +kernel
def cell544:PairCell.Row:=⟨33,40,9,3,19,some 19,7,some 7,386045,[MeasuredChoices.test843],[AxisChoices.test1828]⟩
def choice544:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check544:PairPrices.valid cell544 (0:Fin 18) choice544:=by decide +kernel
def cell545:PairCell.Row:=⟨33,40,9,3,19,some 19,8,some 8,386045,[MeasuredChoices.test843],[AxisChoices.test1829]⟩
def choice545:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check545:PairPrices.valid cell545 (0:Fin 18) choice545:=by decide +kernel
def cell546:PairCell.Row:=⟨33,40,9,3,19,some 19,9,some 9,386045,[MeasuredChoices.test843],[AxisChoices.test1830]⟩
def choice546:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check546:PairPrices.valid cell546 (0:Fin 18) choice546:=by decide +kernel
def cell547:PairCell.Row:=⟨33,40,9,3,19,some 19,10,some 10,386045,[MeasuredChoices.test843],[AxisChoices.test1831]⟩
def choice547:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check547:PairPrices.valid cell547 (0:Fin 18) choice547:=by decide +kernel
def cell548:PairCell.Row:=⟨33,40,9,3,19,some 19,11,some 11,386045,[MeasuredChoices.test843],[AxisChoices.test1832]⟩
def choice548:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check548:PairPrices.valid cell548 (0:Fin 18) choice548:=by decide +kernel
def cell549:PairCell.Row:=⟨33,40,9,3,19,some 19,12,some 12,386045,[MeasuredChoices.test843],[AxisChoices.test1833]⟩
def choice549:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check549:PairPrices.valid cell549 (0:Fin 18) choice549:=by decide +kernel
def cell550:PairCell.Row:=⟨33,40,9,3,19,some 19,13,some 13,386045,[MeasuredChoices.test843],[AxisChoices.test1834]⟩
def choice550:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check550:PairPrices.valid cell550 (0:Fin 18) choice550:=by decide +kernel
def cell551:PairCell.Row:=⟨33,40,9,3,19,some 19,14,some 14,386045,[MeasuredChoices.test843],[AxisChoices.test1835]⟩
def choice551:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check551:PairPrices.valid cell551 (0:Fin 18) choice551:=by decide +kernel
def cell552:PairCell.Row:=⟨33,40,9,3,19,some 19,15,some 15,386045,[MeasuredChoices.test843],[AxisChoices.test1836]⟩
def choice552:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check552:PairPrices.valid cell552 (0:Fin 18) choice552:=by decide +kernel
def cell553:PairCell.Row:=⟨33,40,9,3,19,some 19,16,some 16,386045,[MeasuredChoices.test843],[AxisChoices.test1837]⟩
def choice553:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check553:PairPrices.valid cell553 (0:Fin 18) choice553:=by decide +kernel
def cell554:PairCell.Row:=⟨33,40,9,3,19,some 19,17,some 17,386045,[MeasuredChoices.test843],[AxisChoices.test1838]⟩
def choice554:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check554:PairPrices.valid cell554 (0:Fin 18) choice554:=by decide +kernel
def cell555:PairCell.Row:=⟨33,40,9,3,19,some 19,18,some 18,386045,[MeasuredChoices.test843],[AxisChoices.test1839]⟩
def choice555:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check555:PairPrices.valid cell555 (0:Fin 18) choice555:=by decide +kernel
def cell556:PairCell.Row:=⟨33,40,9,3,19,some 19,19,some 19,386045,[MeasuredChoices.test843],[AxisChoices.test1840]⟩
def choice556:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check556:PairPrices.valid cell556 (0:Fin 18) choice556:=by decide +kernel
def cell557:PairCell.Row:=⟨33,40,9,3,18,some 18,0,some 0,386045,[MeasuredChoices.test831],[AxisChoices.test1821]⟩
def choice557:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check557:PairPrices.valid cell557 (0:Fin 18) choice557:=by decide +kernel
def cell558:PairCell.Row:=⟨33,40,9,3,18,some 18,1,some 1,386045,[MeasuredChoices.test831],[AxisChoices.test1822]⟩
def choice558:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check558:PairPrices.valid cell558 (0:Fin 18) choice558:=by decide +kernel
def cell559:PairCell.Row:=⟨33,40,9,3,18,some 18,2,some 2,386045,[MeasuredChoices.test831],[AxisChoices.test1823]⟩
def choice559:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check559:PairPrices.valid cell559 (0:Fin 18) choice559:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2618

-- Source: Research6969.PairReceipts028
section Z6969Source2619
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell560:PairCell.Row:=⟨33,40,9,3,18,some 18,3,some 3,386045,[MeasuredChoices.test831],[AxisChoices.test1824]⟩
def choice560:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check560:PairPrices.valid cell560 (0:Fin 18) choice560:=by decide +kernel
def cell561:PairCell.Row:=⟨33,40,9,3,18,some 18,4,some 4,386045,[MeasuredChoices.test831],[AxisChoices.test1825]⟩
def choice561:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check561:PairPrices.valid cell561 (0:Fin 18) choice561:=by decide +kernel
def cell562:PairCell.Row:=⟨33,40,9,3,18,some 18,5,some 5,386045,[MeasuredChoices.test831],[AxisChoices.test1826]⟩
def choice562:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check562:PairPrices.valid cell562 (0:Fin 18) choice562:=by decide +kernel
def cell563:PairCell.Row:=⟨33,40,9,3,18,some 18,6,some 6,386045,[MeasuredChoices.test831],[AxisChoices.test1827]⟩
def choice563:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check563:PairPrices.valid cell563 (0:Fin 18) choice563:=by decide +kernel
def cell564:PairCell.Row:=⟨33,40,9,3,18,some 18,7,some 7,386045,[MeasuredChoices.test831],[AxisChoices.test1828]⟩
def choice564:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check564:PairPrices.valid cell564 (0:Fin 18) choice564:=by decide +kernel
def cell565:PairCell.Row:=⟨33,40,9,3,18,some 18,8,some 8,386045,[MeasuredChoices.test831],[AxisChoices.test1829]⟩
def choice565:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check565:PairPrices.valid cell565 (0:Fin 18) choice565:=by decide +kernel
def cell566:PairCell.Row:=⟨33,40,9,3,18,some 18,9,some 9,386045,[MeasuredChoices.test831],[AxisChoices.test1830]⟩
def choice566:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check566:PairPrices.valid cell566 (0:Fin 18) choice566:=by decide +kernel
def cell567:PairCell.Row:=⟨33,40,9,3,18,some 18,10,some 10,386045,[MeasuredChoices.test831],[AxisChoices.test1831]⟩
def choice567:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check567:PairPrices.valid cell567 (0:Fin 18) choice567:=by decide +kernel
def cell568:PairCell.Row:=⟨33,40,9,3,18,some 18,11,some 11,386045,[MeasuredChoices.test831],[AxisChoices.test1832]⟩
def choice568:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check568:PairPrices.valid cell568 (0:Fin 18) choice568:=by decide +kernel
def cell569:PairCell.Row:=⟨33,40,9,3,18,some 18,12,some 12,386045,[MeasuredChoices.test831],[AxisChoices.test1833]⟩
def choice569:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check569:PairPrices.valid cell569 (0:Fin 18) choice569:=by decide +kernel
def cell570:PairCell.Row:=⟨33,40,9,3,18,some 18,13,some 13,386045,[MeasuredChoices.test831],[AxisChoices.test1834]⟩
def choice570:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check570:PairPrices.valid cell570 (0:Fin 18) choice570:=by decide +kernel
def cell571:PairCell.Row:=⟨33,40,9,3,18,some 18,14,some 14,386045,[MeasuredChoices.test831],[AxisChoices.test1835]⟩
def choice571:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check571:PairPrices.valid cell571 (0:Fin 18) choice571:=by decide +kernel
def cell572:PairCell.Row:=⟨33,40,9,3,18,some 18,15,some 15,386045,[MeasuredChoices.test831],[AxisChoices.test1836]⟩
def choice572:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check572:PairPrices.valid cell572 (0:Fin 18) choice572:=by decide +kernel
def cell573:PairCell.Row:=⟨33,40,9,3,18,some 18,16,some 16,386045,[MeasuredChoices.test831],[AxisChoices.test1837]⟩
def choice573:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check573:PairPrices.valid cell573 (0:Fin 18) choice573:=by decide +kernel
def cell574:PairCell.Row:=⟨33,40,9,3,18,some 18,17,some 17,386045,[MeasuredChoices.test831],[AxisChoices.test1838]⟩
def choice574:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check574:PairPrices.valid cell574 (0:Fin 18) choice574:=by decide +kernel
def cell575:PairCell.Row:=⟨33,40,9,3,18,some 18,18,some 18,386045,[MeasuredChoices.test831],[AxisChoices.test1839]⟩
def choice575:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check575:PairPrices.valid cell575 (0:Fin 18) choice575:=by decide +kernel
def cell576:PairCell.Row:=⟨33,40,9,3,17,some 17,0,some 0,386045,[MeasuredChoices.test821],[AxisChoices.test1821]⟩
def choice576:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check576:PairPrices.valid cell576 (0:Fin 18) choice576:=by decide +kernel
def cell577:PairCell.Row:=⟨33,40,9,3,17,some 17,1,some 1,386045,[MeasuredChoices.test821],[AxisChoices.test1822]⟩
def choice577:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check577:PairPrices.valid cell577 (0:Fin 18) choice577:=by decide +kernel
def cell578:PairCell.Row:=⟨33,40,9,3,17,some 17,2,some 2,386045,[MeasuredChoices.test821],[AxisChoices.test1823]⟩
def choice578:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check578:PairPrices.valid cell578 (0:Fin 18) choice578:=by decide +kernel
def cell579:PairCell.Row:=⟨33,40,9,3,17,some 17,3,some 3,386045,[MeasuredChoices.test821],[AxisChoices.test1824]⟩
def choice579:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check579:PairPrices.valid cell579 (0:Fin 18) choice579:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2619

-- Source: Research6969.PairReceipts029
section Z6969Source2620
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell580:PairCell.Row:=⟨33,40,9,3,17,some 17,4,some 4,386045,[MeasuredChoices.test821],[AxisChoices.test1825]⟩
def choice580:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check580:PairPrices.valid cell580 (0:Fin 18) choice580:=by decide +kernel
def cell581:PairCell.Row:=⟨33,40,9,3,17,some 17,5,some 5,386045,[MeasuredChoices.test821],[AxisChoices.test1826]⟩
def choice581:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check581:PairPrices.valid cell581 (0:Fin 18) choice581:=by decide +kernel
def cell582:PairCell.Row:=⟨33,40,9,3,17,some 17,6,some 6,386045,[MeasuredChoices.test821],[AxisChoices.test1827]⟩
def choice582:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check582:PairPrices.valid cell582 (0:Fin 18) choice582:=by decide +kernel
def cell583:PairCell.Row:=⟨33,40,9,3,17,some 17,7,some 7,386045,[MeasuredChoices.test821],[AxisChoices.test1828]⟩
def choice583:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check583:PairPrices.valid cell583 (0:Fin 18) choice583:=by decide +kernel
def cell584:PairCell.Row:=⟨33,40,9,3,17,some 17,8,some 8,386045,[MeasuredChoices.test821],[AxisChoices.test1829]⟩
def choice584:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check584:PairPrices.valid cell584 (0:Fin 18) choice584:=by decide +kernel
def cell585:PairCell.Row:=⟨33,40,9,3,17,some 17,9,some 9,386045,[MeasuredChoices.test821],[AxisChoices.test1830]⟩
def choice585:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check585:PairPrices.valid cell585 (0:Fin 18) choice585:=by decide +kernel
def cell586:PairCell.Row:=⟨33,40,9,3,17,some 17,10,some 10,386045,[MeasuredChoices.test821],[AxisChoices.test1831]⟩
def choice586:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check586:PairPrices.valid cell586 (0:Fin 18) choice586:=by decide +kernel
def cell587:PairCell.Row:=⟨33,40,9,3,17,some 17,11,some 11,386045,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
def choice587:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check587:PairPrices.valid cell587 (0:Fin 18) choice587:=by decide +kernel
def cell588:PairCell.Row:=⟨33,40,9,3,17,some 17,12,some 12,386045,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
def choice588:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check588:PairPrices.valid cell588 (0:Fin 18) choice588:=by decide +kernel
def cell589:PairCell.Row:=⟨33,40,9,3,17,some 17,13,some 13,386045,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
def choice589:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check589:PairPrices.valid cell589 (0:Fin 18) choice589:=by decide +kernel
def cell590:PairCell.Row:=⟨33,40,9,3,17,some 17,14,some 14,386045,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
def choice590:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check590:PairPrices.valid cell590 (0:Fin 18) choice590:=by decide +kernel
def cell591:PairCell.Row:=⟨33,40,9,3,17,some 17,15,some 15,386045,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
def choice591:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check591:PairPrices.valid cell591 (0:Fin 18) choice591:=by decide +kernel
def cell592:PairCell.Row:=⟨33,40,9,3,17,some 17,16,some 16,386045,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
def choice592:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check592:PairPrices.valid cell592 (0:Fin 18) choice592:=by decide +kernel
def cell593:PairCell.Row:=⟨33,40,9,3,17,some 17,17,some 17,386045,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
def choice593:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check593:PairPrices.valid cell593 (0:Fin 18) choice593:=by decide +kernel
def cell594:PairCell.Row:=⟨33,40,9,3,16,some 16,0,some 0,386045,[MeasuredChoices.test807],[AxisChoices.test1821]⟩
def choice594:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check594:PairPrices.valid cell594 (0:Fin 18) choice594:=by decide +kernel
def cell595:PairCell.Row:=⟨33,40,9,3,16,some 16,1,some 1,386045,[MeasuredChoices.test807],[AxisChoices.test1822]⟩
def choice595:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check595:PairPrices.valid cell595 (0:Fin 18) choice595:=by decide +kernel
def cell596:PairCell.Row:=⟨33,40,9,3,16,some 16,2,some 2,386045,[MeasuredChoices.test807],[AxisChoices.test1823]⟩
def choice596:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check596:PairPrices.valid cell596 (0:Fin 18) choice596:=by decide +kernel
def cell597:PairCell.Row:=⟨33,40,9,3,16,some 16,3,some 3,386045,[MeasuredChoices.test807],[AxisChoices.test1824]⟩
def choice597:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check597:PairPrices.valid cell597 (0:Fin 18) choice597:=by decide +kernel
def cell598:PairCell.Row:=⟨33,40,9,3,16,some 16,4,some 4,386045,[MeasuredChoices.test807],[AxisChoices.test1825]⟩
def choice598:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check598:PairPrices.valid cell598 (0:Fin 18) choice598:=by decide +kernel
def cell599:PairCell.Row:=⟨33,40,9,3,16,some 16,5,some 5,386045,[MeasuredChoices.test807],[AxisChoices.test1826]⟩
def choice599:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check599:PairPrices.valid cell599 (0:Fin 18) choice599:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2620

-- Source: Research6969.PairReceipts030
section Z6969Source2621
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell600:PairCell.Row:=⟨33,40,9,3,16,some 16,6,some 6,386045,[MeasuredChoices.test807],[AxisChoices.test1827]⟩
def choice600:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check600:PairPrices.valid cell600 (0:Fin 18) choice600:=by decide +kernel
def cell601:PairCell.Row:=⟨33,40,9,3,16,some 16,7,some 7,386045,[MeasuredChoices.test807],[AxisChoices.test1828]⟩
def choice601:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check601:PairPrices.valid cell601 (0:Fin 18) choice601:=by decide +kernel
def cell602:PairCell.Row:=⟨33,40,9,3,16,some 16,8,some 8,386045,[MeasuredChoices.test807],[AxisChoices.test1829]⟩
def choice602:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check602:PairPrices.valid cell602 (0:Fin 18) choice602:=by decide +kernel
def cell603:PairCell.Row:=⟨33,40,9,3,16,some 16,9,some 9,386045,[MeasuredChoices.test807],[AxisChoices.test1830]⟩
def choice603:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check603:PairPrices.valid cell603 (0:Fin 18) choice603:=by decide +kernel
def cell604:PairCell.Row:=⟨33,40,9,3,16,some 16,10,some 10,386045,[MeasuredChoices.test807],[AxisChoices.test1831]⟩
def choice604:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check604:PairPrices.valid cell604 (0:Fin 18) choice604:=by decide +kernel
def cell605:PairCell.Row:=⟨33,40,9,3,16,some 16,11,some 11,386045,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
def choice605:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check605:PairPrices.valid cell605 (0:Fin 18) choice605:=by decide +kernel
def cell606:PairCell.Row:=⟨33,40,9,3,16,some 16,12,some 12,386045,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
def choice606:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check606:PairPrices.valid cell606 (0:Fin 18) choice606:=by decide +kernel
def cell607:PairCell.Row:=⟨33,40,9,3,16,some 16,13,some 13,386045,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
def choice607:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check607:PairPrices.valid cell607 (0:Fin 18) choice607:=by decide +kernel
def cell608:PairCell.Row:=⟨33,40,9,3,16,some 16,14,some 14,386045,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
def choice608:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check608:PairPrices.valid cell608 (0:Fin 18) choice608:=by decide +kernel
def cell609:PairCell.Row:=⟨33,40,9,3,16,some 16,15,some 15,386045,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
def choice609:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check609:PairPrices.valid cell609 (0:Fin 18) choice609:=by decide +kernel
def cell610:PairCell.Row:=⟨33,40,9,3,16,some 16,16,some 16,386045,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
def choice610:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check610:PairPrices.valid cell610 (0:Fin 18) choice610:=by decide +kernel
def cell611:PairCell.Row:=⟨33,40,9,3,15,some 15,0,some 0,386045,[MeasuredChoices.test797],[AxisChoices.test1821]⟩
def choice611:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check611:PairPrices.valid cell611 (0:Fin 18) choice611:=by decide +kernel
def cell612:PairCell.Row:=⟨33,40,9,3,15,some 15,1,some 1,386045,[MeasuredChoices.test797],[AxisChoices.test1822]⟩
def choice612:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check612:PairPrices.valid cell612 (0:Fin 18) choice612:=by decide +kernel
def cell613:PairCell.Row:=⟨33,40,9,3,15,some 15,2,some 2,386045,[MeasuredChoices.test797],[AxisChoices.test1823]⟩
def choice613:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check613:PairPrices.valid cell613 (0:Fin 18) choice613:=by decide +kernel
def cell614:PairCell.Row:=⟨33,40,9,3,15,some 15,3,some 3,386045,[MeasuredChoices.test797],[AxisChoices.test1824]⟩
def choice614:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check614:PairPrices.valid cell614 (0:Fin 18) choice614:=by decide +kernel
def cell615:PairCell.Row:=⟨33,40,9,3,15,some 15,4,some 4,386045,[MeasuredChoices.test797],[AxisChoices.test1825]⟩
def choice615:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check615:PairPrices.valid cell615 (0:Fin 18) choice615:=by decide +kernel
def cell616:PairCell.Row:=⟨33,40,9,3,15,some 15,5,some 5,386045,[MeasuredChoices.test797],[AxisChoices.test1826]⟩
def choice616:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check616:PairPrices.valid cell616 (0:Fin 18) choice616:=by decide +kernel
def cell617:PairCell.Row:=⟨33,40,9,3,15,some 15,6,some 6,386045,[MeasuredChoices.test797],[AxisChoices.test1827]⟩
def choice617:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check617:PairPrices.valid cell617 (0:Fin 18) choice617:=by decide +kernel
def cell618:PairCell.Row:=⟨33,40,9,3,15,some 15,7,some 7,386045,[MeasuredChoices.test797],[AxisChoices.test1828]⟩
def choice618:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check618:PairPrices.valid cell618 (0:Fin 18) choice618:=by decide +kernel
def cell619:PairCell.Row:=⟨33,40,9,3,15,some 15,8,some 8,386045,[MeasuredChoices.test797],[AxisChoices.test1829]⟩
def choice619:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check619:PairPrices.valid cell619 (0:Fin 18) choice619:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2621

-- Source: Research6969.HardFit1At110
section Z6969Source2622
set_option autoImplicit true
namespace Research6969.HardFit1At110
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,13,some 14⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell627 PairReceipts.choice627 PairReceipts.check627 (none) (by decide)
theorem case110: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,13,some 14⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell611 PairReceipts.choice611 PairReceipts.check611 (none) (by decide)
private theorem leaf2:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell612 PairReceipts.choice612 PairReceipts.check612 (none) (by decide)
private theorem leaf3:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell613 PairReceipts.choice613 PairReceipts.check613 (none) (by decide)
private theorem leaf4:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell614 PairReceipts.choice614 PairReceipts.check614 (none) (by decide)
private theorem leaf5:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell615 PairReceipts.choice615 PairReceipts.check615 (none) (by decide)
private theorem leaf6:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell616 PairReceipts.choice616 PairReceipts.check616 (none) (by decide)
private theorem leaf7:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell617 PairReceipts.choice617 PairReceipts.check617 (none) (by decide)
private theorem leaf8:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell618 PairReceipts.choice618 PairReceipts.check618 (none) (by decide)
private theorem leaf9:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell619 PairReceipts.choice619 PairReceipts.check619 (none) (by decide)
private theorem leaf10:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell620 PairReceipts.choice620 PairReceipts.check620 (none) (by decide)
private theorem leaf11:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell621 PairReceipts.choice621 PairReceipts.check621 (none) (by decide)
private theorem leaf12:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell622 PairReceipts.choice622 PairReceipts.check622 (none) (by decide)
private theorem leaf13:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell623 PairReceipts.choice623 PairReceipts.check623 (none) (by decide)
private theorem leaf14:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell624 PairReceipts.choice624 PairReceipts.check624 (none) (by decide)
private theorem leaf15:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell625 PairReceipts.choice625 PairReceipts.check625 (none) (by decide)
private theorem leaf16:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell626 PairReceipts.choice626 PairReceipts.check626 (none) (by decide)
private theorem axis17:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,14,some 15,386045,none⟩:=PairRoute.axis 14 leaf15 leaf16
private theorem axis18:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,13,some 15,386045,none⟩:=PairRoute.axis 13 leaf14 axis17
private theorem axis19:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,12,some 15,386045,none⟩:=PairRoute.axis 12 leaf13 axis18
private theorem axis20:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,11,some 15,386045,none⟩:=PairRoute.axis 11 leaf12 axis19
private theorem axis21:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,10,some 15,386045,none⟩:=PairRoute.axis 10 leaf11 axis20
private theorem axis22:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,9,some 15,386045,none⟩:=PairRoute.axis 9 leaf10 axis21
private theorem axis23:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,8,some 15,386045,none⟩:=PairRoute.axis 8 leaf9 axis22
private theorem axis24:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,7,some 15,386045,none⟩:=PairRoute.axis 7 leaf8 axis23
private theorem axis25:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,6,some 15,386045,none⟩:=PairRoute.axis 6 leaf7 axis24
private theorem axis26:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,5,some 15,386045,none⟩:=PairRoute.axis 5 leaf6 axis25
private theorem axis27:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,4,some 15,386045,none⟩:=PairRoute.axis 4 leaf5 axis26
private theorem axis28:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,3,some 15,386045,none⟩:=PairRoute.axis 3 leaf4 axis27
private theorem axis29:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,2,some 15,386045,none⟩:=PairRoute.axis 2 leaf3 axis28
private theorem axis30:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,1,some 15,386045,none⟩:=PairRoute.axis 1 leaf2 axis29
private theorem axis31:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,0,some 15,386045,none⟩:=PairRoute.axis 0 leaf1 axis30
private theorem allAxes32:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,15,some 15⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis31
theorem case111: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,15,some 15⟩:=PairRoute.start _ allAxes32
private theorem leaf33:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell594 PairReceipts.choice594 PairReceipts.check594 (none) (by decide)
private theorem leaf34:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell595 PairReceipts.choice595 PairReceipts.check595 (none) (by decide)
private theorem leaf35:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell596 PairReceipts.choice596 PairReceipts.check596 (none) (by decide)
private theorem leaf36:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell597 PairReceipts.choice597 PairReceipts.check597 (none) (by decide)
private theorem leaf37:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell598 PairReceipts.choice598 PairReceipts.check598 (none) (by decide)
private theorem leaf38:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell599 PairReceipts.choice599 PairReceipts.check599 (none) (by decide)
private theorem leaf39:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell600 PairReceipts.choice600 PairReceipts.check600 (none) (by decide)
private theorem leaf40:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell601 PairReceipts.choice601 PairReceipts.check601 (none) (by decide)
private theorem leaf41:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell602 PairReceipts.choice602 PairReceipts.check602 (none) (by decide)
private theorem leaf42:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell603 PairReceipts.choice603 PairReceipts.check603 (none) (by decide)
private theorem leaf43:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell604 PairReceipts.choice604 PairReceipts.check604 (none) (by decide)
private theorem leaf44:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell605 PairReceipts.choice605 PairReceipts.check605 (none) (by decide)
private theorem leaf45:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell606 PairReceipts.choice606 PairReceipts.check606 (none) (by decide)
private theorem leaf46:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell607 PairReceipts.choice607 PairReceipts.check607 (none) (by decide)
private theorem leaf47:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell608 PairReceipts.choice608 PairReceipts.check608 (none) (by decide)
private theorem leaf48:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell609 PairReceipts.choice609 PairReceipts.check609 (none) (by decide)
private theorem leaf49:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell610 PairReceipts.choice610 PairReceipts.check610 (none) (by decide)
private theorem axis50:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,15,some 16,386045,none⟩:=PairRoute.axis 15 leaf48 leaf49
private theorem axis51:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,14,some 16,386045,none⟩:=PairRoute.axis 14 leaf47 axis50
private theorem axis52:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,13,some 16,386045,none⟩:=PairRoute.axis 13 leaf46 axis51
private theorem axis53:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,12,some 16,386045,none⟩:=PairRoute.axis 12 leaf45 axis52
private theorem axis54:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,11,some 16,386045,none⟩:=PairRoute.axis 11 leaf44 axis53
private theorem axis55:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,10,some 16,386045,none⟩:=PairRoute.axis 10 leaf43 axis54
private theorem axis56:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,9,some 16,386045,none⟩:=PairRoute.axis 9 leaf42 axis55
private theorem axis57:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,8,some 16,386045,none⟩:=PairRoute.axis 8 leaf41 axis56
private theorem axis58:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,7,some 16,386045,none⟩:=PairRoute.axis 7 leaf40 axis57
private theorem axis59:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,6,some 16,386045,none⟩:=PairRoute.axis 6 leaf39 axis58
private theorem axis60:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,5,some 16,386045,none⟩:=PairRoute.axis 5 leaf38 axis59
private theorem axis61:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,4,some 16,386045,none⟩:=PairRoute.axis 4 leaf37 axis60
private theorem axis62:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,3,some 16,386045,none⟩:=PairRoute.axis 3 leaf36 axis61
private theorem axis63:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,2,some 16,386045,none⟩:=PairRoute.axis 2 leaf35 axis62
private theorem axis64:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,1,some 16,386045,none⟩:=PairRoute.axis 1 leaf34 axis63
private theorem axis65:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,0,some 16,386045,none⟩:=PairRoute.axis 0 leaf33 axis64
private theorem allAxes66:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,16,some 16⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis65
theorem case112: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,16,some 16⟩:=PairRoute.start _ allAxes66
private theorem leaf67:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell576 PairReceipts.choice576 PairReceipts.check576 (none) (by decide)
private theorem leaf68:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell577 PairReceipts.choice577 PairReceipts.check577 (none) (by decide)
private theorem leaf69:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell578 PairReceipts.choice578 PairReceipts.check578 (none) (by decide)
private theorem leaf70:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell579 PairReceipts.choice579 PairReceipts.check579 (none) (by decide)
private theorem leaf71:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell580 PairReceipts.choice580 PairReceipts.check580 (none) (by decide)
private theorem leaf72:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell581 PairReceipts.choice581 PairReceipts.check581 (none) (by decide)
private theorem leaf73:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell582 PairReceipts.choice582 PairReceipts.check582 (none) (by decide)
private theorem leaf74:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell583 PairReceipts.choice583 PairReceipts.check583 (none) (by decide)
private theorem leaf75:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell584 PairReceipts.choice584 PairReceipts.check584 (none) (by decide)
private theorem leaf76:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell585 PairReceipts.choice585 PairReceipts.check585 (none) (by decide)
private theorem leaf77:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell586 PairReceipts.choice586 PairReceipts.check586 (none) (by decide)
private theorem leaf78:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell587 PairReceipts.choice587 PairReceipts.check587 (none) (by decide)
private theorem leaf79:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell588 PairReceipts.choice588 PairReceipts.check588 (none) (by decide)
private theorem leaf80:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell589 PairReceipts.choice589 PairReceipts.check589 (none) (by decide)
private theorem leaf81:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell590 PairReceipts.choice590 PairReceipts.check590 (none) (by decide)
private theorem leaf82:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell591 PairReceipts.choice591 PairReceipts.check591 (none) (by decide)
private theorem leaf83:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell592 PairReceipts.choice592 PairReceipts.check592 (none) (by decide)
private theorem leaf84:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell593 PairReceipts.choice593 PairReceipts.check593 (none) (by decide)
private theorem axis85:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,16,some 17,386045,none⟩:=PairRoute.axis 16 leaf83 leaf84
private theorem axis86:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,15,some 17,386045,none⟩:=PairRoute.axis 15 leaf82 axis85
private theorem axis87:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,14,some 17,386045,none⟩:=PairRoute.axis 14 leaf81 axis86
private theorem axis88:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,13,some 17,386045,none⟩:=PairRoute.axis 13 leaf80 axis87
private theorem axis89:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,12,some 17,386045,none⟩:=PairRoute.axis 12 leaf79 axis88
private theorem axis90:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,11,some 17,386045,none⟩:=PairRoute.axis 11 leaf78 axis89
private theorem axis91:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,10,some 17,386045,none⟩:=PairRoute.axis 10 leaf77 axis90
private theorem axis92:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,9,some 17,386045,none⟩:=PairRoute.axis 9 leaf76 axis91
private theorem axis93:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,8,some 17,386045,none⟩:=PairRoute.axis 8 leaf75 axis92
private theorem axis94:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,7,some 17,386045,none⟩:=PairRoute.axis 7 leaf74 axis93
private theorem axis95:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,6,some 17,386045,none⟩:=PairRoute.axis 6 leaf73 axis94
private theorem axis96:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,5,some 17,386045,none⟩:=PairRoute.axis 5 leaf72 axis95
private theorem axis97:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,4,some 17,386045,none⟩:=PairRoute.axis 4 leaf71 axis96
private theorem axis98:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,3,some 17,386045,none⟩:=PairRoute.axis 3 leaf70 axis97
private theorem axis99:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,2,some 17,386045,none⟩:=PairRoute.axis 2 leaf69 axis98
private theorem axis100:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,1,some 17,386045,none⟩:=PairRoute.axis 1 leaf68 axis99
private theorem axis101:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,0,some 17,386045,none⟩:=PairRoute.axis 0 leaf67 axis100
private theorem allAxes102:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,17,some 17⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis101
theorem case113: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,17,some 17⟩:=PairRoute.start _ allAxes102
private theorem leaf103:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell557 PairReceipts.choice557 PairReceipts.check557 (none) (by decide)
private theorem leaf104:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell558 PairReceipts.choice558 PairReceipts.check558 (none) (by decide)
private theorem leaf105:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell559 PairReceipts.choice559 PairReceipts.check559 (none) (by decide)
private theorem leaf106:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell560 PairReceipts.choice560 PairReceipts.check560 (none) (by decide)
private theorem leaf107:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell561 PairReceipts.choice561 PairReceipts.check561 (none) (by decide)
private theorem leaf108:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell562 PairReceipts.choice562 PairReceipts.check562 (none) (by decide)
private theorem leaf109:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell563 PairReceipts.choice563 PairReceipts.check563 (none) (by decide)
private theorem leaf110:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell564 PairReceipts.choice564 PairReceipts.check564 (none) (by decide)
private theorem leaf111:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell565 PairReceipts.choice565 PairReceipts.check565 (none) (by decide)
private theorem leaf112:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell566 PairReceipts.choice566 PairReceipts.check566 (none) (by decide)
private theorem leaf113:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell567 PairReceipts.choice567 PairReceipts.check567 (none) (by decide)
private theorem leaf114:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell568 PairReceipts.choice568 PairReceipts.check568 (none) (by decide)
private theorem leaf115:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell569 PairReceipts.choice569 PairReceipts.check569 (none) (by decide)
private theorem leaf116:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell570 PairReceipts.choice570 PairReceipts.check570 (none) (by decide)
private theorem leaf117:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell571 PairReceipts.choice571 PairReceipts.check571 (none) (by decide)
private theorem leaf118:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell572 PairReceipts.choice572 PairReceipts.check572 (none) (by decide)
private theorem leaf119:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell573 PairReceipts.choice573 PairReceipts.check573 (none) (by decide)
private theorem leaf120:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell574 PairReceipts.choice574 PairReceipts.check574 (none) (by decide)
private theorem leaf121:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell575 PairReceipts.choice575 PairReceipts.check575 (none) (by decide)
private theorem axis122:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,17,some 18,386045,none⟩:=PairRoute.axis 17 leaf120 leaf121
private theorem axis123:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,16,some 18,386045,none⟩:=PairRoute.axis 16 leaf119 axis122
private theorem axis124:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,15,some 18,386045,none⟩:=PairRoute.axis 15 leaf118 axis123
private theorem axis125:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,14,some 18,386045,none⟩:=PairRoute.axis 14 leaf117 axis124
private theorem axis126:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,13,some 18,386045,none⟩:=PairRoute.axis 13 leaf116 axis125
private theorem axis127:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,12,some 18,386045,none⟩:=PairRoute.axis 12 leaf115 axis126
private theorem axis128:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,11,some 18,386045,none⟩:=PairRoute.axis 11 leaf114 axis127
private theorem axis129:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,10,some 18,386045,none⟩:=PairRoute.axis 10 leaf113 axis128
private theorem axis130:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,9,some 18,386045,none⟩:=PairRoute.axis 9 leaf112 axis129
private theorem axis131:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,8,some 18,386045,none⟩:=PairRoute.axis 8 leaf111 axis130
private theorem axis132:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,7,some 18,386045,none⟩:=PairRoute.axis 7 leaf110 axis131
private theorem axis133:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,6,some 18,386045,none⟩:=PairRoute.axis 6 leaf109 axis132
private theorem axis134:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,5,some 18,386045,none⟩:=PairRoute.axis 5 leaf108 axis133
private theorem axis135:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,4,some 18,386045,none⟩:=PairRoute.axis 4 leaf107 axis134
private theorem axis136:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,3,some 18,386045,none⟩:=PairRoute.axis 3 leaf106 axis135
private theorem axis137:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,2,some 18,386045,none⟩:=PairRoute.axis 2 leaf105 axis136
private theorem axis138:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,1,some 18,386045,none⟩:=PairRoute.axis 1 leaf104 axis137
private theorem axis139:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,0,some 18,386045,none⟩:=PairRoute.axis 0 leaf103 axis138
private theorem allAxes140:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,18,some 18⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis139
theorem case114: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,18,some 18⟩:=PairRoute.start _ allAxes140
private theorem leaf141:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell537 PairReceipts.choice537 PairReceipts.check537 (none) (by decide)
private theorem leaf142:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell538 PairReceipts.choice538 PairReceipts.check538 (none) (by decide)
private theorem leaf143:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell539 PairReceipts.choice539 PairReceipts.check539 (none) (by decide)
private theorem leaf144:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell540 PairReceipts.choice540 PairReceipts.check540 (none) (by decide)
private theorem leaf145:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell541 PairReceipts.choice541 PairReceipts.check541 (none) (by decide)
private theorem leaf146:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell542 PairReceipts.choice542 PairReceipts.check542 (none) (by decide)
private theorem leaf147:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell543 PairReceipts.choice543 PairReceipts.check543 (none) (by decide)
private theorem leaf148:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell544 PairReceipts.choice544 PairReceipts.check544 (none) (by decide)
private theorem leaf149:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell545 PairReceipts.choice545 PairReceipts.check545 (none) (by decide)
private theorem leaf150:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell546 PairReceipts.choice546 PairReceipts.check546 (none) (by decide)
private theorem leaf151:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell547 PairReceipts.choice547 PairReceipts.check547 (none) (by decide)
private theorem leaf152:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell548 PairReceipts.choice548 PairReceipts.check548 (none) (by decide)
private theorem leaf153:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell549 PairReceipts.choice549 PairReceipts.check549 (none) (by decide)
private theorem leaf154:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell550 PairReceipts.choice550 PairReceipts.check550 (none) (by decide)
private theorem leaf155:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell551 PairReceipts.choice551 PairReceipts.check551 (none) (by decide)
private theorem leaf156:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell552 PairReceipts.choice552 PairReceipts.check552 (none) (by decide)
private theorem leaf157:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell553 PairReceipts.choice553 PairReceipts.check553 (none) (by decide)
private theorem leaf158:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell554 PairReceipts.choice554 PairReceipts.check554 (none) (by decide)
private theorem leaf159:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell555 PairReceipts.choice555 PairReceipts.check555 (none) (by decide)
private theorem leaf160:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,19,some 19,386045,none⟩:=PairLeaves.paired PairReceipts.cell556 PairReceipts.choice556 PairReceipts.check556 (none) (by decide)
private theorem axis161:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,18,some 19,386045,none⟩:=PairRoute.axis 18 leaf159 leaf160
private theorem axis162:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,17,some 19,386045,none⟩:=PairRoute.axis 17 leaf158 axis161
private theorem axis163:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,16,some 19,386045,none⟩:=PairRoute.axis 16 leaf157 axis162
private theorem axis164:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,15,some 19,386045,none⟩:=PairRoute.axis 15 leaf156 axis163
private theorem axis165:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,14,some 19,386045,none⟩:=PairRoute.axis 14 leaf155 axis164
private theorem axis166:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,13,some 19,386045,none⟩:=PairRoute.axis 13 leaf154 axis165
private theorem axis167:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,12,some 19,386045,none⟩:=PairRoute.axis 12 leaf153 axis166
private theorem axis168:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,11,some 19,386045,none⟩:=PairRoute.axis 11 leaf152 axis167
private theorem axis169:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,10,some 19,386045,none⟩:=PairRoute.axis 10 leaf151 axis168
private theorem axis170:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,9,some 19,386045,none⟩:=PairRoute.axis 9 leaf150 axis169
private theorem axis171:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,8,some 19,386045,none⟩:=PairRoute.axis 8 leaf149 axis170
private theorem axis172:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,7,some 19,386045,none⟩:=PairRoute.axis 7 leaf148 axis171
private theorem axis173:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,6,some 19,386045,none⟩:=PairRoute.axis 6 leaf147 axis172
private theorem axis174:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,5,some 19,386045,none⟩:=PairRoute.axis 5 leaf146 axis173
private theorem axis175:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,4,some 19,386045,none⟩:=PairRoute.axis 4 leaf145 axis174
private theorem axis176:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,3,some 19,386045,none⟩:=PairRoute.axis 3 leaf144 axis175
private theorem axis177:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,2,some 19,386045,none⟩:=PairRoute.axis 2 leaf143 axis176
private theorem axis178:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,1,some 19,386045,none⟩:=PairRoute.axis 1 leaf142 axis177
private theorem axis179:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,0,some 19,386045,none⟩:=PairRoute.axis 0 leaf141 axis178
private theorem allAxes180:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,19,some 19⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis179
theorem case115: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,19,some 19⟩:=PairRoute.start _ allAxes180
private theorem leaf181:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell516 PairReceipts.choice516 PairReceipts.check516 (none) (by decide)
private theorem leaf182:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell517 PairReceipts.choice517 PairReceipts.check517 (none) (by decide)
private theorem leaf183:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell518 PairReceipts.choice518 PairReceipts.check518 (none) (by decide)
private theorem leaf184:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell519 PairReceipts.choice519 PairReceipts.check519 (none) (by decide)
private theorem leaf185:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell520 PairReceipts.choice520 PairReceipts.check520 (none) (by decide)
private theorem leaf186:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell521 PairReceipts.choice521 PairReceipts.check521 (none) (by decide)
private theorem leaf187:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell522 PairReceipts.choice522 PairReceipts.check522 (none) (by decide)
private theorem leaf188:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell523 PairReceipts.choice523 PairReceipts.check523 (none) (by decide)
private theorem leaf189:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell524 PairReceipts.choice524 PairReceipts.check524 (none) (by decide)
private theorem leaf190:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell525 PairReceipts.choice525 PairReceipts.check525 (none) (by decide)
private theorem leaf191:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell526 PairReceipts.choice526 PairReceipts.check526 (none) (by decide)
private theorem leaf192:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell527 PairReceipts.choice527 PairReceipts.check527 (none) (by decide)
private theorem leaf193:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell528 PairReceipts.choice528 PairReceipts.check528 (none) (by decide)
private theorem leaf194:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell529 PairReceipts.choice529 PairReceipts.check529 (none) (by decide)
private theorem leaf195:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell530 PairReceipts.choice530 PairReceipts.check530 (none) (by decide)
private theorem leaf196:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell531 PairReceipts.choice531 PairReceipts.check531 (none) (by decide)
private theorem leaf197:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell532 PairReceipts.choice532 PairReceipts.check532 (none) (by decide)
private theorem leaf198:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell533 PairReceipts.choice533 PairReceipts.check533 (none) (by decide)
private theorem leaf199:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell534 PairReceipts.choice534 PairReceipts.check534 (none) (by decide)
private theorem leaf200:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,19,some 19,386045,none⟩:=PairLeaves.paired PairReceipts.cell535 PairReceipts.choice535 PairReceipts.check535 (none) (by decide)
private theorem leaf201:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,20,some 20,386045,none⟩:=PairLeaves.paired PairReceipts.cell536 PairReceipts.choice536 PairReceipts.check536 (none) (by decide)
private theorem axis202:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,19,some 20,386045,none⟩:=PairRoute.axis 19 leaf200 leaf201
private theorem axis203:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,18,some 20,386045,none⟩:=PairRoute.axis 18 leaf199 axis202
private theorem axis204:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,17,some 20,386045,none⟩:=PairRoute.axis 17 leaf198 axis203
private theorem axis205:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,16,some 20,386045,none⟩:=PairRoute.axis 16 leaf197 axis204
private theorem axis206:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,15,some 20,386045,none⟩:=PairRoute.axis 15 leaf196 axis205
private theorem axis207:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,14,some 20,386045,none⟩:=PairRoute.axis 14 leaf195 axis206
private theorem axis208:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,13,some 20,386045,none⟩:=PairRoute.axis 13 leaf194 axis207
private theorem axis209:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,12,some 20,386045,none⟩:=PairRoute.axis 12 leaf193 axis208
private theorem axis210:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,11,some 20,386045,none⟩:=PairRoute.axis 11 leaf192 axis209
private theorem axis211:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,10,some 20,386045,none⟩:=PairRoute.axis 10 leaf191 axis210
private theorem axis212:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,9,some 20,386045,none⟩:=PairRoute.axis 9 leaf190 axis211
private theorem axis213:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,8,some 20,386045,none⟩:=PairRoute.axis 8 leaf189 axis212
private theorem axis214:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,7,some 20,386045,none⟩:=PairRoute.axis 7 leaf188 axis213
private theorem axis215:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,6,some 20,386045,none⟩:=PairRoute.axis 6 leaf187 axis214
private theorem axis216:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,5,some 20,386045,none⟩:=PairRoute.axis 5 leaf186 axis215
private theorem axis217:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,4,some 20,386045,none⟩:=PairRoute.axis 4 leaf185 axis216
private theorem axis218:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,3,some 20,386045,none⟩:=PairRoute.axis 3 leaf184 axis217
private theorem axis219:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,2,some 20,386045,none⟩:=PairRoute.axis 2 leaf183 axis218
private theorem axis220:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,1,some 20,386045,none⟩:=PairRoute.axis 1 leaf182 axis219
private theorem axis221:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,0,some 20,386045,none⟩:=PairRoute.axis 0 leaf181 axis220
private theorem allAxes222:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,20,some 20⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis221
theorem case116: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,20,some 20⟩:=PairRoute.start _ allAxes222
private theorem leaf223:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell494 PairReceipts.choice494 PairReceipts.check494 (none) (by decide)
private theorem leaf224:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell495 PairReceipts.choice495 PairReceipts.check495 (none) (by decide)
private theorem leaf225:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell496 PairReceipts.choice496 PairReceipts.check496 (none) (by decide)
private theorem leaf226:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell497 PairReceipts.choice497 PairReceipts.check497 (none) (by decide)
private theorem leaf227:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell498 PairReceipts.choice498 PairReceipts.check498 (none) (by decide)
private theorem leaf228:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell499 PairReceipts.choice499 PairReceipts.check499 (none) (by decide)
private theorem leaf229:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell500 PairReceipts.choice500 PairReceipts.check500 (none) (by decide)
private theorem leaf230:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell501 PairReceipts.choice501 PairReceipts.check501 (none) (by decide)
private theorem leaf231:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell502 PairReceipts.choice502 PairReceipts.check502 (none) (by decide)
private theorem leaf232:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell503 PairReceipts.choice503 PairReceipts.check503 (none) (by decide)
private theorem leaf233:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell504 PairReceipts.choice504 PairReceipts.check504 (none) (by decide)
private theorem leaf234:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell505 PairReceipts.choice505 PairReceipts.check505 (none) (by decide)
private theorem leaf235:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell506 PairReceipts.choice506 PairReceipts.check506 (none) (by decide)
private theorem leaf236:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell507 PairReceipts.choice507 PairReceipts.check507 (none) (by decide)
private theorem leaf237:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell508 PairReceipts.choice508 PairReceipts.check508 (none) (by decide)
private theorem leaf238:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell509 PairReceipts.choice509 PairReceipts.check509 (none) (by decide)
private theorem leaf239:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell510 PairReceipts.choice510 PairReceipts.check510 (none) (by decide)
private theorem leaf240:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell511 PairReceipts.choice511 PairReceipts.check511 (none) (by decide)
private theorem leaf241:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell512 PairReceipts.choice512 PairReceipts.check512 (none) (by decide)
private theorem leaf242:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,19,some 19,386045,none⟩:=PairLeaves.paired PairReceipts.cell513 PairReceipts.choice513 PairReceipts.check513 (none) (by decide)
private theorem leaf243:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,20,some 20,386045,none⟩:=PairLeaves.paired PairReceipts.cell514 PairReceipts.choice514 PairReceipts.check514 (none) (by decide)
private theorem leaf244:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,21,some 21,386045,none⟩:=PairLeaves.paired PairReceipts.cell515 PairReceipts.choice515 PairReceipts.check515 (none) (by decide)
private theorem axis245:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,20,some 21,386045,none⟩:=PairRoute.axis 20 leaf243 leaf244
private theorem axis246:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,19,some 21,386045,none⟩:=PairRoute.axis 19 leaf242 axis245
private theorem axis247:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,18,some 21,386045,none⟩:=PairRoute.axis 18 leaf241 axis246
private theorem axis248:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,17,some 21,386045,none⟩:=PairRoute.axis 17 leaf240 axis247
private theorem axis249:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,16,some 21,386045,none⟩:=PairRoute.axis 16 leaf239 axis248
private theorem axis250:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,15,some 21,386045,none⟩:=PairRoute.axis 15 leaf238 axis249
private theorem axis251:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,14,some 21,386045,none⟩:=PairRoute.axis 14 leaf237 axis250
private theorem axis252:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,13,some 21,386045,none⟩:=PairRoute.axis 13 leaf236 axis251
private theorem axis253:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,12,some 21,386045,none⟩:=PairRoute.axis 12 leaf235 axis252
private theorem axis254:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,11,some 21,386045,none⟩:=PairRoute.axis 11 leaf234 axis253
private theorem axis255:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,10,some 21,386045,none⟩:=PairRoute.axis 10 leaf233 axis254
private theorem axis256:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,9,some 21,386045,none⟩:=PairRoute.axis 9 leaf232 axis255
private theorem axis257:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,8,some 21,386045,none⟩:=PairRoute.axis 8 leaf231 axis256
private theorem axis258:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,7,some 21,386045,none⟩:=PairRoute.axis 7 leaf230 axis257
private theorem axis259:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,6,some 21,386045,none⟩:=PairRoute.axis 6 leaf229 axis258
private theorem axis260:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,5,some 21,386045,none⟩:=PairRoute.axis 5 leaf228 axis259
private theorem axis261:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,4,some 21,386045,none⟩:=PairRoute.axis 4 leaf227 axis260
private theorem axis262:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,3,some 21,386045,none⟩:=PairRoute.axis 3 leaf226 axis261
private theorem axis263:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,2,some 21,386045,none⟩:=PairRoute.axis 2 leaf225 axis262
private theorem axis264:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,1,some 21,386045,none⟩:=PairRoute.axis 1 leaf224 axis263
private theorem axis265:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,0,some 21,386045,none⟩:=PairRoute.axis 0 leaf223 axis264
private theorem allAxes266:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,21,some 21⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis265
theorem case117: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,21,some 21⟩:=PairRoute.start _ allAxes266
private theorem leaf267:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,22,some 22⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell493 PairReceipts.choice493 PairReceipts.check493 (none) (by decide)
theorem case118: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,22,some 22⟩:=PairRoute.start _ leaf267
private theorem leaf268:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,23,some 24⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell492 PairReceipts.choice492 PairReceipts.check492 (none) (by decide)
theorem case119: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,23,some 24⟩:=PairRoute.start _ leaf268
end Research6969.HardFit1At110
end Z6969Source2622

-- Source: Research6969.HardFit1At120
section Z6969Source2623
set_option autoImplicit true
namespace Research6969.HardFit1At120
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,25,some 26⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell491 PairReceipts.choice491 PairReceipts.check491 (none) (by decide)
theorem case120: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,25,some 26⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,27,some 28⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell490 PairReceipts.choice490 PairReceipts.check490 (none) (by decide)
theorem case121: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,27,some 28⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,29,some 32⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell489 PairReceipts.choice489 PairReceipts.check489 (none) (by decide)
theorem case122: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,29,some 32⟩:=PairRoute.start _ leaf2
private theorem leaf3:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,33,some 36⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell488 PairReceipts.choice488 PairReceipts.check488 (none) (by decide)
theorem case123: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,33,some 36⟩:=PairRoute.start _ leaf3
private theorem leaf4:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,37,some 40⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell487 PairReceipts.choice487 PairReceipts.check487 (none) (by decide)
theorem case124: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,37,some 40⟩:=PairRoute.start _ leaf4
private theorem leaf5:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,41,some 48⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell486 PairReceipts.choice486 PairReceipts.check486 (none) (by decide)
theorem case125: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,41,some 48⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,49,some 64⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell485 PairReceipts.choice485 PairReceipts.check485 (none) (by decide)
theorem case126: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,49,some 64⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,3,65,some 96⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell484 PairReceipts.choice484 PairReceipts.check484 (none) (by decide)
theorem case127: NormalRoute.Done (0:Fin 18) ⟨33,40,9,3,65,some 96⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,13,some 16⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell634 PairReceipts.choice634 PairReceipts.check634 (none) (by decide)
theorem case128: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,13,some 16⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,17,some 20⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell633 PairReceipts.choice633 PairReceipts.check633 (none) (by decide)
theorem case129: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit1At120
end Z6969Source2623

-- Source: Research6969.PairReceipts035
section Z6969Source2624
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell700:PairCell.Row:=⟨41,49,9,2,57,some 64,63,some 63,257363,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check700:(cell700.cap (0:Fin 18)).grade<cell700.lowerGrade-cell700.off:=by decide +kernel
def cell701:PairCell.Row:=⟨41,49,9,2,57,some 64,64,some 64,257363,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check701:(cell701.cap (0:Fin 18)).grade<cell701.lowerGrade-cell701.off:=by decide +kernel
def cell702:PairCell.Row:=⟨41,49,9,2,49,some 56,0,none,257363,[MeasuredChoices.test62],[]⟩
def choice702:PairPrices.Decision:=⟨(.node 8000000000000000),.whole,.impossible,285209⟩
theorem check702:PairPrices.valid cell702 (0:Fin 18) choice702:=by decide +kernel
def cell703:PairCell.Row:=⟨41,49,9,2,49,some 56,0,none,285209,[MeasuredChoices.test104],[]⟩
def choice703:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check703:PairPrices.valid cell703 (0:Fin 18) choice703:=by decide +kernel
def cell704:PairCell.Row:=⟨41,49,9,2,41,some 48,0,none,257363,[MeasuredChoices.test50],[]⟩
def choice704:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check704:PairPrices.valid cell704 (0:Fin 18) choice704:=by decide +kernel
def cell705:PairCell.Row:=⟨41,49,9,2,33,some 40,0,none,257363,[MeasuredChoices.test44],[]⟩
def choice705:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check705:PairPrices.valid cell705 (0:Fin 18) choice705:=by decide +kernel
def cell706:PairCell.Row:=⟨41,49,9,2,29,some 32,0,none,257363,[MeasuredChoices.test39],[]⟩
def choice706:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check706:PairPrices.valid cell706 (0:Fin 18) choice706:=by decide +kernel
def cell707:PairCell.Row:=⟨41,49,9,2,25,some 28,0,none,257363,[MeasuredChoices.test36],[]⟩
def choice707:PairPrices.Decision:=⟨(.node 8000000000000000),.whole,.impossible,302619⟩
theorem check707:PairPrices.valid cell707 (0:Fin 18) choice707:=by decide +kernel
def cell708:PairCell.Row:=⟨41,49,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩
def choice708:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check708:PairPrices.valid cell708 (0:Fin 18) choice708:=by decide +kernel
def cell709:PairCell.Row:=⟨41,49,9,2,21,some 24,0,none,257363,[MeasuredChoices.test25],[]⟩
def choice709:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check709:PairPrices.valid cell709 (0:Fin 18) choice709:=by decide +kernel
def cell710:PairCell.Row:=⟨41,49,9,2,17,some 20,0,none,257363,[],[]⟩
def choice710:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check710:PairPrices.valid cell710 (0:Fin 18) choice710:=by decide +kernel
def cell711:PairCell.Row:=⟨41,49,9,2,13,some 16,0,none,257363,[],[]⟩
def choice711:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check711:PairPrices.valid cell711 (0:Fin 18) choice711:=by decide +kernel
def cell712:PairCell.Row:=⟨41,49,9,2,9,some 12,0,none,257363,[],[]⟩
def choice712:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check712:PairPrices.valid cell712 (0:Fin 18) choice712:=by decide +kernel
def cell713:PairCell.Row:=⟨41,49,9,2,4,some 8,0,none,257363,[],[]⟩
def choice713:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check713:PairPrices.valid cell713 (0:Fin 18) choice713:=by decide +kernel
def cell714:PairCell.Row:=⟨41,49,9,3,47,some 48,0,some 0,386045,[MeasuredChoices.test1141],[AxisChoices.test1821]⟩
def choice714:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check714:PairPrices.valid cell714 (0:Fin 18) choice714:=by decide +kernel
def cell715:PairCell.Row:=⟨41,49,9,3,47,some 48,1,some 1,386045,[MeasuredChoices.test1141],[AxisChoices.test1822]⟩
def choice715:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check715:PairPrices.valid cell715 (0:Fin 18) choice715:=by decide +kernel
def cell716:PairCell.Row:=⟨41,49,9,3,47,some 48,2,some 2,386045,[MeasuredChoices.test1141],[AxisChoices.test1823]⟩
def choice716:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check716:PairPrices.valid cell716 (0:Fin 18) choice716:=by decide +kernel
def cell717:PairCell.Row:=⟨41,49,9,3,47,some 48,3,some 3,386045,[MeasuredChoices.test1141],[AxisChoices.test1824]⟩
def choice717:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check717:PairPrices.valid cell717 (0:Fin 18) choice717:=by decide +kernel
def cell718:PairCell.Row:=⟨41,49,9,3,47,some 48,4,some 4,386045,[MeasuredChoices.test1141],[AxisChoices.test1825]⟩
def choice718:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check718:PairPrices.valid cell718 (0:Fin 18) choice718:=by decide +kernel
def cell719:PairCell.Row:=⟨41,49,9,3,47,some 48,5,some 5,386045,[MeasuredChoices.test1141],[AxisChoices.test1826]⟩
def choice719:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check719:PairPrices.valid cell719 (0:Fin 18) choice719:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2624

-- Source: Research6969.PairReceipts258
section Z6969Source2625
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5160:PairCell.Row:=⟨64,654,12,2,25,some 28,0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩
def choice5160:PairPrices.Decision:=⟨.surface,.intersection,.impossible,0⟩
theorem check5160:PairPrices.valid cell5160 (8:Fin 18) choice5160:=by decide +kernel
def cell5161:PairCell.Row:=⟨64,654,12,2,21,some 24,0,none,257363,[MeasuredChoices.test26],[]⟩
def choice5161:PairPrices.Decision:=⟨.surface,.intersection,.impossible,0⟩
theorem check5161:PairPrices.valid cell5161 (8:Fin 18) choice5161:=by decide +kernel
def cell5162:PairCell.Row:=⟨64,654,12,2,17,some 20,0,none,257363,[],[]⟩
def choice5162:PairPrices.Decision:=⟨.surface,.intersection,.impossible,0⟩
theorem check5162:PairPrices.valid cell5162 (8:Fin 18) choice5162:=by decide +kernel
def cell5163:PairCell.Row:=⟨64,654,12,2,13,some 16,0,none,257363,[],[]⟩
def choice5163:PairPrices.Decision:=⟨.surface,.intersection,.impossible,0⟩
theorem check5163:PairPrices.valid cell5163 (8:Fin 18) choice5163:=by decide +kernel
def cell5164:PairCell.Row:=⟨64,654,12,2,9,some 12,0,none,257363,[],[]⟩
def choice5164:PairPrices.Decision:=⟨.surface,.intersection,.surface,0⟩
theorem check5164:PairPrices.valid cell5164 (8:Fin 18) choice5164:=by decide +kernel
def cell5165:PairCell.Row:=⟨33,40,9,4,25,some 28,0,none,514727,[MeasuredChoices.test1272],[]⟩
theorem check5165:ThreeRule.check cell5165 (0:Fin 18)=true:=by decide +kernel
def cell5166:PairCell.Row:=⟨41,49,9,3,65,some 96,0,none,386045,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩
theorem check5166:ThreeRule.check cell5166 (0:Fin 18)=true:=by decide +kernel
def cell5167:PairCell.Row:=⟨41,49,9,3,57,some 64,0,none,386045,[MeasuredChoices.test1144],[]⟩
theorem check5167:ThreeRule.check cell5167 (0:Fin 18)=true:=by decide +kernel
def cell5168:PairCell.Row:=⟨41,49,9,3,49,some 56,0,none,386045,[MeasuredChoices.test1143],[]⟩
theorem check5168:ThreeRule.check cell5168 (0:Fin 18)=true:=by decide +kernel
def cell5169:PairCell.Row:=⟨25,27,9,3,21,some 24,0,none,386045,[MeasuredChoices.test869],[]⟩
theorem check5169:ThreeRule.check cell5169 (1:Fin 18)=true:=by decide +kernel
def cell5170:PairCell.Row:=⟨28,32,9,3,25,some 28,0,none,386045,[MeasuredChoices.test924],[]⟩
theorem check5170:ThreeRule.check cell5170 (1:Fin 18)=true:=by decide +kernel
def cell5171:PairCell.Row:=⟨33,40,9,3,33,some 40,0,none,386045,[MeasuredChoices.test1029],[]⟩
theorem check5171:ThreeRule.check cell5171 (1:Fin 18)=true:=by decide +kernel
def cell5172:PairCell.Row:=⟨41,49,9,3,65,some 96,0,none,386045,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩
theorem check5172:ThreeRule.check cell5172 (1:Fin 18)=true:=by decide +kernel
def cell5173:PairCell.Row:=⟨41,49,9,3,49,some 64,0,none,386045,[MeasuredChoices.test1143],[]⟩
theorem check5173:ThreeRule.check cell5173 (1:Fin 18)=true:=by decide +kernel
def cell5174:PairCell.Row:=⟨41,49,9,3,45,some 48,0,none,386045,[MeasuredChoices.test1139],[]⟩
theorem check5174:ThreeRule.check cell5174 (1:Fin 18)=true:=by decide +kernel
def cell5175:PairCell.Row:=⟨41,49,9,3,41,some 44,0,none,386045,[MeasuredChoices.test1133],[]⟩
theorem check5175:ThreeRule.check cell5175 (1:Fin 18)=true:=by decide +kernel
def cell5176:PairCell.Row:=⟨50,50,10,3,15,some 15,0,some 0,386045,[MeasuredChoices.test797],[AxisChoices.test1821]⟩
def choice5176:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check5176:PairPrices.valid cell5176 (1:Fin 18) choice5176:=by decide +kernel
def cell5177:PairCell.Row:=⟨50,50,10,3,15,some 15,1,some 1,386045,[MeasuredChoices.test797],[AxisChoices.test1822]⟩
def choice5177:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check5177:PairPrices.valid cell5177 (1:Fin 18) choice5177:=by decide +kernel
def cell5178:PairCell.Row:=⟨50,50,10,3,15,some 15,2,some 2,386045,[MeasuredChoices.test797],[AxisChoices.test1823]⟩
def choice5178:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check5178:PairPrices.valid cell5178 (1:Fin 18) choice5178:=by decide +kernel
def cell5179:PairCell.Row:=⟨50,50,10,3,15,some 15,3,some 3,386045,[MeasuredChoices.test797],[AxisChoices.test1824]⟩
def choice5179:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check5179:PairPrices.valid cell5179 (1:Fin 18) choice5179:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2625

-- Source: Research6969.HardFit1At130
section Z6969Source2626
set_option autoImplicit true
namespace Research6969.HardFit1At130
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,21,some 24⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell632 PairReceipts.choice632 PairReceipts.check632 (none) (by decide)
theorem case130: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,21,some 24⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,25,some 28⟩,0,none,514727,none⟩:=PairLeaves.three PairReceipts.cell5165 PairReceipts.check5165 (by decide) (none)
theorem case131: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,25,some 28⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,29,some 32⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell631 PairReceipts.choice631 PairReceipts.check631 (none) (by decide)
theorem case132: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,29,some 32⟩:=PairRoute.start _ leaf2
private theorem leaf3:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,4,33,some 40⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell630 PairReceipts.choice630 PairReceipts.check630 (none) (by decide)
theorem case133: NormalRoute.Done (0:Fin 18) ⟨33,40,9,4,33,some 40⟩:=PairRoute.start _ leaf3
private theorem leaf4:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,1,65,some 96⟩,0,none,128681,none⟩:=PairLeaves.paired PairReceipts.cell635 PairReceipts.choice635 PairReceipts.check635 (none) (by decide)
theorem case134: NormalRoute.Done (0:Fin 18) ⟨41,49,9,1,65,some 96⟩:=PairRoute.start _ leaf4
private theorem leaf5:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,4,some 8⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell713 PairReceipts.choice713 PairReceipts.check713 (none) (by decide)
theorem case135: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,4,some 8⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,9,some 12⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell712 PairReceipts.choice712 PairReceipts.check712 (none) (by decide)
theorem case136: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,13,some 16⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell711 PairReceipts.choice711 PairReceipts.check711 (none) (by decide)
theorem case137: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,17,some 20⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell710 PairReceipts.choice710 PairReceipts.check710 (none) (by decide)
theorem case138: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (0:Fin 18) ⟨⟨41,49,9,2,21,some 24⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell709 PairReceipts.choice709 PairReceipts.check709 (none) (by decide)
theorem case139: NormalRoute.Done (0:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf9
end Research6969.HardFit1At130
end Z6969Source2626
