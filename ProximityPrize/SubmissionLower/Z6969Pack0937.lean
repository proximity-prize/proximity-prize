import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0936
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.HardFit1At070
section Z6969Source2603
set_option autoImplicit true
namespace Research6969.HardFit1At070
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,21,some 24⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell299 PairReceipts.choice299 PairReceipts.check299 (none) (by decide)
theorem case70: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,25,some 28⟩,0,none,257363,some 302619⟩:=PairLeaves.paired PairReceipts.cell297 PairReceipts.choice297 PairReceipts.check297 (some 302619) (by decide)
private theorem leaf2:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,25,some 28⟩,0,none,302619,none⟩:=PairLeaves.paired PairReceipts.cell298 PairReceipts.choice298 PairReceipts.check298 (none) (by decide)
private theorem weight3:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,25,some 28⟩,0,none,257363,none⟩:=PairRoute.weight 302619 leaf1 leaf2
theorem case71: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ weight3
private theorem leaf4:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,29,some 32⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell296 PairReceipts.choice296 PairReceipts.check296 (none) (by decide)
theorem case72: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,29,some 32⟩:=PairRoute.start _ leaf4
private theorem leaf5:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,33,some 40⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell295 PairReceipts.choice295 PairReceipts.check295 (none) (by decide)
theorem case73: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,33,some 40⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,41,some 48⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell294 PairReceipts.choice294 PairReceipts.check294 (none) (by decide)
theorem case74: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,41,some 48⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,49,some 64⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell293 PairReceipts.choice293 PairReceipts.check293 (none) (by decide)
theorem case75: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,49,some 64⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,2,65,some 96⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell292 PairReceipts.choice292 PairReceipts.check292 (none) (by decide)
theorem case76: NormalRoute.Done (0:Fin 18) ⟨28,32,9,2,65,some 96⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,4,some 8⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell467 PairReceipts.choice467 PairReceipts.check467 (none) (by decide)
theorem case77: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,4,some 8⟩:=PairRoute.start _ leaf9
private theorem leaf10:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,9,some 12⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell466 PairReceipts.choice466 PairReceipts.check466 (none) (by decide)
theorem case78: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf10
private theorem leaf11:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,13,some 14⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell465 PairReceipts.choice465 PairReceipts.check465 (none) (by decide)
theorem case79: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,13,some 14⟩:=PairRoute.start _ leaf11
end Research6969.HardFit1At070
end Z6969Source2603

-- Source: Research6969.PairReceipts016
section Z6969Source2604
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell320:PairCell.Row:=⟨28,32,9,3,22,some 22,11,some 11,386045,[MeasuredChoices.test882],[AxisChoices.test1832]⟩
def choice320:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check320:PairPrices.valid cell320 (0:Fin 18) choice320:=by decide +kernel
def cell321:PairCell.Row:=⟨28,32,9,3,22,some 22,12,some 12,386045,[MeasuredChoices.test882],[AxisChoices.test1833]⟩
def choice321:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check321:PairPrices.valid cell321 (0:Fin 18) choice321:=by decide +kernel
def cell322:PairCell.Row:=⟨28,32,9,3,22,some 22,13,some 13,386045,[MeasuredChoices.test882],[AxisChoices.test1834]⟩
def choice322:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check322:PairPrices.valid cell322 (0:Fin 18) choice322:=by decide +kernel
def cell323:PairCell.Row:=⟨28,32,9,3,22,some 22,14,some 14,386045,[MeasuredChoices.test882],[AxisChoices.test1835]⟩
def choice323:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check323:PairPrices.valid cell323 (0:Fin 18) choice323:=by decide +kernel
def cell324:PairCell.Row:=⟨28,32,9,3,22,some 22,15,some 15,386045,[MeasuredChoices.test882],[AxisChoices.test1836]⟩
def choice324:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check324:PairPrices.valid cell324 (0:Fin 18) choice324:=by decide +kernel
def cell325:PairCell.Row:=⟨28,32,9,3,22,some 22,16,some 16,386045,[MeasuredChoices.test882],[AxisChoices.test1837]⟩
def choice325:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check325:PairPrices.valid cell325 (0:Fin 18) choice325:=by decide +kernel
def cell326:PairCell.Row:=⟨28,32,9,3,22,some 22,17,some 17,386045,[MeasuredChoices.test882],[AxisChoices.test1838]⟩
def choice326:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check326:PairPrices.valid cell326 (0:Fin 18) choice326:=by decide +kernel
def cell327:PairCell.Row:=⟨28,32,9,3,22,some 22,18,some 18,386045,[MeasuredChoices.test882],[AxisChoices.test1839]⟩
def choice327:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check327:PairPrices.valid cell327 (0:Fin 18) choice327:=by decide +kernel
def cell328:PairCell.Row:=⟨28,32,9,3,22,some 22,19,some 19,386045,[MeasuredChoices.test882],[AxisChoices.test1840]⟩
def choice328:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check328:PairPrices.valid cell328 (0:Fin 18) choice328:=by decide +kernel
def cell329:PairCell.Row:=⟨28,32,9,3,22,some 22,20,some 20,386045,[MeasuredChoices.test882],[AxisChoices.test1841]⟩
def choice329:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check329:PairPrices.valid cell329 (0:Fin 18) choice329:=by decide +kernel
def cell330:PairCell.Row:=⟨28,32,9,3,22,some 22,21,some 21,386045,[MeasuredChoices.test882],[AxisChoices.test1842]⟩
def choice330:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check330:PairPrices.valid cell330 (0:Fin 18) choice330:=by decide +kernel
def cell331:PairCell.Row:=⟨28,32,9,3,22,some 22,22,some 22,386045,[MeasuredChoices.test882],[AxisChoices.test1843]⟩
def choice331:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check331:PairPrices.valid cell331 (0:Fin 18) choice331:=by decide +kernel
def cell332:PairCell.Row:=⟨28,32,9,3,21,some 21,0,some 0,386045,[MeasuredChoices.test869],[AxisChoices.test1821]⟩
def choice332:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check332:PairPrices.valid cell332 (0:Fin 18) choice332:=by decide +kernel
def cell333:PairCell.Row:=⟨28,32,9,3,21,some 21,1,some 1,386045,[MeasuredChoices.test869],[AxisChoices.test1822]⟩
def choice333:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check333:PairPrices.valid cell333 (0:Fin 18) choice333:=by decide +kernel
def cell334:PairCell.Row:=⟨28,32,9,3,21,some 21,2,some 2,386045,[MeasuredChoices.test869],[AxisChoices.test1823]⟩
def choice334:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check334:PairPrices.valid cell334 (0:Fin 18) choice334:=by decide +kernel
def cell335:PairCell.Row:=⟨28,32,9,3,21,some 21,3,some 3,386045,[MeasuredChoices.test869],[AxisChoices.test1824]⟩
def choice335:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check335:PairPrices.valid cell335 (0:Fin 18) choice335:=by decide +kernel
def cell336:PairCell.Row:=⟨28,32,9,3,21,some 21,4,some 4,386045,[MeasuredChoices.test869],[AxisChoices.test1825]⟩
def choice336:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check336:PairPrices.valid cell336 (0:Fin 18) choice336:=by decide +kernel
def cell337:PairCell.Row:=⟨28,32,9,3,21,some 21,5,some 5,386045,[MeasuredChoices.test869],[AxisChoices.test1826]⟩
def choice337:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check337:PairPrices.valid cell337 (0:Fin 18) choice337:=by decide +kernel
def cell338:PairCell.Row:=⟨28,32,9,3,21,some 21,6,some 6,386045,[MeasuredChoices.test869],[AxisChoices.test1827]⟩
def choice338:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check338:PairPrices.valid cell338 (0:Fin 18) choice338:=by decide +kernel
def cell339:PairCell.Row:=⟨28,32,9,3,21,some 21,7,some 7,386045,[MeasuredChoices.test869],[AxisChoices.test1828]⟩
def choice339:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check339:PairPrices.valid cell339 (0:Fin 18) choice339:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2604

-- Source: Research6969.PairReceipts017
section Z6969Source2605
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell340:PairCell.Row:=⟨28,32,9,3,21,some 21,8,some 8,386045,[MeasuredChoices.test869],[AxisChoices.test1829]⟩
def choice340:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check340:PairPrices.valid cell340 (0:Fin 18) choice340:=by decide +kernel
def cell341:PairCell.Row:=⟨28,32,9,3,21,some 21,9,some 9,386045,[MeasuredChoices.test869],[AxisChoices.test1830]⟩
def choice341:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check341:PairPrices.valid cell341 (0:Fin 18) choice341:=by decide +kernel
def cell342:PairCell.Row:=⟨28,32,9,3,21,some 21,10,some 10,386045,[MeasuredChoices.test869],[AxisChoices.test1831]⟩
def choice342:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check342:PairPrices.valid cell342 (0:Fin 18) choice342:=by decide +kernel
def cell343:PairCell.Row:=⟨28,32,9,3,21,some 21,11,some 11,386045,[MeasuredChoices.test869],[AxisChoices.test1832]⟩
def choice343:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check343:PairPrices.valid cell343 (0:Fin 18) choice343:=by decide +kernel
def cell344:PairCell.Row:=⟨28,32,9,3,21,some 21,12,some 12,386045,[MeasuredChoices.test869],[AxisChoices.test1833]⟩
def choice344:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check344:PairPrices.valid cell344 (0:Fin 18) choice344:=by decide +kernel
def cell345:PairCell.Row:=⟨28,32,9,3,21,some 21,13,some 13,386045,[MeasuredChoices.test869],[AxisChoices.test1834]⟩
def choice345:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check345:PairPrices.valid cell345 (0:Fin 18) choice345:=by decide +kernel
def cell346:PairCell.Row:=⟨28,32,9,3,21,some 21,14,some 14,386045,[MeasuredChoices.test869],[AxisChoices.test1835]⟩
def choice346:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check346:PairPrices.valid cell346 (0:Fin 18) choice346:=by decide +kernel
def cell347:PairCell.Row:=⟨28,32,9,3,21,some 21,15,some 15,386045,[MeasuredChoices.test869],[AxisChoices.test1836]⟩
def choice347:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check347:PairPrices.valid cell347 (0:Fin 18) choice347:=by decide +kernel
def cell348:PairCell.Row:=⟨28,32,9,3,21,some 21,16,some 16,386045,[MeasuredChoices.test869],[AxisChoices.test1837]⟩
def choice348:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check348:PairPrices.valid cell348 (0:Fin 18) choice348:=by decide +kernel
def cell349:PairCell.Row:=⟨28,32,9,3,21,some 21,17,some 17,386045,[MeasuredChoices.test869],[AxisChoices.test1838]⟩
def choice349:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check349:PairPrices.valid cell349 (0:Fin 18) choice349:=by decide +kernel
def cell350:PairCell.Row:=⟨28,32,9,3,21,some 21,18,some 18,386045,[MeasuredChoices.test869],[AxisChoices.test1839]⟩
def choice350:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check350:PairPrices.valid cell350 (0:Fin 18) choice350:=by decide +kernel
def cell351:PairCell.Row:=⟨28,32,9,3,21,some 21,19,some 19,386045,[MeasuredChoices.test869],[AxisChoices.test1840]⟩
def choice351:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check351:PairPrices.valid cell351 (0:Fin 18) choice351:=by decide +kernel
def cell352:PairCell.Row:=⟨28,32,9,3,21,some 21,20,some 20,386045,[MeasuredChoices.test869],[AxisChoices.test1841]⟩
def choice352:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check352:PairPrices.valid cell352 (0:Fin 18) choice352:=by decide +kernel
def cell353:PairCell.Row:=⟨28,32,9,3,21,some 21,21,some 21,386045,[MeasuredChoices.test869],[AxisChoices.test1842]⟩
def choice353:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check353:PairPrices.valid cell353 (0:Fin 18) choice353:=by decide +kernel
def cell354:PairCell.Row:=⟨28,32,9,3,20,some 20,0,some 0,386045,[MeasuredChoices.test856],[AxisChoices.test1821]⟩
def choice354:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check354:PairPrices.valid cell354 (0:Fin 18) choice354:=by decide +kernel
def cell355:PairCell.Row:=⟨28,32,9,3,20,some 20,1,some 1,386045,[MeasuredChoices.test856],[AxisChoices.test1822]⟩
def choice355:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check355:PairPrices.valid cell355 (0:Fin 18) choice355:=by decide +kernel
def cell356:PairCell.Row:=⟨28,32,9,3,20,some 20,2,some 2,386045,[MeasuredChoices.test856],[AxisChoices.test1823]⟩
def choice356:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check356:PairPrices.valid cell356 (0:Fin 18) choice356:=by decide +kernel
def cell357:PairCell.Row:=⟨28,32,9,3,20,some 20,3,some 3,386045,[MeasuredChoices.test856],[AxisChoices.test1824]⟩
def choice357:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check357:PairPrices.valid cell357 (0:Fin 18) choice357:=by decide +kernel
def cell358:PairCell.Row:=⟨28,32,9,3,20,some 20,4,some 4,386045,[MeasuredChoices.test856],[AxisChoices.test1825]⟩
def choice358:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check358:PairPrices.valid cell358 (0:Fin 18) choice358:=by decide +kernel
def cell359:PairCell.Row:=⟨28,32,9,3,20,some 20,5,some 5,386045,[MeasuredChoices.test856],[AxisChoices.test1826]⟩
def choice359:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check359:PairPrices.valid cell359 (0:Fin 18) choice359:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2605

-- Source: Research6969.PairReceipts018
section Z6969Source2606
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell360:PairCell.Row:=⟨28,32,9,3,20,some 20,6,some 6,386045,[MeasuredChoices.test856],[AxisChoices.test1827]⟩
def choice360:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check360:PairPrices.valid cell360 (0:Fin 18) choice360:=by decide +kernel
def cell361:PairCell.Row:=⟨28,32,9,3,20,some 20,7,some 7,386045,[MeasuredChoices.test856],[AxisChoices.test1828]⟩
def choice361:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check361:PairPrices.valid cell361 (0:Fin 18) choice361:=by decide +kernel
def cell362:PairCell.Row:=⟨28,32,9,3,20,some 20,8,some 8,386045,[MeasuredChoices.test856],[AxisChoices.test1829]⟩
def choice362:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check362:PairPrices.valid cell362 (0:Fin 18) choice362:=by decide +kernel
def cell363:PairCell.Row:=⟨28,32,9,3,20,some 20,9,some 9,386045,[MeasuredChoices.test856],[AxisChoices.test1830]⟩
def choice363:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check363:PairPrices.valid cell363 (0:Fin 18) choice363:=by decide +kernel
def cell364:PairCell.Row:=⟨28,32,9,3,20,some 20,10,some 10,386045,[MeasuredChoices.test856],[AxisChoices.test1831]⟩
def choice364:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check364:PairPrices.valid cell364 (0:Fin 18) choice364:=by decide +kernel
def cell365:PairCell.Row:=⟨28,32,9,3,20,some 20,11,some 11,386045,[MeasuredChoices.test856],[AxisChoices.test1832]⟩
def choice365:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check365:PairPrices.valid cell365 (0:Fin 18) choice365:=by decide +kernel
def cell366:PairCell.Row:=⟨28,32,9,3,20,some 20,12,some 12,386045,[MeasuredChoices.test856],[AxisChoices.test1833]⟩
def choice366:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check366:PairPrices.valid cell366 (0:Fin 18) choice366:=by decide +kernel
def cell367:PairCell.Row:=⟨28,32,9,3,20,some 20,13,some 13,386045,[MeasuredChoices.test856],[AxisChoices.test1834]⟩
def choice367:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check367:PairPrices.valid cell367 (0:Fin 18) choice367:=by decide +kernel
def cell368:PairCell.Row:=⟨28,32,9,3,20,some 20,14,some 14,386045,[MeasuredChoices.test856],[AxisChoices.test1835]⟩
def choice368:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check368:PairPrices.valid cell368 (0:Fin 18) choice368:=by decide +kernel
def cell369:PairCell.Row:=⟨28,32,9,3,20,some 20,15,some 15,386045,[MeasuredChoices.test856],[AxisChoices.test1836]⟩
def choice369:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check369:PairPrices.valid cell369 (0:Fin 18) choice369:=by decide +kernel
def cell370:PairCell.Row:=⟨28,32,9,3,20,some 20,16,some 16,386045,[MeasuredChoices.test856],[AxisChoices.test1837]⟩
def choice370:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check370:PairPrices.valid cell370 (0:Fin 18) choice370:=by decide +kernel
def cell371:PairCell.Row:=⟨28,32,9,3,20,some 20,17,some 17,386045,[MeasuredChoices.test856],[AxisChoices.test1838]⟩
def choice371:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check371:PairPrices.valid cell371 (0:Fin 18) choice371:=by decide +kernel
def cell372:PairCell.Row:=⟨28,32,9,3,20,some 20,18,some 18,386045,[MeasuredChoices.test856],[AxisChoices.test1839]⟩
def choice372:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check372:PairPrices.valid cell372 (0:Fin 18) choice372:=by decide +kernel
def cell373:PairCell.Row:=⟨28,32,9,3,20,some 20,19,some 19,386045,[MeasuredChoices.test856],[AxisChoices.test1840]⟩
def choice373:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check373:PairPrices.valid cell373 (0:Fin 18) choice373:=by decide +kernel
def cell374:PairCell.Row:=⟨28,32,9,3,20,some 20,20,some 20,386045,[MeasuredChoices.test856],[AxisChoices.test1841]⟩
def choice374:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check374:PairPrices.valid cell374 (0:Fin 18) choice374:=by decide +kernel
def cell375:PairCell.Row:=⟨28,32,9,3,19,some 19,0,some 0,386045,[MeasuredChoices.test843],[AxisChoices.test1821]⟩
def choice375:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check375:PairPrices.valid cell375 (0:Fin 18) choice375:=by decide +kernel
def cell376:PairCell.Row:=⟨28,32,9,3,19,some 19,1,some 1,386045,[MeasuredChoices.test843],[AxisChoices.test1822]⟩
def choice376:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check376:PairPrices.valid cell376 (0:Fin 18) choice376:=by decide +kernel
def cell377:PairCell.Row:=⟨28,32,9,3,19,some 19,2,some 2,386045,[MeasuredChoices.test843],[AxisChoices.test1823]⟩
def choice377:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check377:PairPrices.valid cell377 (0:Fin 18) choice377:=by decide +kernel
def cell378:PairCell.Row:=⟨28,32,9,3,19,some 19,3,some 3,386045,[MeasuredChoices.test843],[AxisChoices.test1824]⟩
def choice378:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check378:PairPrices.valid cell378 (0:Fin 18) choice378:=by decide +kernel
def cell379:PairCell.Row:=⟨28,32,9,3,19,some 19,4,some 4,386045,[MeasuredChoices.test843],[AxisChoices.test1825]⟩
def choice379:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check379:PairPrices.valid cell379 (0:Fin 18) choice379:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2606

-- Source: Research6969.PairReceipts019
section Z6969Source2607
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell380:PairCell.Row:=⟨28,32,9,3,19,some 19,5,some 5,386045,[MeasuredChoices.test843],[AxisChoices.test1826]⟩
def choice380:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check380:PairPrices.valid cell380 (0:Fin 18) choice380:=by decide +kernel
def cell381:PairCell.Row:=⟨28,32,9,3,19,some 19,6,some 6,386045,[MeasuredChoices.test843],[AxisChoices.test1827]⟩
def choice381:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check381:PairPrices.valid cell381 (0:Fin 18) choice381:=by decide +kernel
def cell382:PairCell.Row:=⟨28,32,9,3,19,some 19,7,some 7,386045,[MeasuredChoices.test843],[AxisChoices.test1828]⟩
def choice382:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check382:PairPrices.valid cell382 (0:Fin 18) choice382:=by decide +kernel
def cell383:PairCell.Row:=⟨28,32,9,3,19,some 19,8,some 8,386045,[MeasuredChoices.test843],[AxisChoices.test1829]⟩
def choice383:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check383:PairPrices.valid cell383 (0:Fin 18) choice383:=by decide +kernel
def cell384:PairCell.Row:=⟨28,32,9,3,19,some 19,9,some 9,386045,[MeasuredChoices.test843],[AxisChoices.test1830]⟩
def choice384:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check384:PairPrices.valid cell384 (0:Fin 18) choice384:=by decide +kernel
def cell385:PairCell.Row:=⟨28,32,9,3,19,some 19,10,some 10,386045,[MeasuredChoices.test843],[AxisChoices.test1831]⟩
def choice385:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check385:PairPrices.valid cell385 (0:Fin 18) choice385:=by decide +kernel
def cell386:PairCell.Row:=⟨28,32,9,3,19,some 19,11,some 11,386045,[MeasuredChoices.test843],[AxisChoices.test1832]⟩
def choice386:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check386:PairPrices.valid cell386 (0:Fin 18) choice386:=by decide +kernel
def cell387:PairCell.Row:=⟨28,32,9,3,19,some 19,12,some 12,386045,[MeasuredChoices.test843],[AxisChoices.test1833]⟩
def choice387:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check387:PairPrices.valid cell387 (0:Fin 18) choice387:=by decide +kernel
def cell388:PairCell.Row:=⟨28,32,9,3,19,some 19,13,some 13,386045,[MeasuredChoices.test843],[AxisChoices.test1834]⟩
def choice388:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check388:PairPrices.valid cell388 (0:Fin 18) choice388:=by decide +kernel
def cell389:PairCell.Row:=⟨28,32,9,3,19,some 19,14,some 14,386045,[MeasuredChoices.test843],[AxisChoices.test1835]⟩
def choice389:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check389:PairPrices.valid cell389 (0:Fin 18) choice389:=by decide +kernel
def cell390:PairCell.Row:=⟨28,32,9,3,19,some 19,15,some 15,386045,[MeasuredChoices.test843],[AxisChoices.test1836]⟩
def choice390:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check390:PairPrices.valid cell390 (0:Fin 18) choice390:=by decide +kernel
def cell391:PairCell.Row:=⟨28,32,9,3,19,some 19,16,some 16,386045,[MeasuredChoices.test843],[AxisChoices.test1837]⟩
def choice391:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check391:PairPrices.valid cell391 (0:Fin 18) choice391:=by decide +kernel
def cell392:PairCell.Row:=⟨28,32,9,3,19,some 19,17,some 17,386045,[MeasuredChoices.test843],[AxisChoices.test1838]⟩
def choice392:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check392:PairPrices.valid cell392 (0:Fin 18) choice392:=by decide +kernel
def cell393:PairCell.Row:=⟨28,32,9,3,19,some 19,18,some 18,386045,[MeasuredChoices.test843],[AxisChoices.test1839]⟩
def choice393:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check393:PairPrices.valid cell393 (0:Fin 18) choice393:=by decide +kernel
def cell394:PairCell.Row:=⟨28,32,9,3,19,some 19,19,some 19,386045,[MeasuredChoices.test843],[AxisChoices.test1840]⟩
def choice394:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check394:PairPrices.valid cell394 (0:Fin 18) choice394:=by decide +kernel
def cell395:PairCell.Row:=⟨28,32,9,3,18,some 18,0,some 0,386045,[MeasuredChoices.test831],[AxisChoices.test1821]⟩
def choice395:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check395:PairPrices.valid cell395 (0:Fin 18) choice395:=by decide +kernel
def cell396:PairCell.Row:=⟨28,32,9,3,18,some 18,1,some 1,386045,[MeasuredChoices.test831],[AxisChoices.test1822]⟩
def choice396:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check396:PairPrices.valid cell396 (0:Fin 18) choice396:=by decide +kernel
def cell397:PairCell.Row:=⟨28,32,9,3,18,some 18,2,some 2,386045,[MeasuredChoices.test831],[AxisChoices.test1823]⟩
def choice397:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check397:PairPrices.valid cell397 (0:Fin 18) choice397:=by decide +kernel
def cell398:PairCell.Row:=⟨28,32,9,3,18,some 18,3,some 3,386045,[MeasuredChoices.test831],[AxisChoices.test1824]⟩
def choice398:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check398:PairPrices.valid cell398 (0:Fin 18) choice398:=by decide +kernel
def cell399:PairCell.Row:=⟨28,32,9,3,18,some 18,4,some 4,386045,[MeasuredChoices.test831],[AxisChoices.test1825]⟩
def choice399:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check399:PairPrices.valid cell399 (0:Fin 18) choice399:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2607

-- Source: Research6969.PairReceipts020
section Z6969Source2608
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell400:PairCell.Row:=⟨28,32,9,3,18,some 18,5,some 5,386045,[MeasuredChoices.test831],[AxisChoices.test1826]⟩
def choice400:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check400:PairPrices.valid cell400 (0:Fin 18) choice400:=by decide +kernel
def cell401:PairCell.Row:=⟨28,32,9,3,18,some 18,6,some 6,386045,[MeasuredChoices.test831],[AxisChoices.test1827]⟩
def choice401:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check401:PairPrices.valid cell401 (0:Fin 18) choice401:=by decide +kernel
def cell402:PairCell.Row:=⟨28,32,9,3,18,some 18,7,some 7,386045,[MeasuredChoices.test831],[AxisChoices.test1828]⟩
def choice402:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check402:PairPrices.valid cell402 (0:Fin 18) choice402:=by decide +kernel
def cell403:PairCell.Row:=⟨28,32,9,3,18,some 18,8,some 8,386045,[MeasuredChoices.test831],[AxisChoices.test1829]⟩
def choice403:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check403:PairPrices.valid cell403 (0:Fin 18) choice403:=by decide +kernel
def cell404:PairCell.Row:=⟨28,32,9,3,18,some 18,9,some 9,386045,[MeasuredChoices.test831],[AxisChoices.test1830]⟩
def choice404:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check404:PairPrices.valid cell404 (0:Fin 18) choice404:=by decide +kernel
def cell405:PairCell.Row:=⟨28,32,9,3,18,some 18,10,some 10,386045,[MeasuredChoices.test831],[AxisChoices.test1831]⟩
def choice405:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check405:PairPrices.valid cell405 (0:Fin 18) choice405:=by decide +kernel
def cell406:PairCell.Row:=⟨28,32,9,3,18,some 18,11,some 11,386045,[MeasuredChoices.test831],[AxisChoices.test1832]⟩
def choice406:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check406:PairPrices.valid cell406 (0:Fin 18) choice406:=by decide +kernel
def cell407:PairCell.Row:=⟨28,32,9,3,18,some 18,12,some 12,386045,[MeasuredChoices.test831],[AxisChoices.test1833]⟩
def choice407:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check407:PairPrices.valid cell407 (0:Fin 18) choice407:=by decide +kernel
def cell408:PairCell.Row:=⟨28,32,9,3,18,some 18,13,some 13,386045,[MeasuredChoices.test831],[AxisChoices.test1834]⟩
def choice408:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check408:PairPrices.valid cell408 (0:Fin 18) choice408:=by decide +kernel
def cell409:PairCell.Row:=⟨28,32,9,3,18,some 18,14,some 14,386045,[MeasuredChoices.test831],[AxisChoices.test1835]⟩
def choice409:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check409:PairPrices.valid cell409 (0:Fin 18) choice409:=by decide +kernel
def cell410:PairCell.Row:=⟨28,32,9,3,18,some 18,15,some 15,386045,[MeasuredChoices.test831],[AxisChoices.test1836]⟩
def choice410:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check410:PairPrices.valid cell410 (0:Fin 18) choice410:=by decide +kernel
def cell411:PairCell.Row:=⟨28,32,9,3,18,some 18,16,some 16,386045,[MeasuredChoices.test831],[AxisChoices.test1837]⟩
def choice411:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check411:PairPrices.valid cell411 (0:Fin 18) choice411:=by decide +kernel
def cell412:PairCell.Row:=⟨28,32,9,3,18,some 18,17,some 17,386045,[MeasuredChoices.test831],[AxisChoices.test1838]⟩
def choice412:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check412:PairPrices.valid cell412 (0:Fin 18) choice412:=by decide +kernel
def cell413:PairCell.Row:=⟨28,32,9,3,18,some 18,18,some 18,386045,[MeasuredChoices.test831],[AxisChoices.test1839]⟩
def choice413:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check413:PairPrices.valid cell413 (0:Fin 18) choice413:=by decide +kernel
def cell414:PairCell.Row:=⟨28,32,9,3,17,some 17,0,some 0,386045,[MeasuredChoices.test821],[AxisChoices.test1821]⟩
def choice414:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check414:PairPrices.valid cell414 (0:Fin 18) choice414:=by decide +kernel
def cell415:PairCell.Row:=⟨28,32,9,3,17,some 17,1,some 1,386045,[MeasuredChoices.test821],[AxisChoices.test1822]⟩
def choice415:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check415:PairPrices.valid cell415 (0:Fin 18) choice415:=by decide +kernel
def cell416:PairCell.Row:=⟨28,32,9,3,17,some 17,2,some 2,386045,[MeasuredChoices.test821],[AxisChoices.test1823]⟩
def choice416:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check416:PairPrices.valid cell416 (0:Fin 18) choice416:=by decide +kernel
def cell417:PairCell.Row:=⟨28,32,9,3,17,some 17,3,some 3,386045,[MeasuredChoices.test821],[AxisChoices.test1824]⟩
def choice417:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check417:PairPrices.valid cell417 (0:Fin 18) choice417:=by decide +kernel
def cell418:PairCell.Row:=⟨28,32,9,3,17,some 17,4,some 4,386045,[MeasuredChoices.test821],[AxisChoices.test1825]⟩
def choice418:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check418:PairPrices.valid cell418 (0:Fin 18) choice418:=by decide +kernel
def cell419:PairCell.Row:=⟨28,32,9,3,17,some 17,5,some 5,386045,[MeasuredChoices.test821],[AxisChoices.test1826]⟩
def choice419:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check419:PairPrices.valid cell419 (0:Fin 18) choice419:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2608

-- Source: Research6969.PairReceipts021
section Z6969Source2609
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell420:PairCell.Row:=⟨28,32,9,3,17,some 17,6,some 6,386045,[MeasuredChoices.test821],[AxisChoices.test1827]⟩
def choice420:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check420:PairPrices.valid cell420 (0:Fin 18) choice420:=by decide +kernel
def cell421:PairCell.Row:=⟨28,32,9,3,17,some 17,7,some 7,386045,[MeasuredChoices.test821],[AxisChoices.test1828]⟩
def choice421:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check421:PairPrices.valid cell421 (0:Fin 18) choice421:=by decide +kernel
def cell422:PairCell.Row:=⟨28,32,9,3,17,some 17,8,some 8,386045,[MeasuredChoices.test821],[AxisChoices.test1829]⟩
def choice422:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check422:PairPrices.valid cell422 (0:Fin 18) choice422:=by decide +kernel
def cell423:PairCell.Row:=⟨28,32,9,3,17,some 17,9,some 9,386045,[MeasuredChoices.test821],[AxisChoices.test1830]⟩
def choice423:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check423:PairPrices.valid cell423 (0:Fin 18) choice423:=by decide +kernel
def cell424:PairCell.Row:=⟨28,32,9,3,17,some 17,10,some 10,386045,[MeasuredChoices.test821],[AxisChoices.test1831]⟩
def choice424:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check424:PairPrices.valid cell424 (0:Fin 18) choice424:=by decide +kernel
def cell425:PairCell.Row:=⟨28,32,9,3,17,some 17,11,some 11,386045,[MeasuredChoices.test821],[AxisChoices.test1832]⟩
def choice425:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check425:PairPrices.valid cell425 (0:Fin 18) choice425:=by decide +kernel
def cell426:PairCell.Row:=⟨28,32,9,3,17,some 17,12,some 12,386045,[MeasuredChoices.test821],[AxisChoices.test1833]⟩
def choice426:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check426:PairPrices.valid cell426 (0:Fin 18) choice426:=by decide +kernel
def cell427:PairCell.Row:=⟨28,32,9,3,17,some 17,13,some 13,386045,[MeasuredChoices.test821],[AxisChoices.test1834]⟩
def choice427:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check427:PairPrices.valid cell427 (0:Fin 18) choice427:=by decide +kernel
def cell428:PairCell.Row:=⟨28,32,9,3,17,some 17,14,some 14,386045,[MeasuredChoices.test821],[AxisChoices.test1835]⟩
def choice428:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check428:PairPrices.valid cell428 (0:Fin 18) choice428:=by decide +kernel
def cell429:PairCell.Row:=⟨28,32,9,3,17,some 17,15,some 15,386045,[MeasuredChoices.test821],[AxisChoices.test1836]⟩
def choice429:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check429:PairPrices.valid cell429 (0:Fin 18) choice429:=by decide +kernel
def cell430:PairCell.Row:=⟨28,32,9,3,17,some 17,16,some 16,386045,[MeasuredChoices.test821],[AxisChoices.test1837]⟩
def choice430:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check430:PairPrices.valid cell430 (0:Fin 18) choice430:=by decide +kernel
def cell431:PairCell.Row:=⟨28,32,9,3,17,some 17,17,some 17,386045,[MeasuredChoices.test821],[AxisChoices.test1838]⟩
def choice431:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check431:PairPrices.valid cell431 (0:Fin 18) choice431:=by decide +kernel
def cell432:PairCell.Row:=⟨28,32,9,3,16,some 16,0,some 0,386045,[MeasuredChoices.test807],[AxisChoices.test1821]⟩
def choice432:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check432:PairPrices.valid cell432 (0:Fin 18) choice432:=by decide +kernel
def cell433:PairCell.Row:=⟨28,32,9,3,16,some 16,1,some 1,386045,[MeasuredChoices.test807],[AxisChoices.test1822]⟩
def choice433:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check433:PairPrices.valid cell433 (0:Fin 18) choice433:=by decide +kernel
def cell434:PairCell.Row:=⟨28,32,9,3,16,some 16,2,some 2,386045,[MeasuredChoices.test807],[AxisChoices.test1823]⟩
def choice434:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check434:PairPrices.valid cell434 (0:Fin 18) choice434:=by decide +kernel
def cell435:PairCell.Row:=⟨28,32,9,3,16,some 16,3,some 3,386045,[MeasuredChoices.test807],[AxisChoices.test1824]⟩
def choice435:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check435:PairPrices.valid cell435 (0:Fin 18) choice435:=by decide +kernel
def cell436:PairCell.Row:=⟨28,32,9,3,16,some 16,4,some 4,386045,[MeasuredChoices.test807],[AxisChoices.test1825]⟩
def choice436:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check436:PairPrices.valid cell436 (0:Fin 18) choice436:=by decide +kernel
def cell437:PairCell.Row:=⟨28,32,9,3,16,some 16,5,some 5,386045,[MeasuredChoices.test807],[AxisChoices.test1826]⟩
def choice437:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check437:PairPrices.valid cell437 (0:Fin 18) choice437:=by decide +kernel
def cell438:PairCell.Row:=⟨28,32,9,3,16,some 16,6,some 6,386045,[MeasuredChoices.test807],[AxisChoices.test1827]⟩
def choice438:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check438:PairPrices.valid cell438 (0:Fin 18) choice438:=by decide +kernel
def cell439:PairCell.Row:=⟨28,32,9,3,16,some 16,7,some 7,386045,[MeasuredChoices.test807],[AxisChoices.test1828]⟩
def choice439:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check439:PairPrices.valid cell439 (0:Fin 18) choice439:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2609

-- Source: Research6969.PairReceipts022
section Z6969Source2610
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell440:PairCell.Row:=⟨28,32,9,3,16,some 16,8,some 8,386045,[MeasuredChoices.test807],[AxisChoices.test1829]⟩
def choice440:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check440:PairPrices.valid cell440 (0:Fin 18) choice440:=by decide +kernel
def cell441:PairCell.Row:=⟨28,32,9,3,16,some 16,9,some 9,386045,[MeasuredChoices.test807],[AxisChoices.test1830]⟩
def choice441:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check441:PairPrices.valid cell441 (0:Fin 18) choice441:=by decide +kernel
def cell442:PairCell.Row:=⟨28,32,9,3,16,some 16,10,some 10,386045,[MeasuredChoices.test807],[AxisChoices.test1831]⟩
def choice442:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check442:PairPrices.valid cell442 (0:Fin 18) choice442:=by decide +kernel
def cell443:PairCell.Row:=⟨28,32,9,3,16,some 16,11,some 11,386045,[MeasuredChoices.test807],[AxisChoices.test1832]⟩
def choice443:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check443:PairPrices.valid cell443 (0:Fin 18) choice443:=by decide +kernel
def cell444:PairCell.Row:=⟨28,32,9,3,16,some 16,12,some 12,386045,[MeasuredChoices.test807],[AxisChoices.test1833]⟩
def choice444:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check444:PairPrices.valid cell444 (0:Fin 18) choice444:=by decide +kernel
def cell445:PairCell.Row:=⟨28,32,9,3,16,some 16,13,some 13,386045,[MeasuredChoices.test807],[AxisChoices.test1834]⟩
def choice445:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check445:PairPrices.valid cell445 (0:Fin 18) choice445:=by decide +kernel
def cell446:PairCell.Row:=⟨28,32,9,3,16,some 16,14,some 14,386045,[MeasuredChoices.test807],[AxisChoices.test1835]⟩
def choice446:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check446:PairPrices.valid cell446 (0:Fin 18) choice446:=by decide +kernel
def cell447:PairCell.Row:=⟨28,32,9,3,16,some 16,15,some 15,386045,[MeasuredChoices.test807],[AxisChoices.test1836]⟩
def choice447:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check447:PairPrices.valid cell447 (0:Fin 18) choice447:=by decide +kernel
def cell448:PairCell.Row:=⟨28,32,9,3,16,some 16,16,some 16,386045,[MeasuredChoices.test807],[AxisChoices.test1837]⟩
def choice448:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check448:PairPrices.valid cell448 (0:Fin 18) choice448:=by decide +kernel
def cell449:PairCell.Row:=⟨28,32,9,3,15,some 15,0,some 0,386045,[MeasuredChoices.test797],[AxisChoices.test1821]⟩
def choice449:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check449:PairPrices.valid cell449 (0:Fin 18) choice449:=by decide +kernel
def cell450:PairCell.Row:=⟨28,32,9,3,15,some 15,1,some 1,386045,[MeasuredChoices.test797],[AxisChoices.test1822]⟩
def choice450:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check450:PairPrices.valid cell450 (0:Fin 18) choice450:=by decide +kernel
def cell451:PairCell.Row:=⟨28,32,9,3,15,some 15,2,some 2,386045,[MeasuredChoices.test797],[AxisChoices.test1823]⟩
def choice451:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check451:PairPrices.valid cell451 (0:Fin 18) choice451:=by decide +kernel
def cell452:PairCell.Row:=⟨28,32,9,3,15,some 15,3,some 3,386045,[MeasuredChoices.test797],[AxisChoices.test1824]⟩
def choice452:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check452:PairPrices.valid cell452 (0:Fin 18) choice452:=by decide +kernel
def cell453:PairCell.Row:=⟨28,32,9,3,15,some 15,4,some 4,386045,[MeasuredChoices.test797],[AxisChoices.test1825]⟩
def choice453:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check453:PairPrices.valid cell453 (0:Fin 18) choice453:=by decide +kernel
def cell454:PairCell.Row:=⟨28,32,9,3,15,some 15,5,some 5,386045,[MeasuredChoices.test797],[AxisChoices.test1826]⟩
def choice454:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check454:PairPrices.valid cell454 (0:Fin 18) choice454:=by decide +kernel
def cell455:PairCell.Row:=⟨28,32,9,3,15,some 15,6,some 6,386045,[MeasuredChoices.test797],[AxisChoices.test1827]⟩
def choice455:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check455:PairPrices.valid cell455 (0:Fin 18) choice455:=by decide +kernel
def cell456:PairCell.Row:=⟨28,32,9,3,15,some 15,7,some 7,386045,[MeasuredChoices.test797],[AxisChoices.test1828]⟩
def choice456:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check456:PairPrices.valid cell456 (0:Fin 18) choice456:=by decide +kernel
def cell457:PairCell.Row:=⟨28,32,9,3,15,some 15,8,some 8,386045,[MeasuredChoices.test797],[AxisChoices.test1829]⟩
def choice457:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check457:PairPrices.valid cell457 (0:Fin 18) choice457:=by decide +kernel
def cell458:PairCell.Row:=⟨28,32,9,3,15,some 15,9,some 9,386045,[MeasuredChoices.test797],[AxisChoices.test1830]⟩
def choice458:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check458:PairPrices.valid cell458 (0:Fin 18) choice458:=by decide +kernel
def cell459:PairCell.Row:=⟨28,32,9,3,15,some 15,10,some 10,386045,[MeasuredChoices.test797],[AxisChoices.test1831]⟩
def choice459:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check459:PairPrices.valid cell459 (0:Fin 18) choice459:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2610

-- Source: Research6969.HardFit1At080
section Z6969Source2611
set_option autoImplicit true
namespace Research6969.HardFit1At080
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell449 PairReceipts.choice449 PairReceipts.check449 (none) (by decide)
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell450 PairReceipts.choice450 PairReceipts.check450 (none) (by decide)
private theorem leaf2:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell451 PairReceipts.choice451 PairReceipts.check451 (none) (by decide)
private theorem leaf3:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell452 PairReceipts.choice452 PairReceipts.check452 (none) (by decide)
private theorem leaf4:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell453 PairReceipts.choice453 PairReceipts.check453 (none) (by decide)
private theorem leaf5:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell454 PairReceipts.choice454 PairReceipts.check454 (none) (by decide)
private theorem leaf6:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell455 PairReceipts.choice455 PairReceipts.check455 (none) (by decide)
private theorem leaf7:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell456 PairReceipts.choice456 PairReceipts.check456 (none) (by decide)
private theorem leaf8:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell457 PairReceipts.choice457 PairReceipts.check457 (none) (by decide)
private theorem leaf9:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell458 PairReceipts.choice458 PairReceipts.check458 (none) (by decide)
private theorem leaf10:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell459 PairReceipts.choice459 PairReceipts.check459 (none) (by decide)
private theorem leaf11:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell460 PairReceipts.choice460 PairReceipts.check460 (none) (by decide)
private theorem leaf12:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell461 PairReceipts.choice461 PairReceipts.check461 (none) (by decide)
private theorem leaf13:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell462 PairReceipts.choice462 PairReceipts.check462 (none) (by decide)
private theorem leaf14:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell463 PairReceipts.choice463 PairReceipts.check463 (none) (by decide)
private theorem leaf15:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell464 PairReceipts.choice464 PairReceipts.check464 (none) (by decide)
private theorem axis16:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,14,some 15,386045,none⟩:=PairRoute.axis 14 leaf14 leaf15
private theorem axis17:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,13,some 15,386045,none⟩:=PairRoute.axis 13 leaf13 axis16
private theorem axis18:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,12,some 15,386045,none⟩:=PairRoute.axis 12 leaf12 axis17
private theorem axis19:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,11,some 15,386045,none⟩:=PairRoute.axis 11 leaf11 axis18
private theorem axis20:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,10,some 15,386045,none⟩:=PairRoute.axis 10 leaf10 axis19
private theorem axis21:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,9,some 15,386045,none⟩:=PairRoute.axis 9 leaf9 axis20
private theorem axis22:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,8,some 15,386045,none⟩:=PairRoute.axis 8 leaf8 axis21
private theorem axis23:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,7,some 15,386045,none⟩:=PairRoute.axis 7 leaf7 axis22
private theorem axis24:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,6,some 15,386045,none⟩:=PairRoute.axis 6 leaf6 axis23
private theorem axis25:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,5,some 15,386045,none⟩:=PairRoute.axis 5 leaf5 axis24
private theorem axis26:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,4,some 15,386045,none⟩:=PairRoute.axis 4 leaf4 axis25
private theorem axis27:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,3,some 15,386045,none⟩:=PairRoute.axis 3 leaf3 axis26
private theorem axis28:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,2,some 15,386045,none⟩:=PairRoute.axis 2 leaf2 axis27
private theorem axis29:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,1,some 15,386045,none⟩:=PairRoute.axis 1 leaf1 axis28
private theorem axis30:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,0,some 15,386045,none⟩:=PairRoute.axis 0 leaf0 axis29
private theorem allAxes31:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,15,some 15⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis30
theorem case80: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,15,some 15⟩:=PairRoute.start _ allAxes31
private theorem leaf32:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell432 PairReceipts.choice432 PairReceipts.check432 (none) (by decide)
private theorem leaf33:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell433 PairReceipts.choice433 PairReceipts.check433 (none) (by decide)
private theorem leaf34:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell434 PairReceipts.choice434 PairReceipts.check434 (none) (by decide)
private theorem leaf35:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell435 PairReceipts.choice435 PairReceipts.check435 (none) (by decide)
private theorem leaf36:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell436 PairReceipts.choice436 PairReceipts.check436 (none) (by decide)
private theorem leaf37:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell437 PairReceipts.choice437 PairReceipts.check437 (none) (by decide)
private theorem leaf38:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell438 PairReceipts.choice438 PairReceipts.check438 (none) (by decide)
private theorem leaf39:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell439 PairReceipts.choice439 PairReceipts.check439 (none) (by decide)
private theorem leaf40:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell440 PairReceipts.choice440 PairReceipts.check440 (none) (by decide)
private theorem leaf41:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell441 PairReceipts.choice441 PairReceipts.check441 (none) (by decide)
private theorem leaf42:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell442 PairReceipts.choice442 PairReceipts.check442 (none) (by decide)
private theorem leaf43:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell443 PairReceipts.choice443 PairReceipts.check443 (none) (by decide)
private theorem leaf44:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell444 PairReceipts.choice444 PairReceipts.check444 (none) (by decide)
private theorem leaf45:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell445 PairReceipts.choice445 PairReceipts.check445 (none) (by decide)
private theorem leaf46:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell446 PairReceipts.choice446 PairReceipts.check446 (none) (by decide)
private theorem leaf47:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell447 PairReceipts.choice447 PairReceipts.check447 (none) (by decide)
private theorem leaf48:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell448 PairReceipts.choice448 PairReceipts.check448 (none) (by decide)
private theorem axis49:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,15,some 16,386045,none⟩:=PairRoute.axis 15 leaf47 leaf48
private theorem axis50:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,14,some 16,386045,none⟩:=PairRoute.axis 14 leaf46 axis49
private theorem axis51:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,13,some 16,386045,none⟩:=PairRoute.axis 13 leaf45 axis50
private theorem axis52:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,12,some 16,386045,none⟩:=PairRoute.axis 12 leaf44 axis51
private theorem axis53:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,11,some 16,386045,none⟩:=PairRoute.axis 11 leaf43 axis52
private theorem axis54:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,10,some 16,386045,none⟩:=PairRoute.axis 10 leaf42 axis53
private theorem axis55:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,9,some 16,386045,none⟩:=PairRoute.axis 9 leaf41 axis54
private theorem axis56:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,8,some 16,386045,none⟩:=PairRoute.axis 8 leaf40 axis55
private theorem axis57:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,7,some 16,386045,none⟩:=PairRoute.axis 7 leaf39 axis56
private theorem axis58:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,6,some 16,386045,none⟩:=PairRoute.axis 6 leaf38 axis57
private theorem axis59:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,5,some 16,386045,none⟩:=PairRoute.axis 5 leaf37 axis58
private theorem axis60:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,4,some 16,386045,none⟩:=PairRoute.axis 4 leaf36 axis59
private theorem axis61:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,3,some 16,386045,none⟩:=PairRoute.axis 3 leaf35 axis60
private theorem axis62:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,2,some 16,386045,none⟩:=PairRoute.axis 2 leaf34 axis61
private theorem axis63:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,1,some 16,386045,none⟩:=PairRoute.axis 1 leaf33 axis62
private theorem axis64:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,0,some 16,386045,none⟩:=PairRoute.axis 0 leaf32 axis63
private theorem allAxes65:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,16,some 16⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis64
theorem case81: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,16,some 16⟩:=PairRoute.start _ allAxes65
private theorem leaf66:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell414 PairReceipts.choice414 PairReceipts.check414 (none) (by decide)
private theorem leaf67:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell415 PairReceipts.choice415 PairReceipts.check415 (none) (by decide)
private theorem leaf68:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell416 PairReceipts.choice416 PairReceipts.check416 (none) (by decide)
private theorem leaf69:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell417 PairReceipts.choice417 PairReceipts.check417 (none) (by decide)
private theorem leaf70:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell418 PairReceipts.choice418 PairReceipts.check418 (none) (by decide)
private theorem leaf71:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell419 PairReceipts.choice419 PairReceipts.check419 (none) (by decide)
private theorem leaf72:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell420 PairReceipts.choice420 PairReceipts.check420 (none) (by decide)
private theorem leaf73:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell421 PairReceipts.choice421 PairReceipts.check421 (none) (by decide)
private theorem leaf74:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell422 PairReceipts.choice422 PairReceipts.check422 (none) (by decide)
private theorem leaf75:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell423 PairReceipts.choice423 PairReceipts.check423 (none) (by decide)
private theorem leaf76:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell424 PairReceipts.choice424 PairReceipts.check424 (none) (by decide)
private theorem leaf77:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell425 PairReceipts.choice425 PairReceipts.check425 (none) (by decide)
private theorem leaf78:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell426 PairReceipts.choice426 PairReceipts.check426 (none) (by decide)
private theorem leaf79:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell427 PairReceipts.choice427 PairReceipts.check427 (none) (by decide)
private theorem leaf80:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell428 PairReceipts.choice428 PairReceipts.check428 (none) (by decide)
private theorem leaf81:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell429 PairReceipts.choice429 PairReceipts.check429 (none) (by decide)
private theorem leaf82:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell430 PairReceipts.choice430 PairReceipts.check430 (none) (by decide)
private theorem leaf83:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell431 PairReceipts.choice431 PairReceipts.check431 (none) (by decide)
private theorem axis84:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,16,some 17,386045,none⟩:=PairRoute.axis 16 leaf82 leaf83
private theorem axis85:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,15,some 17,386045,none⟩:=PairRoute.axis 15 leaf81 axis84
private theorem axis86:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,14,some 17,386045,none⟩:=PairRoute.axis 14 leaf80 axis85
private theorem axis87:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,13,some 17,386045,none⟩:=PairRoute.axis 13 leaf79 axis86
private theorem axis88:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,12,some 17,386045,none⟩:=PairRoute.axis 12 leaf78 axis87
private theorem axis89:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,11,some 17,386045,none⟩:=PairRoute.axis 11 leaf77 axis88
private theorem axis90:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,10,some 17,386045,none⟩:=PairRoute.axis 10 leaf76 axis89
private theorem axis91:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,9,some 17,386045,none⟩:=PairRoute.axis 9 leaf75 axis90
private theorem axis92:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,8,some 17,386045,none⟩:=PairRoute.axis 8 leaf74 axis91
private theorem axis93:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,7,some 17,386045,none⟩:=PairRoute.axis 7 leaf73 axis92
private theorem axis94:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,6,some 17,386045,none⟩:=PairRoute.axis 6 leaf72 axis93
private theorem axis95:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,5,some 17,386045,none⟩:=PairRoute.axis 5 leaf71 axis94
private theorem axis96:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,4,some 17,386045,none⟩:=PairRoute.axis 4 leaf70 axis95
private theorem axis97:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,3,some 17,386045,none⟩:=PairRoute.axis 3 leaf69 axis96
private theorem axis98:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,2,some 17,386045,none⟩:=PairRoute.axis 2 leaf68 axis97
private theorem axis99:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,1,some 17,386045,none⟩:=PairRoute.axis 1 leaf67 axis98
private theorem axis100:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,0,some 17,386045,none⟩:=PairRoute.axis 0 leaf66 axis99
private theorem allAxes101:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,17,some 17⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis100
theorem case82: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,17,some 17⟩:=PairRoute.start _ allAxes101
private theorem leaf102:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell395 PairReceipts.choice395 PairReceipts.check395 (none) (by decide)
private theorem leaf103:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell396 PairReceipts.choice396 PairReceipts.check396 (none) (by decide)
private theorem leaf104:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell397 PairReceipts.choice397 PairReceipts.check397 (none) (by decide)
private theorem leaf105:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell398 PairReceipts.choice398 PairReceipts.check398 (none) (by decide)
private theorem leaf106:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell399 PairReceipts.choice399 PairReceipts.check399 (none) (by decide)
private theorem leaf107:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell400 PairReceipts.choice400 PairReceipts.check400 (none) (by decide)
private theorem leaf108:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell401 PairReceipts.choice401 PairReceipts.check401 (none) (by decide)
private theorem leaf109:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell402 PairReceipts.choice402 PairReceipts.check402 (none) (by decide)
private theorem leaf110:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell403 PairReceipts.choice403 PairReceipts.check403 (none) (by decide)
private theorem leaf111:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell404 PairReceipts.choice404 PairReceipts.check404 (none) (by decide)
private theorem leaf112:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell405 PairReceipts.choice405 PairReceipts.check405 (none) (by decide)
private theorem leaf113:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell406 PairReceipts.choice406 PairReceipts.check406 (none) (by decide)
private theorem leaf114:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell407 PairReceipts.choice407 PairReceipts.check407 (none) (by decide)
private theorem leaf115:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell408 PairReceipts.choice408 PairReceipts.check408 (none) (by decide)
private theorem leaf116:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell409 PairReceipts.choice409 PairReceipts.check409 (none) (by decide)
private theorem leaf117:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell410 PairReceipts.choice410 PairReceipts.check410 (none) (by decide)
private theorem leaf118:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell411 PairReceipts.choice411 PairReceipts.check411 (none) (by decide)
private theorem leaf119:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell412 PairReceipts.choice412 PairReceipts.check412 (none) (by decide)
private theorem leaf120:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell413 PairReceipts.choice413 PairReceipts.check413 (none) (by decide)
private theorem axis121:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,17,some 18,386045,none⟩:=PairRoute.axis 17 leaf119 leaf120
private theorem axis122:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,16,some 18,386045,none⟩:=PairRoute.axis 16 leaf118 axis121
private theorem axis123:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,15,some 18,386045,none⟩:=PairRoute.axis 15 leaf117 axis122
private theorem axis124:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,14,some 18,386045,none⟩:=PairRoute.axis 14 leaf116 axis123
private theorem axis125:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,13,some 18,386045,none⟩:=PairRoute.axis 13 leaf115 axis124
private theorem axis126:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,12,some 18,386045,none⟩:=PairRoute.axis 12 leaf114 axis125
private theorem axis127:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,11,some 18,386045,none⟩:=PairRoute.axis 11 leaf113 axis126
private theorem axis128:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,10,some 18,386045,none⟩:=PairRoute.axis 10 leaf112 axis127
private theorem axis129:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,9,some 18,386045,none⟩:=PairRoute.axis 9 leaf111 axis128
private theorem axis130:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,8,some 18,386045,none⟩:=PairRoute.axis 8 leaf110 axis129
private theorem axis131:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,7,some 18,386045,none⟩:=PairRoute.axis 7 leaf109 axis130
private theorem axis132:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,6,some 18,386045,none⟩:=PairRoute.axis 6 leaf108 axis131
private theorem axis133:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,5,some 18,386045,none⟩:=PairRoute.axis 5 leaf107 axis132
private theorem axis134:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,4,some 18,386045,none⟩:=PairRoute.axis 4 leaf106 axis133
private theorem axis135:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,3,some 18,386045,none⟩:=PairRoute.axis 3 leaf105 axis134
private theorem axis136:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,2,some 18,386045,none⟩:=PairRoute.axis 2 leaf104 axis135
private theorem axis137:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,1,some 18,386045,none⟩:=PairRoute.axis 1 leaf103 axis136
private theorem axis138:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,0,some 18,386045,none⟩:=PairRoute.axis 0 leaf102 axis137
private theorem allAxes139:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,18,some 18⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis138
theorem case83: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,18,some 18⟩:=PairRoute.start _ allAxes139
private theorem leaf140:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell375 PairReceipts.choice375 PairReceipts.check375 (none) (by decide)
private theorem leaf141:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell376 PairReceipts.choice376 PairReceipts.check376 (none) (by decide)
private theorem leaf142:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell377 PairReceipts.choice377 PairReceipts.check377 (none) (by decide)
private theorem leaf143:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell378 PairReceipts.choice378 PairReceipts.check378 (none) (by decide)
private theorem leaf144:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell379 PairReceipts.choice379 PairReceipts.check379 (none) (by decide)
private theorem leaf145:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell380 PairReceipts.choice380 PairReceipts.check380 (none) (by decide)
private theorem leaf146:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell381 PairReceipts.choice381 PairReceipts.check381 (none) (by decide)
private theorem leaf147:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell382 PairReceipts.choice382 PairReceipts.check382 (none) (by decide)
private theorem leaf148:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell383 PairReceipts.choice383 PairReceipts.check383 (none) (by decide)
private theorem leaf149:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell384 PairReceipts.choice384 PairReceipts.check384 (none) (by decide)
private theorem leaf150:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell385 PairReceipts.choice385 PairReceipts.check385 (none) (by decide)
private theorem leaf151:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell386 PairReceipts.choice386 PairReceipts.check386 (none) (by decide)
private theorem leaf152:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell387 PairReceipts.choice387 PairReceipts.check387 (none) (by decide)
private theorem leaf153:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell388 PairReceipts.choice388 PairReceipts.check388 (none) (by decide)
private theorem leaf154:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell389 PairReceipts.choice389 PairReceipts.check389 (none) (by decide)
private theorem leaf155:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell390 PairReceipts.choice390 PairReceipts.check390 (none) (by decide)
private theorem leaf156:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell391 PairReceipts.choice391 PairReceipts.check391 (none) (by decide)
private theorem leaf157:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell392 PairReceipts.choice392 PairReceipts.check392 (none) (by decide)
private theorem leaf158:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell393 PairReceipts.choice393 PairReceipts.check393 (none) (by decide)
private theorem leaf159:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,19,some 19,386045,none⟩:=PairLeaves.paired PairReceipts.cell394 PairReceipts.choice394 PairReceipts.check394 (none) (by decide)
private theorem axis160:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,18,some 19,386045,none⟩:=PairRoute.axis 18 leaf158 leaf159
private theorem axis161:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,17,some 19,386045,none⟩:=PairRoute.axis 17 leaf157 axis160
private theorem axis162:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,16,some 19,386045,none⟩:=PairRoute.axis 16 leaf156 axis161
private theorem axis163:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,15,some 19,386045,none⟩:=PairRoute.axis 15 leaf155 axis162
private theorem axis164:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,14,some 19,386045,none⟩:=PairRoute.axis 14 leaf154 axis163
private theorem axis165:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,13,some 19,386045,none⟩:=PairRoute.axis 13 leaf153 axis164
private theorem axis166:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,12,some 19,386045,none⟩:=PairRoute.axis 12 leaf152 axis165
private theorem axis167:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,11,some 19,386045,none⟩:=PairRoute.axis 11 leaf151 axis166
private theorem axis168:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,10,some 19,386045,none⟩:=PairRoute.axis 10 leaf150 axis167
private theorem axis169:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,9,some 19,386045,none⟩:=PairRoute.axis 9 leaf149 axis168
private theorem axis170:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,8,some 19,386045,none⟩:=PairRoute.axis 8 leaf148 axis169
private theorem axis171:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,7,some 19,386045,none⟩:=PairRoute.axis 7 leaf147 axis170
private theorem axis172:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,6,some 19,386045,none⟩:=PairRoute.axis 6 leaf146 axis171
private theorem axis173:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,5,some 19,386045,none⟩:=PairRoute.axis 5 leaf145 axis172
private theorem axis174:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,4,some 19,386045,none⟩:=PairRoute.axis 4 leaf144 axis173
private theorem axis175:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,3,some 19,386045,none⟩:=PairRoute.axis 3 leaf143 axis174
private theorem axis176:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,2,some 19,386045,none⟩:=PairRoute.axis 2 leaf142 axis175
private theorem axis177:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,1,some 19,386045,none⟩:=PairRoute.axis 1 leaf141 axis176
private theorem axis178:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,0,some 19,386045,none⟩:=PairRoute.axis 0 leaf140 axis177
private theorem allAxes179:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,19,some 19⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis178
theorem case84: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,19,some 19⟩:=PairRoute.start _ allAxes179
private theorem leaf180:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell354 PairReceipts.choice354 PairReceipts.check354 (none) (by decide)
private theorem leaf181:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell355 PairReceipts.choice355 PairReceipts.check355 (none) (by decide)
private theorem leaf182:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell356 PairReceipts.choice356 PairReceipts.check356 (none) (by decide)
private theorem leaf183:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell357 PairReceipts.choice357 PairReceipts.check357 (none) (by decide)
private theorem leaf184:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell358 PairReceipts.choice358 PairReceipts.check358 (none) (by decide)
private theorem leaf185:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell359 PairReceipts.choice359 PairReceipts.check359 (none) (by decide)
private theorem leaf186:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell360 PairReceipts.choice360 PairReceipts.check360 (none) (by decide)
private theorem leaf187:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell361 PairReceipts.choice361 PairReceipts.check361 (none) (by decide)
private theorem leaf188:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell362 PairReceipts.choice362 PairReceipts.check362 (none) (by decide)
private theorem leaf189:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell363 PairReceipts.choice363 PairReceipts.check363 (none) (by decide)
private theorem leaf190:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell364 PairReceipts.choice364 PairReceipts.check364 (none) (by decide)
private theorem leaf191:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell365 PairReceipts.choice365 PairReceipts.check365 (none) (by decide)
private theorem leaf192:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell366 PairReceipts.choice366 PairReceipts.check366 (none) (by decide)
private theorem leaf193:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell367 PairReceipts.choice367 PairReceipts.check367 (none) (by decide)
private theorem leaf194:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell368 PairReceipts.choice368 PairReceipts.check368 (none) (by decide)
private theorem leaf195:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell369 PairReceipts.choice369 PairReceipts.check369 (none) (by decide)
private theorem leaf196:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell370 PairReceipts.choice370 PairReceipts.check370 (none) (by decide)
private theorem leaf197:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell371 PairReceipts.choice371 PairReceipts.check371 (none) (by decide)
private theorem leaf198:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell372 PairReceipts.choice372 PairReceipts.check372 (none) (by decide)
private theorem leaf199:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,19,some 19,386045,none⟩:=PairLeaves.paired PairReceipts.cell373 PairReceipts.choice373 PairReceipts.check373 (none) (by decide)
private theorem leaf200:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,20,some 20,386045,none⟩:=PairLeaves.paired PairReceipts.cell374 PairReceipts.choice374 PairReceipts.check374 (none) (by decide)
private theorem axis201:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,19,some 20,386045,none⟩:=PairRoute.axis 19 leaf199 leaf200
private theorem axis202:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,18,some 20,386045,none⟩:=PairRoute.axis 18 leaf198 axis201
private theorem axis203:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,17,some 20,386045,none⟩:=PairRoute.axis 17 leaf197 axis202
private theorem axis204:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,16,some 20,386045,none⟩:=PairRoute.axis 16 leaf196 axis203
private theorem axis205:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,15,some 20,386045,none⟩:=PairRoute.axis 15 leaf195 axis204
private theorem axis206:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,14,some 20,386045,none⟩:=PairRoute.axis 14 leaf194 axis205
private theorem axis207:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,13,some 20,386045,none⟩:=PairRoute.axis 13 leaf193 axis206
private theorem axis208:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,12,some 20,386045,none⟩:=PairRoute.axis 12 leaf192 axis207
private theorem axis209:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,11,some 20,386045,none⟩:=PairRoute.axis 11 leaf191 axis208
private theorem axis210:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,10,some 20,386045,none⟩:=PairRoute.axis 10 leaf190 axis209
private theorem axis211:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,9,some 20,386045,none⟩:=PairRoute.axis 9 leaf189 axis210
private theorem axis212:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,8,some 20,386045,none⟩:=PairRoute.axis 8 leaf188 axis211
private theorem axis213:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,7,some 20,386045,none⟩:=PairRoute.axis 7 leaf187 axis212
private theorem axis214:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,6,some 20,386045,none⟩:=PairRoute.axis 6 leaf186 axis213
private theorem axis215:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,5,some 20,386045,none⟩:=PairRoute.axis 5 leaf185 axis214
private theorem axis216:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,4,some 20,386045,none⟩:=PairRoute.axis 4 leaf184 axis215
private theorem axis217:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,3,some 20,386045,none⟩:=PairRoute.axis 3 leaf183 axis216
private theorem axis218:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,2,some 20,386045,none⟩:=PairRoute.axis 2 leaf182 axis217
private theorem axis219:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,1,some 20,386045,none⟩:=PairRoute.axis 1 leaf181 axis218
private theorem axis220:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,0,some 20,386045,none⟩:=PairRoute.axis 0 leaf180 axis219
private theorem allAxes221:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,20,some 20⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis220
theorem case85: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,20,some 20⟩:=PairRoute.start _ allAxes221
private theorem leaf222:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell332 PairReceipts.choice332 PairReceipts.check332 (none) (by decide)
private theorem leaf223:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell333 PairReceipts.choice333 PairReceipts.check333 (none) (by decide)
private theorem leaf224:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell334 PairReceipts.choice334 PairReceipts.check334 (none) (by decide)
private theorem leaf225:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell335 PairReceipts.choice335 PairReceipts.check335 (none) (by decide)
private theorem leaf226:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell336 PairReceipts.choice336 PairReceipts.check336 (none) (by decide)
private theorem leaf227:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell337 PairReceipts.choice337 PairReceipts.check337 (none) (by decide)
private theorem leaf228:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell338 PairReceipts.choice338 PairReceipts.check338 (none) (by decide)
private theorem leaf229:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell339 PairReceipts.choice339 PairReceipts.check339 (none) (by decide)
private theorem leaf230:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell340 PairReceipts.choice340 PairReceipts.check340 (none) (by decide)
private theorem leaf231:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell341 PairReceipts.choice341 PairReceipts.check341 (none) (by decide)
private theorem leaf232:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell342 PairReceipts.choice342 PairReceipts.check342 (none) (by decide)
private theorem leaf233:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell343 PairReceipts.choice343 PairReceipts.check343 (none) (by decide)
private theorem leaf234:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell344 PairReceipts.choice344 PairReceipts.check344 (none) (by decide)
private theorem leaf235:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell345 PairReceipts.choice345 PairReceipts.check345 (none) (by decide)
private theorem leaf236:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell346 PairReceipts.choice346 PairReceipts.check346 (none) (by decide)
private theorem leaf237:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell347 PairReceipts.choice347 PairReceipts.check347 (none) (by decide)
private theorem leaf238:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell348 PairReceipts.choice348 PairReceipts.check348 (none) (by decide)
private theorem leaf239:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell349 PairReceipts.choice349 PairReceipts.check349 (none) (by decide)
private theorem leaf240:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell350 PairReceipts.choice350 PairReceipts.check350 (none) (by decide)
private theorem leaf241:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,19,some 19,386045,none⟩:=PairLeaves.paired PairReceipts.cell351 PairReceipts.choice351 PairReceipts.check351 (none) (by decide)
private theorem leaf242:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,20,some 20,386045,none⟩:=PairLeaves.paired PairReceipts.cell352 PairReceipts.choice352 PairReceipts.check352 (none) (by decide)
private theorem leaf243:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,21,some 21,386045,none⟩:=PairLeaves.paired PairReceipts.cell353 PairReceipts.choice353 PairReceipts.check353 (none) (by decide)
private theorem axis244:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,20,some 21,386045,none⟩:=PairRoute.axis 20 leaf242 leaf243
private theorem axis245:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,19,some 21,386045,none⟩:=PairRoute.axis 19 leaf241 axis244
private theorem axis246:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,18,some 21,386045,none⟩:=PairRoute.axis 18 leaf240 axis245
private theorem axis247:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,17,some 21,386045,none⟩:=PairRoute.axis 17 leaf239 axis246
private theorem axis248:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,16,some 21,386045,none⟩:=PairRoute.axis 16 leaf238 axis247
private theorem axis249:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,15,some 21,386045,none⟩:=PairRoute.axis 15 leaf237 axis248
private theorem axis250:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,14,some 21,386045,none⟩:=PairRoute.axis 14 leaf236 axis249
private theorem axis251:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,13,some 21,386045,none⟩:=PairRoute.axis 13 leaf235 axis250
private theorem axis252:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,12,some 21,386045,none⟩:=PairRoute.axis 12 leaf234 axis251
private theorem axis253:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,11,some 21,386045,none⟩:=PairRoute.axis 11 leaf233 axis252
private theorem axis254:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,10,some 21,386045,none⟩:=PairRoute.axis 10 leaf232 axis253
private theorem axis255:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,9,some 21,386045,none⟩:=PairRoute.axis 9 leaf231 axis254
private theorem axis256:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,8,some 21,386045,none⟩:=PairRoute.axis 8 leaf230 axis255
private theorem axis257:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,7,some 21,386045,none⟩:=PairRoute.axis 7 leaf229 axis256
private theorem axis258:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,6,some 21,386045,none⟩:=PairRoute.axis 6 leaf228 axis257
private theorem axis259:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,5,some 21,386045,none⟩:=PairRoute.axis 5 leaf227 axis258
private theorem axis260:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,4,some 21,386045,none⟩:=PairRoute.axis 4 leaf226 axis259
private theorem axis261:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,3,some 21,386045,none⟩:=PairRoute.axis 3 leaf225 axis260
private theorem axis262:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,2,some 21,386045,none⟩:=PairRoute.axis 2 leaf224 axis261
private theorem axis263:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,1,some 21,386045,none⟩:=PairRoute.axis 1 leaf223 axis262
private theorem axis264:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,0,some 21,386045,none⟩:=PairRoute.axis 0 leaf222 axis263
private theorem allAxes265:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,21,some 21⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis264
theorem case86: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,21,some 21⟩:=PairRoute.start _ allAxes265
private theorem leaf266:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,0,some 0,386045,none⟩:=PairLeaves.paired PairReceipts.cell309 PairReceipts.choice309 PairReceipts.check309 (none) (by decide)
private theorem leaf267:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,1,some 1,386045,none⟩:=PairLeaves.paired PairReceipts.cell310 PairReceipts.choice310 PairReceipts.check310 (none) (by decide)
private theorem leaf268:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,2,some 2,386045,none⟩:=PairLeaves.paired PairReceipts.cell311 PairReceipts.choice311 PairReceipts.check311 (none) (by decide)
private theorem leaf269:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,3,some 3,386045,none⟩:=PairLeaves.paired PairReceipts.cell312 PairReceipts.choice312 PairReceipts.check312 (none) (by decide)
private theorem leaf270:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,4,some 4,386045,none⟩:=PairLeaves.paired PairReceipts.cell313 PairReceipts.choice313 PairReceipts.check313 (none) (by decide)
private theorem leaf271:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,5,some 5,386045,none⟩:=PairLeaves.paired PairReceipts.cell314 PairReceipts.choice314 PairReceipts.check314 (none) (by decide)
private theorem leaf272:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,6,some 6,386045,none⟩:=PairLeaves.paired PairReceipts.cell315 PairReceipts.choice315 PairReceipts.check315 (none) (by decide)
private theorem leaf273:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,7,some 7,386045,none⟩:=PairLeaves.paired PairReceipts.cell316 PairReceipts.choice316 PairReceipts.check316 (none) (by decide)
private theorem leaf274:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,8,some 8,386045,none⟩:=PairLeaves.paired PairReceipts.cell317 PairReceipts.choice317 PairReceipts.check317 (none) (by decide)
private theorem leaf275:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,9,some 9,386045,none⟩:=PairLeaves.paired PairReceipts.cell318 PairReceipts.choice318 PairReceipts.check318 (none) (by decide)
private theorem leaf276:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,10,some 10,386045,none⟩:=PairLeaves.paired PairReceipts.cell319 PairReceipts.choice319 PairReceipts.check319 (none) (by decide)
private theorem leaf277:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,11,some 11,386045,none⟩:=PairLeaves.paired PairReceipts.cell320 PairReceipts.choice320 PairReceipts.check320 (none) (by decide)
private theorem leaf278:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,12,some 12,386045,none⟩:=PairLeaves.paired PairReceipts.cell321 PairReceipts.choice321 PairReceipts.check321 (none) (by decide)
private theorem leaf279:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,13,some 13,386045,none⟩:=PairLeaves.paired PairReceipts.cell322 PairReceipts.choice322 PairReceipts.check322 (none) (by decide)
private theorem leaf280:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,14,some 14,386045,none⟩:=PairLeaves.paired PairReceipts.cell323 PairReceipts.choice323 PairReceipts.check323 (none) (by decide)
private theorem leaf281:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,15,some 15,386045,none⟩:=PairLeaves.paired PairReceipts.cell324 PairReceipts.choice324 PairReceipts.check324 (none) (by decide)
private theorem leaf282:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,16,some 16,386045,none⟩:=PairLeaves.paired PairReceipts.cell325 PairReceipts.choice325 PairReceipts.check325 (none) (by decide)
private theorem leaf283:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,17,some 17,386045,none⟩:=PairLeaves.paired PairReceipts.cell326 PairReceipts.choice326 PairReceipts.check326 (none) (by decide)
private theorem leaf284:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,18,some 18,386045,none⟩:=PairLeaves.paired PairReceipts.cell327 PairReceipts.choice327 PairReceipts.check327 (none) (by decide)
private theorem leaf285:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,19,some 19,386045,none⟩:=PairLeaves.paired PairReceipts.cell328 PairReceipts.choice328 PairReceipts.check328 (none) (by decide)
private theorem leaf286:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,20,some 20,386045,none⟩:=PairLeaves.paired PairReceipts.cell329 PairReceipts.choice329 PairReceipts.check329 (none) (by decide)
private theorem leaf287:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,21,some 21,386045,none⟩:=PairLeaves.paired PairReceipts.cell330 PairReceipts.choice330 PairReceipts.check330 (none) (by decide)
private theorem leaf288:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,22,some 22,386045,none⟩:=PairLeaves.paired PairReceipts.cell331 PairReceipts.choice331 PairReceipts.check331 (none) (by decide)
private theorem axis289:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,21,some 22,386045,none⟩:=PairRoute.axis 21 leaf287 leaf288
private theorem axis290:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,20,some 22,386045,none⟩:=PairRoute.axis 20 leaf286 axis289
private theorem axis291:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,19,some 22,386045,none⟩:=PairRoute.axis 19 leaf285 axis290
private theorem axis292:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,18,some 22,386045,none⟩:=PairRoute.axis 18 leaf284 axis291
private theorem axis293:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,17,some 22,386045,none⟩:=PairRoute.axis 17 leaf283 axis292
private theorem axis294:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,16,some 22,386045,none⟩:=PairRoute.axis 16 leaf282 axis293
private theorem axis295:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,15,some 22,386045,none⟩:=PairRoute.axis 15 leaf281 axis294
private theorem axis296:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,14,some 22,386045,none⟩:=PairRoute.axis 14 leaf280 axis295
private theorem axis297:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,13,some 22,386045,none⟩:=PairRoute.axis 13 leaf279 axis296
private theorem axis298:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,12,some 22,386045,none⟩:=PairRoute.axis 12 leaf278 axis297
private theorem axis299:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,11,some 22,386045,none⟩:=PairRoute.axis 11 leaf277 axis298
private theorem axis300:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,10,some 22,386045,none⟩:=PairRoute.axis 10 leaf276 axis299
private theorem axis301:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,9,some 22,386045,none⟩:=PairRoute.axis 9 leaf275 axis300
private theorem axis302:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,8,some 22,386045,none⟩:=PairRoute.axis 8 leaf274 axis301
private theorem axis303:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,7,some 22,386045,none⟩:=PairRoute.axis 7 leaf273 axis302
private theorem axis304:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,6,some 22,386045,none⟩:=PairRoute.axis 6 leaf272 axis303
private theorem axis305:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,5,some 22,386045,none⟩:=PairRoute.axis 5 leaf271 axis304
private theorem axis306:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,4,some 22,386045,none⟩:=PairRoute.axis 4 leaf270 axis305
private theorem axis307:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,3,some 22,386045,none⟩:=PairRoute.axis 3 leaf269 axis306
private theorem axis308:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,2,some 22,386045,none⟩:=PairRoute.axis 2 leaf268 axis307
private theorem axis309:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,1,some 22,386045,none⟩:=PairRoute.axis 1 leaf267 axis308
private theorem axis310:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,0,some 22,386045,none⟩:=PairRoute.axis 0 leaf266 axis309
private theorem allAxes311:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,22,some 22⟩,0,none,386045,none⟩:=PairRoute.axes_of_total axis310
theorem case87: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,22,some 22⟩:=PairRoute.start _ allAxes311
private theorem leaf312:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,23,some 24⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell308 PairReceipts.choice308 PairReceipts.check308 (none) (by decide)
theorem case88: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,23,some 24⟩:=PairRoute.start _ leaf312
private theorem leaf313:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,25,some 26⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell307 PairReceipts.choice307 PairReceipts.check307 (none) (by decide)
theorem case89: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,25,some 26⟩:=PairRoute.start _ leaf313
end Research6969.HardFit1At080
end Z6969Source2611

-- Source: Research6969.PairReceipts024
section Z6969Source2612
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell480:PairCell.Row:=⟨33,40,9,2,17,some 20,0,none,257363,[],[]⟩
def choice480:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check480:PairPrices.valid cell480 (0:Fin 18) choice480:=by decide +kernel
def cell481:PairCell.Row:=⟨33,40,9,2,13,some 16,0,none,257363,[],[]⟩
def choice481:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check481:PairPrices.valid cell481 (0:Fin 18) choice481:=by decide +kernel
def cell482:PairCell.Row:=⟨33,40,9,2,9,some 12,0,none,257363,[],[]⟩
def choice482:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check482:PairPrices.valid cell482 (0:Fin 18) choice482:=by decide +kernel
def cell483:PairCell.Row:=⟨33,40,9,2,4,some 8,0,none,257363,[],[]⟩
def choice483:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check483:PairPrices.valid cell483 (0:Fin 18) choice483:=by decide +kernel
def cell484:PairCell.Row:=⟨33,40,9,3,65,some 96,0,none,386045,[MeasuredChoices.test1147],[]⟩
def choice484:PairPrices.Decision:=⟨.marked,.whole,.impossible,0⟩
theorem check484:PairPrices.valid cell484 (0:Fin 18) choice484:=by decide +kernel
def cell485:PairCell.Row:=⟨33,40,9,3,49,some 64,0,none,386045,[MeasuredChoices.test1143],[]⟩
def choice485:PairPrices.Decision:=⟨.marked,.whole,.impossible,0⟩
theorem check485:PairPrices.valid cell485 (0:Fin 18) choice485:=by decide +kernel
def cell486:PairCell.Row:=⟨33,40,9,3,41,some 48,0,none,386045,[MeasuredChoices.test1133],[]⟩
def choice486:PairPrices.Decision:=⟨.marked,.whole,.impossible,0⟩
theorem check486:PairPrices.valid cell486 (0:Fin 18) choice486:=by decide +kernel
def cell487:PairCell.Row:=⟨33,40,9,3,37,some 40,0,none,386045,[MeasuredChoices.test1079],[]⟩
def choice487:PairPrices.Decision:=⟨.marked,.whole,.impossible,0⟩
theorem check487:PairPrices.valid cell487 (0:Fin 18) choice487:=by decide +kernel
def cell488:PairCell.Row:=⟨33,40,9,3,33,some 36,0,none,386045,[MeasuredChoices.test1029],[]⟩
def choice488:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check488:PairPrices.valid cell488 (0:Fin 18) choice488:=by decide +kernel
def cell489:PairCell.Row:=⟨33,40,9,3,29,some 32,0,none,386045,[MeasuredChoices.test977],[]⟩
def choice489:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check489:PairPrices.valid cell489 (0:Fin 18) choice489:=by decide +kernel
def cell490:PairCell.Row:=⟨33,40,9,3,27,some 28,0,none,386045,[MeasuredChoices.test952],[]⟩
def choice490:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check490:PairPrices.valid cell490 (0:Fin 18) choice490:=by decide +kernel
def cell491:PairCell.Row:=⟨33,40,9,3,25,some 26,0,none,386045,[MeasuredChoices.test924],[]⟩
def choice491:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check491:PairPrices.valid cell491 (0:Fin 18) choice491:=by decide +kernel
def cell492:PairCell.Row:=⟨33,40,9,3,23,some 24,0,none,386045,[MeasuredChoices.test896],[]⟩
def choice492:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check492:PairPrices.valid cell492 (0:Fin 18) choice492:=by decide +kernel
def cell493:PairCell.Row:=⟨33,40,9,3,22,some 22,0,none,386045,[MeasuredChoices.test882],[]⟩
def choice493:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check493:PairPrices.valid cell493 (0:Fin 18) choice493:=by decide +kernel
def cell494:PairCell.Row:=⟨33,40,9,3,21,some 21,0,some 0,386045,[MeasuredChoices.test869],[AxisChoices.test1821]⟩
def choice494:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check494:PairPrices.valid cell494 (0:Fin 18) choice494:=by decide +kernel
def cell495:PairCell.Row:=⟨33,40,9,3,21,some 21,1,some 1,386045,[MeasuredChoices.test869],[AxisChoices.test1822]⟩
def choice495:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check495:PairPrices.valid cell495 (0:Fin 18) choice495:=by decide +kernel
def cell496:PairCell.Row:=⟨33,40,9,3,21,some 21,2,some 2,386045,[MeasuredChoices.test869],[AxisChoices.test1823]⟩
def choice496:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check496:PairPrices.valid cell496 (0:Fin 18) choice496:=by decide +kernel
def cell497:PairCell.Row:=⟨33,40,9,3,21,some 21,3,some 3,386045,[MeasuredChoices.test869],[AxisChoices.test1824]⟩
def choice497:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check497:PairPrices.valid cell497 (0:Fin 18) choice497:=by decide +kernel
def cell498:PairCell.Row:=⟨33,40,9,3,21,some 21,4,some 4,386045,[MeasuredChoices.test869],[AxisChoices.test1825]⟩
def choice498:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check498:PairPrices.valid cell498 (0:Fin 18) choice498:=by decide +kernel
def cell499:PairCell.Row:=⟨33,40,9,3,21,some 21,5,some 5,386045,[MeasuredChoices.test869],[AxisChoices.test1826]⟩
def choice499:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check499:PairPrices.valid cell499 (0:Fin 18) choice499:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2612

-- Source: Research6969.HardFit1At090
section Z6969Source2613
set_option autoImplicit true
namespace Research6969.HardFit1At090
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,27,some 28⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell306 PairReceipts.choice306 PairReceipts.check306 (none) (by decide)
theorem case90: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,27,some 28⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,29,some 32⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell305 PairReceipts.choice305 PairReceipts.check305 (none) (by decide)
theorem case91: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,29,some 32⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,3,33,some 40⟩,0,none,386045,none⟩:=PairLeaves.paired PairReceipts.cell304 PairReceipts.choice304 PairReceipts.check304 (none) (by decide)
theorem case92: NormalRoute.Done (0:Fin 18) ⟨28,32,9,3,33,some 40⟩:=PairRoute.start _ leaf2
private theorem leaf3:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,4,13,some 16⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell470 PairReceipts.choice470 PairReceipts.check470 (none) (by decide)
theorem case93: NormalRoute.Done (0:Fin 18) ⟨28,32,9,4,13,some 16⟩:=PairRoute.start _ leaf3
private theorem leaf4:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,4,17,some 20⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell469 PairReceipts.choice469 PairReceipts.check469 (none) (by decide)
theorem case94: NormalRoute.Done (0:Fin 18) ⟨28,32,9,4,17,some 20⟩:=PairRoute.start _ leaf4
private theorem leaf5:PairRoute.Done (0:Fin 18) ⟨⟨28,32,9,4,21,some 24⟩,0,none,514727,none⟩:=PairLeaves.paired PairReceipts.cell468 PairReceipts.choice468 PairReceipts.check468 (none) (by decide)
theorem case95: NormalRoute.Done (0:Fin 18) ⟨28,32,9,4,21,some 24⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,1,65,some 96⟩,0,none,128681,none⟩:=PairLeaves.paired PairReceipts.cell471 PairReceipts.choice471 PairReceipts.check471 (none) (by decide)
theorem case96: NormalRoute.Done (0:Fin 18) ⟨33,40,9,1,65,some 96⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,4,some 8⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell483 PairReceipts.choice483 PairReceipts.check483 (none) (by decide)
theorem case97: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,4,some 8⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,9,some 12⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell482 PairReceipts.choice482 PairReceipts.check482 (none) (by decide)
theorem case98: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (0:Fin 18) ⟨⟨33,40,9,2,13,some 16⟩,0,none,257363,none⟩:=PairLeaves.paired PairReceipts.cell481 PairReceipts.choice481 PairReceipts.check481 (none) (by decide)
theorem case99: NormalRoute.Done (0:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit1At090
end Z6969Source2613

-- Source: Research6969.PairReceipts031
section Z6969Source2614
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell620:PairCell.Row:=⟨33,40,9,3,15,some 15,9,some 9,386045,[MeasuredChoices.test797],[AxisChoices.test1830]⟩
def choice620:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check620:PairPrices.valid cell620 (0:Fin 18) choice620:=by decide +kernel
def cell621:PairCell.Row:=⟨33,40,9,3,15,some 15,10,some 10,386045,[MeasuredChoices.test797],[AxisChoices.test1831]⟩
def choice621:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check621:PairPrices.valid cell621 (0:Fin 18) choice621:=by decide +kernel
def cell622:PairCell.Row:=⟨33,40,9,3,15,some 15,11,some 11,386045,[MeasuredChoices.test797],[AxisChoices.test1832]⟩
def choice622:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check622:PairPrices.valid cell622 (0:Fin 18) choice622:=by decide +kernel
def cell623:PairCell.Row:=⟨33,40,9,3,15,some 15,12,some 12,386045,[MeasuredChoices.test797],[AxisChoices.test1833]⟩
def choice623:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check623:PairPrices.valid cell623 (0:Fin 18) choice623:=by decide +kernel
def cell624:PairCell.Row:=⟨33,40,9,3,15,some 15,13,some 13,386045,[MeasuredChoices.test797],[AxisChoices.test1834]⟩
def choice624:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check624:PairPrices.valid cell624 (0:Fin 18) choice624:=by decide +kernel
def cell625:PairCell.Row:=⟨33,40,9,3,15,some 15,14,some 14,386045,[MeasuredChoices.test797],[AxisChoices.test1835]⟩
def choice625:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check625:PairPrices.valid cell625 (0:Fin 18) choice625:=by decide +kernel
def cell626:PairCell.Row:=⟨33,40,9,3,15,some 15,15,some 15,386045,[MeasuredChoices.test797],[AxisChoices.test1836]⟩
def choice626:PairPrices.Decision:=⟨.markedAxis,.whole,.impossible,0⟩
theorem check626:PairPrices.valid cell626 (0:Fin 18) choice626:=by decide +kernel
def cell627:PairCell.Row:=⟨33,40,9,3,13,some 14,0,none,386045,[MeasuredChoices.test770],[]⟩
def choice627:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check627:PairPrices.valid cell627 (0:Fin 18) choice627:=by decide +kernel
def cell628:PairCell.Row:=⟨33,40,9,3,9,some 12,0,none,386045,[MeasuredChoices.test724],[]⟩
def choice628:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check628:PairPrices.valid cell628 (0:Fin 18) choice628:=by decide +kernel
def cell629:PairCell.Row:=⟨33,40,9,3,4,some 8,0,none,386045,[MeasuredChoices.test671],[]⟩
def choice629:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check629:PairPrices.valid cell629 (0:Fin 18) choice629:=by decide +kernel
def cell630:PairCell.Row:=⟨33,40,9,4,33,some 40,0,none,514727,[MeasuredChoices.test1298],[]⟩
def choice630:PairPrices.Decision:=⟨.marked,.whole,.impossible,0⟩
theorem check630:PairPrices.valid cell630 (0:Fin 18) choice630:=by decide +kernel
def cell631:PairCell.Row:=⟨33,40,9,4,29,some 32,0,none,514727,[MeasuredChoices.test1285],[]⟩
def choice631:PairPrices.Decision:=⟨.marked,.whole,.impossible,0⟩
theorem check631:PairPrices.valid cell631 (0:Fin 18) choice631:=by decide +kernel
def cell632:PairCell.Row:=⟨33,40,9,4,21,some 24,0,none,514727,[MeasuredChoices.test1270],[]⟩
def choice632:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check632:PairPrices.valid cell632 (0:Fin 18) choice632:=by decide +kernel
def cell633:PairCell.Row:=⟨33,40,9,4,17,some 20,0,none,514727,[MeasuredChoices.test1268],[]⟩
def choice633:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check633:PairPrices.valid cell633 (0:Fin 18) choice633:=by decide +kernel
def cell634:PairCell.Row:=⟨33,40,9,4,13,some 16,0,none,514727,[MeasuredChoices.test1256],[]⟩
def choice634:PairPrices.Decision:=⟨.surface,.whole,.impossible,0⟩
theorem check634:PairPrices.valid cell634 (0:Fin 18) choice634:=by decide +kernel
def cell635:PairCell.Row:=⟨41,49,9,1,65,some 96,0,none,128681,[MeasuredChoices.test7],[]⟩
def choice635:PairPrices.Decision:=⟨.affine,.whole,.impossible,0⟩
theorem check635:PairPrices.valid cell635 (0:Fin 18) choice635:=by decide +kernel
def cell636:PairCell.Row:=⟨41,49,9,2,65,some 96,0,none,257363,[MeasuredChoices.test86,MeasuredChoices.test87],[]⟩
def choice636:PairPrices.Decision:=⟨.marked,.whole,.impossible,0⟩
theorem check636:PairPrices.valid cell636 (0:Fin 18) choice636:=by decide +kernel
def cell637:PairCell.Row:=⟨41,49,9,2,57,some 64,0,some 0,257363,[MeasuredChoices.test79],[]⟩
def choice637:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check637:PairPrices.valid cell637 (0:Fin 18) choice637:=by decide +kernel
def cell638:PairCell.Row:=⟨41,49,9,2,57,some 64,1,some 1,257363,[MeasuredChoices.test79],[]⟩
def choice638:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check638:PairPrices.valid cell638 (0:Fin 18) choice638:=by decide +kernel
def cell639:PairCell.Row:=⟨41,49,9,2,57,some 64,2,some 2,257363,[MeasuredChoices.test79],[]⟩
def choice639:PairPrices.Decision:=⟨.separate,.whole,.impossible,0⟩
theorem check639:PairPrices.valid cell639 (0:Fin 18) choice639:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2614
