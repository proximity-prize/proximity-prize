import ProximityPrize.SubmissionLower.R6970Height2308ContentAdapter
import ProximityPrize.SubmissionLower.R6970Height2313AlternateContracts
import ProximityPrize.SubmissionLower.Bundle6970_7a0ead0a3fc2768d
import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.R6970HeightPowerRadiusGeometry

set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.SeedFourGrade656

open _root_.Research6970.Height2313.Research6969

private theorem beginAt {i} (r : NormalRoute.Region)
    (all : PairRoute.Done i ⟨r,0,none,r.graph*(131071-2313)-1,none⟩) : NormalRoute.Done i r := by
  intro s h
  have w := NormalGeometry.base s
  rw [h.2.2.2.1] at w
  exact all s ⟨h,Nat.zero_le _,by simp,w,by simp⟩

private theorem powercell606 : _root_.Research6969.PhysicalWindow.Cover
    (_root_.Research6969.RadiusPowerExclusion.Positive (RadiusPowerSheets.entry 30000 64 1 8 65 128757)) 2313 2306 [2313] :=
  ⟨by decide, by decide, by decide +kernel, rfl⟩

theorem billcell606 : NormalRoute.Done (3:Fin 18) ⟨64,656,12,1,65,none⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.radiusPower _ 30000 128757 (by decide) powercell606 (by decide) (by decide) (by decide) (by decide))

private def rowc605_0 : PairCell.Row := ⟨64,656,9,1,0,some 40,0,none,128757,[],[]⟩
private def pricec605_0 : PairPrices.Decision := ⟨.affine,.intersection,.impossible,0⟩
private theorem leafc605_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,1,0,some 40⟩,0,none,128757,none⟩ :=
  PairLeaves.paired rowc605_0 pricec605_0 (by decide +kernel) (none) (by decide)

theorem billc605 : NormalRoute.Done (3:Fin 18) ⟨64,656,12,1,0,some 40⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (beginAt _ leafc605_0)

private theorem powercell608 : _root_.Research6969.PhysicalWindow.Cover
    (_root_.Research6969.RadiusPowerExclusion.Positive (RadiusPowerSheets.entry 30000 64 2 7 53 257515)) 2313 2306 [2313] :=
  ⟨by decide, by decide, by decide +kernel, rfl⟩

theorem billcell608 : NormalRoute.Done (3:Fin 18) ⟨64,656,12,2,53,none⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.radiusPower _ 30000 257515 (by decide) powercell608 (by decide) (by decide) (by decide) (by decide))

private def rowcell607_0 : PairCell.Row := ⟨64,656,9,2,0,some 3,0,none,257515,[],[]⟩
private def pricecell607_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafcell607_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,0,some 3⟩,0,none,257515,none⟩ :=
  PairLeaves.paired rowcell607_0 pricecell607_0 (by decide +kernel) (none) (by decide)

theorem billcell607 : NormalRoute.Done (3:Fin 18) ⟨64,656,12,2,0,some 3⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (beginAt _ leafcell607_0)

private def rowcell4072_0 : PairCell.Row := ⟨64,656,9,1,41,some 48,0,none,128757,[MeasuredChoices.test4],[]⟩
private def pricecell4072_0 : PairPrices.Decision := ⟨.affine,.intersection,.impossible,0⟩
private theorem leafcell4072_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,1,41,some 48⟩,0,none,128757,none⟩ :=
  PairLeaves.paired rowcell4072_0 pricecell4072_0 (by decide +kernel) (none) (by decide)

theorem billcell4072 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,1,41,some 48⟩,0,none,128659,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4072_0)

private def rowcell4071_0 : PairCell.Row := ⟨64,656,9,1,49,some 64,0,none,128757,[MeasuredChoices.test6],[]⟩
private def pricecell4071_0 : PairPrices.Decision := ⟨.affine,.intersection,.impossible,0⟩
private theorem leafcell4071_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,1,49,some 64⟩,0,none,128757,none⟩ :=
  PairLeaves.paired rowcell4071_0 pricecell4071_0 (by decide +kernel) (none) (by decide)

theorem billcell4071 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,1,49,some 64⟩,0,none,128659,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4071_0)

private def rowcell4201_0 : PairCell.Row := ⟨64,656,9,2,4,some 8,0,none,257515,[],[]⟩
private def pricecell4201_0 : PairPrices.Decision := ⟨.surface,.intersection,.surface,0⟩
private theorem leafcell4201_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,4,some 8⟩,0,none,257515,none⟩ :=
  PairLeaves.paired rowcell4201_0 pricecell4201_0 (by decide +kernel) (none) (by decide)

theorem billcell4201 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,4,some 8⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4201_0)

private def rowcell4200_0 : PairCell.Row := ⟨64,656,9,2,9,some 12,0,none,257515,[],[]⟩
private def pricecell4200_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafcell4200_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,9,some 12⟩,0,none,257515,none⟩ :=
  PairLeaves.paired rowcell4200_0 pricecell4200_0 (by decide +kernel) (none) (by decide)

theorem billcell4200 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,9,some 12⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4200_0)

private def rowcell4199_0 : PairCell.Row := ⟨64,656,9,2,13,some 16,0,none,257515,[],[]⟩
private def pricecell4199_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafcell4199_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,13,some 16⟩,0,none,257515,none⟩ :=
  PairLeaves.paired rowcell4199_0 pricecell4199_0 (by decide +kernel) (none) (by decide)

theorem billcell4199 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,13,some 16⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4199_0)

private def rowcell4198_0 : PairCell.Row := ⟨64,656,9,2,17,some 20,0,none,257515,[],[]⟩
private def pricecell4198_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafcell4198_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,17,some 20⟩,0,none,257515,none⟩ :=
  PairLeaves.paired rowcell4198_0 pricecell4198_0 (by decide +kernel) (none) (by decide)

theorem billcell4198 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,17,some 20⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4198_0)

private def rowp4197_0 : PairCell.Row := ⟨64,656,9,2,21,some 22,0,none,257515,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩
private def pricep4197_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4197_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,21,some 22⟩,0,none,257515,none⟩ :=
  PairLeaves.paired rowp4197_0 pricep4197_0 (by decide +kernel) (none) (by decide)

theorem billp4197 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,21,some 22⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4197_0)

private def rowp4195_0 : PairCell.Row := ⟨64,656,9,2,23,some 24,0,none,257515,[MeasuredChoices.test29,MeasuredChoices.test30],[]⟩
private def pricep4195_0 : PairPrices.Decision := ⟨(.node 28128048211584585),.intersection,.impossible,307280⟩
private theorem leafp4195_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,23,some 24⟩,0,none,257515,some 307280⟩ :=
  PairLeaves.paired rowp4195_0 pricep4195_0 (by decide +kernel) (some 307280) (by decide)

theorem billp4195 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,23,some 24⟩,0,none,257319,some 307280⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4195_0)

private def rowp4196_0 : PairCell.Row := ⟨64,656,9,2,23,some 24,0,none,307280,[MeasuredChoices.test348,MeasuredChoices.test425],[]⟩
private def pricep4196_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4196_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,23,some 24⟩,0,none,307280,none⟩ :=
  PairLeaves.paired rowp4196_0 pricep4196_0 (by decide +kernel) (none) (by decide)

theorem billp4196 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,23,some 24⟩,0,none,307280,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4196_0)

private def rowcell4193_0 : PairCell.Row := ⟨64,656,9,2,25,some 26,0,none,257515,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩
private def pricecell4193_0 : PairPrices.Decision := ⟨(.node 7865558894203006),.intersection,.impossible,303418⟩
private theorem leafcell4193_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,25,some 26⟩,0,none,257515,some 303418⟩ :=
  PairLeaves.paired rowcell4193_0 pricecell4193_0 (by decide +kernel) (some 303418) (by decide)

theorem billcell4193 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,25,some 26⟩,0,none,257319,some 303418⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4193_0)

private def rowp4194_0 : PairCell.Row := ⟨64,656,9,2,25,some 26,0,none,303418,[MeasuredChoices.test167,MeasuredChoices.test172],[]⟩
private def pricep4194_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4194_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,25,some 26⟩,0,none,303418,none⟩ :=
  PairLeaves.paired rowp4194_0 pricep4194_0 (by decide +kernel) (none) (by decide)

theorem billp4194 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,25,some 26⟩,0,none,303418,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4194_0)

private def rowcell4191_0 : PairCell.Row := ⟨64,656,9,2,27,some 28,0,none,257515,[MeasuredChoices.test37],[]⟩
private def pricecell4191_0 : PairPrices.Decision := ⟨(.node 7880313335284333),.intersection,.impossible,302619⟩
private theorem leafcell4191_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,27,some 28⟩,0,none,257515,some 302619⟩ :=
  PairLeaves.paired rowcell4191_0 pricecell4191_0 (by decide +kernel) (some 302619) (by decide)

theorem billcell4191 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,27,some 28⟩,0,none,257319,some 302619⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4191_0)

private def rowcell4192_0 : PairCell.Row := ⟨64,656,9,2,27,some 28,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩
private def pricecell4192_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafcell4192_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,27,some 28⟩,0,none,302619,none⟩ :=
  PairLeaves.paired rowcell4192_0 pricecell4192_0 (by decide +kernel) (none) (by decide)

theorem billcell4192 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,27,some 28⟩,0,none,302619,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafcell4192_0)

private def rowcell4189_0 : PairCell.Row := ⟨64,656,9,2,29,some 32,0,none,257515,[MeasuredChoices.test39],[]⟩
private def pricecell4189_0 : PairPrices.Decision := ⟨(.node 7900572595486972),.intersection,.impossible,300842⟩
private theorem leafcell4189_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,29,some 32⟩,0,none,257515,some 300842⟩ :=
  PairLeaves.paired rowcell4189_0 pricecell4189_0 (by decide +kernel) (some 300842) (by decide)

theorem billcell4189 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,29,some 32⟩,0,none,257319,some 300842⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4189_0)

private def rowp4190_0 : PairCell.Row := ⟨64,656,9,2,29,some 32,0,none,300842,[MeasuredChoices.test164,MeasuredChoices.test165],[]⟩
private def pricep4190_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4190_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,29,some 32⟩,0,none,300842,none⟩ :=
  PairLeaves.paired rowp4190_0 pricep4190_0 (by decide +kernel) (none) (by decide)

theorem billp4190 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,29,some 32⟩,0,none,300842,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4190_0)

private def rowcell4187_0 : PairCell.Row := ⟨64,656,9,2,33,some 36,0,none,257515,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩
private def pricecell4187_0 : PairPrices.Decision := ⟨(.node 7915295194626570),.intersection,.impossible,298829⟩
private theorem leafcell4187_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,33,some 36⟩,0,none,257515,some 298829⟩ :=
  PairLeaves.paired rowcell4187_0 pricecell4187_0 (by decide +kernel) (some 298829) (by decide)

theorem billcell4187 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,33,some 36⟩,0,none,257319,some 298829⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4187_0)

private def rowp4188_0 : PairCell.Row := ⟨64,656,9,2,33,some 36,0,none,298829,[MeasuredChoices.test161],[]⟩
private def pricep4188_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4188_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,33,some 36⟩,0,none,298829,none⟩ :=
  PairLeaves.paired rowp4188_0 pricep4188_0 (by decide +kernel) (none) (by decide)

theorem billp4188 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,33,some 36⟩,0,none,298829,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4188_0)

private def rowcell4185_0 : PairCell.Row := ⟨64,656,9,2,37,some 40,0,none,257515,[MeasuredChoices.test45,MeasuredChoices.test46],[]⟩
private def pricecell4185_0 : PairPrices.Decision := ⟨(.node 7925749599661125),.intersection,.impossible,296579⟩
private theorem leafcell4185_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,37,some 40⟩,0,none,257515,some 296579⟩ :=
  PairLeaves.paired rowcell4185_0 pricecell4185_0 (by decide +kernel) (some 296579) (by decide)

theorem billcell4185 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,37,some 40⟩,0,none,257319,some 296579⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4185_0)

private def rowp4186_0 : PairCell.Row := ⟨64,656,9,2,37,some 40,0,none,296579,[MeasuredChoices.test158],[]⟩
private def pricep4186_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4186_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,37,some 40⟩,0,none,296579,none⟩ :=
  PairLeaves.paired rowp4186_0 pricep4186_0 (by decide +kernel) (none) (by decide)

theorem billp4186 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,37,some 40⟩,0,none,296579,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4186_0)

private def rowcell4183_0 : PairCell.Row := ⟨64,656,9,2,41,some 44,0,none,257515,[MeasuredChoices.test50],[]⟩
private def pricecell4183_0 : PairPrices.Decision := ⟨(.node 7933422015607066),.intersection,.impossible,294092⟩
private theorem leafcell4183_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,41,some 44⟩,0,none,257515,some 294092⟩ :=
  PairLeaves.paired rowcell4183_0 pricecell4183_0 (by decide +kernel) (some 294092) (by decide)

theorem billcell4183 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,41,some 44⟩,0,none,257319,some 294092⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4183_0)

private def rowp4184_0 : PairCell.Row := ⟨64,656,9,2,41,some 44,0,none,294092,[MeasuredChoices.test124,MeasuredChoices.test140],[]⟩
private def pricep4184_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4184_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,41,some 44⟩,0,none,294092,none⟩ :=
  PairLeaves.paired rowp4184_0 pricep4184_0 (by decide +kernel) (none) (by decide)

theorem billp4184 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,41,some 44⟩,0,none,294092,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4184_0)

private def rowp4182_0 : PairCell.Row := ⟨64,656,9,2,45,some 46,0,none,257515,[MeasuredChoices.test55,MeasuredChoices.test56],[]⟩
private def pricep4182_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4182_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,45,some 46⟩,0,none,257515,none⟩ :=
  PairLeaves.paired rowp4182_0 pricep4182_0 (by decide +kernel) (none) (by decide)

theorem billp4182 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,45,some 46⟩,0,none,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4182_0)

private def rowp4180_0 : PairCell.Row := ⟨64,656,9,2,47,some 48,0,none,257515,[MeasuredChoices.test57,MeasuredChoices.test58],[]⟩
private def pricep4180_0 : PairPrices.Decision := ⟨(.node 29457171958066585),.intersection,.impossible,303874⟩
private theorem leafp4180_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,47,some 48⟩,0,none,257515,some 303874⟩ :=
  PairLeaves.paired rowp4180_0 pricep4180_0 (by decide +kernel) (some 303874) (by decide)

theorem billp4180 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,47,some 48⟩,0,none,257319,some 303874⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4180_0)

private def rowp4181_0 : PairCell.Row := ⟨64,656,9,2,47,some 48,0,none,303874,[MeasuredChoices.test190],[]⟩
private def pricep4181_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4181_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,47,some 48⟩,0,none,303874,none⟩ :=
  PairLeaves.paired rowp4181_0 pricep4181_0 (by decide +kernel) (none) (by decide)

theorem billp4181 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,47,some 48⟩,0,none,303874,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4181_0)

private def rowcell4178_0 : PairCell.Row := ⟨64,656,9,2,49,some 49,0,none,257515,[MeasuredChoices.test62],[]⟩
private def pricecell4178_0 : PairPrices.Decision := ⟨(.node 7940443735681404),.intersection,.impossible,290650⟩
private theorem leafcell4178_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,49,some 49⟩,0,none,257515,some 290650⟩ :=
  PairLeaves.paired rowcell4178_0 pricecell4178_0 (by decide +kernel) (some 290650) (by decide)

theorem billcell4178 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,49,some 49⟩,0,none,257319,some 290650⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4178_0)

private def rowp4179_0 : PairCell.Row := ⟨64,656,9,2,49,some 49,0,none,290650,[MeasuredChoices.test120],[]⟩
private def pricep4179_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafp4179_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,49,some 49⟩,0,none,290650,none⟩ :=
  PairLeaves.paired rowp4179_0 pricep4179_0 (by decide +kernel) (none) (by decide)

theorem billp4179 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,49,some 49⟩,0,none,290650,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafp4179_0)

private def rowcell4127_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,0,some 0,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4127_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4127_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,0,some 0,257515,none⟩ :=
  PairLeaves.paired rowcell4127_0 pricecell4127_0 (by decide +kernel) (none) (by decide)

theorem billcell4127 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,0,some 0,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4127_0)

private def rowcell4128_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,1,some 1,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4128_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4128_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,1,some 1,257515,none⟩ :=
  PairLeaves.paired rowcell4128_0 pricecell4128_0 (by decide +kernel) (none) (by decide)

theorem billcell4128 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,1,some 1,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4128_0)

private def rowcell4129_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,2,some 2,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4129_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4129_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,2,some 2,257515,none⟩ :=
  PairLeaves.paired rowcell4129_0 pricecell4129_0 (by decide +kernel) (none) (by decide)

theorem billcell4129 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,2,some 2,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4129_0)

private def rowcell4130_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,3,some 3,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4130_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4130_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,3,some 3,257515,none⟩ :=
  PairLeaves.paired rowcell4130_0 pricecell4130_0 (by decide +kernel) (none) (by decide)

theorem billcell4130 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,3,some 3,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4130_0)

private def rowcell4131_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,4,some 4,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4131_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4131_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,4,some 4,257515,none⟩ :=
  PairLeaves.paired rowcell4131_0 pricecell4131_0 (by decide +kernel) (none) (by decide)

theorem billcell4131 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,4,some 4,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4131_0)

private def rowcell4132_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,5,some 5,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4132_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4132_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,5,some 5,257515,none⟩ :=
  PairLeaves.paired rowcell4132_0 pricecell4132_0 (by decide +kernel) (none) (by decide)

theorem billcell4132 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,5,some 5,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4132_0)

private def rowcell4133_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,6,some 6,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4133_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4133_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,6,some 6,257515,none⟩ :=
  PairLeaves.paired rowcell4133_0 pricecell4133_0 (by decide +kernel) (none) (by decide)

theorem billcell4133 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,6,some 6,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4133_0)

private def rowcell4134_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,7,some 7,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4134_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4134_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,7,some 7,257515,none⟩ :=
  PairLeaves.paired rowcell4134_0 pricecell4134_0 (by decide +kernel) (none) (by decide)

theorem billcell4134 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,7,some 7,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4134_0)

private def rowcell4135_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,8,some 8,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4135_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4135_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,8,some 8,257515,none⟩ :=
  PairLeaves.paired rowcell4135_0 pricecell4135_0 (by decide +kernel) (none) (by decide)

theorem billcell4135 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,8,some 8,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4135_0)

private def rowcell4136_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,9,some 9,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4136_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4136_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,9,some 9,257515,none⟩ :=
  PairLeaves.paired rowcell4136_0 pricecell4136_0 (by decide +kernel) (none) (by decide)

theorem billcell4136 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,9,some 9,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4136_0)

private def rowcell4137_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,10,some 10,257515,[MeasuredChoices.test64],[]⟩
private def pricecell4137_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4137_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,10,some 10,257515,none⟩ :=
  PairLeaves.paired rowcell4137_0 pricecell4137_0 (by decide +kernel) (none) (by decide)

theorem billcell4137 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,10,some 10,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4137_0)

private def rowcell4138_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,11,some 11,257515,[MeasuredChoices.test64],[AxisChoices.test1774]⟩
private def pricecell4138_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4138_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,11,some 11,257515,none⟩ :=
  PairLeaves.paired rowcell4138_0 pricecell4138_0 (by decide +kernel) (none) (by decide)

theorem billcell4138 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,11,some 11,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4138_0)

private def rowcell4139_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,12,some 12,257515,[MeasuredChoices.test64],[AxisChoices.test1775]⟩
private def pricecell4139_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4139_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,12,some 12,257515,none⟩ :=
  PairLeaves.paired rowcell4139_0 pricecell4139_0 (by decide +kernel) (none) (by decide)

theorem billcell4139 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,12,some 12,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4139_0)

private def rowcell4140_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,13,some 13,257515,[MeasuredChoices.test64],[AxisChoices.test1776]⟩
private def pricecell4140_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4140_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,13,some 13,257515,none⟩ :=
  PairLeaves.paired rowcell4140_0 pricecell4140_0 (by decide +kernel) (none) (by decide)

theorem billcell4140 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,13,some 13,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4140_0)

private def rowcell4141_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,14,some 14,257515,[MeasuredChoices.test64],[AxisChoices.test1777]⟩
private def pricecell4141_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4141_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,14,some 14,257515,none⟩ :=
  PairLeaves.paired rowcell4141_0 pricecell4141_0 (by decide +kernel) (none) (by decide)

theorem billcell4141 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,14,some 14,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4141_0)

private def rowcell4142_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,15,some 15,257515,[MeasuredChoices.test64],[AxisChoices.test1778]⟩
private def pricecell4142_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4142_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,15,some 15,257515,none⟩ :=
  PairLeaves.paired rowcell4142_0 pricecell4142_0 (by decide +kernel) (none) (by decide)

theorem billcell4142 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,15,some 15,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4142_0)

private def rowcell4143_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,16,some 16,257515,[MeasuredChoices.test64],[AxisChoices.test1779]⟩
private def pricecell4143_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4143_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,16,some 16,257515,none⟩ :=
  PairLeaves.paired rowcell4143_0 pricecell4143_0 (by decide +kernel) (none) (by decide)

theorem billcell4143 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,16,some 16,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4143_0)

private def rowcell4144_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,17,some 17,257515,[MeasuredChoices.test64],[AxisChoices.test1780]⟩
private def pricecell4144_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4144_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,17,some 17,257515,none⟩ :=
  PairLeaves.paired rowcell4144_0 pricecell4144_0 (by decide +kernel) (none) (by decide)

theorem billcell4144 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,17,some 17,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4144_0)

private def rowcell4145_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,18,some 18,257515,[MeasuredChoices.test64],[AxisChoices.test1781]⟩
private def pricecell4145_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4145_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,18,some 18,257515,none⟩ :=
  PairLeaves.paired rowcell4145_0 pricecell4145_0 (by decide +kernel) (none) (by decide)

theorem billcell4145 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,18,some 18,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4145_0)

private def rowcell4146_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,19,some 19,257515,[MeasuredChoices.test64],[AxisChoices.test1782]⟩
private def pricecell4146_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4146_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,19,some 19,257515,none⟩ :=
  PairLeaves.paired rowcell4146_0 pricecell4146_0 (by decide +kernel) (none) (by decide)

theorem billcell4146 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,19,some 19,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4146_0)

private def rowcell4147_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,20,some 20,257515,[MeasuredChoices.test64],[AxisChoices.test1783]⟩
private def pricecell4147_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4147_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,20,some 20,257515,none⟩ :=
  PairLeaves.paired rowcell4147_0 pricecell4147_0 (by decide +kernel) (none) (by decide)

theorem billcell4147 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,20,some 20,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4147_0)

private def rowcell4148_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,21,some 21,257515,[MeasuredChoices.test64],[AxisChoices.test1784]⟩
private def pricecell4148_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4148_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,21,some 21,257515,none⟩ :=
  PairLeaves.paired rowcell4148_0 pricecell4148_0 (by decide +kernel) (none) (by decide)

theorem billcell4148 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,21,some 21,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4148_0)

private def rowcell4149_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,22,some 22,257515,[MeasuredChoices.test64],[AxisChoices.test1785]⟩
private def pricecell4149_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4149_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,22,some 22,257515,none⟩ :=
  PairLeaves.paired rowcell4149_0 pricecell4149_0 (by decide +kernel) (none) (by decide)

theorem billcell4149 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,22,some 22,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4149_0)

private def rowcell4150_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,23,some 23,257515,[MeasuredChoices.test64],[AxisChoices.test1786]⟩
private def pricecell4150_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4150_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,23,some 23,257515,none⟩ :=
  PairLeaves.paired rowcell4150_0 pricecell4150_0 (by decide +kernel) (none) (by decide)

theorem billcell4150 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,23,some 23,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4150_0)

private def rowcell4151_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,24,some 24,257515,[MeasuredChoices.test64],[AxisChoices.test1787]⟩
private def pricecell4151_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4151_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,24,some 24,257515,none⟩ :=
  PairLeaves.paired rowcell4151_0 pricecell4151_0 (by decide +kernel) (none) (by decide)

theorem billcell4151 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,24,some 24,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4151_0)

private def rowcell4152_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,25,some 25,257515,[MeasuredChoices.test64],[AxisChoices.test1788]⟩
private def pricecell4152_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4152_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,25,some 25,257515,none⟩ :=
  PairLeaves.paired rowcell4152_0 pricecell4152_0 (by decide +kernel) (none) (by decide)

theorem billcell4152 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,25,some 25,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4152_0)

private def rowcell4153_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,26,some 26,257515,[MeasuredChoices.test64],[AxisChoices.test1789]⟩
private def pricecell4153_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4153_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,26,some 26,257515,none⟩ :=
  PairLeaves.paired rowcell4153_0 pricecell4153_0 (by decide +kernel) (none) (by decide)

theorem billcell4153 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,26,some 26,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4153_0)

private def rowcell4154_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,27,some 27,257515,[MeasuredChoices.test64],[AxisChoices.test1790]⟩
private def pricecell4154_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4154_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,27,some 27,257515,none⟩ :=
  PairLeaves.paired rowcell4154_0 pricecell4154_0 (by decide +kernel) (none) (by decide)

theorem billcell4154 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,27,some 27,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4154_0)

private def rowcell4155_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,28,some 28,257515,[MeasuredChoices.test64],[AxisChoices.test1791]⟩
private def pricecell4155_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4155_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,28,some 28,257515,none⟩ :=
  PairLeaves.paired rowcell4155_0 pricecell4155_0 (by decide +kernel) (none) (by decide)

theorem billcell4155 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,28,some 28,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4155_0)

private def rowcell4156_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,29,some 29,257515,[MeasuredChoices.test64],[AxisChoices.test1792]⟩
private def pricecell4156_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4156_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,29,some 29,257515,none⟩ :=
  PairLeaves.paired rowcell4156_0 pricecell4156_0 (by decide +kernel) (none) (by decide)

theorem billcell4156 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,29,some 29,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4156_0)

private def rowp4157_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,30,some 30,257515,[MeasuredChoices.test64],[AxisChoices.test1792,AxisChoices.test1793]⟩
private def pricep4157_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4157_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,30,some 30,257515,none⟩ :=
  PairLeaves.paired rowp4157_0 pricep4157_0 (by decide +kernel) (none) (by decide)

theorem billp4157 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,30,some 30,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4157_0)

private def rowp4158_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,31,some 31,257515,[MeasuredChoices.test64],[AxisChoices.test1794]⟩
private def pricep4158_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4158_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,31,some 31,257515,none⟩ :=
  PairLeaves.paired rowp4158_0 pricep4158_0 (by decide +kernel) (none) (by decide)

theorem billp4158 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,31,some 31,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4158_0)

private def rowcell4159_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,32,some 32,257515,[MeasuredChoices.test64],[AxisChoices.test1795]⟩
private def pricecell4159_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4159_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,32,some 32,257515,none⟩ :=
  PairLeaves.paired rowcell4159_0 pricecell4159_0 (by decide +kernel) (none) (by decide)

theorem billcell4159 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,32,some 32,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4159_0)

private def rowcell4160_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,33,some 33,257515,[MeasuredChoices.test64],[AxisChoices.test1796]⟩
private def pricecell4160_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4160_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,33,some 33,257515,none⟩ :=
  PairLeaves.paired rowcell4160_0 pricecell4160_0 (by decide +kernel) (none) (by decide)

theorem billcell4160 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,33,some 33,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4160_0)

private def rowcell4161_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,34,some 34,257515,[MeasuredChoices.test64],[AxisChoices.test1797]⟩
private def pricecell4161_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4161_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,34,some 34,257515,none⟩ :=
  PairLeaves.paired rowcell4161_0 pricecell4161_0 (by decide +kernel) (none) (by decide)

theorem billcell4161 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,34,some 34,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4161_0)

private def rowcell4162_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,35,some 35,257515,[MeasuredChoices.test64],[AxisChoices.test1798]⟩
private def pricecell4162_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4162_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,35,some 35,257515,none⟩ :=
  PairLeaves.paired rowcell4162_0 pricecell4162_0 (by decide +kernel) (none) (by decide)

theorem billcell4162 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,35,some 35,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4162_0)

private def rowcell4163_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,36,some 36,257515,[MeasuredChoices.test64],[AxisChoices.test1799]⟩
private def pricecell4163_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4163_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,36,some 36,257515,none⟩ :=
  PairLeaves.paired rowcell4163_0 pricecell4163_0 (by decide +kernel) (none) (by decide)

theorem billcell4163 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,36,some 36,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4163_0)

private def rowcell4164_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,37,some 37,257515,[MeasuredChoices.test64],[AxisChoices.test1800]⟩
private def pricecell4164_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4164_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,37,some 37,257515,none⟩ :=
  PairLeaves.paired rowcell4164_0 pricecell4164_0 (by decide +kernel) (none) (by decide)

theorem billcell4164 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,37,some 37,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4164_0)

private def rowcell4165_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,38,some 38,257515,[MeasuredChoices.test64],[AxisChoices.test1800]⟩
private def pricecell4165_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4165_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,38,some 38,257515,none⟩ :=
  PairLeaves.paired rowcell4165_0 pricecell4165_0 (by decide +kernel) (none) (by decide)

theorem billcell4165 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,38,some 38,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4165_0)

private def rowcell4166_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,39,some 39,257515,[MeasuredChoices.test64],[AxisChoices.test1802]⟩
private def pricecell4166_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4166_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,39,some 39,257515,none⟩ :=
  PairLeaves.paired rowcell4166_0 pricecell4166_0 (by decide +kernel) (none) (by decide)

theorem billcell4166 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,39,some 39,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4166_0)

private def rowcell4167_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,40,some 40,257515,[MeasuredChoices.test64],[AxisChoices.test1803]⟩
private def pricecell4167_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4167_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,40,some 40,257515,none⟩ :=
  PairLeaves.paired rowcell4167_0 pricecell4167_0 (by decide +kernel) (none) (by decide)

theorem billcell4167 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,40,some 40,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4167_0)

private def rowcell4168_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,41,some 41,257515,[MeasuredChoices.test64],[AxisChoices.test1804]⟩
private def pricecell4168_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4168_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,41,some 41,257515,none⟩ :=
  PairLeaves.paired rowcell4168_0 pricecell4168_0 (by decide +kernel) (none) (by decide)

theorem billcell4168 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,41,some 41,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4168_0)

private def rowcell4169_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,42,some 42,257515,[MeasuredChoices.test64],[AxisChoices.test1804]⟩
private def pricecell4169_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4169_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,42,some 42,257515,none⟩ :=
  PairLeaves.paired rowcell4169_0 pricecell4169_0 (by decide +kernel) (none) (by decide)

theorem billcell4169 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,42,some 42,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4169_0)

private def rowcell4170_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,43,some 43,257515,[MeasuredChoices.test64],[AxisChoices.test1806]⟩
private def pricecell4170_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4170_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,43,some 43,257515,none⟩ :=
  PairLeaves.paired rowcell4170_0 pricecell4170_0 (by decide +kernel) (none) (by decide)

theorem billcell4170 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,43,some 43,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4170_0)

private def rowcell4171_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,44,some 44,257515,[MeasuredChoices.test64],[AxisChoices.test1807]⟩
private def pricecell4171_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4171_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,44,some 44,257515,none⟩ :=
  PairLeaves.paired rowcell4171_0 pricecell4171_0 (by decide +kernel) (none) (by decide)

theorem billcell4171 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,44,some 44,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4171_0)

private def rowcell4172_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,45,some 45,257515,[MeasuredChoices.test64],[AxisChoices.test1808]⟩
private def pricecell4172_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4172_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,45,some 45,257515,none⟩ :=
  PairLeaves.paired rowcell4172_0 pricecell4172_0 (by decide +kernel) (none) (by decide)

theorem billcell4172 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,45,some 45,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4172_0)

private def rowcell4173_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,46,some 46,257515,[MeasuredChoices.test64],[AxisChoices.test1809]⟩
private def pricecell4173_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4173_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,46,some 46,257515,none⟩ :=
  PairLeaves.paired rowcell4173_0 pricecell4173_0 (by decide +kernel) (none) (by decide)

theorem billcell4173 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,46,some 46,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4173_0)

private def rowcell4174_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,47,some 47,257515,[MeasuredChoices.test64],[AxisChoices.test1809]⟩
private def pricecell4174_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4174_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,47,some 47,257515,none⟩ :=
  PairLeaves.paired rowcell4174_0 pricecell4174_0 (by decide +kernel) (none) (by decide)

theorem billcell4174 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,47,some 47,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4174_0)

private def rowp4175_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,48,some 48,257515,[MeasuredChoices.test64],[AxisChoices.test1809,AxisChoices.test1811]⟩
private def pricep4175_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4175_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,48,some 48,257515,none⟩ :=
  PairLeaves.paired rowp4175_0 pricep4175_0 (by decide +kernel) (none) (by decide)

theorem billp4175 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,48,some 48,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4175_0)

private def rowp4176_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,49,some 49,257515,[MeasuredChoices.test64],[AxisChoices.test1812]⟩
private def pricep4176_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4176_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,49,some 49,257515,none⟩ :=
  PairLeaves.paired rowp4176_0 pricep4176_0 (by decide +kernel) (none) (by decide)

theorem billp4176 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,49,some 49,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4176_0)

private def rowp4177_0 : PairCell.Row := ⟨64,656,9,2,50,some 50,50,some 50,257515,[MeasuredChoices.test64],[AxisChoices.test1813]⟩
private def pricep4177_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4177_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,50,some 50⟩,50,some 50,257515,none⟩ :=
  PairLeaves.paired rowp4177_0 pricep4177_0 (by decide +kernel) (none) (by decide)

theorem billp4177 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,50,some 50⟩,50,some 50,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4177_0)

private def rowcell4075_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,0,some 0,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4075_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4075_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,0,some 0,257515,none⟩ :=
  PairLeaves.paired rowcell4075_0 pricecell4075_0 (by decide +kernel) (none) (by decide)

theorem billcell4075 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,0,some 0,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4075_0)

private def rowcell4076_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,1,some 1,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4076_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4076_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,1,some 1,257515,none⟩ :=
  PairLeaves.paired rowcell4076_0 pricecell4076_0 (by decide +kernel) (none) (by decide)

theorem billcell4076 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,1,some 1,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4076_0)

private def rowcell4077_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,2,some 2,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4077_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4077_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,2,some 2,257515,none⟩ :=
  PairLeaves.paired rowcell4077_0 pricecell4077_0 (by decide +kernel) (none) (by decide)

theorem billcell4077 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,2,some 2,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4077_0)

private def rowcell4078_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,3,some 3,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4078_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4078_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,3,some 3,257515,none⟩ :=
  PairLeaves.paired rowcell4078_0 pricecell4078_0 (by decide +kernel) (none) (by decide)

theorem billcell4078 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,3,some 3,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4078_0)

private def rowcell4079_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,4,some 4,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4079_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4079_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,4,some 4,257515,none⟩ :=
  PairLeaves.paired rowcell4079_0 pricecell4079_0 (by decide +kernel) (none) (by decide)

theorem billcell4079 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,4,some 4,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4079_0)

private def rowcell4080_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,5,some 5,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4080_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4080_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,5,some 5,257515,none⟩ :=
  PairLeaves.paired rowcell4080_0 pricecell4080_0 (by decide +kernel) (none) (by decide)

theorem billcell4080 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,5,some 5,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4080_0)

private def rowcell4081_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,6,some 6,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4081_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4081_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,6,some 6,257515,none⟩ :=
  PairLeaves.paired rowcell4081_0 pricecell4081_0 (by decide +kernel) (none) (by decide)

theorem billcell4081 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,6,some 6,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4081_0)

private def rowcell4082_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,7,some 7,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4082_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4082_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,7,some 7,257515,none⟩ :=
  PairLeaves.paired rowcell4082_0 pricecell4082_0 (by decide +kernel) (none) (by decide)

theorem billcell4082 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,7,some 7,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4082_0)

private def rowcell4083_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,8,some 8,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4083_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4083_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,8,some 8,257515,none⟩ :=
  PairLeaves.paired rowcell4083_0 pricecell4083_0 (by decide +kernel) (none) (by decide)

theorem billcell4083 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,8,some 8,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4083_0)

private def rowcell4084_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,9,some 9,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4084_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4084_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,9,some 9,257515,none⟩ :=
  PairLeaves.paired rowcell4084_0 pricecell4084_0 (by decide +kernel) (none) (by decide)

theorem billcell4084 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,9,some 9,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4084_0)

private def rowcell4085_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,10,some 10,257515,[MeasuredChoices.test66],[]⟩
private def pricecell4085_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4085_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,10,some 10,257515,none⟩ :=
  PairLeaves.paired rowcell4085_0 pricecell4085_0 (by decide +kernel) (none) (by decide)

theorem billcell4085 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,10,some 10,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4085_0)

private def rowcell4086_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,11,some 11,257515,[MeasuredChoices.test66],[AxisChoices.test1774]⟩
private def pricecell4086_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4086_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,11,some 11,257515,none⟩ :=
  PairLeaves.paired rowcell4086_0 pricecell4086_0 (by decide +kernel) (none) (by decide)

theorem billcell4086 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,11,some 11,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4086_0)

private def rowcell4087_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,12,some 12,257515,[MeasuredChoices.test66],[AxisChoices.test1775]⟩
private def pricecell4087_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4087_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,12,some 12,257515,none⟩ :=
  PairLeaves.paired rowcell4087_0 pricecell4087_0 (by decide +kernel) (none) (by decide)

theorem billcell4087 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,12,some 12,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4087_0)

private def rowcell4088_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,13,some 13,257515,[MeasuredChoices.test66],[AxisChoices.test1776]⟩
private def pricecell4088_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4088_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,13,some 13,257515,none⟩ :=
  PairLeaves.paired rowcell4088_0 pricecell4088_0 (by decide +kernel) (none) (by decide)

theorem billcell4088 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,13,some 13,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4088_0)

private def rowcell4089_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,14,some 14,257515,[MeasuredChoices.test66],[AxisChoices.test1777]⟩
private def pricecell4089_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4089_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,14,some 14,257515,none⟩ :=
  PairLeaves.paired rowcell4089_0 pricecell4089_0 (by decide +kernel) (none) (by decide)

theorem billcell4089 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,14,some 14,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4089_0)

private def rowcell4090_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,15,some 15,257515,[MeasuredChoices.test66],[AxisChoices.test1778]⟩
private def pricecell4090_0 : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩
private theorem leafcell4090_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,15,some 15,257515,none⟩ :=
  PairLeaves.paired rowcell4090_0 pricecell4090_0 (by decide +kernel) (none) (by decide)

theorem billcell4090 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,15,some 15,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4090_0)

private def rowcell4091_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,16,some 16,257515,[MeasuredChoices.test66],[AxisChoices.test1779]⟩
private def pricecell4091_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4091_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,16,some 16,257515,none⟩ :=
  PairLeaves.paired rowcell4091_0 pricecell4091_0 (by decide +kernel) (none) (by decide)

theorem billcell4091 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,16,some 16,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4091_0)

private def rowcell4092_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,17,some 17,257515,[MeasuredChoices.test66],[AxisChoices.test1780]⟩
private def pricecell4092_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4092_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,17,some 17,257515,none⟩ :=
  PairLeaves.paired rowcell4092_0 pricecell4092_0 (by decide +kernel) (none) (by decide)

theorem billcell4092 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,17,some 17,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4092_0)

private def rowcell4093_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,18,some 18,257515,[MeasuredChoices.test66],[AxisChoices.test1781]⟩
private def pricecell4093_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4093_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,18,some 18,257515,none⟩ :=
  PairLeaves.paired rowcell4093_0 pricecell4093_0 (by decide +kernel) (none) (by decide)

theorem billcell4093 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,18,some 18,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4093_0)

private def rowcell4094_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,19,some 19,257515,[MeasuredChoices.test66],[AxisChoices.test1782]⟩
private def pricecell4094_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4094_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,19,some 19,257515,none⟩ :=
  PairLeaves.paired rowcell4094_0 pricecell4094_0 (by decide +kernel) (none) (by decide)

theorem billcell4094 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,19,some 19,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4094_0)

private def rowcell4095_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,20,some 20,257515,[MeasuredChoices.test66],[AxisChoices.test1783]⟩
private def pricecell4095_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4095_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,20,some 20,257515,none⟩ :=
  PairLeaves.paired rowcell4095_0 pricecell4095_0 (by decide +kernel) (none) (by decide)

theorem billcell4095 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,20,some 20,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4095_0)

private def rowcell4096_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,21,some 21,257515,[MeasuredChoices.test66],[AxisChoices.test1784]⟩
private def pricecell4096_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4096_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,21,some 21,257515,none⟩ :=
  PairLeaves.paired rowcell4096_0 pricecell4096_0 (by decide +kernel) (none) (by decide)

theorem billcell4096 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,21,some 21,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4096_0)

private def rowcell4097_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,22,some 22,257515,[MeasuredChoices.test66],[AxisChoices.test1785]⟩
private def pricecell4097_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4097_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,22,some 22,257515,none⟩ :=
  PairLeaves.paired rowcell4097_0 pricecell4097_0 (by decide +kernel) (none) (by decide)

theorem billcell4097 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,22,some 22,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4097_0)

private def rowcell4098_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,23,some 23,257515,[MeasuredChoices.test66],[AxisChoices.test1786]⟩
private def pricecell4098_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4098_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,23,some 23,257515,none⟩ :=
  PairLeaves.paired rowcell4098_0 pricecell4098_0 (by decide +kernel) (none) (by decide)

theorem billcell4098 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,23,some 23,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4098_0)

private def rowcell4099_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,24,some 24,257515,[MeasuredChoices.test66],[AxisChoices.test1787]⟩
private def pricecell4099_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4099_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,24,some 24,257515,none⟩ :=
  PairLeaves.paired rowcell4099_0 pricecell4099_0 (by decide +kernel) (none) (by decide)

theorem billcell4099 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,24,some 24,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4099_0)

private def rowcell4100_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,25,some 25,257515,[MeasuredChoices.test66],[AxisChoices.test1788]⟩
private def pricecell4100_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4100_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,25,some 25,257515,none⟩ :=
  PairLeaves.paired rowcell4100_0 pricecell4100_0 (by decide +kernel) (none) (by decide)

theorem billcell4100 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,25,some 25,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4100_0)

private def rowcell4101_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,26,some 26,257515,[MeasuredChoices.test66],[AxisChoices.test1789]⟩
private def pricecell4101_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4101_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,26,some 26,257515,none⟩ :=
  PairLeaves.paired rowcell4101_0 pricecell4101_0 (by decide +kernel) (none) (by decide)

theorem billcell4101 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,26,some 26,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4101_0)

private def rowcell4102_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,27,some 27,257515,[MeasuredChoices.test66],[AxisChoices.test1790]⟩
private def pricecell4102_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4102_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,27,some 27,257515,none⟩ :=
  PairLeaves.paired rowcell4102_0 pricecell4102_0 (by decide +kernel) (none) (by decide)

theorem billcell4102 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,27,some 27,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4102_0)

private def rowcell4103_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,28,some 28,257515,[MeasuredChoices.test66],[AxisChoices.test1791]⟩
private def pricecell4103_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4103_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,28,some 28,257515,none⟩ :=
  PairLeaves.paired rowcell4103_0 pricecell4103_0 (by decide +kernel) (none) (by decide)

theorem billcell4103 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,28,some 28,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4103_0)

private def rowcell4104_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,29,some 29,257515,[MeasuredChoices.test66],[AxisChoices.test1792]⟩
private def pricecell4104_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4104_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,29,some 29,257515,none⟩ :=
  PairLeaves.paired rowcell4104_0 pricecell4104_0 (by decide +kernel) (none) (by decide)

theorem billcell4104 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,29,some 29,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4104_0)

private def rowp4105_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,30,some 30,257515,[MeasuredChoices.test66],[AxisChoices.test1792,AxisChoices.test1793]⟩
private def pricep4105_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4105_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,30,some 30,257515,none⟩ :=
  PairLeaves.paired rowp4105_0 pricep4105_0 (by decide +kernel) (none) (by decide)

theorem billp4105 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,30,some 30,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4105_0)

private def rowp4106_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,31,some 31,257515,[MeasuredChoices.test66],[AxisChoices.test1794]⟩
private def pricep4106_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4106_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,31,some 31,257515,none⟩ :=
  PairLeaves.paired rowp4106_0 pricep4106_0 (by decide +kernel) (none) (by decide)

theorem billp4106 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,31,some 31,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4106_0)

private def rowcell4107_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,32,some 32,257515,[MeasuredChoices.test66],[AxisChoices.test1795]⟩
private def pricecell4107_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4107_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,32,some 32,257515,none⟩ :=
  PairLeaves.paired rowcell4107_0 pricecell4107_0 (by decide +kernel) (none) (by decide)

theorem billcell4107 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,32,some 32,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4107_0)

private def rowcell4108_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,33,some 33,257515,[MeasuredChoices.test66],[AxisChoices.test1796]⟩
private def pricecell4108_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4108_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,33,some 33,257515,none⟩ :=
  PairLeaves.paired rowcell4108_0 pricecell4108_0 (by decide +kernel) (none) (by decide)

theorem billcell4108 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,33,some 33,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4108_0)

private def rowcell4109_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,34,some 34,257515,[MeasuredChoices.test66],[AxisChoices.test1797]⟩
private def pricecell4109_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4109_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,34,some 34,257515,none⟩ :=
  PairLeaves.paired rowcell4109_0 pricecell4109_0 (by decide +kernel) (none) (by decide)

theorem billcell4109 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,34,some 34,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4109_0)

private def rowcell4110_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,35,some 35,257515,[MeasuredChoices.test66],[AxisChoices.test1798]⟩
private def pricecell4110_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4110_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,35,some 35,257515,none⟩ :=
  PairLeaves.paired rowcell4110_0 pricecell4110_0 (by decide +kernel) (none) (by decide)

theorem billcell4110 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,35,some 35,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4110_0)

private def rowcell4111_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,36,some 36,257515,[MeasuredChoices.test66],[AxisChoices.test1799]⟩
private def pricecell4111_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4111_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,36,some 36,257515,none⟩ :=
  PairLeaves.paired rowcell4111_0 pricecell4111_0 (by decide +kernel) (none) (by decide)

theorem billcell4111 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,36,some 36,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4111_0)

private def rowcell4112_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,37,some 37,257515,[MeasuredChoices.test66],[AxisChoices.test1800]⟩
private def pricecell4112_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4112_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,37,some 37,257515,none⟩ :=
  PairLeaves.paired rowcell4112_0 pricecell4112_0 (by decide +kernel) (none) (by decide)

theorem billcell4112 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,37,some 37,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4112_0)

private def rowcell4113_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,38,some 38,257515,[MeasuredChoices.test66],[AxisChoices.test1800]⟩
private def pricecell4113_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4113_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,38,some 38,257515,none⟩ :=
  PairLeaves.paired rowcell4113_0 pricecell4113_0 (by decide +kernel) (none) (by decide)

theorem billcell4113 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,38,some 38,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4113_0)

private def rowcell4114_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,39,some 39,257515,[MeasuredChoices.test66],[AxisChoices.test1802]⟩
private def pricecell4114_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4114_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,39,some 39,257515,none⟩ :=
  PairLeaves.paired rowcell4114_0 pricecell4114_0 (by decide +kernel) (none) (by decide)

theorem billcell4114 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,39,some 39,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4114_0)

private def rowcell4115_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,40,some 40,257515,[MeasuredChoices.test66],[AxisChoices.test1803]⟩
private def pricecell4115_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4115_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,40,some 40,257515,none⟩ :=
  PairLeaves.paired rowcell4115_0 pricecell4115_0 (by decide +kernel) (none) (by decide)

theorem billcell4115 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,40,some 40,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4115_0)

private def rowcell4116_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,41,some 41,257515,[MeasuredChoices.test66],[AxisChoices.test1804]⟩
private def pricecell4116_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4116_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,41,some 41,257515,none⟩ :=
  PairLeaves.paired rowcell4116_0 pricecell4116_0 (by decide +kernel) (none) (by decide)

theorem billcell4116 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,41,some 41,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4116_0)

private def rowcell4117_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,42,some 42,257515,[MeasuredChoices.test66],[AxisChoices.test1804]⟩
private def pricecell4117_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4117_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,42,some 42,257515,none⟩ :=
  PairLeaves.paired rowcell4117_0 pricecell4117_0 (by decide +kernel) (none) (by decide)

theorem billcell4117 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,42,some 42,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4117_0)

private def rowcell4118_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,43,some 43,257515,[MeasuredChoices.test66],[AxisChoices.test1806]⟩
private def pricecell4118_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4118_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,43,some 43,257515,none⟩ :=
  PairLeaves.paired rowcell4118_0 pricecell4118_0 (by decide +kernel) (none) (by decide)

theorem billcell4118 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,43,some 43,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4118_0)

private def rowcell4119_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,44,some 44,257515,[MeasuredChoices.test66],[AxisChoices.test1807]⟩
private def pricecell4119_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4119_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,44,some 44,257515,none⟩ :=
  PairLeaves.paired rowcell4119_0 pricecell4119_0 (by decide +kernel) (none) (by decide)

theorem billcell4119 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,44,some 44,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4119_0)

private def rowcell4120_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,45,some 45,257515,[MeasuredChoices.test66],[AxisChoices.test1808]⟩
private def pricecell4120_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4120_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,45,some 45,257515,none⟩ :=
  PairLeaves.paired rowcell4120_0 pricecell4120_0 (by decide +kernel) (none) (by decide)

theorem billcell4120 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,45,some 45,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4120_0)

private def rowcell4121_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,46,some 46,257515,[MeasuredChoices.test66],[AxisChoices.test1809]⟩
private def pricecell4121_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4121_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,46,some 46,257515,none⟩ :=
  PairLeaves.paired rowcell4121_0 pricecell4121_0 (by decide +kernel) (none) (by decide)

theorem billcell4121 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,46,some 46,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4121_0)

private def rowcell4122_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,47,some 47,257515,[MeasuredChoices.test66],[AxisChoices.test1809]⟩
private def pricecell4122_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafcell4122_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,47,some 47,257515,none⟩ :=
  PairLeaves.paired rowcell4122_0 pricecell4122_0 (by decide +kernel) (none) (by decide)

theorem billcell4122 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,47,some 47,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4122_0)

private def rowp4123_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,48,some 48,257515,[MeasuredChoices.test66],[AxisChoices.test1809,AxisChoices.test1811]⟩
private def pricep4123_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4123_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,48,some 48,257515,none⟩ :=
  PairLeaves.paired rowp4123_0 pricep4123_0 (by decide +kernel) (none) (by decide)

theorem billp4123 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,48,some 48,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4123_0)

private def rowp4124_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,49,some 49,257515,[MeasuredChoices.test66],[AxisChoices.test1812]⟩
private def pricep4124_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4124_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,49,some 49,257515,none⟩ :=
  PairLeaves.paired rowp4124_0 pricep4124_0 (by decide +kernel) (none) (by decide)

theorem billp4124 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,49,some 49,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4124_0)

private def rowp4125_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,50,some 50,257515,[MeasuredChoices.test66],[AxisChoices.test1813]⟩
private def pricep4125_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4125_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,50,some 50,257515,none⟩ :=
  PairLeaves.paired rowp4125_0 pricep4125_0 (by decide +kernel) (none) (by decide)

theorem billp4125 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,50,some 50,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4125_0)

private def rowp4126_0 : PairCell.Row := ⟨64,656,9,2,51,some 51,51,some 51,257515,[MeasuredChoices.test66],[AxisChoices.test1814]⟩
private def pricep4126_0 : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
private theorem leafp4126_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,51,some 51⟩,51,some 51,257515,none⟩ :=
  PairLeaves.paired rowp4126_0 pricep4126_0 (by decide +kernel) (none) (by decide)

theorem billp4126 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,51,some 51⟩,51,some 51,257319,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafp4126_0)

private def rowcell4073_0 : PairCell.Row := ⟨64,656,9,2,52,some 52,0,none,257515,[MeasuredChoices.test66,MeasuredChoices.test69],[]⟩
private def pricecell4073_0 : PairPrices.Decision := ⟨(.node 7943669425457175),.intersection,.impossible,288407⟩
private theorem leafcell4073_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,52,some 52⟩,0,none,257515,some 288407⟩ :=
  PairLeaves.paired rowcell4073_0 pricecell4073_0 (by decide +kernel) (some 288407) (by decide)

theorem billcell4073 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,52,some 52⟩,0,none,257319,some 288407⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (AlternateDispatch.raiseWeight (by decide) leafcell4073_0)

private def rowcell4074_0 : PairCell.Row := ⟨64,656,9,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩
private def pricecell4074_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leafcell4074_0 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,9,2,52,some 52⟩,0,none,288407,none⟩ :=
  PairLeaves.paired rowcell4074_0 pricecell4074_0 (by decide +kernel) (none) (by decide)

theorem billcell4074 : PairRoute.Done (3:Fin 18) ⟨⟨64,656,12,2,52,some 52⟩,0,none,288407,none⟩ :=
  PairRoute.withNineBelow (by decide) (by decide) (by decide) (leafcell4074_0)

end Research6970.Height2313.Research6969.SeedFourGrade656
