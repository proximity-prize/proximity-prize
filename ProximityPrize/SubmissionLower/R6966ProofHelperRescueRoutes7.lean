import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked17
import ProximityPrize.SubmissionLower.R6966ProofHelperRescueChecked18

set_option Elab.async false

namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem route42 (stage : Fin 17) : Checked (request 42 stage) := by
  fin_cases stage
  · exact step642_verified
  · exact step643_verified
  · exact step644_verified
  · exact step645_verified
  · exact step646_verified
  · exact step647_verified
  · exact step648_verified
  · exact step649_verified
  · exact step650_verified
  · exact step649_verified
  · exact step651_verified
  · exact step653_verified
  · exact step652_verified
  · exact step654_verified
  · exact step655_verified
  · exact step656_verified
  · exact step657_verified
#print axioms route42

theorem route43 (stage : Fin 17) : Checked (request 43 stage) := by
  fin_cases stage
  · exact step658_verified
  · exact step659_verified
  · exact step660_verified
  · exact step661_verified
  · exact step662_verified
  · exact step663_verified
  · exact step664_verified
  · exact step665_verified
  · exact step666_verified
  · exact step665_verified
  · exact step667_verified
  · exact step669_verified
  · exact step668_verified
  · exact step670_verified
  · exact step671_verified
  · exact step672_verified
  · exact step673_verified
#print axioms route43

theorem route44 (stage : Fin 17) : Checked (request 44 stage) := by
  fin_cases stage
  · exact step674_verified
  · exact step675_verified
  · exact step676_verified
  · exact step677_verified
  · exact step678_verified
  · exact step679_verified
  · exact step680_verified
  · exact step681_verified
  · exact step682_verified
  · exact step681_verified
  · exact step683_verified
  · exact step685_verified
  · exact step684_verified
  · exact step686_verified
  · exact step687_verified
  · exact step688_verified
  · exact step689_verified
#print axioms route44

theorem route45 (stage : Fin 17) : Checked (request 45 stage) := by
  fin_cases stage
  · exact step690_verified
  · exact step691_verified
  · exact step692_verified
  · exact step693_verified
  · exact step694_verified
  · exact step695_verified
  · exact step696_verified
  · exact step697_verified
  · exact step698_verified
  · exact step697_verified
  · exact step699_verified
  · exact step701_verified
  · exact step700_verified
  · exact step702_verified
  · exact step703_verified
  · exact step704_verified
  · exact step705_verified
#print axioms route45

theorem route46 (stage : Fin 17) : Checked (request 46 stage) := by
  fin_cases stage
  · exact step706_verified
  · exact step707_verified
  · exact step708_verified
  · exact step709_verified
  · exact step710_verified
  · exact step711_verified
  · exact step712_verified
  · exact step713_verified
  · exact step714_verified
  · exact step713_verified
  · exact step715_verified
  · exact step717_verified
  · exact step716_verified
  · exact step718_verified
  · exact step719_verified
  · exact step720_verified
  · exact step721_verified
#print axioms route46

theorem route47 (stage : Fin 17) : Checked (request 47 stage) := by
  fin_cases stage
  · exact step722_verified
  · exact step723_verified
  · exact step724_verified
  · exact step725_verified
  · exact step726_verified
  · exact step727_verified
  · exact step728_verified
  · exact step729_verified
  · exact step730_verified
  · exact step729_verified
  · exact step731_verified
  · exact step733_verified
  · exact step732_verified
  · exact step734_verified
  · exact step735_verified
  · exact step736_verified
  · exact step737_verified
#print axioms route47

end Research6966.HelperRescueCatalogue
