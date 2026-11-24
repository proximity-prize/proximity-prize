import ProximityPrize.SubmissionLower.ZVQ2TVd
set_option Elab.async false
section
set_option autoImplicit true
namespace qoK3iCb
open P5 (p)
open P5_7_2 (fO)
open q7F2qKe (wX weakAgreement scalarWitness aSz originCount afterFree)
open qB9xHGe (StopRates)
private def wB (b:fO) :Bool:=(List.range 52).all fun i=>scalarCheck b (i+3) (extra b (i+3)) (copies b (i+3))
private theorem wit_of {b:fO} (h:wB b=true) :BandWitness b:=
 witness_of_checks fun i=>List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
private def fB (b:fO) :Bool:=
 decide (0≤num (uq b 36) 36) &&
 decide ((1-floorRate/graphRate 1)*(1+3*262144/((weakAgreement-wX b:ℕ) :ℚ)) ≤ aoF uq b 0) &&
 decide ((13+8*262144/((weakAgreement-wX b:ℕ) :ℚ))*(graphRate 2-floorRate)/(graphRate 2-16)≤aoF uq b 0) &&
 (List.range 52).all fun g=>decide (FloorGrade uq b (g+3))
private theorem flo_of {b:fO} (h:fB b=true) :FloorOK uq b := by
 unfold fB at h
 rw [Bool.and_eq_true,Bool.and_eq_true,Bool.and_eq_true] at h
 obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩:=h
 exact ⟨of_decide_eq_true h1,of_decide_eq_true h2,of_decide_eq_true h3,
  fun g=>of_decide_eq_true (List.all_eq_true.mp h4 g.val (List.mem_range.mpr g.isLt))⟩
private def sB (b:fO) :Bool:=
 (List.range (originCount b)).all fun o=>(List.range (afterFree b)).all fun j=>rowCheck b o (j+1) && fastCheck uq b o (j+1)
private theorem sto_of {b:fO} (hw:BandWitness b) (hf:FloorOK uq b) (h:sB b=true) :BandStops b := by
 intro o j
 have h1:=List.all_eq_true.mp (List.all_eq_true.mp h o.val (List.mem_range.mpr o.isLt)) j.val (List.mem_range.mpr j.isLt)
 rw [Bool.and_eq_true] at h1
 exact stop_of_checks hw hf h1.1 h1.2
end qoK3iCb
end
set_option autoImplicit true
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace qoK3iCb
private abbrev b12 :P5_7_2.fO:=⟨12,by decide⟩
private theorem NK:BandWitness b12 :=wit_of (by decide +kernel)
private theorem ZZ:FloorOK uq b12 :=flo_of (by decide +kernel)
theorem dK:BandStops b12 :=sto_of NK ZZ (by decide +kernel)
private abbrev b13:P5_7_2.fO:=⟨13,by decide⟩
private theorem Jj:BandWitness b13:=wit_of (by decide +kernel)
private theorem f13:FloorOK uq b13:=flo_of (by decide +kernel)
theorem e8:BandStops b13:=sto_of Jj f13 (by decide +kernel)
end qoK3iCb
