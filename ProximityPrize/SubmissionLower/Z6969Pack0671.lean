import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0670
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0667

set_option Elab.async false

-- Source: Research6969.HighDispatchSeed2
section Z6969Source1116
set_option autoImplicit true
namespace Research6969.HighDispatchSeed2
open NormalRoute HighPackets
open TransitionPacket.NormalCatalogue
theorem count (need:HighPendingSeed2.Required) (s:State (1:Fin 18)):s.labels.card≤CertifiedCell.target:=by
  let b:=TransitionClassification.band s.f.natDegree
  have first:=TransitionClassification.lower_bound s.high
  have last:=OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤TransitionClassification.maxGraph b): Tail (1:Fin 18) (TransitionClassification.grade b) (OrdinaryComplete.upper (savedMainGrade 1+savedRescueGrade 1) b) (TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch2Band0.allDegrees need a p h
    · exact HighDispatch2Band1.allDegrees need a p h
    · exact HighDispatch2Band2.allDegrees need a p h
    · exact HighDispatch2Band3.allDegrees need a p h
    · exact HighDispatch2Band4.allDegrees need a p h
    · exact HighDispatch2Band5.allDegrees need a p h
    · exact HighDispatch2Band6.allDegrees need a p h
    · exact HighDispatch2Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6969.HighDispatchSeed2
end Z6969Source1116

-- Source: Research6969.HighPendingSeed3
section Z6969Source1117
set_option autoImplicit true
namespace Research6969.HighPendingSeed3
open NormalRoute
def regions:Array Region:=#[⟨23,24,9,2,4,some 8⟩,⟨23,24,9,2,9,some 12⟩,⟨23,24,9,2,13,some 16⟩,⟨23,24,9,2,17,some 20⟩,⟨23,24,9,2,21,some 22⟩,⟨23,24,9,2,23,some 24⟩,⟨23,24,9,2,25,some 28⟩,⟨23,24,9,2,29,some 32⟩,⟨23,24,9,3,4,some 8⟩,⟨23,24,9,3,9,some 12⟩,⟨23,24,9,3,13,some 14⟩,⟨23,24,9,3,15,some 16⟩,⟨23,24,9,3,17,some 20⟩,⟨25,27,9,2,4,some 8⟩,⟨25,27,9,2,9,some 12⟩,⟨25,27,9,2,13,some 16⟩,⟨25,27,9,2,17,some 20⟩,⟨25,27,9,2,21,some 22⟩,⟨25,27,9,2,23,some 24⟩,⟨25,27,9,2,25,some 28⟩,⟨25,27,9,2,29,some 32⟩,⟨25,27,9,3,4,some 8⟩,⟨25,27,9,3,9,some 12⟩,⟨25,27,9,3,13,some 14⟩,⟨25,27,9,3,15,some 15⟩,⟨25,27,9,3,16,some 16⟩,⟨25,27,9,3,17,some 17⟩,⟨25,27,9,3,18,some 18⟩,⟨25,27,9,3,19,some 20⟩,⟨25,27,9,3,21,some 24⟩,⟨28,32,9,2,4,some 8⟩,⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 22⟩,⟨28,32,9,2,23,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨28,32,9,2,29,some 32⟩,⟨28,32,9,2,33,some 40⟩,⟨28,32,9,3,4,some 8⟩,⟨28,32,9,3,9,some 12⟩,⟨28,32,9,3,13,some 14⟩,⟨28,32,9,3,15,some 15⟩,⟨28,32,9,3,16,some 16⟩,⟨28,32,9,3,17,some 17⟩,⟨28,32,9,3,18,some 18⟩,⟨28,32,9,3,19,some 19⟩,⟨28,32,9,3,20,some 20⟩,⟨28,32,9,3,21,some 21⟩,⟨28,32,9,3,22,some 22⟩,⟨28,32,9,3,23,some 24⟩,⟨28,32,9,3,25,some 28⟩,⟨33,40,9,2,4,some 8⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 22⟩,⟨33,40,9,2,23,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨33,40,9,2,29,some 32⟩,⟨33,40,9,2,33,some 40⟩,⟨33,40,9,2,41,some 48⟩,⟨33,40,9,2,49,some 64⟩,⟨33,40,9,2,65,some 96⟩,⟨33,40,9,3,4,some 8⟩,⟨33,40,9,3,9,some 12⟩,⟨33,40,9,3,13,some 14⟩,⟨33,40,9,3,15,some 15⟩,⟨33,40,9,3,16,some 16⟩,⟨33,40,9,3,17,some 17⟩,⟨33,40,9,3,18,some 18⟩,⟨33,40,9,3,19,some 19⟩,⟨33,40,9,3,20,some 20⟩,⟨33,40,9,3,21,some 21⟩,⟨33,40,9,3,22,some 22⟩,⟨33,40,9,3,23,some 24⟩,⟨33,40,9,3,25,some 26⟩,⟨33,40,9,3,27,some 28⟩,⟨33,40,9,3,29,some 32⟩,⟨33,40,9,3,33,some 40⟩,⟨33,40,9,4,25,some 28⟩,⟨41,49,9,2,4,some 8⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 22⟩,⟨41,49,9,2,23,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨41,49,9,2,29,some 32⟩,⟨41,49,9,2,33,some 40⟩,⟨41,49,9,2,41,some 48⟩,⟨41,49,9,2,49,some 64⟩,⟨41,49,9,2,65,some 96⟩,⟨41,49,9,3,4,some 8⟩,⟨41,49,9,3,9,some 12⟩,⟨41,49,9,3,13,some 14⟩,⟨41,49,9,3,15,some 15⟩,⟨41,49,9,3,16,some 16⟩,⟨41,49,9,3,17,some 17⟩,⟨41,49,9,3,18,some 18⟩,⟨41,49,9,3,19,some 19⟩,⟨41,49,9,3,20,some 20⟩,⟨41,49,9,3,21,some 21⟩,⟨41,49,9,3,22,some 22⟩,⟨41,49,9,3,23,some 24⟩,⟨41,49,9,3,25,some 26⟩,⟨41,49,9,3,27,some 28⟩,⟨41,49,9,3,29,some 32⟩,⟨41,49,9,3,33,some 36⟩,⟨41,49,9,3,37,some 40⟩,⟨41,49,9,3,41,some 44⟩,⟨41,49,9,3,45,some 48⟩,⟨41,49,9,3,49,some 64⟩,⟨41,49,9,3,65,some 96⟩,⟨50,63,10,2,4,some 8⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 22⟩,⟨50,63,10,2,23,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,29,some 32⟩,⟨50,63,10,2,33,some 40⟩,⟨50,63,10,2,41,some 44⟩,⟨50,63,10,2,45,some 48⟩,⟨50,63,10,2,49,some 50⟩,⟨50,63,10,2,51,some 51⟩,⟨50,63,10,2,52,some 52⟩,⟨50,63,10,2,53,some 53⟩,⟨50,63,10,2,54,some 54⟩,⟨50,63,10,2,55,some 55⟩,⟨50,63,10,2,56,some 56⟩,⟨50,63,10,2,57,some 57⟩,⟨50,63,10,2,58,some 58⟩,⟨50,63,10,2,59,some 60⟩,⟨50,63,10,2,61,some 64⟩,⟨50,63,10,3,4,some 8⟩,⟨50,63,10,3,9,some 12⟩,⟨50,63,10,3,13,some 13⟩,⟨50,63,10,3,14,some 14⟩,⟨50,63,10,3,15,some 15⟩,⟨50,63,10,3,16,some 16⟩,⟨50,63,10,3,17,some 17⟩,⟨50,63,10,3,18,some 18⟩,⟨50,63,10,3,19,some 19⟩,⟨50,63,10,3,20,some 20⟩,⟨50,63,10,3,21,some 21⟩,⟨50,63,10,3,22,some 22⟩,⟨50,63,10,3,23,some 23⟩,⟨50,63,10,3,24,some 24⟩,⟨50,63,10,3,25,some 25⟩,⟨50,63,10,3,26,some 26⟩,⟨50,63,10,3,27,some 27⟩,⟨50,63,10,3,28,some 28⟩,⟨50,63,10,3,29,some 29⟩,⟨50,63,10,3,30,some 30⟩,⟨50,63,10,3,31,some 32⟩,⟨50,63,10,3,33,some 33⟩,⟨50,63,10,3,34,some 34⟩,⟨50,63,10,3,35,some 35⟩,⟨50,63,10,3,36,some 36⟩,⟨50,63,10,3,37,some 37⟩,⟨50,63,10,3,38,some 38⟩,⟨50,63,10,3,39,some 39⟩,⟨64,722,12,1,0,some 0⟩,⟨64,722,12,1,1,some 1⟩,⟨64,722,12,1,2,some 3⟩,⟨64,722,12,1,4,some 8⟩,⟨64,722,12,1,9,some 12⟩,⟨64,722,12,1,13,some 16⟩,⟨64,722,12,1,17,some 20⟩,⟨64,722,12,1,21,some 24⟩,⟨64,722,12,1,25,some 28⟩,⟨64,722,12,1,29,some 32⟩,⟨64,722,12,1,33,some 40⟩,⟨64,722,12,1,41,some 48⟩,⟨64,722,12,1,49,some 64⟩,⟨64,722,12,2,4,some 8⟩,⟨64,722,12,2,9,some 12⟩,⟨64,722,12,2,13,some 16⟩,⟨64,722,12,2,17,some 20⟩,⟨64,722,12,2,21,some 22⟩,⟨64,722,12,2,23,some 24⟩,⟨64,722,12,2,25,some 28⟩,⟨64,722,12,2,29,some 32⟩,⟨64,722,12,2,33,some 36⟩,⟨64,722,12,2,37,some 40⟩,⟨64,722,12,2,41,some 44⟩,⟨64,722,12,2,45,some 48⟩,⟨64,722,12,2,49,some 50⟩,⟨64,722,12,2,51,some 51⟩,⟨64,722,12,2,52,some 52⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (2:Fin 18) (atIndex j)
end Research6969.HighPendingSeed3
end Z6969Source1117

-- Source: Research6969.SharedGradeInvoice3
section Z6969Source1118
set_option autoImplicit true
namespace Research6969.SharedGradeInvoice3
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
theorem counted (r : Region) (grade : r.gradeHi ≤ 23) : Done (2 : Fin 18) r := by
  apply small r 23 grade (by decide) (by decide +kernel) (by decide +kernel)
  change ∀ i j : Fin 24, i.val + j.val ≤ 23 → JointLedger.Pass SmallCertificates.primary3 SmallCertificates.rescue3
    (JointRouted.seedWeight 133482 3) (JointRouted.ordWeight 133482 1) CertifiedCell.target i.val j.val
  rw [SmallCertificates.seed_price3, SmallCertificates.ordinate_price]
  exact ExtendedJointBills.bill3
end Research6969.SharedGradeInvoice3
end Z6969Source1118

-- Source: Research6969.HighDispatch3Band0
section Z6969Source1119
set_option autoImplicit true
namespace Research6969.HighDispatch3Band0
open NormalRoute
theorem allDegrees (_ : HighPendingSeed3.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (2 : Fin 18) 22 22 9 a 0 :=
  SharedGradeInvoice3.counted _ (by decide : 22 ≤ 23)
end Research6969.HighDispatch3Band0
end Z6969Source1119

-- Source: Research6969.WholeGraphCases010
section Z6969Source1120
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell320: Row := ⟨22,22,9,2,2049,none,[test99],.excluded⟩
theorem checked320: cell320.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell321: Row := ⟨22,22,9,3,0,some 3,[],.surface⟩
theorem checked321: cell321.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell322: Row := ⟨22,22,9,3,21,some 40,[test869],.marked⟩
theorem checked322: cell322.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell323: Row := ⟨22,22,9,3,41,some 256,[test1132],.marked⟩
theorem checked323: cell323.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell324: Row := ⟨22,22,9,3,257,some 512,[test1153],.marked⟩
theorem checked324: cell324.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell325: Row := ⟨22,22,9,3,513,some 1024,[test1154,test1155],.marked⟩
theorem checked325: cell325.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell326: Row := ⟨22,22,9,3,1025,some 2048,[test1156,test1157],.marked⟩
theorem checked326: cell326.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell327: Row := ⟨22,22,9,3,8193,none,[test1162],.excluded⟩
theorem checked327: cell327.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell328: Row := ⟨22,22,9,4,0,some 1,[],.surface⟩
theorem checked328: cell328.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell329: Row := ⟨22,22,9,4,2,some 64,[test1215],.marked⟩
theorem checked329: cell329.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell330: Row := ⟨22,22,9,4,65,some 512,[test1369],.marked⟩
theorem checked330: cell330.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell331: Row := ⟨22,22,9,4,513,some 1024,[test1378],.marked⟩
theorem checked331: cell331.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell332: Row := ⟨22,22,9,5,0,some 1,[],.surface⟩
theorem checked332: cell332.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell333: Row := ⟨22,22,9,5,2,some 128,[test1448],.marked⟩
theorem checked333: cell333.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell334: Row := ⟨22,22,9,5,129,some 512,[test1528],.marked⟩
theorem checked334: cell334.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell335: Row := ⟨22,22,9,5,513,some 1024,[test1533],.marked⟩
theorem checked335: cell335.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell336: Row := ⟨22,22,9,6,0,some 1,[],.surface⟩
theorem checked336: cell336.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell337: Row := ⟨22,22,9,6,2,some 256,[test1566],.marked⟩
theorem checked337: cell337.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell338: Row := ⟨22,22,9,6,257,some 1024,[test1665],.marked⟩
theorem checked338: cell338.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell339: Row := ⟨23,24,9,1,0,some 128,[],.affine⟩
theorem checked339: cell339.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell340: Row := ⟨23,24,9,1,129,some 512,[test11,test12],.marked⟩
theorem checked340: cell340.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell341: Row := ⟨23,24,9,1,513,none,[test15],.excluded⟩
theorem checked341: cell341.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell342: Row := ⟨23,24,9,2,0,some 3,[],.surface⟩
theorem checked342: cell342.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell343: Row := ⟨23,24,9,2,33,some 64,[test43],.marked⟩
theorem checked343: cell343.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell344: Row := ⟨23,24,9,2,65,some 256,[test86],.marked⟩
theorem checked344: cell344.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell345: Row := ⟨23,24,9,2,257,some 1024,[test92,test93],.marked⟩
theorem checked345: cell345.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell346: Row := ⟨23,24,9,2,1025,none,[test96],.excluded⟩
theorem checked346: cell346.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell347: Row := ⟨23,24,9,3,0,some 3,[],.surface⟩
theorem checked347: cell347.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell348: Row := ⟨23,24,9,3,21,some 24,[test869],.marked⟩
theorem checked348: cell348.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell349: Row := ⟨23,24,9,3,25,some 64,[test924],.marked⟩
theorem checked349: cell349.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell350: Row := ⟨23,24,9,3,65,some 256,[test1147],.marked⟩
theorem checked350: cell350.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell351: Row := ⟨23,24,9,3,257,some 512,[test1152,test1153],.marked⟩
theorem checked351: cell351.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1120

-- Source: Research6969.WholeGraphCases011
section Z6969Source1121
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell352: Row := ⟨23,24,9,3,513,some 1024,[test1154,test1155],.marked⟩
theorem checked352: cell352.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell353: Row := ⟨23,24,9,3,1025,some 2048,[test1156,test1157],.marked⟩
theorem checked353: cell353.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell354: Row := ⟨23,24,9,3,4097,none,[test1161],.excluded⟩
theorem checked354: cell354.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell355: Row := ⟨23,24,9,4,0,some 1,[],.surface⟩
theorem checked355: cell355.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell356: Row := ⟨23,24,9,4,2,some 40,[test1215],.marked⟩
theorem checked356: cell356.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell357: Row := ⟨23,24,9,4,41,some 256,[test1329],.marked⟩
theorem checked357: cell357.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell358: Row := ⟨23,24,9,4,257,some 512,[test1376],.marked⟩
theorem checked358: cell358.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell359: Row := ⟨23,24,9,4,513,some 1024,[test1377,test1378],.marked⟩
theorem checked359: cell359.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell360: Row := ⟨23,24,9,5,0,some 1,[],.surface⟩
theorem checked360: cell360.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell361: Row := ⟨23,24,9,5,2,some 128,[test1448],.marked⟩
theorem checked361: cell361.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell362: Row := ⟨23,24,9,5,129,some 512,[test1528],.marked⟩
theorem checked362: cell362.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell363: Row := ⟨23,24,9,5,513,some 1024,[test1533],.marked⟩
theorem checked363: cell363.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell364: Row := ⟨23,24,9,6,0,some 1,[],.surface⟩
theorem checked364: cell364.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell365: Row := ⟨23,24,9,6,2,some 256,[test1566],.marked⟩
theorem checked365: cell365.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell366: Row := ⟨23,24,9,6,257,some 1024,[test1665],.marked⟩
theorem checked366: cell366.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell367: Row := ⟨25,27,9,1,0,some 128,[],.affine⟩
theorem checked367: cell367.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell368: Row := ⟨25,27,9,1,129,some 512,[test11,test12],.marked⟩
theorem checked368: cell368.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell369: Row := ⟨25,27,9,1,513,none,[test15],.excluded⟩
theorem checked369: cell369.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell370: Row := ⟨25,27,9,2,0,some 3,[],.surface⟩
theorem checked370: cell370.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell371: Row := ⟨25,27,9,2,33,some 48,[test44],.marked⟩
theorem checked371: cell371.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell372: Row := ⟨25,27,9,2,49,some 128,[test62],.marked⟩
theorem checked372: cell372.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell373: Row := ⟨25,27,9,2,129,some 256,[test90,test91],.marked⟩
theorem checked373: cell373.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell374: Row := ⟨25,27,9,2,257,some 1024,[test92,test93],.marked⟩
theorem checked374: cell374.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell375: Row := ⟨25,27,9,2,1025,none,[test96],.excluded⟩
theorem checked375: cell375.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell376: Row := ⟨25,27,9,3,0,some 3,[],.surface⟩
theorem checked376: cell376.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell377: Row := ⟨25,27,9,3,25,some 32,[test924],.marked⟩
theorem checked377: cell377.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell378: Row := ⟨25,27,9,3,33,some 96,[test1029],.marked⟩
theorem checked378: cell378.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell379: Row := ⟨25,27,9,3,97,some 256,[test1149],.marked⟩
theorem checked379: cell379.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell380: Row := ⟨25,27,9,3,257,some 512,[test1152,test1153],.marked⟩
theorem checked380: cell380.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell381: Row := ⟨25,27,9,3,513,some 1024,[test1154,test1155],.marked⟩
theorem checked381: cell381.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell382: Row := ⟨25,27,9,3,1025,none,[test1156],.excluded⟩
theorem checked382: cell382.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell383: Row := ⟨25,27,9,4,0,some 1,[],.surface⟩
theorem checked383: cell383.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1121

-- Source: Research6969.HighDispatch3Band1
section Z6969Source1122
set_option autoImplicit true
namespace Research6969.HighDispatch3Band1
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem leaf1_513:Done (2:Fin 18) ⟨23,24,9,1,513,none⟩:=entire WholeRows.cell341 WholeRows.checked341
private theorem tail1_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 1 513:=leaf1_513
private theorem leaf1_129:Done (2:Fin 18) ⟨23,24,9,1,129,some 512⟩:=entire WholeRows.cell340 WholeRows.checked340
private theorem tail1_129 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 1 129:=join (leaf1_129) (tail1_513 needed)
private theorem leaf1_0:Done (2:Fin 18) ⟨23,24,9,1,0,some 128⟩:=entire WholeRows.cell339 WholeRows.checked339
private theorem tail1_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 1 0:=join (leaf1_0) (tail1_129 needed)
private theorem leaf2_1025:Done (2:Fin 18) ⟨23,24,9,2,1025,none⟩:=entire WholeRows.cell346 WholeRows.checked346
private theorem tail2_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 1025:=leaf2_1025
private theorem leaf2_257:Done (2:Fin 18) ⟨23,24,9,2,257,some 1024⟩:=entire WholeRows.cell345 WholeRows.checked345
private theorem tail2_257 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 257:=join (leaf2_257) (tail2_1025 needed)
private theorem leaf2_65:Done (2:Fin 18) ⟨23,24,9,2,65,some 256⟩:=entire WholeRows.cell344 WholeRows.checked344
private theorem tail2_65 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 65:=join (leaf2_65) (tail2_257 needed)
private theorem leaf2_33:Done (2:Fin 18) ⟨23,24,9,2,33,some 64⟩:=entire WholeRows.cell343 WholeRows.checked343
private theorem tail2_33 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 33:=join (leaf2_33) (tail2_65 needed)
private theorem leaf2_29 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,29,some 32⟩:=needed ⟨7,by decide⟩
private theorem tail2_29 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 29:=join (leaf2_29 needed) (tail2_33 needed)
private theorem leaf2_25 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,25,some 28⟩:=needed ⟨6,by decide⟩
private theorem tail2_25 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 25:=join (leaf2_25 needed) (tail2_29 needed)
private theorem leaf2_23 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,23,some 24⟩:=needed ⟨5,by decide⟩
private theorem tail2_23 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 23:=join (leaf2_23 needed) (tail2_25 needed)
private theorem leaf2_21 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,21,some 22⟩:=needed ⟨4,by decide⟩
private theorem tail2_21 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 21:=join (leaf2_21 needed) (tail2_23 needed)
private theorem leaf2_17 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,17,some 20⟩:=needed ⟨3,by decide⟩
private theorem tail2_17 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 17:=join (leaf2_17 needed) (tail2_21 needed)
private theorem leaf2_13 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,13,some 16⟩:=needed ⟨2,by decide⟩
private theorem tail2_13 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 13:=join (leaf2_13 needed) (tail2_17 needed)
private theorem leaf2_9 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,9,some 12⟩:=needed ⟨1,by decide⟩
private theorem tail2_9 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 9:=join (leaf2_9 needed) (tail2_13 needed)
private theorem leaf2_4 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,2,4,some 8⟩:=needed ⟨0,by decide⟩
private theorem tail2_4 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 4:=join (leaf2_4 needed) (tail2_9 needed)
private theorem leaf2_0:Done (2:Fin 18) ⟨23,24,9,2,0,some 3⟩:=entire WholeRows.cell342 WholeRows.checked342
private theorem tail2_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 0:=join (leaf2_0) (tail2_4 needed)
private theorem leaf3_4097:Done (2:Fin 18) ⟨23,24,9,3,4097,none⟩:=entire WholeRows.cell354 WholeRows.checked354
private theorem tail3_4097 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 4097:=leaf3_4097
private theorem leaf3_2049:Done (2:Fin 18) ⟨23,24,9,3,2049,some 4096⟩:=power _ 385979 (by decide) PowerReceipts.power20 (by decide) (by decide) (by decide)
private theorem tail3_2049 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 2049:=join (leaf3_2049) (tail3_4097 needed)
private theorem leaf3_1025:Done (2:Fin 18) ⟨23,24,9,3,1025,some 2048⟩:=entire WholeRows.cell353 WholeRows.checked353
private theorem tail3_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 1025:=join (leaf3_1025) (tail3_2049 needed)
private theorem leaf3_513:Done (2:Fin 18) ⟨23,24,9,3,513,some 1024⟩:=entire WholeRows.cell352 WholeRows.checked352
private theorem tail3_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 513:=join (leaf3_513) (tail3_1025 needed)
private theorem leaf3_257:Done (2:Fin 18) ⟨23,24,9,3,257,some 512⟩:=entire WholeRows.cell351 WholeRows.checked351
private theorem tail3_257 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 257:=join (leaf3_257) (tail3_513 needed)
private theorem leaf3_65:Done (2:Fin 18) ⟨23,24,9,3,65,some 256⟩:=entire WholeRows.cell350 WholeRows.checked350
private theorem tail3_65 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 65:=join (leaf3_65) (tail3_257 needed)
private theorem leaf3_25:Done (2:Fin 18) ⟨23,24,9,3,25,some 64⟩:=entire WholeRows.cell349 WholeRows.checked349
private theorem tail3_25 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 25:=join (leaf3_25) (tail3_65 needed)
private theorem leaf3_21:Done (2:Fin 18) ⟨23,24,9,3,21,some 24⟩:=entire WholeRows.cell348 WholeRows.checked348
private theorem tail3_21 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 21:=join (leaf3_21) (tail3_25 needed)
private theorem leaf3_17 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,3,17,some 20⟩:=needed ⟨12,by decide⟩
private theorem tail3_17 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 17:=join (leaf3_17 needed) (tail3_21 needed)
private theorem leaf3_15 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,3,15,some 16⟩:=needed ⟨11,by decide⟩
private theorem tail3_15 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 15:=join (leaf3_15 needed) (tail3_17 needed)
private theorem leaf3_13 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,3,13,some 14⟩:=needed ⟨10,by decide⟩
private theorem tail3_13 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 13:=join (leaf3_13 needed) (tail3_15 needed)
private theorem leaf3_9 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,3,9,some 12⟩:=needed ⟨9,by decide⟩
private theorem tail3_9 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 9:=join (leaf3_9 needed) (tail3_13 needed)
private theorem leaf3_4 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨23,24,9,3,4,some 8⟩:=needed ⟨8,by decide⟩
private theorem tail3_4 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 4:=join (leaf3_4 needed) (tail3_9 needed)
private theorem leaf3_0:Done (2:Fin 18) ⟨23,24,9,3,0,some 3⟩:=entire WholeRows.cell347 WholeRows.checked347
private theorem tail3_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 0:=join (leaf3_0) (tail3_4 needed)
private theorem leaf4_32769:Done (2:Fin 18) ⟨23,24,9,4,32769,none⟩:=power _ 514639 (by decide) PowerReceipts.power25 (by decide) (by decide) (by decide)
private theorem tail4_32769 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 32769:=leaf4_32769
private theorem leaf4_8193:Done (2:Fin 18) ⟨23,24,9,4,8193,some 32768⟩:=power _ 514639 (by decide) PowerReceipts.power24 (by decide) (by decide) (by decide)
private theorem tail4_8193 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 8193:=join (leaf4_8193) (tail4_32769 needed)
private theorem leaf4_4097:Done (2:Fin 18) ⟨23,24,9,4,4097,some 8192⟩:=power _ 514639 (by decide) PowerReceipts.power23 (by decide) (by decide) (by decide)
private theorem tail4_4097 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 4097:=join (leaf4_4097) (tail4_8193 needed)
private theorem leaf4_2049:Done (2:Fin 18) ⟨23,24,9,4,2049,some 4096⟩:=power _ 514639 (by decide) PowerReceipts.power22 (by decide) (by decide) (by decide)
private theorem tail4_2049 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 2049:=join (leaf4_2049) (tail4_4097 needed)
private theorem leaf4_1025:Done (2:Fin 18) ⟨23,24,9,4,1025,some 2048⟩:=power _ 514639 (by decide) PowerReceipts.power21 (by decide) (by decide) (by decide)
private theorem tail4_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 1025:=join (leaf4_1025) (tail4_2049 needed)
private theorem leaf4_513:Done (2:Fin 18) ⟨23,24,9,4,513,some 1024⟩:=entire WholeRows.cell359 WholeRows.checked359
private theorem tail4_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 513:=join (leaf4_513) (tail4_1025 needed)
private theorem leaf4_257:Done (2:Fin 18) ⟨23,24,9,4,257,some 512⟩:=entire WholeRows.cell358 WholeRows.checked358
private theorem tail4_257 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 257:=join (leaf4_257) (tail4_513 needed)
private theorem leaf4_41:Done (2:Fin 18) ⟨23,24,9,4,41,some 256⟩:=entire WholeRows.cell357 WholeRows.checked357
private theorem tail4_41 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 41:=join (leaf4_41) (tail4_257 needed)
private theorem leaf4_2:Done (2:Fin 18) ⟨23,24,9,4,2,some 40⟩:=entire WholeRows.cell356 WholeRows.checked356
private theorem tail4_2 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 2:=join (leaf4_2) (tail4_41 needed)
private theorem leaf4_0:Done (2:Fin 18) ⟨23,24,9,4,0,some 1⟩:=entire WholeRows.cell355 WholeRows.checked355
private theorem tail4_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 0:=join (leaf4_0) (tail4_2 needed)
private theorem leaf5_32769:Done (2:Fin 18) ⟨23,24,9,5,32769,none⟩:=power _ 643299 (by decide) PowerReceipts.power30 (by decide) (by decide) (by decide)
private theorem tail5_32769 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 32769:=leaf5_32769
private theorem leaf5_8193:Done (2:Fin 18) ⟨23,24,9,5,8193,some 32768⟩:=power _ 643299 (by decide) PowerReceipts.power29 (by decide) (by decide) (by decide)
private theorem tail5_8193 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 8193:=join (leaf5_8193) (tail5_32769 needed)
private theorem leaf5_4097:Done (2:Fin 18) ⟨23,24,9,5,4097,some 8192⟩:=power _ 643299 (by decide) PowerReceipts.power28 (by decide) (by decide) (by decide)
private theorem tail5_4097 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 4097:=join (leaf5_4097) (tail5_8193 needed)
private theorem leaf5_2049:Done (2:Fin 18) ⟨23,24,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power27 (by decide) (by decide) (by decide)
private theorem tail5_2049 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 2049:=join (leaf5_2049) (tail5_4097 needed)
private theorem leaf5_1025:Done (2:Fin 18) ⟨23,24,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power26 (by decide) (by decide) (by decide)
private theorem tail5_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 1025:=join (leaf5_1025) (tail5_2049 needed)
private theorem leaf5_513:Done (2:Fin 18) ⟨23,24,9,5,513,some 1024⟩:=entire WholeRows.cell363 WholeRows.checked363
private theorem tail5_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 513:=join (leaf5_513) (tail5_1025 needed)
private theorem leaf5_129:Done (2:Fin 18) ⟨23,24,9,5,129,some 512⟩:=entire WholeRows.cell362 WholeRows.checked362
private theorem tail5_129 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 129:=join (leaf5_129) (tail5_513 needed)
private theorem leaf5_2:Done (2:Fin 18) ⟨23,24,9,5,2,some 128⟩:=entire WholeRows.cell361 WholeRows.checked361
private theorem tail5_2 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 2:=join (leaf5_2) (tail5_129 needed)
private theorem leaf5_0:Done (2:Fin 18) ⟨23,24,9,5,0,some 1⟩:=entire WholeRows.cell360 WholeRows.checked360
private theorem tail5_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 0:=join (leaf5_0) (tail5_2 needed)
private theorem leaf6_32769:Done (2:Fin 18) ⟨23,24,9,6,32769,none⟩:=power _ 771959 (by decide) PowerReceipts.power35 (by decide) (by decide) (by decide)
private theorem tail6_32769 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 32769:=leaf6_32769
private theorem leaf6_8193:Done (2:Fin 18) ⟨23,24,9,6,8193,some 32768⟩:=power _ 771959 (by decide) PowerReceipts.power34 (by decide) (by decide) (by decide)
private theorem tail6_8193 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 8193:=join (leaf6_8193) (tail6_32769 needed)
private theorem leaf6_4097:Done (2:Fin 18) ⟨23,24,9,6,4097,some 8192⟩:=power _ 771959 (by decide) PowerReceipts.power33 (by decide) (by decide) (by decide)
private theorem tail6_4097 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 4097:=join (leaf6_4097) (tail6_8193 needed)
private theorem leaf6_2049:Done (2:Fin 18) ⟨23,24,9,6,2049,some 4096⟩:=power _ 771959 (by decide) PowerReceipts.power32 (by decide) (by decide) (by decide)
private theorem tail6_2049 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 2049:=join (leaf6_2049) (tail6_4097 needed)
private theorem leaf6_1025:Done (2:Fin 18) ⟨23,24,9,6,1025,some 2048⟩:=power _ 771959 (by decide) PowerReceipts.power31 (by decide) (by decide) (by decide)
private theorem tail6_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 1025:=join (leaf6_1025) (tail6_2049 needed)
private theorem leaf6_257:Done (2:Fin 18) ⟨23,24,9,6,257,some 1024⟩:=entire WholeRows.cell366 WholeRows.checked366
private theorem tail6_257 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 257:=join (leaf6_257) (tail6_1025 needed)
private theorem leaf6_2:Done (2:Fin 18) ⟨23,24,9,6,2,some 256⟩:=entire WholeRows.cell365 WholeRows.checked365
private theorem tail6_2 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 2:=join (leaf6_2) (tail6_257 needed)
private theorem leaf6_0:Done (2:Fin 18) ⟨23,24,9,6,0,some 1⟩:=entire WholeRows.cell364 WholeRows.checked364
private theorem tail6_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 0:=join (leaf6_0) (tail6_2 needed)
theorem allDegrees (needed:HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤6):
    Tail (2:Fin 18) 23 24 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
  · exact tail5_0 needed
  · exact tail6_0 needed
end Research6969.HighDispatch3Band1
end Z6969Source1122

-- Source: Research6969.WholeGraphCases012
section Z6969Source1123
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell384: Row := ⟨25,27,9,4,2,some 12,[test1215],.surface⟩
theorem checked384: cell384.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell385: Row := ⟨25,27,9,4,13,some 48,[test1256],.marked⟩
theorem checked385: cell385.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell386: Row := ⟨25,27,9,4,49,some 256,[test1352],.marked⟩
theorem checked386: cell386.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell387: Row := ⟨25,27,9,4,257,some 512,[test1376],.marked⟩
theorem checked387: cell387.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell388: Row := ⟨25,27,9,4,513,some 1024,[test1377,test1378],.marked⟩
theorem checked388: cell388.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell389: Row := ⟨25,27,9,4,2049,none,[test1382],.excluded⟩
theorem checked389: cell389.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell390: Row := ⟨25,27,9,5,0,some 1,[],.surface⟩
theorem checked390: cell390.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell391: Row := ⟨25,27,9,5,2,some 96,[test1448],.marked⟩
theorem checked391: cell391.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell392: Row := ⟨25,27,9,5,97,some 512,[test1527],.marked⟩
theorem checked392: cell392.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell393: Row := ⟨25,27,9,5,4097,none,[test1861],.excluded⟩
theorem checked393: cell393.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell394: Row := ⟨28,32,9,1,0,some 128,[],.affine⟩
theorem checked394: cell394.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell395: Row := ⟨28,32,9,1,129,some 512,[test11,test12],.marked⟩
theorem checked395: cell395.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell396: Row := ⟨28,32,9,1,513,none,[test15],.excluded⟩
theorem checked396: cell396.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell397: Row := ⟨28,32,9,2,0,some 3,[],.surface⟩
theorem checked397: cell397.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell398: Row := ⟨28,32,9,2,41,some 64,[test50],.marked⟩
theorem checked398: cell398.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell399: Row := ⟨28,32,9,2,65,some 128,[test87],.marked⟩
theorem checked399: cell399.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell400: Row := ⟨28,32,9,2,129,some 256,[test90,test91],.marked⟩
theorem checked400: cell400.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell401: Row := ⟨28,32,9,2,257,none,[test92],.excluded⟩
theorem checked401: cell401.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell402: Row := ⟨28,32,9,3,0,some 3,[],.surface⟩
theorem checked402: cell402.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell403: Row := ⟨28,32,9,3,29,some 32,[test977],.marked⟩
theorem checked403: cell403.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell404: Row := ⟨28,32,9,3,33,some 48,[test1029],.marked⟩
theorem checked404: cell404.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell405: Row := ⟨28,32,9,3,49,some 128,[test1142],.marked⟩
theorem checked405: cell405.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell406: Row := ⟨28,32,9,3,129,some 256,[test1150,test1151],.marked⟩
theorem checked406: cell406.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell407: Row := ⟨28,32,9,3,257,some 512,[test1152,test1153],.marked⟩
theorem checked407: cell407.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell408: Row := ⟨28,32,9,3,513,none,[test1154],.excluded⟩
theorem checked408: cell408.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell409: Row := ⟨28,32,9,4,0,some 1,[],.surface⟩
theorem checked409: cell409.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell410: Row := ⟨28,32,9,4,2,some 12,[test1215],.surface⟩
theorem checked410: cell410.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell411: Row := ⟨28,32,9,4,13,some 16,[test1256],.surface⟩
theorem checked411: cell411.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell412: Row := ⟨28,32,9,4,17,some 28,[test1268],.marked⟩
theorem checked412: cell412.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell413: Row := ⟨28,32,9,4,29,some 64,[test1285],.marked⟩
theorem checked413: cell413.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell414: Row := ⟨28,32,9,4,65,some 128,[test1370],.marked⟩
theorem checked414: cell414.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell415: Row := ⟨28,32,9,4,129,some 256,[test1374],.marked⟩
theorem checked415: cell415.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1123

-- Source: Research6969.HighDispatch3Band2
section Z6969Source1124
set_option autoImplicit true
namespace Research6969.HighDispatch3Band2
open NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem leaf1_513:Done (2:Fin 18) ⟨25,27,9,1,513,none⟩:=entire WholeRows.cell369 WholeRows.checked369
private theorem tail1_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 1 513:=leaf1_513
private theorem leaf1_129:Done (2:Fin 18) ⟨25,27,9,1,129,some 512⟩:=entire WholeRows.cell368 WholeRows.checked368
private theorem tail1_129 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 1 129:=join (leaf1_129) (tail1_513 needed)
private theorem leaf1_0:Done (2:Fin 18) ⟨25,27,9,1,0,some 128⟩:=entire WholeRows.cell367 WholeRows.checked367
private theorem tail1_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 1 0:=join (leaf1_0) (tail1_129 needed)
private theorem leaf2_1025:Done (2:Fin 18) ⟨25,27,9,2,1025,none⟩:=entire WholeRows.cell375 WholeRows.checked375
private theorem tail2_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 1025:=leaf2_1025
private theorem leaf2_257:Done (2:Fin 18) ⟨25,27,9,2,257,some 1024⟩:=entire WholeRows.cell374 WholeRows.checked374
private theorem tail2_257 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 257:=join (leaf2_257) (tail2_1025 needed)
private theorem leaf2_129:Done (2:Fin 18) ⟨25,27,9,2,129,some 256⟩:=entire WholeRows.cell373 WholeRows.checked373
private theorem tail2_129 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 129:=join (leaf2_129) (tail2_257 needed)
private theorem leaf2_49:Done (2:Fin 18) ⟨25,27,9,2,49,some 128⟩:=entire WholeRows.cell372 WholeRows.checked372
private theorem tail2_49 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 49:=join (leaf2_49) (tail2_129 needed)
private theorem leaf2_33:Done (2:Fin 18) ⟨25,27,9,2,33,some 48⟩:=entire WholeRows.cell371 WholeRows.checked371
private theorem tail2_33 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 33:=join (leaf2_33) (tail2_49 needed)
private theorem leaf2_29 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,29,some 32⟩:=needed ⟨20,by decide⟩
private theorem tail2_29 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 29:=join (leaf2_29 needed) (tail2_33 needed)
private theorem leaf2_25 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,25,some 28⟩:=needed ⟨19,by decide⟩
private theorem tail2_25 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 25:=join (leaf2_25 needed) (tail2_29 needed)
private theorem leaf2_23 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,23,some 24⟩:=needed ⟨18,by decide⟩
private theorem tail2_23 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 23:=join (leaf2_23 needed) (tail2_25 needed)
private theorem leaf2_21 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,21,some 22⟩:=needed ⟨17,by decide⟩
private theorem tail2_21 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 21:=join (leaf2_21 needed) (tail2_23 needed)
private theorem leaf2_17 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,17,some 20⟩:=needed ⟨16,by decide⟩
private theorem tail2_17 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 17:=join (leaf2_17 needed) (tail2_21 needed)
private theorem leaf2_13 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,13,some 16⟩:=needed ⟨15,by decide⟩
private theorem tail2_13 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 13:=join (leaf2_13 needed) (tail2_17 needed)
private theorem leaf2_9 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,9,some 12⟩:=needed ⟨14,by decide⟩
private theorem tail2_9 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 9:=join (leaf2_9 needed) (tail2_13 needed)
private theorem leaf2_4 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,2,4,some 8⟩:=needed ⟨13,by decide⟩
private theorem tail2_4 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 4:=join (leaf2_4 needed) (tail2_9 needed)
private theorem leaf2_0:Done (2:Fin 18) ⟨25,27,9,2,0,some 3⟩:=entire WholeRows.cell370 WholeRows.checked370
private theorem tail2_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 0:=join (leaf2_0) (tail2_4 needed)
private theorem leaf3_1025:Done (2:Fin 18) ⟨25,27,9,3,1025,none⟩:=entire WholeRows.cell382 WholeRows.checked382
private theorem tail3_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 1025:=leaf3_1025
private theorem leaf3_513:Done (2:Fin 18) ⟨25,27,9,3,513,some 1024⟩:=entire WholeRows.cell381 WholeRows.checked381
private theorem tail3_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 513:=join (leaf3_513) (tail3_1025 needed)
private theorem leaf3_257:Done (2:Fin 18) ⟨25,27,9,3,257,some 512⟩:=entire WholeRows.cell380 WholeRows.checked380
private theorem tail3_257 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 257:=join (leaf3_257) (tail3_513 needed)
private theorem leaf3_97:Done (2:Fin 18) ⟨25,27,9,3,97,some 256⟩:=entire WholeRows.cell379 WholeRows.checked379
private theorem tail3_97 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 97:=join (leaf3_97) (tail3_257 needed)
private theorem leaf3_33:Done (2:Fin 18) ⟨25,27,9,3,33,some 96⟩:=entire WholeRows.cell378 WholeRows.checked378
private theorem tail3_33 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 33:=join (leaf3_33) (tail3_97 needed)
private theorem leaf3_25:Done (2:Fin 18) ⟨25,27,9,3,25,some 32⟩:=entire WholeRows.cell377 WholeRows.checked377
private theorem tail3_25 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 25:=join (leaf3_25) (tail3_33 needed)
private theorem leaf3_21 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,21,some 24⟩:=needed ⟨29,by decide⟩
private theorem tail3_21 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 21:=join (leaf3_21 needed) (tail3_25 needed)
private theorem leaf3_19 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,19,some 20⟩:=needed ⟨28,by decide⟩
private theorem tail3_19 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 19:=join (leaf3_19 needed) (tail3_21 needed)
private theorem leaf3_18 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,18,some 18⟩:=needed ⟨27,by decide⟩
private theorem tail3_18 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 18:=join (leaf3_18 needed) (tail3_19 needed)
private theorem leaf3_17 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,17,some 17⟩:=needed ⟨26,by decide⟩
private theorem tail3_17 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 17:=join (leaf3_17 needed) (tail3_18 needed)
private theorem leaf3_16 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,16,some 16⟩:=needed ⟨25,by decide⟩
private theorem tail3_16 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 16:=join (leaf3_16 needed) (tail3_17 needed)
private theorem leaf3_15 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,15,some 15⟩:=needed ⟨24,by decide⟩
private theorem tail3_15 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 15:=join (leaf3_15 needed) (tail3_16 needed)
private theorem leaf3_13 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,13,some 14⟩:=needed ⟨23,by decide⟩
private theorem tail3_13 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 13:=join (leaf3_13 needed) (tail3_15 needed)
private theorem leaf3_9 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,9,some 12⟩:=needed ⟨22,by decide⟩
private theorem tail3_9 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 9:=join (leaf3_9 needed) (tail3_13 needed)
private theorem leaf3_4 (needed:HighPendingSeed3.Required):Done (2:Fin 18) ⟨25,27,9,3,4,some 8⟩:=needed ⟨21,by decide⟩
private theorem tail3_4 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 4:=join (leaf3_4 needed) (tail3_9 needed)
private theorem leaf3_0:Done (2:Fin 18) ⟨25,27,9,3,0,some 3⟩:=entire WholeRows.cell376 WholeRows.checked376
private theorem tail3_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 0:=join (leaf3_0) (tail3_4 needed)
private theorem leaf4_2049:Done (2:Fin 18) ⟨25,27,9,4,2049,none⟩:=entire WholeRows.cell389 WholeRows.checked389
private theorem tail4_2049 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 2049:=leaf4_2049
private theorem leaf4_1025:Done (2:Fin 18) ⟨25,27,9,4,1025,some 2048⟩:=power _ 514639 (by decide) PowerReceipts.power38 (by decide) (by decide) (by decide)
private theorem tail4_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 1025:=join (leaf4_1025) (tail4_2049 needed)
private theorem leaf4_513:Done (2:Fin 18) ⟨25,27,9,4,513,some 1024⟩:=entire WholeRows.cell388 WholeRows.checked388
private theorem tail4_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 513:=join (leaf4_513) (tail4_1025 needed)
private theorem leaf4_257:Done (2:Fin 18) ⟨25,27,9,4,257,some 512⟩:=entire WholeRows.cell387 WholeRows.checked387
private theorem tail4_257 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 257:=join (leaf4_257) (tail4_513 needed)
private theorem leaf4_49:Done (2:Fin 18) ⟨25,27,9,4,49,some 256⟩:=entire WholeRows.cell386 WholeRows.checked386
private theorem tail4_49 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 49:=join (leaf4_49) (tail4_257 needed)
private theorem leaf4_13:Done (2:Fin 18) ⟨25,27,9,4,13,some 48⟩:=entire WholeRows.cell385 WholeRows.checked385
private theorem tail4_13 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 13:=join (leaf4_13) (tail4_49 needed)
private theorem leaf4_2:Done (2:Fin 18) ⟨25,27,9,4,2,some 12⟩:=entire WholeRows.cell384 WholeRows.checked384
private theorem tail4_2 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 2:=join (leaf4_2) (tail4_13 needed)
private theorem leaf4_0:Done (2:Fin 18) ⟨25,27,9,4,0,some 1⟩:=entire WholeRows.cell383 WholeRows.checked383
private theorem tail4_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 0:=join (leaf4_0) (tail4_2 needed)
private theorem leaf5_4097:Done (2:Fin 18) ⟨25,27,9,5,4097,none⟩:=entire WholeRows.cell393 WholeRows.checked393
private theorem tail5_4097 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 4097:=leaf5_4097
private theorem leaf5_2049:Done (2:Fin 18) ⟨25,27,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power41 (by decide) (by decide) (by decide)
private theorem tail5_2049 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 2049:=join (leaf5_2049) (tail5_4097 needed)
private theorem leaf5_1025:Done (2:Fin 18) ⟨25,27,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power40 (by decide) (by decide) (by decide)
private theorem tail5_1025 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 1025:=join (leaf5_1025) (tail5_2049 needed)
private theorem leaf5_513:Done (2:Fin 18) ⟨25,27,9,5,513,some 1024⟩:=power _ 643299 (by decide) PowerReceipts.power39 (by decide) (by decide) (by decide)
private theorem tail5_513 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 513:=join (leaf5_513) (tail5_1025 needed)
private theorem leaf5_97:Done (2:Fin 18) ⟨25,27,9,5,97,some 512⟩:=entire WholeRows.cell392 WholeRows.checked392
private theorem tail5_97 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 97:=join (leaf5_97) (tail5_513 needed)
private theorem leaf5_2:Done (2:Fin 18) ⟨25,27,9,5,2,some 96⟩:=entire WholeRows.cell391 WholeRows.checked391
private theorem tail5_2 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 2:=join (leaf5_2) (tail5_97 needed)
private theorem leaf5_0:Done (2:Fin 18) ⟨25,27,9,5,0,some 1⟩:=entire WholeRows.cell390 WholeRows.checked390
private theorem tail5_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 0:=join (leaf5_0) (tail5_2 needed)
theorem allDegrees (needed:HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤5):
    Tail (2:Fin 18) 25 27 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
  · exact tail5_0 needed
end Research6969.HighDispatch3Band2
end Z6969Source1124

-- Source: Research6969.WholeGraphCases013
section Z6969Source1125
set_option autoImplicit true
namespace Research6969.WholeRows
open CertifiedCell
open MeasuredChoices
set_option maxRecDepth 16000
set_option maxHeartbeats 900000
def cell416: Row := ⟨28,32,9,4,257,some 512,[test1375,test1376],.marked⟩
theorem checked416: cell416.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell417: Row := ⟨28,32,9,4,513,some 1024,[test1377,test1378],.marked⟩
theorem checked417: cell417.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell418: Row := ⟨28,32,9,4,1025,none,[test1379],.excluded⟩
theorem checked418: cell418.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell419: Row := ⟨33,40,9,1,0,some 128,[],.affine⟩
theorem checked419: cell419.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell420: Row := ⟨33,40,9,1,129,none,[test12],.excluded⟩
theorem checked420: cell420.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell421: Row := ⟨33,40,9,2,0,some 3,[],.surface⟩
theorem checked421: cell421.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell422: Row := ⟨33,40,9,2,97,some 128,[test88,test89],.marked⟩
theorem checked422: cell422.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell423: Row := ⟨33,40,9,2,129,none,[test91],.excluded⟩
theorem checked423: cell423.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell424: Row := ⟨33,40,9,3,0,some 3,[],.surface⟩
theorem checked424: cell424.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell425: Row := ⟨33,40,9,3,41,some 48,[test1133],.marked⟩
theorem checked425: cell425.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell426: Row := ⟨33,40,9,3,49,some 64,[test1143],.marked⟩
theorem checked426: cell426.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell427: Row := ⟨33,40,9,3,65,some 96,[test1147],.marked⟩
theorem checked427: cell427.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell428: Row := ⟨33,40,9,3,97,some 128,[test1148,test1149],.marked⟩
theorem checked428: cell428.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell429: Row := ⟨33,40,9,3,129,some 256,[test1150,test1151],.marked⟩
theorem checked429: cell429.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell430: Row := ⟨33,40,9,3,257,none,[test1152],.excluded⟩
theorem checked430: cell430.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell431: Row := ⟨33,40,9,4,0,some 1,[],.surface⟩
theorem checked431: cell431.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell432: Row := ⟨33,40,9,4,2,some 12,[test1215],.surface⟩
theorem checked432: cell432.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell433: Row := ⟨33,40,9,4,13,some 16,[test1256],.surface⟩
theorem checked433: cell433.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell434: Row := ⟨33,40,9,4,17,some 20,[test1268],.surface⟩
theorem checked434: cell434.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell435: Row := ⟨33,40,9,4,21,some 24,[test1270],.surface⟩
theorem checked435: cell435.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell436: Row := ⟨33,40,9,4,29,some 32,[test1285],.marked⟩
theorem checked436: cell436.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell437: Row := ⟨33,40,9,4,33,some 48,[test1298],.marked⟩
theorem checked437: cell437.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell438: Row := ⟨33,40,9,4,49,some 96,[test1353],.marked⟩
theorem checked438: cell438.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell439: Row := ⟨33,40,9,4,97,some 128,[test1371,test1372],.marked⟩
theorem checked439: cell439.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell440: Row := ⟨33,40,9,4,129,some 256,[test1373,test1374],.marked⟩
theorem checked440: cell440.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell441: Row := ⟨33,40,9,4,257,none,[test1375],.excluded⟩
theorem checked441: cell441.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell442: Row := ⟨41,49,9,1,0,some 128,[],.affine⟩
theorem checked442: cell442.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell443: Row := ⟨41,49,9,1,129,none,[test12],.excluded⟩
theorem checked443: cell443.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell444: Row := ⟨41,49,9,2,0,some 3,[],.surface⟩
theorem checked444: cell444.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell445: Row := ⟨41,49,9,2,97,none,[test88],.excluded⟩
theorem checked445: cell445.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell446: Row := ⟨41,49,9,3,0,some 3,[],.surface⟩
theorem checked446: cell446.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
def cell447: Row := ⟨41,49,9,3,97,none,[test1148],.excluded⟩
theorem checked447: cell447.check SmallCertificates.primary3 SmallCertificates.rescue3 :=
  FastCell.checked (by decide +kernel)
end Research6969.WholeRows
end Z6969Source1125

-- Source: Research6969.HighDispatch3Band3
section Z6969Source1126
set_option autoImplicit true
namespace Research6969.HighDispatch3Band3
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (2:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell394 checked394) <|
      join (entire cell395 checked395) <|
      entire cell396 checked396
  · exact
      join (entire cell397 checked397) <|
      join (needed ⟨30,by decide⟩) <|
      join (needed ⟨31,by decide⟩) <|
      join (needed ⟨32,by decide⟩) <|
      join (needed ⟨33,by decide⟩) <|
      join (needed ⟨34,by decide⟩) <|
      join (needed ⟨35,by decide⟩) <|
      join (needed ⟨36,by decide⟩) <|
      join (needed ⟨37,by decide⟩) <|
      join (needed ⟨38,by decide⟩) <|
      join (entire cell398 checked398) <|
      join (entire cell399 checked399) <|
      join (entire cell400 checked400) <|
      entire cell401 checked401
  · exact
      join (entire cell402 checked402) <|
      join (needed ⟨39,by decide⟩) <|
      join (needed ⟨40,by decide⟩) <|
      join (needed ⟨41,by decide⟩) <|
      join (needed ⟨42,by decide⟩) <|
      join (needed ⟨43,by decide⟩) <|
      join (needed ⟨44,by decide⟩) <|
      join (needed ⟨45,by decide⟩) <|
      join (needed ⟨46,by decide⟩) <|
      join (needed ⟨47,by decide⟩) <|
      join (needed ⟨48,by decide⟩) <|
      join (needed ⟨49,by decide⟩) <|
      join (needed ⟨50,by decide⟩) <|
      join (needed ⟨51,by decide⟩) <|
      join (entire cell403 checked403) <|
      join (entire cell404 checked404) <|
      join (entire cell405 checked405) <|
      join (entire cell406 checked406) <|
      join (entire cell407 checked407) <|
      entire cell408 checked408
  · exact
      join (entire cell409 checked409) <|
      join (entire cell410 checked410) <|
      join (entire cell411 checked411) <|
      join (entire cell412 checked412) <|
      join (entire cell413 checked413) <|
      join (entire cell414 checked414) <|
      join (entire cell415 checked415) <|
      join (entire cell416 checked416) <|
      join (entire cell417 checked417) <|
      entire cell418 checked418
end Research6969.HighDispatch3Band3
end Z6969Source1126

-- Source: Research6969.HighDispatch3Band4
section Z6969Source1127
set_option autoImplicit true
namespace Research6969.HighDispatch3Band4
open NormalRoute WholeRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false

theorem allDegrees (needed:HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (2:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact
      join (entire cell419 checked419) <|
      entire cell420 checked420
  · exact
      join (entire cell421 checked421) <|
      join (needed ⟨52,by decide⟩) <|
      join (needed ⟨53,by decide⟩) <|
      join (needed ⟨54,by decide⟩) <|
      join (needed ⟨55,by decide⟩) <|
      join (needed ⟨56,by decide⟩) <|
      join (needed ⟨57,by decide⟩) <|
      join (needed ⟨58,by decide⟩) <|
      join (needed ⟨59,by decide⟩) <|
      join (needed ⟨60,by decide⟩) <|
      join (needed ⟨61,by decide⟩) <|
      join (needed ⟨62,by decide⟩) <|
      join (needed ⟨63,by decide⟩) <|
      join (entire cell422 checked422) <|
      entire cell423 checked423
  · exact
      join (entire cell424 checked424) <|
      join (needed ⟨64,by decide⟩) <|
      join (needed ⟨65,by decide⟩) <|
      join (needed ⟨66,by decide⟩) <|
      join (needed ⟨67,by decide⟩) <|
      join (needed ⟨68,by decide⟩) <|
      join (needed ⟨69,by decide⟩) <|
      join (needed ⟨70,by decide⟩) <|
      join (needed ⟨71,by decide⟩) <|
      join (needed ⟨72,by decide⟩) <|
      join (needed ⟨73,by decide⟩) <|
      join (needed ⟨74,by decide⟩) <|
      join (needed ⟨75,by decide⟩) <|
      join (needed ⟨76,by decide⟩) <|
      join (needed ⟨77,by decide⟩) <|
      join (needed ⟨78,by decide⟩) <|
      join (needed ⟨79,by decide⟩) <|
      join (entire cell425 checked425) <|
      join (entire cell426 checked426) <|
      join (entire cell427 checked427) <|
      join (entire cell428 checked428) <|
      join (entire cell429 checked429) <|
      entire cell430 checked430
  · exact
      join (entire cell431 checked431) <|
      join (entire cell432 checked432) <|
      join (entire cell433 checked433) <|
      join (entire cell434 checked434) <|
      join (entire cell435 checked435) <|
      join (needed ⟨80,by decide⟩) <|
      join (entire cell436 checked436) <|
      join (entire cell437 checked437) <|
      join (entire cell438 checked438) <|
      join (entire cell439 checked439) <|
      join (entire cell440 checked440) <|
      entire cell441 checked441
end Research6969.HighDispatch3Band4
end Z6969Source1127
