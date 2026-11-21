import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2Part528

set_option Elab.async false

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem tail528 : affineFeeChunk w2 528 23 = 5683868184 := by
  exact fee2Part528
private theorem tail504 : affineFeeChunk w2 504 47 = 47996295792 := by
  rw [show 47 = 24+23 by decide, affineFeeChunk_append, fee2Part504]
  change 42312427608 + affineFeeChunk w2 528 23 = 47996295792
  rw [tail528]
private theorem tail480 : affineFeeChunk w2 480 71 = 164883416328 := by
  rw [show 71 = 24+47 by decide, affineFeeChunk_append, fee2Part480]
  change 116887120536 + affineFeeChunk w2 504 47 = 164883416328
  rw [tail504]
private theorem tail456 : affineFeeChunk w2 456 95 = 394291363296 := by
  rw [show 95 = 24+71 by decide, affineFeeChunk_append, fee2Part456]
  change 229407946968 + affineFeeChunk w2 480 71 = 394291363296
  rw [tail480]
private theorem tail432 : affineFeeChunk w2 432 119 = 774159220242 := by
  rw [show 119 = 24+95 by decide, affineFeeChunk_append, fee2Part432]
  change 379867856946 + affineFeeChunk w2 456 95 = 774159220242
  rw [tail456]
private theorem tail408 : affineFeeChunk w2 408 143 = 1340259529350 := by
  rw [show 143 = 24+119 by decide, affineFeeChunk_append, fee2Part408]
  change 566100309108 + affineFeeChunk w2 432 119 = 1340259529350
  rw [tail432]
private theorem tail384 : affineFeeChunk w2 384 167 = 2114183000858 := by
  rw [show 167 = 24+143 by decide, affineFeeChunk_append, fee2Part384]
  change 773923471508 + affineFeeChunk w2 408 143 = 2114183000858
  rw [tail408]
private theorem tail360 : affineFeeChunk w2 360 191 = 3113026817966 := by
  rw [show 191 = 24+167 by decide, affineFeeChunk_append, fee2Part360]
  change 998843817108 + affineFeeChunk w2 384 167 = 3113026817966
  rw [tail384]
private theorem tail336 : affineFeeChunk w2 336 215 = 4349076856002 := by
  rw [show 215 = 24+191 by decide, affineFeeChunk_append, fee2Part336]
  change 1236050038036 + affineFeeChunk w2 360 191 = 4349076856002
  rw [tail360]
private theorem tail312 : affineFeeChunk w2 312 239 = 5830080329174 := by
  rw [show 239 = 24+215 by decide, affineFeeChunk_append, fee2Part312]
  change 1481003473172 + affineFeeChunk w2 336 215 = 5830080329174
  rw [tail336]
private theorem tail288 : affineFeeChunk w2 288 263 = 7560336701964 := by
  rw [show 263 = 24+239 by decide, affineFeeChunk_append, fee2Part288]
  change 1730256372790 + affineFeeChunk w2 312 239 = 7560336701964
  rw [tail312]
private theorem tail264 : affineFeeChunk w2 264 287 = 9541268730298 := by
  rw [show 287 = 24+263 by decide, affineFeeChunk_append, fee2Part264]
  change 1980932028334 + affineFeeChunk w2 288 263 = 9541268730298
  rw [tail288]
private theorem tail240 : affineFeeChunk w2 240 311 = 11772061917920 := by
  rw [show 311 = 24+287 by decide, affineFeeChunk_append, fee2Part240]
  change 2230793187622 + affineFeeChunk w2 264 287 = 11772061917920
  rw [tail264]
private theorem tail216 : affineFeeChunk w2 216 335 = 14250364203726 := by
  rw [show 335 = 24+311 by decide, affineFeeChunk_append, fee2Part216]
  change 2478302285806 + affineFeeChunk w2 240 311 = 14250364203726
  rw [tail240]
private theorem tail192 : affineFeeChunk w2 192 359 = 16972995258420 := by
  rw [show 359 = 24+335 by decide, affineFeeChunk_append, fee2Part192]
  change 2722631054694 + affineFeeChunk w2 216 335 = 16972995258420
  rw [tail216]
private theorem tail168 : affineFeeChunk w2 168 383 = 19936893225640 := by
  rw [show 383 = 24+359 by decide, affineFeeChunk_append, fee2Part168]
  change 2963897967220 + affineFeeChunk w2 192 359 = 19936893225640
  rw [tail192]
private theorem tail144 : affineFeeChunk w2 144 407 = 23140452953310 := by
  rw [show 407 = 24+383 by decide, affineFeeChunk_append, fee2Part144]
  change 3203559727670 + affineFeeChunk w2 168 383 = 23140452953310
  rw [tail168]
private theorem tail120 : affineFeeChunk w2 120 431 = 26583955404588 := by
  rw [show 431 = 24+407 by decide, affineFeeChunk_append, fee2Part120]
  change 3443502451278 + affineFeeChunk w2 144 407 = 26583955404588
  rw [tail144]
private theorem tail96 : affineFeeChunk w2 96 455 = 30269414604178 := by
  rw [show 455 = 24+431 by decide, affineFeeChunk_append, fee2Part96]
  change 3685459199590 + affineFeeChunk w2 120 431 = 30269414604178
  rw [tail120]
private theorem tail72 : affineFeeChunk w2 72 479 = 34200402769680 := by
  rw [show 479 = 24+455 by decide, affineFeeChunk_append, fee2Part72]
  change 3930988165502 + affineFeeChunk w2 96 455 = 34200402769680
  rw [tail96]
private theorem tail48 : affineFeeChunk w2 48 503 = 38382446977410 := by
  rw [show 503 = 24+479 by decide, affineFeeChunk_append, fee2Part48]
  change 4182044207730 + affineFeeChunk w2 72 479 = 38382446977410
  rw [tail72]
private theorem tail24 : affineFeeChunk w2 24 527 = 42824976941068 := by
  rw [show 527 = 24+503 by decide, affineFeeChunk_append, fee2Part24]
  change 4442529963658 + affineFeeChunk w2 48 503 = 42824976941068
  rw [tail48]
theorem affineFeeWindow2 : affineFeeChunk w2 0 551 = 47539326131990 := by
  rw [show 551 = 24+527 by decide, affineFeeChunk_append, fee2Part0]
  change 4714349190922 + affineFeeChunk w2 24 527 = 47539326131990
  rw [tail24]

end Low48PrimaryPivot
