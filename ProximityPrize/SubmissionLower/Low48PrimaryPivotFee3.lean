import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3Part528

set_option Elab.async false

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem tail528 : affineFeeChunk w3 528 23 = 1438223176 := by
  exact fee3Part528
private theorem tail504 : affineFeeChunk w3 504 47 = 11375797866 := by
  rw [show 47 = 24+23 by decide, affineFeeChunk_append, fee3Part504]
  change 9937574690 + affineFeeChunk w3 528 23 = 11375797866
  rw [tail528]
private theorem tail480 : affineFeeChunk w3 480 71 = 36403670450 := by
  rw [show 71 = 24+47 by decide, affineFeeChunk_append, fee3Part480]
  change 25027872584 + affineFeeChunk w3 504 47 = 36403670450
  rw [tail504]
private theorem tail456 : affineFeeChunk w3 456 95 = 81069956050 := by
  rw [show 95 = 24+71 by decide, affineFeeChunk_append, fee3Part456]
  change 44666285600 + affineFeeChunk w3 480 71 = 81069956050
  rw [tail480]
private theorem tail432 : affineFeeChunk w3 432 119 = 148478299600 := by
  rw [show 119 = 24+95 by decide, affineFeeChunk_append, fee3Part432]
  change 67408343550 + affineFeeChunk w3 456 95 = 148478299600
  rw [tail456]
private theorem tail408 : affineFeeChunk w3 408 143 = 240933104822 := by
  rw [show 143 = 24+119 by decide, affineFeeChunk_append, fee3Part408]
  change 92454805222 + affineFeeChunk w3 432 119 = 240933104822
  rw [tail432]
private theorem tail384 : affineFeeChunk w3 384 167 = 361001437374 := by
  rw [show 167 = 24+143 by decide, affineFeeChunk_append, fee3Part384]
  change 120068332552 + affineFeeChunk w3 408 143 = 361001437374
  rw [tail408]
private theorem tail360 : affineFeeChunk w3 360 191 = 512198702910 := by
  rw [show 191 = 24+167 by decide, affineFeeChunk_append, fee3Part360]
  change 151197265536 + affineFeeChunk w3 384 167 = 512198702910
  rw [tail384]
private theorem tail336 : affineFeeChunk w3 336 215 = 698584425014 := by
  rw [show 215 = 24+191 by decide, affineFeeChunk_append, fee3Part336]
  change 186385722104 + affineFeeChunk w3 360 191 = 698584425014
  rw [tail360]
private theorem tail312 : affineFeeChunk w3 312 239 = 924349835792 := by
  rw [show 239 = 24+215 by decide, affineFeeChunk_append, fee3Part312]
  change 225765410778 + affineFeeChunk w3 336 215 = 924349835792
  rw [tail336]
private theorem tail288 : affineFeeChunk w3 288 263 = 1193266891858 := by
  rw [show 263 = 24+239 by decide, affineFeeChunk_append, fee3Part288]
  change 268917056066 + affineFeeChunk w3 312 239 = 1193266891858
  rw [tail312]
private theorem tail264 : affineFeeChunk w3 264 287 = 1508620405236 := by
  rw [show 287 = 24+263 by decide, affineFeeChunk_append, fee3Part264]
  change 315353513378 + affineFeeChunk w3 288 263 = 1508620405236
  rw [tail288]
private theorem tail240 : affineFeeChunk w3 240 311 = 1873489837558 := by
  rw [show 311 = 24+287 by decide, affineFeeChunk_append, fee3Part240]
  change 364869432322 + affineFeeChunk w3 264 287 = 1873489837558
  rw [tail264]
private theorem tail216 : affineFeeChunk w3 216 335 = 2290744525656 := by
  rw [show 335 = 24+311 by decide, affineFeeChunk_append, fee3Part216]
  change 417254688098 + affineFeeChunk w3 240 311 = 2290744525656
  rw [tail240]
private theorem tail192 : affineFeeChunk w3 192 359 = 2763037134516 := by
  rw [show 359 = 24+335 by decide, affineFeeChunk_append, fee3Part192]
  change 472292608860 + affineFeeChunk w3 216 335 = 2763037134516
  rw [tail216]
private theorem tail168 : affineFeeChunk w3 168 383 = 3292797110622 := by
  rw [show 383 = 24+359 by decide, affineFeeChunk_append, fee3Part168]
  change 529759976106 + affineFeeChunk w3 192 359 = 3292797110622
  rw [tail192]
private theorem tail144 : affineFeeChunk w3 144 407 = 3882224420624 := by
  rw [show 407 = 24+383 by decide, affineFeeChunk_append, fee3Part144]
  change 589427310002 + affineFeeChunk w3 168 383 = 3882224420624
  rw [tail168]
private theorem tail120 : affineFeeChunk w3 120 431 = 4533286015394 := by
  rw [show 431 = 24+407 by decide, affineFeeChunk_append, fee3Part120]
  change 651061594770 + affineFeeChunk w3 144 407 = 4533286015394
  rw [tail144]
private theorem tail96 : affineFeeChunk w3 96 455 = 5247715723284 := by
  rw [show 455 = 24+431 by decide, affineFeeChunk_append, fee3Part96]
  change 714429707890 + affineFeeChunk w3 120 431 = 5247715723284
  rw [tail120]
private theorem tail72 : affineFeeChunk w3 72 479 = 6027014775552 := by
  rw [show 479 = 24+455 by decide, affineFeeChunk_append, fee3Part72]
  change 779299052268 + affineFeeChunk w3 96 455 = 6027014775552
  rw [tail96]
private theorem tail48 : affineFeeChunk w3 48 503 = 6872452337202 := by
  rw [show 503 = 24+479 by decide, affineFeeChunk_append, fee3Part48]
  change 845437561650 + affineFeeChunk w3 72 479 = 6872452337202
  rw [tail72]
private theorem tail24 : affineFeeChunk w3 24 527 = 7785066037828 := by
  rw [show 527 = 24+503 by decide, affineFeeChunk_append, fee3Part24]
  change 912613700626 + affineFeeChunk w3 48 503 = 7785066037828
  rw [tail48]
theorem affineFeeWindow3 : affineFeeChunk w3 0 551 = 8765662500604 := by
  rw [show 551 = 24+527 by decide, affineFeeChunk_append, fee3Part0]
  change 980596462776 + affineFeeChunk w3 24 527 = 8765662500604
  rw [tail24]

end Low48PrimaryPivot
