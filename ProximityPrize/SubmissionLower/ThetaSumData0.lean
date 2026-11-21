import ProximityPrize.SubmissionLower.ThetaSumDefs

/-! Kernel-checked chunks of the theta savings sum (generated; values from the exact ledger). -/

namespace ThetaSum

theorem c1354 : chunk 1354 8 = 109 := by decide +kernel
theorem a1354 : chunk 1354 8 = 109 := c1354
theorem c1362 : chunk 1362 8 = 1224 := by decide +kernel
theorem a1362 : chunk 1354 16 = 1333 := by
  have h := chunk_join a1354 c1362
  exact h
theorem c1370 : chunk 1370 8 = 5564 := by decide +kernel
theorem a1370 : chunk 1354 24 = 6897 := by
  have h := chunk_join a1362 c1370
  exact h
theorem c1378 : chunk 1378 8 = 16713 := by decide +kernel
theorem a1378 : chunk 1354 32 = 23610 := by
  have h := chunk_join a1370 c1378
  exact h
theorem c1386 : chunk 1386 8 = 39620 := by decide +kernel
theorem a1386 : chunk 1354 40 = 63230 := by
  have h := chunk_join a1378 c1386
  exact h
theorem c1394 : chunk 1394 8 = 80600 := by decide +kernel
theorem a1394 : chunk 1354 48 = 143830 := by
  have h := chunk_join a1386 c1394
  exact h
theorem c1402 : chunk 1402 8 = 147333 := by decide +kernel
theorem a1402 : chunk 1354 56 = 291163 := by
  have h := chunk_join a1394 c1402
  exact h
theorem c1410 : chunk 1410 8 = 248864 := by decide +kernel
theorem a1410 : chunk 1354 64 = 540027 := by
  have h := chunk_join a1402 c1410
  exact h
theorem c1418 : chunk 1418 8 = 395604 := by decide +kernel
theorem a1418 : chunk 1354 72 = 935631 := by
  have h := chunk_join a1410 c1418
  exact h
theorem c1426 : chunk 1426 8 = 599329 := by decide +kernel
theorem a1426 : chunk 1354 80 = 1534960 := by
  have h := chunk_join a1418 c1426
  exact h
theorem c1434 : chunk 1434 8 = 873180 := by decide +kernel
theorem a1434 : chunk 1354 88 = 2408140 := by
  have h := chunk_join a1426 c1434
  exact h
theorem c1442 : chunk 1442 8 = 1231664 := by decide +kernel
theorem a1442 : chunk 1354 96 = 3639804 := by
  have h := chunk_join a1434 c1442
  exact h
theorem c1450 : chunk 1450 8 = 1690653 := by decide +kernel
theorem a1450 : chunk 1354 104 = 5330457 := by
  have h := chunk_join a1442 c1450
  exact h
theorem c1458 : chunk 1458 8 = 2267384 := by decide +kernel
theorem a1458 : chunk 1354 112 = 7597841 := by
  have h := chunk_join a1450 c1458
  exact h
theorem c1466 : chunk 1466 8 = 2980460 := by decide +kernel
theorem a1466 : chunk 1354 120 = 10578301 := by
  have h := chunk_join a1458 c1466
  exact h
theorem c1474 : chunk 1474 8 = 3849849 := by decide +kernel
theorem a1474 : chunk 1354 128 = 14428150 := by
  have h := chunk_join a1466 c1474
  exact h
theorem c1482 : chunk 1482 8 = 4896884 := by decide +kernel
theorem a1482 : chunk 1354 136 = 19325034 := by
  have h := chunk_join a1474 c1482
  exact h
theorem c1490 : chunk 1490 8 = 6144264 := by decide +kernel
theorem a1490 : chunk 1354 144 = 25469298 := by
  have h := chunk_join a1482 c1490
  exact h
theorem c1498 : chunk 1498 8 = 7616053 := by decide +kernel
theorem a1498 : chunk 1354 152 = 33085351 := by
  have h := chunk_join a1490 c1498
  exact h
theorem c1506 : chunk 1506 8 = 9337680 := by decide +kernel
theorem a1506 : chunk 1354 160 = 42423031 := by
  have h := chunk_join a1498 c1506
  exact h
theorem c1514 : chunk 1514 8 = 11335940 := by decide +kernel
theorem a1514 : chunk 1354 168 = 53758971 := by
  have h := chunk_join a1506 c1514
  exact h
theorem c1522 : chunk 1522 8 = 13638993 := by decide +kernel
theorem a1522 : chunk 1354 176 = 67397964 := by
  have h := chunk_join a1514 c1522
  exact h
theorem c1530 : chunk 1530 8 = 16276364 := by decide +kernel
theorem a1530 : chunk 1354 184 = 83674328 := by
  have h := chunk_join a1522 c1530
  exact h
theorem c1538 : chunk 1538 8 = 19278944 := by decide +kernel
theorem a1538 : chunk 1354 192 = 102953272 := by
  have h := chunk_join a1530 c1538
  exact h
theorem c1546 : chunk 1546 8 = 22634457 := by decide +kernel
theorem a1546 : chunk 1354 200 = 125587729 := by
  have h := chunk_join a1538 c1546
  exact h
theorem c1554 : chunk 1554 8 = 26255674 := by decide +kernel
theorem a1554 : chunk 1354 208 = 151843403 := by
  have h := chunk_join a1546 c1554
  exact h

theorem part0 : chunk 1354 208 = 151843403 := a1554

end ThetaSum
