import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_e9774b3fc07c89e3

section Pack_Z6970H2307PackedBand04Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid4_198_0 : (thresholds4_198.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_198.take 5) (by decide +kernel)

private theorem valid4_198_5 : (thresholds4_198.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_198.drop 5) (by decide +kernel)

theorem valid4_198 : thresholds4_198.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_198 5 valid4_198_0 (valid4_198_5)

private theorem valid4_204_0 : (thresholds4_204.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_204.take 5) (by decide +kernel)

private theorem valid4_204_5 : (thresholds4_204.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_204.drop 5) (by decide +kernel)

theorem valid4_204 : thresholds4_204.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_204 5 valid4_204_0 (valid4_204_5)

private theorem valid4_210_0 : (thresholds4_210.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_210.take 4) (by decide +kernel)

private theorem valid4_210_4 : (thresholds4_210.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_210.drop 4) (by decide +kernel)

theorem valid4_210 : thresholds4_210.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_210 4 valid4_210_0 (valid4_210_4)

private theorem valid4_216_0 : (thresholds4_216.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_216.take 4) (by decide +kernel)

private theorem valid4_216_4 : (thresholds4_216.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_216.drop 4) (by decide +kernel)

theorem valid4_216 : thresholds4_216.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_216 4 valid4_216_0 (valid4_216_4)

private theorem valid4_222_0 : (thresholds4_222.take 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_222.take 3) (by decide +kernel)

private theorem valid4_222_3 : (thresholds4_222.drop 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_222.drop 3) (by decide +kernel)

theorem valid4_222 : thresholds4_222.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_222 3 valid4_222_0 (valid4_222_3)

private theorem valid4_228_0 : (thresholds4_228.take 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_228.take 3) (by decide +kernel)

private theorem valid4_228_3 : (thresholds4_228.drop 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_228.drop 3) (by decide +kernel)

theorem valid4_228 : thresholds4_228.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_228 3 valid4_228_0 (valid4_228_3)

private theorem valid4_234_0 : (thresholds4_234.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_234.take 5) (by decide +kernel)

private theorem valid4_234_5 : (thresholds4_234.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_234.drop 5) (by decide +kernel)

theorem valid4_234 : thresholds4_234.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_234 5 valid4_234_0 (valid4_234_5)

private theorem valid4_240_0 : (thresholds4_240.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_240.take 4) (by decide +kernel)

private theorem valid4_240_4 : (thresholds4_240.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_240.drop 4) (by decide +kernel)

theorem valid4_240 : thresholds4_240.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_240 4 valid4_240_0 (valid4_240_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part004

section Pack_Z6970H2307PackedBand04Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid4_246_0 : (thresholds4_246.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_246.take 4) (by decide +kernel)

private theorem valid4_246_4 : (thresholds4_246.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_246.drop 4) (by decide +kernel)

theorem valid4_246 : thresholds4_246.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_246 4 valid4_246_0 (valid4_246_4)

theorem valid4_252 : thresholds4_252.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_252 (by decide +kernel)

private theorem valid4_258_0 : (thresholds4_258.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_258.take 5) (by decide +kernel)

private theorem valid4_258_5 : (thresholds4_258.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_258.drop 5) (by decide +kernel)

theorem valid4_258 : thresholds4_258.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_258 5 valid4_258_0 (valid4_258_5)

private theorem valid4_264_0 : (thresholds4_264.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_264.take 4) (by decide +kernel)

private theorem valid4_264_4 : (thresholds4_264.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_264.drop 4) (by decide +kernel)

theorem valid4_264 : thresholds4_264.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_264 4 valid4_264_0 (valid4_264_4)

theorem valid4_270 : thresholds4_270.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_270 (by decide +kernel)

private theorem valid4_276_0 : (thresholds4_276.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_276.take 5) (by decide +kernel)

private theorem valid4_276_5 : (thresholds4_276.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_276.drop 5) (by decide +kernel)

theorem valid4_276 : thresholds4_276.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_276 5 valid4_276_0 (valid4_276_5)

private theorem valid4_282_0 : (thresholds4_282.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_282.take 5) (by decide +kernel)

private theorem valid4_282_5 : (thresholds4_282.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_282.drop 5) (by decide +kernel)

theorem valid4_282 : thresholds4_282.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_282 5 valid4_282_0 (valid4_282_5)

theorem valid4_288 : thresholds4_288.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_288 (by decide +kernel)

private theorem valid4_294_0 : (thresholds4_294.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_294.take 5) (by decide +kernel)

private theorem valid4_294_5 : (thresholds4_294.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_294.drop 5) (by decide +kernel)

theorem valid4_294 : thresholds4_294.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_294 5 valid4_294_0 (valid4_294_5)

private theorem valid4_300_0 : (thresholds4_300.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_300.take 5) (by decide +kernel)

private theorem valid4_300_5 : (thresholds4_300.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_300.drop 5) (by decide +kernel)

theorem valid4_300 : thresholds4_300.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_300 5 valid4_300_0 (valid4_300_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part005

section Pack_Z6970H2307PackedBand04Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid4_306_0 : (thresholds4_306.take 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_306.take 4) (by decide +kernel)

private theorem valid4_306_4 : (thresholds4_306.drop 4).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_306.drop 4) (by decide +kernel)

theorem valid4_306 : thresholds4_306.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_306 4 valid4_306_0 (valid4_306_4)

private theorem valid4_312_0 : (thresholds4_312.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_312.take 5) (by decide +kernel)

private theorem valid4_312_5 : (thresholds4_312.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_312.drop 5) (by decide +kernel)

theorem valid4_312 : thresholds4_312.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_312 5 valid4_312_0 (valid4_312_5)

private theorem valid4_318_0 : (thresholds4_318.take 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_318.take 3) (by decide +kernel)

private theorem valid4_318_3 : (thresholds4_318.drop 3).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_318.drop 3) (by decide +kernel)

theorem valid4_318 : thresholds4_318.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_318 3 valid4_318_0 (valid4_318_3)

private theorem valid4_324_0 : (thresholds4_324.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_324.take 5) (by decide +kernel)

private theorem valid4_324_5 : (thresholds4_324.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_324.drop 5) (by decide +kernel)

theorem valid4_324 : thresholds4_324.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_324 5 valid4_324_0 (valid4_324_5)

private theorem valid4_330_0 : (thresholds4_330.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_330.take 5) (by decide +kernel)

private theorem valid4_330_5 : (thresholds4_330.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_330.drop 5) (by decide +kernel)

theorem valid4_330 : thresholds4_330.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_330 5 valid4_330_0 (valid4_330_5)

theorem valid4_336 : thresholds4_336.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_336 (by decide +kernel)

theorem valid4_342 : thresholds4_342.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_342 (by decide +kernel)

theorem valid4_348 : thresholds4_348.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_348 (by decide +kernel)

theorem valid4_354 : thresholds4_354.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_354 (by decide +kernel)

theorem valid4_360 : thresholds4_360.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_360 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part006

section Pack_Z6970H2307PackedBand04Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid4_366 : thresholds4_366.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_366 (by decide +kernel)

theorem valid4_372 : thresholds4_372.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_372 (by decide +kernel)

theorem valid4_378 : thresholds4_378.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_378 (by decide +kernel)

theorem valid4_384 : thresholds4_384.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_384 (by decide +kernel)

theorem valid4_390 : thresholds4_390.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_390 (by decide +kernel)

theorem valid4_396 : thresholds4_396.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_396 (by decide +kernel)

theorem valid4_402 : thresholds4_402.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_402 (by decide +kernel)

theorem valid4_408 : thresholds4_408.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_408 (by decide +kernel)

theorem valid4_414 : thresholds4_414.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_414 (by decide +kernel)

theorem valid4_420 : thresholds4_420.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_420 (by decide +kernel)

theorem valid4_426 : thresholds4_426.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_426 (by decide +kernel)

theorem valid4_432 : thresholds4_432.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_432 (by decide +kernel)

theorem valid4_438 : thresholds4_438.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_438 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part007

section Pack_Z6970H2307PackedBand04Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid4_444 : thresholds4_444.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_444 (by decide +kernel)

theorem valid4_450 : thresholds4_450.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_450 (by decide +kernel)

theorem valid4_456 : thresholds4_456.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_456 (by decide +kernel)

theorem valid4_462 : thresholds4_462.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_462 (by decide +kernel)

theorem valid4_468 : thresholds4_468.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_468 (by decide +kernel)

private theorem valid4_474_0 : (thresholds4_474.take 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_474.take 5) (by decide +kernel)

private theorem valid4_474_5 : (thresholds4_474.drop 5).all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 (thresholds4_474.drop 5) (by decide +kernel)

theorem valid4_474 : thresholds4_474.all (checked ⟨4,3,1⟩)=true :=
  all_take_drop (checked ⟨4,3,1⟩) thresholds4_474 5 valid4_474_0 (valid4_474_5)

theorem valid4_480 : thresholds4_480.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_480 (by decide +kernel)

theorem valid4_486 : thresholds4_486.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_486 (by decide +kernel)

theorem valid4_492 : thresholds4_492.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_492 (by decide +kernel)

theorem valid4_498 : thresholds4_498.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_498 (by decide +kernel)

theorem valid4_504 : thresholds4_504.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_504 (by decide +kernel)

theorem valid4_510 : thresholds4_510.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_510 (by decide +kernel)

theorem valid4_516 : thresholds4_516.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_516 (by decide +kernel)

theorem valid4_522 : thresholds4_522.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_522 (by decide +kernel)

theorem valid4_528 : thresholds4_528.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_528 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part008

section Pack_Z6970H2307PackedBand04Part009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid4_534 : thresholds4_534.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_534 (by decide +kernel)

theorem valid4_540 : thresholds4_540.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_540 (by decide +kernel)

theorem valid4_546 : thresholds4_546.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_546 (by decide +kernel)

theorem valid4_552 : thresholds4_552.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_552 (by decide +kernel)

theorem valid4_558 : thresholds4_558.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_558 (by decide +kernel)

theorem valid4_564 : thresholds4_564.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_564 (by decide +kernel)

theorem valid4_570 : thresholds4_570.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_570 (by decide +kernel)

theorem valid4_576 : thresholds4_576.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_576 (by decide +kernel)

theorem valid4_582 : thresholds4_582.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_582 (by decide +kernel)

theorem valid4_588 : thresholds4_588.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_588 (by decide +kernel)

theorem valid4_594 : thresholds4_594.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_594 (by decide +kernel)

theorem valid4_600 : thresholds4_600.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_600 (by decide +kernel)

theorem valid4_606 : thresholds4_606.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_606 (by decide +kernel)

theorem valid4_612 : thresholds4_612.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_612 (by decide +kernel)

theorem valid4_618 : thresholds4_618.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_618 (by decide +kernel)

theorem valid4_624 : thresholds4_624.all (checked ⟨4,3,1⟩)=true :=
  checkedVerified ⟨4,3,1⟩ prefixMap4 thresholds4_624 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand04Part009

section Pack_Z6970H2307PackedBand05Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid5_0_0 : (thresholds5_0.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_0.take 4) (by decide +kernel)

private theorem valid5_0_4 : (thresholds5_0.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_0.drop 4) (by decide +kernel)

theorem valid5_0 : thresholds5_0.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_0 4 valid5_0_0 (valid5_0_4)

theorem valid5_6 : thresholds5_6.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_6 (by decide +kernel)

theorem valid5_12 : thresholds5_12.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_12 (by decide +kernel)

theorem valid5_18 : thresholds5_18.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_18 (by decide +kernel)

private theorem valid5_24_0 : (thresholds5_24.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_24.take 4) (by decide +kernel)

private theorem valid5_24_4 : (thresholds5_24.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_24.drop 4) (by decide +kernel)

theorem valid5_24 : thresholds5_24.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_24 4 valid5_24_0 (valid5_24_4)

theorem valid5_30 : thresholds5_30.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_30 (by decide +kernel)

private theorem valid5_36_0 : (thresholds5_36.take 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_36.take 3) (by decide +kernel)

private theorem valid5_36_3 : (thresholds5_36.drop 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_36.drop 3) (by decide +kernel)

theorem valid5_36 : thresholds5_36.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_36 3 valid5_36_0 (valid5_36_3)

private theorem valid5_42_0 : (thresholds5_42.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_42.take 4) (by decide +kernel)

private theorem valid5_42_4 : (thresholds5_42.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_42.drop 4) (by decide +kernel)

theorem valid5_42 : thresholds5_42.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_42 4 valid5_42_0 (valid5_42_4)

private theorem valid5_48_0 : (thresholds5_48.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_48.take 5) (by decide +kernel)

private theorem valid5_48_5 : (thresholds5_48.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_48.drop 5) (by decide +kernel)

theorem valid5_48 : thresholds5_48.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_48 5 valid5_48_0 (valid5_48_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part000

section Pack_Z6970H2307PackedBand05Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid5_54_0 : (thresholds5_54.take 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_54.take 3) (by decide +kernel)

private theorem valid5_54_3 : (thresholds5_54.drop 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_54.drop 3) (by decide +kernel)

theorem valid5_54 : thresholds5_54.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_54 3 valid5_54_0 (valid5_54_3)

private theorem valid5_60_0 : (thresholds5_60.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_60.take 4) (by decide +kernel)

private theorem valid5_60_4 : (thresholds5_60.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_60.drop 4) (by decide +kernel)

theorem valid5_60 : thresholds5_60.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_60 4 valid5_60_0 (valid5_60_4)

private theorem valid5_66_0 : (thresholds5_66.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_66.take 4) (by decide +kernel)

private theorem valid5_66_4 : (thresholds5_66.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_66.drop 4) (by decide +kernel)

theorem valid5_66 : thresholds5_66.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_66 4 valid5_66_0 (valid5_66_4)

private theorem valid5_72_0 : (thresholds5_72.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_72.take 5) (by decide +kernel)

private theorem valid5_72_5 : (thresholds5_72.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_72.drop 5) (by decide +kernel)

theorem valid5_72 : thresholds5_72.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_72 5 valid5_72_0 (valid5_72_5)

private theorem valid5_78_0 : (thresholds5_78.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_78.take 4) (by decide +kernel)

private theorem valid5_78_4 : (thresholds5_78.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_78.drop 4) (by decide +kernel)

theorem valid5_78 : thresholds5_78.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_78 4 valid5_78_0 (valid5_78_4)

private theorem valid5_84_0 : (thresholds5_84.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_84.take 4) (by decide +kernel)

private theorem valid5_84_4 : (thresholds5_84.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_84.drop 4) (by decide +kernel)

theorem valid5_84 : thresholds5_84.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_84 4 valid5_84_0 (valid5_84_4)

private theorem valid5_90_0 : (thresholds5_90.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_90.take 5) (by decide +kernel)

private theorem valid5_90_5 : (thresholds5_90.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_90.drop 5) (by decide +kernel)

theorem valid5_90 : thresholds5_90.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_90 5 valid5_90_0 (valid5_90_5)

private theorem valid5_96_0 : (thresholds5_96.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_96.take 4) (by decide +kernel)

private theorem valid5_96_4 : (thresholds5_96.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_96.drop 4) (by decide +kernel)

theorem valid5_96 : thresholds5_96.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_96 4 valid5_96_0 (valid5_96_4)

private theorem valid5_102_0 : (thresholds5_102.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_102.take 4) (by decide +kernel)

private theorem valid5_102_4 : (thresholds5_102.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_102.drop 4) (by decide +kernel)

theorem valid5_102 : thresholds5_102.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_102 4 valid5_102_0 (valid5_102_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part001

section Pack_Z6970H2307PackedBand05Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid5_108_0 : (thresholds5_108.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_108.take 5) (by decide +kernel)

private theorem valid5_108_5 : (thresholds5_108.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_108.drop 5) (by decide +kernel)

theorem valid5_108 : thresholds5_108.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_108 5 valid5_108_0 (valid5_108_5)

private theorem valid5_114_0 : (thresholds5_114.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_114.take 4) (by decide +kernel)

private theorem valid5_114_4 : (thresholds5_114.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_114.drop 4) (by decide +kernel)

theorem valid5_114 : thresholds5_114.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_114 4 valid5_114_0 (valid5_114_4)

theorem valid5_120 : thresholds5_120.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_120 (by decide +kernel)

private theorem valid5_126_0 : (thresholds5_126.take 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_126.take 3) (by decide +kernel)

private theorem valid5_126_3 : (thresholds5_126.drop 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_126.drop 3) (by decide +kernel)

theorem valid5_126 : thresholds5_126.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_126 3 valid5_126_0 (valid5_126_3)

private theorem valid5_132_0 : (thresholds5_132.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_132.take 5) (by decide +kernel)

private theorem valid5_132_5 : (thresholds5_132.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_132.drop 5) (by decide +kernel)

theorem valid5_132 : thresholds5_132.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_132 5 valid5_132_0 (valid5_132_5)

private theorem valid5_138_0 : (thresholds5_138.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_138.take 4) (by decide +kernel)

private theorem valid5_138_4 : (thresholds5_138.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_138.drop 4) (by decide +kernel)

theorem valid5_138 : thresholds5_138.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_138 4 valid5_138_0 (valid5_138_4)

private theorem valid5_144_0 : (thresholds5_144.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_144.take 4) (by decide +kernel)

private theorem valid5_144_4 : (thresholds5_144.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_144.drop 4) (by decide +kernel)

theorem valid5_144 : thresholds5_144.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_144 4 valid5_144_0 (valid5_144_4)

private theorem valid5_150_0 : (thresholds5_150.take 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_150.take 3) (by decide +kernel)

private theorem valid5_150_3 : (thresholds5_150.drop 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_150.drop 3) (by decide +kernel)

theorem valid5_150 : thresholds5_150.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_150 3 valid5_150_0 (valid5_150_3)

private theorem valid5_156_0 : (thresholds5_156.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_156.take 4) (by decide +kernel)

private theorem valid5_156_4 : (thresholds5_156.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_156.drop 4) (by decide +kernel)

theorem valid5_156 : thresholds5_156.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_156 4 valid5_156_0 (valid5_156_4)

private theorem valid5_162_0 : (thresholds5_162.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_162.take 5) (by decide +kernel)

private theorem valid5_162_5 : (thresholds5_162.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_162.drop 5) (by decide +kernel)

theorem valid5_162 : thresholds5_162.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_162 5 valid5_162_0 (valid5_162_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part002

section Pack_Z6970H2307PackedBand05Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid5_168_0 : (thresholds5_168.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_168.take 5) (by decide +kernel)

private theorem valid5_168_5 : (thresholds5_168.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_168.drop 5) (by decide +kernel)

theorem valid5_168 : thresholds5_168.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_168 5 valid5_168_0 (valid5_168_5)

private theorem valid5_174_0 : (thresholds5_174.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_174.take 5) (by decide +kernel)

private theorem valid5_174_5 : (thresholds5_174.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_174.drop 5) (by decide +kernel)

theorem valid5_174 : thresholds5_174.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_174 5 valid5_174_0 (valid5_174_5)

private theorem valid5_180_0 : (thresholds5_180.take 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_180.take 3) (by decide +kernel)

private theorem valid5_180_3 : (thresholds5_180.drop 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_180.drop 3) (by decide +kernel)

theorem valid5_180 : thresholds5_180.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_180 3 valid5_180_0 (valid5_180_3)

private theorem valid5_186_0 : (thresholds5_186.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_186.take 5) (by decide +kernel)

private theorem valid5_186_5 : (thresholds5_186.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_186.drop 5) (by decide +kernel)

theorem valid5_186 : thresholds5_186.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_186 5 valid5_186_0 (valid5_186_5)

private theorem valid5_192_0 : (thresholds5_192.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_192.take 5) (by decide +kernel)

private theorem valid5_192_5 : (thresholds5_192.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_192.drop 5) (by decide +kernel)

theorem valid5_192 : thresholds5_192.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_192 5 valid5_192_0 (valid5_192_5)

private theorem valid5_198_0 : (thresholds5_198.take 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_198.take 3) (by decide +kernel)

private theorem valid5_198_3 : ((thresholds5_198.drop 3).take 1).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 ((thresholds5_198.drop 3).take 1) (by decide +kernel)

private theorem valid5_198_4 : (thresholds5_198.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_198.drop 4) (by decide +kernel)

theorem valid5_198 : thresholds5_198.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_198 3 valid5_198_0 (all_take_drop (checked ⟨5,3,1⟩) (thresholds5_198.drop 3) 1 valid5_198_3 (valid5_198_4))

private theorem valid5_204_0 : (thresholds5_204.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_204.take 5) (by decide +kernel)

private theorem valid5_204_5 : (thresholds5_204.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_204.drop 5) (by decide +kernel)

theorem valid5_204 : thresholds5_204.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_204 5 valid5_204_0 (valid5_204_5)

private theorem valid5_210_0 : (thresholds5_210.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_210.take 5) (by decide +kernel)

private theorem valid5_210_5 : (thresholds5_210.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_210.drop 5) (by decide +kernel)

theorem valid5_210 : thresholds5_210.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_210 5 valid5_210_0 (valid5_210_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part003

section Pack_Z6970H2307PackedBand05Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid5_216_0 : (thresholds5_216.take 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_216.take 3) (by decide +kernel)

private theorem valid5_216_3 : (thresholds5_216.drop 3).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_216.drop 3) (by decide +kernel)

theorem valid5_216 : thresholds5_216.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_216 3 valid5_216_0 (valid5_216_3)

private theorem valid5_222_0 : (thresholds5_222.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_222.take 5) (by decide +kernel)

private theorem valid5_222_5 : (thresholds5_222.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_222.drop 5) (by decide +kernel)

theorem valid5_222 : thresholds5_222.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_222 5 valid5_222_0 (valid5_222_5)

private theorem valid5_228_0 : (thresholds5_228.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_228.take 5) (by decide +kernel)

private theorem valid5_228_5 : (thresholds5_228.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_228.drop 5) (by decide +kernel)

theorem valid5_228 : thresholds5_228.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_228 5 valid5_228_0 (valid5_228_5)

theorem valid5_234 : thresholds5_234.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_234 (by decide +kernel)

private theorem valid5_240_0 : (thresholds5_240.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_240.take 4) (by decide +kernel)

private theorem valid5_240_4 : (thresholds5_240.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_240.drop 4) (by decide +kernel)

theorem valid5_240 : thresholds5_240.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_240 4 valid5_240_0 (valid5_240_4)

theorem valid5_246 : thresholds5_246.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_246 (by decide +kernel)

theorem valid5_252 : thresholds5_252.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_252 (by decide +kernel)

private theorem valid5_258_0 : (thresholds5_258.take 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_258.take 4) (by decide +kernel)

private theorem valid5_258_4 : (thresholds5_258.drop 4).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_258.drop 4) (by decide +kernel)

theorem valid5_258 : thresholds5_258.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_258 4 valid5_258_0 (valid5_258_4)

private theorem valid5_264_0 : (thresholds5_264.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_264.take 5) (by decide +kernel)

private theorem valid5_264_5 : (thresholds5_264.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_264.drop 5) (by decide +kernel)

theorem valid5_264 : thresholds5_264.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_264 5 valid5_264_0 (valid5_264_5)

theorem valid5_270 : thresholds5_270.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_270 (by decide +kernel)

private theorem valid5_276_0 : (thresholds5_276.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_276.take 5) (by decide +kernel)

private theorem valid5_276_5 : (thresholds5_276.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_276.drop 5) (by decide +kernel)

theorem valid5_276 : thresholds5_276.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_276 5 valid5_276_0 (valid5_276_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part004

section Pack_Z6970H2307PackedBand05Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid5_282 : thresholds5_282.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_282 (by decide +kernel)

private theorem valid5_288_0 : (thresholds5_288.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_288.take 5) (by decide +kernel)

private theorem valid5_288_5 : (thresholds5_288.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_288.drop 5) (by decide +kernel)

theorem valid5_288 : thresholds5_288.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_288 5 valid5_288_0 (valid5_288_5)

private theorem valid5_294_0 : (thresholds5_294.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_294.take 5) (by decide +kernel)

private theorem valid5_294_5 : (thresholds5_294.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_294.drop 5) (by decide +kernel)

theorem valid5_294 : thresholds5_294.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_294 5 valid5_294_0 (valid5_294_5)

theorem valid5_300 : thresholds5_300.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_300 (by decide +kernel)

theorem valid5_306 : thresholds5_306.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_306 (by decide +kernel)

private theorem valid5_312_0 : (thresholds5_312.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_312.take 5) (by decide +kernel)

private theorem valid5_312_5 : (thresholds5_312.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_312.drop 5) (by decide +kernel)

theorem valid5_312 : thresholds5_312.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_312 5 valid5_312_0 (valid5_312_5)

theorem valid5_318 : thresholds5_318.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_318 (by decide +kernel)

theorem valid5_324 : thresholds5_324.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_324 (by decide +kernel)

theorem valid5_330 : thresholds5_330.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_330 (by decide +kernel)

theorem valid5_336 : thresholds5_336.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_336 (by decide +kernel)

theorem valid5_342 : thresholds5_342.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_342 (by decide +kernel)

theorem valid5_348 : thresholds5_348.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_348 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part005

section Pack_Z6970H2307PackedBand05Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid5_354 : thresholds5_354.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_354 (by decide +kernel)

theorem valid5_360 : thresholds5_360.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_360 (by decide +kernel)

theorem valid5_366 : thresholds5_366.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_366 (by decide +kernel)

theorem valid5_372 : thresholds5_372.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_372 (by decide +kernel)

theorem valid5_378 : thresholds5_378.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_378 (by decide +kernel)

private theorem valid5_384_0 : (thresholds5_384.take 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_384.take 5) (by decide +kernel)

private theorem valid5_384_5 : (thresholds5_384.drop 5).all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 (thresholds5_384.drop 5) (by decide +kernel)

theorem valid5_384 : thresholds5_384.all (checked ⟨5,3,1⟩)=true :=
  all_take_drop (checked ⟨5,3,1⟩) thresholds5_384 5 valid5_384_0 (valid5_384_5)

theorem valid5_390 : thresholds5_390.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_390 (by decide +kernel)

theorem valid5_396 : thresholds5_396.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_396 (by decide +kernel)

theorem valid5_402 : thresholds5_402.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_402 (by decide +kernel)

theorem valid5_408 : thresholds5_408.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_408 (by decide +kernel)

theorem valid5_414 : thresholds5_414.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_414 (by decide +kernel)

theorem valid5_420 : thresholds5_420.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_420 (by decide +kernel)

theorem valid5_426 : thresholds5_426.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_426 (by decide +kernel)

theorem valid5_432 : thresholds5_432.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_432 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part006

section Pack_Z6970H2307PackedBand05Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid5_438 : thresholds5_438.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_438 (by decide +kernel)

theorem valid5_444 : thresholds5_444.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_444 (by decide +kernel)

theorem valid5_450 : thresholds5_450.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_450 (by decide +kernel)

theorem valid5_456 : thresholds5_456.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_456 (by decide +kernel)

theorem valid5_462 : thresholds5_462.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_462 (by decide +kernel)

theorem valid5_468 : thresholds5_468.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_468 (by decide +kernel)

theorem valid5_474 : thresholds5_474.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_474 (by decide +kernel)

theorem valid5_480 : thresholds5_480.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_480 (by decide +kernel)

theorem valid5_486 : thresholds5_486.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_486 (by decide +kernel)

theorem valid5_492 : thresholds5_492.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_492 (by decide +kernel)

theorem valid5_498 : thresholds5_498.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_498 (by decide +kernel)

theorem valid5_504 : thresholds5_504.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_504 (by decide +kernel)

theorem valid5_510 : thresholds5_510.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_510 (by decide +kernel)

theorem valid5_516 : thresholds5_516.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_516 (by decide +kernel)

theorem valid5_522 : thresholds5_522.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_522 (by decide +kernel)

theorem valid5_528 : thresholds5_528.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_528 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part007

section Pack_Z6970H2307PackedBand05Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid5_534 : thresholds5_534.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_534 (by decide +kernel)

theorem valid5_540 : thresholds5_540.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_540 (by decide +kernel)

theorem valid5_546 : thresholds5_546.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_546 (by decide +kernel)

theorem valid5_552 : thresholds5_552.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_552 (by decide +kernel)

theorem valid5_558 : thresholds5_558.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_558 (by decide +kernel)

theorem valid5_564 : thresholds5_564.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_564 (by decide +kernel)

theorem valid5_570 : thresholds5_570.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_570 (by decide +kernel)

theorem valid5_576 : thresholds5_576.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_576 (by decide +kernel)

theorem valid5_582 : thresholds5_582.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_582 (by decide +kernel)

theorem valid5_588 : thresholds5_588.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_588 (by decide +kernel)

theorem valid5_594 : thresholds5_594.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_594 (by decide +kernel)

theorem valid5_600 : thresholds5_600.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_600 (by decide +kernel)

theorem valid5_606 : thresholds5_606.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_606 (by decide +kernel)

theorem valid5_612 : thresholds5_612.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_612 (by decide +kernel)

theorem valid5_618 : thresholds5_618.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_618 (by decide +kernel)

theorem valid5_624 : thresholds5_624.all (checked ⟨5,3,1⟩)=true :=
  checkedVerified ⟨5,3,1⟩ prefixMap5 thresholds5_624 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand05Part008

section Pack_Z6970H2307PackedBand06Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid6_0_0 : (thresholds6_0.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_0.take 4) (by decide +kernel)

private theorem valid6_0_4 : (thresholds6_0.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_0.drop 4) (by decide +kernel)

theorem valid6_0 : thresholds6_0.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_0 4 valid6_0_0 (valid6_0_4)

theorem valid6_6 : thresholds6_6.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_6 (by decide +kernel)

theorem valid6_12 : thresholds6_12.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_12 (by decide +kernel)

theorem valid6_18 : thresholds6_18.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_18 (by decide +kernel)

theorem valid6_24 : thresholds6_24.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_24 (by decide +kernel)

private theorem valid6_30_0 : (thresholds6_30.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_30.take 4) (by decide +kernel)

private theorem valid6_30_4 : (thresholds6_30.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_30.drop 4) (by decide +kernel)

theorem valid6_30 : thresholds6_30.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_30 4 valid6_30_0 (valid6_30_4)

private theorem valid6_36_0 : (thresholds6_36.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_36.take 5) (by decide +kernel)

private theorem valid6_36_5 : (thresholds6_36.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_36.drop 5) (by decide +kernel)

theorem valid6_36 : thresholds6_36.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_36 5 valid6_36_0 (valid6_36_5)

private theorem valid6_42_0 : (thresholds6_42.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_42.take 4) (by decide +kernel)

private theorem valid6_42_4 : (thresholds6_42.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_42.drop 4) (by decide +kernel)

theorem valid6_42 : thresholds6_42.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_42 4 valid6_42_0 (valid6_42_4)

private theorem valid6_48_0 : (thresholds6_48.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_48.take 4) (by decide +kernel)

private theorem valid6_48_4 : (thresholds6_48.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_48.drop 4) (by decide +kernel)

theorem valid6_48 : thresholds6_48.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_48 4 valid6_48_0 (valid6_48_4)

private theorem valid6_54_0 : (thresholds6_54.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_54.take 4) (by decide +kernel)

private theorem valid6_54_4 : (thresholds6_54.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_54.drop 4) (by decide +kernel)

theorem valid6_54 : thresholds6_54.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_54 4 valid6_54_0 (valid6_54_4)

private theorem valid6_60_0 : (thresholds6_60.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_60.take 4) (by decide +kernel)

private theorem valid6_60_4 : (thresholds6_60.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_60.drop 4) (by decide +kernel)

theorem valid6_60 : thresholds6_60.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_60 4 valid6_60_0 (valid6_60_4)

private theorem valid6_66_0 : (thresholds6_66.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_66.take 4) (by decide +kernel)

private theorem valid6_66_4 : (thresholds6_66.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_66.drop 4) (by decide +kernel)

theorem valid6_66 : thresholds6_66.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_66 4 valid6_66_0 (valid6_66_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part000

section Pack_Z6970H2307PackedBand06Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid6_72_0 : (thresholds6_72.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_72.take 4) (by decide +kernel)

private theorem valid6_72_4 : (thresholds6_72.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_72.drop 4) (by decide +kernel)

theorem valid6_72 : thresholds6_72.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_72 4 valid6_72_0 (valid6_72_4)

theorem valid6_78 : thresholds6_78.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_78 (by decide +kernel)

private theorem valid6_84_0 : (thresholds6_84.take 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_84.take 3) (by decide +kernel)

private theorem valid6_84_3 : (thresholds6_84.drop 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_84.drop 3) (by decide +kernel)

theorem valid6_84 : thresholds6_84.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_84 3 valid6_84_0 (valid6_84_3)

private theorem valid6_90_0 : (thresholds6_90.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_90.take 4) (by decide +kernel)

private theorem valid6_90_4 : (thresholds6_90.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_90.drop 4) (by decide +kernel)

theorem valid6_90 : thresholds6_90.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_90 4 valid6_90_0 (valid6_90_4)

private theorem valid6_96_0 : (thresholds6_96.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_96.take 4) (by decide +kernel)

private theorem valid6_96_4 : (thresholds6_96.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_96.drop 4) (by decide +kernel)

theorem valid6_96 : thresholds6_96.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_96 4 valid6_96_0 (valid6_96_4)

private theorem valid6_102_0 : (thresholds6_102.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_102.take 4) (by decide +kernel)

private theorem valid6_102_4 : (thresholds6_102.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_102.drop 4) (by decide +kernel)

theorem valid6_102 : thresholds6_102.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_102 4 valid6_102_0 (valid6_102_4)

theorem valid6_108 : thresholds6_108.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_108 (by decide +kernel)

private theorem valid6_114_0 : (thresholds6_114.take 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_114.take 3) (by decide +kernel)

private theorem valid6_114_3 : (thresholds6_114.drop 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_114.drop 3) (by decide +kernel)

theorem valid6_114 : thresholds6_114.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_114 3 valid6_114_0 (valid6_114_3)

private theorem valid6_120_0 : (thresholds6_120.take 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_120.take 3) (by decide +kernel)

private theorem valid6_120_3 : (thresholds6_120.drop 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_120.drop 3) (by decide +kernel)

theorem valid6_120 : thresholds6_120.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_120 3 valid6_120_0 (valid6_120_3)

private theorem valid6_126_0 : (thresholds6_126.take 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_126.take 3) (by decide +kernel)

private theorem valid6_126_3 : (thresholds6_126.drop 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_126.drop 3) (by decide +kernel)

theorem valid6_126 : thresholds6_126.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_126 3 valid6_126_0 (valid6_126_3)

private theorem valid6_132_0 : (thresholds6_132.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_132.take 4) (by decide +kernel)

private theorem valid6_132_4 : (thresholds6_132.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_132.drop 4) (by decide +kernel)

theorem valid6_132 : thresholds6_132.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_132 4 valid6_132_0 (valid6_132_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part001

section Pack_Z6970H2307PackedBand06Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid6_138 : thresholds6_138.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_138 (by decide +kernel)

private theorem valid6_144_0 : (thresholds6_144.take 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_144.take 3) (by decide +kernel)

private theorem valid6_144_3 : (thresholds6_144.drop 3).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_144.drop 3) (by decide +kernel)

theorem valid6_144 : thresholds6_144.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_144 3 valid6_144_0 (valid6_144_3)

private theorem valid6_150_0 : (thresholds6_150.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_150.take 5) (by decide +kernel)

private theorem valid6_150_5 : (thresholds6_150.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_150.drop 5) (by decide +kernel)

theorem valid6_150 : thresholds6_150.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_150 5 valid6_150_0 (valid6_150_5)

private theorem valid6_156_0 : (thresholds6_156.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_156.take 5) (by decide +kernel)

private theorem valid6_156_5 : (thresholds6_156.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_156.drop 5) (by decide +kernel)

theorem valid6_156 : thresholds6_156.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_156 5 valid6_156_0 (valid6_156_5)

private theorem valid6_162_0 : (thresholds6_162.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_162.take 4) (by decide +kernel)

private theorem valid6_162_4 : (thresholds6_162.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_162.drop 4) (by decide +kernel)

theorem valid6_162 : thresholds6_162.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_162 4 valid6_162_0 (valid6_162_4)

private theorem valid6_168_0 : (thresholds6_168.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_168.take 4) (by decide +kernel)

private theorem valid6_168_4 : (thresholds6_168.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_168.drop 4) (by decide +kernel)

theorem valid6_168 : thresholds6_168.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_168 4 valid6_168_0 (valid6_168_4)

private theorem valid6_174_0 : (thresholds6_174.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_174.take 4) (by decide +kernel)

private theorem valid6_174_4 : (thresholds6_174.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_174.drop 4) (by decide +kernel)

theorem valid6_174 : thresholds6_174.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_174 4 valid6_174_0 (valid6_174_4)

theorem valid6_180 : thresholds6_180.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_180 (by decide +kernel)

private theorem valid6_186_0 : (thresholds6_186.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_186.take 5) (by decide +kernel)

private theorem valid6_186_5 : (thresholds6_186.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_186.drop 5) (by decide +kernel)

theorem valid6_186 : thresholds6_186.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_186 5 valid6_186_0 (valid6_186_5)

private theorem valid6_192_0 : (thresholds6_192.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_192.take 4) (by decide +kernel)

private theorem valid6_192_4 : (thresholds6_192.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_192.drop 4) (by decide +kernel)

theorem valid6_192 : thresholds6_192.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_192 4 valid6_192_0 (valid6_192_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part002

section Pack_Z6970H2307PackedBand06Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid6_198_0 : (thresholds6_198.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_198.take 4) (by decide +kernel)

private theorem valid6_198_4 : (thresholds6_198.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_198.drop 4) (by decide +kernel)

theorem valid6_198 : thresholds6_198.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_198 4 valid6_198_0 (valid6_198_4)

private theorem valid6_204_0 : (thresholds6_204.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_204.take 5) (by decide +kernel)

private theorem valid6_204_5 : (thresholds6_204.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_204.drop 5) (by decide +kernel)

theorem valid6_204 : thresholds6_204.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_204 5 valid6_204_0 (valid6_204_5)

private theorem valid6_210_0 : (thresholds6_210.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_210.take 5) (by decide +kernel)

private theorem valid6_210_5 : (thresholds6_210.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_210.drop 5) (by decide +kernel)

theorem valid6_210 : thresholds6_210.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_210 5 valid6_210_0 (valid6_210_5)

private theorem valid6_216_0 : (thresholds6_216.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_216.take 4) (by decide +kernel)

private theorem valid6_216_4 : (thresholds6_216.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_216.drop 4) (by decide +kernel)

theorem valid6_216 : thresholds6_216.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_216 4 valid6_216_0 (valid6_216_4)

private theorem valid6_222_0 : (thresholds6_222.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_222.take 5) (by decide +kernel)

private theorem valid6_222_5 : (thresholds6_222.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_222.drop 5) (by decide +kernel)

theorem valid6_222 : thresholds6_222.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_222 5 valid6_222_0 (valid6_222_5)

private theorem valid6_228_0 : (thresholds6_228.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_228.take 5) (by decide +kernel)

private theorem valid6_228_5 : (thresholds6_228.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_228.drop 5) (by decide +kernel)

theorem valid6_228 : thresholds6_228.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_228 5 valid6_228_0 (valid6_228_5)

private theorem valid6_234_0 : (thresholds6_234.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_234.take 5) (by decide +kernel)

private theorem valid6_234_5 : (thresholds6_234.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_234.drop 5) (by decide +kernel)

theorem valid6_234 : thresholds6_234.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_234 5 valid6_234_0 (valid6_234_5)

theorem valid6_240 : thresholds6_240.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_240 (by decide +kernel)

theorem valid6_246 : thresholds6_246.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_246 (by decide +kernel)

private theorem valid6_252_0 : (thresholds6_252.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_252.take 4) (by decide +kernel)

private theorem valid6_252_4 : (thresholds6_252.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_252.drop 4) (by decide +kernel)

theorem valid6_252 : thresholds6_252.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_252 4 valid6_252_0 (valid6_252_4)

private theorem valid6_258_0 : (thresholds6_258.take 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_258.take 4) (by decide +kernel)

private theorem valid6_258_4 : (thresholds6_258.drop 4).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_258.drop 4) (by decide +kernel)

theorem valid6_258 : thresholds6_258.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_258 4 valid6_258_0 (valid6_258_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part003

section Pack_Z6970H2307PackedBand06Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid6_264 : thresholds6_264.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_264 (by decide +kernel)

private theorem valid6_270_0 : (thresholds6_270.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_270.take 5) (by decide +kernel)

private theorem valid6_270_5 : (thresholds6_270.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_270.drop 5) (by decide +kernel)

theorem valid6_270 : thresholds6_270.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_270 5 valid6_270_0 (valid6_270_5)

private theorem valid6_276_0 : (thresholds6_276.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_276.take 5) (by decide +kernel)

private theorem valid6_276_5 : (thresholds6_276.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_276.drop 5) (by decide +kernel)

theorem valid6_276 : thresholds6_276.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_276 5 valid6_276_0 (valid6_276_5)

theorem valid6_282 : thresholds6_282.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_282 (by decide +kernel)

theorem valid6_288 : thresholds6_288.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_288 (by decide +kernel)

private theorem valid6_294_0 : (thresholds6_294.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_294.take 5) (by decide +kernel)

private theorem valid6_294_5 : (thresholds6_294.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_294.drop 5) (by decide +kernel)

theorem valid6_294 : thresholds6_294.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_294 5 valid6_294_0 (valid6_294_5)

theorem valid6_300 : thresholds6_300.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_300 (by decide +kernel)

theorem valid6_306 : thresholds6_306.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_306 (by decide +kernel)

theorem valid6_312 : thresholds6_312.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_312 (by decide +kernel)

private theorem valid6_318_0 : (thresholds6_318.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_318.take 5) (by decide +kernel)

private theorem valid6_318_5 : (thresholds6_318.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_318.drop 5) (by decide +kernel)

theorem valid6_318 : thresholds6_318.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_318 5 valid6_318_0 (valid6_318_5)

theorem valid6_324 : thresholds6_324.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_324 (by decide +kernel)

theorem valid6_330 : thresholds6_330.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_330 (by decide +kernel)

theorem valid6_336 : thresholds6_336.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_336 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part004

section Pack_Z6970H2307PackedBand06Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid6_342 : thresholds6_342.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_342 (by decide +kernel)

private theorem valid6_348_0 : (thresholds6_348.take 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_348.take 5) (by decide +kernel)

private theorem valid6_348_5 : (thresholds6_348.drop 5).all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 (thresholds6_348.drop 5) (by decide +kernel)

theorem valid6_348 : thresholds6_348.all (checked ⟨6,3,1⟩)=true :=
  all_take_drop (checked ⟨6,3,1⟩) thresholds6_348 5 valid6_348_0 (valid6_348_5)

theorem valid6_354 : thresholds6_354.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_354 (by decide +kernel)

theorem valid6_360 : thresholds6_360.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_360 (by decide +kernel)

theorem valid6_366 : thresholds6_366.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_366 (by decide +kernel)

theorem valid6_372 : thresholds6_372.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_372 (by decide +kernel)

theorem valid6_378 : thresholds6_378.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_378 (by decide +kernel)

theorem valid6_384 : thresholds6_384.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_384 (by decide +kernel)

theorem valid6_390 : thresholds6_390.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_390 (by decide +kernel)

theorem valid6_396 : thresholds6_396.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_396 (by decide +kernel)

theorem valid6_402 : thresholds6_402.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_402 (by decide +kernel)

theorem valid6_408 : thresholds6_408.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_408 (by decide +kernel)

theorem valid6_414 : thresholds6_414.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_414 (by decide +kernel)

theorem valid6_420 : thresholds6_420.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_420 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part005

section Pack_Z6970H2307PackedBand06Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid6_426 : thresholds6_426.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_426 (by decide +kernel)

theorem valid6_432 : thresholds6_432.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_432 (by decide +kernel)

theorem valid6_438 : thresholds6_438.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_438 (by decide +kernel)

theorem valid6_444 : thresholds6_444.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_444 (by decide +kernel)

theorem valid6_450 : thresholds6_450.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_450 (by decide +kernel)

theorem valid6_456 : thresholds6_456.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_456 (by decide +kernel)

theorem valid6_462 : thresholds6_462.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_462 (by decide +kernel)

theorem valid6_468 : thresholds6_468.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_468 (by decide +kernel)

theorem valid6_474 : thresholds6_474.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_474 (by decide +kernel)

theorem valid6_480 : thresholds6_480.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_480 (by decide +kernel)

theorem valid6_486 : thresholds6_486.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_486 (by decide +kernel)

theorem valid6_492 : thresholds6_492.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_492 (by decide +kernel)

theorem valid6_498 : thresholds6_498.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_498 (by decide +kernel)

theorem valid6_504 : thresholds6_504.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_504 (by decide +kernel)

theorem valid6_510 : thresholds6_510.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_510 (by decide +kernel)

theorem valid6_516 : thresholds6_516.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_516 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part006

section Pack_Z6970H2307PackedBand06Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid6_522 : thresholds6_522.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_522 (by decide +kernel)

theorem valid6_528 : thresholds6_528.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_528 (by decide +kernel)

theorem valid6_534 : thresholds6_534.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_534 (by decide +kernel)

theorem valid6_540 : thresholds6_540.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_540 (by decide +kernel)

theorem valid6_546 : thresholds6_546.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_546 (by decide +kernel)

theorem valid6_552 : thresholds6_552.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_552 (by decide +kernel)

theorem valid6_558 : thresholds6_558.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_558 (by decide +kernel)

theorem valid6_564 : thresholds6_564.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_564 (by decide +kernel)

theorem valid6_570 : thresholds6_570.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_570 (by decide +kernel)

theorem valid6_576 : thresholds6_576.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_576 (by decide +kernel)

theorem valid6_582 : thresholds6_582.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_582 (by decide +kernel)

theorem valid6_588 : thresholds6_588.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_588 (by decide +kernel)

theorem valid6_594 : thresholds6_594.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_594 (by decide +kernel)

theorem valid6_600 : thresholds6_600.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_600 (by decide +kernel)

theorem valid6_606 : thresholds6_606.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_606 (by decide +kernel)

theorem valid6_612 : thresholds6_612.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_612 (by decide +kernel)

theorem valid6_618 : thresholds6_618.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_618 (by decide +kernel)

theorem valid6_624 : thresholds6_624.all (checked ⟨6,3,1⟩)=true :=
  checkedVerified ⟨6,3,1⟩ prefixMap6 thresholds6_624 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand06Part007

section Pack_Z6970H2307PackedBand07Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid7_0_0 : (thresholds7_0.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_0.take 4) (by decide +kernel)

private theorem valid7_0_4 : (thresholds7_0.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_0.drop 4) (by decide +kernel)

theorem valid7_0 : thresholds7_0.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_0 4 valid7_0_0 (valid7_0_4)

theorem valid7_6 : thresholds7_6.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_6 (by decide +kernel)

theorem valid7_12 : thresholds7_12.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_12 (by decide +kernel)

theorem valid7_18 : thresholds7_18.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_18 (by decide +kernel)

theorem valid7_24 : thresholds7_24.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_24 (by decide +kernel)

private theorem valid7_30_0 : (thresholds7_30.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_30.take 5) (by decide +kernel)

private theorem valid7_30_5 : (thresholds7_30.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_30.drop 5) (by decide +kernel)

theorem valid7_30 : thresholds7_30.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_30 5 valid7_30_0 (valid7_30_5)

private theorem valid7_36_0 : (thresholds7_36.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_36.take 5) (by decide +kernel)

private theorem valid7_36_5 : (thresholds7_36.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_36.drop 5) (by decide +kernel)

theorem valid7_36 : thresholds7_36.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_36 5 valid7_36_0 (valid7_36_5)

private theorem valid7_42_0 : (thresholds7_42.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_42.take 4) (by decide +kernel)

private theorem valid7_42_4 : (thresholds7_42.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_42.drop 4) (by decide +kernel)

theorem valid7_42 : thresholds7_42.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_42 4 valid7_42_0 (valid7_42_4)

private theorem valid7_48_0 : (thresholds7_48.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_48.take 4) (by decide +kernel)

private theorem valid7_48_4 : (thresholds7_48.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_48.drop 4) (by decide +kernel)

theorem valid7_48 : thresholds7_48.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_48 4 valid7_48_0 (valid7_48_4)

private theorem valid7_54_0 : (thresholds7_54.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_54.take 4) (by decide +kernel)

private theorem valid7_54_4 : (thresholds7_54.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_54.drop 4) (by decide +kernel)

theorem valid7_54 : thresholds7_54.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_54 4 valid7_54_0 (valid7_54_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part000

section Pack_Z6970H2307PackedBand07Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid7_60_0 : (thresholds7_60.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_60.take 3) (by decide +kernel)

private theorem valid7_60_3 : ((thresholds7_60.drop 3).take 1).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 ((thresholds7_60.drop 3).take 1) (by decide +kernel)

private theorem valid7_60_4 : (thresholds7_60.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_60.drop 4) (by decide +kernel)

theorem valid7_60 : thresholds7_60.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_60 3 valid7_60_0 (all_take_drop (checked ⟨7,3,1⟩) (thresholds7_60.drop 3) 1 valid7_60_3 (valid7_60_4))

theorem valid7_66 : thresholds7_66.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_66 (by decide +kernel)

private theorem valid7_72_0 : (thresholds7_72.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_72.take 3) (by decide +kernel)

private theorem valid7_72_3 : (thresholds7_72.drop 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_72.drop 3) (by decide +kernel)

theorem valid7_72 : thresholds7_72.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_72 3 valid7_72_0 (valid7_72_3)

private theorem valid7_78_0 : (thresholds7_78.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_78.take 5) (by decide +kernel)

private theorem valid7_78_5 : (thresholds7_78.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_78.drop 5) (by decide +kernel)

theorem valid7_78 : thresholds7_78.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_78 5 valid7_78_0 (valid7_78_5)

theorem valid7_84 : thresholds7_84.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_84 (by decide +kernel)

private theorem valid7_90_0 : (thresholds7_90.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_90.take 3) (by decide +kernel)

private theorem valid7_90_3 : (thresholds7_90.drop 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_90.drop 3) (by decide +kernel)

theorem valid7_90 : thresholds7_90.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_90 3 valid7_90_0 (valid7_90_3)

private theorem valid7_96_0 : (thresholds7_96.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_96.take 4) (by decide +kernel)

private theorem valid7_96_4 : (thresholds7_96.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_96.drop 4) (by decide +kernel)

theorem valid7_96 : thresholds7_96.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_96 4 valid7_96_0 (valid7_96_4)

private theorem valid7_102_0 : (thresholds7_102.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_102.take 4) (by decide +kernel)

private theorem valid7_102_4 : (thresholds7_102.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_102.drop 4) (by decide +kernel)

theorem valid7_102 : thresholds7_102.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_102 4 valid7_102_0 (valid7_102_4)

private theorem valid7_108_0 : (thresholds7_108.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_108.take 3) (by decide +kernel)

private theorem valid7_108_3 : (thresholds7_108.drop 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_108.drop 3) (by decide +kernel)

theorem valid7_108 : thresholds7_108.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_108 3 valid7_108_0 (valid7_108_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part001

section Pack_Z6970H2307PackedBand07Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid7_114_0 : (thresholds7_114.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_114.take 5) (by decide +kernel)

private theorem valid7_114_5 : (thresholds7_114.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_114.drop 5) (by decide +kernel)

theorem valid7_114 : thresholds7_114.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_114 5 valid7_114_0 (valid7_114_5)

private theorem valid7_120_0 : (thresholds7_120.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_120.take 4) (by decide +kernel)

private theorem valid7_120_4 : (thresholds7_120.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_120.drop 4) (by decide +kernel)

theorem valid7_120 : thresholds7_120.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_120 4 valid7_120_0 (valid7_120_4)

theorem valid7_126 : thresholds7_126.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_126 (by decide +kernel)

private theorem valid7_132_0 : (thresholds7_132.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_132.take 3) (by decide +kernel)

private theorem valid7_132_3 : ((thresholds7_132.drop 3).take 2).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 ((thresholds7_132.drop 3).take 2) (by decide +kernel)

private theorem valid7_132_5 : (thresholds7_132.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_132.drop 5) (by decide +kernel)

theorem valid7_132 : thresholds7_132.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_132 3 valid7_132_0 (all_take_drop (checked ⟨7,3,1⟩) (thresholds7_132.drop 3) 2 valid7_132_3 (valid7_132_5))

private theorem valid7_138_0 : (thresholds7_138.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_138.take 5) (by decide +kernel)

private theorem valid7_138_5 : (thresholds7_138.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_138.drop 5) (by decide +kernel)

theorem valid7_138 : thresholds7_138.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_138 5 valid7_138_0 (valid7_138_5)

private theorem valid7_144_0 : (thresholds7_144.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_144.take 5) (by decide +kernel)

private theorem valid7_144_5 : (thresholds7_144.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_144.drop 5) (by decide +kernel)

theorem valid7_144 : thresholds7_144.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_144 5 valid7_144_0 (valid7_144_5)

private theorem valid7_150_0 : (thresholds7_150.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_150.take 3) (by decide +kernel)

private theorem valid7_150_3 : (thresholds7_150.drop 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_150.drop 3) (by decide +kernel)

theorem valid7_150 : thresholds7_150.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_150 3 valid7_150_0 (valid7_150_3)

theorem valid7_156 : thresholds7_156.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_156 (by decide +kernel)

private theorem valid7_162_0 : (thresholds7_162.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_162.take 3) (by decide +kernel)

private theorem valid7_162_3 : (thresholds7_162.drop 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_162.drop 3) (by decide +kernel)

theorem valid7_162 : thresholds7_162.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_162 3 valid7_162_0 (valid7_162_3)

private theorem valid7_168_0 : (thresholds7_168.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_168.take 4) (by decide +kernel)

private theorem valid7_168_4 : (thresholds7_168.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_168.drop 4) (by decide +kernel)

theorem valid7_168 : thresholds7_168.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_168 4 valid7_168_0 (valid7_168_4)

private theorem valid7_174_0 : (thresholds7_174.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_174.take 4) (by decide +kernel)

private theorem valid7_174_4 : (thresholds7_174.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_174.drop 4) (by decide +kernel)

theorem valid7_174 : thresholds7_174.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_174 4 valid7_174_0 (valid7_174_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part002

section Pack_Z6970H2307PackedBand07Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid7_180 : thresholds7_180.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_180 (by decide +kernel)

private theorem valid7_186_0 : (thresholds7_186.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_186.take 4) (by decide +kernel)

private theorem valid7_186_4 : (thresholds7_186.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_186.drop 4) (by decide +kernel)

theorem valid7_186 : thresholds7_186.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_186 4 valid7_186_0 (valid7_186_4)

private theorem valid7_192_0 : (thresholds7_192.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_192.take 5) (by decide +kernel)

private theorem valid7_192_5 : (thresholds7_192.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_192.drop 5) (by decide +kernel)

theorem valid7_192 : thresholds7_192.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_192 5 valid7_192_0 (valid7_192_5)

private theorem valid7_198_0 : (thresholds7_198.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_198.take 4) (by decide +kernel)

private theorem valid7_198_4 : (thresholds7_198.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_198.drop 4) (by decide +kernel)

theorem valid7_198 : thresholds7_198.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_198 4 valid7_198_0 (valid7_198_4)

private theorem valid7_204_0 : (thresholds7_204.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_204.take 5) (by decide +kernel)

private theorem valid7_204_5 : (thresholds7_204.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_204.drop 5) (by decide +kernel)

theorem valid7_204 : thresholds7_204.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_204 5 valid7_204_0 (valid7_204_5)

theorem valid7_210 : thresholds7_210.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_210 (by decide +kernel)

private theorem valid7_216_0 : (thresholds7_216.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_216.take 4) (by decide +kernel)

private theorem valid7_216_4 : (thresholds7_216.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_216.drop 4) (by decide +kernel)

theorem valid7_216 : thresholds7_216.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_216 4 valid7_216_0 (valid7_216_4)

private theorem valid7_222_0 : (thresholds7_222.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_222.take 5) (by decide +kernel)

private theorem valid7_222_5 : (thresholds7_222.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_222.drop 5) (by decide +kernel)

theorem valid7_222 : thresholds7_222.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_222 5 valid7_222_0 (valid7_222_5)

private theorem valid7_228_0 : (thresholds7_228.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_228.take 5) (by decide +kernel)

private theorem valid7_228_5 : (thresholds7_228.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_228.drop 5) (by decide +kernel)

theorem valid7_228 : thresholds7_228.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_228 5 valid7_228_0 (valid7_228_5)

private theorem valid7_234_0 : (thresholds7_234.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_234.take 4) (by decide +kernel)

private theorem valid7_234_4 : (thresholds7_234.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_234.drop 4) (by decide +kernel)

theorem valid7_234 : thresholds7_234.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_234 4 valid7_234_0 (valid7_234_4)

private theorem valid7_240_0 : (thresholds7_240.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_240.take 5) (by decide +kernel)

private theorem valid7_240_5 : (thresholds7_240.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_240.drop 5) (by decide +kernel)

theorem valid7_240 : thresholds7_240.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_240 5 valid7_240_0 (valid7_240_5)

theorem valid7_246 : thresholds7_246.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_246 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part003

section Pack_Z6970H2307PackedBand07Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid7_252_0 : (thresholds7_252.take 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_252.take 4) (by decide +kernel)

private theorem valid7_252_4 : (thresholds7_252.drop 4).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_252.drop 4) (by decide +kernel)

theorem valid7_252 : thresholds7_252.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_252 4 valid7_252_0 (valid7_252_4)

private theorem valid7_258_0 : (thresholds7_258.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_258.take 5) (by decide +kernel)

private theorem valid7_258_5 : (thresholds7_258.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_258.drop 5) (by decide +kernel)

theorem valid7_258 : thresholds7_258.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_258 5 valid7_258_0 (valid7_258_5)

theorem valid7_264 : thresholds7_264.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_264 (by decide +kernel)

private theorem valid7_270_0 : (thresholds7_270.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_270.take 5) (by decide +kernel)

private theorem valid7_270_5 : (thresholds7_270.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_270.drop 5) (by decide +kernel)

theorem valid7_270 : thresholds7_270.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_270 5 valid7_270_0 (valid7_270_5)

theorem valid7_276 : thresholds7_276.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_276 (by decide +kernel)

theorem valid7_282 : thresholds7_282.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_282 (by decide +kernel)

theorem valid7_288 : thresholds7_288.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_288 (by decide +kernel)

theorem valid7_294 : thresholds7_294.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_294 (by decide +kernel)

theorem valid7_300 : thresholds7_300.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_300 (by decide +kernel)

private theorem valid7_306_0 : (thresholds7_306.take 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_306.take 3) (by decide +kernel)

private theorem valid7_306_3 : (thresholds7_306.drop 3).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_306.drop 3) (by decide +kernel)

theorem valid7_306 : thresholds7_306.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_306 3 valid7_306_0 (valid7_306_3)

theorem valid7_312 : thresholds7_312.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_312 (by decide +kernel)

theorem valid7_318 : thresholds7_318.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_318 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part004

section Pack_Z6970H2307PackedBand07Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid7_324 : thresholds7_324.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_324 (by decide +kernel)

theorem valid7_330 : thresholds7_330.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_330 (by decide +kernel)

theorem valid7_336 : thresholds7_336.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_336 (by decide +kernel)

theorem valid7_342 : thresholds7_342.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_342 (by decide +kernel)

private theorem valid7_348_0 : (thresholds7_348.take 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_348.take 5) (by decide +kernel)

private theorem valid7_348_5 : (thresholds7_348.drop 5).all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 (thresholds7_348.drop 5) (by decide +kernel)

theorem valid7_348 : thresholds7_348.all (checked ⟨7,3,1⟩)=true :=
  all_take_drop (checked ⟨7,3,1⟩) thresholds7_348 5 valid7_348_0 (valid7_348_5)

theorem valid7_354 : thresholds7_354.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_354 (by decide +kernel)

theorem valid7_360 : thresholds7_360.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_360 (by decide +kernel)

theorem valid7_366 : thresholds7_366.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_366 (by decide +kernel)

theorem valid7_372 : thresholds7_372.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_372 (by decide +kernel)

theorem valid7_378 : thresholds7_378.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_378 (by decide +kernel)

theorem valid7_384 : thresholds7_384.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_384 (by decide +kernel)

theorem valid7_390 : thresholds7_390.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_390 (by decide +kernel)

theorem valid7_396 : thresholds7_396.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_396 (by decide +kernel)

theorem valid7_402 : thresholds7_402.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_402 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part005

section Pack_Z6970H2307PackedBand07Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid7_408 : thresholds7_408.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_408 (by decide +kernel)

theorem valid7_414 : thresholds7_414.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_414 (by decide +kernel)

theorem valid7_420 : thresholds7_420.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_420 (by decide +kernel)

theorem valid7_426 : thresholds7_426.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_426 (by decide +kernel)

theorem valid7_432 : thresholds7_432.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_432 (by decide +kernel)

theorem valid7_438 : thresholds7_438.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_438 (by decide +kernel)

theorem valid7_444 : thresholds7_444.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_444 (by decide +kernel)

theorem valid7_450 : thresholds7_450.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_450 (by decide +kernel)

theorem valid7_456 : thresholds7_456.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_456 (by decide +kernel)

theorem valid7_462 : thresholds7_462.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_462 (by decide +kernel)

theorem valid7_468 : thresholds7_468.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_468 (by decide +kernel)

theorem valid7_474 : thresholds7_474.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_474 (by decide +kernel)

theorem valid7_480 : thresholds7_480.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_480 (by decide +kernel)

theorem valid7_486 : thresholds7_486.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_486 (by decide +kernel)

theorem valid7_492 : thresholds7_492.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_492 (by decide +kernel)

theorem valid7_498 : thresholds7_498.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_498 (by decide +kernel)

theorem valid7_504 : thresholds7_504.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_504 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part006

section Pack_Z6970H2307PackedBand07Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid7_510 : thresholds7_510.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_510 (by decide +kernel)

theorem valid7_516 : thresholds7_516.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_516 (by decide +kernel)

theorem valid7_522 : thresholds7_522.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_522 (by decide +kernel)

theorem valid7_528 : thresholds7_528.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_528 (by decide +kernel)

theorem valid7_534 : thresholds7_534.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_534 (by decide +kernel)

theorem valid7_540 : thresholds7_540.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_540 (by decide +kernel)

theorem valid7_546 : thresholds7_546.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_546 (by decide +kernel)

theorem valid7_552 : thresholds7_552.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_552 (by decide +kernel)

theorem valid7_558 : thresholds7_558.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_558 (by decide +kernel)

theorem valid7_564 : thresholds7_564.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_564 (by decide +kernel)

theorem valid7_570 : thresholds7_570.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_570 (by decide +kernel)

theorem valid7_576 : thresholds7_576.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_576 (by decide +kernel)

theorem valid7_582 : thresholds7_582.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_582 (by decide +kernel)

theorem valid7_588 : thresholds7_588.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_588 (by decide +kernel)

theorem valid7_594 : thresholds7_594.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_594 (by decide +kernel)

theorem valid7_600 : thresholds7_600.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_600 (by decide +kernel)

theorem valid7_606 : thresholds7_606.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_606 (by decide +kernel)

theorem valid7_612 : thresholds7_612.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_612 (by decide +kernel)

theorem valid7_618 : thresholds7_618.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_618 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part007

section Pack_Z6970H2307PackedBand07Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid7_624 : thresholds7_624.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_624 (by decide +kernel)

theorem valid7_630 : thresholds7_630.all (checked ⟨7,3,1⟩)=true :=
  checkedVerified ⟨7,3,1⟩ prefixMap7 thresholds7_630 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand07Part008

section Pack_Z6970H2307PackedBand08Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid8_0_0 : (thresholds8_0.take 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_0.take 3) (by decide +kernel)

private theorem valid8_0_3 : (thresholds8_0.drop 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_0.drop 3) (by decide +kernel)

theorem valid8_0 : thresholds8_0.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_0 3 valid8_0_0 (valid8_0_3)

theorem valid8_6 : thresholds8_6.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_6 (by decide +kernel)

theorem valid8_12 : thresholds8_12.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_12 (by decide +kernel)

theorem valid8_18 : thresholds8_18.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_18 (by decide +kernel)

theorem valid8_24 : thresholds8_24.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_24 (by decide +kernel)

private theorem valid8_30_0 : (thresholds8_30.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_30.take 4) (by decide +kernel)

private theorem valid8_30_4 : (thresholds8_30.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_30.drop 4) (by decide +kernel)

theorem valid8_30 : thresholds8_30.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_30 4 valid8_30_0 (valid8_30_4)

private theorem valid8_36_0 : (thresholds8_36.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_36.take 5) (by decide +kernel)

private theorem valid8_36_5 : (thresholds8_36.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_36.drop 5) (by decide +kernel)

theorem valid8_36 : thresholds8_36.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_36 5 valid8_36_0 (valid8_36_5)

theorem valid8_42 : thresholds8_42.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_42 (by decide +kernel)

private theorem valid8_48_0 : (thresholds8_48.take 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_48.take 3) (by decide +kernel)

private theorem valid8_48_3 : (thresholds8_48.drop 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_48.drop 3) (by decide +kernel)

theorem valid8_48 : thresholds8_48.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_48 3 valid8_48_0 (valid8_48_3)

theorem valid8_54 : thresholds8_54.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_54 (by decide +kernel)

private theorem valid8_60_0 : (thresholds8_60.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_60.take 4) (by decide +kernel)

private theorem valid8_60_4 : (thresholds8_60.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_60.drop 4) (by decide +kernel)

theorem valid8_60 : thresholds8_60.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_60 4 valid8_60_0 (valid8_60_4)

private theorem valid8_66_0 : (thresholds8_66.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_66.take 5) (by decide +kernel)

private theorem valid8_66_5 : (thresholds8_66.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_66.drop 5) (by decide +kernel)

theorem valid8_66 : thresholds8_66.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_66 5 valid8_66_0 (valid8_66_5)

private theorem valid8_72_0 : (thresholds8_72.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_72.take 5) (by decide +kernel)

private theorem valid8_72_5 : (thresholds8_72.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_72.drop 5) (by decide +kernel)

theorem valid8_72 : thresholds8_72.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_72 5 valid8_72_0 (valid8_72_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part000

section Pack_Z6970H2307PackedBand08Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid8_78_0 : (thresholds8_78.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_78.take 4) (by decide +kernel)

private theorem valid8_78_4 : (thresholds8_78.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_78.drop 4) (by decide +kernel)

theorem valid8_78 : thresholds8_78.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_78 4 valid8_78_0 (valid8_78_4)

private theorem valid8_84_0 : (thresholds8_84.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_84.take 5) (by decide +kernel)

private theorem valid8_84_5 : (thresholds8_84.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_84.drop 5) (by decide +kernel)

theorem valid8_84 : thresholds8_84.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_84 5 valid8_84_0 (valid8_84_5)

private theorem valid8_90_0 : (thresholds8_90.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_90.take 4) (by decide +kernel)

private theorem valid8_90_4 : (thresholds8_90.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_90.drop 4) (by decide +kernel)

theorem valid8_90 : thresholds8_90.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_90 4 valid8_90_0 (valid8_90_4)

private theorem valid8_96_0 : (thresholds8_96.take 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_96.take 3) (by decide +kernel)

private theorem valid8_96_3 : (thresholds8_96.drop 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_96.drop 3) (by decide +kernel)

theorem valid8_96 : thresholds8_96.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_96 3 valid8_96_0 (valid8_96_3)

private theorem valid8_102_0 : (thresholds8_102.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_102.take 4) (by decide +kernel)

private theorem valid8_102_4 : (thresholds8_102.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_102.drop 4) (by decide +kernel)

theorem valid8_102 : thresholds8_102.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_102 4 valid8_102_0 (valid8_102_4)

theorem valid8_108 : thresholds8_108.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_108 (by decide +kernel)

private theorem valid8_114_0 : (thresholds8_114.take 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_114.take 3) (by decide +kernel)

private theorem valid8_114_3 : (thresholds8_114.drop 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_114.drop 3) (by decide +kernel)

theorem valid8_114 : thresholds8_114.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_114 3 valid8_114_0 (valid8_114_3)

private theorem valid8_120_0 : (thresholds8_120.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_120.take 4) (by decide +kernel)

private theorem valid8_120_4 : (thresholds8_120.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_120.drop 4) (by decide +kernel)

theorem valid8_120 : thresholds8_120.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_120 4 valid8_120_0 (valid8_120_4)

theorem valid8_126 : thresholds8_126.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_126 (by decide +kernel)

private theorem valid8_132_0 : (thresholds8_132.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_132.take 4) (by decide +kernel)

private theorem valid8_132_4 : (thresholds8_132.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_132.drop 4) (by decide +kernel)

theorem valid8_132 : thresholds8_132.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_132 4 valid8_132_0 (valid8_132_4)

private theorem valid8_138_0 : (thresholds8_138.take 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_138.take 3) (by decide +kernel)

private theorem valid8_138_3 : (thresholds8_138.drop 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_138.drop 3) (by decide +kernel)

theorem valid8_138 : thresholds8_138.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_138 3 valid8_138_0 (valid8_138_3)

private theorem valid8_144_0 : (thresholds8_144.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_144.take 5) (by decide +kernel)

private theorem valid8_144_5 : (thresholds8_144.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_144.drop 5) (by decide +kernel)

theorem valid8_144 : thresholds8_144.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_144 5 valid8_144_0 (valid8_144_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part001

section Pack_Z6970H2307PackedBand08Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid8_150_0 : (thresholds8_150.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_150.take 4) (by decide +kernel)

private theorem valid8_150_4 : (thresholds8_150.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_150.drop 4) (by decide +kernel)

theorem valid8_150 : thresholds8_150.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_150 4 valid8_150_0 (valid8_150_4)

private theorem valid8_156_0 : (thresholds8_156.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_156.take 4) (by decide +kernel)

private theorem valid8_156_4 : (thresholds8_156.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_156.drop 4) (by decide +kernel)

theorem valid8_156 : thresholds8_156.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_156 4 valid8_156_0 (valid8_156_4)

private theorem valid8_162_0 : (thresholds8_162.take 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_162.take 3) (by decide +kernel)

private theorem valid8_162_3 : (thresholds8_162.drop 3).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_162.drop 3) (by decide +kernel)

theorem valid8_162 : thresholds8_162.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_162 3 valid8_162_0 (valid8_162_3)

theorem valid8_168 : thresholds8_168.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_168 (by decide +kernel)

private theorem valid8_174_0 : (thresholds8_174.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_174.take 4) (by decide +kernel)

private theorem valid8_174_4 : (thresholds8_174.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_174.drop 4) (by decide +kernel)

theorem valid8_174 : thresholds8_174.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_174 4 valid8_174_0 (valid8_174_4)

private theorem valid8_180_0 : (thresholds8_180.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_180.take 4) (by decide +kernel)

private theorem valid8_180_4 : (thresholds8_180.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_180.drop 4) (by decide +kernel)

theorem valid8_180 : thresholds8_180.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_180 4 valid8_180_0 (valid8_180_4)

private theorem valid8_186_0 : (thresholds8_186.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_186.take 5) (by decide +kernel)

private theorem valid8_186_5 : (thresholds8_186.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_186.drop 5) (by decide +kernel)

theorem valid8_186 : thresholds8_186.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_186 5 valid8_186_0 (valid8_186_5)

private theorem valid8_192_0 : (thresholds8_192.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_192.take 5) (by decide +kernel)

private theorem valid8_192_5 : (thresholds8_192.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_192.drop 5) (by decide +kernel)

theorem valid8_192 : thresholds8_192.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_192 5 valid8_192_0 (valid8_192_5)

theorem valid8_198 : thresholds8_198.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_198 (by decide +kernel)

private theorem valid8_204_0 : (thresholds8_204.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_204.take 4) (by decide +kernel)

private theorem valid8_204_4 : (thresholds8_204.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_204.drop 4) (by decide +kernel)

theorem valid8_204 : thresholds8_204.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_204 4 valid8_204_0 (valid8_204_4)

theorem valid8_210 : thresholds8_210.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_210 (by decide +kernel)

private theorem valid8_216_0 : (thresholds8_216.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_216.take 5) (by decide +kernel)

private theorem valid8_216_5 : (thresholds8_216.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_216.drop 5) (by decide +kernel)

theorem valid8_216 : thresholds8_216.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_216 5 valid8_216_0 (valid8_216_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part002

section Pack_Z6970H2307PackedBand08Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid8_222 : thresholds8_222.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_222 (by decide +kernel)

theorem valid8_228 : thresholds8_228.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_228 (by decide +kernel)

private theorem valid8_234_0 : (thresholds8_234.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_234.take 4) (by decide +kernel)

private theorem valid8_234_4 : (thresholds8_234.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_234.drop 4) (by decide +kernel)

theorem valid8_234 : thresholds8_234.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_234 4 valid8_234_0 (valid8_234_4)

private theorem valid8_240_0 : (thresholds8_240.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_240.take 5) (by decide +kernel)

private theorem valid8_240_5 : (thresholds8_240.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_240.drop 5) (by decide +kernel)

theorem valid8_240 : thresholds8_240.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_240 5 valid8_240_0 (valid8_240_5)

private theorem valid8_246_0 : (thresholds8_246.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_246.take 4) (by decide +kernel)

private theorem valid8_246_4 : (thresholds8_246.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_246.drop 4) (by decide +kernel)

theorem valid8_246 : thresholds8_246.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_246 4 valid8_246_0 (valid8_246_4)

theorem valid8_252 : thresholds8_252.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_252 (by decide +kernel)

theorem valid8_258 : thresholds8_258.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_258 (by decide +kernel)

theorem valid8_264 : thresholds8_264.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_264 (by decide +kernel)

theorem valid8_270 : thresholds8_270.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_270 (by decide +kernel)

theorem valid8_276 : thresholds8_276.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_276 (by decide +kernel)

private theorem valid8_282_0 : (thresholds8_282.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_282.take 5) (by decide +kernel)

private theorem valid8_282_5 : (thresholds8_282.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_282.drop 5) (by decide +kernel)

theorem valid8_282 : thresholds8_282.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_282 5 valid8_282_0 (valid8_282_5)

private theorem valid8_288_0 : (thresholds8_288.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_288.take 5) (by decide +kernel)

private theorem valid8_288_5 : (thresholds8_288.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_288.drop 5) (by decide +kernel)

theorem valid8_288 : thresholds8_288.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_288 5 valid8_288_0 (valid8_288_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part003

section Pack_Z6970H2307PackedBand08Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid8_294_0 : (thresholds8_294.take 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_294.take 4) (by decide +kernel)

private theorem valid8_294_4 : (thresholds8_294.drop 4).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_294.drop 4) (by decide +kernel)

theorem valid8_294 : thresholds8_294.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_294 4 valid8_294_0 (valid8_294_4)

theorem valid8_300 : thresholds8_300.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_300 (by decide +kernel)

theorem valid8_306 : thresholds8_306.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_306 (by decide +kernel)

theorem valid8_312 : thresholds8_312.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_312 (by decide +kernel)

theorem valid8_318 : thresholds8_318.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_318 (by decide +kernel)

private theorem valid8_324_0 : (thresholds8_324.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_324.take 5) (by decide +kernel)

private theorem valid8_324_5 : (thresholds8_324.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_324.drop 5) (by decide +kernel)

theorem valid8_324 : thresholds8_324.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_324 5 valid8_324_0 (valid8_324_5)

theorem valid8_330 : thresholds8_330.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_330 (by decide +kernel)

private theorem valid8_336_0 : (thresholds8_336.take 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_336.take 5) (by decide +kernel)

private theorem valid8_336_5 : (thresholds8_336.drop 5).all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 (thresholds8_336.drop 5) (by decide +kernel)

theorem valid8_336 : thresholds8_336.all (checked ⟨8,3,1⟩)=true :=
  all_take_drop (checked ⟨8,3,1⟩) thresholds8_336 5 valid8_336_0 (valid8_336_5)

theorem valid8_342 : thresholds8_342.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_342 (by decide +kernel)

theorem valid8_348 : thresholds8_348.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_348 (by decide +kernel)

theorem valid8_354 : thresholds8_354.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_354 (by decide +kernel)

theorem valid8_360 : thresholds8_360.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_360 (by decide +kernel)

theorem valid8_366 : thresholds8_366.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_366 (by decide +kernel)

theorem valid8_372 : thresholds8_372.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_372 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part004

section Pack_Z6970H2307PackedBand08Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid8_378 : thresholds8_378.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_378 (by decide +kernel)

theorem valid8_384 : thresholds8_384.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_384 (by decide +kernel)

theorem valid8_390 : thresholds8_390.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_390 (by decide +kernel)

theorem valid8_396 : thresholds8_396.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_396 (by decide +kernel)

theorem valid8_402 : thresholds8_402.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_402 (by decide +kernel)

theorem valid8_408 : thresholds8_408.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_408 (by decide +kernel)

theorem valid8_414 : thresholds8_414.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_414 (by decide +kernel)

theorem valid8_420 : thresholds8_420.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_420 (by decide +kernel)

theorem valid8_426 : thresholds8_426.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_426 (by decide +kernel)

theorem valid8_432 : thresholds8_432.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_432 (by decide +kernel)

theorem valid8_438 : thresholds8_438.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_438 (by decide +kernel)

theorem valid8_444 : thresholds8_444.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_444 (by decide +kernel)

theorem valid8_450 : thresholds8_450.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_450 (by decide +kernel)

theorem valid8_456 : thresholds8_456.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_456 (by decide +kernel)

theorem valid8_462 : thresholds8_462.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_462 (by decide +kernel)

theorem valid8_468 : thresholds8_468.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_468 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part005

section Pack_Z6970H2307PackedBand08Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid8_474 : thresholds8_474.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_474 (by decide +kernel)

theorem valid8_480 : thresholds8_480.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_480 (by decide +kernel)

theorem valid8_486 : thresholds8_486.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_486 (by decide +kernel)

theorem valid8_492 : thresholds8_492.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_492 (by decide +kernel)

theorem valid8_498 : thresholds8_498.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_498 (by decide +kernel)

theorem valid8_504 : thresholds8_504.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_504 (by decide +kernel)

theorem valid8_510 : thresholds8_510.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_510 (by decide +kernel)

theorem valid8_516 : thresholds8_516.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_516 (by decide +kernel)

theorem valid8_522 : thresholds8_522.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_522 (by decide +kernel)

theorem valid8_528 : thresholds8_528.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_528 (by decide +kernel)

theorem valid8_534 : thresholds8_534.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_534 (by decide +kernel)

theorem valid8_540 : thresholds8_540.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_540 (by decide +kernel)

theorem valid8_546 : thresholds8_546.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_546 (by decide +kernel)

theorem valid8_552 : thresholds8_552.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_552 (by decide +kernel)

theorem valid8_558 : thresholds8_558.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_558 (by decide +kernel)

theorem valid8_564 : thresholds8_564.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_564 (by decide +kernel)

theorem valid8_570 : thresholds8_570.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_570 (by decide +kernel)

theorem valid8_576 : thresholds8_576.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_576 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part006

section Pack_Z6970H2307PackedBand08Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid8_582 : thresholds8_582.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_582 (by decide +kernel)

theorem valid8_588 : thresholds8_588.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_588 (by decide +kernel)

theorem valid8_594 : thresholds8_594.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_594 (by decide +kernel)

theorem valid8_600 : thresholds8_600.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_600 (by decide +kernel)

theorem valid8_606 : thresholds8_606.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_606 (by decide +kernel)

theorem valid8_612 : thresholds8_612.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_612 (by decide +kernel)

theorem valid8_618 : thresholds8_618.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_618 (by decide +kernel)

theorem valid8_624 : thresholds8_624.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_624 (by decide +kernel)

theorem valid8_630 : thresholds8_630.all (checked ⟨8,3,1⟩)=true :=
  checkedVerified ⟨8,3,1⟩ prefixMap8 thresholds8_630 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand08Part007

section Pack_Z6970H2307PackedBand09Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid9_0_0 : (thresholds9_0.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_0.take 4) (by decide +kernel)

private theorem valid9_0_4 : (thresholds9_0.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_0.drop 4) (by decide +kernel)

theorem valid9_0 : thresholds9_0.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_0 4 valid9_0_0 (valid9_0_4)

theorem valid9_6 : thresholds9_6.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_6 (by decide +kernel)

theorem valid9_12 : thresholds9_12.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_12 (by decide +kernel)

theorem valid9_18 : thresholds9_18.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_18 (by decide +kernel)

theorem valid9_24 : thresholds9_24.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_24 (by decide +kernel)

private theorem valid9_30_0 : (thresholds9_30.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_30.take 4) (by decide +kernel)

private theorem valid9_30_4 : (thresholds9_30.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_30.drop 4) (by decide +kernel)

theorem valid9_30 : thresholds9_30.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_30 4 valid9_30_0 (valid9_30_4)

theorem valid9_36 : thresholds9_36.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_36 (by decide +kernel)

private theorem valid9_42_0 : (thresholds9_42.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_42.take 4) (by decide +kernel)

private theorem valid9_42_4 : (thresholds9_42.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_42.drop 4) (by decide +kernel)

theorem valid9_42 : thresholds9_42.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_42 4 valid9_42_0 (valid9_42_4)

theorem valid9_48 : thresholds9_48.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_48 (by decide +kernel)

private theorem valid9_54_0 : (thresholds9_54.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_54.take 5) (by decide +kernel)

private theorem valid9_54_5 : (thresholds9_54.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_54.drop 5) (by decide +kernel)

theorem valid9_54 : thresholds9_54.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_54 5 valid9_54_0 (valid9_54_5)

private theorem valid9_60_0 : (thresholds9_60.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_60.take 4) (by decide +kernel)

private theorem valid9_60_4 : (thresholds9_60.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_60.drop 4) (by decide +kernel)

theorem valid9_60 : thresholds9_60.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_60 4 valid9_60_0 (valid9_60_4)

private theorem valid9_66_0 : (thresholds9_66.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_66.take 5) (by decide +kernel)

private theorem valid9_66_5 : (thresholds9_66.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_66.drop 5) (by decide +kernel)

theorem valid9_66 : thresholds9_66.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_66 5 valid9_66_0 (valid9_66_5)

private theorem valid9_72_0 : (thresholds9_72.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_72.take 4) (by decide +kernel)

private theorem valid9_72_4 : (thresholds9_72.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_72.drop 4) (by decide +kernel)

theorem valid9_72 : thresholds9_72.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_72 4 valid9_72_0 (valid9_72_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part000

section Pack_Z6970H2307PackedBand09Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid9_78_0 : (thresholds9_78.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_78.take 4) (by decide +kernel)

private theorem valid9_78_4 : (thresholds9_78.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_78.drop 4) (by decide +kernel)

theorem valid9_78 : thresholds9_78.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_78 4 valid9_78_0 (valid9_78_4)

private theorem valid9_84_0 : (thresholds9_84.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_84.take 4) (by decide +kernel)

private theorem valid9_84_4 : (thresholds9_84.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_84.drop 4) (by decide +kernel)

theorem valid9_84 : thresholds9_84.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_84 4 valid9_84_0 (valid9_84_4)

private theorem valid9_90_0 : (thresholds9_90.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_90.take 5) (by decide +kernel)

private theorem valid9_90_5 : (thresholds9_90.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_90.drop 5) (by decide +kernel)

theorem valid9_90 : thresholds9_90.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_90 5 valid9_90_0 (valid9_90_5)

private theorem valid9_96_0 : (thresholds9_96.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_96.take 5) (by decide +kernel)

private theorem valid9_96_5 : (thresholds9_96.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_96.drop 5) (by decide +kernel)

theorem valid9_96 : thresholds9_96.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_96 5 valid9_96_0 (valid9_96_5)

theorem valid9_102 : thresholds9_102.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_102 (by decide +kernel)

private theorem valid9_108_0 : (thresholds9_108.take 3).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_108.take 3) (by decide +kernel)

private theorem valid9_108_3 : (thresholds9_108.drop 3).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_108.drop 3) (by decide +kernel)

theorem valid9_108 : thresholds9_108.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_108 3 valid9_108_0 (valid9_108_3)

private theorem valid9_114_0 : (thresholds9_114.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_114.take 5) (by decide +kernel)

private theorem valid9_114_5 : (thresholds9_114.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_114.drop 5) (by decide +kernel)

theorem valid9_114 : thresholds9_114.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_114 5 valid9_114_0 (valid9_114_5)

private theorem valid9_120_0 : (thresholds9_120.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_120.take 5) (by decide +kernel)

private theorem valid9_120_5 : (thresholds9_120.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_120.drop 5) (by decide +kernel)

theorem valid9_120 : thresholds9_120.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_120 5 valid9_120_0 (valid9_120_5)

private theorem valid9_126_0 : (thresholds9_126.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_126.take 4) (by decide +kernel)

private theorem valid9_126_4 : (thresholds9_126.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_126.drop 4) (by decide +kernel)

theorem valid9_126 : thresholds9_126.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_126 4 valid9_126_0 (valid9_126_4)

theorem valid9_132 : thresholds9_132.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_132 (by decide +kernel)

private theorem valid9_138_0 : (thresholds9_138.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_138.take 5) (by decide +kernel)

private theorem valid9_138_5 : (thresholds9_138.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_138.drop 5) (by decide +kernel)

theorem valid9_138 : thresholds9_138.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_138 5 valid9_138_0 (valid9_138_5)

private theorem valid9_144_0 : (thresholds9_144.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_144.take 4) (by decide +kernel)

private theorem valid9_144_4 : (thresholds9_144.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_144.drop 4) (by decide +kernel)

theorem valid9_144 : thresholds9_144.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_144 4 valid9_144_0 (valid9_144_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part001
