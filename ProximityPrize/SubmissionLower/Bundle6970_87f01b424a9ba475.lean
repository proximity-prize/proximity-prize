import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_e9774b3fc07c89e3

section Pack_Z6970H2307PackedBand09Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid9_150_0 : (thresholds9_150.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_150.take 4) (by decide +kernel)

private theorem valid9_150_4 : (thresholds9_150.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_150.drop 4) (by decide +kernel)

theorem valid9_150 : thresholds9_150.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_150 4 valid9_150_0 (valid9_150_4)

private theorem valid9_156_0 : (thresholds9_156.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_156.take 5) (by decide +kernel)

private theorem valid9_156_5 : (thresholds9_156.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_156.drop 5) (by decide +kernel)

theorem valid9_156 : thresholds9_156.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_156 5 valid9_156_0 (valid9_156_5)

theorem valid9_162 : thresholds9_162.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_162 (by decide +kernel)

private theorem valid9_168_0 : (thresholds9_168.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_168.take 4) (by decide +kernel)

private theorem valid9_168_4 : (thresholds9_168.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_168.drop 4) (by decide +kernel)

theorem valid9_168 : thresholds9_168.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_168 4 valid9_168_0 (valid9_168_4)

private theorem valid9_174_0 : (thresholds9_174.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_174.take 5) (by decide +kernel)

private theorem valid9_174_5 : (thresholds9_174.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_174.drop 5) (by decide +kernel)

theorem valid9_174 : thresholds9_174.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_174 5 valid9_174_0 (valid9_174_5)

theorem valid9_180 : thresholds9_180.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_180 (by decide +kernel)

private theorem valid9_186_0 : (thresholds9_186.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_186.take 4) (by decide +kernel)

private theorem valid9_186_4 : (thresholds9_186.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_186.drop 4) (by decide +kernel)

theorem valid9_186 : thresholds9_186.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_186 4 valid9_186_0 (valid9_186_4)

private theorem valid9_192_0 : (thresholds9_192.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_192.take 5) (by decide +kernel)

private theorem valid9_192_5 : (thresholds9_192.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_192.drop 5) (by decide +kernel)

theorem valid9_192 : thresholds9_192.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_192 5 valid9_192_0 (valid9_192_5)

private theorem valid9_198_0 : (thresholds9_198.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_198.take 5) (by decide +kernel)

private theorem valid9_198_5 : (thresholds9_198.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_198.drop 5) (by decide +kernel)

theorem valid9_198 : thresholds9_198.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_198 5 valid9_198_0 (valid9_198_5)

private theorem valid9_204_0 : (thresholds9_204.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_204.take 4) (by decide +kernel)

private theorem valid9_204_4 : (thresholds9_204.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_204.drop 4) (by decide +kernel)

theorem valid9_204 : thresholds9_204.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_204 4 valid9_204_0 (valid9_204_4)

private theorem valid9_210_0 : (thresholds9_210.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_210.take 5) (by decide +kernel)

private theorem valid9_210_5 : (thresholds9_210.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_210.drop 5) (by decide +kernel)

theorem valid9_210 : thresholds9_210.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_210 5 valid9_210_0 (valid9_210_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part002

section Pack_Z6970H2307PackedBand09Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid9_216_0 : (thresholds9_216.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_216.take 4) (by decide +kernel)

private theorem valid9_216_4 : (thresholds9_216.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_216.drop 4) (by decide +kernel)

theorem valid9_216 : thresholds9_216.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_216 4 valid9_216_0 (valid9_216_4)

private theorem valid9_222_0 : (thresholds9_222.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_222.take 5) (by decide +kernel)

private theorem valid9_222_5 : (thresholds9_222.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_222.drop 5) (by decide +kernel)

theorem valid9_222 : thresholds9_222.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_222 5 valid9_222_0 (valid9_222_5)

theorem valid9_228 : thresholds9_228.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_228 (by decide +kernel)

private theorem valid9_234_0 : (thresholds9_234.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_234.take 5) (by decide +kernel)

private theorem valid9_234_5 : (thresholds9_234.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_234.drop 5) (by decide +kernel)

theorem valid9_234 : thresholds9_234.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_234 5 valid9_234_0 (valid9_234_5)

private theorem valid9_240_0 : (thresholds9_240.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_240.take 5) (by decide +kernel)

private theorem valid9_240_5 : (thresholds9_240.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_240.drop 5) (by decide +kernel)

theorem valid9_240 : thresholds9_240.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_240 5 valid9_240_0 (valid9_240_5)

theorem valid9_246 : thresholds9_246.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_246 (by decide +kernel)

private theorem valid9_252_0 : (thresholds9_252.take 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_252.take 4) (by decide +kernel)

private theorem valid9_252_4 : (thresholds9_252.drop 4).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_252.drop 4) (by decide +kernel)

theorem valid9_252 : thresholds9_252.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_252 4 valid9_252_0 (valid9_252_4)

private theorem valid9_258_0 : (thresholds9_258.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_258.take 5) (by decide +kernel)

private theorem valid9_258_5 : (thresholds9_258.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_258.drop 5) (by decide +kernel)

theorem valid9_258 : thresholds9_258.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_258 5 valid9_258_0 (valid9_258_5)

theorem valid9_264 : thresholds9_264.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_264 (by decide +kernel)

private theorem valid9_270_0 : (thresholds9_270.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_270.take 5) (by decide +kernel)

private theorem valid9_270_5 : (thresholds9_270.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_270.drop 5) (by decide +kernel)

theorem valid9_270 : thresholds9_270.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_270 5 valid9_270_0 (valid9_270_5)

theorem valid9_276 : thresholds9_276.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_276 (by decide +kernel)

theorem valid9_282 : thresholds9_282.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_282 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part003

section Pack_Z6970H2307PackedBand09Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid9_288 : thresholds9_288.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_288 (by decide +kernel)

theorem valid9_294 : thresholds9_294.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_294 (by decide +kernel)

theorem valid9_300 : thresholds9_300.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_300 (by decide +kernel)

private theorem valid9_306_0 : (thresholds9_306.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_306.take 5) (by decide +kernel)

private theorem valid9_306_5 : (thresholds9_306.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_306.drop 5) (by decide +kernel)

theorem valid9_306 : thresholds9_306.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_306 5 valid9_306_0 (valid9_306_5)

private theorem valid9_312_0 : (thresholds9_312.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_312.take 5) (by decide +kernel)

private theorem valid9_312_5 : (thresholds9_312.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_312.drop 5) (by decide +kernel)

theorem valid9_312 : thresholds9_312.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_312 5 valid9_312_0 (valid9_312_5)

theorem valid9_318 : thresholds9_318.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_318 (by decide +kernel)

private theorem valid9_324_0 : (thresholds9_324.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_324.take 5) (by decide +kernel)

private theorem valid9_324_5 : (thresholds9_324.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_324.drop 5) (by decide +kernel)

theorem valid9_324 : thresholds9_324.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_324 5 valid9_324_0 (valid9_324_5)

theorem valid9_330 : thresholds9_330.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_330 (by decide +kernel)

private theorem valid9_336_0 : (thresholds9_336.take 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_336.take 5) (by decide +kernel)

private theorem valid9_336_5 : (thresholds9_336.drop 5).all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 (thresholds9_336.drop 5) (by decide +kernel)

theorem valid9_336 : thresholds9_336.all (checked ⟨9,3,1⟩)=true :=
  all_take_drop (checked ⟨9,3,1⟩) thresholds9_336 5 valid9_336_0 (valid9_336_5)

theorem valid9_342 : thresholds9_342.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_342 (by decide +kernel)

theorem valid9_348 : thresholds9_348.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_348 (by decide +kernel)

theorem valid9_354 : thresholds9_354.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_354 (by decide +kernel)

theorem valid9_360 : thresholds9_360.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_360 (by decide +kernel)

theorem valid9_366 : thresholds9_366.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_366 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part004

section Pack_Z6970H2307PackedBand09Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid9_372 : thresholds9_372.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_372 (by decide +kernel)

theorem valid9_378 : thresholds9_378.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_378 (by decide +kernel)

theorem valid9_384 : thresholds9_384.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_384 (by decide +kernel)

theorem valid9_390 : thresholds9_390.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_390 (by decide +kernel)

theorem valid9_396 : thresholds9_396.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_396 (by decide +kernel)

theorem valid9_402 : thresholds9_402.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_402 (by decide +kernel)

theorem valid9_408 : thresholds9_408.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_408 (by decide +kernel)

theorem valid9_414 : thresholds9_414.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_414 (by decide +kernel)

theorem valid9_420 : thresholds9_420.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_420 (by decide +kernel)

theorem valid9_426 : thresholds9_426.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_426 (by decide +kernel)

theorem valid9_432 : thresholds9_432.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_432 (by decide +kernel)

theorem valid9_438 : thresholds9_438.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_438 (by decide +kernel)

theorem valid9_444 : thresholds9_444.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_444 (by decide +kernel)

theorem valid9_450 : thresholds9_450.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_450 (by decide +kernel)

theorem valid9_456 : thresholds9_456.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_456 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part005

section Pack_Z6970H2307PackedBand09Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid9_462 : thresholds9_462.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_462 (by decide +kernel)

theorem valid9_468 : thresholds9_468.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_468 (by decide +kernel)

theorem valid9_474 : thresholds9_474.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_474 (by decide +kernel)

theorem valid9_480 : thresholds9_480.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_480 (by decide +kernel)

theorem valid9_486 : thresholds9_486.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_486 (by decide +kernel)

theorem valid9_492 : thresholds9_492.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_492 (by decide +kernel)

theorem valid9_498 : thresholds9_498.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_498 (by decide +kernel)

theorem valid9_504 : thresholds9_504.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_504 (by decide +kernel)

theorem valid9_510 : thresholds9_510.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_510 (by decide +kernel)

theorem valid9_516 : thresholds9_516.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_516 (by decide +kernel)

theorem valid9_522 : thresholds9_522.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_522 (by decide +kernel)

theorem valid9_528 : thresholds9_528.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_528 (by decide +kernel)

theorem valid9_534 : thresholds9_534.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_534 (by decide +kernel)

theorem valid9_540 : thresholds9_540.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_540 (by decide +kernel)

theorem valid9_546 : thresholds9_546.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_546 (by decide +kernel)

theorem valid9_552 : thresholds9_552.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_552 (by decide +kernel)

theorem valid9_558 : thresholds9_558.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_558 (by decide +kernel)

theorem valid9_564 : thresholds9_564.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_564 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part006

section Pack_Z6970H2307PackedBand09Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid9_570 : thresholds9_570.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_570 (by decide +kernel)

theorem valid9_576 : thresholds9_576.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_576 (by decide +kernel)

theorem valid9_582 : thresholds9_582.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_582 (by decide +kernel)

theorem valid9_588 : thresholds9_588.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_588 (by decide +kernel)

theorem valid9_594 : thresholds9_594.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_594 (by decide +kernel)

theorem valid9_600 : thresholds9_600.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_600 (by decide +kernel)

theorem valid9_606 : thresholds9_606.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_606 (by decide +kernel)

theorem valid9_612 : thresholds9_612.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_612 (by decide +kernel)

theorem valid9_618 : thresholds9_618.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_618 (by decide +kernel)

theorem valid9_624 : thresholds9_624.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_624 (by decide +kernel)

theorem valid9_630 : thresholds9_630.all (checked ⟨9,3,1⟩)=true :=
  checkedVerified ⟨9,3,1⟩ prefixMap9 thresholds9_630 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand09Part007

section Pack_Z6970H2307PackedBand10Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid10_0_0 : (thresholds10_0.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_0.take 4) (by decide +kernel)

private theorem valid10_0_4 : (thresholds10_0.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_0.drop 4) (by decide +kernel)

theorem valid10_0 : thresholds10_0.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_0 4 valid10_0_0 (valid10_0_4)

theorem valid10_6 : thresholds10_6.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_6 (by decide +kernel)

theorem valid10_12 : thresholds10_12.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_12 (by decide +kernel)

theorem valid10_18 : thresholds10_18.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_18 (by decide +kernel)

theorem valid10_24 : thresholds10_24.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_24 (by decide +kernel)

private theorem valid10_30_0 : (thresholds10_30.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_30.take 4) (by decide +kernel)

private theorem valid10_30_4 : (thresholds10_30.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_30.drop 4) (by decide +kernel)

theorem valid10_30 : thresholds10_30.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_30 4 valid10_30_0 (valid10_30_4)

private theorem valid10_36_0 : (thresholds10_36.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_36.take 5) (by decide +kernel)

private theorem valid10_36_5 : (thresholds10_36.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_36.drop 5) (by decide +kernel)

theorem valid10_36 : thresholds10_36.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_36 5 valid10_36_0 (valid10_36_5)

private theorem valid10_42_0 : (thresholds10_42.take 2).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_42.take 2) (by decide +kernel)

private theorem valid10_42_2 : ((thresholds10_42.drop 2).take 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 ((thresholds10_42.drop 2).take 3) (by decide +kernel)

private theorem valid10_42_5 : (thresholds10_42.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_42.drop 5) (by decide +kernel)

theorem valid10_42 : thresholds10_42.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_42 2 valid10_42_0 (all_take_drop (checked ⟨2,4,1⟩) (thresholds10_42.drop 2) 3 valid10_42_2 (valid10_42_5))

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part000

section Pack_Z6970H2307PackedBand10Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid10_48_0 : (thresholds10_48.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_48.take 5) (by decide +kernel)

private theorem valid10_48_5 : (thresholds10_48.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_48.drop 5) (by decide +kernel)

theorem valid10_48 : thresholds10_48.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_48 5 valid10_48_0 (valid10_48_5)

private theorem valid10_54_0 : (thresholds10_54.take 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_54.take 3) (by decide +kernel)

private theorem valid10_54_3 : (thresholds10_54.drop 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_54.drop 3) (by decide +kernel)

theorem valid10_54 : thresholds10_54.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_54 3 valid10_54_0 (valid10_54_3)

private theorem valid10_60_0 : (thresholds10_60.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_60.take 4) (by decide +kernel)

private theorem valid10_60_4 : (thresholds10_60.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_60.drop 4) (by decide +kernel)

theorem valid10_60 : thresholds10_60.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_60 4 valid10_60_0 (valid10_60_4)

private theorem valid10_66_0 : (thresholds10_66.take 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_66.take 3) (by decide +kernel)

private theorem valid10_66_3 : (thresholds10_66.drop 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_66.drop 3) (by decide +kernel)

theorem valid10_66 : thresholds10_66.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_66 3 valid10_66_0 (valid10_66_3)

private theorem valid10_72_0 : (thresholds10_72.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_72.take 4) (by decide +kernel)

private theorem valid10_72_4 : ((thresholds10_72.drop 4).take 1).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 ((thresholds10_72.drop 4).take 1) (by decide +kernel)

private theorem valid10_72_5 : (thresholds10_72.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_72.drop 5) (by decide +kernel)

theorem valid10_72 : thresholds10_72.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_72 4 valid10_72_0 (all_take_drop (checked ⟨2,4,1⟩) (thresholds10_72.drop 4) 1 valid10_72_4 (valid10_72_5))

private theorem valid10_78_0 : (thresholds10_78.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_78.take 4) (by decide +kernel)

private theorem valid10_78_4 : (thresholds10_78.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_78.drop 4) (by decide +kernel)

theorem valid10_78 : thresholds10_78.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_78 4 valid10_78_0 (valid10_78_4)

private theorem valid10_84_0 : (thresholds10_84.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_84.take 4) (by decide +kernel)

private theorem valid10_84_4 : (thresholds10_84.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_84.drop 4) (by decide +kernel)

theorem valid10_84 : thresholds10_84.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_84 4 valid10_84_0 (valid10_84_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part001

section Pack_Z6970H2307PackedBand10Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid10_90_0 : (thresholds10_90.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_90.take 4) (by decide +kernel)

private theorem valid10_90_4 : (thresholds10_90.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_90.drop 4) (by decide +kernel)

theorem valid10_90 : thresholds10_90.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_90 4 valid10_90_0 (valid10_90_4)

private theorem valid10_96_0 : (thresholds10_96.take 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_96.take 3) (by decide +kernel)

private theorem valid10_96_3 : (thresholds10_96.drop 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_96.drop 3) (by decide +kernel)

theorem valid10_96 : thresholds10_96.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_96 3 valid10_96_0 (valid10_96_3)

private theorem valid10_102_0 : (thresholds10_102.take 2).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_102.take 2) (by decide +kernel)

private theorem valid10_102_2 : ((thresholds10_102.drop 2).take 2).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 ((thresholds10_102.drop 2).take 2) (by decide +kernel)

private theorem valid10_102_4 : (thresholds10_102.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_102.drop 4) (by decide +kernel)

theorem valid10_102 : thresholds10_102.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_102 2 valid10_102_0 (all_take_drop (checked ⟨2,4,1⟩) (thresholds10_102.drop 2) 2 valid10_102_2 (valid10_102_4))

private theorem valid10_108_0 : (thresholds10_108.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_108.take 5) (by decide +kernel)

private theorem valid10_108_5 : (thresholds10_108.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_108.drop 5) (by decide +kernel)

theorem valid10_108 : thresholds10_108.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_108 5 valid10_108_0 (valid10_108_5)

private theorem valid10_114_0 : (thresholds10_114.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_114.take 5) (by decide +kernel)

private theorem valid10_114_5 : (thresholds10_114.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_114.drop 5) (by decide +kernel)

theorem valid10_114 : thresholds10_114.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_114 5 valid10_114_0 (valid10_114_5)

private theorem valid10_120_0 : (thresholds10_120.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_120.take 5) (by decide +kernel)

private theorem valid10_120_5 : (thresholds10_120.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_120.drop 5) (by decide +kernel)

theorem valid10_120 : thresholds10_120.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_120 5 valid10_120_0 (valid10_120_5)

private theorem valid10_126_0 : (thresholds10_126.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_126.take 4) (by decide +kernel)

private theorem valid10_126_4 : (thresholds10_126.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_126.drop 4) (by decide +kernel)

theorem valid10_126 : thresholds10_126.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_126 4 valid10_126_0 (valid10_126_4)

private theorem valid10_132_0 : (thresholds10_132.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_132.take 4) (by decide +kernel)

private theorem valid10_132_4 : (thresholds10_132.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_132.drop 4) (by decide +kernel)

theorem valid10_132 : thresholds10_132.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_132 4 valid10_132_0 (valid10_132_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part002

section Pack_Z6970H2307PackedBand10Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid10_138_0 : (thresholds10_138.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_138.take 5) (by decide +kernel)

private theorem valid10_138_5 : (thresholds10_138.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_138.drop 5) (by decide +kernel)

theorem valid10_138 : thresholds10_138.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_138 5 valid10_138_0 (valid10_138_5)

private theorem valid10_144_0 : (thresholds10_144.take 2).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_144.take 2) (by decide +kernel)

private theorem valid10_144_2 : (thresholds10_144.drop 2).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_144.drop 2) (by decide +kernel)

theorem valid10_144 : thresholds10_144.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_144 2 valid10_144_0 (valid10_144_2)

private theorem valid10_150_0 : (thresholds10_150.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_150.take 4) (by decide +kernel)

private theorem valid10_150_4 : (thresholds10_150.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_150.drop 4) (by decide +kernel)

theorem valid10_150 : thresholds10_150.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_150 4 valid10_150_0 (valid10_150_4)

private theorem valid10_156_0 : (thresholds10_156.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_156.take 4) (by decide +kernel)

private theorem valid10_156_4 : (thresholds10_156.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_156.drop 4) (by decide +kernel)

theorem valid10_156 : thresholds10_156.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_156 4 valid10_156_0 (valid10_156_4)

private theorem valid10_162_0 : (thresholds10_162.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_162.take 4) (by decide +kernel)

private theorem valid10_162_4 : (thresholds10_162.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_162.drop 4) (by decide +kernel)

theorem valid10_162 : thresholds10_162.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_162 4 valid10_162_0 (valid10_162_4)

private theorem valid10_168_0 : (thresholds10_168.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_168.take 4) (by decide +kernel)

private theorem valid10_168_4 : (thresholds10_168.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_168.drop 4) (by decide +kernel)

theorem valid10_168 : thresholds10_168.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_168 4 valid10_168_0 (valid10_168_4)

private theorem valid10_174_0 : (thresholds10_174.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_174.take 5) (by decide +kernel)

private theorem valid10_174_5 : (thresholds10_174.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_174.drop 5) (by decide +kernel)

theorem valid10_174 : thresholds10_174.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_174 5 valid10_174_0 (valid10_174_5)

private theorem valid10_180_0 : (thresholds10_180.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_180.take 5) (by decide +kernel)

private theorem valid10_180_5 : (thresholds10_180.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_180.drop 5) (by decide +kernel)

theorem valid10_180 : thresholds10_180.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_180 5 valid10_180_0 (valid10_180_5)

private theorem valid10_186_0 : (thresholds10_186.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_186.take 5) (by decide +kernel)

private theorem valid10_186_5 : (thresholds10_186.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_186.drop 5) (by decide +kernel)

theorem valid10_186 : thresholds10_186.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_186 5 valid10_186_0 (valid10_186_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part003

section Pack_Z6970H2307PackedBand10Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid10_192_0 : (thresholds10_192.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_192.take 5) (by decide +kernel)

private theorem valid10_192_5 : (thresholds10_192.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_192.drop 5) (by decide +kernel)

theorem valid10_192 : thresholds10_192.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_192 5 valid10_192_0 (valid10_192_5)

private theorem valid10_198_0 : (thresholds10_198.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_198.take 5) (by decide +kernel)

private theorem valid10_198_5 : (thresholds10_198.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_198.drop 5) (by decide +kernel)

theorem valid10_198 : thresholds10_198.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_198 5 valid10_198_0 (valid10_198_5)

private theorem valid10_204_0 : (thresholds10_204.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_204.take 5) (by decide +kernel)

private theorem valid10_204_5 : (thresholds10_204.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_204.drop 5) (by decide +kernel)

theorem valid10_204 : thresholds10_204.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_204 5 valid10_204_0 (valid10_204_5)

private theorem valid10_210_0 : (thresholds10_210.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_210.take 4) (by decide +kernel)

private theorem valid10_210_4 : (thresholds10_210.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_210.drop 4) (by decide +kernel)

theorem valid10_210 : thresholds10_210.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_210 4 valid10_210_0 (valid10_210_4)

private theorem valid10_216_0 : (thresholds10_216.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_216.take 4) (by decide +kernel)

private theorem valid10_216_4 : (thresholds10_216.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_216.drop 4) (by decide +kernel)

theorem valid10_216 : thresholds10_216.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_216 4 valid10_216_0 (valid10_216_4)

private theorem valid10_222_0 : (thresholds10_222.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_222.take 5) (by decide +kernel)

private theorem valid10_222_5 : (thresholds10_222.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_222.drop 5) (by decide +kernel)

theorem valid10_222 : thresholds10_222.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_222 5 valid10_222_0 (valid10_222_5)

private theorem valid10_228_0 : (thresholds10_228.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_228.take 4) (by decide +kernel)

private theorem valid10_228_4 : (thresholds10_228.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_228.drop 4) (by decide +kernel)

theorem valid10_228 : thresholds10_228.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_228 4 valid10_228_0 (valid10_228_4)

private theorem valid10_234_0 : (thresholds10_234.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_234.take 4) (by decide +kernel)

private theorem valid10_234_4 : (thresholds10_234.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_234.drop 4) (by decide +kernel)

theorem valid10_234 : thresholds10_234.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_234 4 valid10_234_0 (valid10_234_4)

private theorem valid10_240_0 : (thresholds10_240.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_240.take 5) (by decide +kernel)

private theorem valid10_240_5 : (thresholds10_240.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_240.drop 5) (by decide +kernel)

theorem valid10_240 : thresholds10_240.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_240 5 valid10_240_0 (valid10_240_5)

private theorem valid10_246_0 : (thresholds10_246.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_246.take 4) (by decide +kernel)

private theorem valid10_246_4 : (thresholds10_246.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_246.drop 4) (by decide +kernel)

theorem valid10_246 : thresholds10_246.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_246 4 valid10_246_0 (valid10_246_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part004

section Pack_Z6970H2307PackedBand10Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid10_252_0 : (thresholds10_252.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_252.take 5) (by decide +kernel)

private theorem valid10_252_5 : (thresholds10_252.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_252.drop 5) (by decide +kernel)

theorem valid10_252 : thresholds10_252.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_252 5 valid10_252_0 (valid10_252_5)

private theorem valid10_258_0 : (thresholds10_258.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_258.take 5) (by decide +kernel)

private theorem valid10_258_5 : (thresholds10_258.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_258.drop 5) (by decide +kernel)

theorem valid10_258 : thresholds10_258.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_258 5 valid10_258_0 (valid10_258_5)

private theorem valid10_264_0 : (thresholds10_264.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_264.take 5) (by decide +kernel)

private theorem valid10_264_5 : (thresholds10_264.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_264.drop 5) (by decide +kernel)

theorem valid10_264 : thresholds10_264.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_264 5 valid10_264_0 (valid10_264_5)

private theorem valid10_270_0 : (thresholds10_270.take 3).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_270.take 3) (by decide +kernel)

private theorem valid10_270_3 : ((thresholds10_270.drop 3).take 1).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 ((thresholds10_270.drop 3).take 1) (by decide +kernel)

private theorem valid10_270_4 : (thresholds10_270.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_270.drop 4) (by decide +kernel)

theorem valid10_270 : thresholds10_270.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_270 3 valid10_270_0 (all_take_drop (checked ⟨2,4,1⟩) (thresholds10_270.drop 3) 1 valid10_270_3 (valid10_270_4))

theorem valid10_276 : thresholds10_276.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_276 (by decide +kernel)

theorem valid10_282 : thresholds10_282.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_282 (by decide +kernel)

private theorem valid10_288_0 : (thresholds10_288.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_288.take 4) (by decide +kernel)

private theorem valid10_288_4 : (thresholds10_288.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_288.drop 4) (by decide +kernel)

theorem valid10_288 : thresholds10_288.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_288 4 valid10_288_0 (valid10_288_4)

private theorem valid10_294_0 : (thresholds10_294.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_294.take 5) (by decide +kernel)

private theorem valid10_294_5 : (thresholds10_294.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_294.drop 5) (by decide +kernel)

theorem valid10_294 : thresholds10_294.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_294 5 valid10_294_0 (valid10_294_5)

theorem valid10_300 : thresholds10_300.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_300 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part005

section Pack_Z6970H2307PackedBand10Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid10_306 : thresholds10_306.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_306 (by decide +kernel)

private theorem valid10_312_0 : (thresholds10_312.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_312.take 5) (by decide +kernel)

private theorem valid10_312_5 : (thresholds10_312.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_312.drop 5) (by decide +kernel)

theorem valid10_312 : thresholds10_312.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_312 5 valid10_312_0 (valid10_312_5)

private theorem valid10_318_0 : (thresholds10_318.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_318.take 5) (by decide +kernel)

private theorem valid10_318_5 : (thresholds10_318.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_318.drop 5) (by decide +kernel)

theorem valid10_318 : thresholds10_318.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_318 5 valid10_318_0 (valid10_318_5)

theorem valid10_324 : thresholds10_324.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_324 (by decide +kernel)

private theorem valid10_330_0 : (thresholds10_330.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_330.take 5) (by decide +kernel)

private theorem valid10_330_5 : (thresholds10_330.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_330.drop 5) (by decide +kernel)

theorem valid10_330 : thresholds10_330.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_330 5 valid10_330_0 (valid10_330_5)

theorem valid10_336 : thresholds10_336.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_336 (by decide +kernel)

private theorem valid10_342_0 : (thresholds10_342.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_342.take 5) (by decide +kernel)

private theorem valid10_342_5 : (thresholds10_342.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_342.drop 5) (by decide +kernel)

theorem valid10_342 : thresholds10_342.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_342 5 valid10_342_0 (valid10_342_5)

theorem valid10_348 : thresholds10_348.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_348 (by decide +kernel)

theorem valid10_354 : thresholds10_354.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_354 (by decide +kernel)

theorem valid10_360 : thresholds10_360.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_360 (by decide +kernel)

private theorem valid10_366_0 : (thresholds10_366.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_366.take 5) (by decide +kernel)

private theorem valid10_366_5 : (thresholds10_366.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_366.drop 5) (by decide +kernel)

theorem valid10_366 : thresholds10_366.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_366 5 valid10_366_0 (valid10_366_5)

theorem valid10_372 : thresholds10_372.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_372 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part006

section Pack_Z6970H2307PackedBand10Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid10_378_0 : (thresholds10_378.take 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_378.take 4) (by decide +kernel)

private theorem valid10_378_4 : (thresholds10_378.drop 4).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_378.drop 4) (by decide +kernel)

theorem valid10_378 : thresholds10_378.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_378 4 valid10_378_0 (valid10_378_4)

theorem valid10_384 : thresholds10_384.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_384 (by decide +kernel)

theorem valid10_390 : thresholds10_390.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_390 (by decide +kernel)

private theorem valid10_396_0 : (thresholds10_396.take 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_396.take 5) (by decide +kernel)

private theorem valid10_396_5 : (thresholds10_396.drop 5).all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 (thresholds10_396.drop 5) (by decide +kernel)

theorem valid10_396 : thresholds10_396.all (checked ⟨2,4,1⟩)=true :=
  all_take_drop (checked ⟨2,4,1⟩) thresholds10_396 5 valid10_396_0 (valid10_396_5)

theorem valid10_402 : thresholds10_402.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_402 (by decide +kernel)

theorem valid10_408 : thresholds10_408.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_408 (by decide +kernel)

theorem valid10_414 : thresholds10_414.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_414 (by decide +kernel)

theorem valid10_420 : thresholds10_420.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_420 (by decide +kernel)

theorem valid10_426 : thresholds10_426.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_426 (by decide +kernel)

theorem valid10_432 : thresholds10_432.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_432 (by decide +kernel)

theorem valid10_438 : thresholds10_438.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_438 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part007

section Pack_Z6970H2307PackedBand10Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid10_444 : thresholds10_444.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_444 (by decide +kernel)

theorem valid10_450 : thresholds10_450.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_450 (by decide +kernel)

theorem valid10_456 : thresholds10_456.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_456 (by decide +kernel)

theorem valid10_462 : thresholds10_462.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_462 (by decide +kernel)

theorem valid10_468 : thresholds10_468.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_468 (by decide +kernel)

theorem valid10_474 : thresholds10_474.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_474 (by decide +kernel)

theorem valid10_480 : thresholds10_480.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_480 (by decide +kernel)

theorem valid10_486 : thresholds10_486.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_486 (by decide +kernel)

theorem valid10_492 : thresholds10_492.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_492 (by decide +kernel)

theorem valid10_498 : thresholds10_498.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_498 (by decide +kernel)

theorem valid10_504 : thresholds10_504.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_504 (by decide +kernel)

theorem valid10_510 : thresholds10_510.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_510 (by decide +kernel)

theorem valid10_516 : thresholds10_516.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_516 (by decide +kernel)

theorem valid10_522 : thresholds10_522.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_522 (by decide +kernel)

theorem valid10_528 : thresholds10_528.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_528 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part008

section Pack_Z6970H2307PackedBand10Part009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid10_534 : thresholds10_534.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_534 (by decide +kernel)

theorem valid10_540 : thresholds10_540.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_540 (by decide +kernel)

theorem valid10_546 : thresholds10_546.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_546 (by decide +kernel)

theorem valid10_552 : thresholds10_552.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_552 (by decide +kernel)

theorem valid10_558 : thresholds10_558.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_558 (by decide +kernel)

theorem valid10_564 : thresholds10_564.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_564 (by decide +kernel)

theorem valid10_570 : thresholds10_570.all (checked ⟨2,4,1⟩)=true :=
  checkedVerified ⟨2,4,1⟩ prefixMap10 thresholds10_570 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand10Part009

section Pack_Z6970H2307PackedBand11Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid11_0_0 : (thresholds11_0.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_0.take 4) (by decide +kernel)

private theorem valid11_0_4 : (thresholds11_0.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_0.drop 4) (by decide +kernel)

theorem valid11_0 : thresholds11_0.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_0 4 valid11_0_0 (valid11_0_4)

theorem valid11_6 : thresholds11_6.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_6 (by decide +kernel)

theorem valid11_12 : thresholds11_12.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_12 (by decide +kernel)

theorem valid11_18 : thresholds11_18.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_18 (by decide +kernel)

theorem valid11_24 : thresholds11_24.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_24 (by decide +kernel)

private theorem valid11_30_0 : (thresholds11_30.take 1).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_30.take 1) (by decide +kernel)

private theorem valid11_30_1 : ((thresholds11_30.drop 1).take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 ((thresholds11_30.drop 1).take 4) (by decide +kernel)

private theorem valid11_30_5 : (thresholds11_30.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_30.drop 5) (by decide +kernel)

theorem valid11_30 : thresholds11_30.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_30 1 valid11_30_0 (all_take_drop (checked ⟨3,4,1⟩) (thresholds11_30.drop 1) 4 valid11_30_1 (valid11_30_5))

private theorem valid11_36_0 : (thresholds11_36.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_36.take 5) (by decide +kernel)

private theorem valid11_36_5 : (thresholds11_36.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_36.drop 5) (by decide +kernel)

theorem valid11_36 : thresholds11_36.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_36 5 valid11_36_0 (valid11_36_5)

private theorem valid11_42_0 : (thresholds11_42.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_42.take 5) (by decide +kernel)

private theorem valid11_42_5 : (thresholds11_42.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_42.drop 5) (by decide +kernel)

theorem valid11_42 : thresholds11_42.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_42 5 valid11_42_0 (valid11_42_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part000

section Pack_Z6970H2307PackedBand11Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid11_48_0 : (thresholds11_48.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_48.take 4) (by decide +kernel)

private theorem valid11_48_4 : (thresholds11_48.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_48.drop 4) (by decide +kernel)

theorem valid11_48 : thresholds11_48.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_48 4 valid11_48_0 (valid11_48_4)

private theorem valid11_54_0 : (thresholds11_54.take 1).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_54.take 1) (by decide +kernel)

private theorem valid11_54_1 : ((thresholds11_54.drop 1).take 1).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 ((thresholds11_54.drop 1).take 1) (by decide +kernel)

private theorem valid11_54_2 : (thresholds11_54.drop 2).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_54.drop 2) (by decide +kernel)

theorem valid11_54 : thresholds11_54.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_54 1 valid11_54_0 (all_take_drop (checked ⟨3,4,1⟩) (thresholds11_54.drop 1) 1 valid11_54_1 (valid11_54_2))

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part001

section Pack_Z6970H2307PackedBand11Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid11_60_0 : (thresholds11_60.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_60.take 4) (by decide +kernel)

private theorem valid11_60_4 : (thresholds11_60.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_60.drop 4) (by decide +kernel)

theorem valid11_60 : thresholds11_60.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_60 4 valid11_60_0 (valid11_60_4)

private theorem valid11_66_0 : (thresholds11_66.take 1).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_66.take 1) (by decide +kernel)

private theorem valid11_66_1 : ((thresholds11_66.drop 1).take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 ((thresholds11_66.drop 1).take 4) (by decide +kernel)

private theorem valid11_66_5 : (thresholds11_66.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_66.drop 5) (by decide +kernel)

theorem valid11_66 : thresholds11_66.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_66 1 valid11_66_0 (all_take_drop (checked ⟨3,4,1⟩) (thresholds11_66.drop 1) 4 valid11_66_1 (valid11_66_5))

private theorem valid11_72_0 : (thresholds11_72.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_72.take 4) (by decide +kernel)

private theorem valid11_72_4 : (thresholds11_72.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_72.drop 4) (by decide +kernel)

theorem valid11_72 : thresholds11_72.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_72 4 valid11_72_0 (valid11_72_4)

private theorem valid11_78_0 : (thresholds11_78.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_78.take 5) (by decide +kernel)

private theorem valid11_78_5 : (thresholds11_78.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_78.drop 5) (by decide +kernel)

theorem valid11_78 : thresholds11_78.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_78 5 valid11_78_0 (valid11_78_5)

private theorem valid11_84_0 : (thresholds11_84.take 3).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_84.take 3) (by decide +kernel)

private theorem valid11_84_3 : (thresholds11_84.drop 3).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_84.drop 3) (by decide +kernel)

theorem valid11_84 : thresholds11_84.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_84 3 valid11_84_0 (valid11_84_3)

private theorem valid11_90_0 : (thresholds11_90.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_90.take 4) (by decide +kernel)

private theorem valid11_90_4 : (thresholds11_90.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_90.drop 4) (by decide +kernel)

theorem valid11_90 : thresholds11_90.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_90 4 valid11_90_0 (valid11_90_4)

private theorem valid11_96_0 : (thresholds11_96.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_96.take 5) (by decide +kernel)

private theorem valid11_96_5 : (thresholds11_96.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_96.drop 5) (by decide +kernel)

theorem valid11_96 : thresholds11_96.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_96 5 valid11_96_0 (valid11_96_5)

private theorem valid11_102_0 : (thresholds11_102.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_102.take 4) (by decide +kernel)

private theorem valid11_102_4 : (thresholds11_102.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_102.drop 4) (by decide +kernel)

theorem valid11_102 : thresholds11_102.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_102 4 valid11_102_0 (valid11_102_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part002

section Pack_Z6970H2307PackedBand11Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid11_108_0 : (thresholds11_108.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_108.take 4) (by decide +kernel)

private theorem valid11_108_4 : (thresholds11_108.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_108.drop 4) (by decide +kernel)

theorem valid11_108 : thresholds11_108.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_108 4 valid11_108_0 (valid11_108_4)

private theorem valid11_114_0 : (thresholds11_114.take 3).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_114.take 3) (by decide +kernel)

private theorem valid11_114_3 : (thresholds11_114.drop 3).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_114.drop 3) (by decide +kernel)

theorem valid11_114 : thresholds11_114.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_114 3 valid11_114_0 (valid11_114_3)

private theorem valid11_120_0 : (thresholds11_120.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_120.take 4) (by decide +kernel)

private theorem valid11_120_4 : (thresholds11_120.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_120.drop 4) (by decide +kernel)

theorem valid11_120 : thresholds11_120.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_120 4 valid11_120_0 (valid11_120_4)

private theorem valid11_126_0 : (thresholds11_126.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_126.take 4) (by decide +kernel)

private theorem valid11_126_4 : (thresholds11_126.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_126.drop 4) (by decide +kernel)

theorem valid11_126 : thresholds11_126.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_126 4 valid11_126_0 (valid11_126_4)

private theorem valid11_132_0 : (thresholds11_132.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_132.take 5) (by decide +kernel)

private theorem valid11_132_5 : (thresholds11_132.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_132.drop 5) (by decide +kernel)

theorem valid11_132 : thresholds11_132.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_132 5 valid11_132_0 (valid11_132_5)

private theorem valid11_138_0 : (thresholds11_138.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_138.take 4) (by decide +kernel)

private theorem valid11_138_4 : (thresholds11_138.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_138.drop 4) (by decide +kernel)

theorem valid11_138 : thresholds11_138.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_138 4 valid11_138_0 (valid11_138_4)

private theorem valid11_144_0 : (thresholds11_144.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_144.take 5) (by decide +kernel)

private theorem valid11_144_5 : (thresholds11_144.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_144.drop 5) (by decide +kernel)

theorem valid11_144 : thresholds11_144.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_144 5 valid11_144_0 (valid11_144_5)

private theorem valid11_150_0 : (thresholds11_150.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_150.take 4) (by decide +kernel)

private theorem valid11_150_4 : (thresholds11_150.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_150.drop 4) (by decide +kernel)

theorem valid11_150 : thresholds11_150.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_150 4 valid11_150_0 (valid11_150_4)

private theorem valid11_156_0 : (thresholds11_156.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_156.take 5) (by decide +kernel)

private theorem valid11_156_5 : (thresholds11_156.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_156.drop 5) (by decide +kernel)

theorem valid11_156 : thresholds11_156.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_156 5 valid11_156_0 (valid11_156_5)

private theorem valid11_162_0 : (thresholds11_162.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_162.take 4) (by decide +kernel)

private theorem valid11_162_4 : (thresholds11_162.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_162.drop 4) (by decide +kernel)

theorem valid11_162 : thresholds11_162.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_162 4 valid11_162_0 (valid11_162_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part003

section Pack_Z6970H2307PackedBand11Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid11_168_0 : (thresholds11_168.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_168.take 5) (by decide +kernel)

private theorem valid11_168_5 : (thresholds11_168.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_168.drop 5) (by decide +kernel)

theorem valid11_168 : thresholds11_168.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_168 5 valid11_168_0 (valid11_168_5)

private theorem valid11_174_0 : (thresholds11_174.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_174.take 5) (by decide +kernel)

private theorem valid11_174_5 : (thresholds11_174.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_174.drop 5) (by decide +kernel)

theorem valid11_174 : thresholds11_174.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_174 5 valid11_174_0 (valid11_174_5)

private theorem valid11_180_0 : (thresholds11_180.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_180.take 5) (by decide +kernel)

private theorem valid11_180_5 : (thresholds11_180.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_180.drop 5) (by decide +kernel)

theorem valid11_180 : thresholds11_180.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_180 5 valid11_180_0 (valid11_180_5)

private theorem valid11_186_0 : (thresholds11_186.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_186.take 5) (by decide +kernel)

private theorem valid11_186_5 : (thresholds11_186.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_186.drop 5) (by decide +kernel)

theorem valid11_186 : thresholds11_186.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_186 5 valid11_186_0 (valid11_186_5)

theorem valid11_192 : thresholds11_192.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_192 (by decide +kernel)

private theorem valid11_198_0 : (thresholds11_198.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_198.take 4) (by decide +kernel)

private theorem valid11_198_4 : (thresholds11_198.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_198.drop 4) (by decide +kernel)

theorem valid11_198 : thresholds11_198.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_198 4 valid11_198_0 (valid11_198_4)

private theorem valid11_204_0 : (thresholds11_204.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_204.take 4) (by decide +kernel)

private theorem valid11_204_4 : (thresholds11_204.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_204.drop 4) (by decide +kernel)

theorem valid11_204 : thresholds11_204.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_204 4 valid11_204_0 (valid11_204_4)

private theorem valid11_210_0 : (thresholds11_210.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_210.take 5) (by decide +kernel)

private theorem valid11_210_5 : (thresholds11_210.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_210.drop 5) (by decide +kernel)

theorem valid11_210 : thresholds11_210.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_210 5 valid11_210_0 (valid11_210_5)

theorem valid11_216 : thresholds11_216.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_216 (by decide +kernel)

private theorem valid11_222_0 : (thresholds11_222.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_222.take 5) (by decide +kernel)

private theorem valid11_222_5 : (thresholds11_222.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_222.drop 5) (by decide +kernel)

theorem valid11_222 : thresholds11_222.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_222 5 valid11_222_0 (valid11_222_5)

theorem valid11_228 : thresholds11_228.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_228 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part004

section Pack_Z6970H2307PackedBand11Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid11_234_0 : (thresholds11_234.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_234.take 4) (by decide +kernel)

private theorem valid11_234_4 : (thresholds11_234.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_234.drop 4) (by decide +kernel)

theorem valid11_234 : thresholds11_234.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_234 4 valid11_234_0 (valid11_234_4)

theorem valid11_240 : thresholds11_240.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_240 (by decide +kernel)

private theorem valid11_246_0 : (thresholds11_246.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_246.take 5) (by decide +kernel)

private theorem valid11_246_5 : (thresholds11_246.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_246.drop 5) (by decide +kernel)

theorem valid11_246 : thresholds11_246.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_246 5 valid11_246_0 (valid11_246_5)

private theorem valid11_252_0 : (thresholds11_252.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_252.take 5) (by decide +kernel)

private theorem valid11_252_5 : (thresholds11_252.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_252.drop 5) (by decide +kernel)

theorem valid11_252 : thresholds11_252.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_252 5 valid11_252_0 (valid11_252_5)

private theorem valid11_258_0 : (thresholds11_258.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_258.take 5) (by decide +kernel)

private theorem valid11_258_5 : (thresholds11_258.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_258.drop 5) (by decide +kernel)

theorem valid11_258 : thresholds11_258.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_258 5 valid11_258_0 (valid11_258_5)

theorem valid11_264 : thresholds11_264.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_264 (by decide +kernel)

theorem valid11_270 : thresholds11_270.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_270 (by decide +kernel)

theorem valid11_276 : thresholds11_276.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_276 (by decide +kernel)

private theorem valid11_282_0 : (thresholds11_282.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_282.take 5) (by decide +kernel)

private theorem valid11_282_5 : (thresholds11_282.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_282.drop 5) (by decide +kernel)

theorem valid11_282 : thresholds11_282.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_282 5 valid11_282_0 (valid11_282_5)

theorem valid11_288 : thresholds11_288.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_288 (by decide +kernel)

theorem valid11_294 : thresholds11_294.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_294 (by decide +kernel)

private theorem valid11_300_0 : (thresholds11_300.take 3).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_300.take 3) (by decide +kernel)

private theorem valid11_300_3 : (thresholds11_300.drop 3).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_300.drop 3) (by decide +kernel)

theorem valid11_300 : thresholds11_300.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_300 3 valid11_300_0 (valid11_300_3)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part005

section Pack_Z6970H2307PackedBand11Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid11_306_0 : (thresholds11_306.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_306.take 5) (by decide +kernel)

private theorem valid11_306_5 : (thresholds11_306.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_306.drop 5) (by decide +kernel)

theorem valid11_306 : thresholds11_306.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_306 5 valid11_306_0 (valid11_306_5)

theorem valid11_312 : thresholds11_312.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_312 (by decide +kernel)

private theorem valid11_318_0 : (thresholds11_318.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_318.take 5) (by decide +kernel)

private theorem valid11_318_5 : (thresholds11_318.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_318.drop 5) (by decide +kernel)

theorem valid11_318 : thresholds11_318.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_318 5 valid11_318_0 (valid11_318_5)

private theorem valid11_324_0 : (thresholds11_324.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_324.take 4) (by decide +kernel)

private theorem valid11_324_4 : (thresholds11_324.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_324.drop 4) (by decide +kernel)

theorem valid11_324 : thresholds11_324.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_324 4 valid11_324_0 (valid11_324_4)

private theorem valid11_330_0 : (thresholds11_330.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_330.take 5) (by decide +kernel)

private theorem valid11_330_5 : (thresholds11_330.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_330.drop 5) (by decide +kernel)

theorem valid11_330 : thresholds11_330.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_330 5 valid11_330_0 (valid11_330_5)

private theorem valid11_336_0 : (thresholds11_336.take 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_336.take 4) (by decide +kernel)

private theorem valid11_336_4 : (thresholds11_336.drop 4).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_336.drop 4) (by decide +kernel)

theorem valid11_336 : thresholds11_336.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_336 4 valid11_336_0 (valid11_336_4)

theorem valid11_342 : thresholds11_342.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_342 (by decide +kernel)

theorem valid11_348 : thresholds11_348.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_348 (by decide +kernel)

theorem valid11_354 : thresholds11_354.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_354 (by decide +kernel)

theorem valid11_360 : thresholds11_360.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_360 (by decide +kernel)

theorem valid11_366 : thresholds11_366.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_366 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part006

section Pack_Z6970H2307PackedBand11Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid11_372 : thresholds11_372.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_372 (by decide +kernel)

theorem valid11_378 : thresholds11_378.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_378 (by decide +kernel)

theorem valid11_384 : thresholds11_384.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_384 (by decide +kernel)

theorem valid11_390 : thresholds11_390.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_390 (by decide +kernel)

theorem valid11_396 : thresholds11_396.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_396 (by decide +kernel)

theorem valid11_402 : thresholds11_402.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_402 (by decide +kernel)

theorem valid11_408 : thresholds11_408.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_408 (by decide +kernel)

theorem valid11_414 : thresholds11_414.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_414 (by decide +kernel)

theorem valid11_420 : thresholds11_420.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_420 (by decide +kernel)

private theorem valid11_426_0 : (thresholds11_426.take 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_426.take 5) (by decide +kernel)

private theorem valid11_426_5 : (thresholds11_426.drop 5).all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 (thresholds11_426.drop 5) (by decide +kernel)

theorem valid11_426 : thresholds11_426.all (checked ⟨3,4,1⟩)=true :=
  all_take_drop (checked ⟨3,4,1⟩) thresholds11_426 5 valid11_426_0 (valid11_426_5)

theorem valid11_432 : thresholds11_432.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_432 (by decide +kernel)

theorem valid11_438 : thresholds11_438.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_438 (by decide +kernel)

theorem valid11_444 : thresholds11_444.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_444 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part007

section Pack_Z6970H2307PackedBand11Part008

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid11_450 : thresholds11_450.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_450 (by decide +kernel)

theorem valid11_456 : thresholds11_456.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_456 (by decide +kernel)

theorem valid11_462 : thresholds11_462.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_462 (by decide +kernel)

theorem valid11_468 : thresholds11_468.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_468 (by decide +kernel)

theorem valid11_474 : thresholds11_474.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_474 (by decide +kernel)

theorem valid11_480 : thresholds11_480.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_480 (by decide +kernel)

theorem valid11_486 : thresholds11_486.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_486 (by decide +kernel)

theorem valid11_492 : thresholds11_492.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_492 (by decide +kernel)

theorem valid11_498 : thresholds11_498.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_498 (by decide +kernel)

theorem valid11_504 : thresholds11_504.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_504 (by decide +kernel)

theorem valid11_510 : thresholds11_510.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_510 (by decide +kernel)

theorem valid11_516 : thresholds11_516.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_516 (by decide +kernel)

theorem valid11_522 : thresholds11_522.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_522 (by decide +kernel)

theorem valid11_528 : thresholds11_528.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_528 (by decide +kernel)

theorem valid11_534 : thresholds11_534.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_534 (by decide +kernel)

theorem valid11_540 : thresholds11_540.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_540 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part008

section Pack_Z6970H2307PackedBand11Part009

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid11_546 : thresholds11_546.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_546 (by decide +kernel)

theorem valid11_552 : thresholds11_552.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_552 (by decide +kernel)

theorem valid11_558 : thresholds11_558.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_558 (by decide +kernel)

theorem valid11_564 : thresholds11_564.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_564 (by decide +kernel)

theorem valid11_570 : thresholds11_570.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_570 (by decide +kernel)

theorem valid11_576 : thresholds11_576.all (checked ⟨3,4,1⟩)=true :=
  checkedVerified ⟨3,4,1⟩ prefixMap11 thresholds11_576 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand11Part009

section Pack_Z6970H2307PackedBand12Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid12_0_0 : (thresholds12_0.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_0.take 4) (by decide +kernel)

private theorem valid12_0_4 : (thresholds12_0.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_0.drop 4) (by decide +kernel)

theorem valid12_0 : thresholds12_0.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_0 4 valid12_0_0 (valid12_0_4)

theorem valid12_6 : thresholds12_6.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_6 (by decide +kernel)

theorem valid12_12 : thresholds12_12.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_12 (by decide +kernel)

theorem valid12_18 : thresholds12_18.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_18 (by decide +kernel)

theorem valid12_24 : thresholds12_24.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_24 (by decide +kernel)

theorem valid12_30 : thresholds12_30.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_30 (by decide +kernel)

private theorem valid12_36_0 : (thresholds12_36.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_36.take 5) (by decide +kernel)

private theorem valid12_36_5 : (thresholds12_36.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_36.drop 5) (by decide +kernel)

theorem valid12_36 : thresholds12_36.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_36 5 valid12_36_0 (valid12_36_5)

private theorem valid12_42_0 : (thresholds12_42.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_42.take 4) (by decide +kernel)

private theorem valid12_42_4 : (thresholds12_42.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_42.drop 4) (by decide +kernel)

theorem valid12_42 : thresholds12_42.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_42 4 valid12_42_0 (valid12_42_4)

private theorem valid12_48_0 : (thresholds12_48.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_48.take 4) (by decide +kernel)

private theorem valid12_48_4 : (thresholds12_48.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_48.drop 4) (by decide +kernel)

theorem valid12_48 : thresholds12_48.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_48 4 valid12_48_0 (valid12_48_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part000

section Pack_Z6970H2307PackedBand12Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid12_54_0 : (thresholds12_54.take 3).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_54.take 3) (by decide +kernel)

private theorem valid12_54_3 : ((thresholds12_54.drop 3).take 1).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 ((thresholds12_54.drop 3).take 1) (by decide +kernel)

private theorem valid12_54_4 : (thresholds12_54.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_54.drop 4) (by decide +kernel)

theorem valid12_54 : thresholds12_54.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_54 3 valid12_54_0 (all_take_drop (checked ⟨4,4,1⟩) (thresholds12_54.drop 3) 1 valid12_54_3 (valid12_54_4))

private theorem valid12_60_0 : (thresholds12_60.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_60.take 4) (by decide +kernel)

private theorem valid12_60_4 : (thresholds12_60.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_60.drop 4) (by decide +kernel)

theorem valid12_60 : thresholds12_60.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_60 4 valid12_60_0 (valid12_60_4)

private theorem valid12_66_0 : (thresholds12_66.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_66.take 4) (by decide +kernel)

private theorem valid12_66_4 : (thresholds12_66.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_66.drop 4) (by decide +kernel)

theorem valid12_66 : thresholds12_66.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_66 4 valid12_66_0 (valid12_66_4)

private theorem valid12_72_0 : (thresholds12_72.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_72.take 4) (by decide +kernel)

private theorem valid12_72_4 : (thresholds12_72.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_72.drop 4) (by decide +kernel)

theorem valid12_72 : thresholds12_72.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_72 4 valid12_72_0 (valid12_72_4)

private theorem valid12_78_0 : (thresholds12_78.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_78.take 4) (by decide +kernel)

private theorem valid12_78_4 : (thresholds12_78.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_78.drop 4) (by decide +kernel)

theorem valid12_78 : thresholds12_78.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_78 4 valid12_78_0 (valid12_78_4)

private theorem valid12_84_0 : (thresholds12_84.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_84.take 4) (by decide +kernel)

private theorem valid12_84_4 : (thresholds12_84.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_84.drop 4) (by decide +kernel)

theorem valid12_84 : thresholds12_84.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_84 4 valid12_84_0 (valid12_84_4)

theorem valid12_90 : thresholds12_90.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_90 (by decide +kernel)

private theorem valid12_96_0 : (thresholds12_96.take 3).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_96.take 3) (by decide +kernel)

private theorem valid12_96_3 : (thresholds12_96.drop 3).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_96.drop 3) (by decide +kernel)

theorem valid12_96 : thresholds12_96.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_96 3 valid12_96_0 (valid12_96_3)

private theorem valid12_102_0 : (thresholds12_102.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_102.take 5) (by decide +kernel)

private theorem valid12_102_5 : (thresholds12_102.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_102.drop 5) (by decide +kernel)

theorem valid12_102 : thresholds12_102.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_102 5 valid12_102_0 (valid12_102_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part001

section Pack_Z6970H2307PackedBand12Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid12_108_0 : (thresholds12_108.take 3).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_108.take 3) (by decide +kernel)

private theorem valid12_108_3 : (thresholds12_108.drop 3).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_108.drop 3) (by decide +kernel)

theorem valid12_108 : thresholds12_108.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_108 3 valid12_108_0 (valid12_108_3)

private theorem valid12_114_0 : (thresholds12_114.take 3).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_114.take 3) (by decide +kernel)

private theorem valid12_114_3 : (thresholds12_114.drop 3).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_114.drop 3) (by decide +kernel)

theorem valid12_114 : thresholds12_114.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_114 3 valid12_114_0 (valid12_114_3)

private theorem valid12_120_0 : (thresholds12_120.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_120.take 4) (by decide +kernel)

private theorem valid12_120_4 : (thresholds12_120.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_120.drop 4) (by decide +kernel)

theorem valid12_120 : thresholds12_120.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_120 4 valid12_120_0 (valid12_120_4)

private theorem valid12_126_0 : (thresholds12_126.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_126.take 4) (by decide +kernel)

private theorem valid12_126_4 : (thresholds12_126.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_126.drop 4) (by decide +kernel)

theorem valid12_126 : thresholds12_126.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_126 4 valid12_126_0 (valid12_126_4)

private theorem valid12_132_0 : (thresholds12_132.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_132.take 5) (by decide +kernel)

private theorem valid12_132_5 : (thresholds12_132.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_132.drop 5) (by decide +kernel)

theorem valid12_132 : thresholds12_132.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_132 5 valid12_132_0 (valid12_132_5)

private theorem valid12_138_0 : (thresholds12_138.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_138.take 5) (by decide +kernel)

private theorem valid12_138_5 : (thresholds12_138.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_138.drop 5) (by decide +kernel)

theorem valid12_138 : thresholds12_138.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_138 5 valid12_138_0 (valid12_138_5)

private theorem valid12_144_0 : (thresholds12_144.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_144.take 4) (by decide +kernel)

private theorem valid12_144_4 : (thresholds12_144.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_144.drop 4) (by decide +kernel)

theorem valid12_144 : thresholds12_144.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_144 4 valid12_144_0 (valid12_144_4)

private theorem valid12_150_0 : (thresholds12_150.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_150.take 4) (by decide +kernel)

private theorem valid12_150_4 : (thresholds12_150.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_150.drop 4) (by decide +kernel)

theorem valid12_150 : thresholds12_150.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_150 4 valid12_150_0 (valid12_150_4)

private theorem valid12_156_0 : (thresholds12_156.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_156.take 4) (by decide +kernel)

private theorem valid12_156_4 : (thresholds12_156.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_156.drop 4) (by decide +kernel)

theorem valid12_156 : thresholds12_156.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_156 4 valid12_156_0 (valid12_156_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part002

section Pack_Z6970H2307PackedBand12Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid12_162_0 : (thresholds12_162.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_162.take 5) (by decide +kernel)

private theorem valid12_162_5 : (thresholds12_162.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_162.drop 5) (by decide +kernel)

theorem valid12_162 : thresholds12_162.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_162 5 valid12_162_0 (valid12_162_5)

private theorem valid12_168_0 : (thresholds12_168.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_168.take 5) (by decide +kernel)

private theorem valid12_168_5 : (thresholds12_168.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_168.drop 5) (by decide +kernel)

theorem valid12_168 : thresholds12_168.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_168 5 valid12_168_0 (valid12_168_5)

private theorem valid12_174_0 : (thresholds12_174.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_174.take 4) (by decide +kernel)

private theorem valid12_174_4 : (thresholds12_174.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_174.drop 4) (by decide +kernel)

theorem valid12_174 : thresholds12_174.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_174 4 valid12_174_0 (valid12_174_4)

private theorem valid12_180_0 : (thresholds12_180.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_180.take 4) (by decide +kernel)

private theorem valid12_180_4 : (thresholds12_180.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_180.drop 4) (by decide +kernel)

theorem valid12_180 : thresholds12_180.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_180 4 valid12_180_0 (valid12_180_4)

private theorem valid12_186_0 : (thresholds12_186.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_186.take 4) (by decide +kernel)

private theorem valid12_186_4 : (thresholds12_186.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_186.drop 4) (by decide +kernel)

theorem valid12_186 : thresholds12_186.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_186 4 valid12_186_0 (valid12_186_4)

theorem valid12_192 : thresholds12_192.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_192 (by decide +kernel)

theorem valid12_198 : thresholds12_198.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_198 (by decide +kernel)

private theorem valid12_204_0 : (thresholds12_204.take 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_204.take 4) (by decide +kernel)

private theorem valid12_204_4 : (thresholds12_204.drop 4).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_204.drop 4) (by decide +kernel)

theorem valid12_204 : thresholds12_204.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_204 4 valid12_204_0 (valid12_204_4)

private theorem valid12_210_0 : (thresholds12_210.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_210.take 5) (by decide +kernel)

private theorem valid12_210_5 : (thresholds12_210.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_210.drop 5) (by decide +kernel)

theorem valid12_210 : thresholds12_210.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_210 5 valid12_210_0 (valid12_210_5)

private theorem valid12_216_0 : (thresholds12_216.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_216.take 5) (by decide +kernel)

private theorem valid12_216_5 : (thresholds12_216.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_216.drop 5) (by decide +kernel)

theorem valid12_216 : thresholds12_216.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_216 5 valid12_216_0 (valid12_216_5)

theorem valid12_222 : thresholds12_222.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_222 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part003

section Pack_Z6970H2307PackedBand12Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid12_228 : thresholds12_228.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_228 (by decide +kernel)

private theorem valid12_234_0 : (thresholds12_234.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_234.take 5) (by decide +kernel)

private theorem valid12_234_5 : (thresholds12_234.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_234.drop 5) (by decide +kernel)

theorem valid12_234 : thresholds12_234.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_234 5 valid12_234_0 (valid12_234_5)

private theorem valid12_240_0 : (thresholds12_240.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_240.take 5) (by decide +kernel)

private theorem valid12_240_5 : (thresholds12_240.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_240.drop 5) (by decide +kernel)

theorem valid12_240 : thresholds12_240.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_240 5 valid12_240_0 (valid12_240_5)

theorem valid12_246 : thresholds12_246.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_246 (by decide +kernel)

theorem valid12_252 : thresholds12_252.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_252 (by decide +kernel)

theorem valid12_258 : thresholds12_258.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_258 (by decide +kernel)

private theorem valid12_264_0 : (thresholds12_264.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_264.take 5) (by decide +kernel)

private theorem valid12_264_5 : (thresholds12_264.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_264.drop 5) (by decide +kernel)

theorem valid12_264 : thresholds12_264.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_264 5 valid12_264_0 (valid12_264_5)

theorem valid12_270 : thresholds12_270.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_270 (by decide +kernel)

private theorem valid12_276_0 : (thresholds12_276.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_276.take 5) (by decide +kernel)

private theorem valid12_276_5 : (thresholds12_276.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_276.drop 5) (by decide +kernel)

theorem valid12_276 : thresholds12_276.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_276 5 valid12_276_0 (valid12_276_5)

theorem valid12_282 : thresholds12_282.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_282 (by decide +kernel)

theorem valid12_288 : thresholds12_288.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_288 (by decide +kernel)

theorem valid12_294 : thresholds12_294.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_294 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part004

section Pack_Z6970H2307PackedBand12Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid12_300 : thresholds12_300.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_300 (by decide +kernel)

theorem valid12_306 : thresholds12_306.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_306 (by decide +kernel)

private theorem valid12_312_0 : (thresholds12_312.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_312.take 5) (by decide +kernel)

private theorem valid12_312_5 : (thresholds12_312.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_312.drop 5) (by decide +kernel)

theorem valid12_312 : thresholds12_312.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_312 5 valid12_312_0 (valid12_312_5)

theorem valid12_318 : thresholds12_318.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_318 (by decide +kernel)

theorem valid12_324 : thresholds12_324.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_324 (by decide +kernel)

theorem valid12_330 : thresholds12_330.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_330 (by decide +kernel)

private theorem valid12_336_0 : (thresholds12_336.take 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_336.take 5) (by decide +kernel)

private theorem valid12_336_5 : (thresholds12_336.drop 5).all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 (thresholds12_336.drop 5) (by decide +kernel)

theorem valid12_336 : thresholds12_336.all (checked ⟨4,4,1⟩)=true :=
  all_take_drop (checked ⟨4,4,1⟩) thresholds12_336 5 valid12_336_0 (valid12_336_5)

theorem valid12_342 : thresholds12_342.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_342 (by decide +kernel)

theorem valid12_348 : thresholds12_348.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_348 (by decide +kernel)

theorem valid12_354 : thresholds12_354.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_354 (by decide +kernel)

theorem valid12_360 : thresholds12_360.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_360 (by decide +kernel)

theorem valid12_366 : thresholds12_366.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_366 (by decide +kernel)

theorem valid12_372 : thresholds12_372.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_372 (by decide +kernel)

theorem valid12_378 : thresholds12_378.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_378 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part005

section Pack_Z6970H2307PackedBand12Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid12_384 : thresholds12_384.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_384 (by decide +kernel)

theorem valid12_390 : thresholds12_390.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_390 (by decide +kernel)

theorem valid12_396 : thresholds12_396.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_396 (by decide +kernel)

theorem valid12_402 : thresholds12_402.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_402 (by decide +kernel)

theorem valid12_408 : thresholds12_408.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_408 (by decide +kernel)

theorem valid12_414 : thresholds12_414.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_414 (by decide +kernel)

theorem valid12_420 : thresholds12_420.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_420 (by decide +kernel)

theorem valid12_426 : thresholds12_426.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_426 (by decide +kernel)

theorem valid12_432 : thresholds12_432.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_432 (by decide +kernel)

theorem valid12_438 : thresholds12_438.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_438 (by decide +kernel)

theorem valid12_444 : thresholds12_444.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_444 (by decide +kernel)

theorem valid12_450 : thresholds12_450.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_450 (by decide +kernel)

theorem valid12_456 : thresholds12_456.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_456 (by decide +kernel)

theorem valid12_462 : thresholds12_462.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_462 (by decide +kernel)

theorem valid12_468 : thresholds12_468.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_468 (by decide +kernel)

theorem valid12_474 : thresholds12_474.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_474 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part006

section Pack_Z6970H2307PackedBand12Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid12_480 : thresholds12_480.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_480 (by decide +kernel)

theorem valid12_486 : thresholds12_486.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_486 (by decide +kernel)

theorem valid12_492 : thresholds12_492.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_492 (by decide +kernel)

theorem valid12_498 : thresholds12_498.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_498 (by decide +kernel)

theorem valid12_504 : thresholds12_504.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_504 (by decide +kernel)

theorem valid12_510 : thresholds12_510.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_510 (by decide +kernel)

theorem valid12_516 : thresholds12_516.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_516 (by decide +kernel)

theorem valid12_522 : thresholds12_522.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_522 (by decide +kernel)

theorem valid12_528 : thresholds12_528.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_528 (by decide +kernel)

theorem valid12_534 : thresholds12_534.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_534 (by decide +kernel)

theorem valid12_540 : thresholds12_540.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_540 (by decide +kernel)

theorem valid12_546 : thresholds12_546.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_546 (by decide +kernel)

theorem valid12_552 : thresholds12_552.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_552 (by decide +kernel)

theorem valid12_558 : thresholds12_558.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_558 (by decide +kernel)

theorem valid12_564 : thresholds12_564.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_564 (by decide +kernel)

theorem valid12_570 : thresholds12_570.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_570 (by decide +kernel)

theorem valid12_576 : thresholds12_576.all (checked ⟨4,4,1⟩)=true :=
  checkedVerified ⟨4,4,1⟩ prefixMap12 thresholds12_576 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand12Part007

section Pack_Z6970H2307PackedBand13Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid13_0_0 : (thresholds13_0.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_0.take 4) (by decide +kernel)

private theorem valid13_0_4 : (thresholds13_0.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_0.drop 4) (by decide +kernel)

theorem valid13_0 : thresholds13_0.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_0 4 valid13_0_0 (valid13_0_4)

theorem valid13_6 : thresholds13_6.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_6 (by decide +kernel)

theorem valid13_12 : thresholds13_12.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_12 (by decide +kernel)

theorem valid13_18 : thresholds13_18.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_18 (by decide +kernel)

theorem valid13_24 : thresholds13_24.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_24 (by decide +kernel)

theorem valid13_30 : thresholds13_30.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_30 (by decide +kernel)

private theorem valid13_36_0 : (thresholds13_36.take 3).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_36.take 3) (by decide +kernel)

private theorem valid13_36_3 : ((thresholds13_36.drop 3).take 2).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 ((thresholds13_36.drop 3).take 2) (by decide +kernel)

private theorem valid13_36_5 : (thresholds13_36.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_36.drop 5) (by decide +kernel)

theorem valid13_36 : thresholds13_36.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_36 3 valid13_36_0 (all_take_drop (checked ⟨5,4,1⟩) (thresholds13_36.drop 3) 2 valid13_36_3 (valid13_36_5))

private theorem valid13_42_0 : (thresholds13_42.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_42.take 5) (by decide +kernel)

private theorem valid13_42_5 : (thresholds13_42.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_42.drop 5) (by decide +kernel)

theorem valid13_42 : thresholds13_42.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_42 5 valid13_42_0 (valid13_42_5)

private theorem valid13_48_0 : (thresholds13_48.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_48.take 5) (by decide +kernel)

private theorem valid13_48_5 : (thresholds13_48.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_48.drop 5) (by decide +kernel)

theorem valid13_48 : thresholds13_48.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_48 5 valid13_48_0 (valid13_48_5)

private theorem valid13_54_0 : (thresholds13_54.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_54.take 5) (by decide +kernel)

private theorem valid13_54_5 : (thresholds13_54.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_54.drop 5) (by decide +kernel)

theorem valid13_54 : thresholds13_54.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_54 5 valid13_54_0 (valid13_54_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part000

section Pack_Z6970H2307PackedBand13Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid13_60_0 : (thresholds13_60.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_60.take 4) (by decide +kernel)

private theorem valid13_60_4 : (thresholds13_60.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_60.drop 4) (by decide +kernel)

theorem valid13_60 : thresholds13_60.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_60 4 valid13_60_0 (valid13_60_4)

private theorem valid13_66_0 : (thresholds13_66.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_66.take 5) (by decide +kernel)

private theorem valid13_66_5 : (thresholds13_66.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_66.drop 5) (by decide +kernel)

theorem valid13_66 : thresholds13_66.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_66 5 valid13_66_0 (valid13_66_5)

private theorem valid13_72_0 : (thresholds13_72.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_72.take 5) (by decide +kernel)

private theorem valid13_72_5 : (thresholds13_72.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_72.drop 5) (by decide +kernel)

theorem valid13_72 : thresholds13_72.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_72 5 valid13_72_0 (valid13_72_5)

private theorem valid13_78_0 : (thresholds13_78.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_78.take 4) (by decide +kernel)

private theorem valid13_78_4 : (thresholds13_78.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_78.drop 4) (by decide +kernel)

theorem valid13_78 : thresholds13_78.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_78 4 valid13_78_0 (valid13_78_4)

theorem valid13_84 : thresholds13_84.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_84 (by decide +kernel)

private theorem valid13_90_0 : (thresholds13_90.take 3).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_90.take 3) (by decide +kernel)

private theorem valid13_90_3 : (thresholds13_90.drop 3).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_90.drop 3) (by decide +kernel)

theorem valid13_90 : thresholds13_90.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_90 3 valid13_90_0 (valid13_90_3)

private theorem valid13_96_0 : (thresholds13_96.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_96.take 5) (by decide +kernel)

private theorem valid13_96_5 : (thresholds13_96.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_96.drop 5) (by decide +kernel)

theorem valid13_96 : thresholds13_96.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_96 5 valid13_96_0 (valid13_96_5)

private theorem valid13_102_0 : (thresholds13_102.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_102.take 4) (by decide +kernel)

private theorem valid13_102_4 : (thresholds13_102.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_102.drop 4) (by decide +kernel)

theorem valid13_102 : thresholds13_102.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_102 4 valid13_102_0 (valid13_102_4)

theorem valid13_108 : thresholds13_108.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_108 (by decide +kernel)

private theorem valid13_114_0 : (thresholds13_114.take 3).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_114.take 3) (by decide +kernel)

private theorem valid13_114_3 : (thresholds13_114.drop 3).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_114.drop 3) (by decide +kernel)

theorem valid13_114 : thresholds13_114.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_114 3 valid13_114_0 (valid13_114_3)

private theorem valid13_120_0 : (thresholds13_120.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_120.take 4) (by decide +kernel)

private theorem valid13_120_4 : (thresholds13_120.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_120.drop 4) (by decide +kernel)

theorem valid13_120 : thresholds13_120.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_120 4 valid13_120_0 (valid13_120_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part001

section Pack_Z6970H2307PackedBand13Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid13_126_0 : (thresholds13_126.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_126.take 4) (by decide +kernel)

private theorem valid13_126_4 : (thresholds13_126.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_126.drop 4) (by decide +kernel)

theorem valid13_126 : thresholds13_126.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_126 4 valid13_126_0 (valid13_126_4)

private theorem valid13_132_0 : (thresholds13_132.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_132.take 4) (by decide +kernel)

private theorem valid13_132_4 : (thresholds13_132.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_132.drop 4) (by decide +kernel)

theorem valid13_132 : thresholds13_132.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_132 4 valid13_132_0 (valid13_132_4)

private theorem valid13_138_0 : (thresholds13_138.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_138.take 4) (by decide +kernel)

private theorem valid13_138_4 : (thresholds13_138.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_138.drop 4) (by decide +kernel)

theorem valid13_138 : thresholds13_138.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_138 4 valid13_138_0 (valid13_138_4)

private theorem valid13_144_0 : (thresholds13_144.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_144.take 4) (by decide +kernel)

private theorem valid13_144_4 : (thresholds13_144.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_144.drop 4) (by decide +kernel)

theorem valid13_144 : thresholds13_144.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_144 4 valid13_144_0 (valid13_144_4)

private theorem valid13_150_0 : (thresholds13_150.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_150.take 5) (by decide +kernel)

private theorem valid13_150_5 : (thresholds13_150.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_150.drop 5) (by decide +kernel)

theorem valid13_150 : thresholds13_150.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_150 5 valid13_150_0 (valid13_150_5)

theorem valid13_156 : thresholds13_156.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_156 (by decide +kernel)

private theorem valid13_162_0 : (thresholds13_162.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_162.take 4) (by decide +kernel)

private theorem valid13_162_4 : (thresholds13_162.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_162.drop 4) (by decide +kernel)

theorem valid13_162 : thresholds13_162.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_162 4 valid13_162_0 (valid13_162_4)

private theorem valid13_168_0 : (thresholds13_168.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_168.take 5) (by decide +kernel)

private theorem valid13_168_5 : (thresholds13_168.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_168.drop 5) (by decide +kernel)

theorem valid13_168 : thresholds13_168.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_168 5 valid13_168_0 (valid13_168_5)

private theorem valid13_174_0 : (thresholds13_174.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_174.take 5) (by decide +kernel)

private theorem valid13_174_5 : (thresholds13_174.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_174.drop 5) (by decide +kernel)

theorem valid13_174 : thresholds13_174.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_174 5 valid13_174_0 (valid13_174_5)

theorem valid13_180 : thresholds13_180.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_180 (by decide +kernel)

private theorem valid13_186_0 : (thresholds13_186.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_186.take 4) (by decide +kernel)

private theorem valid13_186_4 : (thresholds13_186.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_186.drop 4) (by decide +kernel)

theorem valid13_186 : thresholds13_186.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_186 4 valid13_186_0 (valid13_186_4)

private theorem valid13_192_0 : (thresholds13_192.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_192.take 5) (by decide +kernel)

private theorem valid13_192_5 : (thresholds13_192.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_192.drop 5) (by decide +kernel)

theorem valid13_192 : thresholds13_192.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_192 5 valid13_192_0 (valid13_192_5)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part002

section Pack_Z6970H2307PackedBand13Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid13_198_0 : (thresholds13_198.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_198.take 4) (by decide +kernel)

private theorem valid13_198_4 : (thresholds13_198.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_198.drop 4) (by decide +kernel)

theorem valid13_198 : thresholds13_198.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_198 4 valid13_198_0 (valid13_198_4)

private theorem valid13_204_0 : (thresholds13_204.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_204.take 5) (by decide +kernel)

private theorem valid13_204_5 : (thresholds13_204.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_204.drop 5) (by decide +kernel)

theorem valid13_204 : thresholds13_204.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_204 5 valid13_204_0 (valid13_204_5)

private theorem valid13_210_0 : (thresholds13_210.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_210.take 5) (by decide +kernel)

private theorem valid13_210_5 : (thresholds13_210.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_210.drop 5) (by decide +kernel)

theorem valid13_210 : thresholds13_210.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_210 5 valid13_210_0 (valid13_210_5)

private theorem valid13_216_0 : (thresholds13_216.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_216.take 4) (by decide +kernel)

private theorem valid13_216_4 : (thresholds13_216.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_216.drop 4) (by decide +kernel)

theorem valid13_216 : thresholds13_216.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_216 4 valid13_216_0 (valid13_216_4)

theorem valid13_222 : thresholds13_222.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_222 (by decide +kernel)

theorem valid13_228 : thresholds13_228.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_228 (by decide +kernel)

theorem valid13_234 : thresholds13_234.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_234 (by decide +kernel)

private theorem valid13_240_0 : (thresholds13_240.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_240.take 5) (by decide +kernel)

private theorem valid13_240_5 : (thresholds13_240.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_240.drop 5) (by decide +kernel)

theorem valid13_240 : thresholds13_240.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_240 5 valid13_240_0 (valid13_240_5)

theorem valid13_246 : thresholds13_246.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_246 (by decide +kernel)

private theorem valid13_252_0 : (thresholds13_252.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_252.take 5) (by decide +kernel)

private theorem valid13_252_5 : (thresholds13_252.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_252.drop 5) (by decide +kernel)

theorem valid13_252 : thresholds13_252.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_252 5 valid13_252_0 (valid13_252_5)

theorem valid13_258 : thresholds13_258.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_258 (by decide +kernel)

theorem valid13_264 : thresholds13_264.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_264 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part003

section Pack_Z6970H2307PackedBand13Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private theorem valid13_270_0 : (thresholds13_270.take 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_270.take 5) (by decide +kernel)

private theorem valid13_270_5 : (thresholds13_270.drop 5).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_270.drop 5) (by decide +kernel)

theorem valid13_270 : thresholds13_270.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_270 5 valid13_270_0 (valid13_270_5)

theorem valid13_276 : thresholds13_276.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_276 (by decide +kernel)

theorem valid13_282 : thresholds13_282.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_282 (by decide +kernel)

theorem valid13_288 : thresholds13_288.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_288 (by decide +kernel)

theorem valid13_294 : thresholds13_294.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_294 (by decide +kernel)

theorem valid13_300 : thresholds13_300.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_300 (by decide +kernel)

theorem valid13_306 : thresholds13_306.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_306 (by decide +kernel)

theorem valid13_312 : thresholds13_312.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_312 (by decide +kernel)

theorem valid13_318 : thresholds13_318.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_318 (by decide +kernel)

theorem valid13_324 : thresholds13_324.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_324 (by decide +kernel)

theorem valid13_330 : thresholds13_330.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_330 (by decide +kernel)

theorem valid13_336 : thresholds13_336.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_336 (by decide +kernel)

theorem valid13_342 : thresholds13_342.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_342 (by decide +kernel)

private theorem valid13_348_0 : (thresholds13_348.take 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_348.take 4) (by decide +kernel)

private theorem valid13_348_4 : (thresholds13_348.drop 4).all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 (thresholds13_348.drop 4) (by decide +kernel)

theorem valid13_348 : thresholds13_348.all (checked ⟨5,4,1⟩)=true :=
  all_take_drop (checked ⟨5,4,1⟩) thresholds13_348 4 valid13_348_0 (valid13_348_4)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part004

section Pack_Z6970H2307PackedBand13Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid13_354 : thresholds13_354.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_354 (by decide +kernel)

theorem valid13_360 : thresholds13_360.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_360 (by decide +kernel)

theorem valid13_366 : thresholds13_366.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_366 (by decide +kernel)

theorem valid13_372 : thresholds13_372.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_372 (by decide +kernel)

theorem valid13_378 : thresholds13_378.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_378 (by decide +kernel)

theorem valid13_384 : thresholds13_384.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_384 (by decide +kernel)

theorem valid13_390 : thresholds13_390.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_390 (by decide +kernel)

theorem valid13_396 : thresholds13_396.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_396 (by decide +kernel)

theorem valid13_402 : thresholds13_402.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_402 (by decide +kernel)

theorem valid13_408 : thresholds13_408.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_408 (by decide +kernel)

theorem valid13_414 : thresholds13_414.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_414 (by decide +kernel)

theorem valid13_420 : thresholds13_420.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_420 (by decide +kernel)

theorem valid13_426 : thresholds13_426.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_426 (by decide +kernel)

theorem valid13_432 : thresholds13_432.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_432 (by decide +kernel)

theorem valid13_438 : thresholds13_438.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_438 (by decide +kernel)

theorem valid13_444 : thresholds13_444.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_444 (by decide +kernel)

theorem valid13_450 : thresholds13_450.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_450 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part005

section Pack_Z6970H2307PackedBand13Part006

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid13_456 : thresholds13_456.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_456 (by decide +kernel)

theorem valid13_462 : thresholds13_462.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_462 (by decide +kernel)

theorem valid13_468 : thresholds13_468.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_468 (by decide +kernel)

theorem valid13_474 : thresholds13_474.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_474 (by decide +kernel)

theorem valid13_480 : thresholds13_480.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_480 (by decide +kernel)

theorem valid13_486 : thresholds13_486.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_486 (by decide +kernel)

theorem valid13_492 : thresholds13_492.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_492 (by decide +kernel)

theorem valid13_498 : thresholds13_498.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_498 (by decide +kernel)

theorem valid13_504 : thresholds13_504.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_504 (by decide +kernel)

theorem valid13_510 : thresholds13_510.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_510 (by decide +kernel)

theorem valid13_516 : thresholds13_516.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_516 (by decide +kernel)

theorem valid13_522 : thresholds13_522.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_522 (by decide +kernel)

theorem valid13_528 : thresholds13_528.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_528 (by decide +kernel)

theorem valid13_534 : thresholds13_534.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_534 (by decide +kernel)

theorem valid13_540 : thresholds13_540.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_540 (by decide +kernel)

theorem valid13_546 : thresholds13_546.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_546 (by decide +kernel)

theorem valid13_552 : thresholds13_552.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_552 (by decide +kernel)

theorem valid13_558 : thresholds13_558.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_558 (by decide +kernel)

theorem valid13_564 : thresholds13_564.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_564 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part006

section Pack_Z6970H2307PackedBand13Part007

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

theorem valid13_570 : thresholds13_570.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_570 (by decide +kernel)

theorem valid13_576 : thresholds13_576.all (checked ⟨5,4,1⟩)=true :=
  checkedVerified ⟨5,4,1⟩ prefixMap13 thresholds13_576 (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedBand13Part007
