import ProximityPrize.SubmissionLower.LowerGeometry
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.MovingFiberKernels6815
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
namespace A
theorem coefficient_exact : coefficientCount 23924340 131071 76330 39=5372513324094290 := by
  rw [show 23924340=182*131071+69418 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 182 69418 131071 76330 39
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 132 76330 39=20494511840 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end A
namespace B
theorem coefficient_exact : coefficientCount 30086670 131071 15421 50=2165386041082735 := by
  rw [show 30086670=229*131071+71411 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 229 71411 131071 15421 50
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 166 15421 50=8260292112 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end B
namespace TCap
theorem coefficient_exact : coefficientCount 45673740 131071 11193 78=5528547372439440 := by
  rw [show 45673740=348*131071+61032 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 348 61032 131071 11193 78
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 252 11193 78=21089734219 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 45673740 131071 11193 78-262144*localRankBound 252 11193 78=85333904 := by
  norm_num only [coefficient_exact,rank_exact]
theorem quotient_count_exact : coefficientCount 45673740 131071 0 78=45673740 := by decide +kernel
theorem quotient_count_lt : coefficientCount 45673740 131071 0 78<85333904 := by rw [quotient_count_exact]; decide +kernel
end TCap
namespace Source00
theorem coefficient_exact : coefficientCount 11599498755 131071 3840000 19840=30707103195602755936705787 := by
  rw [show 11599498755=88497*131071+108468 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88497 108468 131071 3840000 19840
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 63999 3840000 19840=116780376202356671680 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 11599498755 131071 3840000 19840-262144*localRankBound 63999 3840000 19840=93828256412168595823867 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 93828256412168595823867≤coefficientCount 11599498755 131071 3840000 19840-262144*localRankBound 63999 3840000 19840 := by rw [nullity_exact]
theorem shape : 11599498755+19840≤131071*(88497+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    93828256412168595823867≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 11599498755 131071 3840000 19840 63999 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 11599498755 3840000 19840 63999 93828256412168595823867 u0 u1 nullity_lower
end Source00
namespace Source01
theorem coefficient_exact : coefficientCount 5799840000 131071 3200000 9888=3203068458886446493984520 := by
  rw [show 5799840000=44249*131071+79321 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44249 79321 131071 3200000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 3200000 9888=12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5799840000 131071 3200000 9888-262144*localRankBound 32000 3200000 9888=12051170488452604225288 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 12051170488452604225288≤coefficientCount 5799840000 131071 3200000 9888-262144*localRankBound 32000 3200000 9888 := by rw [nullity_exact]
theorem shape : 5799840000+9888≤131071*(44249+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    12051170488452604225288≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 5799840000 131071 3200000 9888 32000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 5799840000 3200000 9888 32000 12051170488452604225288 u0 u1 nullity_lower
end Source01
namespace Source02
theorem coefficient_exact : coefficientCount 5799840000 131071 2880000 9888=2880973021201531445984520 := by
  rw [show 5799840000=44249*131071+79321 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44249 79321 131071 2880000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 2880000 9888=10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5799840000 131071 2880000 9888-262144*localRankBound 32000 2880000 9888=10494049854430335745288 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 10494049854430335745288≤coefficientCount 5799840000 131071 2880000 9888-262144*localRankBound 32000 2880000 9888 := by rw [nullity_exact]
theorem shape : 5799840000+9888≤131071*(44249+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    10494049854430335745288≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 5799840000 131071 2880000 9888 32000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 5799840000 2880000 9888 32000 10494049854430335745288 u0 u1 nullity_lower
end Source02
namespace Source03
theorem coefficient_exact : coefficientCount 2899920000 131071 1062000 4940=132437019288815010683775 := by
  rw [show 2899920000=22124*131071+105196 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22124 105196 131071 1062000 4940
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 16000 1062000 4940=503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2899920000 131071 1062000 4940-262144*localRankBound 16000 1062000 4940=423032138525943634815 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 423032138525943634815≤coefficientCount 2899920000 131071 1062000 4940-262144*localRankBound 16000 1062000 4940 := by rw [nullity_exact]
theorem shape : 2899920000+4940≤131071*(22124+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    423032138525943634815≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 2899920000 131071 1062000 4940 16000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 2899920000 1062000 4940 16000 423032138525943634815 u0 u1 nullity_lower
end Source03
namespace Source04
theorem coefficient_exact : coefficientCount 1449960000 131071 531000 2470=8279436385594675048202 := by
  rw [show 1449960000=11062*131071+52598 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11062 52598 131071 531000 2470
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 8000 531000 2470=31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 1449960000 131071 531000 2470-262144*localRankBound 8000 531000 2470=26128801782659821322 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 26128801782659821322≤coefficientCount 1449960000 131071 531000 2470-262144*localRankBound 8000 531000 2470 := by rw [nullity_exact]
theorem shape : 1449960000+2470≤131071*(11062+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    26128801782659821322≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 1449960000 131071 531000 2470 8000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 1449960000 531000 2470 8000 26128801782659821322 u0 u1 nullity_lower
end Source04
namespace Source05
theorem coefficient_exact : coefficientCount 181245000 131071 88902 308=2717882477285942235 := by
  rw [show 181245000=1382*131071+104878 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1382 104878 131071 88902 308
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 1000 88902 308=10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 181245000 131071 88902 308-262144*localRankBound 1000 88902 308=8232573564822491 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 8232573564822491≤coefficientCount 181245000 131071 88902 308-262144*localRankBound 1000 88902 308 := by rw [nullity_exact]
theorem shape : 181245000+308≤131071*(1382+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    8232573564822491≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 181245000 131071 88902 308 1000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 181245000 88902 308 1000 8232573564822491 u0 u1 nullity_lower
end Source05
namespace Source06
theorem coefficient_exact : coefficientCount 2537430000 131071 3640000 4267=303020312516603787210897 := by
  rw [show 2537430000=19359*131071+26511 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19359 26511 131071 3640000 4267
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 14000 3640000 4267=1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2537430000 131071 3640000 4267-262144*localRankBound 14000 3640000 4267=1324669961085702762641 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1324669961085702762641≤coefficientCount 2537430000 131071 3640000 4267-262144*localRankBound 14000 3640000 4267 := by rw [nullity_exact]
theorem shape : 2537430000+4267≤131071*(19359+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1324669961085702762641≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 2537430000 131071 3640000 4267 14000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 2537430000 3640000 4267 14000 1324669961085702762641 u0 u1 nullity_lower
end Source06
end ProximityPrize.SubmissionLower.MovingFiberKernels6815
