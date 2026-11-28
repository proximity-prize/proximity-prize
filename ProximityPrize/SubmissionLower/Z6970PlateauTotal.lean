import ProximityPrize.SubmissionLower.Bundle6970_14fb4a88f76c1c84
import ProximityPrize.SubmissionLower.Bundle6970_14fb4a88f76c1c84
import ProximityPrize.SubmissionLower.Bundle6970_dbcfe41a7c5dbb59
import ProximityPrize.SubmissionLower.Bundle6970_dbcfe41a7c5dbb59
import ProximityPrize.SubmissionLower.Bundle6970_e7be49e43ce3855b
import ProximityPrize.SubmissionLower.Bundle6970_e7be49e43ce3855b
import ProximityPrize.SubmissionLower.Bundle6970_6a9c0637e4e77975
import ProximityPrize.SubmissionLower.Bundle6970_6a9c0637e4e77975
import ProximityPrize.SubmissionLower.Z6970PlateauChunkedBatch160
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_4f8f215cdc98af46
import ProximityPrize.SubmissionLower.Bundle6970_ad0f3f708d0db891
import ProximityPrize.SubmissionLower.Bundle6970_ad0f3f708d0db891
import ProximityPrize.SubmissionLower.Bundle6970_ad0f3f708d0db891
import ProximityPrize.SubmissionLower.Bundle6970_ad0f3f708d0db891
import ProximityPrize.SubmissionLower.Bundle6970_ad0f3f708d0db891
import ProximityPrize.SubmissionLower.Bundle6970_ad0f3f708d0db891
import ProximityPrize.SubmissionLower.Z6970PlateauChunkedBatch500

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range20To60 : chunk 20 40 = 46095153895072 :=
  join_chunk (f := 20) (a := 20) (b := 20) (u := 23769366268436) (v := 22325787626636) range20To40 range40To60

theorem range0To60 : chunk 0 60 = 71360048570908 :=
  join_chunk (f := 0) (a := 20) (b := 40) (u := 25264894675836) (v := 46095153895072) range0To20 range20To60

theorem range80To120 : chunk 80 40 = 37856760752178 :=
  join_chunk (f := 80) (a := 20) (b := 20) (u := 19581905817338) (v := 18274854934840) range80To100 range100To120

theorem range60To120 : chunk 60 60 = 58787826980614 :=
  join_chunk (f := 60) (a := 20) (b := 40) (u := 20931066228436) (v := 37856760752178) range60To80 range80To120

theorem range0To120 : chunk 0 120 = 130147875551522 :=
  join_chunk (f := 0) (a := 60) (b := 60) (u := 71360048570908) (v := 58787826980614) range0To60 range60To120

theorem range140To180 : chunk 140 40 = 30351342017080 :=
  join_chunk (f := 140) (a := 20) (b := 20) (u := 15774636611640) (v := 14576705405440) range140To160 range160To180

theorem range120To180 : chunk 120 60 = 47358003684520 :=
  join_chunk (f := 120) (a := 20) (b := 40) (u := 17006661667440) (v := 30351342017080) range120To140 range140To180

theorem range180To220 : chunk 180 40 = 25689312460680 :=
  join_chunk (f := 180) (a := 20) (b := 20) (u := 13411408966840) (v := 12277903493840) range180To200 range200To220

theorem range220To260 : chunk 220 40 = 21281927101080 :=
  join_chunk (f := 220) (a := 20) (b := 20) (u := 11175960464440) (v := 10105966636640) range220To240 range240To260

theorem range180To260 : chunk 180 80 = 46971239561760 :=
  join_chunk (f := 180) (a := 40) (b := 40) (u := 25689312460680) (v := 21281927101080) range180To220 range220To260

theorem range120To260 : chunk 120 140 = 94329243246280 :=
  join_chunk (f := 120) (a := 60) (b := 80) (u := 47358003684520) (v := 46971239561760) range120To180 range180To260

theorem range0To260 : chunk 0 260 = 224477118797802 :=
  join_chunk (f := 0) (a := 120) (b := 140) (u := 130147875551522) (v := 94329243246280) range0To120 range120To260

theorem range280To320 : chunk 280 40 = 15167227160680 :=
  join_chunk (f := 280) (a := 20) (b := 20) (u := 8066450017840) (v := 7100777142840) range280To300 range300To320

theorem range260To320 : chunk 260 60 = 24236151209120 :=
  join_chunk (f := 260) (a := 20) (b := 40) (u := 9068924048440) (v := 15167227160680) range260To280 range280To320

theorem range340To380 : chunk 340 40 = 9747962283080 :=
  join_chunk (f := 340) (a := 20) (b := 20) (u := 5291841651640) (v := 4456120631440) range340To360 range360To380

theorem range320To380 : chunk 320 60 = 15922715584520 :=
  join_chunk (f := 320) (a := 20) (b := 40) (u := 6174753301440) (v := 9747962283080) range320To340 range340To380

theorem range260To380 : chunk 260 120 = 40158866793640 :=
  join_chunk (f := 260) (a := 60) (b := 60) (u := 24236151209120) (v := 15922715584520) range260To320 range320To380

theorem range400To440 : chunk 400 40 = 5227755433820 :=
  join_chunk (f := 400) (a := 20) (b := 20) (u := 2945640631840) (v := 2282114801980) range400To420 range420To440

theorem range380To440 : chunk 380 60 = 8900039392660 :=
  join_chunk (f := 380) (a := 20) (b := 40) (u := 3672283958840) (v := 5227755433820) range380To400 range400To440

theorem range440To480 : chunk 440 40 = 2859415340674 :=
  join_chunk (f := 440) (a := 20) (b := 20) (u := 1688243463180) (v := 1171171877494) range440To460 range460To480

theorem range480To501 : chunk 480 21 = 765862761432 :=
  join_chunk (f := 480) (a := 20) (b := 1) (u := 738654464518) (v := 27208296914) range480To500 oneChunk500

theorem range440To501 : chunk 440 61 = 3625278102106 :=
  join_chunk (f := 440) (a := 40) (b := 21) (u := 2859415340674) (v := 765862761432) range440To480 range480To501

theorem range380To501 : chunk 380 121 = 12525317494766 :=
  join_chunk (f := 380) (a := 60) (b := 61) (u := 8900039392660) (v := 3625278102106) range380To440 range440To501

theorem range260To501 : chunk 260 241 = 52684184288406 :=
  join_chunk (f := 260) (a := 120) (b := 121) (u := 40158866793640) (v := 12525317494766) range260To380 range380To501

theorem range0To501 : chunk 0 501 = 277161303086208 :=
  join_chunk (f := 0) (a := 260) (b := 241) (u := 224477118797802) (v := 52684184288406) range0To260 range260To501

theorem exact_plateau_sum : chunk 0 501 = 277161303086208 := range0To501

end ExpandedPlateauSum6970
