import ProximityPrize.SubmissionLower.Bundle6970_b40f827c7a689676
import ProximityPrize.SubmissionLower.Bundle6970_1215e0a34d36bb31

section Pack_Z6970PlateauChunkedBatch380

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range380To382 : chunk 380 2 = 401600990568 :=
  join_chunk (f := 380) (a := 1) (b := 1) (u := 201777065148) (v := 199823925420) oneChunk380 oneChunk381

theorem range383To385 : chunk 383 2 = 389939510040 :=
  join_chunk (f := 383) (a := 1) (b := 1) (u := 195936743694) (v := 194002766346) oneChunk383 oneChunk384

theorem range382To385 : chunk 382 3 = 587815662280 :=
  join_chunk (f := 382) (a := 1) (b := 2) (u := 197876152240) (v := 389939510040) oneChunk382 range383To385

theorem range380To385 : chunk 380 5 = 989416652848 :=
  join_chunk (f := 380) (a := 2) (b := 3) (u := 401600990568) (v := 587815662280) range380To382 range382To385

theorem range385To387 : chunk 385 2 = 382234402320 :=
  join_chunk (f := 385) (a := 1) (b := 1) (u := 192077224020) (v := 190157178300) oneChunk385 oneChunk386

theorem range388To390 : chunk 388 2 = 370781925408 :=
  join_chunk (f := 388) (a := 1) (b := 1) (u := 186339662012) (v := 184442263396) oneChunk388 oneChunk389

theorem range387To390 : chunk 387 3 = 559027564180 :=
  join_chunk (f := 387) (a := 1) (b := 2) (u := 188245638772) (v := 370781925408) oneChunk387 range388To390

theorem range385To390 : chunk 385 5 = 941261966500 :=
  join_chunk (f := 385) (a := 2) (b := 3) (u := 382234402320) (v := 559027564180) range385To387 range387To390

theorem range380To390 : chunk 380 10 = 1930678619348 :=
  join_chunk (f := 380) (a := 5) (b := 5) (u := 989416652848) (v := 941261966500) range380To385 range385To390

theorem range390To392 : chunk 390 2 = 363217870886 :=
  join_chunk (f := 390) (a := 1) (b := 1) (u := 182550494468) (v := 180667376418) oneChunk390 oneChunk391

theorem range393To395 : chunk 393 2 = 351979588380 :=
  join_chunk (f := 393) (a := 1) (b := 1) (u := 176921259438) (v := 175058328942) oneChunk393 oneChunk394

theorem range392To395 : chunk 392 3 = 530769544112 :=
  join_chunk (f := 392) (a := 1) (b := 2) (u := 178789955732) (v := 351979588380) oneChunk392 range393To395

theorem range390To395 : chunk 390 5 = 893987414998 :=
  join_chunk (f := 390) (a := 2) (b := 3) (u := 363217870886) (v := 530769544112) range390To392 range392To395

theorem range395To397 : chunk 395 2 = 344560097448 :=
  join_chunk (f := 395) (a := 1) (b := 1) (u := 173204197134) (v := 171355900314) oneChunk395 oneChunk396

theorem range398To400 : chunk 398 2 = 333541349786 :=
  join_chunk (f := 398) (a := 1) (b := 1) (u := 167682959140) (v := 165858390646) oneChunk398 oneChunk399

theorem range397To400 : chunk 397 3 = 503057827046 :=
  join_chunk (f := 397) (a := 1) (b := 2) (u := 169516477260) (v := 333541349786) oneChunk397 range398To400

theorem range395To400 : chunk 395 5 = 847617924494 :=
  join_chunk (f := 395) (a := 2) (b := 3) (u := 344560097448) (v := 503057827046) range395To397 range397To400

theorem range390To400 : chunk 390 10 = 1741605339492 :=
  join_chunk (f := 390) (a := 5) (b := 5) (u := 893987414998) (v := 847617924494) range390To395 range395To400

theorem range380To400 : chunk 380 20 = 3672283958840 :=
  join_chunk (f := 380) (a := 10) (b := 10) (u := 1930678619348) (v := 1741605339492) range380To390 range390To400

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch380

section Pack_Z6970PlateauChunkedBatch400

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range400To402 : chunk 400 2 = 326270028986 :=
  join_chunk (f := 400) (a := 1) (b := 1) (u := 164039797788) (v := 162230231198) oneChunk400 oneChunk401

theorem range403To405 : chunk 403 2 = 315476295308 :=
  join_chunk (f := 403) (a := 1) (b := 1) (u := 158632295900) (v := 156843999408) oneChunk403 oneChunk404

theorem range402To405 : chunk 402 3 = 475903007012 :=
  join_chunk (f := 402) (a := 1) (b := 2) (u := 160426711704) (v := 315476295308) oneChunk402 range403To405

theorem range400To405 : chunk 400 5 = 802173035998 :=
  join_chunk (f := 400) (a := 2) (b := 3) (u := 326270028986) (v := 475903007012) range400To402 range402To405

theorem range405To407 : chunk 405 2 = 308356847308 :=
  join_chunk (f := 405) (a := 1) (b := 1) (u := 155064884810) (v := 153291962498) oneChunk405 oneChunk406

theorem range408To410 : chunk 408 2 = 297793756526 :=
  join_chunk (f := 408) (a := 1) (b := 1) (u := 149770905648) (v := 148022850878) oneChunk408 oneChunk409

theorem range407To410 : chunk 407 3 = 449322057592 :=
  join_chunk (f := 407) (a := 1) (b := 2) (u := 151528301066) (v := 297793756526) oneChunk407 range408To410

theorem range405To410 : chunk 405 5 = 757678904900 :=
  join_chunk (f := 405) (a := 2) (b := 3) (u := 308356847308) (v := 449322057592) range405To407 range407To410

theorem range400To410 : chunk 400 10 = 1559851940898 :=
  join_chunk (f := 400) (a := 5) (b := 5) (u := 802173035998) (v := 757678904900) range400To405 range405To410

theorem range410To412 : chunk 410 2 = 290829980144 :=
  join_chunk (f := 410) (a := 1) (b := 1) (u := 146281136608) (v := 144548843536) oneChunk410 oneChunk411

theorem range413To415 : chunk 413 2 = 280503299748 :=
  join_chunk (f := 413) (a := 1) (b := 1) (u := 141106591404) (v := 139396708344) oneChunk413 oneChunk414

theorem range412To415 : chunk 412 3 = 423326265954 :=
  join_chunk (f := 412) (a := 1) (b := 2) (u := 142822966206) (v := 280503299748) oneChunk412 range413To415

theorem range410To415 : chunk 410 5 = 714156246098 :=
  join_chunk (f := 410) (a := 2) (b := 3) (u := 290829980144) (v := 423326265954) range410To412 range412To415

theorem range415To417 : chunk 415 2 = 273699089926 :=
  join_chunk (f := 415) (a := 1) (b := 1) (u := 137696409924) (v := 136002680002) oneChunk415 oneChunk416

theorem range418To420 : chunk 418 2 = 263614737304 :=
  join_chunk (f := 418) (a := 1) (b := 1) (u := 132641201236) (v := 130973536068) oneChunk418 oneChunk419

theorem range417To420 : chunk 417 3 = 397933354918 :=
  join_chunk (f := 417) (a := 1) (b := 2) (u := 134318617614) (v := 263614737304) oneChunk417 range418To420

theorem range415To420 : chunk 415 5 = 671632444844 :=
  join_chunk (f := 415) (a := 2) (b := 3) (u := 273699089926) (v := 397933354918) range415To417 range417To420

theorem range410To420 : chunk 410 10 = 1385788690942 :=
  join_chunk (f := 410) (a := 5) (b := 5) (u := 714156246098) (v := 671632444844) range410To415 range415To420

theorem range400To420 : chunk 400 20 = 2945640631840 :=
  join_chunk (f := 400) (a := 10) (b := 10) (u := 1559851940898) (v := 1385788690942) range400To410 range410To420

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch400

section Pack_Z6970PlateauChunkedBatch420

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range420To422 : chunk 420 2 = 256974085106 :=
  join_chunk (f := 420) (a := 1) (b := 1) (u := 129312595172) (v := 127661489934) oneChunk420 oneChunk421

theorem range423To425 : chunk 423 2 = 247138115748 :=
  join_chunk (f := 423) (a := 1) (b := 1) (u := 124382806896) (v := 122755308852) oneChunk423 oneChunk424

theorem range422To425 : chunk 422 3 = 373155303726 :=
  join_chunk (f := 422) (a := 1) (b := 2) (u := 126017187978) (v := 247138115748) oneChunk422 range423To425

theorem range420To425 : chunk 420 5 = 630129388832 :=
  join_chunk (f := 420) (a := 2) (b := 3) (u := 256974085106) (v := 373155303726) range420To422 range422To425

theorem range425To427 : chunk 425 2 = 240665107698 :=
  join_chunk (f := 425) (a := 1) (b := 1) (u := 121137817670) (v := 119527290028) oneChunk425 oneChunk426

theorem range428To430 : chunk 428 2 = 231083725466 :=
  join_chunk (f := 428) (a := 1) (b := 1) (u := 116333466774) (v := 114750258692) oneChunk428 oneChunk429

theorem range427To430 : chunk 427 3 = 349010581474 :=
  join_chunk (f := 427) (a := 1) (b := 2) (u := 117926856008) (v := 231083725466) oneChunk427 range428To430

theorem range425To430 : chunk 425 5 = 589675689172 :=
  join_chunk (f := 425) (a := 2) (b := 3) (u := 240665107698) (v := 349010581474) range425To427 range427To430

theorem range420To430 : chunk 420 10 = 1219805078004 :=
  join_chunk (f := 420) (a := 5) (b := 5) (u := 630129388832) (v := 589675689172) range420To425 range425To430

theorem range430To432 : chunk 430 2 = 224782542932 :=
  join_chunk (f := 430) (a := 1) (b := 1) (u := 113174177390) (v := 111608365542) oneChunk430 oneChunk431

theorem range433To435 : chunk 433 2 = 215462088016 :=
  join_chunk (f := 433) (a := 1) (b := 1) (u := 108501519408) (v := 106960568608) oneChunk433 oneChunk434

theorem range432To435 : chunk 432 3 = 325511851228 :=
  join_chunk (f := 432) (a := 1) (b := 2) (u := 110049763212) (v := 215462088016) oneChunk432 range433To435

theorem range430To435 : chunk 430 5 = 550294394160 :=
  join_chunk (f := 430) (a := 2) (b := 3) (u := 224782542932) (v := 325511851228) range430To432 range432To435

theorem range435To437 : chunk 435 2 = 209337007156 :=
  join_chunk (f := 435) (a := 1) (b := 1) (u := 105430066176) (v := 103906940980) oneChunk435 oneChunk436

theorem range438To440 : chunk 438 2 = 200283967894 :=
  join_chunk (f := 438) (a := 1) (b := 1) (u := 100889230764) (v := 99394737130) oneChunk438 oneChunk439

theorem range437To440 : chunk 437 3 = 302678322660 :=
  join_chunk (f := 437) (a := 1) (b := 2) (u := 102394354766) (v := 200283967894) oneChunk437 range438To440

theorem range435To440 : chunk 435 5 = 512015329816 :=
  join_chunk (f := 435) (a := 2) (b := 3) (u := 209337007156) (v := 302678322660) range435To437 range437To440

theorem range430To440 : chunk 430 10 = 1062309723976 :=
  join_chunk (f := 430) (a := 5) (b := 5) (u := 550294394160) (v := 512015329816) range430To435 range435To440

theorem range420To440 : chunk 420 20 = 2282114801980 :=
  join_chunk (f := 420) (a := 10) (b := 10) (u := 1219805078004) (v := 1062309723976) range420To430 range430To440

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch420

section Pack_Z6970PlateauChunkedBatch440

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range440To442 : chunk 440 2 = 194339359684 :=
  join_chunk (f := 440) (a := 1) (b := 1) (u := 97907791430) (v := 96431568254) oneChunk440 oneChunk441

theorem range443To445 : chunk 443 2 = 185560360616 :=
  join_chunk (f := 443) (a := 1) (b := 1) (u := 93505206160) (v := 92055154456) oneChunk443 oneChunk444

theorem range442To445 : chunk 442 3 = 280523340098 :=
  join_chunk (f := 442) (a := 1) (b := 2) (u := 94962979482) (v := 185560360616) oneChunk442 range443To445

theorem range440To445 : chunk 440 5 = 474862699782 :=
  join_chunk (f := 440) (a := 2) (b := 3) (u := 194339359684) (v := 280523340098) range440To442 range442To445

theorem range445To447 : chunk 445 2 = 179800690824 :=
  join_chunk (f := 445) (a := 1) (b := 1) (u := 90616011900) (v := 89184678924) oneChunk445 oneChunk446

theorem range448To450 : chunk 448 2 = 171302504762 :=
  join_chunk (f := 448) (a := 1) (b := 1) (u := 86351918490) (v := 84950586272) oneChunk448 oneChunk449

theorem range447To450 : chunk 447 3 = 259066854326 :=
  join_chunk (f := 447) (a := 1) (b := 2) (u := 87764349564) (v := 171302504762) oneChunk447 range448To450

theorem range445To450 : chunk 445 5 = 438867545150 :=
  join_chunk (f := 445) (a := 2) (b := 3) (u := 179800690824) (v := 259066854326) range445To447 range447To450

theorem range440To450 : chunk 440 10 = 913730244932 :=
  join_chunk (f := 440) (a := 5) (b := 5) (u := 474862699782) (v := 438867545150) range440To445 range445To450

theorem range450To452 : chunk 450 2 = 165732333972 :=
  join_chunk (f := 450) (a := 1) (b := 1) (u := 83557241792) (v := 82175092180) oneChunk450 oneChunk451

theorem range453To455 : chunk 453 2 = 157521869806 :=
  join_chunk (f := 453) (a := 1) (b := 1) (u := 79438240476) (v := 78083629330) oneChunk453 oneChunk454

theorem range452To455 : chunk 452 3 = 238322890310 :=
  join_chunk (f := 452) (a := 1) (b := 2) (u := 80801020504) (v := 157521869806) oneChunk452 range453To455

theorem range450To455 : chunk 450 5 = 404055224282 :=
  join_chunk (f := 450) (a := 2) (b := 3) (u := 165732333972) (v := 238322890310) range450To452 range452To455

theorem range455To457 : chunk 455 2 = 152145853394 :=
  join_chunk (f := 455) (a := 1) (b := 1) (u := 76740407384) (v := 75405446010) oneChunk455 oneChunk456

theorem range458To460 : chunk 458 2 = 144230168412 :=
  join_chunk (f := 458) (a := 1) (b := 1) (u := 72766851318) (v := 71463317094) oneChunk458 oneChunk459

theorem range457To460 : chunk 457 3 = 218312140572 :=
  join_chunk (f := 457) (a := 1) (b := 2) (u := 74081972160) (v := 144230168412) oneChunk457 range458To460

theorem range455To460 : chunk 455 5 = 370457993966 :=
  join_chunk (f := 455) (a := 2) (b := 3) (u := 152145853394) (v := 218312140572) range455To457 range457To460

theorem range450To460 : chunk 450 10 = 774513218248 :=
  join_chunk (f := 450) (a := 5) (b := 5) (u := 404055224282) (v := 370457993966) range450To455 range455To460

theorem range440To460 : chunk 440 20 = 1688243463180 :=
  join_chunk (f := 440) (a := 10) (b := 10) (u := 913730244932) (v := 774513218248) range440To450 range450To460

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch440

section Pack_Z6970PlateauChunkedBatch460

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range460To462 : chunk 460 2 = 139053056570 :=
  join_chunk (f := 460) (a := 1) (b := 1) (u := 70168229060) (v := 68884827510) oneChunk460 oneChunk461

theorem range463To465 : chunk 463 2 = 131439344014 :=
  join_chunk (f := 463) (a := 1) (b := 1) (u := 66346891766) (v := 65092452248) oneChunk463 oneChunk464

theorem range462To465 : chunk 462 3 = 199049310092 :=
  join_chunk (f := 462) (a := 1) (b := 2) (u := 67609966078) (v := 131439344014) oneChunk462 range463To465

theorem range460To465 : chunk 460 5 = 338102366662 :=
  join_chunk (f := 460) (a := 2) (b := 3) (u := 139053056570) (v := 199049310092) range460To462 range462To465

theorem range465To467 : chunk 465 2 = 126465981784 :=
  join_chunk (f := 465) (a := 1) (b := 1) (u := 63849901266) (v := 62616080518) oneChunk465 oneChunk466

theorem range468To470 : chunk 468 2 = 119161584032 :=
  join_chunk (f := 468) (a := 1) (b := 1) (u := 60181246936) (v := 58980337096) oneChunk468 oneChunk469

theorem range467To470 : chunk 467 3 = 180555834542 :=
  join_chunk (f := 467) (a := 1) (b := 2) (u := 61394250510) (v := 119161584032) oneChunk467 range468To470

theorem range465To470 : chunk 465 5 = 307021816326 :=
  join_chunk (f := 465) (a := 2) (b := 3) (u := 126465981784) (v := 180555834542) range465To467 range467To470

theorem range460To470 : chunk 460 10 = 645124182988 :=
  join_chunk (f := 460) (a := 5) (b := 5) (u := 338102366662) (v := 307021816326) range460To465 range465To470

theorem range470To472 : chunk 470 2 = 114396912380 :=
  join_chunk (f := 470) (a := 1) (b := 1) (u := 57788350654) (v := 56608561726) oneChunk470 oneChunk471

theorem range473To475 : chunk 473 2 = 107409310304 :=
  join_chunk (f := 473) (a := 1) (b := 1) (u := 54279328204) (v := 53129982100) oneChunk473 oneChunk474

theorem range472To475 : chunk 472 3 = 162847104228 :=
  join_chunk (f := 472) (a := 1) (b := 2) (u := 55437793924) (v := 107409310304) oneChunk472 range473To475

theorem range470To475 : chunk 470 5 = 277244016608 :=
  join_chunk (f := 470) (a := 2) (b := 3) (u := 114396912380) (v := 162847104228) range470To472 range472To475

theorem range475To477 : chunk 475 2 = 102858367076 :=
  join_chunk (f := 475) (a := 1) (b := 1) (u := 51993043436) (v := 50865323640) oneChunk475 oneChunk476

theorem range478To480 : chunk 478 2 = 96195193394 :=
  join_chunk (f := 478) (a := 1) (b := 1) (u := 48644230102) (v := 47550963292) oneChunk478 oneChunk479

theorem range477To480 : chunk 477 3 = 145945310822 :=
  join_chunk (f := 477) (a := 1) (b := 2) (u := 49750117428) (v := 96195193394) oneChunk477 range478To480

theorem range475To480 : chunk 475 5 = 248803677898 :=
  join_chunk (f := 475) (a := 2) (b := 3) (u := 102858367076) (v := 145945310822) range475To477 range477To480

theorem range470To480 : chunk 470 10 = 526047694506 :=
  join_chunk (f := 470) (a := 5) (b := 5) (u := 277244016608) (v := 248803677898) range470To475 range475To480

theorem range460To480 : chunk 460 20 = 1171171877494 :=
  join_chunk (f := 460) (a := 10) (b := 10) (u := 645124182988) (v := 526047694506) range460To470 range470To480

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch460

section Pack_Z6970PlateauChunkedBatch480

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem range480To482 : chunk 480 2 = 91863113384 :=
  join_chunk (f := 480) (a := 1) (b := 1) (u := 46467116146) (v := 45395997238) oneChunk480 oneChunk481

theorem range483To485 : chunk 483 2 = 85532139716 :=
  join_chunk (f := 483) (a := 1) (b := 1) (u := 43285638580) (v := 42246501136) oneChunk483 oneChunk484

theorem range482To485 : chunk 482 3 = 129866539252 :=
  join_chunk (f := 482) (a := 1) (b := 2) (u := 44334399536) (v := 85532139716) oneChunk482 range483To485

theorem range480To485 : chunk 480 5 = 221729652636 :=
  join_chunk (f := 480) (a := 2) (b := 3) (u := 91863113384) (v := 129866539252) range480To482 range482To485

theorem range485To487 : chunk 485 2 = 81424154646 :=
  join_chunk (f := 485) (a := 1) (b := 1) (u := 41220309734) (v := 40203844912) oneChunk485 oneChunk486

theorem range488To490 : chunk 488 2 = 75433304584 :=
  join_chunk (f := 488) (a := 1) (b := 1) (u := 38206857934) (v := 37226446650) oneChunk488 oneChunk489

theorem range487To490 : chunk 487 3 = 114633740802 :=
  join_chunk (f := 487) (a := 1) (b := 2) (u := 39200436218) (v := 75433304584) oneChunk487 range488To490

theorem range485To490 : chunk 485 5 = 196057895448 :=
  join_chunk (f := 485) (a := 2) (b := 3) (u := 81424154646) (v := 114633740802) range485To487 range487To490

theorem range480To490 : chunk 480 10 = 417787548084 :=
  join_chunk (f := 480) (a := 5) (b := 5) (u := 221729652636) (v := 196057895448) range480To485 range485To490

theorem range490To492 : chunk 490 2 = 71554743126 :=
  join_chunk (f := 490) (a := 1) (b := 1) (u := 36255970372) (v := 35298772754) oneChunk490 oneChunk491

theorem range493To495 : chunk 493 2 = 65912079040 :=
  join_chunk (f := 493) (a := 1) (b := 1) (u := 33417849352) (v := 32494229688) oneChunk493 oneChunk494

theorem range492To495 : chunk 492 3 = 100263694538 :=
  join_chunk (f := 492) (a := 1) (b := 2) (u := 34351615498) (v := 65912079040) oneChunk492 range493To495

theorem range490To495 : chunk 490 5 = 171818437664 :=
  join_chunk (f := 490) (a := 2) (b := 3) (u := 71554743126) (v := 100263694538) range490To492 range492To495

theorem range495To497 : chunk 495 2 = 62268366788 :=
  join_chunk (f := 495) (a := 1) (b := 1) (u := 31584114370) (v := 30684252418) oneChunk495 oneChunk496

theorem range498To500 : chunk 498 2 = 56982103146 :=
  join_chunk (f := 498) (a := 1) (b := 1) (u := 28922126266) (v := 28059976880) oneChunk498 oneChunk499

theorem range497To500 : chunk 497 3 = 86780111982 :=
  join_chunk (f := 497) (a := 1) (b := 2) (u := 29798008836) (v := 56982103146) oneChunk497 range498To500

theorem range495To500 : chunk 495 5 = 149048478770 :=
  join_chunk (f := 495) (a := 2) (b := 3) (u := 62268366788) (v := 86780111982) range495To497 range497To500

theorem range490To500 : chunk 490 10 = 320866916434 :=
  join_chunk (f := 490) (a := 5) (b := 5) (u := 171818437664) (v := 149048478770) range490To495 range495To500

theorem range480To500 : chunk 480 20 = 738654464518 :=
  join_chunk (f := 480) (a := 10) (b := 10) (u := 417787548084) (v := 320866916434) range480To490 range490To500

end ExpandedPlateauSum6970
end Pack_Z6970PlateauChunkedBatch480
