import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
open ProximityPrize.SubmissionBinaryLower B6402IntFarkas
namespace Binary6402NativeCaps
def allowance (m B W D q H cap : ℕ) (c : CapWitness) : Bool :=
  if c.useP64 then
    let mb := max (4*W/1048575) (4*B)
    checkSideP64 1 m B W D q c &&
    decide ((c.Cd+mb+B+1)*H+(c.Cd+mb+B)*q*B+c.Ch*B≤cap)
  else
    let den := 1482750-1048575
    let num := 2097152-1048575
    let psi := 1+(2*1048575-1)*(2*B-1)+2*(B-(2*1048575+1))
    decide (1≤B ∧ (((2*B-1)*den+num*psi)*H+num*q*B+q*(2097152-1048575-1)*B*den ≤ cap*den))

def witness0 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap0 : allowance 40 149 157207567 55364784 1 2737497 4117892515161989 witness0=true := by decide +kernel
def witness1 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap1 : allowance 40 149 157207567 55364784 2 2775333 4174807647121513 witness1=true := by decide +kernel
def witness2 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap2 : allowance 20 74 78603783 27682392 1 364457 271349262018626 witness2=true := by decide +kernel
def witness3 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap3 : allowance 20 74 78603783 27682392 2 369434 275054865617532 witness3=true := by decide +kernel
def witness4 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap4 : allowance 12 43 45232891 13841196 1 139266 59955529851960 witness4=true := by decide +kernel
def witness5 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap5 : allowance 12 43 45232891 13841196 2 141474 60906142274976 witness5=true := by decide +kernel
def witness6 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,4295079053,0,0⟩
theorem cap6 : allowance 8446 27939 29296488449 86130075 1 636946694 3200000000000000000 witness6=true := by decide +kernel
def witness7 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,8590158106,0,0⟩
theorem cap7 : allowance 8446 27939 29296488449 86130075 2 1273893389 6400000000000000000 witness7=true := by decide +kernel
def witness8 : CapWitness := ⟨true,399,4294967296,436,333,433842,5023419846,4295078833,0,0⟩
theorem cap8 : allowance 8446 27884 29238732641 86130075 1 636946831 3200000000000000000 witness8=true := by decide +kernel
def witness9 : CapWitness := ⟨true,399,4294967296,436,333,433842,5023419846,8590157666,0,0⟩
theorem cap9 : allowance 8446 27884 29238732641 86130075 2 1273893663 6400000000000000000 witness9=true := by decide +kernel
def witness10 : CapWitness := ⟨true,194,4294967296,667,654,433521,2449912901,4295137871,0,0⟩
theorem cap10 : allowance 12917 42643 44715177971 41733311 1 1305937819 3200000000000000000 witness10=true := by decide +kernel
def witness11 : CapWitness := ⟨true,194,4294967296,667,654,433521,2449912901,8590275742,0,0⟩
theorem cap11 : allowance 12917 42643 44715177971 41733311 2 2611875638 6400000000000000000 witness11=true := by decide +kernel
def witness12 : CapWitness := ⟨true,169,4294967296,820,757,433418,2138759617,4295177179,0,0⟩
theorem cap12 : allowance 15898 52470 55019521811 36364460 1 1495852983 3200000000000000000 witness12=true := by decide +kernel
def witness13 : CapWitness := ⟨true,169,4294967296,820,757,433418,2138759617,8590354358,0,0⟩
theorem cap13 : allowance 15898 52470 55019521811 36364460 2 2991705967 6400000000000000000 witness13=true := by decide +kernel
def witness14 : CapWitness := ⟨true,81,4294967296,431,1411,432764,1031009360,4295077617,0,0⟩
theorem cap14 : allowance 8467 27580 28920102849 17259510 1 3103197012 3200000000000000000 witness14=true := by decide +kernel
def witness15 : CapWitness := ⟨true,81,4294967296,431,1411,432764,1031009360,8590155234,0,0⟩
theorem cap15 : allowance 8467 27580 28920102849 17259510 2 6206394024 6400000000000000000 witness15=true := by decide +kernel
def witness16 : CapWitness := ⟨true,57,4294967296,120,1935,432240,730672327,4294997978,0,0⟩
theorem cap16 : allowance 2400 7670 8043301631 12079595 1 2873861721 2100000000000000000 witness16=true := by decide +kernel
def witness17 : CapWitness := ⟨true,57,4294967296,120,1935,432240,730672327,8589995956,0,0⟩
theorem cap17 : allowance 2400 7670 8043301631 12079595 2 5747723443 4200000000000000000 witness17=true := by decide +kernel
def witness18 : CapWitness := ⟨true,39,4294967296,21,2789,431386,504558818,4294972451,0,0⟩
theorem cap18 : allowance 350 1288 1351448989 8178892 1 347156501 175169292686641318 witness18=true := by decide +kernel
def witness19 : CapWitness := ⟨true,39,1073741824,81,2797,431378,504568137,3000000000,0,0⟩
theorem cap19 : allowance 350 1288 1351448989 8178892 2 352148071 177690129158901331 witness19=true := by decide +kernel
def witness20 : CapWitness := ⟨true,23,4294967296,7,4657,429518,297858423,5000000000,0,0⟩
theorem cap20 : allowance 120 440 461975811 4613734 1 50685878 15099658409114628 witness20=true := by decide +kernel
def witness21 : CapWitness := ⟨true,23,1073741824,28,4659,429516,297859800,5000000000,0,0⟩
theorem cap21 : allowance 120 440 461975811 4613734 2 51421148 15318868258401204 witness21=true := by decide +kernel
def witness22 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap22 : allowance 80 299 314415135 110729568 1 10018396 30292660535263279 witness22=true := by decide +kernel
def witness23 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap23 : allowance 80 299 314415135 110729568 2 10156674 30710772537539751 witness23=true := by decide +kernel
def witness24 : CapWitness := ⟨true,39,4294967296,21,2789,431386,504558818,4294972451,0,0⟩
theorem cap24 : allowance 350 1288 1351448989 8178892 1 347156496 175169290163815008 witness24=true := by decide +kernel
def witness25 : CapWitness := ⟨true,39,1073741824,81,2797,431378,504568137,3000000000,0,0⟩
theorem cap25 : allowance 350 1288 1351448989 8178892 2 352148065 177690126131453845 witness25=true := by decide +kernel
def witness26 : CapWitness := ⟨true,23,4294967296,7,4657,429518,297858423,5000000000,0,0⟩
theorem cap26 : allowance 120 440 461975811 4613734 1 50685879 15099658706975254 witness26=true := by decide +kernel
def witness27 : CapWitness := ⟨true,23,1073741824,28,4659,429516,297859800,5000000000,0,0⟩
theorem cap27 : allowance 120 440 461975811 4613734 2 51421149 15318868556263207 witness27=true := by decide +kernel
def witness28 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap28 : allowance 80 299 314415135 110729568 1 10018395 30292657511559662 witness28=true := by decide +kernel
def witness29 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap29 : allowance 80 299 314415135 110729568 2 10156673 30710769513836134 witness29=true := by decide +kernel
def witness30 : CapWitness := ⟨true,138,4294967296,667,884,433291,1743524710,4295137824,0,0⟩
theorem cap30 : allowance 12917 42632 44702993405 29548745 1 1834990570 3200000000000000000 witness30=true := by decide +kernel
def witness31 : CapWitness := ⟨true,138,4294967296,667,884,433291,1743524710,8590275648,0,0⟩
theorem cap31 : allowance 12917 42632 44702993405 29548745 2 3669981140 6400000000000000000 witness31=true := by decide +kernel
def witness32 : CapWitness := ⟨true,39,4294967296,21,2789,431386,504558818,4294972451,0,0⟩
theorem cap32 : allowance 350 1288 1351448989 8178892 1 346358579 174766688963655754 witness32=true := by decide +kernel
def witness33 : CapWitness := ⟨true,39,1073741824,81,2797,431378,504568137,3000000000,0,0⟩
theorem cap33 : allowance 350 1288 1351448989 8178892 2 351338672 177281726997614512 witness33=true := by decide +kernel
def witness34 : CapWitness := ⟨true,23,4294967296,7,4657,429518,297858423,5000000000,0,0⟩
theorem cap34 : allowance 120 440 461975811 4613734 1 50637408 15085221104572408 witness34=true := by decide +kernel
def witness35 : CapWitness := ⟨true,23,1073741824,28,4659,429516,297859800,5000000000,0,0⟩
theorem cap35 : allowance 120 440 461975811 4613734 2 51371975 15304221490127685 witness35=true := by decide +kernel
def witness36 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap36 : allowance 80 299 314415135 110729568 1 10017935 30291266607895842 witness36=true := by decide +kernel
def witness37 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap37 : allowance 80 299 314415135 110729568 2 10156208 30709363491654229 witness37=true := by decide +kernel
def witness38 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap38 : allowance 80 299 314415135 110729568 2 10156207 30709360467950612 witness38=true := by decide +kernel
def witness39 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap39 : allowance 80 299 314415135 110729568 1 10018394 30292654487856045 witness39=true := by decide +kernel
def witness40 : CapWitness := ⟨true,39,4294967296,21,2789,431386,504558818,4294972451,0,0⟩
theorem cap40 : allowance 350 1288 1351448989 8178892 1 347156530 175169307319033916 witness40=true := by decide +kernel
def witness41 : CapWitness := ⟨true,39,1073741824,81,2797,431378,504568137,3000000000,0,0⟩
theorem cap41 : allowance 350 1288 1351448989 8178892 2 352148100 177690143791564180 witness41=true := by decide +kernel
def witness42 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap42 : allowance 80 299 314415135 110729568 2 10156672 30710766490132517 witness42=true := by decide +kernel
def witness43 : CapWitness := ⟨true,39,4294967296,21,2789,431386,504558818,4294972451,0,0⟩
theorem cap43 : allowance 350 1288 1351448989 8178892 1 346358576 174766687449959968 witness43=true := by decide +kernel
def witness44 : CapWitness := ⟨true,39,1073741824,81,2797,431378,504568137,3000000000,0,0⟩
theorem cap44 : allowance 350 1288 1351448989 8178892 2 351338669 177281725483890769 witness44=true := by decide +kernel
def witness45 : CapWitness := ⟨true,23,1073741824,28,4659,429516,297859800,5000000000,0,0⟩
theorem cap45 : allowance 120 440 461975811 4613734 2 51371974 15304221192265682 witness45=true := by decide +kernel
def witness46 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap46 : allowance 80 299 314415135 110729568 1 10017936 30291269631599459 witness46=true := by decide +kernel
def witness47 : CapWitness := ⟨true,23,4294967296,7,4657,429518,297858423,5000000000,0,0⟩
theorem cap47 : allowance 120 440 461975811 4613734 1 50637409 15085221402433034 witness47=true := by decide +kernel
def witness48 : CapWitness := ⟨true,23,1073741824,28,4659,429516,297859800,5000000000,0,0⟩
theorem cap48 : allowance 120 440 461975811 4613734 2 51371976 15304221787989688 witness48=true := by decide +kernel
def witness49 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap49 : allowance 12 43 45232891 13841196 1 32217 13869804058128 witness49=true := by decide +kernel
def witness50 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap50 : allowance 12 43 45232891 13841196 2 32682 14070036561120 witness50=true := by decide +kernel
def witness51 : CapWitness := ⟨true,104,4294967296,432,1114,433061,1311822899,4295077636,0,0⟩
theorem cap51 : allowance 8467 27585 28924947315 22103976 1 2438979326 3200000000000000000 witness51=true := by decide +kernel
def witness52 : CapWitness := ⟨true,104,4294967296,432,1114,433061,1311822899,8590155272,0,0⟩
theorem cap52 : allowance 8467 27585 28924947315 22103976 2 4877958653 6400000000000000000 witness52=true := by decide +kernel
def witness53 : CapWitness := ⟨true,149,4294967296,127,757,433418,1883055793,4294999673,0,0⟩
theorem cap53 : allowance 2389 8094 8487573159 31960605 1 1115158068 2100000000000000000 witness53=true := by decide +kernel
def witness54 : CapWitness := ⟨true,149,4294967296,127,757,433418,1883055793,8589999346,0,0⟩
theorem cap54 : allowance 2389 8094 8487573159 31960605 2 2230316137 4200000000000000000 witness54=true := by decide +kernel
def witness55 : CapWitness := ⟨true,149,4294967296,127,757,433418,1883055793,4294999626,0,0⟩
theorem cap55 : allowance 2389 8082 8475346703 31960605 1 1115158143 2100000000000000000 witness55=true := by decide +kernel
def witness56 : CapWitness := ⟨true,149,4294967296,127,757,433418,1883055793,8589999252,0,0⟩
theorem cap56 : allowance 2389 8082 8475346703 31960605 2 2230316286 4200000000000000000 witness56=true := by decide +kernel
def witness57 : CapWitness := ⟨true,121,4294967296,203,937,433238,1532998324,4295019230,0,0⟩
theorem cap57 : allowance 3985 12983 13614355991 25920796 1 1369757147 2100000000000000000 witness57=true := by decide +kernel
def witness58 : CapWitness := ⟨true,121,4294967296,203,937,433238,1532998324,8590038460,0,0⟩
theorem cap58 : allowance 3985 12983 13614355991 25920796 2 2739514295 4200000000000000000 witness58=true := by decide +kernel
def witness59 : CapWitness := ⟨true,121,4294967296,203,937,433238,1532998324,4295019229,0,0⟩
theorem cap59 : allowance 3985 12983 13614041351 25920796 1 1369757148 2100000000000000000 witness59=true := by decide +kernel
def witness60 : CapWitness := ⟨true,121,4294967296,203,937,433238,1532998324,8590038458,0,0⟩
theorem cap60 : allowance 3985 12983 13614041351 25920796 2 2739514297 4200000000000000000 witness60=true := by decide +kernel
def witness61 : CapWitness := ⟨true,166,4294967296,305,704,433471,2093456600,4295045179,0,0⟩
theorem cap61 : allowance 5977 19470 20416758677 35588634 1 1003019583 2100000000000000000 witness61=true := by decide +kernel
def witness62 : CapWitness := ⟨true,166,4294967296,305,704,433471,2093456600,8590090358,0,0⟩
theorem cap62 : allowance 5977 19470 20416758677 35588634 2 2006039166 4200000000000000000 witness62=true := by decide +kernel
def witness63 : CapWitness := ⟨true,53,4294967296,55,2069,432106,672272027,4294981358,0,0⟩
theorem cap63 : allowance 1100 3515 3686513247 11072962 1 1859291785 1250000000000000000 witness63=true := by decide +kernel
def witness64 : CapWitness := ⟨true,53,4294967296,55,2069,432106,672272027,8589962716,0,0⟩
theorem cap64 : allowance 1100 3515 3686513247 11072962 2 3718583570 2500000000000000000 witness64=true := by decide +kernel
def witness65 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap65 : allowance 200 740 776390947 7969177 1 133371331 65676497610037343 witness65=true := by decide +kernel
def witness66 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap66 : allowance 200 740 776390947 7969177 2 135265617 66609634171525021 witness66=true := by decide +kernel
def witness67 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap67 : allowance 80 299 314415135 110729568 1 12179646 36827639977504529 witness67=true := by decide +kernel
def witness68 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap68 : allowance 80 299 314415135 110729568 2 12347841 37336212120890790 witness68=true := by decide +kernel
def witness69 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap69 : allowance 80 299 314415135 110729568 1 27369684 82757812820471975 witness69=true := by decide +kernel
def witness70 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap70 : allowance 80 299 314415135 110729568 2 27748148 83902176099701209 witness70=true := by decide +kernel
def witness71 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap71 : allowance 12 43 45232891 13841196 1 32220 13871095589832 witness71=true := by decide +kernel
def witness72 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap72 : allowance 12 43 45232891 13841196 2 32685 14071328092824 witness72=true := by decide +kernel
def witness73 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap73 : allowance 80 299 314415135 110729568 1 27392865 82827905294017652 witness73=true := by decide +kernel
def witness74 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap74 : allowance 80 299 314415135 110729568 2 27771650 83973239182107943 witness74=true := by decide +kernel
def witness75 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap75 : allowance 12 43 45232891 13841196 1 49588 21348203134856 witness75=true := by decide +kernel
def witness76 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap76 : allowance 12 43 45232891 13841196 2 50336 21670270128592 witness76=true := by decide +kernel
def witness77 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap77 : allowance 80 299 314415135 110729568 1 12179644 36827633930097295 witness77=true := by decide +kernel
def witness78 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap78 : allowance 80 299 314415135 110729568 2 12347840 37336209097187173 witness78=true := by decide +kernel
def witness79 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap79 : allowance 80 299 314415135 110729568 1 27369687 82757821891582826 witness79=true := by decide +kernel
def witness80 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap80 : allowance 80 299 314415135 110729568 2 27748151 83902185170812060 witness80=true := by decide +kernel
def witness81 : CapWitness := ⟨true,127,4294967296,436,924,433251,1609695573,4295078828,0,0⟩
theorem cap81 : allowance 8446 27883 29237600369 27241995 1 1987679094 3200000000000000000 witness81=true := by decide +kernel
def witness82 : CapWitness := ⟨true,127,4294967296,436,924,433251,1609695573,8590157656,0,0⟩
theorem cap82 : allowance 8446 27883 29237600369 27241995 2 3975358189 6400000000000000000 witness82=true := by decide +kernel
def witness83 : CapWitness := ⟨true,91,4294967296,436,1264,432911,1150130779,4295078798,0,0⟩
theorem cap83 : allowance 8446 27875 29229673061 19314687 1 2781823201 3200000000000000000 witness83=true := by decide +kernel
def witness84 : CapWitness := ⟨true,91,4294967296,436,1264,432911,1150130779,8590157596,0,0⟩
theorem cap84 : allowance 8446 27875 29229673061 19314687 2 5563646403 6400000000000000000 witness84=true := by decide +kernel
def witness85 : CapWitness := ⟨true,160,4294967296,124,706,433469,2017981550,4294998856,0,0⟩
theorem cap85 : allowance 2385 7890 8273336149 34288447 1 1040598779 2100000000000000000 witness85=true := by decide +kernel
def witness86 : CapWitness := ⟨true,160,4294967296,124,706,433469,2017981550,8589997712,0,0⟩
theorem cap86 : allowance 2385 7890 8273336149 34288447 2 2081197558 4200000000000000000 witness86=true := by decide +kernel
def witness87 : CapWitness := ⟨true,181,4294967296,305,649,433526,2289191161,4295045192,0,0⟩
theorem cap87 : allowance 5977 19474 20420135123 38965080 1 917259553 2100000000000000000 witness87=true := by decide +kernel
def witness88 : CapWitness := ⟨true,181,4294967296,305,649,433526,2289191161,8590090384,0,0⟩
theorem cap88 : allowance 5977 19474 20420135123 38965080 2 1834519106 4200000000000000000 witness88=true := by decide +kernel
def witness89 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap89 : allowance 200 740 776390947 7969177 1 133362535 65672166340073315 witness89=true := by decide +kernel
def witness90 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap90 : allowance 200 740 776390947 7969177 2 135256696 66605241349861868 witness90=true := by decide +kernel
def witness91 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap91 : allowance 80 299 314415135 110729568 1 12178869 36825290559794120 witness91=true := by decide +kernel
def witness92 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap92 : allowance 80 299 314415135 110729568 2 12347054 37333832466144211 witness92=true := by decide +kernel
def witness93 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap93 : allowance 20 74 78603783 27682392 1 3129761 2330201156985482 witness93=true := by decide +kernel
def witness94 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap94 : allowance 20 74 78603783 27682392 2 3173263 2362589780336863 witness94=true := by decide +kernel
def witness95 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap95 : allowance 200 740 776390947 262982724 1 202259535 1515102681173026613 witness95=true := by decide +kernel
def witness96 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap96 : allowance 200 740 776390947 262982724 2 205132751 1536625609226345136 witness96=true := by decide +kernel
def witness97 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap97 : allowance 20 74 78603783 27682392 1 977104 727483356821859 witness97=true := by decide +kernel
def witness98 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap98 : allowance 20 74 78603783 27682392 2 990616 737543524303630 witness98=true := by decide +kernel
def witness99 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap99 : allowance 12 43 45232891 13841196 1 29516 12706995013960 witness99=true := by decide +kernel
def witness100 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap100 : allowance 12 43 45232891 13841196 2 29937 12888285051960 witness100=true := by decide +kernel
def witness101 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,4295079042,0,0⟩
theorem cap101 : allowance 8446 27936 29293520933 86130075 1 636946702 3200000000000000000 witness101=true := by decide +kernel
def witness102 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,8590158084,0,0⟩
theorem cap102 : allowance 8446 27936 29293520933 86130075 2 1273893404 6400000000000000000 witness102=true := by decide +kernel
def witness103 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,4295019293,0,0⟩
theorem cap103 : allowance 3985 12999 13630713791 42278596 1 846312630 2100000000000000000 witness103=true := by decide +kernel
def witness104 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,8590038586,0,0⟩
theorem cap104 : allowance 3985 12999 13630713791 42278596 2 1692625260 4200000000000000000 witness104=true := by decide +kernel
def witness105 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,4295019280,0,0⟩
theorem cap105 : allowance 3985 12996 13627372901 42278596 1 846312644 2100000000000000000 witness105=true := by decide +kernel
def witness106 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,8590038560,0,0⟩
theorem cap106 : allowance 3985 12996 13627372901 42278596 2 1692625288 4200000000000000000 witness106=true := by decide +kernel
def witness107 : CapWitness := ⟨true,213,4294967296,316,559,433616,2689148968,4295048115,0,0⟩
theorem cap107 : allowance 5973 20204 21186378809 45864673 1 780834394 2100000000000000000 witness107=true := by decide +kernel
def witness108 : CapWitness := ⟨true,213,4294967296,316,559,433616,2689148968,8590096230,0,0⟩
theorem cap108 : allowance 5973 20204 21186378809 45864673 2 1561668789 4200000000000000000 witness108=true := by decide +kernel
def witness109 : CapWitness := ⟨true,141,4294967296,300,821,433354,1781032592,4295044002,0,0⟩
theorem cap109 : allowance 6000 19176 20108254079 30198988 1 1178962389 2100000000000000000 witness109=true := by decide +kernel
def witness110 : CapWitness := ⟨true,141,4294967296,300,821,433354,1781032592,8590088004,0,0⟩
theorem cap110 : allowance 6000 19176 20108254079 30198988 2 2357924779 4200000000000000000 witness110=true := by decide +kernel
def witness111 : CapWitness := ⟨true,85,4294967296,59,1301,432874,1073423304,4294982370,0,0⟩
theorem cap111 : allowance 1100 3768 3951802777 17993564 1 1164459375 1250000000000000000 witness111=true := by decide +kernel
def witness112 : CapWitness := ⟨true,85,4294967296,59,1301,432874,1073423304,8589964740,0,0⟩
theorem cap112 : allowance 1100 3768 3951802777 17993564 2 2328918750 2500000000000000000 witness112=true := by decide +kernel
def witness113 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap113 : allowance 200 740 776390947 7969177 1 133383193 65682338620077509 witness113=true := by decide +kernel
def witness114 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap114 : allowance 200 740 776390947 7969177 2 135277647 66615557907048811 witness114=true := by decide +kernel
def witness115 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap115 : allowance 80 299 314415135 110729568 1 12180856 36831298658881099 witness115=true := by decide +kernel
def witness116 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap116 : allowance 80 299 314415135 110729568 2 12349069 37339925228932466 witness116=true := by decide +kernel
def witness117 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap117 : allowance 20 74 78603783 27682392 1 363179 270397752628784 witness117=true := by decide +kernel
def witness118 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap118 : allowance 20 74 78603783 27682392 2 368138 274089954686988 witness118=true := by decide +kernel
def witness119 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap119 : allowance 12 43 45232891 13841196 1 55156 23745285977480 witness119=true := by decide +kernel
def witness120 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap120 : allowance 12 43 45232891 13841196 2 55995 24106529432904 witness120=true := by decide +kernel
def witness121 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap121 : allowance 12 43 45232891 13841196 1 39616 17055151750760 witness121=true := by decide +kernel
def witness122 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap122 : allowance 12 43 45232891 13841196 2 40202 17307476032480 witness122=true := by decide +kernel
def witness123 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap123 : allowance 80 299 314415135 110729568 1 16364292 49480769223569111 witness123=true := by decide +kernel
def witness124 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap124 : allowance 80 299 314415135 110729568 2 16590414 50164495446377331 witness124=true := by decide +kernel
def witness125 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap125 : allowance 12 43 45232891 13841196 1 29518 12707856035096 witness125=true := by decide +kernel
def witness126 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap126 : allowance 12 43 45232891 13841196 2 29939 12889146073096 witness126=true := by decide +kernel
def witness127 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap127 : allowance 12 43 45232891 13841196 1 39619 17056443282464 witness127=true := by decide +kernel
def witness128 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap128 : allowance 12 43 45232891 13841196 2 40205 17308767564184 witness128=true := by decide +kernel
def witness129 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap129 : allowance 80 299 314415135 110729568 1 16371289 49501926077777260 witness129=true := by decide +kernel
def witness130 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap130 : allowance 80 299 314415135 110729568 2 16597507 50185942576132712 witness130=true := by decide +kernel
def witness131 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap131 : allowance 12 43 45232891 13841196 1 29519 12708286545664 witness131=true := by decide +kernel
def witness132 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap132 : allowance 12 43 45232891 13841196 2 29941 12890007094232 witness132=true := by decide +kernel
def witness133 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap133 : allowance 12 43 45232891 13841196 1 39620 17056873793032 witness133=true := by decide +kernel
def witness134 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap134 : allowance 12 43 45232891 13841196 2 40206 17309198074752 witness134=true := by decide +kernel
def witness135 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap135 : allowance 80 299 314415135 110729568 1 16377769 49521519677215420 witness135=true := by decide +kernel
def witness136 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap136 : allowance 80 299 314415135 110729568 2 16604077 50205808308896402 witness136=true := by decide +kernel
def witness137 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap137 : allowance 200 740 776390947 7969177 1 133383185 65682334680768765 witness137=true := by decide +kernel
def witness138 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap138 : allowance 200 740 776390947 7969177 2 135277639 66615553967740067 witness138=true := by decide +kernel
def witness139 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap139 : allowance 80 299 314415135 110729568 1 12180854 36831292611473865 witness139=true := by decide +kernel
def witness140 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap140 : allowance 80 299 314415135 110729568 2 12349067 37339919181525232 witness140=true := by decide +kernel
def witness141 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap141 : allowance 80 299 314415135 110729568 1 16364286 49480751081347409 witness141=true := by decide +kernel
def witness142 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap142 : allowance 80 299 314415135 110729568 2 16590407 50164474280452012 witness142=true := by decide +kernel
def witness143 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap143 : allowance 12 43 45232891 13841196 1 29517 12707425524528 witness143=true := by decide +kernel
def witness144 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap144 : allowance 12 43 45232891 13841196 1 39618 17056012771896 witness144=true := by decide +kernel
def witness145 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap145 : allowance 12 43 45232891 13841196 2 40204 17308337053616 witness145=true := by decide +kernel
def witness146 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap146 : allowance 80 299 314415135 110729568 1 16365908 49485655528614183 witness146=true := by decide +kernel
def witness147 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap147 : allowance 80 299 314415135 110729568 2 16592052 50169448272901977 witness147=true := by decide +kernel
def witness148 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,4295079042,0,0⟩
theorem cap148 : allowance 8446 27936 29293521905 86130075 1 636946702 3200000000000000000 witness148=true := by decide +kernel
def witness149 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,8590158084,0,0⟩
theorem cap149 : allowance 8446 27936 29293521905 86130075 2 1273893404 6400000000000000000 witness149=true := by decide +kernel
def witness150 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,4295019280,0,0⟩
theorem cap150 : allowance 3985 12996 13627373171 42278596 1 846312644 2100000000000000000 witness150=true := by decide +kernel
def witness151 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,8590038560,0,0⟩
theorem cap151 : allowance 3985 12996 13627373171 42278596 2 1692625288 4200000000000000000 witness151=true := by decide +kernel
def witness152 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap152 : allowance 200 740 776390947 7969177 1 133383177 65682330741460021 witness152=true := by decide +kernel
def witness153 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap153 : allowance 200 740 776390947 7969177 2 135277631 66615550028431323 witness153=true := by decide +kernel
def witness154 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,4295079042,0,0⟩
theorem cap154 : allowance 8446 27936 29293527737 86130075 1 636946702 3200000000000000000 witness154=true := by decide +kernel
def witness155 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,8590158084,0,0⟩
theorem cap155 : allowance 8446 27936 29293527737 86130075 2 1273893404 6400000000000000000 witness155=true := by decide +kernel
def witness156 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,4295019280,0,0⟩
theorem cap156 : allowance 3985 12996 13627374791 42278596 1 846312644 2100000000000000000 witness156=true := by decide +kernel
def witness157 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,8590038560,0,0⟩
theorem cap157 : allowance 3985 12996 13627374791 42278596 2 1692625288 4200000000000000000 witness157=true := by decide +kernel
def witness158 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap158 : allowance 200 740 776390947 7969177 1 133383205 65682344529040625 witness158=true := by decide +kernel
def witness159 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap159 : allowance 200 740 776390947 7969177 2 135277659 66615563816011927 witness159=true := by decide +kernel
def witness160 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap160 : allowance 80 299 314415135 110729568 2 12349068 37339922205228849 witness160=true := by decide +kernel
def witness161 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap161 : allowance 12 43 45232891 13841196 1 48559 20905207760384 witness161=true := by decide +kernel
def witness162 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap162 : allowance 12 43 45232891 13841196 2 49290 21219956074464 witness162=true := by decide +kernel
def witness163 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap163 : allowance 80 299 314415135 110729568 1 16364283 49480742010236558 witness163=true := by decide +kernel
def witness164 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap164 : allowance 80 299 314415135 110729568 2 16590404 50164465209341161 witness164=true := by decide +kernel
def witness165 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap165 : allowance 12 43 45232891 13841196 1 103528 44569943172776 witness165=true := by decide +kernel
def witness166 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap166 : allowance 12 43 45232891 13841196 2 105154 45269998445216 witness166=true := by decide +kernel
def witness167 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap167 : allowance 12 43 45232891 13841196 1 128352 55256937512808 witness167=true := by decide +kernel
def witness168 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap168 : allowance 12 43 45232891 13841196 2 130382 56130919054720 witness168=true := by decide +kernel
def witness169 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap169 : allowance 80 299 314415135 110729568 1 16371298 49501953291109813 witness169=true := by decide +kernel
def witness170 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap170 : allowance 80 299 314415135 110729568 2 16597516 50185969789465265 witness170=true := by decide +kernel
def witness171 : CapWitness := ⟨true,231,4294967296,316,519,433656,2918918963,4295048130,0,0⟩
theorem cap171 : allowance 5973 20208 21190342463 49828327 1 719369587 2100000000000000000 witness171=true := by decide +kernel
def witness172 : CapWitness := ⟨true,231,4294967296,316,519,433656,2918918963,8590096260,0,0⟩
theorem cap172 : allowance 5973 20208 21190342463 49828327 2 1438739175 4200000000000000000 witness172=true := by decide +kernel
def witness173 : CapWitness := ⟨true,234,4294967296,431,527,433648,2951830095,4295077617,0,0⟩
theorem cap173 : allowance 8467 27580 28920102849 50394512 1 711322117 2100000000000000000 witness173=true := by decide +kernel
def witness174 : CapWitness := ⟨true,234,4294967296,431,527,433648,2951830095,8590155234,0,0⟩
theorem cap174 : allowance 8467 27580 28920102849 50394512 2 1422644235 4200000000000000000 witness174=true := by decide +kernel
def witness175 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap175 : allowance 200 740 776390947 7969177 1 133373416 65677524292378748 witness175=true := by decide +kernel
def witness176 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap176 : allowance 200 740 776390947 7969177 2 135267731 66610675133860623 witness176=true := by decide +kernel
def witness177 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap177 : allowance 80 299 314415135 110729568 1 12180182 36829260682643241 witness177=true := by decide +kernel
def witness178 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap178 : allowance 80 299 314415135 110729568 2 12348385 37337857015658438 witness178=true := by decide +kernel
def witness179 : CapWitness := ⟨true,242,4294967296,432,512,433663,3053959762,4295077883,0,0⟩
theorem cap179 : allowance 8446 27646 28989779774 52156191 1 1047706009 3200000000000000000 witness179=true := by decide +kernel
def witness180 : CapWitness := ⟨true,242,4294967296,432,512,433663,3053959762,8590155766,0,0⟩
theorem cap180 : allowance 8446 27646 28989779774 52156191 2 2095412019 6400000000000000000 witness180=true := by decide +kernel
def witness181 : CapWitness := ⟨true,102,4294967296,645,1161,433014,1294901903,4295132246,0,0⟩
theorem cap181 : allowance 13000 41237 43240727919 21810380 1 2470658238 3200000000000000000 witness181=true := by decide +kernel
def witness182 : CapWitness := ⟨true,102,4294967296,645,1161,433014,1294901903,8590264492,0,0⟩
theorem cap182 : allowance 13000 41237 43240727919 21810380 2 4941316477 6400000000000000000 witness182=true := by decide +kernel
def witness183 : CapWitness := ⟨true,127,4294967296,432,923,433252,1609691862,4295077788,0,0⟩
theorem cap183 : allowance 8446 27623 28964865578 27241995 1 1987686235 3200000000000000000 witness183=true := by decide +kernel
def witness184 : CapWitness := ⟨true,127,4294967296,432,923,433252,1609691862,8590155576,0,0⟩
theorem cap184 : allowance 8446 27623 28964865578 27241995 2 3975372470 6400000000000000000 witness184=true := by decide +kernel
def witness185 : CapWitness := ⟨true,157,4294967296,654,786,433389,1986690609,4295134619,0,0⟩
theorem cap185 : allowance 12950 41830 43862841056 33743167 1 1610417033 3200000000000000000 witness185=true := by decide +kernel
def witness186 : CapWitness := ⟨true,157,4294967296,654,786,433389,1986690609,8590269238,0,0⟩
theorem cap186 : allowance 12950 41830 43862841056 33743167 2 3220834067 6400000000000000000 witness186=true := by decide +kernel
def witness187 : CapWitness := ⟨true,138,4294967296,660,883,433292,1743520691,4295136233,0,0⟩
theorem cap187 : allowance 12917 42234 44285869607 29548745 1 1834998271 3200000000000000000 witness187=true := by decide +kernel
def witness188 : CapWitness := ⟨true,138,4294967296,660,883,433292,1743520691,8590272466,0,0⟩
theorem cap188 : allowance 12917 42234 44285869607 29548745 2 3669996542 6400000000000000000 witness188=true := by decide +kernel
def witness189 : CapWitness := ⟨true,152,4294967296,805,828,433347,1915022895,4295173193,0,0⟩
theorem cap189 : allowance 15938 51474 53974642163 32505761 1 1670606844 3200000000000000000 witness189=true := by decide +kernel
def witness190 : CapWitness := ⟨true,152,4294967296,805,828,433347,1915022895,8590346386,0,0⟩
theorem cap190 : allowance 15938 51474 53974642163 32505761 2 3341213688 6400000000000000000 witness190=true := by decide +kernel
def witness191 : CapWitness := ⟨true,117,4294967296,126,958,433217,1481906531,4294999301,0,0⟩
theorem cap191 : allowance 2389 8001 8390055529 25039999 1 1417023978 2100000000000000000 witness191=true := by decide +kernel
def witness192 : CapWitness := ⟨true,117,4294967296,126,958,433217,1481906531,8589998602,0,0⟩
theorem cap192 : allowance 2389 8001 8390055529 25039999 2 2834047956 4200000000000000000 witness192=true := by decide +kernel
def witness193 : CapWitness := ⟨true,116,4294967296,122,966,433209,1470969525,4294998526,0,0⟩
theorem cap193 : allowance 2385 7807 8186828574 24851257 1 1427561360 2100000000000000000 witness193=true := by decide +kernel
def witness194 : CapWitness := ⟨true,116,4294967296,122,966,433209,1470969525,8589997052,0,0⟩
theorem cap194 : allowance 2385 7807 8186828574 24851257 2 2855122720 4200000000000000000 witness194=true := by decide +kernel
def witness195 : CapWitness := ⟨true,303,4294967296,645,447,433728,3823743381,4295132246,0,0⟩
theorem cap195 : allowance 13000 41237 43240727919 65431142 1 549082867 2100000000000000000 witness195=true := by decide +kernel
def witness196 : CapWitness := ⟨true,303,4294967296,645,447,433728,3823743381,8590264492,0,0⟩
theorem cap196 : allowance 13000 41237 43240727919 65431142 2 1098165734 4200000000000000000 witness196=true := by decide +kernel
def witness197 : CapWitness := ⟨true,155,4294967296,209,739,433436,1956034896,4295020609,0,0⟩
theorem cap197 : allowance 3982 13328 13975899935 33218884 1 1073521309 2100000000000000000 witness197=true := by decide +kernel
def witness198 : CapWitness := ⟨true,155,4294967296,209,739,433436,1956034896,8590041218,0,0⟩
theorem cap198 : allowance 3982 13328 13975899935 33218884 2 2147042619 4200000000000000000 witness198=true := by decide +kernel
def witness199 : CapWitness := ⟨true,155,4294967296,208,739,433436,1956034896,4295020537,0,0⟩
theorem cap199 : allowance 3982 13310 13957025855 33218884 1 1073521416 2100000000000000000 witness199=true := by decide +kernel
def witness200 : CapWitness := ⟨true,155,4294967296,208,739,433436,1956034896,8590041074,0,0⟩
theorem cap200 : allowance 3982 13310 13957025855 33218884 2 2147042833 4200000000000000000 witness200=true := by decide +kernel
def witness201 : CapWitness := ⟨true,209,4294967296,305,568,433607,2632000601,4295045200,0,0⟩
theorem cap201 : allowance 5962 19476 20422052159 44879046 1 797791382 2100000000000000000 witness201=true := by decide +kernel
def witness202 : CapWitness := ⟨true,209,4294967296,305,568,433607,2632000601,8590090400,0,0⟩
theorem cap202 : allowance 5962 19476 20422052159 44879046 2 1595582764 4200000000000000000 witness202=true := by decide +kernel
def witness203 : CapWitness := ⟨true,209,4294967296,305,568,433607,2632000601,4295045154,0,0⟩
theorem cap203 : allowance 5962 19464 20410019627 44879046 1 797791431 2100000000000000000 witness203=true := by decide +kernel
def witness204 : CapWitness := ⟨true,209,4294967296,305,568,433607,2632000601,8590090308,0,0⟩
theorem cap204 : allowance 5962 19464 20410019627 44879046 2 1595582862 4200000000000000000 witness204=true := by decide +kernel
def witness205 : CapWitness := ⟨true,256,4294967296,428,486,433689,3232662765,4295076688,0,0⟩
theorem cap205 : allowance 8467 27348 28676434645 55238978 1 649528102 2100000000000000000 witness205=true := by decide +kernel
def witness206 : CapWitness := ⟨true,256,4294967296,428,486,433689,3232662765,8590153376,0,0⟩
theorem cap206 : allowance 8467 27348 28676434645 55238978 2 1299056204 4200000000000000000 witness206=true := by decide +kernel
def witness207 : CapWitness := ⟨true,166,4294967296,302,704,433471,2093456600,4295044510,0,0⟩
theorem cap207 : allowance 5977 19303 20241226943 35588634 1 1003020493 2100000000000000000 witness207=true := by decide +kernel
def witness208 : CapWitness := ⟨true,166,4294967296,302,704,433471,2093456600,8590089020,0,0⟩
theorem cap208 : allowance 5977 19303 20241226943 35588634 2 2006040986 4200000000000000000 witness208=true := by decide +kernel
def witness209 : CapWitness := ⟨true,166,4294967296,302,704,433471,2093456600,4295044426,0,0⟩
theorem cap209 : allowance 5977 19282 20219285825 35588634 1 1003020607 2100000000000000000 witness209=true := by decide +kernel
def witness210 : CapWitness := ⟨true,166,4294967296,302,704,433471,2093456600,8590088852,0,0⟩
theorem cap210 : allowance 5977 19282 20219285825 35588634 2 2006041215 4200000000000000000 witness210=true := by decide +kernel
def witness211 : CapWitness := ⟨true,234,4294967296,427,527,433648,2951830095,4295076551,0,0⟩
theorem cap211 : allowance 8467 27313 28640526589 50394512 1 711323094 2100000000000000000 witness211=true := by decide +kernel
def witness212 : CapWitness := ⟨true,234,4294967296,427,527,433648,2951830095,8590153102,0,0⟩
theorem cap212 : allowance 8467 27313 28640526589 50394512 2 1422646188 4200000000000000000 witness212=true := by decide +kernel
def witness213 : CapWitness := ⟨true,234,4294967296,427,527,433648,2951830095,4295076491,0,0⟩
theorem cap213 : allowance 8467 27298 28624994399 50394512 1 711323149 2100000000000000000 witness213=true := by decide +kernel
def witness214 : CapWitness := ⟨true,234,4294967296,427,527,433648,2951830095,8590152982,0,0⟩
theorem cap214 : allowance 8467 27298 28624994399 50394512 2 1422646298 4200000000000000000 witness214=true := by decide +kernel
def witness215 : CapWitness := ⟨true,234,4294967296,428,527,433648,2951830095,4295076669,0,0⟩
theorem cap215 : allowance 8467 27343 28671590179 50394512 1 711322984 2100000000000000000 witness215=true := by decide +kernel
def witness216 : CapWitness := ⟨true,234,4294967296,428,527,433648,2951830095,8590153338,0,0⟩
theorem cap216 : allowance 8467 27343 28671590179 50394512 2 1422645969 4200000000000000000 witness216=true := by decide +kernel
def witness217 : CapWitness := ⟨true,85,4294967296,90,1305,432870,1080748542,4294990135,0,0⟩
theorem cap217 : allowance 1800 5709 5987177711 18119393 1 1156546821 1250000000000000000 witness217=true := by decide +kernel
def witness218 : CapWitness := ⟨true,85,4294967296,90,1305,432870,1080748542,8589980270,0,0⟩
theorem cap218 : allowance 1800 5709 5987177711 18119393 2 2313093643 2500000000000000000 witness218=true := by decide +kernel
def witness219 : CapWitness := ⟨true,38,1073741824,46,2864,431311,492409891,3076923077,0,0⟩
theorem cap219 : allowance 200 729 764437173 7969177 1 115020758 56640380321591923 witness219=true := by decide +kernel
def witness220 : CapWitness := ⟨true,38,1073741824,46,2864,431311,492409891,3076923077,0,0⟩
theorem cap220 : allowance 200 729 764437173 7969177 2 116615580 57426051232965081 witness220=true := by decide +kernel
def witness221 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap221 : allowance 80 295 309381967 105696400 1 11167338 33314235252844521 witness221=true := by decide +kernel
def witness222 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap222 : allowance 80 295 309381967 105696400 2 11317845 33763225783357985 witness222=true := by decide +kernel
def witness223 : CapWitness := ⟨true,67,4294967296,425,1690,432485,857171784,4295075964,0,0⟩
theorem cap223 : allowance 8500 27167 28486693279 14260633 1 3732452564 3200000000000000000 witness223=true := by decide +kernel
def witness224 : CapWitness := ⟨true,67,4294967296,425,1690,432485,857171784,8590151928,0,0⟩
theorem cap224 : allowance 8500 27167 28486693279 14260633 2 7464905129 6400000000000000000 witness224=true := by decide +kernel
def witness225 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap225 : allowance 200 740 776390947 7969177 1 131065116 64540885995656848 witness225=true := by decide +kernel
def witness226 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap226 : allowance 200 740 776390947 7969177 2 132926629 65457884686461137 witness226=true := by decide +kernel
def witness227 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap227 : allowance 80 299 314415135 110729568 1 12100133 36587216231806008 witness227=true := by decide +kernel
def witness228 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap228 : allowance 80 299 314415135 110729568 2 12267228 37092462301213569 witness228=true := by decide +kernel
def witness229 : CapWitness := ⟨true,9,4294967296,46,11274,422901,127771017,12000000000,0,0⟩
theorem cap229 : allowance 900 2913 3054825679 1677721 1 1380044031 176385060686452383 witness229=true := by decide +kernel
def witness230 : CapWitness := ⟨true,9,4294967296,46,11274,422901,127771017,12000000000,0,0⟩
theorem cap230 : allowance 900 2913 3054825679 1677721 2 1411941690 180461493909403518 witness230=true := by decide +kernel
def witness231 : CapWitness := ⟨true,25,4294967296,46,4301,429874,322167897,4615384616,0,0⟩
theorem cap231 : allowance 900 2913 3054825679 5033164 1 1380039932 444639048843053575 witness231=true := by decide +kernel
def witness232 : CapWitness := ⟨true,25,4294967296,46,4301,429874,322167897,8589957898,0,0⟩
theorem cap232 : allowance 900 2913 3054825679 5033164 2 1411937497 454928401379838920 witness232=true := by decide +kernel
def witness233 : CapWitness := ⟨true,48,4294967296,46,2279,431896,613943142,4294978949,0,0⟩
theorem cap233 : allowance 900 2913 3054825679 10066329 1 1380031734 847295421486419247 witness233=true := by decide +kernel
def witness234 : CapWitness := ⟨true,48,4294967296,46,2279,431896,613943142,8589957898,0,0⟩
theorem cap234 : allowance 900 2913 3054825679 10066329 2 1411929110 866893361110972672 witness234=true := by decide +kernel
def witness235 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap235 : allowance 200 740 776390947 7969177 1 133381918 65681710792746434 witness235=true := by decide +kernel
def witness236 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap236 : allowance 200 740 776390947 7969177 2 135276355 66614921708686655 witness236=true := by decide +kernel
def witness237 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap237 : allowance 80 299 314415135 110729568 1 12180755 36830993264815782 witness237=true := by decide +kernel
def witness238 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap238 : allowance 80 299 314415135 110729568 2 12348966 37339613787459915 witness238=true := by decide +kernel
def witness239 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,4295079042,0,0⟩
theorem cap239 : allowance 8446 27936 29293529357 86130075 1 636946702 3200000000000000000 witness239=true := by decide +kernel
def witness240 : CapWitness := ⟨true,399,4294967296,437,333,433842,5023419846,8590158084,0,0⟩
theorem cap240 : allowance 8446 27936 29293529357 86130075 2 1273893404 6400000000000000000 witness240=true := by decide +kernel
def witness241 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,4295019280,0,0⟩
theorem cap241 : allowance 3985 12996 13627375241 42278596 1 846312644 2100000000000000000 witness241=true := by decide +kernel
def witness242 : CapWitness := ⟨true,197,4294967296,204,587,433588,2481183468,8590038560,0,0⟩
theorem cap242 : allowance 3985 12996 13627375241 42278596 2 1692625288 4200000000000000000 witness242=true := by decide +kernel
def witness243 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap243 : allowance 12 43 45232891 13841196 1 48319 20801885224064 witness243=true := by decide +kernel
def witness244 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap244 : allowance 12 43 45232891 13841196 2 49047 21115342006440 witness244=true := by decide +kernel
def witness245 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap245 : allowance 80 299 314415135 110729568 1 16364285 49480748057643792 witness245=true := by decide +kernel
def witness246 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap246 : allowance 80 299 314415135 110729568 2 16590406 50164471256748395 witness246=true := by decide +kernel
def witness247 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap247 : allowance 12 43 45232891 13841196 1 103521 44566929598800 witness247=true := by decide +kernel
def witness248 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap248 : allowance 12 43 45232891 13841196 2 105147 45266984871240 witness248=true := by decide +kernel
def witness249 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap249 : allowance 200 740 776390947 7969177 1 133383186 65682335173182358 witness249=true := by decide +kernel
def witness250 : CapWitness := ⟨true,38,1073741824,47,2864,431311,492409891,3076923077,0,0⟩
theorem cap250 : allowance 200 740 776390947 7969177 2 135277640 66615554460153660 witness250=true := by decide +kernel
def witness251 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap251 : allowance 80 299 314415135 110729568 1 12180855 36831295635177482 witness251=true := by decide +kernel
def witness252 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap252 : allowance 12 43 45232891 13841196 1 128344 55253493428264 witness252=true := by decide +kernel
def witness253 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap253 : allowance 12 43 45232891 13841196 2 130374 56127474970176 witness253=true := by decide +kernel
def witness254 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap254 : allowance 80 299 314415135 110729568 1 16365905 49485646457503332 witness254=true := by decide +kernel
def witness255 : CapWitness := ⟨false,0,0,0,0,0,0,0,0,0⟩
theorem cap255 : allowance 80 299 314415135 110729568 2 16592049 50169439201791126 witness255=true := by decide +kernel
theorem total1 : (1515102681173026613+3200000000000000000+2100000000000000000+1250000000000000000+65682344529040625+36831298658881099 : ℕ)=8167616324360948337 := by decide
theorem total2 : (1536625609226345136+6400000000000000000+4200000000000000000+2500000000000000000+66615563816011927+37339925228932466 : ℕ)=14740581098271289529 := by decide
#print axioms cap255
end Binary6402NativeCaps
